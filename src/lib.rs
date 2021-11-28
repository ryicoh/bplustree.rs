use std::{
    cell::RefCell,
    fmt::{Debug, Formatter},
    rc::Rc,
};

pub struct BPlusTree<K: Ord + Debug, V: Clone> {
    root: Node<K, V>,
}

impl<K: Ord + Debug, V: Clone> Debug for BPlusTree<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", &self.root)
    }
}

impl<K: Ord + Debug, V: Clone> BPlusTree<K, V> {
    pub fn new(capacity: usize) -> Self {
        Self {
            root: Node::Leaf(LeafNodeRef::new(capacity, None)),
        }
    }

    pub fn set(&mut self, key: K, val: V) -> SetResult {
        let search = self.root.search(&key, vec![]);
        if search.found {
            LeafNodeRef(search.leaf.clone()).update(search.key_index, val);
            return SetResult::Updated;
        }

        if let Some(new_node) = LeafNodeRef(search.leaf.clone()).insert(&search, key, val) {
            if search.path.is_empty() {
                self.root = new_node;
            } else {
                let mut node1: Rc<RefCell<InternalNode<K, V>>> = self.root.to_internal().unwrap();
                let mut node2: Rc<RefCell<InternalNode<K, V>>> = self.root.to_internal().unwrap();
                for (i, idx) in search.path[..(search.path.len() - 1)].iter().enumerate() {
                    if i % 2 == 0 {
                        node2 = node1.borrow_mut().children[*idx].to_internal().unwrap();
                    } else {
                        node1 = node2.borrow_mut().children[*idx].to_internal().unwrap();
                    }
                }

                let idx = search.path[search.path.len() - 1];
                if search.path.len() % 2 == 0 {
                    node2.borrow_mut().children[idx] = new_node;
                } else {
                    node1.borrow_mut().children[idx] = new_node;
                }
            }
        }

        assert!(self.root.check_sorted().is_ok());
        SetResult::Inserted
    }

    pub fn get(&self, key: &K, opt: &GetOption<K>) -> Vec<V> {
        let search = self.root.search(&key, vec![]);

        if opt.limit != 0 || opt.to.is_some() {
            todo!();
        }

        if !search.found {
            return vec![];
        }

        let leaf = search.leaf.borrow();
        vec![leaf.values[search.key_index].clone()]
    }
}

pub struct GetOption<'a, K> {
    limit: usize,
    to: Option<&'a K>,
}

struct SearchResult<K: Ord + Debug, V> {
    leaf: Rc<RefCell<LeafNode<K, V>>>,
    path: Vec<usize>,
    leaf_index: usize,
    key_index: usize,
    found: bool,
}

#[derive(PartialEq, Debug)]
pub enum SetResult {
    Updated,
    Inserted,
}

enum Node<K: Ord + Debug, V> {
    Internal(InternalNodeRef<K, V>),
    Leaf(LeafNodeRef<K, V>),
}

impl<K: Ord + Debug, V> Debug for Node<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Node::Internal(internal) => {
                for (i, child) in internal.0.borrow().children.iter().enumerate() {
                    if i != 0 {
                        write!(f, "{:?}", internal.0.borrow().keys[i - 1].borrow()).unwrap();
                    }
                    write!(f, "{:?} ", child).unwrap();
                }
                Ok(())
            }
            Node::Leaf(leaf) => {
                write!(f, "[").unwrap();
                for (i, key) in leaf.0.borrow().keys.iter().enumerate() {
                    write!(f, "{:?}", key.borrow()).unwrap();
                    if i + 1 != leaf.0.borrow().keys.len() {
                        write!(f, ",").unwrap();
                    }
                }
                write!(f, "]").unwrap();
                Ok(())
            }
        }
    }
}

impl<K: Ord + Debug, V> Node<K, V> {
    fn search(&self, key: &K, mut path: Vec<usize>) -> SearchResult<K, V> {
        let res = match self {
            Node::Internal(internal) => internal
                .0
                .borrow()
                .keys
                .binary_search_by(|k| k.borrow().cmp(&key)),
            Node::Leaf(leaf) => leaf
                .0
                .borrow()
                .keys
                .binary_search_by(|k| k.borrow().cmp(&key)),
        };

        let found = res.is_ok();
        let mut index = match res {
            Result::Ok(idx) => idx,
            Result::Err(idx) => idx,
        };

        match self {
            Node::Internal(internal) => {
                if found {
                    index += 1
                }

                path.push(index);
                internal.0.borrow().children[index].search(key, path)
            }
            Node::Leaf(leaf) => SearchResult {
                leaf: leaf.0.clone(),
                leaf_index: if let Some(idx) = path.last() { *idx } else { 0 },
                key_index: index,
                found,
                path: path.to_vec(),
            },
        }
    }

    #[allow(dead_code)]
    fn to_leaf(&self) -> Result<Rc<RefCell<LeafNode<K, V>>>, ()> {
        match self {
            Node::Internal(_) => Err(()),
            Node::Leaf(leaf) => Ok(leaf.0.clone()),
        }
    }

    #[allow(dead_code)]
    fn to_internal(&self) -> Result<Rc<RefCell<InternalNode<K, V>>>, ()> {
        match self {
            Node::Internal(internal) => Ok(internal.0.clone()),
            Node::Leaf(_) => Err(()),
        }
    }

    fn check_sorted(&self) -> Result<(), ()> {
        match self {
            Node::Internal(internal) => {
                assert!(is_sorted(&internal.0.borrow().keys));
                for child in &internal.0.borrow().children {
                    assert!(child.check_sorted().is_ok());
                }
                for pair in internal.0.borrow().children.windows(2) {
                    if let Node::Leaf(left) = &pair[0] {
                        if let Node::Leaf(right) = &pair[1] {
                            if left.0.borrow().keys.is_empty() || right.0.borrow().keys.is_empty() {
                                continue;
                            }
                            assert!(left.0.borrow().keys.last() < right.0.borrow().keys.first());
                            assert!(std::ptr::eq(
                                left.0.borrow().next.as_ref().unwrap().as_ptr(),
                                right.0.as_ptr()
                            ));
                        }
                    }
                }
            }
            Node::Leaf(leaf) => {
                assert!(is_sorted(&leaf.0.borrow().keys));
            }
        }
        Ok(())
    }
}

struct InternalNodeRef<K: Ord + Debug, V>(Rc<RefCell<InternalNode<K, V>>>);

impl<K: Ord + Debug, V> InternalNodeRef<K, V> {
    fn new(capacity: usize) -> Self {
        Self(Rc::new(RefCell::new(InternalNode {
            keys: Vec::with_capacity(capacity),
            children: Vec::with_capacity(capacity),
        })))
    }
}

fn is_sorted<T>(data: &Vec<T>) -> bool
where
    T: Ord,
{
    data.windows(2).all(|w| w[0] <= w[1])
}

struct InternalNode<K: Ord + Debug, V> {
    children: Vec<Node<K, V>>,
    keys: Vec<Rc<RefCell<K>>>,
}

struct LeafNodeRef<K: Ord + Debug, V>(Rc<RefCell<LeafNode<K, V>>>);
struct LeafNode<K: Ord + Debug, V> {
    parent: Option<Rc<RefCell<InternalNode<K, V>>>>,
    keys: Vec<Rc<RefCell<K>>>,
    values: Vec<V>,
    prev: Option<Rc<RefCell<LeafNode<K, V>>>>,
    next: Option<Rc<RefCell<LeafNode<K, V>>>>,
}

impl<K: Ord + Debug, V> LeafNodeRef<K, V> {
    fn new(capacity: usize, parent: Option<Rc<RefCell<InternalNode<K, V>>>>) -> Self {
        Self(Rc::new(RefCell::new(LeafNode {
            keys: Vec::with_capacity(capacity),
            values: Vec::with_capacity(capacity),
            parent,
            prev: None,
            next: None,
        })))
    }

    fn update(&mut self, index: usize, val: V) {
        self.0.borrow_mut().values[index] = val;
    }

    fn insert(&self, search: &SearchResult<K, V>, key: K, val: V) -> Option<Node<K, V>> {
        let key_rc = Rc::new(RefCell::new(key));

        assert!(is_sorted(&self.0.borrow().keys));
        self.0
            .borrow_mut()
            .keys
            .insert(search.key_index, key_rc.clone());
        assert!(is_sorted(&self.0.borrow().keys));

        self.0.borrow_mut().values.insert(search.key_index, val);

        if self.0.borrow().keys.len() == self.0.borrow().keys.capacity() {
            if let Some(node) = self.split(search) {
                return Some(Node::Internal(node));
            }
        }
        None
    }

    fn split(&self, search: &SearchResult<K, V>) -> Option<InternalNodeRef<K, V>> {
        let capacity = self.0.borrow().keys.capacity();
        let center = capacity / 2;

        if self.0.borrow().parent.is_some() {
            if self.0.borrow().parent.as_ref().unwrap().borrow().keys.len() != capacity {
                let new_leaf = LeafNodeRef::new(
                    capacity,
                    Some(self.0.borrow().parent.as_ref().unwrap().clone()),
                );
                self.0
                    .borrow()
                    .parent
                    .as_ref()
                    .unwrap()
                    .borrow_mut()
                    .keys
                    .insert(search.leaf_index, self.0.borrow().keys[center].clone());
                assert!(is_sorted(
                    &self.0.borrow().parent.as_ref().unwrap().borrow().keys
                ));

                for _ in center..capacity {
                    new_leaf
                        .0
                        .borrow_mut()
                        .keys
                        .push(self.0.borrow_mut().keys.remove(center));
                    new_leaf
                        .0
                        .borrow_mut()
                        .values
                        .push(self.0.borrow_mut().values.remove(center));
                }
                assert!(is_sorted(&self.0.borrow_mut().keys));
                assert!(is_sorted(&new_leaf.0.borrow().keys));

                if search.leaf_index + 1
                    < self
                        .0
                        .borrow()
                        .parent
                        .as_ref()
                        .unwrap()
                        .borrow()
                        .children
                        .len()
                {
                    let next = self
                        .0
                        .borrow()
                        .parent
                        .as_ref()
                        .unwrap()
                        .borrow_mut()
                        .children[search.leaf_index + 1]
                        .to_leaf()
                        .unwrap();
                    next.borrow_mut().prev = Some(new_leaf.0.clone());
                    new_leaf.0.borrow_mut().next = Some(next);
                }

                new_leaf.0.borrow_mut().prev = Some(self.0.clone());
                self.0.clone().borrow_mut().next = Some(new_leaf.0.clone());

                self.0
                    .borrow()
                    .parent
                    .as_ref()
                    .unwrap()
                    .borrow_mut()
                    .children
                    .insert(search.leaf_index + 1, Node::Leaf(new_leaf));

                assert!(is_sorted(&self.0.borrow().keys));
                return None;
            }
        }

        let new_node = InternalNodeRef::<K, V>::new(capacity);
        let left_leaf = LeafNodeRef::new(capacity, Some(new_node.0.clone()));
        let right_leaf = LeafNodeRef::new(capacity, Some(new_node.0.clone()));

        new_node
            .0
            .borrow_mut()
            .keys
            .push(self.0.borrow().keys[center].clone());

        for idx in 0..center {
            left_leaf
                .0
                .borrow_mut()
                .keys
                .push(self.0.borrow().keys[idx].clone());
            left_leaf
                .0
                .borrow_mut()
                .values
                .push(self.0.borrow_mut().values.swap_remove(idx));
        }
        assert!(is_sorted(&left_leaf.0.borrow().keys));

        for idx in center..capacity {
            right_leaf
                .0
                .borrow_mut()
                .keys
                .push(self.0.borrow().keys[idx].clone());
            right_leaf
                .0
                .borrow_mut()
                .values
                .push(self.0.borrow_mut().values.pop().unwrap());
        }
        assert!(is_sorted(&right_leaf.0.borrow().keys));

        left_leaf.0.borrow_mut().next = Some(right_leaf.0.clone());
        right_leaf.0.borrow_mut().prev = Some(left_leaf.0.clone());
        new_node.0.borrow_mut().children.push(Node::Leaf(left_leaf));
        new_node
            .0
            .borrow_mut()
            .children
            .push(Node::Leaf(right_leaf));

        return Some(new_node);
    }
}

#[cfg(test)]
mod tests {
    use rand::prelude::SliceRandom;

    use super::*;

    #[test]
    fn set_test() {
        let mut tree = BPlusTree::<String, String>::new(3);
        assert_eq!(
            tree.set("key1".to_string(), "val1".to_string()),
            SetResult::Inserted
        );

        assert_eq!(
            tree.root.to_leaf().unwrap().borrow().keys,
            vec![Rc::new(RefCell::new("key1".to_string()))],
        );
        assert_eq!(
            tree.root.to_leaf().unwrap().borrow().values,
            vec!["val1".to_string()],
        );

        assert_eq!(
            tree.set("key2".to_string(), "val2".to_string()),
            SetResult::Inserted
        );
        assert_eq!(
            tree.set("key2".to_string(), "new_val2".to_string()),
            SetResult::Updated
        );

        assert_eq!(
            tree.root.to_leaf().unwrap().borrow().values,
            vec!["val1".to_string(), "new_val2".to_string()],
        );

        assert_eq!(
            tree.set("key3".to_string(), "val3".to_string()),
            SetResult::Inserted
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().keys,
            vec![Rc::new(RefCell::new("key2".to_string()))],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[0]
                .to_leaf()
                .unwrap()
                .borrow()
                .keys,
            vec![Rc::new(RefCell::new("key1".to_string()))],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[0]
                .to_leaf()
                .unwrap()
                .borrow()
                .values,
            vec!["val1".to_string()],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[1]
                .to_leaf()
                .unwrap()
                .borrow()
                .values,
            vec!["new_val2".to_string(), "val3".to_string()],
        );

        assert_eq!(
            tree.set("key0".to_string(), "val0".to_string()),
            SetResult::Inserted
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().keys,
            vec![Rc::new(RefCell::new("key2".to_string()))],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[0]
                .to_leaf()
                .unwrap()
                .borrow()
                .keys,
            vec![
                Rc::new(RefCell::new("key0".to_string())),
                Rc::new(RefCell::new("key1".to_string()))
            ],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[0]
                .to_leaf()
                .unwrap()
                .borrow()
                .values,
            vec!["val0".to_string(), "val1".to_string()],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[1]
                .to_leaf()
                .unwrap()
                .borrow()
                .values,
            vec!["new_val2".to_string(), "val3".to_string()],
        );

        assert_eq!(
            tree.set("key4".to_string(), "val4".to_string()),
            SetResult::Inserted
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().keys,
            vec![
                Rc::new(RefCell::new("key2".to_string())),
                Rc::new(RefCell::new("key3".to_string())),
            ],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[0]
                .to_leaf()
                .unwrap()
                .borrow()
                .keys,
            vec![
                Rc::new(RefCell::new("key0".to_string())),
                Rc::new(RefCell::new("key1".to_string())),
            ],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[0]
                .to_leaf()
                .unwrap()
                .borrow()
                .values,
            vec!["val0".to_string(), "val1".to_string()],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[1]
                .to_leaf()
                .unwrap()
                .borrow()
                .keys,
            vec![Rc::new(RefCell::new("key2".to_string())),],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[1]
                .to_leaf()
                .unwrap()
                .borrow()
                .values,
            vec!["new_val2".to_string()],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[2]
                .to_leaf()
                .unwrap()
                .borrow()
                .keys,
            vec![
                Rc::new(RefCell::new("key3".to_string())),
                Rc::new(RefCell::new("key4".to_string())),
            ],
        );
        assert_eq!(
            tree.root.to_internal().unwrap().borrow().children[2]
                .to_leaf()
                .unwrap()
                .borrow()
                .values,
            vec!["val3".to_string(), "val4".to_string()],
        );
    }

    #[test]
    fn set_random_i64_test() {
        let mut tree = BPlusTree::<i64, ()>::new(5);
        let mut rng = rand::thread_rng();
        let mut nums: Vec<i64> = (1..1000).collect();
        nums.shuffle(&mut rng);

        for n in nums {
            assert_eq!(tree.set(n, ()), SetResult::Inserted);
        }
    }

    #[test]
    fn get_random_i64_test() {
        let mut tree = BPlusTree::<i64, String>::new(5);
        let mut rng = rand::thread_rng();
        let mut nums: Vec<i64> = (0..1000).collect();
        nums.shuffle(&mut rng);

        for n in &nums {
            assert_eq!(tree.set(*n, n.to_string()), SetResult::Inserted);
            println!("{:?}", n);
            println!("{:?}", tree);
        }

        for n in &nums {
            assert_eq!(
                tree.get(n, &GetOption { limit: 0, to: None }),
                vec![n.to_string()]
            );
        }
    }
}
