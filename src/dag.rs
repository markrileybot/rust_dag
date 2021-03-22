#![cfg_attr(feature = "cargo-clippy", allow(clippy::needless_return))]

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

type Link<T> = Rc<RefCell<Node<T>>>;

///
/// Things that can be visited with a closure or a function pointer.
///
/// Obviously the function pointer is better to use if you don't
/// need to pass state
///
trait Visitable<T> {
    ///
    /// Visit mutably.  This is good for when you want to keep state
    /// and use it outside of the visit.
    ///
    fn visit_mut<V>(&self, visitor: &mut V) -> bool
        where V: FnMut(&T, bool, bool) -> bool;

    ///
    /// Visit with a function pointer.  Simpler.
    ///
    fn visit(&self, visitor: fn(&T, bool, bool) -> bool) -> bool;
}

///
/// dag node
///
struct Node<T> {
    entry: T,
    outs: Vec<Link<T>>,
    ins: Vec<Link<T>>,
}

impl <T> Display for Node<T> where T: Display {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.entry)
    }
}

impl <T> PartialEq for Node<T> where T: Hash + Eq {
    fn eq(&self, other: &Self) -> bool {
        return self.entry.eq(&other.entry);
    }
}

impl <T> Hash for Node<T> where T: Hash + Eq {
    fn hash<H: Hasher>(&self, state: &mut H) {
        return self.entry.hash(state);
    }
}

impl <T> Node<T> where T: Clone + Hash + Eq {
    ///
    /// Creates a Node as a Link.  Nodes don't really live
    /// outside of Links so this is better.
    ///
    fn new_link(value: T) -> Link<T> {
        return Rc::new(RefCell::new(Node {
            entry: value,
            outs: Vec::new(),
            ins: Vec::new()
        }));
    }

    ///
    /// Is this a head? (no ins)
    ///
    fn is_head(&self) -> bool {
        return self.ins.is_empty();
    }

    ///
    /// Is this a tail? (no outs)
    ///
    fn is_tail(&self) -> bool {
        return self.outs.is_empty();
    }

    ///
    /// Add an out
    ///
    fn link_out(&mut self, node: Link<T>) {
        if !self.outs.contains(&node) {
            self.outs.push(node);
        }
    }

    ///
    /// Add an in
    ///
    fn link_in(&mut self, node: Link<T>) {
        if !self.ins.contains(&node) {
            self.ins.push(node);
        }
    }

    ///
    /// Find all direct links that also have indirect links
    /// and remove them.
    ///
    fn get_removable_direct_links(&self) -> Vec<Link<T>> {
        let mut removals: Vec<Link<T>> = Vec::new();
        for link in &self.outs {
            for link2 in &self.outs {
                if link != link2 &&
                    link2.borrow().visit_mut(&mut |c, _, _| c == &link.borrow().entry) {
                    removals.push(link.clone());
                    break;
                }
            }
        }

        return removals;
    }

    ///
    /// Detect and return the first cycle in this nodes out path
    ///    b
    /// a / \ d - e
    ///   \ /
    ///    c
    fn get_cycle_path(&self) -> Option<Vec<T>> {
        let mut path: Vec<T> = Vec::new();
        self.get_cycle_path_internal(&mut path);
        if path.is_empty() {
            return None;
        }
        return Some(path);
    }

    fn get_cycle_path_internal(&self, path: &mut Vec<T>) -> bool {
        if path.contains(&self.entry) {
            path.push(self.entry.clone());
            return true;
        }
        path.push(self.entry.clone());
        for link in &self.outs {
            if link.borrow().get_cycle_path_internal(path) {
                return true;
            }
        }
        path.pop();
        return false;
    }

    ///
    /// link 2 nodes.  The direction is from -> to
    ///
    fn link(node_from: Link<T>, node_to: Link<T>) {
        if node_from != node_to {
            node_from.borrow_mut().link_out(node_to.clone());
            node_to.borrow_mut().link_in(node_from.clone());
        }
    }
}

///
/// Visitable impl
///
impl <T> Visitable<T> for Node<T> where T: Clone + Hash + Eq {
    fn visit_mut<V>(&self, visitor: &mut V) -> bool
        where V: FnMut(&T, bool, bool) -> bool {

        if visitor(&self.entry, self.is_head(), self.is_tail()) {
            return true;
        }
        for link in &self.outs {
            if link.borrow().visit_mut(visitor) {
                return true;
            }
        }
        return false;
    }

    fn visit(&self, visitor: fn(&T, bool, bool) -> bool) -> bool {
        if visitor(&self.entry, self.is_head(), self.is_tail()) {
            return true;
        }
        for link in &self.outs {
            if link.borrow().visit(visitor) {
                return true;
            }
        }
        return false;
    }
}

///
/// A thing that holds links in a hash map and a graph.
/// The key to the map is T
///
struct HashDAG<T> {
    map: HashMap<T, Link<T>>
}

impl <T> HashDAG<T> where T: Clone + Hash + Eq + Display {
    fn new() -> Self {
        return Self {
            map: HashMap::new()
        }
    }

    ///
    /// Add and/or link o1 and o2.  Returns self for fluent fun
    ///
    fn link(&mut self, o1: T, o2: T) -> & mut Self {
        let link1 = self.map.entry(o1.clone())
            .or_insert_with(|| Node::new_link(o1)).clone();
        let link2 = self.map.entry(o2.clone())
            .or_insert_with(|| Node::new_link(o2)).clone();
        Node::link(link1, link2);
        return self;
    }

    fn sort(&self) {
        for link in self.map.values() {
            let removables = link.borrow().get_removable_direct_links();
            link.borrow_mut().outs.retain(|link| !removables.contains(link));
            for remove in removables {
                remove.borrow_mut().ins.retain(|li| li != link);
            }
        }
    }

    ///
    /// Get all the cycles in the graph
    ///
    fn get_cycles(&self, first: bool) -> Vec<Vec<T>> {
        let mut head_count = 0;
        let mut paths: Vec<Vec<T>> = Vec::new();
        for link in self.map.values() {
            let node = link.borrow();
            if node.is_head() {
                head_count += 1;
                if let Some(cycle) = node.get_cycle_path() {
                    paths.push(cycle);
                    if first {
                        break;
                    }
                }
            }
        }

        // if head count is 0 then the entire thing is a cycle
        if head_count == 0 {
            let link = self.map.values().find(|_| true).unwrap();
            let node = link.borrow();
            if let Some(cycle) = node.get_cycle_path() {
                paths.push(cycle);
            }
        }

        return paths;
    }

    ///
    /// Does the graph contain any cycles?
    ///
    fn contains_cycle(&self) -> bool {
        return !(self.get_cycles(true).is_empty());
    }

    fn is_singly_linked(&self) -> bool {
        let mut head_count: usize = 0;
        let mut tail_count: usize = 0;
        for link in self.map.values() {
            let node = link.borrow();
            if node.is_head() {
                head_count += 1;
                if node.outs.len() != 1 {
                    return false;
                }
            } else if node.is_tail() {
                tail_count += 1;
                if node.ins.len() != 1 {
                    return false;
                }
            } else if node.ins.len() != 1 || node.outs.len() != 1 {
                return false;
            }
        }
        return head_count == 1 && tail_count == 1;
    }
}

impl <T> Visitable<T> for HashDAG<T> where T: Clone + Hash + Eq {
    fn visit_mut<V>(&self, visitor: &mut V) -> bool
        where V: FnMut(&T, bool, bool) -> bool {
        for link in self.map.values() {
            let node = link.borrow();
            if node.is_head() && node.visit_mut(visitor) {
                return true;
            }
        }
        return false;
    }

    fn visit(&self, visitor: fn(&T, bool, bool) -> bool) -> bool {
        for link in self.map.values() {
            let node = link.borrow();
            if node.is_head() && node.visit(visitor) {
                return true;
            }
        }
        return false;
    }
}

#[cfg(test)]
mod tests {
    use std::iter::FromIterator;

    use crate::dag::{HashDAG, Visitable};

    #[test]
    fn test_stuff() {
        let mut dag: HashDAG<char> = HashDAG::new();
        dag.link('c', 'd')
            .link('a', 'd')
            .link('b', 'c')
            .link('a', 'b')
            .link('a', 'c')
            .link('a', 'b')
            .link('a', 'a');

        let printer = |c: &char, head: bool, tail: bool| {
            if tail {
                println!("{} >>", c);
            } else if head {
                print!("<< {}->", c);
            } else {
                print!("{}->", c);
            }
            return false;
        };

        assert_eq!(dag.is_singly_linked(), false);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(printer);

        dag.sort();
        assert_eq!(dag.is_singly_linked(), true);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(printer);

        dag.link('a', 'x');
        dag.link('d', 'x');
        assert_eq!(dag.is_singly_linked(), false);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(printer);

        dag.sort();
        assert_eq!(dag.is_singly_linked(), true);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(printer);

        dag.link('c', 'f');
        dag.link('f', 'd');
        assert_eq!(dag.is_singly_linked(), false);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(printer);

        dag.sort();
        assert_eq!(dag.is_singly_linked(), true);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(printer);

        dag.link('x', 'd');
        assert_eq!(dag.is_singly_linked(), false);
        assert_eq!(dag.contains_cycle(), true);
        let cycles: Vec<String> = dag.get_cycles(false).iter()
            .map(String::from_iter)
            .collect();
        println!("{}", cycles.join("\n"));
    }
}