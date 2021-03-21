use std::cell::RefCell;
use std::collections::HashMap;
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
struct Node<T> where T: Hash + Eq {
    value: T,
    outs: Vec<Link<T>>,
    ins: Vec<Link<T>>,
}

impl <T> PartialEq for Node<T> where T: Hash + Eq {
    fn eq(&self, other: &Self) -> bool {
        return self.value.eq(&other.value);
    }
}

impl <T> Hash for Node<T> where T: Hash + Eq {
    fn hash<H: Hasher>(&self, state: &mut H) {
        return self.value.hash(state);
    }
}

impl <T> Node<T> where T: Clone + Hash + Eq {
    ///
    /// Creates a Node as a Link.  Nodes don't really live
    /// outside of Links so this is better.
    ///
    fn new_link(value: T) -> Link<T> {
        return Rc::new(RefCell::new(Node {
            value,
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
        self.outs.push(node);
    }

    ///
    /// Add an in
    ///
    fn link_in(&mut self, node: Link<T>) {
        self.ins.push(node);
    }

    ///
    /// Detect and return the first cycle in this nodes out path
    ///
    fn get_cycle_path(&self) -> Option<Vec<T>> {
        let mut path: Vec<T> = Vec::new();
        if !self.visit_mut(&mut |c, _, _| {
            if path.contains(c) {
                path.push(c.clone());
                return true;
            }
            path.push(c.clone());
            return false;
        }) {
            return None;
        }
        return Some(path);
    }

    ///
    /// link 2 nodes.  The direction is from -> to
    ///
    fn link(node_from: Link<T>, node_to: Link<T>) {
        node_from.borrow_mut().link_out(node_to.clone());
        node_to.borrow_mut().link_in(node_from.clone());
    }
}

///
/// Visitable impl
///
impl <T> Visitable<T> for Node<T> where T: Clone + Hash + Eq {
    fn visit_mut<V>(&self, visitor: &mut V) -> bool
        where V: FnMut(&T, bool, bool) -> bool {

        if visitor(&self.value, self.is_head(), self.is_tail()) {
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
        if visitor(&self.value, self.is_head(), self.is_tail()) {
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
struct HashDAG<T> where T: Clone + Hash + Eq {
    map: HashMap<T, Link<T>>
}

impl <T> HashDAG<T> where T: Clone + Hash + Eq {
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
            for link in self.map.values() {
                let node = link.borrow();
                if let Some(cycle) = node.get_cycle_path() {
                    paths.push(cycle);
                }
                break;
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
}

impl <T> Visitable<T> for HashDAG<T> where T: Clone + Hash + Eq {
    fn visit_mut<V>(&self, visitor: &mut V) -> bool
        where V: FnMut(&T, bool, bool) -> bool {
        for link in self.map.values() {
            let node = link.borrow();
            if node.is_head() {
                if node.visit_mut(visitor) {
                    return true;
                }
            }
        }
        return false;
    }

    fn visit(&self, visitor: fn(&T, bool, bool) -> bool) -> bool {
        for link in self.map.values() {
            let node = link.borrow();
            if node.is_head() {
                if node.visit(visitor) {
                    return true;
                }
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
            .link('a', 'b')
            .link('y', 'z')
            .link('b', 'c')
            .link('x', 'y');

        dag.visit(|c: &char, head: bool, tail: bool| {
            println!("{} {} {}", c, head, tail);
            return false;
        });

        println!("Contains cycle: {}", dag.contains_cycle());

        dag.link('z', 'a');

        println!("Contains cycle: {}", dag.contains_cycle());

        dag.visit(|c: &char, head: bool, tail: bool| {
            println!("{} {} {}", c, head, tail);
            return false;
        });

        dag.link('b', 'z');

        let x: Vec<String> = dag.get_cycles(false).iter()
            .map(|a| String::from_iter(a))
            .collect();
        println!("Contains cycle: {}", dag.contains_cycle());
        println!("Cycles {}", x.join("\n"));
    }
}