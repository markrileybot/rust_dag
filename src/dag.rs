#![cfg_attr(feature = "cargo-clippy", allow(clippy::needless_return))]

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::option::Option::Some;
use std::rc::Rc;

type Link<T> = Rc<RefCell<Node<T>>>;

trait Owner {}

struct VisitState<T> {
    entry: Option<T>,
    head: bool,
    tail: bool,
    level: usize
}

impl <T> VisitState<T> {
    fn new() -> Self {
        return Self {
            entry: None,
            head: false,
            tail: false,
            level: 0
        }
    }
}

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
        where V: FnMut(&VisitState<T>) -> bool {
        return self._visit_mut(&mut VisitState::new(), visitor);
    }

    ///
    /// Visit borrowed
    ///
    fn visit_ref<V>(&self, visitor: &V) -> bool
        where V: Fn(&VisitState<T>) -> bool {
        return self._visit_ref(&mut VisitState::new(), visitor);
    }

    ///
    /// Visit with a function pointer.  Simpler.
    ///
    fn visit(&self, visitor: fn(&VisitState<T>) -> bool) -> bool {
        return self._visit(&mut VisitState::new(), visitor);
    }

    ///
    /// Visit mutably.  This is good for when you want to keep state
    /// and use it outside of the visit.
    ///
    fn _visit_mut<V>(&self, state: &mut VisitState<T>, visitor: &mut V) -> bool
        where V: FnMut(&VisitState<T>) -> bool;

    ///
    /// Visit borrowed
    ///
    fn _visit_ref<V>(&self, state: &mut VisitState<T>, visitor: &V) -> bool
        where V: Fn(&VisitState<T>) -> bool;

    ///
    /// Visit with a function pointer.  Simpler.
    ///
    fn _visit(&self, state: &mut VisitState<T>, visitor: fn(&VisitState<T>) -> bool) -> bool;
}

///
/// dag node
///
struct Node<T> {
    entry: T,
    outs: Vec<Link<T>>,
    ins: Vec<Link<T>>
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
    /// Is this singly linked? (single out and single in)
    fn is_singly_linked(&self) -> bool {
        return (self.is_head() && self.outs.len() == 1)
            || (self.is_tail() && self.ins.len() == 1)
            || (self.outs.len() == 1 && self.ins.len() == 1);
    }

    ///
    /// Is this guy an island? (no links)
    ///
    fn is_island(&self) -> bool {
        return self.is_head() && self.is_tail();
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
    /// Remove an out
    ///
    fn unlink_out(&mut self, node: &Link<T>) {
        self.outs.retain(|li| li != node);
    }

    ///
    /// Remove an in
    ///
    fn unlink_in(&mut self, node: &Link<T>) {
        self.ins.retain(|li| li != node);
    }

    ///
    /// Find all direct links that also have indirect links and remove them.
    ///
    fn get_removable_direct_links(&self) -> Vec<Link<T>> {
        let mut removals: Vec<Link<T>> = Vec::new();
        for link in &self.outs {
            let node = link.borrow();
            for link2 in &self.outs {
                let node2 = link2.borrow();
                if link != link2 && node2.visit_ref(&|s|
                    s.entry.as_ref().unwrap() == &node.entry) {
                    removals.push(link.clone());
                    break;
                }
            }
        }

        return removals;
    }

    ///
    /// Detect and return the first cycle in this nodes out path
    ///
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
    fn link(node_from: &Link<T>, node_to: &Link<T>) {
        if node_from != node_to {
            node_from.borrow_mut().link_out(node_to.clone());
            node_to.borrow_mut().link_in(node_from.clone());
        }
    }

    ///
    /// unlink 2 nodes.  The direction is from -> to
    ///
    fn unlink(node_from: &Link<T>, node_to: &Link<T>) {
        node_from.borrow_mut().unlink_out(&node_to);
        node_to.borrow_mut().unlink_in(&node_from);
    }

    ///
    /// unlink everything from/to node_from
    ///
    fn unlink_all(node_from: &Link<T>) {
        let mut outs_clone: Vec<Link<T>> = Vec::new();
        let mut ins_clone: Vec<Link<T>> = Vec::new();
        {
            let node = node_from.borrow();
            for me_out in &node.outs {
                outs_clone.push(me_out.clone());
            }
            for me_in in &node.ins {
                ins_clone.push(me_in.clone());
            }
        }

        for l in outs_clone {
            Node::unlink(node_from, &l);
        }
        for l in ins_clone {
            Node::unlink(&l, node_from);
        }
    }
}

macro_rules! node_visit_impl {
    ($self:expr, $state:expr, $visitor:expr, $visit_call:ident) => {{
        $state.entry = Some($self.entry.clone());
        $state.head = $self.is_head();
        $state.tail = $self.is_tail();
        $state.level += 1;

        if $visitor(&$state) {
            return true;
        }
        for link in &$self.outs {
            let node = link.borrow();
            if node.$visit_call($state, $visitor) {
                return true;
            }
        }

        $state.level -= 1;
        return false;
    }}
}

///
/// Visitable impl
///
impl <T> Visitable<T> for Node<T> where T: Clone + Hash + Eq {

    fn _visit_mut<V>(&self, state: &mut VisitState<T>, visitor: &mut V) -> bool
        where V: FnMut(&VisitState<T>) -> bool {
        node_visit_impl!(self, state, visitor, _visit_mut);
    }

    fn _visit_ref<V>(&self, state: &mut VisitState<T>, visitor: &V) -> bool
        where V: Fn(&VisitState<T>) -> bool {
        node_visit_impl!(self, state, visitor, _visit_ref);
    }

    fn _visit(&self, state: &mut VisitState<T>, visitor: fn(&VisitState<T>) -> bool) -> bool {
        node_visit_impl!(self, state, visitor, _visit);
    }
}

impl <T> Owner for Node<T> {}

///
/// A thing that holds links in a hash map and a graph.
/// The key to the map is T
///
struct HashDAG<T> {
    map: HashMap<T, Link<T>>
}

///
/// An iter over HashDAG that is sorted
///
struct SortedIter<'a, T> {
    map: &'a HashMap<T, Link<T>>,
    seen: HashSet<T>,
    head_count: usize,
    tail_count: usize
}

impl <'a, T> SortedIter<'a, T> {
    fn new(map: &'a HashMap<T, Link<T>>) -> Self {
        let map_len = map.len();
        return Self {
            map,
            head_count: 0,
            tail_count: 0,
            seen: HashSet::with_capacity(map_len)
        }
    }
}

impl <'a, T> Iterator for SortedIter<'a, T> where T: Clone + Hash + Eq {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let map = self.map;
        let mut iter_count: usize = 0;
        while self.seen.len() < map.len() {
            for link in map.values() {

                iter_count += 1;

                let node = link.borrow();

                // if we've seen it, next
                if self.seen.contains(&node.entry) {
                    continue;
                }

                if node.is_head() {
                    self.head_count += 1;
                } else if node.is_tail() {
                    self.tail_count += 1;
                }


                // if all the ins have been seen (returned)
                if node.ins.iter().all(|l| self.seen.contains(&l.borrow().entry)) {
                    self.seen.insert(node.entry.clone());
                    return Some(node.entry.clone());
                }
            }

            // if we get here then we've hit every node.  This is most likely a cycle.
            if iter_count >= map.len() {
                break;
            }
        }

        return None;
    }
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
    fn link(& mut self, o1: T, o2: T) -> & mut Self {
        let link1 = self.map.entry(o1.clone())
            .or_insert_with(|| Node::new_link(o1)).clone();
        let link2 = self.map.entry(o2.clone())
            .or_insert_with(|| Node::new_link(o2));
        Node::link(&link1, &link2);
        return self;
    }

    ///
    /// Add and/or link o1 and o2.  Returns self for fluent fun
    ///
    fn unlink(&self, o1: &T, o2: &T) -> & Self {
        let maybe_link1 = self.map.get(o1);
        let maybe_link2 = self.map.get(o2);
        if let Some(link1) = maybe_link1 {
            if let Some(link2) = maybe_link2 {
                Node::unlink(link1, link2);
            }
        }
        return self;
    }

    ///
    /// Remove the thing
    ///
    fn remove(& mut self, o: &T)  -> & mut Self {
        if let Some(link) = self.map.remove(o) {
            Node::unlink_all(&link);
        }
        return self;
    }

    ///
    /// Flattens the graph into a singly linked thing if possible
    ///
    fn flatten(&self) {
        for link in self.map.values() {
            let removables = link.borrow().get_removable_direct_links();
            for remove in removables {
                Node::unlink(link, &remove);
            }
        }
    }

    ///
    /// Gets a sorted iter
    ///
    fn sorted_iter(&self) -> SortedIter<T> {
        return SortedIter::new(&self.map);
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
            } else if node.is_tail() {
                tail_count += 1;
            }
            if !node.is_singly_linked() {
                return false;
            }
        }
        return head_count == 1 && tail_count == 1;
    }
}

macro_rules! hashdag_visit_impl {
    ($self:expr, $state:expr, $visitor:expr, $visit_call:ident) => {{
        for link in $self.map.values() {
            let node = link.borrow();
            if node.is_head() && node.$visit_call($state, $visitor) {
                return true;
            }
        }
        return false;
    }}
}
impl <T> Visitable<T> for HashDAG<T> where T: Clone + Hash + Eq {
    fn _visit_mut<V>(&self, state: &mut VisitState<T>, visitor: &mut V) -> bool
        where V: FnMut(&VisitState<T>) -> bool {
        hashdag_visit_impl!(self, state, visitor, _visit_mut);
    }

    fn _visit_ref<V>(&self, state: &mut VisitState<T>, visitor: &V) -> bool
        where V: Fn(&VisitState<T>) -> bool {
        hashdag_visit_impl!(self, state, visitor, _visit_ref);
    }

    fn _visit(&self, state: &mut VisitState<T>, visitor: fn(&VisitState<T>) -> bool) -> bool {
        hashdag_visit_impl!(self, state, visitor, _visit);
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::min;
    use std::iter::FromIterator;

    use crate::dag::{HashDAG, Visitable, VisitState};

    fn dag_printer(state: &VisitState<char>) -> bool {
        if state.tail {
            println!("{} >>", state.entry.unwrap());
        } else if state.head {
            print!("<< {}->", state.entry.unwrap());
        } else {
            print!("{}->", state.entry.unwrap());
        }
        return false;
    }

    #[test]
    fn test_stuff_2() {
        let mut dag: HashDAG<char> = HashDAG::new();
        dag.link('c', 'd')
            .link('a', 'd')
            .link('b', 'c')
            .link('a', 'b')
            .link('a', 'c')
            .link('a', 'b')
            .link('a', 'a')
            .link('c', 'f')
            .link('b', 'f')
            .link('f', 'd');

        println!("KAHN Sorted");
        for x in dag.sorted_iter() {
            print!("{}", x);
        }

        println!("\nKAHN Sorted without f");
        dag.remove(&'f');
        for x in dag.sorted_iter() {
            print!("{}", x);
        }

        println!("\nKAHN Sorted with internal cycle");
        dag.link('c', 'b');
        for x in dag.sorted_iter() {
            print!("{}", x);
        }

        println!("\nKAHN Sorted with external cycle");
        dag.link('d', 'a');
        for x in dag.sorted_iter() {
            print!("{}", x);
        }
    }

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

        assert_eq!(dag.is_singly_linked(), false);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(dag_printer);
        println!(" KAHN Sorted (non-destructive) ");
        for x in dag.sorted_iter() {
            print!("{}", x);
        }
        println!("\n");

        dag.flatten();
        assert_eq!(dag.is_singly_linked(), true);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(dag_printer);

        dag.link('a', 'x');
        dag.link('d', 'x');
        assert_eq!(dag.is_singly_linked(), false);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(dag_printer);

        dag.flatten();
        assert_eq!(dag.is_singly_linked(), true);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(dag_printer);

        dag.link('c', 'f');
        dag.link('f', 'd');
        assert_eq!(dag.is_singly_linked(), false);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(dag_printer);

        dag.flatten();
        assert_eq!(dag.is_singly_linked(), true);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(dag_printer);

        dag.link('x', 'd');
        assert_eq!(dag.is_singly_linked(), false);
        assert_eq!(dag.contains_cycle(), true);
        let cycles: Vec<String> = dag.get_cycles(false).iter()
            .map(String::from_iter)
            .collect();
        println!("{}", cycles.join("\n"));


        dag.unlink(&'x', &'d');
        assert_eq!(dag.is_singly_linked(), true);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(dag_printer);
    }

    #[test]
    fn test_alphabet_finder() {
        let words = vec![
            "baa".to_string(), "abcd".to_string(),
            "abca".to_string(), "cab".to_string(),
            "cad".to_string()
        ];
        let mut dag: HashDAG<char> = HashDAG::new();
        for (index, word) in words.iter().enumerate() {
            if index + 1 < words.len() {
                let next_word = &words[index + 1];
                let len = min(word.len(), next_word.len());
                for i in 0..len {
                    let word_c = word.chars().nth(i).unwrap();
                    let next_word_c = next_word.chars().nth(i).unwrap();
                    if word_c != next_word_c {
                        dag.link(word_c, next_word_c);
                        break;
                    }
                }
            }
        }

        assert_eq!(dag.is_singly_linked(), false);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(dag_printer);

        dag.flatten();
        assert_eq!(dag.is_singly_linked(), true);
        assert_eq!(dag.contains_cycle(), false);
        dag.visit(dag_printer);
    }
}