from codecs import lookup_error
from typing import Dict, Set, Tuple, List
from unionfind import UnionFind

MAX_ECLASS_SIZE = 10000

class ENode:
    def __init__(self, op, children = []) -> None:
        self.class_id = -1
        self.op = op
        self.children: List[int] = children


class EClass:
    def __init__(self, id) -> None:
        self.id: int = id
        self.enodes: List[ENode] = []
        self.parents: Dict[ENode, int] = {}

    def add_enode(self, enode):
        self.enodes.append(enode)

class EGraph:
    def __init__(self) -> None:
        self.union_find = UnionFind(MAX_ECLASS_SIZE)
        self.eclass_map: Dict[int, EClass] = {}
        self.hashcons: Dict[ENode, int] = {}
        self.eclass_id_counter = 0
        self.worklists: List[int] = []

    def find(self, id: int) -> int:
        return self.union_find.find(id)

    def lookup_enode(self, enode) -> int:
        if enode in self.hashcons:
            return self.hashcons[enode]
        else:
            return -1

    def add(self, enode: ENode) -> int:
        enode = self.canonicalize(enode)
        lookup_result = self.lookup_enode(enode)
        if lookup_result != -1:
            return lookup_result
        else:
            eclass_id = self.new_singleton_eclass(enode)
            # TODO: update children's parents is missing
            self.hashcons[enode] = eclass_id
            return eclass_id

    def canonicalize(self, enode: ENode):
        new_children = [self.find(e) for e in enode.children]
        return self.make_enode(enode.op, new_children)

    def union(self, eclass_id1: int, eclass_id2: int):
        if self.find(eclass_id1) == self.find(eclass_id2):
            return self.find(eclass_id1)
        self.union_find.union(eclass_id1, eclass_id2)
        new_id = self.union_find.find(eclass_id1)
        self.worklists.append(new_id)
        return new_id

    def ematch(self):
        pass

    def make_enode(self, op, children):
        enode = ENode(op, children)
        return enode

    def new_singleton_eclass(self, enode):
        new_eclass_id = self.eclass_id_counter
        self.eclass_id_counter += 1
        eclass = EClass(new_eclass_id)
        eclass.add_enode(enode)
        self.eclass_map[new_eclass_id] = eclass
        return new_eclass_id

    def rebuild(self):
        while len(self.worklists) > 0:
            todo = self.worklists
            self.worklists.clear()
            todo = {self.find(eclass) for eclass in todo}
            for eclass in todo:
                self.repair(eclass)

    def repair(self, eclass_id: int):
        eclass = self.eclass_map[eclass_id]
        for (p_node, p_eclass) in eclass.parents.items():
            del self.hashcons[p_node]
            p_node = self.canonicalize(p_node)
            self.hashcons[p_node] = self.find(p_eclass)

        new_parents: Dict[ENode, int] = {}
        for (p_node, p_eclass) in eclass.parents.items():
            p_node = self.canonicalize(p_node)
            if p_node in new_parents:
                self.union(p_eclass, new_parents[p_node])
            new_parents[p_node] = self.find(p_eclass)
        eclass.parents = new_parents
