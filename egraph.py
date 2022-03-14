from codecs import lookup_error
from typing import Dict, Set, Tuple, List
from unionfind import UnionFind

MAX_ECLASS_SIZE = 10000

class ENode:
    id_counter = 0
    # TODO: add type
    def __init__(self, token) -> None:
        self.id = ENode.id_counter
        ENode.id_counter += 1
        self.class_id = -1
        self.token = token


class EClass:
    def __init__(self, id) -> None:
        self.id: int = id
        self.nodes: List[ENode] = []
        self.parents: List[Tuple[ENode, int]] = []

    def add_enode(self, node):
        self.nodes.append(node)

class EGraph:
    def __init__(self) -> None:
        self.union_find = UnionFind(MAX_ECLASS_SIZE)
        self.eclass_map: Dict[int, EClass] = {}
        self.hashcons: Dict[int, int] = {}
        self.eclass_id_counter = 0

    def find(self, id: int) -> int:
        return self.union_find.find(id)

    def lookup_enode(self, id: int) -> int:
        if id in self.hashcons:
            return self.hashcons[id]
        else:
            return -1

    def add(self, node: ENode) -> int:
        lookup_result = self.lookup_enode(node.id)
        if lookup_result != -1:
            return lookup_result
        else:
            eclass_id = self.eclass_id_counter
            self.eclass_id_counter += 1
            self.hashcons[node.id] = eclass_id
            eclass = EClass(eclass_id)
            eclass.add_enode(node)
            self.eclass_map[eclass_id] = eclass
            return eclass_id

    def union(self, eclass_id1: int, eclass_id2: int):
        pass
        # self.union_find.union(id_a, id_b)

    def ematch(self):
        pass

