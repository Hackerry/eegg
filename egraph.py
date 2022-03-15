from codecs import lookup_error
from typing import Dict, Set, Tuple, List
from unionfind import UnionFind
import ast

MAX_ECLASS_SIZE = 10000

class ENode:
    def __init__(self, op) -> None:
        self.class_id = -1
        self.op = op
        self.children: List[int] = []
        self.is_variable = False
        
    def get_hashable_string(self):
        return self.op + str(self.children)
    
    def hash(self):
        # print("Hash of:", self.get_hashable_string(), hash(self.get_hashable_string()))
        return hash(self.get_hashable_string())
    
    # Pretty print
    def __str__(self):
        # return "ENode(%s:%s)" % (self.class_id, self.op)
        return "ENode(%s%s)" % (self.op, self.children)
    def __repr__(self):
        # return "ENode(%s:%s)" % (self.class_id, self.op)
        return "ENode(%s%s)" % (self.op, self.children)

class EClass:
    def __init__(self, id) -> None:
        self.id: int = id
        self.enodes: List[ENode] = []
        self.parents: List[ENode, int] = []

    def add_enode(self, enode:ENode):
        self.enodes.append(enode)
        enode.class_id = self.id
    
    # Pretty print
    def __str__(self):
        return "{EClass-%s: %s}" % (self.id, str(self.enodes))
    def __repr__(self):
        return "{EClass-%s: %s}" % (self.id, str(self.enodes))

class EGraph:
    def __init__(self) -> None:
        self.union_find = UnionFind(MAX_ECLASS_SIZE)
        self.eclass_map: Dict[int, EClass] = {}
        self.hashcons: Dict[int, ENode] = {}
        self.eclass_id_counter = 0
        self.worklists: List[int] = []
        self.saturated: bool = False
    
    def init_graph(self, expr):
        tnode = ast.parse(expr, mode='eval')
        # print(ast.dump(tnode.body))
        self.generate_enodes_from_ast(tnode.body, with_class=True)

    def find(self, id: int) -> int:
        return self.union_find.find(id)

    # def add(self, enode: ENode) -> int:
    #     enode = self.canonicalize(enode)
    #     if enode in self.hashcons:
    #         return 
    #     else:
    #         eclass_id = self.new_singleton_eclass(enode)
    #         for child in enode.children:
    #             child_eclass = self.eclass_map[child]
    #             child_eclass.parents[enode] = eclass_id
    #         self.hashcons[enode] = eclass_id
    #         return eclass_id

    def canonicalize(self, enode: ENode):
        new_children = [self.find(e) for e in enode.children]
        return ENode(enode.op, new_children)

    def union(self, eclass_id1: int, eclass_id2: int):
        if self.find(eclass_id1) == self.find(eclass_id2):
            return self.find(eclass_id1)
        self.union_find.union(eclass_id1, eclass_id2)
        new_id = self.union_find.find(eclass_id1)
        self.worklists.append(new_id)
        return new_id

    def ematch(self, lhs_node:ENode) -> List[Tuple[int, Dict[str, int]]]:
        # Store matchings
        matches = []
        
        # Find matches for current rule
        for class_id in self.eclass_map.keys():
            eclass = self.eclass_map[class_id]
            
            variables = {}
            if self.ematch_helper(eclass, lhs_node, variables):
                print("Found matching:", eclass, "with variables", variables)
                matches.append((eclass.id, variables))
        
        return matches
                
    def ematch_helper(self, eclass:EClass, pnode:ENode, variables:Dict[str, int]):
        # print("eclass:", eclass, "pnode:", pnode, variables)
        
        # Find enodes that match the expression with variables holes
        for enode in eclass.enodes:
            # This is a variable hole
            if pnode.is_variable:
                # print("Consider setting variable", pnode.op, "as", enode)
                if pnode.op not in variables:
                    # Record variable hole as filled
                    variables[pnode.op] = enode.class_id
                elif variables[pnode.op] != enode:
                    # A variable is filled with 2 distinct value, report inconsistency
                    return False
            # This is a literal and ops don't match
            elif pnode.op != enode.op: return False
            
            # Recurse on children
            if not pnode.is_variable and len(pnode.children) != len(enode.children):
                return False
            for i in range(len(pnode.children)):
                if not self.ematch_helper_match(self.eclass_map[enode.children[i]], pnode.children[i], variables):
                    # Children don't match
                    return False
            
            # Children match
            return True

    def add(self, rhs_node:ENode, matches:List[Tuple[int, Dict[str, int]]]):
        # Id pairs to merge
        merge_ids = []
        
        # Apply rewrites to matched portions
        for (eclass_id, variables) in matches:
            # Generate new eclass for this matching
            new_eclass = self.add_helper(rhs_node, None, variables)
            print("Generated eclass:", new_eclass)
            print("New classes:")
            self.print_eclass_map()
            
            # Record merge ids
            merge_ids.append((eclass_id, new_eclass))
        
        return merge_ids
    
    def add_helper(self, pnode:ENode, parent:ENode, variables:Dict[str, ENode]):
        print("pnode:", pnode)
        
        # This is a variable, reuse enode
        if pnode.is_variable:
            # Load stored variable and update parent pointer
            enode = variables[pnode.op]
            if parent != None and parent not in self.eclass_map[enode.class_id].parents:
                self.eclass_map[enode.class_id].parents.append(parent)
            return enode.class_id
        
        # This is a concret symbol, create new class
        enode = ENode(pnode.op)
        eclass = self.eclass_map[self.new_singleton_eclass(enode)]
        
        # Get children enodes and update parent pointers
        children = []
        for child in pnode.children:
            class_id = self.ematch_helper_generate(child, enode, variables)
            children.append(class_id)
        
        # Update new node's parent and children pointers
        enode.children.extend(children)
        if parent != None:
            eclass.parents.append(parent)
        
        # Generate hash for new enode
        self.store_hash(enode)
        
        return eclass.id
    
    def eq_sat(self, rules:List[Tuple[str, str]], iteration_limit = 1):
        cur_iter = 0
        print("Rewrite rules:", rules)
        while not self.saturated and cur_iter < iteration_limit:
            # Store matched enodes
            matches = []
            
            # Read possible rewrite-change locations
            for rule in rules:
                # Pre-processing the right hand expr
                lhs = ast.parse(rule[0], mode='eval').body
                # print("AST: %s => %s" % (ast.dump(lhs), ast.dump(rhs)))
                lhs_node = self.generate_enodes_from_ast(lhs, with_class=False)
                # print("Dummy Enodes: %s => %s" % (lhs_node, rhs_node))
                
                # First, find all matching enodes to the rewrite rule
                matches.append(self.ematch(lhs_node))
            
            # Check length match
            assert len(matches) == len(rules)
            
            # Apply rewrites
            for i in range(len(rules)):
                # Pre-processing the left hand expr
                rhs = ast.parse(rules[i][1], mode='eval').body
                # print("AST: %s => %s" % (ast.dump(lhs), ast.dump(rhs)))
                rhs_node = self.generate_enodes_from_ast(rhs, with_class=False)
                # print("Dummy Enodes: %s => %s" % (lhs_node, rhs_node))
                
                # Then apply all rewrites
                class_pairs = self.add(rhs_node, matches[i])
                
                # Merge class pairs
                self.merge(class_pairs)
            
            cur_iter += 1
    
    # Parse an ast to enode structure
    # with_class is enabled when constructing the egraph
    #               disabled when generating egraph-like structure for ematch
    def generate_enodes_from_ast(self, tnode, with_class=False):
        # Name is variable hole
        if isinstance(tnode, ast.Name):
            enode = ENode(str(tnode.id))
            enode.is_variable = True
            return enode
        elif isinstance(tnode, ast.Constant):
            enode = ENode(str(tnode.value))
            
            # Generate class
            if with_class:
                # Check hash for potential duplicates
                hash = enode.hash()
                if hash in self.hashcons:
                    return self.eclass_map[self.hashcons[hash].class_id]
                
                # Generate class and hash
                eclass = self.eclass_map[self.new_singleton_eclass(enode)]
                self.store_hash(enode)
                # print("Create new eclass:", eclass)
                return eclass
            else:
                return enode
        elif isinstance(tnode, ast.BinOp):
            left = self.generate_enodes_from_ast(tnode.left, with_class)
            right = self.generate_enodes_from_ast(tnode.right, with_class)
            # print("Left:", left, "Right:", right)
            
            # Create parent node and class
            if isinstance(tnode.op, ast.Add): op = "+"
            elif isinstance(tnode.op, ast.Sub): op = "-"
            elif isinstance(tnode.op, ast.Mult): op = "*"
            elif isinstance(tnode.op, ast.Div): op = "/"
            else:
                op = ' '
                print("Invalid op:", ast.dump(tnode))
            
            enode = ENode(op)
            if with_class:
                # Assemble enode
                enode.children.append(left.id)
                enode.children.append(right.id)
                
                # Compute hash for duplicates
                hash = enode.hash()
                if hash in self.hashcons:
                    return self.eclass_map[self.hashcons[hash].class_id]
                
                eclass = self.eclass_map[self.new_singleton_eclass(enode)]
            
                # Register parents and children
                left.parents.append(enode)
                right.parents.append(enode)
                
                # Generate hashcons for each enode
                self.store_hash(enode)
                return eclass
            else:
                enode.children.append(left)
                enode.children.append(right)
                return enode
        else:
            print("Error parsing node:", ast.dump(tnode))
            return None

    def new_singleton_eclass(self, enode):
        # Update enode class id
        new_eclass_id = self.eclass_id_counter
        
        # Update class id counter
        self.eclass_id_counter += 1
        
        # Create new singleton and add to eclass map
        eclass = EClass(new_eclass_id)
        eclass.add_enode(enode)
        self.eclass_map[new_eclass_id] = eclass
        
        return new_eclass_id

    def store_hash(self, enode):
        hash = enode.hash()
        if hash in self.hashcons:
            print("Warning: hash %s already present of %s" % (hash, enode))
        self.hashcons[hash] = enode

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
    
    def print_eclass_map(self):
        for i in self.eclass_map:
            print("%s: %s" % (i, self.eclass_map[i]))

egraph = EGraph()
# egraph.init_graph("3*4+3*6")
egraph.init_graph("3*1+3*2")
egraph.print_eclass_map()
# print(egraph.hashcons)

# node = ast.parse("x+'y'", mode='eval')
# print(ast.dump(node.body))
# enode = egraph.generate_enodes_from_ast(node.body)
# print(enode)
rules = [("x*1+x*z", "x*(1+z)")]
# rules = [("3*5+2*5", "5*(2+3)")]
egraph.apply_rules_to_egraph(rules)

