from codecs import lookup_error
from typing import Dict, Set, Tuple, List
from unionfind import UnionFind
import ast

MAX_ECLASS_SIZE = 1000
MAX_COST = 1e10

class ENode:
    def __init__(self, op):
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
    def __init__(self, id):
        self.id: int = id
        self.enodes: List[ENode] = []
        self.parents: Dict[ENode, int] = {}

    def add_enode(self, enode:ENode):
        self.enodes.append(enode)
        enode.class_id = self.id

    # Pretty print
    def __str__(self):
        return "{EClass-%s: %s}" % (self.id, str(self.enodes))
    def __repr__(self):
        return "{EClass-%s: %s}" % (self.id, str(self.enodes))

class EGraph:
    def __init__(self):
        self.union_find = UnionFind(MAX_ECLASS_SIZE)
        self.eclass_map: Dict[int, EClass] = {}
        self.hashcons: Dict[int, int] = {}
        self.eclass_id_counter = 0
        self.worklists: List[int] = []
        self.saturated: bool = False
        self.top_level_eclass_id = -1

    def init_graph(self, expr):
        tnode = ast.parse(expr, mode='eval')
        # print(ast.dump(tnode.body))
        self.generate_enodes_from_ast(tnode.body, with_class=True, top_level=True)

    def canonicalize(self, enode: ENode):
        new_children = [self.union_find.find(e) for e in enode.children]
        enode.children = new_children

    def ematch(self, lhs_node:ENode):
        # Store matchings
        matches = []

        # Find matches for current rule
        for class_id in self.eclass_map.keys():
            eclass = self.eclass_map[class_id]

            variables = {}
            if self.ematch_helper(eclass, lhs_node, variables):
                print("Found matching:", eclass, "with variables", variables, "lhs being", lhs_node)
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
                elif variables[pnode.op] != enode.class_id:
                    # A variable is filled with 2 distinct value, report inconsistency
                    return False
            # This is a literal and ops don't match
            elif pnode.op != enode.op: return False

            # Recurse on children
            if not pnode.is_variable and len(pnode.children) != len(enode.children):
                return False
            for i in range(len(pnode.children)):
                if not self.ematch_helper(self.eclass_map[enode.children[i]], pnode.children[i], variables):
                    # Children don't match
                    return False

            # Children match
            return True

    def add(self, rhs_node:ENode, matches:List[Tuple[int, Dict[str, int]]]):
        # Id pairs to merge
        merge_ids = []

        # Find matchings for the rewrite
        for (eclass_id, variables) in matches:
            # Generate new eclass for this matching
            new_eclass = self.add_helper(rhs_node, variables)

            # print("Generated eclass:", new_eclass)
            # print("Now classes:")
            # self.print_eclass_map()

            # Record merge ids
            merge_ids.append((eclass_id, new_eclass))

        print("Merge ids:", merge_ids)
        return merge_ids

    def add_helper(self, pnode:ENode, variables:Dict[str, int]):
        # This is a variable, reuse enode
        if pnode.is_variable:
            # Load stored variable and update parent pointer
            return variables[pnode.op]

        # This is a concret symbol, create new class
        enode = ENode(pnode.op)

        # Get children enodes and update parent pointers
        children = []
        for child in pnode.children:
            class_id = self.add_helper(child, variables)
            children.append(class_id)
        enode.children.extend(children)

        # Check hashing
        self.canonicalize(enode)
        hash = enode.hash()
        if hash in self.hashcons:
            # Duplicate
            eclass = self.hashcons[hash]
            return eclass

        eclass = self.eclass_map[self.new_singleton_eclass(enode)]

        # Update new node's parent and children pointers
        for child_class_id in children:
            self.eclass_map[child_class_id].parents[enode] = eclass.id

        # Generate hash for new enode
        self.canonicalize(enode)
        self.store_hash(enode)

        return eclass.id

    def eq_sat(self, rules:List[Tuple[str, str]], iteration_limit = 1):
        cur_iter = 0
        print("Rewrite rules:", rules)
        while not self.saturated and cur_iter < iteration_limit:
            # Store matched enodes
            matches = []

            self.saturated = True

            # Read possible rewrite-change locations
            for rule in rules:
                # Pre-processing the right hand expr
                lhs = ast.parse(rule[0], mode='eval').body
                # print("AST: %s => %s" % (ast.dump(lhs), ast.dump(rhs)))
                lhs_node = self.generate_enodes_from_ast(lhs, with_class=False)
                # print("Dummy Enodes: %s => %s" % (lhs_node, rhs_node))

                # First, find all matching enodes to the rewrite rule
                matches.append(self.ematch(lhs_node))

            print("Rewrite rule matches:", matches)

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
                print("Merge class pairs:", class_pairs)
                self.print_eclass_map()

                for (class1, class2) in class_pairs:
                    # Merge class pairs
                    self.merge(class1, class2)

                    self.print_eclass_map()

                    # Rebuild and restore invariants
                    self.rebuild()

                # print(self.union_find)

            cur_iter += 1

        print("Finish in %s iterations" % cur_iter)

    def merge(self, class1, class2):
        id1 = self.union_find.find(class1)
        id2 = self.union_find.find(class2)
        if id1 == id2:
            return id1

        # Not saturated
        self.saturated = False

        # Union two nodes in the structure
        new_id = self.union_find.union(id1, id2)
        self.worklists.append(new_id)

        # Actually union two classes
        if new_id == id1: other_id = id2
        else: other_id = id1

        # Merge nodes and parents, delete old class
        self.eclass_map[new_id].enodes.extend(self.eclass_map[other_id].enodes)
        self.eclass_map[new_id].parents.update(self.eclass_map[other_id].parents)
        del self.eclass_map[other_id]
        if other_id == self.top_level_eclass_id:
            self.top_level_eclass_id = new_id
        print("Delete class:", other_id, "used:", new_id)

        return new_id

    def rebuild(self):
        print("Work list:", self.worklists)
        while len(self.worklists) > 0:
            # Find all class ids affected by this merge
            classes = [self.union_find.find(eclass) for eclass in self.worklists]
            self.worklists = []
            for eclass in classes:
                self.repair(eclass)

    def repair(self, eclass_id: int):
        eclass = self.eclass_map[eclass_id]

        for (p_node, p_eclass) in eclass.parents.items():
            # Remove old hashing and store new hashing
            del self.hashcons[p_node.hash()]
            self.canonicalize(p_node)
            new_hash = p_node.hash()
            print(p_node)
            self.hashcons[new_hash] = self.union_find.find(p_eclass)

        new_parents: Dict[ENode, int] = {}
        for (p_node, p_eclass) in eclass.parents.items():
            self.canonicalize(p_node)

            # Duplicate parents, merge
            if p_node in new_parents:
                self.merge(p_eclass, new_parents[p_node])

                # self.saturated = False

            new_parents[p_node] = self.union_find.find(p_eclass)
        # Update new parents
        eclass.parents = new_parents

    # Parse an ast to enode structure
    # with_class is enabled when constructing the egraph
    #               disabled when generating egraph-like structure for ematch
    def generate_enodes_from_ast(self, tnode, with_class=False, top_level=False):
        # print("Generate node dump:", ast.dump(tnode))

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
                    return self.eclass_map[self.hashcons[hash]]

                # Generate class and hash
                eclass = self.eclass_map[self.new_singleton_eclass(enode)]
                self.store_hash(enode)
                # print("Create new eclass:", eclass)
                if top_level:
                    self.top_level_eclass_id = eclass.id
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
                # print("L:", left, "R:", right)
                enode.children.append(left.id)
                enode.children.append(right.id)

                # Compute hash for duplicates
                hash = enode.hash()
                if hash in self.hashcons:
                    return self.eclass_map[self.hashcons[hash]]

                eclass = self.eclass_map[self.new_singleton_eclass(enode)]

                # Register parents and children
                left.parents[enode] = eclass.id
                right.parents[enode] = eclass.id

                # Generate hashcons for each enode
                self.store_hash(enode)
                if top_level:
                    self.top_level_eclass_id = eclass.id
                # print("Return:", eclass)
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

    def store_hash(self, enode:ENode):
        hash = enode.hash()
        if hash in self.hashcons:
            print("Warning: hash %s already present of %s" % (hash, enode))
        self.hashcons[hash] = enode.class_id

    def print_eclass_map(self):
        print("printing eclass map")
        for i in self.eclass_map:
            print("%s: %s" % (i, self.eclass_map[i]))

    def find_min_ast(self):
        top_eclass = self.eclass_map[self.top_level_eclass_id]
        cost, expr = self.find_min_ast_eclass(top_eclass)
        return cost, expr

    def find_min_ast_eclass(self, eclass: EClass):
        costs = []
        exprs = []
        for enode in eclass.enodes:
            cost, expr = self.find_min_ast_enode(enode)
            costs.append(cost)
            exprs.append(expr)
        min_cost = MAX_COST
        idx = -1
        for i in range(len(costs)):
            if costs[i] < min_cost:
                min_cost = costs[i]
                idx = i
        return costs[idx], exprs[idx]

    def find_min_ast_enode(self, enode: ENode):
        if enode.is_variable:
            return (1, enode.op)
        if len(enode.children) > 1:
            assert(len(enode.children) == 2)
            lhs_cost, lhs_expr = self.find_min_ast_eclass(self.eclass_map[enode.children[0]])
            rhs_cost, rhs_expr = self.find_min_ast_eclass(self.eclass_map[enode.children[1]])
            return 1 + lhs_cost + rhs_cost, f"({enode.op} {lhs_expr} {rhs_expr})"
        else:
            return (1, enode.op)