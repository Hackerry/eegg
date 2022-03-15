import argparse
from egraph import EGraph

def parse_args():
    parser = argparse.ArgumentParser()


# single distributive law
def testcase1():
    return "4*3+4*2", [("x*y+x*z", "x*(y+z)")]

# communitive and distributive
def testcase2():
    return "3*4+2*4", [("x*y+x*z", "x*(y+z)"), ("x * y", "y * x")]


def main():
    expr, rules = testcase2()
    egraph = EGraph()
    # egraph.init_graph("3+4")
    # egraph.init_graph("3+0")
    # egraph.init_graph("(3+3)+(3+3)")
    # egraph.init_graph("3*4+2*4")
    egraph.init_graph(expr)
    # egraph.init_graph("'x'*2/2")
    egraph.print_eclass_map()
    print("egraph top_class id ", egraph.top_level_eclass_id)
    # print(egraph.hashcons)

    # rules = [("x*y+x*z", "x*(y+z)"), ("x+y", "y+x")]
    # rules = [("x*y+x*z", "x*(y+z)")] # this is working
    # rules = [("y", "y*1")]
    egraph.eq_sat(rules, iteration_limit=5)

    print()
    print("Final classes:")
    egraph.print_eclass_map()
    print("egraph top_class id ", egraph.top_level_eclass_id)

    print()
    print("Min AST Expr:", egraph.find_min_ast())

if __name__ == "__main__":
    main()
