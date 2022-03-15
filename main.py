import argparse
from egraph import EGraph

def parse_args():
    parser = argparse.ArgumentParser()


def main():
    egraph = EGraph()
    # egraph.init_graph("3+4")
    # egraph.init_graph("3+0")
    # egraph.init_graph("(3+3)+(3+3)")
    egraph.init_graph("3*4+2*4")
    # egraph.init_graph("'x'*2/2")
    egraph.print_eclass_map()
    # print(egraph.hashcons)

    rules = [("x*y+x*z", "x*(y+z)"), ("x+y", "y+x")]
    # rules = [("y", "y*1")]
    egraph.eq_sat(rules, iteration_limit=2)

    print()
    print("Final classes:")
    egraph.print_eclass_map()

    print()
    print("Min AST Expr:", egraph.find_min_ast())

if __name__ == "__main__":
    main()
