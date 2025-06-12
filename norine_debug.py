"""
    Script for checking encoding for bugs. We filter isomorphic copies using different tools and check whether numbers coincide.
"""

import itertools
import argparse
import math
import random

from pysat.formula import *
from pysat.solvers import Solver
from pysat.card import CardEnc


def lex_smaller_eq(enc, vpool, seq1, seq2, maxcomparisons=None):
        """Ensure that seq1 is lexicographically smaller or equal than seq2"""
        assert len(seq1) == len(seq2)
        all_previous_equal = vpool.id()
        enc.append([+all_previous_equal])
        prefix_length = len(seq1)
        if maxcomparisons is not None:
            prefix_length = maxcomparisons
        rcnt = 0
        for i in range(len(seq1)):
            if seq1[i] == seq2[i]: continue
            rcnt += 1
            enc.append([-all_previous_equal, -seq1[i], +seq2[i]])  # all previous equal implies seq1[i] <= seq2[i]
            all_previous_equal_new = vpool.id()
            enc.append([-all_previous_equal, -seq1[i], +all_previous_equal_new])
            enc.append([-all_previous_equal, +seq2[i], +all_previous_equal_new])
            all_previous_equal = all_previous_equal_new
            if maxcomparisons is not None and rcnt > maxcomparisons:
                break
        return enc

def anti(v):
    return tuple((1 - x) for x in v)

def flip_i(v, i):
    return tuple((1 - x) if j == i else x for j, x in enumerate(v))
        
def swap(i, j, v):
    u = list(v)
    u[i], u[j] = u[j], u[i]
    return tuple(u)
    
def encode(n, sum_upper_bound, fprime=False, deg_constraint=None):
    """
    Encoding from Section 6 of the Overleaf
    """
    enc = CNF()

    vpool = IDPool(start_from=1)
    vertices = list(itertools.product([0, 1], repeat=n))
    graph = {}
    for v in vertices:
        graph[v] = set()
        for i in range(n):
            neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
            graph[v].add(tuple(neighbor))
            
    for v in vertices:
        assert len(graph[v]) == n, f"Graph is not a hypercube: {v} has {len(graph[v])} neighbors"
    

    r = lambda u, v: vpool.id(f"r_{min(u,v), max(u, v)}")

    var_to_edge = dict()

    # add dummy clauses to ensure that the variables are created
    for u in vertices:
        for v in graph[u]:
            var_to_edge[r(u, v)] = (u, v)
            enc.append([r(u, v), -r(u, v)])

    colors = ['red', 'blue']




    pc = lambda color, u, v, s: vpool.id(f"p^{color}_{u, v, s}")

    pt = lambda u, s : vpool.id(f"p^t_{u, s}")


    def dist(u, v):
        return sum(1 for i in range(len(u)) if u[i] != v[i])
        # return sum(u[i] != v[i] for i in range(len(u)))

            

    # Eq 4, 5:
    for u in vertices:
        if u > anti(u): continue
        for v in graph[u]:
            enc.append([-r(u, v), pc('red', u, v, 0)])
            enc.append([r(u, v), pc('blue', u, v, 0)])


    # Eq 6, 7, 8, 9
    for u in vertices:
        if u > anti(u): continue
        for w in vertices:
            if w in graph[u]: continue
            for v in graph[w]:
                if dist(u, v) + 1 == dist(u, w):
                    for s in range(n):
                        # Eq 6.
                        enc.append([-pc('red', u, v, s), -r(v, w), pc('red', u, w, s)])
                        # Eq 7.
                        enc.append([-pc('blue', u, v, s), r(v, w), pc('blue', u, w, s)])

                        if s < n-1:
                            # Eq 8.
                            enc.append([-pc('red', u, v, s), r(v, w), pc('blue', u, w, s+1)])
                            
                            # Eq 9.
                            enc.append([-pc('blue', u, v, s), -r(v, w), pc('red', u, w, s+1)])

    # Eq 10.
    for u in vertices:
        if u > anti(u): continue
        for v in vertices:
            if u == v: continue
            for color in colors:
                for s in range(n-1):
                    enc.append([-pc(color, u, v, s), pc(color, u, v, s+1)])


    # Eq 11.
    for u in vertices:
        if u > anti(u): continue
        for s in range(n):
            # enc.add_var(f"p^t_{u, s}")
            for color in colors:
                enc.append([-pc('red', u, anti(u), s), pt(u, s)])
                enc.append([-pc('blue', u, anti(u), s), pt(u, s)])

    if fprime:
        for u in vertices:
            if u > anti(u): continue
            # enc.add_var(f"p^t_{u, -1}")
            for s in range(n):
                enc.append([-pc('red', u, anti(u), s), -pc('blue', u, anti(u), s), pt(u, s-1)])



    # Eq 12.
    if not fprime:
        sum_vars = []
        for u in vertices:
            if u < anti(u):
                for s in range(n):
                    sum_vars.append(-pt(u, s))

        enc.extend(CardEnc.atleast(sum_vars, bound=sum_upper_bound, vpool=vpool, encoding=7))
        # enc.at_least_k(sum_vars, sum_upper_bound)
    else:
        sum_vars = []
        for u in vertices:
            if u < anti(u):
                for s in range(-1, n):
                    sum_vars.append(-pt(u, s))
        enc.extend(CardEnc.atleast(sum_vars, bound=sum_upper_bound + (len(vertices) // 2), vpool=vpool, encoding=7))
        # enc.at_least_k(sum_vars, sum_upper_bound + (len(vertices) // 2))
    


    print(f"number of clauses: {len(enc.clauses)}")
            
    ## Symmetry breaking
    MAX_COMPARISONS = 60

    # cls_pre_sb = enc.n_clauses()
    original_signed_edges = [(1, (u, v)) for u in vertices for v in graph[u] if u < v]
    for i in range(n):
        permuted_edges = [(s, (flip_i(u, i), flip_i(v, i))) for s, (u, v) in original_signed_edges]
        enc = lex_smaller_eq(enc, vpool, [s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges])
      
    for i, j in itertools.combinations(range(n), 2):
        permuted_edges = [(s, (swap(i, j, u), swap(i, j, v))) for s, (u, v) in original_signed_edges]
        enc = lex_smaller_eq(enc, vpool, [s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges], maxcomparisons=MAX_COMPARISONS)
        
    for (i, j) in itertools.combinations(range(n), 2):
        for k in range(n):
            permuted_edges = [(s, (swap(i, j, flip_i(u, k)), swap(i, j, flip_i(v, k)))) for s, (u, v) in original_signed_edges]
            enc = lex_smaller_eq(enc, vpool, [s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges], maxcomparisons=MAX_COMPARISONS)

    for P in itertools.permutations(range(n)):
        for flip_dimensions in itertools.product([0, 1], repeat=n):
            def permute_and_flip(v):
                # print(f"Permuting {v} with {P} and flipping {flip_dimensions}")
                return tuple((v[P[i]] if flip_dimensions[i] == 0 else 1 - v[P[i]] for i in range(n)))
            permuted_edges = [(s, (permute_and_flip(u), permute_and_flip(v))) for s, (u, v) in original_signed_edges]
            enc = lex_smaller_eq(enc, vpool, [s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges], maxcomparisons=MAX_COMPARISONS)

            # enc.lex_less_equal([s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges], max_comparisons=MAX_COMPARISONS)
    # print(f"Added {enc.n_clauses() - cls_pre_sb} symmetry breaking clauses")

    print(f"number of clauses: {len(enc.clauses)}")


    return enc, var_to_edge



def checkLexMin(red_edges, n, plusNegated=False):
    """
        Checks whether minimal
    """

    vertices = list(itertools.product([0, 1], repeat=n))
    graph = {}
    for v in vertices:
        graph[v] = set()
        for i in range(n):
            neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
            graph[v].add(tuple(neighbor))

    original_edges = [(u, v) for u in vertices for v in graph[u] if u < v]

    def edges_to_sequence(red_edges):
        return [1 if (u, v) in red_edges or (v,u) in red_edges else 0 for u, v in original_edges]

    original_edges_seq = edges_to_sequence(red_edges)


    for perm_dimensions in itertools.permutations(range(n)):
        for flip_dimensions in itertools.product([0, 1], repeat=n):

            def permute_and_flip(v):
                # print(f"Permuting {v} with {perm_dimensions} and flipping {flip_dimensions}")
                return tuple((v[perm_dimensions[i]] if flip_dimensions[i] == 0 else 1 - v[perm_dimensions[i]] for i in range(n)))
            
            permuted_edges = [(permute_and_flip(u), permute_and_flip(v)) for u,v in red_edges]
            permuted_edges_seq = edges_to_sequence(permuted_edges)


            if permuted_edges_seq < original_edges_seq:
                return False
            
            if plusNegated:
                if (not permuted_edges_seq) < original_edges_seq:
                    return False
    return True


def graph6(red_edges, n):
    import networkx as nx
    g = nx.Graph()


    vertices = list(itertools.product([0, 1], repeat=n))
    graph = {}
    for v in vertices:
        graph[v] = set()
        for i in range(n):
            neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
            graph[v].add(tuple(neighbor))

    c = 0
    for u in vertices:
        for v in graph[u]:
            if u < v:
                if (u, v) in red_edges or (v, u) in red_edges:
                    g.add_edge(u, v,)
                else:
                    g.add_edge(u, f"c{c}")
                    g.add_edge(v, f"c{c}")
                    c += 1
    return nx.to_graph6_bytes(g, header=False).decode('utf-8').strip()


import os 

if __name__ == "__main__":         
    argparser = argparse.ArgumentParser(description="Norine's conjecture")
    argparser.add_argument("-n", type=int, help="Order of the hypercube graph", required=True)
    argparser.add_argument("-b", type=int, help="Upper bound ", required=True)
    args = argparser.parse_args()
    N = args.n


    encoding, var_to_edge = encode(N, args.b, None, None)

    encoding.to_file(f"norine_switches_pysat_{N}_{args.b}.cnf")
    exit()


    # create solver and enumerate all solutions

    solver = Solver()
    for clause in encoding:
        solver.add_clause(clause)
    r = True

    num_edge_vars = 2 ** (N - 1) * N

    num_models = 0
    num_minimal_models = 0

    solutions = []


    path_for_graphs = f"graphs_{N}.g6"
    path_for_filtered_graphs = f"graphs_filtered_{N}.g6"

    os.remove(path_for_graphs) if os.path.exists(path_for_graphs) else None

    print("Start solving...")
    while r:
        r = solver.solve()
        # print("Result:", r)

        if r:
            num_models += 1
            model = solver.get_model()
            # print("Model:", model)

            # print red edges
            red_edges = [var_to_edge[abs(lit)] for lit in model[:num_edge_vars] if lit > 0]
            # print("Red edges:", red_edges)

            # print("Model number:", num_models)

            if checkLexMin(red_edges, N):
                num_minimal_models += 1
            
            print("Number of edges:", len(red_edges))

            with open(path_for_graphs, 'a') as f:
                f.write(graph6(red_edges, N) + '\n')


            solutions.append(red_edges)

            # block model on edge variables
            solver.add_clause([-model[i] for i in range(num_edge_vars)])

            if num_models == 10:
                break

    print(f"Number of models: {num_models}")
    print(f"Number of minimal models: {num_minimal_models}")

    os.system(f"shortg {path_for_graphs} {path_for_filtered_graphs}")

            

        
    
