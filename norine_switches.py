from eznf import modeler
import itertools
import argparse
import math
import random

def anti(v):
    return tuple((1 - x) for x in v)

def flip_i(v, i):
    return tuple((1 - x) if j == i else x for j, x in enumerate(v))
        
def swap(i, j, v):
    u = list(v)
    u[i], u[j] = u[j], u[i]
    return tuple(u)
    
def encode(n, sum_upper_bound, fprime=False):
    """
    Encoding from Section 6 of the Overleaf
    """
    enc = modeler.Modeler()
    vertices = list(itertools.product([0, 1], repeat=n))
    graph = {}
    for v in vertices:
        graph[v] = set()
        for i in range(n):
            neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
            graph[v].add(tuple(neighbor))
            
    for v in vertices:
        assert len(graph[v]) == n, f"Graph is not a hypercube: {v} has {len(graph[v])} neighbors"
    
    for u in vertices:
        for v in graph[u]:
            if u < v:
                enc.add_var(f"r_{u, v}")

    print("Base variables:", enc.n_vars())

    def r(u, v):
        return enc.v(f"r_{min(u, v), max(u, v)}")
    

    colors = ['red', 'blue']

    for u in vertices:
        if u > anti(u): continue
        for v in vertices:
            for color in colors:
                for s in range(n):
                    enc.add_var(f"p^{color}_{u, v, s}")


    def dist(u, v):
        return sum(1 for i in range(len(u)) if u[i] != v[i])
        # return sum(u[i] != v[i] for i in range(len(u)))
            

    # Eq 4, 5:
    for u in vertices:
        if u > anti(u): continue
        for v in graph[u]:
            enc.add_clause([-r(u, v), f"p^red_{u, v, 0}"])
            enc.add_clause([r(u, v), f"p^blue_{u, v, 0}"])


    # Eq 6, 7, 8, 9
    for u in vertices:
        if u > anti(u): continue
        for w in vertices:
            if w in graph[u]: continue
            for v in graph[w]:
                if dist(u, v) + 1 == dist(u, w):
                    for s in range(n):
                        # Eq 6.
                        enc.add_clause([f"-p^red_{u, v, s}", -r(v, w), f"p^red_{u, w, s}"])
                        # Eq 7.
                        enc.add_clause([f"-p^blue_{u, v, s}", r(v, w), f"p^blue_{u, w, s}"])

                        if s < n-1:
                            # Eq 8.
                            enc.add_clause([f"-p^red_{u, v, s}", r(v, w), f"p^blue_{u, w, s+1}"])
                            
                            # Eq 9.
                            enc.add_clause([f"-p^blue_{u, v, s}", -r(v, w), f"p^red_{u, w, s+1}"])

    # Eq 10.
    for u in vertices:
        if u > anti(u): continue
        for v in vertices:
            if u == v: continue
            for color in colors:
                for s in range(n-1):
                    enc.add_clause([f"-p^{color}_{u, v, s}", f"p^{color}_{u, v, s+1}"])


    # Eq 11.
    for u in vertices:
        if u > anti(u): continue
        for s in range(n):
            enc.add_var(f"p^t_{u, s}")
            for color in colors:
                enc.add_clause([f"-p^red_{u, anti(u), s}", f"p^t_{u, s}"])
                enc.add_clause([f"-p^blue_{u, anti(u), s}", f"p^t_{u, s}"])

    if fprime:
        for u in vertices:
            if u > anti(u): continue
            enc.add_var(f"p^t_{u, -1}")
            for s in range(n):
                enc.add_clause([f"-p^red_{u, anti(u), s}", f"-p^blue_{u, anti(u), s}", f"p^t_{u, s-1}"])



    # Eq 12.
    if not fprime:
        sum_vars = []
        for u in vertices:
            if u < anti(u):
                for s in range(n):
                    sum_vars.append(f"-p^t_{u, s}")

        enc.at_least_k(sum_vars, sum_upper_bound)
    else:
        sum_vars = []
        for u in vertices:
            if u < anti(u):
                for s in range(-1, n):
                    sum_vars.append(f"-p^t_{u, s}")

        enc.at_least_k(sum_vars, sum_upper_bound + (len(vertices) // 2))
    

     ## Symmetry breaking
    MAX_COMPARISONS = 70

    cls_pre_sb = enc.n_clauses()
    original_signed_edges = [(1, (u, v)) for u in vertices for v in graph[u] if u < v]
    for i in range(n):
        permuted_edges = [(s, (flip_i(u, i), flip_i(v, i))) for s, (u, v) in original_signed_edges]
        enc.lex_less_equal([s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges])
      
    for i, j in itertools.combinations(range(n), 2):
        permuted_edges = [(s, (swap(i, j, u), swap(i, j, v))) for s, (u, v) in original_signed_edges]
        enc.lex_less_equal([s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges], max_comparisons=10000)
        
    for (i, j) in itertools.combinations(range(n), 2):
        for k in range(n):
            permuted_edges = [(s, (swap(i, j, flip_i(u, k)), swap(i, j, flip_i(v, k)))) for s, (u, v) in original_signed_edges]
            enc.lex_less_equal([s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges], max_comparisons=MAX_COMPARISONS)
    print(f"Added {enc.n_clauses() - cls_pre_sb} symmetry breaking clauses")
 
    cubing_depth = 15
    def cube_gen():
        random.seed(42) # for shuffling the cubes
        cubes = []
        edges = []
        for u in [vertices[30], vertices[50], vertices[60], vertices[80]]:
        # for u in vertices[30:35]:
            for v in graph[u]:
                if u < v:
                    edges.append((u, v))
        # random.shuffle(edges)
        edges = edges[:cubing_depth]
        
        edges_lits = []
        for u, v in edges:
            elit = r(u, v)
            if -elit in edges_lits:
                continue
            edges_lits.append(elit)
        
        for edge_vals in itertools.product([0, 1], repeat=len(edges_lits)):
            cube = []
            for i, edge_lit in enumerate(edges_lits):
                if edge_vals[i] == 1:
                    cube.append(edge_lit)
                else:
                    cube.append(-edge_lit)
            cubes.append(cube)
        random.shuffle(cubes)
        return cubes
        
    if cubing_depth is not None and cubing_depth > 0:
        enc.cube_and_conquer(cube_generator=cube_gen, output_file=f"norine_{n}_switches_cubing{cubing_depth}.cubes")

    cubes = cube_gen()
    random_cube = random.choice(cubes)
    for l in random_cube:
        enc.add_clause([l])

    return enc
    


if __name__ == "__main__":         
    argparser = argparse.ArgumentParser(description="Norine's conjecture")
    argparser.add_argument("-n", type=int, help="Order of the hypercube graph", required=True)
    argparser.add_argument('-b', type=int, help="Bound on the sum (Eq 12.)", required=True)
    argparser.add_argument('-prime', action='store_true')
    N = argparser.parse_args().n
    b = argparser.parse_args().b
    prime = argparser.parse_args().prime


    encoding = encode(N, b, prime)
    filename = f"norine_switches_{N}_{b}{'_prime' if prime else ''}.cnf"
    encoding.serialize(filename)

    print(f"Serialized encoding to {filename}")
            
    
