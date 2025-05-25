from eznf import modeler
import itertools
import argparse
import random

def anti(v):
    return tuple((1 - x) for x in v)

def lex_smaller(seq1, seq2, enc, max_comparisons=float('inf')):
    """Ensure that seq1 is lexicographically smaller or equal than seq2"""
    assert len(seq1) == len(seq2)
    clauses = []
    v_name = f"_lex_{enc.n_vars()+1}"
    enc.add_var(v_name)
    all_previous_equal = enc.v(v_name)
    clauses.append([all_previous_equal])
    cnt_supp = 0
    cnt_skip = 0
    for i in range(len(seq1)):
        if cnt_supp >= max_comparisons:
            break
            # pass
        if seq1[i] == seq2[i]:
            cnt_skip += 1
            continue
        clauses.append([-all_previous_equal, -seq1[i], +seq2[i]])  # all previous equal implies seq1[i] <= seq2[i]
        cnt_supp += 1
        vname_new = f"_lex_{enc.n_vars()+1}"
        enc.add_var(vname_new)
        all_previous_equal_new = enc.v(vname_new)
        clauses.append([-all_previous_equal, -seq1[i], +all_previous_equal_new])
        clauses.append([-all_previous_equal, +seq2[i], +all_previous_equal_new])
        all_previous_equal = all_previous_equal_new
    # print(f"cnt skip {cnt_skip}, cnt supp {cnt_supp}")
    
    enc.add_clauses(clauses)
    
# def lex_smaller_reverse(seq1, seq2, enc):
#     lex_smaller(seq2, seq1, enc)



def encode(n, deg_constraint, cubing_depth):
    """
    Encode whether there is a 2-coloring of the edges of the hypercube graph on n vertices
    such that antipodal edges have different colors, and no monochromatic path exists between antipodal vertices.
    """
    vertices = list(itertools.product([0, 1], repeat=n))
    graph = {}
    for v in vertices:
        graph[v] = set()
        for i in range(n):
            neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
            graph[v].add(tuple(neighbor))
            
    for v in vertices:
        assert len(graph[v]) == n, f"Graph is not a hypercube: {v} has {len(graph[v])} neighbors"
    
    enc = modeler.Modeler()
    for u in vertices:
        for v in graph[u]:
            if u < v:
                if [u, v] < sorted([anti(u), anti(v)]):
                    enc.add_var(f"r_{u, v}")
                
    print(f"Neighbors of {vertices[0]}: {graph[vertices[0]]}")
    
    def e(u, v):
        if u > v:
            u, v = v, u
    
        au, av = anti(u), anti(v)
        if au > av:
            au, av = av, au
        
        if [u, v] < [au, av]:
            return enc.v(f"r_{u, v}")
        return -enc.v(f"r_{au, av}")

    def e_safe(u, v):
        return e(u, v) 
        return enc.v(f"r_{u, v}") if u < v else -enc.v(f"r_{v, u}")

    print("r variables:", enc.n_vars())
    
    def flip_i(v, i):
        return tuple((1 - x) if j == i else x for j, x in enumerate(v))
        
    def swap(i, j, v):
        u = list(v)
        u[i], u[j] = u[j], u[i]
        return tuple(u)
    
   
    original_edges = []
    for u in vertices:
        for v in graph[u]:
            if u < v and [u, v] < sorted([anti(u), anti(v)]):
                original_edges.append((u, v))

    
    def int_to_bin(n_):
        return tuple(int(x) for x in bin(n_)[2:].zfill(n))
    
    positive_edges = []
    negative_edges = []

    if deg_constraint >= 0:
        enc.exactly_k([e(int_to_bin(0), v) for v in graph[int_to_bin(0)]], deg_constraint)
        for u in range(1, 2**n):
            if deg_constraint == 1:
                enc.add_clause([e(int_to_bin(u), v) for v in graph[int_to_bin(u)]])
                enc.add_clause([-e(int_to_bin(u), v) for v in graph[int_to_bin(u)]])
            else:
                enc.at_least_k([e(int_to_bin(u), v) for v in graph[int_to_bin(u)]], deg_constraint)
                enc.at_least_k([-e(int_to_bin(u), v) for v in graph[int_to_bin(u)]], deg_constraint)

    rest = [e for e in original_edges if e not in positive_edges and e not in negative_edges]
    
    original_signed_edges = [(-1, e) for e in positive_edges] + [(1,e) for e in negative_edges] + [(1,e) for e in rest]
    
    MAX_COMPARISONS = 80 # 10000000 # e9 # 90 if n == 8 else 80
    
    cls_pre_sb = enc.n_clauses()
    for i in range(n):
        permuted_edges = [ (s,(flip_i(u, i), flip_i(v, i))) for s, (u, v) in original_signed_edges]
        lex_smaller([s * e(u, v) for s, (u, v) in original_signed_edges], [s * e(u, v) for s, (u, v) in permuted_edges], enc, max_comparisons=MAX_COMPARISONS)
      
    for i, j in itertools.combinations(range(n), 2):
        permuted_edges = [(s, (swap(i, j, u), swap(i, j, v))) for s, (u, v) in original_signed_edges]
        lex_smaller([s * e(u, v) for s, (u, v) in original_signed_edges], [s* e(u, v) for s, (u, v) in permuted_edges], enc, max_comparisons=MAX_COMPARISONS)
        
    for (i, j) in itertools.combinations(range(n), 2):
        for k in range(n):
            permuted_edges = [(s, (swap(i, j, flip_i(u, k)), swap(i, j, flip_i(v, k)))) for s, (u, v) in original_signed_edges]
            lex_smaller([s*e(u, v) for s, (u, v) in original_signed_edges], [s* e(u, v) for s, (u, v) in permuted_edges], enc, max_comparisons=MAX_COMPARISONS)
    
           
       
    print(f"Added {enc.n_clauses() - cls_pre_sb} symmetry breaking clauses")
    
    
    def geodesics(u, v):
        if u == v:
            return [[]]
        ans = []
        for i in range(len(u)):
            if u[i] != v[i]:
                # print(f"Flipping index {i} in {u} to get {flip_i(u, i)}")
                new_u = flip_i(u, i)
                rgeo = geodesics(new_u, v)

                for g in rgeo:
                    ans.append([(u, new_u)] + g)
        return ans

                
    for u in vertices:
        antigeos = geodesics(u, anti(u))
        for antigeo in antigeos:
            enc.add_clause([-e(p1, p2) for (p1, p2) in antigeo])
        # enc.add_clause([-e(p1, p1) for (p1, p2) in geodesics(u, anti(u))])
        
    def cube_gen():
        random.seed(42)
        cubes = []
        edges = []
        # for u in [vertices[30], vertices[50], vertices[60], vertices[80]]:
        for u in vertices[30:35]:
            for v in graph[u]:
                if u < v:
                    edges.append((u, v))
        # random.shuffle(edges)
        edges = edges[:cubing_depth]
        
        edges_lits = []
        for u, v in edges:
            elit = e(u, v)
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
        
    enc.cube_and_conquer(cube_generator=cube_gen, output_file=f"norine_{n}_deg{deg_constraint}_cubing{cubing_depth}.cubes")

    return enc
    
    
def decode(model, n):
    vertices = list(itertools.product([0, 1], repeat=n))
    
    for k in model.keys():
        if k.startswith("rpath_"):
            print(f"{k} = {model[k]}")
    
    graph = {}
    for v in vertices:
        graph[v] = set()
        for i in range(n):
            neighbor = [v[j] if i != j else (1- v[j]) for j in range(n)]
            graph[v].add(tuple(neighbor))
    
    for u in vertices:
        for v in graph[u]:
            if u < v:
                if [u, v] < sorted([anti(u), anti(v)]):
                    if model[f"r_{u, v}"] == 1:
                        print(f"Edge {u} - {v} is red")
                    else:
                        print(f"Edge {u} - {v} is blue")
                else:
                    if model[f"r_{tuple(sorted([anti(u), anti(v)]))}"] == 1:
                        print(f"Edge {anti(u)} - {anti(v)} is red")
                    else:
                        print(f"Edge {anti(u)} - {anti(v)} is blue")
                    
argparser = argparse.ArgumentParser(description="Norine's conjecture")
argparser.add_argument("-n", type=int, help="Order of the hypercube graph", required=True)
argparser.add_argument("-d", type=int, help="Enforces that vertex 0 is of min degree and has degree d", required=True)
argparser.add_argument("-c", type=int, help="Depth of the cubing (generates 2^c cubes)", required=True)
N = argparser.parse_args().n
deg_constraint = argparser.parse_args().d
cubing_depth = argparser.parse_args().c
encoding = encode(N, deg_constraint, cubing_depth)
filename = f"norinepath_{N}_deg{deg_constraint}_cubing{cubing_depth}.cnf"
encoding.serialize(filename)
print(f"Serialized encoding to {filename}")
            
    
