from eznf import modeler
import itertools
import argparse
import random

def anti(v):
    return tuple((1 - x) for x in v)

def lex_smaller(seq1, seq2, enc):
    """Ensure that seq1 is lexicographically smaller or equal than seq2"""
    assert len(seq1) == len(seq2)
    clauses = []
    v_name = f"_lex_{enc.n_vars()+1}"
    enc.add_var(v_name)
    all_previous_equal = enc.v(v_name)
    clauses.append([all_previous_equal])
    for i in range(len(seq1)):
        clauses.append([-all_previous_equal, -seq1[i], +seq2[i]])  # all previous equal implies seq1[i] <= seq2[i]
        vname_new = f"_lex_{enc.n_vars()+1}"
        enc.add_var(vname_new)
        all_previous_equal_new = enc.v(vname_new)
        clauses.append([-all_previous_equal, -seq1[i], +all_previous_equal_new])
        clauses.append([-all_previous_equal, +seq2[i], +all_previous_equal_new])
        all_previous_equal = all_previous_equal_new
    
    enc.add_clauses(clauses)



def encode(n):
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
                # if [u, v] < sorted([anti(u), anti(v)]):
                enc.add_var(f"r_{u, v}")
                
    # assert enc.n_vars() == n*(2**(n-1)), f"Expected {n*(2**(n-1))} variables, got {enc.n_vars()}"
    
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
    for u in vertices:
        for v in vertices:
            if u < v:
                enc.add_var(f"rpath_{u, v}")
                # enc.add_var(f"bpath_{u, v}")
                
    def rpath(u, v):
        return enc.v(f"rpath_{min(u, v), max(u, v)}")
            
    for u in vertices:
        for v in graph[u]:
            enc.add_clause([-e_safe(u, v), rpath(u, v)])
            # enc.add_clause([-rpath(u, v), e_safe(u, v)])
            
    # for v in list(graph[u])[:n//2]:
    #     enc.add_clause([e_safe(u, v)])
    
    def flip_i(v, i):
        return tuple((1 - x) if j == i else x for j, x in enumerate(v))
        
    def swap(i, j, v):
        u = list(v)
        u[i], u[j] = u[j], u[i]
        return tuple(u)
    
    cls_pre_sb = enc.n_clauses()
    original_edges = []
    for u in vertices:
        for v in graph[u]:
            if u < v and [u, v] < sorted([anti(u), anti(v)]):
                original_edges.append((u, v))
                
   
    
    # original_edges = [(u, v) for u in vertices for v in graph[u] if u < v]
    original_edges = original_edges[:50]
    
    enc.exactly_k([e(vertices[0], v) for v in graph[vertices[0]]], 1)
    
    
    

    
    for i in range(n):
        permuted_edges = [(flip_i(u, i), flip_i(v, i)) for u, v in original_edges]
        lex_smaller([e(u, v) for u, v in original_edges], [e(u, v) for u, v in permuted_edges], enc)
      
    for i, j in itertools.combinations(range(n), 2):
        permuted_edges = [(swap(i, j, u), swap(i, j, v)) for u, v in original_edges]
        lex_smaller([e(u, v) for u, v in original_edges], [e(u, v) for u, v in permuted_edges], enc)
        
    for (i, j) in itertools.combinations(range(n), 2):
        for k in range(n):
            permuted_edges = [(swap(i, j, flip_i(u, k)), swap(i, j, flip_i(v, k))) for u, v in original_edges]
            lex_smaller([e(u, v) for u, v in original_edges], [e(u, v) for u, v in permuted_edges], enc)

           
       
    print(f"Added {enc.n_clauses() - cls_pre_sb} symmetry breaking clauses")

    for u in vertices:
        for v in graph[u]:
            for w in vertices:
                if w in (u, v):
                    # print("skipping?")
                    continue
               
                cls = [-e_safe(u, v), -rpath(v,  w), rpath(u, w)]
                # print(f"Adding clause: {cls}")
                enc.add_clause(cls)
                
    # for (u, v, w) in itertools.combinations(vertices, 3):
    #     # if w < u:
    #     #     continue
    #     enc.add_clause([-rpath(u, v), -rpath(v, w), rpath(u, w)])

    for u in vertices:
        enc.add_clause([-rpath(u, anti(u))])
        
    def cube_gen():
        cubes = []
        edges = []
        for u in vertices[30:35]:
            for v in graph[u]:
                if u < v:
                    edges.append((u, v))
        edges = edges[:13]
        
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
        return cubes
        
    enc.cube_and_conquer(cube_generator=cube_gen, output_file="norine.cubes")

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
argparser.add_argument("-n", type=int, help="Order of the hypercube graph", default=4)
N = argparser.parse_args().n
encoding = encode(N)
encoding.serialize(f"norine_{N}.cnf")
print(f"Serialized encoding to norine_{N}.cnf")
# encoding.solve_and_decode(lambda m: decode(m, N))
            
    