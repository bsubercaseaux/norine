from eznf import modeler
import itertools
import argparse
import random

def anti(v):
    return tuple((1 - x) for x in v)

def flip_i(v, i):
    return tuple((1 - x) if j == i else x for j, x in enumerate(v))
        
def swap(i, j, v):
    u = list(v)
    u[i], u[j] = u[j], u[i]
    return tuple(u)
    
def encode(n, deg_constraint, cubing_depth, compact_encoding=False):
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
            if u < v and [u, v] < sorted([anti(u), anti(v)]):
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
    print("r variables:", enc.n_vars())

    original_edges = []
    for u in vertices:
        for v in graph[u]:
            if u < v and [u, v] < sorted([anti(u), anti(v)]):
                original_edges.append((u, v))

    def int_to_bin(n_):
        return tuple(int(x) for x in bin(n_)[2:].zfill(n))
    
    positive_edges = []
    negative_edges = []

    # Their symmetry breaking clauses
    for ik, vk in enumerate(graph[int_to_bin(0)]):
        if ik <= (n+1)//2: # ceil((n)/2)
            enc.add_clause([e(int_to_bin(0), vk)])
        elif ik == (n+1)//2 + 1:
            enc.add_clause([-e(int_to_bin(0), vk)])
        else:
            break

    if deg_constraint is not None and deg_constraint >= 0:
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
    
    MAX_COMPARISONS =  70 if n == 8 else 40
    
    cls_pre_sb = enc.n_clauses()
    # for i in range(n):
    #     permuted_edges = [(s, (flip_i(u, i), flip_i(v, i))) for s, (u, v) in original_signed_edges]
    #     enc.lex_less_equal([s * e(u, v) for s, (u, v) in original_signed_edges], [s * e(u, v) for s, (u, v) in permuted_edges])
      
    # for i, j in itertools.combinations(range(n), 2):
    #     permuted_edges = [(s, (swap(i, j, u), swap(i, j, v))) for s, (u, v) in original_signed_edges]
    #     enc.lex_less_equal([s * e(u, v) for s, (u, v) in original_signed_edges], [s* e(u, v) for s, (u, v) in permuted_edges], max_comparisons=MAX_COMPARISONS)
        
    # for (i, j) in itertools.combinations(range(n), 2):
    #     for k in range(n):
    #         permuted_edges = [(s, (swap(i, j, flip_i(u, k)), swap(i, j, flip_i(v, k)))) for s, (u, v) in original_signed_edges]
    #         enc.lex_less_equal([s*e(u, v) for s, (u, v) in original_signed_edges], [s* e(u, v) for s, (u, v) in permuted_edges], max_comparisons=MAX_COMPARISONS)
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

    if not compact_encoding:          
        for u in vertices:
            antigeos = geodesics(u, anti(u))
            for antigeo in antigeos:
                enc.add_clause([-e(p1, p2) for (p1, p2) in antigeo])

    def dist(u, v):
        return sum(1 for i in range(len(u)) if u[i] != v[i])
    
    def D(u, r):
        return [v for v in vertices if dist(u, v) == r]
    
    if compact_encoding:
        for u in vertices:
            if u > anti(u):
                continue

            for v in vertices:
               enc.add_var(f"rpath_{u, v}_{dist(u, v)}")

            enc.add_clause([f"rpath_{u, u}_0"])

            for i in range(1, n+1):
                for v in D(u, i):
                    for vp in D(u, i-1):
                        if v in graph[vp]:
                            enc.add_var(f"rpath_{u, v}_via_{vp}_{i}")
                            enc.add_clause([f"-rpath_{u, vp}_{i-1}", -e(vp, v), f"rpath_{u, v}_via_{vp}_{i}"])

                            enc.add_clause([f"-rpath_{u, v}_via_{vp}_{i}", f"rpath_{u, v}_{i}"])

        for u in vertices:
            if u > anti(u):
                continue
            enc.add_clause([f"-rpath_{u, anti(u)}_{n}"])




    ###
    ### f(k) = c
    ###

    ### in the i-th subpath you have (i-1)*k 1-bits when entering,
    #  and i*k 1-bits when leaving

    ### Fix a coloring c of the edges of the hypercube graph
    ### Take a random geodesic R between 0^n and 1^n
        ### 0^n -> v_1 -> v_2 -> ... -> v_{n-1} -> 1^n
        ### Each v_i has i 1-bits.
        ### P_j := v_{(j-1)*k} -> ... -> v_{j*k}
        ### E[colorSwitches(P_j)] <= f(k)
        ### E[colorSwitches(R)] = sum_{j=1}^{n/k} E[colorSwitches(P_j)]
        ###                     + sum_{j=1}^{n/k} E[colorSwitchesBetweeen(P_j, P_{j+1})]

    ### E[colorSwitches(R)] <= n/k * f(k) + (n/k - 1) = n/k * (f(k)+1) - 1
    ### k = 3 ->  E[colorSwitches(R)] <= 2n/3 (best is 3/8n)

    ### k = 5 -> E[colorSwitches(R)] <= n/5 * (9/4) = 9n/20 
    ###     if we could argue n/k * (f(k) + 1/2), then for k=5 we get n/5 * (7/4) = 7n/20
    ### k = 6 -> E[colorSwitches(R)] <= n/6 *  (f(6) + 1) = 
    #                






        
    def cube_gen():
        random.seed(42) # for shuffling the cubes
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
        
    if cubing_depth is not None and cubing_depth > 0:
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

if __name__ == "__main__":         
    argparser = argparse.ArgumentParser(description="Norine's conjecture")
    argparser.add_argument("-n", type=int, help="Order of the hypercube graph", required=True)
    argparser.add_argument("-d", type=int, help="Enforces that vertex 0 is of min degree and has degree d")
    argparser.add_argument("-c", type=int, help="Depth of the cubing (generates 2^c cubes)")
    argparser.add_argument("-e", action="store_true", help="Use compact encoding (default: False)")
    N = argparser.parse_args().n
    deg_constraint = argparser.parse_args().d
    cubing_depth = argparser.parse_args().c
    compact_encoding = argparser.parse_args().e
    encoding = encode(N, deg_constraint, cubing_depth, compact_encoding=compact_encoding)
    filename = f"norine_{N}_deg{deg_constraint}.cnf" if deg_constraint is not None else f"norinepath_{N}_plain.cnf"
    encoding.serialize(filename)
    print(f"Serialized encoding to {filename}")
            
    
