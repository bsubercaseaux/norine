from eznf import modeler
import itertools
import argparse

def anti(v):
    return tuple((1 - x) for x in v)

def flip_i(v, i):
    return tuple((1 - x) if j == i else x for j, x in enumerate(v))
        
def swap(i, j, v):
    u = list(v)
    u[i], u[j] = u[j], u[i]
    return tuple(u)

def encode(n):
    enc = modeler.Modeler()
    vertices = list(itertools.product([0, 1], repeat=n))
    graph = {}
    for v in vertices:
        graph[v] = []
        for i in range(n):
            neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
            graph[v].append(tuple(neighbor))


    
    for u in vertices:
        for v in graph[u]:
            if u < v:
                enc.add_var(f"r_{u, v}")

    def r(u,v):
        return enc.v(f"r_{min(u,v), max(u,v)}")

    for u in vertices:
        for v in graph[u]:
            if u < v and [u, v] < sorted([anti(u), anti(v)]):
                enc.add_clause([r(u,v), r(anti(u), anti(v))])
                enc.add_clause([-r(u,v), -r(anti(u), anti(v))])

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
        if u < anti(u):
            antigeos = geodesics(u, anti(u))
            for antigeo in antigeos:
                enc.add_clause([r(p1, p2) for (p1, p2) in antigeo])

    max_comparisons = 12
    original_signed_edges = [(1, (u, v)) for u in vertices for v in graph[u] if u < v]
    for i in range(n):
        permuted_edges = [(s, (flip_i(u, i), flip_i(v, i))) for s, (u, v) in original_signed_edges]
        enc.lex_less_equal([s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges])
      
    for i, j in itertools.combinations(range(n), 2):
        permuted_edges = [(s, (swap(i, j, u), swap(i, j, v))) for s, (u, v) in original_signed_edges]
        enc.lex_less_equal([s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges], max_comparisons=max_comparisons)
        
    for (i, j) in itertools.combinations(range(n), 2):
        for k in range(n):
            permuted_edges = [(s, (swap(i, j, flip_i(u, k)), swap(i, j, flip_i(v, k)))) for s, (u, v) in original_signed_edges]
            enc.lex_less_equal([s * r(u, v) for s, (u, v) in original_signed_edges], [s * r(u, v) for s, (u, v) in permuted_edges], max_comparisons=max_comparisons)
    # print(f"Added {enc.n_clauses() - cls_pre_sb} symmetry breaking clauses")

    # for i, v in enumerate(graph[vertices[0]]):
    #     if i < (len(graph[vertices[0]]) + 1) // 2:
    #         enc.add_clause([r(vertices[0], v)])
    #     elif i == (len(graph[vertices[0]]) + 1) // 2:
    #         enc.add_clause([-r(vertices[0], v)])

    return enc


def decode(model, n):
    vertices = list(itertools.product([0, 1], repeat=n))
    graph = {}
    for v in vertices:
        graph[v] = []
        for i in range(n):
            neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
            graph[v].append(tuple(neighbor))

    result = {}
    for u in vertices:
        for v in graph[u]:
            if model[f"r_{u, v}"]:
                result[(u, v)] = True
            else:
                result[(u, v)] = False
    print(result)
    return result

argparser = argparse.ArgumentParser(description="Frankston encoding generator")
argparser.add_argument("-n", "--n", type=int, default=6, help="Number of bits in the hypercube")
args = argparser.parse_args()
encoding = encode(args.n)
encoding.serialize(f"frankston_encoding_{args.n}.cnf")
# encoding.solve_and_decode(lambda model: decode(model, args.n))
