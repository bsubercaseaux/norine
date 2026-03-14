import itertools
from dataclasses import dataclass

from pysat.formula import CNF, IDPool


def anti(v):
    return tuple((1 - x) for x in v)


def flip_i(v, i):
    return tuple((1 - x) if j == i else x for j, x in enumerate(v))


def swap(i, j, v):
    u = list(v)
    u[i], u[j] = u[j], u[i]
    return tuple(u)


def dist(u, v):
    return sum(1 for i in range(len(u)) if u[i] != v[i])


def antipodal_representatives(vertices):
    for u in vertices:
        if u > anti(u):
            continue
        yield u


@dataclass
class EncodingContext:
    n: int
    enc: CNF
    vpool: IDPool
    vertices: list
    graph: dict
    antipodal: bool
    r: callable
    var_to_edge: dict


def build_hypercube_graph(n):
    vertices = list(itertools.product([0, 1], repeat=n))
    vertices = [v[::-1] for v in vertices]  # reverse to match the order with SMS TODO
    graph = {}
    for v in vertices:
        graph[v] = []
        for i in range(n):
            neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
            graph[v].append(tuple(neighbor))
    return vertices, graph


def build_encoding_context(n, antipodal=False):
    enc = CNF()
    vpool = IDPool(start_from=1)
    vertices, graph = build_hypercube_graph(n)

    for v in vertices:
        assert len(graph[v]) == n, f"Graph is not a hypercube: {v} has {len(graph[v])} neighbors"

    r = lambda u, v: vpool.id(f"r_{min(u, v), max(u, v)}")

    var_to_edge = {}
    # Ensure edge variables are created first (important for dynamic symmetry breaking).
    for u in vertices:
        for v in graph[u]:
            var_to_edge[r(u, v)] = (u, v)
            enc.append([r(u, v), -r(u, v)])

    if antipodal:
        for u in vertices:
            for v in graph[u]:
                if v < u:
                    continue
                enc.append([-r(u, v), -r(anti(u), anti(v))])
                enc.append([r(u, v), r(anti(u), anti(v))])

        r_old = r

        def r_antipodal(u, v):
            if v < u:
                u, v = v, u
            if u < anti(v):
                return r_old(u, v)
            return -r_old(anti(u), anti(v))

        r = r_antipodal

    return EncodingContext(
        n=n,
        enc=enc,
        vpool=vpool,
        vertices=vertices,
        graph=graph,
        antipodal=antipodal,
        r=r,
        var_to_edge=var_to_edge,
    )
