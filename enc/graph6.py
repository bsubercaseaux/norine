"""
    Transform coloring of hypercube to unique unlabeled grpah in graph6 format (for more than 3 dimensions).
"""

import itertools

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
                    g.add_edge(
                        u,
                        v,
                    )
                else:
                    g.add_edge(u, f"c{c}")
                    g.add_edge(v, f"c{c}")
                    c += 1
    return nx.to_graph6_bytes(g, header=False).decode("utf-8").strip()
