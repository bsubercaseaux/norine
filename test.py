from sage.all import *
from itertools import *

gs = []
# gs = gs

k = 3

def graph_to_unique_unlabeled_graph(red_edges, negated = False):

    for u,v in red_edges:
        assert u < v, "Edges must be ordered (u < v)."
        # at most one bit difference
        assert bin(u ^ v).count('1') == 1, "vertices in edges must differ by exactly one bit."
    c = 2**k + 1
    g = Graph()
    for i in range(2**k):
        for x in range(k):
            # flip the xth bit of i
            j = i ^ (1 << x)

            if j < i:
                continue

            present = (i, j) in red_edges
            if negated:
                present = not present
            
            if present:
                g.add_edge(i, j)
            else:
                g.add_edge(i, c)
                g.add_edge(j, c)
                c += 1
    return g


# print("Unlabeled grpahs in g6 format:")
for g in gs:
    g_unlabeled = graph_to_unique_unlabeled_graph(g, negated=False)
    print(g_unlabeled.graph6_string())
    # print(g_unlabeled.canonical_label(edge_labels=true).sage().graph6_string())


exit()

# transform labeled hypercube to unlabeled graph so I can use nauty to get unique solutions
def labeled_hypercube_to_unlabeled_graph(red_edges, negated = False):

    # sanity check whether the edges are valid i.e., at most one bit is flipped
    for u, v in red_edges:
        assert  bin(u ^ v).count('1') == 1, "vertices in edges must differ by exactly one bit."
        assert u < v, "Edges must be ordered (u < v)."
    
    # print("Number of edges:",  len(red_edges) if not negated else 2**(k-1) * k - len(red_edges))

    g = Graph()
    for i in range(2**k):
        for x in range(k):
            # flip the xth bit of i
            j = i ^ (1 << x)

            if j < i:
                continue

            present = (i, j) in red_edges
            if negated:
                present = not present
            g.add_edge(i, j, present)
    return g


tranformed_graphs = [labeled_hypercube_to_unlabeled_graph(g, negated=False) for g in gs]
# tranformed_partial_graphs = [labeled_hypercube_to_unlabeled_graph(g, negated=False) for g in gs_partialy_sym_break]
# print("Add negated graphs")
# tranformed_graphs += [labeled_hypercube_to_unlabeled_graph(g, negated=True) for g in gs]
# get canonical forms of the graphs
canonical_forms = [g.canonical_label(edge_labels=true).graph6_string() for g in tranformed_graphs]
# canonical_forms_partial = [g.canonical_label(edge_labels=true).graph6_string() for g in tranformed_partial_graphs]



print("\n")


print("Number of graphs:", len(tranformed_graphs))
# print("Canonical forms of the graphs:")
# for form in canonical_forms:
#     print(form)
print("Number of unique graphs:", len(set(canonical_forms)))

# # check if canonical_forms_partial is a subset of canonical_forms
# if set(canonical_forms_partial).issubset(set(canonical_forms)):
#     print("All partialy symmetric graphs are contained in the full set of graphs.")

#unique graphs
for s in sorted(set(canonical_forms)):
    print(s)