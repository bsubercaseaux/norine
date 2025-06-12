import itertools

def checkLexMin(red_edges, n, plusNegated=False):
    """
        Checks whether minimal
    """

    vertices = list(itertools.product([0, 1], repeat=n))
    vertices = [v[::-1] for v in vertices]
    graph = {}
    for v in vertices:
        graph[v] = []
        for i in range(n):
            neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
            graph[v].append(tuple(neighbor))

    original_edges = [(u, v) for u in vertices for v in graph[u] if u < v]

    # print("original_edges")
    # print(original_edges)
    # exit()
    
    def edges_to_sequence(red_edges):
        return [1 if (u, v) in red_edges or (v,u) in red_edges else 0 for u, v in original_edges]

    original_edges_seq = edges_to_sequence(red_edges)


    for perm_dimensions in itertools.permutations(range(n)):
        for flip_dimensions in itertools.product([0, 1], repeat=n):

            # def permute_and_flip(v):
            #     # print(f"Permuting {v} with {perm_dimensions} and flipping {flip_dimensions}")
            #     return tuple((v[perm_dimensions[i]] if flip_dimensions[i] == 0 else 1 - v[perm_dimensions[i]] for i in range(n)))
            

            def permute_and_flip(v):
                # print(f"Permuting {v} with {perm_dimensions} and flipping {flip_dimensions}")

                v_perm = [v[perm_dimensions[i]] for i in range(n)]

                # flip
                v_perm_flip = [v_perm[i] if flip_dimensions[i] == 0 else 1 - v_perm[i] for i in range(n)]
                return tuple(v_perm_flip)
            
            permuted_ordering = [(permute_and_flip(u), permute_and_flip(v)) for u,v in original_edges]
            # permuted_edges = [(permute_and_flip(u), permute_and_flip(v)) for u,v in red_edges]
            # permuted_edges_seq = edges_to_sequence(permuted_edges)
            permuted_edges_seq = [1 if (u,v) in red_edges or (v,u) in red_edges else 0 for u,v in permuted_ordering]


            if permuted_edges_seq < original_edges_seq:
                print("Original edge ordering:", str(original_edges).replace(" ", ""))
                print("Permuted edge ordering:", str([(permute_and_flip(u), permute_and_flip(v)) for u,v in original_edges]).replace(" ", ""))

                print("First index where different", min([i for i in range(len(permuted_edges_seq)) if original_edges_seq[i] > permuted_edges_seq[i]]))

                print("Orig seq:", original_edges_seq)
                print("Perm seq:", permuted_edges_seq)

                print("Witness permutation:", perm_dimensions)
                print("Witness flip:", flip_dimensions)
                return False
            
            if plusNegated:
                if (not permuted_edges_seq) < original_edges_seq:
                    return False
    return True

def checkFirstVertexMindegree(red_edges):
    elements = [v for v,_ in red_edges] + [v for _,v in red_edges]

    unique_elements = set(elements)

    counts = {u: sum(1 for v in elements if v == u) for u in unique_elements}

    # print(counts)

    for u in counts:
        assert (0,0,0) not in counts or  counts[u] >= counts[(0,0,0)]





n = 3
count_min = 0

vertices = list(itertools.product([0, 1], repeat=n))
graph = {}
for v in vertices:
    graph[v] = set()
    for i in range(n):
        neighbor = [v[j] if i != j else (1 - v[j]) for j in range(n)]
        graph[v].add(tuple(neighbor))

original_edges = [(u, v) for u in vertices for v in graph[u] if u < v]

# print("Original edges:", original_edges)

with open("./dynamic/asdf", "r") as f:
    for line in f:
        if line.startswith("["):
            red_edges = eval(line.strip())
            # print(red_edges)
            if checkLexMin(red_edges, n, plusNegated=False):
                # print("YES")
                count_min += 1
            else:
                print("NO")
                print(str(red_edges).replace(" ", ""))

            checkFirstVertexMindegree(red_edges)

            
print("Number of lexicographically minimal models:", count_min)