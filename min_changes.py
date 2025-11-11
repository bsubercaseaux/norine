import heapq
import random

def min_color_switch_geodesic(n, color_of_edge):
    """
    Find a path of length n in the n-cube from 0^n to 1^n
    minimizing the number of times the 2-coloring flips.

    Args:
      n: dimension of the cube.
      color_of_edge(v, i) -> 0 or 1,
         the color of the edge from vertex v in direction i.

    Returns:
      path: list of vertices (as ints in [0,2^n)) from 0 to 2^n-1
      switches: minimum number of color-changes along that path.
    """
    N = 1 << n
    target = N - 1
    INF = float('inf')

    # dist[v][c] = best total weight to reach state (v, last_color=c)
    dist = [[INF, INF] for _ in range(N)]
    prev = [[(None,None,None) for _ in range(2)] for _ in range(N)]
    pq = []

    # We encode cost so that:
    #  • Primary cost = (n+1) per edge → ensures any length>n path is more expensive
    #  • Secondary cost = +1 whenever color flips from the previous edge.
    #
    # At the very first step there is no “previous color,” so we just pay (n+1)
    # and set last_color = the color of that first edge, with zero flips so far.

    for i in range(n):
        u = 1 << i
        c = color_of_edge(0, i)
        w = n + 1
        if w < dist[u][c]:
            dist[u][c] = w
            prev[u][c] = (0, None, i)    # came from 0, no prev_color, via bit-flip i
            heapq.heappush(pq, (w, u, c))

    # Dijkstra on states (vertex, last_color)
    while pq:
        w, v, c_prev = heapq.heappop(pq)
        if w > dist[v][c_prev]:
            continue
        if v == target:
            break

        for i in range(n):
            u = v ^ (1 << i)
            c_edge = color_of_edge(v, i)
            cost_flip = 0 if c_edge == c_prev else 1
            w2 = w + (n + 1) + cost_flip
            if w2 < dist[u][c_edge]:
                dist[u][c_edge] = w2
                prev[u][c_edge] = (v, c_prev, i)
                heapq.heappush(pq, (w2, u, c_edge))

    # pick the better ending color
    c_end = 0 if dist[target][0] <= dist[target][1] else 1
    total_w = dist[target][c_end]
    switches = total_w - n*(n+1)

    # reconstruct the bit-flip sequence
    flips = []
    v, c = target, c_end
    while v != 0:
        pv, pc, bit = prev[v][c]
        flips.append(bit)
        v, c = pv, pc
    flips.reverse()

    # build the vertex path
    path = [0]
    cur = 0
    for bit in flips:
        cur ^= 1 << bit
        path.append(cur)

    return path, switches

n = 7
mx = 0
for it in range(500):
    color = [ [random.choice([0, 1]) for _ in range(n)] for _ in range(1<<n) ]

    def color_of_edge(v,i):
        return color[v][i]


    ans = min_color_switch_geodesic(n, color_of_edge)
    mx = max(mx, ans[1])

print(f"Max switches for n={n}: {mx}")