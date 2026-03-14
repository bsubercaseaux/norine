from encoding_context import anti, antipodal_representatives, dist

# Conjecture order in this module follows the paper:
# C1: monochromatic path, C2: monochromatic geodesic,
# C3: <=1 color change path, C4: <=1 color change geodesic.


def _add_monochromatic_reachability(ctx, geodesic_only):
    # For C1/C2, p_{u,v} stands for RED reachability only (paper notation).
    p = lambda u, v: ctx.vpool.id(f"p_{u, v}")

    for u in antipodal_representatives(ctx.vertices):
        for v in ctx.graph[u]:
            ctx.enc.append([-ctx.r(u, v), p(u, v)])

    for u in antipodal_representatives(ctx.vertices):
        for w in ctx.vertices:
            if w in ctx.graph[u]:
                continue
            for v in ctx.graph[w]:
                if geodesic_only and dist(u, v) + 1 != dist(u, w):
                    continue
                ctx.enc.append([-p(u, v), -ctx.r(v, w), p(u, w)])

    return p


def _forbid_monochromatic_antipodal_pair(ctx, p):
    for u in antipodal_representatives(ctx.vertices):
        ctx.enc.append([-p(u, anti(u))])


def _add_one_change_reachability(ctx, geodesic_only):
    # q_{u,v,s}^color means "there is a u->v path with at most s color changes, ending with color".
    q = lambda color, u, v, s: ctx.vpool.id(f"q_{color}_{u, v, s}")
    swaps = [0, 1]
    colors = ["red", "blue"]

    for u in antipodal_representatives(ctx.vertices):
        for v in ctx.graph[u]:
            ctx.enc.append([-ctx.r(u, v), q("red", u, v, 0)])
            ctx.enc.append([ctx.r(u, v), q("blue", u, v, 0)])

    for u in antipodal_representatives(ctx.vertices):
        for w in ctx.vertices:
            if w in ctx.graph[u]:
                continue
            for v in ctx.graph[w]:
                if geodesic_only and dist(u, v) + 1 != dist(u, w):
                    continue
                for s in swaps:
                    ctx.enc.append([-q("red", u, v, s), -ctx.r(v, w), q("red", u, w, s)])
                    ctx.enc.append([-q("blue", u, v, s), ctx.r(v, w), q("blue", u, w, s)])
                    if s == 0:
                        ctx.enc.append([-q("red", u, v, 0), ctx.r(v, w), q("blue", u, w, 1)])
                        ctx.enc.append([-q("blue", u, v, 0), -ctx.r(v, w), q("red", u, w, 1)])

    for u in antipodal_representatives(ctx.vertices):
        for v in ctx.vertices:
            if u == v:
                continue
            for color in colors:
                ctx.enc.append([-q(color, u, v, 0), q(color, u, v, 1)])

    return q


def _forbid_one_change_antipodal_pair(ctx, q):
    for u in antipodal_representatives(ctx.vertices):
        ctx.enc.append([-q("red", u, anti(u), 0)])
        ctx.enc.append([-q("blue", u, anti(u), 0)])
        ctx.enc.append([-q("red", u, anti(u), 1)])
        ctx.enc.append([-q("blue", u, anti(u), 1)])


def encode_conjecture1(ctx):
    if not ctx.antipodal:
        raise ValueError("Conjecture 1 encoding assumes antipodal coloring. Use --antipodal-coloring.")
    p = _add_monochromatic_reachability(ctx, geodesic_only=False)
    _forbid_monochromatic_antipodal_pair(ctx, p)


def encode_conjecture2(ctx):
    if not ctx.antipodal:
        raise ValueError("Conjecture 2 encoding assumes antipodal coloring. Use --antipodal-coloring.")
    p = _add_monochromatic_reachability(ctx, geodesic_only=True)
    _forbid_monochromatic_antipodal_pair(ctx, p)


def encode_conjecture3(ctx):
    q = _add_one_change_reachability(ctx, geodesic_only=False)
    _forbid_one_change_antipodal_pair(ctx, q)


def encode_conjecture4(ctx):
    q = _add_one_change_reachability(ctx, geodesic_only=True)
    _forbid_one_change_antipodal_pair(ctx, q)
