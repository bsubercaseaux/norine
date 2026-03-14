from pysat.card import CardEnc

from encoding_context import anti, antipodal_representatives, dist


def _compute_swap_levels(n, sum_upper_bound, conjecture6, b2, b3):
    s_values = []
    if sum_upper_bound:
        s_values.extend(list(range(n)))
    if conjecture6:
        s_values.extend([0, 1])
    if b2 is not None:
        s_values.extend([0, 1, 2])
    if b3:
        s_values.append(0)
    return sorted(list(set(s_values)))


def encode_f_family(
    ctx,
    sum_upper_bound,
    fprime=False,
    card_type=1,
    path_version=False,
    b2=None,
    b3=None,
    conjecture6=False,
):
    s_values = _compute_swap_levels(ctx.n, sum_upper_bound, conjecture6, b2, b3)
    assert s_values != [], "S must not be empty for f/f' style encoding"

    colors = ["red", "blue"]
    pc = lambda color, u, v, s: ctx.vpool.id(f"p^{color}_{u, v, s}")
    pt = lambda u, s: ctx.vpool.id(f"p^t_{u, s}")

    # Eq. 5, 6
    for u in antipodal_representatives(ctx.vertices):
        for v in ctx.graph[u]:
            ctx.enc.append([-ctx.r(u, v), pc("red", u, v, 0)])
            if not (ctx.antipodal and s_values == [0]):
                ctx.enc.append([ctx.r(u, v), pc("blue", u, v, 0)])

    # Eq. 7, 8, 9, 10
    for u in antipodal_representatives(ctx.vertices):
        for w in ctx.vertices:
            if w in ctx.graph[u]:
                continue
            for v in ctx.graph[w]:
                if path_version or dist(u, v) + 1 == dist(u, w):
                    for s in s_values:
                        ctx.enc.append([-pc("red", u, v, s), -ctx.r(v, w), pc("red", u, w, s)])
                        if not (ctx.antipodal and s_values == [0]):
                            ctx.enc.append([-pc("blue", u, v, s), ctx.r(v, w), pc("blue", u, w, s)])

                        if s < ctx.n - 1:
                            ctx.enc.append([-pc("red", u, v, s), ctx.r(v, w), pc("blue", u, w, s + 1)])
                            if not (ctx.antipodal and s_values == [0]):
                                ctx.enc.append([-pc("blue", u, v, s), -ctx.r(v, w), pc("red", u, w, s + 1)])

    # Eq. 11
    for u in antipodal_representatives(ctx.vertices):
        for v in ctx.vertices:
            if u == v:
                continue
            for color in colors:
                for s in s_values:
                    if s < max(s_values):
                        ctx.enc.append([-pc(color, u, v, s), pc(color, u, v, s + 1)])

    # Eq. 12
    if sum_upper_bound or b2 or b3 or conjecture6:
        for u in antipodal_representatives(ctx.vertices):
            for s in range(ctx.n):
                for color in colors:
                    ctx.enc.append([-pc("red", u, anti(u), s), pt(u, s)])
                    ctx.enc.append([-pc("blue", u, anti(u), s), pt(u, s)])

    if fprime:
        for u in antipodal_representatives(ctx.vertices):
            for s in s_values:
                ctx.enc.append([-pc("red", u, anti(u), s), -pc("blue", u, anti(u), s), pt(u, s - 1)])

    if sum_upper_bound:
        # Eq. 13
        if not fprime:
            sum_vars = []
            for u in ctx.vertices:
                if u < anti(u):
                    for s in s_values:
                        sum_vars.append(-pt(u, s))
            ctx.enc.extend(CardEnc.atleast(sum_vars, bound=sum_upper_bound, vpool=ctx.vpool, encoding=card_type))
        else:
            sum_vars = []
            for u in ctx.vertices:
                if u < anti(u):
                    for s in [-1] + s_values:
                        sum_vars.append(-pt(u, s))
            ctx.enc.extend(
                CardEnc.atleast(
                    sum_vars,
                    bound=sum_upper_bound + (len(ctx.vertices) // 2),
                    vpool=ctx.vpool,
                    encoding=card_type,
                )
            )

    if conjecture6:
        # All blocked on the "main" geodesic.
        for i in range(ctx.n + 1):
            v = tuple([0] * (ctx.n - i) + [1] * i)
            ctx.enc.append([-pt(v, 1)])

    if b2:
        ctx.enc.extend(
            CardEnc.atleast(
                [-pt(u, 1) for u in ctx.vertices if u < anti(u)],
                bound=b2,
                vpool=ctx.vpool,
                encoding=card_type,
            )
        )

    if b3:
        assert len([-pt(u, 0) for u in ctx.vertices if u < anti(u)]) <= b3, (
            "b3 must be larger than the number of antipodal pairs otherwise pysat fails"
        )
        ctx.enc.extend(
            CardEnc.atleast(
                [-pt(u, 0) for u in ctx.vertices if u < anti(u)],
                bound=b3,
                vpool=ctx.vpool,
                encoding=card_type,
            )
        )
