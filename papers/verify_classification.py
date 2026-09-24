from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, permutations, product


def mod1(x):
    x = F(x)
    return x - x.numerator // x.denominator


def canon_rot(rel):
    rel = [mod1(x) for x in rel]
    return min(tuple(sorted(mod1(x - a) for x in rel)) for a in set(rel))


def rp(p):
    return tuple(F(j, p) for j in range(p))


def subtract_rel(s, t, a, b):
    r = mod1(a - b)
    out = list(s)
    out.remove(a)
    removed = False
    for x in t:
        y = mod1(x + r)
        if not removed and y == a:
            removed = True
        else:
            out.append(mod1(y + F(1, 2)))
    assert removed
    return tuple(out)


def construct_subs(p, ts):
    base = rp(p)
    out = set()
    for shared in combinations(base, len(ts)):
        for chosen in product(*ts):
            rel = tuple(base)
            ok = True
            for a, t, b in zip(shared, ts, chosen):
                if a not in rel:
                    ok = False
                    break
                rel = subtract_rel(rel, t, a, b)
            if ok:
                out.add(canon_rot(rel))
    return out


def construct_outer(p, tsets):
    out = set()
    for ts in product(*tsets):
        out |= construct_subs(p, [list(t) for t in ts])
    return out


r2, r3, r5, r7, r11 = map(rp, (2, 3, 5, 7, 11))
types = {
    "R2": {canon_rot(r2)},
    "R3": {canon_rot(r3)},
    "R5": {canon_rot(r5)},
    "R7": {canon_rot(r7)},
    "R11": {canon_rot(r11)},
}

for j in range(1, 5):
    types[f"R5:{j}R3"] = construct_subs(5, [r3] * j)
types["R5:R3"] = types["R5:1R3"]

for j in range(1, 6):
    types[f"R7:{j}R3"] = construct_subs(7, [r3] * j)
types["R7:R3"] = types["R7:1R3"]

types["R7:R5"] = construct_outer(7, [types["R5"]])
types["R7:R5,R3"] = construct_outer(7, [types["R5"], types["R3"]])
types["R7:R5,2R3"] = construct_outer(7, [types["R5"], types["R3"], types["R3"]])
types["R7:(R5:R3)"] = construct_outer(7, [types["R5:R3"]])
types["R7:(R5:R3),R3"] = construct_outer(7, [types["R5:R3"], types["R3"]])
types["R7:(R5:2R3)"] = construct_outer(7, [types["R5:2R3"]])
types["R11:R3"] = construct_outer(11, [types["R3"]])

# Table 1 of Poonen-Rubinstein.
assert len(types["R2"]) == 1
assert len(types["R3"]) == 1
assert len(types["R5"]) == 1
assert len(types["R5:R3"]) == 1
assert len(types["R5:2R3"]) == 2
assert len(types["R7"]) == 1
assert len(types["R5:3R3"]) == 2
assert len(types["R7:R3"]) == 1
assert len(types["R5:4R3"]) == 1
assert len(types["R7:2R3"]) == 3
assert len(types["R7:3R3"]) == 5
assert len(types["R7:R5"]) == 1
assert len(types["R7:4R3"]) == 5
assert len(types["R7:R5,R3"]) == 6
assert len(types["R7:(R5:R3)"]) == 6
assert len(types["R11"]) == 1
assert [len(types[x]) for x in (
    "R7:5R3",
    "R7:R5,2R3",
    "R7:(R5:R3),R3",
    "R7:(R5:2R3)",
    "R11:R3",
)] == [3, 15, 36, 14, 1]

# Table 2 of Poonen-Rubinstein: all decompositions of weight 12.
table2 = [
    ["R7:5R3"],
    ["R7:R5,2R3"],
    ["R7:(R5:R3),R3"],
    ["R7:(R5:2R3)"],
    ["R11:R3"],
    ["R7:3R3", "R2"],
    ["R7:R5", "R2"],
    ["R5:4R3", "R3"],
    ["R7:2R3", "R3"],
    ["R5:3R3", "R2", "R2"],
    ["R7:R3", "R2", "R2"],
    ["R5:2R3", "R5"],
    ["R7", "R5"],
    ["R5:2R3", "R3", "R2"],
    ["R7", "R3", "R2"],
    ["R5:R3", "R5:R3"],
    ["R5:R3", "R3", "R3"],
    ["R5:R3", "R2", "R2", "R2"],
    ["R5", "R5", "R2"],
    ["R5", "R3", "R2", "R2"],
    ["R3", "R3", "R3", "R3"],
    ["R3", "R3", "R2", "R2", "R2"],
    ["R2", "R2", "R2", "R2", "R2", "R2"],
]
assert len(table2) == 23


@lru_cache(None)
def variants(t):
    return tuple(sorted(types[t]))


def conj_canon(rel):
    return canon_rot(tuple(mod1(-x) for x in rel))


@lru_cache(None)
def conj_map(t):
    v = variants(t)
    pos = {x: i for i, x in enumerate(v)}
    return tuple(pos[conj_canon(x)] for x in v)


def rotate(rel, t):
    return tuple(sorted(mod1(x + t) for x in rel))


def self_rots(rel):
    cand = set()
    for a in rel:
        for b in rel:
            s = mod1(-(a + b))
            cand.add(mod1(s / 2))
            cand.add(mod1(s / 2 + F(1, 2)))
    return tuple(sorted(t for t in cand if Counter(rotate(rel, t)) == Counter(mod1(-x) for x in rotate(rel, t))))


@lru_cache(None)
def self_relations(t, i):
    rel = variants(t)[i]
    return tuple(sorted(set(rotate(rel, x) for x in self_rots(rel))))


def stable_structures(comp):
    out = set()
    vlists = [range(len(variants(t))) for t in comp]
    for vv in product(*vlists):
        used = [False] * len(comp)

        def rec(sr, pb):
            try:
                i = next(j for j in range(len(comp)) if not used[j])
            except StopIteration:
                out.add((tuple(sorted(sr)), tuple(sorted(pb))))
                return
            t, vi = comp[i], vv[i]
            if conj_map(t)[vi] == vi:
                for rr in self_relations(t, vi):
                    used[i] = True
                    rec(sr + list(rr), pb)
                    used[i] = False
            for j in range(i + 1, len(comp)):
                if used[j] or comp[j] != t:
                    continue
                if vv[j] == conj_map(t)[vi]:
                    used[i] = used[j] = True
                    r = variants(t)[vi]
                    rec(sr, pb + [min(canon_rot(r), conj_canon(r))])
                    used[i] = used[j] = False

        rec([], [])
    return out


def conjugate_pairs(rel):
    c = Counter(mod1(x) for x in rel)
    pairs = []
    for x in (F(0), F(1, 2)):
        if c[x] % 2:
            return None
        pairs += [(x, x)] * (c[x] // 2)
        c[x] = 0
    seen = set()
    for x in sorted(c):
        if c[x] == 0 or x in seen:
            continue
        y = mod1(-x)
        if c[x] != c[y]:
            return None
        pairs += [(x, y)] * c[x]
        seen |= {x, y}
    return pairs


def const_choices(sr):
    pairs = conjugate_pairs(sr)
    if pairs is None:
        return None
    return [[(None, 0, 2 * a)] if a == b else [(None, 0, 2 * a), (None, 0, 2 * b)] for a, b in pairs]


def form_choices(sr, pb):
    out = const_choices(sr)
    if out is None:
        return []
    for j, rel in enumerate(pb):
        for r in rel:
            out.append([(j, 1, 2 * r), (j, -1, -2 * r)])
    assert len(out) == 6
    return out


def lift(raw, side):
    lo, hi = (F(-3, 2), F(1, 2)) if side == "L" else (F(-1, 2), F(3, 2))
    z0 = (raw - (lo + hi) / 2) // 2
    for z in range(int(z0) - 2, int(z0) + 3):
        x = raw - 2 * z
        if lo < x < hi:
            return x
    return None


def floor_fraction(x):
    return x.numerator // x.denominator


def ceil_fraction(x):
    return -floor_fraction(-x)


def z_values(coeff, const, target):
    lo = hi = const
    for a in coeff:
        if a >= 0:
            hi += 2 * a
        else:
            lo += 2 * a
    z0 = ceil_fraction((lo - target) / 2)
    z1 = floor_fraction((hi - target) / 2)
    return range(z0, z1 + 1)


def solve_assignment(forms, sides):
    vars0 = sorted({v for v, _, _ in forms if v is not None})
    pos = {v: i for i, v in enumerate(vars0)}
    k = len(vars0)
    assert k <= 2  # true for the first 22 types of Table 2

    al = [F(0)] * k
    ar = [F(0)] * k
    cl = cr = F(0)
    for (v, s, c), side in zip(forms, sides):
        if side == "L":
            cl += c
            if v is not None:
                al[pos[v]] += s
        else:
            cr += c
            if v is not None:
                ar[pos[v]] += s

    out = set()
    for zl in z_values(al, cl, F(-1, 2)):
        bl = F(-1, 2) + 2 * zl - cl
        for zr in z_values(ar, cr, F(5, 2)):
            br = F(5, 2) + 2 * zr - cr

            if k == 0:
                if bl or br:
                    continue
                q = []
            elif k == 1:
                a, b = al[0], ar[0]
                if a:
                    q0 = bl / a
                    if b * q0 != br:
                        continue
                elif b:
                    q0 = br / b
                    if a * q0 != bl:
                        continue
                else:
                    if bl or br:
                        continue
                    # A free parameter would remain. In the first 22 types
                    # every such case has a zero angle; detect it below.
                    q0 = None
                if q0 is None:
                    if any(v is None and lift(c, side) is None for (v, _, c), side in zip(forms, sides)):
                        continue
                    raise AssertionError("unexpected admissible family before 6R2")
                if not (0 <= q0 < 2):
                    continue
                q = [q0]
            else:
                a, b = al
                c, d = ar
                det = a * d - b * c
                if det:
                    q0 = (bl * d - b * br) / det
                    q1 = (a * br - bl * c) / det
                    if not (0 <= q0 < 2 and 0 <= q1 < 2):
                        continue
                    q = [q0, q1]
                else:
                    if a * br != c * bl or b * br != d * bl:
                        continue
                    # The only rank-deficient cases among the first 22
                    # Table 2 types force alpha = 1/2 on the left or
                    # alpha = 3/2 on the right, hence a zero angle.
                    if any(v is None and lift(c0, side) is None for (v, _, c0), side in zip(forms, sides)):
                        continue
                    raise AssertionError("unexpected admissible family before 6R2")

            left, right = [], []
            ok = True
            for (v, s, c0), side in zip(forms, sides):
                raw = c0 if v is None else s * q[pos[v]] + c0
                alpha = lift(raw, side)
                if alpha is None:
                    ok = False
                    break
                if side == "L":
                    left.append((F(1, 2) - alpha) / 2)
                else:
                    right.append((F(3, 2) - alpha) / 2)
            if not ok or len(left) != 3 or len(right) != 3:
                continue
            if sum(left) != 1 or sum(right) != 1:
                continue
            left = tuple(sorted(left))
            right = tuple(sorted(right))
            if left != right:
                out.add(tuple(sorted((left, right))))
    return out


sporadic = set()
for comp in table2[:-1]:
    for sr, pb in stable_structures(tuple(comp)):
        choices = form_choices(sr, pb)
        for forms in product(*choices):
            forms = tuple(forms)
            for li in combinations(range(6), 3):
                sides = ["R"] * 6
                for i in li:
                    sides[i] = "L"
                sporadic |= solve_assignment(forms, tuple(sides))

expected = {
    tuple(sorted(((F(1, 12), F(5, 12), F(1, 2)), (F(1, 8), F(1, 4), F(5, 8))))),
    tuple(sorted(((F(1, 30), F(11, 30), F(3, 5)), (F(1, 15), F(1, 5), F(11, 15))))),
    tuple(sorted(((F(2, 15), F(2, 5), F(7, 15)), (F(1, 5), F(7, 30), F(17, 30))))),
}
assert sporadic == expected

print("Table 1 reconstructed: OK")
print("Table 2 types:", len(table2))
print("First 22 types: exactly three nontrivial solutions")
for pair in sorted(sporadic):
    print(pair)
print("Type 23 is 6R2 and is handled algebraically in the proof note.")
