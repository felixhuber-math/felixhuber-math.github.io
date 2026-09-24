from sympy import Poly, cyclotomic_poly, symbols

x = symbols("x")


def a(n):
    return ((n*n + 6)//12
            - ((n - 4)//8 if n % 4 == 0 else 0)
            - (1 if n % 24 == 0 else 0)
            - (2 if n % 30 == 0 else 0))


def reductions(n):
    p = Poly(cyclotomic_poly(n, x), x)
    c = [int(p.nth(i)) for i in range(p.degree())]
    d = p.degree()
    r = []
    for k in range(n):
        if k < d:
            v = [0]*d
            v[k] = 1
        else:
            v = [0]*d
            for j, z in enumerate(c):
                if z:
                    w = r[k - d + j]
                    for h, y in enumerate(w):
                        v[h] -= z*y
        r.append(tuple(v))
    return r


def exact_count(n):
    r = reductions(n)
    d = len(r[0])
    seen = set()
    for u in range(1, n//3 + 1):
        for v in range(u, (n - u)//2 + 1):
            w = n - u - v
            ru, rv, rw = r[u], r[v], r[w]
            rnu, rnv, rnw = r[n - u], r[n - v], r[n - w]
            seen.add(tuple(ru[h] + rv[h] + rw[h] - rnu[h] - rnv[h] - rnw[h]
                           for h in range(d)))
    return len(seen)


def tri(t):
    return tuple(sorted(t))


def predicted_pairs(n):
    e = set()
    if n % 4 == 0:
        m = n//4
        for k in range(1, m):
            p = tri((k, 2*m - 2*k, 2*m + k))
            q = tri((2*k, m - k, 3*m - k))
            if p != q:
                e.add(tuple(sorted((p, q))))
    if n % 24 == 0:
        h = n//24
        e.add(tuple(sorted((tri((2*h, 10*h, 12*h)), tri((3*h, 6*h, 15*h))))))
    if n % 30 == 0:
        h = n//30
        e.add(tuple(sorted((tri((h, 11*h, 18*h)), tri((2*h, 6*h, 22*h))))))
        e.add(tuple(sorted((tri((4*h, 12*h, 14*h)), tri((6*h, 7*h, 17*h))))))
    return e


for n in range(3, 301):
    assert exact_count(n) == a(n)
print("Exact cyclotomic count, n = 3..300: OK")

for n in (360, 600, 720):
    assert exact_count(n) == a(n)
print("Exact cyclotomic count, selected n up to 720: OK")

for n in range(3, 10001):
    e = predicted_pairs(n)
    c = ((n - 4)//8 if n % 4 == 0 else 0) + (1 if n % 24 == 0 else 0) + 2*(1 if n % 30 == 0 else 0)
    assert len(e) == c
    deg = {}
    for p, q in e:
        deg[p] = deg.get(p, 0) + 1
        deg[q] = deg.get(q, 0) + 1
    assert max(deg.values(), default=0) <= 1
print("Predicted collision pairs are distinct, n = 3..10000: OK")
