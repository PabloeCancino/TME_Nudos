"""SONDA 26 (2026-10-01), camino (B), etapa S3: la desigualdad de genero en su forma ABSTRACTA de tres involuciones.

Conjunto H de 4c extremos de aristas. Estructura fija en cada cruce (bloque de 4 extremos 4q..4q+3, en orden ciclico):
    a (suavizacion A)     = (0 1)(2 3)      b (suavizacion B) = (1 2)(3 0)      (y el paso por el cruce x = (0 2)(1 3));
    a y b son involuciones sin puntos fijos, y a∘b tiene todos sus ciclos de longitud 2.
eps = CUALQUIER involucion sin puntos fijos de H (que empareja los extremos de cada arista). Esto cubre todos los diagramas de Gauss
(orientables o no) con 'curvas' arbitrarias.
  s_a = numero de orbitas de <eps, a>;  s_b = numero de orbitas de <eps, b>;  k = numero de orbitas de <eps, a, b> (componentes conexas).
Tesis (a probar en Lean):   s_a + s_b  <=  c + 2k.
Ademas, relacion con permutaciones:  p = eps∘a,  q = eps∘b,  x = a∘b :  p^{-1}∘q = x  y  cyc(p) = 2 s_a,  cyc(q) = 2 s_b
(cyc = numero de ciclos, con puntos fijos); y el trio (p, x, q^{-1}) tiene producto 1 con k' orbitas, k <= k' <= 2k, y por la
desigualdad de Riemann-Hurwitz  cyc(p)+cyc(x)+cyc(q) <= |H| + 2k'.
Se comprueba exhaustivamente para c <= 4 (todas las eps) y por muestreo para c = 5, 6.
Uso: python 26_involuciones_abstracto.py
"""
import itertools
import random
import sys


def fpf_involutions(points):
    if not points:
        yield []
        return
    x, rest = points[0], points[1:]
    for y in rest:
        for m in fpf_involutions([z for z in rest if z != y]):
            yield [(x, y)] + m


def orbits(n, gens):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for g in gens:
        for i in range(n):
            ra, rb = find(i), find(g[i])
            if ra != rb:
                parent[ra] = rb
    return len({find(i) for i in range(n)})


def cycles(perm):
    n = len(perm)
    seen = [False] * n
    cnt = 0
    for i in range(n):
        if not seen[i]:
            cnt += 1
            j = i
            while not seen[j]:
                seen[j] = True
                j = perm[j]
    return cnt


def compose(f, g):  # f∘g
    return [f[g[i]] for i in range(len(f))]


def inverse(f):
    r = [0] * len(f)
    for i, v in enumerate(f):
        r[v] = i
    return r


def check(c, pairs, stats):
    n = 4 * c
    eps = [0] * n
    for x, y in pairs:
        eps[x] = y
        eps[y] = x
    a = [0] * n
    b = [0] * n
    for q in range(c):
        o = 4 * q
        for (u, v) in ((0, 1), (2, 3)):
            a[o + u], a[o + v] = o + v, o + u
        for (u, v) in ((1, 2), (3, 0)):
            b[o + u], b[o + v] = o + v, o + u
    s_a = orbits(n, [eps, a])
    s_b = orbits(n, [eps, b])
    k = orbits(n, [eps, a, b])
    stats["total"] += 1
    if s_a + s_b > c + 2 * k:
        stats["viola_desigualdad"] += 1
    # relacion con permutaciones
    p = compose(eps, a)
    q = compose(eps, b)
    x = compose(a, b)
    if cycles(p) != 2 * s_a or cycles(q) != 2 * s_b:
        stats["viola_ciclos"] += 1
    prod = compose(compose(p, x), inverse(q))
    if prod != list(range(n)):
        stats["producto_no_1"] += 1
    kp = orbits(n, [p, x, q])
    if not (k <= kp <= 2 * k):
        stats["viola_orbitas"] += 1
    if cycles(p) + cycles(x) + cycles(q) > n + 2 * kp:
        stats["viola_RH"] += 1
    if kp == 2 * k:
        stats["orientables"] += 1


def main():
    random.seed(0)
    for c in (1, 2, 3, 4):
        stats = dict(total=0, viola_desigualdad=0, viola_ciclos=0, producto_no_1=0, viola_orbitas=0, viola_RH=0, orientables=0)
        for pairs in fpf_involutions(list(range(4 * c))):
            check(c, pairs, stats)
        print(f"c={c} (exhaustivo): {stats}", flush=True)
    for c in (5, 6):
        stats = dict(total=0, viola_desigualdad=0, viola_ciclos=0, producto_no_1=0, viola_orbitas=0, viola_RH=0, orientables=0)
        for _ in range(60000):
            pts = list(range(4 * c))
            random.shuffle(pts)
            pairs = [(pts[2 * i], pts[2 * i + 1]) for i in range(2 * c)]
            check(c, pairs, stats)
        print(f"c={c} (muestra de 60000): {stats}", flush=True)


if __name__ == "__main__":
    main()
