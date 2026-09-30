# -*- coding: utf-8 -*-
"""
08_geometria_r3.py  --  Paso 0 de R3 (Etapa 1): patrones (orden, signo) de un R3 GEOMETRICO REAL.

Modelo (sin dependencias, aritmetica entera/Fraction):
  * Tres rectas en posicion general que forman un triangulo:
        l0: y = 0        dir base (1, 0)
        l1: x = 0        dir base (0, 1)
        l2: x + y = c    dir base (1,-1)          c = +1 (cara "antes") o c = -1 (cara "despues")
    Pasar de c=+1 a c=-1 es mover la hebra l2 sobre el cruce (0,0) de l0 y l1: un R3.
  * Cada recta se orienta con eps_i = +-1 (2^3 = 8 orientaciones; 4 modulo inversion global).
  * "Etiquetado": la hebra abstracta k (k = 0,1,2 del codigo de Gauss) es la recta fisica lab[k]
    (6 etiquetados, que incluyen las dos quiralidades del triangulo).
  * Alturas fijas h[k] (permutacion de 0,1,2): la hebra con mayor h pasa por encima.
  * Signo del cruce {k,j}: producto cruzado (dir del paso superior) x (dir del paso inferior);
    positivo si > 0 (el cruce estandar: sup (1,1), inf (-1,1) da +2 > 0).
  * Orden de la hebra k: recorriendo la recta en su sentido, cual de sus dos cruces va primero.
    Codificacion de Lean: o[k] = False si el primer cruce de la hebra k es con la hebra (k+1)%3,
    o[k] = True si es con la hebra (k+2)%3.
  * Cruce {k,j} se indexa por (k+j)%3  ({0,1}->1, {0,2}->2, {1,2}->0).

Resultado clave (comprobado por asserts al ejecutar):
  1. Las dos caras (c=+1 y c=-1) tienen los MISMOS signos y las ordenes o complementados (!o).
  2. Se enumeran los 6*8*6 = 288 (etiquetado, orientacion, alturas) y se recogen los pares
     (o, s) distintos.  El conjunto V es cerrado por o -> !o y por s -> !s.
  3. Comprobacion numerica INDEPENDIENTE (implementacion propia del corchete de estados en
     Fraction, con A=2 y A=3) en diagramas de Gauss aleatorios: el corchete es invariante EXACTAMENTE
     para (o,s) en V; y falla (control negativo) cuando (o,s) no esta en V.

La tabla se imprime al ejecutar: `python 08_geometria_r3.py`.
"""
from fractions import Fraction
from itertools import permutations, product
import random

LINES = {  # (punto, direccion base) ; l2 depende de c
    0: lambda c: ((0, 0), (1, 0)),
    1: lambda c: ((0, 0), (0, 1)),
    2: lambda c: ((c, 0), (1, -1)),
}


def cross(u, v):
    return u[0] * v[1] - u[1] * v[0]


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]


def intersect(p, d, q, e):
    # p + t d = q + s e   ->  t = cross(q-p, e) / cross(d, e)
    den = cross(d, e)
    assert den != 0
    t = Fraction(cross((q[0] - p[0], q[1] - p[1]), e), den)
    return (p[0] + t * d[0], p[1] + t * d[1])


def config(lab, eps, h, c):
    """Devuelve (o, s): o[k] orden de la hebra k; s[idx] signo (True = positivo) del cruce idx=(k+j)%3."""
    phys = {}
    for k in range(3):
        p, d = LINES[lab[k]](c)
        phys[k] = (p, (eps[k] * d[0], eps[k] * d[1]))
    o = [None] * 3
    for k in range(3):
        p, d = phys[k]
        ts = {}
        for j in range(3):
            if j == k:
                continue
            q, e = phys[j]
            pt = intersect(p, d, q, e)
            ts[j] = dot(pt, d)
        first = min(ts, key=lambda j: ts[j])
        o[k] = (first == (k + 2) % 3)
    s = [None] * 3
    for k in range(3):
        for j in range(k + 1, 3):
            over, under = (k, j) if h[k] > h[j] else (j, k)
            s[(k + j) % 3] = cross(phys[over][1], phys[under][1]) > 0
    return tuple(o), tuple(s)


def enumerate_valid():
    V = {}
    for lab in permutations(range(3)):
        for eps in product((1, -1), repeat=3):
            for h in permutations(range(3)):
                oa, sa = config(lab, eps, h, +1)
                ob, sb = config(lab, eps, h, -1)
                assert sa == sb, "los signos deben conservarse en un R3"
                assert ob == tuple(not x for x in oa), "cada hebra invierte el orden"
                V.setdefault((oa, sa), []).append((lab, eps, h, +1))
                V.setdefault((ob, sb), []).append((lab, eps, h, -1))
    return V


# ---------------------------------------------------------------- corchete (independiente)
def bracket_word(w, A):
    """w: lista de (label, over, pos). Corchete de Kauffman por estados, como Word.bracket."""
    m = len(w)
    labels = sorted({l for (l, _, _) in w})
    over = {l: [i for i, (a, o, _) in enumerate(w) if a == l and o][0] for l in labels}
    under = {l: [i for i, (a, o, _) in enumerate(w) if a == l and not o][0] for l in labels}
    sign = {l: [p for (a, o, p) in w if a == l and o][0] for l in labels}
    n = len(labels)
    B = 1 / Fraction(A)
    d = -(Fraction(A) ** 2) - B ** 2
    total = Fraction(0)
    for st in product((True, False), repeat=n):
        parent = list(range(m))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb

        na = 0
        for l, a in zip(labels, st):
            o_, u_ = over[l], under[l]
            po, pu = (o_ - 1) % m, (u_ - 1) % m
            if a == sign[l]:
                union(po, u_)
                union(pu, o_)
            else:
                union(po, pu)
                union(o_, u_)
            na += a
        loops = len({find(x) for x in range(m)})
        total += Fraction(A) ** na * B ** (n - na) * d ** (loops - 1)
    return total


def random_word(n, rng):
    labs = list(range(1, n + 1))
    letters = [(l, True) for l in labs] + [(l, False) for l in labs]
    rng.shuffle(letters)
    sg = {l: rng.random() < 0.5 for l in labs}
    return [(l, o, sg[l]) for (l, o) in letters]


def insert_r3(w, pos, o, s, ovc):
    """Inserta el triangulo en las aristas pos[0..2] (posiciones de letras distintas: la arista
    k va de la letra pos[k] a la siguiente).  o[k]: orden de la hebra k (ver modulo).
    s[idx]: signo del cruce (k+j)%3; ovc[idx]: True si la letra con k<j es la superior."""
    base = max(l for (l, _, _) in w) + 1
    lab = {0: base + 0, 1: base + 1, 2: base + 2}   # cruce idx -> etiqueta

    def letter(k, j):
        idx = (k + j) % 3
        top = (ovc[idx] == (k < j))
        return (lab[idx], top, s[idx])

    ins = {}
    for k in range(3):
        a, b = (k + 1) % 3, (k + 2) % 3
        seq = [b, a] if o[k] else [a, b]
        ins[pos[k]] = [letter(k, j) for j in seq]
    out = []
    for i, x in enumerate(w):
        out.append(x)
        out.extend(ins.get(i, []))
    return out


def test_pattern(o, s, A, rng, trials=12):
    for _ in range(trials):
        n = rng.choice([1, 2, 3, 4])
        w = random_word(n, rng)
        if len(w) < 3:
            w = random_word(2, rng)
        pos = rng.sample(range(len(w)), 3)
        ovc = [rng.random() < 0.5 for _ in range(3)]
        w1 = insert_r3(w, pos, o, s, ovc)
        w2 = insert_r3(w, pos, tuple(not x for x in o), s, ovc)
        if bracket_word(w1, A) != bracket_word(w2, A):
            return False
    return True


def main():
    V = enumerate_valid()
    print("Pares (o, s) distintos realizados por un R3 geometrico:", len(V))
    print("  o = (o0,o1,o2): 0 = primer cruce con la hebra k+1, 1 = con la k+2;")
    print("  s = signos de los cruces de indice 0,1,2 (idx=(k+j)%3; 1 = positivo)")
    for (o, s), cfgs in sorted(V.items()):
        print("  o=%s s=%s  #configs=%d" % (tuple(int(x) for x in o),
                                             tuple(int(x) for x in s), len(cfgs)))
    for (o, s) in V:
        assert (tuple(not x for x in o), s) in V
        assert (o, tuple(not x for x in s)) in V
    rng = random.Random(20260929)
    good, bad = [], []
    for o in product((False, True), repeat=3):
        for s in product((False, True), repeat=3):
            r = all(test_pattern(o, s, A, rng) for A in (2, 3))
            (good if r else bad).append((o, s))
    print("Patrones (de 64) que conservan el corchete numericamente:", len(good))
    print("Coinciden EXACTAMENTE con los geometricos:", set(good) == set(V))
    print("Control negativo: %d patrones NO geometricos rompen la invariancia" % len(bad))
    assert set(good) == set(V)
    return V, good, bad


if __name__ == "__main__":
    main()
