"""SONDA 20 (2026-10-01): con transiciones R1/R2 FIELES (biyectivas), ¿se cumplen A6 y A7 para n = 3?

Modelo de `Isotopic` reparado, sobre configuraciones INDEXADAS (como `RationalConfiguration n`):
  * configuracion de grado d: tupla de d cruces (o, u, s), o != u en Z/2d, cobertura total;
  * rotacion: suma k a todas las posiciones (conserva indices y signos);
  * R1-reduccion en el indice i si `is_R1_candidate` (posiciones adyacentes y ningun otro cruce interlazado):
    se quita el cruce i; las posiciones restantes se renumeran por rango (orden lineal), los indices saltan i;
  * R2-reduccion en (a,b) si `is_R2_candidate` (superiores adyacentes, inferiores adyacentes, interlazados,
    signos opuestos): se quitan los dos cruces; renumeracion por rango; los indices saltan a y b;
  * R3: VACUO en el modelo (sondas 17), no se incluye;
  * las expansiones son las inversas (simetria de `Isotopic`).
La clase de K es la cerradura bajo rotaciones, reducciones y expansiones, acotada a grado <= CAP.

Preguntas (n = 3, CAP = 5):
  A6: si K no tiene candidatos R1/R2 (irreducible), ¿su clase acotada contiene grados < 3?  (si si, A6 falso)
  A7: si K1 es irreducible, ¿todo K2 de grado 3 en su clase es rotacion exacta de K1?        (si no, A7 falso)
Uso: python 20_transiciones_fieles.py
"""
import itertools
import sys
from collections import deque

CAP = 5


def interlaced(c1, c2):
    a1, b1 = min(c1[0], c1[1]), max(c1[0], c1[1])
    a2, b2 = min(c2[0], c2[1]), max(c2[0], c2[1])
    return (a1 < a2 < b1 < b2) or (a2 < a1 < b2 < b1)


def adj(p, q, N):
    return (p + 1) % N == q or (q + 1) % N == p


def r1_cands(K):
    N = 2 * len(K)
    return [i for i, c in enumerate(K)
            if adj(c[0], c[1], N) and all(not interlaced(c, d) for j, d in enumerate(K) if j != i)]


def r2_cands(K):
    N = 2 * len(K)
    out = []
    for a, b in itertools.permutations(range(len(K)), 2):
        ca, cb = K[a], K[b]
        if (adj(ca[0], cb[0], N) and adj(ca[1], cb[1], N) and interlaced(ca, cb) and ca[2] != cb[2]):
            out.append((a, b))
    return out


def remove(K, idxs):
    """Quita los cruces `idxs` y renumera las posiciones restantes por rango."""
    gone = sorted(p for i in idxs for p in (K[i][0], K[i][1]))
    rank = lambda x: x - sum(1 for g in gone if g < x)
    return tuple((rank(c[0]), rank(c[1]), c[2]) for i, c in enumerate(K) if i not in idxs)


def rotations(K):
    N = 2 * len(K)
    return {tuple(((c[0] + k) % N, (c[1] + k) % N, c[2]) for c in K) for k in range(N)}


def insert_positions(K, gaps):
    """Desplaza las posiciones de K abriendo huecos de 2 posiciones en cada gap (gap g = antes de la
    posicion g). `gaps` ordenados y distintos; devuelve (K desplazada, lista de posiciones libres)."""
    def shift(x):
        return x + 2 * sum(1 for g in gaps if g <= x)
    K2 = tuple((shift(c[0]), shift(c[1]), c[2]) for c in K)
    free = [(g + 2 * t) for t, g in enumerate(gaps)]  # primera posicion del hueco t
    return K2, free


def expansions(K, cap=CAP):
    """Todas las K'' de grado len(K)+1 y len(K)+2 que se reducen a K por una transicion fiel."""
    d = len(K)
    N = 2 * d
    out = set()
    # R1: hueco de 2 posiciones en gap g (0..N), nuevo cruce adyacente, indice t, orientacion, signo
    for g in range(N + 1):
        K2, free = insert_positions(K, [g])
        p = free[0]
        for t in range(d + 1):
            for (o, u) in ((p, p + 1), (p + 1, p)):
                for s in (False, True):
                    new = list(K2)
                    new.insert(t, (o, u, s))
                    new = tuple(new)
                    if t in r1_cands(new) and remove(new, [t]) == K:
                        out.add(new)
    # R2: dos huecos (gaps g1 <= g2), dos cruces nuevos
    if d + 2 <= cap:
        for g1 in range(N + 1):
            for g2 in range(g1, N + 1):
                gaps = [g1, g2]
                if g1 == g2:
                    # dos huecos consecutivos = un hueco de 4: se contempla como g1 con 4 posiciones
                    K2 = tuple((c[0] + (4 if g1 <= c[0] else 0), c[1] + (4 if g1 <= c[1] else 0), c[2]) for c in K)
                    free = [g1, g1 + 2]
                else:
                    K2, free = insert_positions(K, gaps)
                (p, q) = free
                for (po, pu) in (((p, p + 1)), ((p + 1, p))):
                    pass
                for ovs in ((p, p + 1), (p + 1, p)):
                    for uns in ((q, q + 1), (q + 1, q)):
                        for s in (False, True):
                            ca = (ovs[0], uns[0], s)
                            cb = (ovs[1], uns[1], not s)
                            for ta in range(d + 1):
                                for tb in range(d + 2):
                                    new = list(K2)
                                    new.insert(ta, ca)
                                    new.insert(tb, cb)
                                    new = tuple(new)
                                    # los indices de a y b en `new`
                                    ia = ta if tb > ta else ta + 1
                                    ib = tb if tb <= ta else tb
                                    # localizar por contenido
                                    try:
                                        ia = new.index(ca)
                                        ib = new.index(cb)
                                    except ValueError:
                                        continue
                                    if ia == ib:
                                        continue
                                    if (ia, ib) in r2_cands(new) and remove(new, [ia, ib]) == K:
                                        out.add(new)
    return out


def canon(K):
    return min(rotations(K))


def canon_set(K):
    """Clase de rotacion del diagrama SIN indices (conjunto de cruces)."""
    return min(tuple(sorted(R)) for R in rotations(K))


def classify(K, cap=CAP):
    """Clase de K bajo rotacion, R1/R2 y sus inversas, con UN representante canonico (minima rotacion)
    por clase de rotacion (las transiciones son equivariantes bajo rotacion)."""
    start = canon(K)
    seen = {start}
    dq = deque([start])
    while dq:
        X = dq.popleft()
        d = len(X)
        nxt = set()
        for i in r1_cands(X):
            if d - 1 >= 1:
                nxt.add(remove(X, [i]))
        for (a, b) in r2_cands(X):
            if d - 2 >= 1:
                nxt.add(remove(X, [a, b]))
        if d + 1 <= cap:
            nxt |= expansions(X, cap)
        for Y in nxt:
            c = canon(Y)
            if c not in seen:
                seen.add(c)
                dq.append(c)
        if len(seen) > 300000:
            print("   (cota de nodos alcanzada)", flush=True)
            break
    return seen


def configs(n):
    N = 2 * n
    from itertools import product

    def matchings(avail):
        if not avail:
            yield []
            return
        x, rest = avail[0], avail[1:]
        for y in rest:
            for m in matchings([z for z in rest if z != y]):
                yield [(x, y)] + m
    out = set()
    for m in matchings(list(range(N))):
        for perm in itertools.permutations(range(n)):
            for orient in product([False, True], repeat=n):
                for signs in product([False, True], repeat=n):
                    cr = [None] * n
                    for slot, (pair, o, s) in zip(perm, zip(m, orient, signs)):
                        a, b = pair
                        cr[slot] = (b, a, s) if o else (a, b, s)
                    out.add(tuple(cr))
    return out


def main():
    import random
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    sample = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else CAP
    allc = configs(n)
    irr = [K for K in allc if not r1_cands(K) and not r2_cands(K)]
    print(f"n={n}: {len(allc)} configuraciones indexadas, {len(irr)} irreducibles (sin candidatos)", flush=True)
    # un representante por clase de rotacion DEL DIAGRAMA sin indices
    by_set = {}
    for K in sorted(irr):
        by_set.setdefault(canon_set(K), K)
    reps = list(by_set.values())
    print(f"  {len(reps)} clases de rotacion (sin indices) de irreducibles", flush=True)
    if sample and sample < len(reps):
        random.seed(0)
        reps = random.sample(reps, sample)
        print(f"  muestra de {len(reps)} clases (semilla 0), cap de grado {cap}", flush=True)
    a6_bad, a7_real, tot, relabel_only = [], [], 0, 0
    for t, K in enumerate(reps):
        cls = classify(K, cap)
        tot += 1
        if t % 10 == 0:
            print(f"   ... {t}/{len(reps)}", flush=True)
        mind = min(len(X) for X in cls)
        deg_n = [X for X in cls if len(X) == n]
        if mind < n:
            a6_bad.append((K, mind))
        real = [X for X in deg_n if canon_set(X) != canon_set(K)]
        if real:
            a7_real.append((K, len(real), real[0]))
        elif len(deg_n) > 1:
            relabel_only += 1
    print(f"  A6 (irreducible => grado minimo n): contraejemplos {len(a6_bad)} de {tot}")
    for K, m in a6_bad[:3]:
        print("     ", K, "-> clase alcanza grado", m)
    print(f"  A7 salvo permutacion de indices: diagramas realmente distintos en la clase: {len(a7_real)} de {tot}")
    print(f"  clases cuya unica diferencia son reetiquetados de indices: {relabel_only} de {tot}")
    for K, c, X in a7_real[:4]:
        print("     DIAGRAMA DISTINTO:", K, "|", c, "p.ej.", X)


if __name__ == "__main__":
    main()
