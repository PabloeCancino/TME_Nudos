"""SONDA 17 (2026-10-01): fase 0 del plan de axiomas de Basic, axioma A7.

A7 = `minimal_isotopic_implies_rotation`:
    n = min_degree K1  ->  Isotopic <n,K1> <n,K2>  ->  exists k, K2 = rotate_knot k K1
(igualdad EXACTA de configuraciones indexadas por Fin n).

Replica EXACTAMENTE las definiciones de TMENudos/Basic.lean:
  * configuracion de n cruces: tupla indexada (o, u, pos) con o != u en Z/2n y cobertura total;
  * are_interlaced: intervalos [min,max] por valor, a1<a2<b1<b2 o a2<a1<b2<b1 (orden lineal);
  * is_adjacent p q: p+1=q o q+1=p (mod 2n);
  * is_R1_candidate K i: ady(o_i,u_i) y ningun otro cruce interlazado con i;
  * is_R2_candidate K a b: a!=b, ady(oa,ob), ady(ua,ub), interlazados, pos distintos;
  * is_R3_candidate K i j k: distintos, seis posiciones sin repetir, exactamente un patron de dos
    pares interlazados y el tercero no, y orden ciclico de [oi,oj,ok,ui,uj,uk];
  * is_R3_transition K K' i j k: candidato en K y SIME K = SIME K' (lista (razon, pos) indice a indice);
  * SIME K = [(razon_i, pos_i)], razon_i = (u_i - o_i) mod 2n;
  * rotate_knot k: suma k a over y under de cada cruce, conservando indice y signo.

Pregunta: ¿existe K1 con un triple R3-candidato y K2 con el mismo SIME que NO sea rotacion de K1?
Si es asi, la regla R3 une K1 con K2 y A7 (que exige K2 = rotate K1) solo puede ser cierto si K1 no
es minimo. Se informa ademas si la clase de K1 contiene configuraciones con candidato R1/R2.
Uso: python 17_sonda_A7.py
"""
import itertools
import sys
from collections import defaultdict


def matchings(avail):
    if not avail:
        yield []
        return
    x, rest = avail[0], avail[1:]
    for y in rest:
        r2 = [z for z in rest if z != y]
        for m in matchings(r2):
            yield [(x, y)] + m


def all_configs(n):
    """Todas las configuraciones indexadas: cada particion en n parejas, todas las asignaciones
    de pareja a indice, orientacion (over/under) y signo."""
    N = 2 * n
    out = []
    for m in matchings(list(range(N))):
        for perm in itertools.permutations(range(n)):
            for orient in itertools.product([False, True], repeat=n):
                for signs in itertools.product([False, True], repeat=n):
                    cr = [None] * n
                    for slot, (pair, o, s) in zip(perm, zip(m, orient, signs)):
                        a, b = pair
                        cr[slot] = (b, a, s) if o else (a, b, s)
                    out.append(tuple(cr))
    return sorted(set(out))


def interlaced(c1, c2):
    a1, b1 = min(c1[0], c1[1]), max(c1[0], c1[1])
    a2, b2 = min(c2[0], c2[1]), max(c2[0], c2[1])
    return (a1 < a2 < b1 < b2) or (a2 < a1 < b2 < b1)


def adjacent(p, q, N):
    return (p + 1) % N == q or (q + 1) % N == p


def is_r1_cand(K, i, N):
    c = K[i]
    return adjacent(c[0], c[1], N) and all(not interlaced(c, K[j]) for j in range(len(K)) if j != i)


def is_r2_cand(K, a, b, N):
    ca, cb = K[a], K[b]
    return (a != b and adjacent(ca[0], cb[0], N) and adjacent(ca[1], cb[1], N)
            and interlaced(ca, cb) and ca[2] != cb[2])


def cyclic_order(lst):
    for k in range(len(lst)):
        r = lst[k:] + lst[:k]
        if all(r[t] < r[t + 1] for t in range(len(r) - 1)):
            return True
    return False


def is_r3_cand(K, i, j, k):
    if len({i, j, k}) < 3:
        return False
    ci, cj, ck = K[i], K[j], K[k]
    six = [ci[0], cj[0], ck[0], ci[1], cj[1], ck[1]]
    if len(set(six)) < 6:
        return False
    ij, jk, ik = interlaced(ci, cj), interlaced(cj, ck), interlaced(ci, ck)
    pat = (ij and jk and not ik) or (ij and ik and not jk) or (ik and jk and not ij)
    return pat and cyclic_order(six)


def sime(K, N):
    return tuple(((c[1] - c[0]) % N, c[2]) for c in K)


def rotate(K, k, N):
    return tuple(((c[0] + k) % N, (c[1] + k) % N, c[2]) for c in K)


def has_r3_triple(K):
    n = len(K)
    return [(i, j, k) for i, j, k in itertools.permutations(range(n), 3) if is_r3_cand(K, i, j, k)]


def main(n):
    N = 2 * n
    configs = all_configs(n)
    print(f"n={n}: {len(configs)} configuraciones indexadas")
    by_sime = defaultdict(list)
    for K in configs:
        by_sime[sime(K, N)].append(K)
    with_r3 = [K for K in configs if has_r3_triple(K)]
    print(f"  con algun triple R3-candidato: {len(with_r3)}")
    bad = []  # (K1, K2) con R3 K1->K2 (mismo SIME) y K2 no rotacion de K1
    for K1 in with_r3:
        rots = {rotate(K1, k, N) for k in range(N)}
        for K2 in by_sime[sime(K1, N)]:
            if K2 not in rots:
                bad.append((K1, K2))
    print(f"  pares (K1,K2) unidos por R3 con K2 NO rotacion de K1: {len(bad)}")
    k1s = {b[0] for b in bad}
    print(f"  K1 distintos con ese defecto: {len(k1s)}")
    # ¿es K1 'minimo' al menos localmente? sin candidatos R1/R2 en K1 ni en su clase SIME
    def reducible_candidates(K):
        r1 = any(is_r1_cand(K, i, N) for i in range(len(K)))
        r2 = any(is_r2_cand(K, a, b, N) for a in range(len(K)) for b in range(len(K)))
        return r1 or r2
    irr = [K1 for K1 in k1s if not reducible_candidates(K1)]
    print(f"  de ellos, sin candidato R1/R2 directo en K1: {len(irr)}")
    clase_limpia = [K1 for K1 in irr
                    if all(not reducible_candidates(K) for K in by_sime[sime(K1, N)])]
    print(f"  y con TODA su clase SIME sin candidato R1/R2: {len(clase_limpia)}")
    for K1 in clase_limpia[:3]:
        K2 = next(K for K in by_sime[sime(K1, N)] if K not in {rotate(K1, k, N) for k in range(N)})
        print("   ejemplo K1 =", K1, "| K2 =", K2, "| triples R3 de K1:", has_r3_triple(K1)[:2])
    return len(bad), len(clase_limpia)


if __name__ == "__main__":
    for n in (3, 4):
        main(n)
