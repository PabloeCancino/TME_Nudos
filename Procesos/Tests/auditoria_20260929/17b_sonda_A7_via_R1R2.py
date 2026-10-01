"""SONDA 17b: A7 por la via de R1/R2 (R3 es vacuo, ver 17_sonda_A7.py).

Las transiciones R1/R2 de Basic.lean son 'existenciales en ambos sentidos': K' (grado n-1 o n-2)
es objetivo de K si el CONJUNTO de pares (razon, signo) de K' coincide con el de K sin los cruces
eliminados (no es una biyeccion ni respeta posiciones). Como Isotopic es simetrico y transitivo,
dos configuraciones K1, K2 del mismo grado quedan unidas si ambas son objetivo de un mismo K''.

Se calcula el grafo sobre nodos (grado, conjunto de (razon, signo)) para grados 1..4 con las
definiciones exactas de candidato R1/R2, y se pregunta: a) ¿hay K'' con 1 candidato R1 cuyo objetivo
tiene el mismo conjunto que una configuracion K1 de grado 3 que NO tenga candidatos?; b) desde ese nodo,
¿se alcanza un grado menor que 3 dentro de la cota? Si no, K1 es 'minima' en la cota y A7 exigiria que
todos los K2 de ese conjunto fueran rotaciones de K1: se cuenta cuantos no lo son.
"""
import itertools
import sys
from collections import defaultdict, deque
sys.path.insert(0, ".")
import importlib.util
spec = importlib.util.spec_from_file_location("s17", "17_sonda_A7.py")
s17 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s17)


def sset(K, N, drop=()):
    return frozenset(((c[1] - c[0]) % N, c[2]) for t, c in enumerate(K) if t not in drop)


def build(maxdeg):
    configs = {d: s17.all_configs(d) for d in range(1, maxdeg + 1)}
    realizable = {d: {sset(K, 2 * d) for K in configs[d]} for d in configs}
    edges = defaultdict(set)
    for d in range(1, maxdeg + 1):
        N = 2 * d
        for K in configs[d]:
            S = sset(K, N)
            for i in range(d):
                if s17.is_r1_cand(K, i, N) and d >= 2:
                    T = sset(K, N, (i,))
                    if T in realizable[d - 1]:
                        edges[(d, S)].add((d - 1, T)); edges[(d - 1, T)].add((d, S))
            for a in range(d):
                for b in range(d):
                    if s17.is_r2_cand(K, a, b, N) and d >= 3:
                        T = sset(K, N, (a, b))
                        if T in realizable[d - 2]:
                            edges[(d, S)].add((d - 2, T)); edges[(d - 2, T)].add((d, S))
    return configs, realizable, edges


def main():
    maxdeg = 4
    configs, realizable, edges = build(maxdeg)
    print("nodos con aristas:", len(edges))
    # nodos de grado 3 y su grado minimo alcanzable (en la cota maxdeg)
    seen_cls = {}
    res = []
    for S in realizable[3]:
        start = (3, S)
        if start in seen_cls:
            continue
        comp, dq = {start}, deque([start])
        while dq:
            x = dq.popleft()
            for y in edges.get(x, ()):
                if y not in comp:
                    comp.add(y); dq.append(y)
        for x in comp:
            seen_cls[x] = comp
        mind = min(d for d, _ in comp)
        res.append((S, mind, len(comp)))
    print("conjuntos de grado 3:", len(res))
    # K1 de grado 3 sin candidatos, cuyo conjunto S esta unido a un K'' de grado 4 (arista), y mind==3
    N = 6
    cnt_k1 = cnt_bad = 0
    ejemplos = []
    for S, mind, size in res:
        if mind < 3 or (3, S) not in edges:
            continue
        up = [y for y in edges[(3, S)] if y[0] == 4]
        if not up:
            continue
        ks = [K for K in configs[3] if sset(K, N) == S]
        for K1 in ks:
            if any(s17.is_r1_cand(K1, i, N) for i in range(3)) or any(
                    s17.is_r2_cand(K1, a, b, N) for a in range(3) for b in range(3)):
                continue
            rots = {s17.rotate(K1, k, N) for k in range(N)}
            outs = [K2 for K2 in ks if K2 not in rots]
            cnt_k1 += 1
            if outs:
                cnt_bad += 1
                if len(ejemplos) < 3:
                    ejemplos.append((K1, outs[0], sorted(S)))
    print(f"K1 de grado 3 sin candidatos, en clase con grado minimo 3 (cota 4) y unida a grado 4: {cnt_k1}")
    print(f"  de ellos con algun K2 (mismo conjunto, mismo grado) que NO es rotacion de K1: {cnt_bad}")
    for e in ejemplos:
        print("  ejemplo: K1 =", e[0], "| K2 =", e[1], "| conjunto (razon,signo) =", e[2])


main()
