"""SONDA 19 (2026-10-01): ¿es A7 falso incluso en la teoria clasica de nudos? (diagramas distintos del mismo nudo)

A7 = `minimal_isotopic_implies_rotation`: dos configuraciones minimas isotopicas son rotacion una de otra.
En teoria de nudos, dos diagramas alternantes reducidos del MISMO nudo pueden diferir por un FLYPE y no ser
isomorfos como diagramas (conjetura de Tait, probada). Si pasa, A7 es falso para la teoria clasica y no solo
para el modelo formal.

Prueba: se enumeran las configuraciones PLANARES, ALTERNANTES y SIN candidato R1/R2 (como en 18b) y se calcula
su polinomio de Jones (corchete de Kauffman por estados, misma convencion que Etapa1_GaussWord.lean:
aristas e_j de la posicion j a la j+1; suavizacion orientada une (e_{o-1}, e_u) y (e_{u-1}, e_o), la no
orientada une (e_{o-1}, e_{u-1}) y (e_o, e_u); cruce positivo: A = orientada, negativo: A = no orientada;
lazos = componentes conexas; Jones = (-A^3)^(-w) <D>). Se agrupa por Jones y se mira:
  * clases de ROTACION distintas con el mismo Jones;
  * y tras identificar tambien la REFLEXION (invertir el sentido de recorrido: p -> -p, mismo signo), que
    no es un cambio de nudo (solo reorientarlo): clases DIHEDRICAS distintas con el mismo Jones.
Si hay clases diedricas distintas con igual Jones y el mismo n, son candidatos a flype (o a nudos distintos
con igual Jones). Se informa tambien si sus SIMEcic coinciden (si coinciden, la reconstruccion las unificaria).
Uso: python 19_sonda_jones_flype.py [nmax]
"""
import itertools
import sys
from collections import defaultdict
import importlib.util

spec = importlib.util.spec_from_file_location("s18", "18_sonda_reconstruccion.py")
s18 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s18)


# ---------- polinomios de Laurent en A como dict {exp: coef} ----------
def padd(p, q):
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, 0) + c
        if r[e] == 0:
            del r[e]
    return r


def pmul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            r[e1 + e2] = r.get(e1 + e2, 0) + c1 * c2
    return {e: c for e, c in r.items() if c != 0}


def ppow(p, k):
    r = {0: 1}
    for _ in range(k):
        r = pmul(r, p)
    return r


D = {2: -1, -2: -1}  # d = -A^2 - A^-2


def components(m, pairs):
    parent = list(range(m))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in pairs:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    return len({find(x) for x in range(m)})


def jones(cfg, N):
    """cfg: tupla de (o, u, s) con s=True positivo. Devuelve el Jones como dict."""
    n = len(cfg)
    writhe = sum(1 if s else -1 for _, _, s in cfg)
    total = {}
    prev = lambda j: (j - 1) % N
    for st in itertools.product([True, False], repeat=n):  # True = suavizacion A
        pairs = []
        for (o, u, s), a in zip(cfg, st):
            orient = (a == s)  # A y positivo -> orientada; B y negativo -> orientada
            if orient:
                pairs += [(prev(o), u), (prev(u), o)]
            else:
                pairs += [(prev(o), prev(u)), (o, u)]
        loops = components(N, pairs)
        nA = sum(st)
        term = {nA - (n - nA): 1}
        term = pmul(term, ppow(D, loops - 1))
        total = padd(total, term)
    # (-A^3)^(-w)
    fac = {-3 * writhe: (-1) ** (abs(writhe))}
    return pmul(fac, total)


def reflect(cfg, N):
    return tuple(sorted(((-o) % N, (-u) % N, s) for o, u, s in cfg))


def dih_class(cfg, N):
    return min(s18.rot_class(cfg, N), s18.rot_class(reflect(cfg, N), N))


def run(n):
    N = 2 * n
    groups = defaultdict(lambda: defaultdict(set))  # jones -> dihclass -> {rotclasses}
    seen = set()
    for parity in (0, 1):
        overs = [p for p in range(N) if p % 2 == parity]
        unders = [p for p in range(N) if p % 2 != parity]
        for perm in itertools.permutations(unders):
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for o, u, s in zip(overs, perm, signs)))
                if cfg in seen:
                    continue
                seen.add(cfg)
                if not s18.planar(N, cfg) or s18.reducible_candidate(cfg, N):
                    continue
                j = tuple(sorted(jones(cfg, N).items()))
                groups[j][dih_class(cfg, N)].add(s18.rot_class(cfg, N))
    rot_classes = sum(len(rs) for g in groups.values() for rs in g.values())
    print(f"n={n}: clases de rotacion {rot_classes}, clases diedricas {sum(len(g) for g in groups.values())}, "
          f"valores de Jones distintos {len(groups)}")
    multi_dih = {j: g for j, g in groups.items() if len(g) > 1}
    multi_rot = {j: g for j, g in groups.items() if any(len(rs) > 1 for rs in g.values())}
    print(f"   Jones con >1 clase DIEDRICA (candidatos a flype / mutacion): {len(multi_dih)}")
    print(f"   Jones con una clase diedrica que contiene >1 clase de rotacion (reflexion): {len(multi_rot)}")
    for j, g in list(multi_dih.items())[:3]:
        reps = [sorted(rs)[0] for rs in g.values()]
        print("   ejemplo Jones", j[:3], "...  -> representantes:", reps[:2])
    return multi_dih


if __name__ == "__main__":
    for n in range(3, (int(sys.argv[1]) if len(sys.argv) > 1 else 6) + 1):
        run(n)
