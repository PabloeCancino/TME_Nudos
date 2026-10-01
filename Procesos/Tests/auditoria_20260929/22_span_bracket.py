"""SONDA 22 (2026-10-01), camino (B), fase B1: ¿el span del corchete de Kauffman es 4n para los diagramas
alternantes planares REDUCIDOS, y menor en los no reducidos?

Diagrama alternante: pasos superiores en todas las posiciones pares o todas las impares (como en las sondas 18b/19).
REDUCIDO = sin cuerdas aisladas (una cuerda aislada, sin ninguna entrelazada, es un cruce nugatorio).
Se mide: span = grado maximo - grado minimo del corchete <D> en la variable A (misma convencion que
Etapa1_GaussWord.lean y la sonda 19); y los circulos s_A y s_B de los estados todo-A y todo-B.
Se comprueba:  (i) reducido y conexo  =>  span = 4n   y   s_A + s_B = n + 2;
               (ii) no reducido  =>  span < 4n.
Uso: python 22_span_bracket.py [nmax]
"""
import itertools
import sys
import importlib.util

spec = importlib.util.spec_from_file_location("s19", "19_sonda_jones_flype.py")
s19 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s19)
s18 = s19.s18


def bracket_and_circles(cfg, N):
    """Devuelve (polinomio <D> como dict, circulos del estado todo-A, circulos del estado todo-B)."""
    n = len(cfg)
    prev = lambda j: (j - 1) % N
    total = {}
    sA = sB = None
    for st in itertools.product([True, False], repeat=n):
        pairs = []
        for (o, u, s), a in zip(cfg, st):
            orient = (a == s)
            if orient:
                pairs += [(prev(o), u), (prev(u), o)]
            else:
                pairs += [(prev(o), prev(u)), (o, u)]
        loops = s19.components(N, pairs)
        if all(st):
            sA = loops
        if not any(st):
            sB = loops
        nA = sum(st)
        term = s19.pmul({nA - (n - nA): 1}, s19.ppow(s19.D, loops - 1))
        total = s19.padd(total, term)
    return total, sA, sB


def isolated_chords(cfg, N):
    """Numero de cuerdas sin ninguna otra entrelazada (nugatorias)."""
    cnt = 0
    for c in cfg:
        if not any(s18.interlaced(c, d) for d in cfg if d is not c and d[:2] != c[:2]):
            cnt += 1
    return cnt


def run(n):
    N = 2 * n
    seen = set()
    stats = {"red": 0, "red_ok": 0, "red_bad": [], "nored": 0, "nored_lt": 0, "nored_bad": [], "sAsB_bad": []}
    for parity in (0, 1):
        overs = [p for p in range(N) if p % 2 == parity]
        unders = [p for p in range(N) if p % 2 != parity]
        for perm in itertools.permutations(unders):
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for o, u, s in zip(overs, perm, signs)))
                if cfg in seen:
                    continue
                seen.add(cfg)
                if not s18.planar(N, cfg):
                    continue
                poly, sA, sB = bracket_and_circles(cfg, N)
                span = (max(poly) - min(poly)) if poly else 0
                iso = isolated_chords(cfg, N)
                if iso == 0:
                    stats["red"] += 1
                    if span == 4 * n:
                        stats["red_ok"] += 1
                    elif len(stats["red_bad"]) < 3:
                        stats["red_bad"].append((cfg, span))
                    if sA + sB != n + 2 and len(stats["sAsB_bad"]) < 3:
                        stats["sAsB_bad"].append((cfg, sA, sB))
                else:
                    stats["nored"] += 1
                    if span < 4 * n:
                        stats["nored_lt"] += 1
                    elif len(stats["nored_bad"]) < 3:
                        stats["nored_bad"].append((cfg, span, iso))
    print(f"n={n}: alternantes planares reducidos {stats['red']} (span = 4n en {stats['red_ok']}); "
          f"no reducidos {stats['nored']} (span < 4n en {stats['nored_lt']})", flush=True)
    for e in stats["red_bad"]:
        print("   REDUCIDO con span != 4n:", e)
    for e in stats["sAsB_bad"]:
        print("   REDUCIDO con sA+sB != n+2:", e)
    for e in stats["nored_bad"]:
        print("   NO reducido con span >= 4n:", e)


if __name__ == "__main__":
    for n in range(2, (int(sys.argv[1]) if len(sys.argv) > 1 else 6) + 1):
        run(n)
