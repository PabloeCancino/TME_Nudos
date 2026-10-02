"""SONDA 23 (2026-10-01), camino (B), etapa S3: la desigualdad de genero  s_A + s_B <= n + 2  para CUALQUIER diagrama de Gauss firmado
de UNA sola curva (planar o no), con n cruces.

s_A = circulos del estado todo-A, s_B = circulos del estado todo-B (misma convencion que Etapa1_GaussWord.lean y la sonda 19).
Se enumeran TODAS las palabras de Gauss con signos (emparejamiento x orientacion x signos), n <= 5, y se mide el maximo de
(s_A + s_B) - (n + 2). La tesis: ese maximo es 0 (la igualdad se da exactamente cuando la superficie de Turaev tiene genero 0), y la
paridad: s_A + s_B = n + 2 - 2g con g >= 0 entero, es decir (n + 2) - (s_A + s_B) es PAR y >= 0.
Se informa tambien cuantos diagramas son planares y alternantes con igualdad.
Uso: python 23_desigualdad_genero.py [nmax]
"""
import itertools
import sys
from collections import Counter
import importlib.util

spec = importlib.util.spec_from_file_location("s19", "19_sonda_jones_flype.py")
s19 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s19)
s18 = s19.s18


def matchings(avail):
    if not avail:
        yield []
        return
    x, rest = avail[0], avail[1:]
    for y in rest:
        for m in matchings([z for z in rest if z != y]):
            yield [(x, y)] + m


def circles(cfg, N, A_state):
    prev = lambda j: (j - 1) % N
    pairs = []
    for o, u, s in cfg:
        orient = (A_state == s)
        if orient:
            pairs += [(prev(o), u), (prev(u), o)]
        else:
            pairs += [(prev(o), prev(u)), (o, u)]
    return s19.components(N, pairs)


def run(n):
    N = 2 * n
    deficit = Counter()      # (n+2) - (sA+sB)
    planar_eq = planar_total = 0
    seen = set()
    for m in matchings(list(range(N))):
        for orient in itertools.product([False, True], repeat=n):
            ch = [(b, a) if o else (a, b) for (a, b), o in zip(m, orient)]
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for (o, u), s in zip(ch, signs)))
                if cfg in seen:
                    continue
                seen.add(cfg)
                sA = circles(cfg, N, True)
                sB = circles(cfg, N, False)
                d = (n + 2) - (sA + sB)
                deficit[d] += 1
                if s18.planar(N, cfg):
                    planar_total += 1
                    if d == 0:
                        planar_eq += 1
    items = sorted(deficit.items())
    ok = all(d >= 0 and d % 2 == 0 for d, _ in items)
    print(f"n={n}: diagramas {sum(deficit.values())}; distribucion de (n+2)-(sA+sB): {items}; "
          f"todo >= 0 y par: {ok}; planares {planar_total} (con igualdad {planar_eq})", flush=True)


if __name__ == "__main__":
    for n in range(1, (int(sys.argv[1]) if len(sys.argv) > 1 else 5) + 1):
        run(n)
