"""SONDA 24 (2026-10-01), camino (B), etapa S5: ADECUACION de los alternantes planares.

Un diagrama es A-adecuado si, partiendo del estado todo-A, cambiar UNA sola suavizacion a B BAJA el numero de circulos
(s' = s_A - 1) para todo cruce; B-adecuado si, partiendo de todo-B, cambiar una a A baja los circulos (s' = s_B - 1).
Tesis: un alternante planar sin cuerdas aisladas (reducido) es A- y B-adecuado; si tiene una cuerda aislada, FALLA.
Se cuenta, para los alternantes planares de n <= 6: reducidos adecuados / reducidos no adecuados / no reducidos adecuados.
Uso: python 24_adecuacion.py [nmax]
"""
import itertools
import sys
import importlib.util

spec = importlib.util.spec_from_file_location("s22", "22_span_bracket.py")
s22 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s22)
s19 = s22.s19
s18 = s22.s18


def circles_state(cfg, N, st):
    prev = lambda j: (j - 1) % N
    pairs = []
    for (o, u, s), a in zip(cfg, st):
        orient = (a == s)
        if orient:
            pairs += [(prev(o), u), (prev(u), o)]
        else:
            pairs += [(prev(o), prev(u)), (o, u)]
    return s19.components(N, pairs)


def adequate(cfg, N):
    n = len(cfg)
    allA = [True] * n
    allB = [False] * n
    sA = circles_state(cfg, N, allA)
    sB = circles_state(cfg, N, allB)
    a_ok = b_ok = True
    for i in range(n):
        st = list(allA); st[i] = False
        if circles_state(cfg, N, st) != sA - 1:
            a_ok = False
        st = list(allB); st[i] = True
        if circles_state(cfg, N, st) != sB - 1:
            b_ok = False
    return a_ok, b_ok


def run(n):
    N = 2 * n
    seen = set()
    res = {"red_ad": 0, "red_noad": 0, "nored_ad": 0, "nored_noad": 0}
    ejemplos = []
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
                a_ok, b_ok = adequate(cfg, N)
                red = s22.isolated_chords(cfg, N) == 0
                key = ("red" if red else "nored") + ("_ad" if (a_ok and b_ok) else "_noad")
                res[key] += 1
                if red and not (a_ok and b_ok) and len(ejemplos) < 3:
                    ejemplos.append((cfg, a_ok, b_ok))
    print(f"n={n}: reducidos adecuados {res['red_ad']}, reducidos NO adecuados {res['red_noad']}, "
          f"no reducidos adecuados {res['nored_ad']}, no reducidos no adecuados {res['nored_noad']}", flush=True)
    for e in ejemplos:
        print("   REDUCIDO no adecuado:", e)


if __name__ == "__main__":
    for n in range(2, (int(sys.argv[1]) if len(sys.argv) > 1 else 6) + 1):
        run(n)
