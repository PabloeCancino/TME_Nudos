"""SONDA 29: en todo diagrama ALTERNANTE (planar o no), numero de caras (ciclos de sigma∘alpha, sonda 15) = s_A + s_B.
Es lo que demuestra `caras_eq_of_alternante` en Lean (SpanAlternante.lean). Comprobacion exhaustiva n <= 6 sobre las palabras alternantes."""
import itertools, sys, importlib.util
def load(n, f):
    sp = importlib.util.spec_from_file_location(n, f); m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m); return m
sys.argv = [sys.argv[0]]
s23 = load("s23", "23_desigualdad_genero.py"); s18 = s23.s18
tot = bad = 0
for n in range(1, 7):
    N = 2 * n
    t = b = 0
    for parity in (0, 1):
        overs = [p for p in range(N) if p % 2 == parity]
        unders = [p for p in range(N) if p % 2 != parity]
        for perm in itertools.permutations(unders):
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for o, u, s in zip(overs, perm, signs)))
                F = s18.faces(N, cfg)
                sA = s23.circles(cfg, N, True); sB = s23.circles(cfg, N, False)
                t += 1
                if F != sA + sB:
                    b += 1
    print(f"n={n}: alternantes {t}, caras != sA+sB en {b}", flush=True)
    tot += t; bad += b
print(f"TOTAL {tot}, contraejemplos {bad}")
