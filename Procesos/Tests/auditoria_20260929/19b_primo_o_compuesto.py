"""SONDA 19b: de los pares con igual Jones y distinta clase diedrica (sonda 19), ¿cuantos son diagramas
COMPUESTOS (suma conexa: un intervalo ciclico propio cerrado bajo 'compañero de cuerda') y cuantos PRIMOS?
Un par PRIMO con igual Jones y diagramas no isomorfos es un candidato a FLYPE genuino."""
import sys, itertools
from collections import defaultdict
import importlib.util
spec = importlib.util.spec_from_file_location("s19", "19_sonda_jones_flype.py")
s19 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s19)
s18 = s19.s18

def partner_map(cfg):
    m = {}
    for o, u, s in cfg:
        m[o] = u; m[u] = o
    return m

def composite(cfg, N):
    """True si existe un intervalo ciclico propio I (2 <= |I| <= N-2) con partner(I) subconjunto de I."""
    m = partner_map(cfg)
    for start in range(N):
        for length in range(2, N - 1):
            I = {(start + t) % N for t in range(length)}
            if all(m[x] in I for x in I):
                return True
    return False

def run(n):
    N = 2 * n
    groups = defaultdict(lambda: defaultdict(list))
    seen = set()
    for parity in (0, 1):
        overs = [p for p in range(N) if p % 2 == parity]
        unders = [p for p in range(N) if p % 2 != parity]
        for perm in itertools.permutations(unders):
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for o, u, s in zip(overs, perm, signs)))
                if cfg in seen: continue
                seen.add(cfg)
                if not s18.planar(N, cfg) or s18.reducible_candidate(cfg, N): continue
                j = tuple(sorted(s19.jones(cfg, N).items()))
                groups[j][s19.dih_class(cfg, N)].append(cfg)
    prime_cnt = comp_cnt = 0
    for j, g in groups.items():
        if len(g) <= 1: continue
        reps = [v[0] for v in g.values()]
        flags = [composite(c, N) for c in reps]
        if all(flags): comp_cnt += 1
        elif not any(flags): prime_cnt += 1
        else: print(f"   n={n}: Jones con mezcla primo/compuesto: {flags}")
        if not any(flags):
            print(f"   n={n}: PAR PRIMO con igual Jones, distinta clase diedrica:")
            for c in reps[:2]: print("      ", c)
    print(f"n={n}: Jones con >1 clase diedrica: todos compuestos {comp_cnt}, todos primos {prime_cnt}")

for n in range(6, (int(sys.argv[1]) if len(sys.argv) > 1 else 7) + 1):
    run(n)
