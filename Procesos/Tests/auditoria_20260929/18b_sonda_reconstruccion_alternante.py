"""SONDA 18b: ¿el SIME es completo entre las configuraciones PLANARES ALTERNANTES sin candidato R1/R2?

Alternante: a lo largo de las 2n posiciones se alternan paso por encima y paso por debajo, es decir, las
posiciones superiores son todas las pares o todas las impares. Un diagrama alternante reducido es minimo
(Kauffman-Murasugi-Thistlethwaite); aqui 'sin candidato R1/R2' sustituye a 'reducido'.
Se cuentan colisiones: clases de rotacion distintas con el mismo SIME ciclico. Uso: python 18b_... [nmax]
"""
import itertools
import sys
from collections import defaultdict
import importlib.util
spec = importlib.util.spec_from_file_location("s18", "18_sonda_reconstruccion.py")
s18 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s18)


def run(n):
    N = 2 * n
    groups = defaultdict(set)
    total = planar_cnt = irr_cnt = 0
    for parity in (0, 1):
        overs = [p for p in range(N) if p % 2 == parity]
        unders = [p for p in range(N) if p % 2 != parity]
        for perm in itertools.permutations(unders):
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for o, u, s in zip(overs, perm, signs)))
                total += 1
                if not s18.planar(N, cfg):
                    continue
                planar_cnt += 1
                if s18.reducible_candidate(cfg, N):
                    continue
                irr_cnt += 1
                groups[s18.invariants(cfg, N)['SIMEcic']].add(s18.rot_class(cfg, N))
    bad = {k: v for k, v in groups.items() if len(v) > 1}
    print(f"n={n}: alternantes {total}, planares {planar_cnt}, sin R1/R2 {irr_cnt}, "
          f"clases SIME {len(groups)}, con >1 clase de rotacion: {len(bad)}")
    for k, v in list(bad.items())[:2]:
        print("   colision SIME", k, "->", sorted(v)[:2])


for n in range(2, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 7):
    run(n)
