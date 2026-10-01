"""SONDA 21 (2026-10-01): ¿es LOCALMENTE CONFLUENTE el sistema de reduccion R1/R2 sobre diagramas SIN indices?

Si el sistema es terminante (cada paso baja el grado en 1 o 2: trivial) y localmente confluente, el lema de Newman da
FORMA NORMAL UNICA por clase, y de ahi: (A6) irreducible => grado minimo; (A7) dos minimos de la misma clase son el
mismo diagrama salvo rotacion. Esta sonda comprueba la confluencia local EXHAUSTIVAMENTE para grados <= NMAX_EXH y
por muestreo para grados mayores.

Diagrama sin indices = conjunto de cruces (o, u, s) con cobertura total en Z/2d. Movimientos (mismas condiciones que
Basic.lean, `is_R1_candidate` e `is_R2_candidate`):
  * R1 en el cruce c: posiciones adyacentes y ningun otro cruce interlazado con c; se quita c y las posiciones
    restantes se renumeran por rango;
  * R2 en (a,b): superiores adyacentes, inferiores adyacentes, interlazados, signos opuestos; se quitan ambos.
Un PAR CRITICO es un diagrama K con dos reducciones de un paso K -> K1 y K -> K2 (distintas). Es JOINABLE si K1 y K2
tienen un descendiente comun (salvo rotacion). Se cuentan pares criticos y los no joinables.
Uso: python 21_confluencia_local.py [nmax_exh] [n_muestra_grande]
"""
import itertools
import random
import sys
import importlib.util
import os

ALLOW_EMPTY = os.environ.get("ALLOW_EMPTY", "0") == "1"

spec = importlib.util.spec_from_file_location("s20", "20_transiciones_fieles.py")
s20 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s20)


def sort_cfg(K):
    return tuple(sorted(K))


def steps(K):
    """Reducciones de un paso (sin indices): lista de (tipo, indices quitados, resultado canonico)."""
    out = []
    # `RationalConfiguration 0` es un tipo vacio en Basic: no hay reducciones que dejen 0 cruces
    for i in s20.r1_cands(K):
        if ALLOW_EMPTY or len(K) - 1 >= 1:
            out.append(("R1", (i,), sort_cfg(s20.remove(K, [i]))))
    seen = set()
    for (a, b) in s20.r2_cands(K):
        key = tuple(sorted((a, b)))
        if key in seen or (not ALLOW_EMPTY and len(K) - 2 < 1):
            continue
        seen.add(key)
        out.append(("R2", key, sort_cfg(s20.remove(K, list(key)))))
    return out


def canon(D):
    if not D:
        return ()
    return min(tuple(sorted(R)) for R in s20.rotations(D))


def descendants(D, memo):
    D = canon(D)
    if D in memo:
        return memo[D]
    res = {D}
    for _, _, R in steps(D):
        res |= descendants(R, memo)
    memo[D] = res
    return res


def check(K, memo, stats):
    st = steps(K)
    for x in range(len(st)):
        for y in range(x + 1, len(st)):
            stats["criticos"] += 1
            d1 = descendants(st[x][2], memo)
            d2 = descendants(st[y][2], memo)
            if not (d1 & d2):
                stats["no_joinables"] += 1
                if len(stats["ejemplos"]) < 3:
                    stats["ejemplos"].append((K, st[x][:2], st[y][:2]))
    return


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    nbig = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    random.seed(1)
    for n in range(2, nmax + 1):
        allc = s20.configs(n)
        # unindexados: un representante por conjunto
        uniq = {}
        for K in allc:
            uniq.setdefault(sort_cfg(K), K)
        stats = {"criticos": 0, "no_joinables": 0, "ejemplos": []}
        memo = {}
        reducibles = 0
        for key, K in uniq.items():
            if steps(K):
                reducibles += 1
                check(K, memo, stats)
        print(f"n={n}: diagramas {len(uniq)}, con alguna reduccion {reducibles}, pares criticos {stats['criticos']}, "
              f"NO joinables {stats['no_joinables']}", flush=True)
        for e in stats["ejemplos"]:
            print("   no joinable:", e)
    if nbig:
        # casos grandes: caminata aleatoria de EXPANSIONES R1/R2 desde configuraciones pequenas (estructura reducible)
        def rand_small(d):
            N = 2 * d
            perm = list(range(N))
            random.shuffle(perm)
            return tuple((perm[2 * t], perm[2 * t + 1], random.random() < 0.5) for t in range(d))

        for target in (5, 6):
            stats = {"criticos": 0, "no_joinables": 0, "ejemplos": []}
            memo = {}
            tested = 0
            while tested < nbig:
                K = rand_small(random.choice([2, 3]))
                while len(K) < target:
                    ex = list(s20.expansions(K, target))
                    ex = [X for X in ex if len(X) <= target]
                    if not ex:
                        break
                    K = random.choice(ex)
                if len(K) != target or not steps(K):
                    continue
                tested += 1
                check(K, memo, stats)
            print(f"n={target} (muestra de {tested} por expansiones): pares criticos {stats['criticos']}, "
                  f"NO joinables {stats['no_joinables']}", flush=True)
            for e in stats["ejemplos"]:
                print("   no joinable:", e)


if __name__ == "__main__":
    main()
