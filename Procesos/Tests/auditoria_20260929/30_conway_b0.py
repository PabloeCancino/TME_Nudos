"""SONDA 30 (2026-10-05), camino (B), fase B0: palabras de Gauss de la forma de Conway C(a1,...,ak).

Construccion: 4-plat. Cuatro hebras en las posiciones 0..3. El cruce i-esimo es un cruce de las hebras
(l, l+1) con l = 1 (hebras del medio) si i es par (bloque a_1, a_3, ...) y l = 0 si i es impar (bloque a_2, ...).
Hay a_j cruces consecutivos en el bloque j. Casquetes (plat): abajo (0,1) y (2,3); arriba (0,1) y (2,3).
Todos los cruces de un bloque tienen el mismo tipo; los bloques alternan el tipo para que el diagrama
sea alternante (se comprueba, no se supone).
Puertos del cruce c: 4c+0 = abajo-izq (BL), 4c+1 = abajo-der (BR), 4c+2 = arriba-izq (TL), 4c+3 = arriba-der (TR);
las hebras del cruce son BL-TR y BR-TL. El signo se calcula por geometria (positivo si cruz(sup, inf) > 0), con
la misma convencion que `faces` de la sonda 18 (orden ccw out_o, out_u, in_o, in_u), y se valida con planaridad.

Se calcula: numero de componentes (p par => enlace; si no es una curva NO se emite palabra), alternancia,
planaridad (faces de 18), fraccion p/q = a1 + 1/(a2 + 1/(...)), determinante |V(-1)|, Jones salvo imagen
especular/signo, y se compara con el censo de alternantes planares reducidos de n <= NCENSO (por defecto 6;
con 7 tarda varios minutos) y con los Jones conocidos de 27_palabras_lean.py.
Uso (desde esta carpeta): python 30_conway_b0.py [nmax=7] [ncenso=6] [--palabras]
"""
import sys
import importlib.util
from fractions import Fraction
from itertools import product

spec = importlib.util.spec_from_file_location("s24", "24_adecuacion.py")
s24 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s24)
s22, s18, s19 = s24.s22, s24.s18, s24.s19
spec27 = importlib.util.spec_from_file_location("s27", "27_palabras_lean.py")
s27 = importlib.util.module_from_spec(spec27)
spec27.loader.exec_module(s27)

OPP = {0: 3, 3: 0, 1: 2, 2: 1}
DIR = {0: (1, 1), 3: (-1, -1), 1: (-1, 1), 2: (1, -1)}


def compositions(n):
    if n == 0:
        yield []
        return
    for first in range(1, n + 1):
        for rest in compositions(n - first):
            yield [first] + rest


def conway_diagram(a, ov=(True, False)):
    """Devuelve (componentes, cruces) con componentes = lista de listas de (c, over?, dir)."""
    left, over_big = [], []
    for j, aj in enumerate(a):
        for _ in range(aj):
            left.append(1 if j % 2 == 0 else 0)
            over_big.append(ov[j % 2])
    n = len(left)
    seq = [[] for _ in range(4)]
    partner = {}

    def link(p, q):
        partner[p] = q
        partner[q] = p

    for c, l in enumerate(left):
        seq[l] += [4 * c + 0, 4 * c + 2]
        seq[l + 1] += [4 * c + 1, 4 * c + 3]
    for pos in range(4):
        s = seq[pos]
        for j in range(1, len(s) - 1, 2):
            link(s[j], s[j + 1])
    top = ((0, 1), (2, 3)) if len(a) % 2 == 1 else ((1, 2), (0, 3))
    cap = {}
    for (p, q) in ((0, 1), (2, 3)):
        cap[('b', p)] = ('b', q); cap[('b', q)] = ('b', p)
    for (p, q) in top:
        cap[('t', p)] = ('t', q); cap[('t', q)] = ('t', p)

    def port_of(node):
        side, pos = node
        return seq[pos][0] if side == 'b' else seq[pos][-1]

    for pos in range(4):
        for side in ('b', 't'):
            if not seq[pos]:
                continue
            node = (side, pos)
            cur = cap[node]
            while not seq[cur[1]]:  # hebra desnuda: cruzar al otro extremo
                cur = cap[('t' if cur[0] == 'b' else 'b', cur[1])]
            link(port_of(node), port_of(cur))
    seen, comps = set(), []
    for start in range(4 * n):
        if start in seen:
            continue
        comp, p = [], start
        while p not in seen:
            seen.add(p)
            c = p // 4
            strand_is_BLTR = (p % 4) in (0, 3)
            comp.append((c, over_big[c] == strand_is_BLTR, DIR[p % 4]))
            seen.add(OPP[p % 4] + 4 * c)
            p = partner[OPP[p % 4] + 4 * c]
        comps.append(comp)
    return comps, n


def to_cfg(comp, n):
    """cfg (o, u, s) y letters de Lean (label, over, pos) a partir de UNA componente."""
    N = len(comp)
    where = {}
    for idx, (c, over, d) in enumerate(comp):
        where.setdefault(c, {})["o" if over else "u"] = (idx, d)
    cfg = []
    for c in sorted(where):
        (po, do), (pu, du) = where[c]["o"], where[c]["u"]
        cross = do[0] * du[1] - do[1] * du[0]
        cfg.append((po, pu, cross > 0))
    return tuple(sorted(cfg)), N


def alternante(comp):
    return all(comp[i][1] != comp[(i + 1) % len(comp)][1] for i in range(len(comp)))


def frac(a):
    x = Fraction(a[-1])
    for ai in reversed(a[:-1]):
        x = ai + 1 / x
    return x


def jkey(cfg, N):
    poly, _, _ = s22.bracket_and_circles(cfg, N)
    seq = s27.jones_seq(cfg, poly)
    c = [tuple(seq), tuple(reversed(seq)), tuple(-x for x in seq), tuple(-x for x in reversed(seq))]
    return min(c), seq


def det(seq):
    # coeficientes de menor a mayor exponente en t: V(-1) en valor absoluto
    return abs(sum(c * (-1) ** k for k, c in enumerate(seq)))


def census(nmax):
    keys = {}
    for n in range(3, nmax + 1):
        N = 2 * n
        seen = set()
        cnt = 0
        import itertools
        for parity in (0, 1):
            overs = [p for p in range(N) if p % 2 == parity]
            unders = [p for p in range(N) if p % 2 != parity]
            for perm in itertools.permutations(unders):
                for signs in itertools.product([False, True], repeat=n):
                    cfg = tuple(sorted((o, u, s) for o, u, s in zip(overs, perm, signs)))
                    if cfg in seen:
                        continue
                    seen.add(cfg)
                    if not s18.planar(N, cfg) or s22.isolated_chords(cfg, N) != 0:
                        continue
                    cnt += 1
                    keys.setdefault(n, set()).add(jkey(cfg, N)[0])
        print(f"   censo n={n}: {cnt} reducidos planares alternantes, {len(keys[n])} claves de Jones", flush=True)
    return keys


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 and not sys.argv[1].startswith("--") else 7
    ncen = int(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith("--") else 6
    palabras = "--palabras" in sys.argv
    cen = census(ncen) if ncen >= 3 else {}
    conoc = {}
    for nm, k in s27.CONOCIDOS.items():
        for cand in (k, k[::-1], [-x for x in k], [-x for x in k[::-1]]):
            conoc[tuple(cand)] = nm
    resumen = {}
    bad = 0
    for n in range(1, nmax + 1):
        tot = knots = links = 0
        for a in compositions(n):
            tot += 1
            comps, nn = conway_diagram(a)
            assert nn == sum(a) == n  # (d) cruces = suma
            f = frac(a)
            p, q = f.numerator, f.denominator
            if len(comps) != 1:
                links += 1
                # una componente no es nudo: p debe ser par (enlace de 2 componentes) -- se comprueba
                if p % 2 != 0:
                    print("  DISCREPANCIA: C%s tiene %d componentes con p=%d impar" % (a, len(comps), p)); bad += 1
                if not all(alternante(c) or len(c) == 0 for c in comps) and len(comps) == 1:
                    pass
                continue
            knots += 1
            if p % 2 == 0:
                print("  DISCREPANCIA: C%s es una curva con p=%d par" % (a, p)); bad += 1
            comp = comps[0]
            if not alternante(comp):
                print("  DISCREPANCIA: C%s no alterna" % a); bad += 1
                continue
            cfg, N = to_cfg(comp, n)
            if N != 2 * n:
                print("  DISCREPANCIA: C%s longitud %d != 2n" % (a, N)); bad += 1
            if not s18.planar(N, cfg):
                print("  DISCREPANCIA: C%s no planar" % a); bad += 1
                continue
            iso = s22.isolated_chords(cfg, N)
            key, seq = jkey(cfg, N)
            d = det(seq)
            nm = conoc.get(tuple(seq)) or conoc.get(key)
            en_censo = None
            if n in cen:
                en_censo = key in cen[n]
                if not en_censo:
                    print("  DISCREPANCIA: C%s Jones no esta en el censo de n=%d" % (a, n)); bad += 1
            if d != p:
                print("  DISCREPANCIA: C%s det(Jones)=%d != p=%d" % (a, d, p)); bad += 1
            a_ok, b_ok = s24.adequate(cfg, N)
            sA = s24.circles_state(cfg, N, [True] * n)
            sB = s24.circles_state(cfg, N, [False] * n)
            resumen.setdefault(n, {})[tuple(a)] = (p, q, key, nm, iso, a_ok and b_ok and sA + sB == n + 2, en_censo)
            print("  C%-14s n=%d p/q=%d/%d det=%d alt=si planar=si cuerdas_aisladas=%d adecuado=%s sA+sB=n+2:%s censo=%s nombre=%s"
                  % (a, n, p, q, d, iso, a_ok and b_ok, sA + sB == n + 2, en_censo, nm))
            if palabras and n <= 5:
                print("     Word:", s27.lean_word("w", s27.cfg_to_word(cfg, N)).replace("\n", " "))
        print("n=%d: %d listas, %d una curva, %d con >1 componente (enlaces)" % (n, tot, knots, links), flush=True)
    # clases por Jones: listas distintas con la misma clave deben tener (p,q) equivalentes por Schubert
    print("\n== Agrupacion por Jones (mismo n) y Schubert q' = q^{+-1} mod p, tambien q' = -q^{+-1} (imagen especular) ==")
    for n, d in sorted(resumen.items()):
        porclave = {}
        for a, (p, q, key, nm, iso, ad, ec) in d.items():
            porclave.setdefault(key, []).append((a, p, q))
        for key, lst in porclave.items():
            ps = {x[1] for x in lst}
            ok = len(ps) == 1
            if ok:
                p = next(iter(ps))
                base = lst[0][2]
                inv = pow(base, -1, p) if p > 1 else 0
                for (a, _, q) in lst:
                    if p > 1 and (q % p) not in (base % p, inv % p, (-base) % p, (-inv) % p):
                        ok = False
            if not ok:
                print("  DISCREPANCIA Schubert en n=%d: %s" % (n, lst)); bad += 1
        print("n=%d: %d listas -> %d clases de Jones; todas coherentes con Schubert (salvo discrepancias arriba)"
              % (n, len(d), len(porclave)))
    print("\nDISCREPANCIAS TOTALES:", bad)


if __name__ == "__main__":
    main()
