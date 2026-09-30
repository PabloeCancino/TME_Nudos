"""SONDA (2026-09-30): conteos de K3 con el signo como dato, ANTES de migrar TCN.

Reproduce exactamente las definiciones de TCN (TMENudos/TCN_02_Reidemeister.lean, TCN_04, TCN_08):
  * configuración K3 = 3 parejas ordenadas (o,u) en Z/6 que cubren las 6 posiciones (120 sin signo);
  * hasR1: alguna pareja consecutiva (u = o +- 1);
  * hasR2: dos parejas distintas p,q con formsR2Pattern (extremos superiores consecutivos Y
    extremos inferiores consecutivos, con los 4 casos +-); en la versión FIRMADA se añade que los
    signos de p y q sean OPUESTOS (regla 4 del plan de migración);
  * acción de D6: x -> x+i  y  x -> -(x+i), sobre o y u a la vez, CONSERVANDO el signo;
  * paridad de Gauss: cada pareja se entrelaza con un número par de las otras.
Uso: python 14_conteos_k3_firmados.py
"""
import itertools
from collections import Counter

N = 6


def matchings(avail):
    if not avail:
        yield []
        return
    x, rest = avail[0], avail[1:]
    for y in rest:
        r2 = [z for z in rest if z != y]
        for m in matchings(r2):
            yield [(x, y)] + m


def unsigned_configs():
    out = []
    for m in matchings(list(range(N))):
        for orient in itertools.product([False, True], repeat=3):
            out.append(tuple(sorted((b, a) if o else (a, b) for (a, b), o in zip(m, orient))))
    return sorted(set(out))


def consecutive(p):
    return (p[1] - p[0]) % N in (1, N - 1)


def forms_r2(p, q):
    a, b = p
    c, d = q
    return ((c - a) % N == 1 and (d - b) % N == 1) or ((c - a) % N == N - 1 and (d - b) % N == N - 1) \
        or ((c - a) % N == 1 and (d - b) % N == N - 1) or ((c - a) % N == N - 1 and (d - b) % N == 1)


def has_r1(pairs):
    return any(consecutive(p[:2]) for p in pairs)


def has_r2(pairs, signed):
    for p in pairs:
        for q in pairs:
            if p[:2] != q[:2] and forms_r2(p[:2], q[:2]):
                if not signed or p[2] != q[2]:
                    return True
    return False


def between(a, b, x):
    lo, hi = min(a, b), max(a, b)
    return lo < x < hi


def interlace(p, q):
    a, b = p[:2]
    c, d = q[:2]
    if len({a, b, c, d}) < 4:
        return False
    return between(a, b, c) != between(a, b, d)


def gauss_even(pairs):
    return all(sum(interlace(p, q) for q in pairs if q != p) % 2 == 0 for p in pairs)


def act(g, pairs):
    kind, i = g
    f = (lambda x: (x + i) % N) if kind == 'r' else (lambda x: (-(x + i)) % N)
    return tuple(sorted((f(p[0]), f(p[1])) + p[2:] for p in pairs))


D6 = [('r', i) for i in range(N)] + [('s', i) for i in range(N)]


def swap(pairs):
    return tuple(sorted((p[1], p[0]) + ((not p[2],) if len(p) == 3 else ()) for p in pairs))


def orbits(confs):
    confs = set(confs)
    seen, res = set(), []
    for c in sorted(confs):
        if c in seen:
            continue
        orb = {act(g, c) for g in D6}
        seen |= orb
        res.append(sorted(orb))
    return res


def report(title, confs, signed):
    irr = [c for c in confs if not has_r1(c) and not has_r2(c, signed)]
    real = [c for c in irr if gauss_even(c)]
    oi = orbits(irr)
    orl = orbits(real)
    print(f"--- {title}")
    print(f"  configuraciones: {len(confs)}")
    print(f"  irreducibles (sin R1 ni R2): {len(irr)}   órbitas D6: {len(oi)}   tamaños: {sorted(len(o) for o in oi)}")
    print(f"  realizables (irreducibles y paridad de Gauss): {len(real)}   órbitas: {len(orl)}   tamaños: {sorted(len(o) for o in orl)}")
    return irr, real


U = unsigned_configs()
report("SIN signo (debe reproducir TCN: 120, 14 = 12 + 2, realizables 2)", [tuple(c) for c in U], False)

S = sorted({tuple(sorted(tuple(list(p) + [s]) for p, s in zip(c, signs)))
            for c in U for signs in itertools.product([False, True], repeat=3)})
irr, real = report("CON signo como dato (R2 exige signos opuestos)", S, True)

# ¿cuántas firmadas reducibles sin signo pasan a irreducibles firmadas (R2 bloqueado por signos iguales)?
sin_signo_irr = {tuple(sorted(p[:2] for p in c)) for c in irr}
print(f"  sin signo olvidado, las irreducibles firmadas cubren {len(sin_signo_irr)} configuraciones distintas")
nuevas = [c for c in irr if has_r2([(p[0], p[1], None) for p in c], False)]
print(f"  irreducibles firmadas que SÍ serían reducibles por R2 sin mirar el signo: {len(nuevas)}")

# trébol y espejo firmados
tref = tuple(sorted([(0, 3, True), (4, 1, True), (2, 5, True)]))
mir = swap(tref)
print("  trébol firmado irreducible:", tref in irr, "| realizable:", tref in real)
print("  espejo firmado irreducible:", mir in irr, "| realizable:", mir in real)
print("  espejo en la órbita D6 del trébol:", mir in {act(g, tref) for g in D6})
print("  órbita D6 del trébol firmado:", len({act(g, tref) for g in D6}), "| del espejo:", len({act(g, mir) for g in D6}))
# las órbitas realizables
for o in orbits(real):
    print("   órbita realizable de tamaño", len(o), "ejemplo:", o[0])
# bajo D6 x swap
def orb2(c):
    s = {act(g, c) for g in D6}
    return s | {act(g, swap(c)) for g in D6}
print("  realizables: órbitas bajo D6 x intercambio:", len({frozenset(orb2(c)) for c in real}))


# ---------------------------------------------------------------------------------------------
# CONSISTENCIA DE SIGNOS (hallazgo de la sonda): con el signo como dato LIBRE salen configuraciones
# que no son diagramas planos (p. ej. un trébol con signos mixtos). Una condición necesaria que SÍ
# mira el signo: en un diagrama clásico el ÍNDICE de cada cruce es 0. Para la cuerda c = (o,u),
# sea A el arco que va de o a u en sentido creciente (posiciones estrictamente intermedias); para
# cada cuerda d entrelazada con c: suma +sgn(d) si el extremo superior de d cae en A, y -sgn(d) si
# cae el inferior.
def arc(o, u):
    out, x = set(), (o + 1) % N
    while x != u:
        out.add(x)
        x = (x + 1) % N
    return out


def index_zero(pairs):
    for c in pairs:
        A = arc(c[0], c[1])
        tot = 0
        for d in pairs:
            if d is c or d[:2] == c[:2] or not interlace(c, d):
                continue
            s = 1 if d[2] else -1
            tot += s if d[0] in A else -s
        if tot != 0:
            return False
    return True


print("\n=== Con la condición de ÍNDICE CERO (consistencia de signos con la planaridad) ===")
cons = [c for c in S if index_zero(c)]
print("  firmadas con índice cero en todas las cuerdas:", len(cons), "de", len(S))
irr_c = [c for c in cons if not has_r1(c) and not has_r2(c, True)]
real_c = [c for c in irr_c if gauss_even(c)]
print("  de ellas, irreducibles:", len(irr_c), " | realizables (irreducible + Gauss par):", len(real_c))
oc = orbits(real_c)
print("  realizables con índice cero: órbitas D6:", len(oc), "tamaños:", sorted(len(o) for o in oc))
for o in oc:
    print("   ", o[0])
print("  ¿trébol firmado y espejo firmado cumplen índice cero?", index_zero(tref), index_zero(mir))
mixto = tuple(sorted([(0, 3, True), (4, 1, True), (2, 5, False)]))
print("  trébol con signos mixtos (+,+,-): índice cero =", index_zero(mixto), "| Gauss par =", gauss_even(mixto))
special = tuple(sorted([(0, 2, True), (1, 4, True), (3, 5, True)]))
print("  specialClass (+,+,+): índice cero =", index_zero(special))
