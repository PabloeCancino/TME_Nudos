"""SONDA (2026-09-30): ¿es el ÍNDICE CERO suficiente para que un diagrama de Gauss firmado sea planar?

Criterio EXACTO de planaridad (independiente del índice): la configuración firmada (cuerdas (o,u) con
signo) determina un MAPA COMBINATORIO. En el vértice de la cuerda c hay 4 semiaristas:
salida/entrada de la rama SUPERIOR (posición o) y de la INFERIOR (posición u). El signo fija el orden
cíclico antihorario en el vértice:
   cruce positivo: dir_sup = 0°, dir_inf = +90°  =>  orden CCW: sale_sup, sale_inf, entra_sup, entra_inf
   cruce negativo: dir_sup = 0°, dir_inf = -90°  =>  orden CCW: sale_sup, entra_inf, entra_sup, sale_inf
(las 'entra_*' apuntan hacia atrás: ángulo + 180°). Las caras son los ciclos de sigma∘alpha, y el
diagrama es PLANAR (género 0) sii V - E + F = 2 con V = n, E = 2n, es decir F = n + 2.
Controles: el trébol (0,3),(4,1),(2,5) todo + y su espejo todo - deben ser planares.

Se compara, para n = 3 y n = 4, el conjunto planar con el conjunto "índice cero" (la condición
necesaria usada en TCN_05) y con la paridad de Gauss. Uso: python 15_genero_vs_indice_cero.py
"""
import itertools
import sys


def matchings(avail):
    if not avail:
        yield []
        return
    x, rest = avail[0], avail[1:]
    for y in rest:
        r2 = [z for z in rest if z != y]
        for m in matchings(r2):
            yield [(x, y)] + m


def configs(n):
    N = 2 * n
    for m in matchings(list(range(N))):
        for orient in itertools.product([False, True], repeat=n):
            ch = [(b, a) if o else (a, b) for (a, b), o in zip(m, orient)]
            for signs in itertools.product([False, True], repeat=n):
                yield N, tuple(sorted((o, u, s) for (o, u), s in zip(ch, signs)))


def faces(N, cfg):
    # darts: ('out', p), ('in', p) para cada posición p
    alpha = {}
    for p in range(N):
        alpha[('out', p)] = ('in', (p + 1) % N)
        alpha[('in', (p + 1) % N)] = ('out', p)
    sigma = {}
    for o, u, s in cfg:
        if s:
            order = [('out', o), ('out', u), ('in', o), ('in', u)]
        else:
            order = [('out', o), ('in', u), ('in', o), ('out', u)]
        for i in range(4):
            sigma[order[i]] = order[(i + 1) % 4]
    seen, cyc = set(), 0
    for d in alpha:
        if d in seen:
            continue
        cyc += 1
        x = d
        while x not in seen:
            seen.add(x)
            x = sigma[alpha[x]]
    return cyc


def planar(N, cfg):
    return faces(N, cfg) == N // 2 + 2


def between(N, a, b, x):
    return x != a and x != b and ((x - a) % N) < ((b - a) % N)


def interlace(N, p, q):
    a, b = p[:2]
    c, d = q[:2]
    if len({a, b, c, d}) < 4:
        return False
    return between(N, a, b, c) != between(N, a, b, d)


def gauss_even(N, cfg):
    return all(sum(interlace(N, p, q) for q in cfg if q != p) % 2 == 0 for p in cfg)


def index_zero(N, cfg):
    for c in cfg:
        tot = 0
        for d in cfg:
            if d[:2] == c[:2] or not interlace(N, c, d):
                continue
            s = 1 if d[2] else -1
            tot += s if between(N, c[0], c[1], d[0]) else -s
        if tot != 0:
            return False
    return True


def run(n):
    N = 2 * n
    total = pl = iz = both = gz = 0
    iz_not_pl, pl_not_iz, ge_not_pl = [], [], []
    for _, cfg in configs(n):
        total += 1
        P, I, G = planar(N, cfg), index_zero(N, cfg), gauss_even(N, cfg)
        pl += P
        iz += I
        gz += G
        both += P and I
        if I and G and not P and len(iz_not_pl) < 3:
            iz_not_pl.append(cfg)
        if P and not I and len(pl_not_iz) < 3:
            pl_not_iz.append(cfg)
        if G and not P and len(ge_not_pl) < 3:
            ge_not_pl.append(cfg)
    print(f"n={n}: total {total} | planares {pl} | índice cero {iz} | Gauss par {gz} | planar∧índice0 {both}")
    print(f"   planar pero NO índice cero (debe ser 0 si el índice es necesario): "
          f"{sum(1 for _, c in configs(n) if planar(N, c) and not index_zero(N, c))}")
    print(f"   índice cero ∧ Gauss par pero NO planar: "
          f"{sum(1 for _, c in configs(n) if index_zero(N, c) and gauss_even(N, c) and not planar(N, c))}")
    print(f"   índice cero pero NO planar: "
          f"{sum(1 for _, c in configs(n) if index_zero(N, c) and not planar(N, c))}")
    print("   ejemplos índice0∧Gauss no planar:", iz_not_pl)
    print("   ejemplos planar sin índice0:", pl_not_iz)
    print("   ejemplos Gauss par no planar:", ge_not_pl)


tref = (3 * 2, tuple(sorted([(0, 3, True), (4, 1, True), (2, 5, True)])))
mir = (6, tuple(sorted([(3, 0, False), (1, 4, False), (5, 2, False)])))
print("control trébol planar:", planar(*tref), "| espejo planar:", planar(*mir))
mix = (6, tuple(sorted([(0, 3, True), (4, 1, True), (2, 5, False)])))
print("trébol mixto planar:", planar(*mix), "(esperado False)")
for n in (1, 2, 3, 4):
    run(n)
if len(sys.argv) > 1 and sys.argv[1] == "5":
    run(5)
