"""SONDA 18 (2026-10-01): fase 1 del plan de axiomas de Basic, reparacion de `reconstruct_from_first`.

Hallazgos previos: (i) el axioma es falso por el indexado (sonda 16); (ii) mas hondo: las razones (IME) y
aun el IME firmado (SIME) NO determinan la configuracion salvo rotacion en general. Ejemplo (n = 3):
  (0,3,+),(1,4,+),(2,5,+)   [configuracion especial, NO planar]   frente a
  (0,3,+),(4,1,+),(2,5,+)   [el trebol, planar]
tienen las mismas razones (3,3,3) y signos, y no son rotacion una de otra.

Pregunta de esta sonda: ¿el SIME determina la configuracion salvo rotacion si se restringe a las
configuraciones PLANARES (genero 0, criterio exacto de la sonda 15)? Se prueban varios invariantes
independientes del indexado de los cruces:
  * SIMEcic: lista de (razon, signo) en orden creciente de la posicion superior, minima por rotacion
    ciclica de la lista (rotar posiciones permuta ciclicamente ese orden);
  * IMEcic: lo mismo sin el signo;
  * MULTI: el multiconjunto de (razon, signo).
Para cada invariante se cuentan las clases de invariante que contienen MAS DE UNA clase de rotacion
(= contraejemplos a que el invariante sea completo). Se hace sobre: (a) todas las configuraciones,
(b) las planares, (c) las planares sin candidato R1/R2 (irreducibles posicionales).
Uso: python 18_sonda_reconstruccion.py [nmax]
"""
import itertools
import sys
from collections import defaultdict


def matchings(avail):
    if not avail:
        yield []
        return
    x, rest = avail[0], avail[1:]
    for y in rest:
        r2 = [z for z in rest if z != y]
        for m in matchings(r2):
            yield [(x, y)] + m


def faces(N, cfg):
    alpha = {}
    for p in range(N):
        alpha[('out', p)] = ('in', (p + 1) % N)
        alpha[('in', (p + 1) % N)] = ('out', p)
    sigma = {}
    for o, u, s in cfg:
        order = ([('out', o), ('out', u), ('in', o), ('in', u)] if s
                 else [('out', o), ('in', u), ('in', o), ('out', u)])
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


def interlaced(c1, c2):
    a1, b1 = min(c1[:2]), max(c1[:2])
    a2, b2 = min(c2[:2]), max(c2[:2])
    return (a1 < a2 < b1 < b2) or (a2 < a1 < b2 < b1)


def adjacent(p, q, N):
    return (p + 1) % N == q or (q + 1) % N == p


def reducible_candidate(cfg, N):
    n = len(cfg)
    for i, c in enumerate(cfg):
        if adjacent(c[0], c[1], N) and all(not interlaced(c, d) for j, d in enumerate(cfg) if j != i):
            return True
    for a in range(n):
        for b in range(n):
            ca, cb = cfg[a], cfg[b]
            if (a != b and adjacent(ca[0], cb[0], N) and adjacent(ca[1], cb[1], N)
                    and interlaced(ca, cb) and ca[2] != cb[2]):
                return True
    return False


def rotate(cfg, k, N):
    return tuple(sorted(((o + k) % N, (u + k) % N, s) for o, u, s in cfg))


def rot_class(cfg, N):
    return min(rotate(cfg, k, N) for k in range(N))


def cyc_min(seq):
    return min(tuple(seq[i:] + seq[:i]) for i in range(len(seq)))


def invariants(cfg, N):
    by_over = sorted(cfg, key=lambda c: c[0])
    sime = [((u - o) % N, s) for o, u, s in by_over]
    ime = [r for r, _ in sime]
    return {
        'SIMEcic': cyc_min(sime),
        'IMEcic': cyc_min(ime),
        'MULTI': tuple(sorted(sime)),
    }


def run(n):
    N = 2 * n
    groups = {k: {'all': defaultdict(set), 'planar': defaultdict(set), 'irr': defaultdict(set)}
              for k in ('SIMEcic', 'IMEcic', 'MULTI')}
    ejemplos = {}
    cnt = {'all': 0, 'planar': 0, 'irr': 0}
    seen = set()
    for m in matchings(list(range(N))):
        for orient in itertools.product([False, True], repeat=n):
            ch = [(b, a) if o else (a, b) for (a, b), o in zip(m, orient)]
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for (o, u), s in zip(ch, signs)))
                if cfg in seen:
                    continue
                seen.add(cfg)
                rc = rot_class(cfg, N)
                inv = invariants(cfg, N)
                pl = planar(N, cfg)
                irr = pl and not reducible_candidate(cfg, N)
                cnt['all'] += 1
                cnt['planar'] += pl
                cnt['irr'] += irr
                for name, val in inv.items():
                    groups[name]['all'][val].add(rc)
                    if pl:
                        groups[name]['planar'][val].add(rc)
                    if irr:
                        groups[name]['irr'][val].add(rc)
    print(f"n={n}: configuraciones {cnt['all']}, planares {cnt['planar']}, planares sin candidato R1/R2 {cnt['irr']}")
    for name in ('SIMEcic', 'IMEcic', 'MULTI'):
        row = []
        for sub in ('all', 'planar', 'irr'):
            g = groups[name][sub]
            bad = [v for v, cl in g.items() if len(cl) > 1]
            row.append(f"{sub}: {len(g)} clases de invariante, {len(bad)} con >1 clase de rotacion")
            if bad and sub in ('planar', 'irr') and (name, sub) not in ejemplos:
                ejemplos[(name, sub)] = (bad[0], sorted(g[bad[0]])[:2])
        print(f"  {name:8s} | " + " | ".join(row))
    for (name, sub), (val, cls) in ejemplos.items():
        print(f"   contraejemplo {name}/{sub}: invariante {val} -> clases {cls}")


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    for n in range(1, nmax + 1):
        run(n)
