"""SONDA 25 (2026-10-01), camino (B), etapa S5: en un diagrama ALTERNANTE PLANAR, los circulos de los estados todo-A y todo-B SON las caras del mapa.

Para cada diagrama alternante planar se calculan:
  * las caras: orbitas de sigma∘alpha sobre las semiaristas (la construccion de la sonda 15); cada cara se describe por el CONJUNTO de aristas
    e_j (j -> j+1) que recorre (la semiarista out_p corresponde a la arista e_p; in_p, a la arista e_{p-1});
  * los circulos de los estados todo-A y todo-B: componentes conexas del grafo de aristas con las parejas de suavizacion de la sonda 19
    (una arista = un vertice; cada cruce une 2 parejas), cada una descrita por su conjunto de aristas.
Tesis: la coleccion {circulos A} U {circulos B} coincide, como coleccion de conjuntos de aristas, con la coleccion de caras (cada cara es
exactamente un circulo de uno de los dos estados). Se cuenta tambien el caso NO alternante planar, donde se espera que NO se cumpla.
Uso: python 25_circulos_son_caras.py [nmax]
"""
import itertools
import sys
from collections import Counter
import importlib.util

spec = importlib.util.spec_from_file_location("s19", "19_sonda_jones_flype.py")
s19 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s19)
s18 = s19.s18


def face_edge_sets(N, cfg):
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
    seen, faces = set(), []
    for d in alpha:
        if d in seen:
            continue
        edges, x = set(), d
        while x not in seen:
            seen.add(x)
            kind, p = x
            edges.add(p if kind == 'out' else (p - 1) % N)
            x = sigma[alpha[x]]
        faces.append(frozenset(edges))
    return Counter(faces)


def state_circle_edge_sets(N, cfg, A_state):
    prev = lambda j: (j - 1) % N
    parent = list(range(N))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for o, u, s in cfg:
        if A_state == s:
            pairs = [(prev(o), u), (prev(u), o)]
        else:
            pairs = [(prev(o), prev(u)), (o, u)]
        for a, b in pairs:
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb
    groups = {}
    for e in range(N):
        groups.setdefault(find(e), set()).add(e)
    return Counter(frozenset(g) for g in groups.values())


def run(n):
    N = 2 * n
    seen = set()
    alt_ok = alt_bad = nonalt_ok = nonalt_bad = 0
    ejemplos = []
    for m in s19.itertools.product([0], repeat=0):
        pass
    # enumeracion: alternantes (como 18b) y TODOS los planares (para comparar con los no alternantes)
    def matchings(avail):
        if not avail:
            yield []
            return
        x, rest = avail[0], avail[1:]
        for y in rest:
            for mm in matchings([z for z in rest if z != y]):
                yield [(x, y)] + mm

    for mm in matchings(list(range(N))):
        for orient in itertools.product([False, True], repeat=n):
            ch = [(b, a) if o else (a, b) for (a, b), o in zip(mm, orient)]
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for (o, u), s in zip(ch, signs)))
                if cfg in seen:
                    continue
                seen.add(cfg)
                if not s18.planar(N, cfg):
                    continue
                alternante = len({o % 2 for o, u, s in cfg}) == 1
                faces = face_edge_sets(N, cfg)
                circ = state_circle_edge_sets(N, cfg, True) + state_circle_edge_sets(N, cfg, False)
                ok = (faces == circ)
                if alternante:
                    if ok:
                        alt_ok += 1
                    else:
                        alt_bad += 1
                        if len(ejemplos) < 3:
                            ejemplos.append(cfg)
                else:
                    if ok:
                        nonalt_ok += 1
                    else:
                        nonalt_bad += 1
    print(f"n={n}: alternantes planares: caras = circulos en {alt_ok}, NO en {alt_bad}; "
          f"no alternantes planares: caras = circulos en {nonalt_ok}, NO en {nonalt_bad}", flush=True)
    for e in ejemplos:
        print("   alternante con caras != circulos:", e)


if __name__ == "__main__":
    for n in range(1, (int(sys.argv[1]) if len(sys.argv) > 1 else 5) + 1):
        run(n)
