"""SONDA 31 (2026-10-05), camino (B): forma cerrada "por pasadas" de la palabra de Gauss de C(a1..ak).

HALLAZGO que se verifica aqui (n <= NMAX, por defecto 10):
  La palabra de Gauss de conwayWord(a) (cuando p es impar) es la CONCATENACION de 2k "pasadas" de bloque.
  Una pasada del bloque j recorre sus a_j cruces en orden ascendente (e_j, e_j+1, ..., e_j+a_j-1) o
  descendente, siendo e_j = a_1+...+a_{j-1}. Cada bloque se recorre exactamente dos veces.
  Las pasadas (bloque, sentido) las determina un recorrido en el GRAFO DE EXTREMOS de bloque
  (4 extremos por bloque), que depende solo de k y de las PARIDADES de los a_j:
    * dentro del bloque j: a_j impar -> extremo BL<->TR, BR<->TL; a_j par -> BL<->TL, BR<->TR;
    * entre bloques: carril x (0..3); el bloque j usa los carriles (1,2) si j par y (0,1) si j impar;
      el extremo superior del carril x de un bloque se une al extremo inferior del siguiente bloque que use
      el carril x (y analogamente hacia abajo); sin vecino: casquete (misma regla que la sonda 30).
  Ademas la palabra con etiquetas, la alternancia (sobre/bajo segun la paridad de la posicion, empezando
  por encima), y el signo (uniforme por bloque: depende del sentido de las dos pasadas) se verifican.
Uso (desde esta carpeta): python 31_conway_forma_cerrada.py [nmax=10]
"""
import sys
import importlib.util

spec = importlib.util.spec_from_file_location("s30", "30_conway_b0.py")
s30 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s30)


def lanes(j):
    return (1, 2) if j % 2 == 0 else (0, 1)


def passes(a):
    """Recorrido en el grafo de extremos. Devuelve la lista de (bloque, sentido) con sentido +1 (asc) o -1 (desc),
    o None si la curva no es unica. Empieza entrando por abajo-izquierda del bloque 0."""
    k = len(a)
    users = {x: [j for j in range(k) if x in lanes(j)] for x in range(4)}
    top_cap = {0: 1, 1: 0, 2: 3, 3: 2} if k % 2 == 1 else {1: 2, 2: 1, 0: 3, 3: 0}
    bot_cap = {0: 1, 1: 0, 2: 3, 3: 2}

    def enter_from_below(x, start_after=None):
        """el trazo sube por el carril x, ultimo bloque visitado en start_after (None = desde el fondo).
        Devuelve (bloque, carril de entrada) por su extremo inferior, aplicando casquetes si hace falta."""
        us = users[x]
        if start_after is None:
            nxt = us[0] if us else None
        else:
            later = [j for j in us if j > start_after]
            nxt = later[0] if later else None
        if nxt is not None:
            return (nxt, x, +1)
        # casquete superior: pasa al carril top_cap[x] y baja
        return enter_from_above(top_cap[x], None)

    def enter_from_above(x, start_before):
        us = users[x]
        if start_before is None:
            prv = us[-1] if us else None
        else:
            earlier = [j for j in us if j < start_before]
            prv = earlier[-1] if earlier else None
        if prv is not None:
            return (prv, x, -1)
        return enter_from_below(bot_cap[x], None)

    # estado: (bloque, carril por el que se entra, sentido de entrada +1 = por abajo)
    state = (0, 1, +1)
    res = []
    seen = set()
    for _ in range(2 * k + 2):
        j, x, d = state
        if (j, x, d) in seen:
            break
        seen.add((j, x, d))
        res.append((j, d))
        # salida: carril de salida
        l, r = lanes(j)
        odd = a[j] % 2 == 1
        y = (r if x == l else l) if odd else x
        if d == +1:
            state = enter_from_below(y, j)
        else:
            state = enter_from_above(y, j)
    if len(res) != 2 * k or state != (0, 1, +1):
        return None
    return res


def word_from_passes(a, ps):
    start = [sum(a[:j]) for j in range(len(a))]
    w = []
    for j, d in ps:
        r = list(range(start[j], start[j] + a[j]))
        w += r if d == +1 else r[::-1]
    return w


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    bad = 0
    tot = 0
    for n in range(1, nmax + 1):
        cnt = 0
        for a in s30.compositions(n):
            comps, nn = s30.conway_diagram(a)
            ps = passes(a)
            es_curva = len(comps) == 1
            if es_curva != (ps is not None):
                print("DISCREPANCIA curva/pasadas", a, es_curva, ps); bad += 1; continue
            if not es_curva:
                continue
            tot += 1; cnt += 1
            comp = comps[0]
            labels = [c for c, o, d in comp]
            if labels != word_from_passes(a, ps):
                print("DISCREPANCIA etiquetas", a, labels, ps); bad += 1; continue
            # sobre/bajo por paridad de posicion, empezando por encima
            if [o for c, o, d in comp] != [i % 2 == 0 for i in range(len(comp))]:
                print("DISCREPANCIA over/paridad", a); bad += 1
            # cada bloque exactamente dos veces
            if sorted(j for j, d in ps) != sorted(list(range(len(a))) * 2):
                print("DISCREPANCIA 2 pasadas por bloque", a); bad += 1
            # signo uniforme por bloque y regla: depende de si las dos pasadas son paralelas
            cfg, N = s30.to_cfg(comp, n)
            sg = {}
            for idx, (po, pu, s) in enumerate(cfg):
                c = comp[po][0]
                sg[c] = s
            start = [sum(a[:j]) for j in range(len(a))]
            for j in range(len(a)):
                vals = {sg[c] for c in range(start[j], start[j] + a[j])}
                dirs = [d for jj, d in ps if jj == j]
                par = dirs[0] == dirs[1]
                if len(vals) != 1:
                    print("DISCREPANCIA signo no uniforme en bloque", a, j); bad += 1
                else:
                    # regla: signo = (j par) xor (paralelas)  [se imprime si falla]
                    pred = (j % 2 == 0) == par
                    if next(iter(vals)) != pred and next(iter(vals)) != (not pred):
                        bad += 1
            rule_ok = all(
                {sg[c] for c in range(start[j], start[j] + a[j])} == {((j % 2 == 0) == ([d for jj, d in ps if jj == j][0] == [d for jj, d in ps if jj == j][1]))}
                for j in range(len(a)))
            globals().setdefault("RULE", [0, 0])
            RULE[0 if rule_ok else 1] += 1
        print("n=%d: %d listas de una curva verificadas (pasadas == palabra)" % (n, cnt), flush=True)
    print("total una curva:", tot, " DISCREPANCIAS:", bad)
    print("regla de signo 'signo(bloque j) = [j par] == [pasadas paralelas]': cumple %d, no cumple %d" % tuple(RULE))
    # muestra
    for a in ([3], [2, 2], [3, 2], [2, 3], [3, 1, 2], [2, 1, 1, 2], [1, 1, 3], [2, 2, 1]):
        print(a, passes(a))


if __name__ == "__main__":
    main()
