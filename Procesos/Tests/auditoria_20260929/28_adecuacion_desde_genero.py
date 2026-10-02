"""SONDA 28 (2026-10-02), camino (B), etapa S5c: ¿sale la ADECUACION de la igualdad de genero  s_A + s_B = c + 2  y de que cada cuerda
este entrelazada con otra, SIN geometria?

Tesis (a probar en Lean con un L2 refinado): para TODO diagrama de Gauss firmado de UNA curva con n cruces, sin hipotesis de planaridad ni de
alternancia, si  s_A + s_B = n + 2  y el cruce x esta entrelazado con algun otro cruce, entonces
    lazos(todo-A con x cambiado a B) = s_A - 1     (A-adecuado en x)
    lazos(todo-B con x cambiado a A) = s_B - 1     (B-adecuado en x).
Idea de la prueba: desacoplar x (usar en x el emparejamiento B tambien en el 'a') deja una estructura de tres involuciones con ab involucion con 4 puntos
fijos mas; L1 da  lazos(sigma_x) + s_B <= (c - 1) + 2 k_x,  con k_x = 1 exactamente cuando la cuerda de x se entrelaza con otra.
Se prueba por cálculo exhaustivo para n <= 5 sobre TODAS las palabras de una curva (967 680 en n = 5), incluidas no planares y no orientables.
También se cuenta el recíproco: cuerda aislada => la adecuación en x FALLA (cuando hay igualdad).
Uso: python 28_adecuacion_desde_genero.py [nmax]
"""
import itertools
import sys
from collections import Counter
import importlib.util

spec = importlib.util.spec_from_file_location("s23", "23_desigualdad_genero.py")
s23 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s23)
s19 = s23.s19
s18 = s23.s18


def circles_state(cfg, N, st):
    prev = lambda j: (j - 1) % N
    pairs = []
    for (o, u, s), a in zip(cfg, st):
        orient = (a == s)
        if orient:
            pairs += [(prev(o), u), (prev(u), o)]
        else:
            pairs += [(prev(o), prev(u)), (o, u)]
    return s19.components(N, pairs)


def interlaced_with_other(cfg, i):
    c = cfg[i]
    return any(s18.interlaced(c, d) for j, d in enumerate(cfg) if j != i)


def run(n):
    N = 2 * n
    seen = set()
    st = Counter()
    for m in s23.matchings(list(range(N))):
        for orient in itertools.product([False, True], repeat=n):
            ch = [(b, a) if o else (a, b) for (a, b), o in zip(m, orient)]
            for signs in itertools.product([False, True], repeat=n):
                cfg = tuple(sorted((o, u, s) for (o, u), s in zip(ch, signs)))
                if cfg in seen:
                    continue
                seen.add(cfg)
                allA, allB = [True] * n, [False] * n
                sA = circles_state(cfg, N, allA)
                sB = circles_state(cfg, N, allB)
                if sA + sB != n + 2:
                    continue
                st["genero0"] += 1
                for i in range(n):
                    a_st = list(allA); a_st[i] = False
                    b_st = list(allB); b_st[i] = True
                    dropA = circles_state(cfg, N, a_st) == sA - 1
                    dropB = circles_state(cfg, N, b_st) == sB - 1
                    entr = interlaced_with_other(cfg, i)
                    st[("entrelazada" if entr else "aislada", "A" , dropA)] += 1
                    st[("entrelazada" if entr else "aislada", "B", dropB)] += 1
    print(f"n={n}: diagramas con s_A+s_B = n+2: {st['genero0']}", flush=True)
    for k in sorted(k for k in st if isinstance(k, tuple)):
        print(f"   {k[0]:12s} estado {k[1]}: adecuacion en x = {k[2]!s:5s}  -> {st[k]}")
    viol = st[("entrelazada", "A", False)] + st[("entrelazada", "B", False)]
    rec = st[("aislada", "A", True)] + st[("aislada", "B", True)]
    print(f"   VIOLACIONES de la tesis (entrelazada y NO adecuada): {viol} | aislada pero adecuada (recíproco falla): {rec}", flush=True)


if __name__ == "__main__":
    for n in range(1, (int(sys.argv[1]) if len(sys.argv) > 1 else 5) + 1):
        run(n)
