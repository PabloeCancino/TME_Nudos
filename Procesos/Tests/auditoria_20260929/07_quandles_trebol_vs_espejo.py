# EXPERIMENTO (2026-09-29). Busca quandles finitos cuyo número de coloraciones distinga el trébol de su espejo.
# Resultado: ninguno entre las tablas de orden 2 a 6 (1, 5, 36, 404 y 6658 tablas etiquetadas de orden 2, 3, 4, 5 y 6).
# Uso: python 07_quandles_trebol_vs_espejo.py N   (N = orden; solo se explora ese orden).
"""Busca quandles finitos que distingan el trébol de su espejo por número de coloraciones.

Convención: x*y = x ▷ y (operación derecha). Axiomas: (1) x*x = x; (2) y -> x*y es biyectiva
(para cada y fija, x -> x*y biyectiva); (3) (x*y)*z = (x*z)*(y*z).
Trébol: (x,y,z) con z = x*y, x = y*z, y = z*x.
Espejo: la misma condición con la operación inversa (x *^-1 y).
"""
import itertools
import sys

sys.setrecursionlimit(10000)


def quandles(n):
    """Genera todas las tablas de quandle de orden n (columnas: para cada y, x -> x*y es permutación con y*y=y)."""
    perms = list(itertools.permutations(range(n)))
    cols = []
    for y in range(n):
        cols.append([p for p in perms if p[y] == y])  # x*y = p[x], con y*y = y

    table = [None] * n  # table[y] = permutación p_y: x*y = p_y[x]

    def check_partial(upto):
        # verifica distributividad para las columnas ya fijadas
        for y in range(upto + 1):
            for z in range(upto + 1):
                py, pz = table[y], table[z]
                for x in range(n):
                    # (x*y)*z == (x*z)*(y*z)
                    a = pz[py[x]]
                    b = table[py_z(pz, y)][pz[x]] if py_z(pz, y) <= upto else None
                    if b is not None and a != b:
                        return False
        return True

    def py_z(pz, y):
        return pz[y]  # y*z

    res = []

    def rec(y):
        if y == n:
            # comprobación completa
            ok = True
            for a in range(n):
                for b in range(n):
                    pa, pb = table[a], table[b]
                    for x in range(n):
                        if pb[pa[x]] != table[pb[a]][pb[x]]:
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    break
            if ok:
                res.append(tuple(tuple(t) for t in table))
            return
        for p in cols[y]:
            table[y] = p
            if check_partial(y):
                rec(y + 1)
        table[y] = None

    rec(0)
    return res


def inv_perm(p):
    q = [0] * len(p)
    for i, v in enumerate(p):
        q[v] = i
    return tuple(q)


def count_trefoil(tab, n, op_inverse=False):
    if op_inverse:
        tab = tuple(inv_perm(p) for p in tab)  # x *^-1 y = inv(p_y)[x]
    star = lambda x, y: tab[y][x]
    c = 0
    for x in range(n):
        for y in range(n):
            z = star(x, y)
            if star(y, z) == x and star(z, x) == y:
                c += 1
    return c


def iso_key(tab, n):
    return None


def main():
    maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    for n in range(maxn, maxn + 1):
        qs = quandles(n)
        found = []
        for q in qs:
            a = count_trefoil(q, n, False)
            b = count_trefoil(q, n, True)
            if a != b:
                found.append((a, b, q))
        print(f"orden {n}: {len(qs)} tablas de quandle; distinguen trébol/espejo: {len(found)}")
        for a, b, q in found[:2]:
            print("   col(trébol)=", a, " col(espejo)=", b)
            print("   tabla (columna y -> [x*y para x=0..]):", q)


main()
