# Búsqueda bibliográfica sobre la originalidad de la ruta por involuciones (2026-10-02)

**Alcance y límites.** Cuatro agentes buscaron en la web. Casi todo se vio en resúmenes y fragmentos de buscador; los PDFs de Lando–Zvonkin salieron ilegibles y Springer pidió autenticación. Las referencias NO están verificadas contra el texto original. Ausencia de resultados no prueba que algo no exista.
Camino que respalda: (A), la base formal. Nada de esto toca el camino (B).

## 1. Desigualdad de género s_A + s_B <= c + 2 (L1 en SpanGenero)
- No se encontró una fuente que la pruebe con un trío de involuciones sobre los 2c extremos y una desigualdad de tipo Riemann–Hurwitz.
- Marco conocido que la implica (visto solo en resúmenes): mapas como tres involuciones sin punto fijo sobre las banderas, con vértices, aristas y caras como órbitas (Bryant–Singerman, Quart. J. Math. Oxford 36, 1985; arXiv 1001.2936). La característica de Euler es 2−g en el caso no orientable, de modo que la desigualdad equivale a chi <= 2.
- Hipermapas y tríos de permutaciones con producto 1: Lando–Zvonkin, *Graphs on Surfaces and Their Applications* (Springer 2004), cap. 1 (sin número de teorema verificado).
- Superficie de Turaev: Turaev 1987, Enseign. Math. 33; Dasbach–Futer–Kalfagianni–Lin–Stoltzfus (arXiv math/0605571); Champanerkar–Kofman, survey (arXiv 1406.1945). Lo vieron por resumen; el método de prueba no se verificó.
- Herramienta combinatoria más cercana (permutaciones sobre extremos de cuerdas, género por ciclos): Cohn–Lempel (arXiv 0904.4361) y Traldi (arXiv 0911.5504). No se vio que la apliquen a s_A + s_B.
- **Lectura honesta:** es muy probable que L1 sea una instancia de la fórmula de Euler para mapas, aplicada a la superficie de Turaev. Presentarla como «aplicación directa de la fórmula de Euler para hipermapas/mapas», sin reclamarla como resultado nuevo.

## 2. Adecuación desde género cero y cuerda entrelazada (S5c)
- El enunciado «género de Turaev 0 y reducido => adecuado => span = 4c» es conocido por la vía geométrica (Turaev 1987).
- La ruta puramente combinatoria (código de Gauss, desigualdad de género sobre el estado desacoplado en un cruce, L2 refinado con puntos fijos) no apareció citada.
- Más cercanas, por abrir: Qazaqzeh–Chbili (arXiv 2404.03463, ancho del Jones = c − g_T implica adecuado) y graph-links de Ilyutko–Manturov (arXiv 0810.5522, 1001.0384).
- **Lectura honesta:** posible novedad solo como presentación, sin confirmar.

## 3. Formalizaciones previas
- Teorema de minimalidad de cruces alternantes (Kauffman–Murasugi–Thistlethwaite): no se encontró formalización en ningún asistente de pruebas. Tampoco género de Turaev ni adecuación.
- Corchete de Kauffman en Isabelle/HOL: Prathamesh, ITP 2015 (LNCS 9236), Archive of Formal Proofs; invariancia del corchete para links enmarcados.
- Lean 4, TauCeti (github.com/TauCetiProject/TauCeti), directorio KnotTheory: PD-codes, Gauss, Temperley–Lieb; en PRs #10703, #7395 y #7405, R1 y R2 orientados, con R3 pendiente. Sin alternantes ni número de cruces. Proyecto en movimiento: conviene revisarlo.
- Otros: shua/leanknot, jsboige/CoursIA (issue 2874). Nada del teorema.
- **Redacción prudente:** «hasta donde sabemos, no existe formalización previa». Antes de decirlo en público, hacer GitHub code search («Kauffman», «alternating») y revisar el índice del AFP, que no se hicieron.

## Pendiente para confirmar con texto completo
Lando–Zvonkin cap. 1; Jones–Singerman 1978; Bryant–Singerman 1985 sec. 2; Turaev 1987; Lickorish cap. 5; Qazaqzeh–Chbili; Ilyutko–Manturov.
