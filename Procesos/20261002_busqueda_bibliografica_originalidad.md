# Búsqueda bibliográfica sobre la originalidad de la ruta por involuciones (2026-10-02, actualizada 2026-10-05)

Camino que respalda: (A), la base formal. Nada de esto toca el camino (B).
Método: agentes con búsqueda web. Se distingue «LEÍDO en el texto» de «visto en resumen» y de «suposición». Búsquedas web de octubre de 2026; ausencia de resultados no prueba inexistencia.

## Veredicto
1. **L1 (s_A + s_B <= c + 2): no es novedad.** Es la fórmula de Euler de hipermapas/mapas aplicada a la superficie de Turaev.
2. **S5c (adecuación desde género cero y cuerda entrelazada): no es novedad.** Ilyutko–Manturov, arXiv 0810.5522, Lema 6.3, lo prueba por vía combinatoria.
3. **Formalización en Lean: no se encontró formalización previa** de la minimalidad de cruces alternante. Es el aporte que queda, más una posible variante de prueba (ver §2).

## 1. Desigualdad de género (L1)
LEÍDO en el texto:
- Lando–Zvonkin, *Graphs on Surfaces and Their Applications* (PDF de los autores): Def. 1.1.1 (constelación: permutaciones de producto 1 con grupo transitivo), Def. 1.5.1 (hipermapa = 3-constelación) y **Prop. 1.5.3, fórmula (1.4): c(σ)+c(α)+c(φ) = n + 2 − 2g**. La transitividad es hipótesis. El libro no da versión no transitiva.
- Garijo et al., arXiv 2305.03107, Def. 1 de la sección 2: mapas como tres involuciones sin puntos fijos (τ0τ2 = τ2τ0) **sin exigir transitividad**; k(M) componentes, χ = v − e + f, género de Euler eg = 2k − χ >= 0.
- arXiv 2601.14635, Def. 2.1: χ = 2 − 2g (orientable) o 2 − g (no orientable).
Suposición mía, no leída literal: de eg >= 0 se sigue χ <= 2k, que es L1 en el caso no transitivo (2·orb en lugar de 2).
**Corrección:** el informe anterior atribuyó arXiv 1001.2936 a Bryant–Singerman; es Kwon et al. (encajes regulares no orientables de K_{n,n}). Bryant–Singerman 1985 no se leyó.
Citar para L1: Lando–Zvonkin Prop. 1.5.3 y Garijo et al. Def. 1.

## 2. Adecuación desde género cero (S5c)
LEÍDO en el texto (PDF extraído):
- **Ilyutko–Manturov, arXiv 0810.5522, §6:** Lema 6.3, un grafo alternante (género de Turaev 0, k + l = n + 2) es adecuado si y solo si no tiene vértices aislados (vértice aislado = cuerda no entrelazada = cruce nugatorio). Lemas 6.1 y 6.2 (span <= 4n − 4g, y adecuado implica igualdad); Teorema 6.2 (alternante sin vértices aislados es minimal). Prueba: álgebra lineal sobre Z2 y desigualdad de género sobre estados complementarios, sin caras monocromáticas.
  Salvedad del agente: el paso «todos los estados de un círculo equidistan del A-estado» se afirma sin demostración, y la cota sobre el estado opuesto se justifica con «obviamente». Mi prueba en Lean (L2 refinado con puntos fijos de a·b, estado desacoplado aX/bX) podría completar esos pasos de otra manera. Es juicio del agente, sin comparar a fondo.
- Qazaqzeh–Chbili, arXiv 2404.03463: NO contiene el argumento (Jones coloreado y proyectores Jones–Wenzl; hipótesis de igualdad de amplitud).
- Ilyutko–Manturov, arXiv 1001.0384 (survey): solo enuncia la minimalidad (Teorema 5.3), sin prueba ni Lema 6.3.
Citar para S5c: Ilyutko–Manturov 0810.5522, Lema 6.3 y Teorema 6.2.

## 3. Formalizaciones previas
VISTO en las páginas:
- AFP, «Knot Theory» (Prathamesh, 2016): tangles, links enmarcados, corchete de Kauffman e invariancia. La ficha no menciona número de cruces, alternancia ni Tait. Única entrada de nudos del índice de topología.
- TauCeti (Lean), `TauCeti/KnotTheory`: PD codes con corchete y Jones; sin archivos Alternating, Adequate, Span, Tait ni CrossingNumber. NO se abrieron `PDCode/Kauffman.lean` ni `PDCode/Jones.lean`.
- CoursIA issue 2874 (didáctico, 8 `sorry`), leanknot, conway-knots (tangles racionales por coloración): no tocan el teorema.
**No revisado:** Zulip de Lean, búsqueda de código en GitHub (exige login), Coq/Rocq y Agda en particular, arXiv directo.
**Redacción prudente:** «no hemos encontrado formalización previa en AFP, TauCeti, GitHub ni arXiv (búsquedas web, octubre 2026); lo más cercano es Prathamesh (corchete e invariancia) y TauCeti (corchete y Jones sobre PD codes)».

## 4. Seguimiento de los pendientes menores (2026-10-05)

### 4.1 TauCeti (clonado en el scratchpad, commit 3054e6f; LEÍDO en los archivos)
- **No tiene nada de span, grado, adecuación, Turaev, Tait, número de cruces ni diagramas alternantes** (grep sin resultados en `KnotTheory/`; sin `sorry` en esa carpeta). Tu formalización S5–S7 no está duplicada ahí.
- Tiene la infraestructura de base: `kauffmanBracket` como suma sobre estados con `stateLoopCount`; `jonesPolynomial` con invariancia (R1, R3, clasp); y en `PDCode/Planar.lean` caras y planaridad: `eulerChar_toPermutationTriple` (eulerChar = faceCount − n), **`faceCount_le` (faceCount ≤ n + 2·componentes conexas)** e `isPlanar_iff_faceCount_eq_of_isConnected`.
- **Matiz importante:** `faceCount_le` es una desigualdad de tipo Euler para tríos de permutaciones de PD codes, ya formalizada en Lean. Es del mismo tipo que mi L1, pero sobre otra estructura (rotación de cruces, no tres involuciones) y no la relaciona con los estados A/B. No revisé issues ni PRs abiertos del repo.

### 4.2 Comparación de mi S5c con Ilyutko–Manturov (el agente leyó §6 de IM y `SpanNoNugatorio.lean`; no abrió `SpanGenero.lean` ni recompiló)
- Esqueleto global idéntico (cota span <= 4c − 4g, igualdad por adecuación, contradicción con un diagrama de menos cruces). No es original.
- Núcleo distinto: IM compara el estado cambiado con su opuesto, usa la equidistancia de estados de un círculo y una movida en dos vértices; mi prueba usa una sola desigualdad con los 4 puntos fijos del cruce desacoplado (`L2_refinado`) y `orb = 1`.
- Paso 2 de IM (cota del estado opuesto, «obviamente»): mi prueba lo **reemplaza** por la desigualdad general de L1. Paso 4 (equidistancia, sin demostración en su texto): mi prueba lo **evita**.
- Diferencias de alcance: IM cubre grafo-enlaces generales (con corank sobre Z2, citando sin prueba el teorema de Soboleva / Bar-Natan–Garoufalidis); la mía solo diagramas de Gauss de una curva sin libres, pero con círculos = órbitas formalizado. `NonNugatory` es más fuerte que «sin vértices aislados» salvo cuando toda cuerda está entrelazada (S5e); el recíproco no está probado.
- Redacción prudente: «variante distinta del Lema 6.3 dentro del mismo esqueleto», no «resultado nuevo».

### 4.3 Zulip y búsqueda de código en GitHub: NO realizados
Exigen sesión o un buscador que los agentes no tienen, y el comando `gh` de esta máquina no es la CLI de GitHub. Quedan para hacer a mano.

## Pendiente
- Zulip de Lean y búsqueda de código en GitHub con sesión iniciada (a mano).
- Issues y PRs abiertos de TauCeti (span, adecuación).
- Bryant–Singerman 1985 (sec. 2) y Jones–Singerman 1978, no leídos.
- Mirar `faceCount_le` de TauCeti frente a mi L1 (¿se puede reutilizar o comparar?).
