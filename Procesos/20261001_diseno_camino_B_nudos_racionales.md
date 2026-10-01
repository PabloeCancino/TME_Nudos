# Diseño del camino (B): clasificación de nudos racionales (SEPARADO de (A))

**Fecha:** 2026-10-01 · **Estado:** DISEÑO, no implementado. Decisión del autor (bitácora, sección `000000000`): (A) es la base formal y (B)
es un objetivo declarado pero separado. Este documento NO modifica ni depende de las conclusiones de (A) más allá de reutilizarlas.

## 1. Qué es (B) y qué no es
* **Es:** trabajar con la equivalencia de NUDOS (no solo de diagramas módulo R1/R2): diagramas módulo R1, R2 **y R3**, con la
  clasificación de los nudos racionales (2-puentes) por su fracción continua `p/q`.
* **No es:** una demostración de topología. El teorema de Reidemeister (equivalencia de diagramas ⇔ isotopía ambiental) y la
  clasificación de Schubert (1956) son resultados de la literatura y NO se formalizan desde cero. Se usan como convención o como
  axiomas citados, siempre etiquetados.
* **Por qué (A) no basta:** sin R3 ni flypes, el mismo nudo tiene formas normales distintas desde n = 7 (sondas 19 y 19b).

## 2. Marco formal disponible (reutilizable)
| Pieza | Dónde | Estado |
|---|---|---|
| Equivalencia de nudos como `GRel` (isomorfismo, R1, R1 libre, R2, R3) y `NudoV` | `Etapa1_Nudos.lean` | demostrada, sin axiomas |
| Invariancia del corchete de Kauffman y del Jones bajo `GRel` (`jones_rel`) | `Etapa1_*` | demostrada |
| Trébol ≠ espejo ≠ trivial; granny ≠ square (por Jones) | `Etapa1_Nudos.lean` | demostrado |
| Planaridad exacta por género 0 (caras de σ∘α) | `Etapa1_Planaridad.lean` | demostrada |
| `ClassicalKnot` (planares módulo pasos entre planares) | `Etapa1_Clasico.lean` | demostrado |
| Forma normal de diagramas módulo R1/R2 (A) | `FormaNormal.lean` | demostrada |
| Axiomas de Schubert (25) y `jones2` | `Schubert.lean` | citados |

La noción de equivalencia de (B) es `GRel`/`NudoV` de la capa de Gauss, porque es la única con la invariancia del Jones demostrada.
La palabra de `FormaNormal.lean` y el `Word` de `Etapa1_GaussWord.lean` son la misma idea; el puente entre ambos se construye en la fase B2.

## 3. Hechos de la literatura que (B) usa (a transcribir como axiomas etiquetados, NO como verdades propias)
1. **Schubert (1956):** los nudos racionales `K(p/q)` y `K(p'/q')` son equivalentes si y solo si `p = p'` y `q' ≡ q^{±1} (mod p)`
   (módulo imagen especular según la orientación considerada).
2. **Tait / Menasco-Thistlethwaite (1993), conjetura del flyping:** dos diagramas alternantes reducidos del mismo nudo se
   relacionan por una sucesión de flypes.
3. **Kauffman, Murasugi y Thistlethwaite:** un diagrama alternante reducido tiene el menor número de cruces entre todos los
   diagramas de su nudo; la demostración usa el span del corchete de Kauffman.
4. **Conway:** todo nudo racional admite una forma normal `C(a₁, …, a_k)` (diagrama de 4 trenzas).

**Regla heredada de la auditoría:** ningún axioma se admite sin (a) transcribir fielmente un teorema publicado, (b) sondar si deriva
`False` junto con el resto, y (c) comprobarlo por cálculo en n ≤ 8. El axioma falso `reconstruct_from_first` es la lección.

## 4. Hallazgo que da peso a (B): el span del Jones puede PROBAR la minimalidad real
El punto 3 no tiene por qué ser un axioma. Para un diagrama alternante reducido de `n` cruces, el span del corchete de Kauffman vale
`4n`; para cualquier diagrama de `c` cruces vale como mucho `4c`. Como el Jones es invariante bajo `GRel` (ya demostrado), se obtiene:
**un diagrama alternante reducido de n cruces tiene n cruces mínimos entre TODOS los diagramas equivalentes por R1, R2 y R3.**
Esa es la minimalidad a nivel de nudo, que el axioma A6 de `Basic` intentaba afirmar y no podía.
* Ingrediente combinatorio: las contribuciones de los estados «todo A» y «todo B» ocupan los grados extremos y no se cancelan en
  un diagrama alternante reducido, porque `s_A + s_B = n + 2` (con `s_A`, `s_B` los círculos de cada estado), igualdad que usa la
  PLANARIDAD (la fórmula de Euler de la sección 2). Es la misma maquinaria de caras de `Etapa1_Planaridad.lean`.
* **CORRECCIÓN DOBLE (sondas 22b y 22c).** La sonda 22b (n ≤ 4) pareció indicar que «reducido» equivale a «sin R1/R2» en alternantes; eso es FALSO en general y el primer contraejemplo aparece en n = 7. Lo que sí vale:
  * (a) todo candidato R1 es una cuerda aislada, luego **reducido ⇒ sin R1** (y en alternantes, sin R2 siempre, porque R2 exige pasos superiores consecutivos y en un alternante los consecutivos alternan). Es decir, **reducido ⇒ irreducible**.
  * (b) el recíproco FALLA: dos tréboles unidos por una cuerda aislada (cuerda `(0,7)` con un trébol en cada arco; n = 7) es planar, alternante, tiene una cuerda aislada y NO tiene ningún candidato R1 ni R2 (sonda 22c). Una cuerda aislada con bloques entrelazados a ambos lados no tiene extremos adyacentes. Por eso a partir de n = 7 hay más irreducibles (788) que reducidos (676).
* **Consecuencia para (A) y (B).** Las palabras irreducibles de (A) NO son todas diagramas reducidos de (B): los reducidos son un subconjunto propio. El teorema del span necesita la hipótesis EXPLÍCITA «sin cuerdas aisladas»; no se deduce de (A). La relación es: reducido ⇒ irreducible, pero no al revés.
* Dificultad: media-alta, pero acotada y sin literatura externa. Es el entregable de mayor valor científico de (B).

## 5. Fases
**B0. Definiciones.** Palabras de Conway `conway [a₁,…,a_k]` como `Word`, con su signo y su cruce alternante; la fracción `p/q`;
el diagrama vacío y el nudo trivial. Referencia en Python y validación contra el censo de las sondas (todo diagrama planar,
alternante y reducido hasta n = 7 debe tener Jones igual al de una forma de Conway).

**B1. Censo por cálculo (Python, sondas 22 a 25).** (22) implementar el flype sobre palabras de Gauss y calcular las clases
módulo flype, rotación y reflexión hasta n = 8; (23) comprobar que esas clases coinciden con las clases de Jones salvo imagen
especular; (24) comprobar `s_A + s_B = n + 2` y que los coeficientes extremos del corchete no se anulan en alternantes reducidos;
(25) contrastar el número de clases racionales con tablas publicadas de nudos de 2 puentes. No se citan cifras de memoria.

**B2. Certificados formales en Lean (n ≤ N).**
* *Distintos:* dos nudos son distintos si sus Jones en `A = 2` difieren (ya hay `jones_rel`, `jones_ofWord`); da una tabla
  verificada de nudos racionales distintos hasta N.
* *Iguales:* certificados de equivalencia como sucesiones de movimientos. Para no construir términos `GRel` enormes, un
  VERIFICADOR booleano de caminos sobre `Word` con demostración de corrección (`checkPath p = true → GRel (ofWord a) (ofWord b)`),
  y cada certificado se verifica con `decide`. Requiere el puente `Word` de `FormaNormal` ↔ `GDiag` de `Etapa1_Puente`.
* Resultado: una tabla de clasificación de nudos racionales hasta N, con equivalencias y no equivalencias VERIFICADAS, sin
  axiomas de la literatura.

**B3. El span y la minimalidad (el teorema de mayor valor).** Demostrar `span (bracket w) = 4n` para `w` alternante, planar y
reducido; de ahí, minimalidad de cruces a nivel de nudo. Después, la capa de axiomas citados (Schubert, flyping) separada y
etiquetada, solo para los enunciados que no se logren demostrar, con sondas de consistencia como en el modelo `jones2`.

**B4 (abierto, investigación).** Demostrar para todo n que un diagrama alternante reducido de un nudo racional es equivalente por
flypes a su forma de Conway. Exige teoría estructural de tangles racionales. No se compromete.

## 6. Relación con (A)
* (A) da, a nivel de diagrama, la forma normal única módulo R1/R2: «irreducible ⇒ grado mínimo». (B) añade R3 y flypes.
* La minimalidad de (A) vale para la relación R1/R2; la de (B3) vale para TODA la equivalencia de nudos, y es estrictamente más fuerte
  para diagramas alternantes reducidos.
* Es razonable que el teorema de (B3) enuncie: «`w` alternante reducido e irreducible por (A) ⇒ `w` tiene el mínimo de cruces entre
  todos los diagramas de su nudo».

## 7. Riesgos
| Riesgo | Mitigación |
|---|---|
| Admitir un axioma de la literatura mal transcrito (como `reconstruct_from_first`) | Regla de la sección 3: transcripción fiel, sonda de `False` y verificación por cálculo n ≤ 8 |
| El flype es un movimiento no local sobre listas; su implementación puede ser frágil | B1 lo valida por cálculo y por la coincidencia con las clases de Jones antes de tocar Lean |
| El puente entre `Word` y `GDiag` es el cuello de botella de B2 | Empezar por los movimientos que ya tienen el lema de invariancia (R1, R2) y añadir R3 al final |
| El span exige entender los estados extremos con signos y orientación | La sonda 22 ya lo comprueba (ver sección 10); formalizar después |
| Que (B4) resulte inabarcable | Se declara abierto; B0 a B3 ya forman un resultado completo sin él |

## 8. Orden recomendado y criterio de éxito
1. **B1** (cálculo): barato, y decide si el resto es viable.
2. **B3** antes que B2: el teorema del span es el de mayor valor y no depende del puente `Word`↔`GDiag` de certificados.
3. **B2** para la tabla verificada.
4. B4 solo si todo lo anterior sale.

**Éxito mínimo:** B3 demostrado (minimalidad real de cruces para alternantes reducidos) o la tabla verificada de B2 hasta n = 7.

## 9. Qué NO promete
No demuestra la clasificación de Schubert ni el teorema de Reidemeister; no cubre nudos no racionales; no cambia nada de (A).

## 10. Resultados de la fase B1 hechos hasta ahora

**Sonda 22 (span del corchete, exhaustiva para diagramas alternantes planares):**

| n | reducidos | con span = 4n | no reducidos | con span < 4n |
|---|---|---|---|---|
| 2 | 0 | 0 | 16 | 16 |
| 3 | 4 | 4 | 80 | 80 |
| 4 | 8 | 8 | 512 | 512 |
| 5 | 24 | 24 | 3 568 | 3 568 |
| 6 | 168 | 168 | 26 624 | 26 624 |

| 7 | 676 | 676 | 210 736 | 210 736 |

Cumplimiento del 100 %: reducido ⇒ span = 4n; no reducido ⇒ span < 4n. Tampoco hubo ningún reducido con `s_A + s_B ≠ n + 2` (n ≤ 6). El teorema del span (B3) es viable por cálculo. OJO: en alternantes, reducido ⇒ irreducible pero NO al revés (sección 4, sonda 22c).

**Pendiente de B1:** flypes y clases de Jones (sondas 23 a 25 del plan), n = 7 y 8, y la contrastación con tablas de nudos racionales.
