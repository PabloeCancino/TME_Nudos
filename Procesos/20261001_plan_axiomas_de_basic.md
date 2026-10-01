# Plan: los cinco axiomas de `Basic`, de axioma a teorema (n ≤ 4)

**Fecha:** 2026-10-01 · **Estado:** PLAN, con un hallazgo previo ya demostrado (sección 1).
**Objetivo:** reducir lo axiomático de `Basic.lean` donde se pueda **demostrar**, empezando por lo que un cálculo exhaustivo sobre n ≤ 4 permite decidir. Es el paso que más cambia el valor científico del proyecto: hoy la clasificación general descansa en axiomas que nunca se han puesto a prueba.

## 1. Hallazgo previo: `reconstruct_from_first` es FALSO

Prueba en Lean: `Procesos/Tests/auditoria_20260929/16_refuta_reconstruct_from_first.lean`.

El axioma dice: si dos configuraciones de `n` cruces tienen las mismas razones modulares **índice a índice**, entonces existe un desplazamiento uniforme `k` con `over₂ᵢ = over₁ᵢ + k` para todo `i`.

Contraejemplo con `n = 3` (`ZMod 6`, signos todos `+`): `KA = [(0,3), (1,4), (2,5)]` y `KB = [(0,3), (2,5), (1,4)]`. Las razones coinciden (3, 3, 3) y las posiciones superiores son `(0,1,2)` frente a `(0,2,1)`, que no difieren en una constante. Con el axioma se deriva `False` (`#print axioms` lo muestra dependiendo de él).

**Consecuencia.** Todo lo que depende de `reconstruct_from_first` no es fiable: `rotation_of_ratio_pos_eq`, `same_IME_implies_rotation`, `same_SIME_implies_rotation` e `IME_complete` (esta última por la cadena de dependencias). Los resultados que no lo usan siguen valiendo; entre ellos todo `TCN_*`, la capa de Gauss, la planaridad y `ClassicalKnot`.

**Causa probable.** El enunciado compara cruces por su *índice* en `Fin n`, no como conjunto. Permutar los índices de un mismo diagrama cambia la lista sin cambiar el nudo. La versión pretendida (la implementación Python original) suponía los cruces ordenados canónicamente.

## 2. Los cinco axiomas

| Axioma | Qué afirma | Qué se sabe | Ataque | Prioridad |
|---|---|---|---|---|
| `reconstruct_from_first` | mismas razones ⇒ posiciones salvo desplazamiento | **Falso** (n = 3) | reparar el enunciado y probar el caso corregido por `decide` | **1** |
| `minimal_isotopic_implies_rotation` (A7) | dos configuraciones mínimas isotópicas son rotación una de otra | **Muy probablemente falso en el modelo** (Fase 0 hecha, sección 3.1): las transiciones R1/R2 son laxas (comparan conjuntos de pares razón-signo, no posiciones) | demostrar la falsedad con un invariante de grado, o reparar las transiciones | **2** |
| `axiom_irreducible_is_minimal` (A6) | irreducible ⇒ grado mínimo de su clase | Falso en general para diagramas no alternantes (el desenredo de Goeritz, 10 cruces). Para n ≤ 4 podría ser cierto | comprobar en n ≤ 4 que ninguna configuración alcanzable por R3 y rotación es reducible | 3 |
| `to_continued_fraction` | asigna una fracción continua a cada configuración | Es una función opaca: no hay nada que probar | definirla de forma concreta (sobre las realizables) | 4 |
| `schubert_classification` | isotópicos ⇔ fracciones continuas iguales módulo 1 | Cita de Schubert (1949), pero el enunciado cubre configuraciones **no planares**, para las que no hay nudo | restringirla a las realizables y probar n ≤ 4 | 5 |

## 3. Fases

### Fase 0. Sondas de falsedad (barata, antes de probar nada)
Para cada axioma se intenta **derivar `False`** o encontrar un contraejemplo por búsqueda exhaustiva, antes de invertir en una demostración. La sonda 16 ya lo hizo con `reconstruct_from_first`. Falta:
- **A7:** buscar `K1` irreducible con un triple R3-candidato (`is_R3_candidate`) y `K2` con el mismo `SIME` pero que no sea rotación de `K1`. Si existe, `A6 + A7 + R3` dan `False`.
- **A6:** para n ≤ 4, calcular la componente de `K` bajo R3 y rotación y comprobar que no contiene configuraciones reducibles.
**Criterio de salida:** cada axioma queda marcado como *refutado*, *no refutado hasta n ≤ 4* o *no evaluable*, con el archivo de prueba que lo respalda.

### 3.1 Resultado de la Fase 0 para A7 (sondas 17 y 17b, hecho el 2026-10-01)

**(a) `is_R3_candidate` es vacuo.** En n = 3 y n = 4 (5 760 y 645 120 configuraciones indexadas) NO hay ninguna con un triple R3-candidato. Razón: la condición de "orden cíclico" de las seis posiciones obliga a que las tres cuerdas se crucen entre sí dos a dos, y a la vez el candidato exige que exactamente un par NO se crucen. Son incompatibles. Luego `Isotopic.R3_move` nunca se activa, y mi sospecha inicial sobre R3 (la tabla original de este plan) era errónea. Falta la demostración general en Lean (`¬ is_R3_candidate K i j k`); solo está comprobado por cálculo para n ≤ 4.

**(b) La laxitud real está en R1/R2.** `is_R1_transition` e `is_R2_transition` solo exigen que el CONJUNTO de pares (razón, signo) de `K'` coincida con el de `K` sin los cruces eliminados, no que se respeten posiciones, multiplicidades ni orden. Como `Isotopic` es simétrica y transitiva, dos configuraciones del mismo grado quedan unidas si ambas son objetivo de un mismo `K''` de grado mayor.

**(c) Resultado de la sonda 17b** (grados 1 a 4): hay 720 configuraciones `K1` de grado 3, sin candidatos R1/R2, cuya clase no baja de grado 3 dentro de la cota y que están unidas a una de grado 4, con un `K2` del mismo conjunto que NO es rotación de `K1`. Ejemplo: `K1 = [(0,2,−), (1,4,−), (5,3,+)]` y `K2 = [(0,2,−), (4,1,−), (5,3,+)]` (el segundo cruce con over y under intercambiados). Con eso A7 se contradice, salvo que `min_degree K1 ≠ 3`.

**(d) Lo que NO está demostrado.** La contradicción formal exige `n = min_degree K1`, es decir, que la clase de `K1` no contenga ningún grado menor, en TODOS los grados (la sonda solo mira hasta 4). Eso requiere un invariante. Un candidato natural (podar los pares de razón ±1) falla porque R2 puede eliminar pares de razón intermedia. Por tanto el estado correcto es: **A7 no está refutado formalmente, pero hay evidencia fuerte de que es falso en el modelo actual**, y el defecto está en las transiciones, no en el axioma.

**Consecuencia para el plan.** Reparar A7 sin reparar las transiciones no sirve. Las transiciones R1/R2 deben ser biyectivas: `K'` obtenido de `K` por una renumeración que respete posiciones, no por igualdad de conjuntos.

### 3.2 Resultado de la Fase 1: qué es cierto de verdad (sondas 18 y 18b, 2026-10-01)

**La reparación no es solo de indexado.** Los teoremas `rotation_of_ratio_pos_eq` y `same_IME_implies_rotation` están enunciados para configuraciones ARBITRARIAS, así que son falsos como teoremas, no solo el axioma. Ejemplo (n = 3, todos `+`): `(0,3),(1,4),(2,5)` (configuración especial, NO planar) y `(0,3),(4,1),(2,5)` (el trébol) tienen las mismas razones y signos y no son rotación una de otra. Es decir, **ni el IME ni el SIME son invariantes completos en general.**

**Qué sí es cierto** (invariante `SIMEcic` = lista de pares (razón, signo) en orden creciente de la posición superior, mínima por rotación cíclica; colisión = dos clases de rotación distintas con el mismo `SIMEcic`):

| Conjunto de configuraciones | n = 3 | n = 4 | n = 5 |
|---|---|---|---|
| todas | 28 colisiones | 546 | 15 784 |
| planares | **0** | 1 | 14 |
| planares sin candidato R1/R2 | **0** | 1 | **0** |
| **planares, alternantes y sin candidato R1/R2** (sonda 18b) | **0** | **0** | **0** |

La última fila se mantiene sin colisiones hasta **n = 7** (n = 6: 168 configuraciones en 18 clases; n = 7: 788 en 58). Las colisiones de n = 4 y n = 5 en las filas intermedias son diagramas **no alternantes**, para los que "sin candidato R1/R2" no implica mínimo (por ejemplo `(0,3,−),(1,6,−),(2,5,+),(7,4,+)`, con pasos superiores consecutivos 0, 1, 2).

**Enunciado reparado (candidato).** Para configuraciones planares, alternantes y sin candidato R1/R2, el `SIMEcic` determina la clase de rotación. Comprobado por cálculo hasta n = 7; no hay demostración general.

**Dos consecuencias.**
1. La dirección «mismo SIME ⇒ isotópicos» de `IME_complete` es falsa tal como está (la hipótesis "irreducible" admite diagramas no alternantes con igual SIME y sin ser rotación); debe restringirse a planares alternantes. CORRECCIÓN (2026-10-01): `isotopic_irreducible_same_SIME` (la dirección «isotópicos ⇒ mismo SIME») NO queda refutada por estas colisiones: depende de A6 y A7, que son sospechosos pero no refutados formalmente.
2. La noción formal de "irreducible" (sin R1/R2) NO es "mínimo" fuera de los diagramas alternantes, así que A6 (`axiom_irreducible_is_minimal`) tampoco puede ser cierto en general; en el modelo actual R3 es vacuo y no puede reducir esos casos.

**Lo que falta para la Fase 1 formal:** definir `SIMEcic` e índices ordenados en Lean, enunciar el teorema para n = 3 y n = 4 (n = 3 ya está cubierto por `TCN_06`: 4 configuraciones realizables) y probarlo con `decide +kernel`, enumerando por posición superior ordenada para no recorrer las 645 120 configuraciones indexadas de n = 4.

### 3.3 Fase 1 formal: HECHA (rama `reconstruccion`, `TMENudos/Reconstruccion.lean`, 2026-10-01)

Compila en ~5 min, sin `sorry`, axiomas ni `native_decide`; los teoremas principales dependen solo de `propext`, `Classical.choice` y `Quot.sound`. Importa solo `Basic` (no modifica nada).

* **Teorema reparado, `reconstruccion_3`, `reconstruccion_4`, `reconstruccion_5`:** para `K₁ K₂ : RationalConfiguration n` ordenadas y alternantes (`SortedAlt`), `Planar` y sin candidatos R1/R2 (`NoCand`), `SIMEcic K₁ = SIMEcic K₂` implica que existen un reindexado cíclico `j` y una rotación `k` con `K₂.crossings (i + j) = rotate_crossing k (K₁.crossings i)`.
* **Variante sin planaridad, `reconstruccionNP_3` y `reconstruccionNP_4`:** la planaridad es redundante para n = 3 y 4. Para n = 5 NO se prueba: `checkNP 5` supera 10 minutos en el kernel y una build conjunta con ella abortó Lean (código 0xC0000409).
* **Puente general en n (`bridge`):** toda `K` con `SortedAlt` es `buildL p σ s` (posiciones superiores `2i + p`, inferiores `2σ(i) + 1 − p`). También `noCand_iff`, `SIMEcic_eq`, `rot_of_relB` y la reducción `main_gen`.
* **Conteos por `decide +kernel`:** `cands_3/4/5` = 96, 768, 7680; configuraciones válidas 4, 8, 24; clases de SIME 2, 2, 4 (coinciden con la sonda 18b).
* **Contraejemplos probados que justifican cada hipótesis:** (a) `kA`/`kB` (sonda 16): sin ordenación la conclusión falla; (b) `tA` (trébol) y `kA`: mismo `SIMEcic`, no rotación, `kA` no es planar ni alternante; (c) `mA`/`mB` de n = 4: planares, sin candidatos, mismo `SIMEcic`, no rotación, no alternantes.
* **Dependientes del axioma falso** (calculado con `CollectAxioms`): `rotation_of_ratio_pos_eq`, `same_IME_implies_rotation`, `same_SIME_implies_rotation`, `IME_complete`.

**Qué NO se logró:** el enunciado para n general (solo n = 3, 4, 5 por cálculo exhaustivo); la Fase 3 (restringir los teoremas de `Basic`); A6 y A7 siguen sin resolverse.

### 3.4 Hallazgo que cambia el rumbo: A7 es falso también en la teoría clásica (sondas 19 y 19b, 2026-10-01)

**Prueba.** Se enumeran las configuraciones planares, alternantes y sin candidato R1/R2 y se calcula su
polinomio de Jones (corchete de Kauffman por estados, misma convención que `Etapa1_GaussWord.lean`).
Se agrupa por Jones y se compara con las clases de rotación y las clases diédricas (rotación más
reflexión del sentido de recorrido).

| n | clases de rotación | clases diédricas | valores de Jones | Jones con >1 clase diédrica |
|---|---|---|---|---|
| 3 | 2 | 2 | 2 | 0 (trébol derecho e izquierdo) |
| 4 | 2 | 1 | 1 | 0 (el nudo de ocho, anfiquiral) |
| 5 | 4 | 4 | 4 | 0 (5₁ y 5₂ con sus espejos) |
| 6 | 18 | 9 | 8 | 1 (sonda 19b: un par «primo») |
| 7 | 58 | 38 | 19 | 11 (6 pares primos y 5 compuestos) |

La verificación de cordura pasa: los valores de n = 3, 4 y 5 son los nudos esperados.

**Lectura.**
* **n = 6:** el par primo tiene las mismas cuerdas y TODOS los signos invertidos. Es la simetría de un
  nudo anfiquiral (6₃): el mismo nudo con un diagrama y su imagen especular. No es un flype.
* **n = 7:** hay pares primos con SIGNOS IGUALES y cuerdas distintas, p. ej.
  `(2,9),(4,11),(6,13),(8,1),(10,7),(12,5)` frente a `(2,9),(4,13),(6,11),(8,1),(10,5),(12,7)` (todos
  `−`). Son diagramas alternantes reducidos NO isomorfos con el mismo Jones: candidatos a **flype**
  (conjetura de Tait, teorema de Menasco-Thistlethwaite). Igual Jones no prueba que sean el mismo nudo,
  pero con n ≤ 7 y diagramas alternantes reducidos es la explicación esperada.

**Consecuencia.** Con una isotopía FIEL (R1, R2 y R3 reales), dos diagramas mínimos del mismo nudo no
tienen por qué ser rotación uno del otro: difieren por flypes y por simetrías (reflexión, anfiquiralidad).
Por tanto A7 (`minimal_isotopic_implies_rotation`) es FALSO para la teoría clásica de nudos a partir de
n = 7, y `isotopic_irreducible_same_SIME` ("isotópicos ⇒ mismo SIME") también. Esto es independiente de
la laxitud de las transiciones (sección 3.1): reparar las transiciones R1/R2 no puede hacer cierto A7.

**Qué sí puede ser cierto** (hipótesis a estudiar, NO demostrada):
1. El SIME de la FORMA NORMAL de Conway/Schubert (un representante canónico por nudo racional) clasifica
   los nudos racionales: es la lectura correcta de "T5: existencia y unicidad de la forma normal".
2. `Isotopic` restringido a R1/R2 más rotación (sin flypes ni R3), donde A6/A7 se pueden decidir para
   n ≤ 4 por cálculo exhaustivo sobre transiciones biyectivas.
3. Sustituir A7 por el enunciado correcto: "minimales isotópicos ⇒ equivalentes por flypes y simetrías",
   que es el teorema de Menasco-Thistlethwaite (se citaría como axioma de la literatura, no como propio).

### 3.5 Fase 3 HECHA: `Basic` coherente con lo publicado (rama `fase3-basic`, 2026-10-01)

Verificación: los 48 módulos de `TMENudos/` compilan por nombre y en serie (19 min 44 s), 0 errores y 0
alertas. Axiomas de `Basic`: 5 → 4 (total del proyecto 50 → 49).

* **`reconstruct_from_first` eliminado.** Su conclusión es ahora la definición `UniformOverShift K₁ K₂`
  (desplazamiento uniforme de las posiciones superiores), usada como HIPÓTESIS.
* **Tres teoremas reparados y demostrados sin axiomas propios** (solo `propext` y `Quot.sound`):
  `rotation_of_ratio_pos_eq`, `same_IME_implies_rotation`, `same_SIME_implies_rotation`; todos con la
  hipótesis `UniformOverShift`.
* **`IME_complete`:** la dirección «mismo SIME ⇒ isotópicos» exige el principio de reconstrucción `h_rec`
  como hipótesis explícita; la dirección «isotópicos ⇒ mismo SIME» sigue dependiendo de A6 y A7, y por la
  sección 3.4 es falsa para la isotopía fiel a partir de n = 7.
* **A6 y A7** llevan en su documentación el estado de sospecha y la referencia a las sondas.
* Los cuatro teoremas solo se usaban dentro de `Basic`: ningún otro módulo cambió.

### 3.6 Transiciones fieles R1/R2 (sonda 20, 2026-10-01): A6 se sostiene y A7 es cierto salvo reetiquetado

**Modelo.** `Isotopic` reparado: rotación, R1 y R2 con transiciones BIYECTIVAS (se quitan los cruces
eliminados, las posiciones restantes se renumeran por rango y los índices saltan los quitados), y sus
inversas (simetría); R3 queda fuera por ser vacuo (sonda 17). Es el modelo «solo R1, R2 y rotación»,
sin flypes. Cerradura acotada a grado ≤ 5.

**Resultado para n = 3** (220 clases de rotación de configuraciones irreducibles, indexadas):

| Pregunta | Resultado |
|---|---|
| A6: ¿irreducible ⇒ grado mínimo n? | **Se cumple**: 0 contraejemplos en 220 |
| A7 literal: ¿todo K₂ de grado 3 de la clase es rotación EXACTA de K₁? | **Falla en 220 de 220**: cada clase tiene 5 miembros que no son rotación |
| ¿Algún K₂ es un diagrama distinto incluso reindexando? | **0 de 220**: los 5 son las otras 5 permutaciones de los índices (3! − 1) |

**Lectura.** A7 falla solo por el etiquetado `Fin n` de `RationalConfiguration`; es verdadero para la
relación R1/R2/rotación «salvo permutación de índices»: `∃ k σ, K₂ = rotate k (K₁ ∘ σ)`. Para n = 3 y
grados ≤ 5.

**Hallazgos combinados (3.4 + 3.6).**
* Sin R3 (solo R1, R2 y rotación), el A7 reformulado «salvo permutación de índices» es plausible; A6 también.
* Con una isotopía fiel completa (con R3 y flypes), A7 es falso desde n = 7 (sección 3.4).
* Por tanto la reparación correcta del modelo de `Basic` NO es hacer cierto el A7 actual, sino:
  (a) cambiar su conclusión a «salvo permutación de índices», y (b) declarar que la relación `Isotopic`
  de `Basic` es R1/R2/rotación y NO la isotopía de nudos, con lo cual la clasificación que se obtiene es
  de DIAGRAMAS irreducibles módulo R1/R2, no de nudos.

### Fase 1. Reparar y probar `reconstruct`
1. Sonda Python exhaustiva (n ≤ 6) de candidatos de enunciado: (a) añadir la hipótesis de que los cruces están ordenados por posición superior; (b) comparar como multiconjuntos de `(razón, signo)`; (c) exigir el desplazamiento solo salvo permutación de índices.
2. Elegir el candidato que no admita contraejemplos y cuyo enunciado sea el que realmente usan los teoremas dependientes.
3. Formalizarlo y probarlo para n = 3 y n = 4 con `decide +kernel` sobre las configuraciones finitas.
4. Sustituir el axioma por: un teorema para cada n ≤ 4, y el enunciado general **marcado como conjetura**, no como axioma, si no se logra la demostración general.

### Fase 2. A7 y A6
Con el mismo método: si la sonda no encuentra contraejemplo, repararlo y probarlo para n ≤ 4. Si lo encuentra, es un hallazgo y el axioma se sustituye por la versión correcta.

### Fase 3. Propagación
Rehacer los teoremas dependientes (`same_SIME_implies_rotation`, `IME_complete`, `isotopic_irreducible_same_SIME`) con las hipótesis corregidas o restringidos a n ≤ 4. Actualizar `MapaMental_TME.md`, la bitácora y los conteos de axiomas.

### Fase 4 (opcional). Definir `to_continued_fraction`
Concreta, sobre las configuraciones realizables, y probar `schubert_classification` para n ≤ 4 contra una lista conocida de nudos racionales (trébol, figura ocho, 5₁, 5₂).

## 4. Criterio de éxito y riesgos

**Éxito mínimo:** al menos uno de los axiomas de `Basic` pasa a teorema para n ≤ 4, y los otros cuatro quedan clasificados con evidencia (refutado o no refutado hasta n ≤ 4).

| Riesgo | Mitigación |
|---|---|
| `Basic.lean` es largo y cada cambio recompila los dependientes (decenas de minutos) | Trabajar el enunciado nuevo en un archivo aparte importando `Basic`, y tocar `Basic` solo al final |
| Que la reparación cambie el sentido de los teoremas que usan el axioma | Fase 3 revisa cada uno; el criterio es no debilitar sin decirlo |
| Que A6 sea cierto en n ≤ 4 y falso en general, y el resultado se lea como confirmación | Declarar siempre la cota: «probado para n ≤ 4», nunca «probado» a secas |
| `decide` sobre n = 4 puede ser muy lento (K3 ya tardaba minutos) | Enumerar por emparejamientos en lugar de subconjuntos de pares, como en `TCN_06` |

## 5. Lo que este plan NO promete
No demuestra la clasificación general ni el teorema de Schubert. Si todo sale, el resultado honesto es: «para n ≤ 4, la reconstrucción, la unicidad de la forma mínima y la clasificación de nudos racionales están demostradas desde cero en Lean», más una lista de axiomas generales reducida y mejor etiquetada.
