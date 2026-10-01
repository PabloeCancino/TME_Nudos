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
| `minimal_isotopic_implies_rotation` (A7) | dos configuraciones mínimas isotópicas son rotación una de otra | **Sospechoso**: mismo defecto de indexado, y la transición R3 solo exige `SIME` igual | buscar un contraejemplo exhaustivo en n = 3 y 4; si no hay, reparar y probar | **2** |
| `axiom_irreducible_is_minimal` (A6) | irreducible ⇒ grado mínimo de su clase | Falso en general para diagramas no alternantes (el desenredo de Goeritz, 10 cruces). Para n ≤ 4 podría ser cierto | comprobar en n ≤ 4 que ninguna configuración alcanzable por R3 y rotación es reducible | 3 |
| `to_continued_fraction` | asigna una fracción continua a cada configuración | Es una función opaca: no hay nada que probar | definirla de forma concreta (sobre las realizables) | 4 |
| `schubert_classification` | isotópicos ⇔ fracciones continuas iguales módulo 1 | Cita de Schubert (1949), pero el enunciado cubre configuraciones **no planares**, para las que no hay nudo | restringirla a las realizables y probar n ≤ 4 | 5 |

## 3. Fases

### Fase 0. Sondas de falsedad (barata, antes de probar nada)
Para cada axioma se intenta **derivar `False`** o encontrar un contraejemplo por búsqueda exhaustiva, antes de invertir en una demostración. La sonda 16 ya lo hizo con `reconstruct_from_first`. Falta:
- **A7:** buscar `K1` irreducible con un triple R3-candidato (`is_R3_candidate`) y `K2` con el mismo `SIME` pero que no sea rotación de `K1`. Si existe, `A6 + A7 + R3` dan `False`.
- **A6:** para n ≤ 4, calcular la componente de `K` bajo R3 y rotación y comprobar que no contiene configuraciones reducibles.
**Criterio de salida:** cada axioma queda marcado como *refutado*, *no refutado hasta n ≤ 4* o *no evaluable*, con el archivo de prueba que lo respalda.

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
