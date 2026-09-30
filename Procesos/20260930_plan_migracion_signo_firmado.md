# Plan de migración de `Basic` y `TCN` al signo como dato

**Fecha:** 2026-09-30 · **Rama:** `migracion-signo` (sale de `master`, que ya contiene toda la etapa 1) · **Estado:** PLAN, en ejecución por etapas
**Decisión del autor:** adoptar el signo del cruce como DATO en la teoría modular, migrando `Basic` y `TCN` con los cambios en cascada que haga falta. La justificación demostrada está en la bitácora (secciones 4.26 y 4.29): con el signo derivado de las posiciones la teoría modular no puede representar el trébol de la otra quiralidad.

## 1. Alcance medido

| Módulo | Tamaño | Qué usa |
|---|---|---|
| `Basic.lean` | 1 614 líneas | `RationalCrossing` (17 usos), `RationalConfiguration` (93), `crossing_sign`, `zmod_sign`, `swap_*`, `rotate_*`, `ratio_val` |
| `CrossingPairIsomorphism.lean` | 499 | `RationalCrossing` (46) y `OrderedPair`/`K3Config` de TCN (33): **enlaza las dos teorías** |
| `KN_Isomorphism.lean` | — | `RationalCrossing` (28) frente a `OrderedPairN` de `KN_General` (sin signo) |
| `TCN_08_Uniformity`, `TCN_09`, `TCN_10` | 357 / 229 / — | `RationalConfiguration` y `RationalCrossing` |
| `TCN_01` a `TCN_08`, `TCN_AUX`, `TNC_05_1` | unas 4 400 líneas | `OrderedPair`/`K3Config` en más de 250 sitios |
| Capa paralela (fuera de la build) | — | `Modular_Signo`, `Etapa1_Bridge`, `Etapa1_Modular`: hoy definen su propio cruce firmado; pasarán a apoyarse en el cruce firmado de `Basic` |

## 2. Reglas de migración (válidas para todas las etapas)

1. **El signo es un campo del cruce.** `Basic.RationalCrossing` y `TCN.OrderedPair` ganan `pos : Bool` (`true` = positivo), como ÚLTIMO campo. No se añade valor por defecto.
2. **Semántica de las operaciones:**
   - `rotate` (cambio de punto de partida) **conserva** el signo.
   - `swap` (imagen especular, τ) **intercambia** over y under y **niega** el signo.
   - La acción de D₆ de `TCN_04` (rotaciones y reflexión σ) **conserva** el signo.
3. **El signo derivado desaparece como definición** y queda como caso particular: `crossing_sign` pasa a leerse del campo; para construir un cruce con el signo antiguo se usa una función `withDerivedSign` explícita (conserva la lectura de los teoremas antiguos en los casos antipodales y no antipodales).
4. **Movimientos con signo (solo donde el código ya los define):** R1 admite cualquier signo; R2 exige signos **opuestos** en los dos cruces (es lo que se demostró en `Etapa1_R2`); R3 se deja como está salvo que el archivo ya lo distinga. Los candidatos R1/R2/R3 de `Basic` son marcadores de posición: si añadir la condición de signo rompe demostraciones ajenas, se documenta y se difiere.
5. **Los conteos se recalculan, no se adivinan.** Cada cifra que cambie (120 configuraciones, 14 irreducibles, 12 + 2 órbitas, 2 realizables, 7/60, 1/60, 118) se recalcula por `decide`/`#eval` y se registra con el valor antiguo y el nuevo.
6. **Nada de `sorry` ni axiomas nuevos**; cada etapa termina con la **build completa de los 34 módulos más la raíz** en 0 errores y 0 alertas, y solo entonces se commitea.
7. **Lo que no es de `Basic`/`TCN`** (`KN_General`, `KN_00`..`KN_04`) **no se migra**: `KN_Isomorphism` se reformula como isomorfismo entre el cruce firmado de `Basic` y el cruce sin signo de `KN` **por un factor `Bool`** (cruce firmado ≃ cruce sin signo × signo).

## 3. Etapas (cada una deja la build en verde antes de commitear)

**Etapa 1. `Basic` y dependientes cuyo vínculo es con `Basic`.**
`RationalCrossing` gana `pos`; se actualizan `Fintype`/`DecidableEq`/`ext`, `swap_crossing`, `rotate_crossing`, `crossing_sign`, `writhe`, `signed_matrix` y todo lo de `Basic` que construya cruces. Después `Bridge`, `KN_Isomorphism` (con el factor `Bool`), `TCN_08_Uniformity`, `TCN_09`, `TCN_10`. `CrossingPairIsomorphism` se adapta a "cruce firmado de `Basic` ≃ par sin signo de `TCN` × `Bool`" mientras `TCN` siga sin signo.

**Etapa 2. `TCN_01` a `TCN_04` y `CrossingPairIsomorphism` final.**
`OrderedPair` gana `pos`; `K3Config` pasa a 960 configuraciones; la acción de D₆ conserva el signo; los emparejamientos de `TCN_03`; `CrossingPairIsomorphism` vuelve a ser un isomorfismo directo entre cruces firmados.

**Etapa 3. `TCN_05` a `TCN_08`, `TCN_AUX`, `TNC_05_1`.**
Se recalculan órbitas, estabilizadores, irreducibles (con R2 condicionado al signo), la clasificación y "realizable" (la paridad de Gauss no depende del signo). La clase del trébol se reparte en varias órbitas firmadas (según `Modular_Signo`: 16 configuraciones firmadas en 4 órbitas de tamaños 2, 6, 6, 2); cuántas son irreducibles y realizables se determina por cálculo.

**Etapa 4. Limpieza de la capa paralela.** `Modular_Signo`, `Etapa1_Bridge` y `Etapa1_Modular` se apoyan en el cruce firmado de `Basic`/`TCN` en lugar de sus copias; se retira lo duplicado.

## 4. Riesgos y señales tempranas

| Riesgo | Señal temprana |
|---|---|
| Teoremas de conteo de `TCN_05` a `TCN_08` que dependen de `decide` sobre 120 configuraciones y pasan a 960 (tiempo y `maxRecDepth`) | Medir el tiempo de `decide +kernel` sobre 960 en `TCN_01` antes de reescribir nada más |
| Que algún enunciado de `TCN_06`/`TCN_07` sea falso con el signo como dato (p. ej. "exactamente dos clases") | Recalcular por `#eval` las órbitas de las irreducibles firmadas ANTES de reformular |
| Desajuste de convenciones entre `Basic` y `TCN` que rompa `CrossingPairIsomorphism` | Las reglas 1 y 2 se aplican idénticas en ambas teorías; el isomorfismo debe conservar `pos` |
| Que el isomorfismo con `KN` deje de ser isomorfismo | Reformulación por producto con `Bool` (regla 7), comprobada por cardinalidad |

## 5. Lo que este plan NO hace

- No toca `KN_General` ni `KN_00`..`KN_04`.
- No cambia los axiomas de `Schubert`, `Reidemeister` ni `Bridge` (en particular, `rational_to_diagram` sigue siendo axioma).
- No sube nada a `origin`.

## 6. Hallazgo de la sonda de conteos (añadido antes de la Etapa 3)

Sonda: `Procesos/Tests/auditoria_20260929/14_conteos_k3_firmados.py`, que reproduce las definiciones de `TCN` (R1 por pareja consecutiva, R2 por `formsR2Pattern`, acción de D₆, paridad de Gauss). **Control:** sin signo reproduce exactamente lo ya demostrado (120 configuraciones, 14 irreducibles en órbitas de 12 y 2, 2 realizables).

| Con el signo como dato libre | Sin signo | Con signo libre (R2 exige signos opuestos) | Con signo **y** índice cero |
|---|---|---|---|
| Configuraciones | 120 | **960** | 336 |
| Irreducibles (sin R1 ni R2) | 14 (órbitas de 12 y 2) | **172** (18 órbitas) | **4** |
| Realizables | 2 | **28** (6 órbitas) | **4** (2 órbitas de tamaño 2) |

**Conclusión de diseño (nueva regla 8).** Con el signo como dato LIBRE el tipo firmado genera configuraciones que no son diagramas planos (por ejemplo un trébol con signos mixtos, que pasa la paridad de Gauss pero no la consistencia de signos), y por tanto "irreducible" y "realizable" sobrecuentan. Hace falta una condición de consistencia que mire el signo. La condición usada es el **índice cero**: en un diagrama clásico el índice de cada cruce es 0, donde el índice de la cuerda `c = (o,u)` es la suma, sobre las cuerdas `d` entrelazadas con `c`, de `+sgn(d)` si el extremo superior de `d` cae en el arco que va de `o` a `u`, y `-sgn(d)` si cae el inferior. Es una condición **necesaria** de planaridad (no se ha demostrado suficiente; para K3 la sonda da exactamente los dos tréboles).

- El TIPO firmado sigue siendo libre (960 configuraciones, sin restringir); la clasicidad se impone por **predicados** (`gaussEven` y `indexZero`), como ya se hizo con la paridad de Gauss.
- **"Realizable" en K3 firmado** = irreducible (con R2 condicionado al signo) ∧ índice cero. Resultado esperado y a demostrar: 4 configuraciones en 2 órbitas de tamaño 2, que son el trébol derecho (signos +) y el izquierdo (signos −), este último la imagen de `swapS` del primero.
- **Teorema de clasificación esperado** (sustituye a "exactamente dos clases"): entre las configuraciones firmadas irreducibles con índice cero hay exactamente dos clases de D₆, el trébol derecho y el izquierdo. Las 172 irreducibles sin la condición de índice no son una clasificación con sentido.
- **La conjetura de que el índice cero caracteriza la planaridad en K3 no se ha demostrado**; se ha comprobado que su conjunto coincide con el de los dos tréboles, que es lo que hace falta para la etapa 3.
