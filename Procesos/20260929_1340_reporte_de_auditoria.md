# Reporte de auditoría del sistema TMENudos

**Fecha:** 2026-09-29 · **Toolchain:** Lean v4.29.0 · **Mathlib:** v4.29.0
**Alcance:** los 34 módulos de `TMENudos/` (`lake build` de todos, con el linter `mathlibStandardSet` del lakefile activo).

## 1. Resumen

| Métrica | Antes | Después |
|---|---|---|
| Módulos con errores de compilación | 8 (más varios ocultos por dependencias) | **0** |
| Errores de compilación | ~90 visibles | **0** |
| Alertas de linter/estilo (excluyendo `sorry`) | 104 solo en `Basic.lean`, más las de otros módulos | **0** |
| Módulos que compilan | 18 o menos de 34 (8 fallaban y otros 8, que dependen de ellos, no llegaron a compilarse) | **34 de 34** |

Verificación final: `lake build TMENudos` más los 33 módulos restantes por nombre, 3326 trabajos, 0 errores, 0 alertas distintas de `declaration uses sorry`.

Cambios registrados en la rama `auditoria-2026-09-29`:

| Commit | Contenido |
|---|---|
| `75708bd` | Auditoría general: 23 archivos corregidos y este reporte. |
| `df86e7b` | Corrección de los axiomas inconsistentes `R1_inverse` y `R2_inverse`. |
| `ed140db` | `reidemeister_equivalent` pasa a ser una relación inductiva. |
| `92dee92`, `bdb627b` | Reporte actualizado y mapa de ruta (`20260929_1408_mapa_de_ruta.md`). |
| `73f869e` | Etapa 0: saneamiento de los enunciados falsos de las secciones 3.2 y 3.3, y renombrado de τ a `swap`. |
| `dbdf9dd` | Bitácora de la sesión (`20260929_1451_bitacora_de_sesion.md`) y pruebas archivadas. |
| `957e156` | Correcciones de imprecisiones detectadas al revisar los tres documentos. |
| (saneamiento de `Schubert`) | Clase A de `Schubert`: existencia y unicidad de la factorización prima como axiomas citados; se cierran 10 `sorry`. |

En la auditoría inicial no se agregaron axiomas; uno pasó de axioma a teorema (`iso_preserves_r1`) y se quitaron 3 axiomas duplicados de `TCN_08_Realizabilidad_EJEMPLO_DIDACTICO`. Los commits posteriores reemplazaron 5 axiomas por versiones corregidas (secciones 3.1 y 4).

## 2. Correcciones aplicadas

### Base
- **`Basic.lean`**: 104 alertas eliminadas: 68 líneas vacías dentro de comandos, 36 `simp` flexibles reemplazados por `simp only [...]`, y `List.Chain'` (obsoleto) por `List.IsChain`.
- **`Reidemeister.lean`**: faltaba `import Mathlib.Data.Rat.Defs`. Sin él, `ℚ` se trataba como variable implícita, lo que rompía `Reidemeister`, `Schubert` y `Bridge`.
- **`TestPoly.lean`**: definición marcada `noncomputable`.
- **`KN_00_Fundamentos_General.lean`**, **`KN_01_Reidemeister_General.lean`**: espacios en `(2 * n)` y `push_neg` → `push Not`.

### Familia KN
- **`KN_00_Combinatoria`** (17 errores): instancia `Fintype` de `OrderedPair` reconstruida; `total_ordered_pairs` y `config_is_perfect_matching` demostrados; `perfect_matching_partition` con sintaxis corregida; `configs_finite` reformulado (estaba mal formado).
- **`KN_03_Invariantes_General`** (5 errores): instancias `Decidable`, `sign_rotate` e `IDE_rotate` reparadas.
- **`KN_04_Clasificacion_General`**: se añadió `[NeZero n]`; `orbit_stabilizer` demostrado completo.
- **`KN_Examples`** (9 errores): trébol derecho, izquierdo, `k_4_1` y `k_4_2` construidos sin `sorry`.
- **`KN_Isomorphism`**: dos alertas de `simp` flexible.
- **`KN_Instance_K3`**: imports sin prefijo `TMENudos.` y varias demostraciones reescritas con `decide`.

### Familia TCN y `CrossingPairIsomorphism`
- **`TCN_03`** (25 errores): lema `existsUnique_of_filter_card` y `decide` en lugar de `simp`.
- **`TCN_04`**: la notación `g • K` absorbía `= R` por precedencia. Se cambió a `notation:73 (priority := high)`. Este error rompía TCN_06, 07 y 08.
- **`TCN_05`**: `orbits_disjoint` demostrado.
- **`TCN_AUX`**: reescrito (usaba `D6Action`, `D6`, `rotatePair` y `orbit_self`, que no existen).
- **`TCN_08_Realizabilidad`**: `irreducible_dichotomy` estaba mal formado (un `String` usado como `Prop`).
- **`TNC_05_1`**: se redujo a un lema verdadero; se eliminó `orbit_bijection`, cuyo enunciado era falso.
- **`CrossingPairIsomorphism`** (28 errores): faltaba `open KnotTheory`; se añadió `Fintype OrderedPair` en `TCN_01`.

## 3. Hallazgos que requieren decisión

Estas son fallas de contenido matemático. La auditoría inicial no modificó enunciados. Los commits posteriores sí modificaron los de la sección 3.1, con aprobación del autor.

### 3.1 Inconsistencia: `R1_inverse` y `R2_inverse` (corregido)
**Problema original.** `R1_inverse` permitía demostrar `False`, verificado en Lean. Con n=0 y un movimiento que elimina un giro, el axioma exigía `KnotConfig 1 = KnotConfig 0`, pero `KnotConfig 0` tiene un solo elemento y `KnotConfig 1` tiene infinitos. La causa era la resta natural (0 − 1 = 0). `R2_inverse` tenía el mismo problema. Todo lo que importa `Reidemeister` (`Schubert`, `Bridge`, `TMENudos`) podía demostrar cualquier cosa.

**Primer intento, insuficiente.** Añadir la hipótesis de tamaño `1 ≤ n` no bastó: se volvió a derivar `False`. El fallo es más profundo, porque "eliminar y luego agregar" no puede ser la identidad para todo diagrama: eliminar pierde información. Con n=1, esa identidad obligaría a que eliminar fuera inyectivo desde un conjunto infinito hacia uno de un solo elemento.

**Corrección aplicada (commit `df86e7b`).** Los axiomas solo afirman la dirección válida, agregar y luego eliminar:
- `R1_inverse` con la hipótesis `move.add_twist = true`.
- `R2_inverse` con la hipótesis `move.add_crossings = true`.
- `reidemeister_inverse` se reformuló con las mismas hipótesis (era falso para n=0) y quedó demostrado.

**Verificación.** Las dos derivaciones de `False` dejaron de compilar. Ningún otro módulo usaba estos axiomas.

**Consistencia.** Verificada por un modelo (`Procesos/Tests/auditoria_20260929/06_modelo_de_consistencia.lean`). Se exhibe en Lean una interpretación de `Reidemeister`, `Schubert` y `Bridge` en la que los 34 axiomas (11 + 21 + 2) valen como teoremas demostrados, cuyo `#print axioms` es solo `propext`, `Classical.choice` y `Quot.sound`. Es consistencia relativa a Lean+Mathlib; ver los límites en la bitácora, sección 4.15. Las versiones corregidas de `R1_inverse` y `R2_inverse` admiten un modelo, como se argumentaba (agregar un cruce es inyectivo y quitarlo es su inversa por la izquierda); antes esa afirmación no estaba formalizada.

### 3.2 Enunciados falsos en TCN_06 (corregido en la etapa 0)
Con las definiciones actuales, los tamaños reales son: `specialClass` estabilizador 1 y órbita 12; `trefoilKnot` 6 y 2; `mirrorTrefoil` 6 y 2. `mirrorTrefoil = r³ • trefoilKnot` (y `= swap trefoilKnot`, comprobado con `decide`), de modo que las dos órbitas del trébol coinciden.

**Corrección.** La clasificación de K3 pasa de tres órbitas (6+4+4) a **dos órbitas de 12 y 2 elementos**, que suman las 14 configuraciones sin R1 ni R2, con representantes `specialClass` y `trefoilKnot`.
- Eliminados: `stab_special_card`, `stab_trefoil_card`, `stab_mirror_card`, `orbits_disjoint_trefoil_mirror`, `three_orbits_pairwise_disjoint` y `trefoil_not_in_mirror_orbit`. Reemplazos: `stab_*_card_actual`, `two_orbits_sum_to_14`, `two_orbits_disjoint`, `two_orbits_cover_all` y `orbit_mirrorTrefoil_eq_orbit_trefoilKnot`.
- `total_realizable_configs`: 8 → 14. `realizable_fraction`: 1/15 → 7/60. `non_realizable_count`: 112 → 106.
- `exactly_two_classes` lleva ahora la condición "cada clase es una órbita"; sin ella el enunciado era falso.
- `configs_no_r1_no_r2_card` y `card_k3_config` (120) dejaron de ser axioma y `sorry`, y se demuestran con `decide +kernel`.
- Ya no hay `sorry` en `TCN_05` a `TCN_08` ni en `TCN_AUX`.

**Decisiones abiertas** (mapa de ruta, sección 10): en este modelo el trébol y su imagen especular caen en la misma órbita; y "realizable" incluye a `specialClass`.

### 3.3 Enunciados falsos en la teoría KN (corregido en la etapa 0)
`gap_mirror`, `IDE_mirror`, `IME_mirror` e `IME_eq_of_mem_orbit` eran falsos, no solo difíciles: con `mirror(a,b) = (-a,-b)`, el gap del reflejado es `2n − 2 − gap`. Contraejemplo con n=2 y K = {(0,1),(2,3)}: `IME K = 0` e `IME K.mirror = 4`.

**Corrección** (detalle de la convención en el mapa de ruta, sección 4):
- `gap_mirror` → `gap_mirror_add` (`p.gap + p.mirror.gap + 2 = 2n`) y `gap_reverse_mirror`.
- `IDE_mirror` e `IME_mirror` eliminados; en su lugar `not_IME_mirror`, que prueba que `IME` no es invariante bajo σ.
- `IME_eq_of_mem_orbit` → `IME_eq_of_mem_rotate_orbit` (primer nivel, orientado) e **`IME2_eq_of_mem_orbit`** (segundo nivel, no orientado), con `IME2 K = (min, max)` de `IME` sobre K y σK. Demostrados también `IME2_mirror` e `IME2_rotate`.
- `(mirror K).ime = K.ime` → `ime_swap_multiset` (igualdad de multiconjuntos, para todo n).
- El intercambio over/under (τ) se renombra a `swap` en `Basic`, `TCN_01`, `KN_General` y `KN_Examples`. El comentario T4.1 de `Basic` se corrige: τ conmuta con las rotaciones, así que ese grupo es abeliano, no diédrico.

**Experimento** (n=3 y n=4): `IME2` es constante en cada órbita de D₂ₙ, pero `IME` no es un invariante completo. Es un solo entero y no separa las órbitas (13 órbitas con 10 valores en n=3; 121 con 28 en n=4).

### 3.4 Otros `sorry` de fondo
Tras la etapa 0 quedan dos fuera de `Reidemeister` y `Schubert`:
- `perfect_matchings_upper_bound` (`KN_00_Combinatoria.lean:300`): verdadero, falta la biyección de conteo.
- `KN_Instance_K3.lean:40`: igualdad de tipos entre una estructura y un subtipo. Lo correcto sería una `Equiv`.

Resueltos en la etapa 0 (la versión anterior de esta sección aún los listaba): `configsNoR1NoR2` y `configs_no_r1_no_r2_card` (`TCN_05`), y `card_k3_config` (`TCN_08_Realizabilidad`).

## 4. Clasificación de los `sorry` de Reidemeister y Schubert

Situación inicial: 39 `sorry` reales (12 en `Reidemeister`, 27 en `Schubert`) y 33 axiomas entre ambos. Tras el commit `ed140db` quedaron 32, y tras la etapa 0 quedaron 31 (5 en `Reidemeister`, 26 en `Schubert`, por la reformulación de `reidemeister_preserves_decomposition`). Tras el saneamiento de la clase A de `Schubert` (ver más abajo) quedan **21** (5 en `Reidemeister`, 16 en `Schubert`). Los axiomas de `Schubert` bajan de 22 a 21, así que `Reidemeister` y `Schubert` suman ahora 32 (11 + 21). Además, 5 de los de `Reidemeister` (`R1_inverse`, `R2_inverse` y los tres `R*_preserves_isotopy`) cambiaron de enunciado.

| Clase | Reidemeister | Schubert | Total |
|---|---|---|---|
| A. Demostrables (hoy o con arreglo menor) | 0 | 0 | 0 |
| B. Enunciado dudoso o falso | 1 | 7 | 8 |
| C. Dependen de teoría que falta | 4 | 9 | 13 |

### Resueltos en `Reidemeister` (7 de 12)
- `reidemeister_equivalent` (antes con cuerpo `sorry`) es ahora una relación inductiva con los constructores `refl`, `symm`, `trans`, `R1`, `R2` y `R3`. R1 y R2 se dan solo en la dirección de agregar; la eliminación sale por `symm`.
- `reidemeister_refl`, `reidemeister_symm` y `reidemeister_trans` se reducen a los constructores.
- `reidemeister_soundness` e `invariant_criterion` se demuestran por inducción sobre la relación.
- `reidemeister_inverse` se demuestra a partir de los axiomas corregidos (sección 3.1).
- `R1_preserves_isotopy`, `R2_preserves_isotopy` y `R3_preserves_isotopy` eran axiomas vacíos (`∃ K', K' = apply_R1 K move` siempre es cierto). Se reemplazaron por enunciados con contenido sobre `topologically_equivalent`. Sin ellos no se puede probar la solidez.

Estas demostraciones aún dependen de `sorryAx`, por una razón indirecta: las funciones `apply_R*` están definidas con `sorry`. El compilador lo cuenta como dependencia aunque los teoremas no usen su contenido.

### Problema estructural (resuelto)
`DiagramSetoid`, y con él `Knot`, se construía sobre `reidemeister_refl`, `reidemeister_symm` y `reidemeister_trans`, que eran `sorry`. Ahora esas tres son consecuencias directas de los constructores de la relación inductiva, y el setoid ya no descansa sobre `sorry` propio. `Schubert` y `Bridge` no requirieron cambios.

### A. Demostrables: resueltos (saneamiento de `Schubert`)
Se aplicó el principio del mapa de ruta (los teoremas profundos ya establecidos se declaran axiomas con cita):
- **`schubert_existence_axiom`** (nuevo axioma, Schubert 1949): todo nudo es suma conexa de una lista finita de primos. Con él, `prime_decomposition` se define con `Classical.choose`, y `prime_decomposition_prime` y `prime_decomposition_reconstructs` dejan de ser axiomas y pasan a ser teoremas. La primera ya no admite la disyunción `is_prime P ∨ P ≅ unknot`: los factores son primos.
- **`schubert_uniqueness`** pasa de teorema con `sorry` a **axioma** (Schubert 1949, unicidad), con la misma firma.
- Con eso quedan demostrados `schubert_existence`, `schubert_unique_factorization` (con un lema `foldl_perm` de invariancia por permutación) y `factorization_problem`.
- Efecto en cadena: la longitud de la descomposición no depende de la factorización elegida (`decomposition_length_eq`), y de ahí se demuestran `complexity_additive`, `composite_characterization`, `example_has_two_prime_factors`, `granny_knot_composite` y `granny_knot_decomposition` (antes `square_knot_*`; ver el cambio de nombres más abajo). Lemas nuevos: `unknot_sum`, `foldl_shift`, `foldl_append`, `decomposition_length_add`, `decomposition_nil_iff`.
- Axiomas de `Schubert`: 21 antes y después (entran 2, salen 2). El total del proyecto sigue en 47.
- Dependencias: `#print axioms` de los teoremas cerrados muestra solo los axiomas citados y los de la suma conexa (más el `sorryAx` indirecto de `apply_R*`).
- **Verificación de dependencias.** Además de `#print axioms`, se rastreó qué constantes de la cadena de dependencias de cada teorema cerrado contienen `sorry` directamente (incluidos los constructores de tipos inductivos): en los 13 teoremas son solo `apply_R1`, `apply_R2` y `apply_R3`. Ningún `sorry` propio de `Schubert` (`is_satellite`, `torus_knot`, …) se filtra. Prueba archivada en `Procesos/Tests/auditoria_20260929/05_rastreo_de_sorry_en_teoremas_cerrados.lean`.
- **Consistencia:** los dos axiomas son verdaderos para nudos reales y, además, su consistencia con el resto de los axiomas de `Reidemeister`, `Schubert` y `Bridge` está verificada por un modelo (bitácora, sección 4.15). Límite: el modelo es degenerado en lo geométrico (los "nudos" del modelo son multiconjuntos de racionales no nulos), así que prueba que no hay contradicción entre los axiomas, no que describan nudos reales.

### B. Enunciado dudoso o falso (8)
- `minimal_characterization` (`Reidemeister.lean:403`): falso; el lado derecho es siempre `False`, y el diagrama vacío es mínimo.
- `schubert_torus_knot_primality` (217): falso; T(1,q) es el nudo trivial, no primo, y gcd(1,q)=1. Debería exigir p,q ≥ 2.
- `schubert_complement_sum` (288): compara tipos con igualdad. El complemento de K₁#K₂ se obtiene pegando los complementos a lo largo de un anillo, no por suma conexa.
- `schubert_companion_theorem` (195-196) y `schubert_is_JSJ_special_case` (372, 374): tienen `sorry` dentro del propio enunciado.
- ~~`reidemeister_preserves_decomposition`~~ Resuelto en la etapa 0: se eliminó el axioma `reidemeister_equivalent` de `Schubert` (chocaba en nombre con la relación inductiva de `Reidemeister`) y el teorema se reformuló con `K₁ ≅ K₂` y se demostró.
- `alexander_multiplicative` (353): el polinomio de Alexander se define salvo unidades ±tᵏ; aquí es un `Polynomial ℤ`.
- ~~Nombres intercambiados de `square_knot` y `granny_knot`~~ Corregido: `granny_knot := trefoil # trefoil` (nudo de la abuela) y `square_knot := trefoil # mirror trefoil` (nudo cuadrado). Los teoremas que ya estaban demostrados hablaban de trébol # trébol, así que pasaron a llamarse `granny_knot_composite` y `granny_knot_decomposition`. No hay versiones para `square_knot` porque exigirían que la imagen especular del trébol sea prima, y `mirror` es un axioma sin propiedades; no se agregó ningún axioma nuevo. `granny_distinct_from_square` conserva su enunciado.

### C. Dependen de teoría que falta (13)
- `apply_R1`, `apply_R2`, `apply_R3` (`Reidemeister.lean`, líneas 91, 123 y 155): `KnotConfig` no modela la conexión de las hebras.
- `knot_equivalence_decidable` (`Reidemeister.lean:386`): requiere el teorema de Haken.
- ~~Unicidad de Schubert y lo que se apoya en ella~~ Resuelto: la unicidad es ahora un axioma citado y `complexity_additive`, `composite_characterization` y `example_has_two_prime_factors` están demostrados (ver la clase A).
- Sin definición: `is_satellite` (177), `satellite_pattern` (180), `torus_knot` (205), con su simetría (221) y género (225); `bridge_number` (246) con su aditividad (260); `genus_additive` (326); `granny_distinct_from_square` (419).

Las valoraciones matemáticas de esta sección son del auditor y conviene revisarlas. Solo las inconsistencias de `R1_inverse` y `R2_inverse` (sección 3.1) están comprobadas en Lean.

## 5. Estado de `sorry` y axiomas

Tras el saneamiento de la clase A de `Schubert`, `sorry` en el código: **23** en total (33 tras la etapa 0). `Schubert` 16, `Reidemeister` 5, y 1 en cada uno de `KN_00_Combinatoria` (`perfect_matchings_upper_bound`) y `KN_Instance_K3` (línea 40, una igualdad de tipos que debería ser una `Equiv`). Los módulos `KN_03`, `KN_03b`, `KN_04`, `KN_Examples` y toda la cadena `TCN` ya no tienen `sorry`.

Axiomas: **47** (sin cambio neto tras el saneamiento de `Schubert`: salen `prime_decomposition_prime` y `prime_decomposition_reconstructs`, entran `schubert_existence_axiom` y `schubert_uniqueness`). `Schubert` 21, `Reidemeister` 11, `Basic` 5, `KN_01` 5, `Bridge` 2, y 1 en cada uno de `KN_00_Combinatoria`, `TCN_01` y `TCN_08_UniformityCriterion`.

## 6. Observaciones de mantenimiento

- `TMENudos.lean` solo importa `Basic`, `Reidemeister`, `Schubert`, `Bridge` y `TCN_01`. Los otros 29 módulos no forman parte de la biblioteca por defecto y hay que compilarlos por nombre.
- Archivos sueltos en la raíz que probablemente sobran: `build_error.log`, `temp_mirror_theorems.txt`, `lean-toolchain.backup`.
- Dos módulos, `KN_*` y `TCN_*`, implementan la misma teoría en paralelo. Conviene decidir cuál es el canónico.

## 7. Orden de trabajo recomendado

1. ~~Corregir `R1_inverse` y `R2_inverse`~~ Hecho (commit `df86e7b`, sección 3.1).
2. ~~Redefinir `reidemeister_equivalent` de forma inductiva~~ Hecho (commit `ed140db`, sección 4).
3. ~~Decidir los representantes o conteos de `TCN_06`~~ Hecho en la etapa 0 (sección 3.2).
4. ~~Reformular `gap_mirror`, `IDE_mirror` e `ime`~~ Hecho en la etapa 0 (sección 3.3).
5. ~~Arreglar `prime_decomposition`~~ Hecho (sección 4, clase A). Quedan los enunciados falsos de la clase B (`Schubert`), que requieren su aprobación.
6. Etapa 1 del mapa de ruta: tipo de diagrama concreto, y con él definiciones para `apply_R1`, `apply_R2` y `apply_R3`. Es lo que elimina la dependencia indirecta de `sorryAx`.
