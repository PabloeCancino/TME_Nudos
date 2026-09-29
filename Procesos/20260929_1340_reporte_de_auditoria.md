# Reporte de auditoría del sistema TMENudos

**Fecha:** 2026-09-29 · **Toolchain:** Lean v4.29.0 · **Mathlib:** v4.29.0
**Alcance:** los 34 módulos de `TMENudos/` (`lake build` de todos, con el linter `mathlibStandardSet` del lakefile activo).

## 1. Resumen

| Métrica | Antes | Después |
|---|---|---|
| Módulos con errores de compilación | 8 (más varios ocultos por dependencias) | **0** |
| Errores de compilación | ~90 visibles | **0** |
| Alertas de linter/estilo (excluyendo `sorry`) | 104 solo en `Basic.lean`, más las de otros módulos | **0** |
| Módulos que compilan | 26 de 34 | **34 de 34** |

Verificación final: `lake build TMENudos` más los 33 módulos restantes por nombre, 3326 trabajos, 0 errores, 0 alertas distintas de `declaration uses sorry`.

Cambios registrados en la rama `auditoria-2026-09-29`:

| Commit | Contenido |
|---|---|
| `75708bd` | Auditoría general: 23 archivos corregidos y este reporte. |
| `df86e7b` | Corrección de los axiomas inconsistentes `R1_inverse` y `R2_inverse`. |
| `ed140db` | `reidemeister_equivalent` pasa a ser una relación inductiva. |

En la auditoría inicial no se agregaron axiomas; uno pasó de axioma a teorema (`iso_preserves_r1`). Los commits posteriores reemplazaron 5 axiomas por versiones corregidas (secciones 3.1 y 4).

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

**Advertencia.** No se ha demostrado que el sistema sea consistente. Mientras `apply_R1`, `apply_R2` y `apply_R3` sean `sorry`, sus axiomas no tienen un modelo verificado en Lean. El argumento es que las versiones corregidas admiten un modelo (agregar un cruce es inyectivo y quitarlo es su inversa por la izquierda), pero no está formalizado.

### 3.2 Enunciados falsos en TCN_06 (con arrastre a TCN_07 y TCN_08)
Con las definiciones actuales:

| Representante | |Stab| real | |Orb| real | Enunciado original |
|---|---|---|---|
| `specialClass` | 1 | 12 | 2 / 6 |
| `trefoilKnot` | 6 | 2 | 3 / 4 |
| `mirrorTrefoil` | 6 | 2 | 3 / 4 |

`mirrorTrefoil = r³ • trefoilKnot`, así que ambas órbitas coinciden y `orbits_disjoint_trefoil_mirror` es falso. También son falsos `three_orbits_sum_to_14`, `representatives_not_equivalent` y los conteos 8 y 4+4. Hay que decidir si se corrigen los representantes o los conteos. Se añadieron versiones verdaderas: `stab_special_card_actual`, `stab_trefoil_card_actual`, `stab_mirror_card_actual`.

### 3.3 Enunciados falsos en la teoría KN
- **`OrderedPair.gap_mirror`** (`KN_03_Invariantes_General.lean:90`): falso. `mirror` manda `(a,b)` a `(-a,-b)`. Contraejemplo con n=2 y p=(0,1): los huecos valen 0 y 2.
- **`KnConfig.IDE_mirror`** (línea 144): probablemente falso por lo mismo. De él dependen `IME_mirror` (KN_03b) y el caso espejo de `IME_eq_of_mem_orbit` (KN_04).
- **`(mirror K).ime = K.ime`** (`KN_Examples.lean:123`): no se puede probar como igualdad de listas, porque `dme` usa `Finset.toList`, que no fija un orden. Habría que usar multiconjuntos o listas ordenadas.

### 3.4 Otros `sorry` de fondo
- `perfect_matchings_upper_bound` (`KN_00_Combinatoria.lean:300`): verdadero, falta la biyección de conteo.
- `KN_Instance_K3.lean:41`: igualdad de tipos entre una estructura y un subtipo. Lo correcto sería una `Equiv`.
- `TCN_05_Orbitas.lean:218`: `configsNoR1NoR2`, junto con `axiom configs_no_r1_no_r2_card`.
- `TCN_08_Realizabilidad.lean:70`: `card_k3_config`.

## 4. Clasificación de los `sorry` de Reidemeister y Schubert

Situación inicial: 39 `sorry` reales (12 en `Reidemeister`, 27 en `Schubert`) y 33 axiomas entre ambos. Tras el commit `ed140db` quedan **32** (5 en `Reidemeister`, 27 en `Schubert`). Los axiomas siguen siendo 33, aunque 5 de ellos (`R1_inverse`, `R2_inverse` y los tres `R*_preserves_isotopy`) cambiaron de enunciado.

| Clase | Reidemeister | Schubert | Total |
|---|---|---|---|
| A. Demostrables (hoy o con arreglo menor) | 0 | 4 | 4 |
| B. Enunciado dudoso o falso | 1 | 10 | 11 |
| C. Dependen de teoría que falta | 4 | 13 | 17 |

### Resueltos en `Reidemeister` (7 de 12)
- `reidemeister_equivalent` (antes con cuerpo `sorry`) es ahora una relación inductiva con los constructores `refl`, `symm`, `trans`, `R1`, `R2` y `R3`. R1 y R2 se dan solo en la dirección de agregar; la eliminación sale por `symm`.
- `reidemeister_refl`, `reidemeister_symm` y `reidemeister_trans` se reducen a los constructores.
- `reidemeister_soundness` e `invariant_criterion` se demuestran por inducción sobre la relación.
- `reidemeister_inverse` se demuestra a partir de los axiomas corregidos (sección 3.1).
- `R1_preserves_isotopy`, `R2_preserves_isotopy` y `R3_preserves_isotopy` eran axiomas vacíos (`∃ K', K' = apply_R1 K move` siempre es cierto). Se reemplazaron por enunciados con contenido sobre `topologically_equivalent`. Sin ellos no se puede probar la solidez.

Estas demostraciones aún dependen de `sorryAx`, por una razón indirecta: las funciones `apply_R*` están definidas con `sorry`. El compilador lo cuenta como dependencia aunque los teoremas no usen su contenido.

### Problema estructural (resuelto)
`DiagramSetoid`, y con él `Knot`, se construía sobre `reidemeister_refl`, `reidemeister_symm` y `reidemeister_trans`, que eran `sorry`. Ahora esas tres son consecuencias directas de los constructores de la relación inductiva, y el setoid ya no descansa sobre `sorry` propio. `Schubert` y `Bridge` no requirieron cambios.

### A. Demostrables (4, todos en Schubert)
- `prime_decomposition` (110), `schubert_existence` (134), `schubert_unique_factorization` (167) y `factorization_problem` (386): axiomatizando la existencia y filtrando nudos triviales.

### B. Enunciado dudoso o falso (11)
- `minimal_characterization` (`Reidemeister.lean:403`): falso; el lado derecho es siempre `False`, y el diagrama vacío es mínimo.
- `schubert_torus_knot_primality` (217): falso; T(1,q) es el nudo trivial, no primo, y gcd(1,q)=1. Debería exigir p,q ≥ 2.
- `schubert_complement_sum` (288): compara tipos con igualdad. El complemento de K₁#K₂ se obtiene pegando los complementos a lo largo de un anillo, no por suma conexa.
- `schubert_companion_theorem` (195-196) y `schubert_is_JSJ_special_case` (372, 374): tienen `sorry` dentro del propio enunciado.
- `reidemeister_preserves_decomposition` (341): el axioma `reidemeister_equivalent` de `Schubert` choca en nombre con el de `Reidemeister`, que ahora es una relación inductiva. Sigue pendiente.
- `alexander_multiplicative` (353): el polinomio de Alexander se define salvo unidades ±tᵏ; aquí es un `Polynomial ℤ`.
- `square_knot_composite` y `square_knot_decomposition` (406, 410): nombres intercambiados. El nudo cuadrado es trébol # espejo, y el nudo de la abuela (*granny*) es trébol # trébol. Además usan una `prime_decomposition` arbitraria.

### C. Dependen de teoría que falta (17)
- `apply_R1`, `apply_R2`, `apply_R3` (`Reidemeister.lean`, líneas 91, 123 y 155): `KnotConfig` no modela la conexión de las hebras.
- `knot_equivalence_decidable` (`Reidemeister.lean:386`): requiere el teorema de Haken.
- Unicidad de Schubert (156) y lo que se apoya en ella: `complexity_additive` (305), `composite_characterization` (318) y `example_has_two_prime_factors` (426).
- Sin definición: `is_satellite` (177), `satellite_pattern` (180), `torus_knot` (205), con su simetría (221) y género (225); `bridge_number` (246) con su aditividad (260); `genus_additive` (326); `granny_distinct_from_square` (419).

Las valoraciones matemáticas de esta sección son del auditor y conviene revisarlas. Solo las inconsistencias de `R1_inverse` y `R2_inverse` (sección 3.1) están comprobadas en Lean.

## 5. Estado de `sorry` y axiomas

`sorry` (avisos del compilador en la auditoría inicial, algunos duplicados; `Reidemeister` tiene ahora 5 en el código, ver sección 4): `Reidemeister` 16, `Schubert` 25, `TCN_06` 5, `KN_03` 2, `TCN_07` 2, y 1 en cada uno de `KN_00_Combinatoria`, `KN_Examples`, `KN_Instance_K3`, `TCN_05` y `TCN_08_Realizabilidad`.

Axiomas: `Schubert` 22, `Reidemeister` 11, `Basic` 5, `KN_01` 5, `Bridge` 2, y 1 en cada uno de `KN_00_Combinatoria`, `TCN_01`, `TCN_05` y `TCN_08_UniformityCriterion`. Total: 49.

## 6. Observaciones de mantenimiento

- `TMENudos.lean` solo importa `Basic`, `Reidemeister`, `Schubert`, `Bridge` y `TCN_01`. Los otros 29 módulos no forman parte de la biblioteca por defecto y hay que compilarlos por nombre.
- Archivos sueltos en la raíz que probablemente sobran: `build_error.log`, `temp_mirror_theorems.txt`, `lean-toolchain.backup`.
- Dos módulos, `KN_*` y `TCN_*`, implementan la misma teoría en paralelo. Conviene decidir cuál es el canónico.

## 7. Orden de trabajo recomendado

1. ~~Corregir `R1_inverse` y `R2_inverse`~~ Hecho (commit `df86e7b`, sección 3.1).
2. ~~Redefinir `reidemeister_equivalent` de forma inductiva~~ Hecho (commit `ed140db`, sección 4). Cerró 7 de los 12 `sorry` de `Reidemeister`.
3. Decidir los representantes o conteos de `TCN_06` (sección 3.2).
4. Reformular `gap_mirror`, `IDE_mirror` e `ime` (sección 3.3).
5. Arreglar `prime_decomposition` y los enunciados falsos de la clase B, incluido el choque de nombre entre el axioma `reidemeister_equivalent` de `Schubert` y la relación de `Reidemeister`.
6. Dar definiciones concretas a `apply_R1`, `apply_R2` y `apply_R3`. Es lo que elimina la dependencia indirecta de `sorryAx` y permite justificar los axiomas del grupo de Reidemeister.
