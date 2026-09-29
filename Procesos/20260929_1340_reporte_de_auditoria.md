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

Todos los cambios están sin commit (23 archivos modificados). No se agregaron axiomas; uno pasó de axioma a teorema (`iso_preserves_r1`).

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

Estas son fallas de contenido matemático. No se modificaron los enunciados.

### 3.1 Inconsistencia: `R1_inverse` y `R2_inverse` (crítico)
`R1_inverse` (`Reidemeister.lean:188`) permite demostrar `False`, verificado en Lean. Con n=0 y un movimiento que elimina un giro, el axioma exige `KnotConfig 1 = KnotConfig 0`. Pero `KnotConfig 0` tiene un solo elemento y `KnotConfig 1` tiene infinitos. La causa es la resta natural (0 − 1 = 0). `R2_inverse` tiene el mismo problema.

**Consecuencia:** todo lo que importa `Reidemeister` (`Schubert`, `Bridge`, `TMENudos`) puede demostrar cualquier cosa, y sus resultados no son fiables.

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

39 `sorry` reales (12 en `Reidemeister`, 27 en `Schubert`) y 33 axiomas entre ambos.

| Clase | Reidemeister | Schubert | Total |
|---|---|---|---|
| A. Demostrables (hoy o con arreglo menor) | 5 | 4 | 9 |
| B. Enunciado dudoso o falso | 2 | 10 | 12 |
| C. Dependen de teoría que falta | 5 | 13 | 18 |

### A. Demostrables
- `reidemeister_refl`, `reidemeister_symm`, `reidemeister_trans` (líneas 205, 212, 222) e `invariant_criterion` (342): tras redefinir `reidemeister_equivalent` de forma inductiva.
- `reidemeister_inverse` (327): se deduce de `R1_inverse` y `R2_inverse`, pero esos axiomas son contradictorios.
- `prime_decomposition` (110), `schubert_existence` (134), `schubert_unique_factorization` (167) y `factorization_problem` (386): axiomatizando la existencia y filtrando nudos triviales.

### B. Enunciado dudoso o falso
- `reidemeister_equivalent` (183): el cuerpo de la definición es `sorry`.
- `minimal_characterization` (372): falso; el lado derecho es siempre `False`, y el diagrama vacío es mínimo.
- `schubert_torus_knot_primality` (217): falso; T(1,q) es el nudo trivial, no primo, y gcd(1,q)=1. Debería exigir p,q ≥ 2.
- `schubert_complement_sum` (288): compara tipos con igualdad. El complemento de K₁#K₂ se obtiene pegando los complementos a lo largo de un anillo, no por suma conexa.
- `schubert_companion_theorem` (195-196) y `schubert_is_JSJ_special_case` (372, 374): tienen `sorry` dentro del propio enunciado.
- `reidemeister_preserves_decomposition` (341): el axioma `reidemeister_equivalent` de `Schubert` choca en nombre con el de `Reidemeister`.
- `alexander_multiplicative` (353): el polinomio de Alexander se define salvo unidades ±tᵏ; aquí es un `Polynomial ℤ`.
- `square_knot_composite` y `square_knot_decomposition` (406, 410): nombres intercambiados. El nudo cuadrado es trébol # espejo, y el nudo de la abuela (*granny*) es trébol # trébol. Además usan una `prime_decomposition` arbitraria.

### C. Dependen de teoría que falta
- `apply_R1`, `apply_R2`, `apply_R3` (91, 127, 163): `KnotConfig` no modela la conexión de las hebras.
- `reidemeister_soundness` (282): falta un axioma que ligue los movimientos con `topologically_equivalent`.
- `knot_equivalence_decidable` (355): requiere el teorema de Haken.
- Unicidad de Schubert (156) y lo que se apoya en ella: `complexity_additive` (305), `composite_characterization` (318) y `example_has_two_prime_factors` (426).
- Sin definición: `is_satellite` (177), `satellite_pattern` (180), `torus_knot` (205), con su simetría (221) y género (225); `bridge_number` (246) con su aditividad (260); `genus_additive` (326); `granny_distinct_from_square` (419).

Las valoraciones matemáticas de esta sección son del auditor y conviene revisarlas. Solo la inconsistencia de `R1_inverse` está comprobada en Lean.

### Problema estructural
`DiagramSetoid`, y con él `Knot`, se construye sobre `reidemeister_refl`, `reidemeister_symm` y `reidemeister_trans`, que son `sorry`. Todo `Schubert` y `Bridge` descansa sobre eso. Solución sugerida: definir la equivalencia como relación inductiva generada por R1, R2, R3, reflexividad, simetría y transitividad.

## 5. Estado de `sorry` y axiomas

`sorry` (avisos del compilador, algunos duplicados): `Reidemeister` 16, `Schubert` 25, `TCN_06` 5, `KN_03` 2, `TCN_07` 2, y 1 en cada uno de `KN_00_Combinatoria`, `KN_Examples`, `KN_Instance_K3`, `TCN_05` y `TCN_08_Realizabilidad`.

Axiomas: `Schubert` 22, `Reidemeister` 11, `Basic` 5, `KN_01` 5, `Bridge` 2, y 1 en cada uno de `KN_00_Combinatoria`, `TCN_01`, `TCN_05` y `TCN_08_UniformityCriterion`. Total: 49.

## 6. Observaciones de mantenimiento

- `TMENudos.lean` solo importa `Basic`, `Reidemeister`, `Schubert`, `Bridge` y `TCN_01`. Los otros 29 módulos no forman parte de la biblioteca por defecto y hay que compilarlos por nombre.
- Archivos sueltos en la raíz que probablemente sobran: `build_error.log`, `temp_mirror_theorems.txt`, `lean-toolchain.backup`.
- Dos módulos, `KN_*` y `TCN_*`, implementan la misma teoría en paralelo. Conviene decidir cuál es el canónico.

## 7. Orden de trabajo recomendado

1. Corregir `R1_inverse` y `R2_inverse` (por ejemplo, con la hipótesis `move.add_twist = true ∨ 1 ≤ n`, o con tipos indexados). Es lo más urgente, porque hoy invalida `Reidemeister` y lo que depende de él.
2. Redefinir `reidemeister_equivalent` de forma inductiva. Con eso se cierran de 4 a 6 `sorry`.
3. Decidir los representantes o conteos de `TCN_06` (sección 3.2).
4. Reformular `gap_mirror`, `IDE_mirror` e `ime` (sección 3.3).
5. Arreglar `prime_decomposition` y los enunciados falsos de la clase B.
6. Hacer un commit con lo ya corregido, antes de iniciar los cambios de contenido de los pasos 1 a 5.
