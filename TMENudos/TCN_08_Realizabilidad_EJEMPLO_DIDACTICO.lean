-- TCN_08_Realizabilidad_EJEMPLO_COMPLETO.lean
-- Ejemplo: Cómo se ve el teorema principal completamente probado
-- (Corregido en la auditoría 2026-09-29: dos órbitas de tamaños 12 y 2, total 14.)
-- Revisión Opción 1 (paridad de Gauss): sólo la órbita del trébol es realizable, total 2.
-- Revisión Etapa 3 (signo dato): realizables = órbitas de los dos tréboles, total 4.

import TMENudos.TCN_05_Orbitas
import TMENudos.TCN_06_Representantes
import TMENudos.TCN_07_Clasificacion

/-!
# Ejemplo Completo: Teorema de Conteo de Configuraciones Realizables

Este archivo muestra cómo se ve el teorema `total_realizable_configs`
completamente probado sin `sorry` statements.

## Estrategia de Prueba

1. Definir `realizableConfigs` como la unión de las órbitas de los dos tréboles
2. Sustituir las cardinalidades conocidas (`orbit_trefoilKnot_card`, `orbit_mirrorTrefoil_card`: 2)
   y la disjunción de las órbitas (`orbits_disjoint_trefoil_mirror`)

## Cambios respecto a la versión anterior (antes → después)

Motivo: con el signo como dato el trébol izquierdo (signos −) deja de estar en la órbita del
derecho (signos +): son DOS órbitas de 2 configuraciones, y ambas son realizables (irreducibles con
paridad de Gauss e índice cero).  La órbita de `specialClass` (12) no cumple ni la paridad de
Gauss ni el índice cero.

- `realizableConfigs`: `orbit trefoilKnot` → `orbit trefoilKnot ∪ orbit mirrorTrefoil`
  (antes de eso: `orbit specialClass ∪ orbit trefoilKnot`).
- `total_realizable_configs`: `= 2` → `= 4` (antes aún: 14).
- `realizable_fraction`: `= 1/60` → `= 1/240` (4/960; antes aún 7/60).
- `isRealizable` aquí es la forma simplificada `K ∈ orbit trefoilKnot ∨ K ∈ orbit mirrorTrefoil`;
  en `TCN_08` se define como `(¬hasR1 ∧ ¬hasR2) ∧ gaussEven ∧ indexZero` y se prueba equivalente.

Nota: este archivo es aislado (no importa TCN_08 porque redefine los mismos nombres).

-/

namespace KnotTheory

open OrderedPair K3Config DihedralD6

/-! ## Teoremas Auxiliares

Ya disponibles en los módulos importados:
`orbit_trefoilKnot_card`, `orbit_mirrorTrefoil_card` y
`orbits_disjoint_trefoil_mirror` (TCN_06). -/

/-! ## Definición de Realizabilidad -/

/-- Versión didáctica de `isRealizable` (aislada del módulo TCN_08 para el ejemplo):
    pertenencia a la órbita de uno de los dos tréboles (equivalente a la definición de TCN_08).
    Antes: `K ∈ orbit trefoilKnot`. -/
def isRealizable (K : K3Config) : Prop :=
  K ∈ orbit trefoilKnot ∨ K ∈ orbit mirrorTrefoil

/-- Versión didáctica de `realizableConfigs`.
    Antes: `orbit trefoilKnot`. -/
def realizableConfigs : Finset K3Config :=
  orbit trefoilKnot ∪ orbit mirrorTrefoil

/-! ## Teorema Principal (VERSIÓN COMPLETA SIN SORRY) -/

/-- **TEOREMA: Cardinalidad de Configuraciones Realizables**

    El número total de configuraciones K₃ realizables es exactamente 4 (antes: 2).

    **Demostración completa:**
    ```
    |realizableConfigs| = |orbit trefoilKnot| + |orbit mirrorTrefoil| = 2 + 2
    ```
-/
theorem total_realizable_configs :
    realizableConfigs.card = 4 := by
  unfold realizableConfigs
  rw [Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr
      orbits_disjoint_trefoil_mirror), orbit_trefoilKnot_card, orbit_mirrorTrefoil_card]

/-! ## Teoremas Derivados -/

/-- Fracción de configuraciones realizables: 4/960 = 1/240 (antes 2/120 = 1/60) -/
theorem realizable_fraction :
    (realizableConfigs.card : ℚ) / totalConfigs = 1 / 240 := by
  rw [total_realizable_configs]
  unfold totalConfigs
  norm_num

/-- El conjunto de realizables tiene exactamente 4 elementos -/
example : realizableConfigs.card = 4 := total_realizable_configs

end KnotTheory

/-!
## Análisis de la Prueba

### Dependencias
1. `orbit_trefoilKnot_card`, `orbit_mirrorTrefoil_card`, `orbits_disjoint_trefoil_mirror` (TCN_06)

### Tácticas Usadas
- `unfold`: Expandir definiciones
- `rw`: reescritura (cardinal de unión disjunta) y aritmética (fracción)

### Por Qué Funciona

`realizableConfigs` es la unión disjunta de las dos órbitas de tréboles, cada una de
cardinalidad 2 (por órbita-estabilizador con |Stab| = 6).  Antes era una sola órbita (la del
trébol, porque sin signo el izquierdo era `r³ •` el derecho); y antes aún la unión disjunta de
`specialClass` (12) y el trébol (2).

**No hay magia, no hay axiomas ocultos, todo es verificable.**

### Lecciones para Otros Teoremas (versión actual de TCN_08)

**`non_realizable_count`:** 960 - 4 = 956 (`omega` con la partición
`finset_card_partition`; antes 120 - 2 = 118).

**`realizable_orbit_card_eq_two`:** si K es realizable, `orbit K` es la órbita de uno de los dos
tréboles (`orbit_eq_of_mem`), y su cardinalidad es 2.

### Estado de Verificación

Este archivo no usa `sorry` ni axiomas; sus dependencias (TCN_05, TCN_06) están demostradas.

-/
