-- TCN_04_DihedralD6.lean
-- Teoría Combinatoria de Nudos K₃: Bloque 4 - Grupo Diédrico D₆

import TMENudos.TCN_01_Fundamentos
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Bloque 4: Grupo Diédrico D₆

Definición del grupo D₆ usando la implementación de Mathlib y acciones sobre configuraciones.

## Autor

Dr. Pablo Eduardo Cancino Marentes

-/

namespace KnotTheory

open DihedralGroup

/-! ## Definición del Grupo -/

/-- El grupo diédrico D₆ con 12 elementos -/
abbrev DihedralD6 := DihedralGroup 6

namespace DihedralD6

/-! ## Elementos Generadores -/

/-- Rotación básica -/
def rGen : DihedralD6 := r 1

/-- Reflexión básica -/
def sGen : DihedralD6 := sr 0

/-! ## Propiedades del Grupo -/

/-- El grupo D₆ tiene exactamente 12 elementos -/
theorem card_eq_12 : Fintype.card DihedralD6 = 12 := by
  simp [DihedralGroup.card]

/-- rGen tiene orden 6 -/
theorem rGen_order_six : orderOf rGen = 6 := by
  unfold rGen
  rw [orderOf_r_one]

/-- sGen tiene orden 2 -/
theorem sGen_order_two : orderOf sGen = 2 := by
  unfold sGen
  rw [orderOf_sr]

/-! ## Acciones del Grupo D₆ -/

/-- Acción de D₆ sobre Z/6Z.

    NOTA: DihedralGroup de Mathlib no permite pattern matching directo.
    Usamos sorry por ahora hasta implementar usando API de Mathlib correctamente. -/
def actionZMod (g : DihedralD6) (i : ZMod 6) : ZMod 6 :=
  sorry  -- Implementar usando representación de DihedralGroup

/-- Acción sobre OrderedPair -/
def actOnPair (g : DihedralD6) (p : OrderedPair) : OrderedPair :=
  OrderedPair.make
    (actionZMod g p.fst)
    (actionZMod g p.snd)
    (by sorry)  -- Probar que actionZMod preserva p.fst ≠ p.snd

/-- Acción sobre K3Config -/
def actOnConfig (g : DihedralD6) (K : K3Config) : K3Config := {
  pairs := K.pairs.image (actOnPair g)
  card_eq := by sorry  -- Probar inyectividad
  is_partition := by sorry  -- Probar preservación de partición
}

/-- Notación para acción -/
notation:70 g " • " K => actOnConfig g K

/-! ## Propiedades de las Acciones -/

/-- La identidad fija todas las configuraciones -/
theorem actOnConfig_id (K : K3Config) : actOnConfig 1 K = K := by
  sorry

/-- La acción respeta la composición -/
theorem actOnConfig_comp (g₁ g₂ : DihedralD6) (K : K3Config) :
  actOnConfig (g₁ * g₂) K = actOnConfig g₁ (actOnConfig g₂ K) := by
  sorry

/-!
## Resumen

✅ **Grupo D₆**: Via Mathlib
✅ **12 elementos**: `card_eq_12`
✅ **Generadores**: `rGen`, `sGen`
✅ **Acciones**: Definidas (con sorry para implementación)
⚠️ **Pendiente**: Implementar acciones usando API de Mathlib

## Próximos Pasos

Las acciones están estructuralmente definidas pero requieren implementación
concreta usando la API de DihedralGroup de Mathlib.

-/

end DihedralD6
end KnotTheory
