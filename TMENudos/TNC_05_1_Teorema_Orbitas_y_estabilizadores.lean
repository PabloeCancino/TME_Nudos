-- TNC_05_1_Teorema_Orbitas_y_estabilizadores.lean
-- Sustento para los teoremas de órbitas y estabilizadores

import TMENudos.TCN_05_Orbitas

/-!
# Sustento: Teorema Órbita-Estabilizador

Esta versión previa del archivo duplicaba (con demostraciones incompletas o incorrectas)
declaraciones que ya están demostradas en `TMENudos.TCN_05_Orbitas`:

- `card_D6`
- `stabilizer_is_subgroup`
- `orbit_stabilizer`
- `orbit_card_from_stabilizer`
- `orbit_stabilizer'`
- `orbit_card_dvd`
- `stabilizer_card_dvd`

Se eliminaron los duplicados (causaban errores de "already declared"). Además se eliminó
el lema privado `orbit_bijection`, cuyo enunciado era falso (la igualdad correcta involucra
conjugación: `Stab(g • K) = g Stab(K) g⁻¹`).

Aquí se dejan únicamente reexpresiones útiles de los resultados de `TCN_05_Orbitas`.
-/

namespace KnotTheory

open DihedralD6 K3Config

/-- El estabilizador de `g • K` es el conjugado del estabilizador de `K`:
    `h ∈ Stab(K)` implica `g * h * g⁻¹ ∈ Stab(g • K)`. -/
theorem conj_mem_stabilizer_smul (K : K3Config) (g h : DihedralD6) (hh : h ∈ Stab(K)) :
    g * h * g⁻¹ ∈ Stab(DihedralD6.actOnConfig g K) := by
  unfold stabilizer at hh ⊢
  have hh' : DihedralD6.actOnConfig h K = K := (Finset.mem_filter.mp hh).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [← DihedralD6.actOnConfig_comp]
  have : g * h * g⁻¹ * g = g * h := by group
  rw [this, DihedralD6.actOnConfig_comp, hh']

end KnotTheory
