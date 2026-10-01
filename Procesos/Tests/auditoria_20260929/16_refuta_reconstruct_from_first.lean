-- SONDA 16 (2026-10-01): el axioma `reconstruct_from_first` de Basic.lean es FALSO tal como esta escrito.
-- Contraejemplo con n = 3: dos configuraciones con las mismas razones indice a indice y sin desplazamiento
-- uniforme. De el se deriva `False`. Compila con: lake env lean Procesos/Tests/auditoria_20260929/16_refuta_reconstruct_from_first.lean
import TMENudos.Basic
open TMENudos

def c03 : RationalCrossing 3 := ⟨(0 : ℝ[3]), (3 : ℝ[3]), by decide, true⟩
def c14 : RationalCrossing 3 := ⟨(1 : ℝ[3]), (4 : ℝ[3]), by decide, true⟩
def c25 : RationalCrossing 3 := ⟨(2 : ℝ[3]), (5 : ℝ[3]), by decide, true⟩

/-- Tres cruces antipodales (0,3),(1,4),(2,5), en ese orden de índices. -/
def KA : RationalConfiguration 3 where
  crossings := fun i => if i = 0 then c03 else if i = 1 then c14 else c25
  coverage := by decide

/-- Los mismos tres cruces con los índices 1 y 2 intercambiados. -/
def KB : RationalConfiguration 3 where
  crossings := fun i => if i = 0 then c03 else if i = 1 then c25 else c14
  coverage := by decide

theorem mismas_razones : ∀ i : Fin 3, ratio_val (KA.crossings i) = ratio_val (KB.crossings i) := by
  decide

theorem sin_desplazamiento_uniforme :
    ¬ ∃ k : ℝ[3], ∀ i : Fin 3, (KB.crossings i).over_pos = (KA.crossings i).over_pos + k := by
  decide

/-- Si el axioma fuera cierto se derivaría False. -/
theorem reconstruct_from_first_da_False : False := by
  obtain ⟨k, hk⟩ := reconstruct_from_first KA KB mismas_razones
  exact sin_desplazamiento_uniforme ⟨k, hk⟩

#print axioms reconstruct_from_first_da_False
