-- KN_03b_Invariantes_IME.lean
-- Teorema IME_rotate (requiere importar KN_03 para acceder a IDE_rotate)
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Enero 9, 2026

import TMENudos.KN_03_Invariantes_General

namespace KnotTheory.General

namespace KnConfig

variable {n : ℕ}

/-- IME es invariante bajo rotación -/
theorem IME_rotate (K : KnConfig n) (k : ZMod (2 * n)) :
    (K.rotate k).IME = K.IME := by
  simp only [IME, rotate]
  rw [Finset.sum_image]
  · congr 1
    ext p
    exact IDE_rotate K p k
  · intro p₁ _ p₂ _ heq
    have h1 : p₁.fst = p₂.fst := by
      have := congr_arg OrderedPair.fst heq
      simp only [OrderedPair.rotate] at this
      exact add_right_cancel this
    have h2 : p₁.snd = p₂.snd := by
      have := congr_arg OrderedPair.snd heq
      simp only [OrderedPair.rotate] at this
      exact add_right_cancel this
    cases p₁; cases p₂
    simp_all

end KnConfig

end KnotTheory.General
