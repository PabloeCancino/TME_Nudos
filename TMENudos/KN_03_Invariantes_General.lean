-- KN_03_Invariantes_General.lean
-- Invariantes para Configuraciones K_n
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Enero 9, 2026

import TMENudos.KN_00_Fundamentos_General
import TMENudos.KN_02_Grupo_Dihedral_General

namespace KnotTheory.General

namespace OrderedPair

variable {n : ℕ}

/-- El "Gap" o brecha de un par (u, v) es el número de puntos
    estrictamente entre u y v en el sentido cíclico u → v.
    Se calcula como (v - u - 1) en Z_{2n}, llevado a Nat. -/
def gap (p : OrderedPair n) : ℕ := (p.snd - p.fst).val - 1

/-- Predicado: x está estrictamente en el arco u → v -/
def encompasses (p : OrderedPair n) (x : ZMod (2 * n)) : Prop :=
  (x - p.fst).val > 0 ∧ (x - p.fst).val < (p.snd - p.fst).val

instance (p : OrderedPair n) (x : ZMod (2 * n)) : Decidable (p.encompasses x) :=
  inferInstance

/-- Signo del par: +1 si la "longitud" (ratio) es impar, -1 si es par. -/
def sign (p : OrderedPair n) : Int :=
  if p.ratio.val % 2 == 1 then 1 else -1

/-- Dos pares están entrelazados si sus extremos se alternan. -/
def isInterlaced (p q : OrderedPair n) : Prop :=
  (p.encompasses q.fst ∧ ¬p.encompasses q.snd) ∨
  (¬p.encompasses q.fst ∧ p.encompasses q.snd)

instance : DecidableRel (@isInterlaced n) :=
  fun p q => inferInstance

/-- El gap es invariante bajo rotación -/
theorem gap_rotate (p : OrderedPair n) (k : ZMod (2 * n)) :
    (p.rotate k).gap = p.gap := by
  simp [gap, rotate]

/-- El signo es invariante bajo rotación -/
theorem sign_rotate (p : OrderedPair n) (k : ZMod (2 * n)) :
    (p.rotate k).sign = p.sign := by
  simp [sign, rotate, ratio_rotate]

/-- Encompasses is preserved under simultaneous rotation -/
theorem encompasses_rotate (p : OrderedPair n) (x : ZMod (2 * n)) (k : ZMod (2 * n)) :
    (p.rotate k).encompasses (x + k) ↔ p.encompasses x := by
  sorry

/-- Interlacing is preserved under simultaneous rotation -/
theorem isInterlaced_rotate (p q : OrderedPair n) (k : ZMod (2 * n)) :
    (p.rotate k).isInterlaced (q.rotate k) ↔ p.isInterlaced q := by
  simp only [isInterlaced, rotate]
  constructor <;> intro h
  · cases h with
    | inl h => left
               exact ⟨(encompasses_rotate p q.fst k).mp h.1,
                      mt (encompasses_rotate p q.snd k).mpr h.2⟩
    | inr h => right
               exact ⟨mt (encompasses_rotate p q.fst k).mpr h.1,
                      (encompasses_rotate p q.snd k).mp h.2⟩
  · cases h with
    | inl h => left
               exact ⟨(encompasses_rotate p q.fst k).mpr h.1,
                      mt (encompasses_rotate p q.snd k).mp h.2⟩
    | inr h => right
               exact ⟨mt (encompasses_rotate p q.fst k).mp h.1,
                      (encompasses_rotate p q.snd k).mpr h.2⟩

end OrderedPair

namespace KnConfig

variable {n : ℕ}

/-- IDE (Interlaced Distance Encircled) de un par p en una configuración K.
    Definido como: gap(p) - cantidad de pares que entrelazan a p -/
def IDE (K : KnConfig n) (p : OrderedPair n) : Int :=
  (p.gap : Int) - ((K.pairs.filter (fun q => p.isInterlaced q)).card : Int)

/-- IME (Interlaced Mass Encircled) de la configuración.
    Suma de los IDE de todos los pares. -/
def IME (K : KnConfig n) : Int :=
  K.pairs.sum (fun p => K.IDE p)

/-- IDE es invariante bajo rotación de la configuración -/
theorem IDE_rotate (K : KnConfig n) (p : OrderedPair n) (k : ZMod (2 * n)) :
    K.rotate k |>.IDE (p.rotate k) = K.IDE p := by
  simp only [IDE, OrderedPair.gap_rotate]
  congr 1
  simp only [rotate]
  have h : (K.pairs.image (fun q => q.rotate k)).filter (fun q => (p.rotate k).isInterlaced q) =
           (K.pairs.filter (fun q => p.isInterlaced q)).image (fun q => q.rotate k) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro ⟨⟨r, hr, hrq⟩, hint⟩
      use r, ⟨hr, by rw [← hrq]; exact (isInterlaced_rotate p r k).mp hint⟩, hrq
    · intro ⟨r, ⟨hr, hint⟩, hrq⟩
      use r, hr, hrq
      rw [← hrq]
      exact (isInterlaced_rotate p r k).mpr hint
  rw [h, Finset.card_image_of_injective]
  intro p₁ p₂ heq
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

/-- IME es invariante bajo rotación -/
theorem IME_rotate (K : KnConfig n) (k : ZMod (2 * n)) :
    (K.rotate k).IME = K.IME := by
  sorry

end KnConfig

end KnotTheory.General
