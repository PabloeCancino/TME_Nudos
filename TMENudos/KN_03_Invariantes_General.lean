-- KN_03_Invariantes_General.lean
-- Invariantes para Configuraciones K_n
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Enero 9, 2026
--
-- CONVENCION: este modulo (IME₁ = `KnConfig.IME`) es de PRIMER nivel (nudo
-- ORIENTADO: solo rotaciones, grupo Z/2n; igual que `Isotopic` en `Basic.lean`).
-- El segundo nivel (no orientado, con σ = `mirror`, grupo D₂ₙ) esta en KN_03b
-- (`IME2`) y KN_04. La involucion over/under (`p.reverse`, KN_00: imagen
-- especular real τ, quiralidad) es un eje ortogonal y no es σ.

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

instance (p : OrderedPair n) (x : ZMod (2 * n)) : Decidable (p.encompasses x) := by
  unfold encompasses
  infer_instance

/-- Signo del par: +1 si la "longitud" (ratio) es impar, -1 si es par. -/
def sign (p : OrderedPair n) : Int :=
  if p.ratio.val % 2 == 1 then 1 else -1

/-- Dos pares están entrelazados si sus extremos se alternan. -/
def isInterlaced (p q : OrderedPair n) : Prop :=
  (p.encompasses q.fst ∧ ¬p.encompasses q.snd) ∨
  (¬p.encompasses q.fst ∧ p.encompasses q.snd)

instance : DecidableRel (@isInterlaced n) :=
  fun p q => by
    unfold isInterlaced
    infer_instance

/-- El gap es invariante bajo rotación -/
theorem gap_rotate (p : OrderedPair n) (k : ZMod (2 * n)) :
    (p.rotate k).gap = p.gap := by
  simp [gap, rotate]

/-- El signo es invariante bajo rotación -/
theorem sign_rotate (p : OrderedPair n) (k : ZMod (2 * n)) :
    (p.rotate k).sign = p.sign := by
  unfold sign
  rw [ratio_rotate]

/-- Encompasses is preserved under simultaneous rotation -/
theorem encompasses_rotate (p : OrderedPair n) (x : ZMod (2 * n)) (k : ZMod (2 * n)) :
    (p.rotate k).encompasses (x + k) ↔ p.encompasses x := by
  simp only [encompasses, rotate]
  have h1 : (x + k - (p.fst + k)).val = (x - p.fst).val := by
    congr 1
    ring
  have h2 : (p.snd + k - (p.fst + k)).val = (p.snd - p.fst).val := by
    congr 1
    ring
  rw [h1, h2]

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

/-- CAMBIO DE ENUNCIADO (auditoría):
    antes:   `p.mirror.gap = p.gap`  (FALSO: contraejemplo n=2, p=(0,1): huecos 0 y 2)
    después: `p.gap + p.mirror.gap + 2 = 2 * n` (con `[NeZero n]`; para n = 0, ZMod 0 = ℤ
    y la identidad no aplica).
    `mirror` manda (a,b) a (-a,-b): invierte el sentido de recorrido, así que el arco
    a → b pasa a ser (en las etiquetas nuevas) el arco complementario, y los huecos
    de ambos arcos suman 2n - 2. -/
theorem gap_mirror_add [NeZero n] (p : OrderedPair n) :
    p.gap + p.mirror.gap + 2 = 2 * n := by
  have hne : p.snd - p.fst ≠ 0 := p.ratio_ne_zero
  have hne' : p.fst - p.snd ≠ 0 := fun h => hne (by rw [← neg_sub, h, neg_zero])
  have h1 : (p.fst - p.snd).val = 2 * n - (p.snd - p.fst).val := by
    rw [← neg_sub, ZMod.neg_val, if_neg hne]
  have h2 : (p.mirror.snd - p.mirror.fst) = p.fst - p.snd := by
    simp only [mirror]; ring
  have hpos1 : 0 < (p.snd - p.fst).val := ZMod.val_pos.mpr hne
  have hpos2 : 0 < (p.fst - p.snd).val := ZMod.val_pos.mpr hne'
  have hlt := ZMod.val_lt (p.snd - p.fst)
  unfold gap
  rw [h2]
  omega

/-- CAMBIO DE ENUNCIADO (auditoría): el gap SÍ es invariante bajo la reflexión
    geométrica que además intercambia over y under, `p ↦ p.reverse.mirror = (-b, -a)`.
    (Esto es la reflexión de imagen especular más el cambio de parametrización.) -/
theorem gap_reverse_mirror (p : OrderedPair n) :
    p.reverse.mirror.gap = p.gap := by
  have h : p.reverse.mirror.snd - p.reverse.mirror.fst = p.snd - p.fst := by
    simp only [mirror, reverse]; ring
  unfold gap
  rw [h]

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
    (K.rotate k).IDE (p.rotate k) = K.IDE p := by
  simp only [IDE, OrderedPair.gap_rotate]
  congr 1
  simp only [rotate]
  have h : (K.pairs.image (fun q => q.rotate k)).filter (fun q => (p.rotate k).isInterlaced q) =
           (K.pairs.filter (fun q => p.isInterlaced q)).image (fun q => q.rotate k) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨r, hr, hrq⟩, hint⟩
      subst hrq
      exact ⟨r, ⟨hr, (OrderedPair.isInterlaced_rotate p r k).mp hint⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hint⟩, hrq⟩
      subst hrq
      exact ⟨⟨r, hr, rfl⟩, (OrderedPair.isInterlaced_rotate p r k).mpr hint⟩
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

/-- CAMBIO DE ENUNCIADO (auditoría): se ELIMINA `IDE_mirror`
    (antes: `K.mirror.IDE p.mirror = K.IDE p`, sorry y FALSO).
    Como `gap p.mirror = 2n - 2 - gap p` (ver `gap_mirror_add`), IDE no es invariante bajo
    `mirror`; ver el contraejemplo `not_IME_mirror` (n = 2).
    Esto muestra que IME₁ NO es un invariante de segundo nivel; para eso se usa
    `IME2` (KN_03b). -/
theorem not_IME_mirror : ∃ K : KnConfig 2, K.mirror.IME ≠ K.IME := by
  let S : Finset (OrderedPair 2) := {⟨0, 1, by decide⟩, ⟨2, 3, by decide⟩}
  refine ⟨⟨S, by decide, by decide⟩, ?_⟩
  decide

end KnConfig

end KnotTheory.General
