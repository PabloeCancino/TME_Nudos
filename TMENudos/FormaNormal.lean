import Mathlib

/-!
# Forma normal única para la reducción R1/R2 (Etapa 1)

Modelo de palabras de Gauss con signos (listas cíclicas), movimientos R1/R2, equivalencia
(rotación más reetiquetado), lema de Newman módulo una equivalencia (abstracto) e infraestructura
geométrica simple (conmutación y persistencia de candidatos).
Ver `Procesos/20261001_diseno_forma_normal.md`.
-/

namespace FormaNormal

/-! ## 1. Lema de Newman módulo una equivalencia (abstracto) -/

section Newman

open Relation

variable {α : Type} {R E : α → α → Prop}

/-- La compatibilidad se levanta a la cerradura reflexivo-transitiva. -/
theorem lift_compat
    (hcomp : ∀ x x' y, E x x' → R x y → ∃ y', R x' y' ∧ E y y')
    {x x' y : α} (hxx : E x x') (hxy : ReflTransGen R x y) :
    ∃ y', ReflTransGen R x' y' ∧ E y y' := by
  induction hxy with
  | refl => exact ⟨x', .refl, hxx⟩
  | tail _ hbc ih =>
    obtain ⟨y1, h1, e1⟩ := ih
    obtain ⟨y2, h2, e2⟩ := hcomp _ _ _ e1 hbc
    exact ⟨y2, h1.tail h2, e2⟩

/-- **Lema de Newman módulo una equivalencia**: terminación, compatibilidad y confluencia local
módulo `E` implican confluencia módulo `E`. -/
theorem newman_mod (hE : Equivalence E) (hwf : WellFounded (flip R))
    (hcomp : ∀ x x' y, E x x' → R x y → ∃ y', R x' y' ∧ E y y')
    (hloc : ∀ x y z, R x y → R x z →
      ∃ y' z', ReflTransGen R y y' ∧ ReflTransGen R z z' ∧ E y' z') :
    ∀ x y z, ReflTransGen R x y → ReflTransGen R x z →
      ∃ y' z', ReflTransGen R y y' ∧ ReflTransGen R z z' ∧ E y' z' := by
  intro x
  induction x using hwf.induction with
  | _ x ih =>
    intro y z hy hz
    rcases hy.cases_head with h | ⟨y1, hxy1, hy1y⟩
    · subst h
      exact ⟨z, z, hz, .refl, hE.refl z⟩
    rcases hz.cases_head with h | ⟨z1, hxz1, hz1z⟩
    · subst h
      exact ⟨y, y, .refl, hy, hE.refl y⟩
    obtain ⟨u, v, hu, hv, huv⟩ := hloc x y1 z1 hxy1 hxz1
    obtain ⟨y2, u2, hy2, hu2, e1⟩ := ih y1 hxy1 y u hy1y hu
    obtain ⟨v2, hv2, e2⟩ := lift_compat hcomp huv hu2
    obtain ⟨z2, v3, hz2, hv3, e3⟩ := ih z1 hxz1 z v2 hz1z (hv.trans hv2)
    obtain ⟨y3, hy3, e4⟩ := lift_compat hcomp (hE.symm (hE.trans e1 e2)) hv3
    exact ⟨y3, z2, hy2.trans hy3, hz2, hE.symm (hE.trans e3 e4)⟩

/-- **Forma normal única módulo `E`**. -/
theorem normal_form_unique (hE : Equivalence E) (hwf : WellFounded (flip R))
    (hcomp : ∀ x x' y, E x x' → R x y → ∃ y', R x' y' ∧ E y y')
    (hloc : ∀ x y z, R x y → R x z →
      ∃ y' z', ReflTransGen R y y' ∧ ReflTransGen R z z' ∧ E y' z')
    {x n n' : α} (hn : ReflTransGen R x n) (hn' : ReflTransGen R x n')
    (hirr : ¬ ∃ y, R n y) (hirr' : ¬ ∃ y, R n' y) : E n n' := by
  obtain ⟨y', z', h1, h2, e⟩ := newman_mod hE hwf hcomp hloc x n n' hn hn'
  have hy : y' = n := by
    rcases h1.cases_head with h | ⟨c, hc, _⟩
    · exact h.symm
    · exact absurd ⟨c, hc⟩ hirr
  have hz : z' = n' := by
    rcases h2.cases_head with h | ⟨c, hc, _⟩
    · exact h.symm
    · exact absurd ⟨c, hc⟩ hirr'
  rw [hy, hz] at e
  exact e

/-- **Existencia de forma normal**: todo elemento alcanza un irreducible. -/
theorem exists_normal_form (hwf : WellFounded (flip R)) (x : α) :
    ∃ n, ReflTransGen R x n ∧ ¬ ∃ y, R n y := by
  induction x using hwf.induction with
  | _ x ih =>
    by_cases h : ∃ y, R x y
    · obtain ⟨y, hy⟩ := h
      obtain ⟨n, hn, hirr⟩ := ih y hy
      exact ⟨n, .head hy hn, hirr⟩
    · exact ⟨x, .refl, h⟩

/-- Newman estándar (`E` = igualdad), corolario del caso módulo `E`. -/
theorem newman (hwf : WellFounded (flip R))
    (hloc : ∀ x y z, R x y → R x z →
      ∃ w, ReflTransGen R y w ∧ ReflTransGen R z w) :
    ∀ x y z, ReflTransGen R x y → ReflTransGen R x z →
      ∃ w, ReflTransGen R y w ∧ ReflTransGen R z w := by
  have hcomp : ∀ x x' y, x = x' → R x y → ∃ y', R x' y' ∧ y = y' := by
    intro x x' y h hxy; subst h; exact ⟨y, hxy, rfl⟩
  have hloc' : ∀ x y z, R x y → R x z →
      ∃ y' z', ReflTransGen R y y' ∧ ReflTransGen R z z' ∧ y' = z' := by
    intro x y z h1 h2
    obtain ⟨w, hw1, hw2⟩ := hloc x y z h1 h2
    exact ⟨w, w, hw1, hw2, rfl⟩
  intro x y z hy hz
  obtain ⟨y', z', h1, h2, e⟩ := newman_mod (E := (· = ·)) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    hwf hcomp hloc' x y z hy hz
  subst e
  exact ⟨y', h1, h2⟩

end Newman

/-! ## 2. Modelo: palabras de Gauss con signos -/

/-- Una letra: etiqueta del cruce, paso por arriba (`up`) o por abajo, y signo. -/
structure Letter where
  label : ℕ
  up : Bool
  pos : Bool
  deriving DecidableEq, Repr

/-- Palabra (lista cíclica). -/
abbrev W := List Letter

/-- Buena formación: cada etiqueta que aparece lo hace exactamente dos veces, una por arriba y
otra por abajo, con el mismo signo. -/
def Wf (w : W) : Prop :=
  ∀ c : ℕ, w.filter (fun l => l.label = c) = [] ∨
    ∃ s : Bool, (w.filter (fun l => l.label = c)).Perm [⟨c, true, s⟩, ⟨c, false, s⟩]

/-- Quitar el cruce `c` (sin renumerar). -/
def remove (w : W) (c : ℕ) : W := w.filter (fun l => l.label ≠ c)

/-- Quitar dos cruces. -/
def remove2 (w : W) (a b : ℕ) : W := remove (remove w a) b

/-- Número de letras con etiqueta `c`. -/
def cnt (c : ℕ) (w : W) : ℕ := w.countP (fun l => l.label = c)

/-- Número de cruces: etiquetas distintas que aparecen. -/
def crossings (w : W) : ℕ := (w.map Letter.label).toFinset.card

theorem mem_remove {w : W} {c : ℕ} {l : Letter} : l ∈ remove w c ↔ l ∈ w ∧ l.label ≠ c := by
  simp [remove]

theorem remove_remove_comm (w : W) (c d : ℕ) : remove (remove w c) d = remove (remove w d) c := by
  simp only [remove, List.filter_filter]
  congr 1
  funext l
  exact Bool.and_comm _ _

/-- Conmutación de quitar cruces disjuntos (forma general con filtros). -/
theorem filter_filter_comm (w : W) (p q : Letter → Bool) :
    (w.filter p).filter q = (w.filter q).filter p := by
  simp only [List.filter_filter]
  congr 1
  funext l
  exact Bool.and_comm _ _

theorem filter_label_remove (w : W) (d c : ℕ) :
    (remove w d).filter (fun l => l.label = c) =
      if c = d then [] else w.filter (fun l => l.label = c) := by
  unfold remove
  rw [List.filter_filter]
  split_ifs with h
  · subst h
    simp
  · congr 1
    funext l
    by_cases hl : l.label = c
    · simp [hl, h]
    · simp [hl]

theorem cnt_remove {w : W} {c d : ℕ} (h : c ≠ d) : cnt c (remove w d) = cnt c w := by
  unfold cnt remove
  rw [List.countP_filter]
  congr 1
  funext l
  by_cases hl : l.label = c
  · simp [hl, h]
  · simp [hl]

theorem cnt_eq_length_filter (c : ℕ) (w : W) :
    cnt c w = (w.filter (fun l => l.label = c)).length := by
  simp [cnt, List.countP_eq_length_filter]

theorem wf_remove {w : W} (hw : Wf w) (d : ℕ) : Wf (remove w d) := by
  intro c
  rw [filter_label_remove]
  split_ifs with h
  · exact Or.inl rfl
  · exact hw c

theorem wf_remove2 {w : W} (hw : Wf w) (a b : ℕ) : Wf (remove2 w a b) :=
  wf_remove (wf_remove hw a) b

theorem wf_rotate {w : W} (hw : Wf w) (k : ℕ) : Wf (w.rotate k) := by
  intro c
  have hp := (List.rotate_perm w k).filter (fun l => decide (l.label = c))
  rcases hw c with h | ⟨s, hs⟩
  · left
    rw [h] at hp
    exact List.perm_nil.mp hp
  · right
    exact ⟨s, hp.trans hs⟩

theorem wf_cnt_le {w : W} (hw : Wf w) (c : ℕ) : cnt c w ≤ 2 := by
  rw [cnt_eq_length_filter]
  rcases hw c with h | ⟨s, hs⟩
  · rw [h]; simp
  · rw [hs.length_eq]; simp

theorem wf_nil : Wf [] := fun _ => Or.inl rfl

/-! ### Cruces -/

theorem crossings_remove {w : W} {c : ℕ} (hc : c ∈ w.map Letter.label) :
    crossings (remove w c) + 1 = crossings w := by
  have : ((remove w c).map Letter.label).toFinset = ((w.map Letter.label).toFinset).erase c := by
    ext x
    simp only [remove, List.mem_toFinset, List.mem_map, List.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨l, ⟨hl, hne⟩, rfl⟩
      exact ⟨by simpa using hne, l, hl, rfl⟩
    · rintro ⟨hne, l, hl, rfl⟩
      exact ⟨l, ⟨hl, by simpa using hne⟩, rfl⟩
  unfold crossings
  rw [this, Finset.card_erase_of_mem (List.mem_toFinset.mpr hc)]
  have : 0 < ((w.map Letter.label).toFinset).card :=
    Finset.card_pos.mpr ⟨c, List.mem_toFinset.mpr hc⟩
  omega

theorem mem_labels_remove {w : W} {a b : ℕ} (hab : b ≠ a) (hb : b ∈ w.map Letter.label) :
    b ∈ (remove w a).map Letter.label := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hb
  exact List.mem_map.mpr ⟨l, mem_remove.mpr ⟨hl, hab⟩, rfl⟩

theorem crossings_remove2 {w : W} {a b : ℕ} (hab : a ≠ b) (ha : a ∈ w.map Letter.label)
    (hb : b ∈ w.map Letter.label) : crossings (remove2 w a b) + 2 = crossings w := by
  have h1 := crossings_remove ha
  have h2 := crossings_remove (mem_labels_remove (Ne.symm hab) hb)
  unfold remove2
  omega

/-- En palabras bien formadas, la longitud es el doble del número de cruces. -/
theorem wf_length_eq {w : W} (hw : Wf w) : w.length = 2 * crossings w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    cases w with
    | nil =>
      simp only [List.length_nil] at hn
      subst hn
      simp [crossings]
    | cons l t =>
      set c := l.label with hc
      have hmem : c ∈ (l :: t).map Letter.label := by simp [hc]
      have hrem := crossings_remove hmem
      have hf : ((l :: t).filter (fun x => x.label = c)).length = 2 := by
        rcases hw c with h | ⟨s, hs⟩
        · simp [hc] at h
        · rw [hs.length_eq]; rfl
      have hsplit := List.length_eq_length_filter_add (l := l :: t) (fun x => decide (x.label = c))
      have hrm : ((l :: t).filter (fun x => !decide (x.label = c))) = remove (l :: t) c := by
        simp [remove]
      rw [hrm, hf] at hsplit
      have hlt : (remove (l :: t) c).length < n := by
        have : 0 < ((l :: t).filter (fun x => x.label = c)).length := by omega
        omega
      have := ih _ hlt (wf_remove hw c) rfl
      omega

/-! ## 3. Rotación, reetiquetado y la equivalencia `≈` -/

theorem rotate_inv (w : W) (k : ℕ) : ∃ j, (w.rotate k).rotate j = w := by
  rcases Nat.eq_zero_or_pos w.length with h | h
  · have : w = [] := List.length_eq_zero_iff.mp h
    subst this
    exact ⟨0, by simp⟩
  · refine ⟨w.length - k % w.length, ?_⟩
    have h1 := Nat.mod_add_div k w.length
    have h2 := Nat.mod_lt k h
    have h3 : k + (w.length - k % w.length) = w.length * (k / w.length + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [List.rotate_rotate, h3, List.rotate_length_mul]

/-- Renombrado de etiquetas. -/
def relabel (f : ℕ → ℕ) (l : Letter) : Letter := { l with label := f l.label }

/-- Etiquetas que aparecen en la palabra. -/
def labelSet (w : W) : Set ℕ := {c | c ∈ w.map Letter.label}

theorem relabel_relabel (f g : ℕ → ℕ) (l : Letter) :
    relabel g (relabel f l) = relabel (g ∘ f) l := rfl

theorem map_relabel_self {w : W} {f : ℕ → ℕ} (h : ∀ c ∈ labelSet w, f c = c) :
    w.map (relabel f) = w := by
  conv_rhs => rw [← List.map_id w]
  apply List.map_congr_left
  intro l hl
  have := h l.label (List.mem_map.mpr ⟨l, hl, rfl⟩)
  cases l
  simp_all [relabel]

theorem labelSet_map_rotate (w : W) (k : ℕ) (f : ℕ → ℕ) :
    labelSet ((w.rotate k).map (relabel f)) = f '' labelSet w := by
  ext c
  simp only [labelSet, Set.mem_setOf_eq, Set.mem_image, List.mem_map, List.mem_rotate]
  constructor
  · rintro ⟨l', ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨l.label, ⟨l, hl, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨relabel f l, ⟨l, hl, rfl⟩, rfl⟩

/-- Equivalencia `≈`: una rotación seguida de un renombrado inyectivo sobre las etiquetas. -/
def Equiv (w w' : W) : Prop :=
  ∃ (k : ℕ) (f : ℕ → ℕ), Set.InjOn f (labelSet w) ∧ (w.rotate k).map (relabel f) = w'

theorem Equiv.refl' (w : W) : Equiv w w :=
  ⟨0, id, Set.injOn_id _, by simpa using map_relabel_self (w := w) (f := id) (fun _ _ => rfl)⟩

theorem Equiv.symm' {w w' : W} (h : Equiv w w') : Equiv w' w := by
  obtain ⟨k, f, hinj, rfl⟩ := h
  obtain ⟨j, hj⟩ := rotate_inv w k
  classical
  set g := Function.invFunOn f (labelSet w) with hg
  have hleft : ∀ c ∈ labelSet w, g (f c) = c := fun c hc => hinj.leftInvOn_invFunOn hc
  refine ⟨j, g, ?_, ?_⟩
  · rw [labelSet_map_rotate]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [hleft a ha, hleft b hb] at hab
    rw [hab]
  · rw [← List.map_rotate, hj, List.map_map]
    have : (relabel g ∘ relabel f) = relabel (g ∘ f) := by
      funext l; rfl
    rw [this]
    exact map_relabel_self (fun c hc => hleft c hc)

theorem Equiv.trans' {w w' w'' : W} (h1 : Equiv w w') (h2 : Equiv w' w'') : Equiv w w'' := by
  obtain ⟨k, f, hf, rfl⟩ := h1
  obtain ⟨k', g, hg, rfl⟩ := h2
  refine ⟨k + k', g ∘ f, ?_, ?_⟩
  · intro a ha b hb hab
    rw [labelSet_map_rotate] at hg
    apply hf ha hb
    exact hg ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hab
  · rw [← List.map_rotate, List.map_map, List.rotate_rotate]
    rfl

/-- `≈` es una relación de equivalencia (sobre todas las palabras, en particular las `Wf`). -/
theorem equiv_equivalence : Equivalence Equiv :=
  ⟨Equiv.refl', Equiv.symm', Equiv.trans'⟩

/-! ## 4. Movimientos R1 y R2 -/

/-- R1 en la etiqueta `c`: sus dos letras son cíclicamente consecutivas (existe una rotación que
las pone en cabeza; con una palabra de 2 letras también cuenta el envolvimiento). -/
def R1cand (w : W) (c : ℕ) : Prop :=
  ∃ (k : ℕ) (x y : Letter) (rest : W), w.rotate k = x :: y :: rest ∧ x.label = c ∧ y.label = c

/-- Dos letras cíclicamente consecutivas `x y` (en ese orden) que cumplen `p x` y `q y`. -/
def Adj (w : W) (p q : Letter → Prop) : Prop :=
  ∃ (k : ℕ) (x y : Letter) (rest : W), w.rotate k = x :: y :: rest ∧ p x ∧ q y

/-- Los pasos del lado `s` (`true` = por arriba) de `a` y `b` son cíclicamente consecutivos. -/
def AdjSide (w : W) (s : Bool) (a b : ℕ) : Prop :=
  Adj w (fun x => x.label = a ∧ x.up = s) (fun y => y.label = b ∧ y.up = s) ∨
  Adj w (fun x => x.label = b ∧ x.up = s) (fun y => y.label = a ∧ y.up = s)

/-- Entrelazado (dirigido): `w = u ++ x :: v ++ y :: z` con `x, y` las dos letras de `a`,
exactamente una letra de `b` en el arco `v` y exactamente una en el arco complementario `z ++ u`.
Es invariante por rotación (`Linked.rotate`). -/
def Linked (w : W) (a b : ℕ) : Prop :=
  ∃ (u : W) (x : Letter) (v : W) (y : Letter) (z : W),
    w = u ++ (x :: (v ++ (y :: z))) ∧ x.label = a ∧ y.label = a ∧
      cnt b v = 1 ∧ cnt b (z ++ u) = 1

/-- Entrelazado de las cuerdas `a` y `b` (simétrico por definición). -/
def Interlaced (w : W) (a b : ℕ) : Prop := Linked w a b ∨ Linked w b a

/-- Los cruces `a` y `b` tienen signos distintos. -/
def OppSign (w : W) (a b : ℕ) : Prop :=
  ∃ x ∈ w, ∃ y ∈ w, x.label = a ∧ y.label = b ∧ x.pos ≠ y.pos

/-- Candidato R2 en `(a, b)`. -/
def R2cand (w : W) (a b : ℕ) : Prop :=
  a ≠ b ∧ AdjSide w true a b ∧ AdjSide w false a b ∧ Interlaced w a b ∧ OppSign w a b

/-- Un paso de reducción: quitar un cruce candidato R1 o dos candidatos R2. -/
def Red (w w' : W) : Prop :=
  (∃ c, R1cand w c ∧ w' = remove w c) ∨ (∃ a b, R2cand w a b ∧ w' = remove2 w a b)

/-! ### Terminación -/

theorem R1cand.mem {w : W} {c : ℕ} (h : R1cand w c) : c ∈ w.map Letter.label := by
  obtain ⟨k, x, y, rest, hk, hx, -⟩ := h
  have : x ∈ w.rotate k := by rw [hk]; simp
  exact List.mem_map.mpr ⟨x, List.mem_rotate.mp this, hx⟩

theorem R2cand.mem {w : W} {a b : ℕ} (h : R2cand w a b) :
    a ∈ w.map Letter.label ∧ b ∈ w.map Letter.label := by
  obtain ⟨-, -, -, -, x, hx, y, hy, hxa, hyb, -⟩ := h
  exact ⟨List.mem_map.mpr ⟨x, hx, hxa⟩, List.mem_map.mpr ⟨y, hy, hyb⟩⟩

/-- Cada paso de `Red` baja el número de cruces (en 1 o en 2). -/
theorem Red.crossings_lt {w w' : W} (h : Red w w') : crossings w' < crossings w := by
  rcases h with ⟨c, hc, rfl⟩ | ⟨a, b, hab, rfl⟩
  · have := crossings_remove hc.mem
    omega
  · have := crossings_remove2 hab.1 hab.mem.1 hab.mem.2
    omega

theorem Red.crossings_eq {w w' : W} (h : Red w w') :
    crossings w' + 1 = crossings w ∨ crossings w' + 2 = crossings w := by
  rcases h with ⟨c, hc, rfl⟩ | ⟨a, b, hab, rfl⟩
  · exact Or.inl (crossings_remove hc.mem)
  · exact Or.inr (crossings_remove2 hab.1 hab.mem.1 hab.mem.2)

/-- `Red` termina: no hay cadenas infinitas de reducciones. -/
theorem red_wf : WellFounded (flip Red) :=
  Subrelation.wf (fun {_ _} h => Red.crossings_lt h) (InvImage.wf crossings wellFounded_lt)

theorem Red.wf_preserved {w w' : W} (hw : Wf w) (h : Red w w') : Wf w' := by
  rcases h with ⟨c, -, rfl⟩ | ⟨a, b, -, rfl⟩
  · exact wf_remove hw c
  · exact wf_remove2 hw a b

/-! ## 5. Infraestructura geométrica simple -/

/-! ### (a) Conmutación -/

/-- Quitar cruces conmuta (cruces cualesquiera). -/
theorem remove_comm (w : W) (c d : ℕ) : remove (remove w c) d = remove (remove w d) c :=
  remove_remove_comm w c d

/-- Quitar dos cruces es simétrico en los dos cruces. -/
theorem remove2_comm (w : W) (a b : ℕ) : remove2 w a b = remove2 w b a :=
  remove_remove_comm w a b

/-! ### (b) Persistencia de candidatos -/

theorem filter_rotate (p : Letter → Bool) (w : W) (k : ℕ) :
    ∃ m, (w.rotate k).filter p = (w.filter p).rotate m := by
  rcases Nat.eq_zero_or_pos w.length with h | h
  · have : w = [] := List.length_eq_zero_iff.mp h
    subst this
    exact ⟨0, by simp⟩
  · have hk : k % w.length ≤ w.length := (Nat.mod_lt k h).le
    refine ⟨((w.take (k % w.length)).filter p).length, ?_⟩
    rw [← List.rotate_mod, List.rotate_eq_drop_append_take hk]
    have hsplit : w.filter p = (w.take (k % w.length)).filter p ++
        (w.drop (k % w.length)).filter p := by
      rw [← List.filter_append, List.take_append_drop]
    rw [hsplit, List.filter_append, List.rotate_append_length_eq]

theorem Adj.remove {w : W} {p q : Letter → Prop} (h : Adj w p q) {d : ℕ}
    (hp : ∀ x, p x → x.label ≠ d) (hq : ∀ y, q y → y.label ≠ d) :
    Adj (remove w d) p q := by
  obtain ⟨k, x, y, rest, hk, hx, hy⟩ := h
  obtain ⟨m, hm⟩ := filter_rotate (fun l => decide (l.label ≠ d)) w k
  refine ⟨m, x, y, rest.filter (fun l => decide (l.label ≠ d)), ?_, hx, hy⟩
  have h1 := hp x hx
  have h2 := hq y hy
  unfold FormaNormal.remove
  rw [← hm, hk]
  simp [h1, h2]

/-- Persistencia de un candidato R1: quitar otro cruce no lo destruye. -/
theorem R1cand.remove {w : W} {c d : ℕ} (h : R1cand w c) (hd : d ≠ c) :
    R1cand (remove w d) c := by
  obtain ⟨k, x, y, rest, hk, hx, hy⟩ := h
  exact Adj.remove (w := w) (p := fun x => x.label = c) (q := fun y => y.label = c)
    ⟨k, x, y, rest, hk, hx, hy⟩ (d := d) (fun x hx => by rw [hx]; exact fun e => hd e.symm)
    (fun y hy => by rw [hy]; exact fun e => hd e.symm)

theorem Linked.remove {w : W} {a b d : ℕ} (h : Linked w a b) (hda : a ≠ d) (hdb : b ≠ d) :
    Linked (remove w d) a b := by
  obtain ⟨u, x, v, y, z, rfl, hx, hy, hv, hz⟩ := h
  have hx' : x.label ≠ d := by rw [hx]; exact hda
  have hy' : y.label ≠ d := by rw [hy]; exact hda
  refine ⟨FormaNormal.remove u d, x, FormaNormal.remove v d, y, FormaNormal.remove z d, ?_,
    hx, hy, ?_, ?_⟩
  · simp [FormaNormal.remove, List.filter_append, hx', hy']
  · rw [cnt_remove hdb]; exact hv
  · have : FormaNormal.remove z d ++ FormaNormal.remove u d =
        FormaNormal.remove (z ++ u) d := by
      simp [FormaNormal.remove, List.filter_append]
    rw [this, cnt_remove hdb]; exact hz

/-- Persistencia de un par R2: quitar un cruce `d ∉ {a, b}` no lo destruye. -/
theorem R2cand.remove {w : W} {a b d : ℕ} (h : R2cand w a b) (hda : d ≠ a) (hdb : d ≠ b) :
    R2cand (remove w d) a b := by
  obtain ⟨hab, ht, hb, hi, x, hx, y, hy, hxa, hyb, hxy⟩ := h
  have ha : ∀ x : Letter, x.label = a ∧ x.up = true → x.label ≠ d :=
    fun x hx => by rw [hx.1]; exact Ne.symm hda
  have hb' : ∀ x : Letter, x.label = b ∧ x.up = true → x.label ≠ d :=
    fun x hx => by rw [hx.1]; exact Ne.symm hdb
  have ha' : ∀ x : Letter, x.label = a ∧ x.up = false → x.label ≠ d :=
    fun x hx => by rw [hx.1]; exact Ne.symm hda
  have hb'' : ∀ x : Letter, x.label = b ∧ x.up = false → x.label ≠ d :=
    fun x hx => by rw [hx.1]; exact Ne.symm hdb
  refine ⟨hab, ?_, ?_, ?_, x, mem_remove.mpr ⟨hx, by rw [hxa]; exact Ne.symm hda⟩,
    y, mem_remove.mpr ⟨hy, by rw [hyb]; exact Ne.symm hdb⟩, hxa, hyb, hxy⟩
  · rcases ht with h | h
    · exact Or.inl (h.remove ha hb')
    · exact Or.inr (h.remove hb' ha)
  · rcases hb with h | h
    · exact Or.inl (h.remove ha' hb'')
    · exact Or.inr (h.remove hb'' ha')
  · rcases hi with h | h
    · exact Or.inl (h.remove (Ne.symm hda) (Ne.symm hdb))
    · exact Or.inr (h.remove (Ne.symm hdb) (Ne.symm hda))

/-! ### Invariancia por rotación del entrelazado -/

theorem cnt_append (c : ℕ) (l l' : W) : cnt c (l ++ l') = cnt c l + cnt c l' :=
  by simp [cnt, List.countP_append]

theorem cnt_cons (c : ℕ) (x : Letter) (l : W) :
    cnt c (x :: l) = (if x.label = c then 1 else 0) + cnt c l := by
  simp [cnt, List.countP_cons, Nat.add_comm]

theorem rotate_one_cons (a : Letter) (l : W) : (a :: l).rotate 1 = l ++ [a] := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]

theorem Linked.rotate_one {w : W} {a b : ℕ} (h : Linked w a b) : Linked (w.rotate 1) a b := by
  obtain ⟨u, x, v, y, z, rfl, hx, hy, hv, hz⟩ := h
  cases u with
  | nil =>
    rw [List.nil_append, rotate_one_cons]
    refine ⟨v, y, z, x, [], by simp, hy, hx, ?_, ?_⟩
    · simpa using hz
    · simpa using hv
  | cons x0 u' =>
    rw [List.cons_append, rotate_one_cons]
    refine ⟨u', x, v, y, z ++ [x0], by simp, hx, hy, hv, ?_⟩
    have : z ++ [x0] ++ u' = z ++ (x0 :: u') := by simp
    rw [this]; simpa using hz

theorem Linked.rotate {w : W} {a b : ℕ} (h : Linked w a b) (k : ℕ) :
    Linked (w.rotate k) a b := by
  induction k generalizing w with
  | zero => simpa using h
  | succ k ih =>
    have := ih h.rotate_one
    rwa [List.rotate_rotate, Nat.add_comm] at this

/-! ### (c) Un candidato R1 no pertenece a un par R2 -/

theorem r1_not_linked_fst {w : W} {a b : ℕ} (hw : Wf w) (h : R1cand w a) : ¬ Linked w a b := by
  intro hl
  obtain ⟨k, x, y, rest, hk, hx, hy⟩ := h
  have hl' := hl.rotate k
  have hw' := wf_rotate hw k
  rw [hk] at hl' hw'
  have hc := wf_cnt_le hw' a
  obtain ⟨u, x', v, y', z, heq, hx', hy', hv, hz⟩ := hl'
  rw [heq] at hc
  simp only [cnt_append, cnt_cons, hx', hy', if_true] at hc
  have hu0 : cnt a u = 0 := by omega
  have hv0 : cnt a v = 0 := by omega
  cases u with
  | nil =>
    rw [List.nil_append] at heq
    cases v with
    | nil => simp [cnt] at hv
    | cons h v' =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨-, hyh, -⟩ := heq
      subst hyh
      simp only [cnt_cons, hy, if_true] at hv0
      omega
  | cons h u' =>
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨hxh, -⟩ := heq
    subst hxh
    simp only [cnt_cons, hx, if_true] at hu0
    omega

theorem r1_not_linked_snd {w : W} {a b : ℕ} (hab : a ≠ b) (h : R1cand w b) :
    ¬ Linked w a b := by
  intro hl
  obtain ⟨k, x, y, rest, hk, hx, hy⟩ := h
  have hl' := hl.rotate k
  rw [hk] at hl'
  obtain ⟨u, x', v, y', z, heq, hx', hy', hv, hz⟩ := hl'
  cases u with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at heq
    obtain ⟨hxx, -⟩ := heq
    subst hxx
    exact hab (hx'.symm.trans hx)
  | cons h u' =>
    cases u' with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨hxh, hyx, -⟩ := heq
      subst hxh hyx
      exact hab (hx'.symm.trans hy)
    | cons h2 u'' =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨hxh, hyh, -⟩ := heq
      subst hxh hyh
      simp only [cnt_append, cnt_cons, hx, hy, if_true] at hz
      omega

/-- Un candidato R1 no pertenece a ningún par candidato R2. -/
theorem R1cand_not_R2 {w : W} {a b : ℕ} (hw : Wf w) (h2 : R2cand w a b) :
    ¬ R1cand w a ∧ ¬ R1cand w b := by
  obtain ⟨hab, -, -, hi, -⟩ := h2
  constructor
  · intro h1
    rcases hi with hl | hl
    · exact r1_not_linked_fst hw h1 hl
    · exact r1_not_linked_snd (Ne.symm hab) h1 hl
  · intro h1
    rcases hi with hl | hl
    · exact r1_not_linked_snd hab h1 hl
    · exact r1_not_linked_fst hw h1 hl

/-! ## 6. `≈` conserva la buena formación; ejemplos de cordura -/

theorem labelSet_rotate (w : W) (k : ℕ) : labelSet (w.rotate k) = labelSet w := by
  ext c
  simp [labelSet, List.mem_rotate]

/-- `≈` conserva la buena formación. -/
theorem wf_equiv {w w' : W} (hw : Wf w) (h : Equiv w w') : Wf w' := by
  obtain ⟨k, f, hinj, rfl⟩ := h
  have hX := wf_rotate hw k
  intro c'
  by_cases hc : ∃ c ∈ labelSet w, f c = c'
  · obtain ⟨c, hcw, rfl⟩ := hc
    have key : ((w.rotate k).map (relabel f)).filter (fun l => l.label = f c) =
        ((w.rotate k).filter (fun l => l.label = c)).map (relabel f) := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro l hl
      have hlw : l.label ∈ labelSet w := by
        rw [← labelSet_rotate w k]
        exact List.mem_map.mpr ⟨l, hl, rfl⟩
      simp only [Function.comp, relabel, decide_eq_decide]
      exact ⟨fun e => hinj hlw hcw e, fun e => by rw [e]⟩
    rw [key]
    rcases hX c with h | ⟨s, hs⟩
    · left; rw [h]; rfl
    · right
      exact ⟨s, hs.map (relabel f)⟩
  · left
    rw [List.filter_eq_nil_iff]
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
    intro hlab
    apply hc
    refine ⟨l0.label, ?_, by simpa [relabel] using hlab⟩
    rw [← labelSet_rotate w k]
    exact List.mem_map.mpr ⟨l0, hl0, rfl⟩

/-- Sanidad: un rizo (R1) en una palabra de un solo cruce. -/
example : Red [⟨0, true, false⟩, ⟨0, false, false⟩] [] := by
  left
  refine ⟨0, ⟨0, ⟨0, true, false⟩, ⟨0, false, false⟩, [], rfl, rfl, rfl⟩, ?_⟩
  decide

/-- Sanidad: el envolvimiento último-primero también cuenta como consecutivo (R1). -/
example : R1cand [⟨0, true, false⟩, ⟨1, true, true⟩, ⟨1, false, true⟩, ⟨0, false, false⟩] 0 :=
  ⟨3, ⟨0, false, false⟩, ⟨0, true, false⟩, [⟨1, true, true⟩, ⟨1, false, true⟩], by decide,
    rfl, rfl⟩

/-- Sanidad: un par R2 canónico en una palabra de dos cruces se reduce al diagrama vacío. -/
example : Red [⟨0, true, false⟩, ⟨1, true, true⟩, ⟨0, false, false⟩, ⟨1, false, true⟩] [] := by
  right
  refine ⟨0, 1, ⟨by decide, ?_, ?_, ?_, ?_⟩, by decide⟩
  · exact Or.inl ⟨0, ⟨0, true, false⟩, ⟨1, true, true⟩, [⟨0, false, false⟩, ⟨1, false, true⟩],
      by decide, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · exact Or.inl ⟨2, ⟨0, false, false⟩, ⟨1, false, true⟩, [⟨0, true, false⟩, ⟨1, true, true⟩],
      by decide, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · exact Or.inl ⟨[], ⟨0, true, false⟩, [⟨1, true, true⟩], ⟨0, false, false⟩, [⟨1, false, true⟩],
      by decide, rfl, rfl, by decide, by decide⟩
  · exact ⟨⟨0, true, false⟩, by decide, ⟨1, true, true⟩, by decide, rfl, rfl, by decide⟩

end FormaNormal
