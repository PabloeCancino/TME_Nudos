import Mathlib

/-!
# Forma normal única para la reducción R1/R2 (Etapas 1 a 3)

Modelo de palabras de Gauss con signos (listas cíclicas), movimientos R1/R2, equivalencia
(rotación más reetiquetado), lema de Newman módulo una equivalencia (abstracto) e infraestructura
geométrica simple (conmutación y persistencia de candidatos).
Etapa 2: compatibilidad de `Red` con `Equiv` (`red_compat_equiv`) y el solapamiento de dos pares
R2 con un cruce común (`overlap_mid`, `r2_overlap`).
Etapa 3: confluencia local (`red_local`), forma normal única (`normal_form_unique_words`) y los
corolarios fieles de A6 y A7 (`a6_irreducible_min`, `a7_min_equiv`) sobre la clase
`Cls` = cerradura de equivalencia de `Red ∪ Red⁻¹ ∪ Equiv` en palabras bien formadas.
Es la clasificación de DIAGRAMAS módulo R1/R2 y rotación, no de nudos.
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

/-! ## 7. Compatibilidad de `Red` con `≈` (hipótesis (b) de Newman) -/

/-! ### (a) Invariancia por rotación -/

theorem rotate_rotate_exists (w : W) (k j : ℕ) : ∃ m, (w.rotate k).rotate m = w.rotate j := by
  obtain ⟨i, hi⟩ := rotate_inv w k
  refine ⟨i + j, ?_⟩
  rw [← List.rotate_rotate, hi]

theorem Adj.rotate {w : W} {p q : Letter → Prop} (h : Adj w p q) (k : ℕ) :
    Adj (w.rotate k) p q := by
  obtain ⟨j, x, y, rest, hj, hx, hy⟩ := h
  obtain ⟨m, hm⟩ := rotate_rotate_exists w k j
  exact ⟨m, x, y, rest, by rw [hm, hj], hx, hy⟩

theorem R1cand.rotate {w : W} {c : ℕ} (h : R1cand w c) (k : ℕ) : R1cand (w.rotate k) c :=
  Adj.rotate (p := fun x => x.label = c) (q := fun y => y.label = c) h k

theorem AdjSide.rotate {w : W} {s : Bool} {a b : ℕ} (h : AdjSide w s a b) (k : ℕ) :
    AdjSide (w.rotate k) s a b := by
  rcases h with h | h
  · exact Or.inl (h.rotate k)
  · exact Or.inr (h.rotate k)

theorem OppSign.rotate {w : W} {a b : ℕ} (h : OppSign w a b) (k : ℕ) :
    OppSign (w.rotate k) a b := by
  obtain ⟨x, hx, y, hy, hxa, hyb, hne⟩ := h
  exact ⟨x, List.mem_rotate.mpr hx, y, List.mem_rotate.mpr hy, hxa, hyb, hne⟩

theorem Interlaced.rotate {w : W} {a b : ℕ} (h : Interlaced w a b) (k : ℕ) :
    Interlaced (w.rotate k) a b := by
  rcases h with h | h
  · exact Or.inl (h.rotate k)
  · exact Or.inr (h.rotate k)

theorem R2cand.rotate {w : W} {a b : ℕ} (h : R2cand w a b) (k : ℕ) :
    R2cand (w.rotate k) a b := by
  obtain ⟨hab, h1, h2, h3, h4⟩ := h
  exact ⟨hab, h1.rotate k, h2.rotate k, h3.rotate k, h4.rotate k⟩

theorem remove_rotate (w : W) (c k : ℕ) : ∃ m, remove (w.rotate k) c = (remove w c).rotate m :=
  filter_rotate (fun l => decide (l.label ≠ c)) w k

theorem remove2_rotate (w : W) (a b k : ℕ) :
    ∃ m, remove2 (w.rotate k) a b = (remove2 w a b).rotate m := by
  obtain ⟨m1, h1⟩ := remove_rotate w a k
  obtain ⟨m2, h2⟩ := remove_rotate (remove w a) b m1
  exact ⟨m2, by unfold remove2; rw [h1, h2]⟩

/-- Rotar conserva `Red` (rotando también el resultado). -/
theorem Red.rotate {w x : W} (h : Red w x) (k : ℕ) : ∃ m, Red (w.rotate k) (x.rotate m) := by
  rcases h with ⟨c, hc, rfl⟩ | ⟨a, b, hab, rfl⟩
  · obtain ⟨m, hm⟩ := remove_rotate w c k
    exact ⟨m, Or.inl ⟨c, hc.rotate k, hm.symm⟩⟩
  · obtain ⟨m, hm⟩ := remove2_rotate w a b k
    exact ⟨m, Or.inr ⟨a, b, hab.rotate k, hm.symm⟩⟩

/-! ### (b) Renombrado inyectivo -/

theorem mem_labelSet_of_mem {w : W} {l : Letter} (h : l ∈ w) : l.label ∈ labelSet w :=
  List.mem_map.mpr ⟨l, h, rfl⟩

theorem labelSet_remove_subset (w : W) (c : ℕ) : labelSet (remove w c) ⊆ labelSet w := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  exact mem_labelSet_of_mem (mem_remove.mp hl).1

theorem labelSet_remove2_subset (w : W) (a b : ℕ) : labelSet (remove2 w a b) ⊆ labelSet w :=
  (labelSet_remove_subset _ _).trans (labelSet_remove_subset _ _)

theorem Red.labelSet_subset {w x : W} (h : Red w x) : labelSet x ⊆ labelSet w := by
  rcases h with ⟨c, -, rfl⟩ | ⟨a, b, -, rfl⟩
  · exact labelSet_remove_subset w c
  · exact labelSet_remove2_subset w a b

theorem remove_map_relabel {w : W} {f : ℕ → ℕ} (hf : Set.InjOn f (labelSet w)) {c : ℕ}
    (hc : c ∈ labelSet w) : remove (w.map (relabel f)) (f c) = (remove w c).map (relabel f) := by
  unfold remove
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro l hl
  have hlw := mem_labelSet_of_mem hl
  simp only [Function.comp, relabel, decide_eq_decide, ne_eq]
  exact not_congr ⟨fun e => hf hlw hc e, fun e => by rw [e]⟩

theorem remove2_map_relabel {w : W} {f : ℕ → ℕ} (hf : Set.InjOn f (labelSet w)) {a b : ℕ}
    (ha : a ∈ labelSet w) (hb : b ∈ labelSet w) (hab : a ≠ b) :
    remove2 (w.map (relabel f)) (f a) (f b) = (remove2 w a b).map (relabel f) := by
  unfold remove2
  rw [remove_map_relabel hf ha]
  have hb' : b ∈ labelSet (remove w a) := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hb
    exact mem_labelSet_of_mem (mem_remove.mpr ⟨hl, fun e => hab e.symm⟩)
  exact remove_map_relabel (hf.mono (labelSet_remove_subset w a)) hb'

theorem R1cand.relabelled {w : W} {c : ℕ} (h : R1cand w c) (f : ℕ → ℕ) :
    R1cand (w.map (relabel f)) (f c) := by
  obtain ⟨k, x, y, rest, hk, hx, hy⟩ := h
  refine ⟨k, relabel f x, relabel f y, rest.map (relabel f), ?_, by simp [relabel, hx],
    by simp [relabel, hy]⟩
  rw [← List.map_rotate, hk]
  rfl

theorem Adj.map {w : W} {p q p' q' : Letter → Prop} (φ : Letter → Letter) (h : Adj w p q)
    (hp : ∀ x, p x → p' (φ x)) (hq : ∀ y, q y → q' (φ y)) : Adj (w.map φ) p' q' := by
  obtain ⟨k, x, y, rest, hk, hx, hy⟩ := h
  refine ⟨k, φ x, φ y, rest.map φ, ?_, hp x hx, hq y hy⟩
  rw [← List.map_rotate, hk]
  rfl

theorem AdjSide.relabelled {w : W} {s : Bool} {a b : ℕ} (h : AdjSide w s a b) (f : ℕ → ℕ) :
    AdjSide (w.map (relabel f)) s (f a) (f b) := by
  rcases h with h | h
  · exact Or.inl (h.map (relabel f) (fun x hx => by simp [relabel, hx.1, hx.2])
      (fun x hx => by simp [relabel, hx.1, hx.2]))
  · exact Or.inr (h.map (relabel f) (fun x hx => by simp [relabel, hx.1, hx.2])
      (fun x hx => by simp [relabel, hx.1, hx.2]))

theorem cnt_pos_mem {v : W} {b : ℕ} (h : 0 < cnt b v) : b ∈ labelSet v := by
  obtain ⟨l, hl, hlb⟩ := List.countP_pos_iff.mp h
  have : l.label = b := by simpa using hlb
  rw [← this]
  exact mem_labelSet_of_mem hl

theorem cnt_map_relabel {f : ℕ → ℕ} {S : Set ℕ} (hf : Set.InjOn f S) {v : W} {b : ℕ}
    (hv : ∀ l ∈ v, l.label ∈ S) (hb : b ∈ S) :
    cnt (f b) (v.map (relabel f)) = cnt b v := by
  unfold cnt
  rw [List.countP_map]
  apply List.countP_congr
  intro l hl
  simp only [Function.comp, relabel, decide_eq_true_eq]
  exact ⟨fun e => hf (hv l hl) hb e, fun e => by rw [e]⟩

theorem Linked.relabelled {w : W} {a b : ℕ} (h : Linked w a b) {f : ℕ → ℕ}
    (hf : Set.InjOn f (labelSet w)) : Linked (w.map (relabel f)) (f a) (f b) := by
  obtain ⟨u, x, v, y, z, hw, hx, hy, hv, hz⟩ := h
  have hb : b ∈ labelSet w := by
    have : b ∈ labelSet v := cnt_pos_mem (by omega)
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp this
    exact mem_labelSet_of_mem (by rw [hw]; simp [hl])
  refine ⟨u.map (relabel f), relabel f x, v.map (relabel f), relabel f y, z.map (relabel f),
    by rw [hw]; simp, by simp [relabel, hx], by simp [relabel, hy], ?_, ?_⟩
  · rw [cnt_map_relabel hf (fun l hl => mem_labelSet_of_mem (by rw [hw]; simp [hl])) hb]
    exact hv
  · rw [← List.map_append, cnt_map_relabel hf
      (fun l hl => mem_labelSet_of_mem (by rw [hw]; simp at hl ⊢; tauto)) hb]
    exact hz

theorem Interlaced.relabelled {w : W} {a b : ℕ} (h : Interlaced w a b) {f : ℕ → ℕ}
    (hf : Set.InjOn f (labelSet w)) : Interlaced (w.map (relabel f)) (f a) (f b) := by
  rcases h with h | h
  · exact Or.inl (h.relabelled hf)
  · exact Or.inr (h.relabelled hf)

theorem OppSign.relabelled {w : W} {a b : ℕ} (h : OppSign w a b) (f : ℕ → ℕ) :
    OppSign (w.map (relabel f)) (f a) (f b) := by
  obtain ⟨x, hx, y, hy, hxa, hyb, hne⟩ := h
  exact ⟨relabel f x, List.mem_map.mpr ⟨x, hx, rfl⟩, relabel f y, List.mem_map.mpr ⟨y, hy, rfl⟩,
    by simp [relabel, hxa], by simp [relabel, hyb], hne⟩

theorem R2cand.relabelled {w : W} {a b : ℕ} (h : R2cand w a b) {f : ℕ → ℕ}
    (hf : Set.InjOn f (labelSet w)) : R2cand (w.map (relabel f)) (f a) (f b) := by
  have hm := h.mem
  obtain ⟨hab, h1, h2, h3, h4⟩ := h
  exact ⟨fun e => hab (hf hm.1 hm.2 e), h1.relabelled f, h2.relabelled f, h3.relabelled hf,
    h4.relabelled f⟩

/-- Un renombrado inyectivo (sobre las etiquetas de `w`) conserva `Red`. -/
theorem Red.relabelled {w x : W} {f : ℕ → ℕ} (hf : Set.InjOn f (labelSet w)) (h : Red w x) :
    Red (w.map (relabel f)) (x.map (relabel f)) := by
  rcases h with ⟨c, hc, rfl⟩ | ⟨a, b, hab, rfl⟩
  · exact Or.inl ⟨f c, hc.relabelled f, (remove_map_relabel hf hc.mem).symm⟩
  · refine Or.inr ⟨f a, f b, hab.relabelled hf, ?_⟩
    exact (remove2_map_relabel hf hab.mem.1 hab.mem.2 hab.1).symm

/-- **Hipótesis (b) de Newman**: `Red` es compatible con `≈`. -/
theorem red_compat_equiv {w w' x : W} (he : Equiv w w') (h : Red w x) :
    ∃ x', Red w' x' ∧ Equiv x x' := by
  obtain ⟨k, f, hinj, rfl⟩ := he
  obtain ⟨m, hr⟩ := h.rotate k
  have hinj' : Set.InjOn f (labelSet (w.rotate k)) := by rwa [labelSet_rotate]
  exact ⟨_, hr.relabelled hinj', ⟨m, f, hinj.mono h.labelSet_subset, rfl⟩⟩

/-! ## 8. El solapamiento de dos pares R2 -/

/-! ### (a) Hechos sobre palabras bien formadas -/

theorem Wf.letter_unique {w : W} (hw : Wf w) {x y : Letter} (hx : x ∈ w) (hy : y ∈ w)
    (hl : x.label = y.label) (hu : x.up = y.up) : x = y := by
  have hx' : x ∈ w.filter (fun l => l.label = x.label) := List.mem_filter.mpr ⟨hx, by simp⟩
  have hy' : y ∈ w.filter (fun l => l.label = x.label) := List.mem_filter.mpr ⟨hy, by simp [hl]⟩
  rcases hw x.label with h | ⟨s, hs⟩
  · rw [h] at hx'
    simp at hx'
  · have hx2 := hs.subset hx'
    have hy2 := hs.subset hy'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2 hy2
    rcases x with ⟨lx, ux, px⟩
    rcases y with ⟨ly, uy, py⟩
    simp only at hl hu
    subst hl hu
    rcases hx2 with h1 | h1 <;> rcases hy2 with h2 | h2 <;> simp_all

theorem Wf.pos_eq {w : W} (hw : Wf w) {x y : Letter} (hx : x ∈ w) (hy : y ∈ w)
    (hl : x.label = y.label) : x.pos = y.pos := by
  have hx' : x ∈ w.filter (fun l => l.label = x.label) := List.mem_filter.mpr ⟨hx, by simp⟩
  have hy' : y ∈ w.filter (fun l => l.label = x.label) := List.mem_filter.mpr ⟨hy, by simp [hl]⟩
  rcases hw x.label with h | ⟨s, hs⟩
  · rw [h] at hx'
    simp at hx'
  · have hx2 := hs.subset hx'
    have hy2 := hs.subset hy'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx2 hy2
    have px : x.pos = s := by rcases hx2 with h | h <;> exact congrArg Letter.pos h
    have py : y.pos = s := by rcases hy2 with h | h <;> exact congrArg Letter.pos h
    exact px.trans py.symm

theorem Wf.nodup {w : W} (hw : Wf w) : w.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro l
  have h1 : (w.filter (fun x => x.label = l.label)).count l = w.count l :=
    List.count_filter (by simp)
  rcases hw l.label with h | ⟨s, hs⟩
  · rw [h] at h1
    simp at h1
    omega
  · rw [← h1, hs.count_eq]
    have hnd : ([⟨l.label, true, s⟩, ⟨l.label, false, s⟩] : List Letter).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
      intro hh
      have := congrArg Letter.up (List.mem_singleton.mp hh)
      simp at this
    exact List.nodup_iff_count_le_one.mp hnd l

/-! ### (b) Adyacencia cíclica y tercias -/

/-- `x y` son cíclicamente consecutivas (en ese orden) en `w`. -/
def Cons2 (w : W) (x y : Letter) : Prop := ∃ (k : ℕ) (rest : W), w.rotate k = x :: y :: rest

/-- `x y z` son cíclicamente consecutivas (en ese orden) en `w`. -/
def Tri (w : W) (x y z : Letter) : Prop :=
  ∃ (k : ℕ) (rest : W), w.rotate k = x :: y :: z :: rest

theorem rotate_head_unique {w : W} (hn : w.Nodup) {j k : ℕ} {x : Letter} {s s' : W}
    (hj : w.rotate j = x :: s) (hk : w.rotate k = x :: s') : s = s' := by
  have hlen : 0 < w.length := by
    have := congrArg List.length hj
    rw [List.length_rotate] at this
    simp at this
    omega
  have h1 : (w.rotate j)[0]'(by simp [hj]) = x := by simp [hj]
  have h2 : (w.rotate k)[0]'(by simp [hk]) = x := by simp [hk]
  rw [List.getElem_rotate] at h1 h2
  have h3 : w[(0 + j) % w.length]'(Nat.mod_lt _ hlen) =
      w[(0 + k) % w.length]'(Nat.mod_lt _ hlen) := h1.trans h2.symm
  have h4 := (hn.getElem_inj_iff).mp h3
  have h5 : w.rotate j = w.rotate k := by
    have h6 : j % w.length = k % w.length := by simpa using h4
    rw [← List.rotate_mod w j, ← List.rotate_mod w k, h6]
  rw [h5] at hj
  rw [hj] at hk
  exact (List.cons.inj hk).2

theorem rotate_succ_two {w : W} {k : ℕ} {x y : Letter} {r : W} (h : w.rotate k = x :: y :: r) :
    w.rotate (k + 1) = y :: (r ++ [x]) := by
  rw [← List.rotate_rotate, h, rotate_one_cons]
  rfl

theorem Cons2.rotate {w : W} {x y : Letter} (h : Cons2 w x y) (j : ℕ) : Cons2 (w.rotate j) x y := by
  obtain ⟨k, r, hk⟩ := h
  obtain ⟨m, hm⟩ := rotate_rotate_exists w j k
  exact ⟨m, r, by rw [hm, hk]⟩

theorem tri_of_cons {w : W} (hn : w.Nodup) {x y z : Letter} (h1 : Cons2 w x y) (h2 : Cons2 w y z)
    (hne : x ≠ z) : Tri w x y z := by
  obtain ⟨k, r, hk⟩ := h1
  obtain ⟨j, r', hj⟩ := h2
  have h3 := rotate_succ_two hk
  have h4 := rotate_head_unique hn h3 hj
  cases r with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h4
    exact absurd h4.1 hne
  | cons h t =>
    simp only [List.cons_append, List.cons.injEq] at h4
    rw [h4.1] at hk
    exact ⟨k, t, hk⟩

theorem face_tri {w : W} (hn : w.Nodup) {xa xb xc : Letter}
    (hab : Cons2 w xa xb ∨ Cons2 w xb xa) (hbc : Cons2 w xb xc ∨ Cons2 w xc xb)
    (hac : xa ≠ xc) : Tri w xa xb xc ∨ Tri w xc xb xa := by
  rcases hab with h1 | h1 <;> rcases hbc with h2 | h2
  · exact Or.inl (tri_of_cons hn h1 h2 hac)
  · exfalso
    obtain ⟨k, r, hk⟩ := h1
    obtain ⟨j, r', hj⟩ := h2
    have h3 := rotate_succ_two hk
    have h4 := rotate_succ_two hj
    have h5 := rotate_head_unique hn h3 h4
    have h6 := (List.append_inj' h5 rfl).2
    exact hac (List.cons.inj h6).1
  · exfalso
    obtain ⟨k, r, hk⟩ := h1
    obtain ⟨j, r', hj⟩ := h2
    have h5 := rotate_head_unique hn hk hj
    exact hac (List.cons.inj h5).1
  · exact Or.inr (tri_of_cons hn h2 h1 (Ne.symm hac))

theorem tri_tri {w : W} (hn : w.Nodup) {x1 x2 x3 y1 y2 y3 : Letter}
    (hx : Tri w x1 x2 x3) (hy : Tri w y1 y2 y3)
    (h1 : y1 ≠ x1) (h2 : y1 ≠ x2) (h3 : y1 ≠ x3) (g2 : y2 ≠ x1) (g3 : y3 ≠ x1) :
    ∃ (k : ℕ) (Y Z : W), w.rotate k = x1 :: x2 :: x3 :: (Y ++ y1 :: y2 :: y3 :: Z) := by
  obtain ⟨k, r, hk⟩ := hx
  obtain ⟨j, r2, hj⟩ := hy
  have hy1 : y1 ∈ r := by
    have h0 : y1 ∈ w.rotate j := by rw [hj]; exact List.mem_cons_self
    have h0' : y1 ∈ w.rotate k := List.mem_rotate.mpr (List.mem_rotate.mp h0)
    rw [hk] at h0'
    simp only [List.mem_cons] at h0'
    rcases h0' with h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact h
  obtain ⟨A, B, hr⟩ := List.mem_iff_append.mp hy1
  have hrot : w.rotate (k + (x1 :: x2 :: x3 :: A).length) =
      y1 :: (B ++ (x1 :: x2 :: x3 :: A)) := by
    rw [← List.rotate_rotate, hk, hr]
    have : x1 :: x2 :: x3 :: (A ++ y1 :: B) = (x1 :: x2 :: x3 :: A) ++ (y1 :: B) := by simp
    rw [this, List.rotate_append_length_eq]
    rfl
  have h5 := rotate_head_unique hn hj hrot
  rcases B with _ | ⟨b1, _ | ⟨b2, B'⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at h5
    exact absurd h5.1 g2
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h5
    exact absurd h5.2.1 g3
  · simp only [List.cons_append, List.cons.injEq] at h5
    obtain ⟨rfl, rfl, -⟩ := h5
    exact ⟨k, A, B', by rw [hk, hr]⟩

theorem Adj.cons2 {w : W} {p q : Letter → Prop} (h : Adj w p q) :
    ∃ x y, x ∈ w ∧ y ∈ w ∧ p x ∧ q y ∧ Cons2 w x y := by
  obtain ⟨k, x, y, rest, hk, hx, hy⟩ := h
  have hx' : x ∈ w := List.mem_rotate.mp (by rw [hk]; simp)
  have hy' : y ∈ w := List.mem_rotate.mp (by rw [hk]; simp)
  exact ⟨x, y, hx', hy', hx, hy, k, rest, hk⟩

theorem AdjSide.letters {w : W} {s : Bool} {a b : ℕ} (h : AdjSide w s a b) :
    ∃ x y : Letter, x ∈ w ∧ y ∈ w ∧ x.label = a ∧ x.up = s ∧ y.label = b ∧ y.up = s ∧
      (Cons2 w x y ∨ Cons2 w y x) := by
  rcases h with h | h
  · obtain ⟨x, y, hx, hy, ⟨hxa, hxs⟩, ⟨hyb, hys⟩, hc⟩ := h.cons2
    exact ⟨x, y, hx, hy, hxa, hxs, hyb, hys, Or.inl hc⟩
  · obtain ⟨y, x, hy, hx, ⟨hyb, hys⟩, ⟨hxa, hxs⟩, hc⟩ := h.cons2
    exact ⟨x, y, hx, hy, hxa, hxs, hyb, hys, Or.inr hc⟩

theorem side_tri {w : W} (hw : Wf w) {s : Bool} {a b c : ℕ} (hab : AdjSide w s a b)
    (hbc : AdjSide w s b c) (hac : a ≠ c) :
    ∃ xa xb xc : Letter, xa ∈ w ∧ xb ∈ w ∧ xc ∈ w ∧ xa.label = a ∧ xa.up = s ∧
      xb.label = b ∧ xb.up = s ∧ xc.label = c ∧ xc.up = s ∧
      (Tri w xa xb xc ∨ Tri w xc xb xa) := by
  obtain ⟨xa, xb, hxa, hxb, hla, hua, hlb, hub, hc1⟩ := hab.letters
  obtain ⟨xb', xc, hxb', hxc, hlb', hub', hlc, huc, hc2⟩ := hbc.letters
  have : xb' = xb := hw.letter_unique hxb' hxb (by rw [hlb, hlb']) (by rw [hub, hub'])
  rw [this] at hc2
  exact ⟨xa, xb, xc, hxa, hxb, hxc, hla, hua, hlb, hub, hlc, huc,
    face_tri hw.nodup hc1 hc2 (fun h => hac (by rw [← hla, ← hlc, h]))⟩

/-! ### (c) Simetrías -/

theorem AdjSide.symm {w : W} {s : Bool} {a b : ℕ} (h : AdjSide w s a b) : AdjSide w s b a := by
  unfold AdjSide at h ⊢
  exact h.symm

theorem Interlaced.symm {w : W} {a b : ℕ} (h : Interlaced w a b) : Interlaced w b a :=
  Or.symm h

theorem OppSign.symm {w : W} {a b : ℕ} (h : OppSign w a b) : OppSign w b a := by
  obtain ⟨x, hx, y, hy, hxa, hyb, hne⟩ := h
  exact ⟨y, hy, x, hx, hyb, hxa, Ne.symm hne⟩

theorem R2cand.symm {w : W} {a b : ℕ} (h : R2cand w a b) : R2cand w b a :=
  ⟨Ne.symm h.1, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

/-! ### (d) Arcos del entrelazado -/

theorem cnt_nil (c : ℕ) : cnt c ([] : W) = 0 := rfl

theorem afree {L : W} (hL : Wf L) {a : ℕ} {P V Q : W} {x y : Letter}
    (hL' : L = P ++ x :: (V ++ y :: Q)) (hx : x.label = a) (hy : y.label = a) :
    cnt a P = 0 ∧ cnt a V = 0 ∧ cnt a Q = 0 := by
  have hc := wf_cnt_le hL a
  rw [hL'] at hc
  simp only [cnt_append, cnt_cons, hx, hy, if_true] at hc
  omega

theorem split_first {a : ℕ} {u u' R R' : W} {x x' : Letter} (hu : cnt a u = 0)
    (hu' : cnt a u' = 0) (hx : x.label = a) (hx' : x'.label = a)
    (h : u ++ x :: R = u' ++ x' :: R') : u = u' ∧ x = x' ∧ R = R' := by
  induction u generalizing u' with
  | nil =>
    cases u' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact ⟨rfl, h.1, h.2⟩
    | cons h0 t =>
      exfalso
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have h1 : h0.label = a := by rw [← h.1]; exact hx
      simp only [cnt_cons, h1, if_true] at hu'
      omega
  | cons h0 t ih =>
    cases u' with
    | nil =>
      exfalso
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have h1 : h0.label = a := by rw [h.1]; exact hx'
      simp only [cnt_cons, h1, if_true] at hu
      omega
    | cons h1 t' =>
      simp only [List.cons_append, List.cons.injEq] at h
      have hu2 : cnt a t = 0 := by simp only [cnt_cons] at hu; omega
      have hu2' : cnt a t' = 0 := by simp only [cnt_cons] at hu'; omega
      obtain ⟨e1, e2, e3⟩ := ih hu2 hu2' h.2
      exact ⟨by rw [h.1, e1], e2, e3⟩

theorem Linked.cnt_arc {L : W} (hL : Wf L) {a b : ℕ} (h : Linked L a b) {P V Q : W}
    {x y : Letter} (hL' : L = P ++ x :: (V ++ y :: Q)) (hx : x.label = a) (hy : y.label = a) :
    cnt b V = 1 := by
  obtain ⟨u, x', v, y', z, hw, hx', hy', hv, hz⟩ := h
  obtain ⟨hP, hV, hQ⟩ := afree hL hL' hx hy
  obtain ⟨hu, hv0, hz0⟩ := afree hL hw hx' hy'
  have e : P ++ x :: (V ++ y :: Q) = u ++ x' :: (v ++ y' :: z) := hL'.symm.trans hw
  obtain ⟨h1, h2, h3⟩ := split_first hP hu hx hx' e
  obtain ⟨h4, h5, h6⟩ := split_first hV hv0 hy hy' h3
  rw [h4]
  exact hv

/-- La configuración anidada (`a b c … c b a`) no es entrelazada. -/
theorem nested_false {L : W} (hL : Wf L) {p1 p2 p3 q1 q2 q3 : Letter} {Y Z : W} {α β : ℕ}
    (hL' : L = p1 :: p2 :: p3 :: (Y ++ q3 :: q2 :: q1 :: Z))
    (h1 : p1.label = α) (h1' : q1.label = α) (h2 : p2.label = β) (h2' : q2.label = β)
    (hi : Interlaced L α β) : False := by
  have e1 : L = [] ++ p1 :: ((p2 :: p3 :: (Y ++ [q3, q2])) ++ q1 :: Z) := by rw [hL']; simp
  obtain ⟨-, hV, -⟩ := afree hL e1 h1 h1'
  rcases hi with hl | hl
  · have := hl.cnt_arc hL e1 h1 h1'
    simp only [cnt_append, cnt_cons, cnt_nil, h2, h2', if_true] at this
    omega
  · have e2 : L = [p1] ++ p2 :: ((p3 :: (Y ++ [q3])) ++ q2 :: (q1 :: Z)) := by
      rw [hL']; simp
    have := hl.cnt_arc hL e2 h2 h2'
    simp only [cnt_append, cnt_cons, cnt_nil] at this hV
    omega

/-! ### (e) El caso bueno: tercias paralelas -/

theorem remove_cons_eq {x : Letter} {l : W} {c : ℕ} (h : x.label = c) :
    remove (x :: l) c = remove l c := by
  simp [remove, h]

theorem remove_cons_ne {x : Letter} {l : W} {c : ℕ} (h : x.label ≠ c) :
    remove (x :: l) c = x :: remove l c := by
  simp [remove, h]

theorem remove_append (l l' : W) (c : ℕ) : remove (l ++ l') c = remove l c ++ remove l' c :=
  List.filter_append _ _

theorem remove_of_free {l : W} {c : ℕ} (h : cnt c l = 0) : remove l c = l := by
  unfold remove
  rw [List.filter_eq_self]
  intro a ha
  have := List.countP_eq_zero.mp h a ha
  simpa using this

theorem remove2_label_ne {w : W} {a b : ℕ} {l : Letter} (h : l ∈ remove2 w a b) :
    l.label ≠ a ∧ l.label ≠ b := by
  unfold remove2 at h
  obtain ⟨h1, h2⟩ := mem_remove.mp h
  exact ⟨(mem_remove.mp h1).2, h2⟩

theorem equiv_rotate (x : W) (m : ℕ) : Equiv x (x.rotate m) :=
  ⟨m, id, Set.injOn_id _, map_relabel_self (w := x.rotate m) (f := id) (fun _ _ => rfl)⟩

theorem equiv_remove2_rotate (w : W) (a b k : ℕ) :
    Equiv (remove2 w a b) (remove2 (w.rotate k) a b) := by
  obtain ⟨m, hm⟩ := remove2_rotate w a b k
  rw [hm]
  exact equiv_rotate _ m

theorem relabel_eq_of {f : ℕ → ℕ} {x y : Letter} (hl : f x.label = y.label) (hu : x.up = y.up)
    (hp : x.pos = y.pos) : relabel f x = y := by
  cases x
  cases y
  simp_all [relabel]

theorem injOn_swap {a c : ℕ} {S : Set ℕ} (hS : ∀ x ∈ S, x ≠ a) :
    Set.InjOn (fun x => if x = c then a else x) S := by
  intro x hx y hy hxy
  simp only at hxy
  by_cases h1 : x = c <;> by_cases h2 : y = c
  · rw [h1, h2]
  · rw [if_pos h1, if_neg h2] at hxy
    exact absurd hxy.symm (hS y hy)
  · rw [if_neg h1, if_pos h2] at hxy
    exact absurd hxy (hS x hx)
  · rw [if_neg h1, if_neg h2] at hxy
    exact hxy

theorem label_ne_of_free {Y : W} {c : ℕ} (h : cnt c Y = 0) {l : Letter} (hl : l ∈ Y) :
    l.label ≠ c := by
  have := List.countP_eq_zero.mp h l hl
  simpa using this

theorem good_case {w : W} (hw : Wf w) {p1 p2 p3 q1 q2 q3 : Letter} {Y Z : W} {k : ℕ}
    {α β γ : ℕ} (hk : w.rotate k = p1 :: p2 :: p3 :: (Y ++ q1 :: q2 :: q3 :: Z))
    (hp1 : p1.label = α) (hp2 : p2.label = β) (hp3 : p3.label = γ)
    (hq1 : q1.label = α) (hq2 : q2.label = β) (hq3 : q3.label = γ)
    (hu1 : p1.up = true) (hu3 : p3.up = true) (hv1 : q1.up = false) (hv3 : q3.up = false)
    (hs1 : p1.pos = q1.pos) (hs3 : p3.pos = q3.pos) (hs13 : p1.pos = p3.pos)
    (hab : α ≠ β) (hbc : β ≠ γ) (hac : α ≠ γ) :
    Equiv (remove2 w α β) (remove2 w β γ) := by
  have hL : Wf (p1 :: p2 :: p3 :: (Y ++ q1 :: q2 :: q3 :: Z)) := hk ▸ wf_rotate hw k
  have hcα : cnt α Y = 0 ∧ cnt α Z = 0 := by
    have := wf_cnt_le hL α
    simp only [cnt_cons, cnt_append, hp1, hp2, hp3, hq1, hq2, hq3, if_true, hab.symm, hac.symm,
      if_false] at this
    omega
  have hcβ : cnt β Y = 0 ∧ cnt β Z = 0 := by
    have := wf_cnt_le hL β
    simp only [cnt_cons, cnt_append, hp1, hp2, hp3, hq1, hq2, hq3, if_true, hbc.symm,
      hab, if_false] at this
    omega
  have hcγ : cnt γ Y = 0 ∧ cnt γ Z = 0 := by
    have := wf_cnt_le hL γ
    simp only [cnt_cons, cnt_append, hp1, hp2, hp3, hq1, hq2, hq3, if_true,
      hbc, hac, if_false] at this
    omega
  have n2a : p2.label ≠ α := by rw [hp2]; exact hab.symm
  have n3a : p3.label ≠ α := by rw [hp3]; exact hac.symm
  have m2a : q2.label ≠ α := by rw [hq2]; exact hab.symm
  have m3a : q3.label ≠ α := by rw [hq3]; exact hac.symm
  have n3b : p3.label ≠ β := by rw [hp3]; exact hbc.symm
  have m3b : q3.label ≠ β := by rw [hq3]; exact hbc.symm
  have n1b : p1.label ≠ β := by rw [hp1]; exact hab
  have m1b : q1.label ≠ β := by rw [hq1]; exact hab
  have n1c : p1.label ≠ γ := by rw [hp1]; exact hac
  have m1c : q1.label ≠ γ := by rw [hq1]; exact hac
  have eA : remove (p1 :: p2 :: p3 :: (Y ++ q1 :: q2 :: q3 :: Z)) α =
      p2 :: p3 :: (Y ++ q2 :: q3 :: Z) := by
    rw [remove_cons_eq hp1, remove_cons_ne n2a, remove_cons_ne n3a, remove_append,
      remove_of_free hcα.1, remove_cons_eq hq1, remove_cons_ne m2a, remove_cons_ne m3a,
      remove_of_free hcα.2]
  have eB : remove (p2 :: p3 :: (Y ++ q2 :: q3 :: Z)) β = p3 :: (Y ++ q3 :: Z) := by
    rw [remove_cons_eq hp2, remove_cons_ne n3b, remove_append, remove_of_free hcβ.1,
      remove_cons_eq hq2, remove_cons_ne m3b, remove_of_free hcβ.2]
  have eC : remove (p1 :: p2 :: p3 :: (Y ++ q1 :: q2 :: q3 :: Z)) β =
      p1 :: p3 :: (Y ++ q1 :: q3 :: Z) := by
    rw [remove_cons_ne n1b, remove_cons_eq hp2, remove_cons_ne n3b, remove_append,
      remove_of_free hcβ.1, remove_cons_ne m1b, remove_cons_eq hq2, remove_cons_ne m3b,
      remove_of_free hcβ.2]
  have eD : remove (p1 :: p3 :: (Y ++ q1 :: q3 :: Z)) γ = p1 :: (Y ++ q1 :: Z) := by
    rw [remove_cons_ne n1c, remove_cons_eq hp3, remove_append, remove_of_free hcγ.1,
      remove_cons_ne m1c, remove_cons_eq hq3, remove_of_free hcγ.2]
  have eαβ : remove2 (p1 :: p2 :: p3 :: (Y ++ q1 :: q2 :: q3 :: Z)) α β =
      p3 :: (Y ++ q3 :: Z) := by
    unfold remove2
    rw [eA, eB]
  have eβγ : remove2 (p1 :: p2 :: p3 :: (Y ++ q1 :: q2 :: q3 :: Z)) β γ =
      p1 :: (Y ++ q1 :: Z) := by
    unfold remove2
    rw [eC, eD]
  have hinj : Set.InjOn (fun x => if x = γ then α else x)
      (labelSet (remove2 (p1 :: p2 :: p3 :: (Y ++ q1 :: q2 :: q3 :: Z)) α β)) :=
    injOn_swap (fun x hx => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      exact (remove2_label_ne hl).1)
  have e3 : Equiv (remove2 (p1 :: p2 :: p3 :: (Y ++ q1 :: q2 :: q3 :: Z)) α β)
      (remove2 (p1 :: p2 :: p3 :: (Y ++ q1 :: q2 :: q3 :: Z)) β γ) := by
    refine ⟨0, fun x => if x = γ then α else x, hinj, ?_⟩
    rw [List.rotate_zero, eαβ, eβγ]
    have hY : Y.map (relabel fun x => if x = γ then α else x) = Y := by
      apply map_relabel_self
      intro c hc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
      simp [label_ne_of_free hcγ.1 hl]
    have hZ : Z.map (relabel fun x => if x = γ then α else x) = Z := by
      apply map_relabel_self
      intro c hc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
      simp [label_ne_of_free hcγ.2 hl]
    have h3 : relabel (fun x => if x = γ then α else x) p3 = p1 :=
      relabel_eq_of (by simp [hp3, hp1]) (by rw [hu1, hu3]) hs13.symm
    have h4 : relabel (fun x => if x = γ then α else x) q3 = q1 :=
      relabel_eq_of (by simp [hq3, hq1]) (by rw [hv1, hv3]) (by rw [← hs1, ← hs3, hs13])
    simp only [List.map_cons, List.map_append, hY, hZ, h3, h4]
  have e1 := equiv_remove2_rotate w α β k
  have e2 := equiv_remove2_rotate w β γ k
  rw [hk] at e1 e2
  exact e1.trans' (e3.trans' e2.symm')

/-! ### (f) El solapamiento -/

/-- **El solapamiento**: dos pares R2 `(a, b)` y `(b, c)` con `a ≠ c` en una palabra bien formada
dan resultados equivalentes. -/
theorem overlap_mid {w : W} (hw : Wf w) {a b c : ℕ} (h1 : R2cand w a b) (h2 : R2cand w b c)
    (hac : a ≠ c) : Equiv (remove2 w a b) (remove2 w b c) := by
  obtain ⟨hab, ht1, hb1, hi1, ho1⟩ := h1
  obtain ⟨hbc, ht2, hb2, hi2, ho2⟩ := h2
  obtain ⟨xa, xb, xc, hxa, hxb, hxc, hla, hua, hlb, hub, hlc, huc, htop⟩ :=
    side_tri hw ht1 ht2 hac
  obtain ⟨ya, yb, yc, hya, hyb, hyc, hla', hua', hlb', hub', hlc', huc', hbot⟩ :=
    side_tri hw hb1 hb2 hac
  have s12 : xa.pos ≠ xb.pos := by
    obtain ⟨x, hx, y, hy, hxa', hyb', hne⟩ := ho1
    rw [hw.pos_eq hxa hx (by rw [hla, hxa']), hw.pos_eq hxb hy (by rw [hlb, hyb'])]
    exact hne
  have s23 : xb.pos ≠ xc.pos := by
    obtain ⟨x, hx, y, hy, hxb', hyc', hne⟩ := ho2
    rw [hw.pos_eq hxb hx (by rw [hlb, hxb']), hw.pos_eq hxc hy (by rw [hlc, hyc'])]
    exact hne
  have hxac : xa.pos = xc.pos := by
    revert s12 s23
    cases xa.pos <;> cases xb.pos <;> cases xc.pos <;> simp
  have sa : xa.pos = ya.pos := hw.pos_eq hxa hya (by rw [hla, hla'])
  have sc : xc.pos = yc.pos := hw.pos_eq hxc hyc (by rw [hlc, hlc'])
  have hne : ∀ x y : Letter, x.up = true → y.up = false → y ≠ x := by
    intro x y hx hy h
    rw [h, hx] at hy
    exact Bool.noConfusion hy
  have hLw := wf_rotate hw
  rcases htop with ht | ht <;> rcases hbot with hb | hb
  · obtain ⟨k, Y, Z, hk⟩ := tri_tri hw.nodup ht hb (hne _ _ hua hua') (hne _ _ hub hua')
      (hne _ _ huc hua') (hne _ _ hua hub') (hne _ _ hua huc')
    exact good_case hw hk hla hlb hlc hla' hlb' hlc' hua huc hua' huc' sa sc hxac hab hbc hac
  · obtain ⟨k, Y, Z, hk⟩ := tri_tri hw.nodup ht hb (hne _ _ hua huc') (hne _ _ hub huc')
      (hne _ _ huc huc') (hne _ _ hua hub') (hne _ _ hua hua')
    exact (nested_false (hLw k) hk hla hla' hlb hlb' (hi1.rotate k)).elim
  · obtain ⟨k, Y, Z, hk⟩ := tri_tri hw.nodup ht hb (hne _ _ huc hua') (hne _ _ hub hua')
      (hne _ _ hua hua') (hne _ _ huc hub') (hne _ _ huc huc')
    exact (nested_false (hLw k) hk hlc hlc' hlb hlb' (hi2.symm.rotate k)).elim
  · obtain ⟨k, Y, Z, hk⟩ := tri_tri hw.nodup ht hb (hne _ _ huc huc') (hne _ _ hub huc')
      (hne _ _ hua huc') (hne _ _ huc hub') (hne _ _ huc hua')
    have := good_case hw hk hlc hlb hla hlc' hlb' hla' huc hua huc' hua' sc sa hxac.symm
      hbc.symm hab.symm hac.symm
    rw [remove2_comm w a b, remove2_comm w b c]
    exact this.symm'

/-- Dos pares R2 que comparten algún cruce dan resultados equivalentes (todas las variantes del
solapamiento: el cruce común puede ocupar cualquier papel). -/
theorem r2_overlap {w : W} (hw : Wf w) {a b c d : ℕ} (h1 : R2cand w a b) (h2 : R2cand w c d)
    (hshare : a = c ∨ a = d ∨ b = c ∨ b = d) : Equiv (remove2 w a b) (remove2 w c d) := by
  rcases hshare with rfl | rfl | rfl | rfl
  · by_cases hbd : b = d
    · subst hbd
      exact Equiv.refl' _
    · have := overlap_mid hw h1.symm h2 hbd
      rwa [remove2_comm w b a] at this
  · by_cases hbc : b = c
    · subst hbc
      rw [remove2_comm w a b]
      exact Equiv.refl' _
    · have := overlap_mid hw h1.symm h2.symm hbc
      rwa [remove2_comm w b a, remove2_comm w a c] at this
  · by_cases had : a = d
    · subst had
      rw [remove2_comm w a b]
      exact Equiv.refl' _
    · exact overlap_mid hw h1 h2 had
  · by_cases hac : a = c
    · subst hac
      exact Equiv.refl' _
    · have := overlap_mid hw h1 h2.symm hac
      rwa [remove2_comm w b c] at this

/-! ### Conmutaciones de varios cruces -/

theorem remove2_remove_comm (w : W) (a b c : ℕ) :
    remove2 (remove w c) a b = remove (remove2 w a b) c := by
  unfold remove2
  rw [remove_comm w c a, remove_comm (remove w a) c b]

theorem remove2_remove2_comm (w : W) (a b c d : ℕ) :
    remove2 (remove2 w a b) c d = remove2 (remove2 w c d) a b := by
  unfold remove2 remove
  simp only [List.filter_filter]
  congr 1
  funext l
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true]
  tauto

/-! ### Confluencia local módulo `≈` -/

section Local

open Relation

theorem local_r1_r1 {w : W} {c d : ℕ} (hc : R1cand w c) (hd : R1cand w d) :
    ∃ y' z', ReflTransGen Red (remove w c) y' ∧ ReflTransGen Red (remove w d) z' ∧
      Equiv y' z' := by
  by_cases h : c = d
  · subst h
    exact ⟨_, _, .refl, .refl, Equiv.refl' _⟩
  · refine ⟨remove (remove w c) d, remove (remove w d) c, .single (Or.inl ⟨d, hd.remove h, rfl⟩),
      .single (Or.inl ⟨c, hc.remove (Ne.symm h), rfl⟩), ?_⟩
    rw [remove_comm w c d]
    exact Equiv.refl' _

theorem local_r1_r2 {w : W} (hw : Wf w) {c a b : ℕ} (hc : R1cand w c) (hab : R2cand w a b) :
    ∃ y' z', ReflTransGen Red (remove w c) y' ∧ ReflTransGen Red (remove2 w a b) z' ∧
      Equiv y' z' := by
  obtain ⟨n1, n2⟩ := R1cand_not_R2 hw hab
  have hca : c ≠ a := fun h => n1 (h ▸ hc)
  have hcb : c ≠ b := fun h => n2 (h ▸ hc)
  have hr2 : R2cand (remove w c) a b := hab.remove hca hcb
  have hr1 : R1cand (remove2 w a b) c := by
    unfold remove2
    exact (hc.remove (Ne.symm hca)).remove (Ne.symm hcb)
  refine ⟨remove2 (remove w c) a b, remove (remove2 w a b) c, .single (Or.inr ⟨a, b, hr2, rfl⟩),
    .single (Or.inl ⟨c, hr1, rfl⟩), ?_⟩
  rw [remove2_remove_comm]
  exact Equiv.refl' _

theorem local_r2_r2 {w : W} (hw : Wf w) {a b c d : ℕ} (h1 : R2cand w a b) (h2 : R2cand w c d) :
    ∃ y' z', ReflTransGen Red (remove2 w a b) y' ∧ ReflTransGen Red (remove2 w c d) z' ∧
      Equiv y' z' := by
  by_cases hs : a = c ∨ a = d ∨ b = c ∨ b = d
  · exact ⟨_, _, .refl, .refl, r2_overlap hw h1 h2 hs⟩
  · simp only [not_or] at hs
    obtain ⟨hac, had, hbc, hbd⟩ := hs
    have e1 : R2cand (remove2 w a b) c d := by
      unfold remove2
      exact (h2.remove hac had).remove hbc hbd
    have e2 : R2cand (remove2 w c d) a b := by
      unfold remove2
      exact (h1.remove (Ne.symm hac) (Ne.symm hbc)).remove (Ne.symm had) (Ne.symm hbd)
    refine ⟨remove2 (remove2 w a b) c d, remove2 (remove2 w c d) a b,
      .single (Or.inr ⟨c, d, e1, rfl⟩), .single (Or.inr ⟨a, b, e2, rfl⟩), ?_⟩
    rw [remove2_remove2_comm]
    exact Equiv.refl' _

/-- **Confluencia local módulo `≈`** para palabras bien formadas. -/
theorem red_local {w y z : W} (hw : Wf w) (h1 : Red w y) (h2 : Red w z) :
    ∃ y' z', ReflTransGen Red y y' ∧ ReflTransGen Red z z' ∧ Equiv y' z' := by
  rcases h1 with ⟨c, hc, rfl⟩ | ⟨a, b, hab, rfl⟩ <;>
    rcases h2 with ⟨d, hd, rfl⟩ | ⟨e, f, hef, rfl⟩
  · exact local_r1_r1 hc hd
  · exact local_r1_r2 hw hc hef
  · obtain ⟨y', z', h1, h2, h3⟩ := local_r1_r2 hw hd hab
    exact ⟨z', y', h2, h1, h3.symm'⟩
  · exact local_r2_r2 hw hab hef

end Local

/-! ### Ensamblaje: forma normal única -/

section Assembly

open Relation

/-- `Red` preserva la buena formación a lo largo de cadenas. -/
theorem rtg_wf {x y : W} (hx : Wf x) (h : ReflTransGen Red x y) : Wf y := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact Red.wf_preserved ih hbc

/-- Las cadenas de `Red` no aumentan los cruces. -/
theorem rtg_crossings_le {x y : W} (h : ReflTransGen Red x y) : crossings y ≤ crossings x := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact (Red.crossings_lt hbc).le.trans ih

/-- Si una cadena de `Red` no baja los cruces, es la cadena vacía. -/
theorem rtg_eq_of_crossings {x y : W} (h : ReflTransGen Red x y)
    (he : crossings y = crossings x) : y = x := by
  rcases h.cases_head with h | ⟨c, hxc, hcy⟩
  · exact h.symm
  · have h1 := Red.crossings_lt hxc
    have h2 := rtg_crossings_le hcy
    omega

/-- Palabras bien formadas, como subtipo (para aplicar Newman). -/
abbrev WfW := {w : W // Wf w}

/-- `Red` levantada al subtipo. -/
def RedS (x y : WfW) : Prop := Red x.1 y.1

/-- `≈` levantada al subtipo. -/
def EquivS (x y : WfW) : Prop := Equiv x.1 y.1

theorem equivS_equivalence : Equivalence EquivS :=
  ⟨fun x => equiv_equivalence.refl x.1, fun h => equiv_equivalence.symm h,
    fun h h' => equiv_equivalence.trans h h'⟩

theorem redS_wf : WellFounded (flip RedS) :=
  Subrelation.wf (fun {_ _} h => Red.crossings_lt h)
    (InvImage.wf (fun x : WfW => crossings x.1) wellFounded_lt)

/-- Una cadena de `Red` desde una palabra bien formada se levanta al subtipo. -/
theorem lift_rtg {x y : W} (hx : Wf x) (h : ReflTransGen Red x y) :
    ∃ hy : Wf y, ReflTransGen RedS (⟨x, hx⟩ : WfW) ⟨y, hy⟩ := by
  induction h with
  | refl => exact ⟨hx, .refl⟩
  | tail hab hbc ih =>
    obtain ⟨hb, ih⟩ := ih
    exact ⟨Red.wf_preserved hb hbc, ih.tail hbc⟩

theorem redS_compat : ∀ x x' y : WfW, EquivS x x' → RedS x y →
    ∃ y', RedS x' y' ∧ EquivS y y' := by
  intro x x' y hxx hxy
  obtain ⟨y1, h1, e⟩ := red_compat_equiv hxx hxy
  exact ⟨⟨y1, Red.wf_preserved x'.2 h1⟩, h1, e⟩

theorem redS_local : ∀ x y z : WfW, RedS x y → RedS x z →
    ∃ y' z', ReflTransGen RedS y y' ∧ ReflTransGen RedS z z' ∧ EquivS y' z' := by
  intro x y z h1 h2
  obtain ⟨y', z', hy, hz, e⟩ := red_local x.2 h1 h2
  obtain ⟨hy', ly⟩ := lift_rtg y.2 hy
  obtain ⟨hz', lz⟩ := lift_rtg z.2 hz
  exact ⟨⟨y', hy'⟩, ⟨z', hz'⟩, ly, lz, e⟩

/-- **Forma normal única (palabras)**: dos reducciones de una palabra bien formada a palabras
irreducibles terminan en palabras equivalentes (salvo rotación y renombrado). -/
theorem normal_form_unique_words {w n n' : W} (hw : Wf w) (hn : ReflTransGen Red w n)
    (hn' : ReflTransGen Red w n') (hirr : ¬ ∃ y, Red n y) (hirr' : ¬ ∃ y, Red n' y) :
    Equiv n n' := by
  obtain ⟨h1, l1⟩ := lift_rtg hw hn
  obtain ⟨h2, l2⟩ := lift_rtg hw hn'
  exact normal_form_unique (R := RedS) (E := EquivS) equivS_equivalence redS_wf redS_compat
    redS_local l1 l2 (fun ⟨y, hy⟩ => hirr ⟨y.1, hy⟩) (fun ⟨y, hy⟩ => hirr' ⟨y.1, hy⟩)

/-- **Existencia de forma normal**: toda palabra se reduce a una irreducible. -/
theorem exists_normal_form_words (w : W) : ∃ n, ReflTransGen Red w n ∧ ¬ ∃ y, Red n y :=
  exists_normal_form red_wf w

/-- Confluencia módulo `≈` para palabras bien formadas. -/
theorem red_confluent_mod {w y z : W} (hw : Wf w) (hy : ReflTransGen Red w y)
    (hz : ReflTransGen Red w z) :
    ∃ y' z', ReflTransGen Red y y' ∧ ReflTransGen Red z z' ∧ Equiv y' z' := by
  obtain ⟨hy', ly⟩ := lift_rtg hw hy
  obtain ⟨hz', lz⟩ := lift_rtg hw hz
  obtain ⟨y1, z1, a, b, e⟩ := newman_mod (R := RedS) (E := EquivS) equivS_equivalence redS_wf
    redS_compat redS_local ⟨w, hw⟩ ⟨y, hy'⟩ ⟨z, hz'⟩ ly lz
  exact ⟨y1.1, z1.1, a.lift Subtype.val (fun _ _ h => h), b.lift Subtype.val (fun _ _ h => h), e⟩

end Assembly

/-! ### Corolarios fieles A6 y A7 -/

section Corollaries

open Relation

/-- Paso elemental de la clase: `Red`, su inversa o `≈`, entre palabras bien formadas. -/
def Gen (x y : W) : Prop := Wf x ∧ Wf y ∧ (Red x y ∨ Red y x ∨ Equiv x y)

/-- La clase: cerradura de equivalencia de `Red ∪ Red⁻¹ ∪ ≈` sobre palabras bien formadas. -/
def Cls (x y : W) : Prop := EqvGen Gen x y

/-- `w` tiene el menor número de cruces de su clase. -/
def IsMin (w : W) : Prop := ∀ v : W, Wf v → Cls w v → crossings w ≤ crossings v

theorem irreducible_equiv {u v : W} (h : Equiv u v) (hu : ¬ ∃ z, Red u z) : ¬ ∃ z, Red v z := by
  rintro ⟨z, hz⟩
  obtain ⟨z', hz', -⟩ := red_compat_equiv (equiv_equivalence.symm h) hz
  exact hu ⟨z', hz'⟩

theorem crossings_equiv {u v : W} (hu : Wf u) (h : Equiv u v) : crossings u = crossings v := by
  have hv := wf_equiv hu h
  have h1 := wf_length_eq hu
  have h2 := wf_length_eq hv
  obtain ⟨k, f, -, rfl⟩ := h
  simp only [List.length_map, List.length_rotate] at h2
  omega

theorem cls_of_rtg {x y : W} (hx : Wf x) (h : ReflTransGen Red x y) : Cls x y := by
  induction h with
  | refl => exact EqvGen.refl _
  | tail hab hbc ih =>
    exact EqvGen.trans _ _ _ ih
      (EqvGen.rel _ _ ⟨rtg_wf hx hab, Red.wf_preserved (rtg_wf hx hab) hbc, Or.inl hbc⟩)

/-- Invariante: dos palabras de la misma clase tienen formas normales equivalentes. -/
def SameNF (x y : W) : Prop :=
  x = y ∨ (Wf x ∧ Wf y ∧ ∃ n n' : W, ReflTransGen Red x n ∧ ReflTransGen Red y n' ∧
    (¬ ∃ z, Red n z) ∧ (¬ ∃ z, Red n' z) ∧ Equiv n n')

theorem sameNF_of_gen {x y : W} (h : Gen x y) : SameNF x y := by
  obtain ⟨hx, hy, h | h | h⟩ := h
  · obtain ⟨n, hn, hirr⟩ := exists_normal_form_words y
    exact Or.inr ⟨hx, hy, n, n, .head h hn, hn, hirr, hirr, equiv_equivalence.refl n⟩
  · obtain ⟨n, hn, hirr⟩ := exists_normal_form_words x
    exact Or.inr ⟨hx, hy, n, n, hn, .head h hn, hirr, hirr, equiv_equivalence.refl n⟩
  · obtain ⟨n, hn, hirr⟩ := exists_normal_form_words x
    obtain ⟨y', hy', e⟩ := lift_compat (E := Equiv) (fun _ _ _ => red_compat_equiv) h hn
    exact Or.inr ⟨hx, hy, n, y', hn, hy', hirr, irreducible_equiv e hirr, e⟩

theorem sameNF_symm {x y : W} (h : SameNF x y) : SameNF y x := by
  rcases h with rfl | ⟨hx, hy, n, n', h1, h2, h3, h4, h5⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hy, hx, n', n, h2, h1, h4, h3, equiv_equivalence.symm h5⟩

theorem sameNF_trans {x y z : W} (h1 : SameNF x y) (h2 : SameNF y z) : SameNF x z := by
  rcases h1 with rfl | ⟨hx, hy, n, n', a1, a2, a3, a4, a5⟩
  · exact h2
  rcases h2 with rfl | ⟨hy2, hz, m, m', b1, b2, b3, b4, b5⟩
  · exact Or.inr ⟨hx, hy, n, n', a1, a2, a3, a4, a5⟩
  have e := normal_form_unique_words hy a2 b1 a4 b3
  exact Or.inr ⟨hx, hz, n, m', a1, b2, a3, b4,
    equiv_equivalence.trans a5 (equiv_equivalence.trans e b5)⟩

theorem sameNF_of_cls {x y : W} (h : Cls x y) : SameNF x y := by
  induction h with
  | rel a b hab => exact sameNF_of_gen hab
  | refl a => exact Or.inl rfl
  | symm a b _ ih => exact sameNF_symm ih
  | trans a b c _ _ ih1 ih2 => exact sameNF_trans ih1 ih2

/-- **A6 fiel**: una palabra bien formada e irreducible tiene el menor número de cruces de su
clase (clase = cerradura de equivalencia de `Red ∪ Red⁻¹ ∪ ≈`). -/
theorem a6_irreducible_min {w : W} (hw : Wf w) (hirr : ¬ ∃ y, Red w y) : IsMin w := by
  intro v hv hcl
  rcases sameNF_of_cls hcl with rfl | ⟨-, -, n, n', h1, h2, -, -, he⟩
  · exact le_rfl
  · have hnw : n = w := by
      rcases h1.cases_head with h | ⟨c, hc, -⟩
      · exact h.symm
      · exact absurd ⟨c, hc⟩ hirr
    subst hnw
    have hn' := rtg_wf hv h2
    rw [crossings_equiv hw he]
    exact rtg_crossings_le h2

/-- **A7 fiel**: dos palabras bien formadas de la misma clase y de número de cruces mínimo son
equivalentes (salvo rotación y renombrado). -/
theorem a7_min_equiv {w w' : W} (hw : Wf w) (hw' : Wf w') (hcl : Cls w w') (hm : IsMin w)
    (hm' : IsMin w') : Equiv w w' := by
  rcases sameNF_of_cls hcl with rfl | ⟨-, -, n, n', h1, h2, -, -, he⟩
  · exact equiv_equivalence.refl _
  · have hn := rtg_wf hw h1
    have hn' := rtg_wf hw' h2
    have e1 : n = w := rtg_eq_of_crossings h1
      (le_antisymm (rtg_crossings_le h1) (hm n hn (cls_of_rtg hw h1)))
    have e2 : n' = w' := rtg_eq_of_crossings h2
      (le_antisymm (rtg_crossings_le h2) (hm' n' hn' (cls_of_rtg hw' h2)))
    rw [e1, e2] at he
    exact he

/-- Toda clase tiene un representante de grado mínimo (una forma normal). -/
theorem exists_min_in_class {w : W} (hw : Wf w) :
    ∃ n, ReflTransGen Red w n ∧ Wf n ∧ IsMin n := by
  obtain ⟨n, hn, hirr⟩ := exists_normal_form_words w
  exact ⟨n, hn, rtg_wf hw hn, a6_irreducible_min (rtg_wf hw hn) hirr⟩

end Corollaries

end FormaNormal
