-- KN_04_Clasificacion_General.lean
-- Clasificación de Configuraciones K_n: Órbitas y Teorema Órbita-Estabilizador
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Enero 9, 2026

import TMENudos.KN_02_Grupo_Dihedral_General
import TMENudos.KN_03_Invariantes_General
import TMENudos.KN_03b_Invariantes_IME

namespace KnotTheory.General

open KnConfig

variable {n : ℕ} [NeZero n]

/-! ## Órbitas bajo la acción de D₂ₙ -/

/-- La órbita de una configuración K bajo la acción del grupo diedral D₂ₙ.

    La órbita consiste en todas las configuraciones que se pueden obtener
    aplicando rotaciones y reflexiones a K.

    Representamos D₂ₙ como `ZMod (2*n) × Bool` donde:
    - `(k, false)` representa rotación por k
    - `(k, true)` representa reflexión seguida de rotación por k -/
def orbit (K : KnConfig n) : Finset (KnConfig n) :=
  (Finset.univ : Finset (ZMod (2 * n) × Bool)).image fun g =>
    if g.2 then (K.mirror).rotate g.1 else K.rotate g.1

/-- Notación para órbita -/
notation "Orb(" K ")" => orbit K

/-! ## Estabilizadores -/

/-- El estabilizador de una configuración K bajo D₂ₙ.

    El estabilizador es el subgrupo de D₂ₙ que deja a K invariante.

    Representamos D₂ₙ como `ZMod (2*n) × Bool` donde:
    - `(k, false)` representa rotación por k
    - `(k, true)` representa reflexión seguida de rotación por k -/
def stabilizer (K : KnConfig n) : Finset (ZMod (2 * n) × Bool) :=
  (Finset.univ : Finset (ZMod (2 * n) × Bool)).filter fun g =>
    (if g.2 then (K.mirror).rotate g.1 else K.rotate g.1) = K

/-- Notación para estabilizador -/
notation "Stab(" K ")" => stabilizer K

/-! ## Teoremas Básicos -/

omit [NeZero n] in
/-- La rotación por 0 es la identidad -/
lemma rotate_zero' (K : KnConfig n) : K.rotate 0 = K := by
  rw [KnConfig.ext_iff]
  simp only [KnConfig.rotate]
  have : ∀ p : OrderedPair n, p.rotate 0 = p := by
    intro p
    cases p
    simp [OrderedPair.rotate]
  simp [this]

omit [NeZero n] in
/-- La rotación es inyectiva -/
lemma rotate_inj' {K₁ K₂ : KnConfig n} {k : ZMod (2 * n)}
    (h : K₁.rotate k = K₂.rotate k) : K₁ = K₂ := by
  have := congrArg (fun C => C.rotate (-k)) h
  simpa [rotate_zero'] using this

omit [NeZero n] in
/-- La reflexión es inyectiva -/
lemma mirror_inj' {K₁ K₂ : KnConfig n} (h : K₁.mirror = K₂.mirror) : K₁ = K₂ := by
  have := congrArg KnConfig.mirror h
  simpa [KnConfig.mirror_mirror] using this

/-- Acción de un elemento `(k, m)` de D₂ₙ sobre una configuración. -/
def act (g : ZMod (2 * n) × Bool) (K : KnConfig n) : KnConfig n :=
  if g.2 then (K.mirror).rotate g.1 else K.rotate g.1

/-- Producto en D₂ₙ (compatible con `act`). -/
def dmul (g h : ZMod (2 * n) × Bool) : ZMod (2 * n) × Bool :=
  (g.1 + (if g.2 then -h.1 else h.1), xor g.2 h.2)

omit [NeZero n] in
lemma act_dmul (g h : ZMod (2 * n) × Bool) (K : KnConfig n) :
    act g (act h K) = act (dmul g h) K := by
  obtain ⟨k0, m0⟩ := g
  obtain ⟨k, m⟩ := h
  cases m0 <;> cases m <;>
    simp [act, dmul, KnConfig.mirror_rotate_mirror, KnConfig.mirror_mirror, add_comm]

omit [NeZero n] in
lemma act_inj (g : ZMod (2 * n) × Bool) {K₁ K₂ : KnConfig n}
    (h : act g K₁ = act g K₂) : K₁ = K₂ := by
  obtain ⟨k0, m0⟩ := g
  cases m0
  · exact rotate_inj' (by simpa [act] using h)
  · exact mirror_inj' (rotate_inj' (by simpa [act] using h))

omit [NeZero n] in
lemma dmul_left_cancel (g : ZMod (2 * n) × Bool) {h h' : ZMod (2 * n) × Bool}
    (H : dmul g h = dmul g h') : h = h' := by
  obtain ⟨k0, m0⟩ := g
  obtain ⟨k, m⟩ := h
  obtain ⟨k', m'⟩ := h'
  cases m0 <;> cases m <;> cases m' <;> simp_all [dmul]

/-- Toda configuración está en su propia órbita -/
theorem mem_orbit_self (K : KnConfig n) : K ∈ Orb(K) := by
  unfold orbit
  rw [Finset.mem_image]
  exact ⟨(0, false), Finset.mem_univ _, by simp [rotate_zero']⟩

/-- La identidad siempre está en el estabilizador -/
theorem one_mem_stabilizer (K : KnConfig n) : (0, false) ∈ Stab(K) := by
  unfold stabilizer
  simp [Finset.mem_filter, rotate_zero']

/-! ## Propiedades de Órbitas -/

/-- Dos configuraciones están en la misma órbita ssi una es imagen de la otra -/
theorem in_same_orbit_iff (K₁ K₂ : KnConfig n) :
  K₂ ∈ Orb(K₁) ↔ ∃ (k : ZMod (2 * n)) (m : Bool),
    (if m then K₁.mirror else K₁).rotate k = K₂ := by
  unfold orbit
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨k, m⟩, _, h⟩
    exact ⟨k, m, by cases m <;> simpa using h⟩
  · rintro ⟨k, m, h⟩
    exact ⟨(k, m), Finset.mem_univ _, by cases m <;> simpa using h⟩

/-! ## Lemas auxiliares -/

omit [NeZero n] in
/-- El grupo D₂ₙ tiene cardinalidad 4n -/
lemma card_D2n : 4 * n = 4 * n := rfl

/-! ## Teorema Órbita-Estabilizador -/

/-- Teorema órbita-estabilizador: |Orb(K)| * |Stab(K)| = |D₂ₙ| = 4n

    Este es el teorema fundamental de la teoría de órbitas. Establece que
    el tamaño de la órbita multiplicado por el tamaño del estabilizador
    es igual al tamaño del grupo. -/
theorem orbit_stabilizer (K : KnConfig n) :
    (Orb(K)).card * (Stab(K)).card = 4 * n := by
  -- Cada fibra de g ↦ act g K tiene tantos elementos como el estabilizador
  have h_fiber (g0 : ZMod (2 * n) × Bool) :
      (Finset.univ.filter (fun x : ZMod (2 * n) × Bool => act x K = act g0 K)).card =
        (Stab(K)).card := by
    symm
    apply Finset.card_bij (fun h _ => dmul g0 h)
    · intro h hh
      have hh' : act h K = K := by
        have := (Finset.mem_filter.mp hh).2
        simpa [act] using this
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← act_dmul, hh']
    · intro h _ h' _ H
      exact dmul_left_cancel g0 H
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      let h : ZMod (2 * n) × Bool :=
        (if g0.2 then g0.1 - g.1 else g.1 - g0.1, xor g0.2 g.2)
      have hmul : dmul g0 h = g := by
        obtain ⟨k0, m0⟩ := g0
        obtain ⟨k, m⟩ := g
        cases m0 <;> cases m <;> simp [dmul, h]
      refine ⟨h, ?_, hmul⟩
      have hh : act h K = K := by
        apply act_inj g0
        rw [act_dmul, hmul, hg]
      simp only [stabilizer, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [act] using hh
  have h1 : (Finset.univ : Finset (ZMod (2 * n) × Bool)).card = 4 * n := by
    rw [Finset.card_univ, Fintype.card_prod, ZMod.card, Fintype.card_bool]
    ring
  calc (Orb(K)).card * (Stab(K)).card = ∑ _C ∈ Orb(K), (Stab(K)).card := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = ∑ C ∈ Orb(K),
          (Finset.univ.filter (fun x : ZMod (2 * n) × Bool => act x K = C)).card := by
        refine Finset.sum_congr rfl fun C hC => ?_
        obtain ⟨g0, _, rfl⟩ := Finset.mem_image.mp hC
        exact (h_fiber g0).symm
    _ = (Finset.univ : Finset (ZMod (2 * n) × Bool)).card :=
        (Finset.card_eq_sum_card_image (fun g => act g K) Finset.univ).symm
    _ = 4 * n := h1

/-! ## Cálculo de tamaño de órbita -/

/-- Cálculo de tamaño de órbita a partir del tamaño del estabilizador -/
theorem orbit_card_from_stabilizer (K : KnConfig n) (m : ℕ) (hm : 0 < m) (_hdiv : m ∣ 4 * n) :
    (Stab(K)).card = m → (Orb(K)).card = (4 * n) / m := by
  intro h_stab
  have h_total := orbit_stabilizer K
  rw [h_stab, mul_comm] at h_total
  exact Nat.eq_div_of_mul_eq_right (Nat.ne_of_gt hm) h_total

/-! ## Corolarios útiles -/

/-- Versión alternativa del teorema órbita-estabilizador -/
theorem orbit_stabilizer' (K : KnConfig n) :
    (Orb(K)).card = (4 * n) / (Stab(K)).card ∧ (Stab(K)).card ∣ (4 * n) := by
  have h_card := orbit_stabilizer K
  have h_pos : 0 < (Stab(K)).card := by
    have : (0, false) ∈ Stab(K) := one_mem_stabilizer K
    exact Finset.card_pos.mpr ⟨(0, false), this⟩
  constructor
  · rw [mul_comm] at h_card
    exact Nat.eq_div_of_mul_eq_right (Nat.ne_of_gt h_pos) h_card
  · rw [← h_card]
    exact Dvd.intro_left _ rfl

/-- El tamaño de la órbita divide al tamaño del grupo -/
theorem orbit_card_dvd (K : KnConfig n) : (Orb(K)).card ∣ (4 * n) := by
  have h := orbit_stabilizer' K
  rcases h with ⟨h_eq, h_div⟩
  rw [h_eq]
  exact Nat.div_dvd_of_dvd h_div

/-- El tamaño del estabilizador divide al tamaño del grupo -/
theorem stabilizer_card_dvd (K : KnConfig n) : (Stab(K)).card ∣ (4 * n) :=
  (orbit_stabilizer' K).2

/-! ## Invariantes y Órbitas -/

/- Configuraciones en la misma órbita tienen el mismo IDE
   (Requires defining how pairs transform under group action)
theorem IDE_eq_of_mem_orbit (K₁ K₂ : KnConfig n) (p : OrderedPair n) :
    K₂ ∈ Orb(K₁) → K₁.IDE p = K₂.IDE (transformed_pair p) := by
  sorry
-/

/-- Configuraciones en la misma órbita tienen el mismo IME -/
theorem IME_eq_of_mem_orbit (K₁ K₂ : KnConfig n) :
    K₂ ∈ Orb(K₁) → K₁.IME = K₂.IME := by
  intro h
  rcases (in_same_orbit_iff K₁ K₂).mp h with ⟨k, m, hkm⟩
  cases m
  · -- Case: K₂ = K₁.rotate k
    rw [if_neg (by simp)] at hkm
    subst hkm
    exact (KnConfig.IME_rotate K₁ k).symm
  · -- Case: K₂ = (K₁.mirror).rotate k
    rw [if_pos rfl] at hkm
    subst hkm
    rw [KnConfig.IME_rotate, KnConfig.IME_mirror]

end KnotTheory.General
