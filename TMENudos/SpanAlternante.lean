import Mathlib
import TMENudos.SpanPuente
import TMENudos.SpanGenero

/-!
# Caras de un diagrama alternante (etapa S5d)

Para un diagrama ALTERNANTE el numero de CARAS (ciclos de `sigma * eps`) es
`lazos allA + lazos allB`; con planaridad (caras = c + 2) sale la igualdad de genero
`s_A + s_B = c + 2`.

Modelo `X = iota x Bool` (`false` = entrada, `true` = salida).  La rotacion antihoraria en
el cruce es `sigma (j, s) = (partner j, s xor (sign j xor ovr j))`; coincide con `sigmaD` de
`Etapa1_Planaridad` (positivo: `out o -> out u -> in o -> in u`; negativo:
`out o -> in u -> in o -> out u`) y vale `a` en letras inferiores y `b` en superiores.
-/

open SpanGenero Relation

namespace SpanAlt

/-! ### (A) Abstracto: ciclos dentro de un subconjunto invariante -/

section Abstracto

variable {X : Type*}

/-- Numero de ciclos de `π` contenidos en `Y`. -/
noncomputable def cycOn (π : Equiv.Perm X) (Y : X → Prop) : ℕ :=
  ncs (Setoid.comap (Subtype.val : {x // Y x} → X) (cycSetoid π))

theorem cycSetoid_pres (π : Equiv.Perm X) (Y : X → Prop) (hY : ∀ x, Y x ↔ Y (π x))
    {x y : X} (h : (cycSetoid π) x y) : Y x ↔ Y y := by
  induction h with
  | rel u v h => rw [← h]; exact hY u
  | refl u => exact Iff.rfl
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2

/-- Los ciclos de `π` se reparten entre `Y` y su complemento si `Y` es invariante. -/
theorem cyc_split [Finite X] (π : Equiv.Perm X) (Y : X → Prop) (hY : ∀ x, Y x ↔ Y (π x)) :
    cyc π = cycOn π Y + cycOn π (fun x => ¬ Y x) := by
  classical
  let S1 : Setoid {x // Y x} := Setoid.comap Subtype.val (cycSetoid π)
  let S2 : Setoid {x // ¬ Y x} := Setoid.comap Subtype.val (cycSetoid π)
  let g : Quotient S1 ⊕ Quotient S2 → Quotient (cycSetoid π) :=
    Sum.elim (Quotient.map Subtype.val (fun x y h => h))
      (Quotient.map Subtype.val (fun x y h => h))
  have hg : Function.Bijective g := by
    constructor
    · rintro (p | p) (q | q) h
      · induction p using Quotient.inductionOn with
        | _ x =>
          induction q using Quotient.inductionOn with
          | _ y =>
            have h' : (cycSetoid π) x.1 y.1 := Quotient.exact h
            exact congrArg Sum.inl (Quotient.sound h')
      · induction p using Quotient.inductionOn with
        | _ x =>
          induction q using Quotient.inductionOn with
          | _ y =>
            have h' : (cycSetoid π) x.1 y.1 := Quotient.exact h
            exact absurd ((cycSetoid_pres π Y hY h').1 x.2) y.2
      · induction p using Quotient.inductionOn with
        | _ x =>
          induction q using Quotient.inductionOn with
          | _ y =>
            have h' : (cycSetoid π) x.1 y.1 := Quotient.exact h
            exact absurd ((cycSetoid_pres π Y hY h').2 y.2) x.2
      · induction p using Quotient.inductionOn with
        | _ x =>
          induction q using Quotient.inductionOn with
          | _ y =>
            have h' : (cycSetoid π) x.1 y.1 := Quotient.exact h
            exact congrArg Sum.inr (Quotient.sound h')
    · intro c
      induction c using Quotient.inductionOn with
      | _ z =>
        by_cases hz : Y z
        · exact ⟨Sum.inl (Quotient.mk _ ⟨z, hz⟩), rfl⟩
        · exact ⟨Sum.inr (Quotient.mk _ ⟨z, hz⟩), rfl⟩
  have := Nat.card_congr (Equiv.ofBijective g hg)
  rw [Nat.card_sum] at this
  exact this.symm

theorem cycSetoid_agree [Finite X] (π π' : Equiv.Perm X) (Y : X → Prop)
    (hinv : ∀ x, Y x → Y (π x)) (hag : ∀ x, Y x → π x = π' x) {x y : X} (hx : Y x)
    (h : (cycSetoid π) x y) : (cycSetoid π') x y := by
  obtain ⟨n, rfl⟩ := ((cycSetoid_iff π).1 h).exists_nat_pow_eq
  have key : ∀ n : ℕ, Y ((π ^ n) x) ∧ (π' ^ n) x = (π ^ n) x := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using hx, by simp⟩
    | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply, ih.2]
      exact ⟨hinv _ ih.1, (hag _ ih.1).symm⟩
  rw [← (key n).2]
  exact cyc_pow π' x n

/-- Si `π` y `π'` coinciden en `Y` (invariante), tienen los mismos ciclos dentro de `Y`. -/
theorem cycOn_congr [Finite X] (π π' : Equiv.Perm X) (Y : X → Prop)
    (hinv : ∀ x, Y x → Y (π x)) (hag : ∀ x, Y x → π x = π' x) :
    cycOn π Y = cycOn π' Y := by
  have hinv' : ∀ x, Y x → Y (π' x) := fun x hx => (hag x hx) ▸ hinv x hx
  have hs : Setoid.comap (Subtype.val : {x // Y x} → X) (cycSetoid π) =
      Setoid.comap Subtype.val (cycSetoid π') := by
    ext x y
    exact ⟨fun h => cycSetoid_agree π π' Y hinv hag x.2 h,
      fun h => cycSetoid_agree π' π Y hinv' (fun z hz => (hag z hz).symm) x.2 h⟩
  unfold cycOn
  rw [hs]

/-- **Clave**: si `Y` y su imagen por `ε` son complementarias y `Y` es invariante por
`a * ε`, los ciclos de `a * ε` dentro de `Y` son exactamente las orbitas de `⟨ε, a⟩`. -/
theorem cycOn_eq_orb [Finite X] (ε a : Equiv.Perm X) (hε : ∀ x, ε (ε x) = x)
    (ha : ∀ x, a (a x) = x) (Y : X → Prop) (hY : ∀ x, Y x ↔ ¬ Y (ε x))
    (hpY : ∀ x, Y x ↔ Y (a (ε x))) : cycOn (a * ε) Y = orb {ε, a} := by
  obtain ⟨p, hp⟩ : ∃ p : Equiv.Perm X, p = a * ε := ⟨_, rfl⟩
  rw [← hp]
  have hpa : ∀ x, p x = a (ε x) := fun x => by rw [hp]; rfl
  have conj : ∀ x y, (cycSetoid p) x y → (cycSetoid p) (ε x) (ε y) := by
    intro x y h
    let T : Setoid X := ⟨fun x y => (cycSetoid p) (ε x) (ε y),
      ⟨fun _ => (cycSetoid p).refl _, fun h => (cycSetoid p).symm h,
        fun h1 h2 => (cycSetoid p).trans h1 h2⟩⟩
    refine eqvGen_le (s := T) ?_ h
    rintro u v rfl
    have e : p (ε (p u)) = ε u := by simp only [hpa, hε, ha]
    have := cyc_step p (ε (p u))
    rw [e] at this
    exact (cycSetoid p).symm this
  have hrefl : ∀ x, (cycSetoid p) x x ∨ (cycSetoid p) x (ε x) := fun x =>
    Or.inl ((cycSetoid p).refl x)
  have hsymm : ∀ x y, ((cycSetoid p) x y ∨ (cycSetoid p) x (ε y)) →
      ((cycSetoid p) y x ∨ (cycSetoid p) y (ε x)) := by
    intro x y h
    rcases h with h | h
    · exact Or.inl ((cycSetoid p).symm h)
    · refine Or.inr ((cycSetoid p).symm ?_)
      have := conj _ _ h
      rwa [hε] at this
  have htrans : ∀ x y z, ((cycSetoid p) x y ∨ (cycSetoid p) x (ε y)) →
      ((cycSetoid p) y z ∨ (cycSetoid p) y (ε z)) →
      ((cycSetoid p) x z ∨ (cycSetoid p) x (ε z)) := by
    intro x y z h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl ((cycSetoid p).trans h1 h2)
    · exact Or.inr ((cycSetoid p).trans h1 h2)
    · exact Or.inr ((cycSetoid p).trans h1 (conj _ _ h2))
    · refine Or.inl ((cycSetoid p).trans h1 ?_)
      have := conj _ _ h2
      rwa [hε] at this
  let R : Setoid X := ⟨fun x y => (cycSetoid p) x y ∨ (cycSetoid p) x (ε y),
    ⟨hrefl, fun {x y} h => hsymm x y h, fun {x y z} h1 h2 => htrans x y z h1 h2⟩⟩
  have hOR : ∀ x y, (orbSetoid {ε, a}) x y → (cycSetoid p) x y ∨ (cycSetoid p) x (ε y) := by
    refine orbSetoid_le (t := R) ?_
    intro g hg u
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h <;> rw [h]
    · exact Or.inr (by rw [hε])
    · refine Or.inr ?_
      have e : p (ε (a u)) = u := by simp only [hpa, hε, ha]
      have := cyc_step p (ε (a u))
      rw [e] at this
      exact (cycSetoid p).symm this
  have hCO : ∀ x y, (cycSetoid p) x y → (orbSetoid {ε, a}) x y := by
    intro x y h
    refine eqvGen_le (s := orbSetoid {ε, a}) ?_ h
    rintro u v rfl
    rw [hpa]
    exact (orbSetoid {ε, a}).trans (orb_step (S := {ε, a}) (g := ε) (by simp) u)
      (orb_step (S := {ε, a}) (g := a) (by simp) (ε u))
  have hpres : ∀ x y, (cycSetoid p) x y → (Y x ↔ Y y) := fun x y h =>
    cycSetoid_pres p Y (fun z => by rw [hpa]; exact hpY z) h
  let F : Quotient (Setoid.comap (Subtype.val : {x // Y x} → X) (cycSetoid p)) →
      Quotient (orbSetoid {ε, a}) :=
    Quotient.map Subtype.val (fun x y h => hCO x.1 y.1 h)
  have hinj : Function.Injective F := by
    intro q1 q2 h
    induction q1 using Quotient.inductionOn with
    | _ x =>
      induction q2 using Quotient.inductionOn with
      | _ y =>
        have ho : (orbSetoid {ε, a}) x.1 y.1 := Quotient.exact h
        rcases hOR _ _ ho with hc | hc
        · exact Quotient.sound hc
        · exfalso
          have h1 := (hpres _ _ hc).1 x.2
          exact ((hY y.1).1 y.2) h1
  have hsurj : Function.Surjective F := by
    intro c
    induction c using Quotient.inductionOn with
    | _ z =>
      by_cases hz : Y z
      · exact ⟨Quotient.mk _ ⟨z, hz⟩, rfl⟩
      · have hεz : Y (ε z) := by
          by_contra hc
          exact hz ((hY z).2 hc)
        refine ⟨Quotient.mk _ ⟨ε z, hεz⟩, Quotient.sound ?_⟩
        exact (orbSetoid {ε, a}).symm (orb_step (S := {ε, a}) (g := ε) (by simp) z)
  unfold cycOn orb ncs
  exact Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)

end Abstracto

end SpanAlt

/-! ### (B) La rotacion `sigma` y las caras -/

open SpanAlt

namespace TMENudos.Invariancia.GDiag

section Caras

variable {ι : Type} [DecidableEq ι] [Fintype ι] (D : GDiag ι)

/-- Rotacion antihoraria en el cruce (ver el docstring del modulo). -/
def sigmaFun (x : ι × Bool) : ι × Bool :=
  (D.partner x.1, xor x.2 (xor (D.sign x.1) (D.ovr x.1)))

/-- Inversa explicita de `sigmaFun`. -/
def sigmaInv (x : ι × Bool) : ι × Bool :=
  (D.partner x.1, xor x.2 (xor (D.sign x.1) (!D.ovr x.1)))

/-- La rotacion `sigma`: un 4-ciclo en los extremos de cada cruce. -/
def sigma : Equiv.Perm (ι × Bool) where
  toFun := D.sigmaFun
  invFun := D.sigmaInv
  left_inv := by
    rintro ⟨j, s⟩
    simp only [sigmaInv, sigmaFun, D.partner_partner, D.sign_partner, D.ovr_partner]
    cases s <;> cases D.sign j <;> cases D.ovr j <;> simp
  right_inv := by
    rintro ⟨j, s⟩
    simp only [sigmaInv, sigmaFun, D.partner_partner, D.sign_partner, D.ovr_partner]
    cases s <;> cases D.sign j <;> cases D.ovr j <;> simp

theorem sigma_apply (j : ι) (s : Bool) :
    D.sigma (j, s) = (D.partner j, xor s (xor (D.sign j) (D.ovr j))) := rfl

theorem sigma_fst (x : ι × Bool) : (D.sigma x).1 = D.partner x.1 := rfl

/-- `sigma^2` es el paso por el cruce, `a * b`. -/
theorem sigma_sigma (x : ι × Bool) : D.sigma (D.sigma x) = (x.1, !x.2) := by
  obtain ⟨j, s⟩ := x
  simp only [sigma_apply, D.partner_partner, D.sign_partner, D.ovr_partner]
  cases s <;> cases D.sign j <;> cases D.ovr j <;> simp

theorem sigma_eq_a (x : ι × Bool) (h : D.ovr x.1 = false) : D.sigma x = D.a x := by
  obtain ⟨j, s⟩ := x
  simp only at h
  simp [sigma_apply, a_apply, h]

theorem sigma_eq_b (x : ι × Bool) (h : D.ovr x.1 = true) : D.sigma x = D.b x := by
  obtain ⟨j, s⟩ := x
  simp only at h
  cases hs : D.sign j <;> simp [sigma_apply, b_apply, h, hs]

/-- Letra superior (`ovr = true`). -/
def OvrT (x : ι × Bool) : Prop := D.ovr x.1 = true

/-- Alternancia: las letras consecutivas alternan superior/inferior. -/
def Alt : Prop := ∀ j, D.ovr (D.next j) = !D.ovr j

variable {D}

theorem ovr_eps (halt : D.Alt) (x : ι × Bool) : D.ovr (D.eps x).1 = !D.ovr x.1 := by
  obtain ⟨j, _ | _⟩ := x
  · have h := halt (D.next.symm j)
    rw [Equiv.apply_symm_apply] at h
    simp only [eps_false, prev]
    rw [h]
    simp
  · simpa [eps_true] using halt j

theorem ovrT_eps (halt : D.Alt) (x : ι × Bool) : D.OvrT x ↔ ¬ D.OvrT (D.eps x) := by
  unfold OvrT
  rw [ovr_eps halt]
  cases D.ovr x.1 <;> simp

theorem ovrT_aeps (halt : D.Alt) (x : ι × Bool) : D.OvrT x ↔ D.OvrT (D.a (D.eps x)) := by
  have h := ovr_eps halt x
  have e : (D.a (D.eps x)).1 = D.partner (D.eps x).1 := rfl
  unfold OvrT
  rw [e, D.ovr_partner, h]
  cases D.ovr x.1 <;> simp

theorem ovrT_beps (halt : D.Alt) (x : ι × Bool) : D.OvrT x ↔ D.OvrT (D.b (D.eps x)) := by
  have h := ovr_eps halt x
  have e : (D.b (D.eps x)).1 = D.partner (D.eps x).1 := rfl
  unfold OvrT
  rw [e, D.ovr_partner, h]
  cases D.ovr x.1 <;> simp

theorem ovrT_phi (halt : D.Alt) (x : ι × Bool) : D.OvrT x ↔ D.OvrT ((D.sigma * D.eps) x) := by
  have h := ovr_eps halt x
  have e : ((D.sigma * D.eps) x).1 = D.partner (D.eps x).1 := rfl
  unfold OvrT
  rw [e, D.ovr_partner, h]
  cases D.ovr x.1 <;> simp

/-- **Las caras de un diagrama alternante** (ciclos de `sigma * eps`) son
`lazos allA + lazos allB`. -/
theorem caras_eq_of_alternante (D : GDiag ι) (hfree : D.free = 0) (halt : D.Alt) :
    cyc (D.sigma * D.eps) = D.lazos D.allA + D.lazos D.allB := by
  rw [lazos_allA_eq D hfree, lazos_allB_eq D hfree]
  have hinv : ∀ x, D.OvrT x → D.OvrT ((D.sigma * D.eps) x) := fun x hx => (ovrT_phi halt x).1 hx
  have hinv' : ∀ x, ¬ D.OvrT x → ¬ D.OvrT ((D.sigma * D.eps) x) := fun x hx h =>
    hx ((ovrT_phi halt x).2 h)
  rw [cyc_split (D.sigma * D.eps) D.OvrT (ovrT_phi halt)]
  congr 1
  · rw [cycOn_congr (D.sigma * D.eps) (D.a * D.eps) D.OvrT hinv ?_]
    · exact cycOn_eq_orb D.eps D.a D.eps_eps (D.sm_sm _ _) D.OvrT (ovrT_eps halt)
        (ovrT_aeps halt)
    · intro x hx
      have h1 : D.ovr (D.eps x).1 = false := by
        rw [ovr_eps halt]; unfold OvrT at hx; simp [hx]
      exact D.sigma_eq_a _ h1
  · rw [cycOn_congr (D.sigma * D.eps) (D.b * D.eps) (fun x => ¬ D.OvrT x) hinv' ?_]
    · refine cycOn_eq_orb D.eps D.b D.eps_eps (D.sm_sm _ _) (fun x => ¬ D.OvrT x) ?_ ?_
      · intro x
        have := ovrT_eps halt x
        change ¬ D.OvrT x ↔ ¬¬ D.OvrT (D.eps x)
        tauto
      · intro x
        exact not_congr (ovrT_beps halt x)
    · intro x hx
      have h1 : D.ovr (D.eps x).1 = true := by
        rw [ovr_eps halt]; unfold OvrT at hx; simpa using hx
      exact D.sigma_eq_b _ h1

/-- Planaridad (formula de Euler): caras `= c + 2`. -/
def PlanarD (D : GDiag ι) : Prop :=
  cyc (D.sigma * D.eps) = Fintype.card D.Cross + 2

/-- **Igualdad de genero** para diagramas alternantes planares. -/
theorem hgen_of_alternante_planar (D : GDiag ι) (hfree : D.free = 0) (halt : D.Alt)
    (hpl : D.PlanarD) :
    D.lazos D.allA + D.lazos D.allB = Fintype.card D.Cross + 2 := by
  rw [← caras_eq_of_alternante D hfree halt]
  exact hpl

end Caras

end TMENudos.Invariancia.GDiag

/-! ### (C) Sanidad: el trebol -/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia

/-- El trebol es alternante. -/
theorem alt_trefoil : (ofWord trefoil wf_trefoil).Alt := by
  unfold GDiag.Alt
  decide +kernel

/-- Las caras del trebol: `5 = 3 + 2`, es decir, el trebol (alternante) es planar. -/
theorem planarD_trefoil : (ofWord trefoil wf_trefoil).PlanarD := by
  obtain ⟨hc, hA, hB⟩ := sanidad_trefoil
  have hfree : (ofWord trefoil wf_trefoil).free = 0 := by
    have : trefoil.length ≠ 0 := by decide +kernel
    change (if trefoil.length = 0 then 1 else 0) = 0
    simp [this]
  unfold GDiag.PlanarD
  rw [GDiag.caras_eq_of_alternante _ hfree alt_trefoil, hA, hB, hc]

/-- Igualdad de genero del trebol obtenida del teorema general. -/
theorem hgen_trefoil :
    (ofWord trefoil wf_trefoil).lazos (ofWord trefoil wf_trefoil).allA +
      (ofWord trefoil wf_trefoil).lazos (ofWord trefoil wf_trefoil).allB =
      Fintype.card (ofWord trefoil wf_trefoil).Cross + 2 := by
  obtain ⟨hc, hA, hB⟩ := sanidad_trefoil
  rw [hA, hB, hc]

end TMENudos.Puente

#print axioms SpanAlt.cycOn_eq_orb
#print axioms SpanAlt.cyc_split
#print axioms TMENudos.Invariancia.GDiag.sigma_sigma
#print axioms TMENudos.Invariancia.GDiag.caras_eq_of_alternante
#print axioms TMENudos.Invariancia.GDiag.hgen_of_alternante_planar
#print axioms TMENudos.Puente.alt_trefoil
#print axioms TMENudos.Puente.planarD_trefoil
