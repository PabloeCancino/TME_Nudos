import Mathlib
import TMENudos.Conway
import TMENudos.Etapa1_Nudos

namespace TMENudos.ConwayTabla

open TMENudos.Gauss TMENudos.Puente TMENudos.Invariancia TMENudos.Nudos TMENudos.Conway

/-- Valor del Jones en `A = 2` de la palabra de Conway. -/
def jv (a : List ℕ) : ℚ := Word.jones (2 : ℚ) (conwayWord a)

/-- Tabla: 3_1, 4_1, 5_1, 5_2, 6_1, 6_2, 6_3, 7_1 a 7_5 y dos de 7 cruces mas
(formas de Conway, un representante de cada una). -/
def tabla : List (List ℕ) :=
  [[3], [2,2], [5], [3,2], [4,2], [3,1,2], [2,1,1,2], [7], [5,2], [4,3], [3,1,3], [3,2,2],
   [2,2,1,2], [2,1,1,1,2]]

theorem tabla_ok : tabla.all okCase = true := by decide +kernel

theorem tabla_jones_nodup : (tabla.map jv).Nodup := by decide +kernel

theorem wf_of_mem {a : List ℕ} (h : a ∈ tabla) : Word.wf (conwayWord a) = true := by
  have := List.all_eq_true.mp tabla_ok a h
  simp only [okCase, Bool.and_eq_true] at this
  exact this.1.1.1.1

/-- Dos formas distintas de la tabla NO son `GRel`-equivalentes (por el Jones en `A = 2`). -/
theorem tabla_distintos {a b : List ℕ} (ha : a ∈ tabla) (hb : b ∈ tabla) (hab : a ≠ b) :
    ¬ GRel (Diag.mk _ (ofWord (conwayWord a) (wf_of_mem ha)))
           (Diag.mk _ (ofWord (conwayWord b) (wf_of_mem hb))) := by
  intro h
  have h1 := jones_rel (A := (2 : ℚ)) two_ne_zero' h
  simp only [Diag.jones, jones_ofWord] at h1
  have hinj := List.inj_on_of_nodup_map tabla_jones_nodup ha hb
  exact hab (hinj h1)

/-! ### Equivalencias (iguales): isomorfismo de diagramas de Gauss (solo rotacion y renombrado)

Esto NO es un camino de movimientos R1/R2/R3: es `GRel.iso`, es decir, el mismo diagrama
abstracto con otro punto de partida y otras etiquetas. Cada certificado se comprueba con
`decide +kernel` sobre `Fin m` concreto. -/

open TMENudos.Invariancia in
/-- Un isomorfismo explicito `e` entre dos `GDiag` (compatible con `next`, `partner`, `ovr`,
`sign`, `free`) da `GRel`. -/
theorem grel_of_iso {ι ι' : Type} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']
    (D : GDiag ι) (D' : GDiag ι') (e : ι ≃ ι')
    (hn : ∀ i, e (D.next i) = D'.next (e i)) (hp : ∀ i, e (D.partner i) = D'.partner (e i))
    (ho : ∀ i, D'.ovr (e i) = D.ovr i) (hs : ∀ i, D'.sign (e i) = D.sign i)
    (hf : D.free = D'.free) :
    GRel (Diag.mk ι D) (Diag.mk ι' D') := by
  have h : D.map e = D' := by
    obtain ⟨n1, p1, o1, s1, _, _, _, _, f1⟩ := D
    obtain ⟨n2, p2, o2, s2, _, _, _, _, f2⟩ := D'
    simp only at hn hp ho hs hf
    subst hf
    have hn' : e.permCongr n1 = n2 := by
      ext j
      have := hn (e.symm j)
      simp only [Equiv.apply_symm_apply] at this
      simp [Equiv.permCongr_apply, this]
    have hp' : (fun j => e (p1 (e.symm j))) = p2 := by
      funext j
      have := hp (e.symm j)
      simpa using this
    have ho' : (fun j => o1 (e.symm j)) = o2 := by
      funext j
      have := ho (e.symm j)
      simpa using this.symm
    have hs' : (fun j => s1 (e.symm j)) = s2 := by
      funext j
      have := hs (e.symm j)
      simpa using this.symm
    simp only [GDiag.map]
    congr
  rw [← h]
  exact GRel.iso D e

/-- Desplazamiento cíclico `i ↦ (i + s) % m₂` de `Fin m₁` a `Fin m₂`. -/
def rotFn (m₁ m₂ s : ℕ) (hm : 0 < m₂) (i : Fin m₁) : Fin m₂ :=
  ⟨(i.1 + s) % m₂, Nat.mod_lt _ hm⟩

/-- Certificado de isomorfismo para dos palabras de Conway (rotacion `s` del punto de partida). -/
theorem grel_rot (w₁ w₂ : Word) (h₁ : Word.wf w₁ = true) (h₂ : Word.wf w₂ = true) (s : ℕ)
    (hm : 0 < w₂.length)
    (hb : Function.Bijective (rotFn w₁.length w₂.length s hm))
    (hn : ∀ i : Fin w₁.length, rotFn _ _ s hm (finRotate _ i) =
      finRotate _ (rotFn _ _ s hm i))
    (hp : ∀ i : Fin w₁.length, rotFn _ _ s hm ((ofWord w₁ h₁).partner i) =
      (ofWord w₂ h₂).partner (rotFn _ _ s hm i))
    (ho : ∀ i : Fin w₁.length, (ofWord w₂ h₂).ovr (rotFn _ _ s hm i) = (ofWord w₁ h₁).ovr i)
    (hs : ∀ i : Fin w₁.length, (ofWord w₂ h₂).sign (rotFn _ _ s hm i) = (ofWord w₁ h₁).sign i)
    (hf : (ofWord w₁ h₁).free = (ofWord w₂ h₂).free) :
    GRel (Diag.mk _ (ofWord w₁ h₁)) (Diag.mk _ (ofWord w₂ h₂)) :=
  grel_of_iso _ _ (Equiv.ofBijective _ hb) hn hp ho hs hf

theorem wf_223 : Word.wf (conwayWord [2, 2, 3]) = true := by decide +kernel
theorem wf_322 : Word.wf (conwayWord [3, 2, 2]) = true := by decide +kernel

/-- **Certificado de igualdad (por isomorfismo):** `C(2,2,3)` y `C(3,2,2)` (misma `p = 17`,
`q q' = 35 ≡ 1 (mod 17)`) dan diagramas `GRel`-equivalentes. -/
theorem grel_223_322 :
    GRel (Diag.mk _ (ofWord (conwayWord [2, 2, 3]) wf_223))
         (Diag.mk _ (ofWord (conwayWord [3, 2, 2]) wf_322)) :=
  grel_rot _ _ wf_223 wf_322 10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end TMENudos.ConwayTabla

#print axioms TMENudos.ConwayTabla.tabla_ok
#print axioms TMENudos.ConwayTabla.tabla_jones_nodup
#print axioms TMENudos.ConwayTabla.tabla_distintos
#print axioms TMENudos.ConwayTabla.grel_223_322
