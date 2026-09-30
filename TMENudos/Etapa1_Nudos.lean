import TMENudos.Etapa1_JonesR3
import TMENudos.Etapa1_Puente
import TMENudos.Etapa1_GaussWord

/-!
# Etapa 1: prototipo de nudos virtuales concretos y teoremas de no equivalencia

Se empaqueta un diagrama abstracto `GDiag ι` con su tipo de índices (`Diag`, vive en `Type 1`),
se define la relación de equivalencia generada por isomorfismo y por los movimientos de
Reidemeister que ya están demostrados (`GRel`), y el cociente `NudoV`. El polinomio de Jones
baja al cociente (`jones_rel`), y con él se prueban tres teoremas sobre nudos concretos.

## ALCANCE (leer antes de citar)

* Los movimientos de `GRel` son los **abstractos** sobre `GDiag` (permutaciones `next` y `partner`
  arbitrarias, sin exigir planaridad): el cociente `NudoV` es, por tanto, un cociente de tipo
  **nudos virtuales** (sin el movimiento detour), no el de nudos clásicos.
* Los teoremas `trefoilV_ne_unknotV`, `trefoilV_ne_mirror` y `granny_ne_square` dicen que las
  clases son distintas en ese cociente. Como los movimientos de Reidemeister clásicos son un caso
  particular de los de `GRel`, una equivalencia clásica daría una relación `GRel`; luego estas
  clases tampoco son equivalentes como nudos clásicos. (Esa lectura clásica es una consecuencia
  informal: aquí no se define el cociente de nudos clásicos ni el vínculo con `Knot`.)
* Movimientos que **no** están en `GRel`: R2 sobre la misma arista (`e = f`), R2 y R1 entre
  circunferencias libres (`free`), y cualquier movimiento no demostrado invariante. Añadir más
  constructores exige demostrar la invariancia del Jones para cada uno.
* NO se define ni se afirma nada sobre la suma conexa como operación en `NudoV`: `grannyV` y
  `squareV` son las clases de los diagramas de las palabras concatenadas (`Word.concat`), y no se
  demuestra que esa construcción esté bien definida sobre clases.
-/

namespace TMENudos.Nudos

open TMENudos.Invariancia TMENudos.Gauss TMENudos.Puente

/-- Un diagrama abstracto junto con su tipo de índices. -/
structure Diag : Type 1 where
  ι : Type
  [dec : DecidableEq ι]
  [fin : Fintype ι]
  D : GDiag ι

attribute [instance] Diag.dec Diag.fin

/-- Relación de equivalencia generada por isomorfismo y por los movimientos R1, R1 libre, R2, R3. -/
inductive GRel : Diag → Diag → Prop
  | refl (a : Diag) : GRel a a
  | symm {a b : Diag} : GRel a b → GRel b a
  | trans {a b c : Diag} : GRel a b → GRel b c → GRel a c
  | iso {ι ι' : Type} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']
      (D : GDiag ι) (e : ι ≃ ι') : GRel (Diag.mk ι D) (Diag.mk ι' (D.map e))
  | r1 {ι : Type} [DecidableEq ι] [Fintype ι] [Nonempty ι]
      (D : GDiag ι) (e : ι) (o1 s : Bool) :
      GRel (Diag.mk ι D) (Diag.mk (ι ⊕ Bool) (GDiag.r1 D e o1 s))
  | r1F {ι : Type} [DecidableEq ι] [Fintype ι]
      (D : GDiag ι) (hfree : 1 ≤ D.free) (o1 s : Bool) :
      GRel (Diag.mk ι D) (Diag.mk (ι ⊕ Bool) (GDiag.r1F D o1 s))
  | r2 {ι : Type} [DecidableEq ι] [Fintype ι]
      (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov par s : Bool) :
      GRel (Diag.mk ι D) (Diag.mk (ι ⊕ (Bool × Bool)) (GDiag.r2 D e f hef ov par s))
  | r3 {ι : Type} [DecidableEq ι] [Fintype ι]
      (D : GDiag ι) (e : Fin 3 → ι) (he : Function.Injective e) (o ovc sgc : Fin 3 → Bool)
      (hv : R3.validR3 (o 0) (o 1) (o 2) (sgc 0) (sgc 1) (sgc 2) = true) :
      GRel (Diag.mk (ι ⊕ R3.Lt) (GDiag.tri D e he o ovc sgc))
        (Diag.mk (ι ⊕ R3.Lt) (GDiag.tri D e he (fun i => !o i) ovc sgc))

/-- Jones de un diagrama empaquetado. -/
noncomputable def Diag.jones {K : Type*} [Field K] (A : K) (d : Diag) : K := d.D.jones A

/-- **El Jones es invariante por `GRel`.** -/
theorem jones_rel {K : Type*} [Field K] {A : K} (hA : A ≠ 0) {a b : Diag} (h : GRel a b) :
    a.jones A = b.jones A := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | iso D e => exact (GDiag.jones_map A D e).symm
  | r1 D e o1 s => exact (GDiag.jones_r1 A hA D e o1 s).symm
  | r1F D hfree o1 s => exact (GDiag.jones_r1F A hA D hfree o1 s).symm
  | r2 D e f hef ov par s => exact (GDiag.jones_r2 A hA D e f hef ov par s).symm
  | r3 D e he o ovc sgc hv => exact GDiag.jones_tri D e he o ovc sgc A hA hv

theorem GRel.equivalence : Equivalence GRel :=
  ⟨GRel.refl, GRel.symm, GRel.trans⟩

instance diagSetoid : Setoid Diag := ⟨GRel, GRel.equivalence⟩

/-- Nudos (virtuales, en el sentido del alcance) = diagramas módulo `GRel`. -/
abbrev NudoV : Type 1 := Quotient diagSetoid

/-- Jones de una clase, para `A ≠ 0`. -/
noncomputable def NudoV.jones {K : Type*} [Field K] (A : K) (hA : A ≠ 0) : NudoV → K :=
  Quotient.lift (Diag.jones A) fun _ _ h => jones_rel hA h

theorem NudoV.jones_mk {K : Type*} [Field K] (A : K) (hA : A ≠ 0) (d : Diag) :
    NudoV.jones A hA (Quotient.mk diagSetoid d) = d.jones A := rfl

/-! ### Nudos concretos -/

theorem wf_nil : Word.wf ([] : Word) = true := by decide

/-- El nudo trivial: la clase del diagrama de la palabra vacía (una circunferencia libre). -/
def unknotV : NudoV := Quotient.mk diagSetoid (Diag.mk _ (ofWord [] wf_nil))

def trefoilV : NudoV := Quotient.mk diagSetoid (Diag.mk _ (ofWord trefoil wf_trefoil))

/-- Imagen especular del trébol. -/
def trefoilV' : NudoV :=
  Quotient.mk diagSetoid (Diag.mk _ (ofWord (Word.swap trefoil) wf_swap_trefoil))

def grannyV : NudoV :=
  Quotient.mk diagSetoid (Diag.mk _ (ofWord (Word.concat trefoil trefoil) wf_concat_trefoil))

def squareV : NudoV :=
  Quotient.mk diagSetoid
    (Diag.mk _ (ofWord (Word.concat trefoil (Word.swap trefoil)) wf_concat_trefoil_swap))

theorem jones_unknot_word {K : Type*} [Field K] (A : K) : Word.jones A ([] : Word) = 1 := by
  simp [Word.jones, Word.writhe, Word.bracket, Word.terms, Word.crossings, Word.allStates,
    Word.loops]

theorem two_ne_zero' : (2 : ℚ) ≠ 0 := by norm_num

/-- El Jones en `A = 2` del trébol es `(1/2)^4 + (1/2)^12 - (1/2)^16`. -/
theorem jones_trefoilV :
    NudoV.jones (2 : ℚ) two_ne_zero' trefoilV = (2⁻¹) ^ 4 + (2⁻¹) ^ 12 - (2⁻¹) ^ 16 :=
  jones_ofWord_trefoil (2 : ℚ) two_ne_zero'

theorem jones_trefoilV' :
    NudoV.jones (2 : ℚ) two_ne_zero' trefoilV' = 2 ^ 4 + 2 ^ 12 - 2 ^ 16 :=
  jones_ofWord_swap_trefoil (2 : ℚ) two_ne_zero'

theorem jones_unknotV : NudoV.jones (2 : ℚ) two_ne_zero' unknotV = 1 := by
  change (ofWord ([] : Word) wf_nil).jones (2 : ℚ) = 1
  rw [jones_ofWord, jones_unknot_word]

/-- **El trébol no es trivial.** -/
theorem trefoilV_ne_unknotV : trefoilV ≠ unknotV := by
  intro h
  have := congrArg (NudoV.jones (2 : ℚ) two_ne_zero') h
  rw [jones_trefoilV, jones_unknotV] at this
  norm_num at this

/-- **El trébol es quiral**: distinto de su imagen especular. -/
theorem trefoilV_ne_mirror : trefoilV ≠ trefoilV' := by
  intro h
  have := congrArg (NudoV.jones (2 : ℚ) two_ne_zero') h
  rw [jones_trefoilV, jones_trefoilV'] at this
  norm_num at this

/-- **Nudo de la abuela ≠ nudo cuadrado.** -/
theorem granny_ne_square : grannyV ≠ squareV := by
  intro h
  have := congrArg (NudoV.jones (2 : ℚ) two_ne_zero') h
  exact jones_granny_ne_square
    (by
      have h1 := jones_ofWord (Word.concat trefoil trefoil) wf_concat_trefoil (2 : ℚ)
      have h2 := jones_ofWord (Word.concat trefoil (Word.swap trefoil))
        wf_concat_trefoil_swap (2 : ℚ)
      rw [← h1, ← h2]
      exact this)

#print axioms jones_rel
#print axioms trefoilV_ne_unknotV
#print axioms trefoilV_ne_mirror
#print axioms granny_ne_square

end TMENudos.Nudos
