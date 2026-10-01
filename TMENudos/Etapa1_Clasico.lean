import TMENudos.Etapa1_Planaridad
import TMENudos.Etapa1_Nudos

/-!
# Etapa 1 (Opción 2): nudos CLÁSICOS como diagramas planares módulo movimientos entre planares

Capa paralela (NO la importa `TMENudos.lean`).

## Definición
* `ClassicalDiagram := {w : Word // Word.wf w = true ∧ planar w}`: palabras de Gauss firmadas bien
  formadas cuyo mapa combinatorio es planar (`Etapa1_Planaridad.planar`, género 0 exacto).
* `GStep`: los movimientos ELEMENTALES de `Etapa1_Nudos.GRel` (isomorfismo, R1, R1 libre, R2, R3),
  con exactamente los mismos cinco constructores y datos, SIN los constructores de cierre
  (`refl`, `symm`, `trans`). `GRel` empaqueta movimientos y cierre en un solo inductivo, así que
  no se puede extraer de él el paso elemental; `GStep.toGRel` prueba `GStep ⊆ GRel`, y todas las
  invariancias ya demostradas (`jones_rel`) se reutilizan a través de esa inclusión.
* `StepW a b`: hay un movimiento elemental `GStep` desde `ofWord a` hasta un diagrama
  isomorfo a `ofWord b` (el resultado de R1/R2/R3 tiene otro tipo de índices, así que se compara
  salvo isomorfismo `IsoD`).
* La relación clásica `ClassicalSetoid` es el cierre reflexivo-simétrico-transitivo
  (`Relation.EqvGen`) de `StepW` restringido a `ClassicalDiagram`: **cada paso intermedio es un
  diagrama planar**. `ClassicalKnot` es el cociente.

## Por qué ésta es la noción clásica y no la virtual
`GRel` (y `NudoV` de `Etapa1_Nudos`) es la equivalencia generada por movimientos ABSTRACTOS sobre
diagramas sin exigir planaridad: una cadena de movimientos puede salir de los diagramas planares
(pasar por diagramas virtuales) y volver. Eso da nudos VIRTUALES. Aquí el cociente se toma sobre
el subtipo de planares y la relación sólo une pasos `a → b` con AMBOS extremos planares; una
cadena `a ~ … ~ b` pasa solo por planares. (Un teorema de Goussarov-Polyak-Viro dice que, para
diagramas clásicos, ambas nociones acaban coincidiendo, pero NO se usa ni se prueba aquí: la
definición es la clásica por construcción.)

## Resultados
* `ClassicalKnot.jones`: el Jones baja al cociente (`jones_step`, reutiliza `jones_rel`).
* `trefoilC_ne_mirrorC`: trébol ≠ espejo en `ClassicalKnot`, por Jones en `A = 2`
  (`4111/65536` frente a `-61424`).
* `trefoilC_ne_unknotC`.

## Límites (NO probado)
* La imagen especular `swap` como operación sobre `ClassicalKnot` NO se define: habría que
  probar que `swap` preserva la planaridad y los pasos en general. Solo se prueba para el diagrama
  concreto del trébol (`planar_swap_trefoil`).
* La suma conexa clásica NO se intenta: exige pegar los dos diagramas en la MISMA cara (la
  concatenación de palabras `Word.concat` no determina en qué cara se pega).
* No se prueba que `StepW` sea no trivial más allá de los isomorfismos (no se exhibe un R1/R2/R3
  concreto entre dos palabras); la definición es correcta por construcción, pero este archivo no
  la ejercita con un movimiento.
-/

namespace TMENudos.Clasico

open TMENudos.Invariancia TMENudos.Gauss TMENudos.Puente TMENudos.Nudos TMENudos.Planaridad

/-- Movimientos elementales: los cinco constructores de movimiento de `GRel`, sin el cierre. -/
inductive GStep : Diag → Diag → Prop
  | iso {ι ι' : Type} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']
      (D : GDiag ι) (e : ι ≃ ι') : GStep (Diag.mk ι D) (Diag.mk ι' (D.map e))
  | r1 {ι : Type} [DecidableEq ι] [Fintype ι] [Nonempty ι]
      (D : GDiag ι) (e : ι) (o1 s : Bool) :
      GStep (Diag.mk ι D) (Diag.mk (ι ⊕ Bool) (GDiag.r1 D e o1 s))
  | r1F {ι : Type} [DecidableEq ι] [Fintype ι]
      (D : GDiag ι) (hfree : 1 ≤ D.free) (o1 s : Bool) :
      GStep (Diag.mk ι D) (Diag.mk (ι ⊕ Bool) (GDiag.r1F D o1 s))
  | r2 {ι : Type} [DecidableEq ι] [Fintype ι]
      (D : GDiag ι) (e f : ι) (hef : e ≠ f) (ov par s : Bool) :
      GStep (Diag.mk ι D) (Diag.mk (ι ⊕ (Bool × Bool)) (GDiag.r2 D e f hef ov par s))
  | r3 {ι : Type} [DecidableEq ι] [Fintype ι]
      (D : GDiag ι) (e : Fin 3 → ι) (he : Function.Injective e) (o ovc sgc : Fin 3 → Bool)
      (hv : R3.validR3 (o 0) (o 1) (o 2) (sgc 0) (sgc 1) (sgc 2) = true) :
      GStep (Diag.mk (ι ⊕ R3.Lt) (GDiag.tri D e he o ovc sgc))
        (Diag.mk (ι ⊕ R3.Lt) (GDiag.tri D e he (fun i => !o i) ovc sgc))

/-- Cada movimiento elemental es una instancia de `GRel` (mismo constructor). -/
theorem GStep.toGRel {a b : Diag} (h : GStep a b) : GRel a b := by
  cases h with
  | iso D e => exact GRel.iso D e
  | r1 D e o1 s => exact GRel.r1 D e o1 s
  | r1F D hfree o1 s => exact GRel.r1F D hfree o1 s
  | r2 D e f hef ov par s => exact GRel.r2 D e f hef ov par s
  | r3 D e he o ovc sgc hv => exact GRel.r3 D e he o ovc sgc hv

/-- Isomorfismo de diagramas empaquetados: una biyección de índices que transporta la estructura. -/
def IsoD (d d' : Diag) : Prop := ∃ e : d.ι ≃ d'.ι, d'.D = d.D.map e

theorem IsoD.toGRel {d d' : Diag} (h : IsoD d d') : GRel d d' := by
  obtain ⟨ι, D⟩ := d
  obtain ⟨ι', D'⟩ := d'
  obtain ⟨e, he⟩ := h
  have he' : D' = D.map e := he
  have h1 := GRel.iso D e
  rw [← he'] at h1
  exact h1

/-- Un paso entre palabras: movimiento elemental desde `ofWord a`, salvo isomorfismo, hasta
    `ofWord b`. -/
def StepW (a b : Word) (ha : Word.wf a = true) (hb : Word.wf b = true) : Prop :=
  ∃ d : Diag, GStep (Diag.mk _ (ofWord a ha)) d ∧ IsoD d (Diag.mk _ (ofWord b hb))

theorem StepW.toGRel {a b : Word} {ha : Word.wf a = true} {hb : Word.wf b = true} (h : StepW a b ha hb) :
    GRel (Diag.mk _ (ofWord a ha)) (Diag.mk _ (ofWord b hb)) := by
  obtain ⟨d, h1, h2⟩ := h
  exact GRel.trans h1.toGRel h2.toGRel

/-! ### Diagramas y nudos clásicos -/

/-- **Diagrama clásico**: palabra de Gauss firmada bien formada y planar. -/
def ClassicalDiagram : Type := {w : Word // Word.wf w = true ∧ planar w}

/-- Paso entre dos diagramas clásicos (ambos extremos planares por construcción). -/
def ClStep (a b : ClassicalDiagram) : Prop := StepW a.1 b.1 a.2.1 b.2.1

/-- La equivalencia clásica: cierre de equivalencia de `ClStep` (cadenas SOLO por planares). -/
def ClassicalSetoid : Setoid ClassicalDiagram := Relation.EqvGen.setoid ClStep

/-- **Nudos clásicos** (Opción 2): diagramas planares módulo movimientos entre planares. -/
def ClassicalKnot : Type := Quotient ClassicalSetoid

/-- Jones de un diagrama clásico (el de su palabra). -/
def ClassicalDiagram.jones {K : Type*} [Field K] (A : K) (c : ClassicalDiagram) : K :=
  Word.jones A c.1

/-- El Jones es invariante por un paso clásico (reutiliza `jones_rel`). -/
theorem jones_step {K : Type*} [Field K] {A : K} (hA : A ≠ 0) {a b : ClassicalDiagram}
    (h : ClStep a b) : a.jones A = b.jones A := by
  have h1 : (ofWord a.1 a.2.1).jones A = (ofWord b.1 b.2.1).jones A :=
    jones_rel hA (StepW.toGRel h)
  unfold ClassicalDiagram.jones
  rw [jones_ofWord a.1 a.2.1 A, jones_ofWord b.1 b.2.1 A] at h1
  exact h1

/-- El Jones es invariante por la equivalencia clásica. -/
theorem jones_eqv {K : Type*} [Field K] {A : K} (hA : A ≠ 0) {a b : ClassicalDiagram}
    (h : ClassicalSetoid.r a b) : a.jones A = b.jones A := by
  induction h with
  | rel x y hxy => exact jones_step hA hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **El Jones baja a los nudos clásicos.** -/
noncomputable def ClassicalKnot.jones {K : Type*} [Field K] (A : K) (hA : A ≠ 0) :
    ClassicalKnot → K :=
  Quotient.lift (ClassicalDiagram.jones A) fun _ _ h => jones_eqv hA h

theorem ClassicalKnot.jones_mk {K : Type*} [Field K] (A : K) (hA : A ≠ 0) (c : ClassicalDiagram) :
    ClassicalKnot.jones A hA (Quotient.mk ClassicalSetoid c) = c.jones A := rfl

/-! ### Nudos concretos -/

/-- El trébol derecho como diagrama clásico (`planar_trefoil` por `decide`). -/
def trefoilD : ClassicalDiagram := ⟨trefoil, wf_trefoil, planar_trefoil⟩

/-- Su imagen especular `swap` como diagrama clásico. Solo se prueba la planaridad de ESTE
    diagrama (`planar_swap_trefoil`); no que `swap` preserve la planaridad en general. -/
def mirrorD : ClassicalDiagram := ⟨Word.swap trefoil, wf_swap_trefoil, planar_swap_trefoil⟩

/-- El diagrama vacío (nudo trivial). -/
def unknotD : ClassicalDiagram := ⟨[], wf_nil, Or.inl rfl⟩

def trefoilC : ClassicalKnot := Quotient.mk ClassicalSetoid trefoilD
def mirrorC : ClassicalKnot := Quotient.mk ClassicalSetoid mirrorD
def unknotC : ClassicalKnot := Quotient.mk ClassicalSetoid unknotD

theorem jones_trefoilC :
    ClassicalKnot.jones (2 : ℚ) two_ne_zero' trefoilC = 4111 / 65536 := by
  change Word.jones (2 : ℚ) trefoil = _
  rw [← jones_ofWord trefoil wf_trefoil, jones_ofWord_trefoil (2 : ℚ) two_ne_zero']
  norm_num

theorem jones_mirrorC :
    ClassicalKnot.jones (2 : ℚ) two_ne_zero' mirrorC = -61424 := by
  change Word.jones (2 : ℚ) (Word.swap trefoil) = _
  rw [← jones_ofWord (Word.swap trefoil) wf_swap_trefoil,
    jones_ofWord_swap_trefoil (2 : ℚ) two_ne_zero']
  norm_num

theorem jones_unknotC : ClassicalKnot.jones (2 : ℚ) two_ne_zero' unknotC = 1 := by
  change Word.jones (2 : ℚ) ([] : Word) = 1
  exact jones_unknot_word _

/-- **El trébol es quiral como nudo CLÁSICO**: trébol derecho ≠ izquierdo en `ClassicalKnot`. -/
theorem trefoilC_ne_mirrorC : trefoilC ≠ mirrorC := by
  intro h
  have := congrArg (ClassicalKnot.jones (2 : ℚ) two_ne_zero') h
  rw [jones_trefoilC, jones_mirrorC] at this
  norm_num at this

/-- **El trébol no es trivial como nudo clásico.** -/
theorem trefoilC_ne_unknotC : trefoilC ≠ unknotC := by
  intro h
  have := congrArg (ClassicalKnot.jones (2 : ℚ) two_ne_zero') h
  rw [jones_trefoilC, jones_unknotC] at this
  norm_num at this

#print axioms jones_eqv
#print axioms ClassicalKnot.jones
#print axioms trefoilC_ne_mirrorC
#print axioms trefoilC_ne_unknotC

end TMENudos.Clasico
