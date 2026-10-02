import Mathlib
import TMENudos.SpanNoNugatorio
import TMENudos.SpanAlternante

/-!
# Etapa S6: minimalidad de cruces para diagramas alternantes planares no nugatorios

Ensamblaje de las etapas anteriores del teorema del span:

* `SpanAlternante.hgen_of_alternante_planar`: un diagrama alternante con `PlanarD` (caras = c + 2)
  cumple la igualdad de genero `s_A + s_B = c + 2`.
* `SpanNoNugatorio.minimal_of_nonNugatory`: genero cero y no nugatorio implican que todo diagrama
  de una curva equivalente por `GRel` tiene al menos tantos cruces.

## Que queda demostrado
Para un diagrama `d` sin circunferencias libres, ALTERNANTE, PLANAR (`PlanarD`, a nivel de caras
del mapa combinatorio) y NO NUGATORIO (`NonNugatory`, conectividad al desacoplar cada cruce) y con
algun cruce: todo diagrama `d'` de UNA curva sin libres equivalente por `GRel` tiene al menos
`c(d)` cruces. Es decir, `c(d)` es el numero de cruces del nudo (cota inferior; la superior es el
propio `d`).

## Que NO esta demostrado (hipotesis que quedan abiertas)
* `NonNugatory` no se deduce aun de "toda cuerda esta entrelazada con otra" para palabras de Gauss
  (etapa S5e); solo se ha verificado en el trebol (`SpanNoNugatorio.trefoil_nonNugatory`) y,
  de forma equivalente por calculo, en los censos de `SpanCensos`.
* `PlanarD` es una hipotesis: no se deduce de la definicion de planaridad de `Etapa1_Planaridad`
  (se comprobo por calculo que coinciden, pero la equivalencia no esta formalizada).
-/

namespace TMENudos.Puente

open TMENudos.Gauss TMENudos.Invariancia TMENudos.Nudos

/-- **Minimalidad de cruces para diagramas alternantes planares no nugatorios.** -/
theorem minimal_alternante_planar (d d' : Diag) (h : GRel d d') (hf : d.D.free = 0)
    (halt : d.D.Alt) (hpl : d.D.PlanarD) (hN : d.D.NonNugatory) (hne : Nonempty d.D.Cross)
    (hf' : d'.D.free = 0) (hc : ∀ i j, d'.D.next.SameCycle i j) :
    Fintype.card d.D.Cross ≤ Fintype.card d'.D.Cross :=
  minimal_of_nonNugatory d d' h hf (GDiag.hgen_of_alternante_planar d.D hf halt hpl) hN hne hf' hc

/-- El trebol cumple las hipotesis estructurales (alternante, planar y no nugatorio, sin
circunferencias libres y con cruces): se recupera `3 ≤ cruces` por la ruta general. -/
theorem trefoil_minimal_general (d' : Diag)
    (h : GRel (Diag.mk _ (ofWord trefoil wf_trefoil)) d') (hf' : d'.D.free = 0)
    (hc : ∀ i j, d'.D.next.SameCycle i j) : 3 ≤ Fintype.card d'.D.Cross := by
  have hfree : (Diag.mk _ (ofWord trefoil wf_trefoil)).D.free = 0 := by
    obtain ⟨-, -, -⟩ := sanidad_trefoil
    change (ofWord trefoil wf_trefoil).free = 0
    have : trefoil.length ≠ 0 := by decide +kernel
    change (if trefoil.length = 0 then 1 else 0) = 0
    simp [this]
  have hne : Nonempty (Diag.mk _ (ofWord trefoil wf_trefoil)).D.Cross := by
    obtain ⟨h1, -, -⟩ := sanidad_trefoil
    rw [← Fintype.card_pos_iff, h1]; decide
  have := minimal_alternante_planar _ d' h hfree alt_trefoil planarD_trefoil trefoil_nonNugatory
    hne hf' hc
  have h3 : Fintype.card (Diag.mk _ (ofWord trefoil wf_trefoil)).D.Cross = 3 :=
    (sanidad_trefoil).1
  omega

end TMENudos.Puente

#print axioms TMENudos.Puente.minimal_alternante_planar
#print axioms TMENudos.Puente.trefoil_minimal_general
