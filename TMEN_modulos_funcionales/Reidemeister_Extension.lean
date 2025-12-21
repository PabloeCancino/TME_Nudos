
/-! ## Unificación de Tipos: El Espacio de Diagramas -/

/-- Un diagrama de nudo genérico (sigma type de KnotConfig) -/
structure Diagram where
  n : ℕ
  config : KnotConfig n

/-- Equivalencia de diagramas basada en movimientos de Reidemeister -/
def diagram_equiv (d1 d2 : Diagram) : Prop :=
  reidemeister_equivalent d1.config d2.config

theorem diagram_equiv_refl (d : Diagram) : diagram_equiv d d :=
  reidemeister_refl d.config

theorem diagram_equiv_symm {d1 d2 : Diagram} : diagram_equiv d1 d2 → diagram_equiv d2 d1 :=
  reidemeister_symm

theorem diagram_equiv_trans {d1 d2 d3 : Diagram} :
    diagram_equiv d1 d2 → diagram_equiv d2 d3 → diagram_equiv d1 d3 :=
  reidemeister_trans

/-- El conjunto de diagramas módulo movimientos de Reidemeister -/
instance DiagramSetoid : Setoid Diagram where
  r := diagram_equiv
  iseqv := { refl := diagram_equiv_refl, symm := diagram_equiv_symm, trans := diagram_equiv_trans }
