/- Volcado de los tipos/valores de los objetos ORIGINALES (Reidemeister, Schubert, Bridge), para compararlos con el volcado del modelo (06_modelo_de_consistencia.lean). Uso: ver comentario al final de 06_modelo_de_consistencia.lean. -/
import TMENudos.Bridge

section Fidelidad
open Lean Meta Elab Command

def strip (s : String) : String :=
  ["TMENudos.Reidemeister.ReidemeisterMoves.", "TMENudos.Reidemeister.",
   "TMENudos.SchubertTheorems.", "TMENudos.Bridge.", "Model."].foldl (fun s p => s.replace p "") s

def typeNames : List String := [
  "Crossing.mk", "KnotConfig.mk", "Strand.mk", "R1Move.mk", "R2Move.mk", "R3Move.mk",
  "CrossingSign.Positive", "CrossingSign.Negative",
  "reidemeister_equivalent", "reidemeister_equivalent.refl", "reidemeister_equivalent.symm",
  "reidemeister_equivalent.trans", "reidemeister_equivalent.R1", "reidemeister_equivalent.R2",
  "reidemeister_equivalent.R3", "apply_R1", "apply_R2", "apply_R3",
  "Diagram.mk", "diagram_equiv", "DiagramSetoid", "Knot", "knot_isotopic", "unknot", "is_prime",
  "topologically_equivalent", "topo_equiv_refl", "topo_equiv_symm", "topo_equiv_trans",
  "R1_preserves_isotopy", "R2_preserves_isotopy", "R3_preserves_isotopy",
  "R1_inverse", "R2_inverse", "R3_inverse", "reidemeister_completeness",
  "connected_sum", "connected_sum_comm", "connected_sum_assoc", "connected_sum_unknot",
  "trefoil", "figure_eight", "cinquefoil", "trefoil_is_prime", "figure_eight_is_prime",
  "schubert_existence_axiom", "schubert_uniqueness", "knot_genus", "bridge_number",
  "knot_complement", "knot_group", "manifold_connected_sum", "knot_primality_in_NP", "mirror",
  "alexander_polynomial", "ThreeManifold", "JSJ_decomposition",
  "rational_to_diagram", "rational_to_knot", "rational_equivalence_preserves_isotopy"]

def valueNames : List String :=
  ["Knot", "knot_isotopic", "unknot", "is_prime", "diagram_equiv", "DiagramSetoid"]

def findConst (env : Environment) (short : String) : Option ConstantInfo :=
  ["Model.", "TMENudos.Reidemeister.ReidemeisterMoves.", "TMENudos.Reidemeister.",
   "TMENudos.SchubertTheorems.", "TMENudos.Bridge."].findSome? fun p =>
    env.find? (p ++ short).toName

set_option pp.fullNames true in
set_option pp.funBinderTypes true in
#eval show MetaM Unit from do
  let env ← getEnv
  for s in typeNames do
    match findConst env s with
    | none => IO.println s!"TYPE {s} :: NOT FOUND"
    | some ci =>
      let f ← ppExpr ci.type
      IO.println s!"TYPE {s} :: {strip (f.pretty 100000)}"
  for s in valueNames do
    match findConst env s with
    | some ci =>
      match ci.value? with
      | some v =>
        let f ← ppExpr v
        IO.println s!"VALUE {s} :: {strip (f.pretty 100000)}"
      | none => IO.println s!"VALUE {s} :: (sin valor)"
    | none => IO.println s!"VALUE {s} :: NOT FOUND"

end Fidelidad

/-! Recuento de axiomas declarados en los tres archivos originales. -/
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := [`TMENudos.Reidemeister, `TMENudos.Schubert, `TMENudos.Bridge]
  for m in mods do
    let mut names : Array Name := #[]
    for (n, ci) in env.constants.map₁.toList do
      match ci with
      | .axiomInfo _ =>
        if let some idx := env.getModuleIdxFor? n then
          if env.header.moduleNames[idx.toNat]! == m then names := names.push n
      | _ => pure ()
    IO.println s!"AXIOMS {m} : {names.size}"
