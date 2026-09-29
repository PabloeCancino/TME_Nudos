/- VERIFICACIÓN (2026-09-29). Para cada teorema cerrado en el saneamiento de la clase A de Schubert, lista las constantes de su cadena de dependencias (incluidos los constructores de tipos inductivos) que contienen `sorry` directamente. Resultado esperado y obtenido: solo apply_R1, apply_R2 y apply_R3, es decir, ningún sorry propio de Schubert se filtra. Complementa a `#print axioms`, que solo muestra `sorryAx` sin indicar de dónde viene. Ejecutar con: lake env lean Procesos/Tests/auditoria_20260929/05_rastreo_de_sorry_en_teoremas_cerrados.lean -/
import TMENudos.Schubert
open Lean Elab Command

/-- Clausura transitiva de constantes usadas por `n` (en tipo y valor). -/
partial def depClosure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then depClosure env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => depClosure env rest seen
      | some ci =>
        let used := ci.type.getUsedConstants ++
          (match ci.value? with | some v => v.getUsedConstants | none => #[])
        let ctors : List Name := match ci with
          | .inductInfo v => v.ctors
          | _ => []
        depClosure env (used.toList ++ ctors ++ rest) seen

/-- ¿La constante contiene `sorryAx` directamente en su tipo o su valor? -/
def directSorry (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some ci =>
    ci.type.getUsedConstants.contains ``sorryAx ||
      (match ci.value? with | some v => v.getUsedConstants.contains ``sorryAx | none => false)
  | none => false

elab "#sorry_sources " ids:ident+ : command => do
  let env ← getEnv
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let cl := depClosure env [n] {}
    let srcs := (cl.toList.filter (directSorry env)).map (·.toString)
    logInfo m!"{n}: constantes con sorry directo en su cadena de dependencias = {srcs}"

open TMENudos.SchubertTheorems in
#sorry_sources schubert_existence schubert_unique_factorization factorization_problem
  prime_decomposition_prime prime_decomposition_reconstructs decomposition_length_eq
  decomposition_length_add decomposition_nil_iff complexity_additive
  composite_characterization example_has_two_prime_factors
  granny_knot_composite granny_knot_decomposition
