import TMENudos.Basic
import TMENudos.TCN_06_Representantes
import TMENudos.Etapa1_GaussWord

/-!
# Etapa 1 (exploracion): la teoria modular vista como palabras de Gauss con signo derivado

Archivo de EXPLORACION, no importado desde `TMENudos.lean`. Convierte configuraciones modulares
(`K3Config`, `RationalConfiguration n`) en `Word` (palabras de Gauss con signos) usando el signo
DERIVADO de las posiciones (`Basic.crossing_sign`), y calcula el Jones de la Etapa 1.

Hallazgo (ver los teoremas de la seccion final): en `trefoilKnot` los tres cruces son antipodales
(`u - o = 3` en `ZMod 6`), el signo derivado vale +1 en los tres, y tambien en `swap trefoilKnot`;
la palabra resultante es el trebol DERECHO (con todos los signos positivos), y `mirrorTrefoil`
recibe EXACTAMENTE el mismo Jones. Con signo como dato independiente (o derivado de la paridad de
`o`) el `swap` si cambia el Jones.

Nada aqui usa `sorry`, axiomas nuevos ni `native_decide`.
-/

namespace TMENudos.Modular

open TMENudos.Gauss TMENudos.Gauss.Word

/-! ## 1. Conversion `RationalConfiguration n → Word` (general) -/

/-- Signo derivado de las POSICIONES como `Bool` (`true` si `zmod_sign (u - o) = 1`).

    MIGRACIÓN (signo como dato): antes era `decide (crossing_sign c = 1)`, y `crossing_sign` era
    derivado; ahora `crossing_sign` lee el campo `pos`, así que aquí se escribe explícitamente la
    fórmula derivada (el comportamiento antiguo), para que esta capa de exploración conserve su
    enunciado: el signo derivado pierde la quiralidad. Para leer el campo `pos` ver
    `RationalConfiguration.toWordData`. -/
def derivedPos {n : ℕ} (c : TMENudos.RationalCrossing n) : Bool :=
  decide (TMENudos.zmod_sign (c.under_pos - c.over_pos) = 1)

/-- Palabra de Gauss de longitud `2n` de una configuracion racional: en la posicion `p` esta el
    cruce `i` (primero que la contiene), `over` si `p` es su posicion superior, `pos` = signo
    derivado. -/
def _root_.TMENudos.RationalConfiguration.toWord {n : ℕ} (K : TMENudos.RationalConfiguration n) :
    Word :=
  (List.range (2 * n)).map fun p =>
    let x : ZMod (2 * n) := (p : ZMod (2 * n))
    match (List.finRange n).find? (fun i =>
        decide ((K.crossings i).over_pos = x ∨ (K.crossings i).under_pos = x)) with
    | some i => ⟨i.val, decide ((K.crossings i).over_pos = x), derivedPos (K.crossings i)⟩
    | none => ⟨0, true, true⟩

/-- Palabra de Gauss de una configuración racional leyendo el signo DATO (`pos`) de cada cruce.
    (Nuevo en la migración del signo como dato; `toWord` de arriba conserva el signo derivado de
    las posiciones.) Para cruces construidos con `withDerivedSign` coinciden
    (`trefoilRC_wordData`). -/
def _root_.TMENudos.RationalConfiguration.toWordData {n : ℕ}
    (K : TMENudos.RationalConfiguration n) : Word :=
  (List.range (2 * n)).map fun p =>
    let x : ZMod (2 * n) := (p : ZMod (2 * n))
    match (List.finRange n).find? (fun i =>
        decide ((K.crossings i).over_pos = x ∨ (K.crossings i).under_pos = x)) with
    | some i => ⟨i.val, decide ((K.crossings i).over_pos = x), (K.crossings i).pos⟩
    | none => ⟨0, true, true⟩

/-! ## 2. Conversion `K3Config → Word` -/

open KnotTheory in
/-- Letra de `K : K3Config` en la posicion `p`. La etiqueta del cruce es `min(o.val, u.val)`
    (distinta para cada pareja). Se usa `Finset.sup` sobre las parejas que contienen a `p`
    (hay exactamente una) para que sea computable. -/
def letterAt (K : K3Config) (p : ZMod 6) : Letter :=
  let S := K.pairs.filter (fun q => q.fst = p ∨ q.snd = p)
  ⟨S.sup (fun q => min q.fst.val q.snd.val),
   decide (∃ q ∈ K.pairs, q.fst = p),
   decide (S.sup (fun q => if TMENudos.zmod_sign (n := 3) (q.snd - q.fst) = 1 then 1 else 0) = 1)⟩

open KnotTheory in
/-- Palabra de Gauss (longitud 6) de una `K3Config`, con signo derivado. -/
def K3Config.toWord (K : K3Config) : Word :=
  (List.range 6).map fun i => letterAt K (i : ZMod 6)

/-! ## 3. Version "cruda" (lista de pares `(o, u)` en `ℕ`, n = 3) para enumerar las 120 configuraciones

`rawWord` reproduce `K3Config.toWord`: etiqueta = indice del par, signo = `zmod_sign (u - o)`
calculado con aritmetica en `ℕ` (`d = (u + 6 - o) % 6`, positivo si `0 < d ≤ 3`). -/

/-- Signo derivado (crudo): `true` si `0 < (u - o) mod 6 ≤ 3`. -/
def rawPos (o u : ℕ) : Bool := decide (0 < (u + 6 - o) % 6 ∧ (u + 6 - o) % 6 ≤ 3)

/-- Palabra de Gauss de una lista de pares `(o, u)`. -/
def rawWord (l : List (ℕ × ℕ)) : Word :=
  (List.range 6).map fun p =>
    match (l.zipIdx).find? (fun (q, _) => q.1 == p || q.2 == p) with
    | some (q, _) => ⟨min q.1 q.2, q.1 == p, rawPos q.1 q.2⟩
    | none => ⟨0, true, true⟩

/-- Matchings perfectos ORIENTADOS de una lista de posiciones (todas las orientaciones). -/
def rawConfigs : ℕ → List ℕ → List (List (ℕ × ℕ))
  | 0, _ => [[]]
  | _ + 1, [] => [[]]
  | k + 1, a :: rest =>
    rest.flatMap fun b =>
      (rawConfigs k (rest.erase b)).flatMap fun tl => [(a, b) :: tl, (b, a) :: tl]

/-- Las 120 configuraciones de `K3Config` (15 matchings × 8 orientaciones). -/
def allRaw : List (List (ℕ × ℕ)) := rawConfigs 3 (List.range 6)

/-- R1 (crudo): alguna pareja consecutiva (`snd = fst ± 1` mod 6). -/
def rawR1 (l : List (ℕ × ℕ)) : Bool :=
  l.any fun (a, b) => b == (a + 1) % 6 || b == (a + 5) % 6

/-- R2 (crudo): dos parejas distintas con `q.fst = p.fst ± 1` y `q.snd = p.snd ± 1`. -/
def rawR2 (l : List (ℕ × ℕ)) : Bool :=
  l.any fun p => l.any fun q => p != q &&
    ((q.1 == (p.1 + 1) % 6 || q.1 == (p.1 + 5) % 6) &&
     (q.2 == (p.2 + 1) % 6 || q.2 == (p.2 + 5) % 6))

/-- Configuraciones sin R1 ni R2 (deben ser 14). -/
def rawNoR1R2 : List (List (ℕ × ℕ)) := allRaw.filter fun l => !rawR1 l && !rawR2 l

/-- Accion de D6 sobre posiciones: `r i : x ↦ x + i`, `sr i : x ↦ -(x + i)`. -/
def actRaw (refl : Bool) (i : ℕ) (x : ℕ) : ℕ := if refl then (12 - (x + i) % 6) % 6 else (x + i) % 6

/-- Forma canonica de una configuracion cruda: lista de pares ordenada. -/
def canon (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := l.insertionSort (fun a b => a.1 ≤ b.1)

/-- Orbita (como lista de formas canonicas, sin repetidos) de una configuracion cruda. -/
def orbitRaw (l : List (ℕ × ℕ)) : List (List (ℕ × ℕ)) :=
  (((List.range 6).flatMap fun i => [false, true].map fun r =>
    canon (l.map fun (a, b) => (actRaw r i a, actRaw r i b)))).eraseDups

/-- Clave de orbita: la menor forma canonica (comparacion por la lista de `ℕ`). -/
def orbitKey (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (orbitRaw l).foldl (fun m x => if (x.map fun p => 6 * p.1 + p.2) < (m.map fun p => 6 * p.1 + p.2)
    then x else m) (canon l)

#eval allRaw.length
#eval rawNoR1R2.length
#eval (rawNoR1R2.map orbitKey).eraseDups
#eval ((rawNoR1R2.map orbitKey).eraseDups.map fun k => (orbitRaw k).length)

/-! ## 4. Jones (A = 2, sobre ℚ) de las 14 configuraciones sin R1 ni R2, por orbita -/

/-- Jones en A = 2 de una configuracion cruda. -/
def jr (l : List (ℕ × ℕ)) : ℚ := jones (2 : ℚ) (rawWord l)

#eval rawNoR1R2.map fun l => (orbitKey l, canon l, jr l, Word.writhe (rawWord l))
#eval (rawNoR1R2.map fun l => (orbitKey l, jr l)).eraseDups
#eval jones (2 : ℚ) trefoil
#eval jones (2 : ℚ) (swap trefoil)
#eval jones (2 : ℚ) (K3Config.toWord KnotTheory.trefoilKnot)
#eval jones (2 : ℚ) (K3Config.toWord KnotTheory.mirrorTrefoil)
#eval jones (2 : ℚ) (K3Config.toWord KnotTheory.specialClass)

/-! ### Planaridad de Gauss (paridad de interseccion): ¿es el codigo realizable en el plano?

Condicion necesaria de Gauss: cada cuerda interseca (se entrelaza con) un numero PAR de las demas.
Si falla, la palabra no es un diagrama clasico sino un diagrama virtual. -/

/-- Numero de cuerdas que se entrelazan con la cuerda `p`. -/
def interlaceDeg (l : List (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ :=
  (l.filter fun q =>
    let a := min p.1 p.2; let b := max p.1 p.2
    let inside := fun x => decide (a < x ∧ x < b)
    inside q.1 != inside q.2).length

/-- Condicion de Gauss (todas las cuerdas con grado par). -/
def gaussEven (l : List (ℕ × ℕ)) : Bool := l.all fun p => interlaceDeg l p % 2 == 0

#eval rawNoR1R2.map fun l => (canon l, gaussEven l, jr l)

/-! ## 5. Signo como DATO: palabras con signo explicito `(o, u, σ)` -/

/-- Palabra de Gauss de una lista de cruces `(o, u, σ)` con signo `σ` independiente. -/
def signedWord (l : List (ℕ × ℕ × Bool)) : Word :=
  (List.range 6).map fun p =>
    match (l.zipIdx).find? (fun (q, _) => q.1 == p || q.2.1 == p) with
    | some (q, _) => ⟨min q.1 q.2.1, q.1 == p, q.2.2⟩
    | none => ⟨0, true, true⟩

/-- Intercambio τ con signo como dato: intercambia over/under Y cambia el signo (como `Word.swap`). -/
def swapS (l : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ × Bool) :=
  l.map fun (o, u, s) => (u, o, !s)

/-- El signo derivado, hecho explicito: `σ = rawPos o u`. -/
def withDerived (l : List (ℕ × ℕ)) : List (ℕ × ℕ × Bool) :=
  l.map fun (o, u) => (o, u, rawPos o u)

/-- Trebol con signo explicito (todos +): coincide con `trefoilKnot` con signo derivado. -/
def trefS : List (ℕ × ℕ × Bool) := [(0, 3, true), (4, 1, true), (2, 5, true)]

/-- Regla alternativa "paridad": el signo de un cruce es `+` si su posicion superior es par
    (diagrama alternante con orientacion del plano fija). -/
def withParity (l : List (ℕ × ℕ)) : List (ℕ × ℕ × Bool) :=
  l.map fun (o, u) => (o, u, decide (o % 2 = 0))

/-- Accion de D6 sobre cruces con signo: mueve las posiciones y CONSERVA `σ`. -/
def actS (refl : Bool) (i : ℕ) (l : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ × Bool) :=
  l.map fun (o, u, s) => (actRaw refl i o, actRaw refl i u, s)

def js (l : List (ℕ × ℕ × Bool)) : ℚ := jones (2 : ℚ) (signedWord l)

#eval (js trefS, js (swapS trefS))
#eval js (withDerived [(0, 3), (4, 1), (2, 5)])
#eval js (withParity [(0, 3), (4, 1), (2, 5)])         -- trebol derecho
#eval js (withParity [(3, 0), (1, 4), (5, 2)])         -- mirrorTrefoil con signo por paridad
#eval js (swapS (withParity [(0, 3), (4, 1), (2, 5)])) -- swap del anterior
-- D6 con signo conservado: el Jones es constante en la orbita
#eval (List.range 6).flatMap fun i => [false, true].map fun r => js (actS r i trefS)
#eval (List.range 6).flatMap fun i => [false, true].map fun r =>
  js (actS r i (withDerived [(0, 2), (1, 4), (3, 5)]))
-- ... y con signo derivado (recalculado tras la accion) NO es constante:
#eval (List.range 6).flatMap fun i => [false, true].map fun r =>
  jr ((([(0, 2), (1, 4), (3, 5)] : List (ℕ × ℕ)).map fun (a, b) => (actRaw r i a, actRaw r i b)))
-- con paridad, la rotacion por 1 cambia la quiralidad:
#eval (List.range 6).map fun i => js (withParity ((trefS.map fun (o, u, _) => (o, u)).map
  fun (a, b) => (actRaw false i a, actRaw false i b)))

/-! ## 6. Teoremas (todos por `decide` / `decide +kernel`) -/

open KnotTheory

/-- Valores de referencia de `Etapa1_GaussWord`: trebol derecho y su espejo, en A = 2. -/
theorem jones_trefoil_right : jones (2 : ℚ) trefoil = 4111 / 65536 := by decide +kernel
theorem jones_trefoil_left : jones (2 : ℚ) (swap trefoil) = -61424 := by decide +kernel

/-- (T1) Las palabras de las configuraciones modulares son bien formadas. -/
theorem wf_trefoilKnot : Word.wf (K3Config.toWord trefoilKnot) = true := by decide +kernel
theorem wf_mirrorTrefoil : Word.wf (K3Config.toWord mirrorTrefoil) = true := by decide +kernel
theorem wf_specialClass : Word.wf (K3Config.toWord specialClass) = true := by decide +kernel

/-- (T2) `K3Config.toWord` coincide con la version cruda en los tres representantes. -/
theorem toWord_trefoilKnot : K3Config.toWord trefoilKnot = rawWord [(0, 3), (4, 1), (2, 5)] := by
  decide +kernel
theorem toWord_mirrorTrefoil : K3Config.toWord mirrorTrefoil = rawWord [(3, 0), (1, 4), (5, 2)] := by
  decide +kernel
theorem toWord_specialClass : K3Config.toWord specialClass = rawWord [(0, 2), (1, 4), (3, 5)] := by
  decide +kernel

/-- (T3) Las tres parejas de `trefoilKnot` son antipodales: `u - o = 3` en `ZMod 6`. -/
theorem trefoilKnot_antipodal :
    trefoilKnot.pairs.image (fun p => p.snd - p.fst) = {3} := by decide +kernel

/-- ... y lo mismo en `mirrorTrefoil` (que es `reverse` de cada pareja). -/
theorem mirrorTrefoil_antipodal :
    mirrorTrefoil.pairs.image (fun p => p.snd - p.fst) = {3} := by decide +kernel

/-- `mirrorTrefoil` es `swap` (reverse de cada pareja) de `trefoilKnot`. -/
theorem mirrorTrefoil_eq_reverse :
    mirrorTrefoil.pairs = trefoilKnot.pairs.image OrderedPair.reverse := by
  decide +kernel

/-- (T4) El signo derivado vale +1 en TODAS las parejas de ambos trebol (con la convencion de
    `Basic.zmod_sign`, `n = 3`). -/
theorem derived_sign_trefoil :
    trefoilKnot.pairs.image (fun p => TMENudos.zmod_sign (n := 3) (p.snd - p.fst)) = {1} ∧
    mirrorTrefoil.pairs.image (fun p => TMENudos.zmod_sign (n := 3) (p.snd - p.fst)) = {1} := by
  decide +kernel

/-- En `ZMod (2n)`, `x.val = n` da signo +1: el signo derivado de una pareja antipodal es +1, y
    por tanto invariante bajo el intercambio `(o,u) ↦ (u,o)`. Demostracion general. -/
theorem zmod_sign_antipodal {n : ℕ} [NeZero n] (x : ZMod (2 * n)) (hx : x.val = n) :
    TMENudos.zmod_sign x = 1 := by
  unfold TMENudos.zmod_sign
  have : 0 < x.val := by have := NeZero.pos n; omega
  have h0 := NeZero.ne n
  simp [hx, h0]

/-- **(T5) `trefoilKnot` recibe el Jones del trebol DERECHO** (en A = 2). -/
theorem jones_trefoilKnot : jones (2 : ℚ) (K3Config.toWord trefoilKnot) = 4111 / 65536 := by
  decide +kernel

/-- **(T6) `mirrorTrefoil` recibe el MISMO Jones que `trefoilKnot`**, es decir el del trebol
    derecho: NO el del izquierdo (-61424). -/
theorem jones_mirrorTrefoil : jones (2 : ℚ) (K3Config.toWord mirrorTrefoil) = 4111 / 65536 := by
  decide +kernel

theorem jones_mirror_eq_trefoilKnot :
    jones (2 : ℚ) (K3Config.toWord mirrorTrefoil) = jones (2 : ℚ) (K3Config.toWord trefoilKnot) := by
  decide +kernel

theorem jones_modular_trefoil_ne_left :
    jones (2 : ℚ) (K3Config.toWord mirrorTrefoil) ≠ jones (2 : ℚ) (swap trefoil) := by
  decide +kernel

/-- **(T7) La palabra derivada de `mirrorTrefoil` NO es el `Word.swap` de la de `trefoilKnot`**:
    `Word.swap` cambia los signos, la teoria modular no. -/
theorem toWord_mirror_ne_swap :
    K3Config.toWord mirrorTrefoil ≠ swap (K3Config.toWord trefoilKnot) := by
  decide +kernel

/-- Y el Jones del verdadero `Word.swap` de `trefoilKnot` es el del trebol izquierdo. -/
theorem jones_swap_trefoilKnot :
    jones (2 : ℚ) (swap (K3Config.toWord trefoilKnot)) = -61424 := by
  decide +kernel

/-- **(T8) Perdida de quiralidad**: el Jones modular de `mirrorTrefoil` difiere del de la
    imagen especular genuina de `trefoilKnot`. -/
theorem modular_mirror_not_genuine_mirror :
    jones (2 : ℚ) (K3Config.toWord mirrorTrefoil) ≠
      jones (2 : ℚ) (swap (K3Config.toWord trefoilKnot)) := by
  decide +kernel

/-- **(T9) `specialClass`** tiene Jones 79/1024 (no es 1 ni el de un trebol). -/
theorem jones_specialClass : jones (2 : ℚ) (K3Config.toWord specialClass) = 79 / 1024 := by
  decide +kernel

theorem specialClass_not_unknot : jones (2 : ℚ) (K3Config.toWord specialClass) ≠ 1 := by
  decide +kernel

/-- (T10) Las 14 configuraciones sin R1 ni R2 (version cruda): los valores del Jones. -/
theorem noR1R2_count : rawNoR1R2.length = 14 := by decide +kernel

theorem noR1R2_jones :
    rawNoR1R2.map (fun l => (canon l, jr l)) =
      [([(0, 2), (1, 4), (3, 5)], 79 / 1024), ([(0, 2), (3, 5), (4, 1)], 79 / 1024),
       ([(1, 4), (2, 0), (5, 3)], 949 / 4), ([(2, 0), (4, 1), (5, 3)], 949 / 4),
       ([(0, 3), (2, 5), (4, 1)], 4111 / 65536), ([(1, 4), (3, 0), (5, 2)], 4111 / 65536),
       ([(0, 3), (2, 4), (5, 1)], 79 / 1024), ([(2, 4), (3, 0), (5, 1)], 79 / 1024),
       ([(0, 3), (1, 5), (4, 2)], 949 / 4), ([(1, 5), (3, 0), (4, 2)], 949 / 4),
       ([(1, 3), (2, 5), (4, 0)], 79 / 1024), ([(0, 4), (2, 5), (3, 1)], 949 / 4),
       ([(1, 3), (4, 0), (5, 2)], 79 / 1024), ([(0, 4), (3, 1), (5, 2)], 949 / 4)] := by
  decide +kernel

/-- Las orbitas (D6, con la accion de `TCN_04` sobre posiciones) son exactamente 2. -/
theorem noR1R2_orbits :
    (rawNoR1R2.map orbitKey).eraseDups = [[(0, 2), (1, 4), (3, 5)], [(0, 3), (2, 5), (4, 1)]] := by
  decide +kernel

/-- Solo la orbita del trebol pasa la condicion de Gauss; la de 12 es no planar (virtual). -/
theorem gauss_parity :
    rawNoR1R2.map (fun l => (canon l, gaussEven l)) =
      [([(0, 2), (1, 4), (3, 5)], false), ([(0, 2), (3, 5), (4, 1)], false),
       ([(1, 4), (2, 0), (5, 3)], false), ([(2, 0), (4, 1), (5, 3)], false),
       ([(0, 3), (2, 5), (4, 1)], true), ([(1, 4), (3, 0), (5, 2)], true),
       ([(0, 3), (2, 4), (5, 1)], false), ([(2, 4), (3, 0), (5, 1)], false),
       ([(0, 3), (1, 5), (4, 2)], false), ([(1, 5), (3, 0), (4, 2)], false),
       ([(1, 3), (2, 5), (4, 0)], false), ([(0, 4), (2, 5), (3, 1)], false),
       ([(1, 3), (4, 0), (5, 2)], false), ([(0, 4), (3, 1), (5, 2)], false)] := by
  decide +kernel

/-! ## 7. Propuesta: signo como dato (o regla de paridad) -/

/-- El signo derivado, hecho explicito, reproduce exactamente `rawWord`. -/
theorem withDerived_trefoil :
    signedWord (withDerived [(0, 3), (4, 1), (2, 5)]) = rawWord [(0, 3), (4, 1), (2, 5)] := by
  decide +kernel

/-- **(P1)** Con signo como dato, `swap` cambia el Jones del trebol: derecho (4111/65536) ->
    izquierdo (-61424). -/
theorem signed_trefoil_jones : js trefS = 4111 / 65536 := by decide +kernel
theorem signed_swap_trefoil_jones : js (swapS trefS) = -61424 := by decide +kernel
theorem signed_swap_changes_jones : js (swapS trefS) ≠ js trefS := by decide +kernel

/-- `swapS` corresponde a `Word.swap`; la palabra firmada de `trefS` es `toWord trefoilKnot`. -/
theorem signedWord_trefS : signedWord trefS = K3Config.toWord trefoilKnot := by decide +kernel
theorem signedWord_swapS : signedWord (swapS trefS) = swap (signedWord trefS) := by decide +kernel
theorem signed_wf :
    Word.wf (signedWord trefS) = true ∧ Word.wf (signedWord (swapS trefS)) = true := by
  decide +kernel

/-- **(P2)** Con signo por paridad de `o` (diagrama alternante): `trefoilKnot` -> derecho,
    `mirrorTrefoil` -> izquierdo, y `swapS` de uno es el otro (a nivel de Jones). -/
theorem parity_trefoilKnot : js (withParity [(0, 3), (4, 1), (2, 5)]) = 4111 / 65536 := by
  decide +kernel
theorem parity_mirrorTrefoil : js (withParity [(3, 0), (1, 4), (5, 2)]) = -61424 := by
  decide +kernel
theorem parity_swap :
    js (swapS (withParity [(0, 3), (4, 1), (2, 5)])) = js (withParity [(3, 0), (1, 4), (5, 2)]) := by
  decide +kernel

/-- Con signo como dato, D6 (posiciones) conserva el Jones en la orbita: trebol y orbita de 12. -/
theorem signed_D6_invariant_trefoil :
    ∀ i ∈ List.range 6, ∀ r ∈ [false, true], js (actS r i trefS) = 4111 / 65536 := by
  decide +kernel

theorem signed_D6_invariant_special :
    ∀ i ∈ List.range 6, ∀ r ∈ [false, true],
      js (actS r i (withDerived [(0, 2), (1, 4), (3, 5)])) = 79 / 1024 := by decide +kernel

/-- Con signo DERIVADO, el Jones no es constante en la orbita de 12 (la reflexion invierte el
    signo derivado): la reflexion `x ↦ -x` de `specialClass` da otro valor. -/
theorem derived_D6_not_invariant_special :
    jr [(0, 2), (1, 4), (3, 5)] ≠ jr [(0, 4), (5, 2), (3, 1)] := by
  decide +kernel

/-- Con la regla de paridad, una rotacion por 1 (cambio de punto de partida) cambia la
    quiralidad: la regla exige restringir a rotaciones pares o fijar el nivel de base. -/
theorem parity_rotation_flips :
    js (withParity [(1, 4), (5, 2), (3, 0)]) ≠ js (withParity [(0, 3), (4, 1), (2, 5)]) := by
  decide +kernel

/-! ## 8. Conversion general y ejemplo con `RationalConfiguration 3` -/

open TMENudos in
/-- Trebol como `RationalConfiguration 3`. -/
def trefoilRC : RationalConfiguration 3 where
  crossings := ![RationalCrossing.withDerivedSign 0 3 (by decide),
    RationalCrossing.withDerivedSign 4 1 (by decide),
    RationalCrossing.withDerivedSign 2 5 (by decide)]
  coverage := by decide

open TMENudos in
theorem trefoilRC_word : trefoilRC.toWord = K3Config.toWord trefoilKnot := by decide +kernel

open TMENudos in
/-- Con `withDerivedSign`, leer el signo dato coincide con el signo derivado. -/
theorem trefoilRC_wordData : trefoilRC.toWordData = trefoilRC.toWord := by decide +kernel

open TMENudos in
/-- Con el signo como dato, la imagen especular (`swap_knot`, que niega el signo) SÍ cambia el
    Jones: da el del trébol izquierdo (-61424), a diferencia de `swap_knot_trefoilRC_jones`. -/
theorem swap_knot_trefoilRC_jones_data :
    jones (2 : ℚ) (swap_knot trefoilRC).toWordData = -61424 := by
  decide +kernel

open TMENudos in
theorem swap_knot_trefoilRC_wordData_eq_swap :
    (swap_knot trefoilRC).toWordData = swap trefoilRC.toWordData := by decide +kernel

open TMENudos in
theorem trefoilRC_wf : Word.wf trefoilRC.toWord = true := by decide +kernel

open TMENudos in
theorem trefoilRC_jones : jones (2 : ℚ) trefoilRC.toWord = 4111 / 65536 := by decide +kernel

open TMENudos in
/-- La imagen especular de la teoria modular (`swap_knot`) da tambien el Jones del trebol derecho. -/
theorem swap_knot_trefoilRC_jones : jones (2 : ℚ) (swap_knot trefoilRC).toWord = 4111 / 65536 := by
  decide +kernel

open TMENudos in
theorem swap_knot_trefoilRC_word_ne : (swap_knot trefoilRC).toWord ≠ swap trefoilRC.toWord := by
  decide +kernel

#print axioms jones_mirrorTrefoil
#print axioms modular_mirror_not_genuine_mirror
#print axioms noR1R2_jones
#print axioms signed_swap_trefoil_jones
#print axioms zmod_sign_antipodal
#print axioms swap_knot_trefoilRC_word_ne
#print axioms trefoilRC_wordData
#print axioms swap_knot_trefoilRC_jones_data
#print axioms swap_knot_trefoilRC_wordData_eq_swap

end TMENudos.Modular
