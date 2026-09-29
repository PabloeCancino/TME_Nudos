/- EXPERIMENTO (2026-09-29). Enumera todos los emparejamientos orientados de n=3 (120) y n=4 (1680), calcula órbitas de D_2n y de rotaciones, y compara con IME1 e IME2. Ejecutar con: lake env lean Procesos/Tests/auditoria_20260929/03_experimento_IME2_n3_n4.lean -/
import TMENudos.KN_04_Clasificacion_General
import TMENudos.KN_03b_Invariantes_IME

open KnotTheory.General

/-- Emparejamientos orientados de {0..m-1} como lista de pares (over, under). -/
partial def matchings (avail : List Nat) : List (List (Nat × Nat)) :=
  match avail with
  | [] => [[]]
  | x :: rest =>
    rest.flatMap fun y =>
      let rest' := rest.erase y
      (matchings rest').flatMap fun m => [(x, y) :: m, (y, x) :: m]

def toConfig (n : ℕ) [NeZero n] (l : List (Nat × Nat)) : Option (KnConfig n) :=
  let ps : List (Option (OrderedPair n)) := l.map fun (a, b) =>
    if h : ((a : ZMod (2 * n)) ≠ (b : ZMod (2 * n))) then some ⟨a, b, h⟩ else none
  if ps.all Option.isSome then
    let S : Finset (OrderedPair n) := (ps.filterMap id).toFinset
    if h1 : S.card = n then
      if h2 : ∀ i : ZMod (2 * n), ∃ p ∈ S, p.fst = i ∨ p.snd = i then some ⟨S, h1, h2⟩ else none
    else none
  else none

def keyOf (n : ℕ) (K : KnConfig n) : List ℕ :=
  (K.pairs.image (fun p => p.fst.val * 100 + p.snd.val)).sort (· ≤ ·)

/-- clave canónica de la órbita bajo D_{2n} (rotaciones y reflexión σ = mirror de KN_02) -/
def dihedralKey (n : ℕ) [NeZero n] (K : KnConfig n) : List ℕ :=
  let ks := (List.range (2 * n)).flatMap fun k =>
    [keyOf n (K.rotate (k : ZMod (2 * n))), keyOf n ((K.mirror).rotate (k : ZMod (2 * n)))]
  ks.foldl (fun m k => if k < m then k else m) (ks.head!)

def rotKey (n : ℕ) [NeZero n] (K : KnConfig n) : List ℕ :=
  let ks := (List.range (2 * n)).map fun k => keyOf n (K.rotate (k : ZMod (2 * n)))
  ks.foldl (fun m k => if k < m then k else m) (ks.head!)

def IME2 (n : ℕ) (K : KnConfig n) : Int × Int :=
  let a := K.IME
  let b := K.mirror.IME
  (min a b, max a b)

def allConfigs (n : ℕ) [NeZero n] : List (KnConfig n) :=
  (matchings (List.range (2 * n))).filterMap (toConfig n)

def dedup {α} [BEq α] (l : List α) : List α := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def report (n : ℕ) [NeZero n] : IO Unit := do
  let cs := allConfigs n
  let dkeys := dedup (cs.map (dihedralKey n))
  let rkeys := dedup (cs.map (rotKey n))
  let i2 := dedup (cs.map (IME2 n))
  let i1 := dedup (cs.map (fun K => K.IME))
  -- consistencia: IME2 constante en cada órbita diédrica
  let badD := dkeys.filter fun dk =>
    (dedup ((cs.filter fun K => dihedralKey n K == dk).map (IME2 n))).length > 1
  -- consistencia: IME1 constante en cada órbita de rotaciones
  let badR := rkeys.filter fun rk =>
    (dedup ((cs.filter fun K => rotKey n K == rk).map (fun K => K.IME))).length > 1
  -- separación: cuántos valores de IME2 agrupan más de una órbita diédrica
  let mixD := i2.filter fun v =>
    (dedup ((cs.filter fun K => IME2 n K == v).map (dihedralKey n))).length > 1
  let mixR := i1.filter fun v =>
    (dedup ((cs.filter fun K => K.IME == v).map (rotKey n))).length > 1
  IO.println s!"n={n}: configs={cs.length}, órbitas D_2n={dkeys.length}, órbitas rot={rkeys.length}"
  IO.println s!"  IME1 valores={i1.length}, IME2 valores={i2.length}"
  IO.println s!"  IME2 no constante en órbita D_2n: {badD.length} | IME1 no constante en órbita rot: {badR.length}"
  IO.println s!"  IME2 mezcla órbitas D_2n distintas: {mixD.length} de {i2.length} valores | IME1 mezcla órbitas rot: {mixR.length} de {i1.length} valores"

#eval report 3
#eval report 4
