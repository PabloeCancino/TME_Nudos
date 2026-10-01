import TMENudos.Basic

/-!
# Reconstruccion reparada (Fase 1 del plan de axiomas de `Basic`)

`reconstruct_from_first` (Basic) es FALSO (sonda 16). Aqui se prueba, para n = 3 y n = 4
(y n = 5), el enunciado reparado: entre las configuraciones ORDENADAS y ALTERNANTES
(`SortedAlt`), PLANARES y SIN candidatos R1/R2, el invariante `SIMEcic` determina la clase
de rotacion.

Estructura:
* Parte combinatoria sobre listas de ternas `(over, under, signo)` de naturales
  (planaridad por conteo de caras, candidatos R1/R2, `SIMEcic`), decidida con `decide +kernel`
  sobre un espacio finito pequeno de datos `(paridad, permutacion, signos)`.
* Puente general en `n`: toda `K` con `SortedAlt` es `buildL p sigma signos`, y las nociones
  de `K` (Basic) coinciden con las booleanas de las listas.
-/

namespace TMENudos
namespace Reconstruccion

/-- Terna `(over, under, signo)` de naturales. -/
abbrev Tri := ℕ × ℕ × Bool

/-- Terna por defecto (para `getD`). -/
def d0 : Tri := (0, 0, false)

/-- La terna de un cruce. -/
def tri {n : ℕ} (c : RationalCrossing n) : Tri := (c.over_pos.val, c.under_pos.val, c.pos)

/-- La lista de ternas de una configuracion (por indice). -/
def toL {n : ℕ} (K : RationalConfiguration n) : List Tri :=
  (List.finRange n).map (fun i => tri (K.crossings i))

/-! ## Planaridad exacta por conteo de caras -/

/-- Rotacion antihoraria `sigma` sobre semiaristas (`out p = 2p`, `in p = 2p + 1`). -/
def sigmaD (L : List Tri) (d : ℕ) : ℕ :=
  L.foldr (fun t acc =>
    if d = 2 * t.1 then (if t.2.2 then 2 * t.2.1 else 2 * t.2.1 + 1)
    else if d = 2 * t.2.1 then (if t.2.2 then 2 * t.1 + 1 else 2 * t.1)
    else if d = 2 * t.1 + 1 then (if t.2.2 then 2 * t.2.1 + 1 else 2 * t.2.1)
    else if d = 2 * t.2.1 + 1 then (if t.2.2 then 2 * t.1 else 2 * t.1 + 1)
    else acc) d

/-- Involucion `alpha`: `out p ↦ in (p+1)`, `in q ↦ out (q-1)` (posiciones modulo `N`). -/
def alphaD (N d : ℕ) : ℕ :=
  if d % 2 = 0 then 2 * ((d / 2 + 1) % N) + 1 else 2 * ((d / 2 + N - 1) % N)

/-- Permutacion de caras `sigma ∘ alpha`. -/
def phiD (N : ℕ) (L : List Tri) (d : ℕ) : ℕ := sigmaD L (alphaD N d)

/-- `d` es el minimo de su orbita bajo `f` (con combustible). -/
def orbitMin (f : ℕ → ℕ) (d : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, x => if x < d then false else if x = d then true else orbitMin f d fuel (f x)

/-- Numero de caras: ciclos de `sigma ∘ alpha` (uno por orbita, su minimo). `N` = numero de
posiciones (= 2n). -/
def faceCount (N : ℕ) (L : List Tri) : ℕ :=
  ((List.range (2 * N)).filter
    (fun d => orbitMin (phiD N L) d (2 * N) (phiD N L d))).length

/-- Planaridad exacta: genero 0, es decir `caras = n + 2`. -/
def Planar {n : ℕ} (K : RationalConfiguration n) : Prop :=
  faceCount (2 * n) (toL K) = n + 2

instance {n : ℕ} (K : RationalConfiguration n) : Decidable (Planar K) :=
  inferInstanceAs (Decidable (faceCount (2 * n) (toL K) = n + 2))

/-! ## Candidatos R1/R2 (version booleana) -/

/-- Interlazado (misma condicion que `are_interlaced`). -/
def interlB (c1 c2 : Tri) : Bool :=
  (min c1.1 c1.2.1 < min c2.1 c2.2.1 && min c2.1 c2.2.1 < max c1.1 c1.2.1 &&
      max c1.1 c1.2.1 < max c2.1 c2.2.1) ||
  (min c2.1 c2.2.1 < min c1.1 c1.2.1 && min c1.1 c1.2.1 < max c2.1 c2.2.1 &&
      max c2.1 c2.2.1 < max c1.1 c1.2.1)

/-- Adyacencia modulo `N`. -/
def adjB (N p q : ℕ) : Bool := (p + 1) % N == q || (q + 1) % N == p

/-- Candidato R1 en el indice `i`. -/
def r1B (N : ℕ) (L : List Tri) (i : ℕ) : Bool :=
  adjB N (L.getD i d0).1 (L.getD i d0).2.1 &&
  (List.range L.length).all (fun j => j == i || !interlB (L.getD i d0) (L.getD j d0))

/-- Candidato R2 en el par `(a, b)` (signos opuestos). -/
def r2B (N : ℕ) (L : List Tri) (a b : ℕ) : Bool :=
  a != b && adjB N (L.getD a d0).1 (L.getD b d0).1 &&
  adjB N (L.getD a d0).2.1 (L.getD b d0).2.1 &&
  interlB (L.getD a d0) (L.getD b d0) && ((L.getD a d0).2.2 != (L.getD b d0).2.2)

/-- No hay ningun candidato R1 ni R2. -/
def noRedL (N : ℕ) (L : List Tri) : Bool :=
  (List.range L.length).all (fun i => !r1B N L i) &&
  (List.range L.length).all (fun a => (List.range L.length).all (fun b => !r2B N L a b))

/-- Sin candidatos R1/R2, con las definiciones de `Basic`. -/
def NoCand {n : ℕ} (K : RationalConfiguration n) : Prop :=
  (∀ i : Fin n, ¬ is_R1_candidate K i) ∧ (∀ a b : Fin n, ¬ is_R2_candidate K a b)

/-! ## `SIMEcic` -/

/-- Codificacion inyectiva de `(razon, signo)` en `ℕ`. -/
def key (x : ℕ × Bool) : ℕ := 2 * x.1 + x.2.toNat

/-- Orden lexicografico estricto sobre `List (ℕ × Bool)` (via `key`). -/
def lexLt : List (ℕ × Bool) → List (ℕ × Bool) → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if key a < key b then true else if key b < key a then false else lexLt as bs

/-- Minimo lexicografico entre las rotaciones ciclicas de la lista. -/
def cycMin (l : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (List.range l.length).foldl
    (fun best k => if lexLt (l.rotate k) best then l.rotate k else best) l

/-- `SIME` en orden de indice (= orden creciente del paso superior en `SortedAlt`), rotado a
su minimo ciclico. -/
def SIMEcic {n : ℕ} (K : RationalConfiguration n) : List (ℕ × Bool) := cycMin (SIME K)

/-- Razon modular sobre naturales. -/
def ratioN (N o u : ℕ) : ℕ := (u + N - o) % N

/-- `SIMEcic` calculado sobre la lista de ternas. -/
def simeL (N : ℕ) (L : List Tri) : List (ℕ × Bool) :=
  cycMin (L.map (fun t => (ratioN N t.1 t.2.1, t.2.2)))

/-! ## Ordenada y alternante -/

/-- Pasos superiores estrictamente crecientes con el indice y todos de la misma paridad. -/
def SortedAlt {n : ℕ} (K : RationalConfiguration n) : Prop :=
  (∀ i j : Fin n, i < j → (K.crossings i).over_pos.val < (K.crossings j).over_pos.val) ∧
  (∀ i j : Fin n, (K.crossings i).over_pos.val % 2 = (K.crossings j).over_pos.val % 2)

/-! ## Espacio finito de datos -/

/-- Todas las listas de longitud `k` con entradas `< m`. -/
def allLists (m : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (allLists m k).flatMap (fun l => (List.range m).map (fun x => x :: l))

/-- Todas las listas de booleanos de longitud `k`. -/
def boolLists : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (boolLists k).flatMap (fun l => [false :: l, true :: l])

/-- Permutaciones de `0..n-1` como listas. -/
def perms (n : ℕ) : List (List ℕ) := (allLists n n).filter (fun l => decide l.Nodup)

/-- La configuracion de datos `(p, sigma, signos)`: `over_i = 2i + p`,
`under_i = 2 sigma(i) + (1 - p)`. -/
def buildL (p : ℕ) (σ : List ℕ) (s : List Bool) : List Tri :=
  (List.range σ.length).map (fun i => (2 * i + p, 2 * σ.getD i 0 + (1 - p), s.getD i false))

/-- Todos los candidatos de datos. -/
def cands (n : ℕ) : List (List Tri) :=
  (List.range 2).flatMap (fun p => (perms n).flatMap (fun σ =>
    (boolLists n).map (fun s => buildL p σ s)))

/-- Planar y sin candidatos R1/R2. -/
def goodL (n : ℕ) (L : List Tri) : Bool :=
  noRedL (2 * n) L && decide (faceCount (2 * n) L = n + 2)

/-- Solo sin candidatos R1/R2 (sin planaridad). -/
def goodNP (n : ℕ) (L : List Tri) : Bool := noRedL (2 * n) L

/-- Rotacion de posiciones de una terna. -/
def rotT (N k : ℕ) (t : Tri) : Tri := ((t.1 + k) % N, (t.2.1 + k) % N, t.2.2)

/-- `L2` es `L1` rotada `k` posiciones y reindexada ciclicamente por `j`. -/
def relB (n : ℕ) (L1 L2 : List Tri) : Bool :=
  (List.range n).any (fun j => (List.range (2 * n)).any (fun k =>
    (List.range n).all (fun i => L2.getD ((i + j) % n) d0 == rotT (2 * n) k (L1.getD i d0))))

/-- Comprobacion finita: entre los candidatos que cumplen `g`, igual `SIMEcic` implica
rotacion. -/
def checkWith (g : List Tri → Bool) (n : ℕ) : Bool :=
  let G := (cands n).filter g
  G.all (fun L1 => G.all (fun L2 =>
    !decide (simeL (2 * n) L1 = simeL (2 * n) L2) || relB n L1 L2))

/-- Comprobacion para planares sin R1/R2. -/
def check (n : ℕ) : Bool := checkWith (goodL n) n

/-- Comprobacion sin exigir planaridad. -/
def checkNP (n : ℕ) : Bool := checkWith (goodNP n) n

end Reconstruccion
end TMENudos

open TMENudos.Reconstruccion in
#eval (List.range 6).map fun n => (cands n).length
open TMENudos.Reconstruccion in
#eval (List.range 6).map fun n => ((cands n).filter (goodL n)).length
open TMENudos.Reconstruccion in
#eval (List.range 6).map fun n => (((cands n).filter (goodL n)).map (simeL (2*n))).eraseDups.length
open TMENudos.Reconstruccion in
#eval (List.range 6).map fun n => check n
open TMENudos.Reconstruccion in
#eval (List.range 6).map fun n => checkNP n
