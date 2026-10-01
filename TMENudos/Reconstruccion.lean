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

/-! ## Puente general en `n` -/

theorem mem_allLists (m : ℕ) : ∀ (k : ℕ) (l : List ℕ),
    l ∈ allLists m k ↔ l.length = k ∧ ∀ x ∈ l, x < m
  | 0, l => by cases l <;> simp [allLists]
  | k + 1, l => by
    cases l with
    | nil => simp [allLists]
    | cons a t =>
      simp only [allLists, List.mem_flatMap, List.mem_map, List.mem_range, List.cons.injEq,
        List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨l', hl', x, hx, rfl, rfl⟩
        obtain ⟨h1, h2⟩ := (mem_allLists m k l').1 hl'
        exact ⟨h1, hx, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨t, (mem_allLists m k t).2 ⟨h1, h3⟩, a, h2, rfl, rfl⟩

theorem mem_boolLists : ∀ (k : ℕ) (l : List Bool), l ∈ boolLists k ↔ l.length = k
  | 0, l => by cases l <;> simp [boolLists]
  | k + 1, l => by
    cases l with
    | nil => simp [boolLists]
    | cons a t =>
      simp only [boolLists, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
        List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨l', hl', h⟩
        have h1 := (mem_boolLists k l').1 hl'
        rcases h with h | h <;> simp only [List.cons.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;>
          exact h1
      · intro h
        refine ⟨t, (mem_boolLists k t).2 h, ?_⟩
        cases a <;> simp

theorem buildL_mem_cands {n p : ℕ} {σ : List ℕ} {s : List Bool} (hp : p ≤ 1) (h1 : σ.Nodup)
    (h2 : σ.length = n) (h3 : ∀ x ∈ σ, x < n) (h4 : s.length = n) :
    buildL p σ s ∈ cands n := by
  unfold cands
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, perms, List.mem_filter,
    decide_eq_true_eq]
  exact ⟨p, by omega, σ, ⟨(mem_allLists n n σ).2 ⟨h2, h3⟩, h1⟩, s, (mem_boolLists n s).2 h4, rfl⟩



section Puente

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem toL_length (K : RationalConfiguration n) : (toL K).length = n := by
  simp [toL]

omit [NeZero n] in
theorem toL_getD (K : RationalConfiguration n) (i : ℕ) (h : i < n) :
    (toL K).getD i d0 = tri (K.crossings ⟨i, h⟩) := by
  simp [toL, List.getD_eq_getElem?_getD, h]

omit [NeZero n] in
theorem over_step (K : RationalConfiguration n) (hK : SortedAlt K) (k : ℕ) :
    ∀ a b : Fin n, a.val + k = b.val →
      (K.crossings a).over_pos.val + 2 * k ≤ (K.crossings b).over_pos.val := by
  induction k with
  | zero =>
    intro a b h
    have : a = b := Fin.ext (by simpa using h)
    subst this
    simp
  | succ k ih =>
    intro a b h
    have hm : a.val + k < n := by have := b.isLt; omega
    have h1 := ih a ⟨a.val + k, hm⟩ rfl
    have h2 := hK.1 ⟨a.val + k, hm⟩ b (by simp [Fin.lt_def]; omega)
    have h3 := hK.2 ⟨a.val + k, hm⟩ b
    simp only at h1 h2 h3
    omega

/-- (a) Los pasos superiores de una `SortedAlt` son `2i + p`, con `p ∈ {0, 1}`. -/
theorem over_eq (K : RationalConfiguration n) (hK : SortedAlt K) :
    ∃ p : ℕ, p ≤ 1 ∧ ∀ i : Fin n, (K.crossings i).over_pos.val = 2 * i.val + p := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hl : (⟨n - 1, by omega⟩ : Fin n).val = n - 1 := rfl
  have h6 := over_step K hK (n - 1) ⟨0, hn⟩ ⟨n - 1, by omega⟩ (by simp)
  have h7 := ZMod.val_lt (K.crossings ⟨n - 1, by omega⟩).over_pos
  refine ⟨(K.crossings ⟨0, hn⟩).over_pos.val, by omega, ?_⟩
  intro i
  have h1 := over_step K hK i.val ⟨0, hn⟩ i (by simp)
  have h2 := over_step K hK (n - 1 - i.val) i ⟨n - 1, by omega⟩ (by simp; omega)
  have h4 := hK.2 i ⟨0, hn⟩
  omega

/-- Valor de la posicion `2j + (1 - p)` como elemento de `ZMod (2n)`. -/
def eP (p : ℕ) (j : Fin n) : ℝ[n] := ((2 * j.val + (1 - p) : ℕ) : ZMod (2 * n))

omit [NeZero n] in
theorem eP_val {p : ℕ} (hp : p ≤ 1) (j : Fin n) : (eP p j).val = 2 * j.val + (1 - p) := by
  unfold eP
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have := j.isLt
  omega

omit [NeZero n] in
/-- (b) Los pasos inferiores son `2 sigma(i) + (1 - p)` con `sigma` inyectiva. -/
theorem under_eq (K : RationalConfiguration n) (p : ℕ) (hp : p ≤ 1)
    (ho : ∀ i : Fin n, (K.crossings i).over_pos.val = 2 * i.val + p) :
    ∃ σ : Fin n → Fin n, Function.Injective σ ∧
      ∀ i : Fin n, (K.crossings i).under_pos.val = 2 * (σ i).val + (1 - p) := by
  have hcov : ∀ j : Fin n, ∃ i : Fin n, (K.crossings i).under_pos = eP p j := by
    intro j
    obtain ⟨i, hi | hi⟩ := K.coverage (eP p j)
    · exfalso
      have h1 := ho i
      rw [hi, eP_val hp] at h1
      omega
    · exact ⟨i, hi⟩
  choose h hh using hcov
  have hinj : Function.Injective h := by
    intro a b hab
    have h1 := hh a
    have h2 := hh b
    rw [hab] at h1
    have h3 := congrArg ZMod.val (h1.symm.trans h2)
    rw [eP_val hp, eP_val hp] at h3
    exact Fin.ext (by omega)
  have hsurj : Function.Surjective h := Finite.injective_iff_surjective.mp hinj
  refine ⟨Function.surjInv hsurj, Function.injective_surjInv hsurj, fun i => ?_⟩
  have h1 := hh (Function.surjInv hsurj i)
  rw [Function.surjInv_eq hsurj i] at h1
  rw [h1, eP_val hp]

/-- Puente (2): toda configuracion con `SortedAlt` es `buildL p sigma signos`. -/
theorem bridge (K : RationalConfiguration n) (hK : SortedAlt K) :
    ∃ (p : ℕ) (σ : List ℕ) (s : List Bool), p ≤ 1 ∧ σ.Nodup ∧ σ.length = n ∧
      (∀ x ∈ σ, x < n) ∧ s.length = n ∧ toL K = buildL p σ s := by
  obtain ⟨p, hp, ho⟩ := over_eq K hK
  obtain ⟨σ, hσ, hu⟩ := under_eq K p hp ho
  refine ⟨p, (List.finRange n).map (fun i => (σ i).val),
    (List.finRange n).map (fun i => (K.crossings i).pos), hp, ?_, by simp, ?_, by simp, ?_⟩
  · exact (List.nodup_finRange n).map (fun a b hab => hσ (Fin.ext hab))
  · intro x hx
    simp only [List.mem_map, List.mem_finRange, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (σ i).isLt
  · apply List.ext_getElem
    · simp [toL, buildL]
    · intro i h1 h2
      have hi : i < n := by simpa [toL] using h1
      simp only [toL, buildL, List.getElem_map, List.getElem_finRange, List.getElem_range,
        List.length_map, List.length_finRange, tri]
      have e1 : (List.map (fun i => (σ i).val) (List.finRange n)).getD i 0 = (σ ⟨i, hi⟩).val := by
        simp [List.getD_eq_getElem?_getD, hi]
      have e2 : (List.map (fun i => (K.crossings i).pos) (List.finRange n)).getD i false
          = (K.crossings ⟨i, hi⟩).pos := by
        simp [List.getD_eq_getElem?_getD, hi]
      rw [e1, e2]
      have := ho ⟨i, hi⟩
      have := hu ⟨i, hi⟩
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, rfl⟩ <;> simp_all

end Puente



section Equivalencias

variable {n : ℕ} [NeZero n]

theorem succ_iff (p q : ℝ[n]) : p + 1 = q ↔ (p.val + 1) % (2 * n) = q.val := by
  constructor
  · rintro rfl
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  · intro h
    apply ZMod.val_injective
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    exact h

theorem adj_iff (p q : ℝ[n]) : is_adjacent p q ↔ adjB (2 * n) p.val q.val = true := by
  unfold is_adjacent adjB
  rw [succ_iff p q, succ_iff q p]
  simp

omit [NeZero n] in
theorem tri_over (c : RationalCrossing n) : (tri c).1 = c.over_pos.val := rfl

omit [NeZero n] in
theorem tri_under (c : RationalCrossing n) : (tri c).2.1 = c.under_pos.val := rfl

omit [NeZero n] in
theorem tri_pos (c : RationalCrossing n) : (tri c).2.2 = c.pos := rfl

omit [NeZero n] in
theorem interl_iff (c1 c2 : RationalCrossing n) :
    are_interlaced c1 c2 ↔ interlB (tri c1) (tri c2) = true := by
  unfold are_interlaced crossing_interval interlB tri
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem r1B_iff (K : RationalConfiguration n) (i : Fin n) :
    r1B (2 * n) (toL K) i.val = true ↔ is_R1_candidate K i := by
  unfold r1B is_R1_candidate
  rw [toL_length, toL_getD K i.val i.isLt]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true', Fin.eta, tri_over, tri_under, ← adj_iff]
  apply and_congr Iff.rfl
  constructor
  · intro h j hj hint
    have := h j.val j.isLt
    rw [toL_getD K j.val j.isLt] at this
    rcases this with h1 | h1
    · exact hj (Fin.ext h1)
    · rw [interl_iff] at hint
      simp_all
  · intro h j hj
    by_cases hji : j = i.val
    · exact Or.inl hji
    · right
      rw [toL_getD K j hj]
      have := h ⟨j, hj⟩ (fun e => hji (by simp [← e]))
      rw [interl_iff] at this
      simpa using this

theorem r2B_iff (K : RationalConfiguration n) (a b : Fin n) :
    r2B (2 * n) (toL K) a.val b.val = true ↔ is_R2_candidate K a b := by
  unfold r2B is_R2_candidate
  rw [toL_getD K a.val a.isLt, toL_getD K b.val b.isLt]
  simp only [Fin.eta, Bool.and_eq_true, bne_iff_ne, ne_eq, ← adj_iff, interl_iff, tri_over,
    tri_under, tri_pos, Fin.val_inj, and_assoc]

theorem noCand_iff (K : RationalConfiguration n) :
    NoCand K ↔ noRedL (2 * n) (toL K) = true := by
  unfold noRedL NoCand
  rw [toL_length]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun a ha b hb => ?_⟩
    · have := h1 ⟨i, hi⟩
      rw [← r1B_iff] at this
      simpa using this
    · have := h2 ⟨a, ha⟩ ⟨b, hb⟩
      rw [← r2B_iff] at this
      simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun a b hab => ?_⟩
    · rw [← r1B_iff] at hi
      have := h1 i.val i.isLt
      simp_all
    · rw [← r2B_iff] at hab
      have := h2 a.val a.isLt b.val b.isLt
      simp_all

theorem ratio_val_eq (c : RationalCrossing n) :
    ratio_val c = ratioN (2 * n) c.over_pos.val c.under_pos.val := by
  have h1 := ZMod.val_lt c.over_pos
  unfold ratio_val modular_ratio ratioN
  have : c.under_pos - c.over_pos =
      ((c.under_pos.val + 2 * n - c.over_pos.val : ℕ) : ZMod (2 * n)) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self _
    rw [this]
    ring
  rw [this, ZMod.val_natCast]

theorem SIMEcic_eq (K : RationalConfiguration n) : SIMEcic K = simeL (2 * n) (toL K) := by
  unfold SIMEcic simeL
  congr 1
  unfold SIME toL
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp [Function.comp, tri, ratio_val_eq]

theorem rot_of_relB (K1 K2 : RationalConfiguration n) (h : relB n (toL K1) (toL K2) = true) :
    ∃ (j : Fin n) (k : ℝ[n]), ∀ i : Fin n,
      K2.crossings (i + j) = rotate_crossing k (K1.crossings i) := by
  unfold relB at h
  simp only [List.any_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨j, hj, k, hk, hall⟩ := h
  refine ⟨⟨j, hj⟩, (k : ZMod (2 * n)), fun i => ?_⟩
  have h1 := hall i.val i.isLt
  have hm : (i.val + j) % n < n := Nat.mod_lt _ (by omega)
  rw [toL_getD K2 _ hm, toL_getD K1 _ i.isLt] at h1
  have e : (i + ⟨j, hj⟩ : Fin n) = ⟨(i.val + j) % n, hm⟩ := Fin.ext (by simp [Fin.val_add])
  rw [e]
  simp only [tri, rotT, Prod.mk.injEq] at h1
  obtain ⟨ho, hu, hp⟩ := h1
  apply RationalCrossing.ext
  · apply ZMod.val_injective
    rw [ho]
    simp [rotate_crossing, ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  · apply ZMod.val_injective
    rw [hu]
    simp [rotate_crossing, ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  · simpa [rotate_crossing] using hp

end Equivalencias



section Principal

variable {n : ℕ} [NeZero n]

theorem toL_mem_cands (K : RationalConfiguration n) (hK : SortedAlt K) : toL K ∈ cands n := by
  obtain ⟨p, σ, s, hp, h1, h2, h3, h4, h5⟩ := bridge K hK
  rw [h5]
  exact buildL_mem_cands hp h1 h2 h3 h4

/-- Reduccion general: si la comprobacion finita `checkWith g n` es cierta, entonces dos
configuraciones `SortedAlt` que cumplen `g` y tienen el mismo `SIMEcic` son rotacion una de
otra (con reindexado ciclico). -/
theorem main_gen (g : List Tri → Bool) (hc : checkWith g n = true)
    (K₁ K₂ : RationalConfiguration n) (s₁ : SortedAlt K₁) (s₂ : SortedAlt K₂)
    (g₁ : g (toL K₁) = true) (g₂ : g (toL K₂) = true) (hs : SIMEcic K₁ = SIMEcic K₂) :
    ∃ (j : Fin n) (k : ℝ[n]), ∀ i : Fin n,
      K₂.crossings (i + j) = rotate_crossing k (K₁.crossings i) := by
  unfold checkWith at hc
  simp only [List.all_eq_true, List.mem_filter, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hc
  rcases hc (toL K₁) ⟨toL_mem_cands K₁ s₁, g₁⟩ (toL K₂) ⟨toL_mem_cands K₂ s₂, g₂⟩ with h | h
  · rw [← SIMEcic_eq, ← SIMEcic_eq] at h
    exact absurd hs h
  · exact rot_of_relB K₁ K₂ h

/-- Teorema principal condicional (planares, sin candidatos R1/R2). -/
theorem main_of_check (hc : check n = true)
    (K₁ K₂ : RationalConfiguration n) (s₁ : SortedAlt K₁) (s₂ : SortedAlt K₂)
    (p₁ : Planar K₁) (p₂ : Planar K₂) (c₁ : NoCand K₁) (c₂ : NoCand K₂)
    (hs : SIMEcic K₁ = SIMEcic K₂) :
    ∃ (j : Fin n) (k : ℝ[n]), ∀ i : Fin n,
      K₂.crossings (i + j) = rotate_crossing k (K₁.crossings i) := by
  refine main_gen (goodL n) hc K₁ K₂ s₁ s₂ ?_ ?_ hs
  · simp only [goodL, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(noCand_iff K₁).1 c₁, p₁⟩
  · simp only [goodL, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(noCand_iff K₂).1 c₂, p₂⟩

/-- Teorema principal condicional, variante mas fuerte (sin exigir planaridad). -/
theorem main_of_checkNP (hc : checkNP n = true)
    (K₁ K₂ : RationalConfiguration n) (s₁ : SortedAlt K₁) (s₂ : SortedAlt K₂)
    (c₁ : NoCand K₁) (c₂ : NoCand K₂) (hs : SIMEcic K₁ = SIMEcic K₂) :
    ∃ (j : Fin n) (k : ℝ[n]), ∀ i : Fin n,
      K₂.crossings (i + j) = rotate_crossing k (K₁.crossings i) :=
  main_gen (goodNP n) hc K₁ K₂ s₁ s₂ ((noCand_iff K₁).1 c₁) ((noCand_iff K₂).1 c₂) hs

end Principal


/-! ## Comprobaciones finitas (`decide +kernel`) -/

theorem check_3 : check 3 = true := by decide +kernel
theorem check_4 : check 4 = true := by decide +kernel
theorem check_5 : check 5 = true := by decide +kernel
theorem checkNP_3 : checkNP 3 = true := by decide +kernel
theorem checkNP_4 : checkNP 4 = true := by decide +kernel
-- `checkNP 5` (sin filtro de planaridad) NO se demuestra aqui: el kernel supera 10 minutos y
-- una build conjunta con ella llego a abortar Lean. La variante con planaridad (`check_5`) si.

theorem cands_3 : (cands 3).length = 96 := by decide +kernel
theorem cands_4 : (cands 4).length = 768 := by decide +kernel
theorem cands_5 : (cands 5).length = 7680 := by decide +kernel

theorem good_3 : ((cands 3).filter (goodL 3)).length = 4 := by decide +kernel
theorem good_4 : ((cands 4).filter (goodL 4)).length = 8 := by decide +kernel
theorem good_5 : ((cands 5).filter (goodL 5)).length = 24 := by decide +kernel

theorem clases_3 :
    (((cands 3).filter (goodL 3)).map (simeL (2 * 3))).eraseDups.length = 2 := by decide +kernel
theorem clases_4 :
    (((cands 4).filter (goodL 4)).map (simeL (2 * 4))).eraseDups.length = 2 := by decide +kernel
theorem clases_5 :
    (((cands 5).filter (goodL 5)).map (simeL (2 * 5))).eraseDups.length = 4 := by decide +kernel

/-! ## Teorema principal para `n = 3, 4, 5` -/

/-- Reconstruccion reparada para `n = 3`: entre las configuraciones ordenadas y alternantes,
planares y sin candidatos R1/R2, el mismo `SIMEcic` implica rotacion (con reindexado ciclico). -/
theorem reconstruccion_3 (K₁ K₂ : RationalConfiguration 3) (s₁ : SortedAlt K₁)
    (s₂ : SortedAlt K₂) (p₁ : Planar K₁) (p₂ : Planar K₂) (c₁ : NoCand K₁) (c₂ : NoCand K₂)
    (hs : SIMEcic K₁ = SIMEcic K₂) :
    ∃ (j : Fin 3) (k : ℝ[3]), ∀ i : Fin 3,
      K₂.crossings (i + j) = rotate_crossing k (K₁.crossings i) :=
  main_of_check check_3 K₁ K₂ s₁ s₂ p₁ p₂ c₁ c₂ hs

/-- Igual para `n = 4`. -/
theorem reconstruccion_4 (K₁ K₂ : RationalConfiguration 4) (s₁ : SortedAlt K₁)
    (s₂ : SortedAlt K₂) (p₁ : Planar K₁) (p₂ : Planar K₂) (c₁ : NoCand K₁) (c₂ : NoCand K₂)
    (hs : SIMEcic K₁ = SIMEcic K₂) :
    ∃ (j : Fin 4) (k : ℝ[4]), ∀ i : Fin 4,
      K₂.crossings (i + j) = rotate_crossing k (K₁.crossings i) :=
  main_of_check check_4 K₁ K₂ s₁ s₂ p₁ p₂ c₁ c₂ hs

/-- Igual para `n = 5`. -/
theorem reconstruccion_5 (K₁ K₂ : RationalConfiguration 5) (s₁ : SortedAlt K₁)
    (s₂ : SortedAlt K₂) (p₁ : Planar K₁) (p₂ : Planar K₂) (c₁ : NoCand K₁) (c₂ : NoCand K₂)
    (hs : SIMEcic K₁ = SIMEcic K₂) :
    ∃ (j : Fin 5) (k : ℝ[5]), ∀ i : Fin 5,
      K₂.crossings (i + j) = rotate_crossing k (K₁.crossings i) :=
  main_of_check check_5 K₁ K₂ s₁ s₂ p₁ p₂ c₁ c₂ hs

/-- Variante mas fuerte para `n = 3`: sin hipotesis de planaridad. -/
theorem reconstruccionNP_3 (K₁ K₂ : RationalConfiguration 3) (s₁ : SortedAlt K₁)
    (s₂ : SortedAlt K₂) (c₁ : NoCand K₁) (c₂ : NoCand K₂) (hs : SIMEcic K₁ = SIMEcic K₂) :
    ∃ (j : Fin 3) (k : ℝ[3]), ∀ i : Fin 3,
      K₂.crossings (i + j) = rotate_crossing k (K₁.crossings i) :=
  main_of_checkNP checkNP_3 K₁ K₂ s₁ s₂ c₁ c₂ hs

/-- Variante mas fuerte para `n = 4`: sin hipotesis de planaridad. -/
theorem reconstruccionNP_4 (K₁ K₂ : RationalConfiguration 4) (s₁ : SortedAlt K₁)
    (s₂ : SortedAlt K₂) (c₁ : NoCand K₁) (c₂ : NoCand K₂) (hs : SIMEcic K₁ = SIMEcic K₂) :
    ∃ (j : Fin 4) (k : ℝ[4]), ∀ i : Fin 4,
      K₂.crossings (i + j) = rotate_crossing k (K₁.crossings i) :=
  main_of_checkNP checkNP_4 K₁ K₂ s₁ s₂ c₁ c₂ hs

/-! ## Contraejemplos -/

section Contraejemplos

/-- Cruce de `n` cruces a partir de naturales (las posiciones se leen modulo `2n`). -/
def mkC (n : ℕ) (o u : ℕ) (s : Bool)
    (h : ((o : ℕ) : ZMod (2 * n)) ≠ ((u : ℕ) : ZMod (2 * n)) := by decide) :
    RationalCrossing n := ⟨(o : ZMod (2 * n)), (u : ZMod (2 * n)), h, s⟩

/-- Sonda 16: tres cruces antipodales en orden creciente (`SortedAlt` falla por paridad). -/
def kA : RationalConfiguration 3 where
  crossings := fun i => if i = 0 then mkC 3 0 3 true else if i = 1 then mkC 3 1 4 true
    else mkC 3 2 5 true
  coverage := by decide

/-- Sonda 16: los mismos cruces con los indices 1 y 2 intercambiados. -/
def kB : RationalConfiguration 3 where
  crossings := fun i => if i = 0 then mkC 3 0 3 true else if i = 1 then mkC 3 2 5 true
    else mkC 3 1 4 true
  coverage := by decide

theorem kA_kB_mismas_razones :
    ∀ i : Fin 3, ratio_val (kA.crossings i) = ratio_val (kB.crossings i) := by
  decide

theorem kB_no_ordenada : ¬ (∀ i j : Fin 3, i < j →
    (kB.crossings i).over_pos.val < (kB.crossings j).over_pos.val) := by
  intro h
  have := h 1 2 (by decide)
  revert this
  decide

theorem kA_no_alternante : ¬ SortedAlt kA := by
  intro h
  have := h.2 0 1
  revert this
  decide

theorem kB_no_SortedAlt : ¬ SortedAlt kB := fun h => kB_no_ordenada h.1

theorem kA_kB_mismo_SIMEcic : SIMEcic kA = SIMEcic kB := by decide

/-- Ni siquiera existe una relacion de rotacion (con reindexado ciclico) entre `kA` y `kB`. -/
theorem kA_kB_no_rotacion : ¬ ∃ (j : Fin 3) (k : ℝ[3]), ∀ i : Fin 3,
    kB.crossings (i + j) = rotate_crossing k (kA.crossings i) := by
  decide

/-- Trebol `(0,3,+),(4,1,+),(2,5,+)` (alternante, planar, sin candidatos). -/
def tA : RationalConfiguration 3 where
  crossings := fun i => if i = 0 then mkC 3 0 3 true else if i = 1 then mkC 3 4 1 true
    else mkC 3 2 5 true
  coverage := by decide

theorem tA_planar : Planar tA := by decide

theorem tA_alternante : ∀ i j : Fin 3,
    (tA.crossings i).over_pos.val % 2 = (tA.crossings j).over_pos.val % 2 := by
  decide

theorem tA_noCand : NoCand tA := (noCand_iff tA).2 (by decide)

/-- `kA = (0,3,+),(1,4,+),(2,5,+)` no es planar. -/
theorem kA_no_planar : ¬ Planar kA := by decide

theorem kA_no_alternante' : ¬ (∀ i j : Fin 3,
    (kA.crossings i).over_pos.val % 2 = (kA.crossings j).over_pos.val % 2) := by
  intro h
  have := h 0 1
  revert this
  decide

theorem tA_kA_mismo_SIMEcic : SIMEcic tA = SIMEcic kA := by decide

theorem tA_kA_no_rotacion : ¬ ∃ (j : Fin 3) (k : ℝ[3]), ∀ i : Fin 3,
    kA.crossings (i + j) = rotate_crossing k (tA.crossings i) := by
  decide

/-- Par no alternante de `n = 4`: planares, sin candidatos, mismo `SIMEcic`, no rotacion. -/
def mA : RationalConfiguration 4 where
  crossings := fun i => if i = 0 then mkC 4 0 3 false else if i = 1 then mkC 4 1 6 false
    else if i = 2 then mkC 4 2 5 true else mkC 4 7 4 true
  coverage := by decide

def mB : RationalConfiguration 4 where
  crossings := fun i => if i = 0 then mkC 4 0 3 false else if i = 1 then mkC 4 5 2 false
    else if i = 2 then mkC 4 6 1 true else mkC 4 7 4 true
  coverage := by decide

theorem mA_planar : Planar mA := by decide
theorem mB_planar : Planar mB := by decide
theorem mA_noCand : NoCand mA := (noCand_iff mA).2 (by decide)
theorem mB_noCand : NoCand mB := (noCand_iff mB).2 (by decide)
theorem mA_mB_mismo_SIMEcic : SIMEcic mA = SIMEcic mB := by decide

theorem mA_mB_no_rotacion : ¬ ∃ (j : Fin 4) (k : ℝ[4]), ∀ i : Fin 4,
    mB.crossings (i + j) = rotate_crossing k (mA.crossings i) := by
  decide

theorem mA_no_alternante : ¬ (∀ i j : Fin 4,
    (mA.crossings i).over_pos.val % 2 = (mA.crossings j).over_pos.val % 2) := by
  intro h
  have := h 0 1
  revert this
  decide

theorem mB_no_alternante : ¬ (∀ i j : Fin 4,
    (mB.crossings i).over_pos.val % 2 = (mB.crossings j).over_pos.val % 2) := by
  intro h
  have := h 0 1
  revert this
  decide

end Contraejemplos


end Reconstruccion
end TMENudos

/-! ## Teoremas de `Basic` que dependen de `reconstruct_from_first` (falso)

Calculado recorriendo todos los teoremas de `TMENudos` con `CollectAxioms` (solo estos cuatro
usan el axioma):
* `TMENudos.rotation_of_ratio_pos_eq`
* `TMENudos.same_IME_implies_rotation`
* `TMENudos.same_SIME_implies_rotation`
* `TMENudos.IME_complete`
`isotopic_irreducible_same_SIME` (direccion «isotopicos implica mismo SIME») no usa ese axioma, pero
depende de `axiom_irreducible_is_minimal` y de `minimal_isotopic_implies_rotation` (A6 y A7), que
son sospechosos y NO estan refutados formalmente. Lo que SI se refuta aqui es la direccion
contraria de `IME_complete` (mismo SIME implica isotopicos) para irreducibles no alternantes. -/

#print axioms TMENudos.Reconstruccion.bridge
#print axioms TMENudos.Reconstruccion.noCand_iff
#print axioms TMENudos.Reconstruccion.SIMEcic_eq
#print axioms TMENudos.Reconstruccion.rot_of_relB
#print axioms TMENudos.Reconstruccion.reconstruccion_3
#print axioms TMENudos.Reconstruccion.reconstruccion_4
#print axioms TMENudos.Reconstruccion.reconstruccion_5
#print axioms TMENudos.Reconstruccion.kA_kB_no_rotacion
#print axioms TMENudos.Reconstruccion.mA_mB_no_rotacion
#print axioms TMENudos.isotopic_irreducible_same_SIME
