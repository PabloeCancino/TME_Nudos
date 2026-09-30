import TMENudos.Etapa1_R2

namespace TMENudos.Invariancia

namespace R3

/-! ### Parte finita: las seis letras nuevas y el grafo local de nueve aristas -/

/-- Letras nuevas: `(k, b)` es el paso de la hebra `k` por el cruce con la hebra `k+1`
(`b = false`) o `k+2` (`b = true`). -/
abbrev Lt : Type := Fin 3 × Bool

/-- Vértices locales: las tres aristas base (`inl k`, la arista `e k`) y las seis letras. -/
abbrev Vl : Type := Fin 3 ⊕ Lt

/-- La otra hebra del cruce que contiene la letra `l`. -/
def oth (l : Lt) : Fin 3 := l.1 + (if l.2 then 2 else 1)

/-- La otra letra del mismo cruce. -/
def pL (l : Lt) : Lt := (oth l, !l.2)

/-- Índice del cruce de la letra `l` (`{0,1} ↦ 1`, `{0,2} ↦ 2`, `{1,2} ↦ 0`). -/
def cx (l : Lt) : Fin 3 := l.1 + oth l

/-- Una de las dos letras del cruce `c` (la de la hebra menor). -/
def lo : Fin 3 → Lt
  | 0 => (1, false)
  | 1 => (0, false)
  | 2 => (0, true)

def allLt : List Lt := [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true)]

def allBp : List (Fin 3 × Bool) := allLt

def allVl : List Vl := [.inl 0, .inl 1, .inl 2] ++ allLt.map .inr

/-- Predecesor de la letra `l` en el orden `o` (`o k = false`: la primera letra de la hebra `k`
es la que cruza con `k+1`). -/
def prevV (o : Fin 3 → Bool) (l : Lt) : Vl :=
  if l.2 = o l.1 then .inl l.1 else .inr (l.1, o l.1)

/-- Suavización del cruce de la letra `l` con orientación `ori`, como relación booleana. -/
def smB (o : Fin 3 → Bool) (l : Lt) (ori : Bool) (u v : Vl) : Bool :=
  if ori then (decide (u = prevV o l) && decide (v = .inr (pL l))) ||
      (decide (u = prevV o (pL l)) && decide (v = .inr l))
  else (decide (u = prevV o l) && decide (v = prevV o (pL l))) ||
      (decide (u = .inr l) && decide (v = .inr (pL l)))

/-- Relación local de un estado: `ob c` es la orientación de la suavización del cruce `c`. -/
def NB (o ob : Fin 3 → Bool) (u v : Vl) : Bool :=
  smB o (lo 0) (ob 0) u v || smB o (lo 1) (ob 1) u v || smB o (lo 2) (ob 2) u v

/-- Punto frontera: `(k, false)` es la arista base de la hebra `k`, `(k, true)` la última. -/
def bpV (o : Fin 3 → Bool) (p : Fin 3 × Bool) : Vl :=
  if p.2 then .inr (p.1, !o p.1) else .inl p.1

def r1B (o ob : Fin 3 → Bool) (u v : Vl) : Bool := decide (u = v) || NB o ob u v || NB o ob v u

def rstep (R : Vl → Vl → Bool) (u v : Vl) : Bool := allVl.any fun w => R u w && R w v

/-- Alcanzabilidad local (caminos de longitud ≤ 8). -/
def reachB (o ob : Fin 3 → Bool) : Vl → Vl → Bool := rstep (rstep (rstep (r1B o ob)))

/-- Representante frontera de cada vértice local (`none` en los lazos cerrados). -/
def rep (o ob : Fin 3 → Bool) (u : Vl) : Option (Fin 3 × Bool) :=
  match allBp.find? (fun p => decide (bpV o p = u)) with
  | some p => some p
  | none => allBp.find? (fun p => reachB o ob (bpV o p) u)

/-- Los emparejamientos de las 6 aristas frontera que aparecen (imagen de `allBp`). -/
def matL : ℕ → List (Fin 3 × Bool)
  | 0 => [(2, true), (1, false), (0, true), (2, false), (1, true), (0, false)]
  | 1 => [(2, true), (2, false), (1, true), (1, false), (0, true), (0, false)]
  | 2 => [(1, true), (1, false), (0, true), (0, false), (2, true), (2, false)]
  | 3 => [(1, true), (2, false), (2, true), (0, false), (0, true), (1, false)]
  | 4 => [(0, true), (0, false), (2, true), (2, false), (1, true), (1, false)]
  | 5 => [(1, true), (2, true), (2, false), (0, false), (1, false), (0, true)]
  | 6 => [(0, true), (0, false), (2, false), (2, true), (1, false), (1, true)]
  | 7 => [(2, false), (2, true), (1, true), (1, false), (0, false), (0, true)]
  | 8 => [(2, false), (1, false), (0, true), (2, true), (0, false), (1, true)]
  | 9 => [(1, false), (2, false), (0, false), (2, true), (0, true), (1, true)]
  | 10 => [(1, false), (1, true), (0, false), (0, true), (2, true), (2, false)]
  | 11 => [(2, true), (1, true), (2, false), (0, true), (1, false), (0, false)]
  | 12 => [(1, false), (2, true), (0, false), (2, false), (1, true), (0, true)]
  | 13 => [(2, false), (1, true), (2, true), (0, true), (0, false), (1, false)]
  | _ => allBp

/-- Emparejamiento (código) que induce el patrón local `(o, ori)`. -/
def mi : Bool → Bool → Bool → Bool → Bool → Bool → ℕ
  | false, false, false, false, false, false => 0
  | false, false, false, false, false, true => 1
  | false, false, false, false, true, false => 2
  | false, false, false, false, true, true => 3
  | false, false, false, true, false, false => 4
  | false, false, false, true, false, true => 3
  | false, false, false, true, true, false => 3
  | false, false, false, true, true, true => 3
  | false, false, true, false, false, false => 5
  | false, false, true, false, false, true => 6
  | false, false, true, false, true, false => 5
  | false, false, true, false, true, true => 5
  | false, false, true, true, false, false => 7
  | false, false, true, true, false, true => 8
  | false, false, true, true, true, false => 5
  | false, false, true, true, true, true => 2
  | false, true, false, false, false, false => 9
  | false, true, false, false, false, true => 9
  | false, true, false, false, true, false => 6
  | false, true, false, false, true, true => 9
  | false, true, false, true, false, false => 10
  | false, true, false, true, false, true => 9
  | false, true, false, true, true, false => 11
  | false, true, false, true, true, true => 1
  | false, true, true, false, false, false => 12
  | false, true, true, false, false, true => 10
  | false, true, true, false, true, false => 7
  | false, true, true, false, true, true => 13
  | false, true, true, true, false, false => 12
  | false, true, true, true, false, true => 12
  | false, true, true, true, true, false => 12
  | false, true, true, true, true, true => 4
  | true, false, false, false, false, false => 13
  | true, false, false, false, false, true => 10
  | true, false, false, false, true, false => 7
  | true, false, false, false, true, true => 12
  | true, false, false, true, false, false => 13
  | true, false, false, true, false, true => 13
  | true, false, false, true, true, false => 13
  | true, false, false, true, true, true => 4
  | true, false, true, false, false, false => 11
  | true, false, true, false, false, true => 11
  | true, false, true, false, true, false => 6
  | true, false, true, false, true, true => 11
  | true, false, true, true, false, false => 10
  | true, false, true, true, false, true => 11
  | true, false, true, true, true, false => 9
  | true, false, true, true, true, true => 1
  | true, true, false, false, false, false => 8
  | true, true, false, false, false, true => 6
  | true, true, false, false, true, false => 8
  | true, true, false, false, true, true => 8
  | true, true, false, true, false, false => 7
  | true, true, false, true, false, true => 5
  | true, true, false, true, true, false => 8
  | true, true, false, true, true, true => 2
  | true, true, true, false, false, false => 3
  | true, true, true, false, false, true => 1
  | true, true, true, false, true, false => 2
  | true, true, true, false, true, true => 0
  | true, true, true, true, false, false => 4
  | true, true, true, true, false, true => 0
  | true, true, true, true, true, false => 0
  | true, true, true, true, true, true => 0

/-- Número de lazos cerrados locales del patrón `(o, ori)`. -/
def kk : Bool → Bool → Bool → Bool → Bool → Bool → ℕ
  | false, false, false, false, false, false => 0
  | false, false, false, false, false, true => 0
  | false, false, false, false, true, false => 0
  | false, false, false, false, true, true => 0
  | false, false, false, true, false, false => 0
  | false, false, false, true, false, true => 0
  | false, false, false, true, true, false => 0
  | false, false, false, true, true, true => 1
  | false, false, true, false, false, false => 0
  | false, false, true, false, false, true => 0
  | false, false, true, false, true, false => 1
  | false, false, true, false, true, true => 0
  | false, false, true, true, false, false => 0
  | false, false, true, true, false, true => 0
  | false, false, true, true, true, false => 0
  | false, false, true, true, true, true => 0
  | false, true, false, false, false, false => 0
  | false, true, false, false, false, true => 1
  | false, true, false, false, true, false => 0
  | false, true, false, false, true, true => 0
  | false, true, false, true, false, false => 0
  | false, true, false, true, false, true => 0
  | false, true, false, true, true, false => 0
  | false, true, false, true, true, true => 0
  | false, true, true, false, false, false => 0
  | false, true, true, false, false, true => 0
  | false, true, true, false, true, false => 0
  | false, true, true, false, true, true => 0
  | false, true, true, true, false, false => 1
  | false, true, true, true, false, true => 0
  | false, true, true, true, true, false => 0
  | false, true, true, true, true, true => 0
  | true, false, false, false, false, false => 0
  | true, false, false, false, false, true => 0
  | true, false, false, false, true, false => 0
  | true, false, false, false, true, true => 0
  | true, false, false, true, false, false => 1
  | true, false, false, true, false, true => 0
  | true, false, false, true, true, false => 0
  | true, false, false, true, true, true => 0
  | true, false, true, false, false, false => 0
  | true, false, true, false, false, true => 1
  | true, false, true, false, true, false => 0
  | true, false, true, false, true, true => 0
  | true, false, true, true, false, false => 0
  | true, false, true, true, false, true => 0
  | true, false, true, true, true, false => 0
  | true, false, true, true, true, true => 0
  | true, true, false, false, false, false => 0
  | true, true, false, false, false, true => 0
  | true, true, false, false, true, false => 1
  | true, true, false, false, true, true => 0
  | true, true, false, true, false, false => 0
  | true, true, false, true, false, true => 0
  | true, true, false, true, true, false => 0
  | true, true, false, true, true, true => 0
  | true, true, true, false, false, false => 0
  | true, true, true, false, false, true => 0
  | true, true, true, false, true, false => 0
  | true, true, true, false, true, true => 0
  | true, true, true, true, false, false => 0
  | true, true, true, true, false, true => 0
  | true, true, true, true, true, false => 0
  | true, true, true, true, true, true => 1

def idxBp (p : Fin 3 × Bool) : ℕ := 2 * p.1.val + p.2.toNat

/-- El emparejamiento de código `n` como función. -/
def matOf (n : ℕ) (p : Fin 3 × Bool) : Fin 3 × Bool := (matL n).getD (idxBp p) p

def CheckEq (o ob : Fin 3 → Bool) : Bool :=
  let m := matOf (mi (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2))
  allBp.all (fun p => decide (rep o ob (bpV o p) = some p)) &&
  allVl.all (fun u => allVl.all fun v => !(NB o ob u v) ||
    (match rep o ob u, rep o ob v with
      | some p, some q => decide (p = q) || decide (m p = q) || decide (m q = p)
      | _, _ => false)) &&
  allBp.all (fun p => reachB o ob (bpV o p) (bpV o (m p))) &&
  allVl.all (fun u => match rep o ob u with
    | some p => reachB o ob (bpV o p) u
    | none => false)

def CheckCirc (o ob : Fin 3 → Bool) : Bool :=
  let m := matOf (mi (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2))
  allBp.all (fun p => decide (rep o ob (bpV o p) = some p)) &&
  allVl.all (fun u => allVl.all fun v => !(NB o ob u v) ||
    ((rep o ob u).isNone == (rep o ob v).isNone &&
    (match rep o ob u, rep o ob v with
      | some p, some q => decide (p = q) || decide (m p = q) || decide (m q = p)
      | _, _ => true))) &&
  allBp.all (fun p => reachB o ob (bpV o p) (bpV o (m p))) &&
  allVl.all (fun u => match rep o ob u with
    | some p => reachB o ob (bpV o p) u
    | none => true) &&
  allVl.all (fun u => allVl.all fun v => !(rep o ob u).isNone || !(rep o ob v).isNone ||
    reachB o ob u v) &&
  allVl.any (fun u => (rep o ob u).isNone)

theorem check_all : ∀ o0 o1 o2 x0 x1 x2 : Bool,
    (if kk o0 o1 o2 x0 x1 x2 = 0 then CheckEq ![o0, o1, o2] ![x0, x1, x2]
      else CheckCirc ![o0, o1, o2] ![x0, x1, x2]) = true := by
  sorry

theorem pL_pL : ∀ l : Lt, pL (pL l) = l := by decide

theorem pL_ne : ∀ l : Lt, pL l ≠ l := by decide

theorem cx_pL : ∀ l : Lt, cx (pL l) = cx l := by decide

theorem cx_eq : ∀ l l' : Lt, cx l = cx l' → l' = l ∨ l' = pL l := by decide

/-- La letra superior del cruce `c` según el bit `b`. -/
def tlb (b : Bool) (c : Fin 3) : Lt := if b then lo c else pL (lo c)

theorem cx_tlb : ∀ (b : Bool) (c : Fin 3), cx (tlb b c) = c := by decide

theorem tlb_pL : ∀ (b : Bool) (l : Lt),
    decide (pL l = tlb b (cx l)) = !decide (l = tlb b (cx l)) := by decide


theorem mem_allVl : ∀ u : Vl, u ∈ allVl := by
  intro u
  rcases u with k | ⟨k, b⟩ <;> fin_cases k <;> (try cases b) <;> simp [allVl, allLt]

theorem mem_allBp : ∀ p : Fin 3 × Bool, p ∈ allBp := by decide

/-- Alcanzabilidad en el grafo local. -/
def LR (o ob : Fin 3 → Bool) : Vl → Vl → Prop :=
  Relation.ReflTransGen (fun x y => NB o ob x y = true ∨ NB o ob y x = true)

theorem r1B_sound {o ob : Fin 3 → Bool} {u v : Vl} (h : r1B o ob u v = true) : LR o ob u v := by
  simp only [r1B, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · subst h
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (Or.inl h)
  · exact Relation.ReflTransGen.single (Or.inr h)

theorem rstep_sound {o ob : Fin 3 → Bool} {R : Vl → Vl → Bool}
    (hR : ∀ u v, R u v = true → LR o ob u v) {u v : Vl} (h : rstep R u v = true) : LR o ob u v := by
  simp only [rstep, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨w, -, h1, h2⟩ := h
  exact (hR _ _ h1).trans (hR _ _ h2)

theorem reachB_sound {o ob : Fin 3 → Bool} {u v : Vl} (h : reachB o ob u v = true) :
    LR o ob u v :=
  rstep_sound (fun _ _ h => rstep_sound (fun _ _ h => rstep_sound (fun _ _ h => r1B_sound h) h) h) h

/-- Contenido de `CheckEq`. -/
theorem checkEq_spec (o ob : Fin 3 → Bool) (h : CheckEq o ob = true) :
    (∀ p, rep o ob (bpV o p) = some p) ∧
    (∀ u v, NB o ob u v = true → ∃ p q, rep o ob u = some p ∧ rep o ob v = some q ∧
      (p = q ∨ matOf (mi (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2)) p = q ∨
        matOf (mi (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2)) q = p)) ∧
    (∀ p, reachB o ob (bpV o p) (bpV o (matOf (mi (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2)) p)) =
      true) ∧
    (∀ u, ∃ p, rep o ob u = some p ∧ reachB o ob (bpV o p) u = true) := by
  simp only [CheckEq, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hB, h1⟩, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    simpa using hB p (mem_allBp p)
  · intro u v hN
    have := h1 u (mem_allVl u) v (mem_allVl v)
    rcases hr : rep o ob u with _ | p <;> rcases hr' : rep o ob v with _ | q <;>
      simp [hr, hr', hN] at this
    exact ⟨p, q, rfl, rfl, or_assoc.1 this⟩
  · intro p
    simpa using h2 p (mem_allBp p)
  · intro u
    have := h3 u (mem_allVl u)
    rcases hr : rep o ob u with _ | p
    · simp [hr] at this
    · simp only [hr] at this
      exact ⟨p, rfl, this⟩

/-- Contenido de `CheckCirc`. -/
theorem checkCirc_spec (o ob : Fin 3 → Bool) (h : CheckCirc o ob = true) :
    (∀ p, rep o ob (bpV o p) = some p) ∧
    (∀ u v, NB o ob u v = true → ((rep o ob u = none ↔ rep o ob v = none) ∧
      ∀ p q, rep o ob u = some p → rep o ob v = some q →
      (p = q ∨ matOf (mi (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2)) p = q ∨
        matOf (mi (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2)) q = p))) ∧
    (∀ p, reachB o ob (bpV o p) (bpV o (matOf (mi (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2)) p)) =
      true) ∧
    (∀ u p, rep o ob u = some p → reachB o ob (bpV o p) u = true) ∧
    (∀ u v, rep o ob u = none → rep o ob v = none → reachB o ob u v = true) ∧
    (∃ u, rep o ob u = none) := by
  simp only [CheckCirc, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hB, h1⟩, h2⟩, h3⟩, h4⟩, u0, -, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    simpa using hB p (mem_allBp p)
  · intro u v hN
    have := h1 u (mem_allVl u) v (mem_allVl v)
    rcases hr : rep o ob u with _ | p <;> rcases hr' : rep o ob v with _ | q <;>
      simp [hr, hr', hN] at this ⊢
    exact or_assoc.1 this
  · intro p
    simpa using h2 p (mem_allBp p)
  · intro u p hp
    have := h3 u (mem_allVl u)
    simpa [hp] using this
  · intro u v hu hv
    have := h4 u (mem_allVl u) v (mem_allVl v)
    simpa [hu, hv] using this
  · exact ⟨u0, by simpa using h5⟩


theorem kk_le_one : ∀ a b c d e f : Bool, kk a b c d e f ≤ 1 := by decide


/-! ### Álgebra final: la identidad de Temperley-Lieb del R3 -/

section Alg

variable {K : Type*} [Field K]

/-- Peso de un cruce: `A` para la suavización A y `A⁻¹` para la B. -/
def wt (A : K) (b : Bool) : K := if b then A else A⁻¹

/-- El valor del círculo. -/
def dd (A : K) : K := -(A ^ 2) - A⁻¹ ^ 2

/-- La suma sobre los estados de los tres cruces nuevos, en función de los valores `T n` de los
emparejamientos posibles (`n` es el código de `mi`). `s0 s1 s2` son los signos de los cruces. -/
def FF (A : K) (T : ℕ → K) (o0 o1 o2 s0 s1 s2 : Bool) : K :=
  ∑ b0 : Bool, ∑ b1 : Bool, ∑ b2 : Bool,
    (wt A b0 * wt A b1 * wt A b2) *
      (dd A ^ kk o0 o1 o2 (b0 == s0) (b1 == s1) (b2 == s2) *
        T (mi o0 o1 o2 (b0 == s0) (b1 == s1) (b2 == s2)))

/-- Patrones `(orden, signo)` de un R3 real (tabla del paso 0): se excluye exactamente el caso
`(s0 ≠ s1) = (o0 ≠ o2)` y `(s1 ≠ s2) = (o1 ≠ o2)`, el de las alturas cíclicas. -/
def validR3 (o0 o1 o2 s0 s1 s2 : Bool) : Bool :=
  !(((s0 != s1) == (o0 != o2)) && ((s1 != s2) == (o1 != o2)))

/-- **La identidad de Temperley-Lieb del R3**, para cualquier valor `T n` de los emparejamientos. -/
theorem FF_invariant (A : K) (hA : A ≠ 0) (T : ℕ → K) (o0 o1 o2 s0 s1 s2 : Bool)
    (hv : validR3 o0 o1 o2 s0 s1 s2 = true) :
    FF A T o0 o1 o2 s0 s1 s2 = FF A T (!o0) (!o1) (!o2) s0 s1 s2 := by
  cases o0 <;> cases o1 <;> cases o2 <;> cases s0 <;> cases s1 <;> cases s2 <;>
    first
    | (exfalso; revert hv; decide)
    | (simp only [FF, Fintype.sum_bool, beq_true, beq_false, Bool.not_true,
        Bool.not_false]
       simp only [mi, kk]
       simp only [wt, dd, pow_zero, pow_one, Bool.false_eq_true, ↓reduceIte]
       field_simp
       ring)

end Alg

end R3

namespace GDiag

open R3

variable {ι : Type} [DecidableEq ι] [Fintype ι]

section Def

variable (D : GDiag ι) (e : Fin 3 → ι) (o : Fin 3 → Bool)

/-- Sucesor de la arista `i` en `D'`: si `i = e k`, la primera letra nueva de la hebra `k`. -/
noncomputable def nxt (i : ι) : ι ⊕ Lt :=
  if h : ∃ k, e k = i then .inr (h.choose, o h.choose) else .inl (D.next i)

/-- Predecesor de la arista `i` en `D'`: si `i = next (e k)`, la última letra de la hebra `k`. -/
noncomputable def prv (i : ι) : ι ⊕ Lt :=
  if h : ∃ k, D.next (e k) = i then .inr (h.choose, !o h.choose) else .inl (D.prev i)

variable {e}

theorem nxt_e (he : Function.Injective e) (k : Fin 3) : nxt D e o (e k) = .inr (k, o k) := by
  have h : ∃ j, e j = e k := ⟨k, rfl⟩
  have hc : h.choose = k := he h.choose_spec
  simp only [nxt, dif_pos h, hc]

theorem nxt_of_ne {i : ι} (h : ∀ k, e k ≠ i) : nxt D e o i = .inl (D.next i) := by
  have h' : ¬ ∃ k, e k = i := fun ⟨k, hk⟩ => h k hk
  simp only [nxt, dif_neg h']

theorem prv_next_e (he : Function.Injective e) (k : Fin 3) :
    prv D e o (D.next (e k)) = .inr (k, !o k) := by
  have h : ∃ j, D.next (e j) = D.next (e k) := ⟨k, rfl⟩
  have hc : h.choose = k := he (D.next.injective h.choose_spec)
  simp only [prv, dif_pos h, hc]

theorem prv_of_ne {i : ι} (h : ∀ k, D.next (e k) ≠ i) : prv D e o i = .inl (D.prev i) := by
  have h' : ¬ ∃ k, D.next (e k) = i := fun ⟨k, hk⟩ => h k hk
  simp only [prv, dif_neg h']

variable (e)

/-- La permutación siguiente del diagrama con el triángulo insertado: cada arista `e k` se
parte en `e k → (k, o k) → (k, !o k) → next (e k)`. -/
noncomputable def triNext (he : Function.Injective e) : Equiv.Perm (ι ⊕ Lt) where
  toFun
    | .inl i => nxt D e o i
    | .inr (k, b) => if b = o k then .inr (k, !b) else .inl (D.next (e k))
  invFun
    | .inl i => prv D e o i
    | .inr (k, b) => if b = o k then .inl (e k) else .inr (k, o k)
  left_inv := by
    rintro (i | ⟨k, b⟩)
    · by_cases h : ∃ k, e k = i
      · obtain ⟨k, rfl⟩ := h
        simp [nxt_e D o he]
      · have h' : ∀ k, e k ≠ i := fun k hk => h ⟨k, hk⟩
        have h'' : ∀ k, D.next (e k) ≠ D.next i := fun k hk => h' k (D.next.injective hk)
        simp [nxt_of_ne D o h', prv_of_ne D o h'', prev]
    · by_cases hb : b = o k
      · subst hb
        simp
      · have : b = !o k := by cases b <;> cases h : o k <;> simp_all
        subst this
        simp [prv_next_e D o he]
  right_inv := by
    rintro (i | ⟨k, b⟩)
    · by_cases h : ∃ k, D.next (e k) = i
      · obtain ⟨k, rfl⟩ := h
        simp [prv_next_e D o he]
      · have h' : ∀ k, D.next (e k) ≠ i := fun k hk => h ⟨k, hk⟩
        have h'' : ∀ k, e k ≠ D.next.symm i := fun k hk => h' k (by rw [hk]; simp)
        simp [prv_of_ne D o h', prev, nxt_of_ne D o h'']
    · by_cases hb : b = o k
      · subst hb
        simp [nxt_e D o he]
      · simp [hb]
        cases b <;> cases h : o k <;> simp_all

end Def

section Tri

/-- **El movimiento R3.** Dadas tres aristas distintas `e 0, e 1, e 2` de `D`, se inserta el
triángulo de tres cruces: en la hebra `k` las dos letras nuevas van en el orden `o k`
(`o k = false`: primero el cruce con la hebra `k+1`). `ovc c` dice qué letra del cruce `c` es la
superior y `sgc c` es su signo. Las dos caras del R3 son `tri … o …` y `tri … (¬ o) …`: solo
cambia `next`. -/
noncomputable def tri (D : GDiag ι) (e : Fin 3 → ι) (he : Function.Injective e)
    (o ovc sgc : Fin 3 → Bool) : GDiag (ι ⊕ Lt) where
  next := triNext D e o he
  partner
    | .inl i => .inl (D.partner i)
    | .inr l => .inr (pL l)
  ovr
    | .inl i => D.ovr i
    | .inr l => decide (l = tlb (ovc (cx l)) (cx l))
  sign
    | .inl i => D.sign i
    | .inr l => sgc (cx l)
  partner_partner := by
    rintro (i | l)
    · simp [D.partner_partner]
    · simp [pL_pL]
  partner_ne := by
    rintro (i | l)
    · simp [D.partner_ne]
    · simp [pL_ne]
  ovr_partner := by
    rintro (i | l)
    · simpa using D.ovr_partner i
    · simp only [cx_pL]
      exact tlb_pL _ _
  sign_partner := by
    rintro (i | l)
    · simpa using D.sign_partner i
    · simp [cx_pL]
  free := D.free

variable (D : GDiag ι) (e : Fin 3 → ι) (he : Function.Injective e) (o ovc sgc : Fin 3 → Bool)

@[simp] theorem tri_partner_inl (i : ι) :
    (tri D e he o ovc sgc).partner (.inl i) = .inl (D.partner i) := rfl

@[simp] theorem tri_partner_inr (l : Lt) :
    (tri D e he o ovc sgc).partner (.inr l) = .inr (pL l) := rfl

@[simp] theorem tri_sign_inl (i : ι) : (tri D e he o ovc sgc).sign (.inl i) = D.sign i := rfl

@[simp] theorem tri_sign_inr (l : Lt) : (tri D e he o ovc sgc).sign (.inr l) = sgc (cx l) := rfl

@[simp] theorem tri_ovr_inl (i : ι) : (tri D e he o ovc sgc).ovr (.inl i) = D.ovr i := rfl

theorem tri_ovr_inr (l : Lt) :
    (tri D e he o ovc sgc).ovr (.inr l) = decide (l = tlb (ovc (cx l)) (cx l)) := rfl

theorem tri_prev_inr (k : Fin 3) (b : Bool) :
    (tri D e he o ovc sgc).prev (.inr (k, b)) =
      if b = o k then .inl (e k) else .inr (k, o k) := rfl

theorem tri_prev_inl (z : ι) : (tri D e he o ovc sgc).prev (.inl z) = prv D e o z := rfl


/-! ### Cruces y estados -/

/-- Los cruces de `D'` son los de `D` más los tres nuevos (índice `cx`). -/
def r3Cross : (tri D e he o ovc sgc).Cross ≃ D.Cross ⊕ Fin 3 where
  toFun z :=
    match z with
    | ⟨.inl i, h⟩ => .inl ⟨i, h⟩
    | ⟨.inr l, _⟩ => .inr (cx l)
  invFun w :=
    match w with
    | .inl x => ⟨.inl x.1, x.2⟩
    | .inr c => ⟨.inr (tlb (ovc c) c), by simp [tri_ovr_inr, cx_tlb]⟩
  left_inv := by
    rintro ⟨z, h⟩
    rcases z with i | l
    · rfl
    · have hl : l = tlb (ovc (cx l)) (cx l) := by simpa [tri_ovr_inr] using h
      exact Subtype.ext (congrArg Sum.inr hl.symm)
  right_inv := by
    rintro (x | c)
    · rfl
    · simp [cx_tlb]

/-- `(Fin 3 → Bool) ≃ Bool³`. -/
def tripleEquiv : (Fin 3 → Bool) ≃ Bool × Bool × Bool where
  toFun f := (f 0, f 1, f 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl

/-- Estados de `D'` = estados de `D` × estados de los tres cruces nuevos. -/
def r3State : ((tri D e he o ovc sgc).Cross → Bool) ≃ (D.Cross → Bool) × Bool × Bool × Bool :=
  ((r3Cross D e he o ovc sgc).arrowCongr (Equiv.refl Bool)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr (Equiv.refl _) tripleEquiv))

theorem r3State_symm_apply (σ : D.Cross → Bool) (b0 b1 b2 : Bool)
    (z : (tri D e he o ovc sgc).Cross) :
    (r3State D e he o ovc sgc).symm (σ, b0, b1, b2) z =
      Sum.elim σ ![b0, b1, b2] (r3Cross D e he o ovc sgc z) := rfl

theorem r3State_symm_inl (σ : D.Cross → Bool) (b0 b1 b2 : Bool) (x : D.Cross) :
    (r3State D e he o ovc sgc).symm (σ, b0, b1, b2)
      ((r3Cross D e he o ovc sgc).symm (.inl x)) = σ x := by
  simp [r3State_symm_apply]

theorem r3State_symm_inr (σ : D.Cross → Bool) (b0 b1 b2 : Bool) (j : Fin 3) :
    (r3State D e he o ovc sgc).symm (σ, b0, b1, b2)
      ((r3Cross D e he o ovc sgc).symm (.inr j)) = ![b0, b1, b2] j := by
  simp [r3State_symm_apply]

theorem r3_weight {K : Type*} [Field K] (A : K) (σ : D.Cross → Bool) (b0 b1 b2 : Bool) :
    (∏ z : (tri D e he o ovc sgc).Cross,
        if (r3State D e he o ovc sgc).symm (σ, b0, b1, b2) z then A else A⁻¹) =
      (∏ x : D.Cross, if σ x then A else A⁻¹) *
        ((if b0 then A else A⁻¹) * (if b1 then A else A⁻¹) * (if b2 then A else A⁻¹)) := by
  rw [Fintype.prod_equiv (r3Cross D e he o ovc sgc) _
    (fun w => if (r3State D e he o ovc sgc).symm (σ, b0, b1, b2)
      ((r3Cross D e he o ovc sgc).symm w) then A else A⁻¹)
    (by intro z; simp)]
  rw [Fintype.prod_sum_type, Fin.prod_univ_three]
  simp only [r3State_symm_inl, r3State_symm_inr]
  rfl

theorem r3_rel_iff (σ : D.Cross → Bool) (b0 b1 b2 : Bool) (a c : ι ⊕ Lt) :
    (tri D e he o ovc sgc).rel ((r3State D e he o ovc sgc).symm (σ, b0, b1, b2)) a c ↔
      (∃ x : D.Cross, (tri D e he o ovc sgc).smoothRel (.inl x.1) (σ x == D.sign x.1) a c) ∨
        ∃ j : Fin 3, (tri D e he o ovc sgc).smoothRel (.inr (tlb (ovc j) j))
          (![b0, b1, b2] j == sgc j) a c := by
  unfold rel
  refine (Equiv.exists_congr_left (r3Cross D e he o ovc sgc)).trans ?_
  rw [Sum.exists]
  apply or_congr
  · apply exists_congr
    intro x
    rw [r3State_symm_inl]
    rfl
  · apply exists_congr
    intro j
    rw [r3State_symm_inr]
    have h1 : ((r3Cross D e he o ovc sgc).symm (.inr j)).1 = .inr (tlb (ovc j) j) := rfl
    rw [h1, tri_sign_inr, cx_tlb]


/-! ### La parte "vieja" y la parte "nueva" del grafo de un estado -/

/-- Aristas del grafo reducido: `ι ⊕ Fin 3`, donde `inr k` es la última arista de la hebra `k`. -/
noncomputable def prevR (z : ι) : ι ⊕ Fin 3 :=
  if h : ∃ k, D.next (e k) = z then .inr h.choose else .inl (D.prev z)

/-- Inclusión del grafo reducido en las aristas de `D'`. -/
def piF : ι ⊕ Fin 3 → ι ⊕ Lt
  | .inl i => .inl i
  | .inr k => .inr (k, !o k)

/-- Inclusión de los vértices locales en las aristas de `D'`. -/
def phi : Vl → ι ⊕ Lt
  | .inl k => .inl (e k)
  | .inr l => .inr l

theorem prv_eq (z : ι) : prv D e o z = piF o (prevR D e z) := by
  by_cases h : ∃ k, D.next (e k) = z
  · simp only [prv, prevR, dif_pos h, piF]
  · simp only [prv, prevR, dif_neg h, piF]

theorem tri_prev_inl' (z : ι) :
    (tri D e he o ovc sgc).prev (.inl z) = piF o (prevR D e z) := prv_eq D e o z

/-- Suavización del cruce viejo `x` en el grafo reducido. -/
def smR (x : ι) (ori : Bool) (u v : ι ⊕ Fin 3) : Prop :=
  (ori = true ∧ ((u = prevR D e x ∧ v = .inl (D.partner x)) ∨
      (u = prevR D e (D.partner x) ∧ v = .inl x))) ∨
  (ori = false ∧ ((u = prevR D e x ∧ v = prevR D e (D.partner x)) ∨
      (u = .inl x ∧ v = .inl (D.partner x))))

/-- La parte vieja del grafo reducido de un estado `σ` de `D`. -/
def OaD (σ : D.Cross → Bool) (u v : ι ⊕ Fin 3) : Prop :=
  ∃ x : D.Cross, smR D e x.1 (σ x == D.sign x.1) u v

/-- La parte vieja del grafo de `D'`: la imagen de `OaD`. -/
def Ob (σ : D.Cross → Bool) (a c : ι ⊕ Lt) : Prop :=
  ∃ x y, a = piF o x ∧ c = piF o y ∧ OaD D e σ x y

theorem old_iff (σ : D.Cross → Bool) (a c : ι ⊕ Lt) :
    (∃ x : D.Cross, (tri D e he o ovc sgc).smoothRel (.inl x.1) (σ x == D.sign x.1) a c) ↔
      Ob D e o σ a c := by
  constructor
  · rintro ⟨x, ⟨ho, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨ho, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩⟩
    · exact ⟨prevR D e x.1, .inl (D.partner x.1), by rw [h1, tri_prev_inl'], by rw [h2]; rfl,
        x, Or.inl ⟨ho, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨prevR D e (D.partner x.1), .inl x.1,
        by rw [h1, tri_partner_inl, tri_prev_inl'], by rw [h2]; rfl,
        x, Or.inl ⟨ho, Or.inr ⟨rfl, rfl⟩⟩⟩
    · exact ⟨prevR D e x.1, prevR D e (D.partner x.1), by rw [h1, tri_prev_inl'],
        by rw [h2, tri_partner_inl, tri_prev_inl'], x, Or.inr ⟨ho, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨.inl x.1, .inl (D.partner x.1), by rw [h1]; rfl, by rw [h2]; rfl,
        x, Or.inr ⟨ho, Or.inr ⟨rfl, rfl⟩⟩⟩
  · rintro ⟨u, v, rfl, rfl, x, ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩⟩
    · exact ⟨x, Or.inl ⟨ho, Or.inl ⟨(tri_prev_inl' D e he o ovc sgc x.1).symm, rfl⟩⟩⟩
    · exact ⟨x, Or.inl ⟨ho, Or.inr ⟨by rw [tri_partner_inl, tri_prev_inl'], rfl⟩⟩⟩
    · exact ⟨x, Or.inr ⟨ho, Or.inl ⟨(tri_prev_inl' D e he o ovc sgc x.1).symm,
        by rw [tri_partner_inl, tri_prev_inl']⟩⟩⟩
    · exact ⟨x, Or.inr ⟨ho, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- La parte nueva del grafo de `D'`: la imagen de la relación local `NB`. -/
def Nb (ob : Fin 3 → Bool) (a c : ι ⊕ Lt) : Prop :=
  ∃ u v, a = phi e u ∧ c = phi e v ∧ NB o ob u v = true

omit [DecidableEq ι] [Fintype ι] in
theorem phi_inj (he : Function.Injective e) : Function.Injective (phi e) := by
  rintro (i | l) (j | m) h
  · simp only [phi, Sum.inl.injEq] at h
    rw [he h]
  · simp [phi] at h
  · simp [phi] at h
  · simp only [phi, Sum.inr.injEq] at h
    rw [h]

theorem tri_prev_phi (l : Lt) : (tri D e he o ovc sgc).prev (.inr l) = phi e (prevV o l) := by
  rcases l with ⟨k, b⟩
  by_cases h : b = o k <;> simp [tri_prev_inr, prevV, h, phi]

theorem sm_phi (l : Lt) (ori : Bool) (u v : Vl) :
    (tri D e he o ovc sgc).smoothRel (.inr l) ori (phi e u) (phi e v) ↔
      smB o l ori u v = true := by
  have hi : ∀ a b, phi e a = phi e b ↔ a = b := fun a b => (phi_inj e he).eq_iff
  have h1 : (Sum.inr (pL l) : ι ⊕ Lt) = phi e (.inr (pL l)) := rfl
  have h2 : (Sum.inr l : ι ⊕ Lt) = phi e (.inr l) := rfl
  cases ori <;>
    simp only [smoothRel, tri_partner_inr, tri_prev_phi, smB] <;>
    rw [h1, h2] <;>
    simp [hi]

theorem sm_exists (l : Lt) (ori : Bool) (a c : ι ⊕ Lt)
    (h : (tri D e he o ovc sgc).smoothRel (.inr l) ori a c) :
    ∃ u v, a = phi e u ∧ c = phi e v ∧ smB o l ori u v = true := by
  have key : ∀ u v, a = phi e u → c = phi e v → ∃ u v, a = phi e u ∧ c = phi e v ∧
      smB o l ori u v = true := by
    intro u v hu hv
    refine ⟨u, v, hu, hv, (sm_phi D e he o ovc sgc l ori u v).1 ?_⟩
    rw [← hu, ← hv]
    exact h
  rcases h with ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact key (prevV o l) (.inr (pL l)) (by rw [h1, tri_prev_phi]) (by rw [h2]; rfl)
  · exact key (prevV o (pL l)) (.inr l) (by rw [h1, tri_partner_inr, tri_prev_phi])
      (by rw [h2]; rfl)
  · exact key (prevV o l) (prevV o (pL l)) (by rw [h1, tri_prev_phi])
      (by rw [h2, tri_partner_inr, tri_prev_phi])
  · exact key (.inr l) (.inr (pL l)) (by rw [h1]; rfl) (by rw [h2]; rfl)

theorem NB_iff (ob : Fin 3 → Bool) (u v : Vl) :
    NB o ob u v = true ↔ ∃ j : Fin 3, smB o (lo j) (ob j) u v = true := by
  simp only [NB, Bool.or_eq_true]
  constructor
  · rintro ((h | h) | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  · rintro ⟨j, h⟩
    fin_cases j
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem symX (j : Fin 3) (ori : Bool) (a c : ι ⊕ Lt) :
    ((tri D e he o ovc sgc).smoothRel (.inr (tlb (ovc j) j)) ori a c ∨
        (tri D e he o ovc sgc).smoothRel (.inr (tlb (ovc j) j)) ori c a) ↔
      ((tri D e he o ovc sgc).smoothRel (.inr (lo j)) ori a c ∨
        (tri D e he o ovc sgc).smoothRel (.inr (lo j)) ori c a) := by
  cases hb : ovc j
  · have := smooth_symm (tri D e he o ovc sgc) (.inr (lo j)) ori a c
    simp only [tlb, tri_partner_inr, Bool.false_eq_true, if_false] at this ⊢
    exact this.symm
  · simp [tlb]

theorem new_sym (b0 b1 b2 : Bool) (a c : ι ⊕ Lt) :
    ((∃ j : Fin 3, (tri D e he o ovc sgc).smoothRel (.inr (tlb (ovc j) j))
        (![b0, b1, b2] j == sgc j) a c) ∨
      (∃ j : Fin 3, (tri D e he o ovc sgc).smoothRel (.inr (tlb (ovc j) j))
        (![b0, b1, b2] j == sgc j) c a)) ↔
    (Nb e o (fun j => ![b0, b1, b2] j == sgc j) a c ∨
      Nb e o (fun j => ![b0, b1, b2] j == sgc j) c a) := by
  set ob : Fin 3 → Bool := fun j => ![b0, b1, b2] j == sgc j with hob
  have hY : ∀ j a c, (tri D e he o ovc sgc).smoothRel (.inr (lo j)) (ob j) a c →
      Nb e o ob a c := by
    intro j a c h
    obtain ⟨u, v, hu, hv, hs⟩ := sm_exists D e he o ovc sgc _ _ _ _ h
    exact ⟨u, v, hu, hv, (NB_iff o ob u v).2 ⟨j, hs⟩⟩
  have hN : ∀ a c, Nb e o ob a c → ∃ j, (tri D e he o ovc sgc).smoothRel (.inr (lo j)) (ob j) a c := by
    rintro a c ⟨u, v, rfl, rfl, h⟩
    obtain ⟨j, hj⟩ := (NB_iff o ob u v).1 h
    exact ⟨j, (sm_phi D e he o ovc sgc _ _ u v).2 hj⟩
  constructor
  · rintro (⟨j, h⟩ | ⟨j, h⟩)
    · rcases (symX D e he o ovc sgc j (ob j) a c).1 (Or.inl h) with h' | h'
      · exact Or.inl (hY j a c h')
      · exact Or.inr (hY j c a h')
    · rcases (symX D e he o ovc sgc j (ob j) a c).1 (Or.inr h) with h' | h'
      · exact Or.inl (hY j a c h')
      · exact Or.inr (hY j c a h')
  · rintro (h | h)
    · obtain ⟨j, hj⟩ := hN a c h
      rcases (symX D e he o ovc sgc j (ob j) a c).2 (Or.inl hj) with h' | h'
      · exact Or.inl ⟨j, h'⟩
      · exact Or.inr ⟨j, h'⟩
    · obtain ⟨j, hj⟩ := hN c a h
      rcases (symX D e he o ovc sgc j (ob j) a c).2 (Or.inr hj) with h' | h'
      · exact Or.inl ⟨j, h'⟩
      · exact Or.inr ⟨j, h'⟩

theorem r3_graph_eq (σ : D.Cross → Bool) (b0 b1 b2 : Bool) :
    (tri D e he o ovc sgc).graph ((r3State D e he o ovc sgc).symm (σ, b0, b1, b2)) =
      SimpleGraph.fromRel (fun a c => Ob D e o σ a c ∨
        Nb e o (fun j => ![b0, b1, b2] j == sgc j) a c) := by
  ext a c
  unfold graph
  rw [SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
  apply and_congr_right
  intro _
  have hn := new_sym D e he o ovc sgc b0 b1 b2 a c
  have h1 := old_iff D e he o ovc sgc σ a c
  have h2 := old_iff D e he o ovc sgc σ c a
  rw [r3_rel_iff, r3_rel_iff]
  tauto


/-! ### Conteo de componentes: la parte local se reduce a un emparejamiento de la frontera -/

/-- Punto frontera en el grafo reducido: `(k, false)` es la arista `e k` y `(k, true)` la última
arista de la hebra `k`. -/
def bpA (p : Fin 3 × Bool) : ι ⊕ Fin 3 := if p.2 then .inr p.1 else .inl (e p.1)

/-- Las aristas que el emparejamiento `m` añade al grafo reducido. -/
def NMr (m : Fin 3 × Bool → Fin 3 × Bool) (x y : ι ⊕ Fin 3) : Prop :=
  ∃ p, x = bpA e p ∧ y = bpA e (m p)

omit [DecidableEq ι] [Fintype ι] in
theorem piF_bpA (p : Fin 3 × Bool) : piF o (bpA e p) = phi e (bpV o p) := by
  rcases p with ⟨k, b⟩
  cases b <;> rfl

theorem LR_reach (σ : D.Cross → Bool) (ob : Fin 3 → Bool) {u v : Vl} (h : LR o ob u v) :
    (SimpleGraph.fromRel fun a c => Ob D e o σ a c ∨ Nb e o ob a c).Reachable
      (phi e u) (phi e v) := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hst ih =>
    refine ih.trans ?_
    rcases hst with h | h
    · exact reach_of_or_right (r := Ob D e o σ) (s := Nb e o ob) ⟨b, c, rfl, rfl, h⟩
    · exact (reach_of_or_right (r := Ob D e o σ) (s := Nb e o ob) ⟨c, b, rfl, rfl, h⟩).symm

/-- Retracción total (caso sin lazos cerrados). -/
def rhoE (ob : Fin 3 → Bool) : ι ⊕ Lt → ι ⊕ Fin 3
  | .inl i => .inl i
  | .inr l => bpA e ((rep o ob (.inr l)).getD (0, false))

/-- Retracción parcial (caso con un lazo cerrado). -/
def rhoO (ob : Fin 3 → Bool) : ι ⊕ Lt → Option (ι ⊕ Fin 3)
  | .inl i => some (.inl i)
  | .inr l => (rep o ob (.inr l)).map (bpA e)

omit [DecidableEq ι] [Fintype ι] in
theorem rep_inl (ob : Fin 3 → Bool) (hB : ∀ p, rep o ob (bpV o p) = some p) (k : Fin 3) :
    rep o ob (.inl k) = some (k, false) := by
  have := hB (k, false)
  simpa [bpV] using this

omit [DecidableEq ι] [Fintype ι] in
theorem rhoE_phi (ob : Fin 3 → Bool) (hB : ∀ p, rep o ob (bpV o p) = some p) (u : Vl) :
    rhoE e o ob (phi e u) = bpA e ((rep o ob u).getD (0, false)) := by
  rcases u with k | l
  · simp [rhoE, phi, rep_inl o ob hB k, bpA]
  · rfl

omit [DecidableEq ι] [Fintype ι] in
theorem rhoO_phi (ob : Fin 3 → Bool) (hB : ∀ p, rep o ob (bpV o p) = some p) (u : Vl) :
    rhoO e o ob (phi e u) = (rep o ob u).map (bpA e) := by
  rcases u with k | l
  · simp [rhoO, phi, rep_inl o ob hB k, bpA]
  · rfl

omit [DecidableEq ι] [Fintype ι] in
theorem piF_inr (k : Fin 3) : piF o (.inr k) = phi e (bpV o (k, true)) := by
  simp [piF, phi, bpV]

theorem count_eq (σ : D.Cross → Bool) (ob : Fin 3 → Bool) (m : Fin 3 × Bool → Fin 3 × Bool)
    (hB : ∀ p, rep o ob (bpV o p) = some p)
    (h1 : ∀ u v, NB o ob u v = true → ∃ p q, rep o ob u = some p ∧ rep o ob v = some q ∧
      (p = q ∨ m p = q ∨ m q = p))
    (h2 : ∀ p, reachB o ob (bpV o p) (bpV o (m p)) = true)
    (h3 : ∀ u, ∃ p, rep o ob u = some p ∧ reachB o ob (bpV o p) u = true) :
    Nat.card (SimpleGraph.fromRel fun a c => Ob D e o σ a c ∨ Nb e o ob a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y => OaD D e σ x y ∨ NMr e m x y).ConnectedComponent := by
  refine card_local_eq (piF o) (rhoE e o ob) ?_ (Ob D e o σ) (Nb e o ob) (OaD D e σ) (NMr e m)
    (fun a c h => h) (fun x y h => ⟨x, y, rfl, rfl, h⟩) ?_ ?_ ?_
  · intro x
    rcases x with i | k
    · rfl
    · rw [piF_inr, rhoE_phi e o ob hB, hB]
      simp [bpA]
  · intro a c h
    obtain ⟨u, v, rfl, rfl, hN⟩ := h
    obtain ⟨p, q, hp, hq, hpq⟩ := h1 u v hN
    rw [rhoE_phi e o ob hB, rhoE_phi e o ob hB, hp, hq]
    simp only [Option.getD_some]
    rcases hpq with rfl | hpq | hpq
    · exact SimpleGraph.Reachable.refl _
    · rw [← hpq]
      exact reach_of_or_right (r := OaD D e σ) (s := NMr e m) ⟨p, rfl, rfl⟩
    · rw [← hpq]
      exact (reach_of_or_right (r := OaD D e σ) (s := NMr e m) ⟨q, rfl, rfl⟩).symm
  · intro x y h
    obtain ⟨p, rfl, rfl⟩ := h
    rw [piF_bpA, piF_bpA]
    exact LR_reach D e o σ ob (reachB_sound (h2 p))
  · intro b
    rcases b with i | l
    · exact SimpleGraph.Reachable.refl _
    · obtain ⟨p, hp, hr⟩ := h3 (.inr l)
      have : rhoE e o ob (.inr l) = bpA e p := by simp [rhoE, hp]
      rw [this, piF_bpA]
      exact LR_reach D e o σ ob (reachB_sound hr)

theorem count_circ (σ : D.Cross → Bool) (ob : Fin 3 → Bool) (m : Fin 3 × Bool → Fin 3 × Bool)
    (hB : ∀ p, rep o ob (bpV o p) = some p)
    (h1 : ∀ u v, NB o ob u v = true → ((rep o ob u = none ↔ rep o ob v = none) ∧
      ∀ p q, rep o ob u = some p → rep o ob v = some q → (p = q ∨ m p = q ∨ m q = p)))
    (h2 : ∀ p, reachB o ob (bpV o p) (bpV o (m p)) = true)
    (h3 : ∀ u p, rep o ob u = some p → reachB o ob (bpV o p) u = true)
    (h4 : ∀ u v, rep o ob u = none → rep o ob v = none → reachB o ob u v = true)
    (h5 : ∃ u, rep o ob u = none) :
    Nat.card (SimpleGraph.fromRel fun a c => Ob D e o σ a c ∨ Nb e o ob a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y => OaD D e σ x y ∨ NMr e m x y).ConnectedComponent
        + 1 := by
  obtain ⟨u0, hu0⟩ := h5
  refine card_local_circ (piF o) (rhoO e o ob) (phi e u0)
    (by rw [rhoO_phi e o ob hB, hu0]; rfl) ?_ (Ob D e o σ) (Nb e o ob) (OaD D e σ) (NMr e m)
    (fun a c h => h) (fun x y h => ⟨x, y, rfl, rfl, h⟩) ?_ ?_ ?_ ?_ ?_
  · intro x
    rcases x with i | k
    · rfl
    · rw [piF_inr, rhoO_phi e o ob hB, hB]
      simp [bpA]
  · intro a c x y h ha hc
    obtain ⟨u, v, rfl, rfl, hN⟩ := h
    rw [rhoO_phi e o ob hB, Option.map_eq_some_iff] at ha hc
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hc
    rcases (h1 u v hN).2 p q hp hq with rfl | hpq | hpq
    · exact SimpleGraph.Reachable.refl _
    · rw [← hpq]
      exact reach_of_or_right (r := OaD D e σ) (s := NMr e m) ⟨p, rfl, rfl⟩
    · rw [← hpq]
      exact (reach_of_or_right (r := OaD D e σ) (s := NMr e m) ⟨q, rfl, rfl⟩).symm
  · intro x y h
    obtain ⟨p, rfl, rfl⟩ := h
    rw [piF_bpA, piF_bpA]
    exact LR_reach D e o σ ob (reachB_sound (h2 p))
  · intro a c h
    obtain ⟨u, v, rfl, rfl, hN⟩ := h
    rw [rhoO_phi e o ob hB, rhoO_phi e o ob hB, Option.map_eq_none_iff, Option.map_eq_none_iff]
    exact (h1 u v hN).1
  · intro a c ha hc
    rcases a with i | l
    · simp [rhoO] at ha
    rcases c with j | l'
    · simp [rhoO] at hc
    simp only [rhoO, Option.map_eq_none_iff] at ha hc
    exact LR_reach D e o σ ob (reachB_sound (h4 (.inr l) (.inr l') ha hc))
  · intro b x hb
    rcases b with i | l
    · simp only [rhoO, Option.some.injEq] at hb
      rw [← hb]
      exact SimpleGraph.Reachable.refl _
    · simp only [rhoO, Option.map_eq_some_iff] at hb
      obtain ⟨p, hp, rfl⟩ := hb
      rw [piF_bpA]
      exact LR_reach D e o σ ob (reachB_sound (h3 (.inr l) p hp))

/-- **Lema local.** El número de componentes del grafo de un estado de `D'` es el del grafo
reducido con el emparejamiento `matOf (mi …)` de la frontera, más los lazos locales `kk`. -/
theorem count_local (σ : D.Cross → Bool) (ob : Fin 3 → Bool) :
    Nat.card (SimpleGraph.fromRel fun a c => Ob D e o σ a c ∨ Nb e o ob a c).ConnectedComponent =
      Nat.card (SimpleGraph.fromRel fun x y => OaD D e σ x y ∨
        NMr e (matOf (mi (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2))) x y).ConnectedComponent +
        kk (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2) := by
  have hc := check_all (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2)
  have ho : (![o 0, o 1, o 2] : Fin 3 → Bool) = o := by
    funext i
    fin_cases i <;> rfl
  have hob : (![ob 0, ob 1, ob 2] : Fin 3 → Bool) = ob := by
    funext i
    fin_cases i <;> rfl
  rw [ho, hob] at hc
  by_cases hk : kk (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2) = 0
  · rw [if_pos hk] at hc
    obtain ⟨hB, h1, h2, h3⟩ := checkEq_spec o ob hc
    rw [hk, add_zero]
    exact count_eq D e o σ ob _ hB h1 h2 h3
  · rw [if_neg hk] at hc
    have hk1 : kk (o 0) (o 1) (o 2) (ob 0) (ob 1) (ob 2) = 1 :=
      le_antisymm (kk_le_one _ _ _ _ _ _) (Nat.pos_of_ne_zero hk)
    obtain ⟨hB, h1, h2, h3, h4, h5⟩ := checkCirc_spec o ob hc
    rw [hk1]
    exact count_circ D e o σ ob _ hB h1 h2 h3 h4 h5


/-! ### Lazos de cada estado y teorema principal -/

section Main

/-- Lazos de un estado cuyo grafo reducido lleva el emparejamiento `m` (incluye las
circunferencias libres). -/
noncomputable def Qc (σ : D.Cross → Bool) (m : Fin 3 × Bool → Fin 3 × Bool) : ℕ :=
  Nat.card (SimpleGraph.fromRel fun x y => OaD D e σ x y ∨ NMr e m x y).ConnectedComponent +
    D.free

theorem Qc_pos (σ : D.Cross → Bool) (m : Fin 3 × Bool → Fin 3 × Bool) : 1 ≤ Qc D e σ m := by
  unfold Qc
  haveI : Nonempty (SimpleGraph.fromRel fun x y => OaD D e σ x y ∨ NMr e m x y).ConnectedComponent :=
    ⟨(SimpleGraph.fromRel fun x y => OaD D e σ x y ∨ NMr e m x y).connectedComponentMk
      (.inl (e 0))⟩
  have := Nat.card_pos (α := (SimpleGraph.fromRel fun x y => OaD D e σ x y ∨
    NMr e m x y).ConnectedComponent)
  omega

/-- **Lema de lazos.** Los lazos del estado `(σ, b₀, b₁, b₂)` de `D'`. -/
theorem r3_lazos (σ : D.Cross → Bool) (b0 b1 b2 : Bool) :
    (tri D e he o ovc sgc).lazos ((r3State D e he o ovc sgc).symm (σ, b0, b1, b2)) =
      Qc D e σ (matOf (mi (o 0) (o 1) (o 2) (b0 == sgc 0) (b1 == sgc 1) (b2 == sgc 2))) +
        kk (o 0) (o 1) (o 2) (b0 == sgc 0) (b1 == sgc 1) (b2 == sgc 2) := by
  have h := count_local D e o σ (fun j => ![b0, b1, b2] j == sgc j)
  unfold lazos
  rw [r3_graph_eq, h]
  change _ + _ + D.free = _ + D.free + _
  ring

variable {K : Type*} [Field K]

/-- La suma de estados de `D'` en términos de `FF` (las sumas por emparejamiento). -/
theorem bracket_tri_eq (A : K) :
    (tri D e he o ovc sgc).bracket A =
      ∑ σ : D.Cross → Bool, (∏ x : D.Cross, if σ x then A else A⁻¹) *
        FF A (fun n => dd A ^ (Qc D e σ (matOf n) - 1)) (o 0) (o 1) (o 2)
          (sgc 0) (sgc 1) (sgc 2) := by
  unfold bracket
  rw [← (r3State D e he o ovc sgc).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Fintype.sum_prod_type, FF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b0 _ => Finset.sum_congr rfl fun b1 _ =>
    Finset.sum_congr rfl fun b2 _ => ?_
  rw [r3_weight, r3_lazos]
  have hpos := Qc_pos D e σ (matOf (mi (o 0) (o 1) (o 2) (b0 == sgc 0) (b1 == sgc 1)
    (b2 == sgc 2)))
  rw [show Qc D e σ (matOf (mi (o 0) (o 1) (o 2) (b0 == sgc 0) (b1 == sgc 1) (b2 == sgc 2))) +
      kk (o 0) (o 1) (o 2) (b0 == sgc 0) (b1 == sgc 1) (b2 == sgc 2) - 1 =
      (Qc D e σ (matOf (mi (o 0) (o 1) (o 2) (b0 == sgc 0) (b1 == sgc 1) (b2 == sgc 2))) - 1) +
      kk (o 0) (o 1) (o 2) (b0 == sgc 0) (b1 == sgc 1) (b2 == sgc 2) by omega]
  simp only [wt, dd, pow_add]
  ring

/-- **Invariancia del corchete de Kauffman bajo R3.** Las dos caras del movimiento
(`tri … o …` y `tri … (¬ o) …`, que solo difieren en `next`) tienen el mismo corchete para todos
los patrones `(o, sgc)` de un R3 geométrico (`validR3`, ver la tabla del paso 0), sean cuales
sean las letras superiores `ovc`. -/
theorem bracket_r3 (A : K) (hA : A ≠ 0)
    (hv : validR3 (o 0) (o 1) (o 2) (sgc 0) (sgc 1) (sgc 2) = true) :
    (tri D e he o ovc sgc).bracket A = (tri D e he (fun i => !o i) ovc sgc).bracket A := by
  rw [bracket_tri_eq, bracket_tri_eq]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact FF_invariant A hA _ _ _ _ _ _ _ hv

end Main

end Tri

end GDiag
end TMENudos.Invariancia
