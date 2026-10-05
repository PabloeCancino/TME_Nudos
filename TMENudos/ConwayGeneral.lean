import Mathlib
import TMENudos.Conway

namespace TMENudos.Conway

open TMENudos.Gauss

/-! ### Longitudes (para TODA lista `a`) -/

theorem length_blocks_aux (a : List ℕ) (k : ℕ) :
    ((a.zipIdx k).flatMap fun (aj, j) =>
      List.replicate aj (if j % 2 == 0 then 1 else 0, j % 2 == 0)).length = a.sum := by
  induction a generalizing k with
  | nil => simp
  | cons x t ih => simp [List.zipIdx_cons]

theorem length_blocks (a : List ℕ) : (blocks a).length = a.sum :=
  length_blocks_aux a 0

theorem length_walkAux (L : List (ℕ × ℕ)) (f p : ℕ) : (walkAux L f p).length = f := by
  induction f generalizing p with
  | zero => simp [walkAux]
  | succ f ih => simp [walkAux, ih]

theorem length_walk (a : List ℕ) : (walk a).length = 2 * a.sum := by
  unfold walk
  simp only [length_walkAux, length_blocks]

theorem conwayWord_length (a : List ℕ) : (conwayWord a).length = 2 * a.sum := by
  unfold conwayWord
  simp only [List.length_map, length_walk]

/-! ### Lema de pasada (abstracto): el recorrido sigue una sucesion de puertos `e i`

Si el puerto que sale del cruce al que se entra por `e i` esta unido por `L` con `e (i+1)`
para `i < m`, el recorrido con combustible `j + r` (`j ≤ m`) empieza por `e 0, …, e (j-1)`. -/

theorem walkAux_pasada (L : List (ℕ × ℕ)) (e : ℕ → ℕ) (m : ℕ)
    (h : ∀ i, i < m → partnerOf L ((3 - e i % 4) + 4 * (e i / 4)) = e (i + 1)) :
    ∀ j, j ≤ m → ∀ r, walkAux L (j + r) (e 0) = (List.range j).map e ++ walkAux L r (e j) := by
  intro j
  induction j with
  | zero => intro _ r; simp
  | succ j ih =>
    intro hj r
    have h1 := ih (by omega) (r + 1)
    have e1 : j + 1 + r = j + (r + 1) := by omega
    rw [e1, h1, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
    congr 1
    simp only [walkAux]
    rw [h j (by omega)]

/-- Pasada ascendente por un bloque: entradas `BL, BR, BL, …` (puertos `4(c+i) + (t+i)%2`). -/
def entradaAsc (c t i : ℕ) : ℕ := 4 * (c + i) + (t + i) % 2

/-- Pasada descendente: entradas `TR, TL, TR, …` (puertos `4(c-i) + 3 - (t+i)%2`). -/
def entradaDesc (c t i : ℕ) : ℕ := 4 * (c - i) + 3 - (t + i) % 2

/-! ### Secuencias por posicion (`seqAt`) con desplazamiento -/

/-- Contribucion del cruce `c` (con hebra izquierda en `l`) a la posicion `pos`. -/
def segP (l c pos : ℕ) : List ℕ :=
  if l == pos then [4 * c, 4 * c + 2] else if l + 1 == pos then [4 * c + 1, 4 * c + 3] else []

/-- `seqAt` generalizado con indice inicial `k`. -/
def segs (P : List (ℕ × Bool)) (k pos : ℕ) : List ℕ :=
  (P.zipIdx k).flatMap fun ((l, _), c) => segP l c pos

theorem seqAt_eq (cs : List (ℕ × Bool)) (pos : ℕ) : seqAt cs pos = segs cs 0 pos := rfl

theorem segs_nil (k pos : ℕ) : segs [] k pos = [] := by simp [segs]

theorem segs_cons (x : ℕ × Bool) (P : List (ℕ × Bool)) (k pos : ℕ) :
    segs (x :: P) k pos = segP x.1 k pos ++ segs P (k + 1) pos := by
  simp [segs, List.zipIdx_cons]

theorem segs_append (P Q : List (ℕ × Bool)) (k pos : ℕ) :
    segs (P ++ Q) k pos = segs P k pos ++ segs Q (k + P.length) pos := by
  simp [segs, List.zipIdx_append]

theorem segP_mem (l c pos q : ℕ) (h : q ∈ segP l c pos) : q / 4 = c := by
  unfold segP at h
  split_ifs at h <;> simp at h <;> omega

theorem segP_length (l c pos : ℕ) : (segP l c pos).length % 2 = 0 := by
  unfold segP
  split_ifs <;> simp

theorem segs_mem (P : List (ℕ × Bool)) (k pos q : ℕ) (h : q ∈ segs P k pos) :
    k ≤ q / 4 ∧ q / 4 < k + P.length := by
  induction P generalizing k with
  | nil => simp [segs_nil] at h
  | cons x P ih =>
    rw [segs_cons, List.mem_append] at h
    rcases h with h | h
    · have := segP_mem _ _ _ _ h
      simp only [List.length_cons]
      omega
    · have := ih (k + 1) h
      simp only [List.length_cons]
      omega

theorem segs_even (P : List (ℕ × Bool)) (k pos : ℕ) : (segs P k pos).length % 2 = 0 := by
  induction P generalizing k with
  | nil => simp [segs_nil]
  | cons x P ih =>
    rw [segs_cons, List.length_append]
    have := segP_length x.1 k pos
    have := ih (k + 1)
    omega

theorem segP_nodup (l c pos : ℕ) : (segP l c pos).Nodup := by
  unfold segP
  split_ifs <;> simp

theorem segs_nodup (P : List (ℕ × Bool)) (k pos : ℕ) : (segs P k pos).Nodup := by
  induction P generalizing k with
  | nil => simp [segs_nil]
  | cons x P ih =>
    rw [segs_cons, List.nodup_append]
    refine ⟨segP_nodup _ _ _, ih (k + 1), ?_⟩
    intro q hq q' hq' hqq
    subst hqq
    have h1 := segP_mem _ _ _ _ hq
    have h2 := (segs_mem _ _ _ _ hq').1
    omega

/-! ### Arcos intermedios `midLinks` -/

theorem getD_mid (SA SB : List ℕ) (w0 q w2 w3 : ℕ) :
    (SA ++ w0 :: q :: w2 :: w3 :: SB).getD SA.length 0 = w0 ∧
    (SA ++ w0 :: q :: w2 :: w3 :: SB).getD (SA.length + 1) 0 = q ∧
    (SA ++ w0 :: q :: w2 :: w3 :: SB).getD (SA.length + 2) 0 = w2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [List.getD_eq_getElem?_getD]

theorem mid_mem (SA SB : List ℕ) (w0 q w2 w3 : ℕ) (hm : SA.length % 2 = 0) :
    (q, w2) ∈ midLinks (SA ++ w0 :: q :: w2 :: w3 :: SB) := by
  obtain ⟨-, h1, h2⟩ := getD_mid SA SB w0 q w2 w3
  unfold midLinks
  simp only [List.mem_map, List.mem_range]
  refine ⟨SA.length / 2, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons]
    omega
  · have e1 : 2 * (SA.length / 2) + 1 = SA.length + 1 := by omega
    have e2 : 2 * (SA.length / 2) + 2 = SA.length + 2 := by omega
    rw [e1, e2, h1, h2]

theorem mid_unique (SA SB : List ℕ) (w0 q w2 w3 : ℕ) (hm : SA.length % 2 = 0)
    (hn : (SA ++ w0 :: q :: w2 :: w3 :: SB).Nodup) (e : ℕ × ℕ)
    (he : e ∈ midLinks (SA ++ w0 :: q :: w2 :: w3 :: SB)) (h1 : e.1 = q) : e.2 = w2 := by
  obtain ⟨-, g1, g2⟩ := getD_mid SA SB w0 q w2 w3
  unfold midLinks at he
  simp only [List.mem_map, List.mem_range] at he
  obtain ⟨j, hj, rfl⟩ := he
  simp only at h1 ⊢
  have hlen : (SA ++ w0 :: q :: w2 :: w3 :: SB).length = SA.length + 4 + SB.length := by
    simp; omega
  have hb1 : 2 * j + 1 < (SA ++ w0 :: q :: w2 :: w3 :: SB).length := by omega
  have hb2 : SA.length + 1 < (SA ++ w0 :: q :: w2 :: w3 :: SB).length := by omega
  have key : 2 * j + 1 = SA.length + 1 := by
    rw [List.getD_eq_getElem _ _ hb1] at h1
    rw [List.getD_eq_getElem _ _ hb2] at g1
    have := (List.Nodup.getElem_inj_iff hn).1 (h1.trans g1.symm)
    exact this
  have e2 : 2 * j + 2 = SA.length + 2 := by omega
  rw [e2, g2]

/-! ### Descomposicion de `seqAt` alrededor de dos cruces consecutivos -/

theorem seqAt_dec (P Q : List (ℕ × Bool)) (x y : ℕ × Bool) (pos : ℕ) :
    seqAt (P ++ x :: y :: Q) pos =
      segs P 0 pos ++ (segP x.1 P.length pos ++
        (segP y.1 (P.length + 1) pos ++ segs Q (P.length + 2) pos)) := by
  rw [seqAt_eq, segs_append, segs_cons, segs_cons]
  simp only [Nat.zero_add]

theorem segP_off (l c off : ℕ) (h : off ≤ 1) :
    segP l c (l + off) = [4 * c + off, 4 * c + 2 + off] := by
  unfold segP
  interval_cases off <;> simp

/-- `seqAt` en `x.1 + off`, con dos cruces consecutivos de la misma hebra izquierda. -/
theorem seqAt_dec_off (P Q : List (ℕ × Bool)) (x y : ℕ × Bool) (hxy : x.1 = y.1) (off : ℕ)
    (h : off ≤ 1) :
    seqAt (P ++ x :: y :: Q) (x.1 + off) =
      segs P 0 (x.1 + off) ++ ((4 * P.length + off) :: (4 * P.length + 2 + off) ::
        (4 * (P.length + 1) + off) :: (4 * (P.length + 1) + 2 + off) ::
          segs Q (P.length + 2) (x.1 + off)) := by
  rw [seqAt_dec, ← hxy, segP_off _ _ _ h, segP_off _ _ _ h]
  simp

/-- Un puerto del cruce `c` solo esta en la posicion `x.1 + off`. -/
theorem pos_of_mem (P Q : List (ℕ × Bool)) (x y : ℕ × Bool) (hxy : x.1 = y.1) (off : ℕ)
    (h : off ≤ 1) (pos' : ℕ) (hq : 4 * P.length + 2 + off ∈ seqAt (P ++ x :: y :: Q) pos') :
    pos' = x.1 + off := by
  rw [seqAt_dec, List.mem_append, List.mem_append, List.mem_append] at hq
  rcases hq with hq | hq | hq | hq
  · have := (segs_mem _ _ _ _ hq).2
    omega
  · unfold segP at hq
    split_ifs at hq with h1 h2
    · simp at hq h1; interval_cases off <;> omega
    · simp at hq h2; interval_cases off <;> omega
    · simp at hq
  · have := segP_mem _ _ _ _ hq
    omega
  · have := (segs_mem _ _ _ _ hq).1
    omega

/-! ### Arcos internos de un bloque: `links` une el puerto superior de `c` con el de `c+1` -/

theorem getLastD_dec (SA SB : List ℕ) (w0 q w2 w3 : ℕ) :
    (SA ++ w0 :: q :: w2 :: w3 :: SB).getLastD 0 = w3 ∨
      (SA ++ w0 :: q :: w2 :: w3 :: SB).getLastD 0 ∈ SB := by
  rcases SB.eq_nil_or_concat with rfl | ⟨L, b, rfl⟩
  · left
    rw [show SA ++ w0 :: q :: w2 :: w3 :: [] = (SA ++ [w0, q, w2]) ++ [w3] by simp,
      List.getLastD_concat]
  · right
    rw [List.concat_eq_append,
      show SA ++ w0 :: q :: w2 :: w3 :: (L ++ [b]) = (SA ++ w0 :: q :: w2 :: w3 :: L) ++ [b] by
        simp, List.getLastD_concat]
    simp

theorem links_prop (cs : List (ℕ × Bool)) (k : ℕ) (P Q : List (ℕ × Bool)) (x y : ℕ × Bool)
    (hcs : cs = P ++ x :: y :: Q) (hxy : x.1 = y.1) (off : ℕ) (h : off ≤ 1) (hl : x.1 + off < 4) :
    (4 * P.length + 2 + off, 4 * (P.length + 1) + off) ∈ links cs k ∧
    ∀ e ∈ links cs k, e.1 = 4 * P.length + 2 + off → e.2 = 4 * (P.length + 1) + off := by
  subst hcs
  have hdec := seqAt_dec_off P Q x y hxy off h
  have hev := segs_even P 0 (x.1 + off)
  have hnd := segs_nodup (P ++ x :: y :: Q) 0 (x.1 + off)
  rw [← seqAt_eq, hdec] at hnd
  constructor
  · unfold links
    rw [List.mem_append]
    left
    rw [List.mem_flatMap]
    refine ⟨x.1 + off, by simp; omega, ?_⟩
    rw [hdec]
    exact mid_mem _ _ _ _ _ _ hev
  · intro e he h1
    unfold links at he
    rw [List.mem_append] at he
    rcases he with he | he
    · rw [List.mem_flatMap] at he
      obtain ⟨pos', hp', he⟩ := he
      have hmem : e.1 ∈ seqAt (P ++ x :: y :: Q) pos' := by
        unfold midLinks at he
        simp only [List.mem_map, List.mem_range] at he
        obtain ⟨j, hj, rfl⟩ := he
        simp only
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      rw [h1] at hmem
      have := pos_of_mem P Q x y hxy off h pos' hmem
      subst this
      rw [hdec] at he
      exact mid_unique _ _ _ _ _ _ hev hnd e he h1
    · rw [List.mem_flatMap] at he
      obtain ⟨pos', hp', he⟩ := he
      split_ifs at he with hemp
      · simp at he
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · -- endPort false pos' = cabeza
          simp only [endPort] at h1
          simp only [Bool.false_eq_true, if_false] at h1
          have hne : seqAt (P ++ x :: y :: Q) pos' ≠ [] := by
            intro h0; simp [h0] at hemp
          have hmem : 4 * P.length + 2 + off ∈ seqAt (P ++ x :: y :: Q) pos' := by
            rw [← h1]
            obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hne
            rw [ht]; simp
          have := pos_of_mem P Q x y hxy off h pos' hmem
          subst this
          rw [hdec] at h1
          rcases hS : segs P 0 (x.1 + off) with _ | ⟨a, t⟩
          · rw [hS] at h1
            simp at h1
          · rw [hS] at h1
            have hmem2 : 4 * P.length + 2 + off ∈ segs P 0 (x.1 + off) := by
              rw [← h1, hS]; simp
            have := (segs_mem _ _ _ _ hmem2).2
            omega
        · simp only [endPort] at h1
          simp only [if_true] at h1
          have hne : seqAt (P ++ x :: y :: Q) pos' ≠ [] := by
            intro h0; simp [h0] at hemp
          have hmem : 4 * P.length + 2 + off ∈ seqAt (P ++ x :: y :: Q) pos' := by
            have h5 := List.getLastD_mem_cons (l := seqAt (P ++ x :: y :: Q) pos') (a := 0)
            rw [h1] at h5
            rcases List.mem_cons.1 h5 with h6 | h6
            · omega
            · exact h6
          have := pos_of_mem P Q x y hxy off h pos' hmem
          subst this
          rw [hdec] at h1
          rcases getLastD_dec (segs P 0 (x.1 + off)) (segs Q (P.length + 2) (x.1 + off))
            (4 * P.length + off) (4 * P.length + 2 + off) (4 * (P.length + 1) + off)
            (4 * (P.length + 1) + 2 + off) with h3 | h3
          · rw [h3] at h1
            omega
          · rw [h1] at h3
            have := (segs_mem _ _ _ _ h3).1
            omega

theorem partnerOf_of_mem (L : List (ℕ × ℕ)) (p q : ℕ) (hmem : (p, q) ∈ L)
    (hu : ∀ e ∈ L, e.1 = p → e.2 = q) : partnerOf L p = q := by
  unfold partnerOf
  cases hf : L.find? (fun e => e.1 == p) with
  | some e =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [beq_iff_eq] at h2
    simpa using hu e h1 h2
  | none =>
    have := List.find?_eq_none.1 hf (p, q) hmem
    simp at this

/-- Paso interno de un bloque: `partnerOf` une el puerto superior de `c` con el inferior de `c+1`
(`off = 0`: `TL → BL`; `off = 1`: `TR → BR`). -/
theorem partnerOf_interno (cs : List (ℕ × Bool)) (k : ℕ) (P Q : List (ℕ × Bool))
    (x y : ℕ × Bool) (hcs : cs = P ++ x :: y :: Q) (hxy : x.1 = y.1) (off : ℕ) (h : off ≤ 1)
    (hl : x.1 + off < 4) :
    partnerOf (links cs k) (4 * P.length + 2 + off) = 4 * (P.length + 1) + off := by
  obtain ⟨h1, h2⟩ := links_prop cs k P Q x y hcs hxy off h hl
  exact partnerOf_of_mem _ _ _ h1 h2

/-! ### Los `blocks` y dos cruces consecutivos del mismo bloque -/

/-- Generador de `blocks`. -/
def bgen (p : ℕ × ℕ) : List (ℕ × Bool) :=
  List.replicate p.1 (if p.2 % 2 == 0 then 1 else 0, p.2 % 2 == 0)

theorem blocks_eq (a : List ℕ) : blocks a = (a.zipIdx).flatMap bgen := by
  unfold blocks
  congr 1

theorem blocks_dec (pre post : List ℕ) (m i : ℕ) (hi : i + 1 < m) :
    ∃ P Q : List (ℕ × Bool), ∃ x y : ℕ × Bool,
      blocks (pre ++ m :: post) = P ++ x :: y :: Q ∧ x.1 = y.1 ∧ x.1 ≤ 1 ∧
        P.length = pre.sum + i := by
  set f : ℕ × Bool := (if pre.length % 2 == 0 then 1 else 0, pre.length % 2 == 0) with hf
  refine ⟨blocks pre ++ List.replicate i f,
    List.replicate (m - i - 2) f ++ (post.zipIdx (pre.length + 1)).flatMap bgen, f, f,
    ?_, rfl, ?_, ?_⟩
  · rw [blocks_eq, blocks_eq, List.zipIdx_append, List.flatMap_append, List.zipIdx_cons]
    simp only [List.flatMap_cons, Nat.zero_add, bgen]
    have : m = i + 2 + (m - i - 2) := by omega
    conv_lhs => rw [this, List.replicate_add, List.replicate_add]
    simp [hf]
  · simp only [hf]
    split_ifs <;> simp
  · rw [List.length_append, List.length_replicate, length_blocks]

/-! ### Pasada ascendente por un bloque, para TODA lista `a = pre ++ m :: post`

Si el recorrido entra al bloque (de `m` cruces, el primero es el cruce `pre.sum`) por el cruce
`pre.sum` en el puerto `t ∈ {0,1}` (BL o BR), recorre los cruces del bloque en orden:
las entradas son `entradaAsc pre.sum t i = 4(pre.sum + i) + (t+i)%2`, para `i ≤ m - 1`. -/

theorem walk_pasada_asc (pre post : List ℕ) (m t : ℕ) :
    ∀ j, j ≤ m - 1 → ∀ r,
      walkAux (links (blocks (pre ++ m :: post)) (pre ++ m :: post).length) (j + r)
          (entradaAsc pre.sum t 0) =
        (List.range j).map (entradaAsc pre.sum t) ++
          walkAux (links (blocks (pre ++ m :: post)) (pre ++ m :: post).length) r
            (entradaAsc pre.sum t j) := by
  apply walkAux_pasada
  intro i hi
  obtain ⟨P, Q, x, y, hb, hxy, hx, hP⟩ := blocks_dec pre post m i (by omega)
  have hu : (t + i) % 2 = 0 ∨ (t + i) % 2 = 1 := by omega
  rcases hu with hu | hu
  · have := partnerOf_interno (blocks (pre ++ m :: post)) (pre ++ m :: post).length P Q x y hb hxy
      1 (by omega) (by omega)
    unfold entradaAsc
    rw [hP] at this
    have e1 : 3 - (4 * (pre.sum + i) + (t + i) % 2) % 4 +
        4 * ((4 * (pre.sum + i) + (t + i) % 2) / 4) = 4 * (pre.sum + i) + 2 + 1 := by omega
    have e2 : 4 * (pre.sum + (i + 1)) + (t + (i + 1)) % 2 = 4 * (pre.sum + i + 1) + 1 := by omega
    rw [e1, e2]
    exact this
  · have := partnerOf_interno (blocks (pre ++ m :: post)) (pre ++ m :: post).length P Q x y hb hxy
      0 (by omega) (by omega)
    unfold entradaAsc
    rw [hP] at this
    have e1 : 3 - (4 * (pre.sum + i) + (t + i) % 2) % 4 +
        4 * ((4 * (pre.sum + i) + (t + i) % 2) / 4) = 4 * (pre.sum + i) + 2 + 0 := by omega
    have e2 : 4 * (pre.sum + (i + 1)) + (t + (i + 1)) % 2 = 4 * (pre.sum + i + 1) + 0 := by omega
    rw [e1, e2]
    exact this

/-- Durante una pasada, el paso alterna sobre/bajo: dentro de un bloque `isOver` es la igualdad de
`(cs.getD c).2` con `p % 4 ∈ {0,3}`; las entradas `BL, BR, BL, …` dan `true, false, true, …` si el
cruce del bloque lleva `BL-TR` por encima. -/
theorem isOver_asc (cs : List (ℕ × Bool)) (c t i : ℕ)
    (hc : cs.getD (c + i) (0, false) = cs.getD c (0, false)) :
    isOver cs (entradaAsc c t i) = ((cs.getD c (0, false)).2 == decide ((t + i) % 2 = 0)) := by
  unfold isOver entradaAsc
  have e1 : (4 * (c + i) + (t + i) % 2) / 4 = c + i := by omega
  rw [e1, hc]
  congr 1
  have : (4 * (c + i) + (t + i) % 2) % 4 = (t + i) % 2 := by omega
  rw [this]
  by_cases h : (t + i) % 2 = 0
  · simp [h]
  · simp [h]
    omega

/-- Alternancia dentro de una pasada: pasos consecutivos del mismo bloque alternan sobre/bajo. -/
theorem isOver_asc_alt (cs : List (ℕ × Bool)) (c t i : ℕ)
    (hc : cs.getD (c + i) (0, false) = cs.getD c (0, false))
    (hc' : cs.getD (c + (i + 1)) (0, false) = cs.getD c (0, false)) :
    isOver cs (entradaAsc c t i) ≠ isOver cs (entradaAsc c t (i + 1)) := by
  rw [isOver_asc cs c t i hc, isOver_asc cs c t (i + 1) hc']
  have hu : (t + i) % 2 = 0 ∨ (t + i) % 2 = 1 := by omega
  have hv : (t + (i + 1)) % 2 = 1 - (t + i) % 2 := by omega
  rcases hu with hu | hu <;> rcases hh : (cs.getD c (0, false)).2 <;> simp [hu, hv]

/-- El recorrido de `C(m, …)` empieza por la pasada ascendente del primer bloque:
`walk (m :: post) = [0, 5, 8, …] ++ resto` (las entradas `entradaAsc 0 0 i`, `i < m`). -/
theorem walk_primer_bloque (m : ℕ) (post : List ℕ) (hm : 1 ≤ m) :
    ∃ rest, walk (m :: post) = (List.range m).map (entradaAsc 0 0) ++ rest := by
  have hsum : m ≤ (m :: post).sum := by simp
  have h := walk_pasada_asc [] post m 0 (m - 1) le_rfl (2 * (m :: post).sum - (m - 1))
  simp only [List.nil_append, List.sum_nil] at h
  have e1 : m - 1 + (2 * (m :: post).sum - (m - 1)) = 2 * (m :: post).sum := by omega
  rw [e1] at h
  have e2 : 2 * (m :: post).sum - (m - 1) = (2 * (m :: post).sum - m) + 1 := by omega
  rw [e2] at h
  refine ⟨walkAux (links (blocks (m :: post)) (m :: post).length) (2 * (m :: post).sum - m)
    (partnerOf (links (blocks (m :: post)) (m :: post).length)
      ((3 - entradaAsc 0 0 (m - 1) % 4) + 4 * (entradaAsc 0 0 (m - 1) / 4))), ?_⟩
  have h0 : entradaAsc 0 0 0 = 0 := by simp [entradaAsc]
  rw [h0] at h
  change walkAux _ (2 * (blocks (m :: post)).length) 0 = _
  rw [length_blocks, h]
  have : List.range m = List.range ((m - 1) + 1) := by congr 1; omega
  rw [this, List.range_succ, List.map_append]
  simp [walkAux]

/-- Consecuencia sobre la palabra: las `m` primeras etiquetas de `conwayWord (m :: post)` son
`1, 2, …, m`. -/
theorem conwayWord_primer_bloque (m : ℕ) (post : List ℕ) (hm : 1 ≤ m) :
    ((conwayWord (m :: post)).map (·.label)).take m = (List.range m).map (· + 1) := by
  obtain ⟨rest, h⟩ := walk_primer_bloque m post hm
  have hl : (conwayWord (m :: post)).map (·.label) =
      (walk (m :: post)).map (fun p => p / 4 + 1) := by
    unfold conwayWord
    simp [Function.comp_def]
  rw [hl, h, List.map_append]
  have : ((List.range m).map (entradaAsc 0 0)).map (fun p => p / 4 + 1)
      = (List.range m).map (· + 1) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, entradaAsc]
    omega
  rw [this, List.take_append_of_le_length (by simp)]
  simp

/-! ### Contraste con la sonda 31 (formas por pasadas), casos concretos -/

theorem etiquetas_32 :
    (conwayWord [3, 2]).map (·.label) = [1, 2, 3, 5, 4, 3, 2, 1, 5, 4] := by decide +kernel
theorem etiquetas_23 :
    (conwayWord [2, 3]).map (·.label) = [1, 2, 3, 4, 5, 1, 2, 5, 4, 3] := by decide +kernel
theorem etiquetas_312 :
    (conwayWord [3, 1, 2]).map (·.label) = [1, 2, 3, 5, 6, 1, 2, 3, 4, 6, 5, 4] := by
  decide +kernel

/-! ### Diseno (NO es teorema): lo que falta

Pasada descendente: las entradas `TR, TL, TR, …` (`entradaDesc`) exigen `partnerOf` en sentido
inverso (busqueda por la 2.ª componente): `partnerOf L (4C) = 4(C-1)+2` y `partnerOf L (4C+1) =
4(C-1)+3`, que requiere (i) que ninguna primera componente de `links` sea `4C`/`4C+1` (los
extremos inferiores son `endPort false` solo para el primer cruce de la posicion) y (ii) la
unicidad analoga por 2.ª componente. Es la misma tecnica que `links_prop` (descomposicion
`seqAt_dec`, `Nodup`, indice par), ~100 lineas.

Lema clave abierto (el paso duro): para toda lista `a` con `aᵢ ≥ 1`, `walk a` es la concatenacion
de `2k` pasadas completas de bloque, cada bloque dos veces (sonda 31 hasta n = 12), y el grafo de
extremos de bloque (4 por bloque, uniones por carril + casquetes) con paridades `aⱼ mod 2` tiene un
solo ciclo sii `p` es impar. -/

end TMENudos.Conway

#print axioms TMENudos.Conway.conwayWord_length
#print axioms TMENudos.Conway.links_prop
#print axioms TMENudos.Conway.partnerOf_interno
#print axioms TMENudos.Conway.walk_pasada_asc
#print axioms TMENudos.Conway.isOver_asc_alt
#print axioms TMENudos.Conway.conwayWord_primer_bloque
