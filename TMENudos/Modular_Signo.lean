import TMENudos.Basic
import TMENudos.TCN_01_Fundamentos
import TMENudos.TCN_04_DihedralD6

/-!
# Teoria modular con signo del cruce como DATO explicito

ALCANCE. Esta es una capa ADITIVA: no modifica `Basic` ni `TCN_*`. Implementa la decision del
autor de que, en la teoria modular, el signo de un cruce sea un dato `σ : Bool` (true = positivo)
y no se derive de las posiciones. El signo derivado de `Basic.crossing_sign` queda como caso
particular (`ofDerived`). Migrar `Basic`/`TCN` para que usen esta nocion exige aprobacion aparte
del autor.

Motivo (ver `Etapa1_Modular.lean`): las tres parejas de `trefoilKnot` son antipodales
(`u - o = 3` en `ZMod 6`), el signo derivado vale +1 en ellas y en su intercambio, asi que el
trebol y su imagen especular (`mirrorTrefoil = r³ • trefoilKnot`) no se distinguen. Con signo
como dato, `mirrorS` NO esta en la orbita de D₆ de `trefoilS`.

Sin `sorry`, sin axiomas nuevos, sin `native_decide`.
-/

namespace TMENudos.Signo

open TMENudos

/-! ## 1. Cruce con signo (n general) -/

/-- Cruce con signo explicito: `pos = true` significa positivo.
    -- ETAPA 4: redundante con `Basic.RationalCrossing` (que ya lleva el campo `pos`). Por ahora
    se conserva tal cual: aquí `cross.pos` y `pos` son dos signos independientes; los teoremas de
    esta capa solo usan el campo `SignedCrossing.pos`. -/
@[ext]
structure SignedCrossing (n : ℕ) where
  cross : RationalCrossing n
  pos : Bool
deriving DecidableEq

/-- Imagen especular: intercambia over/under y NIEGA el signo. -/
def swapS {n : ℕ} (c : SignedCrossing n) : SignedCrossing n :=
  ⟨swap_crossing c.cross, !c.pos⟩

/-- Rotacion por `k`; conserva el signo. -/
def rotateS {n : ℕ} (k : ℝ[n]) (c : SignedCrossing n) : SignedCrossing n :=
  ⟨rotate_crossing k c.cross, c.pos⟩

/-- Signo derivado de las POSICIONES como caso particular: `σ := (zmod_sign (u - o) = 1)`.
    MIGRACIÓN: antes → después: antes `decide (crossing_sign c = 1)` (con `crossing_sign` derivado);
    ahora `crossing_sign` lee el campo `pos`, así que se usa `zmod_sign` explícitamente. -/
def ofDerived {n : ℕ} (c : RationalCrossing n) : SignedCrossing n :=
  ⟨c, decide (zmod_sign (c.under_pos - c.over_pos) = 1)⟩

theorem swapS_involutive {n : ℕ} (c : SignedCrossing n) : swapS (swapS c) = c := by
  cases c with
  | mk c b => cases c; simp [swapS, swap_crossing]

theorem rotateS_swapS {n : ℕ} (k : ℝ[n]) (c : SignedCrossing n) :
    rotateS k (swapS c) = swapS (rotateS k c) := by
  cases c with
  | mk c b => cases c; simp [swapS, rotateS, swap_crossing, rotate_crossing]

/-- Para una razon `d ≠ 0`, `zmod_sign (-d) = - zmod_sign d` salvo cuando `d.val = n`. -/
private theorem sign_neg_ne {n : ℕ} [NeZero n] (d : ℝ[n]) (hd : d ≠ 0) :
    zmod_sign (-d) = - zmod_sign d ↔ d.val ≠ n := by
  haveI : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩
  haveI : NeZero d := ⟨hd⟩
  have hv : (-d).val = 2 * n - d.val := ZMod.val_neg_of_ne_zero d
  have hpos : 0 < d.val := by
    rcases Nat.eq_zero_or_pos d.val with h | h
    · exact absurd ((ZMod.val_eq_zero d).mp h) hd
    · exact h
  have hlt : d.val < 2 * n := ZMod.val_lt d
  unfold zmod_sign
  rw [hv]
  split_ifs <;> simp <;> omega

private theorem sign_cases {n : ℕ} (x : ℝ[n]) : zmod_sign x = 1 ∨ zmod_sign x = -1 := by
  unfold zmod_sign; split_ifs <;> simp

/-- El signo derivado conmuta con el intercambio SI Y SOLO SI la razon no es antipodal. -/
theorem ofDerived_swap_iff {n : ℕ} [NeZero n] (c : RationalCrossing n) :
    ofDerived (swap_crossing c) = swapS (ofDerived c) ↔ (modular_ratio c).val ≠ n := by
  have hd : modular_ratio c ≠ 0 := ratio_nonzero c
  have e1 : c.over_pos - c.under_pos = -(modular_ratio c) := by simp [modular_ratio]
  have hc : c.under_pos - c.over_pos = modular_ratio c := rfl
  have key := sign_neg_ne (modular_ratio c) hd
  simp only [ofDerived, swapS, swap_crossing, SignedCrossing.mk.injEq, true_and,
    e1, hc]
  rw [← key]
  rcases sign_cases (modular_ratio c) with h | h <;>
    rcases sign_cases (-(modular_ratio c)) with h' | h' <;> simp [h, h']

/-- Pierde quiralidad: para una pareja antipodal, el signo derivado NO conmuta con el swap. -/
theorem ofDerived_swap_ne_of_antipodal {n : ℕ} [NeZero n] (c : RationalCrossing n)
    (h : (modular_ratio c).val = n) : ofDerived (swap_crossing c) ≠ swapS (ofDerived c) := by
  intro he
  exact ((ofDerived_swap_iff c).mp he) h

/-- Y si no es antipodal, conmuta. -/
theorem ofDerived_swap_of_not_antipodal {n : ℕ} [NeZero n] (c : RationalCrossing n)
    (h : (modular_ratio c).val ≠ n) : ofDerived (swap_crossing c) = swapS (ofDerived c) :=
  (ofDerived_swap_iff c).mpr h

/-- Ejemplo concreto en n = 3: la pareja (0,3) es antipodal y pierde la quiralidad. -/
example : ofDerived (swap_crossing (⟨(0 : ℝ[3]), 3, by decide, true⟩ : RationalCrossing 3)) ≠
    swapS (ofDerived (⟨(0 : ℝ[3]), 3, by decide, true⟩ : RationalCrossing 3)) := by decide +kernel

/-! ## 2. Configuraciones firmadas K3 -/

open KnotTheory

/-- Pareja ordenada en `ZMod 6` con signo. -/
structure SPair where
  fst : ZMod 6
  snd : ZMod 6
  distinct : fst ≠ snd
  pos : Bool
deriving DecidableEq

/-- Constructor con la prueba de distincion automatica. -/
def sp (a b : ZMod 6) (s : Bool) (h : a ≠ b := by decide) : SPair := ⟨a, b, h, s⟩

theorem existsUnique_of_filter_card' {α : Type*} (s : Finset α) (P : α → Prop)
    [DecidablePred P] (h : (s.filter P).card = 1) : ∃! p, p ∈ s ∧ P p := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have ha' : a ∈ s.filter P := by rw [ha]; exact Finset.mem_singleton_self a
  rw [Finset.mem_filter] at ha'
  refine ⟨a, ha', ?_⟩
  rintro y ⟨hy, hP⟩
  have : y ∈ s.filter P := Finset.mem_filter.mpr ⟨hy, hP⟩
  rw [ha] at this
  exact Finset.mem_singleton.mp this

/-- Cobertura: cada elemento de `ZMod 6` aparece exactamente una vez. -/
def Cov (S : Finset SPair) : Prop :=
  ∀ i : ZMod 6, ∃! p, p ∈ S ∧ (i = p.fst ∨ i = p.snd)

/-- Configuracion K3 firmada: tres parejas con signo que particionan `ZMod 6`. -/
structure SignedK3 where
  pairs : Finset SPair
  card_eq : pairs.card = 3
  cover : Cov pairs

namespace SignedK3

theorem ext' {K L : SignedK3} (h : K.pairs = L.pairs) : K = L := by
  cases K; cases L; simp_all

instance : DecidableEq SignedK3 := fun K L =>
  decidable_of_iff (K.pairs = L.pairs) ⟨ext', fun h => by rw [h]⟩

/-- Transporte de una configuracion por una funcion inyectiva de parejas que reetiqueta
    posiciones mediante una biyeccion `φ`. -/
def mapS (K : SignedK3) (f : SPair → SPair) (φ : ZMod 6 → ZMod 6)
    (hφ : Function.Bijective φ) (hf : Function.Injective f)
    (hmem : ∀ p i, (φ i = (f p).fst ∨ φ i = (f p).snd) ↔ (i = p.fst ∨ i = p.snd)) :
    SignedK3 where
  pairs := K.pairs.image f
  card_eq := by rw [Finset.card_image_of_injective _ hf]; exact K.card_eq
  cover := by
    intro i
    obtain ⟨y, hy⟩ := hφ.2 i
    obtain ⟨p, ⟨hp, hpy⟩, huniq⟩ := K.cover y
    refine ⟨f p, ⟨Finset.mem_image_of_mem f hp, ?_⟩, ?_⟩
    · rw [← hy]; exact (hmem p y).mpr hpy
    · rintro q ⟨hq, hqi⟩
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq
      have : p' = p := by
        apply huniq
        refine ⟨hp', ?_⟩
        rw [← hy] at hqi
        exact (hmem p' y).mp hqi
      rw [this]

/-- Imagen especular firmada: intercambia over/under en cada pareja y NIEGA su signo. -/
def swapS (K : SignedK3) : SignedK3 :=
  K.mapS (fun p => ⟨p.snd, p.fst, p.distinct.symm, !p.pos⟩) id Function.bijective_id
    (by
      rintro ⟨a, b, hab, s⟩ ⟨a', b', hab', s'⟩ h
      simp only [SPair.mk.injEq, Bool.not_inj_iff] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3; rfl)
    (fun p i => by simp only [id, or_comm])

end SignedK3

/-- Accion de `g ∈ D₆` sobre una configuracion firmada: mueve las posiciones y CONSERVA el signo
    de cada cruce (tambien bajo la reflexion). -/
def actS (g : DihedralGroup 6) (K : SignedK3) : SignedK3 :=
  K.mapS (fun p => ⟨DihedralD6.actionZMod g p.fst, DihedralD6.actionZMod g p.snd,
      DihedralD6.actionZMod_preserves_ne g _ _ p.distinct, p.pos⟩)
    (DihedralD6.actionZMod g)
    (Finite.injective_iff_bijective.mp (DihedralD6.actionZMod_injective g))
    (by
      rintro ⟨a, b, hab, s⟩ ⟨a', b', hab', s'⟩ h
      simp only [SPair.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      have e1 := DihedralD6.actionZMod_injective g h1
      have e2 := DihedralD6.actionZMod_injective g h2
      subst e1; subst e2; subst h3; rfl)
    (fun p i => by
      constructor
      · rintro (h | h)
        · exact Or.inl (DihedralD6.actionZMod_injective g h)
        · exact Or.inr (DihedralD6.actionZMod_injective g h)
      · rintro (h | h)
        · exact Or.inl (by rw [h])
        · exact Or.inr (by rw [h]))

/-- Trebol firmado: `{(0,3),(4,1),(2,5)}` con σ = + en los tres. -/
def trefoilS : SignedK3 where
  pairs := ({sp 0 3 true, sp 4 1 true, sp 2 5 true} : Finset SPair)
  card_eq := by decide
  cover := fun i => existsUnique_of_filter_card' _ _ (by revert i; decide)

/-- Imagen especular firmada del trebol. -/
def mirrorS : SignedK3 := trefoilS.swapS

theorem swapS_K3_involutive (K : SignedK3) : K.swapS.swapS = K := by
  apply SignedK3.ext'
  change (K.pairs.image _).image _ = K.pairs
  rw [Finset.image_image]
  rw [Finset.image_congr (g := id) (fun p _ => by
    obtain ⟨a, b, h, s⟩ := p
    simp), Finset.image_id]

/-- Los signos de `mirrorS` son todos negativos. -/
theorem mirrorS_pairs : mirrorS.pairs =
    ({sp 3 0 false, sp 1 4 false, sp 5 2 false} : Finset SPair) := by
  decide +kernel

/-- Los 12 elementos de D₆ sobre el trebol firmado dan exactamente 2 configuraciones distintas. -/
theorem orbit_trefoilS_card :
    (Finset.univ.image fun g : DihedralGroup 6 => (actS g trefoilS).pairs).card = 2 := by
  decide +kernel

theorem orbit_mirrorS_card :
    (Finset.univ.image fun g : DihedralGroup 6 => (actS g mirrorS).pairs).card = 2 := by
  decide +kernel

/-- **(a)** `mirrorS` NO esta en la orbita de D₆ de `trefoilS`: el trebol y su imagen especular
    son clases distintas en la teoria firmada. -/
theorem mirrorS_not_in_orbit : ∀ g : DihedralGroup 6, actS g trefoilS ≠ mirrorS := by
  decide +kernel

/-- Las dos orbitas (de 2 elementos cada una) son disjuntas: juntas suman 4 configuraciones. -/
theorem orbits_disjoint_card :
    ((Finset.univ.image fun g : DihedralGroup 6 => (actS g trefoilS).pairs) ∪
      (Finset.univ.image fun g : DihedralGroup 6 => (actS g mirrorS).pairs)).card = 4 := by
  decide +kernel

/-- Sanidad (no vacuidad): hay elementos de D₆ que fijan `trefoilS` y otros que la mueven. -/
theorem orbit_nontrivial : (∃ g : DihedralGroup 6, actS g trefoilS = trefoilS) ∧
    (∃ g : DihedralGroup 6, actS g trefoilS ≠ trefoilS) := by
  decide +kernel

/-- La accion de D₆ conmuta con el swap firmado (sobre el trebol). -/
theorem actS_swapS : ∀ g : DihedralGroup 6, actS g mirrorS = (actS g trefoilS).swapS := by
  decide +kernel

/-! ## 3. El signo derivado como caso particular (n = 3) -/

/-- Signo derivado de una pareja de `K3Config`, via `Basic.zmod_sign` (n = 3). -/
def derivedPos (p : OrderedPair) : Bool :=
  decide (zmod_sign (n := 3) (p.snd - p.fst) = 1)

/-- Trebol derecho sin signo (igual que `trefoilKnot` de TCN_06, que aqui no se importa). -/
def trefoilK3 : K3Config where
  pairs := {OrderedPair.make 0 3 (by decide), OrderedPair.make 4 1 (by decide),
    OrderedPair.make 2 5 (by decide)}
  card_eq := by decide
  is_partition := fun i => existsUnique_of_filter_card' _ _ (by revert i; decide)

/-- `ofDerived` para K3: cada pareja recibe su signo derivado. -/
def ofDerivedK3 (K : K3Config) : SignedK3 where
  pairs := K.pairs.image fun p => ⟨p.fst, p.snd, p.distinct, derivedPos p⟩
  card_eq := by
    rw [Finset.card_image_of_injective _ ?_]
    · exact K.card_eq
    · rintro ⟨a, b, hab⟩ ⟨a', b', hab'⟩ h
      simp only [SPair.mk.injEq] at h
      obtain ⟨h1, h2, _⟩ := h
      subst h1; subst h2; rfl
  cover := by
    intro i
    obtain ⟨p, ⟨hp, hpi⟩, huniq⟩ := K.is_partition i
    refine ⟨⟨p.fst, p.snd, p.distinct, derivedPos p⟩, ⟨Finset.mem_image_of_mem _ hp, hpi⟩, ?_⟩
    rintro q ⟨hq, hqi⟩
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq
    have := huniq p' ⟨hp', hqi⟩
    rw [this]

/-- **(b1)** El trebol con signo derivado ES `trefoilS`. -/
theorem derived_trefoil : ofDerivedK3 trefoilK3 = trefoilS := by
  apply SignedK3.ext'; decide +kernel

/-- `mirrorTrefoil = r³ • trefoilKnot` (definicion de TCN_06) coincide con `swap trefoilK3`. -/
theorem swap_eq_rot3 :
    DihedralD6.actOnConfig (DihedralGroup.r 3) trefoilK3 = trefoilK3.swap := by
  decide +kernel

/-- **(b2)** El signo derivado recoge la perdida de quiralidad: el `swap` no firmado del trebol
    (= `mirrorTrefoil = r³ • trefoilKnot`) recibe el signo derivado +++, y su configuracion
    firmada es `r³ • trefoilS`, es decir, ESTA EN LA ORBITA de `trefoilS` (misma clase). -/
theorem derived_mirror : ofDerivedK3 trefoilK3.swap = actS (DihedralGroup.r 3) trefoilS := by
  apply SignedK3.ext'; decide +kernel

theorem derived_mirror_in_orbit :
    ∃ g : DihedralGroup 6, ofDerivedK3 trefoilK3.swap = actS g trefoilS :=
  ⟨_, derived_mirror⟩

/-- Consecuencia: la imagen especular con signo derivado NO es `mirrorS` ni esta en su orbita. -/
theorem derived_mirror_not_mirrorS :
    ∀ g : DihedralGroup 6, ofDerivedK3 trefoilK3.swap ≠ actS g mirrorS := by
  decide +kernel

theorem derived_mirror_ne_mirrorS : ofDerivedK3 trefoilK3.swap ≠ mirrorS := by
  decide +kernel

/-! ## 4. Conteos (evaluacion) -/

/-- Todos los emparejamientos perfectos orientados de una lista de posiciones. -/
def rawConfigs : ℕ → List ℕ → List (List (ℕ × ℕ))
  | 0, _ => [[]]
  | _ + 1, [] => [[]]
  | k + 1, a :: rest =>
    rest.flatMap fun b =>
      (rawConfigs k (rest.erase b)).flatMap fun tl => [(a, b) :: tl, (b, a) :: tl]

/-- 120 configuraciones sin firmar. -/
def unsigned : List (List (ℕ × ℕ)) := rawConfigs 3 (List.range 6)

/-- Las 8 asignaciones de signo. -/
def signings : List (List Bool) := [true, false].flatMap fun a => [true, false].flatMap fun b =>
  [true, false].map fun c => [a, b, c]

/-- 960 configuraciones firmadas. -/
def signedAll : List (List (ℕ × ℕ × Bool)) :=
  unsigned.flatMap fun l => signings.map fun s => (l.zip s).map fun ((o, u), b) => (o, u, b)

def actRaw (refl : Bool) (i : ℕ) (x : ℕ) : ℕ :=
  if refl then (12 - (x + i) % 6) % 6 else (x + i) % 6

/-- Codigo numerico de una configuracion (invariante del orden de las parejas). -/
def code (l : List (ℕ × ℕ × Bool)) : List ℕ :=
  (l.map fun (o, u, s) => 100 * o + 10 * u + (if s then 1 else 0)).mergeSort

def orbitCodes (l : List (ℕ × ℕ × Bool)) : List (List ℕ) :=
  ((List.range 6).flatMap fun i => [false, true].map fun r =>
    code (l.map fun (o, u, s) => (actRaw r i o, actRaw r i u, s))).eraseDups

/-- Clave de orbita: el menor codigo (lexicografico) de la orbita. -/
def orbitKey (l : List (ℕ × ℕ × Bool)) : List ℕ :=
  (orbitCodes l).foldl (fun m x => if x < m then x else m) (code l)

/-- Pares (clave de orbita, tamano de orbita) sin repetir. -/
def orbitData (ls : List (List (ℕ × ℕ × Bool))) : List (List ℕ × ℕ) :=
  (ls.map fun l => (orbitKey l, (orbitCodes l).length)).eraseDups

#eval unsigned.length
#eval signedAll.length
#eval (orbitData signedAll).length
#eval ((orbitData signedAll).map (·.2)).eraseDups
-- orbitas entre las firmadas del matching {0,3},{1,4},{2,5} (todas las orientaciones)
#eval (orbitData (signedAll.filter fun l =>
  (l.map fun (o, u, _) => min o u).mergeSort == [0, 1, 2] &&
  (l.all fun (o, u, _) => (o + 3) % 6 == u))).map (·.2)

-- las 16 firmadas del trebol (2 configuraciones sin firmar x 8 signos)
#eval (orbitData (signedAll.filter fun l =>
  (l.map fun (o, u, _) => (o, u)).mergeSort (fun a b => a.1 ≤ b.1) == [(0, 3), (2, 5), (4, 1)] ||
  (l.map fun (o, u, _) => (o, u)).mergeSort (fun a b => a.1 ≤ b.1) ==
    [(1, 4), (3, 0), (5, 2)])).map (·.2)

/-! ## 5. Axiomas -/

#print axioms swapS_involutive
#print axioms rotateS_swapS
#print axioms ofDerived_swap_iff
#print axioms ofDerived_swap_ne_of_antipodal
#print axioms swapS_K3_involutive
#print axioms mirrorS_not_in_orbit
#print axioms orbit_trefoilS_card
#print axioms orbit_mirrorS_card
#print axioms orbits_disjoint_card
#print axioms derived_trefoil
#print axioms derived_mirror
#print axioms derived_mirror_not_mirrorS
#print axioms swap_eq_rot3

end TMENudos.Signo
