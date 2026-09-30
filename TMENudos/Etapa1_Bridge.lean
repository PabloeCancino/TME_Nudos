import TMENudos.Basic
import TMENudos.Modular_Signo
import TMENudos.Etapa1_Puente
import TMENudos.Etapa1_Jones
import TMENudos.Etapa1_Modular
import TMENudos.Etapa1_Nudos
import TMENudos.Etapa1_GaussWord

/-!
# Etapa 1: la funcion CONCRETA "configuracion racional -> diagrama" de la capa paralela

`Bridge.lean` declara el axioma `rational_to_diagram {n} (rc : RationalConfiguration n) : Diagram`
(con `Diagram` del modelo antiguo de `Reidemeister.lean`). Aqui se da, en la capa paralela, la
funcion concreta hacia `GDiag` / `Diag` (`Etapa1_Nudos`):

* `SignedRationalConfiguration n`: configuracion racional + signo por cruce como DATO;
  `ofDerived` es el caso particular del signo derivado de `crossing_sign`.
* `ofSigned : SignedRationalConfiguration n → GDiag (ZMod (2*n))` (para `[NeZero n]`), con
  `next i = i + 1`, `partner` = la otra posicion del cruce, `ovr` = "es posicion superior",
  `sign` = signo del cruce, `free = 0`; con los cuatro axiomas de `GDiag` demostrados en general.
* `signedToDiag` y `rationalToDiag` (`Diag`), esta ultima con signo derivado.

## ALCANCE (leer antes de citar)

* Esta es la funcion concreta de la capa paralela. **El axioma `rational_to_diagram` de `Bridge.lean`
  NO se cierra** (su codominio `Diagram` es otro tipo; no se cambia `Diagram` a `GDiag`).
* Los diagramas `GDiag` son de tipo nudo virtual (la planaridad no se exige): `ofSigned` esta
  definida para TODA configuracion racional, planar o no.
* La definicion y los cuatro axiomas son GENERALES en `n`. Las pruebas de que es "la funcion
  correcta" (valores del Jones, distincion de quiralidad) son SOLO para el trebol (n = 3), por
  `decide +kernel` sobre un isomorfismo `Fin 6 ≃ ZMod 6` con el diagrama de la palabra de Gauss.
* Con el signo derivado, el trebol y su espejo modular reciben el MISMO Jones (perdida de
  quiralidad, ver `Etapa1_Modular`); con signo dato se distinguen.

Sin `sorry`, sin axiomas nuevos, sin `native_decide`.
-/

namespace TMENudos.Etapa1Bridge

open TMENudos.Invariancia TMENudos.Gauss TMENudos.Puente TMENudos.Nudos

/-! ## 1. Configuracion racional con signo como dato -/

/-- Configuracion racional con un signo por cruce (`true` = positivo) como DATO. -/
@[ext]
structure SignedRationalConfiguration (n : ℕ) where
  cfg : RationalConfiguration n
  sgn : Fin n → Bool
deriving DecidableEq

namespace SignedRationalConfiguration

/-- El signo derivado de las posiciones (`zmod_sign (u - o)`, el `crossing_sign` antiguo de `Basic`)
    como caso particular. ETAPA 4: redundante con el campo `pos` de `Basic.RationalCrossing`. -/
def ofDerived {n : ℕ} (cfg : RationalConfiguration n) : SignedRationalConfiguration n :=
  ⟨cfg, fun i => decide (zmod_sign ((cfg.crossings i).under_pos - (cfg.crossings i).over_pos) = 1)⟩

/-- Imagen especular: `swap_knot` (intercambia over/under) y NIEGA cada signo. -/
def mirror {n : ℕ} (rc : SignedRationalConfiguration n) : SignedRationalConfiguration n :=
  ⟨swap_knot rc.cfg, fun i => !rc.sgn i⟩

end SignedRationalConfiguration

/-! ## 2. El diagrama `ofSigned` (general en `n`) -/

section OfSigned

variable {n : ℕ} [NeZero n] (rc : SignedRationalConfiguration n)

instance neZeroTwoMul : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩

/-- Indice del (unico) cruce que contiene a la posicion `i`. -/
def cidx (i : ZMod (2 * n)) : Fin n :=
  ((List.finRange n).find? fun k => decide
    ((rc.cfg.crossings k).over_pos = i ∨ (rc.cfg.crossings k).under_pos = i)).getD
      ⟨0, NeZero.pos n⟩

theorem cidx_spec (i : ZMod (2 * n)) :
    (rc.cfg.crossings (cidx rc i)).over_pos = i ∨ (rc.cfg.crossings (cidx rc i)).under_pos = i := by
  obtain ⟨k, hk⟩ := rc.cfg.coverage i
  unfold cidx
  cases h : (List.finRange n).find? fun k => decide
      ((rc.cfg.crossings k).over_pos = i ∨ (rc.cfg.crossings k).under_pos = i) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp h k (List.mem_finRange k)
    simp only [decide_eq_true_eq, not_or] at this
    rcases hk with hk | hk
    · exact this.1 hk
    · exact this.2 hk
  | some m =>
    simpa using List.find?_some h

theorem cidx_eq {i : ZMod (2 * n)} {k : Fin n}
    (h : (rc.cfg.crossings k).over_pos = i ∨ (rc.cfg.crossings k).under_pos = i) :
    cidx rc i = k := by
  by_contra hne
  have hd := fun a b => all_positions_distinct rc.cfg a b
  rcases cidx_spec rc i with hm | hm <;> rcases h with hk | hk
  · exact (hd (cidx rc i) k).2.1 hne (hm.trans hk.symm)
  · exact (hd k (cidx rc i)).2.2 (hk.trans hm.symm)
  · exact (hd (cidx rc i) k).2.2 (hm.trans hk.symm)
  · exact (hd (cidx rc i) k).1 hne (hm.trans hk.symm)

/-- La otra posicion del cruce que contiene a `i`. -/
def spartner (i : ZMod (2 * n)) : ZMod (2 * n) :=
  if (rc.cfg.crossings (cidx rc i)).over_pos = i then (rc.cfg.crossings (cidx rc i)).under_pos
  else (rc.cfg.crossings (cidx rc i)).over_pos

/-- `i` es la posicion superior de su cruce. -/
def sovr (i : ZMod (2 * n)) : Bool := decide ((rc.cfg.crossings (cidx rc i)).over_pos = i)

/-- Signo del cruce que contiene a `i`. -/
def ssign (i : ZMod (2 * n)) : Bool := rc.sgn (cidx rc i)

theorem spartner_over {k : Fin n} {i : ZMod (2 * n)} (h : (rc.cfg.crossings k).over_pos = i) :
    spartner rc i = (rc.cfg.crossings k).under_pos := by
  have hk := cidx_eq rc (Or.inl h)
  simp [spartner, hk, h]

theorem spartner_under {k : Fin n} {i : ZMod (2 * n)} (h : (rc.cfg.crossings k).under_pos = i) :
    spartner rc i = (rc.cfg.crossings k).over_pos := by
  have hk := cidx_eq rc (Or.inr h)
  have hne : (rc.cfg.crossings k).over_pos ≠ i := fun he =>
    (rc.cfg.crossings k).distinct (he.trans h.symm)
  simp [spartner, hk, hne]

theorem sovr_over {k : Fin n} {i : ZMod (2 * n)} (h : (rc.cfg.crossings k).over_pos = i) :
    sovr rc i = true := by
  have hk := cidx_eq rc (Or.inl h)
  simp [sovr, hk, h]

theorem sovr_under {k : Fin n} {i : ZMod (2 * n)} (h : (rc.cfg.crossings k).under_pos = i) :
    sovr rc i = false := by
  have hk := cidx_eq rc (Or.inr h)
  have hne : (rc.cfg.crossings k).over_pos ≠ i := fun he =>
    (rc.cfg.crossings k).distinct (he.trans h.symm)
  simp [sovr, hk, hne]

/-- **El diagrama `GDiag` de una configuracion racional con signo.** -/
def ofSigned : GDiag (ZMod (2 * n)) where
  next := Equiv.addRight 1
  partner := spartner rc
  ovr := sovr rc
  sign := ssign rc
  partner_partner i := by
    rcases cidx_spec rc i with h | h
    · rw [spartner_over rc h, spartner_under rc rfl, h]
    · rw [spartner_under rc h, spartner_over rc rfl, h]
  partner_ne i := by
    rcases cidx_spec rc i with h | h
    · rw [spartner_over rc h]
      exact fun he => (rc.cfg.crossings _).distinct (h.trans he.symm)
    · rw [spartner_under rc h]
      exact fun he => (rc.cfg.crossings _).distinct (he.trans h.symm)
  ovr_partner i := by
    rcases cidx_spec rc i with h | h
    · rw [spartner_over rc h, sovr_under rc rfl, sovr_over rc h]; rfl
    · rw [spartner_under rc h, sovr_over rc rfl, sovr_under rc h]; rfl
  sign_partner i := by
    rcases cidx_spec rc i with h | h
    · rw [spartner_over rc h]
      simp only [ssign, cidx_eq rc (Or.inr (rfl : (rc.cfg.crossings (cidx rc i)).under_pos = _))]
    · rw [spartner_under rc h]
      simp only [ssign, cidx_eq rc (Or.inl (rfl : (rc.cfg.crossings (cidx rc i)).over_pos = _))]
  free := 0

@[simp] theorem ofSigned_partner (i : ZMod (2 * n)) : (ofSigned rc).partner i = spartner rc i := rfl
@[simp] theorem ofSigned_ovr (i : ZMod (2 * n)) : (ofSigned rc).ovr i = sovr rc i := rfl
@[simp] theorem ofSigned_sign (i : ZMod (2 * n)) : (ofSigned rc).sign i = ssign rc i := rfl
@[simp] theorem ofSigned_next (i : ZMod (2 * n)) : (ofSigned rc).next i = i + 1 := rfl
@[simp] theorem ofSigned_free : (ofSigned rc).free = 0 := rfl

end OfSigned

/-! ## 3. Las funciones a `Diag` (capa paralela) -/

/-- **Funcion concreta de la capa paralela** con signo como dato. -/
def signedToDiag {n : ℕ} [NeZero n] (rc : SignedRationalConfiguration n) : Diag :=
  Diag.mk (ZMod (2 * n)) (ofSigned rc)

/-- **Version "como `rational_to_diagram`"**: signo derivado de `crossing_sign`.
Es la funcion concreta de la capa paralela; el axioma `rational_to_diagram` de `Bridge.lean`
NO se cierra con ella (su codominio es el `Diagram` del modelo antiguo). -/
def rationalToDiag {n : ℕ} [NeZero n] (rc : RationalConfiguration n) : Diag :=
  Diag.mk (ZMod (2 * n)) (ofSigned (SignedRationalConfiguration.ofDerived rc))

theorem rationalToDiag_eq {n : ℕ} [NeZero n] (rc : RationalConfiguration n) :
    rationalToDiag rc = signedToDiag (SignedRationalConfiguration.ofDerived rc) := rfl

/-! ## 4. Comparacion con el diagrama de una palabra de Gauss (criterio de correccion) -/

theorem gdiag_ext {ι : Type} [DecidableEq ι] [Fintype ι] {D E : GDiag ι}
    (hn : D.next = E.next) (hp : D.partner = E.partner) (ho : D.ovr = E.ovr)
    (hs : D.sign = E.sign) (hf : D.free = E.free) : D = E := by
  cases D; cases E; simp_all

/-- Si en cada posicion `j` el diagrama de la palabra `w` (transportado por `e`) coincide con
`ofSigned rc`, entonces `ofSigned rc` ES ese diagrama transportado. -/
theorem ofSigned_eq_map {n : ℕ} [NeZero n] (rc : SignedRationalConfiguration n) (w : Word)
    (hw : Word.wf w = true) (e : Fin w.length ≃ ZMod (2 * n)) (hl : w.length ≠ 0)
    (hchk : ∀ j : ZMod (2 * n),
      e ((ofWord w hw).next (e.symm j)) = j + 1 ∧
      e ((ofWord w hw).partner (e.symm j)) = spartner rc j ∧
      (ofWord w hw).ovr (e.symm j) = sovr rc j ∧
      (ofWord w hw).sign (e.symm j) = ssign rc j) :
    ofSigned rc = (ofWord w hw).map e := by
  refine gdiag_ext ?_ ?_ ?_ ?_ ?_
  · ext j
    simp only [ofSigned_next, GDiag.map, Equiv.permCongr_apply]
    exact (hchk j).1.symm
  · funext j
    exact (hchk j).2.1.symm
  · funext j
    exact (hchk j).2.2.1.symm
  · funext j
    exact (hchk j).2.2.2.symm
  · simp [GDiag.map, ofWord, ofWordP, hl]

theorem jones_ofSigned_eq {n : ℕ} [NeZero n] (rc : SignedRationalConfiguration n) (w : Word)
    (hw : Word.wf w = true) (e : Fin w.length ≃ ZMod (2 * n)) (hl : w.length ≠ 0)
    (hchk : ∀ j : ZMod (2 * n),
      e ((ofWord w hw).next (e.symm j)) = j + 1 ∧
      e ((ofWord w hw).partner (e.symm j)) = spartner rc j ∧
      (ofWord w hw).ovr (e.symm j) = sovr rc j ∧
      (ofWord w hw).sign (e.symm j) = ssign rc j)
    {K : Type*} [Field K] (A : K) :
    (ofSigned rc).jones A = Word.jones A w := by
  rw [ofSigned_eq_map rc w hw e hl hchk, GDiag.jones_map, jones_ofWord]

/-- Isomorfismo estandar `Fin (longitud) ≃ ZMod (2*3)` cuando la palabra tiene longitud 6. -/
def eq3 (w : Word) (h : w.length = 6) : Fin w.length ≃ ZMod (2 * 3) :=
  (finCongr h).trans (ZMod.finEquiv 6).toEquiv

/-! ## 5. El trebol (n = 3): configuraciones y palabras -/

open TMENudos.Modular

/-- Trebol firmado `(+,+,+)`: las tres parejas antipodales de `trefoilRC`. -/
def trefSRC : SignedRationalConfiguration 3 := ⟨trefoilRC, ![true, true, true]⟩

/-- Su imagen especular firmada: parejas intercambiadas y signos `(−,−,−)`. -/
def mirrorSRC : SignedRationalConfiguration 3 := trefSRC.mirror

/-- El signo derivado del trebol es `(+,+,+)`: `ofDerived trefoilRC = trefSRC`. -/
theorem ofDerived_trefoilRC : SignedRationalConfiguration.ofDerived trefoilRC = trefSRC := by
  refine SignedRationalConfiguration.ext rfl ?_
  funext i
  fin_cases i <;> decide +kernel

theorem mirrorSRC_sgn : mirrorSRC.sgn = ![false, false, false] := by decide +kernel

theorem mirrorSRC_cfg_pairs :
    (List.finRange 3).map (fun i => ((mirrorSRC.cfg.crossings i).over_pos.val,
      (mirrorSRC.cfg.crossings i).under_pos.val)) = [(3, 0), (1, 4), (5, 2)] := by
  decide +kernel

theorem len_signedWord_tref : (signedWord trefS).length = 6 := by decide +kernel
theorem len_signedWord_mirror : (signedWord (swapS trefS)).length = 6 := by decide +kernel
theorem len_toWord_swap : (swap_knot trefoilRC).toWord.length = 6 := by decide +kernel

theorem wf_toWord_swap : Word.wf (swap_knot trefoilRC).toWord = true := by decide +kernel

/-! ### 5a. Signo dato: Jones del trebol y de su espejo -/

theorem jones_ofSigned_trefSRC : (ofSigned trefSRC).jones (2 : ℚ) = 4111 / 65536 := by
  rw [jones_ofSigned_eq trefSRC (signedWord trefS) signed_wf.1 (eq3 _ len_signedWord_tref)
    (by rw [len_signedWord_tref]; decide) (by decide +kernel) (2 : ℚ)]
  exact signed_trefoil_jones

theorem jones_ofSigned_mirrorSRC : (ofSigned mirrorSRC).jones (2 : ℚ) = -61424 := by
  rw [jones_ofSigned_eq mirrorSRC (signedWord (swapS trefS)) signed_wf.2
    (eq3 _ len_signedWord_mirror) (by rw [len_signedWord_mirror]; decide) (by decide +kernel)
    (2 : ℚ)]
  exact signed_swap_trefoil_jones

/-- Con signo dato, el trebol y su espejo tienen Jones distintos. -/
theorem jones_signed_ne : (ofSigned trefSRC).jones (2 : ℚ) ≠ (ofSigned mirrorSRC).jones (2 : ℚ) := by
  rw [jones_ofSigned_trefSRC, jones_ofSigned_mirrorSRC]; norm_num

/-- **Las clases en `NudoV` de `signedToDiag` del trebol y del espejo firmado son distintas.** -/
theorem signedToDiag_tref_ne_mirror :
    Quotient.mk diagSetoid (signedToDiag trefSRC) ≠
      Quotient.mk diagSetoid (signedToDiag mirrorSRC) := by
  intro h
  have := congrArg (NudoV.jones (2 : ℚ) two_ne_zero') h
  rw [NudoV.jones_mk, NudoV.jones_mk] at this
  exact jones_signed_ne this

/-! ### 5b. Signo derivado: perdida de quiralidad -/

/-- `rationalToDiag` del trebol modular da el Jones del trebol derecho. -/
theorem jones_rationalToDiag_trefoilRC :
    (rationalToDiag trefoilRC).jones (2 : ℚ) = 4111 / 65536 := by
  have h := jones_ofSigned_eq (SignedRationalConfiguration.ofDerived trefoilRC) trefoilRC.toWord
    trefoilRC_wf (eq3 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (2 : ℚ)
  exact h.trans trefoilRC_jones

/-- ... y el de su "espejo" modular (`swap_knot`) da EXACTAMENTE el mismo. -/
theorem jones_rationalToDiag_swap_trefoilRC :
    (rationalToDiag (swap_knot trefoilRC)).jones (2 : ℚ) = 4111 / 65536 := by
  have h := jones_ofSigned_eq (SignedRationalConfiguration.ofDerived (swap_knot trefoilRC))
    (swap_knot trefoilRC).toWord wf_toWord_swap (eq3 _ len_toWord_swap) (by decide +kernel)
    (by decide +kernel) (2 : ℚ)
  exact h.trans swap_knot_trefoilRC_jones

/-- **Perdida de quiralidad del signo derivado**: el Jones no distingue el trebol de su espejo. -/
theorem rationalToDiag_loses_chirality :
    (rationalToDiag trefoilRC).jones (2 : ℚ) = (rationalToDiag (swap_knot trefoilRC)).jones (2 : ℚ) := by
  rw [jones_rationalToDiag_trefoilRC, jones_rationalToDiag_swap_trefoilRC]

/-- ... y el Jones derivado del espejo modular NO es el del trebol izquierdo (`-61424`),
que es el que recibe el espejo con signo dato. -/
theorem rationalToDiag_mirror_ne_genuine_mirror :
    (rationalToDiag (swap_knot trefoilRC)).jones (2 : ℚ) ≠ (ofSigned mirrorSRC).jones (2 : ℚ) := by
  rw [jones_rationalToDiag_swap_trefoilRC, jones_ofSigned_mirrorSRC]; norm_num

/-- El trebol modular con signo derivado es el firmado `(+,+,+)`, asi que ambas rutas coinciden. -/
theorem rationalToDiag_trefoilRC_eq_signed : rationalToDiag trefoilRC = signedToDiag trefSRC := by
  rw [rationalToDiag_eq, ofDerived_trefoilRC]

#print axioms ofSigned
#print axioms jones_ofSigned_trefSRC
#print axioms jones_ofSigned_mirrorSRC
#print axioms signedToDiag_tref_ne_mirror
#print axioms jones_rationalToDiag_trefoilRC
#print axioms rationalToDiag_loses_chirality
#print axioms rationalToDiag_mirror_ne_genuine_mirror

end TMENudos.Etapa1Bridge
