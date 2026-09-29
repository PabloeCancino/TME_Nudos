-- KN_03b_Invariantes_IME.lean
-- Teorema IME_rotate (requiere importar KN_03 para acceder a IDE_rotate)
-- e invariante de segundo nivel IME2.
--
-- CONVENCION DE DOS NIVELES:
--  * PRIMER nivel = nudo ORIENTADO: los codigos se identifican solo por rotacion
--    (grupo Z/2n). KN_03 / KN_03b (IME₁ = `KnConfig.IME`) y `Basic.lean`
--    (`Isotopic` = rotaciones) son de primer nivel.
--  * SEGUNDO nivel = nudo NO ORIENTADO: se identifica ademas por la reflexion
--    σ = `KnConfig.mirror` (KN_02), grupo diedral D₂ₙ. KN_04 y TCN (accion de D₆)
--    son de segundo nivel; el invariante es `IME2`.
--  * La involucion de intercambio over/under (`p.reverse` en KN_00, la imagen
--    especular real τ) es un eje DISTINTO y ORTOGONAL (quiralidad); no es σ.
-- Autor: Dr. Pablo Eduardo Cancino Marentes
-- Fecha: Enero 9, 2026

import TMENudos.KN_03_Invariantes_General

namespace KnotTheory.General

namespace KnConfig

variable {n : ℕ}

/-- IME es invariante bajo rotación -/
theorem IME_rotate (K : KnConfig n) (k : ZMod (2 * n)) :
    (K.rotate k).IME = K.IME := by
  simp only [IME, rotate]
  rw [Finset.sum_image]
  · congr 1
    ext p
    exact IDE_rotate K p k
  · intro p₁ _ p₂ _ heq
    have h1 : p₁.fst = p₂.fst := by
      have := congr_arg OrderedPair.fst heq
      simp only [OrderedPair.rotate] at this
      exact add_right_cancel this
    have h2 : p₁.snd = p₂.snd := by
      have := congr_arg OrderedPair.snd heq
      simp only [OrderedPair.rotate] at this
      exact add_right_cancel this
    cases p₁; cases p₂
    simp_all

/-- IME₂: invariante de SEGUNDO nivel (nudo no orientado), la pareja NO ORDENADA
    `{IME₁ K, IME₁ K.mirror}` implementada como el par `(min, max)` en `ℤ × ℤ`.

    * Primer nivel (orientado): `IME₁ = K.IME` depende del sentido del recorrido;
      solo es invariante bajo rotaciones (`IME_rotate`).
    * Segundo nivel (no orientado): la reflexión σ = `mirror` (`i ↦ -i`) es leer el
      MISMO diagrama al revés, así que no cambia el nudo, pero sí puede cambiar
      `IME₁` (`not_IME_mirror`). Al tomar la pareja no ordenada se olvida el
      sentido de lectura y se obtiene un invariante de la órbita de D₂ₙ
      (`IME2_rotate`, `IME2_mirror`).

    Es un escalar: NO se afirma que separe todas las órbitas. -/
def IME2 (K : KnConfig n) : Int × Int :=
  (min K.IME K.mirror.IME, max K.IME K.mirror.IME)

/-- IME₂ es invariante bajo la reflexión σ. -/
theorem IME2_mirror (K : KnConfig n) : K.mirror.IME2 = K.IME2 := by
  simp only [IME2, mirror_mirror, min_comm, max_comm]

/-- IME₂ es invariante bajo rotación. -/
theorem IME2_rotate (K : KnConfig n) (k : ZMod (2 * n)) :
    (K.rotate k).IME2 = K.IME2 := by
  simp only [IME2, IME_rotate, mirror_rotate_mirror]

/- CAMBIO DE ENUNCIADO (auditoría): se ELIMINA `IME_mirror`
    (antes: `K.mirror.IME = K.IME`, dependía de `IDE_mirror`, que era falso).
    Es falso en general: ver `KnConfig.not_IME_mirror` (n = 2, K = {(0,1),(2,3)}:
    IME K = 0, IME K.mirror = 4). Solución de diseño: el invariante de segundo
    nivel es `IME2` (ver arriba). -/

end KnConfig

end KnotTheory.General
