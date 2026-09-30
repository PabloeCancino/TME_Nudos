import TMENudos.Etapa1_GaussWord

/-!
# SONDA (2026-09-30): ¿está bien definida la suma conexa en el marco de los diagramas de Gauss abstractos?

Motivo: la integración con `Schubert.lean` asume una operación total `connected_sum` con
conmutatividad y factorización única. Si los movimientos abstractos generan nudos VIRTUALES, la
literatura dice que la suma conexa depende del punto de pegado. Esta sonda lo comprueba con el
propio Jones del proyecto: se inserta un diagrama `w₂` en distintas posiciones de `w₁` (y con
distintos puntos de partida de `w₂`); si el Jones cambia con la posición, el resultado NO depende
solo de las clases y la "suma conexa" no está bien definida en ese marco.

Control: con `w₁` PLANAR (trébol) el Jones no debe depender de la posición.
Objeto de prueba: `w₁` = el diagrama de tres cuerdas (0,2),(1,4),(3,5) con signo positivo, que NO
cumple la paridad de Gauss (no es planar).
-/

open TMENudos.Gauss TMENudos.Gauss.Word

/-- Inserta `w₂` (con etiquetas desplazadas) en `w₁` tras `i` letras. -/
def spliceAt (w₁ w₂ : Word) (i : ℕ) : Word :=
  w₁.take i ++ Word.shift (Word.fresh w₁) w₂ ++ w₁.drop i

/-- Diagrama no planar de 3 cruces: cuerdas (0,2), (1,4), (3,5), todas con signo positivo. -/
def virt : Word :=
  [⟨0, true, true⟩, ⟨1, true, true⟩, ⟨0, false, true⟩, ⟨3, true, true⟩, ⟨1, false, true⟩,
   ⟨3, false, true⟩]

#eval wf virt

-- CONTROL: w₁ planar (trébol). Jones de trébol # (trébol en cada posición y punto de partida).
#eval ((List.range 6).map fun i =>
  ((List.range 6).map fun k => jones (2 : ℚ) (spliceAt trefoil (trefoil.rotate k) i)).eraseDups)

-- SONDA: w₁ no planar. Si aparece más de un valor por fila o entre filas, la suma depende del pegado.
#eval ((List.range 6).map fun i =>
  ((List.range 6).map fun k => jones (2 : ℚ) (spliceAt virt (trefoil.rotate k) i)).eraseDups)

-- Todos los valores distintos que aparecen en la sonda.
#eval ((List.range 7).flatMap fun i =>
  (List.range 6).map fun k => jones (2 : ℚ) (spliceAt virt (trefoil.rotate k) i)).eraseDups

-- Referencia: Jones(virt) * Jones(trébol) (lo que daría una suma bien definida y multiplicativa).
#eval jones (2 : ℚ) virt * jones (2 : ℚ) trefoil
#eval jones (2 : ℚ) virt
