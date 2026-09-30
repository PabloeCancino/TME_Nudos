/-
09_r3_numerico.lean -- Paso (c) de R3: prueba numerica INDEPENDIENTE con `Word.bracket`
(la version computable de `Etapa1_GaussWord`, sin ninguna de las definiciones de `Etapa1_R3`
salvo `validR3`, que es el predicado que se audita).

Se inserta el triangulo de tres cruces sobre tres aristas de una palabra de Gauss concreta, con
los dos ordenes `o` y `!o`, y se compara `Word.bracket` en A = 2 y A = 3 (racionales).
  * Para todo (o, s) con `validR3 = true` el corchete NO debe cambiar.
  * Para (o, s) con `validR3 = false` (alturas ciclicas) debe cambiar en algun caso.
Convencion de `tri`: en la hebra k las dos letras nuevas van en el orden `o k`
(`false`: primero el cruce con la hebra k+1); el cruce de indice c = (k+j) % 3 tiene la
letra de la hebra menor arriba sii `ovc c`; su signo es `s c`.
-/
import TMENudos.Etapa1_GaussWord
import TMENudos.Etapa1_R3

open TMENudos.Gauss TMENudos.Gauss.Word

namespace R3Num

/-- Inserta el triangulo: la arista `k` es la que sale de la letra en la posicion `pos k`. -/
def insertR3 (w : Word) (pos : Fin 3 → ℕ) (o s ovc : Fin 3 → Bool) : Word :=
  let base := fresh w
  let letter (k j : Fin 3) : Letter :=
    let idx : Fin 3 := k + j
    ⟨base + idx.val, ovc idx == decide (k < j), s idx⟩
  let ins (k : Fin 3) : List Letter :=
    let a : Fin 3 := k + 1
    let b : Fin 3 := k + 2
    if o k then [letter k b, letter k a] else [letter k a, letter k b]
  ((List.range w.length).zip w).flatMap fun (i, x) =>
    x :: ((List.finRange 3).flatMap fun k => if pos k = i then ins k else [])

def bools3 : List (Fin 3 → Bool) :=
  (List.range 8).map fun n => fun i => (n / 2 ^ i.val) % 2 == 1

/-- Todos los ordenes de tres posiciones distintas (submuestreadas con paso `st`). -/
def posList (len st : ℕ) : List (Fin 3 → ℕ) :=
  let all := (List.range len).flatMap fun a => (List.range len).flatMap fun b =>
    (List.range len).filterMap fun c =>
      if a ≠ b ∧ b ≠ c ∧ a ≠ c then some (![a, b, c] : Fin 3 → ℕ) else none
  (((List.range all.length).zip all).filter fun (i, _) => i % st == 0).map (·.2)

def base1 : Word := trefoil
def base2 : Word := swap trefoil
def base3 : Word := concat trefoil kinkNeg
def base4 : Word :=   -- dos cruces enlazados (Hopf) con signos distintos
  [⟨1, true, true⟩, ⟨2, false, false⟩, ⟨1, false, true⟩, ⟨2, true, false⟩]
def base5 : Word :=   -- lemniscata con un cruce y un lazo
  [⟨1, true, true⟩, ⟨2, true, true⟩, ⟨2, false, true⟩, ⟨1, false, true⟩]

/-- `true` si, para el patron (o, s), el corchete se conserva en todos los casos probados. -/
def conserva (bases : List Word) (st : ℕ) (o s : Fin 3 → Bool) : Bool :=
  bases.all fun w =>
    (posList w.length st).all fun pos =>
      bools3.all fun ovc =>
        [(2 : ℚ), 3].all fun A =>
          bracket A (insertR3 w pos o s ovc) == bracket A (insertR3 w pos (fun i => !o i) s ovc)

def pats : List ((Fin 3 → Bool) × (Fin 3 → Bool)) :=
  bools3.flatMap fun o => bools3.map fun s => (o, s)

def isValid (p : (Fin 3 → Bool) × (Fin 3 → Bool)) : Bool :=
  TMENudos.Invariancia.R3.validR3 (p.1 0) (p.1 1) (p.1 2) (p.2 0) (p.2 1) (p.2 2)

/-- Resumen (no debe fallar): (validos que conservan, validos totales,
    invalidos que rompen, invalidos totales, validos que rompen, invalidos que conservan). -/
def resumen (bases : List Word) (st : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let v := pats.filter isValid
  let i := pats.filter fun p => !isValid p
  ( (v.filter fun p => conserva bases st p.1 p.2).length, v.length,
    (i.filter fun p => !conserva bases st p.1 p.2).length, i.length,
    (v.filter fun p => !conserva bases st p.1 p.2).length,
    (i.filter fun p => conserva bases st p.1 p.2).length )

end R3Num

open R3Num

-- sanidad: las palabras base estan bien formadas y la inserccion tambien
#eval [base1, base2, base3, base4, base5].map wf
#eval (insertR3 base1 ![0, 2, 4] ![false, true, false] ![true, false, true] ![true, true, false]).length
#eval wf (insertR3 base1 ![0, 2, 4] ![false, true, false] ![true, false, true] ![true, true, false])
#eval (pats.filter isValid).length   -- 48
-- (validos que conservan, validos, invalidos que rompen, invalidos, validos que rompen,
--  invalidos que conservan): se espera (48, 48, 16, 16, 0, 0)
#eval resumen [base4, base5] 1      -- 2 cruces, todas las ternas de aristas
#eval resumen [base1] 23             -- trebol, ~1/23 de las ternas
#eval resumen [base2, base3] 150     -- trebol especular y trebol # rizo, muestra
