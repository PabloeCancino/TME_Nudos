/- COMPROBACIÓN (2026-09-29). mirrorTrefoil = swap de trefoilKnot, por decide. -/
import TMENudos.TCN_07_Clasificacion
open KnotTheory
example : mirrorTrefoil = K3Config.swap trefoilKnot := by decide
