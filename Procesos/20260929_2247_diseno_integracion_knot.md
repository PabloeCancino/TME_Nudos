# Diseño de la integración: `Knot` concreto y `granny_distinct_from_square`

**Fecha:** 2026-09-29, 22:47 · **Rama:** `etapa1-spike-gauss` · **Estado:** PROPUESTA, pendiente de su aprobación
**Documentos relacionados:** `20260929_1451_bitacora_de_sesion.md` (sección 0), `20260929_1408_mapa_de_ruta.md`

Este documento existe porque, al preparar la integración con `Reidemeister.lean` y `Schubert.lean`, apareció un problema de fondo que no estaba en el mapa de ruta. Nada de lo descrito aquí se ha aplicado: todo el trabajo de la etapa 1 vive en archivos nuevos que no forman parte de la build.

## 1. Situación

En la rama `etapa1-spike-gauss` hay, sobre el tipo abstracto `GDiag` (diagrama de Gauss con signos), demostrado sin `sorry`: la invariancia del corchete de Kauffman bajo isomorfismo, R1 y R2, y el puente con el corchete computable. R3 y el polinomio de Jones invariante están en curso (se anotará en la bitácora).

Para cerrar `granny_distinct_from_square` (trébol # trébol ≠ trébol # su espejo) faltaría construir `Knot` sobre `GDiag` y sustituir los axiomas `trefoil`, `mirror` y `connected_sum` de `Schubert.lean` por definiciones.

## 2. El problema de fondo: los movimientos abstractos generan nudos VIRTUALES

Los movimientos que se han demostrado (`r1`, `r2`, y `r3` cuando cierre) se aplican a aristas cualesquiera, sin exigir que el diagrama sea plano ni que las aristas compartan una cara. Es decir, `GDiag` módulo esos movimientos modela **nudos virtuales** (diagramas de Gauss módulo movimientos de Reidemeister abstractos), no nudos clásicos.

Consecuencias, en dos direcciones:

**A favor (lo que sí se puede afirmar).** Los movimientos clásicos son casos particulares de los abstractos. Por tanto, todo invariante de los abstractos (el corchete de Kauffman, el Jones) es invariante clásico, y **dos diagramas que el Jones distingue son distintos también como nudos clásicos**. Así, la desigualdad `granny ≠ square` demostrada en el cociente virtual implica la desigualdad clásica. El sentido de la implicación que se necesita es el que sí vale.

**En contra (lo que rompe la integración directa).** Según la literatura de nudos virtuales (Kauffman, Manturov; **no lo he verificado aquí**), la suma conexa de nudos virtuales depende de las elecciones (dónde se pega) y la factorización prima de nudos virtuales no es única. Si eso es cierto, entonces:
- La operación `connected_sum : Knot → Knot → Knot` de `Schubert.lean` no estaría bien definida sobre el cociente virtual.
- Los axiomas `connected_sum_comm`, `connected_sum_assoc`, `schubert_existence_axiom` y `schubert_uniqueness` **serían falsos** si `Knot` pasara a ser el cociente virtual.

Por eso NO conviene redefinir `Schubert.Knot := Quotient DiagramSetoid` con el `Diagram` basado en `GDiag`: se sustituiría un modelo consistente pero abstracto (el que verificó `06_modelo_de_consistencia.lean`) por uno concreto que probablemente contradice los axiomas.

Además, el modelo de consistencia verificado más arriba en esta sesión es de un `Knot` abstracto (multiconjuntos de racionales no nulos); no dice nada de la consistencia con un `Knot` concreto.

## 3. Otros puntos de diseño que condicionan la integración

1. **Universos.** Con índices `ι : Type` arbitrarios, `Σ ι, GDiag ι` vive en `Type 1`, y `Knot` también. Es compatible con `Schubert` (los axiomas `knot_complement : Knot → Type` etc. siguen tipando) pero convendría comprobarlo. Alternativa: indexar por `Fin n`, a costa de la fontanería con `finSumFinEquiv` que se quiso evitar.
2. **Relación de equivalencia.** Habría que definir una relación inductiva `GRel` sobre los diagramas con constructores `refl`, `symm`, `trans`, isomorfismo, `r1`, `r1F`, `r2`, `r3` (y quizá R2 sobre la misma arista y R2 entre circunferencias libres, aún no demostrados).
3. **Suma conexa.** Definirla sobre el cociente exige probar independencia de la arista elegida para pegar, lo que en teoría clásica se hace deslizando un arco anudado a través de los cruces (R2 y R3) y en la virtual falla. Es el trabajo más grande de todos.
4. **`Bridge.lean`.** `rational_to_diagram` podría dejar de ser axioma: `ι := ZMod (2n)`, `next := +1`, la pareja del par `(o,u)`, `ovr` según sea posición superior, y `sign` a partir de `crossing_sign` de `Basic.lean`. Sería un avance real (cierra un axioma de `Bridge`), pero exige decidir si el signo de `Basic` (función de la razón `u − o` respecto de `n`) coincide con el signo geométrico; no se ha examinado.
5. **`Reidemeister.lean`.** Los 11 axiomas actuales se reparten así en un diseño concreto: `R1_inverse`, `R2_inverse` y `R3_inverse` desaparecen (los movimientos pasan a ser relaciones, no funciones); `topologically_equivalent` y las que hablan de él seguirían siendo axiomas (topología real).

## 4. Opciones

**Opción 1 (recomendada a corto plazo): módulo concreto separado, y capa abstracta con invariante axiomatizado.**
- Nuevo módulo (por ejemplo `TMENudos/NudosGauss.lean`) con el `Knot` virtual concreto, la relación, `jones` bien definido sobre el cociente, y el teorema autocontenido `⟦ofWord (concat trefoil trefoil)⟧ ≠ ⟦ofWord (concat trefoil (swap trefoil))⟧`. No toca `Schubert.lean`.
- En `Schubert.lean` (capa abstracta) se cerraría `granny_distinct_from_square` añadiendo un axioma `jones_knot : Knot → LaurentPolynomial ℤ` con su especificación mínima (multiplicativo, valor en el trébol, comportamiento por `mirror`). Su justificación sería el módulo concreto, que demuestra las mismas propiedades para los diagramas concretos, pero **la conexión entre el `Knot` abstracto y el concreto seguiría siendo axiomática**. Habría que ampliar el modelo de consistencia (extender el modelo de multiconjuntos con un `jones` compatible).
- Ventaja: barata, honesta sobre lo que está y no está demostrado, sin riesgo de contradicción. Inconveniente: no elimina los axiomas de la capa abstracta.

**Opción 2: `Knot` clásico concreto con realizabilidad plana.**
- Representar los diagramas como mapas planares (sistema de rotación con característica de Euler correcta) y restringir los movimientos a los clásicos (R2 solo entre aristas de la misma cara). Entonces la suma conexa está bien definida y los axiomas de `Schubert` tienen sentido en el modelo concreto.
- Ventaja: es el objeto matemáticamente correcto y permitiría demostrar de verdad `connected_sum_comm`, etc. Inconveniente: es un proyecto de otra magnitud (caras, orientación, invariancia de la planaridad bajo los movimientos), sin estimación fiable.

**Opción 3: cambiar el marco a nudos virtuales.**
- Reformular `Schubert.lean` para trabajar con nudos virtuales y quitar o debilitar los axiomas de suma conexa y factorización única. Cambia el sentido de la teoría; solo si el autor así lo decide.

## 5. Recomendación

Opción 1 ahora, y dejar la Opción 2 como meta a largo plazo si se quiere eliminar la capa axiomática. Es la única que cierra `granny_distinct_from_square` sin arriesgar la consistencia del sistema y sin prometer más de lo demostrado.

## 6. Qué se hará mientras usted duerme (sin tocar la build principal)

Solo en archivos nuevos de la rama `etapa1-spike-gauss`:
1. Cerrar R3 (`Etapa1_R3.lean`) y verificarlo (en curso).
2. Writhe y Jones invariante sobre `GDiag` para R1 y R2 (`Etapa1_Jones.lean`, en curso) y, cuando R3 cierre, para R3.
3. Prototipo de `Knot` virtual concreto (`GRel`, cociente, `jones` sobre el cociente) y el teorema autocontenido `granny ≠ square` en él, sin tocar ni importar `Reidemeister.lean` ni `Schubert.lean`.

## 7. Decisiones que necesito de usted

1. ¿Opción 1, 2 o 3? (Recomiendo la 1.)
2. Si Opción 1: ¿aceptar el axioma `jones_knot` con su especificación en `Schubert.lean`, o preferir dejar `granny_distinct_from_square` con `sorry` hasta tener el `Knot` clásico?
3. ¿Sustituir el axioma `rational_to_diagram` de `Bridge.lean` por la definición concreta (punto 4 de la sección 3), previa comprobación del signo de `Basic`?
4. Universos: ¿`Type 1` con índices arbitrarios o `Fin n`?
