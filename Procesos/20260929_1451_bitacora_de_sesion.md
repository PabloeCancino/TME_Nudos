# Bitácora de la sesión del 2026-09-29

**Proyecto:** TMENudos (Lean 4 v4.29.0, Mathlib v4.29.0) · **Rama más completa al cierre:** `integracion-opcion1` (28 commits sobre `master`; sin subir a ningún remoto; ver la sección 000)
**Documentos hermanos:**
- `20260929_1340_reporte_de_auditoria.md`: reporte de auditoría (estado y clasificación de los `sorry`).
- `20260929_1408_mapa_de_ruta.md`: mapa de ruta hacia un `Reidemeister.lean` estable.
- `Tests/auditoria_20260929/`: las pruebas ejecutables de esta sesión.

Este documento es el registro cronológico completo: qué se probó, qué se encontró, qué se cambió y por qué, y dónde retomar. Las secciones 1 a 3 sirven para orientarse; la 4 es el registro detallado; la 5 lista lo pendiente.

## 00000000. PAUSA EN LA RAMA `reconstruccion` (2026-10-01, segunda pausa) — RETOMAR AQUÍ

`master` = 6dfe13e (6 commits sin subir a `origin`). Rama `reconstruccion`: `TMENudos/Reconstruccion.lean`.

**Verificado (commit 32c166d):** el borrador de la parte combinatoria COMPILA (`lake build TMENudos.Reconstruccion`, ~40 s) y sus `#eval` coinciden con la sonda 18b: candidatos [2,4,16,96,768,7680], válidos [0,0,0,4,8,24], clases SIME [0,0,0,2,2,4], `check n` = true para n ≤ 5. Hallazgo: `checkNP` (sin planaridad) también da true para n=2..5, así que entre las ordenadas y alternantes sin R1/R2 la planaridad es redundante hasta n=5; lo que rompe la completitud es la alternancia.

**NO verificado:** un segundo agente amplió el archivo a 753 líneas (teoremas por `decide +kernel`, puente `SortedAlt ⇒ buildL`, equivalencias con Basic, teorema principal, contraejemplos) y fue detenido a medias, sin informe. Esa parte no se ha compilado ni revisado; puede no compilar o contener enunciados incorrectos.

**Cómo retomar:** `git checkout reconstruccion`; `lake build TMENudos.Reconstruccion` (una sola build a la vez; las pruebas por `decide +kernel` pueden tardar minutos); leer qué teoremas existen y cuáles faltan frente a la lista de la tarea (1 teoremas finitos, 2 puente general, 3 equivalencias con Basic, 4 teorema principal, 5 contraejemplos, 6 dependencias del axioma falso). Después, Fase 3: restringir `rotation_of_ratio_pos_eq`, `same_IME_implies_rotation`, `same_SIME_implies_rotation`, `IME_complete` e `isotopic_irreducible_same_SIME`.

**Reinicio del equipo (2026-10-01, tarde):** git INTACTO (`fsck` sin errores, árbol limpio, sin `.lock`, todas las ramas). `Basic` compila bien (30 s). La build de `Reconstruccion` que corría se interrumpió tras ~59 min con `Lean exited with code 3221226505` (0xC0000409, fallo del propio Lean, típico de desbordamiento de pila o memoria en un `decide +kernel` enorme): NO es corrupción del repositorio. El borrador de 204 líneas compilaba en 37 s; la parte general ampliada (líneas 1-538: puente, equivalencias, `main_gen`) compila en 17 s. El culpable está en los `decide +kernel` de la sección «Comprobaciones finitas» (probablemente n=5: `check_5`, `checkNP_5`, `cands_5`, `good_5`, `clases_5`). Se mide cada uno por separado con `lake env lean` sobre copias en el scratchpad. NO recompilar `lake build TMENudos.Reconstruccion` completo hasta resolverlo.

---

## 0000000. HALLAZGO (2026-10-01): `reconstruct_from_first` de `Basic` es FALSO — LEER PRIMERO

Prueba: `Procesos/Tests/auditoria_20260929/16_refuta_reconstruct_from_first.lean` (deriva `False` con un contraejemplo de n = 3: cruces antipodales (0,3),(1,4),(2,5) frente a (0,3),(2,5),(1,4); mismas razones índice a índice, sin desplazamiento uniforme). Afecta a `rotation_of_ratio_pos_eq`, `same_IME_implies_rotation`, `same_SIME_implies_rotation` e `IME_complete`. NO afecta a `TCN_*`, la capa de Gauss, la planaridad ni `ClassicalKnot`. El estado ya publicado en `origin` (master 211d1d6) contiene este axioma. Plan de reparación y de prueba para n ≤ 4: `Procesos/20261001_plan_axiomas_de_basic.md`. Los otros cuatro axiomas de `Basic` NO se han probado consistentes: A7 es sospechoso por el mismo defecto de indexado.


**Fase 0 de A7 (sondas 17 y 17b):** `is_R3_candidate` es vacuo (0 candidatos en n=3 y 4); la laxitud real está en las transiciones R1/R2 (conjuntos de pares razón-signo). Hay 720 K1 de grado 3, sin candidatos y mínimos dentro de la cota 4, con K2 no rotación. A7 no está refutado formalmente (falta un invariante de grado), pero es muy probablemente falso en el modelo actual. Detalle en `Procesos/20261001_plan_axiomas_de_basic.md`, sección 3.1.

**Fase 1 (sondas 18 y 18b):** el SIME NO es invariante completo en general (ejemplo n=3: trébol frente a la configuración especial). Restringido a planares, falla ya en n=4 (1 colisión) y n=5 (14). Entre las **planares alternantes sin candidato R1/R2** es completo SIN colisiones hasta n=7. Por tanto `rotation_of_ratio_pos_eq`, `same_IME_implies_rotation`, `IME_complete` e `isotopic_irreducible_same_SIME` son falsos como están y deben restringirse. Detalle y tabla en el plan, sección 3.2.

---

## 000000. PENDIENTES RESUELTOS EN LA RAMA `pendientes` (2026-10-01) — LEER PRIMERO

Rama `pendientes` (sale de `master` = e2c300b; **sin fusionar, nada subido a `origin`**).

| Pendiente | Resultado | Dónde |
|---|---|---|
| 4 tensiones de la Etapa 1 | RESUELTAS (T1 `formR2Pair` con signos opuestos; T2 réplica eliminada, `TCN_08_Uniformity` importa `Basic`; T3 transiciones conservan `pos`; T4 axioma A7 sin cambio) | commits 87a8a05, 3b2b30e |
| ¿índice cero suficiente? | **NO.** Contraejemplo n=4 probado en Lean (`indexZero_not_sufficient`): palabra con índice cero y paridad de Gauss, no planar. Para K₃ SÍ coinciden: `indexZero_iff_planar_toWord` (960 casos, `decide +kernel`) y `isRealizable_iff_irreducible_planar` | `Etapa1_Planaridad.lean` |
| Opción 2 (Knot clásico) | `ClassicalKnot` = diagramas planares módulo movimientos entre planares; `ClassicalKnot.jones` baja al cociente; `trefoilC_ne_mirrorC`, `trefoilC_ne_unknotC` por Jones | `Etapa1_Clasico.lean` |
| axioma `rational_to_diagram` | CERRADO: ahora es una definición (codificación inyectiva `crossingCode`, `rational_to_diagram_injective`). NO afirma respetar movimientos de Reidemeister. Axiomas de `Bridge`: 2 → 1 (total del proyecto 51 → 50) | `Bridge.lean` |

**Planaridad exacta (definición):** mapa combinatorio con orden cíclico fijado por el signo; caras = ciclos de sigma∘alpha; `planar w := w = [] ∨ faces w = n + 2` (género 0). Convención y sonda: `Procesos/Tests/auditoria_20260929/15_genero_vs_indice_cero.py`.

**Límites (qué NO se probó)**
- Que planar ⇒ índice cero en general: comprobado solo hasta n=4 por la sonda (no es teorema).
- `swap` preserva planaridad: solo para el trébol concreto; `ClassicalKnot` no tiene operación espejo general ni suma conexa (exige pegar en la misma cara).
- El axioma `rational_equivalence_preserves_isotopy` de `Bridge` SIGUE (verdadero en el modelo pretendido, pero `HEq` no permite deducir `n = m` sin un argumento de cardinalidad no formalizado).
- `rational_to_knot` depende de `sorryAx` solo vía `apply_R*` (como antes).
- Costos: `Etapa1_Planaridad` tarda ~62 min en compilar desde cero (los `decide +kernel` sobre 960 configuraciones).

**Pendiente de decisión del autor:** fusionar `pendientes` a `master` (avance rápido local) y, aparte, subir a `origin`.

---

## 00000. PAUSA EN LA RAMA `pendientes` (2026-09-30) — RETOMAR AQUÍ

`master` = e2c300b (migración al signo firmado completa y verificada; nada subido a `origin`). Rama de trabajo: `pendientes` (sale de master).

**Hecho y verificado**
- Sonda 15 (`Procesos/Tests/auditoria_20260929/15_genero_vs_indice_cero.py`, commit 7c309f1): criterio EXACTO de planaridad (mapa combinatorio determinado por el signo, género 0 ⇔ V−E+F=2). Resultado: n=3 planar = índice cero (336 = 336); n=4: 4160 planares frente a 4224 con índice cero; hay **64 configuraciones con índice cero y paridad de Gauss que NO son planares**. Por tanto "índice cero ⇒ planar" es FALSO en general (planar ⇒ índice cero se cumple hasta n=4). Falta formalizarlo en Lean.

**Tensiones de la Etapa 1: RESUELTAS Y VERIFICADAS (commit 87a8a05 + este)**. Los 45 módulos de `TMENudos/` (incluidos `Etapa1_*`) compilan por nombre en serie, 0 errores; sin `sorry`/`native_decide`/axiomas nuevos (Basic 5, Uniformity 1).
- T1: `formR2Pair` exige signos opuestos (`formR2Positions` es la parte posicional). `K3_special_has_R2` pasó a `K3_special_no_R2` (los 3 cruces son +); control positivo `K3_special_mixed`. La conclusión antigua "K₃,special es trivial" era un artefacto de ignorar el signo.
- T2: la réplica de `RationalCrossing`/`RationalConfiguration` en `TCN_08_UniformityCriterion` se eliminó; ahora importa `Basic`. El axioma `uniformity_criterion` se mantiene (su conclusión se deduce de `is_dividing_ratio`; sin cambio).
- T3: `is_R1/R2/R3_transition` conservan `pos` en los cruces que sobreviven; R3 exige `SIME K = SIME K'`.
- T4: el axioma A7 `minimal_isotopic_implies_rotation` NO cambia (ya decía `K2 = rotate_knot k K1`, que conserva signos); reformularlo con SIME lo habría debilitado. `SIME` y `SIME_eq_iff` se movieron antes de las transiciones.
- Límite: R1/R2 siguen siendo marcadores de posición (correspondencia existencial en ambos sentidos, sin renumeración).

**Estado al cierre (noche del 30/09):** el agente de planaridad se interrumpió al terminar la sesión anterior. Dejó dos archivos NUEVOS sin verificar: `TMENudos/Etapa1_Planaridad.lean` y `TMENudos/Etapa1_Clasico.lean` (WIP, NO compilados ni revisados; sin informe del agente). Siguiente paso: `lake build TMENudos.Etapa1_Planaridad` y luego `...Etapa1_Clasico` (builds en serie), leer los enunciados, revisar `sorry`/axiomas, y después `Bridge.lean` (`rational_to_diagram` como definición inyectiva).

**Plan siguiente (en orden, builds en SERIE por la poca memoria)**
1. (HECHO) Las 4 tensiones.
2. Archivo nuevo `Etapa1_Planaridad.lean` (capa paralela): `faces`/`planar` sobre `Word` (darts out_p=2p, in_p=2p+1; orden CCW por signo según la sonda), controles (trébol y espejo planares, mixto no), `∀ K : K3Config, indexZero K ↔ planar K.toWord` por `decide +kernel`, y el contraejemplo de n=4 ((0,3,−),(1,6,+),(2,5,−),(4,7,−)) con índice cero y Gauss par pero no planar.
3. Opción 2: `ClassicalKnot` = diagramas planares módulo movimientos que pasan sólo por planares; Jones heredado; trébol ≠ espejo. La suma conexa clásica queda fuera.
4. `Bridge.lean`: `rational_to_diagram` como DEFINICIÓN inyectiva (codificar posición y signo en `ratio_val : ℚ`, con teorema de inyectividad); el axioma `rational_equivalence_preserves_isotopy` probablemente se queda.

---

## 0000. MIGRACIÓN AL SIGNO FIRMADO: ETAPAS 1-4 COMPLETAS (2026-09-30) — LEER PRIMERO

**Rama `migracion-signo`** (sale de `master` = e7e4422; NADA subido a `origin`). Plan: `20260930_plan_migracion_signo_firmado.md`.

| Etapa | Commit | Contenido |
|---|---|---|
| 1 | 8bbb542 | `Basic.RationalCrossing` con `pos : Bool`; swap niega, rotate conserva; `withDerivedSign`; `SIME`; KN_Isomorphism y CrossingPairIsomorphism con factor Bool |
| 2 | 202c1c5 | `TCN.OrderedPair` con `pos` (card 60), `K3Config` (card 960), D₆ conserva signo, R2 con signos opuestos; `CrossingPairIsomorphism` directo |
| 3 | 8726680 | TCN_05..08, AUX, TNC_05_1: recuento firmado, `indexZero`, clasificación firmada |
| 4 | (este commit) | `Modular_Signo` reducido a su sección residual (el prototipo K3 era duplicado y se retiró) |

**Verificación (independiente, en serie):** los 35 módulos distintos de `Etapa1_*` compilan por nombre; los 10 `Etapa1_*` y `Modular_Signo` compilan por nombre; `#print axioms` de los teoremas clave = `propext, Classical.choice, Quot.sound`; sin `sorry`, axiomas ni `native_decide` nuevos (51 axiomas y 17 sorry como antes).

**Cifras antes → después (K3):** configuraciones 120→960; irreducibles 14→172 (18 órbitas; 12 de tamaño 12, 4 de 6, 2 de 2: tamaños sólo por sonda Python, en Lean está probada la suma de estabilizadores 216 = 12·18); con índice cero 336; realizables 2→4 (2 órbitas de tamaño 2: trébol derecho e izquierdo); fracción 1/60→1/240; no realizables 118→956. La órbita de 12 (`specialClass`) ya no es realizable (índice ≠ 0). `mirrorTrefoil = swap trefoilKnot` y NO está en la órbita del trébol.

**Cambios de enunciado (honestos):** eliminados por falsos con signo dato: `two_orbits_sum_to_14`, `two_orbits_disjoint`, `configsNoR1NoR2_eq_two_orbits`, `two_orbits_cover_all`, `configsNoR1NoR2_eq_realizable_union_special`, `irreducible_dichotomy`, `irreducible_realizable_iff_not_special`. Reformulados con `indexZero`: `k3_classification`, `exactly_two_classes`, `representatives_not_equivalent`, `realizable_iff_trefoil_orbits`. "Realizable" = irreducible ∧ Gauss par ∧ índice cero.

**Límites que hay que tener presentes**
- El índice cero es condición NECESARIA de planaridad; que sea suficiente en general NO está demostrado (sólo para K3, por cálculo).
- Costos: `irreducible_stabilizer_sum` 184 s, `indexZero_card` ~112 s, `irreducible_indexZero_iff` 60 s; `TCN_06` compila en ~4 min. El conteo de órbitas como Finset de Finsets (18 y tamaños) se abandonó por costo (>40 min).
- Pendientes abiertos de la Etapa 1: transiciones `is_R*_transition` comparan sólo `ratio_val` (tensión con el axioma de rotación); `formR2Pair` de TCN_10 sin signos opuestos (falsificaría `K3_special_has_R2`); la réplica de `TCN_08_UniformityCriterion` sigue independiente de `Basic`; `SIME` en `IME_complete`.
- Pendientes de proyecto: `rational_to_diagram` (axioma de Bridge), Opción 2 (Knot clásico), fusión de `migracion-signo` a `master` (NO hecha) y subida a `origin` (NO solicitada).

---

## 000. CIERRE DE SESIÓN (2026-09-30) — LEER PRIMERO

> **ACTUALIZACIÓN (sesión de retorno, rama `clase-b-y-capa-paralela`, sale de `integracion-opcion1`):** el autor pidió empezar por lo barato y seguro. Hecho: reformulación de los enunciados falsos de la clase B (sección 4.31). **También hecho: la capa paralela de `rational_to_diagram` (sección 4.32).** **Cifras actuales:** build de los 34 módulos más la raíz con 0 errores y 0 alertas; `sorry` en el código **17** (`Schubert` 11, `Reidemeister` 4, `KN_00_Combinatoria` 1, `KN_Instance_K3` 1); axiomas **51** (sin cambio). Las cifras del cuadro de abajo corresponden al cierre anterior.

**Sesión cerrada por el autor** (se va a la universidad). Todo el trabajo está commiteado: el árbol de trabajo está **limpio** en la rama `integracion-opcion1`, y la build se verificó al cerrar.

### Estado verificado al cierre
| Comprobación | Resultado |
|---|---|
| Build de los 34 módulos más la raíz (`lake build TMENudos` y los módulos por nombre, sin los `Etapa1_*`) | **3 327 trabajos, 0 errores, 0 alertas** distintas de `declaration uses sorry` |
| `sorry` en el código | **22** (`Schubert` 15, `Reidemeister` 5, `KN_00_Combinatoria` 1, `KN_Instance_K3` 1) |
| Axiomas | **51** (`Schubert` 25, `Reidemeister` 11, `Basic` 5, `KN_01` 5, `Bridge` 2, y 1 en cada uno de `KN_00_Combinatoria`, `TCN_01` y `TCN_08_UniformityCriterion`) |
| Modelo de consistencia (`Tests/auditoria_20260929/11_modelo_jones2.lean`) | Cubre los **38 axiomas** de `Reidemeister`, `Schubert` y `Bridge`; sin `sorryAx`; 70 objetos con tipos idénticos a los originales |
| Archivos `Etapa1_*.lean` (fuera de la build) | 9, todos compilan sin `sorry` ni axiomas nuevos |

### Dónde está cada cosa
| Rama | Contenido | Último commit |
|---|---|---|
| `master` | **Sin cambios** | `f3c46bb` |
| `auditoria-2026-09-29` | Auditoría, etapa 0, saneamiento de `Schubert`, modelo de consistencia, quandles | `8179aaa` |
| `etapa1-spike-gauss` | Sale de la anterior: spike, R1, R2, R3, puente, Jones, prototipo de nudos virtuales, exploración modular | `d856bcc` |
| **`integracion-opcion1`** (actual, la más completa) | Sale de la anterior: Opción 1 en `Schubert.lean`, `Modular_Signo`, "realizable" sin la órbita de 12, mapa de rutas | `c5d7416` |

La historia es **lineal**: las tres ramas son antepasadas de `integracion-opcion1` y `master` es antepasado de todas, así que traer todo a `master` sería un avance rápido (54 archivos, 28 commits). **No se ha hecho ni se ha subido nada a ningún remoto**; es decisión del autor.

### Lo conseguido en total (resumen)
- **Compilación y linters:** de 8 módulos con errores (≈90) y cientos de alertas a 0 y 0.
- **Inconsistencias eliminadas:** los axiomas `R1_inverse` y `R2_inverse` permitían demostrar `False`; corregidos y verificados con un modelo.
- **Enunciados falsos corregidos** en `TCN_06` a `TCN_08` (conteos de órbitas) y en la teoría KN (`gap_mirror`, `IDE_mirror`, `IME_mirror`).
- **Invariancia del corchete de Kauffman bajo R1, R2 y R3** sobre diagramas de Gauss con signos, y el Jones invariante; prototipo de nudos virtuales con `trefoil ≠ mirror` y `granny ≠ square`.
- **`granny_distinct_from_square` demostrado en `Schubert.lean`** por la Opción 1 (4 axiomas de `jones2`, consistentes con los demás).
- **Teoría modular:** el signo derivado explica la pérdida de quiralidad; capa aditiva con signo como dato (`Modular_Signo`); "realizable" en K3 excluye la órbita de 12, que no es planar.

### Decisiones y trabajo pendiente
Detalle en la sección **5.6** (mapa de rutas con su riesgo y su sonda) y en `20260929_2247_diseno_integracion_knot.md`. Lo que espera al autor:
1. **Fusionar a `master`** (y cuándo), o seguir trabajando en la rama.
2. **`rational_to_diagram` de `Bridge`:** sigue siendo axioma. Cerrarlo obliga a cambiar `Diagram` a `GDiag`, lo que choca con la Opción 1 (riesgo alto, ver R1 en 5.6). Recomendación: darlo solo en la capa paralela.
3. **Migrar `Basic` y `TCN` al signo firmado** (R3): exige aprobación archivo por archivo y cambia conteos en cascada (120 → 960 configuraciones).
4. **Clase B de `Schubert`** (7 `sorry`): reformular los enunciados falsos (coste bajo, seguro) o axiomatizar los profundos (previa extensión del modelo).
5. **Meta larga:** un `Knot` clásico con planaridad (Opción 2), que convertiría los axiomas de `jones2` en teoremas.
6. Estructura: cuál de `KN_*` y `TCN_*` es canónico; renombrar la σ de `KN_02`; ampliar `TMENudos.lean`.

### Lo que NO se ha hecho (para no dar nada por supuesto)
- La conexión entre el `Knot` abstracto de `Schubert` y el módulo concreto de la etapa 1 **sigue siendo axiomática** (los axiomas de `jones2`).
- La consistencia demostrada es **relativa a Lean y Mathlib** y de un modelo **degenerado** en lo geométrico (`Knot` = multiconjuntos de racionales no nulos); no prueba que el sistema describa nudos reales.
- El riesgo de que la suma conexa virtual no esté bien definida se apoya **solo en la literatura**; la sonda con el Jones (13) es ciega a él (sección 5.6).
- Los valores del Jones están evaluados en A = 2 sobre ℚ; las formas simbólicas en A vienen de un script externo no demostrado, salvo las del trébol y su espejo, que sí están demostradas en cualquier cuerpo.

### Cómo retomar
1. `git checkout integracion-opcion1` (o `master` si se fusionó).
2. `lake build TMENudos` y los módulos por nombre (ver la sección 7) para comprobar que todo sigue en 0 errores.
3. Leer, por este orden: esta sección 000, la 5.6 y `20260929_2247_diseno_integracion_knot.md`.
4. Decidir la ruta siguiente con la lista de comprobación de la sección 5.6 (qué toca, si se puede extender el modelo, si hay contraejemplo pequeño, qué depende de ello, y si la sonda es sensible a lo que se teme).

## 00. Resumen de la noche del 29 al 30 de septiembre (LEER PRIMERO)

> **ACTUALIZACIÓN (2026-09-30, mañana):** el autor tomó las decisiones 1 a 4 de la lista de abajo (todas las recomendadas) y se aplicaron en la rama `integracion-opcion1`: Opción 1 en `Schubert.lean` (sección 4.28), capa modular con signo como dato (4.29) y "realizable" sin la órbita de 12 (4.30). La cuarta (`rational_to_diagram` de `Bridge`) NO se pudo cumplir tal cual: choca con la Opción 1 (ver 4.28). **Cifras al cierre de esa tanda:** 34 módulos más la raíz (35, con el módulo nuevo `Modular_Signo`) compilan con 0 errores y 0 alertas; 22 `sorry` en el código (`Schubert` 15, `Reidemeister` 5, `KN_00_Combinatoria` 1, `KN_Instance_K3` 1); 51 axiomas.

Mientras usted dormía se trabajó con autogestión **solo en archivos nuevos de la rama `etapa1-spike-gauss`**, sin tocar la build principal ni `Reidemeister.lean`, `Schubert.lean` ni `Bridge.lean`. Todo está commiteado (último commit de esta sección: ver `git log`) y **verificado por mí** (compilación desde cero, búsqueda de trampas, `#print axioms`, lectura de enunciados), no solo por los informes de los agentes.

### Lo conseguido
| Hito | Resultado | Sección |
|---|---|---|
| **R3** | Invariancia del corchete de Kauffman bajo el movimiento de tres cruces, sin `sorry` (`Etapa1_R3.lean`). Los 48 patrones válidos coinciden exactamente con la geometría; prueba numérica con control negativo confirmada por mi re-ejecución. | 4.24 |
| **Jones completo** | Invariante bajo isomorfismo, R1, R1 libre, R2 y R3 sobre `GDiag` (`Etapa1_Jones.lean`, `Etapa1_JonesR3.lean`). | 4.23, 4.25 |
| **Prototipo de nudos virtuales** | `trefoilV ≠ unknotV`, **`trefoilV ≠ trefoilV'` (el trébol es quiral)** y **`granny_ne_square`** demostrados en Lean (`Etapa1_Nudos.lean`). | 4.25 |
| **Teoría modular frente al Jones** | El modelo modular de K3 pierde la quiralidad porque el signo se **deriva** de las posiciones; la órbita de 12 (`specialClass`) **no es planar**. | 4.26 |
| **Opción 1 consistente** | Modelo extendido con un axioma `jones2` sin `sorryAx`, y borrador compilado contra `Schubert` real que demuestra el enunciado exacto de `granny_distinct_from_square`. | 4.27 |

### Lo que necesita SU decisión (nada de esto se aplicó)
Detalle en `20260929_2247_diseno_integracion_knot.md`.
1. **Integración con `Schubert`** (opción 1, 2 o 3). Hallazgo: los movimientos abstractos generan nudos **virtuales**; redefinir `Schubert.Knot` como ese cociente probablemente contradiría los axiomas de suma conexa y factorización única. Recomendación: **Opción 1** (capa abstracta con `jones2`), ya comprobada consistente.
2. **Signo como dato** en la teoría modular (la única forma comprobada de representar ambas quiralidades).
3. Qué hacer con la **órbita de 12** de K3, que no es planar (¿virtual? ¿se excluye de "realizable"?).
4. Sustituir el axioma `rational_to_diagram` de `Bridge` por una definición (exige decidir la cuestión del signo).
5. Universos (`Type 1` o `Fin n`).

### Qué NO está hecho
`granny_distinct_from_square` sigue con `sorry` en `Schubert.lean`. El análogo está demostrado en el prototipo y en el borrador, pero la integración espera su decisión. Tampoco se han tocado los enunciados dudosos de clase B de `Schubert`.

### Archivos nuevos de la noche (todos en la rama `etapa1-spike-gauss`)
`TMENudos/`: `Etapa1_R3.lean`, `Etapa1_Jones.lean`, `Etapa1_JonesR3.lean`, `Etapa1_Nudos.lean`, `Etapa1_Modular.lean`. `Procesos/`: `20260929_2247_diseno_integracion_knot.md`, y en `Tests/auditoria_20260929/`: `09_r3_numerico.lean`, `09b_r3_hipotesis.lean`, `11_modelo_jones2.lean`, `12_opcion1_sobre_schubert.lean`.

## 0. Punto de suspensión (leer primero)

> **ACTUALIZACIÓN (2026-09-29, noche):** tras la reanudación, **R3 quedó cerrado y verificado** (sección 4.24) y el **Jones invariante sobre `GDiag`** quedó hecho para R1 y R2 (sección 4.23). El resto de esta sección describe el punto de suspensión original y queda como testimonio; para el estado actual, ver las secciones 4.22 a 4.24 y el documento `20260929_2247_diseno_integracion_knot.md`.

**Sesión suspendida el 2026-09-29 por decisión del autor.** El agente que trabajaba en R3 fue detenido a mano; el resto del trabajo estaba terminado y commiteado.

### Dónde está todo
| Rama | Contenido | Último commit |
|---|---|---|
| `master` | Sin cambios | `f3c46bb` |
| `auditoria-2026-09-29` | Auditoría, correcciones, etapa 0, saneamiento de `Schubert`, modelo de consistencia, exploración de quandles | `8179aaa` |
| **`etapa1-spike-gauss`** (rama actual) | Sale de la anterior. Etapa 1 hacia `granny_distinct_from_square`: spike, R1, R2, puente y R3 a medias | el commit de esta suspensión |

Nada se ha subido a ningún remoto ni se ha integrado en `master`. Para retomar: `git checkout etapa1-spike-gauss`.

### Qué se logró en la etapa 1 (todo verificado con compilación desde cero, sin `sorry`, sin axiomas nuevos)
| Pieza | Archivo | Líneas | Resultado principal |
|---|---|---|---|
| Spike de palabras de Gauss con signos | `Etapa1_GaussWord.lean` | 240 | ⟨3₁⟩ = A⁻⁷ - A⁻³ - A⁵ y su espejo, en cualquier cuerpo; `jones_granny_ne_square` en A = 2 |
| Invariancia bajo R1 | `Etapa1_Invariancia.lean` | 1210 | `bracket_map`, `bracket_r1`, `bracket_r1_free` |
| Invariancia bajo R2 | `Etapa1_R2.lean` | 1060 | `bracket_r2` (8 combinaciones válidas de orientación, orden y signo) |
| Puente abstracto ↔ computable | `Etapa1_Puente.lean` | 701 | `bracket_ofWord`, para toda palabra bien formada |

### R3: qué hay y qué falta (trabajo a medias, **no verificado**)
`TMENudos/Etapa1_R3.lean` (1072 líneas, importa `Etapa1_R2`; no forma parte de la build). El agente lo dejó con la arquitectura completa:
- La parte finita (las seis letras nuevas, el grafo local de nueve aristas, `reachB`, `rep`, `matL`, `mi`, `kk`), el diagrama `tri` que inserta el triángulo con dos caras (`o` y `¬ o`), la biyección de estados `r3State`, el lema de aristas `r3_graph_eq` y los lemas de conteo (`count_eq`, `count_circ`, `count_local`).
- La **identidad algebraica** `FF_invariant` (sin `sorry`, cerrada con `field_simp; ring` por casos): la suma de ocho términos es invariante para los patrones válidos `validR3`.
- El teorema final `bracket_r3` **ya escrito**: el corchete de las dos caras coincide para los patrones `validR3`. Solo depende de lo que falta.
- La tabla de patrones válidos sale de `Procesos/Tests/auditoria_20260929/08_geometria_r3.py` (tres rectas en posición general, productos cruzados): **48 de los 64 pares (orden, signos)** son R3 geométricos, y la condición `validR3` excluye exactamente los otros 16 (alturas cíclicas). Que la cuenta coincida es una comprobación de consistencia, no una prueba de que `validR3` y el script describan el mismo conjunto.

**Lo que falta, con el estado exacto:**
1. **Un `sorry`** en `check_all` (línea 258): la comprobación finita de que, para cada uno de los 64 casos, el procedimiento booleano `CheckEq`/`CheckCirc` devuelve `true`. Es una enumeración decidible de casos finitos; no consta qué estrategia se probó (puede exigir partir en casos, subir `maxRecDepth` o reformular la comprobación).
2. **Un error de compilación** en `r3_lazos` (línea 1024, columna 74: `unsolved goals`, sobre un `Nat.card` de componentes tras el `simp`). El agente iba por ahí cuando se lo detuvo.
3. Todo lo demás del archivo compila hasta ese punto, pero al no compilar entero **no hay garantía** de que el resto sea correcto ni de que los enunciados sean los que se pretendían.
4. No consta que se haya hecho la comprobación numérica previa con `Word.bracket` (como en R2) ni el control negativo; el script de geometría sí está. Conviene hacerlas antes de dar R3 por bueno.

### Qué falta después de R3 para cerrar `granny_distinct_from_square`
1. **Writhe sobre `GDiag`** y prueba de que R1 lo cambia en ±1 y R2 y R3 lo conservan, para pasar del corchete al Jones invariante.
2. **Movimientos y `Knot` sobre `GDiag`** (hitos M2 y M3): que `apply_R1/R2/R3` dejen de ser `sorry` y que `Knot` se construya sobre `GDiag` (con el isomorfismo entre diagramas como igualdad), definiendo `trefoil`, `mirror` y `connected_sum` a partir de `ofWord` y de la concatenación. La suma conexa requiere probar que está bien definida sobre el cociente (multiplicatividad del corchete).
3. **Sustituir los axiomas de `Schubert`** (`trefoil`, `mirror`, `connected_sum`, y los que dependan) por esas definiciones. Esto toca `Reidemeister.lean`, `Schubert.lean` y `Bridge.lean`, es decir, la build de la rama principal, y habrá que rehacer el modelo de consistencia (`06_modelo_de_consistencia.lean`).
4. La desigualdad `jones_granny_ne_square` ya está demostrada en el spike; se traslada al cociente con el puente y la invariancia.

### Cómo retomar (orden sugerido)
1. Cerrar los dos puntos de R3 (el `sorry` y el error) y hacer la verificación de siempre: compilación desde cero, búsqueda de trampas, `#print axioms`, y la comprobación numérica pendiente.
2. Writhe sobre `GDiag`.
3. Diseño de M2/M3 (protocolo del mapa de ruta: proponer el diseño al autor antes de tocar `Reidemeister.lean`).
4. Decisiones abiertas del autor (mapa de ruta, sección 10), en particular la quiralidad del trébol en K3 y qué significa "realizable".

### Cifras del proyecto al suspender (rama `auditoria-2026-09-29`; la rama de la etapa 1 no las cambia)
34 módulos compilan sin errores ni alertas; 23 `sorry` en el código (`Schubert` 16, `Reidemeister` 5, `KN_00_Combinatoria` 1, `KN_Instance_K3` 1); 47 axiomas. Los archivos de la etapa 1 no forman parte de esos 34 módulos.

## 1. Estado final en una tabla (cierre de la auditoría y de la etapa 0)

| Métrica | Al empezar | Al terminar |
|---|---|---|
| Módulos que compilan (de 34) | 18 o menos (8 fallaban y otros 8, que dependen de ellos, no llegaron a compilarse) | **34** |
| Errores de compilación | ~90 visibles (8 módulos) más los ocultos por dependencias | **0** |
| Alertas de linter (excluyendo `sorry`) | 104 solo en `Basic.lean`, más las de otros módulos | **0** |
| `sorry` en el código (23 al cierre del saneamiento de `Schubert`; 33 al cierre de la etapa 0) | No medido en todo el proyecto al empezar; solo `Reidemeister` 12 y `Schubert` 27. Los agentes reportaron además `sorry` en `CrossingPairIsomorphism` (13), `KN_00_Combinatoria`, `KN_03`, `KN_Examples` (5), `TCN_05` y `TCN_06` a `TCN_08` | **23** (`Schubert` 16, `Reidemeister` 5, `KN_00_Combinatoria` 1, `KN_Instance_K3` 1) |
| Axiomas | No medido al empezar. 49 tras la auditoría inicial, que ya había convertido `iso_preserves_r1` en teorema y quitado 3 axiomas duplicados de `TCN_08_EJEMPLO` | **47** |
| Contradicciones demostradas | 1 (`R1_inverse`, y `R2_inverse` igual) | **0 conocidas**; consistencia de los 34 axiomas de `Reidemeister`, `Schubert` y `Bridge` verificada por un modelo (4.15) |

Commits de la sesión:

| Commit | Contenido |
|---|---|
| `75708bd` | Auditoría general: 23 archivos corregidos y primer reporte. |
| `df86e7b` | Corrección de los axiomas inconsistentes `R1_inverse` y `R2_inverse`. |
| `ed140db` | `reidemeister_equivalent` pasa a ser una relación inductiva. |
| `92dee92` | Reporte de auditoría actualizado. |
| `bdb627b` | Mapa de ruta. |
| `73f869e` | Etapa 0: saneamiento de enunciados falsos, convención de dos niveles, `IME2`, renombrado a `swap`. |
| `dbdf9dd` | Esta bitácora y las pruebas archivadas en `Tests/auditoria_20260929/`. |

| `957e156` | Correcciones de imprecisiones detectadas al revisar los tres documentos (ver 5.5). |
| (saneamiento de `Schubert`) | Clase A de `Schubert` (ver 4.14). |

## 2. Los hallazgos que más importan

Ordenados por gravedad. Cada uno tiene su detalle en la sección 4.

1. **Los axiomas `R1_inverse` y `R2_inverse` eran contradictorios.** Permitían demostrar `False` (verificado en Lean). Todo lo que importaba `Reidemeister` (`Schubert`, `Bridge`) podía demostrar cualquier cosa. Corregido. (4.5, 4.6)
2. **Los enunciados de `TCN_06` a `TCN_08` sobre estabilizadores y órbitas eran falsos** con las definiciones reales. La clasificación de K3 no tiene tres órbitas (6+4+4) sino **dos, de 12 y 2 elementos**. Corregido. (4.9)
3. **En la teoría KN, `gap_mirror`, `IDE_mirror`, `IME_mirror` e `IME_eq_of_mem_orbit` eran falsos.** Corregido con una convención de dos niveles. (4.10)
4. **`IME` no es un invariante completo.** Es un solo entero y no separa las órbitas (13 órbitas con 10 valores en n=3; 121 con 28 en n=4). Ningún archivo lo afirma; conviene no afirmarlo nunca. (4.11)
5. **`reidemeister_equivalent` estaba definido con `sorry` en su cuerpo**, y `Knot` (el cociente de `Schubert`) se construía sobre él. Corregido con una relación inductiva. (4.7)
6. **Tres operaciones distintas se llamaban `mirror`**: rotación (ρ), reflexión de posiciones (σ) e intercambio over/under (τ). Aclarado y renombrado τ a `swap`. (4.10)
7. **`Basic.lean` (T4.1) decía "estructura diédrica" pero demostraba una estructura abeliana.** Comentario corregido. (4.10)
8. **Enunciados dudosos o falsos de `Schubert`** (nudos tóricos, complementos, nombres intercambiados de los nudos cuadrado y de la abuela…): **clasificados**; los nombres se corrigieron después (4.14), el resto no. (4.4)

**Qué está comprobado en Lean y qué no.** Comprobado en Lean: la inconsistencia de `R1_inverse` (4.5, 4.6), los tamaños de estabilizadores y órbitas de K3 (4.9), el contraejemplo de `IME` bajo la reflexión y el experimento de `IME2` (4.10, 4.11). **No comprobadas en Lean** (valoración matemática del auditor, conviene revisarla): que T(1,q) sea el nudo trivial, el pegado de complementos a lo largo de un anillo, los nombres del nudo cuadrado y de la abuela, y la normalización del polinomio de Alexander.

## 3. Cómo leer los `sorry` restantes

Hay tres clases, y no todos merecen el mismo esfuerzo:

| Clase | Qué significa | Tratamiento acordado |
|---|---|---|
| A. Demostrables | Se pueden cerrar con un arreglo menor. | Cerrarlos. |
| B. Enunciado dudoso o falso | El enunciado mismo está mal. | Reformularlo con aprobación del autor. |
| C. Dependen de teoría que falta | Requieren topología PL, 3-variedades o un modelo concreto de diagrama. | Los profundos (Reidemeister, Haken, Schubert) como **axiomas con cita**; los combinatorios se construyen. |

Estado actual: 0 de clase A, 8 de clase B y 13 de clase C, más 2 fuera de `Reidemeister` y `Schubert` (ver 5.3).

## 4. Registro cronológico detallado

### 4.1 Encargo inicial y alertas de `Basic.lean`
- Primer intento: `lake env lean` sobre `Basic.lean` mostró una sola alerta (`List.Chain'` obsoleto en la línea 668). Se cambió por `List.IsChain`.
- El autor pegó el texto completo de sus alertas: 104 en total. **No aparecían en mi compilación** porque `lake env lean` no aplica las opciones del `lakefile.toml`, que activa `weak.linter.mathlibStandardSet = true`. **Lección:** hay que compilar con `lake build` o con `-Dweak.linter.mathlibStandardSet=true` para ver lo mismo que ve el editor.
- Reproducidas las 104: 68 de "líneas vacías dentro de comandos" (`linter.style.emptyLine`) y 36 del linter `flexible` (`simp` que modifica el objetivo y luego se usa `exact`, `rw`, etc.).
- Corrección: las líneas vacías se borraron por número de línea exacto, tomado de los avisos de Lean. Los `simp` se reemplazaron por el `simp only [...]` que sugiere `simp?`. Hubo un efecto cascada: al arreglar la línea 551 apareció una alerta nueva en la 553 que antes quedaba oculta.
- Resultado: `Basic.lean` sin alertas. (Nota: al borrar líneas, los números de línea que el autor veía en el editor quedaron desplazados; se le explicó.)

### 4.2 `Bridge.lean` y el import que faltaba
- `Bridge.lean` es corto y sin fallas propias. No compilaba porque su dependencia `Reidemeister.lean` tenía errores reales (líneas 35 y 43).
- **Causa:** `Reidemeister.lean` usaba `ℚ` sin importar `Mathlib.Data.Rat.Defs`. Lean trata un símbolo desconocido como variable implícita (con `relaxedAutoImplicit = false` da otro error, pero el efecto es el mismo), y de ahí salían "universe level metavariables" y "Unknown identifier `Crossing`".
- **Corrección:** `import Mathlib.Data.Rat.Defs` en `Reidemeister.lean`. Con eso compilaron `Reidemeister`, `Schubert` y `Bridge`.

### 4.3 La auditoría general: qué se compiló y qué se encontró
- `TMENudos.lean` solo importa 5 módulos (`Basic`, `Reidemeister`, `Schubert`, `Bridge`, `TCN_01`). Los otros 29 no se compilan con `lake build` por defecto. Se compilaron los 34 pidiéndolos por nombre.
- Errores iniciales por archivo: `CrossingPairIsomorphism` 28, `TCN_03_Matchings` 25, `KN_00_Combinatoria` 17, `KN_Examples` 9, `KN_03_Invariantes_General` 5, `TCN_05_Orbitas` 2, `TestPoly` 1, `KN_Instance_K3` 1. Además, los módulos que dependen de los fallidos (`TCN_06`, `TCN_07`, `TCN_08*`, `TCN_AUX`, `KN_03b`, `KN_04`, `TNC_05_1`…) no se llegaron a compilar y escondían más.
- El trabajo se repartió entre agentes en paralelo por familias de archivos independientes (KN, KN_Examples, TCN), más `TestPoly` y `KN_Instance_K3`.
- Correcciones de esa fase (resumen):
  - **`TestPoly`**: `noncomputable def`.
  - **`KN_00_Combinatoria`**: instancia `Fintype` de `OrderedPair` reconstruida; se demostraron `total_ordered_pairs` y `config_is_perfect_matching`; `perfect_matching_partition` con sintaxis corregida; `configs_finite` estaba mal formado (`configs.card < ℕ+`).
  - **`KN_03_Invariantes_General`**: instancias `Decidable` de `encompasses` e `isInterlaced`, `sign_rotate`, `IDE_rotate` (sintaxis `K.rotate k |>.IDE`).
  - **`KN_04_Clasificacion_General`**: `[NeZero n]` en la sección (para `n=0`, `ZMod 0 = ℤ` es infinito y `orbit_stabilizer` es falso); `orbit_stabilizer` demostrado por completo.
  - **`KN_Examples`**: trébol derecho e izquierdo, `k_4_1` y `k_4_2` construidos sin `sorry`; `example_ k_4_1_dme` tenía un typo de sintaxis.
  - **`KN_Instance_K3`**: los imports no llevaban el prefijo `TMENudos.`; las demostraciones de cobertura por `fin_cases` se cambiaron por `decide`; `push_neg` → `push Not`.
  - **`TCN_04_DihedralD6`**: la notación `g • K` con precedencia 70 absorbía el `= R` siguiente (`g • (K = R)`), lo que rompía `TCN_06`, `TCN_07` y `TCN_08`. Se cambió a `notation:73 (priority := high)`. Fue la causa raíz de muchos errores en cadena.
  - **`TCN_AUX`**: estaba roto por nombres inexistentes (`D6Action`, `D6`, `rotatePair`, `orbit_self`); se reescribió.
  - **`CrossingPairIsomorphism`**: faltaba `open KnotTheory`; `iso_preserves_r1` pasó de axioma a teorema.
  - **`TNC_05_1`**: se reducía a un lema verdadero; se eliminó `orbit_bijection`, cuyo enunciado era falso.

### 4.4 Clasificación de los `sorry` de `Reidemeister` y `Schubert`
- Conteo real: **39 `sorry`** (12 en `Reidemeister`, 27 en `Schubert`) y 33 axiomas. La cifra "~41" del inicio incluía comentarios y avisos duplicados del compilador.
- Clasificados en A (9), B (12), C (18). Detalle completo en el reporte de auditoría, sección 4.
- Solo se leyeron los archivos y se clasificó; no se modificó nada en esa fase.

### 4.5 Hallazgo crítico: `R1_inverse` es contradictorio (verificado)
- **Sospecha:** al clasificar, noté que `R1_inverse` (`Reidemeister.lean:188`) pedía `HEq (apply_R1 (apply_R1 K move) move_inv) K` para todo `n`, incluido `n = 0`.
- **Prueba** (`Tests/auditoria_20260929/01_inconsistencia_R1_inverse_original.lean`): con `n = 0` y un movimiento con `add_twist = false`, la resta natural da `0 - 1 = 0`, luego se vuelve a agregar y se obtiene `KnotConfig 1`. El axioma exige entonces `HEq` entre un elemento de `KnotConfig 1` y uno de `KnotConfig 0`, lo que fuerza que ambos tipos sean iguales; pero `KnotConfig 0` tiene un solo elemento y `KnotConfig 1` tiene infinitos (contiene un `ℚ`). Resultado: `#print axioms` mostró que `False` se deduce con `R1_inverse` como único axioma de contenido (aparecen también `propext`, `Quot.sound` y el `sorryAx` heredado de `apply_R1`, que está definido con `sorry`, pero la demostración no usa su contenido).
- **Consecuencia:** `Reidemeister`, `Schubert`, `Bridge` y todo lo que importe `Reidemeister` era inconsistente.

### 4.6 Corrección de `R1_inverse` y `R2_inverse`, con un primer intento fallido
- **Primer intento (insuficiente):** añadir la hipótesis `move.add_twist = true ∨ 1 ≤ n`. Compiló. Pero antes de darlo por bueno probé si seguía habiendo contradicción.
- **Prueba** (`Tests/.../02_inconsistencia_R1_inverse_con_1_le_n.lean`): con `n = 1`, "eliminar y luego agregar" sería la identidad en `KnotConfig 1`, lo que exige que eliminar sea inyectivo desde un conjunto infinito hacia `KnotConfig 0` (un solo elemento). Se dedujo `False` otra vez.
- **Diagnóstico de fondo:** "eliminar y luego agregar" no puede ser la identidad para todo diagrama, porque eliminar pierde información. Solo es válida la dirección **agregar y luego eliminar**.
- **Corrección final (commit `df86e7b`):** los axiomas llevan la hipótesis `move.add_twist = true` (R1) y `move.add_crossings = true` (R2), con comentarios que explican el porqué. `reidemeister_inverse` se reformuló con las mismas hipótesis (era falso para `n = 0`) y quedó demostrado.
- **Verificación:** las dos derivaciones de `False` dejaron de compilar (es lo esperado). Ningún otro módulo usaba estos axiomas.
- **Consistencia:** en este punto de la sesión solo había un argumento informal (agregar un cruce es inyectivo, quitarlo es su inversa por la izquierda). Más tarde se formalizó con un modelo completo (4.15).

### 4.7 `reidemeister_equivalent` como relación inductiva
- **Problema:** `def reidemeister_equivalent K₁ K₂ := ∃ seq, sorry`. Su cuerpo era `sorry`, y `DiagramSetoid` (y por tanto `Knot`) se construía sobre `reidemeister_refl/symm/trans`, que eran `sorry`.
- **Diseño:** relación inductiva con seis constructores: `refl`, `symm`, `trans`, `R1`, `R2`, `R3`. R1 y R2 solo en dirección de *agregar* (la eliminación sale por `symm`), coherente con 4.6.
- **Los axiomas `R*_preserves_isotopy` eran vacíos** (`∃ K', K' = apply_R1 K move` siempre se cumple). Se reemplazaron por enunciados con contenido: cada movimiento preserva `topologically_equivalent`. Sin eso no se puede probar la solidez.
- **Resultado:** `reidemeister_refl/symm/trans` (una línea cada una), `reidemeister_soundness` e `invariant_criterion` (por inducción). `Reidemeister` pasó de 11 a 5 `sorry` en el código en el commit `ed140db` (12 → 11 en `df86e7b`, al demostrar `reidemeister_inverse`).
- **Detalle técnico:** en `invariant_criterion` hubo que hacer `clear h_equiv` antes de `induction`, porque la hipótesis dependía de `K₁` y `K₂` y la de inducción arrastraba una implicación inservible.
- **Nota:** las demostraciones siguen dependiendo de `sorryAx` de forma indirecta porque `apply_R1/R2/R3` están definidos con `sorry`.

### 4.8 Estrategia: qué demostrar y qué axiomatizar
- **Consulta del autor:** dado que Reidemeister está demostrado históricamente, ¿conviene dedicar el tiempo a estabilizar `Reidemeister.lean`? Respuesta: sí, con una precisión. Que un teorema esté demostrado en papel no implica que esté en Lean; Mathlib no tiene teoría de nudos, y la completitud de Reidemeister, Haken y la unicidad de Schubert necesitan topología PL y de 3-variedades.
- **Principio adoptado:** los teoremas profundos ya establecidos se **declaran axiomas con cita**; el contenido combinatorio se **construye**. Ver `20260929_1408_mapa_de_ruta.md` para las etapas 1 a 5 (tipo de diagrama sobre códigos de Gauss en `ZMod (2n)`, movimientos concretos, corchete de Kauffman, conexión con `Bridge`).

### 4.9 Etapa 0.1: los conteos de `TCN_06` eran falsos
- **Hallazgo** (por `decide` y `#eval`, hecho por el agente de la auditoría inicial): con las definiciones reales, `specialClass` tiene estabilizador 1 y órbita 12; `trefoilKnot` 6 y 2; `mirrorTrefoil` 6 y 2. Los enunciados originales decían 2/6, 3/4 y 3/4.
- `mirrorTrefoil = r³ • trefoilKnot`: está en la misma órbita que `trefoilKnot`. Comprobado también como `mirrorTrefoil = K3Config.swap trefoilKnot` por `decide` (`Tests/.../04_...lean`).
- **Corrección:** la clasificación de K3 pasa a **dos órbitas (12 + 2 = 14)**, con representantes `specialClass` y `trefoilKnot`.
  - Eliminados: `stab_special_card`, `stab_trefoil_card`, `stab_mirror_card`, `orbits_disjoint_trefoil_mirror`, `three_orbits_pairwise_disjoint`, `trefoil_not_in_mirror_orbit`.
  - Nuevos o reformulados: `two_orbits_sum_to_14`, `two_orbits_disjoint`, `two_orbits_cover_all`, `orbit_mirrorTrefoil_eq_orbit_trefoilKnot`, `configsNoR1NoR2_eq_two_orbits`.
  - Conteos: `total_realizable_configs` 8 → 14; `realizable_fraction` 1/15 → 7/60 (coincide con `probability_no_r1_no_r2` de `TCN_02`); `non_realizable_count` 112 → 106.
  - `exactly_two_classes` necesitó la condición extra "cada clase es una órbita"; sin ella el `∃!` era falso (cualquier partición en dos bloques cumplía el resto).
  - `configs_no_r1_no_r2_card` (era axioma) y `card_k3_config` (era `sorry`, vale 120) se demuestran con `decide +kernel`.
- **Decisiones abiertas del autor:** (a) el trébol y su imagen especular caen en la misma órbita con esta acción de D₆; (b) "realizable" incluye a `specialClass` aunque su docstring diga que "tiene R2 a nivel de matching".

### 4.10 Etapa 0.2 y 0.4: la teoría KN y la convención de dos niveles
- **Hallazgo** (agente + verificación): con `mirror(a,b) = (-a,-b)`, `gap` usa `(b-a).val` y el reflejado usa `(a-b).val`; suman `2n`. Por eso son **falsos** (no solo difíciles) `gap_mirror`, `IDE_mirror`, `IME_mirror` e `IME_eq_of_mem_orbit` (esta última porque la órbita incluye `mirror`). Contraejemplo con `n = 2`, `K = {(0,1),(2,3)}`: `IME K = 0` e `IME K.mirror = 4`.
- **Análisis de las tres operaciones** (`ρ`, `σ`, `τ`):

  | Op. | Fórmula | Nombre | Significado |
  |---|---|---|---|
  | ρ | `(a,b) ↦ (a+k, b+k)` | `rotate` | Cambiar el punto de partida. |
  | σ | `(a,b) ↦ (−a,−b)` | `mirror` (KN_02); acción de D₆ (TCN_04) | Leer el **mismo** diagrama al revés. |
  | τ | `(a,b) ↦ (b,a)` | `swap` (antes `mirror`/`reverse`) | Imagen especular real (quiralidad). |

- **Discusión con el autor sobre orientación.** Se propusieron dos salidas (un gap simétrico o redefinir `mirror := σ∘τ`). El autor planteó que el nudo orientado es el análisis de primer nivel y el no orientado el de segundo nivel (analizar la estructura en ambas direcciones). Se confirmó con tres precisiones: punto de partida y sentido son elecciones distintas; "analizar en ambas direcciones" es una definición (tomar la clase `{K, σK}`), no una verificación; el primer nivel distingue más (existen nudos no invertibles).
- **Decisión:** convención de **dos niveles**.
  - Nivel 1 (orientado, sin σ): `IME₁` = el `IME` entero de `KN_03`. Es el nivel de `Basic`, cuya relación `Isotopic` se genera con rotaciones y movimientos R1-R3, sin σ. **Ojo:** el `IME` de `Basic.lean` es una *lista* de razones por cruce (`List ℕ`), un objeto distinto del `IME` entero de `KN_03`; los documentos los llaman igual y no están relacionados formalmente.
  - Nivel 2 (no orientado, D₂ₙ): `IME2 K = (min, max)` de `IME₁` sobre `K` y `σK`. `IME2` se define en `KN_03b` y su teorema de órbita está en `KN_04`; `TCN_*` usa la misma acción de D₆ (segundo nivel) pero no `IME2`.
  - No se simetriza el `gap`: eso perdería información; `IME2` conserva el poder de discriminación de `IME₁`.
- **Implementado:**
  - `gap_mirror` → `gap_mirror_add` (`p.gap + p.mirror.gap + 2 = 2n`) y `gap_reverse_mirror`.
  - `IDE_mirror` e `IME_mirror` eliminados; `not_IME_mirror` (por `decide`, `n = 2`) prueba que `IME₁` no es de segundo nivel.
  - `IME_eq_of_mem_orbit` → `IME_eq_of_mem_rotate_orbit` (nivel 1) e **`IME2_eq_of_mem_orbit`** (nivel 2), con `IME2_mirror` e `IME2_rotate`.
  - `(mirror K).ime = K.ime` (era `sorry`) → `ime_swap_multiset` (igualdad de multiconjuntos, para todo `n`).
  - Renombrado de τ a `swap` en `Basic` (`swap_crossing`, `swap_knot`, `swap_involution`), `TCN_01` (`K3Config.swap` y lemas), `KN_General` y `KN_Examples`. Se conservaron `mirrorTrefoil` (unos 47 usos) y `Experiment_K4` por riesgo/alcance.
  - Comentario T4.1 de `Basic` corregido: `inversion (progression (inversion K)) = progression K` (τ conmuta con las rotaciones); el grupo generado por ρ y τ es abeliano, **no diédrico**; la estructura diédrica proviene de σ.

### 4.11 Experimento: ¿IME2 separa las clases? (`Tests/.../03_...lean`)
- **Método:** enumeración completa de todos los emparejamientos orientados de `{0..2n-1}`, convertidos a `KnConfig` con las definiciones reales; clave canónica de la órbita de D₂ₙ y de rotaciones; comparación con `IME₁` e `IME2`.
- **Resultados:**

  | | n=3 | n=4 |
  |---|---|---|
  | Configuraciones | 120 | 1680 |
  | Órbitas de D₂ₙ | 13 | 121 |
  | Órbitas de rotaciones | 22 | 218 |
  | Valores distintos de `IME₁` / `IME2` | 7 / 10 | 13 / 28 |
  | `IME2` constante en cada órbita D₂ₙ | **sí (0 fallos)** | **sí (0 fallos)** |
  | `IME₁` constante en cada órbita de rotaciones | **sí (0 fallos)** | **sí (0 fallos)** |
  | Valores de `IME2` que mezclan órbitas | 3 de 10 | 25 de 28 |
  | Valores de `IME₁` que mezclan órbitas de rotaciones | 5 de 7 | 11 de 13 |

- **Conclusión:** la **invariancia** se confirma, que es lo que afirman los teoremas restaurados. La **completitud** no se cumple ni para `IME2` ni para `IME₁`: es un solo entero. Como `IME₁` tampoco separa las órbitas de rotaciones, el plan alternativo (clasificar solo por rotaciones) tampoco lo habría arreglado.
- **Límite del experimento:** contó configuraciones crudas (incluye reducibles y no realizables). No se midió la separación dentro de las 14 irreducibles de K3.
- **Detalle técnico:** `Finset.toList` no es computable; se usó una codificación numérica del par y `Finset.sort`.

### 4.12 Etapa 0.3: el choque de nombres en `Schubert`
- `Schubert.lean` declaraba `axiom reidemeister_equivalent : Knot → Knot → Prop`, que chocaba en nombre con la relación inductiva de `Reidemeister` (`Schubert` hace `open` de ese espacio de nombres).
- Se eliminó el axioma (en el cociente `Knot` la equivalencia de Reidemeister *es* la igualdad, `≅`), y `reidemeister_preserves_decomposition` se reformuló con `K₁ ≅ K₂` y se demostró con `congrArg`. Axiomas de `Schubert`: 22 → 21.

### 4.13 Verificaciones finales
- `lake build TMENudos` más los 33 módulos restantes por nombre: 3326 trabajos, 0 errores, 0 alertas distintas de `declaration uses sorry` (dos compilaciones completas independientes, antes y después de la etapa 0).
- Ninguna de las verificaciones se apoyó solo en los informes de los agentes: cada tanda de agentes se cerró con una compilación completa hecha directamente.

### 4.14 Saneamiento de la clase A de `Schubert`
- **Diseño** (principio rector del mapa de ruta): los teoremas profundos ya establecidos se declaran axiomas con cita; lo combinatorio se demuestra.
  - `schubert_existence_axiom` (nuevo): todo nudo tiene una factorización prima (Schubert 1949).
  - `schubert_uniqueness` pasa de teorema con `sorry` a axioma (Schubert 1949), con la misma firma.
  - `prime_decomposition` se define con `Classical.choose` sobre la existencia. `prime_decomposition_prime` y `prime_decomposition_reconstructs` dejan de ser axiomas y pasan a ser teoremas; la primera queda más fuerte (sin la disyunción con el nudo trivial).
- **Demostrados**: `schubert_existence`, `schubert_unique_factorization`, `factorization_problem`, y en cadena `complexity_additive`, `composite_characterization`, `example_has_two_prime_factors`, `granny_knot_composite`, `granny_knot_decomposition` (antes `square_knot_*`). Lemas nuevos: `foldl_perm`, `unknot_sum`, `foldl_shift`, `foldl_append`, `decomposition_length_eq`, `decomposition_length_add`, `decomposition_nil_iff`.
- **Conteo**: `sorry` de `Schubert` 26 → 16 (10 cerrados); axiomas de `Schubert` 21 → 21 (entran 2, salen 2); total del proyecto 23 `sorry` y 47 axiomas.
- **Detalle técnico**: para pasar de "equivalencia `Fin l₁.length ≃ Fin l₂.length` con elementos iguales" a "igualdad de multiconjuntos" se usó `Fin.univ_val_map`, `List.ofFn_get` y `Multiset.map_univ_val_equiv`. La invariancia de la suma conexa iterada por permutación usa `List.Perm.foldl_eq` con la instancia `RightCommutative` derivada de la asociatividad y la conmutatividad.
- **Nombres del nudo cuadrado y del nudo de la abuela (corregidos con la aprobación del autor):** `granny_knot := trefoil # trefoil` y `square_knot := trefoil # mirror trefoil` (antes al revés). Los dos teoremas ya demostrados hablaban de trébol # trébol, así que pasaron a `granny_knot_composite` y `granny_knot_decomposition`. No se crearon versiones para `square_knot`: exigirían que la imagen especular del trébol sea prima, y `mirror` es un axioma sin propiedades (no se agregó ningún axioma). `granny_distinct_from_square` conserva su enunciado. Un reemplazo automático dejó mal el comentario explicativo (decía "antes se llamaba `granny_knot`" en ambos sitios); se detectó al releer el código y se corrigió.
- **Verificación de dependencias de los teoremas cerrados** (`Tests/auditoria_20260929/05_...`): `#print axioms` mostraba `sorryAx` sin decir de dónde. Un primer rastreo devolvió una lista vacía porque no recorría los constructores de los tipos inductivos (la relación de Reidemeister vive ahí); con ese hueco corregido, en los 13 teoremas cerrados las únicas constantes con `sorry` son `apply_R1`, `apply_R2` y `apply_R3`. Ningún `sorry` propio de `Schubert` se filtra, y no aparece ningún axioma inesperado.
- **Consistencia**: los dos axiomas son verdaderos para nudos reales; su consistencia con el resto del sistema se verificó después con un modelo (4.15).
- Verificación: compilación completa de los 34 módulos, 0 errores, 0 alertas distintas de `declaration uses sorry`.

### 4.15 Consistencia de los axiomas de `Reidemeister`, `Schubert` y `Bridge`: un modelo
- **Qué se quería saber.** Si los dos axiomas nuevos de `Schubert` (existencia y unicidad) son consistentes con el resto del sistema mientras `apply_R1/R2/R3` sigan sin definición concreta. `#print axioms` no puede responderlo; la única prueba real es exhibir un **modelo**.
- **Por qué hubo que copiar las definiciones.** En el sistema real `apply_R*` son constantes definidas con `sorry` y `Knot` depende de ellas, así que no se pueden reemplazar en el sitio. El modelo reproduce las definiciones no axiomáticas (`Crossing`, `KnotConfig`, los movimientos, la relación inductiva, `Diagram`, `DiagramSetoid`, `Knot`, `unknot`, `is_prime`…) con `apply_R*` definidas concretamente, y enuncia cada axioma con el texto original, demostrado como teorema.
- **Diseño del modelo.**
  - Invariante `inv K`: el multiconjunto de las razones no nulas de los cruces.
  - R1 y R2 (agregar) añaden cruces de razón 0; quitar retira el último cruce retrayendo las posiciones. Solo se exige la dirección "agregar y luego quitar", que se cumple exactamente.
  - R3 es una involución dentro de la fibra de `inv`, construida con una enumeración sobreyectiva de la fibra.
  - Teorema clave: `reidemeister_equivalent K₁ K₂ ↔ inv K₁ = inv K₂`. Así `Knot` se identifica con los multiconjuntos de racionales no nulos: `#` es la suma, `unknot` es 0, los primos son los multiconjuntos de un solo elemento (`is_prime K ↔ card = 1`), y la existencia y unicidad de la factorización salen de ahí.
  - `topologically_equivalent := reidemeister_equivalent`; `trefoil`, `figure_eight` y `cinquefoil` son `{1}`, `{2}` y `{3}`; `mirror` niega las razones; las demás constantes (`knot_genus`, `bridge_number`, `alexander_polynomial`, tipos de complementos, etc.) son triviales.
- **Resultado.** Compila en unos 21 s sin errores. Los 34 axiomas (11 de `Reidemeister`, 21 de `Schubert`, 2 de `Bridge`) tienen su teorema o definición en el modelo, y el `#print axioms` de todos es solo `propext`, `Classical.choice` y `Quot.sound` (o ningún axioma), sin `sorryAx`. Incluye comprobaciones de no trivialidad: `trefoil ≠ unknot`, `trefoil ≠ figure_eight`, `trefoil # trefoil ≠ trefoil`, `mirror trefoil ≠ trefoil` y dos diagramas de un cruce con razones 1 y 2 no son equivalentes.
- **Verificación independiente (no basada en el informe del agente).** Compilé el archivo yo mismo (0 errores; el único "sorry" del texto está en un comentario; sin `axiom`, `native_decide` ni `unsafe`; los `set_option` son solo de impresión). Comprobé que los 34 nombres de axiomas tienen declaración e `#print axioms` en el modelo. Volqué los tipos de 66 objetos y los valores de `Knot`, `knot_isotopic`, `unknot`, `is_prime`, `diagram_equiv` y `DiagramSetoid`, tanto del modelo como de los archivos originales (`06e_tipos_originales.lean`, que además cuenta los axiomas: 11, 21 y 2): el `diff` es vacío. La única normalización del volcado es quitar prefijos de espacio de nombres.
- **Qué implica y qué no.**
  - Implica: no se puede deducir una contradicción de esos 34 axiomas (consistencia relativa a Lean y Mathlib). Como en el sistema real `apply_R*` son `sorry`, que es un axioma inconsistente por sí mismo, la lectura correcta es que los `sorry` son marcadores de posición que **sí admiten** una definición concreta compatible con todos los axiomas.
  - No implica que el sistema describa nudos reales: el modelo es degenerado en lo geométrico (los nudos del modelo son multiconjuntos de racionales no nulos, sin posiciones).
  - No cubre los axiomas de otros archivos (`Basic`, `KN_00_Combinatoria`, `KN_01`, `TCN_01`, `TCN_08_UniformityCriterion`), que hablan de otros tipos.
  - No cubre los teoremas con `sorry`: en el modelo algunos podrían ser falsos. Por eso `mirror` no es la identidad en el modelo, para que `granny_distinct_from_square` no quede refutado, aunque no se demuestra.
  - Habrá que rehacerlo cuando `apply_R*` tengan definición concreta (etapas 1 a 3 del mapa de ruta).

### 4.16 Exploración: ¿hay una vía barata para `granny_distinct_from_square`?
- **Pregunta.** Para demostrar `granny_distinct_from_square` hace falta un invariante que distinga la quiralidad. Los invariantes de coloración por quandles son mucho más baratos de formalizar que el corchete de Kauffman (la invariancia bajo R1-R3 sale de los axiomas del quandle) y los arcos de un código de Gauss con over y under salen solos. ¿Hay un quandle finito cuyo número de coloraciones distinga el trébol de su espejo?
- **Método** (`Tests/auditoria_20260929/07_quandles_trebol_vs_espejo.py`): fuerza bruta sobre todas las tablas de quandle etiquetadas de orden 2 a 6 (1, 5, 36, 404 y 6658). El espejo se colorea con la operación inversa (el quandle dual). Convención: trébol = ternas (x,y,z) con z = x▷y, x = y▷z, y = z▷x.
- **Resultado:** **ninguno** distingue el trébol de su espejo. La vía de coloraciones simples no sirve a órdenes pequeños; haría falta un quandle mayor o un invariante de cociclo, que ya no es barato. Corolario: el corchete de Kauffman (o el polinomio de Jones) sigue siendo el camino.
- **Límites.** Solo se exploró hasta orden 6; no se descarta que exista un quandle mayor. No se verificó el script contra una lista de quandles de la literatura, solo que los conteos de tablas etiquetadas tienen la forma esperada (1, 5, 36, 404, 6658).

### 4.17 Spike M1: palabras de Gauss con signos y corchete de Kauffman (rama `etapa1-spike-gauss`)
- **Decisiones del autor.** Representación: palabra de Gauss con signos. Primer paso: spike de viabilidad en rama aparte, sin tocar la build.
- **Archivo:** `TMENudos/Etapa1_GaussWord.lean` (no importado por `TMENudos.lean`). Una palabra es una lista de letras `(etiqueta, over, signo)`. El corchete es una suma sobre 2ⁿ estados; los lazos de cada estado se cuentan como componentes conexas de un grafo sobre las 2n aristas, con una etiquetación por relajación sobre listas (computable y apta para `decide`). Incluye `swap` (imagen especular), `concat` (suma conexa), `writhe` y `jones`.
- **Convención de suavización** (verificada con el rizo): la suavización A es la orientada en un cruce positivo y la no orientada en uno negativo. ⟨rizo positivo⟩ = -A³ y ⟨rizo negativo⟩ = -A⁻³, ambos demostrados en A = 2.
- **Demostrado sin `sorry`, con axiomas solo `propext`, `Classical.choice` y `Quot.sound`:**
  - `wf_trefoil`, `wf_swap_trefoil` (buena formación).
  - `terms_trefoil`, `terms_swap_trefoil` (los 8 estados con sus lazos, por `decide`).
  - `bracket_trefoil`: **⟨3₁⟩ = A⁻⁷ - A⁻³ - A⁵ en cualquier cuerpo**, y `bracket_swap_trefoil`: ⟨3₁*⟩ = A⁷ - A³ - A⁻⁵. Coinciden con los valores clásicos; con la normalización del writhe da V(3₁) = t + t³ - t⁴.
  - Casos de cordura en A = 2: invariancia por rotación de las 6 rotaciones del trébol, y multiplicatividad ⟨K₁#K₂⟩ = ⟨K₁⟩⟨K₂⟩ para trébol # trébol y trébol # espejo.
  - **`jones_granny_ne_square`**: el Jones evaluado en A = 2 del nudo de la abuela (trébol # trébol) es distinto del del nudo cuadrado (trébol # espejo). Se demuestra con `decide +kernel` en unos 15 s.
- **Qué falta para cerrar `granny_distinct_from_square`.** Este teorema por sí solo NO lo cierra. Falta: (1) que los movimientos R1-R3 y la rotación existan sobre palabras y que `Knot` se construya sobre ellas (hitos M2 y M3); (2) demostrar que el corchete/Jones es invariante bajo esos movimientos (hito M4, el núcleo y lo más difícil); (3) definir `trefoil`, `mirror` y `connected_sum` en `Knot` a partir de `concat` (M3). Con eso, la desigualdad de arriba se traslada al cociente.
- **Hallazgo de diseño.** No hace falta demostrar la multiplicatividad del corchete en general para este teorema: basta la invariancia y evaluar dos palabras concretas. La multiplicatividad solo se necesita para que la suma conexa esté bien definida sobre `Knot`.
- **Limitaciones.** El spike no demuestra ninguna propiedad general del corchete (ni invariancia ni multiplicatividad); las de rotación y suma conexa son instancias en A = 2. No se exige realizabilidad plana. La representación con etiquetas naturales y listas es cómoda para calcular, pero las demostraciones de invariancia sobre el conteo de componentes conexas (hito M4) siguen siendo el riesgo principal. La distinción de Jones se hizo evaluando en un solo punto, lo que basta para mostrar que los polinomios son distintos.

### 4.18 M4, primera prueba de viabilidad: invariancia del corchete bajo R1 (rama `etapa1-spike-gauss`)
- **Decisión de orden.** El riesgo real del plan es el hito M4 (invariancia), no M2 (movimientos sobre listas). Se atacó primero el caso más simple de M4, el rizo (R1), en una representación pensada para demostrar, antes de invertir en movimientos que quizá hubiera que rehacer.
- **Representación abstracta** (`TMENudos/Etapa1_Invariancia.lean`, 1210 líneas, no importado por `TMENudos.lean`): `GDiag ι` es una estructura sobre identificadores de letras con sucesor cíclico `next`, la pareja `partner` (el otro paso por el mismo cruce), las marcas `ovr` y `sign`, y el número `free` de circunferencias sin cruces. Las aristas se nombran por su letra inicial; los cruces son las letras superiores. Insertar cruces solo añade identificadores (`ι ⊕ Bool`), sin renumerar posiciones como en las listas, y el punto de partida deja de existir (la rotación es gratuita). No se exige un solo ciclo, así que admite enlaces. La lista del spike queda como presentación concreta para calcular.
- **Corchete:** suma sobre estados de `A^{#A} B^{#B} d^{lazos-1}`, con los lazos como componentes conexas de un grafo sobre las aristas más las circunferencias libres. Mismas convenciones que el spike (la suavización es orientada cuando `σ x = sign x`).
- **Demostrado sin `sorry`, con axiomas solo `propext`, `Classical.choice` y `Quot.sound`** (verificado con una compilación desde cero de 28 s y sin alertas de linter):
  - `bracket_map`: el corchete es invariante por isomorfismo (renombrar los identificadores).
  - `bracket_r1`: insertar un rizo en una arista existente multiplica el corchete por `-A³` (signo positivo) o `-A⁻³` (negativo). Necesita `[Nonempty ι]` por la resta natural de `d^(lazos-1)`.
  - `bracket_r1_free`: lo mismo sobre una circunferencia libre.
  - `bracket_emptyCircle` (el círculo vale 1) y `bracket_kink` (el rizo aislado vale `-A³` o `-A⁻³`), que coincide con lo calculado en el spike.
- **Dónde estuvo la dificultad.** No en la matemática del rizo, sino en la contabilidad de tipos: los lemas de conteo de componentes (`card_cc_eq`, `card_cc_succ` para un vértice aislado, `card_cc_sum` para uniones disjuntas), la equivalencia de estados con `(estados) × Bool` y la descomposición de los cruces. Unas 20 iteraciones de compilación; lo que lo hizo manejable fue aislar lemas puros sobre relaciones (`PureR1`).
- **Estimación del agente para lo que falta** (no verificada por mí; es una extrapolación): R2 unas 3 a 5 veces el trabajo de R1 (1500 a 2500 líneas: 4 letras nuevas, 4 estados que se reducen a 2 términos con `d`); R3 unas 3 a 4 veces R2, con el riesgo de exhibir un isomorfismo no trivial entre los dos lados del movimiento y emparejar 8 estados con 8. Conclusión del agente: **M4 es viable con esta técnica.**
- **Limitaciones.**
  - El corchete abstracto es no computable (`Nat.card` sobre componentes conexas), así que no hay `#eval` ni `decide` sobre él. Falta el puente con el corchete computable del spike (entregable 5, no intentado): hay que probar que los lazos abstractos coinciden con la unión-búsqueda del spike, o calcular directamente las componentes de los diagramas concretos.
  - Solo está R1. Faltan R2, R3, y la relación con la suma conexa y con `Knot` (hitos M2 y M3).
  - La estimación para R2 y R3 es del agente y puede quedarse corta: el trabajo de R3 con `next` no trivial no se ha medido.

### 4.19 M4, R2: invariancia del corchete bajo el movimiento de dos cruces
- **Archivo:** `TMENudos/Etapa1_R2.lean` (1060 líneas, importa `Etapa1_Invariancia`, no forma parte de la build).
- **Salvaguarda numérica antes de demostrar.** Como en el modelo abstracto los signos no están ligados a la geometría, se comprobó con la versión de listas del spike (en A = 2 y A = 3) qué combinaciones de (`ov`, `par`, `s`) dejan el corchete invariante. Resultado: **las 8 combinaciones son válidas**, con 0 fallos en todas las palabras probadas (todas las de 1 cruce con signos, 576 pares en las de 2 cruces, trébol y espejo, y 780 pares en 26 palabras de 3 cruces). **Control negativo:** con los dos cruces del mismo signo falla en todos los casos (8/8, 576/576, 60/60 y 780/780), lo que confirma que la prueba discrimina y que la regla de signos (s, ¬s) es la correcta.
- **Demostrado sin `sorry`, con axiomas solo `propext`, `Classical.choice` y `Quot.sound`** (compilación desde cero de 38 s, 0 alertas de linter):
  - `def r2 (D) (e f) (hef : e ≠ f) (ov par s : Bool) : GDiag (ι ⊕ (Bool × Bool))`: inserta dos cruces con una hebra en la arista `e` y la otra en la `f`.
  - **`bracket_r2 : (r2 D e f hef ov par s).bracket A = D.bracket A`**, para todo `ov`, `par` y `s`, con `A ≠ 0`.
- **Obstáculo técnico.** Un solo cruce no basta para el conteo de componentes: en el estado identidad, las aristas intermedias caen en la clase de la *otra* hebra. Se resolvió con una retracción por patrón y tres lemas genéricos nuevos (`card_cc_succ'`, `card_local_eq`, `card_local_circ`), y simetrizando sobre `ov` con `smooth_symm`. La identidad algebraica final se cierra con A·A⁻¹ = 1 y d = -A²-A⁻².
- **Observación de alcance.** Estos movimientos se aplican a dos aristas cualesquiera, sin exigir que compartan una cara, es decir, son los movimientos de Reidemeister sobre diagramas de Gauss abstractos (los de la teoría de nudos virtuales). El corchete resulta invariante bajo ellos. Según la literatura (Goussarov–Polyak–Viro), dos diagramas clásicos equivalentes como virtuales lo son también como clásicos, así que esto no rompe nada; no lo he verificado yo.
- **Estimación del agente para R3** (extrapolación suya): directo, de 1200 a 2000 líneas; derivado de R2 más un cálculo local, de 400 a 700. Recomienda la segunda vía, previo un paso 0 numérico.

### 4.20 El puente entre el corchete abstracto y el computable
- **Problema.** La invariancia (R1, R2, y pronto R3) se demuestra sobre `GDiag`, cuyo corchete es no computable (`Nat.card` de componentes conexas); los valores concretos del trébol y de las sumas conexas se calculan con `decide` sobre `Word`. Hacía falta un puente.
- **Archivo:** `TMENudos/Etapa1_Puente.lean` (701 líneas, importa `Etapa1_Invariancia` y `Etapa1_GaussWord`, no forma parte de la build). Compilación desde cero de 27 s, sin `sorry`, `native_decide` ni axiomas nuevos.
- **Se logró la vía general, no el plan alternativo.**
  - `ofWord (w : Word) (hw : Word.wf w = true) : GDiag (Fin w.length)`: sucesor cíclico `finRotate`, pareja calculada con `findIdx`, `free = 1` solo para la palabra vacía.
  - **`bracket_ofWord : (ofWord w hw).bracket A = Word.bracket A w`**, para toda palabra bien formada y todo cuerpo. No exige `A ≠ 0`: ambos lados usan `A⁻¹` con la misma fórmula, así que el enunciado es más fuerte que el pedido.
  - Corolarios: `bracket_ofWord_trefoil` (⟨3₁⟩ = A⁻⁷ - A⁻³ - A⁵) y `bracket_ofWord_swap_trefoil`, trasladados a `GDiag`; además `wf_concat_trefoil` y `wf_concat_trefoil_swap`.
- **Estructura de la prueba.** (i) Corrección de la unión-búsqueda: el invariante `Inv m comp r` dice que dos posiciones tienen la misma etiqueta si y solo si están conectadas por la clausura equivalencia de las parejas aplicadas; con él, `Nat.card` de componentes es la longitud de `eraseDups`. (ii) Los estados abstractos se biyectan con `Fin n → Bool` alineados con `crossings w`. (iii) Las parejas de `pairsAt` coinciden con `smoothRel`. El caso `m = 0` va aparte.
- **Dificultad.** Lo más laborioso fue la corrección de la unión-búsqueda; el resto fue fontanería de índices `Fin` y `getElem` dependientes.
- **Qué permite.** Los valores concretos calculados con `decide` sobre listas se trasladan al diagrama abstracto donde se demuestra la invariancia.

### 4.21 Suspensión durante R3
- El autor pidió suspender la sesión. El agente de R3 llevaba más de 50 minutos y fue **detenido a mano**; su archivo (`Etapa1_R3.lean`, 1072 líneas) y el script de geometría (`08_geometria_r3.py`) se commitean tal como estaban, marcados como trabajo en curso y no verificado.
- Detalle del estado y de cómo retomar: ver la sección 0 de este documento.
- El agente de R3 no llegó a entregar informe final, así que todo lo dicho sobre él sale de leer el archivo y de compilarlo: 1 `sorry` (`check_all`, línea 258) y 1 error (`r3_lazos`, línea 1024).

### 4.22 Reanudación nocturna (2026-09-29, 22:47)
- **Encargo del autor:** retomar los procesos de esta bitácora con autogestión mientras duerme y aprovechar la noche.
- **Regla que me fijé:** avanzar solo en archivos nuevos de la rama `etapa1-spike-gauss`, sin tocar la build principal ni `Reidemeister.lean`, `Schubert.lean` o `Bridge.lean` (el protocolo del mapa de ruta exige proponer el diseño antes de modificarlos y el autor no está para aprobarlo).
- **Plan:** (1) cerrar R3 (`Etapa1_R3.lean`); (2) writhe y Jones invariante sobre `GDiag` (`Etapa1_Jones.lean`); (3) prototipo de `Knot` virtual concreto y el teorema autocontenido `granny ≠ square` en él; (4) documento de diseño de la integración.
- **Hallazgo de diseño (importante):** los movimientos abstractos sobre `GDiag` generan nudos **virtuales**, no clásicos. La desigualdad demostrada en el cociente virtual implica la clásica (los movimientos clásicos son un caso particular), pero **no se puede redefinir `Schubert.Knot` como ese cociente**: según la literatura (no verificada aquí) la suma conexa virtual no está bien definida y la factorización prima no es única, lo que haría falsos varios axiomas de `Schubert`. Detalle, opciones y recomendación en `Procesos/20260929_2247_diseno_integracion_knot.md`. **Requiere decisión del autor.**

### 4.23 Writhe y polinomio de Jones invariante sobre `GDiag` (R1 y R2)
- **Archivo:** `TMENudos/Etapa1_Jones.lean` (194 líneas, importa `Etapa1_R2`, `Etapa1_Puente` y `Etapa1_GaussWord`, no importa `Etapa1_R3`, no forma parte de la build). Verificado por mí: compilación desde cero de 65 s, sin `sorry`, `native_decide` ni axiomas nuevos, `#print axioms` solo `propext`, `Classical.choice` y `Quot.sound`.
- **Definiciones:** `GDiag.writhe D = ∑ x : D.Cross, (if D.sign x then 1 else -1)` y `GDiag.jones A D = (-(A^3))^(-D.writhe) * D.bracket A`.
- **Demostrado:**
  - `writhe_map`, `writhe_r1` (`+ (if s then 1 else -1)`), `writhe_r1F`, `writhe_r2` (sin cambio: los dos cruces nuevos tienen signos `s` y `¬s` y se cancelan).
  - **Invariancia del Jones:** `jones_map` (sin hipótesis sobre `A`), `jones_r1` (con `[Nonempty ι]`), `jones_r1F` (con `1 ≤ D.free`), `jones_r2`. El caso R1 es el interesante: el factor `-A^{±3}` de `bracket_r1` se cancela con el cambio de writhe; el lema algebraico es `jones_kink_factor`.
  - `jones_of_bracket`: patrón genérico para los movimientos que no cambian el writhe (sirve tal cual para R3).
  - **Puente con el spike:** `writhe_ofWord` y `jones_ofWord : (ofWord w hw).jones A = Word.jones A w`.
  - **Trébol:** `jones_ofWord_trefoil = A⁻⁴ + A⁻¹² - A⁻¹⁶` (es decir, t + t³ - t⁴ con t = A⁻⁴) y `jones_ofWord_swap_trefoil = A⁴ + A¹² - A¹⁶`, ambos en cualquier cuerpo con `A ≠ 0`. Comprobado por mí en A = 2: 1/16 + 1/4096 - 1/65536 = 4111/65536 y 16 + 4096 - 65536 = -61424, que coinciden con los valores del spike.
- **Dificultad.** R1 fue fácil una vez aislado el lema algebraico. Lo más incómodo fue `writhe_ofWordP`: pasar de la suma sobre la lista filtrada al subtipo `Cross` (`sum_filter_map`, `Finset.sum_subtype`).
- **Para añadir R3:** probar `writhe_tri` (las dos caras tienen el mismo writhe, como en `writhe_r2`) y deducir `jones_tri` con `jones_of_bracket`. Conviene hacerlo en un archivo posterior que importe `Etapa1_R3` y `Etapa1_Jones`.

### 4.24 R3 cerrado: invariancia del corchete bajo el movimiento de tres cruces
- **Archivo:** `TMENudos/Etapa1_R3.lean` (1085 líneas, importa `Etapa1_R2`, no forma parte de la build). Verificado por mí: compilación desde cero de 67 s, **sin `sorry`, `native_decide` ni axiomas nuevos**; `#print axioms` de `bracket_r3` y `FF_invariant` solo `propext`, `Classical.choice`, `Quot.sound`. Única desviación de estilo: un `set_option linter.flexible false in` en `checkCirc_spec` (el `simp only` equivalente no cerraba un caso).
- **Teorema final:** `bracket_r3 (A) (hA : A ≠ 0) (hv : validR3 (o 0) (o 1) (o 2) (sgc 0) (sgc 1) (sgc 2) = true) : (tri D e he o ovc sgc).bracket A = (tri D e he (fun i => !o i) ovc sgc).bracket A`, con `he : Function.Injective e` y `e : Fin 3 → ι` las tres aristas. Las dos caras del movimiento comparten letras, partners, `ovr` y signos; solo cambia `next`.
- **Cómo se cerró lo que faltaba** (informe del agente, que compilé y verifiqué):
  - `check_all` (64 casos): una sola línea, `decide +kernel` (sin `native_decide`); no hizo falta reformular.
  - `r3_lazos`: el error no era de `Nat.card`. Quedaban términos `![b0,b1,b2] 0/1/2` sin reducir que `ring` tomaba como átomos distintos de `b0`, `b1`, `b2`; se añadieron `e0/e1/e2 : ![b0,b1,b2] i = bi := rfl` y un `simp only` previo.
- **Verificaciones de fidelidad** (las que no se hicieron antes de la suspensión):
  - **Hipótesis realizables y no vacías** (`Tests/auditoria_20260929/09b_r3_hipotesis.lean`, compilado por mí en 25 s): `validR3` es `true` en casos concretos y `false` en otros, exactamente 48 de los 64 patrones lo cumplen, y `bracket_r3` se instancia sobre el trébol como `GDiag (Fin 6)` con aristas `![0,2,4]` (inyectiva, por `decide`).
  - **Comprobación independiente de la geometría** (`08_geometria_r3.py`): el agente comparó los 48 pares (o, s) del script con una transcripción de `validR3` sobre los 64 pares, y los conjuntos son idénticos (no solo el conteo).
  - **Prueba numérica** (`09_r3_numerico.lean`, solo con el corchete de listas del spike y una inserción del triángulo independiente de `Etapa1_R3`; 5 palabras base, los 64 patrones, los 8 `ovc`, A = 2 y A = 3): según el agente, en todos los grupos sale (48 válidos conservan, 16 excluidos rompen, 0 válidos rompen, 0 excluidos conservan). **Mi re-ejecución de ese archivo (unos 7,5 min) confirmó el informe:** los tres grupos dan `(48, 48, 16, 16, 0, 0)`. Es una muestra de las ternas de aristas en las bases grandes, no todas.
- **Alcance:** `bracket_r3` vale sean cuales sean las letras superiores `ovc`; la exclusión de las alturas cíclicas la hace `validR3` a través de la relación entre órdenes y signos. Como en R2, son movimientos sobre diagramas de Gauss abstractos (los de la teoría virtual).
- **Estado de los tres movimientos:** R1, R2 y R3 tienen invariancia del corchete demostrada sobre `GDiag`. Falta el lado de R3 en el writhe (`writhe_tri`) para tener el Jones completo.

### 4.25 Jones completo y prototipo de nudos virtuales: `trefoil ≠ mirror` y `granny ≠ square`
- **Archivos** (dos, no importados por `TMENudos.lean`, sin importar `Reidemeister`, `Schubert` ni `Bridge`; verificados por mí con compilación desde cero, sin `sorry`, `native_decide` ni axiomas nuevos):
  - `TMENudos/Etapa1_JonesR3.lean` (53 líneas): `writhe_tri : (tri D e he o ovc sgc).writhe = D.writhe + ∑ c : Fin 3, (if sgc c then 1 else -1)` (no depende de `o`, luego las dos caras coinciden) y `jones_tri`. Con esto **el Jones es invariante bajo isomorfismo, R1, R1 libre, R2 y R3** sobre `GDiag`.
  - `TMENudos/Etapa1_Nudos.lean` (167 líneas): `structure Diag : Type 1`, la relación inductiva `GRel` (refl, symm, trans, iso, r1, r1F, r2, r3, con hipótesis realizables), `Diag.jones`, `jones_rel`, el cociente `NudoV`, y los nudos `unknotV`, `trefoilV`, `trefoilV'` (imagen especular), `grannyV` y `squareV`.
- **Teoremas** (axiomas: solo `propext`, `Classical.choice`, `Quot.sound`):
  - `trefoilV_ne_unknotV`: el trébol no es el nudo trivial.
  - **`trefoilV_ne_mirror`: el trébol es quiral**, distinto de su imagen especular.
  - **`granny_ne_square`**: trébol # trébol ≠ trébol # espejo. Es el análogo, en el cociente virtual, de `granny_distinct_from_square`.
  - Los tres se prueban aplicando el Jones en A = 2 sobre ℚ y trasladando con `jones_ofWord` los valores calculados con `decide +kernel` en el spike.
- **Alcance (leído en el comentario del módulo y por mí):** los movimientos son los abstractos (nudos virtuales sin detour). Como los clásicos son un caso particular, las clases distintas en `NudoV` también lo son como nudos clásicos, pero esa lectura es informal: no se define el cociente clásico ni el vínculo con `Knot`. No se afirma nada sobre la suma conexa como operación en el cociente (`grannyV` y `squareV` son las clases de los diagramas de `Word.concat`).
- **Movimientos que no están en `GRel`:** R2 sobre la misma arista (`e = f`), R2 y R1 entre circunferencias libres, y cualquier otro cuya invariancia no esté demostrada.
- **Dificultad:** casi ninguna; el empaquetado de las instancias `DecidableEq`/`Fintype` como campos de instancia no dio problemas.
- **Qué significa para el proyecto.** La parte dura de `granny_distinct_from_square` (invariante bien definido bajo los tres movimientos y cálculo concreto) está hecha en el prototipo. **Lo que falta es la integración con `Schubert.lean`, que depende de una decisión del autor** (ver `20260929_2247_diseno_integracion_knot.md`).

### 4.26 La teoría modular frente al Jones: por qué pierde la quiralidad (exploración)
- **Pregunta.** ¿Es la pérdida de quiralidad del modelo de K3 (`mirrorTrefoil = r³ • trefoilKnot`) consecuencia de que en `Basic.lean` el signo del cruce se derive de las posiciones (`crossing_sign c = zmod_sign (under - over)`) en lugar de ser un dato independiente?
- **Archivo:** `TMENudos/Etapa1_Modular.lean` (404 líneas, importa `Basic`, `TCN_06_Representantes` y `Etapa1_GaussWord`; solo lectura, no modifica nada). Verificado por mí: compilación desde cero de 25 s, sin `sorry`, `native_decide` ni axiomas nuevos (la palabra "sorry" aparece solo en un comentario). Casi todo con `decide +kernel`.
- **Resultado principal: sí.**
  - Las tres parejas de `trefoilKnot` son **antipodales** (`u - o = 3` en `ZMod 6`; `trefoilKnot_antipodal`, `mirrorTrefoil_antipodal`), así que el signo derivado vale +1 en todas (`derived_sign_trefoil`; en general `zmod_sign_antipodal`: `x.val = n → zmod_sign x = 1`, para todo `n`).
  - `mirrorTrefoil` es la imagen de `trefoilKnot` por `reverse` (`mirrorTrefoil_eq_reverse`), pero como el signo no cambia con el intercambio, su Jones es el mismo: `jones_mirror_eq_trefoilKnot` (4111/65536 en A = 2, es decir, el **trébol derecho**).
  - El trébol izquierdo (`swap trefoil`) da -61424 y difiere (`jones_modular_trefoil_ne_left`); la palabra de `mirrorTrefoil` no es el `Word.swap` de la de `trefoilKnot` (`toWord_mirror_ne_swap`). **Con signo derivado, la teoría modular solo produce el trébol derecho en los diagramas de trébol de K3.** Lo sabemos solo para las configuraciones K3 estudiadas; no hay prueba de que ningún otro dato modular represente el izquierdo.
- **Propuesta (comprobada en Lean):** tomar el signo como **dato**: cruces `(o, u, σ)`, con `swapS` que intercambia `o` y `u` y niega `σ`. Entonces el trébol da 4111/65536, su `swapS` da -61424 y difieren (`signed_trefoil_jones`, `signed_swap_trefoil_jones`, `signed_swap_changes_jones`); el signo derivado queda como caso particular (`withDerived_trefoil`); y D₆ (con `σ` conservado) deja el Jones constante en las órbitas (`signed_D6_invariant_trefoil`, `signed_D6_invariant_special`). **Alternativa** (signo por paridad de la posición superior) también separa las quiralidades del trébol, pero una rotación por 1 cambia la quiralidad (`parity_rotation_flips`), y que valga para diagramas alternantes en general es una conjetura del agente, comprobada solo en el trébol.
- **Hallazgo adicional importante: la órbita de 12 (`specialClass`) no es planar.**
  - Con la condición de paridad de Gauss (una cuerda debe entrelazarse con un número par de otras; es una condición **necesaria** de planaridad), solo pasa la órbita de 2 (la del trébol); ninguna de las 12 configuraciones de la otra órbita la cumple (`gauss_parity`). Leí la definición (`interlaceDeg`, `gaussEven`) y es la condición correcta.
  - Su Jones no es el del nudo trivial (`specialClass_not_unknot`) ni el de un trébol (79/1024 ≠ 4111/65536 ≠ -61424). Son objetos virtuales, no diagramas clásicos (la lectura de que los exponentes de A no son congruentes módulo 4 es interpretación del agente, no probada).
  - Con signo derivado, el Jones ni siquiera es constante en esa órbita: hay dos valores (79/1024 para las de writhe derivado +3 y 949/4 para las de -1; `derived_D6_not_invariant_special`), porque la reflexión de D₆ invierte `u - o` y con él el signo derivado. Con el signo como dato desaparece la incoherencia.
- **Qué dice esto de las dos decisiones abiertas del autor** (mapa de ruta, sección 10):
  - *Quiralidad en K3* (n.º 4): tiene explicación. No es un fallo de la acción de D₆, sino de que el signo está derivado. Para representar ambas quiralidades hace falta el signo como dato.
  - *«Realizable» en K3* (n.º 5): que `specialClass` cuente como realizable (por ser «irreducible», sin R1 ni R2) es dudoso, porque ninguna configuración de su órbita es planar; solo la órbita del trébol lo es.
- **Limitaciones:** todo el Jones está evaluado en A = 2 sobre ℚ (las formas simbólicas en A vienen de un script de Python externo, no demostrado); la versión "cruda" con listas está ligada a `K3Config` solo para los tres representantes; el caso general `RationalConfiguration n` solo se ejercitó con n = 3; no se enlazó formalmente con `hasR1`/`hasR2`.

### 4.27 La Opción 1 es consistente: modelo extendido y borrador compilado contra `Schubert`
- **Qué se quería saber.** El riesgo principal de la Opción 1 del documento de diseño (añadir a la capa abstracta de `Schubert.lean` un invariante `jones2 : Knot → ℚ` con su especificación) es que fuera inconsistente con los 34 axiomas ya verificados.
- **Modelo extendido** (`Tests/auditoria_20260929/11_modelo_jones2.lean`, copia del modelo 06 con una extensión): en el modelo, `jones2 K` es el producto sobre los elementos `q` de `Finv K` de un factor `f q` con `f 1 = 4111/65536`, `f (-1) = -61424` y `f q = 1` en otro caso. Se demuestra la multiplicatividad (`jones2_connected_sum`), `jones2_unknot`, `jones2_trefoil` y `jones2_mirror_trefoil`. Verificado por mí: compila con 0 errores; **ningún objeto del archivo (46 con `#print axioms`, los 34 axiomas originales y los nuevos) depende de `sorryAx`**; los nuevos dependen solo de `propext`, `Classical.choice` y `Quot.sound`. Es decir, **la Opción 1 es consistente con los 34 axiomas anteriores** (consistencia relativa a Lean y Mathlib, como el resto).
- **Borrador contra el `Schubert` real** (`Tests/auditoria_20260929/12_opcion1_sobre_schubert.lean`, no modifica `Schubert.lean`): declara `jones2` y sus especificaciones como axiomas en un espacio de nombres aparte y demuestra `granny_distinct_from_square_borrador : ¬(granny_knot ≅ square_knot)` (el enunciado exacto de `Schubert.lean`) por multiplicatividad y los valores en `trefoil` y `mirror trefoil`. Compila con 0 errores. Los axiomas de los que depende son exactamente `connected_sum`, `mirror`, `trefoil`, `jones2`, `jones2_connected_sum`, `jones2_trefoil` y `jones2_mirror_trefoil` (más los estándar y el `sorryAx` heredado de `apply_R*`).
- **Detalle práctico:** `Schubert.lean` no importa `Mathlib.Tactic.Linarith` ni la extensión de `norm_num` para divisiones; si se adopta la Opción 1 allí, habrá que añadir esos imports (sin ellos `norm_num` no decide la desigualdad de racionales).
- **Alcance y límites:** la consistencia relativa no valida que la especificación describa nudos reales. La conexión entre el `Knot` abstracto y el módulo concreto (`Etapa1_Nudos.lean`), que demuestra las mismas propiedades para los diagramas concretos, seguiría siendo axiomática. Este resultado NO decide entre las opciones 1, 2 y 3: solo elimina el riesgo de inconsistencia de la 1.

### 4.28 Decisiones del autor y primera integración en la build: la Opción 1 en `Schubert.lean`
- **Decisiones del autor (2026-09-30), todas las recomendadas:** (1) integración por la **Opción 1** (axioma `jones2` en la capa abstracta); (2) adoptar el **signo del cruce como dato** en la teoría modular; (3) **excluir la órbita de 12 de "realizable"**; (4) sustituir `rational_to_diagram` de `Bridge` por una definición concreta "después de fijar el signo".
- **Conflicto detectado en (4) y cómo se resolvió.** Con la Opción 1, `Knot` sigue siendo el abstracto y el `Diagram` de `Bridge` sigue siendo el del modelo antiguo de `Reidemeister.lean` (cuyas posiciones viven en `Fin n`, no en `ZMod (2n)`). Definir `rational_to_diagram` de forma concreta exigiría cambiar `Diagram` a `GDiag`, justo lo que la Opción 1 evita. **El axioma de `Bridge` NO se cierra**; en su lugar se da la función concreta en la capa paralela (fuera de la build). Esto queda pendiente de una nueva decisión del autor.
- **Rama:** `integracion-opcion1` (sale de `etapa1-spike-gauss`), para separar los cambios de la build principal.
- **Cambio en `Schubert.lean`** (primer cambio de la etapa 1 que entra en la build):
  - Cuatro axiomas nuevos: `jones2 : Knot → ℚ`, `jones2_connected_sum` (multiplicativo), `jones2_trefoil = 4111/65536` y `jones2_mirror_trefoil = -61424`. No se añadió `jones2_unknot` porque la demostración no lo usa.
  - **`granny_distinct_from_square` deja de ser `sorry`** y se demuestra: si fueran iguales, `jones2` de ambos coincidiría, pero valen `(4111/65536)²` y `4111/65536 · (-61424)`. Se añadieron los imports `Mathlib.Tactic.Linarith` y `Mathlib.Tactic.NormNum` (sin ellos `norm_num` no decide la desigualdad de racionales).
  - Comentarios que explican la justificación y **qué queda axiomático: la conexión entre el `Knot` abstracto y el módulo concreto** de la rama de la etapa 1.
- **Cifras de `Schubert`:** `sorry` en el código 16 → **15**; axiomas 21 → **25**. Proyecto: axiomas 47 → **51**; `sorry` 23 → **22** (a falta de lo que cambien las tareas en curso).
- **Modelo de consistencia actualizado** (`Tests/auditoria_20260929/11_modelo_jones2.lean`, ahora el **modelo vigente**; `06_modelo_de_consistencia.lean` queda como registro histórico de la versión de 34 axiomas). Verificado por mí contra el `Schubert` ya modificado: compila con 0 errores y sin `sorryAx`; el recuento de axiomas reales es 11 (Reidemeister) + 25 (Schubert) + 2 (Bridge) = **38**; y el volcado de tipos de **70 objetos** del modelo es idéntico al de los originales (`06e_tipos_originales.lean`, ampliado con los cuatro nombres nuevos), sin ningún "NOT FOUND". Es decir, **los 38 axiomas del sistema real son consistentes entre sí** (consistencia relativa a Lean y Mathlib).
- **Build:** los 34 módulos siguen compilando tras el cambio (verificación final al cerrar los tres bloques de trabajo).

### 4.29 Capa modular con signo como dato: el trébol y su espejo son órbitas distintas
- **Archivo:** `TMENudos/Modular_Signo.lean` (388 líneas; importa `Basic`, `TCN_01_Fundamentos` y `TCN_04_DihedralD6`; **aditivo**: no modifica ningún archivo existente ni entra en `TMENudos.lean`). Verificado por mí: compilación desde cero de 22 s, sin `sorry`, `native_decide` ni axiomas nuevos (esas palabras solo aparecen en el comentario de cabecera); `#print axioms` de los 13 teoremas principales, solo `propext`, `Classical.choice`, `Quot.sound` (dos de ellos, menos).
- **Qué define:** `SignedCrossing n` (un `RationalCrossing n` más un signo `pos : Bool`), `swapS` (intercambia over/under y **niega** el signo), `rotateS` (conserva el signo) y `ofDerived` (el signo derivado de `Basic` como caso particular). Para K3, una estructura propia `SignedK3` (`K3Config` no admite signo por pareja) con `actS g`, la acción de D₆ de `TCN_04` que lleva el signo consigo (también bajo la reflexión), `trefoilS` = {(0,3,+),(4,1,+),(2,5,+)} y `mirrorS := trefoilS.swapS`.
- **Teoremas para `n` general:** `swapS_involutive`, `rotateS_swapS`, y `ofDerived_swap_iff : ofDerived (swap_crossing c) = swapS (ofDerived c) ↔ (modular_ratio c).val ≠ n`, es decir, **el signo derivado coincide con el intercambio firmado si y solo si la pareja no es antipodal**; ahí está exactamente la pérdida de quiralidad.
- **Teoremas para K3 (`decide +kernel`):**
  - **`mirrorS_not_in_orbit : ∀ g : DihedralGroup 6, actS g trefoilS ≠ mirrorS`** (cuantificado sobre los 12 elementos de D₆): **el trébol y su imagen especular son clases distintas en la teoría firmada.**
  - Sanidad: cada órbita tiene exactamente 2 configuraciones (`orbit_trefoilS_card`, `orbit_mirrorS_card`) y su unión tiene 4 (`orbits_disjoint_card`); hay elementos de D₆ que fijan `trefoilS` y otros que la mueven.
  - Con el signo derivado: `derived_trefoil : ofDerivedK3 trefoilK3 = trefoilS`, `swap_eq_rot3` (`mirrorTrefoil = r³ • trefoilKnot`, confirma el hallazgo previo) y `derived_mirror_not_mirrorS : ∀ g, ofDerivedK3 trefoilK3.swap ≠ actS g mirrorS` (con signo derivado el espejo cae en la clase del trébol y nunca en la de `mirrorS`).
  - **Precisión del agente sobre mi pedido:** el derivado del espejo NO es literalmente `trefoilS`, sino `r³ • trefoilS` (`derived_mirror`); igualar `trefoilS` solo vale módulo D₆.
- **Conteos (por `#eval` con listas crudas, NO son teoremas):** 120 configuraciones sin firmar y 960 firmadas (×2³); 90 órbitas de D₆ entre las firmadas, con tamaños {2, 4, 6, 12}; las 16 firmadas de la clase del trébol se reparten en 4 órbitas de tamaños [2, 6, 6, 2] (las dos de tamaño 2 son las de `trefoilS` y `mirrorS`; las otras dos, de signos mixtos).
- **Alcance:** capa aditiva. **La migración de `Basic` y `TCN` para que usen esta noción en lugar del signo derivado exige aprobación aparte** (por archivo), y cambiaría conteos y teoremas en cascada.
- **Sobre la decisión (4):** la función concreta `RationalConfiguration → GDiag` con signo como dato sigue sin escribirse; queda para la capa paralela de la rama de la etapa 1.

### 4.30 "Realizable" en K3 excluye la órbita de 12
- **Decisión del autor:** `isRealizable` deja de significar "sin R1 ni R2" y pasa a exigir también la paridad de Gauss (condición **necesaria** de planaridad); así solo la órbita del trébol (2 configuraciones) es realizable.
- **Archivos** (todos en la build): `TCN_08_Realizabilidad.lean`, `TCN_08_Realizabilidad_EJEMPLO_DIDACTICO.lean` y `TCN_AUX_Teoremas_Auxiliares_Realizabilidad.lean` (este último, solo una nota de comentario). Verificado por mí: los tres compilan con los linters del lakefile, y **la build completa de los 34 módulos más la raíz pasa con 0 errores y 0 alertas**. En el diff añadido no hay `sorry` ni axiomas (las tres menciones son comentarios).
- **Definiciones nuevas:** `strictlyBetween`, `chordsInterlace` (los cuatro extremos distintos y exactamente uno de los de `q` estrictamente entre los de `p`), `gaussEven K` (cada pareja se entrelaza con un número par de las otras) y `isRealizable K := (¬hasR1 K ∧ ¬hasR2 K) ∧ gaussEven K`.
- **Teoremas clave:** `chordsInterlace_actOnPair` (la acción de D₆ conserva el entrelazado; `decide +kernel` sobre todo `ZMod 6`), de donde `gaussEven_iff_of_mem_orbit` (realizable es propiedad de la órbita); **`realizable_iff_trefoil_orbit : isRealizable K ↔ K ∈ orbit trefoilKnot`**; no vacuidad: `isRealizable_trefoilKnot`, `isRealizable_mirrorTrefoil`, `specialClass_not_realizable`, `orbit_specialClass_not_realizable`.
- **Enunciados cambiados (antes → después):** `isRealizable`: `K ∈ Orb(special) ∨ K ∈ Orb(trefoil)` → `(¬R1 ∧ ¬R2) ∧ gaussEven`; `realizableConfigs`: 14 → 2 elementos; `total_realizable_configs`: 14 → **2**; `realizable_fraction`: 7/60 → **1/60**; `non_realizable_count`: 106 → **118** (106 reducibles + 12 irreducibles no planas, con `irreducible_not_realizable_count = 12`); `irreducible_dichotomy`: era una tautología → `isRealizable K ∨ K ∈ Orb(specialClass)`; `k3_realizability_characterization`, `realizable_iff_representative`, `realizable_by_transformation`, `not_realizable_criterion` y `irreducible_realizable_iff` reformulados. `irreducible_is_realizable` (ya falso) se elimina; lo sustituyen `irreducible_of_realizable` (realizable ⇒ irreducible) e `irreducible_realizable_iff_not_special`.
- **Se conserva** la clasificación de `TCN_07` (14 irreducibles en 2 órbitas, de 12 y 2); ahora solo una de las dos clases es realizable.
- **Para que el autor revise (del informe del agente):** (1) `chordsInterlace` exige extremos distintos, porque sin eso el criterio con `.val` no es invariante por rotación cuando dos cuerdas comparten un extremo (en K₃ las cuerdas distintas nunca lo comparten); (2) se definió `isRealizable` como conjunción y se probó su equivalencia con la órbita del trébol, en lugar de definirlo directamente como pertenencia a la órbita; (3) la paridad de Gauss es solo condición necesaria: en K₃ coincide exactamente con el trébol, pero la definición sola no prueba planaridad; (4) `irreducible_dichotomy` y `realizable_orbit_card_cases` conservan el nombre pero cambió su contenido (el segundo es ahora más débil de lo que se cumple); se pueden renombrar; (5) el diff de `TCN_08_Realizabilidad` es grande porque se reescribió buena parte del módulo.

### 4.31 Clase B: reformulación de los enunciados falsos (rama `clase-b-y-capa-paralela`)
- **Decisión del autor:** empezar por lo barato y seguro (reformular los enunciados falsos de la clase B).
- **Resultado:** build de los 34 módulos más la raíz, 0 errores y 0 alertas (3 327 trabajos). `sorry` en el código 22 → **17** (`Schubert` 15 → 11, `Reidemeister` 5 → 4); axiomas sin cambio (51). Cada cambio lleva un comentario "antes → después" en el propio código.
- **Cambios (antes → después):**
  | Enunciado | Antes | Después |
  |---|---|---|
  | `minimal_characterization` (`Reidemeister`) | `is_minimal K ↔ (todo movimiento con `¬add_twist` → False) ∧ (…)`: **falso** (el lado derecho es siempre `False`; el diagrama vacío es minimal). Incluso corregido, "minimal ⇔ sin R1 ni R2 reductores" es falso en teoría de nudos. | Sustituido por dos implicaciones **verdaderas y demostradas**: `not_minimal_of_add_twist` y `not_minimal_of_add_crossings` (un diagrama al que se le agregó un giro, o dos cruces, no es minimal). `sorry` −1. |
  | `schubert_torus_knot_primality` | sin hipótesis: **falso** (`T(1,q)` es el nudo trivial y `gcd 1 q = 1`; igual con `p = 0`) | con `2 ≤ p` y `2 ≤ q`. Sigue con `sorry` (clase C: `torus_knot` no tiene contenido). Además se corrige en el comentario que `T(-p,-q)` es el mismo nudo con la orientación invertida y la imagen especular es `T(p,-q)`. |
  | `schubert_companion_theorem` | `genus K ≥ genus P ∧ ∃ pattern, K ≅ sorry`: parte segunda **mal formada** (`sorry` dentro del enunciado) | solo `genus K ≥ genus P`. Sigue con `sorry` (clase C). `sorry` −1 (dos fichas pasan a una). |
  | `alexander_multiplicative` | igualdad literal en `Polynomial ℤ`, dependiente del representante | `∃ (ε : ℤˣ) (a b : ℕ), C ε * X^a * Δ(K₁#K₂) = X^b * (Δ K₁ * Δ K₂)` (igualdad salvo unidades ±tᵏ). Sigue con `sorry` (clase C). |
  | `schubert_complement_sum` | igualdad de **tipos** y matemáticamente incorrecta (el complemento de `K₁#K₂` se obtiene pegando los complementos a lo largo de un anillo, no por suma conexa) | **eliminado**: una versión verdadera necesita nociones de 3-variedad y pegado que el marco no tiene. Nada depend00eda de él. `sorry` −1. El axioma `manifold_connected_sum` queda sin uso. |
  | `schubert_is_JSJ_special_case` | enunciado con `sorry` dentro de la proposición | **eliminado**: necesita un vínculo `Knot` → `ThreeManifold` que no existe. Nada dependía de él. `sorry` −2. Los axiomas `ThreeManifold` y `JSJ_decomposition` quedan sin uso. |
  | `knot_primality_in_NP` (comentario) | decía "está en NP" | el enunciado solo afirma **decidibilidad**; se corrige el comentario, sin cambiar enunciado ni nombre |
- **Alcance y límites:** ninguna reformulación añade axiomas, y las dos eliminaciones no dejan referencias (comprobado por la compilación completa). Los dos axiomas que quedan sin uso (`manifold_connected_sum`, y `ThreeManifold` con `JSJ_decomposition`) siguen en el modelo de consistencia sin cambios.
- **Qué sigue en clase C tras esto:** `schubert_torus_knot_primality`, `schubert_companion_theorem` y `alexander_multiplicative` ya son enunciados verdaderos, pero dependen de definiciones sin contenido (`torus_knot`, `is_satellite`, `knot_genus`, `alexander_polynomial`).

### 4.32 `rational_to_diagram` en la capa paralela: `Etapa1_Bridge.lean`
- **Decisión del autor:** dar la función concreta solo en la capa paralela; **el axioma `rational_to_diagram` de `Bridge.lean` NO se cierra** (su codominio es el `Diagram` del modelo antiguo; cerrarlo exigiría pasar a `GDiag`, lo que choca con la Opción 1).
- **Archivo:** `TMENudos/Etapa1_Bridge.lean` (329 líneas; importa `Basic`, `Modular_Signo`, `Etapa1_Puente`, `Etapa1_Jones`, `Etapa1_Modular`, `Etapa1_Nudos` y `Etapa1_GaussWord`; no importa `Reidemeister`, `Schubert` ni `Bridge`; fuera de la build). Verificado por mí: compilación desde cero de 29 s, sin `sorry`, `native_decide` ni axiomas nuevos; `#print axioms` de los teoremas principales, solo `propext`, `Classical.choice`, `Quot.sound`.
- **Definiciones (generales en `n`, con `[NeZero n]`):**
  - `SignedRationalConfiguration n` (una `RationalConfiguration n` más `sgn : Fin n → Bool`), con `ofDerived` (el signo derivado de `crossing_sign`) y `mirror` (aplica `swap_knot` y niega cada signo).
  - `ofSigned rc : GDiag (ZMod (2*n))`: `next = +1`, `free = 0`, y `partner`, `ovr`, `sign` a partir del cruce que contiene cada posición (justificado con `coverage` y `all_positions_distinct`); los cuatro axiomas de `GDiag` están demostrados en general.
  - `signedToDiag rc` (signo dato) y `rationalToDiag rc` (signo derivado): la función concreta de la capa paralela, con valores en el `Diag` de `Etapa1_Nudos`.
- **Criterio de corrección** (`ofSigned_eq_map`, general): si en cada posición el diagrama coincide con el de una palabra de Gauss transportado por un isomorfismo, entonces `ofSigned rc = (ofWord w hw).map e`, de donde el Jones coincide con el de la palabra. La comprobación posición por posición se hace con `decide +kernel` sobre `Fin 6 ≃ ZMod 6`.
- **Pruebas de que es la función correcta (solo n = 3, el trébol):**
  - `jones_ofSigned_trefSRC = 4111/65536` (trébol firmado +,+,+) y `jones_ofSigned_mirrorSRC = -61424` (su espejo firmado: parejas intercambiadas y signos -,-,-).
  - `signedToDiag_tref_ne_mirror`: con signo dato, las clases en `NudoV` del trébol y de su espejo son **distintas**.
  - Con signo derivado: `ofDerived_trefoilRC : ofDerived trefoilRC = trefSRC`, `rationalToDiag_loses_chirality` (el Jones del trébol modular y el de su "espejo" `swap_knot` **coinciden**) y `rationalToDiag_mirror_ne_genuine_mirror` (ese valor es distinto del -61424 del espejo genuino). Es exactamente la pérdida de quiralidad explicada en 4.26, ahora vista a través de la función concreta.
- **Limitaciones (del informe y leídas por mí):** las pruebas de corrección cubren solo el trébol; no hay teorema general `ofSigned (ofDerived rc) ≅ ofWord rc.toWord` (el método `ofSigned_eq_map` sirve para cualquier otra configuración con la misma comprobación). Con signo derivado solo se prueba que el Jones coincide, no que las clases en `NudoV` sean iguales. `ofSigned` no exige planaridad, así que las clases son de nudos virtuales (mismo alcance que `Etapa1_Nudos`). El archivo arrastra la importación de `TCN_06_Representantes` vía `Etapa1_Modular`.
- **Qué queda de la decisión (4):** cerrar el axioma de `Bridge` sigue pendiente y depende de la ruta R1 (ver 5.6).

## 5. Pendiente y dónde retomar

### 5.1 Decisiones del autor
> **Estado (2026-09-30):** los puntos 1 y 2 y la integración de la Opción 1 ya están decididos y aplicados (4.28 a 4.30); el punto 3 se resolvió con las palabras de Gauss con signos. Las rutas realmente abiertas hoy están en la sección 5.6.
1. **Quiralidad en K3:** con la acción actual de D₆, el trébol y su imagen especular están en la misma órbita. ¿Es lo pretendido? Si no, hay que cambiar la acción o las definiciones.
2. **"Realizable" en K3:** ¿debe incluir a `specialClass`? Hoy sí.
3. **Etapa 1 del mapa de ruta:** representación del diagrama (código de Gauss extendido frente a PD) y si `KnotConfig` se reemplaza o se conserva como capa.
4. **Nombre de σ:** la reflexión de `KN_02` sigue llamándose `mirror` aunque no es una imagen especular. `reflect` sería más fiel, a costa de un renombrado amplio.

### 5.2 Trabajo técnico identificado
1. ~~Clase A de `Schubert`~~ Resuelta (ver 4.14).
2. **Clase B** (7 `sorry` en `Schubert` y 1 en `Reidemeister`):
   - `minimal_characterization` (`Reidemeister.lean`): falso, el lado derecho es siempre `False`.
   - `schubert_torus_knot_primality`: falso; T(1,q) es el nudo trivial, no primo. Debe exigir p,q ≥ 2.
   - `schubert_complement_sum`: compara tipos con igualdad, y el complemento de K₁#K₂ se pega a lo largo de un anillo, no por suma conexa.
   - `schubert_companion_theorem` y `schubert_is_JSJ_special_case`: tienen `sorry` dentro del propio enunciado.
   - `alexander_multiplicative`: el polinomio de Alexander está definido salvo unidades ±tᵏ.
   - ~~`square_knot` y `granny_knot`~~ Corregidos (ver 4.14).
3. **Etapa 1 a 5 del mapa de ruta:** dar definiciones concretas a `apply_R1/R2/R3` (elimina la dependencia indirecta de `sorryAx`), corchete de Kauffman, conexión con `Bridge`, y demostrar consistencia exhibiendo un modelo.
4. `Experiment_K4.lean` sigue llamando `mirror` a τ (`k4_neq_mirror`, `user_k4_mirror_pairs`).
5. `TMENudos.lean` solo importa 5 de los 34 módulos.

### 5.3 `sorry` y axiomas fuera de `Reidemeister` y `Schubert`
- `KN_00_Combinatoria.lean:300`: `perfect_matchings_upper_bound`, verdadero; falta la biyección de conteo.
- `KN_Instance_K3.lean:40`: igualdad de tipos entre una estructura y un subtipo; lo correcto es una `Equiv`.
- Axiomas: `KN_00_Combinatoria` (`exists_valid_config`), `TCN_01` (1), `TCN_08_UniformityCriterion` (`uniformity_criterion`), `KN_01` (5), `Basic` (5), `Bridge` (2).

### 5.4 Archivos y copias que no forman parte de la build
- `Procesos/codigo LEAN/*_TEST.lean` y `__correcciones_*.lean` contienen copias antiguas con `K.mirror` y otras convenciones. No se tocaron.
- Sueltos en la raíz que probablemente sobran: `build_error.log`, `temp_mirror_theorems.txt`, `lean-toolchain.backup`.
- Hay dos desarrollos paralelos de la misma teoría (`KN_*` y `TCN_*`) más `KN_General`, que además define `OrderedPairN` con su propio `mirror`/`swap`. Conviene decidir cuál es el canónico.

### 5.6 Mapa de rutas abiertas y cómo ver el conflicto o el éxito de antemano (2026-09-30)

**Convención de riesgo.** *Conflicto lógico*: la ruta puede volver inconsistente el sistema de axiomas. *Conflicto de sentido*: es consistente pero deja la teoría vacía o distinta de lo que se quería. *Coste*: solo esfuerzo o cascada de cambios.

| Ruta | Opciones | Riesgo principal | Señal temprana (sonda) |
|---|---|---|---|
| **R1. `rational_to_diagram` de `Bridge`** | (a) dejar el axioma; (b) darlo en la capa paralela (`Diag`); (c) cambiar `Diagram` de `Reidemeister` a `GDiag` | (c) **conflicto lógico y de sentido alto**: `Knot` pasaría a ser el cociente de nudos virtuales y los axiomas de suma conexa y factorización única podrían dejar de valer; el modelo de consistencia (`Knot` = multiconjuntos) dejaría de aplicarse. (a) y (b): ninguno | Para (c): intentar probar `connected_sum_comm` en el cociente concreto; si no hay forma de plantear el modelo, no seguir |
| **R2. De `jones2` axiomático a un `Knot` clásico** (Opción 2) | mapas planares + movimientos clásicos + suma conexa bien definida | No hay contradicción matemática (la teoría clásica cumple los axiomas); el riesgo es de coste. Si sale, los 4 axiomas de `jones2` pasan a teoremas | Probar primero que R1-R3 clásicos conservan la paridad de Gauss (decidible en n pequeño) |
| **R3. Migrar `Basic` y `TCN` al signo como dato** | (a) in situ; (b) solo `TCN` (K3); (c) dejar la capa aditiva `Modular_Signo` | Coste en cascada (conteos: 120 configuraciones pasan a 960, cambian teoremas de `TCN_05` a `TCN_08`, `Basic.Isotopic`, `CrossingPairIsomorphism`). Riesgo lógico bajo | Contar con `grep` cuántos teoremas y módulos dependen de las definiciones que cambian |
| **R4. Clase B de `Schubert`** (7 `sorry`) | (i) reformular los enunciados falsos; (ii) dejarlos; (iii) axiomatizar los verdaderos y profundos con cita | (iii) puede introducir inconsistencia con el modelo (p. ej. axiomas sobre `bridge_number` o `knot_genus`, que en el modelo son constantes) | Extender el modelo de consistencia con el axioma propuesto **antes** de añadirlo (así se hizo con `jones2`) |
| **R5. `sorryAx` de `apply_R*`** | (a) dejarlo; (b) rellenar con las definiciones del modelo; (c) resolverlo con R2 | (b) **conflicto de sentido**: quita el `sorryAx`, pero `Knot` pasa a ser `Multiset ℚ` sin ceros y `trefoil_is_prime` etc. serían teoremas sobre objetos de juguete. (a): los teoremas de `Knot` heredan `sorryAx` (hoy solo vía `apply_R*`, verificado) | Rastreo de dependencias (ya hecho: solo `apply_R1/2/3`) |
| **R6. Estructura** | orden de fusión de ramas; ampliar `TMENudos.lean`; cuál de `KN_*` y `TCN_*` es canónico; renombrar la σ de `KN_02` | Coste; riesgo lógico nulo | — |

**Lectura del semáforo.** Lo de más riesgo es todo lo que mezcle el cociente virtual con los axiomas de suma conexa de `Schubert` (R1c) y lo que vacía la teoría (R5b). Lo de mayor valor a largo plazo es R2. Lo más barato y seguro: R4(i), R1(b) y R6.

**Sondas que ya se usaron en este trabajo, y qué ve y qué no ve cada una:**
| Sonda | Ejemplo aquí | Ve | Es ciega a |
|---|---|---|---|
| Intentar derivar `False` | `R1_inverse` (n = 0 y n = 1) | contradicciones por casos extremos, cardinalidad, resta natural | contradicciones que no aparezcan en casos pequeños |
| Modelo de consistencia | 38 axiomas (11 + 25 + 2) | contradicción lógica entre axiomas | que el modelo sea trivial o de juguete (aquí lo es: `Knot` = multiconjuntos) |
| Cálculo sobre testigos concretos | Jones de K3, paridad de Gauss, quandles | errores de modelado (pérdida de quiralidad, órbita no planar) | lo que el invariante elegido no distingue |
| Rastreo de dependencias | `sorryAx` solo vía `apply_R*` | axiomas o `sorry` inesperados en una cadena | — |
| Doble formulación independiente | prueba numérica de R3 frente a la geometría | definiciones mal copiadas o mal orientadas | errores compartidos por ambas |
| Enunciado sobre caso pequeño antes de demostrar | `gap_mirror` (n = 2) | enunciados falsos | — |

**Sonda de hoy (`Tests/auditoria_20260929/13_sonda_suma_conexa_virtual.lean`) y su lección.** Se insertó un trébol en todas las posiciones y puntos de partida de un diagrama no planar (y de uno planar, como control): el Jones da el mismo valor siempre (324769/67108864 = 79/1024 · 4111/65536). **Esto NO refuta ni confirma que la suma conexa virtual dependa del pegado**: el corchete es multiplicativo para cualquier pegado, así que el Jones es incapaz de verlo. Un resultado nulo con una sonda insensible no prueba nada; para ver esa dependencia haría falta un invariante más fino (de la teoría de nudos virtuales) o comparar clases con una relación más fuerte. El riesgo sigue apoyándose solo en la literatura.

**Lista de comprobación antes de decidir una ruta:** (1) ¿qué axiomas y definiciones toca? (2) ¿se puede extender el modelo de consistencia con el cambio? (3) ¿hay un contraejemplo pequeño por fuerza bruta? (4) ¿qué depende de lo que cambia (`grep`, conteos)? (5) ¿la sonda que voy a usar es sensible a lo que temo?

## 6. Lecciones para la próxima sesión

1. **Compilar siempre con las opciones del lakefile** (`lake build`, o `-Dweak.linter.mathlibStandardSet=true`); `lake env lean` a secas oculta las alertas de estilo.
2. **Verificar una corrección de axiomas intentando derivar `False`.** El primer intento (`1 ≤ n`) compilaba pero seguía siendo inconsistente; solo una prueba explícita lo reveló.
3. **Los enunciados con una resta natural son sospechosos** (`n - 1` con `n = 0`); afecta tipos indexados como `KnotConfig (n - 1)`.
4. **Un `sorry` en el cuerpo de una definición es más grave que uno en un teorema:** contamina todo lo que se construye encima (aquí, `Knot`).
5. **Las cifras de los informes de los agentes hay que verificarlas con una compilación propia**, sobre todo los conteos y las afirmaciones de "no queda ningún `sorry`".
6. **Cuidado con las notaciones de precedencia baja:** `g • K = R` se leía como `g • (K = R)` y rompió tres módulos.
7. **`mirror` significa cosas distintas en distintos archivos.** Antes de tocar cualquier resultado sobre espejos, clasificar cuál de ρ, σ, τ es.

## 7. Cómo reproducir las pruebas

Todo desde la raíz del proyecto (`TME_Nudos`):

| Qué | Comando |
|---|---|
| Compilación completa (34 módulos) | `lake build TMENudos` y luego los módulos restantes por nombre, por ejemplo `lake build TMENudos.KN_Examples` |
| Experimento de `IME2` (n=3 y n=4) | `lake env lean Procesos/Tests/auditoria_20260929/03_experimento_IME2_n3_n4.lean` |
| `mirrorTrefoil = swap trefoilKnot` | `lake env lean Procesos/Tests/auditoria_20260929/04_mirrorTrefoil_es_swap_trefoilKnot.lean` |
| Rastreo de `sorry` en los teoremas cerrados de `Schubert` | `lake env lean Procesos/Tests/auditoria_20260929/05_rastreo_de_sorry_en_teoremas_cerrados.lean` |
| Modelo de consistencia de los 34 axiomas | `lake env lean Procesos/Tests/auditoria_20260929/06_modelo_de_consistencia.lean` (unos 21 s); `06e_tipos_originales.lean` vuelca los tipos de los originales para compararlos |
| Búsqueda de quandles que distingan el trébol de su espejo | `python Procesos/Tests/auditoria_20260929/07_quandles_trebol_vs_espejo.py 6` (unos 30 s) |
| Spike M1 (corchete de Kauffman y Jones sobre palabras de Gauss) | rama `etapa1-spike-gauss`: `lake env lean TMENudos/Etapa1_GaussWord.lean` (unos 18 s) |
| Pruebas históricas de inconsistencia | `01_...` y `02_...` **ya no compilan**; es lo esperado y prueba que la contradicción quedó bloqueada. Sirven de documentación del razonamiento. |

Para volver a ver el estado: `git log --oneline master..auditoria-2026-09-29` lista los commits de esta sesión, y `git diff master --stat` el alcance total.

### 5.5 Correcciones hechas al revisar estos tres documentos
Revisión posterior, contrastando los documentos con el repositorio:
- El número de módulos que compilaban al empezar (26) estaba sobrestimado: 8 fallaban y otros 8 dependían de ellos y no llegaron a compilarse.
- El conteo de axiomas "49 al empezar" era en realidad el de después de la auditoría inicial.
- La sección 3.4 del reporte seguía listando como pendientes `configsNoR1NoR2` y `card_k3_config`, ya resueltos en la etapa 0.
- La sección 4 del reporte decía que los axiomas de `Reidemeister` y `Schubert` seguían siendo 33; ahora son 32 (11 + 21).
- El `sorry` que aparece en `KN_04_Clasificacion_General.lean` (línea ~237) está dentro de un bloque de comentario; no cuenta.
- "`Basic` (`Isotopic`) = rotaciones" era impreciso: incluye también los movimientos R1-R3.
- Faltaba aclarar que el `IME` de `Basic` (lista) y el de `KN_03` (entero) son objetos distintos.
