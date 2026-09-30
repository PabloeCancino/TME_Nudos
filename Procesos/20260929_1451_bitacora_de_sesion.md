# Bitácora de la sesión del 2026-09-29

**Proyecto:** TMENudos (Lean 4 v4.29.0, Mathlib v4.29.0) · **Rama:** `auditoria-2026-09-29` (7 commits sobre `master` al escribir la bitácora, más el de su revisión; sin subir a ningún remoto)
**Documentos hermanos:**
- `20260929_1340_reporte_de_auditoria.md`: reporte de auditoría (estado y clasificación de los `sorry`).
- `20260929_1408_mapa_de_ruta.md`: mapa de ruta hacia un `Reidemeister.lean` estable.
- `Tests/auditoria_20260929/`: las pruebas ejecutables de esta sesión.

Este documento es el registro cronológico completo: qué se probó, qué se encontró, qué se cambió y por qué, y dónde retomar. Las secciones 1 a 3 sirven para orientarse; la 4 es el registro detallado; la 5 lista lo pendiente.

## 1. Estado final en una tabla

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

## 5. Pendiente y dónde retomar

### 5.1 Decisiones del autor
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
