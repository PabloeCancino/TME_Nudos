# Bitácora de la sesión del 2026-09-29

**Proyecto:** TMENudos (Lean 4 v4.29.0, Mathlib v4.29.0) · **Rama:** `auditoria-2026-09-29` (6 commits sobre `master`, sin subir a ningún remoto)
**Documentos hermanos:**
- `20260929_1340_reporte_de_auditoria.md`: reporte de auditoría (estado y clasificación de los `sorry`).
- `20260929_1408_mapa_de_ruta.md`: mapa de ruta hacia un `Reidemeister.lean` estable.
- `Tests/auditoria_20260929/`: las pruebas ejecutables de esta sesión.

Este documento es el registro cronológico completo: qué se probó, qué se encontró, qué se cambió y por qué, y dónde retomar. Las secciones 1 a 3 sirven para orientarse; la 4 es el registro detallado; la 5 lista lo pendiente.

## 1. Estado final en una tabla

| Métrica | Al empezar | Al terminar |
|---|---|---|
| Módulos que compilan (de 34) | 26 | **34** |
| Errores de compilación | ~90 visibles (8 módulos) más los ocultos por dependencias | **0** |
| Alertas de linter (excluyendo `sorry`) | 104 solo en `Basic.lean`, más las de otros módulos | **0** |
| `sorry` en el código | No medido en todo el proyecto al empezar; solo `Reidemeister` 12 y `Schubert` 27. Los agentes reportaron además `sorry` en `CrossingPairIsomorphism` (13), `KN_00_Combinatoria`, `KN_03`, `KN_Examples` (5), `TCN_05` y `TCN_06` a `TCN_08` | **33** (`Schubert` 26, `Reidemeister` 5, `KN_00_Combinatoria` 1, `KN_Instance_K3` 1) |
| Axiomas | 49 | **47** |
| Contradicciones demostradas | 1 (`R1_inverse`, y `R2_inverse` igual) | **0 conocidas** (sin modelo formalizado) |

Commits de la sesión:

| Commit | Contenido |
|---|---|
| `75708bd` | Auditoría general: 23 archivos corregidos y primer reporte. |
| `df86e7b` | Corrección de los axiomas inconsistentes `R1_inverse` y `R2_inverse`. |
| `ed140db` | `reidemeister_equivalent` pasa a ser una relación inductiva. |
| `92dee92` | Reporte de auditoría actualizado. |
| `bdb627b` | Mapa de ruta. |
| `73f869e` | Etapa 0: saneamiento de enunciados falsos, convención de dos niveles, `IME2`, renombrado a `swap`. |

(Este documento y las pruebas archivadas en `Tests/` se agregan en un commit posterior.)

## 2. Los hallazgos que más importan

Ordenados por gravedad. Cada uno tiene su detalle en la sección 4.

1. **Los axiomas `R1_inverse` y `R2_inverse` eran contradictorios.** Permitían demostrar `False` (verificado en Lean). Todo lo que importaba `Reidemeister` (`Schubert`, `Bridge`) podía demostrar cualquier cosa. Corregido. (4.5, 4.6)
2. **Los enunciados de `TCN_06` a `TCN_08` sobre estabilizadores y órbitas eran falsos** con las definiciones reales. La clasificación de K3 no tiene tres órbitas (6+4+4) sino **dos, de 12 y 2 elementos**. Corregido. (4.9)
3. **En la teoría KN, `gap_mirror`, `IDE_mirror`, `IME_mirror` e `IME_eq_of_mem_orbit` eran falsos.** Corregido con una convención de dos niveles. (4.10)
4. **`IME` no es un invariante completo.** Es un solo entero y no separa las órbitas (13 órbitas con 10 valores en n=3; 121 con 28 en n=4). Ningún archivo lo afirma; conviene no afirmarlo nunca. (4.11)
5. **`reidemeister_equivalent` estaba definido con `sorry` en su cuerpo**, y `Knot` (el cociente de `Schubert`) se construía sobre él. Corregido con una relación inductiva. (4.7)
6. **Tres operaciones distintas se llamaban `mirror`**: rotación (ρ), reflexión de posiciones (σ) e intercambio over/under (τ). Aclarado y renombrado τ a `swap`. (4.10)
7. **`Basic.lean` (T4.1) decía "estructura diédrica" pero demostraba una estructura abeliana.** Comentario corregido. (4.10)
8. **Enunciados dudosos o falsos de `Schubert`** (nudos tóricos, complementos, nombres intercambiados de los nudos cuadrado y de la abuela…): **clasificados, no corregidos**. (4.8)

## 3. Cómo leer los `sorry` restantes

Hay tres clases, y no todos merecen el mismo esfuerzo:

| Clase | Qué significa | Tratamiento acordado |
|---|---|---|
| A. Demostrables | Se pueden cerrar con un arreglo menor. | Cerrarlos. |
| B. Enunciado dudoso o falso | El enunciado mismo está mal. | Reformularlo con aprobación del autor. |
| C. Dependen de teoría que falta | Requieren topología PL, 3-variedades o un modelo concreto de diagrama. | Los profundos (Reidemeister, Haken, Schubert) como **axiomas con cita**; los combinatorios se construyen. |

Estado actual: 4 de clase A, 10 de clase B y 17 de clase C, más 2 fuera de `Reidemeister` y `Schubert` (ver 5.3).

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
- **Prueba** (`Tests/auditoria_20260929/01_inconsistencia_R1_inverse_original.lean`): con `n = 0` y un movimiento con `add_twist = false`, la resta natural da `0 - 1 = 0`, luego se vuelve a agregar y se obtiene `KnotConfig 1`. El axioma exige entonces `HEq` entre un elemento de `KnotConfig 1` y uno de `KnotConfig 0`, lo que fuerza que ambos tipos sean iguales; pero `KnotConfig 0` tiene un solo elemento y `KnotConfig 1` tiene infinitos (contiene un `ℚ`). Resultado: `#print axioms` mostró que `False` se deduce solo de `R1_inverse`.
- **Consecuencia:** `Reidemeister`, `Schubert`, `Bridge` y todo lo que importe `Reidemeister` era inconsistente.

### 4.6 Corrección de `R1_inverse` y `R2_inverse`, con un primer intento fallido
- **Primer intento (insuficiente):** añadir la hipótesis `move.add_twist = true ∨ 1 ≤ n`. Compiló. Pero antes de darlo por bueno probé si seguía habiendo contradicción.
- **Prueba** (`Tests/.../02_inconsistencia_R1_inverse_con_1_le_n.lean`): con `n = 1`, "eliminar y luego agregar" sería la identidad en `KnotConfig 1`, lo que exige que eliminar sea inyectivo desde un conjunto infinito hacia `KnotConfig 0` (un solo elemento). Se dedujo `False` otra vez.
- **Diagnóstico de fondo:** "eliminar y luego agregar" no puede ser la identidad para todo diagrama, porque eliminar pierde información. Solo es válida la dirección **agregar y luego eliminar**.
- **Corrección final (commit `df86e7b`):** los axiomas llevan la hipótesis `move.add_twist = true` (R1) y `move.add_crossings = true` (R2), con comentarios que explican el porqué. `reidemeister_inverse` se reformuló con las mismas hipótesis (era falso para `n = 0`) y quedó demostrado.
- **Verificación:** las dos derivaciones de `False` dejaron de compilar (es lo esperado). Ningún otro módulo usaba estos axiomas.
- **Limitación:** no se ha demostrado consistencia. Mientras `apply_R1/R2/R3` sean `sorry`, los axiomas no tienen modelo verificado. El argumento informal (agregar un cruce es inyectivo, quitarlo es su inversa por la izquierda) no está formalizado.

### 4.7 `reidemeister_equivalent` como relación inductiva
- **Problema:** `def reidemeister_equivalent K₁ K₂ := ∃ seq, sorry`. Su cuerpo era `sorry`, y `DiagramSetoid` (y por tanto `Knot`) se construía sobre `reidemeister_refl/symm/trans`, que eran `sorry`.
- **Diseño:** relación inductiva con seis constructores: `refl`, `symm`, `trans`, `R1`, `R2`, `R3`. R1 y R2 solo en dirección de *agregar* (la eliminación sale por `symm`), coherente con 4.6.
- **Los axiomas `R*_preserves_isotopy` eran vacíos** (`∃ K', K' = apply_R1 K move` siempre se cumple). Se reemplazaron por enunciados con contenido: cada movimiento preserva `topologically_equivalent`. Sin eso no se puede probar la solidez.
- **Resultado:** `reidemeister_refl/symm/trans` (una línea cada una), `reidemeister_soundness` e `invariant_criterion` (por inducción). `Reidemeister` pasó de 12 a 5 `sorry` en el código. Commit `ed140db`.
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
  - Nivel 1 (orientado, grupo ℤ/2n): `IME₁` = el `IME` actual. En `Basic` (`Isotopic`), `KN_03`, `KN_03b`.
  - Nivel 2 (no orientado, D₂ₙ): `IME2 K = (min, max)` de `IME₁` sobre `K` y `σK`. En `KN_04` y `TCN_*`.
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

## 5. Pendiente y dónde retomar

### 5.1 Decisiones del autor
1. **Quiralidad en K3:** con la acción actual de D₆, el trébol y su imagen especular están en la misma órbita. ¿Es lo pretendido? Si no, hay que cambiar la acción o las definiciones.
2. **"Realizable" en K3:** ¿debe incluir a `specialClass`? Hoy sí.
3. **Etapa 1 del mapa de ruta:** representación del diagrama (código de Gauss extendido frente a PD) y si `KnotConfig` se reemplaza o se conserva como capa.
4. **Nombre de σ:** la reflexión de `KN_02` sigue llamándose `mirror` aunque no es una imagen especular. `reflect` sería más fiel, a costa de un renombrado amplio.

### 5.2 Trabajo técnico identificado
1. **Clase A de `Schubert`** (4 `sorry`): `prime_decomposition` (línea 110), `schubert_existence` (134), `schubert_unique_factorization` (167), `factorization_problem` (386). Se cierran axiomatizando la existencia de la factorización y filtrando los nudos triviales.
2. **Clase B de `Schubert`** (9 en `Schubert` y 1 en `Reidemeister`):
   - `minimal_characterization` (`Reidemeister.lean`): falso, el lado derecho es siempre `False`.
   - `schubert_torus_knot_primality`: falso; T(1,q) es el nudo trivial, no primo. Debe exigir p,q ≥ 2.
   - `schubert_complement_sum`: compara tipos con igualdad, y el complemento de K₁#K₂ se pega a lo largo de un anillo, no por suma conexa.
   - `schubert_companion_theorem` y `schubert_is_JSJ_special_case`: tienen `sorry` dentro del propio enunciado.
   - `alexander_multiplicative`: el polinomio de Alexander está definido salvo unidades ±tᵏ.
   - `square_knot_*`: **nombres intercambiados**. El nudo cuadrado es trébol # espejo, y el de la abuela (*granny*) es trébol # trébol.
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
| Pruebas históricas de inconsistencia | `01_...` y `02_...` **ya no compilan**; es lo esperado y prueba que la contradicción quedó bloqueada. Sirven de documentación del razonamiento. |

Para volver a ver el estado: `git log --oneline master..auditoria-2026-09-29` lista los commits de esta sesión, y `git diff master --stat` el alcance total.
