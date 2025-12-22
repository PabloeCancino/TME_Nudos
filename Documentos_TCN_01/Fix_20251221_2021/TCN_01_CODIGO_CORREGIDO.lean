-- ============================================================================
-- CÓDIGO CORREGIDO PARA TCN_01_Fundamentos.lean
-- INSERTAR DESPUÉS DE LA LÍNEA 314
-- ============================================================================

/-- Función de signo para enteros.
    
    **Definición:**
    ```
    sign(x) = { +1  si x > 0
              {  0  si x = 0  
              { -1  si x < 0
    ```
    
    Esta función es necesaria porque `Int.sign` no está disponible
    o no funciona correctamente en Mathlib para Lean 4.26.0.
-/
def intSign (x : ℤ) : ℤ :=
  if x > 0 then 1 else if x < 0 then -1 else 0

/-- El signo de -x es el opuesto del signo de x -/
lemma intSign_neg (x : ℤ) : intSign (-x) = -intSign x := by
  unfold intSign
  split_ifs <;> omega

/-- El signo de x*(-1) es el signo de x multiplicado por -1 -/
lemma intSign_mul_neg_one (x : ℤ) : intSign (x * (-1)) = intSign x * (-1) := by
  unfold intSign
  split_ifs <;> omega

-- ============================================================================
-- CAMBIO EN LÍNEA 316
-- ============================================================================

-- ANTES (LÍNEA 316):
-- noncomputable def chiralSigns (K : K3Config) : List ℤ :=
--   K.dme.map Int.sign

-- DESPUÉS (LÍNEA 316):
noncomputable def chiralSigns (K : K3Config) : List ℤ :=
  K.dme.map intSign

-- ============================================================================
-- CAMBIO EN LÍNEAS 943-953 (dentro de writhe_mirror)
-- ============================================================================

-- ANTES (LÍNEAS 943-953):
--   have : (K.dme.map (· * (-1))).map (fun x => if x > 0 then 1 else if x < 0 then -1 else 0) =
--          (K.dme.map (fun x => if x > 0 then 1 else if x < 0 then -1 else 0)).map (· * (-1)) := by
--     apply List.ext_get
--     · simp [List.length_map]
--     intro i h1 h2
--     simp only [List.get_map]
--     have : K.dme[i] = K.dme[i] := rfl
--     cases hd : K.dme[i] <;> simp
--     split_ifs with h3 h4 h5 h6 <;> omega
--   rw [this]
--   exact sum_neg (K.dme.map fun x => if x > 0 then 1 else if x < 0 then -1 else 0)

-- DESPUÉS (LÍNEAS 943-953):
  have : (K.dme.map (· * (-1))).map intSign =
         (K.dme.map intSign).map (· * (-1)) := by
    apply List.ext_get
    · simp [List.length_map]
    intro i h1 h2
    simp only [List.get_map]
    exact intSign_mul_neg_one (K.dme[i])
  rw [this]
  exact sum_neg (K.dme.map intSign)

-- ============================================================================
-- FIN DEL CÓDIGO CORREGIDO
-- ============================================================================

/-!
## Instrucciones de Aplicación

1. **Abrir** TCN_01_Fundamentos.lean

2. **Insertar** después de la línea 314 (antes de `noncomputable def chiralSigns`):
   - def intSign
   - lemma intSign_neg
   - lemma intSign_mul_neg_one

3. **Reemplazar** línea 316:
   - Cambiar `K.dme.map Int.sign` → `K.dme.map intSign`

4. **Reemplazar** líneas 943-953 en el teorema `writhe_mirror`:
   - Usar la versión simplificada con `intSign`

5. **Guardar** y compilar:
   ```bash
   lake build TMENudos.TCN_01_Fundamentos
   ```

## Verificación

Si todo está correcto, verás:
```
✓ [nn/nn] Building TMENudos.TCN_01_Fundamentos
```

Sin errores en línea 993 o alrededores.

-/
