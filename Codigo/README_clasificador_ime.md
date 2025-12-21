# Sistema de Clasificación de Nudos mediante IME

Sistema Python para clasificar e identificar nudos racionales utilizando el **Invariante Modular Estructural (IME)**.

## 📚 Fundamentos Teóricos

El IME está basado en la formalización matemática en `TMENudos/Basic.lean` (líneas 274-285):

```lean
def IME {n : ℕ} (K : RationalConfiguration n) : List ℕ :=
  (List.range n).map (fun i =>
    if h : i < n then
      ratio_val (K.crossings ⟨i, h⟩)
    else
      0)
```

Donde `ratio_val(ci) = (ui - oi) mod 2n` es la **razón modular** del cruce `i`.

### Teorema de Completitud del IME

**Teorema** (Basic.lean): Dos nudos racionales irreducibles son isotópicos si y solo si tienen el mismo IME (salvo rotación cíclica).

Esto significa que el IME es un **invariante completo** para nudos racionales irreducibles.

## 🚀 Instalación

```bash
cd c:\Users\pablo\OneDrive\Documentos\TME_Nudos\Codigo
# No requiere instalación adicional, usa bibliotecas estándar de Python
```

## 📖 Uso Básico

### 1. Calcular el IME de una configuración

```python
from clasificador_ime import calcular_ime

# Nudo trébol: [[o1,u1], [o2,u2], [o3,u3]]
trebol = [[1, 4], [2, 5], [3, 6]]

ime = calcular_ime(trebol)
print(f"IME del trébol: {ime}")
# Salida: IME del trébol: [3, 3, 3]
```

### 2. Detectar equivalencia entre nudos

```python
from clasificador_ime import son_equivalentes

trebol_1 = [[1, 4], [2, 5], [3, 6]]
trebol_rotado = [[3, 6], [4, 1], [5, 2]]

if son_equivalentes(trebol_1, trebol_rotado):
    print("¡Son el mismo nudo!")
```

### 3. Clasificación completa

```python
from clasificador_ime import ClasificadorIME

# Cargar base de datos
clasificador = ClasificadorIME("configuraciones_nudos.json")

# Clasificar un nudo
config = [[1, 6], [2, 7], [3, 8], [4, 5]]
resultado = clasificador.clasificar(config)

print(f"IME: {resultado.ime}")
print(f"Familia: {resultado.familia}")
print(f"¿Es reducible?: {resultado.es_reducible}")
print(f"Equivalentes encontrados: {len(resultado.equivalentes_encontrados)}")
```

### 4. Buscar similares

```python
# El resultado incluye los 5 nudos más similares
for similar in resultado.similares:
    print(f"ID: {similar['id']}, Score: {similar['score_similitud']:.2f}")
```

## 🔧 API Reference

### `ConfiguracionRacional`

Representa una configuración racional de nudos.

```python
config = ConfiguracionRacional([[1,4], [2,5], [3,6]])

# Métodos principales:
ime = config.calcular_ime()              # Lista de razones modulares
ime_norm = config.calcular_ime_normalizado()  # Forma canónica
reducible = config.es_reducible()        # True si es simplificable
familia = config.get_familia()           # Nombre de la familia
```

### `ClasificadorIME`

Clasificador principal con base de datos.

```python
clasificador = ClasificadorIME("base_datos.json")

# Métodos:
resultado = clasificador.clasificar(pares_ordenados)
resultado = clasificador.clasificar_desde_json(config_dict)
familias = clasificador.agrupar_por_familias(lista_configs)
```

### `ResultadoClasificacion`

Resultado de la clasificación (dataclass).

**Atributos:**
- `ime`: Lista de razones modulares
- `ime_normalizado`: Forma canónica (min rotación lexicográfica)
- `n_cruces`: Número de cruces
- `es_reducible`: Boolean
- `familia`: Nombre de la familia
- `configuracion_original`: Pares ordenados originales
- `equivalentes_encontrados`: Lista de nudos equivalentes
- `similares`: Lista de nudos similares con scores

## 📊 Formato de Entrada

### Pares Ordenados

```python
configuracion = [[o1, u1], [o2, u2], ..., [on, un]]
```

Donde `{o1,...,on, u1,...,un} = {1,2,...,2n}` (cobertura del espacio).

### Desde JSON

```json
{
  "id": 1,
  "num_cruces": 3,
  "configuracion_Racional": "[[1,4],[2,5],[3,6]]"
}
```

## 🧪 Ejemplos

Ver `ejemplo_clasificacion_ime.py` para ejemplos completos:

```bash
python ejemplo_clasificacion_ime.py
```

Incluye:
1. Cálculo básico del IME
2. Detección de equivalencia
3. Clasificación completa con similitud
4. Detección de reducibilidad (R1, R2)
5. Agrupación por familias
6. Procesamiento de JSON masivo

## 📐 Características del Sistema

### Equivalencia Exacta
Detecta cuando dos configuraciones representan el mismo nudo:
- Compara IME normalizado (forma canónica)
- Invariante bajo rotaciones cíclicas

### Similitud Estructural
Score compuesto (0.0 - 1.0):
- **40%**: Similitud en número de cruces
- **60%**: Distancia entre distribuciones de razones modulares

### Clasificación por Familias
- `Unknot`: Nudo trivial (0 cruces)
- `Uniforme-n`: Todas las razones iguales
- `Monotona-Creciente-n`: Razones en orden creciente
- `Monotona-Decreciente-n`: Razones en orden decreciente
- `Reducible-n`: Tiene bucles R1 o bigones R2
- `General-n`: Familia general

### Detección de Reducibilidad

**R1 (Bucles)**: Detecta cruces con `|o - u| = 1`

**R2 (Bigones)**: Detecta pares de cruces adyacentes e interlazados

## ⚠️ Limitaciones

1. **Nudos Irreducibles**: El IME es un invariante completo **solo para nudos irreducibles**. Los nudos reducibles pueden tener el mismo IME que otros nudos tras simplificación.

2. **Solo Nudos Racionales**: Este sistema clasifica nudos racionales (2-bridge knots). No aplica a nudos generales.

3. **Equivalencia Modulo Rotación**: Dos configuraciones que difieren solo por rotación tienen el mismo IME normalizado pero IMEs "crudos" diferentes.

## 📚 Referencias Teóricas

- **Formalización Lean**: `TMENudos/Basic.lean`
- **Axiomas Fundamentales**: Líneas 1-89 (Espacios modulares)
- **Definición IME**: Líneas 274-285
- **Teorema de Completitud**: Líneas 776-781
- **Movimientos Reidemeister**: Líneas 625-684

## 🔬 Validación

El sistema ha sido validado contra:
- Teoría formalizada en Lean 4
- Propiedades algebraicas del espacio modular ℤ/(2n)ℤ
- Invarianza bajo operaciones de grupo (rotaciones)

## 📞 Soporte

Para dudas sobre la teoría matemática, consultar:
- `TMENudos/Basic.lean` (formalización completa)
- `theory_mindmap.md` (mapa conceptual)
- Documentos en `Documentos/` (teoremas de Schubert, Reidemeister, etc.)
