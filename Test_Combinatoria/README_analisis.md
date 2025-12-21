# Guía de Uso - Análisis de Configuraciones K3

## Archivos en este directorio

- `clasificador_ime.py` - Motor de clasificación IME
- `configuraciones_nudos_k3.json` - Base de datos de configuraciones a analizar
- `analizar_k3.py` - **Script principal de análisis**
- `resultados_clasificacion_k3.json` - Resultados del análisis (generado automáticamente)

## Uso Básico

### 1. Analizar toda la base de datos

```bash
cd "C:\Users\pablo\OneDrive\Documentos\TME_Nudos\Test_Combinatoria"
python analizar_k3.py
```

Esto procesará **todas** las configuraciones en `configuraciones_nudos_k3.json` y generará:
- Archivo de resultados: `resultados_clasificacion_k3.json`
- Reporte en consola con estadísticas
- Ejemplos de nudos equivalentes

### 2. Analizar una configuración específica

```bash
python analizar_k3.py 42
```

Esto mostrará el análisis detallado solo de la configuración con ID 42:
- IME y IME normalizado
- Si es reducible
- Familia a la que pertenece
- Nudos equivalentes encontrados
- Nudos similares con scores

## Salida del Análisis Completo

El script genera:

### Consola:
```
======================================================================
ANALISIS DE CONFIGURACIONES K3 - Sistema IME
======================================================================

[1/4] Cargando configuraciones...
  Total de configuraciones: 746

[2/4] Inicializando clasificador...
[OK] Base de datos cargada: 746 configuraciones

[3/4] Analizando configuraciones...
  Procesadas: 100/746
  Procesadas: 200/746
  ...
  [OK] Procesadas: 746/746 configuraciones

[4/4] Generando estadisticas...

======================================================================
RESUMEN DE ANALISIS
======================================================================

Total analizadas: 746
Configuraciones unicas (IME): 245
Clases de equivalencia: 120

Distribucion por familias:
  Reducible-3: 450
  General-4: 180
  ...
```

### Archivo JSON (`resultados_clasificacion_k3.json`):

```json
{
  "estadisticas": {
    "total_configuraciones": 746,
    "total_familias": 15,
    "distribucion_familias": { ... },
    "clases_equivalencia": 120,
    "configuraciones_unicas": 245
  },
  "configuraciones": [
    {
      "id": 1,
      "num_cruces": 3,
      "configuracion_original": "[[1,4],[2,5],[3,6]]",
      "ime": [3, 3, 3],
      "ime_normalizado": [3, 3, 3],
      "es_reducible": true,
      "familia": "Reducible-3",
      "num_equivalentes": 5,
      "ids_equivalentes": [1, 23, 45, 67, 89]
    },
    ...
  ]
}
```

## Interpretación de Resultados

### IME (Invariante Modular Estructural)
- Lista de razones modulares `[r1, r2, ..., rn]`
- Caracteriza completamente el nudo

### IME Normalizado
- Forma canónica (rotación lexicográficamente mínima)
- **Importante**: Dos configuraciones con el mismo IME normalizado son el **mismo nudo**

### Clases de Equivalencia
Configuraciones que comparten el mismo IME normalizado representan el mismo nudo bajo isotopía.

Ejemplo:
```
Clase 1: IME = [3, 3, 3]
  IDs equivalentes: [1, 12, 34, 56, 78]
  -> Estos 5 IDs son el mismo nudo (trébol)
```

### Familias
- `Reducible-n`: Puede simplificarse con movimientos de Reidemeister
- `General-n`: Familia general con n cruces
- `Uniforme-n`: Todas las razones modulares son iguales
- `Monotona-Creciente-n`: Razones en orden creciente

## Ejemplos de Uso

### Ejemplo 1: Encontrar todos los nudos equivalentes al trébol

1. Busca el ID del trébol en tu JSON (ej: ID 1)
2. Ejecuta: `python analizar_k3.py 1`
3. Mira la lista de `ids_equivalentes`

### Ejemplo 2: Contar cuántos nudos únicos hay

El valor `configuraciones_unicas` en las estadísticas te dice cuántos nudos diferentes (no equivalentes) existen en tu base de datos.

### Ejemplo 3: Filtrar por familia

Abre `resultados_clasificacion_k3.json` y filtra por el campo `familia`:

```python
import json

with open("resultados_clasificacion_k3.json") as f:
    datos = json.load(f)

# Filtrar solo irreducibles (si los hay)
irreducibles = [c for c in datos["configuraciones"] 
                if not c["es_reducible"]]

print(f"Nudos irreducibles: {len(irreducibles)}")
```

## Notas Importantes

1. **Tiempo de ejecución**: Para 746 configuraciones, el análisis toma ~5-30 segundos
2. **Memoria**: Carga toda la base de datos en RAM (apropiado para datasets de tamaño moderado)
3. **Equivalencias**: El sistema detecta equivalencias bajo rotaciones cíclicas automáticamente

## Solución de Problemas

### No encuentra el archivo
```
[ERROR] No se encuentra el archivo: configuraciones_nudos_k3.json
```
**Solución**: Asegúrate de que `configuraciones_nudos_k3.json` está en el mismo directorio que `analizar_k3.py`

### Error de encoding
Si aparecen caracteres raros en la consola, ejecuta:
```bash
chcp 65001
python analizar_k3.py
```
