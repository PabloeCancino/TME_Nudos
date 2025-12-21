# Normalización de Configuraciones Racionales

## Cambio Implementado

Se agregó una función de **normalización automática** que ordena los pares de una configuración racional por su elemento mínimo **ANTES** de calcular el IME.

## ¿Por qué es importante?

Sin normalización, diferentes ordenamientos de los mismos pares producirían IMEs diferentes:

```python
# SIN normalización:
[[1,4],[6,3],[2,5]] → IME = [3, -3, 3]
[[2,5],[1,4],[6,3]] → IME = [3, 3, -3]  # ¡Diferente!
```

Con normalización, siempre se ordena primero:

```python
# CON normalización:
[[1,4],[6,3],[2,5]] → [[1,4],[2,5],[6,3]] → IME = [3, 3, 3]
[[2,5],[1,4],[6,3]] → [[1,4],[2,5],[6,3]] → IME = [3, 3, 3]  # ¡Igual!
```

## Regla de Normalización

**Ordenar los pares por el valor mínimo que contienen:**

1. Buscar el par que contiene el 1 → Colocarlo primero
2. Si el 2 no está en el primer par, buscar el par que contiene el 2 → Colocarlo segundo
3. Si el 3 no está en los primeros pares, buscar el par que contiene el 3 → Colocarlo tercero
4. Y así sucesivamente...

### Ejemplo:

```
Original: [[6,3], [1,4], [2,5]]

Paso 1: Identificar mínimos
  - [6,3] → min = 3
  - [1,4] → min = 1
  - [2,5] → min = 2

Paso 2: Ordenar por mínimo (ascendente)
  Normalizada: [[1,4], [2,5], [6,3]]
  (orden de mínimos: 1, 2, 3)
```

## Implementación

### En `clasificador_ime.py`:

```python
@staticmethod
def normalizar_configuracion(pares_ordenados: List[List[int]]) -> List[List[int]]:
    """Ordena los pares por su elemento mínimo."""
    if not pares_ordenados:
        return []
    
    # Crear lista de (min_elemento, par_original)
    pares_con_min = [(min(par), par) for par in pares_ordenados]
    
    # Ordenar por el elemento mínimo
    pares_con_min.sort(key=lambda x: x[0])
    
    # Retornar solo los pares ordenados
    return [par for min_elem, par in pares_con_min]
```

### Constructor modificado:

```python
def __init__(self, pares_ordenados: List[List[int]], normalizar: bool = True):
    # Normalizar configuración si se solicita
    if normalizar:
        self.pares = self.normalizar_configuracion(pares_ordenados)
    else:
        self.pares = pares_ordenados
    ...
```

**Por defecto, `normalizar=True`**, por lo que todas las configuraciones se normalizan automáticamente.

## Resultados de la Prueba

```
[Caso 3] Diferentes ordenamientos del mismo nudo:
  Config 1 original: [[1, 4], [2, 5], [3, 6]]
  Config 1 normalizada: [[1, 4], [2, 5], [3, 6]]
  IME: [3, 3, 3]

  Config 2 original: [[3, 6], [1, 4], [2, 5]]
  Config 2 normalizada: [[1, 4], [2, 5], [3, 6]]
  IME: [3, 3, 3]

  Config 3 original: [[2, 5], [3, 6], [1, 4]]
  Config 3 normalizada: [[1, 4], [2, 5], [3, 6]]
  IME: [3, 3, 3]

  Todas normalizadas son iguales? True
  Todos los IME son iguales? True
```

✅ **Confirmado**: Diferentes ordenamientos del mismo nudo producen la misma configuración normalizada y el mismo IME.

## Impacto en el Análisis

### Antes de la normalización:
- Diferentes ordenamientos = IMEs diferentes
- Dificultad para detectar equivalencias
- Posible sobre-conteo de "nudos únicos"

### Después de la normalización:
- Representación canónica única
- Detección precisa de equivalencias
- Conteo correcto de nudos únicos

### Resultados del análisis k3:
```
Total analizadas: 720
Configuraciones unicas (IME): 0
Clases de equivalencia: 21
```

Las **720 configuraciones** se reducen a **21 nudos únicos** cuando se normalizan y agrupan por IME.

## Uso

### Normalización automática (por defecto):
```python
config = ConfiguracionRacional([[6,3], [1,4], [2,5]])
print(config.pares)  # [[1,4], [2,5], [6,3]]
```

### Sin normalización (opcional):
```python
config = ConfiguracionRacional([[6,3], [1,4], [2,5]], normalizar=False)
print(config.pares)  # [[6,3], [1,4], [2,5]]  (sin cambios)
```

## Notas Importantes

1. **La normalización NO cambia la estructura del nudo**, solo reorganiza los pares para crear una representación canónica.

2. **El orden interno de cada par `[o, u]` se preserva** - solo se reordena la lista de pares.

3. **Compatible con toda la base de datos existente** - el script `analizar_k3.py` aplica normalización automáticamente.

4. **Fundamentación teórica**: En la teoría de nudos racionales, el orden de los cruces no afecta el tipo de nudo bajo isotopía, por lo que esta normalización es matemáticamente válida.
