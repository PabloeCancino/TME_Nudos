"""
Cálculo de órbitas del grupo dihédrico D₆ sobre las 14 configuraciones triviales
Este script verifica si hay 2 clases de equivalencia como afirma el teorema original
"""

def normalize_config(config):
    """Normaliza una configuración como tupla ordenada de tuplas ordenadas"""
    return tuple(sorted(config))

def rotation(k, i):
    """Rotación r^k: i ↦ i+k mod 6"""
    return (i + k) % 6

def reflection(i):
    """Reflexión s: i ↦ -i mod 6"""
    return (-i) % 6

def apply_rotation_to_tuple(k, tup):
    """Aplica r^k a una tupla [a,b]"""
    a, b = tup
    return (rotation(k, a), rotation(k, b))

def apply_reflection_to_tuple(tup):
    """Aplica s a una tupla [a,b]"""
    a, b = tup
    return (reflection(a), reflection(b))

def apply_dihedral_element(element, config):
    """
    Aplica un elemento de D₆ a una configuración
    element = ('r', k) para rotación r^k
    element = ('s', k) para reflexión sr^k
    """
    result = []
    
    for tup in config:
        if element[0] == 'r':
            # Rotación pura r^k
            new_tup = apply_rotation_to_tuple(element[1], tup)
        else:  # element[0] == 's'
            # Reflexión seguida de rotación: sr^k = s · r^k
            # Primero aplicar r^k, luego s
            temp_tup = apply_rotation_to_tuple(element[1], tup)
            new_tup = apply_reflection_to_tuple(temp_tup)
        
        result.append(new_tup)
    
    return normalize_config(result)

def generate_d6():
    """Genera todos los 12 elementos de D₆"""
    elements = []
    # Rotaciones r^k para k=0,1,2,3,4,5
    for k in range(6):
        elements.append(('r', k))
    # Reflexiones sr^k para k=0,1,2,3,4,5
    for k in range(6):
        elements.append(('s', k))
    return elements

def compute_orbit(config, d6_elements):
    """Calcula la órbita de una configuración bajo D₆"""
    orbit = set()
    for g in d6_elements:
        transformed = apply_dihedral_element(g, config)
        orbit.add(transformed)
    return orbit

def element_to_string(element):
    """Convierte elemento de D₆ a string legible"""
    if element[0] == 'r':
        if element[1] == 0:
            return "e (identidad)"
        return f"r^{element[1]}"
    else:
        if element[1] == 0:
            return "s"
        return f"sr^{element[1]}"

# Las 14 configuraciones triviales
trivial_configs = [
    # De M₁
    ((0,2), (1,4), (3,5)),
    ((0,2), (4,1), (5,3)),
    ((2,0), (1,4), (5,3)),
    ((2,0), (4,1), (3,5)),
    # De M₂
    ((0,3), (4,1), (5,2)),
    ((3,0), (1,4), (2,5)),
    # De M₃
    ((0,3), (1,5), (4,2)),
    ((0,3), (5,1), (2,4)),
    ((3,0), (1,5), (2,4)),
    ((3,0), (5,1), (4,2)),
    # De M₄
    ((0,4), (3,1), (2,5)),
    ((0,4), (3,1), (5,2)),
    ((4,0), (1,3), (2,5)),
    ((4,0), (1,3), (5,2)),
]

# Normalizar todas las configuraciones
trivial_configs = [normalize_config(c) for c in trivial_configs]

print("="*80)
print("CÁLCULO DE ÓRBITAS DE D₆ SOBRE LAS 14 CONFIGURACIONES TRIVIALES")
print("="*80)
print()

# Generar D₆
d6 = generate_d6()
print(f"Grupo D₆ tiene {len(d6)} elementos")
print()

# Calcular órbitas usando algoritmo de unión
orbits = []
remaining = set(trivial_configs)

while remaining:
    # Tomar una configuración arbitraria
    config = remaining.pop()
    
    # Calcular su órbita
    orbit = compute_orbit(config, d6)
    
    # Añadir a lista de órbitas
    orbits.append(orbit)
    
    # Remover elementos de la órbita del conjunto restante
    remaining -= orbit

print(f"Número de órbitas encontradas: {len(orbits)}")
print()

# Mostrar cada órbita en detalle
for idx, orbit in enumerate(orbits, 1):
    print("="*80)
    print(f"ÓRBITA {idx} (tamaño: {len(orbit)})")
    print("="*80)
    
    # Elegir representante (el lexicográficamente menor)
    representative = min(orbit)
    print(f"\nRepresentante canónico:")
    config_str = ", ".join([f"[{a},{b}]" for a,b in representative])
    print(f"  {{{config_str}}}")
    
    print(f"\nTodos los elementos de la órbita:")
    for i, config in enumerate(sorted(orbit), 1):
        config_str = ", ".join([f"[{a},{b}]" for a,b in config])
        print(f"  {i:2d}. {{{config_str}}}")
    
    # Calcular estabilizador del representante
    stabilizer = []
    for g in d6:
        if apply_dihedral_element(g, representative) == representative:
            stabilizer.append(g)
    
    print(f"\nEstabilizador (elementos que fijan al representante): {len(stabilizer)}")
    for g in stabilizer:
        print(f"  - {element_to_string(g)}")
    
    # Verificar fórmula órbita-estabilizador
    print(f"\nVerificación órbita-estabilizador:")
    print(f"  |Órbita| × |Estabilizador| = {len(orbit)} × {len(stabilizer)} = {len(orbit) * len(stabilizer)}")
    print(f"  |D₆| = {len(d6)}")
    print(f"  ✓ Correcto" if len(orbit) * len(stabilizer) == len(d6) else "  ✗ ERROR")
    
    print()

print("="*80)
print("RESUMEN FINAL")
print("="*80)
print()
print(f"Total de configuraciones triviales: {len(trivial_configs)}")
print(f"Número de órbitas bajo D₆: {len(orbits)}")
print()

if len(orbits) == 2:
    print("✓ TEOREMA VERIFICADO: Hay exactamente 2 clases de equivalencia")
    print()
    print("Las 14 configuraciones se dividen en 2 órbitas:")
    for idx, orbit in enumerate(orbits, 1):
        print(f"  Órbita {idx}: {len(orbit)} configuraciones")
    print()
    print("Esto confirma la clasificación del nudo trefoil y su espejo.")
else:
    print(f"✗ TEOREMA REFUTADO: Hay {len(orbits)} clases de equivalencia (no 2)")
    print()
    print("El teorema original necesita corrección fundamental.")

print()
print("="*80)
print("ANÁLISIS DE QUIRALIDAD")
print("="*80)
print()

if len(orbits) == 2:
    # Verificar si las órbitas son quirales (imágenes especulares)
    print("Verificando si las dos órbitas son imágenes especulares...")
    print()
    
    orbit1_rep = min(orbits[0])
    orbit2_rep = min(orbits[1])
    
    print("Representante Órbita 1:")
    print(f"  {{{', '.join([f'[{a},{b}]' for a,b in orbit1_rep])}}}")
    
    print("\nRepresentante Órbita 2:")
    print(f"  {{{', '.join([f'[{a},{b}]' for a,b in orbit2_rep])}}}")
    
    # Inversión de orientaciones: [a,b] → [b,a]
    inverted_orbit1 = normalize_config([(b,a) for a,b in orbit1_rep])
    
    print("\nInversión de Órbita 1 (cambiar [a,b] → [b,a]):")
    print(f"  {{{', '.join([f'[{a},{b}]' for a,b in inverted_orbit1])}}}")
    
    # Verificar si la inversión está en Órbita 2
    if inverted_orbit1 in orbits[1]:
        print("\n✓ La inversión de Órbita 1 está en Órbita 2")
        print("  → Las órbitas son QUIRALES (imágenes especulares)")
    else:
        print("\n✗ La inversión de Órbita 1 NO está en Órbita 2")
        print("  → Las órbitas no son simplemente quirales")
        
        # Buscar si alguna transformación de D₆ mapea una órbita a la otra
        maps_between = False
        for g in d6:
            if apply_dihedral_element(g, orbit1_rep) in orbits[1]:
                print(f"\n  Pero {element_to_string(g)} mapea Órbita 1 → Órbita 2")
                maps_between = True
                break
        
        if not maps_between:
            print("\n  Ningún elemento de D₆ mapea entre órbitas → ERROR EN LA TEORÍA")

print()
print("="*80)
