"""
Resolución final: Identificar configuraciones que podrían 
ser genuinamente "no triviales"
"""

def forms_r2_ordered(tuple1, tuple2):
    a, b = tuple1
    c, d = tuple2
    
    candidates = [
        ((a+1)%6, (b+1)%6),
        ((a-1)%6, (b-1)%6),
        ((a+1)%6, (b-1)%6),
        ((a-1)%6, (b+1)%6),
    ]
    
    return (c, d) in candidates

def is_consecutive(tuple_ordered):
    a, b = tuple_ordered
    return (b == (a+1)%6) or (b == (a-1)%6)

def config_has_r1(config):
    return any(is_consecutive(t) for t in config)

def config_has_r2(config):
    for i in range(len(config)):
        for j in range(i+1, len(config)):
            if forms_r2_ordered(config[i], config[j]):
                return True
    return False

def matching_to_configs(edges):
    configs = []
    for o1 in [0, 1]:
        for o2 in [0, 1]:
            for o3 in [0, 1]:
                config = []
                for i, (a, b) in enumerate(edges):
                    if [o1, o2, o3][i] == 0:
                        config.append((a, b))
                    else:
                        config.append((b, a))
                configs.append(tuple(sorted(config)))  # Normalizar
    return list(set(configs))  # Eliminar duplicados

def generate_all_matchings():
    from itertools import combinations
    vertices = set(range(6))
    matchings = []
    
    for edge1 in combinations(vertices, 2):
        remaining1 = vertices - set(edge1)
        for edge2 in combinations(remaining1, 2):
            remaining2 = remaining1 - set(edge2)
            edge3 = tuple(sorted(remaining2))
            
            matching = frozenset([
                tuple(sorted(edge1)),
                tuple(sorted(edge2)),
                edge3
            ])
            
            if matching not in matchings:
                matchings.append(matching)
    
    return matchings

print("="*80)
print("RESOLUCIÓN FINAL: CONFIGURACIONES GENUINAMENTE NO TRIVIALES")
print("="*80)
print()

all_matchings = generate_all_matchings()

# Clasificar todos los matchings y sus configuraciones
print("ANÁLISIS EXHAUSTIVO DE TODAS LAS CONFIGURACIONES")
print("="*80)
print()

configs_no_r1_no_r2 = []
configs_by_matching = {}

for matching in all_matchings:
    edges = list(matching)
    configs = matching_to_configs(edges)
    
    for config in configs:
        has_r1 = config_has_r1(config)
        has_r2 = config_has_r2(config)
        
        if not has_r1 and not has_r2:
            configs_no_r1_no_r2.append(config)
            
            matching_key = tuple(sorted(edges))
            if matching_key not in configs_by_matching:
                configs_by_matching[matching_key] = []
            configs_by_matching[matching_key].append(config)

print(f"Total de configuraciones sin R1 ni R2: {len(configs_no_r1_no_r2)}")
print()

if len(configs_no_r1_no_r2) > 0:
    print("Matchings que generan configuraciones sin R1 ni R2:")
    print("-"*80)
    for matching, configs in sorted(configs_by_matching.items()):
        print(f"\nMatching: {{{', '.join([f'{{{a},{b}}}' for a,b in matching])}}}")
        print(f"  Número de configs sin R1 ni R2: {len(configs)}/8")
        print(f"  Configuraciones:")
        for config in configs[:4]:  # Mostrar primeras 4
            config_str = ", ".join([f"[{a},{b}]" for a,b in config])
            print(f"    {{{config_str}}}")
        if len(configs) > 4:
            print(f"    ... y {len(configs)-4} más")
else:
    print(">>> NO HAY CONFIGURACIONES SIN R1 NI R2 <<<")
    print()
    print("Esto confirma que en Z/6Z, TODAS las configuraciones K₃ son reducibles.")

print()
print("="*80)
print("CONTEO FINAL CORREGIDO")
print("="*80)
print()

# Contar todas las configuraciones por tipo
total_configs = 0
configs_with_r1 = 0
configs_with_r2 = 0
configs_trivial = 0

for matching in all_matchings:
    edges = list(matching)
    configs = matching_to_configs(edges)
    
    for config in configs:
        total_configs += 1
        has_r1 = config_has_r1(config)
        has_r2 = config_has_r2(config)
        
        if has_r1:
            configs_with_r1 += 1
        if has_r2:
            configs_with_r2 += 1
        if not has_r1 and not has_r2:
            configs_trivial += 1

# Nota: total_configs puede ser < 120 si hay configuraciones duplicadas
# después de normalización
print(f"Total configuraciones únicas: {total_configs}")
print(f"Configuraciones con R1: {configs_with_r1}")
print(f"Configuraciones con R2: {configs_with_r2}")
print(f"Configuraciones sin R1 ni R2: {configs_trivial}")
print()

if configs_trivial == 0:
    print("="*80)
    print("CONCLUSIÓN DEFINITIVA")
    print("="*80)
    print()
    print("El modelo combinatorio de K₃ en Z/6Z NO captura nudos no triviales.")
    print()
    print("Razón: Todos los nudos de 3 cruces en este modelo son reducibles")
    print("mediante movimientos de Reidemeister R1 o R2.")
    print()
    print("Opciones para el autor:")
    print()
    print("1. ACEPTAR que K₃ en Z/6Z es trivial")
    print("   → Reformular como 'modelo pedagógico'")
    print("   → Buscar nudos no triviales en K₄ (Z/8Z) o superior")
    print()
    print("2. REDEFINIR los movimientos R1/R2")
    print("   → Hacerlos más estrictos (ej: 'todas las orientaciones')")
    print("   → Requiere justificación topológica rigurosa")
    print()
    print("3. CAMBIAR el espacio base")
    print("   → Usar grupos diferentes (no Z/(2n)Z)")
    print("   → Investigar otras estructuras algebraicas")

