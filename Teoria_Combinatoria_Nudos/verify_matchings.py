"""
Verificación exhaustiva de matchings perfectos en Z/6Z
y sus propiedades R1 y R2
"""

from itertools import combinations, permutations

def generate_all_matchings():
    """
    Genera todos los matchings perfectos en Z/6Z
    Un matching es un conjunto de 3 aristas disjuntas que cubren {0,1,2,3,4,5}
    """
    vertices = set(range(6))
    matchings = []
    
    # Para cada forma de particionar 6 elementos en 3 pares
    for edge1 in combinations(vertices, 2):
        remaining1 = vertices - set(edge1)
        for edge2 in combinations(remaining1, 2):
            remaining2 = remaining1 - set(edge2)
            edge3 = tuple(sorted(remaining2))
            
            # Crear matching como conjunto de aristas (tuplas ordenadas)
            matching = frozenset([
                tuple(sorted(edge1)),
                tuple(sorted(edge2)),
                edge3
            ])
            
            if matching not in matchings:
                matchings.append(matching)
    
    return matchings

def is_consecutive_edge(edge):
    """
    Verifica si una arista es consecutiva (diferencia 1 módulo 6)
    """
    a, b = edge
    return abs(a - b) == 1 or abs(a - b) == 5

def has_r1(matching):
    """
    Un matching tiene R1 si contiene al menos una arista consecutiva
    """
    return any(is_consecutive_edge(edge) for edge in matching)

def forms_r2_pattern(edge1, edge2):
    """
    Dos aristas forman patrón R2 si edge2 = {a±1, b±1} donde edge1 = {a,b}
    Verifica todas las 4 posibilidades:
    - (a+1, b+1) mod 6
    - (a-1, b-1) mod 6  
    - (a+1, b-1) mod 6
    - (a-1, b+1) mod 6
    """
    a, b = sorted(edge1)
    c, d = sorted(edge2)
    
    candidates = []
    # Paralelo positivo
    candidates.append(tuple(sorted(((a+1)%6, (b+1)%6))))
    # Paralelo negativo
    candidates.append(tuple(sorted(((a-1)%6, (b-1)%6))))
    # Antiparalelo 1
    candidates.append(tuple(sorted(((a+1)%6, (b-1)%6))))
    # Antiparalelo 2
    candidates.append(tuple(sorted(((a-1)%6, (b+1)%6))))
    
    return (c, d) in candidates

def has_r2(matching):
    """
    Un matching tiene R2 si contiene un par de aristas formando patrón R2
    """
    edges = list(matching)
    for i in range(len(edges)):
        for j in range(i+1, len(edges)):
            if forms_r2_pattern(edges[i], edges[j]):
                return True
    return False

def matching_to_string(matching):
    """
    Convierte un matching a string legible
    """
    edges = sorted([sorted(edge) for edge in matching])
    return "{" + ", ".join([f"{{{a},{b}}}" for a, b in edges]) + "}"

# Generar todos los matchings
print("="*70)
print("VERIFICACIÓN EXHAUSTIVA DE MATCHINGS EN Z/6Z")
print("="*70)
print()

all_matchings = generate_all_matchings()
print(f"Total de matchings perfectos: {len(all_matchings)}")
print()

# Clasificar matchings
matchings_with_r1 = []
matchings_with_r2 = []
matchings_with_r1_or_r2 = []
matchings_trivial = []

print("ANÁLISIS DETALLADO DE CADA MATCHING:")
print("="*70)

for idx, matching in enumerate(all_matchings, 1):
    has_r1_flag = has_r1(matching)
    has_r2_flag = has_r2(matching)
    
    if has_r1_flag:
        matchings_with_r1.append(matching)
    if has_r2_flag:
        matchings_with_r2.append(matching)
    if has_r1_flag or has_r2_flag:
        matchings_with_r1_or_r2.append(matching)
    if not has_r1_flag and not has_r2_flag:
        matchings_trivial.append(matching)
    
    status = []
    if has_r1_flag:
        status.append("R1")
    if has_r2_flag:
        status.append("R2")
    if not has_r1_flag and not has_r2_flag:
        status.append("TRIVIAL")
    
    print(f"{idx:2d}. {matching_to_string(matching):30s} → {', '.join(status) if status else 'Ninguno'}")

print()
print("="*70)
print("RESUMEN DE RESULTADOS:")
print("="*70)
print(f"Total matchings:                    {len(all_matchings)}")
print(f"Matchings con R1:                   {len(matchings_with_r1)}")
print(f"Matchings con R2:                   {len(matchings_with_r2)}")
print(f"Matchings con R1 o R2:              {len(matchings_with_r1_or_r2)}")
print(f"Matchings sin R1 ni R2 (TRIVIALES): {len(matchings_trivial)}")
print()

# Convertir a configuraciones (cada matching × 8 orientaciones)
total_configs = len(all_matchings) * 8
configs_with_r1 = len(matchings_with_r1) * 8
configs_with_r2 = len(matchings_with_r2) * 8
configs_trivial = len(matchings_trivial) * 8

print("="*70)
print("CONTEO DE CONFIGURACIONES (Matchings × 8 orientaciones):")
print("="*70)
print(f"Total configuraciones:              {total_configs}")
print(f"Configuraciones con R1:             {configs_with_r1}")
print(f"Configuraciones con R2:             {configs_with_r2}")
print(f"Configuraciones sin R1 ni R2:       {configs_trivial}")
print()

# Verificación de fórmulas del documento
print("="*70)
print("VERIFICACIÓN DE FÓRMULAS DEL DOCUMENTO:")
print("="*70)
print(f"Total esperado:          120  → Real: {total_configs}  {'✓' if total_configs == 120 else '✗'}")
print(f"Con R1 esperado:          88  → Real: {configs_with_r1}  {'✓' if configs_with_r1 == 88 else '✗'}")
print(f"Con R2 esperado:         104  → Real: {configs_with_r2}  {'✓' if configs_with_r2 == 104 else '✗'}")
print(f"Triviales esperado:       24  → Real: {configs_trivial}  {'✓' if configs_trivial == 24 else '✗'}")
print()

# Mostrar matchings triviales en detalle
if matchings_trivial:
    print("="*70)
    print("MATCHINGS TRIVIALES (sin R1 ni R2) EN DETALLE:")
    print("="*70)
    for idx, matching in enumerate(matchings_trivial, 1):
        print(f"\nMatching Trivial #{idx}: {matching_to_string(matching)}")
        edges = sorted([sorted(edge) for edge in matching])
        
        # Verificar R1
        print("  Verificación R1 (aristas consecutivas):")
        for a, b in edges:
            diff = abs(a - b)
            is_consec = diff == 1 or diff == 5
            print(f"    {{{a},{b}}}: |{a}-{b}| = {min(diff, 6-diff)} → {'CONSECUTIVA' if is_consec else 'NO consecutiva ✓'}")
        
        # Verificar R2
        print("  Verificación R2 (pares de aristas):")
        for i in range(len(edges)):
            for j in range(i+1, len(edges)):
                edge1 = edges[i]
                edge2 = edges[j]
                a, b = edge1
                c, d = edge2
                
                # Calcular candidatos
                cand1 = tuple(sorted(((a+1)%6, (b+1)%6)))
                cand2 = tuple(sorted(((a-1)%6, (b-1)%6)))
                cand3 = tuple(sorted(((a+1)%6, (b-1)%6)))
                cand4 = tuple(sorted(((a-1)%6, (b+1)%6)))
                
                forms_r2 = (c,d) in [cand1, cand2, cand3, cand4]
                
                print(f"    {{{a},{b}}} y {{{c},{d}}}: ", end="")
                if forms_r2:
                    print(f"FORMA R2 ✗")
                    if (c,d) == cand1:
                        print(f"      → Tipo: paralelo positivo ({a},{b}) → ({a+1},{b+1})")
                    elif (c,d) == cand2:
                        print(f"      → Tipo: paralelo negativo ({a},{b}) → ({a-1},{b-1})")
                    else:
                        print(f"      → Tipo: antiparalelo")
                else:
                    print(f"NO forma R2 ✓")

print()
print("="*70)
print("FIN DE LA VERIFICACIÓN")
print("="*70)
