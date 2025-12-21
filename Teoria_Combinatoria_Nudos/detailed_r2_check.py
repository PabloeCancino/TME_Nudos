"""
Verificación detallada de los matchings que el documento 
afirma que NO tienen R2
"""

def forms_r2_pattern(edge1, edge2, verbose=False):
    """
    Dos aristas forman patrón R2 si edge2 = {a±1, b±1} donde edge1 = {a,b}
    """
    a, b = sorted(edge1)
    c, d = sorted(edge2)
    
    # Calcular todos los candidatos
    cand1 = tuple(sorted(((a+1)%6, (b+1)%6)))  # Paralelo +
    cand2 = tuple(sorted(((a-1)%6, (b-1)%6)))  # Paralelo -
    cand3 = tuple(sorted(((a+1)%6, (b-1)%6)))  # Antiparalelo 1
    cand4 = tuple(sorted(((a-1)%6, (b+1)%6)))  # Antiparalelo 2
    
    if verbose:
        print(f"    Arista base: {{{a},{b}}}")
        print(f"    Candidatos R2:")
        print(f"      Paralelo (+): {cand1}")
        print(f"      Paralelo (-): {cand2}")
        print(f"      Antipar. (1): {cand3}")
        print(f"      Antipar. (2): {cand4}")
        print(f"    Arista a verificar: {{{c},{d}}}")
    
    if (c, d) == cand1:
        return True, "paralelo positivo"
    elif (c, d) == cand2:
        return True, "paralelo negativo"
    elif (c, d) == cand3:
        return True, "antiparalelo tipo 1"
    elif (c, d) == cand4:
        return True, "antiparalelo tipo 2"
    else:
        return False, None

# Matchings que el documento afirma que NO tienen R2
suspect_matchings = [
    ("Matching 5 (M₁)", [(0,2), (1,4), (3,5)]),
    ("Matching 8 (M₂)", [(0,3), (1,4), (2,5)]),
    ("Matching 9 (M₃)", [(0,3), (1,5), (2,4)]),
    ("Matching 11 (M₄)", [(0,4), (1,3), (2,5)]),
]

print("="*80)
print("VERIFICACIÓN DETALLADA DE MATCHINGS SOSPECHOSOS")
print("="*80)
print()

for name, edges in suspect_matchings:
    print(f"\n{'='*80}")
    print(f"{name}: {{{', '.join([f'{{{a},{b}}}' for a,b in edges])}}}")
    print(f"{'='*80}")
    
    has_r2 = False
    r2_pairs = []
    
    for i in range(len(edges)):
        for j in range(i+1, len(edges)):
            edge1 = edges[i]
            edge2 = edges[j]
            
            print(f"\n  Verificando par: {{{edge1[0]},{edge1[1]}}} y {{{edge2[0]},{edge2[1]}}}")
            forms_r2, r2_type = forms_r2_pattern(edge1, edge2, verbose=True)
            
            if forms_r2:
                print(f"    ✗ FORMA R2 (tipo: {r2_type})")
                has_r2 = True
                r2_pairs.append((edge1, edge2, r2_type))
            else:
                print(f"    ✓ No forma R2")
    
    print(f"\n  Conclusión: {name} {'TIENE R2 ✗' if has_r2 else 'NO TIENE R2 ✓'}")
    print(f"  Documento afirma: Trivial (sin R2)")
    if has_r2:
        print(f"  >>> CONTRADICCIÓN DETECTADA <<<")
        print(f"\n  Pares R2 encontrados:")
        for edge1, edge2, tipo in r2_pairs:
            print(f"    • {{{edge1[0]},{edge1[1]}}} con {{{edge2[0]},{edge2[1]}}} (tipo: {tipo})")

print("\n" + "="*80)
print("ANÁLISIS DE LA DEFINICIÓN DE R2")
print("="*80)
print()
print("Definición del documento (Sección 5.1):")
print('  "Dos tuplas [a,b] y [c,d] forman un par R2 si:')
print('   (c,d) ∈ {(a+1,b+1), (a-1,b-1), (a+1,b-1), (a-1,b+1)}"')
print()
print("IMPORTANTE: Esta definición se aplica a TUPLAS ORDENADAS [a,b].")
print("Pero en un matching, las aristas son NO ORDENADAS {a,b}.")
print()
print("Pregunta clave: ¿Cómo se traduce esto a matchings?")
print()
print("Interpretación 1 (la que usamos):")
print("  Un matching tiene R2 si existen DOS ARISTAS {a,b} y {c,d} tales que")
print("  para ALGUNA ordenación de ambas, se cumple el patrón R2.")
print()
print("Interpretación 2 (posible intención del documento):")
print("  Un matching tiene R2 solo si TODAS las configuraciones")
print("  (orientaciones) derivadas tienen al menos un par R2.")
print()
print("="*80)
print()

# Verificar interpretación 2
print("VERIFICACIÓN DE INTERPRETACIÓN 2:")
print("-"*80)

for name, edges in suspect_matchings:
    print(f"\n{name}: {{{', '.join([f'{{{a},{b}}}' for a,b in edges])}}}")
    
    # Generar todas las 8 orientaciones
    orientations = []
    for o1 in [0, 1]:  # Orientación de arista 1
        for o2 in [0, 1]:  # Orientación de arista 2
            for o3 in [0, 1]:  # Orientación de arista 3
                config = []
                for i, (a, b) in enumerate(edges):
                    if [o1, o2, o3][i] == 0:
                        config.append((a, b))
                    else:
                        config.append((b, a))
                orientations.append(config)
    
    configs_with_r2 = 0
    
    for config in orientations:
        has_r2 = False
        for i in range(len(config)):
            for j in range(i+1, len(config)):
                a, b = config[i]
                c, d = config[j]
                
                # Verificar R2 con tuplas ORDENADAS
                if ((c, d) == ((a+1)%6, (b+1)%6) or
                    (c, d) == ((a-1)%6, (b-1)%6) or
                    (c, d) == ((a+1)%6, (b-1)%6) or
                    (c, d) == ((a-1)%6, (b+1)%6)):
                    has_r2 = True
                    break
            if has_r2:
                break
        
        if has_r2:
            configs_with_r2 += 1
    
    print(f"  Configuraciones con R2: {configs_with_r2}/8")
    if configs_with_r2 == 8:
        print(f"  → TODAS las configuraciones tienen R2")
    elif configs_with_r2 > 0:
        print(f"  → ALGUNAS configuraciones tienen R2 ({configs_with_r2}/8 = {configs_with_r2/8:.1%})")
        print(f"  → {8-configs_with_r2} configuraciones SIN R2 (estas son 'triviales')")
    else:
        print(f"  → NINGUNA configuración tiene R2")

print("\n" + "="*80)
print("RESUMEN FINAL")
print("="*80)
print()
print("A NIVEL MATCHING (aristas no ordenadas):")
print("  • Los 4 matchings 'candidatos' SÍ tienen pares R2")
print("  • Las aristas pueden formar patrones R2 antiparalelos")
print()
print("A NIVEL CONFIGURACIÓN (tuplas ordenadas):")
print("  • Solo ALGUNAS orientaciones generan pares R2")
print("  • Distribución:")
print("    - M₁: 4/8 configuraciones sin R2 ✓")
print("    - M₂: 2/8 configuraciones sin R2 ✓")
print("    - M₃: 4/8 configuraciones sin R2 ✓")
print("    - M₄: 4/8 configuraciones sin R2 ✓")
print()
print("CONCLUSIÓN:")
print("  El documento confunde 'matching sin R2' con 'configuraciones sin R2'.")
print("  A nivel matching: 0 sin R2")
print("  A nivel configuración: 14 sin R2 (de 4 matchings)")
print()
