"""
Analysis: Are Amphichiral Knots Always Even-Crossing?

This script analyzes the crossing numbers of all known amphichiral knots
to determine if there's a pattern (e.g., always even).
"""

import json


def analyze_amphichiral_crossing_numbers():
    """Analyze crossing numbers of amphichiral knots."""
    
    print("="*80)
    print("  ANÁLISIS: NÚMERO DE CRUCES EN NUDOS ANFIQUIRALES")
    print("="*80)
    
    # Load amphichiral dictionary
    with open("amphichiral_knots_dictionary.json", "r") as f:
        data = json.load(f)
    
    amphichiral_knots = data['amphichiral_knots']
    
    # Collect crossing numbers
    crossing_numbers = {}
    for knot_id, knot_data in amphichiral_knots.items():
        n = knot_data['crossing_number']
        if n not in crossing_numbers:
            crossing_numbers[n] = []
        crossing_numbers[n].append(knot_id)
    
    # Analyze
    print(f"\n### DISTRIBUCIÓN POR NÚMERO DE CRUCES ###\n")
    print(f"{'Cruces':<10} {'Cantidad':<12} {'Par/Impar':<12} {'Nudos':<50}")
    print("-"*80)
    
    even_count = 0
    odd_count = 0
    
    for n in sorted(crossing_numbers.keys()):
        knots = crossing_numbers[n]
        parity = "PAR" if n % 2 == 0 else "IMPAR"
        knots_str = ", ".join(knots[:5])
        if len(knots) > 5:
            knots_str += f", ... ({len(knots)-5} más)"
        
        print(f"{n:<10} {len(knots):<12} {parity:<12} {knots_str:<50}")
        
        if n % 2 == 0:
            even_count += len(knots)
        else:
            odd_count += len(knots)
    
    # Summary
    print(f"\n{'='*80}")
    print(f"  RESUMEN")
    print(f"{'='*80}")
    
    total = even_count + odd_count
    print(f"\nTotal de nudos anfiquirales: {total}")
    print(f"Con número PAR de cruces: {even_count} ({even_count/total*100:.1f}%)")
    print(f"Con número IMPAR de cruces: {odd_count} ({odd_count/total*100:.1f}%)")
    
    # Check the pattern
    print(f"\n### ANÁLISIS DEL PATRÓN ###\n")
    
    if odd_count == 0:
        print("✅ TODOS los nudos anfiquirales tienen número PAR de cruces")
        print("\n**Conclusión**: Existe un patrón claro.")
        print("Los nudos anfiquirales SIEMPRE tienen un número par de cruces.")
    else:
        print(f"⚠️  Hay {odd_count} nudos anfiquirales con número IMPAR de cruces")
        print("\n**Conclusión**: NO todos los nudos anfiquirales tienen número par de cruces.")
        print("El patrón no es universal.")
        
        # List odd-crossing amphichiral knots
        print(f"\nNudos anfiquirales con número IMPAR de cruces:")
        for n in sorted(crossing_numbers.keys()):
            if n % 2 == 1:
                print(f"  {n} cruces: {', '.join(crossing_numbers[n])}")
    
    # Theoretical explanation
    print(f"\n{'='*80}")
    print(f"  EXPLICACIÓN TEÓRICA")
    print(f"{'='*80}")
    
    print("""
Para que un nudo sea anfiqueiral, debe existir una isotopía que lo lleve
a su imagen espejo. Esta simetría puede manifestarse de diferentes formas:

1. **Simetría rotacional**: El nudo se ve igual al rotarlo 180°
2. **Simetría especular**: El nudo tiene un plano de simetría

La relación con el número de cruces depende del tipo de simetría:

- **Nudos con simetría rotacional**: Típicamente tienen número PAR de cruces
  (cada cruce tiene un "par" simétrico)

- **Nudos con simetría especular**: Pueden tener número IMPAR de cruces
  (el cruce central puede estar en el plano de simetría)

Sin embargo, la mayoría de nudos anfiquirales conocidos tienen número par
de cruces, especialmente en los casos más simples.
    """)
    
    # Statistical analysis
    print(f"\n{'='*80}")
    print(f"  ANÁLISIS ESTADÍSTICO")
    print(f"{'='*80}")
    
    print(f"\nDistribución detallada:")
    for n in sorted(crossing_numbers.keys()):
        count = len(crossing_numbers[n])
        parity = "par" if n % 2 == 0 else "impar"
        percentage = count / total * 100
        print(f"  {n} cruces ({parity}): {count} nudos ({percentage:.1f}%)")
    
    # Check if there's a pattern in even numbers
    even_crossings = [n for n in crossing_numbers.keys() if n % 2 == 0]
    if even_crossings:
        print(f"\nNúmeros pares de cruces presentes: {sorted(even_crossings)}")
        print(f"¿Todos los pares están representados? ", end="")
        
        expected_evens = list(range(0, max(even_crossings)+1, 2))
        missing = set(expected_evens) - set(even_crossings)
        if missing:
            print(f"NO - Faltan: {sorted(missing)}")
        else:
            print(f"SÍ - Todos los pares de 0 a {max(even_crossings)} están presentes")
    
    return crossing_numbers, even_count, odd_count


def main():
    """Main analysis."""
    crossing_numbers, even_count, odd_count = analyze_amphichiral_crossing_numbers()
    
    # Save results
    results = {
        'total_knots': even_count + odd_count,
        'even_crossing_count': even_count,
        'odd_crossing_count': odd_count,
        'all_even': odd_count == 0,
        'distribution': {str(k): len(v) for k, v in crossing_numbers.items()}
    }
    
    with open("amphichiral_crossing_analysis.json", "w") as f:
        json.dump(results, f, indent=2)
    
    print(f"\n{'='*80}")
    print(f"  Resultados guardados en: amphichiral_crossing_analysis.json")
    print(f"{'='*80}")


if __name__ == "__main__":
    main()
