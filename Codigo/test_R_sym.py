"""
Cálculo de Invariante Simétrico R_sym(K) para Nudos Anfiquirales
Basado en análisis de Liang & Mislow

R_sym(K) = min(R(K), R(K*))

Para nudos anfiquirales: R_sym(K) = R_sym(K*)
"""

from rational_knot_theory import RationalKnot
from fractions import Fraction
import json

def calculate_R(knot: RationalKnot) -> Fraction:
    """
    Calcula el producto racional R(K) = ∏(oᵢ/uᵢ).
    
    Args:
        knot: Nudo racional
        
    Returns:
        Producto racional
    """
    return knot.rational_product()

def mirror_knot(knot: RationalKnot) -> RationalKnot:
    """
    Crea el espejo del nudo K*.
    
    Según teoría: K* invierte los pares (o,u) → (u,o)
    
    Args:
        knot: Nudo original
        
    Returns:
        Nudo espejo
    """
    return knot.mirror()

def R_sym(knot: RationalKnot) -> Fraction:
    """
    Calcula el invariante simétrico R_sym(K) = min(R(K), R(K*)).
    
    Para nudos anfiquirales: R_sym(K) debería ser igual a R_sym(K*)
    
    Args:
        knot: Nudo
        
    Returns:
        Invariante simétrico
    """
    R_K = calculate_R(knot)
    K_star = mirror_knot(knot)
    R_K_star = calculate_R(K_star)
    
    # Convertir a float para comparación
    R_K_float = float(R_K)
    R_K_star_float = float(R_K_star)
    
    return R_K if R_K_float <= R_K_star_float else R_K_star

def test_R_sym():
    """
    Test del invariante simétrico R_sym para nudos anfiquirales.
    """
    print("=" * 80)
    print("TEST DE INVARIANTE SIMÉTRICO R_sym(K)")
    print("=" * 80)
    print("\nTeoría: Para nudos anfiquirales, R_sym(K) = R_sym(K*)")
    print()
    
    # Cargar base de datos
    try:
        from rolfsen_database_updated import ROLFSEN_KNOTS
        print("✅ Usando rolfsen_database_updated.py\n")
    except:
        from rolfsen_database import ROLFSEN_KNOTS
        print("⚠️ Usando rolfsen_database.py (original)\n")
    
    # Lista de nudos anfiquirales conocidos
    amphichiral_knot_ids = ['4_1', '6_3', '8_3', '8_9', '8_12', '8_17', '8_18']
    
    results = {}
    
    for knot_id in amphichiral_knot_ids:
        if knot_id not in ROLFSEN_KNOTS:
            print(f"{knot_id}: ❌ No encontrado en base de datos")
            continue
        
        knot_info = ROLFSEN_KNOTS[knot_id]
        print(f"{knot_id} ({knot_info.common_name}):")
        
        try:
            # Crear nudo K
            K = RationalKnot.from_pairs(
                knot_info.rational_config,
                knot_info.signs
            )
            
            # Crear espejo K*
            K_star = mirror_knot(K)
            
            # Calcular R(K) y R(K*)
            R_K = calculate_R(K)
            R_K_star = calculate_R(K_star)
            
            # Calcular R_sym
            R_sym_K = R_sym(K)
            R_sym_K_star = R_sym(K_star)
            
            # Verificar simetría
            is_symmetric = (R_sym_K == R_sym_K_star)
            
            # Verificar relación R(K*) = R(K)⁻¹
            R_K_inv = 1 / R_K
            is_inverse = abs(float(R_K_star) - float(R_K_inv)) < 1e-10
            
            print(f"  R(K)      = {R_K} ≈ {float(R_K):.6f}")
            print(f"  R(K*)     = {R_K_star} ≈ {float(R_K_star):.6f}")
            print(f"  R(K*)⁻¹   = {R_K_inv} ≈ {float(R_K_inv):.6f}")
            print(f"  R_sym(K)  = {R_sym_K} ≈ {float(R_sym_K):.6f}")
            print(f"  R_sym(K*) = {R_sym_K_star} ≈ {float(R_sym_K_star):.6f}")
            print(f"  ")
            print(f"  ✓ R(K*) = R(K)⁻¹? {'✅ SÍ' if is_inverse else '❌ NO'}")
            print(f"  ✓ R_sym(K) = R_sym(K*)? {'✅ SÍ' if is_symmetric else '❌ NO'}")
            print()
            
            results[knot_id] = {
                'R_K': float(R_K),
                'R_K_star': float(R_K_star),
                'R_sym_K': float(R_sym_K),
                'R_sym_K_star': float(R_sym_K_star),
                'is_inverse': is_inverse,
                'is_symmetric': is_symmetric
            }
            
        except Exception as e:
            print(f"  ❌ Error: {e}\n")
            import traceback
            traceback.print_exc()
            results[knot_id] = {'error': str(e)}
    
    # Resumen
    print("=" * 80)
    print("RESUMEN")
    print("=" * 80)
    
    total = len([r for r in results.values() if 'error' not in r])
    inverse_count = sum(1 for r in results.values() 
                       if 'is_inverse' in r and r['is_inverse'])
    symmetric_count = sum(1 for r in results.values() 
                         if 'is_symmetric' in r and r['is_symmetric'])
    
    print(f"\nTotal nudos analizados: {total}")
    print(f"Nudos con R(K*) = R(K)⁻¹: {inverse_count}/{total}")
    print(f"Nudos con R_sym(K) = R_sym(K*): {symmetric_count}/{total}")
    
    if total > 0:
        print(f"\nTasa de verificación R(K*) = R(K)⁻¹: {100*inverse_count/total:.1f}%")
        print(f"Tasa de simetría R_sym: {100*symmetric_count/total:.1f}%")
    
    # Guardar resultados
    with open('R_sym_results.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\n✅ Resultados guardados en: R_sym_results.json")
    
    return results

if __name__ == "__main__":
    results = test_R_sym()
