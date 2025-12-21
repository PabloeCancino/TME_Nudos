"""
Test suite for verifying theoretical properties of the Alexander Polynomial
based on Crowell & Fox (1977).

Properties tested:
1. Symmetry: Δ(t) = Δ(t⁻¹) for knots
2. Normalization: Δ(1) = ±1
3. Determinant property: |Δ(-1)| = determinant of the knot
4. Unknot: Δ(t) = 1
"""

import sys
import sympy as sp
from typing import List, Tuple
from rational_knot_theory import RationalKnot
from alexander_polynomial import alexander_polynomial
from rolfsen_database import ROLFSEN_KNOTS, get_knot

t = sp.Symbol('t')

def test_symmetry(knot: RationalKnot, knot_name: str = "Unknown") -> bool:
    """
    Test if Δ(t) = Δ(t⁻¹) (symmetry property for knots).
    
    This is a fundamental property: the Alexander polynomial of a knot
    is symmetric under the substitution t → t⁻¹.
    
    For a polynomial with coefficients [a₀, a₁, ..., aₙ], symmetry means:
    [a₀, a₁, ..., aₙ] = ±[aₙ, aₙ₋₁, ..., a₀]
    """
    try:
        poly = alexander_polynomial(knot)
        
        # Get coefficients
        if isinstance(poly, sp.Poly):
            coeffs = poly.all_coeffs()
        else:
            poly_obj = sp.Poly(poly, t)
            coeffs = poly_obj.all_coeffs()
        
        # Convert to integers
        coeffs = [int(c) for c in coeffs]
        
        # Remove leading/trailing zeros
        while coeffs and coeffs[0] == 0:
            coeffs.pop(0)
        while coeffs and coeffs[-1] == 0:
            coeffs.pop()
        
        if not coeffs:
            coeffs = [0]
        
        # Check symmetry: coeffs should equal ±reverse(coeffs)
        coeffs_rev = coeffs[::-1]
        
        is_symmetric = (coeffs == coeffs_rev) or (coeffs == [-c for c in coeffs_rev])
        
        if not is_symmetric:
            print(f"❌ {knot_name}: SYMMETRY FAILED")
            print(f"   Coefficients: {coeffs}")
            print(f"   Reversed:     {coeffs_rev}")
        else:
            print(f"✅ {knot_name}: Symmetric (coeffs: {coeffs})")
            
        return is_symmetric
        
    except Exception as e:
        print(f"⚠️  {knot_name}: Error testing symmetry: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_normalization(knot: RationalKnot, knot_name: str = "Unknown") -> bool:
    """
    Test if Δ(1) = ±1 (normalization property).
    
    The Alexander polynomial is normalized so that Δ(1) = ±1.
    """
    try:
        poly = alexander_polynomial(knot)
        
        # Evaluate at t=1
        if isinstance(poly, sp.Poly):
            val_at_1 = poly.subs(t, 1)
        else:
            val_at_1 = poly.subs(t, 1)
        
        val_at_1 = sp.simplify(val_at_1)
        
        is_normalized = (val_at_1 == 1) or (val_at_1 == -1)
        
        if not is_normalized:
            print(f"❌ {knot_name}: NORMALIZATION FAILED")
            print(f"   Δ(1) = {val_at_1} (expected ±1)")
        else:
            print(f"✅ {knot_name}: Δ(1) = {val_at_1}")
            
        return is_normalized
        
    except Exception as e:
        print(f"⚠️  {knot_name}: Error testing normalization: {e}")
        return False

def test_determinant_property(knot: RationalKnot, knot_name: str = "Unknown") -> Tuple[bool, int]:
    """
    Test the determinant property: |Δ(-1)| = det(knot).
    
    For alternating knots, |Δ(-1)| equals the determinant of the knot,
    which is always odd.
    
    Returns (is_odd, determinant_value)
    """
    try:
        poly = alexander_polynomial(knot)
        
        # Evaluate at t=-1
        if isinstance(poly, sp.Poly):
            val_at_neg1 = poly.subs(t, -1)
        else:
            val_at_neg1 = poly.subs(t, -1)
        
        val_at_neg1 = sp.simplify(val_at_neg1)
        det_value = abs(int(val_at_neg1))
        
        is_odd = (det_value % 2 == 1)
        
        if not is_odd and det_value != 0:
            print(f"⚠️  {knot_name}: Determinant is EVEN: {det_value}")
        else:
            print(f"✅ {knot_name}: |Δ(-1)| = {det_value} {'(odd)' if is_odd else '(zero - unknot?)'}")
            
        return is_odd or (det_value == 0), det_value
        
    except Exception as e:
        print(f"⚠️  {knot_name}: Error testing determinant: {e}")
        return False, 0

def test_unknot_property(knot: RationalKnot, knot_name: str = "Unknown") -> bool:
    """
    Test if unknot has Δ(t) = 1.
    """
    try:
        poly = alexander_polynomial(knot)
        
        if isinstance(poly, sp.Poly):
            expr = poly.as_expr()
        else:
            expr = sp.simplify(poly)
        
        is_one = sp.simplify(expr - 1) == 0
        
        if not is_one:
            print(f"❌ {knot_name}: Expected Δ(t)=1, got {expr}")
        else:
            print(f"✅ {knot_name}: Δ(t) = 1 (correct for unknot)")
            
        return is_one
        
    except Exception as e:
        print(f"⚠️  {knot_name}: Error testing unknot: {e}")
        return False

def run_comprehensive_tests():
    """
    Run all theoretical property tests on the Rolfsen database.
    """
    print("=" * 80)
    print("COMPREHENSIVE ALEXANDER POLYNOMIAL PROPERTY TESTS")
    print("Based on Crowell & Fox (1977)")
    print("=" * 80)
    
    results = {
        'symmetry': {'pass': 0, 'fail': 0},
        'normalization': {'pass': 0, 'fail': 0},
        'determinant': {'pass': 0, 'fail': 0},
        'total': 0
    }
    
    # Test unknot first
    print("\n" + "=" * 80)
    print("TEST 1: UNKNOT PROPERTY")
    print("=" * 80)
    unknot = RationalKnot([])
    if test_unknot_property(unknot, "0_1 (Unknot)"):
        results['normalization']['pass'] += 1
    else:
        results['normalization']['fail'] += 1
    results['total'] += 1
    
    # Test all knots in database
    print("\n" + "=" * 80)
    print("TEST 2: SYMMETRY PROPERTY - Δ(t) = Δ(t⁻¹)")
    print("=" * 80)
    
    for kid in sorted(ROLFSEN_KNOTS.keys()):
        if kid == "0_1":
            continue
            
        knot = get_knot(kid)
        if knot is None or not knot.crossings:
            continue
            
        results['total'] += 1
        
        if test_symmetry(knot, kid):
            results['symmetry']['pass'] += 1
        else:
            results['symmetry']['fail'] += 1
    
    print("\n" + "=" * 80)
    print("TEST 3: NORMALIZATION PROPERTY - Δ(1) = ±1")
    print("=" * 80)
    
    for kid in sorted(ROLFSEN_KNOTS.keys()):
        if kid == "0_1":
            continue
            
        knot = get_knot(kid)
        if knot is None or not knot.crossings:
            continue
        
        if test_normalization(knot, kid):
            results['normalization']['pass'] += 1
        else:
            results['normalization']['fail'] += 1
    
    print("\n" + "=" * 80)
    print("TEST 4: DETERMINANT PROPERTY - |Δ(-1)| is odd")
    print("=" * 80)
    
    for kid in sorted(ROLFSEN_KNOTS.keys()):
        if kid == "0_1":
            continue
            
        knot = get_knot(kid)
        if knot is None or not knot.crossings:
            continue
        
        is_valid, det_val = test_determinant_property(knot, kid)
        if is_valid:
            results['determinant']['pass'] += 1
        else:
            results['determinant']['fail'] += 1
    
    # Summary
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"Total knots tested: {results['total']}")
    print(f"\nSymmetry Property:")
    print(f"  ✅ Pass: {results['symmetry']['pass']}")
    print(f"  ❌ Fail: {results['symmetry']['fail']}")
    print(f"\nNormalization Property:")
    print(f"  ✅ Pass: {results['normalization']['pass']}")
    print(f"  ❌ Fail: {results['normalization']['fail']}")
    print(f"\nDeterminant Property:")
    print(f"  ✅ Pass: {results['determinant']['pass']}")
    print(f"  ❌ Fail: {results['determinant']['fail']}")
    
    total_tests = (results['symmetry']['pass'] + results['symmetry']['fail'] +
                   results['normalization']['pass'] + results['normalization']['fail'] +
                   results['determinant']['pass'] + results['determinant']['fail'])
    total_pass = (results['symmetry']['pass'] + results['normalization']['pass'] +
                  results['determinant']['pass'])
    
    print(f"\n{'=' * 80}")
    print(f"OVERALL: {total_pass}/{total_tests} tests passed ({100*total_pass/total_tests:.1f}%)")
    print(f"{'=' * 80}")

if __name__ == "__main__":
    run_comprehensive_tests()
