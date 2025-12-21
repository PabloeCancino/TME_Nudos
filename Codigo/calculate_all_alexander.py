"""
Calculate Alexander Polynomial for the Entire Rolfsen Database
"""

import sympy as sp
from typing import Dict, List, Tuple
from rolfsen_database import ROLFSEN_KNOTS, get_knot
from alexander_polynomial import alexander_polynomial
from rational_knot_theory import RationalKnot
import time

def normalize_poly(poly: sp.Poly) -> str:
    """
    Normalize polynomial string representation for comparison.
    Alexander polynomial is defined up to units ±t^k.
    We normalize by making the lowest power t^0 and positive leading coefficient?
    Actually, standard form is usually symmetric if possible, or just canonical.
    
    Here we just return the string representation of the simplified expression.
    """
    expr = poly.as_expr()
    # Expand
    expr = sp.expand(expr)
    return str(expr).replace('**', '^').replace('*', '')

def calculate_all():
    print("=" * 80)
    print("  CALCULATING ALEXANDER POLYNOMIAL FOR ROLFSEN DATABASE")
    print("=" * 80)
    print(f"{'ID':<8} {'Name':<20} {'Alexander Polynomial Δ(t)':<40}")
    print("-" * 80)
    
    results = {}
    start_time = time.time()
    
    # Sort keys by crossing number
    sorted_keys = sorted(ROLFSEN_KNOTS.keys(), 
                        key=lambda x: (int(x.split('_')[0]), int(x.split('_')[1])))
    
    for kid in sorted_keys:
        info = ROLFSEN_KNOTS[kid]
        knot = get_knot(kid)
        
        try:
            poly = alexander_polynomial(knot)
            poly_str = normalize_poly(poly)
            results[kid] = poly_str
            
            print(f"{kid:<8} {info.common_name[:20]:<20} {poly_str:<40}")
            
        except Exception as e:
            print(f"{kid:<8} {info.common_name[:20]:<20} ERROR: {str(e)}")
            results[kid] = "ERROR"
            
    end_time = time.time()
    print("-" * 80)
    print(f"Processed {len(sorted_keys)} knots in {end_time - start_time:.2f} seconds.")
    print("\n")
    
    # Analysis
    analyze_results(results)

def analyze_results(results: Dict[str, str]):
    print("=" * 80)
    print("  ANALYSIS OF RESULTS")
    print("=" * 80)
    
    # 1. Check for duplicates (Knots with same Alexander polynomial)
    poly_to_knots = {}
    for kid, poly in results.items():
        if poly == "ERROR": continue
        if poly not in poly_to_knots:
            poly_to_knots[poly] = []
        poly_to_knots[poly].append(kid)
        
    print("\n1. Knots with Identical Alexander Polynomials:")
    duplicates = {p: k for p, k in poly_to_knots.items() if len(k) > 1}
    
    if not duplicates:
        print("None found.")
    else:
        for poly, knots in duplicates.items():
            print(f"  Δ(t) = {poly}: {', '.join(knots)}")
            
    # 2. Check Chiral Pairs
    # Alexander polynomial should NOT distinguish mirror images.
    # But our database lists chiral knots as single entries (usually).
    # We can check if non-chiral knots have symmetric polynomials?
    # Actually, ALL Alexander polynomials are symmetric Δ(t) = Δ(t^-1).
    
    print("\n2. Verification of Symmetry (Sample):")
    # Check if polynomials look symmetric (heuristic)
    # e.g. t^2 - t + 1 is symmetric if we consider t^-1
    # t - 1 + 1/t
    pass

if __name__ == "__main__":
    calculate_all()
