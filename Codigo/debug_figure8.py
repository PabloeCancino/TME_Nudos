
import sympy as sp
from rational_knot_theory import RationalKnot
from alexander_polynomial import alexander_polynomial
from knot_notation_converter import dt_to_rational
import itertools

def debug_figure8():
    t = sp.Symbol('t')
    expected_poly = -t**2 + 3*t - 1
    expected_poly_sym = t**2 - 3*t + 1 # Symmetric version
    
    print("Debugging Figure-8 Alexander Polynomial")
    print(f"Target Polynomial: {expected_poly} (or symmetric equivalent)")
    
    # Get the structure from DT code
    # DT code for 4_1 is [4, 6, 8, 2]
    dt_knot = dt_to_rational([4, 6, 8, 2])
    pairs = [(c.over, c.under) for c in dt_knot.crossings]
    print(f"Crossing Pairs: {pairs}")
    
    # Try all sign combinations
    n = len(pairs)
    found = False
    
    for signs in itertools.product([1, -1], repeat=n):
        knot = RationalKnot.from_pairs(pairs, signs=list(signs))
        
        try:
            poly = alexander_polynomial(knot)
            expr = poly.as_expr()
            
            # Check if matches expected (up to units +/- t^k)
            # We simplify the difference
            
            # Check direct match
            if sp.simplify(expr - expected_poly) == 0:
                print(f"\nMATCH FOUND! Signs: {signs}")
                print(f"Polynomial: {expr}")
                found = True
                break
                
            # Check symmetric match (multiplied by -1)
            if sp.simplify(expr + expected_poly) == 0:
                print(f"\nMATCH FOUND (Negative)! Signs: {signs}")
                print(f"Polynomial: {expr}")
                found = True
                break
                
            # Check if it matches t^2 - 3t + 1
            if sp.simplify(expr - expected_poly_sym) == 0:
                print(f"\nMATCH FOUND (Symmetric)! Signs: {signs}")
                print(f"Polynomial: {expr}")
                found = True
                break
                
        except Exception as e:
            pass
            
    if not found:
        print("\nNo matching sign configuration found.")
        # Print the polynomial for the "standard" alternating signs
        # Figure 8 is alternating, so signs should alternate along the knot?
        # Or just be such that it is alternating.
        # Let's try to print the polynomial for signs=[1, -1, 1, -1]
        print("\nChecking specific configurations:")
        
        test_signs = [1, -1, 1, -1]
        knot = RationalKnot.from_pairs(pairs, signs=test_signs)
        print(f"Signs {test_signs}: {alexander_polynomial(knot).as_expr()}")
        
        test_signs = [-1, 1, -1, 1]
        knot = RationalKnot.from_pairs(pairs, signs=test_signs)
        print(f"Signs {test_signs}: {alexander_polynomial(knot).as_expr()}")

if __name__ == "__main__":
    debug_figure8()
