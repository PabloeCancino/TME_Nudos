"""
Calculate Alexander Polynomial from Braid Word using Burau/Fox Calculus.
"""

import sympy as sp
from typing import List, Tuple
from fox_calculus import FreeGroupWord, fox_derivative, apply_braid_action, t

def alexander_polynomial_from_braid(braid_word: List[Tuple[int, int]], n_strands: int) -> sp.Poly:
    """
    Calculate Alexander Polynomial for the closure of a braid.
    
    Args:
        braid_word: List of (generator, power).
        n_strands: Number of strands.
        
    Returns:
        sympy.Poly in t
    """
    # 1. Compute Automorphism phi(x_i)
    # The braid acts on the Free Group F_n.
    # We get w_i = phi(x_i)
    images = apply_braid_action(n_strands, braid_word)
    
    # 2. Construct Alexander Matrix (Unreduced)
    # M_{ij} = d(x_i * phi(x_i)^{-1}) / d x_j
    # Evaluated at x_k -> t.
    #
    # Actually, the standard formula for closure is:
    # M = I - J, where J_{ij} = d(phi(x_i))/dx_j
    # This is the Jacobian of the automorphism.
    #
    # Let's verify:
    # Relations: x_i = phi(x_i)  =>  x_i * phi(x_i)^{-1} = 1
    # D(x_i * phi(x_i)^{-1}) = D(x_i) + x_i * D(phi(x_i)^{-1})
    # = delta_{ij} + x_i * (-phi(x_i)^{-1} * D(phi(x_i)))
    # = delta_{ij} - x_i * phi(x_i)^{-1} * J_{ij}
    #
    # Under abelianization x_k -> t:
    # x_i * phi(x_i)^{-1} -> t * t^{-1} = 1.
    # So M_{ij} = delta_{ij} - J_{ij}.
    #
    # So we compute Jacobian J.
    
    rows = []
    for i in range(n_strands):
        w_i = images[i]
        row = []
        for j in range(n_strands):
            # Compute d(w_i)/dx_j
            deriv = fox_derivative(w_i, j+1) # Generators are 1-based
            
            val = 0
            if i == j:
                val = 1 - deriv
            else:
                val = -deriv
            row.append(val)
        rows.append(row)
        
    M = sp.Matrix(rows)
    
    # DEBUG: Print Matrix for small braids
    if n_strands == 3 and len(braid_word) < 5:
        # print(f"DEBUG Burau Matrix:\n{M}")
        pass
        
    # 3. Reduced Alexander Matrix
    # Remove one row and one column (usually last)
    # For a knot (single component), the minor is the polynomial.
    # For a link, it's more complex (0 for split links).
    # We assume it's a knot.
    
    M_minor = M[:-1, :-1]
    
    # 4. Determinant
    det = M_minor.det()
    poly = sp.simplify(det)
    
    # 5. Normalize
    # Multiply by t^k to make lowest power 0 or centered?
    # Standard: Make symmetric and P(1) = +/- 1
    
    # Factor out t^k
    # We want to remove negative powers of t
    # And remove common t factors
    
    # Convert to Poly
    try:
        p = sp.Poly(poly, t)
    except sp.PolificationFailed:
        # Might be 0 or rational function?
        # Should be Laurent polynomial.
        return sp.Poly(0, t)
        
    if p == 0:
        return p
        
    # Get all terms
    terms = p.terms() # list of (monom, coeff)
    if not terms:
        return p
        
    min_deg = min(deg[0] for deg, coeff in terms)
    
    # Shift to start at t^0
    p = p.as_expr() * t**(-min_deg)
    p = sp.simplify(p)
    p = sp.Poly(p, t)
    
    # Normalize sign: P(1) = +/- 1
    val_at_1 = p.subs(t, 1)
    if val_at_1 != 0:
        # We want |P(1)| = 1.
        # If P(1) = 1, good.
        # If P(1) = -1, multiply by -1.
        # If P(1) = k, then it's not a knot polynomial? Or we divide by k?
        # For knots, P(1) is always +/- 1.
        # If we get something else, it might be a link or error.
        # But we just normalize sign.
        if val_at_1 < 0:
            p = -p
            
    # Symmetrize?
    # Alexander polynomial is symmetric P(t) = t^k P(t^-1).
    # We usually present it centered or just positive powers.
    # Let's keep it as positive powers starting at 0.
    
    return p

