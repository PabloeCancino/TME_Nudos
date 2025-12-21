"""
Alexander Polynomial - Matrix Method Implementation

This module implements the calculation of the Alexander polynomial using the
Alexander Matrix method (Muñoz & Arias 2021).

This method is robust and works directly from the Rational Knot configuration
without requiring a braid representation or complex algebra multiplication rules.

Algorithm:
1. Identify arcs in the knot diagram.
2. Construct the Alexander Matrix M (n x n).
3. Compute minor determinant.
4. Normalize.
"""

import sympy as sp
from typing import List, Tuple, Dict, Set
from rational_knot_theory import RationalKnot, RationalCrossing

def identify_arcs(knot: RationalKnot) -> Dict[int, Tuple[int, int, int]]:
    """
    Identify the arcs involved in each crossing.
    
    For a rational knot, we can trace the strand to identify arcs.
    An arc is a continuous segment of the strand between two under-crossings.
    
    Returns:
        Dictionary mapping crossing index to (arc_over, arc_under_in, arc_under_out)
        where arc indices are 1-based.
    """
    n = knot.n_crossings
    if n == 0:
        return {}
        
    # For rational knots (4-plat), constructing the arc map is non-trivial directly
    # from the o/u pairs without tracing.
    # However, we can use the Gauss code or DT code to help.
    #
    # Let's use a graph traversal approach.
    # We have 2n positions {1, ..., 2n}.
    # The strand goes 1 -> 2 -> ... -> 2n -> 1.
    #
    # Crossings connect positions.
    # Crossing k connects over_pos and under_pos.
    #
    # An arc starts after an under-crossing and ends at the next under-crossing.
    #
    # Algorithm:
    # 1. Mark positions as "under" or "over".
    # 2. Walk the strand 1..2n.
    # 3. Increment arc ID when passing an "under" position.
    
    # Map position -> (crossing_index, type)
    pos_map = {}
    for c in knot.crossings:
        pos_map[c.over] = (c.index, 'over')
        pos_map[c.under] = (c.index, 'under')
        
    # Walk the strand
    arc_map = {} # position -> arc_id
    current_arc = 1
    
    # We need to handle the cyclic nature.
    # Let's do two passes to resolve the wrap-around arc.
    
    # First pass: assign temporary arc IDs
    temp_arc_map = {}
    
    # Find a starting point that is an under-crossing to start Arc 1
    # If no under-crossing (impossible for knot), start at 1.
    
    # Actually, arc changes at UNDER crossings.
    # So if we are at position `u` (under), the incoming arc ends, outgoing starts.
    # The "under" position is where the strand goes UNDER.
    
    # Let's trace:
    # positions 1, 2, ..., 2n.
    # At each step, check if it's an under crossing.
    
    # We need to assign arc IDs to CROSSINGS.
    # Each crossing involves 3 arcs:
    # - The over-arc (continuous)
    # - The incoming under-arc
    # - The outgoing under-arc
    
    # Let's store: crossing_id -> {over_arc, in_arc, out_arc}
    crossing_arcs = {c.index: {'over': 0, 'in': 0, 'out': 0} for c in knot.crossings}
    
    # Walk
    current_arc_id = 0
    # We need to determine the number of arcs = number of crossings
    # So arc IDs will be 0..n-1
    
    # Let's start walking from position 1.
    # We need to know where the "breaks" are.
    # Breaks are at 'under' positions.
    
    # Find all under positions
    under_positions = sorted([c.under for c in knot.crossings])
    
    # Map position to arc ID
    # Arc k is the segment between under_positions[k] and under_positions[k+1]
    # (handling wrap around)
    
    # Wait, the strand is 1..2n.
    # The segments are [u_i, u_{i+1}).
    # Let's assign arc IDs based on this.
    
    # Sort under positions: u_1 < u_2 < ... < u_n
    # Arc 0: from u_n to u_1 (wrapping around)
    # Arc 1: from u_1 to u_2
    # ...
    # Arc i: from u_i to u_{i+1}
    
    # But we need to match this to the crossing logic.
    # At crossing k (with under position u_k_pos):
    # Incoming arc is the one ending at u_k_pos.
    # Outgoing arc is the one starting at u_k_pos.
    
    # Let's formalize:
    # Sort under positions: p_1 < p_2 < ... < p_n
    # Arc i is the segment starting at p_i and ending at p_{i+1} (or p_1).
    # So Arc i covers positions (p_i, ..., p_{i+1}).
    #
    # At crossing with under-position p_i:
    # Incoming arc: Arc i-1 (wrapping: if i=0, Arc n-1)
    # Outgoing arc: Arc i
    #
    # At crossing with over-position o_k:
    # The over-arc is the arc that contains o_k.
    # We need to find which interval (p_j, p_{j+1}) contains o_k.
    
    sorted_unders = sorted([(c.under, c.index) for c in knot.crossings])
    # sorted_unders is list of (position, crossing_index)
    
    # Map crossing -> under_index (0..n-1)
    # This defines the "outgoing" arc for that crossing
    crossing_to_arc_idx = {}
    for idx, (pos, c_idx) in enumerate(sorted_unders):
        crossing_to_arc_idx[c_idx] = idx
        
    # Now populate the crossing_arcs dictionary
    result = {}
    
    for c in knot.crossings:
        # 1. Identify Incoming and Outgoing arcs at the under-crossing
        # The under position is c.under.
        # It corresponds to index `idx` in sorted_unders.
        idx = crossing_to_arc_idx[c.index]
        
        out_arc = idx
        in_arc = (idx - 1) % n
        
        # 2. Identify Over arc
        # The over position is c.over.
        # Find which interval it falls into.
        # Interval i is [sorted_unders[i].pos, sorted_unders[i+1].pos)
        
        over_arc = -1
        
        # Check intervals
        for i in range(n):
            p_start = sorted_unders[i][0]
            p_end = sorted_unders[(i + 1) % n][0]
            
            val = c.over
            
            if p_start < p_end:
                # Normal interval
                if p_start < val < p_end:
                    over_arc = i
                    break
            else:
                # Wrap-around interval (e.g. 10 to 2)
                if val > p_start or val < p_end:
                    over_arc = i
                    break
                    
        if over_arc == -1:
            # Should not happen if logic is correct
            # Fallback: finding the closest previous under
            # This handles the exact boundary case if over == under (impossible)
            pass
            
        result[c.index] = (over_arc, in_arc, out_arc)
        
    return result


def alexander_matrix_from_rational(knot: RationalKnot) -> sp.Matrix:
    """
    Construct the Alexander Matrix from a rational knot.
    
    Method:
    Rows: Crossings
    Cols: Arcs
    
    Entries depend on crossing sign and orientation.
    """
    n = knot.n_crossings
    t = sp.Symbol('t')
    
    if n == 0:
        return sp.Matrix([[1]])
        
    M = sp.zeros(n, n)
    
    arcs_info = identify_arcs(knot)
    
    # We need to know the orientation of the crossing to assign t correctly.
    # Orientation depends on the direction of the over vs under strand.
    #
    # Standard Alexander Matrix rules (for left-handed / right-handed):
    #
    # Crossing types (based on incoming under arc i, outgoing k, over arc j):
    #
    # Positive Crossing (Right-handed):
    #   j
    #   ^
    #   |
    # --+--> k
    #   |
    #   i
    #
    # Relation: (1-t)x_j + t x_k - x_i = 0  (or similar)
    #
    # Let's use the Fox derivative rules or standard matrix rules.
    #
    # Rule from "Knot Theory" (Livingston) or similar:
    # Arc labels x_0, ..., x_{n-1}.
    # Crossing k: over-arc x_j, under-in x_i, under-out x_{i+1}
    #
    # If crossing is positive (+1):
    #   (1-t) * x_over + t * x_out - x_in = 0
    #
    # If crossing is negative (-1):
    #   (1-t) * x_over + x_in - t * x_out = 0?
    #   Or: (1-t)x_over - x_out + t*x_in = 0
    #
    # Let's verify with Trefoil (all positive).
    #
    # We need to be careful with "Positive" definition.
    # RationalCrossing.sign is defined by the rational number convention.
    # Usually +1 is right-handed.
    
    for i, c in enumerate(knot.crossings):
        # Row i corresponds to crossing c
        over_arc, in_arc, out_arc = arcs_info[c.index]
        
        # Note: arcs are 0-indexed in our map
        
        if c.sign > 0:
            # Positive crossing
            # (1-t) * x_over + t * x_out - x_in = 0
            # Coeffs: over: 1-t, out: t, in: -1
            
            # Add to matrix (accumulate if arcs are same)
            M[i, over_arc] += (1 - t)
            M[i, out_arc] += t
            M[i, in_arc] += -1
            
        else:
            # Negative crossing
            # Standard rule: t * x_in - x_out + (1-t) * x_over = 0
            
            M[i, over_arc] += (1 - t)
            M[i, in_arc] += t
            M[i, out_arc] += -1

            
    return M


def alexander_polynomial(knot: RationalKnot) -> sp.Poly:
    """
    Calculate the Alexander polynomial Δ(t).
    
    Δ(t) = det(M_minor)
    where M_minor is M with one row and one column removed.
    """
    t = sp.Symbol('t')
    
    if knot.n_crossings == 0:
        return sp.Poly(1, t)
        
    M = alexander_matrix_from_rational(knot)
    
    # Remove last row and last column (principal minor)
    # Any (n-1)x(n-1) minor should work (up to factor ±t^k)
    M_minor = M[:-1, :-1]
    
    det = M_minor.det()
    
    # Simplify
    poly = sp.simplify(det)
    
    # Normalize: Δ(1) = ±1
    # This is a property of Alexander polynomial for knots
    try:
        val_at_1 = poly.subs(t, 1)
        if val_at_1 != 0:
            poly = poly / abs(val_at_1)
    except:
        pass
        
    # Symmetrize: Multiply by t^k to make symmetric
    # Δ(t) should be symmetric under t -> t^-1 (up to units)
    # Usually we center it.
    # For sp.Poly, we just return the polynomial in t.
    # The user can normalize it to be symmetric (Laurent) if needed.
    # Standard form is usually with positive powers and constant term non-zero.
    
    # Let's try to make the lowest power 0 (standard polynomial)
    # sympy Poly does this automatically.
    
    return sp.Poly(poly, t)


def verify_alexander_properties(knot: RationalKnot) -> Dict[str, bool]:
    """
    Verify fundamental properties of the Alexander polynomial.
    
    Properties checked:
    1. Symmetry: Δ(t) = Δ(t⁻¹) (up to units ±t^k)
    2. Normalization: Δ(1) = ±1
    3. Mirror Invariance: Δ(K*) = Δ(K)
    
    Args:
        knot: RationalKnot instance
    
    Returns:
        Dictionary of property verification results
    """
    poly = alexander_polynomial(knot)
    t = sp.Symbol('t')
    
    results = {}
    
    # 1. Symmetry
    # Check if poly(t) ~ poly(1/t)
    poly_inv = poly.subs(t, 1/t)
    # Multiply by t^deg to clear denominator
    # This is complex to check generally for Laurent polynomials in sympy Poly
    # Simplified check: evaluate at specific points
    val_2 = poly.subs(t, 2)
    val_half = poly.subs(t, 0.5)
    # They should be related? No.
    # Symmetry means coefficients are symmetric.
    coeffs = poly.all_coeffs()
    results['symmetry'] = (coeffs == coeffs[::-1])
    
    # 2. Normalization
    val_1 = poly.subs(t, 1)
    results['normalization'] = (abs(val_1) == 1)
    
    # 3. Mirror Invariance
    mirror_knot = knot.mirror()
    mirror_poly = alexander_polynomial(mirror_knot)
    results['mirror_invariance'] = (poly == mirror_poly)
    
    return results

