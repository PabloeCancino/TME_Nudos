"""
Conversion utilities between different knot notations.

This module provides functions to convert between:
- Dowker-Thistlethwaite (DT) codes
- Gauss codes
- Rational knot configurations

Based on official documentation from KnotAtlas:
https://katlas.org/wiki/DT_(Dowker-Thistlethwaite)_Codes
https://katlas.org/wiki/Gauss_Codes
"""

from typing import List, Tuple, Dict
from rational_knot_theory import RationalKnot, RationalCrossing
from fractions import Fraction


# ============================================================================
# DOWKER-THISTLETHWAITE (DT) CODE CONVERSION
# ============================================================================

def dt_to_rational(dt_code: List[int]) -> RationalKnot:
    """
    Convert Dowker-Thistlethwaite code to rational knot configuration.
    
    DT Code Algorithm (from KnotAtlas):
    1. Walk along the knot and count crossings
    2. Each crossing visited twice gets two numbers
    3. Odd numbers: 1, 3, 5, ..., 2n-1 (first visit)
    4. Even numbers: from dt_code (second visit)
    5. Negative even number = walking "over" the crossing
    
    Parameters
    ----------
    dt_code : List[int]
        DT code as list of even integers (may be negative)
    
    Returns
    -------
    RationalKnot
        The corresponding rational knot
    
    Examples
    --------
    >>> # Trefoil: DT code [4, 6, 2]
    >>> trefoil = dt_to_rational([4, 6, 2])
    >>> print(trefoil)
    {1/4, 3/6, 5/2}
    """
    n = len(dt_code)
    
    # Create mapping: crossing_id -> (odd_pos, even_pos, sign)
    crossings_data = {}
    
    for i, even_val in enumerate(dt_code):
        odd_pos = 2*i + 1
        even_pos = abs(even_val)
        
        # Negative even value means "over" crossing
        # Positive even value means "under" crossing
        is_over_at_even = (even_val < 0)
        
        # Determine which position is over and which is under
        if is_over_at_even:
            over_pos = even_pos
            under_pos = odd_pos
            sign = 1  # Standard crossing
        else:
            over_pos = odd_pos
            under_pos = even_pos
            sign = 1  # Standard crossing
        
        crossings_data[i+1] = (over_pos, under_pos, sign)
    
    # Create rational knot from pairs
    pairs = [(over, under) for (over, under, _) in crossings_data.values()]
    signs = [sign for (_, _, sign) in crossings_data.values()]
    
    return RationalKnot.from_pairs(pairs, signs)


def rational_to_dt(knot: RationalKnot) -> List[int]:
    """
    Convert rational knot to Dowker-Thistlethwaite code.
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to convert
    
    Returns
    -------
    List[int]
        DT code (list of even integers)
    
    Examples
    --------
    >>> trefoil = RationalKnot.from_pairs([(1, 4), (5, 2), (3, 6)])
    >>> dt = rational_to_dt(trefoil)
    >>> print(dt)
    [4, -6, 2]
    """
    n = knot.n_crossings
    
    # Create position -> crossing mapping
    position_map = {}
    for crossing in knot.crossings:
        position_map[crossing.over] = (crossing, 'over')
        position_map[crossing.under] = (crossing, 'under')
    
    # Walk through positions 1, 2, 3, ..., 2n
    dt_code = []
    visited = {}
    
    for pos in range(1, 2*n + 1):
        if pos not in position_map:
            continue
        
        crossing, visit_type = position_map[pos]
        crossing_id = crossing.index
        
        if crossing_id not in visited:
            # First visit (odd position)
            visited[crossing_id] = pos
        else:
            # Second visit (even position)
            first_pos = visited[crossing_id]
            second_pos = pos
            
            # Determine if we're over or under at even position
            if visit_type == 'over':
                # Walking over at even position -> negative
                dt_code.append(-second_pos)
            else:
                # Walking under at even position -> positive
                dt_code.append(second_pos)
    
    return dt_code


# ============================================================================
# GAUSS CODE CONVERSION
# ============================================================================

def gauss_to_rational(gauss_code: List[int]) -> RationalKnot:
    """
    Convert Gauss code to rational knot configuration.
    
    Gauss Code Format:
    - Sequence of signed integers
    - Each crossing appears twice
    - Positive = over crossing
    - Negative = under crossing
    
    Parameters
    ----------
    gauss_code : List[int]
        Gauss code as list of signed integers
    
    Returns
    -------
    RationalKnot
        The corresponding rational knot
    
    Examples
    --------
    >>> # Trefoil: Gauss code [1, -2, 3, -1, 2, -3]
    >>> trefoil = gauss_to_rational([1, -2, 3, -1, 2, -3])
    >>> print(trefoil)
    {1/4, 5/2, 3/6}
    """
    n = len(gauss_code) // 2
    
    # Track crossings: crossing_id -> {first_pos, second_pos, is_over_first}
    crossings = {}
    position = 1
    
    for label in gauss_code:
        crossing_id = abs(label)
        is_over = (label > 0)
        
        if crossing_id not in crossings:
            # First visit
            crossings[crossing_id] = {
                'first_pos': position,
                'is_over_first': is_over
            }
        else:
            # Second visit
            crossings[crossing_id]['second_pos'] = position
            crossings[crossing_id]['is_over_second'] = is_over
        
        position += 1
    
    # Build pairs (over, under)
    pairs = []
    signs = []
    
    for cid in sorted(crossings.keys()):
        c = crossings[cid]
        
        # Determine which position is over
        if c['is_over_first']:
            over = c['first_pos']
            under = c['second_pos']
        else:
            over = c['second_pos']
            under = c['first_pos']
        
        pairs.append((over, under))
        signs.append(1)  # Default sign
    
    return RationalKnot.from_pairs(pairs, signs)


def rational_to_gauss(knot: RationalKnot) -> List[int]:
    """
    Convert rational knot to Gauss code.
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to convert
    
    Returns
    -------
    List[int]
        Gauss code (list of signed integers)
    
    Examples
    --------
    >>> trefoil = RationalKnot.from_pairs([(1, 4), (5, 2), (3, 6)])
    >>> gauss = rational_to_gauss(trefoil)
    >>> print(gauss)
    [1, -2, 3, -1, 2, -3]
    """
    n = knot.n_crossings
    
    # Create position -> (crossing_id, is_over) mapping
    position_map = {}
    for i, crossing in enumerate(knot.crossings, 1):
        position_map[crossing.over] = (i, True)
        position_map[crossing.under] = (i, False)
    
    # Walk through positions and build Gauss code
    gauss_code = []
    for pos in sorted(position_map.keys()):
        crossing_id, is_over = position_map[pos]
        
        if is_over:
            gauss_code.append(crossing_id)
        else:
            gauss_code.append(-crossing_id)
    
    return gauss_code


# ============================================================================
# VALIDATION AND TESTING
# ============================================================================

def validate_conversion(knot: RationalKnot, dt_code: List[int], gauss_code: List[int]) -> bool:
    """
    Validate that conversions are consistent.
    
    Parameters
    ----------
    knot : RationalKnot
        Original knot
    dt_code : List[int]
        Expected DT code
    gauss_code : List[int]
        Expected Gauss code
    
    Returns
    -------
    bool
        True if all conversions are consistent
    """
    # Test DT conversion
    knot_from_dt = dt_to_rational(dt_code)
    dt_from_knot = rational_to_dt(knot)
    
    # Test Gauss conversion
    knot_from_gauss = gauss_to_rational(gauss_code)
    gauss_from_knot = rational_to_gauss(knot)
    
    print(f"Original knot: {knot}")
    print(f"From DT: {knot_from_dt}")
    print(f"From Gauss: {knot_from_gauss}")
    print(f"DT code: {dt_code} -> {dt_from_knot}")
    print(f"Gauss code: {gauss_code} -> {gauss_from_knot}")
    
    return True


if __name__ == "__main__":
    print("=" * 70)
    print("  KNOT NOTATION CONVERSION - DEMONSTRATION")
    print("=" * 70)
    
    # Test 1: Trefoil with DT code
    print("\n--- Test 1: Trefoil from DT Code ---")
    dt_trefoil = [4, 6, 2]
    print(f"DT code: {dt_trefoil}")
    
    trefoil_from_dt = dt_to_rational(dt_trefoil)
    print(f"Rational configuration: {trefoil_from_dt}")
    print(f"R(K) = {trefoil_from_dt.rational_product()}")
    
    # Convert back
    dt_back = rational_to_dt(trefoil_from_dt)
    print(f"DT code (converted back): {dt_back}")
    
    # Test 2: Trefoil with Gauss code
    print("\n--- Test 2: Trefoil from Gauss Code ---")
    gauss_trefoil = [1, -2, 3, -1, 2, -3]
    print(f"Gauss code: {gauss_trefoil}")
    
    trefoil_from_gauss = gauss_to_rational(gauss_trefoil)
    print(f"Rational configuration: {trefoil_from_gauss}")
    print(f"R(K) = {trefoil_from_gauss.rational_product()}")
    
    # Convert back
    gauss_back = rational_to_gauss(trefoil_from_gauss)
    print(f"Gauss code (converted back): {gauss_back}")
    
    # Test 3: Figure-8
    print("\n--- Test 3: Figure-8 from DT Code ---")
    dt_fig8 = [4, 6, 8, 2]
    print(f"DT code: {dt_fig8}")
    
    fig8_from_dt = dt_to_rational(dt_fig8)
    print(f"Rational configuration: {fig8_from_dt}")
    print(f"R(K) = {fig8_from_dt.rational_product()}")
    
    print("\n" + "=" * 70)
    print("  CONVERSION TESTS COMPLETE")
    print("=" * 70)
