"""
Reidemeister Moves and Normal Form Algorithm

This module implements the rational Reidemeister moves and the normal form
algorithm for rational knot configurations.
"""

from typing import List, Tuple, Optional, Set
from copy import deepcopy
from rational_knot_theory import RationalKnot, RationalCrossing


# ============================================================================
# REIDEMEISTER MOVE DETECTION
# ============================================================================

def detect_r1_removable(knot: RationalKnot) -> List[int]:
    """
    Detect all R1-removable crossings in the knot.
    
    A crossing is R1-removable if:
    1. |o_i - u_i| = 1
    2. It does not interlace with any other crossing
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to analyze
    
    Returns
    -------
    List[int]
        List of indices (0-indexed) of R1-removable crossings
    """
    r1_removable = []
    
    for i, crossing in enumerate(knot.crossings):
        # Check condition 1: |o - u| = 1
        if not crossing.is_r1_candidate():
            continue
        
        # Check condition 2: no interlacing with other crossings
        interlaced_set = knot.get_interlacing_set(i)
        if len(interlaced_set) == 0:
            r1_removable.append(i)
    
    return r1_removable


def detect_r2_removable(knot: RationalKnot) -> List[Tuple[int, int]]:
    """
    Detect all R2-removable pairs in the knot.
    
    Two crossings form an R2-removable pair if:
    1. |o_a - o_b| = 1
    2. |u_a - u_b| = 1
    3. They interlace only with each other
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to analyze
    
    Returns
    -------
    List[Tuple[int, int]]
        List of pairs (i, j) of R2-removable crossings
    """
    r2_removable = []
    n = knot.n_crossings
    
    for i in range(n):
        for j in range(i+1, n):
            c_i = knot.crossings[i]
            c_j = knot.crossings[j]
            
            # Check conditions 1 and 2
            if abs(c_i.over - c_j.over) != 1:
                continue
            if abs(c_i.under - c_j.under) != 1:
                continue
            
            # Check condition 3: interlace only with each other
            interlaced_i = knot.get_interlacing_set(i)
            interlaced_j = knot.get_interlacing_set(j)
            
            if interlaced_i == {j} and interlaced_j == {i}:
                r2_removable.append((i, j))
    
    return r2_removable


# ============================================================================
# REIDEMEISTER MOVE APPLICATION
# ============================================================================

def renumber_positions(positions: List[int], removed_positions: Set[int]) -> List[int]:
    """
    Renumber positions after removing some positions.
    
    Parameters
    ----------
    positions : List[int]
        Original positions
    removed_positions : Set[int]
        Positions to remove
    
    Returns
    -------
    List[int]
        Renumbered positions
    """
    # Create mapping from old to new positions
    sorted_all = sorted(set(positions))
    sorted_remaining = [p for p in sorted_all if p not in removed_positions]
    
    mapping = {old: new for new, old in enumerate(sorted_remaining, start=1)}
    
    return [mapping.get(p, 0) for p in positions if p not in removed_positions]


def apply_r1_removal(knot: RationalKnot, crossing_idx: int) -> RationalKnot:
    """
    Apply R1 removal: remove a crossing and renumber.
    
    Parameters
    ----------
    knot : RationalKnot
        The original knot
    crossing_idx : int
        Index of the crossing to remove (0-indexed)
    
    Returns
    -------
    RationalKnot
        The knot after R1 removal
    """
    if crossing_idx < 0 or crossing_idx >= knot.n_crossings:
        raise ValueError(f"Invalid crossing index: {crossing_idx}")
    
    # Get the crossing to remove
    removed_crossing = knot.crossings[crossing_idx]
    removed_positions = {removed_crossing.over, removed_crossing.under}
    
    # Collect all positions from remaining crossings
    new_crossings = []
    for i, crossing in enumerate(knot.crossings):
        if i == crossing_idx:
            continue
        
        # Renumber this crossing
        all_positions = []
        for c in knot.crossings:
            if c.index != removed_crossing.index:
                all_positions.extend([c.over, c.under])
        
        # Create mapping
        sorted_positions = sorted(set(all_positions))
        mapping = {old: new for new, old in enumerate(sorted_positions, start=1)}
        
        new_over = mapping[crossing.over]
        new_under = mapping[crossing.under]
        
        new_crossings.append(RationalCrossing(
            index=len(new_crossings) + 1,
            over=new_over,
            under=new_under,
            sign=crossing.sign
        ))
    
    if not new_crossings:
        # Return empty knot
        return RationalKnot([])
    
    return RationalKnot(new_crossings)


def apply_r2_removal(knot: RationalKnot, crossing_indices: Tuple[int, int]) -> RationalKnot:
    """
    Apply R2 removal: remove two crossings and renumber.
    
    Parameters
    ----------
    knot : RationalKnot
        The original knot
    crossing_indices : Tuple[int, int]
        Indices of the two crossings to remove (0-indexed)
    
    Returns
    -------
    RationalKnot
        The knot after R2 removal
    """
    i, j = crossing_indices
    if i < 0 or i >= knot.n_crossings or j < 0 or j >= knot.n_crossings:
        raise ValueError(f"Invalid crossing indices: {i}, {j}")
    
    # Get positions to remove
    removed_positions = {
        knot.crossings[i].over, knot.crossings[i].under,
        knot.crossings[j].over, knot.crossings[j].under
    }
    
    # Collect remaining crossings
    new_crossings = []
    for idx, crossing in enumerate(knot.crossings):
        if idx in {i, j}:
            continue
        
        # Collect all positions from remaining crossings
        all_positions = []
        for idx2, c in enumerate(knot.crossings):
            if idx2 not in {i, j}:
                all_positions.extend([c.over, c.under])
        
        # Create mapping
        sorted_positions = sorted(set(all_positions))
        mapping = {old: new for new, old in enumerate(sorted_positions, start=1)}
        
        new_over = mapping[crossing.over]
        new_under = mapping[crossing.under]
        
        new_crossings.append(RationalCrossing(
            index=len(new_crossings) + 1,
            over=new_over,
            under=new_under,
            sign=crossing.sign
        ))
    
    if not new_crossings:
        return RationalKnot([])
    
    return RationalKnot(new_crossings)


# ============================================================================
# NORMAL FORM ALGORITHM
# ============================================================================

def reduce_to_irreducible(knot: RationalKnot, verbose: bool = False) -> RationalKnot:
    """
    Reduce a knot to its irreducible form by removing all R1- and R2- moves.
    
    The algorithm uses deterministic selection:
    - For R1-: choose crossing with smallest a_i
    - For R2-: choose pair with smallest a_a + a_b
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to reduce
    verbose : bool
        If True, print reduction steps
    
    Returns
    -------
    RationalKnot
        The irreducible knot
    """
    current = deepcopy(knot)
    step = 0
    
    while True:
        # Try to find R1-removable crossings
        r1_candidates = detect_r1_removable(current)
        
        if r1_candidates:
            # Choose the one with smallest a_i
            best_idx = min(r1_candidates, key=lambda i: current.crossings[i].a)
            
            if verbose:
                step += 1
                print(f"Step {step}: Removing R1- crossing at index {best_idx}: "
                      f"{current.crossings[best_idx]}")
            
            current = apply_r1_removal(current, best_idx)
            continue
        
        # Try to find R2-removable pairs
        r2_candidates = detect_r2_removable(current)
        
        if r2_candidates:
            # Choose the pair with smallest a_a + a_b
            best_pair = min(r2_candidates, 
                          key=lambda p: current.crossings[p[0]].a + current.crossings[p[1]].a)
            
            if verbose:
                step += 1
                print(f"Step {step}: Removing R2- pair at indices {best_pair}: "
                      f"{current.crossings[best_pair[0]]}, {current.crossings[best_pair[1]]}")
            
            current = apply_r2_removal(current, best_pair)
            continue
        
        # No more reductions possible
        break
    
    if verbose and step == 0:
        print("Knot is already irreducible")
    
    return current


def cyclic_renumber(knot: RationalKnot, k: int) -> RationalKnot:
    """
    Apply cyclic renumbering R_k to the knot.
    
    R_k(i) = ((i + k - 1) mod 2n) + 1
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to renumber
    k : int
        The rotation amount (0 to 2n-1)
    
    Returns
    -------
    RationalKnot
        The renumbered knot
    """
    if knot.n_crossings == 0:
        return knot
    
    n = knot.n_crossings
    modulo = 2 * n
    
    def rotate(pos: int) -> int:
        return ((pos + k - 1) % modulo) + 1
    
    new_crossings = []
    for crossing in knot.crossings:
        new_crossings.append(RationalCrossing(
            index=crossing.index,
            over=rotate(crossing.over),
            under=rotate(crossing.under),
            sign=crossing.sign
        ))
    
    return RationalKnot(new_crossings)


def lexicographic_minimum(knot: RationalKnot) -> RationalKnot:
    """
    Find the lexicographically minimal cyclic rotation of the knot.
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to minimize
    
    Returns
    -------
    RationalKnot
        The lexicographically minimal rotation
    """
    if knot.n_crossings == 0:
        return knot
    
    n = knot.n_crossings
    rotations = []
    
    # Generate all cyclic rotations
    for k in range(2 * n):
        rotated = cyclic_renumber(knot, k)
        # Sort crossings lexicographically
        sorted_crossings = sorted(rotated.crossings)
        rotations.append((sorted_crossings, rotated))
    
    # Find the lexicographically minimal one
    def crossing_tuple(c):
        return (c.over, c.under, c.sign)
    
    min_rotation = min(rotations, 
                      key=lambda x: [crossing_tuple(c) for c in x[0]])
    
    return min_rotation[1]


def normal_form(knot: RationalKnot, verbose: bool = False) -> RationalKnot:
    """
    Compute the normal form FN(K) = (K_irr)_lex.
    
    The normal form is obtained by:
    1. Reducing to irreducible form (removing all R1- and R2-)
    2. Finding the lexicographically minimal cyclic rotation
    
    Parameters
    ----------
    knot : RationalKnot
        The knot to normalize
    verbose : bool
        If True, print steps
    
    Returns
    -------
    RationalKnot
        The normal form of the knot
    """
    if verbose:
        print("=" * 60)
        print("COMPUTING NORMAL FORM")
        print("=" * 60)
        print(f"\nOriginal knot: {knot}")
        print(f"Degree: {knot.degree}")
    
    # Step 1: Reduce to irreducible
    if verbose:
        print("\n--- Step 1: Reducing to irreducible form ---")
    
    irreducible = reduce_to_irreducible(knot, verbose=verbose)
    
    if verbose:
        print(f"\nIrreducible form: {irreducible}")
        print(f"Degree after reduction: {irreducible.degree}")
    
    # Step 2: Lexicographic minimization
    if verbose:
        print("\n--- Step 2: Lexicographic minimization ---")
    
    normal = lexicographic_minimum(irreducible)
    
    if verbose:
        print(f"\nNormal form: {normal}")
        print("=" * 60)
    
    return normal


def verify_reidemeister_equivalence(knot1: RationalKnot, knot2: RationalKnot) -> bool:
    """
    Check if two knots are equivalent via Reidemeister moves.
    
    Two knots are equivalent if they have the same normal form.
    
    Parameters
    ----------
    knot1, knot2 : RationalKnot
        The knots to compare
    
    Returns
    -------
    bool
        True if equivalent, False otherwise
    """
    fn1 = normal_form(knot1)
    fn2 = normal_form(knot2)
    
    return fn1 == fn2
