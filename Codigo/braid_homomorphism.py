"""
Braid Homomorphism Implementation

This module implements the homomorphism φ₂: Bₙ → CPₙ from the braid group
to the Rook algebra, as described in Bigelow, Ramos, Yi (2011).

The homomorphism ρ = (1/√cd) φ₂ satisfies the skein relation for the
Alexander polynomial.
"""

import sympy as sp
from typing import List, Tuple
from rook_algebra import (
    RookAlgebraElement, d1, d2, d3, d4, d5, d6
)


def phi_2_sigma(j: int, c: sp.Symbol = None, d: sp.Symbol = None) -> RookAlgebraElement:
    """
    Apply homomorphism φ₂ to generator σⱼ.
    
    Formula from paper:
    φ₂(σⱼ) = (-c - d)d1ⱼ - d2ⱼ + cd·d3ⱼ + d·d4ⱼ - cd·d5ⱼ + d6ⱼ
    
    Args:
        j: Index of the braid generator (0-indexed)
        c, d: Symbolic variables
    
    Returns:
        Element of Rook algebra
    """
    if c is None:
        c = sp.Symbol('c')
    if d is None:
        d = sp.Symbol('d')
    
    result = RookAlgebraElement(c=c, d=d)
    
    # Build the linear combination
    result = ((-c - d) * d1(j) - d2(j) + c*d * d3(j) + 
              d * d4(j) - c*d * d5(j) + d6(j))
    
    return result


def phi_2_sigma_inv(j: int, c: sp.Symbol = None, d: sp.Symbol = None) -> RookAlgebraElement:
    """
    Apply homomorphism φ₂ to inverse generator σⱼ⁻¹.
    
    Formula from paper:
    φ₂(σⱼ⁻¹) = (-c - d)d1ⱼ - d2ⱼ + cd·d3ⱼ + d·d4ⱼ - cd·d5ⱼ + cd·d6ⱼ
    
    Note: Only difference from φ₂(σⱼ) is the last term (cd·d6ⱼ instead of d6ⱼ)
    
    Args:
        j: Index of the braid generator (0-indexed)
        c, d: Symbolic variables
    
    Returns:
        Element of Rook algebra
    """
    if c is None:
        c = sp.Symbol('c')
    if d is None:
        d = sp.Symbol('d')
    
    result = RookAlgebraElement(c=c, d=d)
    
    # Build the linear combination
    result = ((-c - d) * d1(j) - d2(j) + c*d * d3(j) + 
              d * d4(j) - c*d * d5(j) + c*d * d6(j))
    
    return result


def phi_2(braid_word: List[Tuple[int, int]], c: sp.Symbol = None, 
          d: sp.Symbol = None) -> RookAlgebraElement:
    """
    Apply homomorphism φ₂ to a braid word.
    
    Args:
        braid_word: List of (index, exponent) pairs
                   e.g., [(0, 1), (1, -1)] represents σ₀ · σ₁⁻¹
        c, d: Symbolic variables
    
    Returns:
        Element of Rook algebra
    """
    if c is None:
        c = sp.Symbol('c')
    if d is None:
        d = sp.Symbol('d')
    
    if not braid_word:
        # Empty braid = identity
        result = RookAlgebraElement(c=c, d=d)
        result.terms = {}  # Identity in algebra
        return result
    
    # Start with identity
    result = None
    
    for index, exponent in braid_word:
        if exponent > 0:
            # Positive generator
            for _ in range(exponent):
                term = phi_2_sigma(index, c, d)
                result = term if result is None else result * term
        elif exponent < 0:
            # Negative generator
            for _ in range(-exponent):
                term = phi_2_sigma_inv(index, c, d)
                result = term if result is None else result * term
    
    return result if result is not None else RookAlgebraElement(c=c, d=d)


def rho(braid_word: List[Tuple[int, int]], c: sp.Symbol = None, 
        d: sp.Symbol = None) -> RookAlgebraElement:
    """
    Apply homomorphism ρ = (1/√cd) φ₂ to a braid word.
    
    This is the homomorphism that satisfies the Alexander polynomial skein relation:
    ρ(σᵢ) - ρ(σᵢ⁻¹) = (1/√cd - √cd) ρ(1)
    
    Args:
        braid_word: List of (index, exponent) pairs
        c, d: Symbolic variables
    
    Returns:
        Element of Rook algebra
    """
    if c is None:
        c = sp.Symbol('c')
    if d is None:
        d = sp.Symbol('d')
    
    # Apply φ₂
    phi_result = phi_2(braid_word, c, d)
    
    # Multiply by 1/√cd
    factor = 1 / sp.sqrt(c * d)
    result = factor * phi_result
    
    return result


def verify_skein_relation(j: int = 0) -> bool:
    """
    Verify that ρ satisfies the Alexander polynomial skein relation.
    
    Should satisfy: ρ(σⱼ) - ρ(σⱼ⁻¹) = (1/√cd - √cd) ρ(1)
    
    Args:
        j: Index to test
    
    Returns:
        True if relation is satisfied
    """
    c = sp.Symbol('c')
    d = sp.Symbol('d')
    
    # Calculate left side
    rho_sigma = rho([(j, 1)], c, d)
    rho_sigma_inv = rho([(j, -1)], c, d)
    left_side = rho_sigma - rho_sigma_inv
    
    # Calculate right side
    rho_identity = rho([], c, d)
    factor = 1/sp.sqrt(c*d) - sp.sqrt(c*d)
    right_side = factor * rho_identity
    
    # Simplify and compare
    difference = sp.simplify(left_side - right_side)
    
    # Check if all terms are zero
    return all(sp.simplify(coeff) == 0 for coeff in difference.terms.values())


# Example usage and tests
if __name__ == "__main__":
    c, d = sp.symbols('c d')
    
    # Test φ₂ on σ₀
    print("φ₂(σ₀):")
    phi_sigma_0 = phi_2_sigma(0, c, d)
    print(phi_sigma_0)
    print()
    
    # Test φ₂ on σ₀⁻¹
    print("φ₂(σ₀⁻¹):")
    phi_sigma_0_inv = phi_2_sigma_inv(0, c, d)
    print(phi_sigma_0_inv)
    print()
    
    # Test ρ on σ₀
    print("ρ(σ₀):")
    rho_sigma_0 = rho([(0, 1)], c, d)
    print(rho_sigma_0)
    print()
    
    # Verify skein relation
    print("Verifying skein relation...")
    if verify_skein_relation(0):
        print("✓ Skein relation verified!")
    else:
        print("✗ Skein relation NOT satisfied")
