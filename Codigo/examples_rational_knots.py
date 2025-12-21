"""
Examples and Demonstrations of Rational Knot Theory

This module provides practical examples of rational knot configurations
and demonstrates the key theoretical properties.
"""

from fractions import Fraction
from rational_knot_theory import (
    RationalKnot, RationalCrossing, 
    verify_mirror_inverse_property, 
    compute_invariants
)
from reidemeister_moves import (
    normal_form, 
    verify_reidemeister_equivalence,
    reduce_to_irreducible
)
import numpy as np


def print_separator(title=""):
    """Print a formatted separator."""
    if title:
        print(f"\n{'=' * 70}")
        print(f"  {title}")
        print('=' * 70)
    else:
        print('-' * 70)


def print_knot_info(knot: RationalKnot, name: str = "Knot"):
    """Print detailed information about a knot."""
    print(f"\n{name}: {knot}")
    print(f"  Degree: {knot.degree}")
    print(f"  Rational product R(K): {knot.rational_product()}")
    print(f"  Interlacing count I(K): {knot.interlacing_count()}")
    print(f"  Normalized invariant F(K): {knot.normalized_invariant():.2f}")
    
    # Print interlacing matrix
    if knot.n_crossings > 0:
        M = knot.get_interlacing_matrix()
        print(f"\n  Interlacing matrix M(K):")
        print("  " + str(M).replace('\n', '\n  '))
        
        # Print signed matrix
        S = knot.get_signed_matrix()
        print(f"\n  Signed matrix S(K):")
        print("  " + str(S).replace('\n', '\n  '))


def example_trefoil():
    """
    Example: The trefoil knot (3_1).
    
    The trefoil is the simplest non-trivial knot with 3 crossings.
    Configuration: {1/4, 5/2, 3/6}
    """
    print_separator("EXAMPLE 1: TREFOIL KNOT (3_1)")
    
    # Create the trefoil
    trefoil = RationalKnot.from_pairs([
        (1, 4),
        (5, 2),
        (3, 6)
    ], signs=[1, 1, 1])
    
    print_knot_info(trefoil, "Trefoil")
    
    # Compute the mirror
    print_separator()
    trefoil_mirror = trefoil.mirror()
    print_knot_info(trefoil_mirror, "Trefoil Mirror")
    
    # Verify mirror-inverse property
    print_separator()
    R_K = trefoil.rational_product()
    R_K_mirror = trefoil_mirror.rational_product()
    product = R_K * R_K_mirror
    
    print(f"\nMirror-Inverse Property Verification:")
    print(f"  R(K) = {R_K}")
    print(f"  R(K*) = {R_K_mirror}")
    print(f"  R(K) × R(K*) = {product}")
    print(f"  Property verified: {verify_mirror_inverse_property(trefoil)}")
    
    # Check if trefoil is irreducible
    print_separator()
    print("\nChecking if trefoil is irreducible...")
    trefoil_reduced = reduce_to_irreducible(trefoil, verbose=True)
    print(f"\nReduced form: {trefoil_reduced}")
    print(f"Is already irreducible: {trefoil == trefoil_reduced}")
    
    # Compute normal form
    print_separator()
    print("\nComputing normal form...")
    trefoil_normal = normal_form(trefoil, verbose=False)
    print(f"Normal form FN(K): {trefoil_normal}")


def example_figure_eight():
    """
    Example: The figure-eight knot (4_1).
    
    The figure-eight is an achiral knot with 4 crossings.
    Configuration: {1/5, 7/2, 3/8, 6/4}
    """
    print_separator("EXAMPLE 2: FIGURE-EIGHT KNOT (4_1)")
    
    # Create the figure-eight knot
    figure_eight = RationalKnot.from_pairs([
        (1, 5),
        (7, 2),
        (3, 8),
        (6, 4)
    ], signs=[1, -1, 1, -1])
    
    print_knot_info(figure_eight, "Figure-Eight")
    
    # Compute the mirror
    print_separator()
    figure_eight_mirror = figure_eight.mirror()
    print_knot_info(figure_eight_mirror, "Figure-Eight Mirror")
    
    # Verify mirror-inverse property
    print_separator()
    print(f"\nMirror-Inverse Property Verification:")
    print(f"  R(K) = {figure_eight.rational_product()}")
    print(f"  R(K*) = {figure_eight_mirror.rational_product()}")
    print(f"  Property verified: {verify_mirror_inverse_property(figure_eight)}")
    
    # Check achirality (figure-8 is achiral, so FN(K) should equal FN(K*))
    print_separator()
    print("\nChecking achirality...")
    fn_k = normal_form(figure_eight)
    fn_k_mirror = normal_form(figure_eight_mirror)
    
    print(f"  FN(K) = {fn_k}")
    print(f"  FN(K*) = {fn_k_mirror}")
    print(f"  Are equivalent: {verify_reidemeister_equivalence(figure_eight, figure_eight_mirror)}")


def example_trivial_knot():
    """
    Example: The trivial (unknot) with added complexity.
    
    Shows how R1 and R2 moves reduce a complex diagram to the trivial knot.
    """
    print_separator("EXAMPLE 3: TRIVIAL KNOT WITH R1/R2 MOVES")
    
    # Create a knot with R1 twist
    print("\n--- Knot with R1 twist ---")
    knot_with_r1 = RationalKnot.from_pairs([
        (1, 2),  # R1 twist: |1-2| = 1
        (3, 6),
        (5, 4)
    ])
    
    print_knot_info(knot_with_r1, "Knot with R1")
    
    print("\nReducing to irreducible form...")
    reduced = reduce_to_irreducible(knot_with_r1, verbose=True)
    print_knot_info(reduced, "Reduced Knot")
    
    # Create a knot with R2 pair
    print_separator()
    print("\n--- Knot with R2 pair ---")
    knot_with_r2 = RationalKnot.from_pairs([
        (1, 4),
        (2, 5),  # R2 pair with previous
        (3, 8),
        (7, 6)
    ])
    
    print_knot_info(knot_with_r2, "Knot with R2")
    
    print("\nReducing to irreducible form...")
    reduced_r2 = reduce_to_irreducible(knot_with_r2, verbose=True)
    print_knot_info(reduced_r2, "Reduced Knot")


def example_cinquefoil():
    """
    Example: The cinquefoil knot (5_1).
    
    A chiral knot with 5 crossings.
    """
    print_separator("EXAMPLE 4: CINQUEFOIL KNOT (5_1)")
    
    # Create the cinquefoil
    cinquefoil = RationalKnot.from_pairs([
        (1, 6),
        (7, 2),
        (3, 8),
        (9, 4),
        (5, 10)
    ], signs=[1, 1, 1, 1, 1])
    
    print_knot_info(cinquefoil, "Cinquefoil")
    
    # Compute the mirror
    print_separator()
    cinquefoil_mirror = cinquefoil.mirror()
    print_knot_info(cinquefoil_mirror, "Cinquefoil Mirror")
    
    # Verify mirror-inverse property
    print_separator()
    print(f"\nMirror-Inverse Property Verification:")
    print(f"  R(K) = {cinquefoil.rational_product()}")
    print(f"  R(K*) = {cinquefoil_mirror.rational_product()}")
    print(f"  Property verified: {verify_mirror_inverse_property(cinquefoil)}")
    
    # Check if they are different knots
    print_separator()
    print("\nChecking chirality...")
    are_equivalent = verify_reidemeister_equivalence(cinquefoil, cinquefoil_mirror)
    print(f"  K equivalent to K*: {are_equivalent}")
    print(f"  Knot is chiral: {not are_equivalent}")


def example_invariants_comparison():
    """
    Example: Compare invariants across different knots.
    """
    print_separator("EXAMPLE 5: INVARIANTS COMPARISON")
    
    knots = {
        "Trefoil": RationalKnot.from_pairs([(1, 4), (5, 2), (3, 6)]),
        "Figure-8": RationalKnot.from_pairs([(1, 5), (7, 2), (3, 8), (6, 4)]),
        "Cinquefoil": RationalKnot.from_pairs([
            (1, 6), (7, 2), (3, 8), (9, 4), (5, 10)
        ])
    }
    
    print("\n{:<15} {:<10} {:<20} {:<10} {:<10}".format(
        "Knot", "Degree", "R(K)", "I(K)", "F(K)"
    ))
    print("-" * 70)
    
    for name, knot in knots.items():
        inv = compute_invariants(knot)
        print("{:<15} {:<10} {:<20} {:<10} {:<10.2f}".format(
            name,
            inv['degree'],
            str(inv['rational_product']),
            inv['interlacing_count'],
            inv['normalized_invariant']
        ))
    
    print_separator()
    print("\nMirror-Inverse Property:")
    for name, knot in knots.items():
        verified = verify_mirror_inverse_property(knot)
        print(f"  {name}: {'✓ VERIFIED' if verified else '✗ FAILED'}")


def run_all_examples():
    """Run all examples."""
    print("\n" + "=" * 70)
    print("  RATIONAL KNOT THEORY - COMPUTATIONAL VALIDATION")
    print("  Examples and Demonstrations")
    print("=" * 70)
    
    example_trefoil()
    print("\n\n")
    
    example_figure_eight()
    print("\n\n")
    
    example_trivial_knot()
    print("\n\n")
    
    example_cinquefoil()
    print("\n\n")
    
    example_invariants_comparison()
    
    print("\n" + "=" * 70)
    print("  ALL EXAMPLES COMPLETED")
    print("=" * 70 + "\n")


if __name__ == "__main__":
    run_all_examples()
