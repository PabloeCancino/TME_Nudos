"""
Rational Link Theory - Extension to Multi-Component Links

This module extends the rational knot theory to handle links (multiple components).
A link is a collection of k disjoint closed curves embedded in R³.

Author: Pablo Eduardo Cancino Marentes
Extension: Multi-component links support
"""

from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass
from fractions import Fraction
from rational_knot_theory import RationalCrossing
import numpy as np


@dataclass
class RationalComponent:
    """
    Represents a single component of a link.
    
    Attributes
    ----------
    component_id : int
        Identifier for this component (1-indexed)
    crossings : List[RationalCrossing]
        List of crossings belonging to this component
    """
    component_id: int
    crossings: List[RationalCrossing]
    
    def rational_product(self) -> Fraction:
        """Compute the rational product for this component."""
        if not self.crossings:
            return Fraction(1, 1)
        
        product = Fraction(1, 1)
        for crossing in self.crossings:
            product *= crossing.rational
        return product
    
    def __repr__(self) -> str:
        crossings_str = ", ".join(str(c) for c in self.crossings)
        return f"C{self.component_id}: {{{crossings_str}}}"


class RationalLink:
    """
    Represents a link as a collection of rational components.
    
    A link consists of k ≥ 1 components, where each component is a
    closed curve with its own sequence of crossings.
    
    Attributes
    ----------
    components : List[RationalComponent]
        List of components in the link
    """
    
    def __init__(self, components: List[RationalComponent]):
        """
        Initialize a rational link.
        
        Parameters
        ----------
        components : List[RationalComponent]
            List of components defining the link
        
        Raises
        ------
        ValueError
            If the configuration is invalid
        """
        self.components = components
        if not self.is_valid():
            raise ValueError("Invalid link configuration: positions must form {1,2,...,2n}")
    
    @classmethod
    def from_components(cls, component_pairs: List[List[Tuple[int, int]]], 
                       signs: Optional[List[List[int]]] = None) -> 'RationalLink':
        """
        Create a RationalLink from component specifications.
        
        Parameters
        ----------
        component_pairs : List[List[Tuple[int, int]]]
            List of components, each containing (over, under) pairs
        signs : Optional[List[List[int]]]
            List of sign lists for each component
        
        Returns
        -------
        RationalLink
            The constructed link
        """
        if signs is None:
            signs = [[1] * len(pairs) for pairs in component_pairs]
        
        components = []
        crossing_id = 1
        
        for comp_id, (pairs, comp_signs) in enumerate(zip(component_pairs, signs), start=1):
            crossings = []
            for (o, u), s in zip(pairs, comp_signs):
                crossings.append(RationalCrossing(
                    index=crossing_id,
                    over=o,
                    under=u,
                    sign=s
                ))
                crossing_id += 1
            components.append(RationalComponent(comp_id, crossings))
        
        return cls(components)
    
    def is_valid(self) -> bool:
        """
        Check if this is a valid link configuration.
        
        Returns
        -------
        bool
            True if valid, False otherwise
        """
        if not self.components:
            return True
        
        # Collect all positions from all components
        positions = set()
        for component in self.components:
            for crossing in component.crossings:
                positions.add(crossing.over)
                positions.add(crossing.under)
        
        # Check if positions form {1,2,...,2n}
        n = self.total_crossings
        expected = set(range(1, 2*n + 1))
        return positions == expected
    
    @property
    def n_components(self) -> int:
        """Return the number of components."""
        return len(self.components)
    
    @property
    def total_crossings(self) -> int:
        """Return the total number of crossings in the link."""
        return sum(len(comp.crossings) for comp in self.components)
    
    def component_products(self) -> List[Fraction]:
        """
        Compute the rational product for each component.
        
        Returns
        -------
        List[Fraction]
            List of rational products, one per component
        """
        return [comp.rational_product() for comp in self.components]
    
    def linking_number(self, comp_i: int, comp_j: int) -> int:
        """
        Compute the linking number between two components.
        
        The linking number is half the sum of signs of crossings
        where component i passes over/under component j.
        
        Parameters
        ----------
        comp_i, comp_j : int
            Component indices (0-indexed)
        
        Returns
        -------
        int
            The linking number
        """
        if comp_i == comp_j:
            return 0
        
        if comp_i >= self.n_components or comp_j >= self.n_components:
            raise ValueError("Component index out of range")
        
        # Get all crossings from both components
        crossings_i = {c.index: c for c in self.components[comp_i].crossings}
        crossings_j = {c.index: c for c in self.components[comp_j].crossings}
        
        # Count signed crossings between the two components
        link_sum = 0
        
        for crossing_i in self.components[comp_i].crossings:
            for crossing_j in self.components[comp_j].crossings:
                # Check if these crossings interact
                # (This is a simplified version - full implementation would need
                # to check actual crossing relationships in the diagram)
                pass
        
        # Note: Full implementation requires analyzing the actual crossing structure
        # This is a placeholder that would need diagram information
        return link_sum // 2
    
    def mirror(self) -> 'RationalLink':
        """
        Return the mirror link with all rationals inverted.
        
        Returns
        -------
        RationalLink
            The mirror link
        """
        mirror_components = []
        for comp in self.components:
            mirror_crossings = [c.mirror() for c in comp.crossings]
            mirror_components.append(RationalComponent(comp.component_id, mirror_crossings))
        return RationalLink(mirror_components)
    
    def __eq__(self, other: 'RationalLink') -> bool:
        """Check equality of two links."""
        if self.n_components != other.n_components:
            return False
        
        # Simple equality check (could be improved)
        for comp1, comp2 in zip(self.components, other.components):
            if len(comp1.crossings) != len(comp2.crossings):
                return False
        
        return True
    
    def __repr__(self) -> str:
        if not self.components:
            return "RationalLink([])"
        components_str = ", ".join(repr(c) for c in self.components)
        return f"RationalLink([{components_str}])"
    
    def __str__(self) -> str:
        if not self.components:
            return "{}"
        components_str = " ∪ ".join(str(c) for c in self.components)
        return f"{{{components_str}}}"


def verify_link_mirror_property(link: RationalLink) -> bool:
    """
    Verify that R(C_i*) = R(C_i)^(-1) for all components.
    
    Parameters
    ----------
    link : RationalLink
        The link to verify
    
    Returns
    -------
    bool
        True if property holds for all components
    """
    link_mirror = link.mirror()
    products = link.component_products()
    products_mirror = link_mirror.component_products()
    
    for R_i, R_i_mirror in zip(products, products_mirror):
        if R_i * R_i_mirror != Fraction(1, 1):
            return False
    
    return True


# ============================================================================
# EXAMPLE LINKS
# ============================================================================

def create_hopf_link() -> RationalLink:
    """
    Create the Hopf link (L2a1).
    
    The Hopf link is the simplest non-trivial link with 2 components
    and 2 crossings. Each component passes through 2 positions.
    
    Configuration:
    - Component 1: positions 1→2→1 (crossings at 1 and 2)
    - Component 2: positions 3→4→3 (crossings at 3 and 4)
    - Crossings: (1,3) and (2,4)
    
    Returns
    -------
    RationalLink
        The Hopf link
    """
    # Each crossing uses 2 positions, so 2 crossings = 4 positions total
    # Component 1 has crossings using positions (1,3) and (2,4)
    # Component 2 has crossings using positions (3,1) and (4,2)
    return RationalLink.from_components([
        [(1, 3)],  # Component 1: one crossing
        [(4, 2)]   # Component 2: one crossing  
    ], signs=[
        [1],
        [1]
    ])


def create_whitehead_link() -> RationalLink:
    """
    Create the Whitehead link (L5a1).
    
    Returns
    -------
    RationalLink
        The Whitehead link
    """
    return RationalLink.from_components([
        [(1, 6), (7, 2), (3, 8), (9, 4), (5, 10)],  # Component 1
        [(2, 7), (8, 3), (4, 9), (10, 5), (6, 1)]   # Component 2
    ])


if __name__ == "__main__":
    print("=" * 70)
    print("  RATIONAL LINK THEORY - DEMONSTRATION")
    print("=" * 70)
    
    # Example 1: Hopf Link
    print("\n--- Example 1: Hopf Link (L2a1) ---")
    hopf = create_hopf_link()
    print(f"Link: {hopf}")
    print(f"Components: {hopf.n_components}")
    print(f"Total crossings: {hopf.total_crossings}")
    
    products = hopf.component_products()
    print(f"\nRational products:")
    for i, R_i in enumerate(products, 1):
        print(f"  R(C{i}) = {R_i}")
    
    # Mirror
    print("\n--- Mirror of Hopf Link ---")
    hopf_mirror = hopf.mirror()
    print(f"Mirror: {hopf_mirror}")
    
    products_mirror = hopf_mirror.component_products()
    print(f"\nRational products of mirror:")
    for i, R_i in enumerate(products_mirror, 1):
        print(f"  R(C{i}*) = {R_i}")
    
    # Verify property
    print("\n--- Verification ---")
    verified = verify_link_mirror_property(hopf)
    print(f"Mirror-inverse property verified: {verified}")
    
    for i, (R_i, R_i_mirror) in enumerate(zip(products, products_mirror), 1):
        product = R_i * R_i_mirror
        print(f"  R(C{i}) × R(C{i}*) = {R_i} × {R_i_mirror} = {product}")
    
    print("\n" + "=" * 70)
    print("  DEMONSTRATION COMPLETE")
    print("=" * 70)
