"""
Rook Algebra Implementation

This module implements the Rook algebra CPₙ as described in:
Bigelow, S., Ramos, E., Yi, R. (2011). "The Alexander and Jones Polynomials 
Through Representations of Rook Algebras"

The Rook algebra provides an elegant method to compute the Alexander polynomial
via homomorphisms from the braid group.
"""

import sympy as sp
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, field
from enum import Enum


class DiagramType(Enum):
    """The 6 basic Rook diagrams."""
    D1 = 1  # Identity (2 vertical lines)
    D2 = 2  # Upper-left crossing
    D3 = 3  # Upper-right crossing
    D4 = 4  # Lower-left crossing
    D5 = 5  # Lower-right crossing
    D6 = 6  # Two horizontal lines (0 vertical lines)


@dataclass(frozen=True)
class RookDiagram:
    """
    Represents a basic Rook diagram.
    
    The 6 basic diagrams are:
    - d1: Identity (2 vertical lines)
    - d2: Upper-left crossing (1 vertical line)
    - d3: Upper-right crossing (1 vertical line)
    - d4: Lower-left crossing (1 vertical line)
    - d5: Lower-right crossing (1 vertical line)
    - d6: Two horizontal lines (0 vertical lines)
    
    Attributes:
        diagram_type: Type of diagram (D1-D6)
        position: Position in the braid (j), 0-indexed
    """
    diagram_type: DiagramType
    position: int
    
    def count_vertical_lines(self) -> int:
        """
        Count the number of vertical lines in the diagram.
        
        Returns:
            2 for d1 (identity)
            0 for d6 (two horizontal lines)
            1 for d2, d3, d4, d5 (crossings)
        """
        if self.diagram_type == DiagramType.D1:
            return 2
        elif self.diagram_type == DiagramType.D6:
            return 0
        else:
            return 1
    
    def __str__(self) -> str:
        return f"d{self.diagram_type.value}_{self.position}"
    
    def __repr__(self) -> str:
        return f"RookDiagram({self.diagram_type.name}, pos={self.position})"


@dataclass
class RookAlgebraElement:
    """
    Represents an element of the Rook algebra CPₙ.
    
    An element is a linear combination of Rook diagrams with coefficients
    that are polynomials in the variables c and d.
    
    Attributes:
        terms: Dictionary mapping RookDiagram to its coefficient (sympy expression)
        c: Symbolic variable c
        d: Symbolic variable d
    """
    terms: Dict[RookDiagram, sp.Expr] = field(default_factory=dict)
    c: sp.Symbol = field(default_factory=lambda: sp.Symbol('c'))
    d: sp.Symbol = field(default_factory=lambda: sp.Symbol('d'))
    
    def __add__(self, other: 'RookAlgebraElement') -> 'RookAlgebraElement':
        """Add two Rook algebra elements."""
        result = RookAlgebraElement(c=self.c, d=self.d)
        result.terms = self.terms.copy()
        
        for diagram, coeff in other.terms.items():
            if diagram in result.terms:
                result.terms[diagram] = sp.simplify(result.terms[diagram] + coeff)
            else:
                result.terms[diagram] = coeff
        
        # Remove zero terms
        result.terms = {d: c for d, c in result.terms.items() if c != 0}
        return result
    
    def __sub__(self, other: 'RookAlgebraElement') -> 'RookAlgebraElement':
        """Subtract two Rook algebra elements."""
        result = RookAlgebraElement(c=self.c, d=self.d)
        result.terms = self.terms.copy()
        
        for diagram, coeff in other.terms.items():
            if diagram in result.terms:
                result.terms[diagram] = sp.simplify(result.terms[diagram] - coeff)
            else:
                result.terms[diagram] = -coeff
        
        # Remove zero terms
        result.terms = {d: c for d, c in result.terms.items() if c != 0}
        return result
    
    def __mul__(self, other) -> 'RookAlgebraElement':
        """
        Multiply Rook algebra elements.
        
        If other is a scalar, multiply all coefficients.
        If other is a RookAlgebraElement, use diagram multiplication rules.
        """
        if isinstance(other, (int, float, sp.Expr)):
            # Scalar multiplication
            result = RookAlgebraElement(c=self.c, d=self.d)
            result.terms = {d: sp.simplify(c * other) for d, c in self.terms.items()}
            return result
        elif isinstance(other, RookAlgebraElement):
            # Algebra multiplication
            result = RookAlgebraElement(c=self.c, d=self.d)
            
            for d1, c1 in self.terms.items():
                for d2, c2 in other.terms.items():
                    # Multiply diagrams
                    product = self._multiply_diagrams(d1, d2)
                    coeff = sp.simplify(c1 * c2)
                    
                    for diagram, factor in product.terms.items():
                        total_coeff = sp.simplify(coeff * factor)
                        if diagram in result.terms:
                            result.terms[diagram] = sp.simplify(result.terms[diagram] + total_coeff)
                        else:
                            result.terms[diagram] = total_coeff
            
            # Remove zero terms
            result.terms = {d: c for d, c in result.terms.items() if c != 0}
            return result
        else:
            raise TypeError(f"Cannot multiply RookAlgebraElement with {type(other)}")
    
    def __rmul__(self, other) -> 'RookAlgebraElement':
        """Right multiplication (for scalar * element)."""
        return self.__mul__(other)
    
    def _multiply_diagrams(self, d1: RookDiagram, d2: RookDiagram) -> 'RookAlgebraElement':
        """
        Multiply two Rook diagrams.
        
        This implements the composition rules for Rook diagrams.
        For now, this is a simplified version. Full implementation requires
        detailed composition rules from the paper.
        """
        # Simplified: if positions don't match, result is zero
        if d1.position != d2.position:
            return RookAlgebraElement(c=self.c, d=self.d)
        
        # For same position, implement basic composition rules
        # This is a placeholder - full rules need to be implemented
        result = RookAlgebraElement(c=self.c, d=self.d)
        
        # Identity cases
        if d1.diagram_type == DiagramType.D1:
            result.terms[d2] = 1
            return result
        if d2.diagram_type == DiagramType.D1:
            result.terms[d1] = 1
            return result
        
        # Placeholder for other cases
        # TODO: Implement full multiplication table from paper
        result.terms[RookDiagram(DiagramType.D6, d1.position)] = 1
        return result
    
    def trace(self) -> sp.Expr:
        """
        Calculate the trace of this element.
        
        The trace counts only diagrams with exactly one vertical line.
        
        Returns:
            Sum of coefficients for diagrams with k=1
        """
        result = sp.Integer(0)
        for diagram, coeff in self.terms.items():
            if diagram.count_vertical_lines() == 1:
                result += coeff
        return sp.simplify(result)
    
    def __str__(self) -> str:
        if not self.terms:
            return "0"
        
        parts = []
        for diagram, coeff in sorted(self.terms.items(), key=lambda x: (x[0].position, x[0].diagram_type.value)):
            if coeff == 1:
                parts.append(str(diagram))
            elif coeff == -1:
                parts.append(f"-{diagram}")
            else:
                parts.append(f"({coeff})*{diagram}")
        
        return " + ".join(parts).replace("+ -", "- ")
    
    def __repr__(self) -> str:
        return f"RookAlgebraElement({len(self.terms)} terms)"


def create_basic_diagram(diagram_type: DiagramType, position: int, 
                        c: sp.Symbol = None, d: sp.Symbol = None) -> RookAlgebraElement:
    """
    Create a basic Rook diagram as an algebra element.
    
    Args:
        diagram_type: Type of diagram (D1-D6)
        position: Position in the braid
        c, d: Symbolic variables (optional)
    
    Returns:
        RookAlgebraElement with single diagram
    """
    if c is None:
        c = sp.Symbol('c')
    if d is None:
        d = sp.Symbol('d')
    
    diagram = RookDiagram(diagram_type, position)
    element = RookAlgebraElement(c=c, d=d)
    element.terms[diagram] = sp.Integer(1)
    return element


# Convenience functions for creating basic diagrams
def d1(j: int) -> RookAlgebraElement:
    """Create d1 diagram at position j (identity)."""
    return create_basic_diagram(DiagramType.D1, j)

def d2(j: int) -> RookAlgebraElement:
    """Create d2 diagram at position j (upper-left crossing)."""
    return create_basic_diagram(DiagramType.D2, j)

def d3(j: int) -> RookAlgebraElement:
    """Create d3 diagram at position j (upper-right crossing)."""
    return create_basic_diagram(DiagramType.D3, j)

def d4(j: int) -> RookAlgebraElement:
    """Create d4 diagram at position j (lower-left crossing)."""
    return create_basic_diagram(DiagramType.D4, j)

def d5(j: int) -> RookAlgebraElement:
    """Create d5 diagram at position j (lower-right crossing)."""
    return create_basic_diagram(DiagramType.D5, j)

def d6(j: int) -> RookAlgebraElement:
    """Create d6 diagram at position j (two horizontal lines)."""
    return create_basic_diagram(DiagramType.D6, j)
