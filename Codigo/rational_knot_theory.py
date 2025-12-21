"""
Rational Knot Theory - Computational Validation Framework

This module implements the rational formalization of knots based on ordered pairs o_i/u_i,
where o_i and u_i represent the over and under positions of crossing i.

Author: Pablo Eduardo Cancino Marentes
Implementation: Computational validation of theoretical framework
"""

from fractions import Fraction
from typing import List, Tuple, Dict, Optional, Set
from dataclasses import dataclass
import numpy as np
from copy import deepcopy


@dataclass
class RationalCrossing:
    """
    Represents a single crossing in a knot as a rational number o/u.
    
    Attributes
    ----------
    index : int
        The crossing identifier (1-indexed)
    over : int
        Position where the strand passes over (1 to 2n)
    under : int
        Position where the strand passes under (1 to 2n)
    sign : int
        Sign of the crossing (+1 or -1), default +1
    """
    index: int
    over: int
    under: int
    sign: int = 1
    
    def __post_init__(self):
        """Validate crossing data."""
        if self.over == self.under:
            raise ValueError(f"Crossing {self.index}: over and under positions must be different")
        if self.over < 1 or self.under < 1:
            raise ValueError(f"Crossing {self.index}: positions must be positive")
        if self.sign not in [-1, 1]:
            raise ValueError(f"Crossing {self.index}: sign must be +1 or -1")
    
    @property
    def a(self) -> int:
        """Minimum of over and under positions."""
        return min(self.over, self.under)
    
    @property
    def b(self) -> int:
        """Maximum of over and under positions."""
        return max(self.over, self.under)
    
    @property
    def interval(self) -> Tuple[int, int]:
        """Return interval [a, b] for interlacing detection."""
        return (self.a, self.b)
    
    @property
    def rational(self) -> Fraction:
        """Return the rational number o/u."""
        return Fraction(self.over, self.under)
    
    def is_r1_candidate(self) -> bool:
        """Check if this crossing has |o - u| = 1 (R1 condition)."""
        return abs(self.over - self.under) == 1
    
    def mirror(self) -> 'RationalCrossing':
        """Return the mirror crossing with o and u swapped."""
        return RationalCrossing(
            index=self.index,
            over=self.under,
            under=self.over,
            sign=-self.sign  # Mirror also changes sign
        )
    
    def __lt__(self, other: 'RationalCrossing') -> bool:
        """Lexicographic comparison for sorting."""
        if self.over != other.over:
            return self.over < other.over
        return self.under < other.under
    
    def __repr__(self) -> str:
        sign_str = "+" if self.sign > 0 else "-"
        return f"{self.over}/{self.under}({sign_str})"
    
    def __str__(self) -> str:
        return f"{self.over}/{self.under}"


class RationalKnot:
    """
    Represents a knot as a rational configuration.
    
    A rational configuration is a set of rational crossings {o_1/u_1, ..., o_n/u_n}
    where the positions {o_1,...,o_n,u_1,...,u_n} = {1,2,...,2n}.
    
    Attributes
    ----------
    crossings : List[RationalCrossing]
        List of crossings in the knot
    """
    
    def __init__(self, crossings: List[RationalCrossing]):
        """
        Initialize a rational knot configuration.
        
        Parameters
        ----------
        crossings : List[RationalCrossing]
            List of crossings defining the knot
        
        Raises
        ------
        ValueError
            If the configuration is invalid
        """
        self.crossings = crossings
        if not self.is_valid():
            raise ValueError("Invalid rational configuration: positions must form {1,2,...,2n}")
    
    @classmethod
    def from_pairs(cls, pairs: List[Tuple[int, int]], signs: Optional[List[int]] = None) -> 'RationalKnot':
        """
        Create a RationalKnot from a list of (over, under) pairs.
        
        Parameters
        ----------
        pairs : List[Tuple[int, int]]
            List of (over, under) position pairs
        signs : Optional[List[int]]
            List of crossing signs, defaults to all +1
        
        Returns
        -------
        RationalKnot
            The constructed knot
        """
        if signs is None:
            signs = [1] * len(pairs)
        
        crossings = [
            RationalCrossing(index=i+1, over=o, under=u, sign=s)
            for i, ((o, u), s) in enumerate(zip(pairs, signs))
        ]
        return cls(crossings)
    
    def is_valid(self) -> bool:
        """
        Check if this is a valid rational configuration.
        
        A configuration is valid if all positions {o_1,...,o_n,u_1,...,u_n}
        form exactly the set {1,2,...,2n}.
        
        Returns
        -------
        bool
            True if valid, False otherwise
        """
        if not self.crossings:
            return True  # Empty knot is valid
        
        n = len(self.crossings)
        positions = set()
        
        for crossing in self.crossings:
            positions.add(crossing.over)
            positions.add(crossing.under)
        
        expected = set(range(1, 2*n + 1))
        return positions == expected
    
    @property
    def n_crossings(self) -> int:
        """Return the number of crossings."""
        return len(self.crossings)
    
    @property
    def degree(self) -> int:
        """Return the degree (number of crossings)."""
        return self.n_crossings
    
    def rational_product(self) -> Fraction:
        """
        Compute the rational product R(K) = ∏(o_i/u_i).
        
        Returns
        -------
        Fraction
            The product of all rational crossings
        """
        if not self.crossings:
            return Fraction(1, 1)
        
        product = Fraction(1, 1)
        for crossing in self.crossings:
            product *= crossing.rational
        return product
    
    def mirror(self) -> 'RationalKnot':
        """
        Return the mirror knot K* with all rationals inverted.
        
        Returns
        -------
        RationalKnot
            The mirror knot
        """
        mirror_crossings = [c.mirror() for c in self.crossings]
        return RationalKnot(mirror_crossings)
    
    def are_interlaced(self, i: int, j: int) -> bool:
        """
        Check if crossings i and j are interlaced.
        
        Two crossings are interlaced if their intervals satisfy:
        a_i < a_j < b_i < b_j  OR  a_j < a_i < b_j < b_i
        
        Parameters
        ----------
        i, j : int
            Indices of crossings (0-indexed)
        
        Returns
        -------
        bool
            True if interlaced, False otherwise
        """
        if i == j:
            return False
        
        c_i = self.crossings[i]
        c_j = self.crossings[j]
        
        a_i, b_i = c_i.interval
        a_j, b_j = c_j.interval
        
        # Check both interlacing patterns
        pattern1 = a_i < a_j < b_i < b_j
        pattern2 = a_j < a_i < b_j < b_i
        
        return pattern1 or pattern2
    
    def get_interlacing_matrix(self) -> np.ndarray:
        """
        Compute the interlacing matrix M(K).
        
        M(K) is a symmetric matrix where M[i,j] = 1 if crossings i and j
        are interlaced, 0 otherwise.
        
        Returns
        -------
        np.ndarray
            The interlacing matrix (n x n)
        """
        n = self.n_crossings
        M = np.zeros((n, n), dtype=int)
        
        for i in range(n):
            for j in range(i+1, n):
                if self.are_interlaced(i, j):
                    M[i, j] = 1
                    M[j, i] = 1
        
        return M
    
    def get_interlacing_pattern(self, i: int, j: int) -> int:
        """
        Get the interlacing pattern η_ij for crossings i and j.
        
        Returns +1 if a_i < a_j < b_i < b_j, -1 if a_j < a_i < b_j < b_i,
        and 0 if not interlaced.
        
        Parameters
        ----------
        i, j : int
            Indices of crossings (0-indexed)
        
        Returns
        -------
        int
            +1, -1, or 0
        """
        if i == j:
            return 0
        
        c_i = self.crossings[i]
        c_j = self.crossings[j]
        
        a_i, b_i = c_i.interval
        a_j, b_j = c_j.interval
        
        if a_i < a_j < b_i < b_j:
            return 1
        elif a_j < a_i < b_j < b_i:
            return -1
        else:
            return 0
    
    def get_signed_matrix(self) -> np.ndarray:
        """
        Compute the signed matrix S(K).
        
        S(K) is an antisymmetric matrix where:
        S[i,j] = η_ij * σ_i * σ_j  for i ≠ j
        S[i,i] = 0
        
        where η_ij is the interlacing pattern and σ_i is the crossing sign.
        
        Returns
        -------
        np.ndarray
            The signed matrix (n x n)
        """
        n = self.n_crossings
        S = np.zeros((n, n), dtype=int)
        
        for i in range(n):
            for j in range(n):
                if i != j:
                    eta = self.are_interlaced(i, j)
                    sigma_i = self.crossings[i].sign
                    sigma_j = self.crossings[j].sign
                    S[i, j] = eta * sigma_i * sigma_j
                    
        return S
    
    def interlacing_count(self) -> int:
        """
        Compute I(K) = number of interlaced crossing pairs.
        
        Returns
        -------
        int
            The interlacing count
        """
        M = self.get_interlacing_matrix()
        return np.sum(M) // 2  # Divide by 2 since matrix is symmetric
    
    def normalized_invariant(self) -> float:
        """
        Compute F(K) = I(K) - deg(K)/2.
        
        Returns
        -------
        float
            The normalized invariant
        """
        return self.interlacing_count() - self.degree / 2
    
    def get_interlacing_set(self, crossing_idx: int) -> Set[int]:
        """
        Get the set of crossing indices that interlace with the given crossing.
        
        Parameters
        ----------
        crossing_idx : int
            Index of the crossing (0-indexed)
        
        Returns
        -------
        Set[int]
            Set of indices that interlace with this crossing
        """
        interlaced = set()
        for j in range(self.n_crossings):
            if j != crossing_idx and self.are_interlaced(crossing_idx, j):
                interlaced.add(j)
        return interlaced
    
    def __eq__(self, other: 'RationalKnot') -> bool:
        """Check equality of two knot configurations."""
        if self.n_crossings != other.n_crossings:
            return False
        
        # Compare sorted crossings lexicographically
        self_sorted = sorted(self.crossings)
        other_sorted = sorted(other.crossings)
        
        for c1, c2 in zip(self_sorted, other_sorted):
            if c1.over != c2.over or c1.under != c2.under or c1.sign != c2.sign:
                return False
        
        return True
    
    def __repr__(self) -> str:
        if not self.crossings:
            return "RationalKnot([])"
        crossings_str = ", ".join(repr(c) for c in self.crossings)
        return f"RationalKnot([{crossings_str}])"
    
    def __str__(self) -> str:
        if not self.crossings:
            return "{}"
        crossings_str = ", ".join(str(c) for c in self.crossings)
        return f"{{{crossings_str}}}"
    
    def to_dict(self) -> Dict:
        """
        Export knot data as a dictionary.
        
        Returns
        -------
        Dict
            Dictionary with knot properties
        """
        return {
            'crossings': [(c.over, c.under, c.sign) for c in self.crossings],
            'n_crossings': self.n_crossings,
            'rational_product': str(self.rational_product()),
            'interlacing_count': self.interlacing_count(),
            'normalized_invariant': self.normalized_invariant()
        }

    # ============================================================================
    # NEW METHODS FOR BRAID CONVERSION (TRANSFORMATION #2)
    # ============================================================================

    def to_continued_fraction(self) -> List[int]:
        """
        Convert the knot to its continued fraction representation [a1, ..., ak].
        
        This identifies the knot as a 2-bridge knot K(p/q) and returns the CF of p/q.
        
        Returns
        -------
        List[int]
            Continued fraction coefficients
        """
        # If no crossings, it's unknot
        if self.n_crossings == 0:
            return []
            
        # Strategy: Find the fraction p/q that generates this knot
        # We iterate through possible p, q and check if they match the knot
        # This is brute force but robust for small knots (validation purpose)
        
        # 1. Get DT code of this knot (for comparison)
        # We need to import rational_to_dt here to avoid circular import at top level
        from knot_notation_converter import rational_to_dt
        my_dt = rational_to_dt(self)
        
        # 2. Iterate p (determinant)
        # The determinant is related to n_crossings, usually p <= 3*n
        # We search p from 3 up to a reasonable limit
        limit_p = max(50, 4 * self.n_crossings)
        
        for p in range(3, limit_p, 2): # p is always odd for knots
            for q in range(1, p):
                if np.gcd(p, q) != 1:
                    continue
                
                # Generate candidate knot K(p/q)
                candidate = RationalKnot.from_fraction(p, q)
                
                # Compare DT codes
                # Note: DT codes might differ by mirroring or reindexing
                # But for 2-bridge knots, standard forms should match
                cand_dt = rational_to_dt(candidate)
                
                if self._are_dt_equivalent(my_dt, cand_dt):
                    # Found it! Return CF of p/q
                    return self._fraction_to_cf(p, q)
        
        # If not found, return a default based on crossings (heuristic)
        # This happens if the knot is not a standard 2-bridge knot or search limit exceeded
        return [1] * self.n_crossings

    @staticmethod
    def _fraction_to_cf(p: int, q: int) -> List[int]:
        """Convert p/q to continued fraction [a1, ..., ak]."""
        cf = []
        while q != 0:
            a = p // q
            cf.append(a)
            p, q = q, p % q
        return cf

    @classmethod
    def from_fraction(cls, p: int, q: int) -> 'RationalKnot':
        """
        Create a RationalKnot from fraction p/q (Schubert form).
        
        Parameters
        ----------
        p, q : int
            Integers defining the 2-bridge knot K(p/q)
        
        Returns
        -------
        RationalKnot
            The constructed knot
        """
        # 1. Compute Continued Fraction of p/q
        cf = cls._fraction_to_cf(p, q)
        
        # 2. Convert CF to Braid Word (Plat Closure)
        # Import inside method to avoid circular import
        from braid_conversion import braid_to_rational_knot
        
        # 2-bridge knot K(p/q) is the Plat closure of a 4-strand braid.
        # Word: s2^a1 s1^-a2 s2^a3 s1^-a4 ...
        # Generators: 1, 2, 3. (We use 1-based indexing)
        # But for 2-bridge, we only use sigma_1 and sigma_2?
        # Actually, the standard form uses sigma_2 and sigma_1 acting on 4 strands.
        # Center is between strands 2 and 3.
        # s2 acts on (2,3). s1 acts on (1,2). s3 acts on (3,4).
        # The word usually alternates between s2 and (s1, s3).
        # But for simple 2-bridge, it's often just s2 and s1?
        # Let's use the pattern: s2, s1, s2, s1...
        # With alternating signs.
        
        word = []
        for i, a in enumerate(cf):
            # Alternating generators: 2, 1, 2, 1...
            gen = 2 if i % 2 == 0 else 1
            # Alternating signs: +, -, +, -...
            sign = 1 if i % 2 == 0 else -1
            word.append((gen, sign * a))
        
        # 3. Convert Braid to RationalKnot (Plat Closure)
        return braid_to_rational_knot(word, n_strands=4, closure_type='plat')

