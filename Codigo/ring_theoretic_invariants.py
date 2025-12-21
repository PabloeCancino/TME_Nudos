"""
Ring-Theoretic Knot Invariants
Implementation of modular arithmetic framework for knot theory

Based on the formalization:
- Knots as cyclic subgroups in ℤ/2nℤ
- Crossings as unique modular relationships
- Modular signatures to distinguish knots with same R(K)

Author: Pablo Eduardo Cancino Marentes
Date: November 28, 2025
"""

import hashlib
from typing import List, Tuple, Set, Dict
from fractions import Fraction
from dataclasses import dataclass
import json


@dataclass
class ModularKnot:
    """
    Represents a knot in the ring-theoretic framework.
    
    Attributes:
        n: Number of crossings
        crossings: List of (over, under) pairs
        ring_modulus: 2n (the modulus for ℤ/2nℤ)
    """
    n: int
    crossings: List[Tuple[int, int]]
    ring_modulus: int
    
    def __post_init__(self):
        """Validate the knot structure."""
        if self.ring_modulus != 2 * self.n:
            raise ValueError(f"Ring modulus must be 2n = {2*self.n}, got {self.ring_modulus}")
        
        if len(self.crossings) != self.n:
            raise ValueError(f"Expected {self.n} crossings, got {len(self.crossings)}")
    
    @classmethod
    def from_rational_knot(cls, rational_knot):
        """Create ModularKnot from RationalKnot object."""
        n = rational_knot.n_crossings
        crossings = [(c.over, c.under) for c in rational_knot.crossings]
        return cls(n=n, crossings=crossings, ring_modulus=2*n)


class RingTheoreticInvariants:
    """Calculator for ring-theoretic knot invariants."""
    
    @staticmethod
    def modular_sequence(knot: ModularKnot) -> List[Tuple[int, int]]:
        """
        Compute the modular sequence S(K).
        
        S(K) = [(o₁ mod 2n, u₁ mod 2n), ..., (oₙ mod 2n, uₙ mod 2n)]
        
        Parameters:
            knot: ModularKnot object
        
        Returns:
            List of (over mod 2n, under mod 2n) pairs
        """
        m = knot.ring_modulus
        return [(o % m, u % m) for o, u in knot.crossings]
    
    @staticmethod
    def modular_signature(knot: ModularKnot, algorithm: str = 'sha256') -> str:
        """
        Compute the modular signature σ(K).
        
        σ(K) = hash(S(K))
        
        Parameters:
            knot: ModularKnot object
            algorithm: Hash algorithm ('sha256', 'md5', etc.)
        
        Returns:
            Hexadecimal hash string
        """
        seq = RingTheoreticInvariants.modular_sequence(knot)
        
        # Create canonical string representation
        seq_str = str(sorted(seq))  # Sort for canonical form
        
        # Compute hash
        if algorithm == 'sha256':
            return hashlib.sha256(seq_str.encode()).hexdigest()
        elif algorithm == 'md5':
            return hashlib.md5(seq_str.encode()).hexdigest()
        else:
            raise ValueError(f"Unknown hash algorithm: {algorithm}")
    
    @staticmethod
    def ordered_pair_set(knot: ModularKnot) -> Set[Tuple[int, int]]:
        """
        Compute the set of ordered pairs P(K).
        
        P(K) = {(o₁, u₁), (o₂, u₂), ..., (oₙ, uₙ)} ⊂ (ℤ/2nℤ)²
        
        Parameters:
            knot: ModularKnot object
        
        Returns:
            Set of ordered pairs
        """
        seq = RingTheoreticInvariants.modular_sequence(knot)
        return set(seq)
    
    @staticmethod
    def verify_uniqueness(knot: ModularKnot) -> bool:
        """
        Verify that all crossing relationships are unique.
        
        Theorem: ∀i ≠ j: ρᵢ ≠ ρⱼ
        
        Parameters:
            knot: ModularKnot object
        
        Returns:
            True if all pairs are unique, False otherwise
        """
        pairs = RingTheoreticInvariants.ordered_pair_set(knot)
        return len(pairs) == knot.n
    
    @staticmethod
    def cyclic_group_elements(knot: ModularKnot) -> List[int]:
        """
        Get all elements of the cyclic group G_K = ℤ/2nℤ.
        
        G_K = ⟨1⟩ = {1, 2, 3, ..., 2n ≡ 0}
        
        Parameters:
            knot: ModularKnot object
        
        Returns:
            List of group elements
        """
        return list(range(knot.ring_modulus))
    
    @staticmethod
    def coset_decomposition(knot: ModularKnot) -> Dict[str, List[Tuple[int, int]]]:
        """
        Decompose crossings into left and right cosets.
        
        Right coset: over positions
        Left coset: under positions
        
        Parameters:
            knot: ModularKnot object
        
        Returns:
            Dictionary with 'right' and 'left' cosets
        """
        right_coset = [o for o, u in knot.crossings]
        left_coset = [u for o, u in knot.crossings]
        
        return {
            'right': right_coset,
            'left': left_coset
        }


class KnotFamilyAnalyzer:
    """Analyze families of knots with the same R(K) value."""
    
    @staticmethod
    def group_by_rational_product(knots: List[Tuple[str, ModularKnot]]) -> Dict[str, List[str]]:
        """
        Group knots by their R(K) value.
        
        Parameters:
            knots: List of (knot_id, ModularKnot) tuples
        
        Returns:
            Dictionary mapping R(K) to list of knot IDs
        """
        from rational_knot_theory import RationalKnot
        import rolfsen_database as rdb
        
        families = {}
        
        for knot_id, mod_knot in knots:
            # Get rational knot
            rat_knot = rdb.get_knot(knot_id)
            if not rat_knot:
                continue
            
            # Calculate R(K)
            R_K = str(rat_knot.rational_product())
            
            if R_K not in families:
                families[R_K] = []
            
            families[R_K].append(knot_id)
        
        return families
    
    @staticmethod
    def distinguish_family(family_knots: List[Tuple[str, ModularKnot]]) -> Dict[str, str]:
        """
        Distinguish knots in a family using modular signatures.
        
        Parameters:
            family_knots: List of (knot_id, ModularKnot) in same family
        
        Returns:
            Dictionary mapping knot_id to signature
        """
        signatures = {}
        
        for knot_id, mod_knot in family_knots:
            sig = RingTheoreticInvariants.modular_signature(mod_knot)
            signatures[knot_id] = sig
        
        return signatures
    
    @staticmethod
    def analyze_family(family_knots: List[Tuple[str, ModularKnot]]) -> Dict:
        """
        Complete analysis of a knot family.
        
        Parameters:
            family_knots: List of (knot_id, ModularKnot) in same family
        
        Returns:
            Analysis results
        """
        results = {
            'family_size': len(family_knots),
            'knots': {},
            'all_unique': True
        }
        
        signatures = KnotFamilyAnalyzer.distinguish_family(family_knots)
        
        # Check uniqueness
        sig_values = list(signatures.values())
        if len(set(sig_values)) != len(sig_values):
            results['all_unique'] = False
        
        # Detailed analysis for each knot
        for knot_id, mod_knot in family_knots:
            results['knots'][knot_id] = {
                'signature': signatures[knot_id],
                'modular_sequence': RingTheoreticInvariants.modular_sequence(mod_knot),
                'ordered_pairs': list(RingTheoreticInvariants.ordered_pair_set(mod_knot)),
                'uniqueness_verified': RingTheoreticInvariants.verify_uniqueness(mod_knot)
            }
        
        return results


def test_7_crossing_family():
    """Test the 7-crossing family with R(K) = 429/2048."""
    import rolfsen_database as rdb
    
    print("=" * 80)
    print("  TESTING 7-CROSSING FAMILY")
    print("=" * 80)
    
    # Get all 7-crossing knots
    family_7 = []
    for knot_id in rdb.get_knots_by_crossing_number(7):
        rat_knot = rdb.get_knot(knot_id)
        if rat_knot:
            R_K = rat_knot.rational_product()
            if R_K == Fraction(429, 2048):
                mod_knot = ModularKnot.from_rational_knot(rat_knot)
                family_7.append((knot_id, mod_knot))
    
    print(f"\nFound {len(family_7)} knots with R(K) = 429/2048")
    
    # Analyze family
    analysis = KnotFamilyAnalyzer.analyze_family(family_7)
    
    print(f"\nAll signatures unique? {analysis['all_unique']}")
    print(f"\nSignatures:")
    for knot_id in sorted(analysis['knots'].keys()):
        sig = analysis['knots'][knot_id]['signature'][:16]  # First 16 chars
        print(f"  {knot_id}: {sig}...")
    
    return analysis


def test_8_crossing_family():
    """Test the 8-crossing family with R(K) = 6435/32768."""
    import rolfsen_database as rdb
    
    print("\n" + "=" * 80)
    print("  TESTING 8-CROSSING FAMILY")
    print("=" * 80)
    
    # Get all 8-crossing knots
    family_8 = []
    for knot_id in rdb.get_knots_by_crossing_number(8):
        rat_knot = rdb.get_knot(knot_id)
        if rat_knot:
            R_K = rat_knot.rational_product()
            if R_K == Fraction(6435, 32768):
                mod_knot = ModularKnot.from_rational_knot(rat_knot)
                family_8.append((knot_id, mod_knot))
    
    print(f"\nFound {len(family_8)} knots with R(K) = 6435/32768")
    
    # Analyze family
    analysis = KnotFamilyAnalyzer.analyze_family(family_8)
    
    print(f"\nAll signatures unique? {analysis['all_unique']}")
    print(f"\nSignatures:")
    for knot_id in sorted(analysis['knots'].keys()):
        sig = analysis['knots'][knot_id]['signature'][:16]
        print(f"  {knot_id}: {sig}...")
    
    return analysis


def main():
    """Main testing routine."""
    
    print("=" * 80)
    print("  RING-THEORETIC KNOT INVARIANTS - IMPLEMENTATION TEST")
    print("=" * 80)
    
    # Test 7-crossing family
    analysis_7 = test_7_crossing_family()
    
    # Test 8-crossing family
    analysis_8 = test_8_crossing_family()
    
    # Save results
    results = {
        '7_crossing_family': analysis_7,
        '8_crossing_family': analysis_8
    }
    
    with open("ring_theoretic_analysis.json", "w") as f:
        # Convert sets to lists for JSON serialization
        def convert_sets(obj):
            if isinstance(obj, set):
                return list(obj)
            elif isinstance(obj, dict):
                return {k: convert_sets(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_sets(item) for item in obj]
            else:
                return obj
        
        json.dump(convert_sets(results), f, indent=2)
    
    print("\n" + "=" * 80)
    print("  Results saved to: ring_theoretic_analysis.json")
    print("=" * 80)


if __name__ == "__main__":
    main()
