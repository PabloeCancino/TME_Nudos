"""
Fox Calculus for Free Groups.

Implements Free Group elements (Words) and Fox Derivatives.
Used for calculating Alexander Polynomials from Braids.
"""

from typing import List, Tuple, Dict
import sympy as sp

# Symbol for the Alexander variable
t = sp.Symbol('t')

class FreeGroupWord:
    """
    Represents a word in a Free Group F_n.
    Stored as a list of (generator_index, power).
    Generator indices are 1-based: 1, ..., n.
    """
    def __init__(self, word: List[Tuple[int, int]]):
        self.word = self._simplify(word)
        
    def _simplify(self, word: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
        """Simplify the word (combine adjacent same generators)."""
        if not word:
            return []
            
        new_word = []
        for gen, power in word:
            if power == 0:
                continue
            if new_word and new_word[-1][0] == gen:
                prev_gen, prev_pow = new_word.pop()
                new_pow = prev_pow + power
                if new_pow != 0:
                    new_word.append((gen, new_pow))
            else:
                new_word.append((gen, power))
        return new_word
        
    def __mul__(self, other: 'FreeGroupWord') -> 'FreeGroupWord':
        return FreeGroupWord(self.word + other.word)
        
    def inv(self) -> 'FreeGroupWord':
        """Inverse of the word."""
        return FreeGroupWord([(gen, -power) for gen, power in reversed(self.word)])
        
    def __repr__(self):
        return "".join([f"x_{g}^{p}" for g, p in self.word])

    @staticmethod
    def generator(i: int) -> 'FreeGroupWord':
        return FreeGroupWord([(i, 1)])
        
    @staticmethod
    def identity() -> 'FreeGroupWord':
        return FreeGroupWord([])

def fox_derivative(word: FreeGroupWord, var_index: int) -> sp.Expr:
    """
    Compute the Fox derivative of a word with respect to generator x_{var_index}.
    Result is an expression in Z[F_n], mapped to Z[t] by abelianization x_i -> t.
    
    Formulas:
    d(uv)/dx = d(u)/dx + u * d(v)/dx
    d(x_i)/dx_j = delta_{ij}
    d(x_i^{-1})/dx_j = -x_i^{-1} * delta_{ij}
    """
    # We compute the derivative and IMMEDIATELY apply the abelianization map x_k -> t.
    # This simplifies the expression handling.
    
    d_val = 0 # Zero polynomial
    current_term = 1 # Represents the prefix 'u' in the product rule, mapped to t^k
    
    for gen, power in word.word:
        # Term is x_gen^power
        # d(x^k)/dx = (1 + x + ... + x^{k-1}) if k > 0
        # d(x^{-k})/dx = -x^{-k} (1 + x + ... + x^{k-1}) if k > 0
        
        # In abelianization: x -> t
        
        if gen == var_index:
            if power > 0:
                # Sum_{m=0}^{power-1} t^m
                term_deriv = sum(t**m for m in range(power))
            else:
                # power = -k
                k = -power
                # -t^{-k} * Sum_{m=0}^{k-1} t^m
                term_deriv = - (t**power) * sum(t**m for m in range(k))
        else:
            term_deriv = 0
            
        # Add to total: current_term * term_deriv
        d_val += current_term * term_deriv
        
        # Update current_term: multiply by x_gen^power -> t^power
        current_term *= t**power
        
    return sp.simplify(d_val)

def apply_braid_action(n_strands: int, braid_word: List[Tuple[int, int]]) -> List[FreeGroupWord]:
    """
    Apply braid automorphism to generators x_1, ..., x_n.
    Returns the list of words [w_1, ..., w_n] where w_i = phi(x_i).
    
    Standard Artin Action (Right Action?):
    sigma_i:
      x_i     -> x_i x_{i+1} x_i^{-1}
      x_{i+1} -> x_i
      x_k     -> x_k (else)
      
    Inverse sigma_i^{-1}:
      x_i     -> x_{i+1}
      x_{i+1} -> x_{i+1}^{-1} x_i x_{i+1}
    """
    # Initialize generators
    generators = [FreeGroupWord.generator(i+1) for i in range(n_strands)]
    
    for gen_idx, power in braid_word:
        # gen_idx is 1-based index of sigma
        i = gen_idx - 1 # 0-based index for list
        
        # Apply sigma_i or sigma_i^{-1} |power| times
        # Note: Braid group is non-abelian, order matters.
        # Usually braid word is read left-to-right.
        # Action is applied sequentially.
        
        steps = abs(power)
        direction = 1 if power > 0 else -1
        
        for _ in range(steps):
            x_i = generators[i]
            x_next = generators[i+1]
            
            if direction == 1:
                # sigma_i
                # x_i -> x_i * x_{i+1} * x_i^{-1}
                # x_{i+1} -> x_i
                new_x_i = x_i * x_next * x_i.inv()
                new_x_next = x_i
            else:
                # sigma_i^{-1}
                # x_i -> x_{i+1}
                # x_{i+1} -> x_{i+1}^{-1} * x_i * x_{i+1}
                new_x_i = x_next
                new_x_next = x_next.inv() * x_i * x_next
                
            generators[i] = new_x_i
            generators[i+1] = new_x_next
            
    return generators
