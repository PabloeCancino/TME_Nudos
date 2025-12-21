# Walkthrough: Formalizing Schubert's Theorems and Reidemeister Moves

C:\Users\pablo\.gemini\antigravity\brain\5cb1387a-a017-45d2-b062-36138357d5e2

This walkthrough documents the process of formalizing Horst Schubert's theorems and Reidemeister moves in Lean 4, as part of the Structural Modular Knot Theory project.

## 1. Overview
The goal was to translate the mathematical content from `Teoremas_de_Horst_Schubert.md` and `Teorema_de_Reidemeister_y_Movimientos_de_Equivalencia_de_Nudos.md` into Lean 4 code. This involved creating two new modules and a bridge:
- `TMENudos/Reidemeister.lean`: Formalizing Reidemeister moves and their properties.
- `TMENudos/Schubert.lean`: Formalizing Schubert's decomposition theorem, companion theorem, and bridge number additivity.
- `TMENudos/Bridge.lean`: Connecting the rational knot theory (Basic.lean) with the general knot theory.

## 2. Formalization Details

### Reidemeister Moves (`Reidemeister.lean`)
We defined the combinatorial structure of knot diagrams using `KnotConfig`.
- **Key Definitions**:
  - `KnotConfig (n : ℕ)`: Represents a knot diagram with `n` crossings.
  - `ReidemeisterMove`: Inductive type for R1, R2, R3 moves.
  - `topologically_equivalent`: Defined via the existence of a sequence of Reidemeister moves.
- **Unification (New)**:
  - `Diagram`: A Sigma type `(n : ℕ) × KnotConfig n` representing any diagram.
  - `DiagramSetoid`: A `Setoid` instance on `Diagram` using Reidemeister equivalence.

### Schubert's Theorems (`Schubert.lean`)
We formalized the high-level algebraic properties of knots.
- **Key Definitions**:
  - `Knot`: Originally an axiom, now defined as `Quotient DiagramSetoid`. This grounds the abstract theory in the combinatorial model.
  - `connected_sum` (`#`): Operation to combine knots.
  - `is_prime`: Definition of prime knots.
  - `bridge_number`: Axiomatic invariant.
- **Theorems**:
  - `schubert_unique_factorization`: Every knot has a unique decomposition into prime knots.
  - `schubert_companion_theorem`: Relates satellite knots to their companions.
  - `schubert_bridge_number_additivity`: `b(K₁ # K₂) = b(K₁) + b(K₂) - 1`.
- **Challenges & Solutions**:
  - **Precedence Issues**: The notation for connected sum (`#`) and isotopy (`≅`) had conflicting precedence, causing parsing errors like `type expected`. We fixed this by setting explicit precedence: `infixl:65 " # "` and `infix:50 " ≅ "`.
  - **Parsing Errors**: Some theorem signatures (e.g., `bridge_number_isotopy`) caused parsing errors due to subtle syntax issues or interaction with previous lines. Cleaning up the file and ensuring proper termination of previous commands resolved this.

### Integration (`Bridge.lean`)
We created a bridge to connect the rational knot theory (`Basic.lean`) with the general theory.
- **Key Definitions**:
  - `rational_to_diagram`: Axiom converting a `RationalConfiguration` to a `Diagram`.
  - `rational_to_knot`: Function lifting this to the `Knot` quotient.
  - `rational_equivalence_preserves_isotopy`: Axiom asserting consistency.

## 3. Integration
All modules were integrated into the main project by adding imports to `TMENudos.lean`.
- `import TMENudos.Reidemeister`
- `import TMENudos.Schubert`
- `import TMENudos.Bridge`

## 4. Verification
The project was successfully built using `lake build`.
- **Result**: `Build completed successfully`.
- **Note**: Many theorems are currently proven with `sorry`, which is expected at this stage of formalization. The focus was on establishing the correct definitions and theorem statements (syntax and type correctness).

## 5. Future Work
- Replace `sorry` with actual proofs.
- Connect `Reidemeister.lean` definitions (combinatorial) with `Schubert.lean` axioms (topological).
- Implement the `jones_polynomial` calculation (currently commented out due to complexity).
