import RequestProject.SquareComplexPi1


/-!
# Monodromy of a covering of square complexes

For a covering `p : T → B` of square complexes, lifting a walk of the base which starts at
`p x₀` gives a walk of `T` starting at `x₀`; its end point depends only on the homotopy class of
the walk.  This defines the **monodromy map**

`FiniteChains.SquareComplex.IsCovering.monodromy : B.Pi1 (p x₀) → Vt`,

which takes values in the fibre over `p x₀`.  The main theorem,
`FiniteChains.SquareComplex.IsCovering.monodromy_bijective`, says that for a connected and simply
connected covering complex the monodromy map is a bijection from the fundamental group of the
base onto the fibre — the combinatorial form of the classical identification
`π₁(B) ≅ p⁻¹(b₀)` for the universal covering.
-/

