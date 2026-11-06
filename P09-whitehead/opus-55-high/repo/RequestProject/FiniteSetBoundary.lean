module

public import RequestProject.MomentAngle

@[expose] public section

/-! Finitely supported simplicial boundaries and the cubical coefficient convention. -/

namespace FiniteChains
variable {V : Type} [DecidableEq V] [LinearOrder V]

/-- The oriented boundary of a simplex, with each vertex ordered by its coordinate. -/
noncomputable def finiteSetBoundary : (Finset V →₀ ℤ) →ₗ[ℤ] (Finset V →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun σ => ∑ j ∈ σ,
    ((-1 : ℤ) ^ ((σ.erase j).filter (fun i => i < j)).card) •
      Finsupp.single (σ.erase j) 1)

@[simp] theorem finiteSetBoundary_single (σ : Finset V) (n : ℤ) :
    finiteSetBoundary (Finsupp.single σ n) = n • ∑ j ∈ σ,
      ((-1 : ℤ) ^ ((σ.erase j).filter (fun i => i < j)).card) •
        Finsupp.single (σ.erase j) 1 := by
  simp [finiteSetBoundary]

variable [Fintype V]

end FiniteChains
