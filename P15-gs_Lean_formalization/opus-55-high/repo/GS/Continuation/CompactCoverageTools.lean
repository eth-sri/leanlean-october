module

public import GS.Extensions.FiniteTopology
public import GS.Extensions.TransportedProjection
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section


/-!
# A compactness tool for neighbourhood coverage

Existing compactness proofs are reused, not replaced or duplicated.
The full-fibre lemma does NOT by itself close OriginalLocalCoverageGoal.
-/

noncomputable section
namespace GS.Continuation

/-- Every open set containing the FULL fibre over x captures a neighbourhood
of x inside the whole compact image. The full-fibre hypothesis is essential:
this lemma does not promote an arbitrary selected branch to a neighbourhood. -/
theorem compact_full_fibre_neighbourhood
    {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
    [T2Space K] [T2Space X] (f : K → X) (hf : Continuous f)
    (s : Set K) (hs : IsCompact s) (U : Set K) (hU : IsOpen U) (x : X)
    (hfull : ∀ k ∈ s, f k = x → k ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ f '' s → y ∈ f '' (s ∩ U) :=
  ⟨(f '' (s \ U))ᶜ, ((hs.diff hU).image hf).isClosed.isOpen_compl, by grind, by grind⟩

end GS.Continuation
