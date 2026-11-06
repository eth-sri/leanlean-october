module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import GS.CompactFibres
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.OrbitCompact
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A compactness tool for neighbourhood coverage

Existing compactness proofs are reused, not replaced or duplicated.
The full-fibre lemma does NOT by itself close OriginalLocalCoverageGoal.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

/-- Every open set containing the FULL fibre over x captures a neighbourhood
of x inside the whole compact image. The full-fibre hypothesis is essential:
this lemma does not promote an arbitrary selected branch to a neighbourhood. -/
theorem compact_full_fibre_neighbourhood
    {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
    [T2Space K] [T2Space X] (f : K → X) (hf : Continuous f)
    (s : Set K) (hs : IsCompact s) (U : Set K) (hU : IsOpen U) (x : X)
    (hfull : ∀ k ∈ s, f k = x → k ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ f '' s → y ∈ f '' (s ∩ U) := by
  have hc : IsCompact (s \ U) :=
    hs.of_isClosed_subset (hs.isClosed.inter hU.isClosed_compl) (fun _ h => h.1)
  have himg : IsClosed (f '' (s \ U)) := (hc.image hf).isClosed
  refine ⟨(f '' (s \ U))ᶜ, himg.isOpen_compl, ?_, ?_⟩
  · rintro ⟨k, hk, he⟩
    exact hk.2 (hfull k hk.1 he)
  · intro y hy
    rintro ⟨k, hk, rfl⟩
    refine ⟨k, ⟨hk, ?_⟩, rfl⟩
    by_contra hn
    exact hy ⟨k, ⟨hk, hn⟩, rfl⟩

end GS.Continuation
