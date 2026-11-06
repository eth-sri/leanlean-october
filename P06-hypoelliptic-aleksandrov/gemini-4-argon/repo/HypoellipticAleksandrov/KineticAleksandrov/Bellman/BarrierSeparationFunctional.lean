module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic

/-! # Separation of a continuous image subspace from the open positive cone -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/- The strictly positive cone in the uniform continuous-function space. -/
def bellmanPositiveCone : Set C(X, ℝ) := {f | ∀ x, 0 < f x}

/- Strict positivity is open in the uniform topology on a compact domain. -/
theorem bellmanPositiveCone_isOpen : IsOpen (bellmanPositiveCone (X := X)) := by
  simpa only [bellmanPositiveCone, mapsTo_univ_iff, mem_Ioi] using
    ContinuousMap.isOpen_setOfPred_mapsTo (X := X) (Y := ℝ) isCompact_univ isOpen_Ioi

omit [CompactSpace X] in
/- The strictly positive cone is convex. -/
theorem bellmanPositiveCone_convex : Convex ℝ (bellmanPositiveCone (X := X)) := by
  intro f hf g hg a b ha hb hab x
  change 0 < a * f x + b * g x
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb' : b = 1 := by linarith only [hab]
    simpa only [zero_mul, zero_add, hb', one_mul] using hg x
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hf x)) (mul_nonneg hb (hg x).le)

/- A subspace avoiding strict positivity has a normalized positive continuous separator. -/
end HypoellipticAleksandrov.KineticAleksandrov
