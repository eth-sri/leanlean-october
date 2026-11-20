module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Tactic.FunProp

@[expose] public section

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

variable {D Z : Type*} [TopologicalSpace D] [TopologicalSpace Z]

/-- The part of a cylinder consisting of selected time slices and a closed side. -/
abbrev CylinderSubspace (T : Set I) (S : Set D) := {z : I × D // z.1 ∈ T ∨ z.2 ∈ S}

variable {T : Set I} {S : Set D} (f : C(T × D, Z)) (H : C(I × S, Z))

noncomputable def cylinderPastingFun (z : CylinderSubspace T S) : Z :=
  if ht : z.1.1 ∈ T then f (⟨z.1.1, ht⟩, z.1.2)
  else H (z.1.1, ⟨z.1.2, z.2.resolve_left ht⟩)

private theorem pasteFun_side (h : ∀ t s, f (t, s.val) = H (t.val, s))
    (z : CylinderSubspace T S) (hz : z.1.2 ∈ S) :
    cylinderPastingFun f H z = H (z.1.1, ⟨z.1.2, hz⟩) := by
  unfold cylinderPastingFun
  split
  · rename_i ht
    exact h ⟨z.1.1, ht⟩ ⟨z.1.2, hz⟩
  · rfl

/-- Paste the slice and side maps on their closed union. -/
noncomputable def cylinderPasting (hT : IsClosed T) (hS : IsClosed S)
    (h : ∀ t s, f (t, s.val) = H (t.val, s)) : C(CylinderSubspace T S, Z) where
  toFun := cylinderPastingFun f H
  continuous_toFun := by
    let A : Set (CylinderSubspace T S) := {z | z.1.1 ∈ T}
    let B : Set (CylinderSubspace T S) := {z | z.1.2 ∈ S}
    have hAB : A ∪ B = Set.univ := Set.eq_univ_of_forall Subtype.property
    have hA : ContinuousOn (cylinderPastingFun f H) A := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous fun z : A => f (⟨z.1.1.1, z.2⟩, z.1.1.2) := by fun_prop
      convert hc using 1
      funext z
      exact dite_eq_left z.2
    have hB : ContinuousOn (cylinderPastingFun f H) B := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous fun z : B => H (z.1.1.1, ⟨z.1.1.2, z.2⟩) := by fun_prop
      convert hc using 1
      funext z
      exact pasteFun_side f H h z.1 z.2
    rw [← continuousOn_univ, ← hAB]
    exact hA.union_of_isClosed hB (hT.preimage (by fun_prop)) (hS.preimage (by fun_prop))

variable {f H} {hT : IsClosed T} {hS : IsClosed S}
  {h : ∀ t s, f (t, s.val) = H (t.val, s)}

theorem cylinderPasting_slice (z : CylinderSubspace T S) (ht : z.1.1 ∈ T) :
    cylinderPasting f H hT hS h z = f (⟨z.1.1, ht⟩, z.1.2) := dite_eq_left ht

theorem cylinderPasting_side (z : CylinderSubspace T S) (hs : z.1.2 ∈ S) :
    cylinderPasting f H hT hS h z = H (z.1.1, ⟨z.1.2, hs⟩) := pasteFun_side f H h z hs

end FiniteChains.RelativeAttachment
