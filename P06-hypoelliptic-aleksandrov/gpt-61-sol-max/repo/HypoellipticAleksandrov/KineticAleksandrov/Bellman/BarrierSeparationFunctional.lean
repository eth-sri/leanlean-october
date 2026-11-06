module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic
import Aesop



/-! # Separation of a continuous image subspace from the open positive cone -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The strictly positive cone in the uniform continuous-function space. -/
def bellmanPositiveCone : Set C(X, ℝ) := {f | ∀ x, 0 < f x}

/-- Strict positivity is open in the uniform topology on a compact domain. -/
theorem bellmanPositiveCone_isOpen : IsOpen (bellmanPositiveCone (X := X)) := by
  simpa only [bellmanPositiveCone, mapsTo_univ_iff, mem_Ioi] using
    ContinuousMap.isOpen_setOfPred_mapsTo (X := X) (Y := ℝ) isCompact_univ isOpen_Ioi

omit [CompactSpace X] in
/-- The strictly positive cone is convex. -/
theorem bellmanPositiveCone_convex : Convex ℝ (bellmanPositiveCone (X := X)) := by
  intro f hf g hg a b ha hb hab x
  change 0 < a * f x + b * g x
  rcases eq_or_lt_of_le ha with rfl | ha'
  · aesop
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hf x)) (mul_nonneg hb (hg x).le)

/-- A subspace avoiding strict positivity has a normalized positive continuous separator. -/
theorem exists_bellman_positive_functional (S : Submodule ℝ C(X, ℝ))
    (hno : Disjoint (bellmanPositiveCone (X := X)) (S : Set C(X, ℝ))) :
    ∃ L : C(X, ℝ) →L[ℝ] ℝ,
      L 1 = 1 ∧ (∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f) ∧
      ∀ f ∈ S, L f = 0 := by

  obtain ⟨l, u, hl, hu⟩ := geometric_hahn_banach_open bellmanPositiveCone_convex
    bellmanPositiveCone_isOpen S.topologicalClosure.convex (hno.closure_right bellmanPositiveCone_isOpen)
  have hu0 : u ≤ 0 := by simpa only [map_zero] using hu 0 S.topologicalClosure.zero_mem
  have hz : ∀ f ∈ S.topologicalClosure, l f = 0 := by
    intro f hf
    by_contra hn
    have hc := hu (((u - 1) / l f) • f) (S.topologicalClosure.smul_mem _ hf)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hn] at hc
    linarith only [hc]
  let g  := -l
  have hgp : ∀ f ∈ bellmanPositiveCone, 0 < g f := by
    intro f hf
    change 0 < -l f
    linarith only [hl f hf, hu0]
  have hg1  := hgp 1 (fun _ => zero_lt_one)

  refine ⟨(g 1)⁻¹ • g, ?_, ?_, ?_⟩
  · simp only [smul_apply, smul_eq_mul, inv_mul_cancel₀ hg1.ne']
  · intro f hf
    exact mul_nonneg (inv_nonneg.mpr hg1.le) ((show ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ g f by
        intro f hf
        by_contra hn
        have hneg  := lt_of_not_ge hn
        let c := (g 1 + 1) / (-g f)
        have hc : 0 < c := div_pos (by linarith only [hg1]) (neg_pos.mpr hneg)

        have h := hgp (1 + c • f) (by
            intro x
            change 0 < 1 + c * f x
            exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hc.le (hf x)))
        rw [map_add, map_smul, smul_eq_mul] at h
        have he : c * g f = -(g 1 + 1) := by
          dsimp [c]
          field_simp [hneg.ne]
        rw [he] at h
        linarith only [h]) f hf)
  · intro f hf

    simp only [smul_apply, smul_eq_mul, g, neg_apply, (hz f (S.le_topologicalClosure hf)), neg_zero, mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov
