module

public import GS.Spectral.Singularity
public import GS.Topology.PlaneCone

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Topological singularities of the original three-factor GS family

The public statements here use the scalar perfect shuffle and consecutive
block sizes `2, q, 2` from `GS.localFamily`.  A point is non-Euclidean in the
actual subspace topology; no differentiability or homology assumption is
made.

The general theorem does not require determinant one.  An explicit
Householder matrix supplies a non-Euclidean point in every size `2q`, `q ≥ 3`.
Thus the conclusion is instantiated for all dimensions in the theorem, not
only for the first example `q = 3`.
-/

set_option autoImplicit false

noncomputable section

open Matrix GS.Local GS.RankLocus

namespace GS.Results
open GS.Spectral

/-- The rank-at-most-one locus for two rows has a topological singularity at
zero, even after taking a product with any finite-dimensional real space. -/
theorem cone_rankOne_not_euclidean (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) := by
  intro hE
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) :=
    {p | p.2.rank ≤ 1}
  let c : Space e 2 (Fin d) ≃ₜ S := {
    toFun p := ⟨(p.1,p.2.val),p.2.property⟩, invFun p := (p.val.1,⟨p.val.2,p.property⟩)
    left_inv _ := rfl, right_inv _ := rfl, continuous_toFun := by fun_prop, continuous_invFun := by fun_prop }
  exact two_row_bad e d hd ((homeo c (0,tip)).symm.move (of_subset hE))

/-- Both the membership and the obstruction come from the same spectral patch. -/
theorem gs_singularity {q : ℕ} (hq : 3 ≤ q) (Q : Mat q) (hQ : Orthogonal Q) (hne : ∀ i j, Q i j ≠ 0) :
    basePoint Q ∈ localFamily q ∧ ¬EuclideanAtSubset (localFamily q) (basePoint Q) := by
  let o : Fin q := ⟨0,by omega⟩
  let A : U ℝ q := ⟨Q,hQ⟩
  let e : (ℝ × ℝ) ≃L[ℝ] V 2 := .ofFinrankEq (by simp [V])
  exact family_singularity A o hne e fun n => two_row_bad n _ (real_width A o hne hq)

/-- Reflection perpendicular to the all-ones vector: `I - (2/q) J`. -/
lemma reflection (𝕜 : Type) [RCLike 𝕜] {q : ℕ} (hq : 3 ≤ q) : ∃ Q : U 𝕜 q, ∀ i j, Q.val i j ≠ 0 := by
  let C : Isometric.Square 𝕜 q := fun _ _ => 2 / (q : 𝕜)
  have hn : (q : 𝕜) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hc : C*C = C+C := by ext; simp [C,mul_apply]; field_simp; ring
  refine ⟨⟨1-C,Isometric.IsU.of_left ?_⟩,?_⟩
  · have eq : Cᴴ = C := by ext; simp [C,conjTranspose_apply,RCLike.star_def]
    rw [conjTranspose_sub,conjTranspose_one,eq]; noncomm_ring [hc]
  · intro i j; change (1 - C) i j ≠ 0
    simp [C,one_apply]; split_ifs <;> field_simp
    all_goals try norm_num
    apply sub_ne_zero.mpr; exact_mod_cast (by omega : q ≠ 2)

/-- Every three-factor family of the specified size has a topological
singularity. In particular, it cannot be a topological manifold without
boundary with its induced matrix topology. -/
theorem exists_nonEuclidean_point (q : ℕ) (hq : 3 ≤ q) :
    ∃ M : Mat (q * 2), M ∈ localFamily q ∧
      ¬ EuclideanAtSubset (localFamily q) M := by
  obtain ⟨Q,h⟩ := reflection ℝ hq; exact ⟨_,gs_singularity hq _ Q.property h⟩

end GS.Results
