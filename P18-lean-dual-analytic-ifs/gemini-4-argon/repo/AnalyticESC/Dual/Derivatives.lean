module

public import AnalyticESC.Dual.Projection

@[expose] public section

/-!
# Derivatives of the dual natural projection

Uniform bounds for `H_w^{(k)}` on `I` (Lemma 2.9), dependence on the common prefix (Lemma 2.11),
and uniform bounds for iterated derivatives of compositions `f_w`, obtained via Cauchy's estimate
on balls inside `B_ε`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- Cauchy's estimate on a disc of radius `ε / 2` around `x ∈ I` inside `B_ε`. -/
theorem norm_iteratedDeriv_le_of_nbhd {ε B : ℝ} (hε : 0 < ε) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hB : ∀ z ∈ nbhd ε, ‖g z‖ ≤ B)
    (k : ℕ) {x : ℝ} (hx : x ∈ I) :
    ‖iteratedDeriv k g x‖ ≤ k.factorial * B / (ε / 2) ^ k := by
  have hsub : closedBall (x : ℂ) (ε / 2) ⊆ nbhd ε :=
    (closedBall_subset_ball (half_lt_self hε)).trans (ball_subset_nbhd hx)
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (half_pos hε)
    ⟨hg.mono (ball_subset_closedBall.trans hsub),
      hg.continuousOn.mono (closure_ball_subset_closedBall.trans hsub)⟩
    fun z hz => hB z (hsub (sphere_subset_closedBall hz))

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- One family `C_k` serving Lemmas 2.9 and 2.11, the latter for every common prefix length
`m ≤ |i ∧ j|`. -/
theorem exists_iteratedDeriv_bounds :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      (∀ k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C k) ∧
      ∀ k, ∀ x ∈ I, ∀ (i j : Word N) (m : ℕ), (m : ℕ∞) ≤ i.commonPrefixLength j →
        ‖iteratedDeriv k (Φ.dualProj i) x - iteratedDeriv k (Φ.dualProj j) x‖ ≤
          2 * C k * Φ.cmax ^ m := by
  obtain ⟨M, hM0, hM, hMd⟩ := Φ.exists_dualProj_bounds
  have hε := Φ.ε_pos
  let C (k : ℕ) : ℝ := k.factorial * M / (ε / 2) ^ k
  refine ⟨C, fun k => by dsimp [C]; positivity,
    fun k x hx w => norm_iteratedDeriv_le_of_nbhd hε (Φ.differentiableOn_dualProj w)
      (fun z hz => hM w z (subset_closure hz)) k hx,
    fun k x hx i j m hm => ?_⟩
  have hnhd := (isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd hε hx)
  rw [← iteratedDeriv_fun_sub
    (((Φ.differentiableOn_dualProj i).analyticAt hnhd).contDiffAt)
    (((Φ.differentiableOn_dualProj j).analyticAt hnhd).contDiffAt)]
  exact (norm_iteratedDeriv_le_of_nbhd hε
    ((Φ.differentiableOn_dualProj i).sub (Φ.differentiableOn_dualProj j))
    (fun z hz => hMd i j m hm z (subset_closure hz)) k hx).trans_eq (by dsimp [C]; ring)

end IFS

end AnalyticESC
