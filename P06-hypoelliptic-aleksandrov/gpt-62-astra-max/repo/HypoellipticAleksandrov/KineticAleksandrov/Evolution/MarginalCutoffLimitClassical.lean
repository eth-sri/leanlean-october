module

import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.Parabolic.Transposition.HarmonicLimit
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import Mathlib
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalCutoffLimit

/-!
# The cutoff limit is a classical solution (Proposition 2.1)

Let `F` be a smooth compactly supported scalar datum and `u_N` classical terminal solutions for the
cutoff data `F_N(y, z) = F(y) χ((z)/(N+1))`.  By the growth tail comparison
(`classical_sub_le_growthBarrier`) the sequence `u_N(p)` is Cauchy at EVERY point of the past closed
cylinder, with `|V - u_N| ≤ ‖F‖ Φ_τ / (N + 1)²`; hence the limit `V` is a locally uniform limit of
functions continuous on the closed cylinder and is itself continuous there, including the terminal
and lateral faces (continuity BEFORE Hörmander).  The weak equation passes to the limit by bounded
convergence; the Hörmander input `` gives a smooth representative, which coincides with
the continuous `V` everywhere.  The limit is a classical terminal solution for the `z`-independent
datum `F(y)`; no covariance and no hypothesis on `B` beyond the standing ones are used.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set MeasureTheory Evolution
open scoped Topology MatrixOrder

theorem tendsto_quadratic_tail (K : ℝ) :
    Tendsto (fun N : ℕ => K / ((N : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
  exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))

/-- A sequence with the quadratic tail bound `|a M - a N| ≤ K / (N+1)²` (`M ≥ N`) is Cauchy. -/
theorem cauchySeq_of_quadratic_tail {a : ℕ → ℝ} {K : ℝ}
    (h : ∀ N M : ℕ, N ≤ M → |a M - a N| ≤ K / ((N : ℝ) + 1) ^ 2) : CauchySeq a := by
  refine cauchySeq_of_le_tendsto_0 (fun N => 2 * (K / (N + 1) ^ 2)) ?_ ?_
  · intro n m N hn hm
    have h1 := h N n hn
    have h2 := h N m hm
    rw [Real.dist_eq]
    calc |a n - a m| ≤ |a n - a N| + |a N - a m| := abs_sub_le _ _ _
      _ = |a n - a N| + |a m - a N| := by rw [abs_sub_comm (a N) (a m)]
      _ ≤ 2 * (K / ((N : ℝ) + 1) ^ 2) := by linarith
  · simpa using (tendsto_quadratic_tail K).const_mul 2

/-- **Cutoff limit** (Proposition 2.1).  The pointwise limit of classical
solutions `u_N` of the cutoff data `F(y) χ_N(z)` exists on the past closed cylinder and is a
classical terminal solution for the `z`-independent datum `F(y)`. -/
theorem classical_limit_of_quadratic_tails {n : ℕ} {lam Lam m L_b : ℝ}
    {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hΩo : IsOpen Ω) (hγ : Continuous γ) (hlam : 0 < lam) (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b) (hm : 0 < m)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    {τ C D : ℝ} (hC0 : 0 ≤ C) (hD : 0 ≤ D) {F : BoundedBorel (EvolutionAmbientState n)}
    {G : ℕ → BoundedBorel (EvolutionAmbientState n)}
    (hsub : ∀ {N M : ℕ}, N ≤ M → ∀ x, |G M x - G N x| ≤ D / ((N : ℝ)+1)^2 * (1+PDE.vecNormSq x.1+PDE.vecNormSq x.2))
    (ht : ∀ x, ∀ᶠ N : ℕ in atTop, G N x = F x)
    (u : ℕ → KineticPoint n → ℝ)
    (hu : ∀ N, IsClassicalTerminalSolution Ω γ B b τ (G N) (u N))
    (hbd : ∀ N, ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u N p| ≤ C) :
    ∃ V : KineticPoint n → ℝ,
      (∀ p ∈ evolutionPastClosedCylinder Ω γ τ, Tendsto (fun N => u N p) atTop (𝓝 (V p))) ∧
      IsClassicalTerminalSolution Ω γ B b τ F V := by
  let :=
    (KineticPoint.homeomorphProd n).isEmbedding.secondCountableTopology
  let S := evolutionPastClosedCylinder Ω γ τ
  let U := evolutionPastOpenCylinder Ω γ τ
  have hUS : U ⊆ S := fun p hp => ⟨hp.1.le, subset_closure hp.2⟩
  obtain ⟨Ct, hCt0, hCt⟩ := classical_sub_le_growthBarrier hΩo hγ hlam hB_ell hb_lipschitz
  -- tail bound
  have hTail : ∀ N M : ℕ, N ≤ M → ∀ p ∈ S,
      |u M p - u N p| ≤ D / (N + 1) ^ 2 * growthBarrier Ct τ p := by
    intro N M hNM p hp
    have hc : 0 ≤ D / (N + 1) ^ 2 := by positivity
    have h1 := hCt τ (G M) (G N) (u M) (u N) _ hc (hu M) (hu N)
      (fun x _ => (le_abs_self _).trans (hsub hNM x)) p hp
    have h2 := hCt τ (G N) (G M) (u N) (u M) _ hc (hu N) (hu M)
      (fun x _ => (le_abs_self _).trans (by
          rw [abs_sub_comm]
          exact hsub hNM x)) p hp
    rw [abs_le]
    constructor <;> linarith
  have hlimex : ∀ p ∈ S, ∃ v, Tendsto (fun N => u N p) atTop (𝓝 v) := fun p hp =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_quadratic_tail
      (K := D * growthBarrier Ct τ p) (fun N M hNM => by
        have := hTail N M hNM p hp
        rwa [div_mul_eq_mul_div] at this))
  let V := fun p => limUnder atTop (fun N => u N p)
  have hV := fun p hp =>
    tendsto_nhds_limUnder (hlimex p hp)
  -- the limit is bounded and satisfies the tail bound
  have hVbd := fun p hp =>
    le_of_tendsto' ((hV p hp).abs) (fun N => hbd N p hp)
  have hVtail : ∀ N : ℕ, ∀ p ∈ S,
      |V p - u N p| ≤ D / (N + 1) ^ 2 * growthBarrier Ct τ p := by
    intro N p hp
    refine le_of_tendsto ((hV p hp).sub_const (u N p) |>.abs) ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    exact hTail N M hM p hp
  -- continuity on the closed cylinder
  have hcont : ContinuousOn V S := by
    have hloc : TendstoLocallyUniformlyOn (fun N => u N) V atTop S := by
      rw [Metric.tendstoLocallyUniformlyOn_iff]
      intro ε hε x hx
      refine ⟨S ∩ {q | growthBarrier Ct τ q < growthBarrier Ct τ x + 1}, ?_, ?_⟩
      · exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
          ((continuous_growthBarrier Ct τ).continuousAt.eventually_lt continuousAt_const
            (lt_add_one _) |>.mono fun q hq => hq))
      · filter_upwards [(tendsto_quadratic_tail (D * (growthBarrier Ct τ x + 1))).eventually (gt_mem_nhds hε)] with N hN y hy
        rw [Real.dist_eq]
        have h1 := hVtail N y hy.1
        have h2 : D / (N + 1) ^ 2 * growthBarrier Ct τ y ≤
            D * (growthBarrier Ct τ x + 1) / (N + 1) ^ 2 := by
          rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hy.2.le hD
        linarith
    exact hloc.continuousOn (Eventually.of_forall fun N => (hu N).2.1).frequently
  -- terminal and lateral values
  have hterm : ∀ p ∈ evolutionTerminalClosure Ω γ τ,
      V p = F (p.position, p.velocity) := by
    intro p hp
    apply tendsto_nhds_unique (hV p ⟨hp.1.le,hp.1 ▸ hp.2⟩)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ht (p.position,p.velocity)] with N hN using (hN ▸ (hu N).2.2.2.2.1 p hp).symm
  have hlat : ∀ p ∈ evolutionLateralFrontier Ω γ τ, V p = 0 := by
    intro p hp
    refine tendsto_nhds_unique (hV p ⟨hp.1, frontier_subset_closure hp.2⟩) ?_
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun N => ?_)
    exact ((hu N).2.2.2.2.2 p hp).symm
  obtain ⟨hs,he⟩ := Transposition.kinetic_harmonic_limit hΩo hγ hlam hB_smooth hB_ell hb_smooth hm hb_coercive u V
    (fun i => (hu i).2.2.1) (fun i => (hu i).2.2.2.1) (fun i p hp => hbd i p (hUS hp)) (hcont.mono hUS) (fun p hp => hV p (hUS hp))
  exact ⟨V,hV,⟨C,hC0,hVbd⟩,hcont,hs,he,hterm,hlat⟩

end HypoellipticAleksandrov.KineticAleksandrov
