module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Uniform Cauchy convergence of actual finite Dirichlet solutions

The common-cylinder estimate is applied after fixing the error parameters. All
analytic hypotheses concern actual finite solutions; no Cauchy bound is assumed.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- A moving-ball Dirichlet exhaustion, with common coefficient and geometric bounds. -/
structure InnerBallExhaustion (n : ℕ) where
  lam : ℝ
  Lam : ℝ
  Lb : ℝ
  a : ℝ
  α : ℝ
  τ : ℝ
  r0 : ℝ
  d : ℝ
  L : ℝ
  C : ℝ
  ε : ℝ
  B : FullKineticCoefficient n
  b : PDE.Vec n → PDE.Vec n
  Γ : ℝ → PDE.Vec n
  F : BoundedBorel (EvolutionAmbientState n)
  hlam : 0 < lam
  hB : HasEverywhereLoewnerBounds lam Lam B
  hBs : IsSmoothFullKineticCoefficient B
  hBsym : IsSymmetricFullKineticCoefficient B
  hbs : IsSmoothDrift b
  hb : HasEuclideanLipschitzDrift Lb b
  haα : a < α
  hατ : α < τ
  hd : 0 < d
  hdr : d < r0 / 4
  hL : 0 ≤ L
  hε : 0 ≤ ε
  hε1 : ε ≤ 1
  hC : 0 ≤ C
  hΓ : Continuous Γ
  hFC : ∀ q, |F q| ≤ C
  hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
    4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)
  β : ℕ → ℝ
  R : ℕ → ℝ
  g : ℕ → ℝ → PDE.Vec n
  u : ℕ → TimeVelocity (n + n) → ℝ
  gap_pos : ∀ k, 0 < β k
  tendsto_gap : Tendsto β atTop (𝓝 0)
  tendsto_radius : Tendsto R atTop atTop
  smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)
  lipschitz : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|
  close : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2
  solution : ∀ k, IsClassicalBackwardDirichletSolution a τ
    (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
    (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
    (fun _ _ => 0) (fun _ _ => 0)
    (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)


namespace InnerBallExhaustion

variable {n : ℕ} (E : InnerBallExhaustion n)

abbrev domain := PDE.euclideanBall (0 : PDE.Vec n) E.r0
abbrev closedSlab := movingClosedSlab E.domain E.Γ E.α E.τ
abbrev innerClosed (δ S : ℝ) :=
  movingClosedSlab (PDE.euclideanBall 0 (E.r0 - δ)) E.Γ E.α E.τ ∩ {p | radialSq p ≤ S ^ 2}
abbrev approximant (k : ℕ) := straightenedPullback (E.g k) (E.u k)
noncomputable abbrev pointLimit (p : KineticPoint n) := limUnder atTop fun k => E.approximant k p

theorem radius_pos : 0 < E.r0 := by linarith [E.hd, E.hdr]

/-- The exhaustion limit on the original interior, extended by zero. -/
def limit (p : KineticPoint n) : ℝ := by
  classical
  exact if p.position ∈ movingDomain E.domain E.Γ p.time then E.pointLimit p else 0

theorem limit_eq {p : KineticPoint n} (hp : p.position ∈ movingDomain E.domain E.Γ p.time) :
    E.limit p = E.pointLimit p := by simp [limit, hp]

end InnerBallExhaustion

set_option maxHeartbeats 1200000 in
/-- Actual finite ellipsoid approximants are uniformly Cauchy on every bounded inner
cylinder. The transported radii only need to tend to infinity. -/
theorem uniformCauchySeqOn_innerBall_dirichlet
    {n : ℕ} (E : InnerBallExhaustion n)
    {δ0 S0 : ℝ} (hδ0 : 0 < δ0) (hδr : δ0 < E.r0) :
    UniformCauchySeqOn (E.approximant) atTop
      (E.innerClosed δ0 S0) := by
  let K := E.innerClosed δ0 S0
  have hr0 := E.radius_pos
  have hL := E.hL
  let cg := growthConstant n E.Lam (PDE.vecEuclideanNorm (E.b 0)) E.Lb
  obtain ⟨M0, hM0⟩ := (isCompact_movingClosedSlab_inter
    (Ω := PDE.euclideanBall 0 (E.r0 - δ0)) E.hΓ E.α E.τ S0).bddAbove_image
    (continuous_growthBarrier cg E.τ).continuousOn
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hΦ : ∀ p ∈ K, growthBarrier cg E.τ p ≤ M :=
    fun p hp => (hM0 ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro e he
  obtain ⟨δ, A, S, hδ, hδδ0, hδr0, hA, hAd, hgap, hS, herr⟩ :=
    exists_small_dirichlet_comparison_parameters
      (div_pos (by linarith : 0 < 1 + E.L) E.hlam) E.hd hδ0
      (by linarith : 0 < E.r0) E.hC hM he S0
  obtain ⟨R0, -, hcompare⟩ := exists_transportedRadius_dirichlet_cauchy_bound
    E.hlam E.hB E.hBs E.hbs E.hb E.haα E.hατ hA.le hAd hgap hδr0 E.hd E.hdr E.hL E.hε E.hε1 E.hC
    E.hΓ E.F E.hFC E.hsupp
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((E.tendsto_gap.eventually (gt_mem_nhds hA)).and
      (E.tendsto_radius.eventually (eventually_ge_atTop R0)))
  refine ⟨N, ?_⟩
  intro k hk l hl p hp
  let j (i : Fin 2) := if i = 0 then k else l
  have hj (i : Fin 2) : N ≤ j i := by dsimp [j]; split_ifs <;> assumption
  have hp' : p ∈ E.innerClosed δ S := by
    refine ⟨⟨hp.1.1, hp.1.2.1, ?_⟩, (show radialSq p ≤ S0 ^ 2 from hp.2).trans hS⟩
    apply mem_closure_movingDomain_iff.mpr
    apply closure_mono (PDE.euclideanBall_mono (by linarith : 0 ≤ E.r0 - δ0)
      (by linarith : E.r0 - δ0 ≤ E.r0 - δ))
    exact mem_closure_movingDomain_iff.mp hp.1.2.2
  have he' := hcompare (fun i => E.β (j i)) (fun i => E.R (j i))
    (fun i => ⟨E.gap_pos _, (hN _ (hj i)).1.le⟩) (fun i => (hN _ (hj i)).2)
    (fun i => E.g (j i)) (fun i => E.smooth _) (fun i => E.lipschitz _)
    (fun i => E.close _) (fun i => E.u (j i)) (fun i => E.solution _) p hp'
  have hbound : growthBarrier cg E.τ p / (1 + S ^ 2) ≤ M / (1 + S ^ 2) :=
    div_le_div_of_nonneg_right (hΦ p hp) (by positivity)
  have hfinal := he'.trans_lt ((mul_le_mul_of_nonneg_left
    (add_le_add hbound (le_refl _)) (mul_nonneg (by norm_num) E.hC)).trans_lt herr)
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simpa only [j, ite_true, h10, ite_false, Real.dist_eq] using hfinal

end HypoellipticAleksandrov.KineticAleksandrov
