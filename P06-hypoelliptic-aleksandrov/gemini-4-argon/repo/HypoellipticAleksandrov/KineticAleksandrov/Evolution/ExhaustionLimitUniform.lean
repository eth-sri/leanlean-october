module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import Mathlib.Topology.UniformSpace.UniformApproximation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
import Mathlib.Topology.MetricSpace.Cauchy
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyComparison
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRadius

/-!
# Locally uniform limits of actual Dirichlet approximants

Completeness is applied to the proved uniform Cauchy property. The pointwise
limit is the same function on all inner cylinders, irrespective of their sizes.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/- The actual finite Dirichlet sequence converges uniformly on every bounded inner
cylinder to its pointwise limit. -/
theorem tendstoUniformlyOn_innerBall_dirichlet
    {n lam Lam Lb B b}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ r0 δ0 S0 d L C ε } (haα : a < α) (hατ : α < τ)
    (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ } (hΓ : Continuous Γ)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ))
    (β R : ℕ → ℝ) (hβpos : ∀ k, 0 < β k)
    (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop)
    (g : ℕ → ℝ → PDE.Vec n) (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k))
    (hgL : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|)
    (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2)
    (u : ℕ → TimeVelocity (n + n) → ℝ)
    (hu : ∀ k, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)) :
    TendstoUniformlyOn (fun k => straightenedPullback (g k) (u k))
      (fun p => limUnder atTop (fun k => straightenedPullback (g k) (u k) p)) atTop
      (movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ S0 ^ 2}) := by
  have h : UniformCauchySeqOn (fun k => straightenedPullback (g k) (u k)) atTop
      (movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ (S0) ^ 2}) := by
    let S0 := (S0)
    let K := movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
      {p | radialSq p ≤ S0 ^ 2}
    let cg := growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb
    obtain ⟨M0, hM0⟩ := (isCompact_movingClosedSlab_inter
      (Ω := PDE.euclideanBall 0 (r0 - δ0)) hΓ α τ S0).bddAbove_image
      (continuous_growthBarrier cg τ).continuousOn
    let M := max M0 0
    have hM : 0 ≤ M := le_max_right _ _
    have hΦ : ∀ p ∈ K, growthBarrier cg τ p ≤ M :=
      fun p hp => (hM0 ⟨p, hp, rfl⟩).trans (le_max_left _ _)
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro e he
    obtain ⟨δ, A, S, hδ, hδδ0, hδr0, hA, hAd, hgap, hS, herr⟩ :=
      exists_small_dirichlet_comparison_parameters
        (div_pos (by linarith : 0 < 1 + L) hlam) hd hδ0
        (by linarith : 0 < r0) hC hM he S0
    obtain ⟨R0, -, hcompare⟩ : ∃ R0 : ℝ, 0 < R0 ∧ ∀ (β R : Fin 2 → ℝ),
      (∀ i, 0 < β i ∧ β i ≤ A) → (∀ i, R0 ≤ R i) →
      ∀ (g : Fin 2 → ℝ → PDE.Vec n),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) →
      (∀ i s t, PDE.vecEuclideanNorm (g i s - g i t) ≤ L * |s - t|) →
      (∀ i s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g i s - Γ s) ≤ β i / 2) →
      ∀ (u : Fin 2 → TimeVelocity (n + n) → ℝ),
      (∀ i, IsClassicalBackwardDirichletSolution a τ
        (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β i) (R i)))
        (straightenedCoefficient B (g i) ε) (straightenedDrift b (g i))
        (fun _ _ => 0) (fun _ _ => 0)
        (fun x => F (g i τ + spatialY x, spatialZ x)) (fun _ => 0) (u i)) →
      ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
        {q | radialSq q ≤ S ^ 2},
        |straightenedPullback (g 0) (u 0) p - straightenedPullback (g 1) (u 1) p| ≤
          2 * C * (growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) τ p /
            (1 + S ^ 2) + barrierW (collarKappa L lam) (δ + 3 / 2 * A) /
              barrierW (collarKappa L lam) d) := by
      have hA := hA.le
      obtain ⟨R0, hR0, hsize⟩ := exists_transportedRadius_common_innerCylinder
        (sub_pos.mpr hδr0) (by linarith : 0 ≤ A / 2)
        (by linarith : (r0 - δ) + A / 2 < r0 - A) S
      refine ⟨R0, hR0, ?_⟩
      intro β R hβ hR g hg hgL hclose u hu p hp
      have hr (i : Fin 2) : 0 < r0 - β i := by linarith [(hβ i).2]
      have hd' (i : Fin 2) : d < r0 - β i := by linarith [(hβ i).2]
      have hc (i : Fin 2) (s : ℝ) (hs : s ∈ Icc α τ) :
          PDE.vecEuclideanNorm (g i s - Γ s) ≤ A / 2 :=
        (hclose i s hs).trans (by linarith [(hβ i).2])
      have ht (i : Fin 2) : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
          2 * d ≤ (r0 - β i) - PDE.vecEuclideanNorm (q.1 - g i τ) :=
        terminal_support_margin_of_innerBall_close ((hβ i).2.trans hAd) hsupp
          (hclose i τ ⟨hατ.le, le_rfl⟩)
      have he := abs_sub_le_common_innerCylinder_straightened_dirichlet
        hlam hB hBs hbs hb haα hατ (sub_pos.mpr hδr0)
        (by linarith : r0 - δ ≤ r0) (by linarith : 0 ≤ A / 2)
        hd hL hε hε1 hC hΓ g (fun i => r0 - β i) R hg hgL hr
        (fun i => hR0.trans_le (hR i)) (fun i => by linarith [(hβ i).1]) hd' hc
        (fun i => hsize _ _ (by linarith [(hβ i).2]) (hR i)) F hFC ht u hu p hp
      have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
      have hW := barrierW_pos hκ hd
      have hm : barrierW (collarKappa L lam) (r0 - (r0 - δ) + A / 2) ≤
          barrierW (collarKappa L lam) (δ + 3 / 2 * A) := by
        have hb' : r0 - (r0 - δ) + A / 2 ≤ δ + 3 / 2 * A := by linarith
        rcases hb'.lt_or_eq with h | h
        · exact (barrierW_strictMono hκ h).le
        · rw [h]
      exact he.trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (div_le_div_of_nonneg_right hm hW.le)) (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((hβlim.eventually (gt_mem_nhds hA)).and
        (hRlim.eventually (eventually_ge_atTop R0)))
    refine ⟨N, ?_⟩
    intro k hk l hl p hp
    let j (i : Fin 2) := if i = 0 then k else l
    have hj (i : Fin 2) : N ≤ j i := by dsimp [j]; split_ifs <;> assumption
    have hp' : p ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
        {p | radialSq p ≤ S ^ 2} := by
      refine ⟨⟨hp.1.1, hp.1.2.1, ?_⟩, (show radialSq p ≤ S0 ^ 2 from hp.2).trans hS⟩
      apply mem_closure_movingDomain_iff.mpr
      apply closure_mono (PDE.euclideanBall_mono (by linarith : 0 ≤ r0 - δ0)
        (by linarith : r0 - δ0 ≤ r0 - δ))
      exact mem_closure_movingDomain_iff.mp hp.1.2.2
    have he' := hcompare (fun i => β (j i)) (fun i => R (j i))
      (fun i => ⟨hβpos _, (hN _ (hj i)).1.le⟩) (fun i => (hN _ (hj i)).2)
      (fun i => g (j i)) (fun i => hg _) (fun i => hgL _)
      (fun i => hclose _) (fun i => u (j i)) (fun i => hu _) p hp'
    have hbound : growthBarrier cg τ p / (1 + S ^ 2) ≤ M / (1 + S ^ 2) :=
      div_le_div_of_nonneg_right (hΦ p hp) (by positivity)
    have hfinal := he'.trans_lt ((mul_le_mul_of_nonneg_left
      (add_le_add hbound (le_refl _)) (by positivity)).trans_lt herr)
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simpa only [j, ite_true, h10, ite_false, Real.dist_eq] using hfinal
  exact h.tendstoUniformlyOn_of_tendsto (fun p hp => (h.cauchySeq hp).tendsto_limUnder)

/- The actual exhaustion limit is continuous and has the original uniform bound on
every bounded inner cylinder. -/
theorem continuousOn_bounded_innerBall_dirichlet_limit
    {n lam Lam Lb B b}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ r0 δ0 S0 d L C ε } (haα : a < α) (hατ : α < τ)
    (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ } (hΓ : Continuous Γ)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ))
    (β R : ℕ → ℝ) (hβpos : ∀ k, 0 < β k)
    (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop)
    (g : ℕ → ℝ → PDE.Vec n) (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k))
    (hgL : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|)
    (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2)
    (u : ℕ → TimeVelocity (n + n) → ℝ)
    (hu : ∀ k, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)) :
    ContinuousOn (fun p => limUnder atTop
      (fun k => straightenedPullback (g k) (u k) p))
      (movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ S0 ^ 2}) ∧
    ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
      {p | radialSq p ≤ S0 ^ 2},
      |limUnder atTop (fun k => straightenedPullback (g k) (u k) p)| ≤ C := by
  let K := movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  have hU := tendstoUniformlyOn_innerBall_dirichlet (S0 := S0)
    hlam hB hBs hbs hb haα hατ hδ0 hδr hd hdr hL hε hε1 hC hΓ F hFC hsupp
    β R hβpos hβlim hRlim g hg hgL hclose u hu
  have hmem := eventually_innerCylinder_mem_straightenedEllipsoid (S := S0)
    hδ0 hδr β R hβlim hRlim g hclose
  have hclosed (k : ℕ) (hk : 0 < r0 - β k ∧ 0 < R k ∧
      ∀ p ∈ K, (straightenedPoint (g k) p).2 ∈
        openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k))) :
      MapsTo (straightenedPoint (g k)) K
        (scalarParabolicClosedCylinder a τ
          (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))) :=
    fun p hp => ⟨⟨haα.le.trans hp.1.1, hp.1.2.1⟩, subset_closure (hk.2.2 p hp)⟩
  refine ⟨hU.continuousOn ?_, fun p hp => ?_⟩
  · exact (hmem.mono fun k hk =>
      (hu k).1.comp (continuous_straightenedPoint (hg k).continuous).continuousOn
        (hclosed k hk)).frequently
  · apply le_of_tendsto (hU.tendsto_at hp |>.abs)
    exact hmem.mono fun k hk => abs_le_straightened_dirichlet
      hlam hB hBs hbs (haα.trans hατ) hk.1 hk.2.1 (hg k) hε F (u k) (hu k)
      hC hFC _ (hclosed k hk hp)

end HypoellipticAleksandrov.KineticAleksandrov
