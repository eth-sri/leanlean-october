module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRegion
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierBound
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRadius
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder


/-- Actual finite ellipsoid solutions satisfy the common inner-cylinder Cauchy bound.
All containment premises are explicit radius inequalities; all analytic bounds are proved. -/
theorem abs_sub_le_common_innerCylinder_straightened_dirichlet
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ ρ r0 η S d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hρ : 0 < ρ) (hρr0 : ρ ≤ r0) (hη : 0 ≤ η)
    (hd : 0 < d) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : Continuous Γ)
    (g : Fin 2 → ℝ → PDE.Vec n) (r R : Fin 2 → ℝ)
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i))
    (hgL : ∀ i s t, PDE.vecEuclideanNorm (g i s - g i t) ≤ L * |s - t|)
    (hr : ∀ i, 0 < r i) (hR : ∀ i, 0 < R i) (hrr0 : ∀ i, r i ≤ r0)
    (hdr : ∀ i, d < r i)
    (hclose : ∀ i s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g i s - Γ s) ≤ η)
    (hsize : ∀ i, (ρ + η) ^ 2 / (r i) ^ 2 + S ^ 2 / (R i) ^ 2 < 1)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ i q, q ∈ tsupport (F : EvolutionAmbientState n → ℝ) →
      2 * d ≤ r i - PDE.vecEuclideanNorm (q.1 - g i τ))
    (u : Fin 2 → TimeVelocity (n + n) → ℝ)
    (hu : ∀ i, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r i) (R i)))
      (straightenedCoefficient B (g i) ε) (straightenedDrift b (g i))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g i τ + spatialY x, spatialZ x)) (fun _ => 0) (u i)) :
    ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 ρ) Γ α τ ∩ {q | radialSq q ≤ S ^ 2},
      |straightenedPullback (g 0) (u 0) p - straightenedPullback (g 1) (u 1) p| ≤
        2 * C * (growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) τ p /
          (1 + S ^ 2) + barrierW (collarKappa L lam) (r0 - ρ + η) /
            barrierW (collarKappa L lam) d) := by
  let K := movingClosedSlab (PDE.euclideanBall 0 ρ) Γ α τ ∩ {q | radialSq q ≤ S ^ 2}
  let A := movingActiveSlab (PDE.euclideanBall 0 ρ) Γ α τ ∩ {q | radialSq q < S ^ 2}
  let v (i : Fin 2) := straightenedPullback (g i) (u i)
  let cg := growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb
  let Φ := growthBarrier (n := n) cg τ
  let Q := barrierW (collarKappa L lam) (r0 - ρ + η) / barrierW (collarKappa L lam) d
  let E := 2 * C * Q
  let k := 2 * C / (1 + S ^ 2)
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hW := barrierW_pos hκ hd
  have hQ : 0 ≤ Q := div_nonneg (by
    unfold barrierW
    have he : Real.exp (-collarKappa L lam * (r0 - ρ + η)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    exact div_nonneg (by linarith) hκ.le) hW.le
  have hE : 0 ≤ E := mul_nonneg (by positivity) hQ
  have hk : 0 ≤ k := div_nonneg (by positivity) (by positivity)
  have hcg : 0 ≤ cg := by
    dsimp only [cg, growthConstant]
    have := PDE.vecEuclideanNorm_nonneg (b 0)
    positivity
  have hmem (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) :
      (straightenedPoint (g i) p).2 ∈
        openEllipsoid (straightenedEllipsoidMatrix n (r i) (R i)) :=
    mem_straightenedEllipsoid_of_common_innerCylinder hρ (hr i) (hR i)
      (hclose i) (hsize i) hp
  have hclosed (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) :
      straightenedPoint (g i) p ∈ scalarParabolicClosedCylinder a τ
        (openEllipsoid (straightenedEllipsoidMatrix n (r i) (R i))) :=
    ⟨⟨haα.le.trans hp.1.1, hp.1.2.1⟩, subset_closure (hmem i p hp)⟩
  have hactive : A ⊆ K := fun p hp =>
    ⟨⟨hp.1.1, hp.1.2.1.le, subset_closure hp.1.2.2⟩,
      (show radialSq p ≤ S ^ 2 from (show radialSq p < S ^ 2 from hp.2).le)⟩
  have hvc (i : Fin 2) : ContinuousOn (v i) K :=
    (hu i).1.comp (continuous_straightenedPoint (hg i).continuous).continuousOn (hclosed i)
  have hreg (i : Fin 2) (p : KineticPoint n) (hp : p ∈ A) :
      IsSliceRegularAt (v i) p ∧ viscousTransportedOperator B b ε (v i) p = 0 :=
    straightenedPullback_dirichlet_sliceRegular
      (isOpen_straightenedEllipsoid n (hr i) (hR i)) (hg i) (hu i) p
      ⟨⟨haα.trans_le hp.1.1, hp.1.2.1⟩, hmem i p (hactive hp)⟩
  have hbound (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) : |v i p| ≤ C :=
    abs_le_straightened_dirichlet hlam hB hBs hbs (haα.trans hατ) (hr i) (hR i)
      (hg i) hε F (u i) (hu i) hC hFC _ (hclosed i p hp)
  have hcollar (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K)
      (hfr : p.position ∈ frontier (movingDomain (PDE.euclideanBall 0 ρ) Γ p.time)) :
      |v i p| ≤ C * Q := by
    have he := abs_le_min_collar_straightened_dirichlet hlam hB hBs hbs haα hατ
      (hr i) (hR i) hd (hdr i) (hg i) hL (hgL i) hε hC F hFC (hsupp i) (u i) (hu i) p
      ⟨⟨hp.1.1, hp.1.2.1⟩, subset_closure (hmem i p hp)⟩
    have hb' := distance_to_approximating_boundary_le_of_common_frontier hρ (hrr0 i)
      (hclose i p.time ⟨hp.1.1, hp.1.2.1⟩) hfr
    have hw : barrierW (collarKappa L lam)
        (r i - PDE.vecEuclideanNorm (p.position - g i p.time)) ≤
        barrierW (collarKappa L lam) (r0 - ρ + η) := by
      rcases hb'.lt_or_eq with h | h
      · exact (barrierW_strictMono hκ h).le
      · rw [h]
    exact he.trans (mul_le_mul_of_nonneg_left
      ((min_le_right _ _).trans (div_le_div_of_nonneg_right hw hW.le)) hC)
  have hφ (p : KineticPoint n) : 0 < Φ p := growthBarrier_pos cg τ p
  have hφreg (p : KineticPoint n) : IsSliceRegularAt Φ p := isSliceRegularAt_growthBarrier cg τ p
  have hφop (p : KineticPoint n) : viscousTransportedOperator B b ε Φ p ≤ -Φ p :=
    viscousTransportedOperator_growthBarrier_le hε1 (fun s y z => (hB s y z).2) hb τ p
  have hterm (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) (hτ : p.time = τ) :
      v i p = F (p.position, p.velocity) := by
    have he := (hu i).2.2.2.1 (straightenedPoint (g i) p).2 (hclosed i p hp).2
    simpa only [v, straightenedPullback, straightenedPoint, hτ,
      spatialY_spatialPack, spatialZ_spatialPack, add_sub_cancel] using he
  have side (s : ℝ) (hs : s = 1 ∨ s = -1) :
      ∀ p ∈ K, s * (v 0 p - v 1 p) ≤ E + k * Φ p := by
    have hmax := bounded_comparison (b := b) (PDE.isOpen_euclideanBall 0 ρ) hΓ hlam hB hε
      (a := α) (u := fun p => s * (v 0 p - v 1 p) - E - k * Φ p)
      ((((hvc 0).sub (hvc 1)).const_smul s).sub continuousOn_const |>.sub
        ((continuous_const.mul (continuous_growthBarrier cg τ)).continuousOn))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      have := hmax p hp
      linarith
    · intro p hp
      exact ((((hreg 0 p hp).1.sub (hreg 1 p hp).1).const_mul s).sub
        (IsSliceRegularAt.const E p)).sub ((hφreg p).const_mul k)
    · intro p hp
      rw [viscousTransportedOperator_sub
          ((((hreg 0 p hp).1.sub (hreg 1 p hp).1).const_mul s).sub
            (IsSliceRegularAt.const E p)) ((hφreg p).const_mul k),
        viscousTransportedOperator_sub
          (((hreg 0 p hp).1.sub (hreg 1 p hp).1).const_mul s) (IsSliceRegularAt.const E p),
        viscousTransportedOperator_const_mul s ((hreg 0 p hp).1.sub (hreg 1 p hp).1),
        viscousTransportedOperator_sub (hreg 0 p hp).1 (hreg 1 p hp).1,
        (hreg 0 p hp).2, (hreg 1 p hp).2, viscousTransportedOperator_const,
        viscousTransportedOperator_const_mul k (hφreg p)]
      have hn := mul_nonpos_of_nonneg_of_nonpos hk (le_trans (hφop p) (by linarith [hφ p]))
      linarith
    · intro p hp hτ
      rw [hterm 0 p hp hτ, hterm 1 p hp hτ, sub_self, mul_zero]
      have := mul_nonneg hk (hφ p).le
      linarith
    · intro p hp hfr
      have h0 := abs_le.mp (hcollar 0 p hp hfr)
      have h1 := abs_le.mp (hcollar 1 p hp hfr)
      have hn := mul_nonneg hk (hφ p).le
      rcases hs with rfl | rfl <;> linarith
    · intro p hp he
      have h0 := abs_le.mp (hbound 0 p hp)
      have h1 := abs_le.mp (hbound 1 p hp)
      have hdom := one_add_radialSq_le_growthBarrier hcg hp.1.2.1
      rw [he] at hdom
      have hb' : 2 * C ≤ k * Φ p := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left hdom (by positivity)
      rcases hs with rfl | rfl <;> linarith
  intro p hp
  have h0 := side 1 (Or.inl rfl) p hp
  have h1 := side (-1) (Or.inr rfl) p hp
  have he : E + k * Φ p = 2 * C * (Φ p / (1 + S ^ 2) + Q) := by
    ring
  rw [he] at h0 h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩



/-- The manuscript Cauchy estimate for actual inner-ball ellipsoid approximants, with
constant independent of both approximation indices and transported truncation radii. -/
theorem exists_transportedRadius_dirichlet_cauchy_bound
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ r0 δ A S d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hA : 0 ≤ A) (hAd : A ≤ d) (hgap : 3 / 2 * A < δ) (hδr : δ < r0)
    (hd : 0 < d) (hdr : d < r0 / 4) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : Continuous Γ)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ (β R : Fin 2 → ℝ),
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
  obtain ⟨R0, hR0, hsize⟩ := exists_transportedRadius_common_innerCylinder
    (sub_pos.mpr hδr) (by linarith : 0 ≤ A / 2)
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
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hm : barrierW (collarKappa L lam) (r0 - (r0 - δ) + A / 2) ≤
      barrierW (collarKappa L lam) (δ + 3 / 2 * A) := by
    have hb' : r0 - (r0 - δ) + A / 2 ≤ δ + 3 / 2 * A := by linarith
    rcases hb'.lt_or_eq with h | h
    · exact (barrierW_strictMono hκ h).le
    · rw [h]
  exact (abs_sub_le_common_innerCylinder_straightened_dirichlet hlam hB hBs hbs hb haα hατ (sub_pos.mpr hδr) (by linarith : r0 - δ ≤ r0) (by linarith : 0 ≤ A / 2) hd hL hε hε1 hC hΓ g (fun i => r0 - β i) R hg hgL hr (fun i => hR0.trans_le (hR i)) (fun i => by linarith [(hβ i).1]) hd' hc (fun i => hsize _ _ (by linarith [(hβ i).2]) (hR i)) F hFC ht u hu p hp).trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (div_le_div_of_nonneg_right hm (barrierW_pos hκ hd).le)) (by positivity))



/-- The concrete growth/collar error can be made arbitrarily small, with any prescribed
inner-radius tolerance and transported cutoff. -/
theorem exists_small_dirichlet_comparison_parameters
    {κ d δ0 r0 C M e : ℝ} (_hκ : 0 < κ) (hd : 0 < d) (hδ0 : 0 < δ0)
    (hr0 : 0 < r0) (hC : 0 ≤ C) (hM : 0 ≤ M) (he : 0 < e) (S0 : ℝ) :
    ∃ δ A S : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ < r0 ∧ 0 < A ∧ A ≤ d ∧
      3 / 2 * A < δ ∧ S0 ^ 2 ≤ S ^ 2 ∧
      2 * C * (M / (1 + S ^ 2) + barrierW κ (δ + 3 / 2 * A) / barrierW κ d) < e := by
  let q (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hq : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hw : Continuous (barrierW κ) := by unfold barrierW; fun_prop
  have harg : Tendsto (fun j => q j + 3 / 2 * (q j / 4)) atTop (𝓝 0) := by
    convert hq.add (tendsto_const_nhds.mul (hq.div_const 4)) using 1
    norm_num
  have herr : Tendsto (fun j =>
      2 * C * (M * q j + barrierW κ (q j + 3 / 2 * (q j / 4)) / barrierW κ d))
      atTop (𝓝 0) := by
    simpa [Function.comp_def, barrierW, Real.exp_zero] using (tendsto_const_nhds (x := 2 * C)).mul (((tendsto_const_nhds (x := M)).mul hq).add ((hw.tendsto 0).comp harg |>.div_const (barrierW κ d)))
  have hjS : ∀ᶠ j : ℕ in atTop, |S0| < (j : ℝ) + 1 :=
    (tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop |S0|)).mono
      fun j hj => by linarith
  obtain ⟨j, hjδ, hjr, hjd, hjS, hje⟩ :=
    (hq.eventually (gt_mem_nhds hδ0)).and
      ((hq.eventually (gt_mem_nhds hr0)).and
        ((hq.eventually (gt_mem_nhds hd)).and (hjS.and
          (herr.eventually (gt_mem_nhds he))))) |>.exists
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hqpos : 0 < q j := by dsimp [q]; positivity
  have hden : (j : ℝ) + 1 ≤ 1 + ((j : ℝ) + 1) ^ 2 := by nlinarith
  have hsmall : M / (1 + ((j : ℝ) + 1) ^ 2) ≤ M * q j := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hM (by positivity) hden
  refine ⟨q j, q j / 4, (j : ℝ) + 1, hqpos, hjδ.le, hjr,
    (by positivity), (by linarith), (by linarith), ?_, ?_⟩
  · nlinarith [sq_abs S0, abs_nonneg S0]
  · exact (mul_le_mul_of_nonneg_left (add_le_add hsmall (le_refl _))
      (by positivity)).trans_lt hje

end HypoellipticAleksandrov.KineticAleksandrov

