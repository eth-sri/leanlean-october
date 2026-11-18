module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCover
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarApproximation
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitSequence
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluing

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory Evolution
open scoped Topology MatrixOrder


/-- Every smooth compact test supported in a fixed bounded inner cylinder satisfies
the regularized adjoint identity for the actual exhaustion limit. -/
theorem integral_regularizedAdjoint_innerBall_dirichlet_limit_eq_zero
    {n : ℕ} {lam Lam Lb m : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B)
    (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hbco : HasUnitDirectionDriftCoercivity m b)
    {a α τ r0 δ0 S0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)
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
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k))
    (ψ : EvolutionVec n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ evolutionHomeomorph n ⁻¹'
      {p : KineticPoint n | α < p.time ∧ p.time < τ ∧
        p.position ∈ movingDomain (PDE.euclideanBall 0 (r0 - δ0)) Γ p.time ∧
        radialSq p < S0 ^ 2}) :
    (∫ p, limUnder atTop (fun k => straightenedPullback (g k) (u k) p) *
      regularizedAdjoint B b ε ψ ((evolutionHomeomorph n).symm p)) = 0  := by
  have tendsto_setIntegral_mul_innerBall_dirichlet {n : ℕ} {lam : ℝ} {Lam : ℝ} {Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B) (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b) (hb : HasEuclideanLipschitzDrift Lb b) {a α τ r0 δ0 S0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ) (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) {Γ : ℝ → PDE.Vec n} (hΓ : Continuous Γ) (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C) (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)) (β R : ℕ → ℝ) (hβpos : ∀ k, 0 < β k) (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop) (g : ℕ → ℝ → PDE.Vec n) (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) (hgL : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|) (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2) (u : ℕ → TimeVelocity (n + n) → ℝ) (hu : ∀ k, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)) (φ : KineticPoint n → ℝ) (hφ : Continuous φ) :
      Tendsto (fun k => ∫ p in
      movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ S0 ^ 2}, straightenedPullback (g k) (u k) p * φ p)
      atTop (𝓝 (∫ p in movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ S0 ^ 2},
        limUnder atTop (fun k => straightenedPullback (g k) (u k) p) * φ p)) := by
    let K := movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
      {p | radialSq p ≤ S0 ^ 2}
    have hK : IsCompact K := isCompact_movingClosedSlab_inter hΓ α τ S0
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
    apply tendsto_integral_filter_of_dominated_convergence (fun p => C * |φ p|)
    · exact hmem.mono fun k hk => (((hu k).1.comp
        (continuous_straightenedPoint (hg k).continuous).continuousOn (hclosed k hk)).mul
          hφ.continuousOn).aestronglyMeasurable hK.measurableSet
    · refine hmem.mono fun k hk => ?_
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_le_straightened_dirichlet hlam hB hBs hbs (haα.trans hατ) hk.1 hk.2.1 (hg k) hε F (u k) (hu k) hC hFC _ (hclosed k hk hp)) (abs_nonneg _)
    · exact (continuous_const.mul hφ.abs).continuousOn.integrableOn_compact hK
    · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      exact (hU.tendsto_at hp).mul tendsto_const_nhds
  let K := movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  let φ (p : KineticPoint n) := regularizedAdjoint B b ε ψ
    ((evolutionHomeomorph n).symm p)
  have hφ : Continuous φ := (contDiff_regularizedAdjoint hBs hbs hψ ε).continuous.comp
    (evolutionHomeomorph n).symm.continuous
  have hKs (x : EvolutionVec n) (hx : x ∈ tsupport ψ) :
      evolutionHomeomorph n x ∈ K := by
    have hp := hs hx
    exact ⟨⟨hp.1.le, hp.2.1.le, subset_closure hp.2.2.1⟩, hp.2.2.2.le⟩
  have hzeroK (p : KineticPoint n) (hp : p ∉ K) : φ p = 0 := by
    apply regularizedAdjoint_eq_zero_of_notMem_tsupport
    intro hx
    exact hp (by simpa using hKs _ hx)
  have hInt := tendsto_setIntegral_mul_innerBall_dirichlet (S0 := S0)
    hlam hB hBs hbs hb haα hατ hδ0 hδr hd hdr hL hε.le hε1 hC hΓ.1
    F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu φ hφ
  have hIz : ∀ᶠ k : ℕ in atTop,
      (∫ p in K, straightenedPullback (g k) (u k) p * φ p) = 0 := by
    filter_upwards [(eventually_innerCylinder_mem_straightenedEllipsoid (S := S0) hδ0 hδr β R hβlim hRlim g hclose)] with k hk
    let D : Set (KineticPoint n) := {p | a < p.time ∧ p.time < τ ∧
      spatialPack (p.position - g k p.time) p.velocity ∈
        openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k))}
    have hΩ : IsAdmissibleEvolutionDomain (PDE.euclideanBall (0 : PDE.Vec n) r0) :=
      Or.inr (Or.inl ⟨0, r0, by linarith, rfl⟩)
    have hsD : tsupport ψ ⊆ evolutionHomeomorph n ⁻¹' D := by
      intro x hx
      have hp := hs hx
      exact ⟨haα.trans hp.1, hp.2.1, hk.2.2 _ (hKs x hx)⟩
    have hzeroD (p : KineticPoint n) (hp : p ∉ D) : φ p = 0 := by
      apply regularizedAdjoint_eq_zero_of_notMem_tsupport
      intro hx
      exact hp (by simpa using hsD hx)
    have he := (weakRegularized_of_straightened_dirichlet (n := n) (hn := hn) (lam := lam) (Lam := Lam) (m := m) (L_b := Lb) (hlam := hlam) (hlamLam := hlamLam) (hm := hm) (hmLb := hmLb) (Ω := PDE.euclideanBall 0 r0) (γ := Γ) (B := B) (b := b) (hΩ := hΩ) (hγ := hΓ) (hB_smooth := hBs) (hB_symm := hBsym) (hB_ell := hB) (hb_smooth := hbs) (hb_lipschitz := hb) (hb_coercive := hbco) a τ (r0 - β k) (R k) (haα.trans hατ) hk.1 hk.2.1 (g k) (hg k) ε hε F (u k) (hu k)).2 ψ hψ hc hsD
    have he' : (∫ p in D, straightenedPullback (g k) (u k) p * φ p) = 0 := by
      simpa [straightenedPullback, straightenedPoint, φ, integral_zero]
        using he
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hzeroK p hp, mul_zero])]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hzeroD p hp, mul_zero])] at he'
    exact he'
  have hlim0 :=
    tendsto_nhds_unique hInt (tendsto_const_nhds.congr' (hIz.mono fun k hk => hk.symm))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun p hp => by rw [hzeroK p hp, mul_zero])] at hlim0
  exact hlim0



/-- The actual Dirichlet exhaustion limit solves the regularized kinetic equation
weakly on every strict bounded inner cylinder. -/
theorem weakRegularized_innerBall_dirichlet_limit
    {n : ℕ} {lam Lam Lb m : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B)
    (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hbco : HasUnitDirectionDriftCoercivity m b)
    {a α τ r0 δ0 S0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)
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
    IsKineticWeakRegularizedSolution B b ε
      (boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0)
      (fun p => limUnder atTop (fun k => straightenedPullback (g k) (u k) p))
      (fun _ => 0) := by
  let U := boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0
  have hU : IsOpen U := isOpen_boundedInnerOpenCylinder _ hΓ.1 _ _ _
  have hcont := (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S0)
    hlam hB hBs hbs hb haα hατ hδ0 hδr hd hdr hL hε.le hε1 hC hΓ.1
    F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu).1.mono
      (boundedInnerOpenCylinder_subset_closed _ Γ α τ S0)
  refine ⟨hcont.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro ψ hψ hc hs
  simp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)]
  · exact (integral_regularizedAdjoint_innerBall_dirichlet_limit_eq_zero hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ0 hδr hd hdr hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu ψ hψ hc hs)
  · rw [regularizedAdjoint_eq_zero_of_notMem_tsupport ε ψ (fun hx =>
      hp (by simpa using hs hx)), mul_zero]



/-- The actual continuous zero extension is smooth and solves the viscous equation
pointwise on every strict bounded inner cylinder, relative to the explicit Hörmander input. -/
theorem classical_innerBallDirichletLimit_on_innerCylinder
    (hH : HormanderHypoellipticityStatement)
    {n : ℕ} {lam Lam Lb m : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B)
    (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hbco : HasUnitDirectionDriftCoercivity m b)
    {a α τ r0 δ0 S0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)
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
    ContDiffOn ℝ (⊤ : ℕ∞) (innerBallDirichletLimit r0 Γ g u ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0) ∧
    ∀ p ∈ boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0,
      viscousTransportedOperator B b ε (innerBallDirichletLimit r0 Γ g u) p = 0  := by
  have contDiffOn_innerBall_dirichlet_limit (hH : HormanderHypoellipticityStatement) {n : ℕ} {lam : ℝ} {Lam : ℝ} {Lb : ℝ} {m : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B) (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b) (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b) {a α τ r0 δ0 S0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ) (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ) (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C) (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)) (β R : ℕ → ℝ) (hβpos : ∀ k, 0 < β k) (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop) (g : ℕ → ℝ → PDE.Vec n) (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) (hgL : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|) (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2) (u : ℕ → TimeVelocity (n + n) → ℝ) (hu : ∀ k, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)) :
      ContDiffOn ℝ (⊤ : ℕ∞)
      ((fun p => limUnder atTop (fun k => straightenedPullback (g k) (u k) p)) ∘
        evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0) := by
    let U := boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0
    let vlim (p : KineticPoint n) :=
      limUnder atTop (fun k => straightenedPullback (g k) (u k) p)
    have hU : IsOpen U := isOpen_boundedInnerOpenCylinder _ hΓ.1 _ _ _
    have hw := weakRegularized_innerBall_dirichlet_limit (S0 := S0)
      hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ0 hδr hd hdr
      hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
    obtain ⟨v, hvs, hae⟩ := exists_smooth_viscous_kinetic_representative
      hH hlam hBs hB hbs U hU ε hε vlim hw
    have hcLim :=
      (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S0)
        hlam hB hBs hbs hb haα hατ hδ0 hδr hd hdr hL hε.le hε1 hC hΓ.1
        F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu).1.mono
          (boundedInnerOpenCylinder_subset_closed _ Γ α τ S0)
    have hcPack :=
      hcLim.comp (evolutionHomeomorph n).continuous.continuousOn (fun _ hx => hx)
    have heq := eqOn_of_ae_eq_of_continuousOn_kinetic hU hcPack hvs.continuousOn hae
    exact hvs.congr (fun x hx => heq hx)
  let U := boundedInnerOpenCylinder (r0 - δ0) Γ α τ S0
  let vlim (p : KineticPoint n) :=
    limUnder atTop (fun k => straightenedPullback (g k) (u k) p)
  have hU : IsOpen U := isOpen_boundedInnerOpenCylinder _ hΓ.1 _ _ _
  have hV :=
    hU.preimage (evolutionHomeomorph n).continuous
  have hsm := contDiffOn_innerBall_dirichlet_limit (S0 := S0)
    hH hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ0 hδr hd hdr
    hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
  have hwPack := (isWeakRegularizedSolution_comp_iff B b ε U vlim (fun _ => 0)).mpr (weakRegularized_innerBall_dirichlet_limit (S0 := S0) hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ0 hδr hd hdr hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu)
  have hinside : ∀ p ∈ U, p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time :=
    fun p hp => innerClosedCylinder_subset_movingBall hδ0 hδr
      (boundedInnerOpenCylinder_subset_closed _ Γ α τ S0 hp)
  refine ⟨hsm.congr (fun x hx => innerBallDirichletLimit_eq_limit r0 Γ g u
    (hinside _ hx)), ?_⟩
  intro p hp
  have hnear : ∀ᶠ q in 𝓝 p,
      q.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ q.time :=
    (isOpen_setOf_mem_movingDomain (PDE.isOpen_euclideanBall 0 r0) hΓ.1).mem_nhds
      (hinside p hp)
  rw [viscousTransportedOperator_congr_germ B b ε (hnear.mono (fun q hq => innerBallDirichletLimit_eq_limit r0 Γ g u hq))]
  let x := (evolutionHomeomorph n).symm p
  have hx : x ∈ evolutionHomeomorph n ⁻¹' U := by
    change evolutionHomeomorph n x ∈ U
    simpa only [x, Homeomorph.apply_symm_apply] using hp
  have hc2 : ContDiffAt ℝ 2 (vlim ∘ evolutionHomeomorph n) x :=
    (hsm.contDiffAt (hV.mem_nhds hx)).of_le (by norm_num)
  have hz := (regularizedOperator_eq_zero_of_smooth_weak hV hBs hBsym hbs ε hsm hwPack) x hx
  rw [(regularizedOperator_comp (B := B) (b := b) ε hc2)] at hz
  simpa only [x, Homeomorph.apply_symm_apply, viscousTransportedOperator] using hz



/-- The continuous zero extension has the original uniform bound and terminal
values, and vanishes on the actual moving lateral boundary. -/
theorem innerBallDirichletLimit_bound_terminal_lateral
    {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    {a α τ r0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ : ℝ → PDE.Vec n} (hΓ : Continuous Γ)
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
    (∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ,
      |innerBallDirichletLimit r0 Γ g u p| ≤ C) ∧
    (∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ, p.time = τ →
      innerBallDirichletLimit r0 Γ g u p = F (p.position, p.velocity)) ∧
    (∀ p : KineticPoint n,
      p.position ∈ frontier (movingDomain (PDE.euclideanBall 0 r0) Γ p.time) →
      innerBallDirichletLimit r0 Γ g u p = 0) := by
  have hr0 : 0 < r0 := by linarith
  have hpoint (p : KineticPoint n)
      (hp : p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ)
      (hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time) :
      |innerBallDirichletLimit r0 Γ g u p| ≤ C := by
    obtain ⟨δ, S, hδ, hδr, hpK, -⟩ :=
      exists_innerClosedCylinder_mem_nhdsWithin hΓ hr0 hp hi
    rw [innerBallDirichletLimit_eq_limit r0 Γ g u hi]
    exact (continuousOn_bounded_innerBall_dirichlet_limit (S0 := S)
      hlam hB hBs hbs hb haα hατ hδ hδr hd hdr hL hε hε1 hC hΓ
      F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu).2 p hpK
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    by_cases hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time
    · exact hpoint p hp hi
    · simpa [innerBallDirichletLimit, ite_eq_right hi] using hC
  · intro p hp ht
    by_cases hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time
    · obtain ⟨δ, S, hδ, hδr, hpK, -⟩ :=
        exists_innerClosedCylinder_mem_nhdsWithin hΓ hr0 hp hi
      have hU := tendstoUniformlyOn_innerBall_dirichlet (S0 := S)
        hlam hB hBs hbs hb haα hατ hδ hδr hd hdr hL hε hε1 hC hΓ
        F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
      have hmem := eventually_innerCylinder_mem_straightenedEllipsoid (S := S)
        hδ hδr β R hβlim hRlim g hclose
      have he : ∀ᶠ k : ℕ in atTop,
          straightenedPullback (g k) (u k) p = F (p.position, p.velocity) := by
        filter_upwards [hmem] with k hk
        have hm := subset_closure (hk.2.2 p hpK)
        simp only [straightenedPoint, ht] at hm
        have het := (hu k).2.2.2.1 _ hm
        simpa only [straightenedPullback, straightenedPoint, ht,
          spatialY_spatialPack, spatialZ_spatialPack, add_sub_cancel] using het
      rw [innerBallDirichletLimit_eq_limit r0 Γ g u hi]
      exact tendsto_nhds_unique (hU.tendsto_at hpK)
        (tendsto_const_nhds.congr' (he.mono fun k hk => hk.symm))
    · have hzero : F (p.position, p.velocity) = 0 := by
        by_contra hne
        have hs := hsupp (p.position, p.velocity)
          (subset_tsupport (F : EvolutionAmbientState n → ℝ) hne)
        have hn := (mem_movingBall_iff_norm_lt hr0).not.mp hi
        rw [ht] at hn
        linarith
      simp only [innerBallDirichletLimit, ite_eq_right hi, hzero]
  · intro p hp
    have hnot : p.position ∉ movingDomain (PDE.euclideanBall 0 r0) Γ p.time :=
      by
        have hopen := isOpen_movingDomain (γ := Γ) (PDE.isOpen_euclideanBall 0 r0) p.time
        change p.position ∈ closure _ ∧ p.position ∉ interior _ at hp
        simpa only [hopen.interior_eq] using hp.2
    exact ite_eq_right hnot



section Data

variable (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
variable {n : ℕ} (hn : 1 ≤ n) {lam Lam m Lb : ℝ}
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb)
variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
variable (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b)
variable {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ) {r0 : ℝ} (hr0 : 0 < r0)

include hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ hr0

/-- Actual finite-slab classical solutions on a moving ball exist with the original
terminal-data bound, relative only to explicit Lieberman and Hörmander inputs. -/
theorem exists_finite_viscous_innerBall_solution
    (a τ : ℝ) (haτ : a < τ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 r0) Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousFiniteSolution (PDE.euclideanBall 0 r0) Γ B b ε a τ F v ∧
        ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ a τ, |v p| ≤ C  := by
  have isClassicalViscousFiniteSolution_innerBallDirichletLimit (hH : HormanderHypoellipticityStatement) {n : ℕ} {lam : ℝ} {Lam : ℝ} {Lb : ℝ} {m : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B) (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b) (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b) {a α τ r0 d L C ε : ℝ} (haα : a < α) (hατ : α < τ) (hd : 0 < d) (hdr : d < r0 / 4) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ) (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C) (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ)) (β R : ℕ → ℝ) (hβpos : ∀ k, 0 < β k) (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop) (g : ℕ → ℝ → PDE.Vec n) (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) (hgL : ∀ k s t, PDE.vecEuclideanNorm (g k s - g k t) ≤ L * |s - t|) (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2) (u : ℕ → TimeVelocity (n + n) → ℝ) (hu : ∀ k, IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)))
      (straightenedCoefficient B (g k) ε) (straightenedDrift b (g k))
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g k τ + spatialY x, spatialZ x)) (fun _ => 0) (u k)) :
      IsClassicalViscousFiniteSolution (PDE.euclideanBall 0 r0) Γ B b ε α τ F
      (innerBallDirichletLimit r0 Γ g u) := by
    have hr0 : 0 < r0 := by linarith
    have htrace := innerBallDirichletLimit_bound_terminal_lateral
      hlam hB hBs hbs hb haα hατ hd hdr hL hε.le hε1 hC hΓ.1
      F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
    have hcont := continuousOn_innerBallDirichletLimit
      hlam hB hBs hbs hb haα hατ hd hdr hL hε.le hε1 hC hΓ.1
      F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
    have hlocal (δ S : ℝ) (hδ : 0 < δ) (hδr : δ < r0) :=
      classical_innerBallDirichletLimit_on_innerCylinder (S0 := S)
        hH hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco haα hατ hδ hδr hd hdr
        hL hε hε1 hC hΓ F hFC hsupp β R hβpos hβlim hRlim g hg hgL hclose u hu
    refine ⟨⟨C, hC, htrace.1⟩, hcont, ?_, ?_, ?_, ?_⟩
    · intro q hq
      let p : KineticPoint n := ⟨q.1, q.2.1, q.2.2⟩
      obtain ⟨δ, S, hδ, hδr, hp⟩ := exists_boundedInnerOpenCylinder_mem hr0
        (p := p) ⟨hq.1, hq.2.1⟩ hq.2.2
      let x := (evolutionProdCLE n).symm q
      have hxp : evolutionHomeomorph n x = p := by
        apply (KineticPoint.equivProd n).injective
        exact (evolutionProdCLE n).apply_symm_apply q
      have hx : x ∈ evolutionHomeomorph n ⁻¹'
          boundedInnerOpenCylinder (r0 - δ) Γ α τ S := by
        change evolutionHomeomorph n x ∈ boundedInnerOpenCylinder (r0 - δ) Γ α τ S
        rw [hxp]
        exact hp
      have hV := (isOpen_boundedInnerOpenCylinder (r0 - δ) hΓ.1 α τ S).preimage
        (evolutionHomeomorph n).continuous
      have hc := ((hlocal δ S hδ hδr).1.contDiffAt (hV.mem_nhds hx)).comp q
        (evolutionProdCLE n).symm.contDiff.contDiffAt
      have hfun : (innerBallDirichletLimit r0 Γ g u ∘ evolutionHomeomorph n) ∘
          (evolutionProdCLE n).symm = fun q =>
            innerBallDirichletLimit r0 Γ g u ⟨q.1, q.2.1, q.2.2⟩ := by
        funext q
        change innerBallDirichletLimit r0 Γ g u
          (evolutionHomeomorph n ((evolutionProdCLE n).symm q)) =
          innerBallDirichletLimit r0 Γ g u ⟨q.1, q.2.1, q.2.2⟩
        apply congrArg (innerBallDirichletLimit r0 Γ g u)
        apply (KineticPoint.equivProd n).injective
        change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
        exact (evolutionProdCLE n).apply_symm_apply q
      simpa only [hfun] using hc.contDiffWithinAt
    · intro p hp ha
      obtain ⟨δ, S, hδ, hδr, hpU⟩ := exists_boundedInnerOpenCylinder_mem hr0
        ⟨ha, hp.2.1⟩ hp.2.2
      exact (hlocal δ S hδ hδr).2 p hpU
    · intro p hp
      have hpc : p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ :=
        ⟨by rw [hp.1]; exact hατ.le, hp.1.le, by simpa only [hp.1] using hp.2⟩
      exact htrace.2.1 p hpc hp.1
    · intro p _ hp
      exact htrace.2.2 p hp
  obtain ⟨d, hd, hdr, hsupp⟩ := exists_innerBall_terminal_support_margin hr0 F hF.2.1
    (fun q hq => (hF.2.2 hq).1)
  obtain ⟨β, R, g, L, u, hL, hβ, hβlim, hR, hg, hgL, hclose, hu⟩ :=
    exists_innerBall_dirichlet_sequence hLE hlam hlamLam hBs hBsym hB hbs hΓ
      (show a - 1 < τ by linarith) hd hdr hε F hF.1 hF.2.1 hsupp
  have hRlim :=
    tendsto_atTop_mono (fun k => (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (hR k)) tendsto_natCast_atTop_atTop
  have hc (k : ℕ) (s : ℝ) (hs : s ∈ Icc a τ) :
      PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2 :=
    hclose k s ⟨by linarith [hs.1], hs.2⟩
  have hv := isClassicalViscousFiniteSolution_innerBallDirichletLimit
    hH hn hlam hlamLam hm hmLb hB hBs hBsym hbs hb hbco
    (show a - 1 < a by linarith) haτ hd hdr hL hε hε1 hC hΓ F hFC hsupp
    β R (fun k => (hβ k).1) hβlim hRlim g hg hgL hc u hu
  refine ⟨innerBallDirichletLimit r0 Γ g u, hv, ?_⟩
  exact (innerBallDirichletLimit_bound_terminal_lateral
    hlam hB hBs hbs hb (show a - 1 < a by linarith) haτ hd hdr hL hε.le hε1 hC hΓ.1
    F hFC hsupp β R (fun k => (hβ k).1) hβlim hRlim g hg hgL hc u hu).1

/-- The moving zero-centred ball branch of An actual bounded classical viscous
past solution exists and is unique, relative to the two analytic hypotheses. -/
theorem exists_viscous_terminalSolution_innerBall
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 r0) Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 r0) Γ B b ε τ F v ∧
      (∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall 0 r0) Γ τ, |v p| ≤ C) ∧
      (∀ w : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 r0) Γ B b ε τ F w →
          EqOn w v (evolutionPastClosedCylinder (PDE.euclideanBall 0 r0) Γ τ)) := by
  apply exists_viscous_terminalSolution_of_finiteSlabs (PDE.isOpen_euclideanBall 0 r0)
    hΓ.1 hlam hB hb hε.le hε1 τ F C hC
  intro a haτ
  exact exists_finite_viscous_innerBall_solution hLE hH hn hlam hlamLam hm hmLb
    hBs hBsym hB hbs hb hbco hΓ hr0 a τ haτ F hF ε hε hε1 C hC hFC

end Data

end HypoellipticAleksandrov.KineticAleksandrov

