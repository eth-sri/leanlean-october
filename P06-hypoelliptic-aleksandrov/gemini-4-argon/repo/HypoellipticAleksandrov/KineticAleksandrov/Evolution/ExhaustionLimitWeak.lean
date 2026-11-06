module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWeakTest
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitUniform

/-!
# The weak equation on strict bounded inner cylinders

The actual limit is continuous, hence locally integrable. Its compact-test
identity is the proved limit of the finite Dirichlet weak equations.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/- The actual Dirichlet exhaustion limit solves the regularized kinetic equation
weakly on every strict bounded inner cylinder. -/
theorem weakRegularized_innerBall_dirichlet_limit
    {n lam Lam Lb m B b}
    (hn : 1 ≤ n) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B)
    (hBsym : IsSymmetricFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hbco : HasUnitDirectionDriftCoercivity m b)
    {a α τ r0 δ0 S0 d L C ε } (haα : a < α) (hατ : α < τ)
    (hδ0 : 0 < δ0) (hδr : δ0 < r0) (hd : 0 < d) (hdr : d < r0 / 4)
    (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
    {Γ } (hΓ : IsContinuousPiecewiseC1 Γ)
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
  have hEq : (∫ p, limUnder atTop (fun k => straightenedPullback (g k) (u k) p) *
      regularizedAdjoint B b ε ψ ((evolutionHomeomorph n).symm p)) = 0 := by
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
    have hInt : Tendsto (fun k => ∫ p in
      movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ (S0) ^ 2}, straightenedPullback (g k) (u k) p * φ p)
      atTop (𝓝 (∫ p in movingClosedSlab (PDE.euclideanBall 0 (r0 - δ0)) Γ α τ ∩
        {p | radialSq p ≤ (S0) ^ 2},
        limUnder atTop (fun k => straightenedPullback (g k) (u k) p) * φ p)) := by
      let S0 := (S0)
      have hε := hε.le
      have hΓ := hΓ.1
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
        have hbnd := abs_le_straightened_dirichlet
          hlam hB hBs hbs (haα.trans hατ) hk.1 hk.2.1 (hg k) hε F (u k) (hu k)
          hC hFC _ (hclosed k hk hp)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right hbnd (abs_nonneg _)
      · exact (continuous_const.mul hφ.abs).continuousOn.integrableOn_compact hK
      · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
        exact (hU.tendsto_at hp).mul tendsto_const_nhds
    have hmem := eventually_innerCylinder_mem_straightenedEllipsoid (S := S0)
      hδ0 hδr β R hβlim hRlim g hclose
    have hIz : ∀ᶠ k : ℕ in atTop,
        (∫ p in K, straightenedPullback (g k) (u k) p * φ p) = 0 := by
      filter_upwards [hmem] with k hk
      let D : Set (KineticPoint n) := {p | a < p.time ∧ p.time < τ ∧
        spatialPack (p.position - g k p.time) p.velocity ∈
          openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k))}
      have hΩ : IsAdmissibleEvolutionDomain (PDE.euclideanBall (0 : PDE.Vec n) r0) :=
        Or.inr (Or.inl ⟨0, r0, by linarith, rfl⟩)
      have hw := weakRegularized_of_straightened_dirichlet
        (n := n) (hn := hn) (lam := lam) (Lam := Lam) (m := m) (L_b := Lb)
        (hlam := hlam) (hlamLam := hlamLam) (hm := hm) (hmLb := hmLb)
        (Ω := PDE.euclideanBall 0 r0) (γ := Γ) (B := B) (b := b)
        (hΩ := hΩ) (hγ := hΓ) (hB_smooth := hBs) (hB_symm := hBsym)
        (hB_ell := hB) (hb_smooth := hbs) (hb_lipschitz := hb) (hb_coercive := hbco)
        a τ (r0 - β k) (R k) (haα.trans hατ) hk.1 hk.2.1 (g k) (hg k)
        ε hε F (u k) (hu k)
      have hsD : tsupport ψ ⊆ evolutionHomeomorph n ⁻¹' D := by
        intro x hx
        have hp := hs hx
        exact ⟨haα.trans hp.1, hp.2.1, hk.2.2 _ (hKs x hx)⟩
      have hzeroD (p : KineticPoint n) (hp : p ∉ D) : φ p = 0 := by
        apply regularizedAdjoint_eq_zero_of_notMem_tsupport
        intro hx
        exact hp (by simpa using hsD hx)
      have he := hw.2 ψ hψ hc hsD
      have he' : (∫ p in D, straightenedPullback (g k) (u k) p * φ p) = 0 := by
        simpa only [straightenedPullback, straightenedPoint, φ, zero_mul, integral_zero]
          using he
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun p hp => by rw [hzeroK p hp, mul_zero])]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun p hp => by rw [hzeroD p hp, mul_zero])] at he'
      exact he'
    have hlim0 : (∫ p in K, limUnder atTop
        (fun k => straightenedPullback (g k) (u k) p) * φ p) = 0 :=
      tendsto_nhds_unique hInt (tendsto_const_nhds.congr' (hIz.mono fun k hk => hk.symm))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hzeroK p hp, mul_zero])] at hlim0
    exact hlim0
  simp only [zero_mul, integral_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)]
  · exact hEq
  · rw [regularizedAdjoint_eq_zero_of_notMem_tsupport ε ψ (fun hx =>
      hp (by simpa using hs hx)), mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov
