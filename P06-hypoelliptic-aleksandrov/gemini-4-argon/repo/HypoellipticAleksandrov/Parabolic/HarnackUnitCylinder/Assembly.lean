module

public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ClassicalWeakEquation
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.LocalWeakHarnack
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ChainGeometry
import HypoellipticAleksandrov.Parabolic.HarnackStability
import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.CoefficientExtension
import HypoellipticAleksandrov.Parabolic.SourceLocalHarnackScaling

/-! # The classical parabolic Harnack inequality on the unit cylinder -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Set
open Filter MeasureTheory
open scoped ENNReal Topology Matrix.Norms.Elementwise

/- Every nonnegative C¹,² solution satisfies the unit-cylinder Harnack comparison. -/
theorem parabolic_harnack_unit_cylinder_aux
    (N ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 < lam)
    (Lam : ℝ) (hlamLam : lam ≤ Lam) :
    ∃ h : ℝ, 0 < h ∧
      ∀ (B : CoefficientField N) (u : TimeVelocity N → ℝ),
        IsContinuousCoefficientOn B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1,
          (coefficientAt B z).IsSymm) →
        HasLowerEllipticityOn lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        HasUpperEllipticityOn Lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        IsScalarC12On u
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        IsNonnegativeOn u
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1,
          scalarTimeDerivative u z =
            matrixContraction (coefficientAt B z) (scalarSpatialHessian u z)) →
        ∀ P ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
            PDE.euclideanBall (0 : PDE.Vec N) (1 / 2 : ℝ),
          ∀ P' ∈ Set.Ioo (3 / 4 : ℝ) 1 ×ˢ
              PDE.euclideanBall (0 : PDE.Vec N) (1 / 2 : ℝ),
            h * u P ≤ u P' := by
  obtain ⟨hBox, hh0, _hh1, hlocal⟩ : ∃ hBox : ℝ, 0 < hBox ∧ hBox ≤ 1 ∧
      ∀ (U : Set (TimeVelocity N)) (B : CoefficientField N)
        (u : TimeVelocity N → ℝ) (t0 : ℝ) (v0 : PDE.Vec N) (r : ℝ),
        IsOpen U → 0 < r →
        parabolicClosedBox 2 r (t0 - r ^ 2) v0 ⊆ U →
        IsContinuousCoefficientOn B U →
        (∀ z ∈ U, (coefficientAt B z).IsSymm) →
        HasLowerEllipticityOn lam B U → HasUpperEllipticityOn Lam B U →
        IsWeakParabolicEquationLoc B U (parabolicExponent N) u →
        ContinuousOn u U → IsNonnegativeOn u U →
        ∀ v ∈ velocityCube v0 (r / 2),
          hBox * u (t0, v0) ≤ u (t0 + r ^ 2, v) := by
    obtain ⟨hBox, C, hh0, hh1, _hC, hsource⟩ :=
      exists_source_local_parabolic_harnack N hN lam hlam Lam hlamLam
    refine ⟨hBox, hh0, hh1, ?_⟩
    intro U B u t0 v0 r hU hr hKU hB hSymm hLower hUpper hWeak hu huNonneg v hv
    let K := parabolicClosedBox 2 r (t0 - r ^ 2) v0
    have hK : IsCompact K := isCompact_parabolicClosedBox _ _ _ _
    let Aext := extendCoefficientByMidpoint B U (ellipticityMidpoint N lam Lam)
    have hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt B :=
      ae_restrict_of_forall_mem hU.measurableSet (fun z hz => by
        simp only [Aext, coefficientAt_extendCoefficientByMidpoint, ite_eq_left hz])
    obtain ⟨_, hExtLower, hExtUpper⟩ :=
      extendCoefficientByMidpoint_global_ellipticity N lam Lam B U
        hSymm hLower hUpper hlamLam
    obtain ⟨J, hUniform, hResidual, hTail⟩ :=
      exists_localizedJet_eventually_nonnegative_residual_mollifications_tendsto N hN lam Lam
        B Aext U K u u hU hK hKU hExtAE
        (isBorel_midpointExtension_of_continuousOn hU hB lam Lam) hExtLower hExtUpper
        hWeak (ae_restrict_of_forall_mem hU.measurableSet huNonneg) hu EventuallyEq.rfl
    let F : ℕ → TimeVelocity N → ℝ := fun n z =>
      parabolicOperator (parabolicMollifyCoefficient Aext n) (parabolicMollifiedValue J.g n) z
    have hFnorm : Tendsto (fun n => parabolicELpNormOn N (F n) K) atTop (nhds 0) := by
      apply Tendsto.congr' ?_ hResidual
      filter_upwards [hTail] with n hn
      have hAE : F n =ᵐ[volume.restrict K]
          weakEquationMollificationResidual Aext J.g n :=
        ae_restrict_of_forall_mem hK.measurableSet hn.2.2.2.2.2.2
      exact (eLpNorm_congr_ae hAE).symm
    have hFreal := tendsto_parabolicLpNormOn_of_tendsto_parabolicELpNormOn_zero hFnorm
    let ε : ℕ → ℝ := fun n =>
      C * r ^ ((N : ℝ) / ((N : ℝ) + 1)) * parabolicLpNormOn N (F n) K
    have hε : Tendsto ε atTop (nhds 0) := by
      simpa only [ε, mul_zero] using tendsto_const_nhds.mul hFreal
    have hsourceMem : (t0, v0) ∈ K := by
      rw [mem_parabolicClosedBox_iff]
      refine ⟨by nlinarith [sq_nonneg r], by nlinarith [sq_nonneg r], ?_⟩
      intro i
      simpa using hr.le
    have htargetMem : (t0 + r ^ 2, v) ∈ K := by
      rw [mem_parabolicClosedBox_iff]
      refine ⟨by nlinarith [sq_nonneg r], by nlinarith, ?_⟩
      intro i
      exact (hv i).le.trans (by linarith)
    have hEventually : ∀ᶠ n in atTop,
        hBox * parabolicMollifiedValue J.g n (t0, v0) ≤
          parabolicMollifiedValue J.g n (t0 + r ^ 2, v) + ε n := by
      filter_upwards [hTail] with n hn
      have hBcontinuous : IsContinuousCoefficient (parabolicMollifyCoefficient Aext n) := by
        change Continuous (fun x i j => coefficientAt (parabolicMollifyCoefficient Aext n) x i j)
        rw [continuous_pi_iff]
        intro i
        rw [continuous_pi_iff]
        intro j
        exact hn.1.continuous.matrix_elem i j
      exact hsource K U (parabolicMollifyCoefficient Aext n) (parabolicMollifiedValue J.g n)
        (F n) t0 v0 r hr hK hKU hU (Subset.refl _)
        (IsContinuousCoefficientOn.of_global hBcontinuous U)
        (contDiffOn_of_global (hn.2.2.2.2.1.of_le
          (by exact WithTop.coe_le_coe.mpr le_top)) U)
        (continuous_parabolicOperator_of_smooth_for_unitCylinder hn.1
          hn.2.2.2.2.1).continuousOn hn.2.2.2.2.2.1
        (HasLowerEllipticityOn.of_global hn.2.2.1 K)
        (HasUpperEllipticityOn.of_global hn.2.2.2.1 K) (fun _ _ => rfl) v hv
    have hleft : Tendsto (fun n => hBox * parabolicMollifiedValue J.g n (t0, v0))
        atTop (nhds (hBox * u (t0, v0))) :=
      tendsto_const_nhds.mul (hUniform.tendsto_at hsourceMem)
    have hright := (hUniform.tendsto_at htargetMem).add hε
    exact le_of_tendsto_of_tendsto hleft (by simpa only [add_zero] using hright) hEventually
  refine ⟨hBox ^ (256 * N), pow_pos hh0 _, ?_⟩
  intro B u hB hSymm hLower hUpper hu huNonneg heq P hP P' hP'
  let U := Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1
  have hU : IsOpen U := isOpen_Ioo.prod (PDE.isOpen_euclideanBall _ _)
  have hWeak := IsScalarC12On.isWeakParabolicEquationLoc hU hu heq (parabolicExponent N)
  let m : ℕ := 256 * N
  let dt : ℝ := (P'.1 - P.1) / (m : ℝ)
  let r : ℝ := Real.sqrt dt
  let t : ℕ → ℝ := fun k => P.1 + (k : ℝ) * dt
  let v : ℕ → PDE.Vec N := fun k =>
    P.2 + ((k : ℝ) / (m : ℝ)) • (P'.2 - P.2)
  have hgeom := unitCylinder_harnack_link_geometry N hN P P' hP hP'
  change 0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧
    (∀ k < m, t (k + 1) = t k + r ^ 2) ∧
    (∀ k < m, parabolicClosedBox 2 r (t k - r ^ 2) (v k) ⊆ U) ∧
    (∀ k < m, v (k + 1) ∈ velocityCube (v k) (r / 2)) at hgeom
  obtain ⟨_hm, hr, hstart, hend, htstep, hboxes, hvstep⟩ := hgeom
  have hchain : ∀ k ≤ m, hBox ^ k * u P ≤ u (t k, v k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [pow_zero, one_mul, hstart, le_refl]
    | succ k ih =>
      intro hk
      have hkm := Nat.lt_of_succ_le hk
      have hlink := hlocal U B u (t k) (v k) r hU hr (hboxes k hkm)
        hB hSymm hLower hUpper hWeak hu.continuousOn huNonneg (v (k + 1)) (hvstep k hkm)
      rw [← htstep k hkm] at hlink
      calc
        hBox ^ (k + 1) * u P = hBox * (hBox ^ k * u P) := by rw [pow_succ]; ring
        _ ≤ hBox * u (t k, v k) :=
          mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hkm)) hh0.le
        _ ≤ u (t (k + 1), v (k + 1)) := hlink
  simpa only [hend] using hchain m le_rfl

end HypoellipticAleksandrov.Parabolic
