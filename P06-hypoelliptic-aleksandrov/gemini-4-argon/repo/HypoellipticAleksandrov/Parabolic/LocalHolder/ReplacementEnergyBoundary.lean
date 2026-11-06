module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyBall
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonTracesBall
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBallBarrier
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonTraces
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnergyExistence
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnvelope
import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothInteriorBootstrap
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyInterior
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBallBarrierSobolev
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierPointwise
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonRepresentative
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonSobolev
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonStationaryCalculus
import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import Mathlib.MeasureTheory.Group.Measure
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalComparison
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalNegation
import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothH10DenseRange
import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothNeighborhoodSpatialSlices
import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierEnergy
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierWeakIdentity
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonEnergyConstant

/-! # Classical signed corrections continuous up to the ball boundary

A finite earlier time collar supplies continuity at the lower face. The two proved
envelopes supply zero terminal and lateral traces, without compact-source restrictions.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set Dirichlet KineticAleksandrov
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise
open scoped Topology
open Matrix
open scoped RealInnerProductSpace

/- Every smooth signed source has a continuous zero-boundary classical correction on a ball. -/
theorem exists_signed_source_ball_correction {d } (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A ) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ W : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
        (fun _ => 0) (fun _ => 0) W := by
  classical
  let Ω := PDE.euclideanBall v₀ r
  have hΩ : IsOpen Ω := PDE.isOpen_euclideanBall v₀ r
  have hΩb : Bornology.IsBounded Ω := Occupation.isBounded_euclideanBall v₀ hr
  have hleft : a - 1 < a := by linarith
  have hleftT := hleft.trans haT
  have hK := isCompact_scalarParabolicClosedCylinder (a - 1) T hΩb
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hFM : ∀ z ∈ scalarParabolicClosedCylinder (a - 1) T Ω, |F z| ≤ M := by
    intro z hz
    rw [← Real.norm_eq_abs]
    exact (hC z hz).trans (le_max_left _ _)
  obtain ⟨w, hw, he, ht, hs⟩ : ∃ w : TimeVelocity d → ℝ,
      IsScalarC12On w (scalarParabolicOpenCylinder (a - 1) T (PDE.euclideanBall v₀ r)) ∧
      (∀ z ∈ scalarParabolicOpenCylinder (a - 1) T (PDE.euclideanBall v₀ r),
        scalarTimeDerivative w z +
          matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) = F z) ∧
      (∀ z ∈ scalarParabolicOpenCylinder (a - 1) T (PDE.euclideanBall v₀ r),
        |w z| ≤ M * (T - z.1)) ∧
      ∀ z ∈ scalarParabolicOpenCylinder (a - 1) T (PDE.euclideanBall v₀ r),
        |w z| ≤ sourceBallBarrier v₀ r lam M z.2 := by
    let a := (a - 1)
    let Ω := PDE.euclideanBall v₀ r
    have hΩ : IsOpen Ω := PDE.isOpen_euclideanBall v₀ r
    have hΩb : Bornology.IsBounded Ω := Occupation.isBounded_euclideanBall v₀ hr
    obtain ⟨u, g, hdu, hu, w, _, hs, hw, he⟩ : ∃ (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
        (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr hleftT) u g),
        IsReverseTimeVariationalEnergySolution a T hleftT hΩ hΩb A
          (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
          ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ 0 u g hdu ∧
        ∃ w : TimeVelocity d → ℝ,
          MemLp w 2 (timeVelocityVolumeOn (Ioo a T ×ˢ Ω)) ∧
          (∀ᵐ t ∂volume.restrict (Ioo a T),
            (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y) ∧
          IsScalarC12On w (scalarParabolicOpenCylinder a T Ω) ∧
          ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
            scalarTimeDerivative w z +
              matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) = F z := by
      have hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
          (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
      have hbs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : PDE.Vec d))
          (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
      have hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
          (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
      have hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
      obtain ⟨u, g, hdu, hu⟩ := exists_reverseTime_variational_energy_solution a T lam Lam
        hleftT hlam hLam hΩ hΩb A (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
        hAs hbs hcs hFs (fun z _ => hlo z.1 z.2) (fun z _ => hhi z.1 z.2)
        (fun _ _ => le_rfl) 0
      obtain ⟨w, hwl, hwslice, hwr, hwe, _⟩ := exists_smoothInteriorBootstrap hd a T hleftT hΩ hΩb
        lam Lam hlam hLam A (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
        hAs hbs hcs hFs (fun z _ => hlo z.1 z.2) (fun z _ => hhi z.1 z.2)
        (fun _ _ => le_rfl) 0 u g hdu hu
      refine ⟨u, g, hdu, hu, w, hwl, hwslice, hwr, ?_⟩
      intro z hz
      simpa only [matrixContraction, coefficientAt, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero, Prod.mk.eta] using hwe z hz
    have htime : ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ M * (T - z.1) := by
      have hw := hw.continuousOn
      have hwslice := hs
      have hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
          (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
      have hbs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : PDE.Vec d))
          (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
      have hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
          (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
      have hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
      have henv := hu.abs_reverseTimeHilbertRepresentative_le_affine a T lam hleftT hlam
        hΩ hΩb A (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y)) hAs hbs hcs hFs
        (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl) 0 M le_rfl hM hFM 0
        (by filter_upwards [Lp.coeFn_zero ℝ 2 (PDE.volumeOn Ω)] with y hy
            rw [hy]; simp only [Pi.zero_apply, abs_zero, le_refl]) u g hdu
      have hraw : ∀ᵐ τ ∂reverseTimeVolume (T - a),
          ∀ hτ : τ ∈ Ioo 0 (T - a),
            ∀ᵐ y ∂PDE.volumeOn Ω, |valueCLM hΩ (u τ) y| ≤ M * τ := by
        filter_upwards [(reverseTimeHilbertRepresentative_spec hΩ (T - a)
          (sub_pos.mpr hleftT) u g hdu).1] with τ hrep hτ
        have hb := henv τ ⟨hτ.1.le, hτ.2.le⟩
        rw [hrep hτ] at hb
        simpa only [zero_add, mul_comm] using hb
      have horig := (sourceTimeReflection_measurePreserving a T).quasiMeasurePreserving.ae hraw
      have hbound : ∀ᵐ t ∂volume.restrict (Ioo a T),
          ∀ᵐ y ∂PDE.volumeOn Ω, |w (t, y)| ≤ M * (T - t) := by
        filter_upwards [hwslice, horig, ae_restrict_mem measurableSet_Ioo] with t hs hr ht
        have ht' : T - t ∈ Ioo 0 (T - a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
        filter_upwards [hs, hr ht'] with y hy hb
        rw [hy]
        exact hb
      exact abs_le_source_time_of_continuousOn_of_ae_slices hΩ a T M w hw hbound
    obtain ⟨q, hq, hqe, hqo⟩ : ∃ q : PDE.H10Function (PDE.euclideanBall v₀ r),
        ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
        EqOn q.toH1Function.toFun (sourceBallBarrier v₀ r lam M)
          (closure (PDE.euclideanBall v₀ r)) ∧
        ∀ z : TimeVelocity d, z.2 ∈ PDE.euclideanBall v₀ r →
          scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
            (fun z => q.toH1Function.toFun z.2) z = sourceBallBarrierForcing lam M A z := by
      obtain ⟨q, hq, _, hqe⟩ := exists_h10_smooth_barrier_eqOn
        (PDE.isOpen_euclideanBall v₀ r)
        (Occupation.isBounded_euclideanBall v₀ hr).isCompact_closure
        (sourceBallBarrier v₀ r lam M) (contDiff_sourceBallBarrier v₀ r lam M)
        (fun y hy => sourceBallBarrier_nonneg v₀ r lam M hlam hM (subset_closure hy))
        (fun y hy => sourceBallBarrier_zero_frontier v₀ r lam M hy)
      refine ⟨q, hq, hqe, ?_⟩
      intro z hz
      rw [stationary_scalarOperator_eqOn (PDE.isOpen_euclideanBall v₀ r)
        q.toH1Function.toFun (sourceBallBarrier v₀ r lam M)
        (hqe.mono subset_closure) A z hz, scalarOperator_sourceBallBarrier]
      rfl
    let G := sourceBallBarrierForcing lam M A
    have hG : ContDiff ℝ (⊤ : ℕ∞) (sourceBallBarrierForcing lam M A) := by
        have htr : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => (A z.1 z.2).trace) := by
          unfold Matrix.trace Matrix.diag
          apply ContDiff.sum
          intro i _
          exact (contDiff_apply ℝ ℝ i).comp
            ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
        exact (contDiff_const.mul htr).neg.div_const _

      /- The ball barrier has an actual smooth H10 realization with its literal trace forcing. -/
    have hqn : ∀ y ∈ Ω, 0 ≤ q.toH1Function.toFun y := by
      intro y hy
      rw [hqe (subset_closure hy)]
      exact sourceBallBarrier_nonneg v₀ r lam M hlam hM (subset_closure hy)
    have hqeq : ∀ z ∈ Icc a T ×ˢ Ω,
        scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
          (fun z => q.toH1Function.toFun z.2) z = G z := fun z hz => hqo z hz.2
    have hGF : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, G z ≤ -|F z| := by
      intro z hz
      have hGle : G z ≤ -M := by
        change sourceBallBarrierForcing lam M A z ≤ -M
        rw [show sourceBallBarrierForcing lam M A z =
          scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0)
            (fun z => sourceBallBarrier v₀ r lam M z.2) z from
              (scalarOperator_sourceBallBarrier v₀ r lam M A z).symm]
        rw [scalarOperator_sourceBallBarrier]
        have htr := (Matrix.le_iff.mp (hlo z.1 z.2)).trace_nonneg
        rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at htr
        simp only [Fintype.card_fin, smul_eq_mul] at htr
        apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hd)) hlam)).2
        nlinarith [mul_nonneg hM (show 0 ≤ (A z.1 z.2).trace - (d : ℝ) * lam by linarith)]
      exact hGle.trans (neg_le_neg (hFM z hz))
    have henergy : ∀ τ : ℝ, ∀ hτ : τ ∈ Icc 0 (T - a), ∀ᵐ y ∂PDE.volumeOn Ω, |reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr hleftT) u g hdu ⟨τ, hτ⟩ y| ≤ q.toH1Function.toFun y := by
      have hq : ContDiff ℝ 2 q.toH1Function.toFun := (hq.of_le (by simp))
      let Q := h10HilbertGraphOfH10Function hΩ q
      let hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
          (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
      let hbs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : PDE.Vec d))
          (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
      let hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
          (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
      let hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
      let hGs : IsSmoothOnNeighborhood G (scalarParabolicClosedCylinder a T Ω) :=
        ⟨univ, isOpen_univ, subset_univ _, hG.contDiffOn⟩
      have hinit : ∀ᵐ y ∂PDE.volumeOn Ω,
          (0 : PDE.ScalarLp Ω 2) y ≤ valueCLM hΩ Q y := by
        filter_upwards [Lp.coeFn_zero ℝ 2 (PDE.volumeOn Ω),
          valueCLM_h10HilbertGraphOfH10Function hΩ q,
          ae_restrict_mem hΩ.measurableSet] with y hy hqy hyo
        rw [hy, hqy]
        exact hqn y hyo
      have hqenergy : IsReverseTimeVariationalEnergySolution a T hleftT hΩ hΩb A
          (fun _ _ => 0) (fun _ _ => 0) (fun t y => G (t, y))
          ⟨univ, isOpen_univ, subset_univ _, hG.contDiffOn⟩
          (valueCLM hΩ (h10HilbertGraphOfH10Function hΩ q))
          (stationarySourceCurve hΩ (T - a) (h10HilbertGraphOfH10Function hΩ q)) 0
          (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr hleftT)
            (h10HilbertGraphOfH10Function hΩ q)) := by
        let Q := h10HilbertGraphOfH10Function hΩ q
        let hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
            (scalarParabolicClosedCylinder a T Ω) :=
          ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
        let hbs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : PDE.Vec d))
            (scalarParabolicClosedCylinder a T Ω) :=
          ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
        let hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
            (scalarParabolicClosedCylinder a T Ω) :=
          ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
        let hFs : IsSmoothOnNeighborhood G (scalarParabolicClosedCylinder a T Ω) :=
          ⟨univ, isOpen_univ, subset_univ _, hG.contDiffOn⟩
        constructor
        · change reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr hleftT)
            (stationarySourceCurve hΩ (T - a) Q) 0
            (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr hleftT) Q)
            ⟨0, ⟨le_rfl, (sub_pos.mpr hleftT).le⟩⟩ = valueCLM hΩ Q
          rw [stationarySourceCurve_hilbertRepresentative]
          rfl
        · filter_upwards [stationarySourceCurve_ae hΩ (T - a) Q,
            Lp.coeFn_zero (H10HilbertGraphDual hΩ) 2 (reverseTimeVolume (T - a))]
            with τ hqτ hgτ
          intro hτ v
          rw [hqτ, hgτ]
          change 0 + reverseTimeSpatialForm hΩ T τ A (fun _ _ => 0) (fun _ _ => 0) Q v = _
          rw [zero_add]
          have hτc : τ ∈ Icc 0 (T - a) := ⟨hτ.1.le, hτ.2.le⟩
          let fτ := reverseTimeSourceSlice T τ (fun t y => G (t, y))
            (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood a T hΩ hΩb
              (fun t y => G (t, y)) hFs τ hτc)
          let L := reverseTimeSpatialFormOperator a T hleftT hΩ hΩb A
            (fun _ _ => 0) (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q
          let R := reverseTimeSourceFunctional hΩ fτ
          have hLR : L = R := by
            apply ContinuousLinearMap.coeFn_injective
            apply Continuous.ext_on
              (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
              L.continuous R.continuous
            rintro _ ⟨ψ, rfl⟩
            change L (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
              R (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)
            have ha : ∀ i j, ContDiffOn ℝ 1 (fun y => A (T - τ) y i j) Ω := by
              intro i j
              exact contDiffOn_one_coefficientEntry_spatialSlice_of_smoothOnNeighborhood
                a T (T - τ) A hAs (by constructor <;> linarith [hτ.1, hτ.2]) i j
            rw [show L _ = reverseTimeSpatialForm hΩ T τ A (fun _ _ => 0)
              (fun _ _ => 0) Q _ from reverseTimeSpatialFormOperator_apply
                a T hleftT hΩ hΩb A (fun _ _ => 0) (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q _,
              reverseTimeSpatialForm_stationary_barrier_weakIdentity hΩ T τ A
                (fun _ _ => 0) (fun _ _ => 0) q hq ha
                (fun _ => continuousOn_const) continuousOn_const ψ]
            change _ = reverseTimeSourceFunctional hΩ fτ _
            rw [reverseTimeSourceFunctional_apply, L2.inner_def, ← integral_neg]
            apply integral_congr_ae
            filter_upwards [coeFn_reverseTimeSourceSlice T τ (fun t y => G (t, y))
              (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood a T hΩ hΩb
                (fun t y => G (t, y)) hFs τ hτc),
              ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ,
              ae_restrict_mem hΩ.measurableSet] with y hFy hψ hy
            rw [hFy, hψ, hqeq (T - τ, y)
              ⟨by constructor <;> linarith [hτ.1, hτ.2], hy⟩]
            simp only [RCLike.inner_apply, conj_trivial]
            ring
          rw [← reverseTimeSpatialFormOperator_apply a T hleftT hΩ hΩb A
            (fun _ _ => 0) (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q v]
          exact congrArg (fun D : H10HilbertGraphDual hΩ => D v) hLR
      have hupper := reverseTimeVariationalEnergySolution_le a T lam hleftT hlam hΩ hΩb
        A (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y)) (fun t y => G (t, y))
        hAs hbs hcs hFs hGs (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl)
        (fun z hz => (hGF z hz).trans (neg_abs_le (F z)))
        0 (valueCLM hΩ Q) hinit u g hdu hu
        (stationarySourceCurve hΩ (T - a) Q) 0
        (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr hleftT) Q) hqenergy
      have hninit : ∀ᵐ y ∂PDE.volumeOn Ω,
          (-(0 : PDE.ScalarLp Ω 2)) y ≤ valueCLM hΩ Q y := by
        simpa only [neg_zero] using hinit
      have hneg := reverseTimeVariationalEnergySolution_le a T lam hleftT hlam hΩ hΩb
        A (fun _ _ => 0) (fun _ _ => 0) (fun t y => -F (t, y)) (fun t y => G (t, y))
        hAs hbs hcs (IsSmoothOnNeighborhood.neg hFs) hGs
        (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl)
        (fun z hz => (hGF z hz).trans (neg_le_neg (le_abs_self (F z))))
        (-0) (valueCLM hΩ Q) hninit ((-1 : ℝ) • u) ((-1 : ℝ) • g)
        (hdu.smul (-1)) hu.neg (stationarySourceCurve hΩ (T - a) Q) 0
        (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr hleftT) Q) hqenergy
      rw [stationarySourceCurve_hilbertRepresentative] at hupper hneg
      rw [reverseTimeHilbertRepresentative_neg_eq] at hneg
      intro τ hτ
      filter_upwards [hupper τ hτ, hneg τ hτ,
        valueCLM_h10HilbertGraphOfH10Function hΩ q,
        Lp.coeFn_neg (reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr hleftT)
          u g hdu ⟨τ, hτ⟩)] with y hu₁ hu₂ hqy hn
      change _ ≤ valueCLM hΩ Q y at hu₁
      change (-reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr hleftT)
        u g hdu ⟨τ, hτ⟩) y ≤ valueCLM hΩ Q y at hu₂
      rw [hn, Pi.neg_apply, hqy] at hu₂
      rw [hqy] at hu₁
      exact abs_le.mpr ⟨by linarith, hu₁⟩
    have hspace := classicalEnergyRepresentative_abs_le_continuous_barrier hΩ a T hleftT
      u g hdu q.toH1Function.toFun hq.continuous henergy w hw.continuousOn hs
    refine ⟨w, hw, he, htime, ?_⟩
    intro z hz
    simpa only [hqe (subset_closure hz.2)] using hspace z hz
  let U := scalarParabolicOpenCylinder (a - 1) T Ω
  let D := scalarParabolicOpenCylinder a T Ω
  let W := sourceInteriorZeroExtension (a - 1) T Ω w
  have hsub : D ⊆ U := prod_mono (Ioo_subset_Ioo hleft.le le_rfl) (Subset.refl _)
  have hWD : EqOn W w D := by
    intro z hz
    exact piecewise_eq_of_mem U w (fun _ => 0) (hsub hz)
  have hwD : IsScalarC12On w D :=
    ⟨hw.continuousOn.mono hsub,
      fun z hz => hw.timeSlice_differentiableAt (hsub hz),
      fun z hz => hw.spatialSlice_contDiffAt (hsub hz),
      hw.continuousOn_scalarTimeDerivative.mono hsub,
      hw.continuousOn_scalarSpatialGradient.mono hsub,
      hw.continuousOn_scalarSpatialHessian.mono hsub⟩
  have hD : IsOpen D := isOpen_Ioo.prod hΩ
  have hWc : ContinuousOn (sourceInteriorZeroExtension (a - 1) T (PDE.euclideanBall v₀ r) w)
      (scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r)) := by
    let a₀ := (a - 1)
    have hw := hw.continuousOn
    classical
    intro p hp
    by_cases hpt : p.1 = T
    · exact (continuousWithinAt_source_zeroExtension_terminal a₀ T M hM w ht p hpt).mono
        (prod_mono (Icc_subset_Icc hleft.le le_rfl) (Subset.refl _))
    · by_cases hpy : p.2 ∈ PDE.euclideanBall v₀ r
      · let U := scalarParabolicOpenCylinder a₀ T (PDE.euclideanBall v₀ r)
        have hU : IsOpen U := isOpen_Ioo.prod (PDE.isOpen_euclideanBall v₀ r)
        have hpu : p ∈ U := ⟨⟨lt_of_lt_of_le hleft hp.1.1,
          lt_of_le_of_ne hp.1.2 hpt⟩, hpy⟩
        have he : sourceInteriorZeroExtension a₀ T (PDE.euclideanBall v₀ r) w =ᶠ[𝓝 p] w := by
          filter_upwards [hU.mem_nhds hpu] with z hz
          exact piecewise_eq_of_mem U w (fun _ => 0) hz
        exact ((hw.continuousAt (hU.mem_nhds hpu)).congr_of_eventuallyEq he).continuousWithinAt
      · have hpf : p.2 ∈ frontier (PDE.euclideanBall v₀ r) := by
          rw [(PDE.isOpen_euclideanBall v₀ r).frontier_eq]
          exact ⟨hp.2, hpy⟩
        have hc : ContinuousAt (sourceInteriorZeroExtension a₀ T (PDE.euclideanBall v₀ r) w) p := by
            classical
            let Ω := PDE.euclideanBall v₀ r
            let U := scalarParabolicOpenCylinder a₀ T Ω
            let W := sourceInteriorZeroExtension a₀ T Ω w
            have hpo : p.2 ∉ Ω := by
              rw [(PDE.isOpen_euclideanBall v₀ r).frontier_eq] at hpf
              exact hpf.2
            have hpW : W p = 0 := by
              exact piecewise_eq_of_notMem U w (fun _ => 0) (fun h => hpo h.2)
            have hbW (z : TimeVelocity d) : ‖W z‖ ≤ |sourceBallBarrier v₀ r lam M z.2| := by
              by_cases hz : z ∈ U
              · rw [show W z = w z from piecewise_eq_of_mem U w (fun _ => 0) hz,
                  Real.norm_eq_abs]
                exact (hs z hz).trans (le_abs_self _)
              · rw [show W z = 0 from piecewise_eq_of_notMem U w (fun _ => 0) hz, norm_zero]
                exact abs_nonneg _
            have hc : Continuous (fun z : TimeVelocity d => |sourceBallBarrier v₀ r lam M z.2|) :=
              ((contDiff_sourceBallBarrier v₀ r lam M).continuous.comp continuous_snd).abs
            have hz : Tendsto (fun z : TimeVelocity d => |sourceBallBarrier v₀ r lam M z.2|)
                (𝓝 p) (𝓝 0) := by
              simpa only [sourceBallBarrier_zero_frontier v₀ r lam M hpf, abs_zero] using
                (hc.continuousAt (x := p)).tendsto
            change Tendsto W (𝓝 p) (𝓝 (W p))
            rw [hpW]
            exact tendsto_zero_iff_norm_tendsto_zero.2
              (squeeze_zero (fun _ => norm_nonneg _) hbW hz)

          /- A time collar and both envelopes give continuity on the entire closed cylinder. -/
        exact hc.continuousWithinAt
  have hWr := Occupation.isScalarC12On_congr_open hD hwD hWD
  obtain ⟨hdt, _, hdd⟩ := Occupation.scalarJet_eqOn_of_eqOn_open hD hWD
  refine ⟨W, hWc, hWr, ?_, ?_, ?_⟩
  · intro z hz
    simp only [scalarParabolicZeroOrderOperator_apply, Pi.zero_apply, PDE.vecDot,
      zero_mul, Finset.sum_const_zero, add_zero, hdt hz, hdd hz]
    exact he z (hsub hz)
  · intro y _
    exact piecewise_eq_of_notMem U w (fun _ => 0)
      (fun h => (lt_irrefl T) h.1.2)
  · intro z hz
    have hzo : z.2 ∉ Ω := by
      have hf := hz.2
      rw [hΩ.frontier_eq] at hf
      exact hf.2
    exact piecewise_eq_of_notMem U w (fun _ => 0) (fun h => hzo h.2)

end HypoellipticAleksandrov.Parabolic.LocalHolder
