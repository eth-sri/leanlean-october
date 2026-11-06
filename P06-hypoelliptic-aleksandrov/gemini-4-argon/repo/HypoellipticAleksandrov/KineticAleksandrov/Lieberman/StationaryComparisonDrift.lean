module

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.StationaryEnergyDrift
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalComparison
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalNegation
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothH10DenseRange
import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothNeighborhoodSpatialSlices
import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierWeakIdentity
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonEnergyConstant

/-! # Two-sided variational bounds by stationary spatial barriers

Comparison with the same barrier bounds the solution and its negative.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open HypoellipticAleksandrov.Parabolic.Dirichlet HypoellipticAleksandrov.Parabolic.LocalHolder
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise
open scoped RealInnerProductSpace

/- A stationary source supersolution bounds the absolute value of the energy solution. -/
theorem variational_abs_le_stationary_withDrift {d Ω} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (a T : ℝ) (haT : a < T) (lam : ℝ) (hlam : 0 < lam)
    (A : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
    (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (F G : TimeVelocity d → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (q : PDE.H10Function Ω) (hq : ContDiff ℝ 2 q.toH1Function.toFun)
    (hqn : ∀ y ∈ Ω, 0 ≤ q.toH1Function.toFun y)
    (heq : ∀ z ∈ Icc a T ×ˢ Ω,
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
        (fun z => q.toH1Function.toFun z.2) z = G z)
    (hGF : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, G z ≤ -|F z|)
    (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
    (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g)
    (hu : IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
      b (fun _ _ => 0) (fun t y => F (t, y))
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ 0 u g hdu) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Icc 0 (T - a), ∀ᵐ y ∂PDE.volumeOn Ω,
      |reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
        u g hdu ⟨τ, hτ⟩ y| ≤ q.toH1Function.toFun y := by
  let Q := h10HilbertGraphOfH10Function hΩ q
  let hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
  let hbs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hb.contDiffOn⟩
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
  have hqenergy : IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
      b (fun _ _ => 0) (fun t y => G (t, y))
      ⟨univ, isOpen_univ, subset_univ _, hG.contDiffOn⟩
      (valueCLM hΩ (h10HilbertGraphOfH10Function hΩ q))
      (stationarySourceCurve hΩ (T - a) (h10HilbertGraphOfH10Function hΩ q)) 0
      (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT)
        (h10HilbertGraphOfH10Function hΩ q)) := by
    let Q := h10HilbertGraphOfH10Function hΩ q
    let hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
        (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
    let hbs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
        (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, hb.contDiffOn⟩
    let hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
        (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
    let hFs : IsSmoothOnNeighborhood G (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, hG.contDiffOn⟩
    constructor
    · change reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
        (stationarySourceCurve hΩ (T - a) Q) 0
        (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) Q)
        ⟨0, ⟨le_rfl, (sub_pos.mpr haT).le⟩⟩ = valueCLM hΩ Q
      rw [stationarySourceCurve_hilbertRepresentative]
      rfl
    · filter_upwards [stationarySourceCurve_ae hΩ (T - a) Q,
        Lp.coeFn_zero (H10HilbertGraphDual hΩ) 2 (reverseTimeVolume (T - a))]
        with τ hqτ hgτ
      intro hτ v
      rw [hqτ, hgτ]
      change 0 + reverseTimeSpatialForm hΩ T τ A b (fun _ _ => 0) Q v = _
      rw [zero_add]
      have hτc : τ ∈ Icc 0 (T - a) := ⟨hτ.1.le, hτ.2.le⟩
      let fτ := reverseTimeSourceSlice T τ (fun t y => G (t, y))
        (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood a T hΩ hΩb
          (fun t y => G (t, y)) hFs τ hτc)
      let L := reverseTimeSpatialFormOperator a T haT hΩ hΩb A
        b (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q
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
        rw [show L _ = reverseTimeSpatialForm hΩ T τ A b
          (fun _ _ => 0) Q _ from reverseTimeSpatialFormOperator_apply
            a T haT hΩ hΩb A b (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q _,
          reverseTimeSpatialForm_stationary_barrier_weakIdentity hΩ T τ A
            b (fun _ _ => 0) q hq ha
            (continuousOn_vectorEntry_spatialSlice_of_smoothOnNeighborhood
              a T (T - τ) b hbs (by constructor <;> linarith [hτ.1, hτ.2])) continuousOn_const ψ]
        change _ = reverseTimeSourceFunctional hΩ fτ _
        rw [reverseTimeSourceFunctional_apply, L2.inner_def, ← integral_neg]
        apply integral_congr_ae
        filter_upwards [coeFn_reverseTimeSourceSlice T τ (fun t y => G (t, y))
          (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood a T hΩ hΩb
            (fun t y => G (t, y)) hFs τ hτc),
          ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ,
          ae_restrict_mem hΩ.measurableSet] with y hFy hψ hy
        rw [hFy, hψ, heq (T - τ, y)
          ⟨by constructor <;> linarith [hτ.1, hτ.2], hy⟩]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      rw [← reverseTimeSpatialFormOperator_apply a T haT hΩ hΩb A
        b (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q v]
      exact congrArg (fun D : H10HilbertGraphDual hΩ => D v) hLR
  have hupper := reverseTimeVariationalEnergySolution_le a T lam haT hlam hΩ hΩb
    A b (fun _ _ => 0) (fun t y => F (t, y)) (fun t y => G (t, y))
    hAs hbs hcs hFs hGs (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl)
    (fun z hz => (hGF z hz).trans (neg_abs_le (F z)))
    0 (valueCLM hΩ Q) hinit u g hdu hu
    (stationarySourceCurve hΩ (T - a) Q) 0
    (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) Q) hqenergy
  have hninit : ∀ᵐ y ∂PDE.volumeOn Ω,
      (-(0 : PDE.ScalarLp Ω 2)) y ≤ valueCLM hΩ Q y := by
    simpa only [neg_zero] using hinit
  have hneg := reverseTimeVariationalEnergySolution_le a T lam haT hlam hΩ hΩb
    A b (fun _ _ => 0) (fun t y => -F (t, y)) (fun t y => G (t, y))
    hAs hbs hcs (IsSmoothOnNeighborhood.neg hFs) hGs
    (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl)
    (fun z hz => (hGF z hz).trans (neg_le_neg (le_abs_self (F z))))
    (-0) (valueCLM hΩ Q) hninit ((-1 : ℝ) • u) ((-1 : ℝ) • g)
    (hdu.smul (-1)) hu.neg (stationarySourceCurve hΩ (T - a) Q) 0
    (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) Q) hqenergy
  rw [stationarySourceCurve_hilbertRepresentative] at hupper hneg
  rw [reverseTimeHilbertRepresentative_neg_eq] at hneg
  intro τ hτ
  filter_upwards [hupper τ hτ, hneg τ hτ,
    valueCLM_h10HilbertGraphOfH10Function hΩ q,
    Lp.coeFn_neg (reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
      u g hdu ⟨τ, hτ⟩)] with y hu₁ hu₂ hqy hn
  change _ ≤ valueCLM hΩ Q y at hu₁
  change (-reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
    u g hdu ⟨τ, hτ⟩) y ≤ valueCLM hΩ Q y at hu₂
  rw [hn, Pi.neg_apply, hqy] at hu₂
  rw [hqy] at hu₁
  exact abs_le.mpr ⟨by linarith, hu₁⟩

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
