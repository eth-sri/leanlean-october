module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev
public import PDEFoundation.Sobolev.ClassicalGradient
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
import HypoellipticAleksandrov.Parabolic.C2ToScalarC12

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Function MeasureTheory Set Topology
open scoped BigOperators

/-- Classical derivative in one native spatial coordinate. -/
noncomputable def spatialPartial {d : ℕ} (i : Fin d)
    (f : PDE.Vec d → ℝ) (y : PDE.Vec d) : ℝ :=
  (fderiv ℝ f y) (PDE.basisVec i)

/-- A spatial coordinate derivative lowers finite differentiability by one
on an open set. -/
theorem ContDiffOn.spatialPartial
    {d n : ℕ} {O : Set (PDE.Vec d)} {f : PDE.Vec d → ℝ}
    (hf : ContDiffOn ℝ (n + 1) f O)
    (hO : IsOpen O) (k : Fin d) :
    ContDiffOn ℝ n (spatialPartial k f) O := by
  have hdf : ContDiffOn ℝ n (fderiv ℝ f) O :=
    hf.fderiv_of_isOpen hO (by simp)
  exact ContDiffOn.clm_apply hdf contDiffOn_const






/-- Integration by parts on an open set when the differentiated right factor
is compactly supported in that set. -/
theorem setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_right
    {d : ℕ} (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (i : Fin d) (f g : PDE.Vec d → ℝ)
    (hf : ContDiffOn ℝ 1 f O) (hg : ContDiffOn ℝ 1 g O)
    (hgcompact : HasCompactSupport g) (hgsupport : tsupport g ⊆ O) :
    (∫ y in O, f y * spatialPartial i g y ∂volume) =
      -∫ y in O, spatialPartial i f y * g y ∂volume    := by
  have continuous_spatialPartial_mul_of_right_compactSupport :
      Continuous (fun y => spatialPartial i f y * g y) := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ O
    · exact (((hf.contDiffAt (hO.mem_nhds hy)).continuousAt_fderiv (by norm_num)).clm_apply
        continuousAt_const).mul
        (hg.contDiffAt (hO.mem_nhds hy)).continuousAt
    · have hyg : y ∉ tsupport g := fun h => hy (hgsupport h)
      have heq : (fun z => spatialPartial i f z * g z) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyg] with z hz
        simp [hz]
      exact continuousAt_const.congr_of_eventuallyEq heq
  have continuous_mul_spatialPartial_of_right_compactSupport :
      Continuous (fun y => f y * spatialPartial i g y) := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ O
    · exact (hf.contDiffAt (hO.mem_nhds hy)).continuousAt.mul
        (((hg.contDiffAt (hO.mem_nhds hy)).continuousAt_fderiv (by norm_num)).clm_apply
          continuousAt_const)
    · have hyg : y ∉ tsupport g := fun h => hy (hgsupport h)
      have hzero : (fun z => spatialPartial i g z) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hyg).fderiv (𝕜 := ℝ)] with z hz
        simp [spatialPartial, hz]
      have heq : (fun z => f z * spatialPartial i g z) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hzero] with z hz
        simp [hz]
      exact continuousAt_const.congr_of_eventuallyEq heq
  have contDiff_mul_of_right_compactSupport :
      ContDiff ℝ 1 (fun y => f y * g y) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ O
    · exact (hf.contDiffAt (hO.mem_nhds hy)).mul (hg.contDiffAt (hO.mem_nhds hy))
    · have hyg : y ∉ tsupport g := fun h => hy (hgsupport h)
      have heq : (fun z => f z * g z) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyg] with z hz
        simp [hz]
      exact (contDiffAt_const (c := 0)).congr_of_eventuallyEq heq
  let p : PDE.Vec d → ℝ := fun y => f y * g y
  have hp :=
    contDiff_mul_of_right_compactSupport
  have hpcompact : HasCompactSupport p := hgcompact.mul_left
  have hAcompact : HasCompactSupport (fun y => f y * spatialPartial i g y) :=
    (hgcompact.fderiv_apply ℝ (PDE.basisVec i)).mul_left
  have hBcompact : HasCompactSupport (fun y => spatialPartial i f y * g y) :=
    hgcompact.mul_left
  have hA : Integrable (fun y => f y * spatialPartial i g y) :=
    continuous_mul_spatialPartial_of_right_compactSupport.integrable_of_hasCompactSupport hAcompact
  have hB : Integrable (fun y => spatialPartial i f y * g y) :=
    continuous_spatialPartial_mul_of_right_compactSupport.integrable_of_hasCompactSupport hBcompact
  have hpint : Integrable p := hp.continuous.integrable_of_hasCompactSupport hpcompact
  have hdpint : Integrable (fun y => fderiv ℝ p y (PDE.basisVec i)) :=
    ((hp.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (hpcompact.fderiv_apply ℝ (PDE.basisVec i))
  have hzero : (∫ y, fderiv ℝ p y (PDE.basisVec i) ∂volume) = 0 := by
    simpa using (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := fun _ => 1) (by simp) (by simpa using hdpint) (by simpa using hpint) (by fun_prop) (fun x _ => hp.differentiable (by norm_num) x))
  have hprod (y : PDE.Vec d) (hy : y ∈ O) :
      fderiv ℝ p y (PDE.basisVec i) =
        spatialPartial i f y * g y + f y * spatialPartial i g y := by
    rw [show p = fun z => f z * g z from rfl]
    rw [fderiv_fun_mul ((hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num))
      ((hg.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num))]
    simp [spatialPartial, add_comm, mul_comm]
  have houtside (y : PDE.Vec d) (hy : y ∉ O) :
      fderiv ℝ p y (PDE.basisVec i) = 0 := by
    exact congrArg (fun L => L (PDE.basisVec i))
      (fderiv_of_notMem_tsupport ℝ (fun hp' => hy (hgsupport (tsupport_mul_subset_right hp'))))
  have hglobal : (∫ y, fderiv ℝ p y (PDE.basisVec i) ∂volume) =
      ∫ y in O, (spatialPartial i f y * g y + f y * spatialPartial i g y) ∂volume := by
    rw [← integral_indicator hO.measurableSet]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ O
    · simp [Set.indicator_of_mem hy, hprod y hy]
    · simp [Set.indicator_of_notMem hy, houtside y hy]
  rw [hglobal] at hzero
  rw [integral_add hB.integrableOn hA.integrableOn] at hzero
  linarith



private theorem spatialPartial_mul_local
    {d : ℕ} {D : Set (PDE.Vec d)} (hD : IsOpen D) (i : Fin d)
    {f g : PDE.Vec d → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (hg : ContDiffOn ℝ 1 g D) {y : PDE.Vec d} (hy : y ∈ D) :
    spatialPartial i (fun x ↦ f x * g x) y =
      spatialPartial i f y * g y + f y * spatialPartial i g y := by
  rw [spatialPartial, fderiv_fun_mul
    ((hf.contDiffAt (hD.mem_nhds hy)).differentiableAt (by norm_num))
    ((hg.contDiffAt (hD.mem_nhds hy)).differentiableAt (by norm_num))]
  simp [ContinuousLinearMap.smul_apply, spatialPartial]
  ring

private theorem integrable_mul_of_right_compactSupport
    {d : ℕ} {D : Set (PDE.Vec d)} {f g : PDE.Vec d → ℝ}
    (hf : ContinuousOn f D) (hg : Continuous g)
    (hgcompact : HasCompactSupport g) (hgsupport : tsupport g ⊆ D) :
    Integrable (fun y ↦ f y * g y) := by
  have hon : IntegrableOn (fun y ↦ f y * g y) (tsupport g) :=
    ((hf.mono hgsupport).mul hg.continuousOn).integrableOn_compact hgcompact
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hon
  exact (Function.support_mul_subset_right f g).trans (subset_tsupport g)

/-- The lower-order remainder in the generic reverse-time classical identity
is integrable against a bundled smooth compactly supported test function. -/
theorem integrableOn_reverseTimeClassicalRemainder_weakTest
    {d : ℕ} {D : Set (PDE.Vec d)} (hD : IsOpen D)
    (r₁ τ : ℝ)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (p : TimeVelocity d → ℝ)
    (ψ : PDE.WeakTestFunction D)
    (ha : ∀ i j : Fin d,
      ContDiffOn ℝ 1 (fun y ↦ a (r₁ - τ) y i j) D)
    (hb : ∀ j : Fin d,
      ContinuousOn (fun y ↦ b (r₁ - τ) y j) D)
    (hc : ContinuousOn (fun y ↦ c (r₁ - τ) y) D)
    (hp : IsScalarC12On p ({r₁ - τ} ×ˢ D)) :
    IntegrableOn
      (fun y ↦
        (-scalarTimeDerivative p (r₁ - τ, y)) * ψ y +
          (∑ j : Fin d,
            reverseTimeDivergenceDrift r₁ a b τ y j *
              scalarSpatialGradient p (r₁ - τ, y) j * ψ y) -
          c (r₁ - τ) y * p (r₁ - τ, y) * ψ y)
      D := by
  have hpair : Continuous (fun y : PDE.Vec d ↦ (r₁ - τ, y)) :=
    continuous_const.prodMk continuous_id
  have hpairMem : MapsTo (fun y : PDE.Vec d ↦ (r₁ - τ, y)) D
      ({r₁ - τ} ×ˢ D) := fun y hy ↦ ⟨Set.mem_singleton _, hy⟩
  have htime : ContinuousOn
      (fun y ↦ scalarTimeDerivative p (r₁ - τ, y)) D :=
    hp.continuousOn_scalarTimeDerivative.comp hpair.continuousOn hpairMem
  have hpvalue : ContinuousOn (fun y ↦ p (r₁ - τ, y)) D :=
    hp.continuousOn.comp hpair.continuousOn hpairMem
  have hgradient (j : Fin d) : ContinuousOn
      (fun y ↦ scalarSpatialGradient p (r₁ - τ, y) j) D :=
    ((continuous_apply j).comp_continuousOn hp.continuousOn_scalarSpatialGradient).comp
      hpair.continuousOn hpairMem
  have hcoeffPartial (i j : Fin d) : ContinuousOn
      (spatialPartial i (fun y ↦ a (r₁ - τ) y i j)) D := by
    exact ((ha i j).fderiv_of_isOpen hD (m := 0) (by norm_num)).clm_apply
      contDiffOn_const |>.continuousOn
  have hdivergence (j : Fin d) : ContinuousOn
      (fun y ↦ scalarSpatialCoefficientDivergence a (r₁ - τ, y) j) D := by
    unfold scalarSpatialCoefficientDivergence
    simpa only [spatialPartial] using
      (continuousOn_finset_sum Finset.univ fun i _ ↦ hcoeffPartial i j)
  have hdrift (j : Fin d) : ContinuousOn
      (fun y ↦ reverseTimeDivergenceDrift r₁ a b τ y j) D := by
    simpa [reverseTimeDivergenceDrift, scalarSpatialCoefficientDivergence_reverseTimeCoefficient, reverseTimeMap_apply, reverseTimeVectorCoefficient_apply, Pi.sub_def] using (hdivergence j).sub (hb j)
  let amplitude : PDE.Vec d → ℝ := fun y ↦
    -scalarTimeDerivative p (r₁ - τ, y) +
      (∑ j : Fin d,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          scalarSpatialGradient p (r₁ - τ, y) j) -
      c (r₁ - τ) y * p (r₁ - τ, y)
  have hamp : ContinuousOn amplitude D :=
    htime.neg.add
      (continuousOn_finset_sum Finset.univ fun j _ ↦ (hdrift j).mul (hgradient j)) |>.sub
        (hc.mul hpvalue)
  have hint : Integrable (fun y ↦ amplitude y * ψ y) :=
    integrable_mul_of_right_compactSupport hamp ψ.contDiff.continuous
      ψ.hasCompactSupport ψ.tsupport_subset
  apply hint.integrableOn.congr_fun
  · intro y _hy
    dsimp only [amplitude]
    ring_nf
    rw [Finset.sum_mul]
    ring_nf
  · exact hD.measurableSet

/-- Generic integrable predecessor: the reverse-time local spatial form of a
classical scalar field equals the negative original-time operator against each
bundled smooth compactly supported test function.  A source-facing obstacle
consumer must derive the stated lower-order remainder integrability. -/
theorem integral_reverseTimeClassicalResidual_weakTest_eq_neg_operator
    {d : ℕ} {D : Set (PDE.Vec d)} (hD : IsOpen D)
    (r₁ τ : ℝ)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) (ell : TimeVelocity d → ℝ)
    (ψ : PDE.WeakTestFunction D)
    (ha : ∀ i j : Fin d, ContDiffOn ℝ 1 (fun y ↦ a (r₁ - τ) y i j) D)
    (hell : IsScalarC12On ell ({r₁ - τ} ×ˢ D))
    (hremainder : IntegrableOn (fun y ↦
      (-scalarTimeDerivative ell (r₁ - τ, y)) * ψ y +
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            scalarSpatialGradient ell (r₁ - τ, y) j * ψ y) -
        c (r₁ - τ) y * ell (r₁ - τ, y) * ψ y) D) :
    (∫ y in D,
      (-scalarTimeDerivative ell (r₁ - τ, y)) * ψ y +
        (∑ i : Fin d, ∑ j : Fin d,
          a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j *
            ψ.partialDeriv i y) +
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            scalarSpatialGradient ell (r₁ - τ, y) j * ψ y) -
        c (r₁ - τ) y * ell (r₁ - τ, y) * ψ y ∂volume) =
      ∫ y in D,
        (-scalarParabolicZeroOrderOperator a b c ell (r₁ - τ, y)) * ψ y ∂volume := by
  let u : PDE.Vec d → ℝ := fun y ↦ ell (r₁ - τ, y)
  have hu2 : ContDiffOn ℝ 2 u D := by
    intro y hy
    exact (hell.spatialSlice_contDiffAt
      (show (r₁ - τ, y) ∈ ({r₁ - τ} ×ˢ D) from ⟨Set.mem_singleton _, hy⟩)).contDiffWithinAt
  have hgrad (j : Fin d) : ContDiffOn ℝ 1 (spatialPartial j u) D :=
    ContDiffOn.spatialPartial hu2 hD j
  have hpsi1 : ContDiffOn ℝ 1 ψ D := ψ.contDiff.contDiffOn.of_le (by simp)
  have hgradient_eq (y : PDE.Vec d) (j : Fin d) :
      scalarSpatialGradient ell (r₁ - τ, y) j = spatialPartial j u y := rfl
  have hhessian_eq (y : PDE.Vec d) (hy : y ∈ D) (i j : Fin d) :
      scalarSpatialHessian ell (r₁ - τ, y) i j =
        spatialPartial i (spatialPartial j u) y := by
    have hdu : DifferentiableAt ℝ (fun x ↦ PDE.classicalGradient u x) y := by
      apply differentiableAt_pi.2
      intro k
      exact ((hu2.contDiffAt (hD.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num) |>.clm_apply (differentiableAt_const (c := PDE.basisVec k))
    unfold scalarSpatialHessian spatialPartial u
    rw [fderiv_pi (fun k ↦ (differentiableAt_pi.mp hdu) k)]
    rfl
  have hflux (i j : Fin d) :
      ContDiffOn ℝ 1
        (fun y ↦ a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j) D := by
    simpa only [hgradient_eq] using (ha i j).mul (hgrad j)
  have hibp (i j : Fin d) :
      (∫ y in D,
        a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j *
          ψ.partialDeriv i y ∂volume) =
        -∫ y in D,
          (spatialPartial i (fun x ↦ a (r₁ - τ) x i j) y *
              scalarSpatialGradient ell (r₁ - τ, y) j +
            a (r₁ - τ) y i j * scalarSpatialHessian ell (r₁ - τ, y) i j) *
            ψ y ∂volume := by
    calc
      _ = ∫ y in D,
          (a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j) *
            spatialPartial i ψ y ∂volume := by
          apply setIntegral_congr_fun hD.measurableSet
          intro y _hy
          rfl
      _ = -∫ y in D,
          spatialPartial i
            (fun y ↦ a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j) y *
            ψ y ∂volume := (setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_right D hD i (fun y ↦ a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j) ψ (hflux i j) hpsi1 ψ.hasCompactSupport ψ.tsupport_subset)
      _ = _ := by
        congr 1
        apply setIntegral_congr_fun hD.measurableSet
        intro y hy
        change spatialPartial i
          (fun x ↦ a (r₁ - τ) x i j * spatialPartial j u x) y * ψ y = _
        rw [spatialPartial_mul_local hD i (ha i j) (hgrad j) hy]
        rw [← hgradient_eq y j, ← hhessian_eq y hy i j]
  let p : PDE.Vec d → ℝ := fun y ↦
    ∑ i : Fin d, ∑ j : Fin d,
      a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j *
        ψ.partialDeriv i y
  let q : PDE.Vec d → ℝ := fun y ↦
    ∑ i : Fin d, ∑ j : Fin d,
      -((spatialPartial i (fun x ↦ a (r₁ - τ) x i j) y *
          scalarSpatialGradient ell (r₁ - τ, y) j +
        a (r₁ - τ) y i j * scalarSpatialHessian ell (r₁ - τ, y) i j) * ψ y)
  let r : PDE.Vec d → ℝ := fun y ↦
    (-scalarTimeDerivative ell (r₁ - τ, y)) * ψ y +
      (∑ j : Fin d,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          scalarSpatialGradient ell (r₁ - τ, y) j * ψ y) -
      c (r₁ - τ) y * ell (r₁ - τ, y) * ψ y
  have hpartialSupport (i : Fin d) : tsupport (spatialPartial i ψ) ⊆ D := by
    apply (closure_minimal ?_ (isClosed_tsupport ψ)).trans ψ.tsupport_subset
    intro y hy
    by_contra hnot
    apply hy
    unfold spatialPartial
    rw [fderiv_of_notMem_tsupport ℝ hnot]
    simp
  have hpij (i j : Fin d) : Integrable (fun y ↦
      a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j *
        ψ.partialDeriv i y) := by
    apply integrable_mul_of_right_compactSupport
      (g := spatialPartial i ψ) (hflux i j).continuousOn
    · exact (ψ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const
    · exact ψ.hasCompactSupport.fderiv_apply ℝ (PDE.basisVec i)
    · exact hpartialSupport i
  have hp : Integrable p :=
    integrable_finset_sum Finset.univ fun i _ ↦
      integrable_finset_sum Finset.univ fun j _ ↦ hpij i j
  have hcoeffPartial (i j : Fin d) : ContinuousOn
      (spatialPartial i (fun x ↦ a (r₁ - τ) x i j)) D := by
    exact ((ha i j).fderiv_of_isOpen hD (m := 0) (by norm_num)).clm_apply
      contDiffOn_const |>.continuousOn
  have hhessianContinuous (i j : Fin d) : ContinuousOn
      (fun y ↦ scalarSpatialHessian ell (r₁ - τ, y) i j) D := by
    have hentry : ContinuousOn (fun z ↦ scalarSpatialHessian ell z i j)
        ({r₁ - τ} ×ˢ D) :=
      (continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hell.continuousOn_scalarSpatialHessian)
    exact hentry.comp (continuous_const.prodMk continuous_id).continuousOn
      fun y hy ↦ ⟨Set.mem_singleton _, hy⟩
  have hqij (i j : Fin d) : Integrable (fun y ↦
      -((spatialPartial i (fun x ↦ a (r₁ - τ) x i j) y *
          scalarSpatialGradient ell (r₁ - τ, y) j +
        a (r₁ - τ) y i j * scalarSpatialHessian ell (r₁ - τ, y) i j) * ψ y)) := by
    apply (integrable_mul_of_right_compactSupport
      (((hcoeffPartial i j).mul (hgrad j).continuousOn).add
        ((ha i j).continuousOn.mul (hhessianContinuous i j)))
      ψ.contDiff.continuous ψ.hasCompactSupport ψ.tsupport_subset).neg
  have hq : Integrable q :=
    integrable_finset_sum Finset.univ fun i _ ↦
      integrable_finset_sum Finset.univ fun j _ ↦ hqij i j
  have hpq : (∫ y in D, p y ∂volume) = ∫ y in D, q y ∂volume := by
    dsimp only [p, q]
    rw [integral_finset_sum Finset.univ (fun i _ ↦
      integrable_finset_sum Finset.univ fun j _ ↦ (hpij i j).integrableOn)]
    simp_rw [integral_finset_sum Finset.univ (fun j _ ↦ (hpij _ j).integrableOn)]
    rw [integral_finset_sum Finset.univ (fun i _ ↦
      integrable_finset_sum Finset.univ fun j _ ↦ (hqij i j).integrableOn)]
    simp_rw [integral_finset_sum Finset.univ (fun j _ ↦ (hqij _ j).integrableOn),
      integral_neg, hibp]
  have hcommon : (∫ x in D, r x + p x ∂volume) =
      ∫ x in D, r x + q x ∂volume := by
    rw [integral_add hremainder hp.integrableOn, integral_add hremainder hq.integrableOn, hpq]
  calc
    _ = ∫ y in D, r y + p y ∂volume := by
      apply setIntegral_congr_fun hD.measurableSet
      intro y _hy
      dsimp only [r, p]
      ring
    _ = ∫ y in D, r y + q y ∂volume := hcommon
    _ = _ := by
      apply setIntegral_congr_fun hD.measurableSet
      intro y _hy
      simp only [r, q, reverseTimeDivergenceDrift,
        scalarSpatialCoefficientDivergence_reverseTimeCoefficient, reverseTimeMap_apply,
        reverseTimeVectorCoefficient_apply,
        scalarParabolicZeroOrderOperator_apply, matrixContraction, PDE.vecDot]
      unfold scalarSpatialCoefficientDivergence
      simp only [Pi.sub_apply, spatialPartial]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      simp_rw [Finset.sum_mul]
      rw [show
        (∑ j : Fin d, ∑ i : Fin d,
          (fderiv ℝ (fun x ↦ a (r₁ - τ) x i j) y) (PDE.basisVec i) *
            scalarSpatialGradient ell (r₁ - τ, y) j * ψ y) =
        ∑ i : Fin d, ∑ j : Fin d,
          (fderiv ℝ (fun x ↦ a (r₁ - τ) x i j) y) (PDE.basisVec i) *
            scalarSpatialGradient ell (r₁ - τ, y) j * ψ y from Finset.sum_comm]
      ring_nf
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_sub_distrib]
      simp_rw [Finset.sum_neg_distrib]
      ring_nf

end HypoellipticAleksandrov.Parabolic

section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open MeasureTheory
open scoped ENNReal

/-- The canonical Hilbert-graph point associated to a representative-level
`H¹₀` function. -/
noncomputable def h10HilbertGraphOfH10Function
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : PDE.H10Function Ω) : H10HilbertGraph hΩ :=
  (h10HilbertGraphContinuousLinearEquiv hΩ).symm (u.toH10Graph hΩ)

/-- The selected value representative of the canonical Hilbert-graph point
agrees almost everywhere with the original representative. -/
theorem valueCLM_h10HilbertGraphOfH10Function
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : PDE.H10Function Ω) :
    (valueCLM hΩ (h10HilbertGraphOfH10Function hΩ u) :
      PDE.Vec d → ℝ) =ᵐ[PDE.volumeOn Ω] u.toH1Function.toFun := by
  simpa
    using! (PDE.W1pFunction.coeFn_toW1pGraph_fst u.toH1Function.toW1pFunction)

/-- Every selected weak-gradient coordinate of the canonical Hilbert-graph
point agrees almost everywhere with the corresponding original coordinate. -/
theorem gradientCoord_h10HilbertGraphOfH10Function
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : PDE.H10Function Ω) (i : Fin d) :
    (fun x => PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
      (gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ u)) x)
      =ᵐ[PDE.volumeOn Ω]
    fun x => u.toH1Function.grad x i := by
  have hgraph :
      h10HilbertGraphContinuousLinearEquiv hΩ
          (h10HilbertGraphOfH10Function hΩ u) = u.toH10Graph hΩ :=
    (h10HilbertGraphContinuousLinearEquiv hΩ).apply_symm_apply _
  have hgradient :
      gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ u) =
        u.toH1Function.toW1pFunction.toW1pGraph.1.2 := by
    simpa using! (congrArg (fun z : PDE.H10Graph hΩ => (z : PDE.H1Graph Ω).1.2) hgraph)
  rw [hgradient]
  filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω 2 i
      u.toH1Function.toW1pFunction.toW1pGraph.1.2,
    PDE.W1pFunction.coeFn_toW1pGraph_snd
      u.toH1Function.toW1pFunction] with x hcoord hgrad
  rw [hcoord]
  rw [hgrad]
  rfl

end HypoellipticAleksandrov.Parabolic.Dirichlet

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Dirichlet Set
open scoped ENNReal

/-- The weak gradient of a smooth H10 representative is its classical gradient. -/
theorem h10Function_grad_ae_classical {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (q : PDE.H10Function Ω)
    (hq : ContDiff ℝ 1 q.toH1Function.toFun) (i : Fin d) :
    (fun x => q.toH1Function.grad x i) =ᵐ[PDE.volumeOn Ω]
      fun x => PDE.classicalGradient q.toH1Function.toFun x i := by
  apply PDE.HasWeakPartialDerivOn.ae_eq hΩ
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((q.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num))
  · have hc : Continuous (fun x => PDE.classicalGradient q.toH1Function.toFun x i) :=
      (continuous_apply i).comp (PDE.ContDiff.continuous_classicalGradient hq)
    exact hc.continuousOn.locallyIntegrableOn hΩ.measurableSet
  · exact q.toH1Function.hasWeakGradient i
  · exact PDE.HasWeakGradientOn.of_contDiff hq i

/-- The canonical Hilbert graph of a smooth barrier has the classical gradient jet. -/
theorem gradientCoord_h10HilbertGraph_ae_classical {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (q : PDE.H10Function Ω)
    (hq : ContDiff ℝ 1 q.toH1Function.toFun) (i : Fin d) :
    (fun x => PDE.hilbertVectorLpCoord Ω 2 i
      (gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ q)) x)
      =ᵐ[PDE.volumeOn Ω] fun x => PDE.classicalGradient q.toH1Function.toFun x i :=
  (gradientCoord_h10HilbertGraphOfH10Function hΩ q i).trans
    (h10Function_grad_ae_classical hΩ q hq i)


private theorem integrableOn_mul_compact_test {d : ℕ} {Ω : Set (PDE.Vec d)}
    {f g : PDE.Vec d → ℝ} (hf : ContinuousOn f Ω) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    IntegrableOn (fun y => f y * g y) Ω := by
  have hK : IntegrableOn (fun y => f y * g y) (tsupport g) :=
    ((hf.mono hgs).mul hg.continuousOn).integrableOn_compact hgc
  exact ((integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f g).trans (subset_tsupport g))).mp hK).integrableOn

/-- The smooth stationary barrier form equals its negative classical operator integral. -/
theorem reverseTimeSpatialForm_stationary_barrier_weakIdentity {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T τ : ℝ) (A : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (q : PDE.H10Function Ω) (hq : ContDiff ℝ 2 q.toH1Function.toFun)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun y => A (T - τ) y i j) Ω)
    (hb : ∀ j, ContinuousOn (fun y => b (T - τ) y j) Ω)
    (hc : ContinuousOn (fun y => c (T - τ) y) Ω)
    (ψ : PDE.WeakTestFunction Ω) :
    reverseTimeSpatialForm hΩ T τ A b c (h10HilbertGraphOfH10Function hΩ q)
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
      ∫ y in Ω, (-scalarParabolicZeroOrderOperator A b c
        (fun z => q.toH1Function.toFun z.2) (T - τ, y)) * ψ y  := by
  have reverseTimeSpatialForm_smooth_barrier_test {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T τ : ℝ) (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (q : PDE.H10Function Ω) (hq : ContDiff ℝ 1 q.toH1Function.toFun) (ψ : PDE.WeakTestFunction Ω) :
      reverseTimeSpatialForm hΩ T τ A b c (h10HilbertGraphOfH10Function hΩ q)
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
      (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
        A (T - τ) y i j * PDE.classicalGradient q.toH1Function.toFun y j *
          ψ.partialDeriv i y) +
      (∑ j : Fin d, ∫ y in Ω, reverseTimeDivergenceDrift T A b τ y j *
        PDE.classicalGradient q.toH1Function.toFun y j * ψ y) -
      ∫ y in Ω, reverseTimeScalarCoefficient T c τ y * q.toH1Function.toFun y * ψ y := by
    rw [reverseTimeSpatialForm_apply]
    have hp (i j : Fin d) :
        (∫ y in Ω, A (T - τ) y i j *
          PDE.hilbertVectorLpCoord Ω 2 j
            (gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ q)) y *
          PDE.hilbertVectorLpCoord Ω 2 i
            (gradientCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)) y) =
        ∫ y in Ω, A (T - τ) y i j *
          PDE.classicalGradient q.toH1Function.toFun y j * ψ.partialDeriv i y := by
      apply integral_congr_ae
      filter_upwards [gradientCoord_h10HilbertGraph_ae_classical hΩ q hq j,
        PDE.coeFn_hilbertVectorLpCoord Ω 2 i
          (gradientCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)),
        ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ i]
        with y hqj hpi hψi
      rw [hqj, hpi, hψi]
    have hb (j : Fin d) :
        (∫ y in Ω, reverseTimeDivergenceDrift T A b τ y j *
          PDE.hilbertVectorLpCoord Ω 2 j
            (gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ q)) y *
          valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) y) =
        ∫ y in Ω, reverseTimeDivergenceDrift T A b τ y j *
          PDE.classicalGradient q.toH1Function.toFun y j * ψ y := by
      apply integral_congr_ae
      filter_upwards [gradientCoord_h10HilbertGraph_ae_classical hΩ q hq j,
        ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ] with y hqj hψ
      rw [hqj, hψ]
    have hc :
        (∫ y in Ω, reverseTimeScalarCoefficient T c τ y *
          valueCLM hΩ (h10HilbertGraphOfH10Function hΩ q) y *
          valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) y) =
        ∫ y in Ω, reverseTimeScalarCoefficient T c τ y * q.toH1Function.toFun y * ψ y := by
      apply integral_congr_ae
      filter_upwards [valueCLM_h10HilbertGraphOfH10Function hΩ q,
        ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ] with y hqv hψ
      rw [hqv, hψ]
    simp_rw [hp, hb, hc]
  let ell : TimeVelocity d → ℝ := fun z => q.toH1Function.toFun z.2
  have hell : IsScalarC12On ell ({T - τ} ×ˢ Ω) :=
    isScalarC12On_of_contDiff_two (hq.comp contDiff_snd) _
  have htime (y : PDE.Vec d) : scalarTimeDerivative ell (T - τ, y) = 0 := by
    change deriv (fun _ => q.toH1Function.toFun y) (T - τ) = 0
    exact deriv_const _ _
  have hgrad (y : PDE.Vec d) (j : Fin d) :
      scalarSpatialGradient ell (T - τ, y) j =
        PDE.classicalGradient q.toH1Function.toFun y j := rfl
  have hpair : Continuous (fun y : PDE.Vec d => (T - τ, y)) :=
    continuous_const.prodMk continuous_id
  have hmaps : MapsTo (fun y => (T - τ, y)) Ω ({T - τ} ×ˢ Ω) :=
    fun _ hy => ⟨mem_singleton _, hy⟩
  have hg (j : Fin d) : ContinuousOn
      (fun y => scalarSpatialGradient ell (T - τ, y) j) Ω :=
    ((continuous_apply j).comp_continuousOn hell.continuousOn_scalarSpatialGradient).comp
      hpair.continuousOn hmaps
  have hd (j : Fin d) : ContinuousOn
      (fun y => reverseTimeDivergenceDrift T A b τ y j) Ω := by
    have hsum : ContinuousOn
        (fun y => ∑ i : Fin d, spatialPartial i (fun x => A (T - τ) x i j) y) Ω := by
      apply continuousOn_finsetSum
      intro i _
      exact ((ha i j).fderiv_of_isOpen hΩ (m := 0) (by norm_num)).clm_apply
        contDiffOn_const |>.continuousOn
    simpa [reverseTimeDivergenceDrift, scalarSpatialCoefficientDivergence_reverseTimeCoefficient, reverseTimeMap_apply, reverseTimeVectorCoefficient_apply, scalarSpatialCoefficientDivergence, spatialPartial, Pi.sub_def] using hsum.sub (hb j)
  have hp (i j : Fin d) : IntegrableOn (fun y => A (T - τ) y i j *
      scalarSpatialGradient ell (T - τ, y) j * ψ.partialDeriv i y) Ω := by
    apply integrableOn_mul_compact_test ((ha i j).continuousOn.mul (hg j))
    · have hψ : ContDiff ℝ 1 (ψ : PDE.Vec d → ℝ) := ψ.contDiff.of_le (by simp)
      exact (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    · exact ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (PDE.basisVec i)
    · exact (tsupport_fderiv_apply_subset ℝ (PDE.basisVec i)).trans ψ.tsupport_subset
  have hdi (j : Fin d) : IntegrableOn (fun y =>
      reverseTimeDivergenceDrift T A b τ y j *
        scalarSpatialGradient ell (T - τ, y) j * ψ y) Ω :=
    integrableOn_mul_compact_test ((hd j).mul (hg j)) ψ.contDiff.continuous
      ψ.hasCompactSupport ψ.tsupport_subset
  have hci : IntegrableOn (fun y => c (T - τ) y * ell (T - τ, y) * ψ y) Ω :=
    integrableOn_mul_compact_test
      (hc.mul (hell.continuousOn.comp hpair.continuousOn hmaps))
      ψ.contDiff.continuous ψ.hasCompactSupport ψ.tsupport_subset
  have hid := integral_reverseTimeClassicalResidual_weakTest_eq_neg_operator hΩ T τ
    A b c ell ψ ha hell
    (integrableOn_reverseTimeClassicalRemainder_weakTest hΩ T τ A b c ell ψ ha hb hc hell)
  simp_rw [htime, neg_zero, zero_mul, zero_add] at hid
  rw [integral_sub (f := fun y =>
      (∑ i : Fin d, ∑ j : Fin d, A (T - τ) y i j *
        scalarSpatialGradient ell (T - τ, y) j * ψ.partialDeriv i y) +
      ∑ j : Fin d, reverseTimeDivergenceDrift T A b τ y j *
        scalarSpatialGradient ell (T - τ, y) j * ψ y)
    (g := fun y => c (T - τ) y * ell (T - τ, y) * ψ y)
    ((integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hp i j))).add
      (integrable_finsetSum Finset.univ (fun j _ => hdi j))) hci,
    integral_add (f := fun y => ∑ i : Fin d, ∑ j : Fin d, A (T - τ) y i j *
      scalarSpatialGradient ell (T - τ, y) j * ψ.partialDeriv i y)
      (g := fun y => ∑ j : Fin d, reverseTimeDivergenceDrift T A b τ y j *
        scalarSpatialGradient ell (T - τ, y) j * ψ y)
      (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hp i j)))
      (integrable_finsetSum Finset.univ (fun j _ => hdi j)),
    integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hp i j)),
    integral_finsetSum Finset.univ (fun j _ => hdi j)] at hid
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hp _ j), hgrad] at hid
  rw [reverseTimeSpatialForm_smooth_barrier_test hΩ T τ A b c q
    (hq.of_le (by norm_num)) ψ]
  exact hid

end HypoellipticAleksandrov.Parabolic.LocalHolder

end

