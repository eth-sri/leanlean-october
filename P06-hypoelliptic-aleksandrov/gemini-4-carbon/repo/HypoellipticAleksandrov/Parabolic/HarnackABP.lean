module

public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.Parabolic.ABP
public import HypoellipticAleksandrov.Parabolic.LocalGluing
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open Filter MeasureTheory Set
open scoped Topology MatrixOrder



/-- The positive exponential weight based at the time `tBase`. -/
def exponentialTimeWeight {d : ℕ} (rho tBase : ℝ) (z : TimeVelocity d) : ℝ :=
  Real.exp (rho * (z.1 - tBase))

/-- The exponential time conjugate of a scalar function. -/
def exponentialConjugate {d : ℕ} (rho tBase : ℝ)
    (w : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  exponentialTimeWeight rho tBase z * w z

/-- Evaluation of the exponential time weight. -/
@[simp] theorem exponentialTimeWeight_apply {d : ℕ} (rho tBase : ℝ)
    (z : TimeVelocity d) :
    exponentialTimeWeight rho tBase z = Real.exp (rho * (z.1 - tBase)) :=
  rfl

/-- Evaluation of the exponential time conjugate. -/
@[simp] theorem exponentialConjugate_apply {d : ℕ} (rho tBase : ℝ)
    (w : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    exponentialConjugate rho tBase w z = exponentialTimeWeight rho tBase z * w z :=
  rfl

/-- The exponential time weight is strictly positive at every point. -/
theorem exponentialTimeWeight_pos {d : ℕ} (rho tBase : ℝ) (z : TimeVelocity d) :
    0 < exponentialTimeWeight rho tBase z :=
  Real.exp_pos _

/-- The exponential time weight is globally smooth. -/
theorem contDiff_exponentialTimeWeight {d : ℕ} (rho tBase : ℝ) :
    ContDiff ℝ ⊤ (exponentialTimeWeight (d := d) rho tBase) := by
  unfold exponentialTimeWeight
  fun_prop


private theorem fderiv_timeCoordinate_apply {d : ℕ}
    (z direction : TimeVelocity d) :
    fderiv ℝ (fun y : TimeVelocity d => y.1) z direction = direction.1 := by
  rw [(hasFDerivAt_fst (𝕜 := ℝ)).fderiv]
  rfl

private theorem fderiv_exponentialTimeWeight_apply {d : ℕ} (rho tBase : ℝ)
    (z direction : TimeVelocity d) :
    fderiv ℝ (exponentialTimeWeight rho tBase) z direction =
      exponentialTimeWeight rho tBase z * (rho * direction.1) := by
  unfold exponentialTimeWeight
  rw [fderiv_exp (by fun_prop)]
  simp
  rw [fderiv_const_mul (by fun_prop) rho]
  simp [ContinuousLinearMap.smul_apply]
  rw [fderiv_fun_sub (by fun_prop) (by fun_prop)]
  simp [fderiv_timeCoordinate_apply, fderiv_const_apply]





/-- The exact project-sign operator identity after exponential time
conjugation. -/
theorem parabolicOperator_exponentialConjugate {d : ℕ} (A : CoefficientField d)
    {rho tBase : ℝ} {w : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hw : ContDiffAt ℝ 2 w z) :
    parabolicOperator A (exponentialConjugate rho tBase w) z =
      exponentialTimeWeight rho tBase z * (parabolicOperator A w z + rho * w z)    := by
  have fderiv_fderiv_apply_eq_fderiv_eval {w : TimeVelocity d → ℝ} {z direction₁ direction₂ : TimeVelocity d} (hw : ContDiffAt ℝ 2 w z) :
      fderiv ℝ (fderiv ℝ w) z direction₁ direction₂ =
      fderiv ℝ (fun y => fderiv ℝ w y direction₂) z direction₁ := by
    have hDw :=
      (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hEval :
        fderiv ℝ (fun y => fderiv ℝ w y direction₂) z =
          (fderiv ℝ (fderiv ℝ w) z).flip direction₂ := by
      simpa using
        ((hDw.hasFDerivAt.clm_apply
          (hasFDerivAt_const direction₂ z)).fderiv)
    simpa using (congrArg (fun L => L direction₁) hEval).symm
  have velocityHessian_exponentialConjugate :
      velocityHessian (exponentialConjugate rho tBase w) z =
      exponentialTimeWeight rho tBase z • velocityHessian w z := by
    have fderiv_fderiv_exponentialTimeWeight_apply (rho : ℝ) (tBase : ℝ) (z direction₁ direction₂ : TimeVelocity d) :
        fderiv ℝ (fderiv ℝ (exponentialTimeWeight rho tBase)) z direction₁ direction₂ =
        exponentialTimeWeight rho tBase z * rho ^ 2 * direction₁.1 * direction₂.1 := by
      let e : TimeVelocity d → ℝ := exponentialTimeWeight rho tBase
      have he : ContDiff ℝ 2 e :=
        (contDiff_exponentialTimeWeight rho tBase).of_le (by norm_num)
      calc
        fderiv ℝ (fderiv ℝ e) z direction₁ direction₂ =
            fderiv ℝ (fun y => fderiv ℝ e y direction₂) z direction₁ :=
          fderiv_fderiv_apply_eq_fderiv_eval he.contDiffAt
        _ = fderiv ℝ (fun y => e y * (rho * direction₂.1)) z direction₁ := by
          congr 2
          funext y
          exact fderiv_exponentialTimeWeight_apply rho tBase y direction₂
        _ = e z * rho ^ 2 * direction₁.1 * direction₂.1 := by
          rw [fderiv_mul_const (by
            exact (contDiff_exponentialTimeWeight rho tBase).differentiable (by norm_num) z)
            (rho * direction₂.1)]
          simp
          rw [fderiv_exponentialTimeWeight_apply]
          ring
    let e : TimeVelocity d → ℝ := exponentialTimeWeight rho tBase
    let g := exponentialConjugate rho tBase w
    have he : ContDiff ℝ 2 e :=
      (contDiff_exponentialTimeWeight rho tBase).of_le (by norm_num)
    have heDiff := he.differentiable (by norm_num) z
    have hwDiff := hw.differentiableAt (by norm_num)
    have hDwe :=
      (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hDe : DifferentiableAt ℝ (fderiv ℝ e) z :=
      (he.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    ext i j
    let direction₁ : TimeVelocity d := (0, Pi.single i 1)
    let direction₂ : TimeVelocity d := (0, Pi.single j 1)
    have hFirst :
        (fun y => fderiv ℝ g y direction₂) =ᶠ[𝓝 z]
          fun y => e y * fderiv ℝ w y direction₂ + w y * fderiv ℝ e y direction₂ := by
      filter_upwards [(hw.eventually (by norm_num))] with y hy
      change fderiv ℝ (fun x => e x * w x) y direction₂ =
        e y * fderiv ℝ w y direction₂ + w y * fderiv ℝ e y direction₂
      rw [fderiv_fun_mul (he.differentiable (by norm_num) y) (hy.differentiableAt (by norm_num))]
      simp
    unfold velocityHessian
    change fderiv ℝ (fderiv ℝ g) z direction₁ direction₂ =
      (e z • velocityHessian w z) i j
    calc
      fderiv ℝ (fderiv ℝ g) z direction₁ direction₂ =
      fderiv ℝ (fun y => fderiv ℝ g y direction₂) z direction₁ :=
        fderiv_fderiv_apply_eq_fderiv_eval (he.contDiffAt.mul hw)
      _ = fderiv ℝ
          (fun y => e y * fderiv ℝ w y direction₂ + w y * fderiv ℝ e y direction₂)
            z direction₁ := by
        exact congrArg (fun L => L direction₁)
          (hFirst.fderiv_eq (𝕜 := ℝ))
      _ = e z * fderiv ℝ (fderiv ℝ w) z direction₁ direction₂ +
            fderiv ℝ e z direction₁ * fderiv ℝ w z direction₂ +
            w z * fderiv ℝ (fderiv ℝ e) z direction₁ direction₂ +
            fderiv ℝ w z direction₁ * fderiv ℝ e z direction₂ := by
        have hEvalW :=
          hDwe.clm_apply (hasFDerivAt_const direction₂ z).differentiableAt
        have hEvalE :=
          hDe.clm_apply (hasFDerivAt_const direction₂ z).differentiableAt
        let first : TimeVelocity d → ℝ := fun y => e y * fderiv ℝ w y direction₂
        let second : TimeVelocity d → ℝ := fun y => w y * fderiv ℝ e y direction₂
        have hfirst : DifferentiableAt ℝ first z := heDiff.mul hEvalW
        have hsecond : DifferentiableAt ℝ second z := hwDiff.mul hEvalE
        calc
          fderiv ℝ
              (fun y => e y * fderiv ℝ w y direction₂ + w y * fderiv ℝ e y direction₂)
              z direction₁ =
              fderiv ℝ first z direction₁ + fderiv ℝ second z direction₁ := by
            change fderiv ℝ (first + second) z direction₁ = _
            rw [fderiv_add hfirst hsecond]
            rfl
          _ = e z * fderiv ℝ (fderiv ℝ w) z direction₁ direction₂ +
              fderiv ℝ e z direction₁ * fderiv ℝ w z direction₂ +
              w z * fderiv ℝ (fderiv ℝ e) z direction₁ direction₂ +
              fderiv ℝ w z direction₁ * fderiv ℝ e z direction₂ := by
            dsimp only [first, second]
            rw [fderiv_fun_mul heDiff hEvalW,
              fderiv_fun_mul hwDiff hEvalE]
            simp
            rw [← fderiv_fderiv_apply_eq_fderiv_eval hw,
              ← fderiv_fderiv_apply_eq_fderiv_eval he.contDiffAt,
              fderiv_exponentialTimeWeight_apply,
              fderiv_exponentialTimeWeight_apply,
              fderiv_fderiv_exponentialTimeWeight_apply]
            ring
      _ = (e z • velocityHessian w z) i j := by
        dsimp only [direction₁, direction₂]
        rw [fderiv_exponentialTimeWeight_apply rho tBase z,
          fderiv_exponentialTimeWeight_apply rho tBase z,
          fderiv_fderiv_exponentialTimeWeight_apply rho tBase z]
        simp [Matrix.smul_apply, velocityHessian]
  have timeDerivative_exponentialConjugate :
      timeDerivative (exponentialConjugate rho tBase w) z =
      exponentialTimeWeight rho tBase z * (timeDerivative w z + rho * w z) := by
    unfold timeDerivative exponentialConjugate
    rw [fderiv_fun_mul ((contDiff_exponentialTimeWeight rho tBase).differentiable (by norm_num) z) (hw.differentiableAt (by norm_num))]
    simp [ContinuousLinearMap.smul_apply]
    rw [fderiv_exponentialTimeWeight_apply]
    simp
    ring
  rw [parabolicOperator_apply, parabolicOperator_apply,
    timeDerivative_exponentialConjugate,
    velocityHessian_exponentialConjugate,
    HypoellipticAleksandrov.matrixContraction_smul_right]
  ring

/-- At a point, exponential conjugation preserves a nonpositive scalar sign. -/
theorem exponentialConjugate_nonpos_iff {d : ℕ} (rho tBase : ℝ)
    (w : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    exponentialConjugate rho tBase w z ≤ 0 ↔ w z ≤ 0 := by
  rw [exponentialConjugate_apply]
  constructor
  · intro h
    exact nonpos_of_mul_nonpos_right h (exponentialTimeWeight_pos rho tBase z)
  · intro hw
    exact mul_nonpos_of_nonneg_of_nonpos (exponentialTimeWeight_pos rho tBase z).le hw




/-- The affine map from the unit cylinder to the local ABP cylinder centered
at `v0`. -/
def localABPAffine {d : ℕ} (v0 : PDE.Vec d) : TimeVelocity d → TimeVelocity d :=
  parabolicAffine (3 / 4) v0 (1 / 2)

/-- The open inner cylinder `(3/4, 1) × B_(1/2)(v0)`, presented as the affine
image of the reference parabolic interior. -/
def localABPInterior {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' parabolicInterior 1 0

/-- The compact closure of the local inner ABP cylinder. -/
def localABPClosure {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' closedParabolicCylinder 1 0

/-- The initial-plus-lateral, but not terminal, boundary of the local ABP
cylinder. -/
def localABPForwardBoundary {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' forwardParabolicBoundary 1 0

/-- The local ABP closure is compact. -/
theorem isCompact_localABPClosure {d : ℕ} (v0 : PDE.Vec d) :
    IsCompact (localABPClosure v0) := by
  unfold localABPClosure localABPAffine
  exact (isCompact_closedParabolicCylinder 1 0).image
    (contDiff_parabolicAffine (3 / 4) v0 (1 / 2)).continuous

/-- The local ABP interior is contained in its compact closure. -/
theorem localABPInterior_subset_closure {d : ℕ} (v0 : PDE.Vec d) :
    localABPInterior v0 ⊆ localABPClosure v0 := by
  unfold localABPInterior localABPClosure
  exact Set.image_mono (parabolicInterior_subset_closedParabolicCylinder 1 0)


/-- The local forward boundary is contained in the compact local ABP closure. -/
theorem localABPForwardBoundary_subset_closure {d : ℕ} (v0 : PDE.Vec d) :
    localABPForwardBoundary v0 ⊆ localABPClosure v0  := by
  have forwardParabolicBoundary_subset_closedParabolicCylinder_one :
      forwardParabolicBoundary 1 (0 : PDE.Vec d) ⊆
      closedParabolicCylinder 1 0 := by
    intro z hz
    rcases mem_forwardParabolicBoundary_iff.mp hz with hinitial | hlateral
    · rcases z with ⟨t, v⟩
      rcases hinitial with ⟨ht, hv⟩
      change t = 0 at ht
      change v ∈ PDE.euclideanClosedBall 0 1 at hv
      subst t
      exact mem_closedParabolicCylinder_iff.mpr
        ⟨by norm_num, by norm_num, hv⟩
    · rcases z with ⟨t, v⟩
      rcases hlateral with ⟨ht0, ht1, hsphere⟩
      exact mem_closedParabolicCylinder_iff.mpr
        ⟨ht0, ht1, by
          change PDE.euclideanSqDist v 0 ≤ 1 ^ 2
          change PDE.euclideanSqDist v 0 = 1 ^ 2 at hsphere
          exact hsphere.le⟩
  unfold localABPForwardBoundary localABPClosure
  exact Set.image_mono forwardParabolicBoundary_subset_closedParabolicCylinder_one

/-- The terminal centre is in the local ABP closure. -/
theorem localABPTarget_mem_closure {d : ℕ} (v0 : PDE.Vec d) :
    (1, v0) ∈ localABPClosure v0 := by
  refine ⟨(1, 0), ?_, ?_⟩
  · exact mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
      change PDE.euclideanSqDist 0 0 ≤ 1 ^ 2
      simp⟩
  · simp only [localABPAffine, parabolicAffine]
    ext
    · norm_num [div_pow]
    · simp



private theorem eventualEq_nhds_of_eventualEq_nhdsSet {α : Type*}
    {β : Type*} [TopologicalSpace α] {K : Set α} {f g : α → β} {x : α}
    (hx : x ∈ K) (hfg : f =ᶠ[𝓝ˢ K] g) : f =ᶠ[𝓝 x] g :=
  (eventually_nhdsSet_iff_forall.mp hfg x hx)


/-- The local ABP consequence requiring lower ellipticity only on the compact
local cylinder used by its cutoff-and-pullback proof. -/
theorem exists_local_abp_inner_cylinder_of_lower_ellipticity_on_closure
    (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (w F : TimeVelocity d → ℝ) (v0 : PDE.Vec d) (rho : ℝ),
        IsOpen U →
        localABPClosure v0 ⊆ U →
        IsContinuousCoefficientOn B U →
        ContDiffOn ℝ 2 w U →
        ContinuousOn F U →
        HasLowerEllipticityOn lam B (localABPClosure v0) →
        IsNonnegativeOn F (localABPInterior v0) →
        (∀ z ∈ localABPInterior v0,
          parabolicOperator B w z + rho * w z ≤ F z) →
        (∀ z ∈ localABPForwardBoundary v0, w z ≤ 0) →
        w (1, v0) ≤
          C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            Real.exp (-rho / 4) *
              parabolicLpNormOn d
                (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
                (localABPInterior v0)  := by
  have exists_local_abp_inner_cylinder_core :
      ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (w F : TimeVelocity d → ℝ) (v0 : PDE.Vec d) (rho : ℝ),
        IsOpen U →
        localABPClosure v0 ⊆ U →
        IsContinuousCoefficientOn B U →
        ContDiffOn ℝ 2 w U →
        ContinuousOn F U →
        HasLowerEllipticityOn lam B (localABPClosure v0) →
        IsNonnegativeOn F (localABPInterior v0) →
        (∀ z ∈ localABPInterior v0,
          parabolicOperator B w z + rho * w z ≤ F z) →
        (∀ z ∈ localABPForwardBoundary v0, w z ≤ 0) →
        w (1, v0) ≤
          C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            Real.exp (-rho / 4) *
              parabolicLpNormOn d
                (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
                (localABPInterior v0) := by
    have referenceTarget_mem_closedParabolicCylinder :
        (1, 0) ∈ closedParabolicCylinder 1 (0 : PDE.Vec d) := by
      exact mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
        change PDE.euclideanSqDist 0 0 ≤ 1 ^ 2
        simp⟩
    have localABPAffine_referenceTarget {d : ℕ} (v0 : PDE.Vec d) :
        localABPAffine v0 (1, 0) = (1, v0) := by
      simp only [localABPAffine, parabolicAffine]
      ext
      · norm_num [div_pow]
      · simp
    have contDiffOn_exponentialConjugate {U : Set (TimeVelocity d)} {rho : ℝ} {tBase : ℝ} {w : TimeVelocity d → ℝ} (hw : ContDiffOn ℝ 2 w U) :
        ContDiffOn ℝ 2 (exponentialConjugate rho tBase w) U := by
      exact (((contDiff_exponentialTimeWeight rho tBase).of_le (by norm_num)).contDiffOn).mul hw
    obtain ⟨C, hC, hABP⟩ :=
      parabolic_abp_unit_of_lower_ellipticity d hd lam hlam
    refine ⟨C, hC, ?_⟩
    intro U B w F v0 rho hU hKU hB hw hF hLow hFnonneg hineq hboundary
    let K := localABPClosure v0
    obtain ⟨b, hbSmooth, hbOne, hbSupport⟩ :=
      exists_smooth_cutoff_tsupport_subset (isCompact_localABPClosure v0) hU hKU
    let ew := exponentialConjugate rho (3 / 4) w
    let H : TimeVelocity d → ℝ := fun z => exponentialTimeWeight rho (3 / 4) z * F z
    let g : TimeVelocity d → ℝ := fun z => b z * ew z
    let G : TimeVelocity d → ℝ := fun z => b z * H z
    let Bbar := cutoffExtendCoefficient b B lam
    have hH : ContinuousOn H U := by
      dsimp only [H]
      exact (contDiff_exponentialTimeWeight rho (3 / 4)).continuous.continuousOn.mul hF
    have hEW : ContDiffOn ℝ 2 ew U := by
      dsimp only [ew]
      exact contDiffOn_exponentialConjugate hw
    have hconj : IsParabolicSubsolutionOn B H ew (localABPInterior v0) := by
      intro z hz
      have hzK := localABPInterior_subset_closure v0 hz
      dsimp only [H, ew]
      rw [parabolicOperator_exponentialConjugate B
        (hw.contDiffAt (hU.mem_nhds (hKU hzK)))]
      exact mul_le_mul_of_nonneg_left (hineq z hz)
        (exponentialTimeWeight_pos rho (3 / 4) z).le
    have hg : ContDiff ℝ 2 g := by
      dsimp only [g]
      exact contDiff_cutoff_mul_of_tsupport_subset hU
        (hbSmooth.of_le (by
          change (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)) hbSupport hEW
    have hG : Continuous G := by
      dsimp only [G]
      exact continuous_cutoff_mul_of_tsupport_subset hU
        (hbSmooth.of_le (by
          change (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)) hbSupport hH
    have hBbar : IsContinuousCoefficient Bbar := by
      dsimp only [Bbar]
      exact continuous_coefficientAt_cutoffExtendCoefficient hU
        (hbSmooth.of_le (by
          change (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)) hbSupport hB
    have hgEq : g =ᶠ[𝓝ˢ K] ew := by
      dsimp only [g]
      exact cutoff_mul_eventuallyEq hbOne
    have hGEq : G =ᶠ[𝓝ˢ K] H := by
      dsimp only [G]
      exact cutoff_mul_eventuallyEq hbOne
    have hBbarEq : coefficientAt Bbar =ᶠ[𝓝ˢ K] coefficientAt B := by
      dsimp only [Bbar]
      exact coefficientAt_cutoffExtendCoefficient_eventuallyEq hbOne
    have hlocalSub : IsParabolicSubsolutionOn Bbar G g (localABPInterior v0) := by
      intro x hx
      have hxK : x ∈ K := localABPInterior_subset_closure v0 hx
      have hoperator : parabolicOperator Bbar g x = parabolicOperator B ew x :=
        parabolicOperator_congr_of_eventuallyEq_of_coefficientAt_eventuallyEq (eventualEq_nhds_of_eventualEq_nhdsSet hxK hBbarEq) (eventualEq_nhds_of_eventualEq_nhdsSet hxK hgEq)
      calc
        parabolicOperator Bbar g x = parabolicOperator B ew x := hoperator
        _ ≤ H x := hconj x hx
        _ = G x := ((eventualEq_nhds_of_eventualEq_nhdsSet hxK hGEq).self_of_nhds).symm
    let a : TimeVelocity d → TimeVelocity d := localABPAffine v0
    let Bhat : CoefficientField d := pullbackCoefficient Bbar (3 / 4) v0 (1 / 2)
    let uhat : TimeVelocity d → ℝ := pullbackScalar g (3 / 4) v0 (1 / 2)
    let fhat : TimeVelocity d → ℝ := fun z => (1 / 2 : ℝ) ^ 2 * G (a z)
    have ha : a = parabolicAffine (3 / 4) v0 (1 / 2) := rfl
    have haCont : Continuous a := by
      dsimp only [a, localABPAffine]
      exact (contDiff_parabolicAffine (3 / 4) v0 (1 / 2)).continuous
    have hBhat : IsContinuousCoefficient Bhat := by
      dsimp only [Bhat]
      change Continuous ((coefficientAt Bbar) ∘ a)
      exact hBbar.comp haCont
    have huhat : ContDiff ℝ 2 uhat := by
      dsimp only [uhat]
      change ContDiff ℝ 2 (g ∘ a)
      exact hg.comp (contDiff_parabolicAffine (3 / 4) v0 (1 / 2))
    have hfhat : Continuous fhat := by
      dsimp only [fhat]
      exact continuous_const.mul (hG.comp haCont)
    have hLowHat : ∀ z ∈ closedParabolicCylinder 1 0,
        lam • 1 ≤ coefficientAt Bhat z := by
      intro z hz
      have hzK : a z ∈ K := ⟨z, hz, rfl⟩
      change lam • 1 ≤ coefficientAt Bbar (a z)
      rw [(eventualEq_nhds_of_eventualEq_nhdsSet hzK hBbarEq).self_of_nhds]
      exact hLow (a z) hzK
    have hsubHat : IsParabolicSubsolutionOn Bhat fhat uhat
        (parabolicInterior 1 0) := by
      intro z hz
      have hza : a z ∈ localABPInterior v0 := ⟨z, hz, rfl⟩
      change parabolicOperator Bhat uhat z ≤ (1 / 2 : ℝ) ^ 2 * G (a z)
      rw [show parabolicOperator Bhat uhat z =
          (1 / 2 : ℝ) ^ 2 * parabolicOperator Bbar g (a z) by
        dsimp only [Bhat, uhat, a]
        exact parabolicOperator_pullbackScalar hg.contDiffAt]
      exact mul_le_mul_of_nonneg_left (hlocalSub (a z) hza) (sq_nonneg (1 / 2 : ℝ))
    have hboundaryHat : ∀ z ∈ forwardParabolicBoundary 1 0,
        uhat z ≤ 0 := by
      intro z hz
      have hza : a z ∈ localABPForwardBoundary v0 := ⟨z, hz, rfl⟩
      have hzaK : a z ∈ K := localABPForwardBoundary_subset_closure v0 hza
      have hew : ew (a z) ≤ 0 := by
        dsimp only [ew]
        exact (exponentialConjugate_nonpos_iff rho (3 / 4) w (a z)).mpr
          (hboundary (a z) hza)
      change uhat z ≤ 0
      change g (a z) ≤ 0
      rw [(eventualEq_nhds_of_eventualEq_nhdsSet hzaK hgEq).self_of_nhds]
      exact hew
    have hABPPoint := hABP (T := 1) (by norm_num) (by norm_num)
      0 Bhat fhat uhat hBhat hfhat huhat hLowHat hsubHat hboundaryHat
        (1, 0) referenceTarget_mem_closedParabolicCylinder
    have hmaxAE :
        (fun z => max (fhat z) 0) =ᵐ[volume.restrict (parabolicInterior 1 0)]
          fun z => (1 / 2 : ℝ) ^ 2 * H (a z) := by
      filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior 1 0)]
        with z hz
      have hza : a z ∈ localABPInterior v0 := ⟨z, hz, rfl⟩
      have hzaK : a z ∈ K := localABPInterior_subset_closure v0 hza
      have hHnonneg : 0 ≤ H (a z) := by
        dsimp only [H]
        exact mul_nonneg (exponentialTimeWeight_pos rho (3 / 4) (a z)).le
          (hFnonneg (a z) hza)
      dsimp only [fhat]
      rw [(eventualEq_nhds_of_eventualEq_nhdsSet hzaK hGEq).self_of_nhds, max_eq_left]
      exact mul_nonneg (sq_nonneg (1 / 2 : ℝ)) hHnonneg
    have hnormMax :
        parabolicLpNormOn d (fun z => max (fhat z) 0)
            (parabolicInterior 1 0) =
          parabolicLpNormOn d (fun z => (1 / 2 : ℝ) ^ 2 * H (a z))
            (parabolicInterior 1 0) := by
      unfold parabolicLpNormOn parabolicELpNormOn
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae hmaxAE)
    have hnorm' :
        parabolicLpNormOn d (fun z => (1 / 2 : ℝ) ^ 2 * H (a z))
            (parabolicInterior 1 0) =
          (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            parabolicLpNormOn d H (localABPInterior v0) := by
      simpa only [a, H, localABPAffine, localABPInterior] using (parabolicLpNormOn_pullback (d := d) (3 / 4) v0 (by norm_num : 0 < (1 / 2 : ℝ)) H (parabolicInterior 1 0))
    have htargetK : (1, v0) ∈ K := by
      dsimp only [K]
      exact localABPTarget_mem_closure v0
    have htargetWeight : exponentialTimeWeight rho (3 / 4) (1, v0) =
        Real.exp (rho / 4) := by
      rw [exponentialTimeWeight_apply]
      congr 1
      ring
    have hweighted :
        exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0) ≤
          C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            parabolicLpNormOn d H (localABPInterior v0) := by
      have huTarget : uhat (1, 0) = g (1, v0) := by
        change g (parabolicAffine (3 / 4) v0 (1 / 2) (1, 0)) = g (1, v0)
        exact congrArg g (by
          simpa only [localABPAffine] using localABPAffine_referenceTarget v0)
      change uhat (1, 0) ≤ _ at hABPPoint
      rw [huTarget, (eventualEq_nhds_of_eventualEq_nhdsSet htargetK hgEq).self_of_nhds] at hABPPoint
      change exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0) ≤ _
        at hABPPoint
      rw [hnormMax, hnorm'] at hABPPoint
      simpa only [mul_assoc] using hABPPoint
    have hcancel : Real.exp (-rho / 4) * Real.exp (rho / 4) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    calc
      w (1, v0) = Real.exp (-rho / 4) *
          (exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0)) := by
        rw [htargetWeight, ← mul_assoc, hcancel, one_mul]
      _ ≤ Real.exp (-rho / 4) *
          (C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            parabolicLpNormOn d H (localABPInterior v0)) :=
        mul_le_mul_of_nonneg_left hweighted (Real.exp_pos _).le
      _ = C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            Real.exp (-rho / 4) *
              parabolicLpNormOn d
                (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
                (localABPInterior v0) := by
        dsimp only [H, exponentialTimeWeight]
        ring
  obtain ⟨C, hC, hcore⟩ :=
    exists_local_abp_inner_cylinder_core
  exact ⟨C, hC, hcore⟩

end HypoellipticAleksandrov.Parabolic

