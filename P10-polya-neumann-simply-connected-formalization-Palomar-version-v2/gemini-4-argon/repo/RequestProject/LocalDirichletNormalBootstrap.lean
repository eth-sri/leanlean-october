module

public import RequestProject.LocalDirichletNormalRecovery
public import RequestProject.LocalDirichletHigherDifferences
public import RequestProject.LocalDirichletTangentialBootstrap

/-!
Actual finite-order normal recovery in a smooth graph half rectangle.
The forcing convention is `div(A ∇u) = -G`. Every recovered derivative
is an ordinary directional derivative of the actual smooth interior
function. The only solution regularity inputs are tangential L² data;
normal derivatives are obtained from the equation. A finite-order
statement permits the genuine tangential energy theorem to shrink the
rectangle with the order. No derivative is evaluated on the flat boundary.
This module is part of the verified dependency chain.
-/

@[expose] public section
noncomputable section

namespace PolyaNeumann

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

variable {v : ℂ → ℂ} {f : ℝ → ℝ}

theorem dirichletBootstrap_differentiableAt  (hU : IsOpen U)
     (hv : ContDiffOn ℝ ∞ v U)  (hz : z ∈ U) :
    DifferentiableAt ℝ v z :=
  (hv.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)

theorem dirichletBootstrap_contDiff_const_mul 
    (hv : ContDiff ℝ ∞ v) (c : ℂ) :
    ContDiff ℝ ∞ (fun z => c * v z) := contDiff_const.mul hv

theorem dirichletBootstrap_contDiffOn_const_mul {U : Set ℂ} 
    (hv : ContDiffOn ℝ ∞ v U) (c : ℂ) :
    ContDiffOn ℝ ∞ (fun z => c * v z) U := contDiffOn_const.mul hv

/-- Iteration of the actual real directional derivative. -/
def dirichletCoordinateDerivative (w : ℂ) : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, u => u
  | k + 1, u => dirD (dirichletCoordinateDerivative w k u) w

@[simp] theorem dirichletCoordinateDerivative_zero w u :
    dirichletCoordinateDerivative w 0 u = u := rfl

@[simp] theorem dirichletCoordinateDerivative_succ w k u :
    dirichletCoordinateDerivative w (k + 1) u =
      dirD (dirichletCoordinateDerivative w k u) w := rfl

theorem dirichletCoordinateDerivative_one_eq_tangential k u :
    dirichletCoordinateDerivative 1 k u = dirichletTangentialDerivative k u := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [dirichletCoordinateDerivative_succ, dirichletTangentialDerivative_succ, ih]

theorem dirichletCoordinateDerivative_iterate w k l u :
    dirichletCoordinateDerivative w k (dirichletCoordinateDerivative w l u) =
      dirichletCoordinateDerivative w (k + l) u := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [dirichletCoordinateDerivative_succ, ih]
      simp [Nat.succ_add]

theorem dirichletCoordinateDerivative_contDiffOn  (hU : IsOpen U)
     (hu : ContDiffOn ℝ ∞ u U) w k :
    ContDiffOn ℝ ∞ (dirichletCoordinateDerivative w k u) U := by
  induction k with
  | zero => exact hu
  | succ k ih => exact dirichlet_contDiffOn_dirD hU ih w

theorem dirichletCoordinateDerivative_contDiff 
    (hu : ContDiff ℝ ∞ u) w k :
    ContDiff ℝ ∞ (dirichletCoordinateDerivative w k u) := by
  induction k with
  | zero => exact hu
  | succ k ih => exact dirichlet_dirD_contDiff ih w

theorem dirichletCoordinateDerivative_eqOn  (hU : IsOpen U)
     (heq : EqOn u v U) w k :
    EqOn (dirichletCoordinateDerivative w k u) (dirichletCoordinateDerivative w k v) U := by
  intro z hz
  exact (show dirichletCoordinateDerivative w k u =ᶠ[𝓝 z] dirichletCoordinateDerivative w k v by
    induction k with
    | zero => exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz, heq⟩
    | succ k ih =>
        exact (ih.fderiv (𝕜 := ℝ)).fun_comp (fun A : ℂ →L[ℝ] ℂ => A w)).self_of_nhds

theorem dirichlet_bootstrap_dirD_eqOn  (hU : IsOpen U)
     (heq : EqOn u v U) w : EqOn (dirD u w) (dirD v w) U :=
  dirichletCoordinateDerivative_eqOn hU heq w 1

theorem dirichlet_bootstrap_dirD_const_mul  
    (hu : DifferentiableAt ℝ u z) c w :
    dirD (fun x => c * u x) w z = c * dirD u w z := by
  change fderiv ℝ (fun x => c * u x) z w = _
  rw [fderiv_const_mul hu c]
  rfl

theorem dirichletCoordinateDerivative_add_eqOn  (hU : IsOpen U)
     (hu : ContDiffOn ℝ ∞ u U)
    (hv : ContDiffOn ℝ ∞ v U) (w : ℂ) k :
    EqOn (dirichletCoordinateDerivative w k (fun z => u z + v z))
      (fun z => dirichletCoordinateDerivative w k u z +
        dirichletCoordinateDerivative w k v z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      exact dirichlet_normal_dirD_add
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz)
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hv w k) hz) w

theorem dirichletCoordinateDerivative_sub_eqOn  (hU : IsOpen U)
     (hu : ContDiffOn ℝ ∞ u U)
    (hv : ContDiffOn ℝ ∞ v U) (w : ℂ) k :
    EqOn (dirichletCoordinateDerivative w k (fun z => u z - v z))
      (fun z => dirichletCoordinateDerivative w k u z -
        dirichletCoordinateDerivative w k v z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      exact dirichlet_normal_dirD_sub
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz)
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hv w k) hz) w

theorem dirichletCoordinateDerivative_const_mul_eqOn  (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ ∞ u U) c w k :
    EqOn (dirichletCoordinateDerivative w k (fun z => c * u z))
      (fun z => c * dirichletCoordinateDerivative w k u z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      exact dirichlet_bootstrap_dirD_const_mul
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz) c w

/-- A coefficient whose derivative in w is zero passes through every
actual w-derivative. No assertion about derivatives at the boundary is used. -/
theorem dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero 
    (hU : IsOpen U)  (ha : ContDiffOn ℝ ∞ a U)
    (hu : ContDiffOn ℝ ∞ u U) w
    (hzero : ∀ z ∈ U, dirD a w z = 0) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k (fun z => a z * u z))
      (fun z => a z * dirichletCoordinateDerivative w k u z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz,
        dirichlet_normal_dirD_mul
          (dirichletBootstrap_differentiableAt hU ha hz)
          (dirichletBootstrap_differentiableAt hU
            (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz) w, hzero z hz]
      simp

/-- Coordinate commutation follows from the actual smooth interior germ. -/
theorem dirichletCoordinateDerivative_dirD_comm_eqOn  (hU : IsOpen U)
     (hu : ContDiffOn ℝ ∞ u U) v w k :
    EqOn (dirichletCoordinateDerivative v k (dirD u w))
      (dirD (dirichletCoordinateDerivative v k u) w) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih v hz]
      exact dirichlet_normal_dirD_comm hU
        (dirichletCoordinateDerivative_contDiffOn hU hu v k) hz w v

theorem dirichletCoordinateDerivative_comm_eqOn  (hU : IsOpen U)
     (hu : ContDiffOn ℝ ∞ u U) v w p q :
    EqOn (dirichletCoordinateDerivative v p (dirichletCoordinateDerivative w q u))
      (dirichletCoordinateDerivative w q (dirichletCoordinateDerivative v p u)) U := by
  induction q with
  | zero => intro z hz; rfl
  | succ q ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichletCoordinateDerivative_dirD_comm_eqOn hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w q) v w p hz,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      rfl

/-- q actual derivatives in the flattened normal direction. -/
local notation "Φ0" => dirichletCoordinateDerivative Complex.I

def dirichletNormalDerivative (q : ℕ) (u : ℂ → ℂ) : ℂ → ℂ :=
  Φ0 q u

/-- The p tangential and q normal actual partial derivative. -/
def dirichletMixedDerivative (p q : ℕ) (u : ℂ → ℂ) : ℂ → ℂ :=
  dirichletTangentialDerivative p (dirichletNormalDerivative q u)

theorem dirichletMixedDerivative_contDiffOn  (hU : IsOpen U)
     (hu : ContDiffOn ℝ ∞ u U) p q :
    ContDiffOn ℝ ∞ (dirichletMixedDerivative p q u) U := by
  rw [dirichletMixedDerivative, ← dirichletCoordinateDerivative_one_eq_tangential]
  exact dirichletCoordinateDerivative_contDiffOn hU
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I q) 1 p

theorem dirichletMixedDerivative_contDiff 
    (hu : ContDiff ℝ ∞ u) p q :
    ContDiff ℝ ∞ (dirichletMixedDerivative p q u) := by
  rw [dirichletMixedDerivative, ← dirichletCoordinateDerivative_one_eq_tangential]
  exact dirichletCoordinateDerivative_contDiff
    (dirichletCoordinateDerivative_contDiff hu Complex.I q) 1 p

theorem dirD_dirichletMixedDerivative_one p q u :
    dirD (dirichletMixedDerivative p q u) 1 = dirichletMixedDerivative (p + 1) q u := rfl

theorem dirD_dirichletMixedDerivative_I_eqOn  (hU : IsOpen U)
     (hu : ContDiffOn ℝ ∞ u U) p q :
    EqOn (dirD (dirichletMixedDerivative p q u) Complex.I)
      (dirichletMixedDerivative p (q + 1) u) U := by
  intro z hz
  simpa [dirichletMixedDerivative, dirichletNormalDerivative, dirichletCoordinateDerivative_one_eq_tangential] using
      (dirichletCoordinateDerivative_dirD_comm_eqOn hU
        (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I q) 1 Complex.I p hz).symm

/-! The coefficient bounds below are genuine compact bounds on the actual
closed rectangle. Only the smooth coefficient, not the solution, is bounded. -/

/-- Recursive Leibniz recovery in L². Each recursive call uses strictly
fewer tangential derivatives of the actual input. The coefficient and all
its tangential derivatives have the compact bounds just proved. -/
theorem dirichletBootstrap_tangential_mul_memLp {a b : ℝ} 
    (hc : ContDiff ℝ ∞ c)
    (hv : ContDiffOn ℝ ∞ v (smoothDirichletHalfBox a b)) (p : ℕ)
    (hLp : ∀ j ≤ p, MemLp (dirichletTangentialDerivative j v) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletTangentialDerivative p (fun z => c z * v z)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  induction p generalizing c v with
  | zero => exact (by
    obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
      hc.continuous.continuousOn
    apply (hLp 0 le_rfl).of_le_mul (c := M) (hc.continuous.aestronglyMeasurable.mul (hLp 0 le_rfl).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    change ‖c z * v z‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hM z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩) (norm_nonneg _))
  | succ p ih =>
      let U := smoothDirichletHalfBox a b
      have hU : IsOpen U := isOpen_smoothDirichletHalfBox a b
      have hdv := dirichlet_contDiffOn_dirD hU hv 1
      have hdc := dirichlet_dirD_contDiff hc 1
      have h₁ := ih hc hdv (fun j hj => by
        rw [dirichletTangentialDerivative_succ_right]
        exact hLp (j + 1) (by omega))
      exact ((ih hdc hv (fun j hj => hLp j (by omega))).add h₁).ae_eq (show dirichletTangentialDerivative (p + 1) (fun z => c z * v z) =ᵐ[volume.restrict U] (fun z => dirichletTangentialDerivative p (fun w => dirD c 1 w * v w) z + dirichletTangentialDerivative p (fun w => c w * dirD v 1 w) z) by
        filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
        rw [← dirichletTangentialDerivative_succ_right]
        simpa [dirichletCoordinateDerivative_one_eq_tangential] using
          ((dirichletCoordinateDerivative_eqOn hU (by
            intro z hz
            exact dirichlet_normal_dirD_mul (hc.differentiable (by simp) z)
              (dirichletBootstrap_differentiableAt hU hv hz) 1) 1 p) hz).trans ((dirichletCoordinateDerivative_add_eqOn hU (hdc.contDiffOn.mul hv) (hc.contDiffOn.mul hdv) 1 p) hz)).symm

theorem dirichletBootstrap_tangential_add_memLp  (hU : IsOpen U)
     (hv : ContDiffOn ℝ ∞ v U)
    (hw : ContDiffOn ℝ ∞ w U) p
    (hvLp : MemLp (dirichletTangentialDerivative p v) 2 (volume.restrict U))
    (hwLp : MemLp (dirichletTangentialDerivative p w) 2 (volume.restrict U)) :
    MemLp (dirichletTangentialDerivative p (fun z => v z + w z)) 2 (volume.restrict U) := by
  apply (hvLp.add hwLp).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  simpa [dirichletCoordinateDerivative_one_eq_tangential] using
    (dirichletCoordinateDerivative_add_eqOn hU hv hw 1 p hz).symm

theorem dirichletBootstrap_tangential_sub_memLp  (hU : IsOpen U)
     (hv : ContDiffOn ℝ ∞ v U)
    (hw : ContDiffOn ℝ ∞ w U) p
    (hvLp : MemLp (dirichletTangentialDerivative p v) 2 (volume.restrict U))
    (hwLp : MemLp (dirichletTangentialDerivative p w) 2 (volume.restrict U)) :
    MemLp (dirichletTangentialDerivative p (fun z => v z - w z)) 2 (volume.restrict U) := by
  apply (hvLp.sub hwLp).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  simpa [dirichletCoordinateDerivative_one_eq_tangential] using
    (dirichletCoordinateDerivative_sub_eqOn hU hv hw 1 p hz).symm

/-! Coefficients depend only on the actual horizontal coordinate. -/

theorem dirichletBootstrap_realCoefficient_dirD_I {r : ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (z : ℂ) :
    dirD (fun w => (r w.re : ℂ)) Complex.I z = 0 := by
  change fderiv ℝ (Complex.ofRealCLM ∘ r ∘ Complex.re) z Complex.I = 0
  rw [(Complex.ofRealCLM.hasFDerivAt.comp z (((hr.differentiable (by simp)) z.re).hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)).fderiv]
  simp

theorem dirichletGraphCurvature_contDiff 
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dirichletGraphCurvature f) := by
  exact Complex.ofRealCLM.contDiff.comp
    (((contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hf).2)).2).comp Complex.reCLM.contDiff)

theorem dirichletNormalCoefficientInverse_contDiff 
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dirichletNormalCoefficientInverse f) := by
  have hr : ContDiff ℝ ∞ (fun x => (1 + (deriv f x) ^ 2)⁻¹) :=
    (contDiff_const.add (((contDiff_infty_iff_deriv.mp hf).2).pow 2)).inv (fun x => by positivity)
  exact Complex.ofRealCLM.contDiff.comp (hr.comp Complex.reCLM.contDiff)

theorem dirD_dirichletNormalCoefficientInverse_I 
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    dirD (dirichletNormalCoefficientInverse f) Complex.I z = 0 := by
  have hr : ContDiff ℝ ∞ (fun x => (1 + (deriv f x) ^ 2)⁻¹) :=
    (contDiff_const.add (((contDiff_infty_iff_deriv.mp hf).2).pow 2)).inv (fun x => by positivity)
  exact dirichletBootstrap_realCoefficient_dirD_I hr z

theorem dirD_two_mul_dirichletGraphSlope_I 
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    dirD (fun w => 2 * dirichletGraphSlope f w) Complex.I z = 0 := by
  rw [dirichlet_bootstrap_dirD_const_mul
    ((dirichletGraphSlope_contDiff hf).differentiable (by simp) z),
    dirD_dirichletGraphSlope_I hf z, mul_zero]

theorem dirichletNormalDerivative_mixed_eqOn  (hU : IsOpen U)
     (hu : ContDiffOn ℝ ∞ u U) q p r :
    EqOn (dirichletNormalDerivative q (dirichletMixedDerivative p r u))
      (dirichletMixedDerivative p (q + r) u) U := by
  intro z hz
  simpa [dirichletNormalDerivative, dirichletMixedDerivative, dirichletCoordinateDerivative_one_eq_tangential, dirichletCoordinateDerivative_iterate] using (dirichletCoordinateDerivative_comm_eqOn hU (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I r) 1 Complex.I p q hz).symm

/-- The actual recovered numerator after q normal differentiations. -/
def dirichletNormalRecoveryExpression (f : ℝ → ℝ) (q : ℕ) (u G : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((-1 : ℂ) * dirichletNormalDerivative q G z +
    dirichletGraphCurvature f z * dirichletNormalDerivative (q + 1) u z) +
    (2 * dirichletGraphSlope f z) * dirichletMixedDerivative 1 (q + 1) u z -
    dirichletMixedDerivative 2 q u z

theorem dirichletNormalRecoveryExpression_contDiffOn  (hU : IsOpen U)
     (hf : ContDiff ℝ ∞ f) 
    (hu : ContDiffOn ℝ ∞ u U) (hG : ContDiffOn ℝ ∞ G U) (q : ℕ) :
    ContDiffOn ℝ ∞ (dirichletNormalRecoveryExpression f q u G) U := by
  exact (((dirichletBootstrap_contDiffOn_const_mul (dirichletCoordinateDerivative_contDiffOn hU hG Complex.I q) (-1)).add ((dirichletGraphCurvature_contDiff hf).contDiffOn.mul (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I (q + 1)))).add ((dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn.mul (dirichletMixedDerivative_contDiffOn hU hu 1 (q + 1)))).sub (dirichletMixedDerivative_contDiffOn hU hu 2 q)

/-! L² closure on the actual half rectangle. -/

theorem dirichletTangentialDerivative_mixed j p q u :
    dirichletTangentialDerivative j (dirichletMixedDerivative p q u) =
      dirichletMixedDerivative (j + p) q u := by
  simpa [dirichletCoordinateDerivative_one_eq_tangential, dirichletMixedDerivative] using
    dirichletCoordinateDerivative_iterate 1 j p (dirichletNormalDerivative q u)

theorem dirichletBootstrap_tangential_const_mul_memLp  (hU : IsOpen U)
     (hv : ContDiffOn ℝ ∞ v U) c p
    (hvLp : MemLp (dirichletTangentialDerivative p v) 2 (volume.restrict U)) :
    MemLp (dirichletTangentialDerivative p (fun z => c * v z)) 2 (volume.restrict U) := by
  apply (hvLp.const_mul c).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  simpa [dirichletCoordinateDerivative_one_eq_tangential] using
    (dirichletCoordinateDerivative_const_mul_eqOn hU hv c 1 p hz).symm

theorem dirichletBootstrap_continuous_memLp {a b : ℝ}
     (hv : Continuous v) :
    MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)) := by
  obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
    hv.continuousOn
  letI : IsFiniteMeasure (volume.restrict (smoothDirichletHalfBox a b)) :=
    ⟨by simpa [Measure.restrict_apply_univ] using
      (dirichlet_halfBox_isBounded (a := a) (b := b)).measure_lt_top⟩
  apply MemLp.of_bound hv.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  exact hM z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

/-- Finite-order recovery from genuine tangential data on one actual
half rectangle. The normal-order induction uses only lower normal orders
of the same total order, rather than an assumed higher normal derivative. -/
theorem dirichlet_mixed_derivative_memLp_of_tangential_data 
     (hf : ContDiff ℝ ∞ f)
     (hu : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox a b))
    (hG : ContDiff ℝ ∞ G)
    (hstrong : ∀ z ∈ smoothDirichletHalfBox a b,
      dirichletFlattenedDivergence f u z = -G z) N
    (htangent : ∀ j ≤ N,
      MemLp (dirichletTangentialDerivative j u) 2
        (volume.restrict (smoothDirichletHalfBox a b)) ∧
      MemLp (dirD (dirichletTangentialDerivative j u) Complex.I) 2
        (volume.restrict (smoothDirichletHalfBox a b))) :
    ∀ p q : ℕ, p + q ≤ N → MemLp (dirichletMixedDerivative p q u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let U := smoothDirichletHalfBox a b
  have hU : IsOpen U := isOpen_smoothDirichletHalfBox a b
  exact fun p q hpq => (show ∀ q p : ℕ, p + q ≤ N → MemLp (dirichletMixedDerivative p q u) 2 (volume.restrict U) by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro p hp
      cases q with
      | zero => exact (htangent p (by omega)).1
      | succ q =>
        cases q with
        | zero =>
            apply (htangent p (by omega)).2.ae_eq
            filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
            have h_inl : EqOn (dirichletMixedDerivative p 1 u) (dirichletNormalDerivative 1 (dirichletTangentialDerivative p u)) U := by
              simpa [dirichletMixedDerivative, dirichletNormalDerivative, dirichletCoordinateDerivative_one_eq_tangential] using
                  dirichletCoordinateDerivative_comm_eqOn hU hu 1 Complex.I p 1
            exact (h_inl hz).symm
        | succ q =>
            have hm : MemLp (dirichletTangentialDerivative p
                (fun z => dirichletNormalCoefficientInverse f z *
                  dirichletNormalRecoveryExpression f q u G z)) 2 (volume.restrict U) := by
              apply dirichletBootstrap_tangential_mul_memLp
                (dirichletNormalCoefficientInverse_contDiff hf)
                (dirichletNormalRecoveryExpression_contDiffOn hU hf hu hG.contDiffOn q) p
              intro j hj
              exact (by
                let U := smoothDirichletHalfBox a b
                have hU : IsOpen U := isOpen_smoothDirichletHalfBox a b
                let t₀ : ℂ → ℂ := fun z => (-1) * dirichletNormalDerivative q G z
                let t₁ : ℂ → ℂ := fun z => dirichletGraphCurvature f z *
                  dirichletNormalDerivative (q + 1) u z
                let t₂ : ℂ → ℂ := fun z => 2 * dirichletGraphSlope f z *
                  dirichletMixedDerivative 1 (q + 1) u z
                let t₃ := dirichletMixedDerivative 2 q u
                have ht₀ : ContDiffOn ℝ ∞ t₀ U :=
                  dirichletBootstrap_contDiffOn_const_mul
                    (dirichletCoordinateDerivative_contDiffOn hU hG.contDiffOn Complex.I q) (-1)
                have ht₁ :=
                  (dirichletGraphCurvature_contDiff hf).contDiffOn.mul
                    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I (q + 1))
                have ht₂ :=
                  (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn.mul
                    (dirichletMixedDerivative_contDiffOn hU hu 1 (q + 1))
                exact dirichletBootstrap_tangential_sub_memLp hU ((ht₀.add ht₁).add ht₂) (dirichletMixedDerivative_contDiffOn hU hu 2 q) j
                  (dirichletBootstrap_tangential_add_memLp hU (ht₀.add ht₁) ht₂ j
                    (dirichletBootstrap_tangential_add_memLp hU ht₀ ht₁ j (dirichletBootstrap_tangential_const_mul_memLp hU (dirichletCoordinateDerivative_contDiffOn hU hG.contDiffOn Complex.I q) (-1) j (dirichletBootstrap_continuous_memLp (dirichletMixedDerivative_contDiff hG j q).continuous)) (by
                      apply dirichletBootstrap_tangential_mul_memLp (dirichletGraphCurvature_contDiff hf)
                        (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I (q + 1)) j
                      intro j hj
                      exact (fun j hj => ih (q + 1) (by omega) j hj) j (by omega))) (by
                      apply dirichletBootstrap_tangential_mul_memLp
                        (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2)
                        (dirichletMixedDerivative_contDiffOn hU hu 1 (q + 1)) j
                      intro j hj
                      rw [dirichletTangentialDerivative_mixed]
                      exact (fun j hj => ih (q + 1) (by omega) j hj) (j + 1) (by omega))) (by
                      rw [dirichletTangentialDerivative_mixed]
                      exact (fun j hj => ih q (by omega) j hj) (j + 2) (by omega)))
            apply hm.ae_eq
            filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
            simpa [dirichletCoordinateDerivative_one_eq_tangential, dirichletMixedDerivative] using ((dirichletCoordinateDerivative_eqOn hU (by
              have hbase : EqOn (dirichletNormalDerivative 2 u)
                  (fun z => dirichletNormalCoefficientInverse f z *
                    dirichletNormalRecoveryExpression f 0 u G z) U := by
                intro z hz
                have hr := dirichlet_normal_derivative_recovery hU hf hu hstrong hz
                rw [dirichlet_normal_dirD_comm hU hu hz 1 Complex.I] at hr
                simpa [dirichletNormalRecoveryExpression, dirichletMixedDerivative, dirichletNormalDerivative, dirichletCoordinateDerivative, dirichletTangentialDerivative, mul_assoc] using hr
              have hq := dirichletCoordinateDerivative_eqOn hU hbase Complex.I q
              have hmul := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
                (dirichletNormalCoefficientInverse_contDiff hf).contDiffOn
                (dirichletNormalRecoveryExpression_contDiffOn hU hf hu hG.contDiffOn 0) Complex.I
                (fun z _ => dirD_dirichletNormalCoefficientInverse_I hf z) q
              intro z hz
              have hleft : Φ0 q (dirichletNormalDerivative 2 u) =
                  dirichletNormalDerivative (q + 2) u :=
                dirichletCoordinateDerivative_iterate Complex.I q 2 u
              rw [← hleft]
              exact (hq hz).trans ((hmul hz).trans (congrArg
                (fun v => dirichletNormalCoefficientInverse f z * v)
                  ((show EqOn (dirichletNormalDerivative q (dirichletNormalRecoveryExpression f 0 u G)) (dirichletNormalRecoveryExpression f q u G) U by
                    let t₀ : ℂ → ℂ := fun z => (-1) * G z
                    let t₁ : ℂ → ℂ := fun z => dirichletGraphCurvature f z * dirichletNormalDerivative 1 u z
                    let t₂ : ℂ → ℂ := fun z => 2 * dirichletGraphSlope f z *
                      dirichletMixedDerivative 1 1 u z
                    let t₃ := dirichletMixedDerivative 2 0 u
                    have h₀ : ContDiffOn ℝ ∞ t₀ U := dirichletBootstrap_contDiffOn_const_mul hG.contDiffOn (-1)
                    have h₁ : ContDiffOn ℝ ∞ t₁ U :=
                      (dirichletGraphCurvature_contDiff hf).contDiffOn.mul
                        (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I 1)
                    have h₂ : ContDiffOn ℝ ∞ t₂ U :=
                      (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn.mul
                        (dirichletMixedDerivative_contDiffOn hU hu 1 1)
                    intro z hz
                    change Φ0 q
                      (fun w => t₀ w + t₁ w + t₂ w - t₃ w) z = _
                    rw [dirichletCoordinateDerivative_sub_eqOn hU ((h₀.add h₁).add h₂) (dirichletMixedDerivative_contDiffOn hU hu 2 0) Complex.I q hz]
                    change Φ0 q
                        (fun w => t₀ w + t₁ w + t₂ w) z -
                      Φ0 q t₃ z = _
                    rw [dirichletCoordinateDerivative_add_eqOn hU (h₀.add h₁) h₂ Complex.I q hz]
                    change (Φ0 q (fun w => t₀ w + t₁ w) z +
                        Φ0 q t₂ z) -
                      Φ0 q t₃ z = _
                    rw [dirichletCoordinateDerivative_add_eqOn hU h₀ h₁ Complex.I q hz]
                    change (Φ0 q t₀ z +
                        Φ0 q t₁ z) +
                      Φ0 q t₂ z -
                      Φ0 q t₃ z = _
                    have ht₀ := dirichletCoordinateDerivative_const_mul_eqOn hU hG.contDiffOn (-1) Complex.I q hz
                    have ht₁ := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
                      (dirichletGraphCurvature_contDiff hf).contDiffOn
                      (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I 1) Complex.I
                      (fun w _ => (by
                        exact dirichletBootstrap_realCoefficient_dirD_I
                          ((contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hf).2)).2) w)) q hz
                    have ht₂ := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
                      (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn
                      (dirichletMixedDerivative_contDiffOn hU hu 1 1) Complex.I
                      (fun w _ => dirD_two_mul_dirichletGraphSlope_I hf w) q hz
                    change Φ0 q t₀ z = _ at ht₀
                    change Φ0 q t₁ z = _ at ht₁
                    change Φ0 q t₂ z = _ at ht₂
                    rw [ht₀, ht₁, ht₂]
                    have hn₁ : Φ0 q (dirichletNormalDerivative 1 u) =
                        dirichletNormalDerivative (q + 1) u :=
                      dirichletCoordinateDerivative_iterate Complex.I q 1 u
                    have hmix₁ := dirichletNormalDerivative_mixed_eqOn hU hu q 1 1 hz
                    have hmix₂ := dirichletNormalDerivative_mixed_eqOn hU hu q 2 0 hz
                    change Φ0 q (dirichletMixedDerivative 1 1 u) z = _
                      at hmix₁
                    change Φ0 q t₃ z = _ at hmix₂
                    change -1 * Φ0 q G z +
                      dirichletGraphCurvature f z *
                        Φ0 q (dirichletNormalDerivative 1 u) z +
                      2 * dirichletGraphSlope f z *
                        Φ0 q (dirichletMixedDerivative 1 1 u) z -
                      Φ0 q t₃ z = _
                    rw [hn₁, hmix₁, hmix₂]
                    simp [dirichletNormalRecoveryExpression, dirichletNormalDerivative]) hz)))) 1 p) hz).symm) q p hpq

/-- This composition uses the actual tangential energy theorem, rather
than leaving tangential high-order regularity as a final premise. -/
theorem exists_dirichlet_halfBox_mixed_derivative_memLp
     (hA : 0 < A) (hb : 0 < b) 
    (hf : ContDiff ℝ ∞ f)  (hLip : LipschitzWith K f)
     (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ ∞ u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ ∞ G) N :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ p q : ℕ, p + q ≤ N → MemLp (dirichletMixedDerivative p q u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ)) := by
  obtain ⟨ρ, hρ, hρA, hρb, htangent⟩ :=
    exists_dirichlet_halfBox_higher_tangential_memLp hA hb hf hLip hc hs hz hm hg hstrong hGs N
  have hWU : smoothDirichletHalfBox ρ ρ ⊆ smoothDirichletHalfBox A b := fun z hz' =>
    ⟨hz'.1.trans (by linarith), hz'.2.1, hz'.2.2.trans hρb⟩
  refine ⟨ρ, hρ, hρA, hρb, ?_⟩
  exact dirichlet_mixed_derivative_memLp_of_tangential_data hf (hs.mono hWU) hGs
    (fun z hz' => hstrong z (hWU hz')) N htangent

end PolyaNeumann
end
