module

public import RequestProject.PlanarTypes

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

theorem dirichletBootstrap_differentiableAt  (hU : IsOpen U)
    {v : PlaneMap} (hv : RealSmoothOn v U)  (hz : z ∈ U) :
    DifferentiableAt ℝ v z :=
  (hv.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)

theorem dirichletBootstrap_contDiff_const_mul {v : PlaneMap}
    (hv : RealSmooth v) c :
    RealSmooth (fun z => c * v z) := contDiff_const.mul hv

theorem dirichletBootstrap_contDiffOn_const_mul  {v : PlaneMap}
    (hv : RealSmoothOn v U) c :
    RealSmoothOn (fun z => c * v z) U := contDiffOn_const.mul hv

/-- Iteration of the actual real directional derivative. -/
@[simp] def dirichletCoordinateDerivative (w : ℂ) : ℕ → (PlaneMap) → (PlaneMap)
  | 0, u => u
  | k + 1, u => dirD (dirichletCoordinateDerivative w k u) w



theorem dirichletCoordinateDerivative_one_eq_tangential k u :
    dirichletCoordinateDerivative 1 k u = dirichletTangentialDerivative k u := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp_all

theorem dirichletCoordinateDerivative_iterate w k l u :
    dirichletCoordinateDerivative w k (dirichletCoordinateDerivative w l u) =
      dirichletCoordinateDerivative w (k + l) u := by
  induction k with
  | zero => simp_all
  | succ k ih =>
      grind only [dirichletCoordinateDerivative.eq_2]

theorem dirichletCoordinateDerivative_contDiffOn  (hU : IsOpen U)
     (hu : RealSmoothOn u U) w k :
    RealSmoothOn (dirichletCoordinateDerivative w k u) U := (Nat.recAux hu (fun k ih => dirichlet_contDiffOn_dirD hU ih w) k)

theorem dirichletCoordinateDerivative_contDiff 
    (hu : RealSmooth u) w k :
    RealSmooth (dirichletCoordinateDerivative w k u) := (Nat.recAux hu (fun k ih => dirichlet_dirD_contDiff ih w) k)

theorem dirichletCoordinateDerivative_eventuallyEq  
    (heq : u =ᶠ[𝓝 z] v) w k :
    dirichletCoordinateDerivative w k u =ᶠ[𝓝 z] dirichletCoordinateDerivative w k v := (Nat.recAux heq (fun k ih => EventuallyEq.fun_comp (EventuallyEq.fderiv ih) fun A => A w) k)

section
variable {U } (hU : IsOpen U) {u v : PlaneMap} (heq : EqOn u v U) (w : ℂ)
include U hU u v heq w

theorem dirichletCoordinateDerivative_eqOn k :
    EqOn (dirichletCoordinateDerivative w k u) (dirichletCoordinateDerivative w k v) U := by
  intro z hz
  have hg  := Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz, heq⟩
  exact (dirichletCoordinateDerivative_eventuallyEq hg w k).self_of_nhds

theorem dirichlet_bootstrap_dirD_eqOn : EqOn (dirD u w) (dirD v w) U :=
  dirichletCoordinateDerivative_eqOn hU heq w 1

end


theorem dirichlet_bootstrap_dirD_const_mul  
    (hu : DifferentiableAt ℝ u z) c w :
    dirD (fun x => c * u x) w z = c * dirD u w z := by
  change fderiv ℝ (fun x => c * u x) z w = _
  rw [fderiv_const_mul hu c]
  rfl

section
variable {U } (hU : IsOpen U) {u v : PlaneMap} (hu : RealSmoothOn u U) (hv : RealSmoothOn v U) (w : ℂ) (k : ℕ)
include U hU u v hu hv w k

theorem dirichletCoordinateDerivative_add_eqOn :
    EqOn (dirichletCoordinateDerivative w k (fun z => u z + v z))
      (fun z => dirichletCoordinateDerivative w k u z +
        dirichletCoordinateDerivative w k v z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative.eq_2,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      exact dirichlet_normal_dirD_add
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz)
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hv w k) hz) w

theorem dirichletCoordinateDerivative_sub_eqOn :
    EqOn (dirichletCoordinateDerivative w k (fun z => u z - v z))
      (fun z => dirichletCoordinateDerivative w k u z -
        dirichletCoordinateDerivative w k v z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative.eq_2,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      exact dirichlet_normal_dirD_sub
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz)
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hv w k) hz) w

end


section
variable {U } (hU : IsOpen U) {u : PlaneMap} (hu : RealSmoothOn u U)

include U hU u hu in
theorem dirichletCoordinateDerivative_const_mul_eqOn c w k :
    EqOn (dirichletCoordinateDerivative w k (fun z => c * u z))
      (fun z => c * dirichletCoordinateDerivative w k u z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative.eq_2,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      exact dirichlet_bootstrap_dirD_const_mul
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz) c w

/-- A coefficient whose derivative in w is zero passes through every
actual w-derivative. No assertion about derivatives at the boundary is used. -/
theorem dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero 
    (hU : IsOpen U)  (ha : RealSmoothOn a U)
    (hu : RealSmoothOn u U) w
    (hzero : ∀ z ∈ U, dirD a w z = 0) k :
    EqOn (dirichletCoordinateDerivative w k (fun z => a z * u z))
      (fun z => a z * dirichletCoordinateDerivative w k u z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative.eq_2,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz,
        dirichlet_normal_dirD_mul
          (dirichletBootstrap_differentiableAt hU ha hz)
          (dirichletBootstrap_differentiableAt hU
            (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz) w, hzero z hz]
      simp_all

section
include U hU u hu

/-- Coordinate commutation follows from the actual smooth interior germ. -/
theorem dirichletCoordinateDerivative_dirD_comm_eqOn v w k :
    EqOn (dirichletCoordinateDerivative v k (dirD u w))
      (dirD (dirichletCoordinateDerivative v k u) w) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative.eq_2,
        dirichlet_bootstrap_dirD_eqOn hU ih v hz]
      exact dirichlet_dirD_comm hU
        (dirichletCoordinateDerivative_contDiffOn hU hu v k) hz w v

theorem dirichletCoordinateDerivative_comm_eqOn v w p q :
    EqOn (dirichletCoordinateDerivative v p (dirichletCoordinateDerivative w q u))
      (dirichletCoordinateDerivative w q (dirichletCoordinateDerivative v p u)) U := by
  induction q with
  | zero => intro z hz; rfl
  | succ q ih =>
      intro z hz
      rw [dirichletCoordinateDerivative.eq_2,
        dirichletCoordinateDerivative_dirD_comm_eqOn hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w q) v w p hz,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      rfl

end


/-- q actual derivatives in the flattened normal direction. -/
def dirichletNormalDerivative q u  :=
  dirichletCoordinateDerivative Complex.I q u

/-- The p tangential and q normal actual partial derivative. -/
def dirichletMixedDerivative p q u  :=
  dirichletTangentialDerivative p (dirichletNormalDerivative q u)

include U hU u hu in
theorem dirichletMixedDerivative_contDiffOn p q :
    RealSmoothOn (dirichletMixedDerivative p q u) U := by
  rw [dirichletMixedDerivative, ← dirichletCoordinateDerivative_one_eq_tangential]
  simp_all [dirichletCoordinateDerivative_contDiffOn, PolyaNeumann.dirichletNormalDerivative]

theorem dirichletMixedDerivative_contDiff 
    (hu : RealSmooth u) p q :
    RealSmooth (dirichletMixedDerivative p q u) := by
  rw [dirichletMixedDerivative, ← dirichletCoordinateDerivative_one_eq_tangential]
  simp_all [dirichletCoordinateDerivative_contDiff, PolyaNeumann.dirichletNormalDerivative]

include U hU u hu in
theorem dirichletMixedDerivative_eq_normal_tangential p q :
    EqOn (dirichletMixedDerivative p q u)
      (dirichletNormalDerivative q (dirichletTangentialDerivative p u)) U := by
  simpa  [dirichletMixedDerivative, dirichletNormalDerivative,
    dirichletCoordinateDerivative_one_eq_tangential] using
      dirichletCoordinateDerivative_comm_eqOn hU hu 1 Complex.I p q

theorem dirD_dirichletMixedDerivative_one p q u :
    dirD (dirichletMixedDerivative p q u) 1 = dirichletMixedDerivative (p + 1) q u := rfl

include U hU u hu in
theorem dirD_dirichletMixedDerivative_I_eqOn p q :
    EqOn (dirD (dirichletMixedDerivative p q u) Complex.I)
      (dirichletMixedDerivative p (q + 1) u) U := by
  intro z hz
  simpa  [dirichletMixedDerivative, dirichletNormalDerivative, dirichletCoordinateDerivative_one_eq_tangential] using
      (dirichletCoordinateDerivative_dirD_comm_eqOn hU
        (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I q) 1 Complex.I p hz).symm

end


/-! The coefficient bounds below are genuine compact bounds on the actual
closed rectangle. Only the smooth coefficient, not the solution, is bounded. -/

section
variable {a b : ℝ} {c v : PlaneMap} (hc : RealSmooth c)
include a b c v hc

theorem dirichletBootstrap_smooth_mul_memLp
    (hv : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (fun z => c z * v z) 2 (volume.restrict (smoothDirichletHalfBox a b)) := by
  obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
    hc.continuous.continuousOn
  apply hv.of_le_mul (c := M) (hc.continuous.aestronglyMeasurable.mul hv.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  change ‖c z * v z‖ ≤ M * ‖v z‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (hM z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩) (norm_nonneg _)

/-- Recursive Leibniz recovery in L². Each recursive call uses strictly
fewer tangential derivatives of the actual input. The coefficient and all
its tangential derivatives have the compact bounds just proved. -/
theorem dirichletBootstrap_tangential_mul_memLp
    (hv : RealSmoothOn v (smoothDirichletHalfBox a b)) p
    (hLp : ∀ j ≤ p, MemLp (dirichletTangentialDerivative j v) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletTangentialDerivative p (fun z => c z * v z)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  induction p generalizing c v with
  | zero => simp_all [dirichletBootstrap_smooth_mul_memLp]
  | succ p ih =>
      let U := smoothDirichletHalfBox a b
      have hU  := isOpen_smoothDirichletHalfBox a b
      have hdv := dirichlet_contDiffOn_dirD hU hv 1
      have hdc := dirichlet_dirD_contDiff hc 1
      have h₀ := ih hdc hv (fun j hj => hLp j (by omega))
      have h₁ := ih hc hdv (fun j hj => by
        rw [dirichletTangentialDerivative_succ_right]
        exact hLp (j + 1) (by omega))
      have hsplit : EqOn (dirD (((c * v))) 1)
          (fun z => dirD c 1 z * v z + c z * dirD v 1 z) U := by
        intro z hz
        exact dirichlet_normal_dirD_mul (hc.differentiable (by simp) z)
          (dirichletBootstrap_differentiableAt hU hv hz) 1
      have hiter := dirichletCoordinateDerivative_eqOn hU hsplit 1 p
      have hadd := dirichletCoordinateDerivative_add_eqOn hU
        (hdc.contDiffOn.mul hv) (hc.contDiffOn.mul hdv) 1 p
      have heq : (dirichletTangentialDerivative (p + 1) (((c * v))))
          =ᵐ[volume.restrict U]
            (fun z => dirichletTangentialDerivative p (fun w => dirD c 1 w * v w) z +
              dirichletTangentialDerivative p (fun w => c w * dirD v 1 w) z) := by
        filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
        rw [← dirichletTangentialDerivative_succ_right]
        simpa  [dirichletCoordinateDerivative_one_eq_tangential] using
          (hiter hz).trans (hadd hz)
      exact (h₀.add h₁).ae_eq heq.symm

end


section
variable {U } (hU : IsOpen U) {v w } (hv : RealSmoothOn v U) (hw : RealSmoothOn w U) (p ) (hvLp : MemLp (dirichletTangentialDerivative p v) 2 (volume.restrict U)) (hwLp : MemLp (dirichletTangentialDerivative p w) 2 (volume.restrict U))
include U hU v w hv hw p hvLp hwLp

theorem dirichletBootstrap_tangential_add_memLp :
    MemLp (dirichletTangentialDerivative p (fun z => v z + w z)) 2 (volume.restrict U) := by
  apply (hvLp.add hwLp).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  simpa  [dirichletCoordinateDerivative_one_eq_tangential] using
    (dirichletCoordinateDerivative_add_eqOn hU hv hw 1 p hz).symm

theorem dirichletBootstrap_tangential_sub_memLp :
    MemLp (dirichletTangentialDerivative p (fun z => v z - w z)) 2 (volume.restrict U) := by
  apply (hvLp.sub hwLp).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  simpa  [dirichletCoordinateDerivative_one_eq_tangential] using
    (dirichletCoordinateDerivative_sub_eqOn hU hv hw 1 p hz).symm

end


/-! Coefficients depend only on the actual horizontal coordinate. -/

theorem dirichletBootstrap_realCoefficient_dirD_I {r : RealMap}
    (hr : RealSmooth r) z :
    dirD (fun w : ℂ => (r w.re : ℂ)) Complex.I z = 0 := by
  have hd := (hr.differentiable (by simp)) z.re
  have hs := Complex.ofRealCLM.hasFDerivAt.comp z
    (hd.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ r ∘ Complex.re) z Complex.I = 0
  rw [hs.fderiv]
  simp_all

section
variable {f : RealMap} (hf : RealSmooth f)
include f hf

theorem dirichletGraphCurvature_contDiff :
    RealSmooth (dirichletGraphCurvature f) := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  exact Complex.ofRealCLM.contDiff.comp
    (((contDiff_infty_iff_deriv.mp hd).2).comp Complex.reCLM.contDiff)

theorem dirD_dirichletGraphCurvature_I z :
    dirD (dirichletGraphCurvature f) Complex.I z = 0 := (dirichletBootstrap_realCoefficient_dirD_I (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).right).right z)

theorem dirichletNormalCoefficientInverse_contDiff :
    RealSmooth (dirichletNormalCoefficientInverse f) := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hr : RealSmooth (fun x : ℝ => (1 + (deriv f x) ^ 2)⁻¹) :=
    (contDiff_const.add (hd.pow 2)).inv (fun x => by positivity)
  exact Complex.ofRealCLM.contDiff.comp (hr.comp Complex.reCLM.contDiff)

theorem dirD_dirichletNormalCoefficientInverse_I z :
    dirD (dirichletNormalCoefficientInverse f) Complex.I z = 0 := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hr : RealSmooth (fun x : ℝ => (1 + (deriv f x) ^ 2)⁻¹) :=
    (contDiff_const.add (hd.pow 2)).inv (fun x => by positivity)
  exact dirichletBootstrap_realCoefficient_dirD_I hr z

theorem dirD_two_mul_dirichletGraphSlope_I z :
    dirD (fun w => (2 : ℂ) * dirichletGraphSlope f w) Complex.I z = 0 := by
  rw [dirichlet_bootstrap_dirD_const_mul
    ((dirichletGraphSlope_contDiff hf).differentiable (by simp) z),
    dirD_dirichletGraphSlope_I hf z, mul_zero]

end


theorem dirichletNormalDerivative_mixed_eqOn  (hU : IsOpen U)
     (hu : RealSmoothOn u U) q p r :
    EqOn (dirichletNormalDerivative q (dirichletMixedDerivative p r u))
      (dirichletMixedDerivative p (q + r) u) U := by
  intro z hz
  have hc := dirichletCoordinateDerivative_comm_eqOn hU
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I r) 1 Complex.I p q hz
  simp_all [dirichletNormalDerivative, dirichletMixedDerivative, dirichletCoordinateDerivative_one_eq_tangential, dirichletCoordinateDerivative_iterate]

/-- The actual recovered numerator after q normal differentiations. -/
def dirichletNormalRecoveryExpression f q u G z  :=
  ((-1 : ℂ) * dirichletNormalDerivative q G z +
    dirichletGraphCurvature f z * dirichletNormalDerivative (q + 1) u z) +
    ((2 : ℂ) * dirichletGraphSlope f z) * dirichletMixedDerivative 1 (q + 1) u z -
    dirichletMixedDerivative 2 q u z

section
variable {U } (hU : IsOpen U) {f : RealMap} (hf : RealSmooth f) {u G : PlaneMap} (hu : RealSmoothOn u U) (hG : RealSmoothOn G U)
include U hU f hf u G hu hG

theorem dirichletNormalRecoveryExpression_contDiffOn q :
    RealSmoothOn (dirichletNormalRecoveryExpression f q u G) U := by
  have h₀ := dirichletBootstrap_contDiffOn_const_mul
    (dirichletCoordinateDerivative_contDiffOn hU hG Complex.I q) (-1)
  have h₁ := (dirichletGraphCurvature_contDiff hf).contDiffOn.mul
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I (q + 1))
  have h₂ := (dirichletBootstrap_contDiff_const_mul
    (dirichletGraphSlope_contDiff hf) 2).contDiffOn.mul
    (dirichletMixedDerivative_contDiffOn hU hu 1 (q + 1))
  exact ((h₀.add h₁).add h₂).sub (dirichletMixedDerivative_contDiffOn hU hu 2 q)

theorem dirichletNormalRecoveryExpression_zero_normal_eqOn q :
    EqOn (dirichletNormalDerivative q (dirichletNormalRecoveryExpression f 0 u G))
      (dirichletNormalRecoveryExpression f q u G) U := by
  let t₀  := fun z => (-1) * G z
  let t₁  := ((dirichletGraphCurvature f * dirichletNormalDerivative 1 u))
  let t₂  := fun z => (2 * dirichletGraphSlope f z) *
    dirichletMixedDerivative 1 1 u z
  let t₃ := dirichletMixedDerivative 2 0 u
  have h₀  := dirichletBootstrap_contDiffOn_const_mul hG (-1)
  have h₁ : RealSmoothOn t₁ U :=
    (dirichletGraphCurvature_contDiff hf).contDiffOn.mul
      (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I 1)
  have h₂  :=
    (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn.mul
      (dirichletMixedDerivative_contDiffOn hU hu 1 1)
  have h₃  := dirichletMixedDerivative_contDiffOn hU hu 2 0
  intro z hz
  change dirichletCoordinateDerivative Complex.I q
    (fun w => (t₀ w + t₁ w) + t₂ w - t₃ w) z = _
  rw [dirichletCoordinateDerivative_sub_eqOn hU ((h₀.add h₁).add h₂) h₃ Complex.I q hz]
  change dirichletCoordinateDerivative Complex.I q
      (fun w => (t₀ w + t₁ w) + t₂ w) z -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  rw [dirichletCoordinateDerivative_add_eqOn hU (h₀.add h₁) h₂ Complex.I q hz]
  change (dirichletCoordinateDerivative Complex.I q (fun w => t₀ w + t₁ w) z +
      dirichletCoordinateDerivative Complex.I q t₂ z) -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  rw [dirichletCoordinateDerivative_add_eqOn hU h₀ h₁ Complex.I q hz]
  change (dirichletCoordinateDerivative Complex.I q t₀ z +
      dirichletCoordinateDerivative Complex.I q t₁ z) +
    dirichletCoordinateDerivative Complex.I q t₂ z -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  have ht₀ := dirichletCoordinateDerivative_const_mul_eqOn hU hG (-1) Complex.I q hz
  have ht₁ := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
    (dirichletGraphCurvature_contDiff hf).contDiffOn
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I 1) Complex.I
    (fun w _ => dirD_dirichletGraphCurvature_I hf w) q hz
  have ht₂ := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
    (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn
    (dirichletMixedDerivative_contDiffOn hU hu 1 1) Complex.I
    (fun w _ => dirD_two_mul_dirichletGraphSlope_I hf w) q hz
  change dirichletCoordinateDerivative Complex.I q t₁ z = _ at ht₁
  rw [ht₀, ht₁, ht₂]
  have hn₁  :=
    dirichletCoordinateDerivative_iterate Complex.I q 1 u
  have hmix₁ := dirichletNormalDerivative_mixed_eqOn hU hu q 1 1 hz
  have hmix₂ := dirichletNormalDerivative_mixed_eqOn hU hu q 2 0 hz
  change dirichletCoordinateDerivative Complex.I q t₃ z = _ at hmix₂
  simp_all [dirichletNormalDerivative, dirichletNormalRecoveryExpression]

/-- Every higher normal formula is derived by differentiating the actual
second-order equation. All Y derivatives of the graph coefficients vanish. -/
theorem dirichlet_normal_higher_derivative_recovery
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z) q :
    EqOn (dirichletNormalDerivative (q + 2) u)
      (fun z => dirichletNormalCoefficientInverse f z *
        dirichletNormalRecoveryExpression f q u G z) U := by
  have hbase : EqOn (dirichletNormalDerivative 2 u)
      (((dirichletNormalCoefficientInverse f * dirichletNormalRecoveryExpression f 0 u G))) U := by
    intro z hz
    have hr := dirichlet_normal_derivative_recovery hU hf hu hstrong hz
    rw [dirichlet_dirD_comm hU hu hz 1 Complex.I] at hr
    simp_all [dirichletNormalRecoveryExpression, dirichletMixedDerivative, dirichletNormalDerivative]
  have hq := dirichletCoordinateDerivative_eqOn hU hbase Complex.I q
  have hmul := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
    (dirichletNormalCoefficientInverse_contDiff hf).contDiffOn
    (dirichletNormalRecoveryExpression_contDiffOn hU hf hu hG 0) Complex.I
    (fun z _ => dirD_dirichletNormalCoefficientInverse_I hf z) q
  intro z hz
  have hleft : dirichletCoordinateDerivative Complex.I q (dirichletNormalDerivative 2 u) =
      dirichletNormalDerivative (q + 2) u :=
    dirichletCoordinateDerivative_iterate Complex.I q 2 u
  rw [← hleft]
  exact (hq hz).trans ((hmul hz).trans (congrArg
    (fun v : ℂ => dirichletNormalCoefficientInverse f z * v)
      (dirichletNormalRecoveryExpression_zero_normal_eqOn hU hf hu hG q hz)))

end


/-! L² closure on the actual half rectangle. -/

theorem dirichletTangentialDerivative_mixed j p q u :
    dirichletTangentialDerivative j (dirichletMixedDerivative p q u) =
      dirichletMixedDerivative (j + p) q u := by
  simpa  [dirichletCoordinateDerivative_one_eq_tangential, dirichletMixedDerivative] using
    dirichletCoordinateDerivative_iterate 1 j p (dirichletNormalDerivative q u)

theorem dirichletBootstrap_tangential_const_mul_memLp  (hU : IsOpen U)
     (hv : RealSmoothOn v U) c p
    (hvLp : MemLp (dirichletTangentialDerivative p v) 2 (volume.restrict U)) :
    MemLp (dirichletTangentialDerivative p (fun z => c * v z)) 2 (volume.restrict U) := by
  apply (hvLp.const_mul c).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  simpa  [dirichletCoordinateDerivative_one_eq_tangential] using
    (dirichletCoordinateDerivative_const_mul_eqOn hU hv c 1 p hz).symm

theorem dirichletBootstrap_continuous_memLp 
    {v : PlaneMap} (hv : Continuous v) :
    MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)) := by
  obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
    hv.continuousOn
  letI : IsFiniteMeasure (volume.restrict (smoothDirichletHalfBox a b)) :=
    ⟨by simpa   using
      (dirichlet_halfBox_isBounded (a := a) (b := b)).measure_lt_top⟩
  apply MemLp.of_bound hv.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  exact hM z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

/-- Every actual forcing derivative is L² on the bounded half rectangle.
This bound belongs to the smooth forcing; none is assumed for the solution. -/
theorem dirichletBootstrap_mixed_forcing_memLp 
     (hG : RealSmooth G) p q :
    MemLp (dirichletMixedDerivative p q G) 2
      (volume.restrict (smoothDirichletHalfBox a b)) :=
  dirichletBootstrap_continuous_memLp (dirichletMixedDerivative_contDiff hG p q).continuous

section
variable {a b } {f : RealMap} (hf : RealSmooth f) {u G : PlaneMap} (hu : RealSmoothOn u (smoothDirichletHalfBox a b)) (hG : RealSmooth G)
include a b f hf u G hu hG

/-- Tangential differentiation of the genuine numerator preserves L²
when the two lower normal levels have their finite cone of L² derivatives. -/
theorem dirichletNormalRecoveryExpression_tangential_memLp N p q (hp : p + q + 2 ≤ N)
    (h₀ : ∀ j, j + q ≤ N → MemLp (dirichletMixedDerivative j q u) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (h₁ : ∀ j, j + (q + 1) ≤ N → MemLp (dirichletMixedDerivative j (q + 1) u) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletTangentialDerivative p (dirichletNormalRecoveryExpression f q u G)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let U := smoothDirichletHalfBox a b
  have hU  := isOpen_smoothDirichletHalfBox a b
  let t₁  := ((dirichletGraphCurvature f * dirichletNormalDerivative (q + 1) u))
  let t₂  := fun z => (2 * dirichletGraphSlope f z) *
    dirichletMixedDerivative 1 (q + 1) u z
  let t₃ := dirichletMixedDerivative 2 q u
  have ht₀  :=
    dirichletBootstrap_contDiffOn_const_mul
      (dirichletCoordinateDerivative_contDiffOn hU hG.contDiffOn Complex.I q) (-1)
  have ht₁  :=
    (dirichletGraphCurvature_contDiff hf).contDiffOn.mul
      (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I (q + 1))
  have ht₂  :=
    (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn.mul
      (dirichletMixedDerivative_contDiffOn hU hu 1 (q + 1))
  have ht₃  := dirichletMixedDerivative_contDiffOn hU hu 2 q
  have hm₀  :=
    dirichletBootstrap_tangential_const_mul_memLp hU
      (dirichletCoordinateDerivative_contDiffOn hU hG.contDiffOn Complex.I q) (-1) p
        (dirichletBootstrap_mixed_forcing_memLp hG p q)
  have hm₁ : MemLp (dirichletTangentialDerivative p t₁) 2 (volume.restrict U) := by
    apply dirichletBootstrap_tangential_mul_memLp (dirichletGraphCurvature_contDiff hf)
      (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I (q + 1)) p
    intro j hj
    exact h₁ j (by omega)
  have hm₂ : MemLp (dirichletTangentialDerivative p t₂) 2 (volume.restrict U) := by
    apply dirichletBootstrap_tangential_mul_memLp
      (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2)
      (dirichletMixedDerivative_contDiffOn hU hu 1 (q + 1)) p
    grind only [dirichletTangentialDerivative_mixed]
  have hm₃ : MemLp (dirichletTangentialDerivative p t₃) 2 (volume.restrict U) := by
    grind only [dirichletTangentialDerivative_mixed]
  exact dirichletBootstrap_tangential_sub_memLp hU ((ht₀.add ht₁).add ht₂) ht₃ p
    (dirichletBootstrap_tangential_add_memLp hU (ht₀.add ht₁) ht₂ p
      (dirichletBootstrap_tangential_add_memLp hU ht₀ ht₁ p hm₀ hm₁) hm₂) hm₃

/-- Finite-order recovery from genuine tangential data on one actual
half rectangle. The normal-order induction uses only lower normal orders
of the same total order, rather than an assumed higher normal derivative. -/
theorem dirichlet_mixed_derivative_memLp_of_tangential_data
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
  have hU  := isOpen_smoothDirichletHalfBox a b
  have hnormal : ∀ q p : ℕ, p + q ≤ N → MemLp (dirichletMixedDerivative p q u) 2
      (volume.restrict U) := by
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
            exact (dirichletMixedDerivative_eq_normal_tangential hU hu p 1 hz).symm
        | succ q =>
            have hlow₀  := (ih q (by omega))
            have hlow₁  :=
              (ih (q + 1) (by omega))
            have hm : MemLp (dirichletTangentialDerivative p
                (fun z => dirichletNormalCoefficientInverse f z *
                  dirichletNormalRecoveryExpression f q u G z)) 2 (volume.restrict U) := by
              apply dirichletBootstrap_tangential_mul_memLp
                (dirichletNormalCoefficientInverse_contDiff hf)
                (dirichletNormalRecoveryExpression_contDiffOn hU hf hu hG.contDiffOn q) p
              intro j hj
              exact dirichletNormalRecoveryExpression_tangential_memLp hf hu hG N j q
                (by omega) hlow₀ hlow₁
            have hrec := dirichletCoordinateDerivative_eqOn hU
              (dirichlet_normal_higher_derivative_recovery hU hf hu hG.contDiffOn hstrong q) 1 p
            apply hm.ae_eq
            filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
            simpa  [dirichletCoordinateDerivative_one_eq_tangential,
              dirichletMixedDerivative] using (hrec hz).symm
  exact fun p q hpq => hnormal q p hpq

end


/-- This composition uses the actual tangential energy theorem, rather
than leaving tangential high-order regularity as a final premise. -/
theorem exists_dirichlet_halfBox_mixed_derivative_memLp
     (hA : 0 < A) (hb : 0 < b) 
    (hf : RealSmooth f)  (hLip : LipschitzWith K f)
     (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : RealSmoothOn u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Coord, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : RealSmooth G) N :
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
