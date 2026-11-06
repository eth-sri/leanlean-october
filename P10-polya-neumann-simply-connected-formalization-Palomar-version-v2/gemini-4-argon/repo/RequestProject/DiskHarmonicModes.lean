module

public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import RequestProject.DiskGeometry
public import RequestProject.ReconGreen

/-!
# Actual harmonic modes on the unit disk

Both `z^m` and `conj(z)^m` are smooth harmonic functions. Their physical
conormal density on the standard positively oriented circle is `m` times
the boundary mode. The signs of their Fourier frequencies are opposite;
the conormal multipliers are both nonnegative.

A fixed compact cutoff is identically one on a neighbourhood of the
closed disk. This makes the classical physical Green formula applicable
to harmonic polynomials without any assumed Fourier--Green identity.
It gives the gradient Gram matrix `2πm δmn` and an actual orthonormal
family in the two-component disk `L²` gradient space. The zero mode is
excluded before normalization.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real ContDiff ComplexConjugate Topology InnerProductSpace

def diskHolomorphicMode (m : ℕ) (z : ℂ) : ℂ := z ^ m

def diskAntiholomorphicMode (m : ℕ) (z : ℂ) : ℂ := conj z ^ m

theorem contDiff_diskHolomorphicMode m :
    ContDiff ℝ ∞ (diskHolomorphicMode m) :=
  contDiff_id.pow m

theorem contDiff_diskAntiholomorphicMode m :
    ContDiff ℝ ∞ (diskAntiholomorphicMode m) :=
  Complex.conjCLE.contDiff.pow m

theorem fderiv_diskHolomorphicMode m z v :
    fderiv ℝ (diskHolomorphicMode m) z v = (m : ℂ) * z ^ (m - 1) * v := by
  change fderiv ℝ (fun w => w ^ m) z v = _
  rw [(hasFDerivAt_pow (𝕜 := ℝ) (x := z) m).fderiv]
  simp

theorem fderiv_diskAntiholomorphicMode m z v :
    fderiv ℝ (diskAntiholomorphicMode m) z v =
      (m : ℂ) * conj z ^ (m - 1) * conj v := by
  change fderiv ℝ (fun w => conj w ^ m) z v = _
  simpa [diskAntiholomorphicMode, Complex.conjCLE_apply] using congrArg (fun A : ℂ →L[ℝ] ℂ => A v) ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z)).pow m).fderiv

theorem dirD_diskHolomorphicMode m v z :
    dirD (diskHolomorphicMode m) v z = (m : ℂ) * z ^ (m - 1) * v :=
  fderiv_diskHolomorphicMode m z v

theorem dirD_diskAntiholomorphicMode m v z :
    dirD (diskAntiholomorphicMode m) v z =
      (m : ℂ) * conj z ^ (m - 1) * conj v :=
  fderiv_diskAntiholomorphicMode m z v

private lemma disk_dirD_const_mul a  
    (hφ : DifferentiableAt ℝ φ z) v :
    dirD (fun w => a * φ w) v z = a * dirD φ v z := by
  unfold dirD
  rw [fderiv_const_mul hφ a]
  simp

theorem lap_diskHolomorphicMode m (z : ℂ) :
    lap (diskHolomorphicMode m) z = 0 := by
  have hd :=
    (contDiff_diskHolomorphicMode (m - 1)).differentiable (by simp) z
  rw [lap, show dirD (diskHolomorphicMode m) 1 = fun w => m * diskHolomorphicMode (m - 1) w by
    funext w
    simp [dirD_diskHolomorphicMode, diskHolomorphicMode], show dirD (diskHolomorphicMode m) Complex.I = fun w => m * Complex.I * diskHolomorphicMode (m - 1) w by
    funext w
    simp [dirD_diskHolomorphicMode, diskHolomorphicMode]
    ring, disk_dirD_const_mul _ hd 1, disk_dirD_const_mul _ hd Complex.I]
  simp [dirD_diskHolomorphicMode]
  calc
    _ = m * (m - 1 : ℕ) * z ^ ((m - 1) - 1) *
        (1 + Complex.I ^ 2) := by ring
    _ = 0 := by rw [Complex.I_sq]; ring

theorem lap_diskAntiholomorphicMode m (z : ℂ) :
    lap (diskAntiholomorphicMode m) z = 0 := by
  have hd :=
    (contDiff_diskAntiholomorphicMode (m - 1)).differentiable (by simp) z
  rw [lap, show dirD (diskAntiholomorphicMode m) 1 = fun w => m * diskAntiholomorphicMode (m - 1) w by
    funext w
    simp [dirD_diskAntiholomorphicMode, diskAntiholomorphicMode], show dirD (diskAntiholomorphicMode m) Complex.I = fun w => m * (-Complex.I) * diskAntiholomorphicMode (m - 1) w by
    funext w
    simp [dirD_diskAntiholomorphicMode, diskAntiholomorphicMode]
    ring, disk_dirD_const_mul _ hd 1, disk_dirD_const_mul _ hd Complex.I]
  simp [dirD_diskAntiholomorphicMode]
  calc
    _ = m * (m - 1 : ℕ) * conj z ^ ((m - 1) - 1) *
        (1 + Complex.I ^ 2) := by ring
    _ = 0 := by rw [Complex.I_sq]; ring

local notation "Φ0" => circleMap 0 1

theorem unitCircle_conormalDirection θ :
    -(Complex.I * deriv (Φ0) θ) = Φ0 θ := by
  rw [deriv_circleMap]
  calc
    _ = -(Complex.I * Complex.I) * Φ0 θ := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem conormal_diskHolomorphicMode m θ :
    fderiv ℝ (diskHolomorphicMode m) (Φ0 θ)
      (-(Complex.I * deriv (Φ0) θ)) =
      (m : ℂ) * diskHolomorphicMode m (Φ0 θ) := by
  rw [unitCircle_conormalDirection, fderiv_diskHolomorphicMode]
  unfold diskHolomorphicMode
  cases m with
  | zero => simp
  | succ m => simp [pow_succ]; ring

theorem conormal_diskAntiholomorphicMode m θ :
    fderiv ℝ (diskAntiholomorphicMode m) (Φ0 θ)
      (-(Complex.I * deriv (Φ0) θ)) =
      (m : ℂ) * diskAntiholomorphicMode m (Φ0 θ) := by
  rw [unitCircle_conormalDirection, fderiv_diskAntiholomorphicMode]
  unfold diskAntiholomorphicMode
  cases m with
  | zero => simp
  | succ m => simp [pow_succ]; ring

theorem diskHolomorphicMode_unitCircle m θ :
    diskHolomorphicMode m (Φ0 θ) =
      Complex.exp ((m : ℂ) * Complex.I * θ) := by
  simp [diskHolomorphicMode, circleMap]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem diskAntiholomorphicMode_unitCircle m θ :
    diskAntiholomorphicMode m (Φ0 θ) =
      Complex.exp (-((m : ℂ) * Complex.I * θ)) := by
  simp [diskAntiholomorphicMode, circleMap, ← Complex.exp_conj]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- A fixed cutoff which equals one on the radius-two disk. -/
def diskHarmonicCutoffBump : ContDiffBump (0 : ℂ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

def diskHarmonicCutoff (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (diskHarmonicCutoffBump z : ℂ) * φ z

theorem diskHarmonicCutoff_testFunction 
    (hφ : ContDiff ℝ ∞ φ) : TestFunction univ (diskHarmonicCutoff φ) := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp diskHarmonicCutoffBump.contDiff).mul hφ, ?_,
    subset_univ _⟩
  exact (diskHarmonicCutoffBump.hasCompactSupport.comp_left
    (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right

theorem diskHarmonicCutoff_eventuallyEq  
    (hz : z ∈ ball 0 2) : diskHarmonicCutoff φ =ᶠ[𝓝 z] φ := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  simp [diskHarmonicCutoff, diskHarmonicCutoffBump.one_of_mem_closedBall (ball_subset_closedBall hw)]

theorem diskHarmonicCutoff_eq_closedDisk φ 
    (hz : z ∈ closedBall 0 1) : diskHarmonicCutoff φ z = φ z := by
  exact (diskHarmonicCutoff_eventuallyEq (closedBall_subset_ball (by norm_num) hz)).self_of_nhds

theorem fderiv_diskHarmonicCutoff_eq  
    (hz : z ∈ ball 0 2) :
    fderiv ℝ (diskHarmonicCutoff φ) z = fderiv ℝ φ z :=
  (diskHarmonicCutoff_eventuallyEq hz).fderiv_eq

theorem dirD_diskHarmonicCutoff_eq  
    (hz : z ∈ ball 0 2) v :
    dirD (diskHarmonicCutoff φ) v z = dirD φ v z := by
  unfold dirD
  rw [fderiv_diskHarmonicCutoff_eq hz]

theorem dirD_diskHarmonicCutoff_eventuallyEq  
    (hz : z ∈ ball 0 2) v :
    dirD (diskHarmonicCutoff φ) v =ᶠ[𝓝 z] dirD φ v := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact dirD_diskHarmonicCutoff_eq hw v

theorem lap_diskHarmonicCutoff_eq  
    (hz : z ∈ ball 0 2) :
    lap (diskHarmonicCutoff φ) z = lap φ z := by
  unfold lap
  change fderiv ℝ (dirD (diskHarmonicCutoff φ) 1) z 1 +
      fderiv ℝ (dirD (diskHarmonicCutoff φ) Complex.I) z Complex.I =
    fderiv ℝ (dirD φ 1) z 1 + fderiv ℝ (dirD φ Complex.I) z Complex.I
  rw [(dirD_diskHarmonicCutoff_eventuallyEq hz 1).fderiv_eq,
    (dirD_diskHarmonicCutoff_eventuallyEq hz Complex.I).fderiv_eq]

theorem integral_disk_boundary_modes m n :
    (∫ θ in 0..(2 * π), diskHolomorphicMode m (Φ0 θ) *
      diskAntiholomorphicMode n (Φ0 θ)) =
      if m = n then (2 * π : ℂ) else 0 := by
  simp_rw [show ∀ θ : ℝ, diskHolomorphicMode m (Φ0 θ) * diskAntiholomorphicMode n (Φ0 θ) = Complex.exp ((m - n) * Complex.I * θ) by
    intro θ
    rw [diskHolomorphicMode_unitCircle, diskAntiholomorphicMode_unitCircle,
      ← Complex.exp_add]
    congr 1
    ring]
  by_cases hmn : m = n
  · simp [hmn, intervalIntegral.integral_const, Complex.real_smul]
  · have hsub : (m : ℂ) - n ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hmn)
    rw [if_neg hmn, integral_exp_mul_complex (mul_ne_zero hsub Complex.I_ne_zero)]
    simp only [show Complex.exp (((m - n) * Complex.I) * (2 * π : ℝ)) = 1 by
      calc
        _ = Complex.exp ((((m - n) : ℤ) : ℂ) *
            (2 * π * Complex.I)) := by
          congr 1
          push_cast
          ring
        _ = 1 := Complex.exp_int_mul_two_pi_mul_I (m - n), Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div]

/-- Green's formula gives the actual disk gradient Gram matrix. The
integrals and the compact cutoff are physical, with ordinary area and
parameter measures. -/
local notation "Φ1" => ball 0 1

theorem integral_disk_holomorphic_antiholomorphic_gradients m n :
    (∫ z in Φ1, ∑ i : Fin 2,
      dirD (diskHolomorphicMode m) (coordDir i) z *
        dirD (diskAntiholomorphicMode n) (coordDir i) z) =
      if m = n then (2 * π : ℂ) * (n : ℂ) else 0 := by
  have hV := diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hV.2.1 hV.1 (by simp)
  calc
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      simp [lap_diskAntiholomorphicMode, dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz)]
    _ = _ := (doubleLayer_eq_integral unitDisk_bounded isLipschitzDomain_unitDisk unitCircle_isBoundaryParam hK hV.2.1 (h := fun θ => diskHolomorphicMode m (Φ0 θ)) (by
          intro θ _
          exact diskHarmonicCutoff_eq_closedDisk _
            (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ)) (contDiff_diskAntiholomorphicMode n)).symm
    _ = n *
        (∫ θ in 0..(2 * π), diskHolomorphicMode m (Φ0 θ) *
          diskAntiholomorphicMode n (Φ0 θ)) := by
      unfold doubleLayer
      simp_rw [conormal_diskAntiholomorphicMode]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      ring
    _ = _ := by
      rw [integral_disk_boundary_modes]
      split_ifs <;> ring

theorem conj_dirD_diskHolomorphicMode m v z :
    conj (dirD (diskHolomorphicMode m) v z) =
      dirD (diskAntiholomorphicMode m) v z := by
  rw [dirD_diskHolomorphicMode, dirD_diskAntiholomorphicMode]
  simp

theorem conj_dirD_diskAntiholomorphicMode m v z :
    conj (dirD (diskAntiholomorphicMode m) v z) =
      dirD (diskHolomorphicMode m) v z := by
  rw [dirD_diskAntiholomorphicMode, dirD_diskHolomorphicMode]
  simp

/-- The actual Hilbert space of the two disk-gradient components. -/
abbrev DiskGradientSpace := PiLp 2 (fun _ : Fin 2 => L2 (ball (0 : ℂ) 1))

def diskTestGradient  (hφ : TestFunction univ φ) : DiskGradientSpace :=
  WithLp.toLp 2 (fun i : Fin 2 =>
    ((hφ.dirD (coordDir i)).memLp' 2 (μ := volume.restrict (ball (0 : ℂ) 1))).toLp
      (dirD φ (coordDir i)))

theorem diskTestGradient_ae {φ : ℂ → ℂ} (hφ : TestFunction univ φ) i :
    ((diskTestGradient hφ i : L2 (Φ1)) : ℂ → ℂ) =ᵐ[
      volume.restrict (Φ1)] dirD φ (coordDir i) :=
  ((hφ.dirD (coordDir i)).memLp' 2 (μ := volume.restrict (Φ1))).coeFn_toLp

theorem inner_diskTestGradient {φ ψ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (hψ : TestFunction univ ψ) :
    ⟪diskTestGradient hφ, diskTestGradient hψ⟫_ℂ =
      ∫ z in Φ1, ∑ i : Fin 2,
        conj (dirD φ (coordDir i) z) * dirD ψ (coordDir i) z := by
  calc
    _ = ∑ i : Fin 2, ∫ z in Φ1,
        conj (dirD φ (coordDir i) z) * dirD ψ (coordDir i) z := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [diskTestGradient_ae hφ i, diskTestGradient_ae hψ i] with z hzφ hzψ
      simp only [RCLike.inner_apply', hzφ, hzψ]
    _ = _ := (integral_finset_sum Finset.univ (fun i _ =>
      ((hφ.dirD (coordDir i)).conj.memLp' 2).integrable_mul
        ((hψ.dirD (coordDir i)).memLp' 2))).symm

def diskHolomorphicGradient (m : ℕ) : DiskGradientSpace :=
  diskTestGradient (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m))

def diskAntiholomorphicGradient (m : ℕ) : DiskGradientSpace :=
  diskTestGradient (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m))

theorem diskHolomorphicGradient_ae m i :
    ((diskHolomorphicGradient m i : L2 (Φ1)) : ℂ → ℂ) =ᵐ[
      volume.restrict (Φ1)] dirD (diskHolomorphicMode m) (coordDir i) := by
  filter_upwards [diskTestGradient_ae
    (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)) i,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskTestGradient
    (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)) i) z = _
  rw [hz, dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hzD)]

theorem diskAntiholomorphicGradient_ae m i :
    ((diskAntiholomorphicGradient m i : L2 (Φ1)) : ℂ → ℂ) =ᵐ[
      volume.restrict (Φ1)] dirD (diskAntiholomorphicMode m) (coordDir i) := by
  filter_upwards [diskTestGradient_ae
    (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)) i,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskTestGradient
    (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)) i) z = _
  rw [hz, dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hzD)]

theorem inner_diskHolomorphicGradient m n :
    ⟪diskHolomorphicGradient m, diskHolomorphicGradient n⟫_ℂ =
      if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := by
  change ⟪diskTestGradient _, diskTestGradient _⟫_ℂ = _
  rw [inner_diskTestGradient]
  calc
    _ = ∫ z in Φ1, ∑ i : Fin 2,
        dirD (diskHolomorphicMode n) (coordDir i) z *
          dirD (diskAntiholomorphicMode m) (coordDir i) z := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      simp only [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz), conj_dirD_diskHolomorphicMode]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [integral_disk_holomorphic_antiholomorphic_gradients]
      simp [eq_comm]

theorem inner_diskAntiholomorphicGradient m n :
    ⟪diskAntiholomorphicGradient m, diskAntiholomorphicGradient n⟫_ℂ =
      if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := by
  change ⟪diskTestGradient _, diskTestGradient _⟫_ℂ = _
  rw [inner_diskTestGradient]
  calc
    _ = ∫ z in Φ1, ∑ i : Fin 2,
        dirD (diskHolomorphicMode m) (coordDir i) z *
          dirD (diskAntiholomorphicMode n) (coordDir i) z := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      simp [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz), conj_dirD_diskAntiholomorphicMode]
    _ = _ := by
      rw [integral_disk_holomorphic_antiholomorphic_gradients]
      split_ifs with hmn
      · rw [hmn]
      · rfl

theorem inner_diskHolomorphicGradient_antiholomorphicGradient m n :
    ⟪diskHolomorphicGradient m, diskAntiholomorphicGradient n⟫_ℂ = 0 := by
  change ⟪diskTestGradient _, diskTestGradient _⟫_ℂ = _
  rw [inner_diskTestGradient]
  calc
    _ = ∫ _z in ball (0 : ℂ) 1, (0 : ℂ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      simp only [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz), conj_dirD_diskHolomorphicMode]
      exact (by
        simp [show coordDir 0 = 1 from rfl, show coordDir 1 = Complex.I from rfl, dirD_diskAntiholomorphicMode]
        calc
          _ = m * conj z ^ (m - 1) * (n * conj z ^ (n - 1)) *
              (1 + Complex.I ^ 2) := by ring
          _ = 0 := by rw [Complex.I_sq]; ring)
    _ = 0 := by simp

theorem inner_diskAntiholomorphicGradient_holomorphicGradient m n :
    ⟪diskAntiholomorphicGradient m, diskHolomorphicGradient n⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_diskHolomorphicGradient_antiholomorphicGradient]
  simp

def diskHarmonicGradientScale (m : ℕ) : ℂ :=
  ((Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ)))⁻¹ : ℝ)

private lemma diskHarmonicGradientScale_normalizes m :
    conj (diskHarmonicGradientScale m) *
      (diskHarmonicGradientScale m * ((2 * π : ℂ) * ((m + 1 : ℕ) : ℂ))) = 1 := by
  have hp : 0 < 2 * π * (m + 1 : ℕ) := by positivity
  simp [diskHarmonicGradientScale]
  exact_mod_cast (by
    field_simp [Real.sqrt_ne_zero'.mpr hp]
    nlinarith [Real.sq_sqrt hp.le])

/-- Nonzero harmonic modes, normalized in the actual two-component
gradient Hilbert space. The left/right sectors have frequencies
`m+1` and `-(m+1)`, respectively; the zero mode is deliberately absent. -/
def diskNormalizedHarmonicGradient : ℕ ⊕ ℕ → DiskGradientSpace
  | Sum.inl m => diskHarmonicGradientScale m • diskHolomorphicGradient (m + 1)
  | Sum.inr m => diskHarmonicGradientScale m • diskAntiholomorphicGradient (m + 1)

theorem orthonormal_diskNormalizedHarmonicGradient :
    Orthonormal ℂ diskNormalizedHarmonicGradient := by
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl m =>
      cases j with
      | inl n =>
          by_cases hmn : m = n
          · subst n
            simp only [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right,
              inner_diskHolomorphicGradient, ite_true]
            calc
              _ = conj (diskHarmonicGradientScale m) *
                  (diskHarmonicGradientScale m * ((2 * π) * (m + 1 : ℕ))) := by
                    ring
              _ = 1 := diskHarmonicGradientScale_normalizes m
          · simp [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right,
              inner_diskHolomorphicGradient, hmn]
      | inr n =>
          simp [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right,
            inner_diskHolomorphicGradient_antiholomorphicGradient]
  | inr m =>
      cases j with
      | inl n =>
          simp [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right,
            inner_diskAntiholomorphicGradient_holomorphicGradient]
      | inr n =>
          by_cases hmn : m = n
          · subst n
            simp only [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right,
              inner_diskAntiholomorphicGradient, ite_true]
            calc
              _ = conj (diskHarmonicGradientScale m) *
                  (diskHarmonicGradientScale m * ((2 * π) * (m + 1 : ℕ))) := by
                    ring
              _ = 1 := diskHarmonicGradientScale_normalizes m
          · simp [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right,
              inner_diskAntiholomorphicGradient, hmn]

end PolyaNeumann

end
