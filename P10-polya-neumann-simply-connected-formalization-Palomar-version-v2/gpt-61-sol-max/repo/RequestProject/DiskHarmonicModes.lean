module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

def diskHolomorphicMode m (z : ℂ)  := z ^ m

def diskAntiholomorphicMode m (z : ℂ)  := conj z ^ m

section
variable (m : ℕ)
include m

theorem contDiff_diskHolomorphicMode :
    RealSmooth (diskHolomorphicMode m) :=
  contDiff_id.pow m

theorem contDiff_diskAntiholomorphicMode :
    RealSmooth (diskAntiholomorphicMode m) :=
  Complex.conjCLE.contDiff.pow m

theorem fderiv_diskHolomorphicMode z v :
    fderiv ℝ (diskHolomorphicMode m) z v = (m : ℂ) * z ^ (m - 1) * v := by
  change fderiv ℝ (fun w : ℂ => w ^ m) z v = _
  rw [(hasFDerivAt_pow (𝕜 := ℝ) (x := z) m).fderiv]
  simp_all

theorem fderiv_diskAntiholomorphicMode z v :
    fderiv ℝ (diskAntiholomorphicMode m) z v =
      (m : ℂ) * conj z ^ (m - 1) * conj v := by
  change fderiv ℝ (fun w : ℂ => conj w ^ m) z v = _
  have h := congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
    ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z)).pow m).fderiv
  simp_all

theorem dirD_diskHolomorphicMode v z :
    dirD (diskHolomorphicMode m) v z = (m : ℂ) * z ^ (m - 1) * v :=
  fderiv_diskHolomorphicMode m z v

theorem dirD_diskAntiholomorphicMode v z :
    dirD (diskAntiholomorphicMode m) v z =
      (m : ℂ) * conj z ^ (m - 1) * conj v :=
  fderiv_diskAntiholomorphicMode m z v

end


private lemma disk_dirD_const_mul a  
    (hφ : DifferentiableAt ℝ φ z) v :
    dirD (fun w => a * φ w) v z = a * dirD φ v z := by
  unfold dirD
  rw [fderiv_const_mul hφ a]
  norm_num

theorem lap_diskHolomorphicMode m z :
    lap (diskHolomorphicMode m) z = 0 := by
  have h1 : dirD (diskHolomorphicMode m) 1 =
      fun w => (m : ℂ) * diskHolomorphicMode (m - 1) w := by
    grind only [dirD_diskHolomorphicMode, diskHolomorphicMode]
  have hI : dirD (diskHolomorphicMode m) Complex.I =
      fun w => ((m : ℂ) * Complex.I) * diskHolomorphicMode (m - 1) w := by
    grind only [dirD_diskHolomorphicMode, diskHolomorphicMode]
  have hd  :=
    (contDiff_diskHolomorphicMode (m - 1)).differentiable (by simp) z
  rw [lap, h1, hI, disk_dirD_const_mul _ hd 1, disk_dirD_const_mul _ hd Complex.I]
  simp  [dirD_diskHolomorphicMode]
  calc
    _ = (m * (m - 1 : ℕ) * z ^ ((m - 1) - 1)) *
        (1 + Complex.I ^ 2) := by ring
    _ = 0 := by rw [Complex.I_sq]; ring

theorem lap_diskAntiholomorphicMode m z :
    lap (diskAntiholomorphicMode m) z = 0 := by
  have h1 : dirD (diskAntiholomorphicMode m) 1 =
      fun w => (m : ℂ) * diskAntiholomorphicMode (m - 1) w := by
    ext <;> simp_all [dirD_diskAntiholomorphicMode, diskAntiholomorphicMode]
  have hI : dirD (diskAntiholomorphicMode m) Complex.I =
      fun w => ((m : ℂ) * (-Complex.I)) * diskAntiholomorphicMode (m - 1) w := by
    funext w
    simp  [dirD_diskAntiholomorphicMode, diskAntiholomorphicMode]
    ring
  have hd  :=
    (contDiff_diskAntiholomorphicMode (m - 1)).differentiable (by simp) z
  rw [lap, h1, hI, disk_dirD_const_mul _ hd 1, disk_dirD_const_mul _ hd Complex.I]
  simp  [dirD_diskAntiholomorphicMode]
  calc
    _ = (m * (m - 1 : ℕ) * conj z ^ ((m - 1) - 1)) *
        (1 + Complex.I ^ 2) := by ring
    _ = 0 := by rw [Complex.I_sq]; ring

theorem unitCircle_conormalDirection θ :
    -(Complex.I * deriv unitCircleMap θ) = unitCircleMap θ := by
  rw [deriv_circleMap]
  calc
    _ = -(Complex.I * Complex.I) * unitCircleMap θ := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

section
variable (m : ℕ) (θ : ℝ)
include m θ

theorem conormal_diskHolomorphicMode :
    fderiv ℝ (diskHolomorphicMode m) (unitCircleMap θ)
      (-(Complex.I * deriv unitCircleMap θ)) =
      (m : ℂ) * diskHolomorphicMode m (unitCircleMap θ) := by
  rw [unitCircle_conormalDirection, fderiv_diskHolomorphicMode]
  unfold diskHolomorphicMode
  cases m with
  | zero => simp
  | succ m => grind

theorem conormal_diskAntiholomorphicMode :
    fderiv ℝ (diskAntiholomorphicMode m) (unitCircleMap θ)
      (-(Complex.I * deriv unitCircleMap θ)) =
      (m : ℂ) * diskAntiholomorphicMode m (unitCircleMap θ) := by
  rw [unitCircle_conormalDirection, fderiv_diskAntiholomorphicMode]
  unfold diskAntiholomorphicMode
  cases m with
  | zero => simp
  | succ m => grind

theorem diskHolomorphicMode_unitCircle :
    diskHolomorphicMode m (unitCircleMap θ) =
      Complex.exp ((m : ℂ) * Complex.I * θ) := by
  simp  [diskHolomorphicMode, circleMap]
  rw [← Complex.exp_nat_mul]
  ring

theorem diskAntiholomorphicMode_unitCircle :
    diskAntiholomorphicMode m (unitCircleMap θ) =
      Complex.exp (-((m : ℂ) * Complex.I * θ)) := by
  simp  [diskAntiholomorphicMode, circleMap, ← Complex.exp_conj]
  rw [← Complex.exp_nat_mul]
  ring

end


theorem disk_antiholomorphic_gradient_bilinear_zero m n z :
    (∑ i : Coord, dirD (diskAntiholomorphicMode m) (coordDir i) z *
      dirD (diskAntiholomorphicMode n) (coordDir i) z) = 0 := by
  simp  [show coordDir 0 = (1 : ℂ) from rfl, show coordDir 1 = Complex.I from rfl, dirD_diskAntiholomorphicMode]
  calc
    _ = (m * conj z ^ (m - 1) * (n * conj z ^ (n - 1))) *
        (1 + Complex.I ^ 2) := by ring
    _ = 0 := by rw [Complex.I_sq]; ring

/-- A fixed cutoff which equals one on the radius-two disk. -/
def diskHarmonicCutoffBump : ContDiffBump (0 : ℂ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

def diskHarmonicCutoff (φ : PlaneMap) z  :=
  (diskHarmonicCutoffBump z : ℂ) * φ z

theorem diskHarmonicCutoff_testFunction 
    (hφ : RealSmooth φ) : TestFunction univ (diskHarmonicCutoff φ) := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp diskHarmonicCutoffBump.contDiff).mul hφ, ?_,
    subset_univ _⟩
  exact (diskHarmonicCutoffBump.hasCompactSupport.comp_left
    (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right

section
variable {φ : PlaneMap} {z } (hz : z ∈ ball (0 : ℂ) 2)

include φ z hz in
theorem diskHarmonicCutoff_eventuallyEq : diskHarmonicCutoff φ =ᶠ[𝓝 z] φ := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  simp  [diskHarmonicCutoff, diskHarmonicCutoffBump.one_of_mem_closedBall (ball_subset_closedBall hw)]

theorem diskHarmonicCutoff_eq_closedDisk φ 
    (hz : z ∈ closedUnitDisk) : diskHarmonicCutoff φ z = φ z := by
  have hz' : z ∈ ball (0 : ℂ) 2 := closedBall_subset_ball (by norm_num) hz
  exact (diskHarmonicCutoff_eventuallyEq hz').self_of_nhds

section
include φ z hz

theorem fderiv_diskHarmonicCutoff_eq :
    fderiv ℝ (diskHarmonicCutoff φ) z = fderiv ℝ φ z :=
  (diskHarmonicCutoff_eventuallyEq hz).fderiv_eq

theorem dirD_diskHarmonicCutoff_eq v :
    dirD (diskHarmonicCutoff φ) v z = dirD φ v z := by
  unfold dirD
  rw [fderiv_diskHarmonicCutoff_eq hz]

theorem dirD_diskHarmonicCutoff_eventuallyEq v :
    dirD (diskHarmonicCutoff φ) v =ᶠ[𝓝 z] dirD φ v := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact dirD_diskHarmonicCutoff_eq hw v

theorem lap_diskHarmonicCutoff_eq :
    lap (diskHarmonicCutoff φ) z = lap φ z := by
  change fderiv ℝ (dirD (diskHarmonicCutoff φ) 1) z 1 +
      fderiv ℝ (dirD (diskHarmonicCutoff φ) Complex.I) z Complex.I =
    fderiv ℝ (dirD φ 1) z 1 + fderiv ℝ (dirD φ Complex.I) z Complex.I
  rw [(dirD_diskHarmonicCutoff_eventuallyEq hz 1).fderiv_eq,
    (dirD_diskHarmonicCutoff_eventuallyEq hz Complex.I).fderiv_eq]

end


end


theorem integral_disk_boundary_modes m n :
    (∫ θ in (0 : ℝ)..circlePeriod, diskHolomorphicMode m (unitCircleMap θ) *
      diskAntiholomorphicMode n (unitCircleMap θ)) =
      if m = n then (2 * π : ℂ) else 0 := by
  have hprod : ∀ θ : ℝ,
      diskHolomorphicMode m (unitCircleMap θ) *
        diskAntiholomorphicMode n (unitCircleMap θ) =
        Complex.exp (((m : ℂ) - (n : ℂ)) * Complex.I * θ) := by
    intro θ
    rw [diskHolomorphicMode_unitCircle, diskAntiholomorphicMode_unitCircle,
      ← Complex.exp_add]
    ring
  simp_rw [hprod]
  by_cases hmn : m = n
  · simp_all
  · have hsub : (m : ℂ) - (n : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hmn)
    have hc  :=
      mul_ne_zero hsub Complex.I_ne_zero
    have he : Complex.exp ((((m : ℂ) - (n : ℂ)) * Complex.I) * (2 * π : ℝ)) = 1 := by
      calc
        _ = Complex.exp (((((m : ℤ) - (n : ℤ)) : ℤ)) *
            (2 * π * Complex.I)) := by
          push_cast
          ring
        _ = 1 := Complex.exp_int_mul_two_pi_mul_I (m - n)
    rw [if_neg hmn, integral_exp_mul_complex hc]
    simp_all

/-- Green's formula gives the actual disk gradient Gram matrix. The
integrals and the compact cutoff are physical, with ordinary area and
parameter measures. -/
theorem integral_disk_holomorphic_antiholomorphic_gradients m n :
    (∫ z in unitDisk, ∑ i : Coord,
      dirD (diskHolomorphicMode m) (coordDir i) z *
        dirD (diskAntiholomorphicMode n) (coordDir i) z) =
      if m = n then (2 * π : ℂ) * (n : ℂ) else 0 := by
  have hV := diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hV.2.1 hV.1 (by simp)
  have htrace : ∀ θ ∈ boundaryInterval,
      diskHarmonicCutoff (diskHolomorphicMode m) (unitCircleMap θ) =
        diskHolomorphicMode m (unitCircleMap θ) := by
    simp_all [diskHarmonicCutoff_eq_closedDisk]
  have hgreen := doubleLayer_eq_integral unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam hK hV.2.1
    (h := fun θ => diskHolomorphicMode m (unitCircleMap θ)) htrace
    (contDiff_diskAntiholomorphicMode n)
  calc
    _ = ∫ z in ball 0 1,
        (diskHarmonicCutoff (diskHolomorphicMode m) z *
          lap (diskAntiholomorphicMode n) z +
          ∑ i : Coord, dirD (diskHarmonicCutoff (diskHolomorphicMode m)) (coordDir i) z *
            dirD (diskAntiholomorphicMode n) (coordDir i) z) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      have hz' : z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hz
      simp_all [lap_diskAntiholomorphicMode, dirD_diskHarmonicCutoff_eq]
    _ = doubleLayer unitCircleMap
        (fun θ => diskHolomorphicMode m (unitCircleMap θ))
        (diskAntiholomorphicMode n) := hgreen.symm
    _ = n *
        (∫ θ in (0)..circlePeriod, diskHolomorphicMode m (unitCircleMap θ) *
          diskAntiholomorphicMode n (unitCircleMap θ)) := by
      unfold doubleLayer
      simp_rw [conormal_diskAntiholomorphicMode]
      rw [← intervalIntegral.integral_const_mul]
      grind
    _ = if m = n then circlePeriod * (n : ℂ) else 0 := by
      rw [integral_disk_boundary_modes]
      split_ifs <;> ring

theorem conj_dirD_diskHolomorphicMode m v z :
    conj (dirD (diskHolomorphicMode m) v z) =
      dirD (diskAntiholomorphicMode m) v z := by
  simp_all [dirD_diskHolomorphicMode, dirD_diskAntiholomorphicMode]

theorem conj_dirD_diskAntiholomorphicMode m v z :
    conj (dirD (diskAntiholomorphicMode m) v z) =
      dirD (diskHolomorphicMode m) v z := by
  simp_all [dirD_diskAntiholomorphicMode, dirD_diskHolomorphicMode]

/-- The actual Hilbert space of the two disk-gradient components. -/
abbrev DiskGradientSpace := PiLp 2 (fun _ : Coord => L2 unitDisk)

def diskTestGradient {φ } (hφ : TestFunction univ φ)  :=
  WithLp.toLp 2 (fun i : Coord =>
    ((hφ.dirD (coordDir i)).memLp' 2 (μ := volume.restrict unitDisk)).toLp
      (dirD φ (coordDir i)))

theorem diskTestGradient_ae  (hφ : TestFunction univ φ) i :
    ((diskTestGradient hφ i : L2 unitDisk) : PlaneMap) =ᵐ[
      volume.restrict unitDisk] dirD φ (coordDir i) :=
  ((hφ.dirD (coordDir i)).memLp' 2 (μ := volume.restrict unitDisk)).coeFn_toLp

theorem inner_diskTestGradient 
    (hφ : TestFunction univ φ) (hψ : TestFunction univ ψ) :
    ⟪diskTestGradient hφ, diskTestGradient hψ⟫_ℂ =
      ∫ z in unitDisk, ∑ i : Coord,
        conj (dirD φ (coordDir i) z) * dirD ψ (coordDir i) z := by
  calc
    _ = ∑ i : Coord, ∫ z in ball 0 1,
        conj (dirD φ (coordDir i) z) * dirD ψ (coordDir i) z := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [diskTestGradient_ae hφ i, diskTestGradient_ae hψ i] with z hzφ hzψ
      simp only [RCLike.inner_apply', hzφ, hzψ]
    _ = _ := (integral_finset_sum Finset.univ (fun i _ =>
      ((hφ.dirD (coordDir i)).conj.memLp' 2).integrable_mul
        ((hψ.dirD (coordDir i)).memLp' 2))).symm

def diskHolomorphicGradient m  :=
  diskTestGradient (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m))

def diskAntiholomorphicGradient m  :=
  diskTestGradient (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m))

theorem diskHolomorphicGradient_ae m i :
    ((diskHolomorphicGradient m i : L2 unitDisk) : PlaneMap) =ᵐ[
      volume.restrict unitDisk] dirD (diskHolomorphicMode m) (coordDir i) := by
  filter_upwards [diskTestGradient_ae
    (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)) i,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskTestGradient
    (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)) i) z = _
  rw [hz, dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hzD)]

theorem diskAntiholomorphicGradient_ae m i :
    ((diskAntiholomorphicGradient m i : L2 unitDisk) : PlaneMap) =ᵐ[
      volume.restrict unitDisk] dirD (diskAntiholomorphicMode m) (coordDir i) := by
  filter_upwards [diskTestGradient_ae
    (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)) i,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskTestGradient
    (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)) i) z = _
  rw [hz, dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hzD)]

section
variable (m n : ℕ)
include m n

theorem inner_diskHolomorphicGradient :
    ⟪diskHolomorphicGradient m, diskHolomorphicGradient n⟫_ℂ =
      if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := by
  change ⟪diskTestGradient _, diskTestGradient _⟫_ℂ = _
  rw [inner_diskTestGradient]
  calc
    _ = ∫ z in ball 0 1, ∑ i : Coord,
        dirD (diskHolomorphicMode n) (coordDir i) z *
          dirD (diskAntiholomorphicMode m) (coordDir i) z := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      have hz' : z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hz
      grind only [dirD_diskHarmonicCutoff_eq, conj_dirD_diskHolomorphicMode]
    _ = _ := by
      rw [integral_disk_holomorphic_antiholomorphic_gradients]
      simp  [eq_comm]

theorem inner_diskAntiholomorphicGradient :
    ⟪diskAntiholomorphicGradient m, diskAntiholomorphicGradient n⟫_ℂ =
      if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := by
  change ⟪diskTestGradient _, diskTestGradient _⟫_ℂ = _
  rw [inner_diskTestGradient]
  calc
    _ = ∫ z in ball 0 1, ∑ i : Coord,
        dirD (diskHolomorphicMode m) (coordDir i) z *
          dirD (diskAntiholomorphicMode n) (coordDir i) z := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      have hz' : z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hz
      simp_all [dirD_diskHarmonicCutoff_eq, conj_dirD_diskAntiholomorphicMode]
    _ = _ := by
      rw [integral_disk_holomorphic_antiholomorphic_gradients]
      simp_all

theorem inner_diskHolomorphicGradient_antiholomorphicGradient :
    ⟪diskHolomorphicGradient m, diskAntiholomorphicGradient n⟫_ℂ = 0 := by
  change ⟪diskTestGradient _, diskTestGradient _⟫_ℂ = _
  rw [inner_diskTestGradient]
  calc
    _ = ∫ _z in unitDisk, (0 : ℂ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      have hz' : z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hz
      simp only [dirD_diskHarmonicCutoff_eq hz', conj_dirD_diskHolomorphicMode]
      exact disk_antiholomorphic_gradient_bilinear_zero m n z
    _ = 0 := by simp

theorem inner_diskAntiholomorphicGradient_holomorphicGradient :
    ⟪diskAntiholomorphicGradient m, diskHolomorphicGradient n⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_diskHolomorphicGradient_antiholomorphicGradient]
  simp

end


def diskHarmonicGradientScale (m : ℕ) : ℂ :=
  ((Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ)))⁻¹ : ℝ)

private lemma diskHarmonicGradientScale_normalizes m :
    conj (diskHarmonicGradientScale m) *
      (diskHarmonicGradientScale m * ((2 * π : ℂ) * ((m + 1 : ℕ) : ℂ))) = 1 := by
  have hp : 0 < 2 * π * ((m + 1 : ℕ) : ℝ) := by positivity
  have hs  :=
    Real.sqrt_ne_zero'.mpr hp
  have hsq := Real.sq_sqrt hp.le
  have hr : (Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ)))⁻¹ *
      ((Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ)))⁻¹ *
        (2 * π * ((m + 1 : ℕ) : ℝ))) = 1 := by
    field_simp
    nlinarith [hsq]
  simp  [diskHarmonicGradientScale]
  exact_mod_cast hr

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
          · simp  [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right, inner_diskHolomorphicGradient]
            grind only [diskHarmonicGradientScale, diskHarmonicGradientScale_normalizes]
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
            grind only [diskHarmonicGradientScale, diskHarmonicGradientScale_normalizes]
          · simp [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right,
              inner_diskAntiholomorphicGradient, hmn]

end PolyaNeumann

end
