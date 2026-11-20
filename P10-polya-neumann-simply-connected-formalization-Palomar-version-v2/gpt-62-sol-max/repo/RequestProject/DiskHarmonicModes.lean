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

section

variable (m : ℕ)
include m

def diskHolomorphicMode  (z : ℂ) : ℂ := z ^ m

def diskAntiholomorphicMode  (z : ℂ) : ℂ := conj z ^ m

theorem contDiff_diskHolomorphicMode  :
    ContDiff ℝ (⊤ : ℕ∞) (diskHolomorphicMode m) :=
  contDiff_id.pow m

theorem contDiff_diskAntiholomorphicMode  :
    ContDiff ℝ (⊤ : ℕ∞) (diskAntiholomorphicMode m) :=
  Complex.conjCLE.contDiff.pow m

theorem fderiv_diskHolomorphicMode  (z v : ℂ) :
    fderiv ℝ (diskHolomorphicMode m) z v = (m : ℂ) * z ^ (m - 1) * v := by
  change fderiv ℝ (fun w : ℂ => w ^ m) z v = _
  rw [(hasFDerivAt_pow (𝕜 := ℝ) (x := z) m).fderiv]
  simp

theorem fderiv_diskAntiholomorphicMode  (z v : ℂ) :
    fderiv ℝ (diskAntiholomorphicMode m) z v =
      (m : ℂ) * conj z ^ (m - 1) * conj v := by
  change fderiv ℝ (fun w : ℂ => conj w ^ m) z v = _
  have h := congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
    ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z)).pow m).fderiv
  simp_all

theorem dirD_diskHolomorphicMode  (v z : ℂ) :
    dirD (diskHolomorphicMode m) v z = (m : ℂ) * z ^ (m - 1) * v :=
  fderiv_diskHolomorphicMode m z v

theorem dirD_diskAntiholomorphicMode  (v z : ℂ) :
    dirD (diskAntiholomorphicMode m) v z =
      (m : ℂ) * conj z ^ (m - 1) * conj v :=
  fderiv_diskAntiholomorphicMode m z v

end

private lemma disk_dirD_const_mul (a : ℂ) {φ : ℂ → ℂ} {z : ℂ}
    (hφ : DifferentiableAt ℝ φ z) (v : ℂ) :
    dirD (fun w => a * φ w) v z = a * dirD φ v z := by
  unfold dirD
  rw [fderiv_const_mul hφ a]
  rfl

theorem lap_diskHolomorphicMode (m : ℕ) (z : ℂ) :
    lap (diskHolomorphicMode m) z = 0 := by
  have h1 : dirD (diskHolomorphicMode m) 1 =
      fun w => (m : ℂ) * diskHolomorphicMode (m - 1) w := by
    grind [dirD_diskHolomorphicMode, mul_one, diskHolomorphicMode]
  have hI : dirD (diskHolomorphicMode m) Complex.I =
      fun w => ((m : ℂ) * Complex.I) * diskHolomorphicMode (m - 1) w := by
    grind [dirD_diskHolomorphicMode, diskHolomorphicMode]
  have hd :=
    (contDiff_diskHolomorphicMode (m - 1)).differentiable (by simp) z
  rw [lap, h1, hI, disk_dirD_const_mul _ hd 1, disk_dirD_const_mul _ hd Complex.I]
  grind [dirD_diskHolomorphicMode, mul_one, Complex.I_sq]

theorem lap_diskAntiholomorphicMode (m : ℕ) (z : ℂ) :
    lap (diskAntiholomorphicMode m) z = 0 := by
  have hs := contDiff_diskHolomorphicMode m
  have hmode : diskAntiholomorphicMode m = fun w => conj (diskHolomorphicMode m w) :=
    funext fun _ => (map_pow _ _ _).symm
  have hd (v : ℂ) : dirD (diskAntiholomorphicMode m) v = fun w => conj (dirD (diskHolomorphicMode m) v w) := by
    rw [hmode]
    exact funext (dirD_conj (hs.of_le (by simp)) v)
  unfold lap
  rw [hd, hd, dirD_conj ((dirD_contDiff hs 1).of_le (by simp)),
    dirD_conj ((dirD_contDiff hs Complex.I).of_le (by simp)), ← map_add]
  exact congrArg conj (lap_diskHolomorphicMode m z) |>.trans (map_zero _)

theorem unitCircle_conormalDirection (θ : ℝ) :
    -(Complex.I * deriv (circleMap 0 1) θ) = circleMap 0 1 θ := by grind [deriv_circleMap, Complex.I_mul_I]

section

variable (m : ℕ) (θ : ℝ)
include m θ

theorem conormal_diskHolomorphicMode  :
    fderiv ℝ (diskHolomorphicMode m) (circleMap 0 1 θ)
      (-(Complex.I * deriv (circleMap 0 1) θ)) =
      (m : ℂ) * diskHolomorphicMode m (circleMap 0 1 θ) := by
  rw [unitCircle_conormalDirection, fderiv_diskHolomorphicMode]
  unfold diskHolomorphicMode
  cases m with
  | zero => simp
  | succ m => grind

theorem conormal_diskAntiholomorphicMode  :
    fderiv ℝ (diskAntiholomorphicMode m) (circleMap 0 1 θ)
      (-(Complex.I * deriv (circleMap 0 1) θ)) =
      (m : ℂ) * diskAntiholomorphicMode m (circleMap 0 1 θ) := by
  rw [unitCircle_conormalDirection, fderiv_diskAntiholomorphicMode]
  unfold diskAntiholomorphicMode
  cases m with
  | zero => simp
  | succ m => grind

theorem diskHolomorphicMode_unitCircle  :
    diskHolomorphicMode m (circleMap 0 1 θ) =
      Complex.exp ((m : ℂ) * Complex.I * θ) := by
  simp  [diskHolomorphicMode, circleMap, Complex.ofReal_one, one_mul, zero_add]
  rw [← Complex.exp_nat_mul]
  ring

theorem diskAntiholomorphicMode_unitCircle  :
    diskAntiholomorphicMode m (circleMap 0 1 θ) =
      Complex.exp (-((m : ℂ) * Complex.I * θ)) := by
  simp only [diskAntiholomorphicMode, circleMap, Complex.ofReal_one, one_mul, zero_add,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_nat_mul]
  ring

end

theorem disk_antiholomorphic_gradient_bilinear_zero (m n : ℕ) (z : ℂ) :
    (∑ i : Fin 2, dirD (diskAntiholomorphicMode m) (coordDir i) z *
      dirD (diskAntiholomorphicMode n) (coordDir i) z) = 0 := by
  simp only [Fin.sum_univ_two, show coordDir 0 = (1 : ℂ) from rfl,
    show coordDir 1 = Complex.I from rfl, dirD_diskAntiholomorphicMode,
    map_one, mul_one, Complex.conj_I]
  grind [Complex.I_sq]

/-- A fixed cutoff which equals one on the radius-two disk. -/
def diskHarmonicCutoffBump : ContDiffBump (0 : ℂ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

def diskHarmonicCutoff (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (diskHarmonicCutoffBump z : ℂ) * φ z

section

variable {φ : ℂ → ℂ}
include φ

theorem diskHarmonicCutoff_testFunction 
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : TestFunction univ (diskHarmonicCutoff φ) := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp diskHarmonicCutoffBump.contDiff).mul hφ, ?_,
    subset_univ _⟩
  exact (diskHarmonicCutoffBump.hasCompactSupport.comp_left
    (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right

theorem diskHarmonicCutoff_eventuallyEq  {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 2) : diskHarmonicCutoff φ =ᶠ[𝓝 z] φ := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  simp  [diskHarmonicCutoff,
    diskHarmonicCutoffBump.one_of_mem_closedBall (ball_subset_closedBall hw),
    Complex.ofReal_one, one_mul]

end

theorem diskHarmonicCutoff_eq_closedDisk (φ : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) : diskHarmonicCutoff φ z = φ z := by
  have hz' : z ∈ ball (0 : ℂ) 2 := closedBall_subset_ball (by norm_num) hz
  exact (diskHarmonicCutoff_eventuallyEq hz').self_of_nhds

section

variable {φ : ℂ → ℂ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) 2)
include φ z hz

theorem fderiv_diskHarmonicCutoff_eq  :
    fderiv ℝ (diskHarmonicCutoff φ) z = fderiv ℝ φ z :=
  (diskHarmonicCutoff_eventuallyEq hz).fderiv_eq

theorem dirD_diskHarmonicCutoff_eq  (v : ℂ) :
    dirD (diskHarmonicCutoff φ) v z = dirD φ v z := by
  unfold dirD
  rw [fderiv_diskHarmonicCutoff_eq hz]

theorem lap_diskHarmonicCutoff_eq :
    lap (diskHarmonicCutoff φ) z = lap φ z := by
  have hd (v : ℂ) : dirD (diskHarmonicCutoff φ) v =ᶠ[𝓝 z] dirD φ v :=
    ((diskHarmonicCutoff_eventuallyEq hz).fderiv (𝕜 := ℝ)).fun_comp (fun L => L v)
  have hdd (v : ℂ) : dirD (dirD (diskHarmonicCutoff φ) v) v z = dirD (dirD φ v) v z :=
    congrArg (fun L : ℂ →L[ℝ] ℂ => L v) (hd v).fderiv_eq
  simp only [lap, hdd]

end

theorem integral_disk_boundary_modes (m n : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * π), diskHolomorphicMode m (circleMap 0 1 θ) *
      diskAntiholomorphicMode n (circleMap 0 1 θ)) =
      if m = n then (2 * π : ℂ) else 0 := by
  have hprod : ∀ θ : ℝ,
      diskHolomorphicMode m (circleMap 0 1 θ) *
        diskAntiholomorphicMode n (circleMap 0 1 θ) =
        Complex.exp (((m : ℂ) - (n : ℂ)) * Complex.I * θ) := by
    intro θ
    rw [diskHolomorphicMode_unitCircle, diskAntiholomorphicMode_unitCircle,
      ← Complex.exp_add]
    ring
  simp_rw [hprod]
  by_cases hmn : m = n
  simp_all
  · have hsub : (m : ℂ) - (n : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (by norm_cast)
    have hc :=
      mul_ne_zero hsub Complex.I_ne_zero
    have he : Complex.exp ((((m : ℂ) - (n : ℂ)) * Complex.I) * (2 * π : ℝ)) = 1 := by
      calc
        _ = Complex.exp (((((m : ℤ) - (n : ℤ)) : ℤ) : ℂ) *
            (2 * π * Complex.I)) := by
          congr 1
          push_cast
          ring
        _ = 1 := Complex.exp_int_mul_two_pi_mul_I ((m : ℤ) - (n : ℤ))
    rw [if_neg hmn, integral_exp_mul_complex hc]
    simp_all

/-- Green's formula gives the actual disk gradient Gram matrix. The
integrals and the compact cutoff are physical, with ordinary area and
parameter measures. -/
theorem integral_disk_holomorphic_antiholomorphic_gradients (m n : ℕ) :
    (∫ z in ball (0 : ℂ) 1, ∑ i : Fin 2,
      dirD (diskHolomorphicMode m) (coordDir i) z *
        dirD (diskAntiholomorphicMode n) (coordDir i) z) =
      if m = n then (2 * π : ℂ) * (n : ℂ) else 0 := by
  have hV := diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hV.2.1 hV.1 (by simp)
  have htrace : ∀ θ ∈ Icc (0 : ℝ) (2 * π),
      diskHarmonicCutoff (diskHolomorphicMode m) (circleMap 0 1 θ) =
        diskHolomorphicMode m (circleMap 0 1 θ) := by
    intro θ _
    exact diskHarmonicCutoff_eq_closedDisk _
      (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ)
  have hgreen := doubleLayer_eq_integral unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam hK hV.2.1
    (h := fun θ => diskHolomorphicMode m (circleMap 0 1 θ)) htrace
    (contDiff_diskAntiholomorphicMode n)
  calc
    _ = ∫ z in ball (0 : ℂ) 1,
        (diskHarmonicCutoff (diskHolomorphicMode m) z *
          lap (diskAntiholomorphicMode n) z +
          ∑ i : Fin 2, dirD (diskHarmonicCutoff (diskHolomorphicMode m)) (coordDir i) z *
            dirD (diskAntiholomorphicMode n) (coordDir i) z) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      have hz' : z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by norm_num) hz
      simp  [lap_diskAntiholomorphicMode, zero_add,
        dirD_diskHarmonicCutoff_eq hz']
    _ = doubleLayer (circleMap 0 1)
        (fun θ => diskHolomorphicMode m (circleMap 0 1 θ))
        (diskAntiholomorphicMode n) := hgreen.symm
    _ = (n : ℂ) *
        (∫ θ in (0 : ℝ)..(2 * π), diskHolomorphicMode m (circleMap 0 1 θ) *
          diskAntiholomorphicMode n (circleMap 0 1 θ)) := by grind [doubleLayer, conormal_diskAntiholomorphicMode, intervalIntegral.integral_const_mul]
    _ = if m = n then (2 * π : ℂ) * (n : ℂ) else 0 := by
      rw [integral_disk_boundary_modes]
      grind

section

variable (m : ℕ) (v z : ℂ)
include m v z

theorem conj_dirD_diskHolomorphicMode  :
    conj (dirD (diskHolomorphicMode m) v z) =
      dirD (diskAntiholomorphicMode m) v z := by simp_all [dirD_diskHolomorphicMode, dirD_diskAntiholomorphicMode]

theorem conj_dirD_diskAntiholomorphicMode  :
    conj (dirD (diskAntiholomorphicMode m) v z) =
      dirD (diskHolomorphicMode m) v z := by simp_all [dirD_diskAntiholomorphicMode, dirD_diskHolomorphicMode]

end

/-- The actual Hilbert space of the two disk-gradient components. -/
abbrev DiskGradientSpace := PiLp 2 (fun _ : Fin 2 => L2 (ball (0 : ℂ) 1))

def diskHarmonicGradient {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : DiskGradientSpace :=
  WithLp.toLp 2 (fun i => (((diskHarmonicCutoff_testFunction hφ).dirD (coordDir i)).memLp' 2).toLp _)

private lemma diskHarmonicGradient_ae {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin 2) :
    (fun z => diskHarmonicGradient hφ i z) =ᵐ[volume.restrict (ball (0 : ℂ) 1)] dirD φ (coordDir i) := by
  filter_upwards [((diskHarmonicCutoff_testFunction hφ).dirD (coordDir i)).memLp' 2 |>.coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  exact hz.trans (dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hzD) _)

private theorem inner_diskHarmonicGradient {φ ψ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ⟪diskHarmonicGradient hφ, diskHarmonicGradient hψ⟫_ℂ =
      ∫ z in ball (0 : ℂ) 1, ∑ i : Fin 2,
        conj (dirD φ (coordDir i) z) * dirD ψ (coordDir i) z := by
  have he (i : Fin 2) : (fun z => ⟪diskHarmonicGradient hφ i z, diskHarmonicGradient hψ i z⟫_ℂ) =ᵐ[
        volume.restrict (ball (0 : ℂ) 1)] fun z => conj (dirD φ (coordDir i) z) * dirD ψ (coordDir i) z := by
    filter_upwards [diskHarmonicGradient_ae hφ i, diskHarmonicGradient_ae hψ i] with z h1 h2
    simp [RCLike.inner_apply', h1, h2, mul_comm]
  rw [PiLp.inner_apply, integral_finset_sum Finset.univ fun i _ =>
    (L2.integrable_inner _ _).congr (he i)]
  exact Finset.sum_congr rfl fun i _ => (L2.inner_def _ _).trans (integral_congr_ae (he i))

def diskHolomorphicGradient (m : ℕ) : DiskGradientSpace :=
  diskHarmonicGradient (contDiff_diskHolomorphicMode m)

def diskAntiholomorphicGradient (m : ℕ) : DiskGradientSpace :=
  diskHarmonicGradient (contDiff_diskAntiholomorphicMode m)

theorem diskHolomorphicGradient_ae (m : ℕ) (i : Fin 2) :
    ((diskHolomorphicGradient m i : L2 (ball (0 : ℂ) 1)) : ℂ → ℂ) =ᵐ[
      volume.restrict (ball (0 : ℂ) 1)] dirD (diskHolomorphicMode m) (coordDir i) :=
  diskHarmonicGradient_ae _ i

theorem diskAntiholomorphicGradient_ae (m : ℕ) (i : Fin 2) :
    ((diskAntiholomorphicGradient m i : L2 (ball (0 : ℂ) 1)) : ℂ → ℂ) =ᵐ[
      volume.restrict (ball (0 : ℂ) 1)] dirD (diskAntiholomorphicMode m) (coordDir i) :=
  diskHarmonicGradient_ae _ i

section

variable (m n : ℕ)
include m n

theorem inner_diskHolomorphicGradient :
    ⟪diskHolomorphicGradient m, diskHolomorphicGradient n⟫_ℂ =
      if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := by
  rw [diskHolomorphicGradient, diskHolomorphicGradient, inner_diskHarmonicGradient]
  simp_rw [conj_dirD_diskHolomorphicMode m, mul_comm (dirD (diskAntiholomorphicMode m) _ _)]
  rw [integral_disk_holomorphic_antiholomorphic_gradients]
  by_cases h : m = n <;> simp_all [eq_comm]

theorem inner_diskAntiholomorphicGradient :
    ⟪diskAntiholomorphicGradient m, diskAntiholomorphicGradient n⟫_ℂ =
      if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := by
  rw [diskAntiholomorphicGradient, diskAntiholomorphicGradient, inner_diskHarmonicGradient]
  simp_rw [conj_dirD_diskAntiholomorphicMode m, integral_disk_holomorphic_antiholomorphic_gradients]
  split_ifs <;> simp_all

private theorem inner_diskHolomorphicGradient_antiholomorphicGradient :
    ⟪diskHolomorphicGradient m, diskAntiholomorphicGradient n⟫_ℂ = 0 := by
  rw [diskHolomorphicGradient, diskAntiholomorphicGradient, inner_diskHarmonicGradient]
  simp only [conj_dirD_diskHolomorphicMode, disk_antiholomorphic_gradient_bilinear_zero, integral_zero]

private theorem inner_diskAntiholomorphicGradient_holomorphicGradient :
    ⟪diskAntiholomorphicGradient m, diskHolomorphicGradient n⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_diskHolomorphicGradient_antiholomorphicGradient, map_zero]

end

def diskHarmonicGradientScale (m : ℕ) : ℂ :=
  ((Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ)))⁻¹ : ℝ)

private lemma diskHarmonicGradientScale_normalizes (m : ℕ) :
    conj (diskHarmonicGradientScale m) *
      (diskHarmonicGradientScale m * ((2 * π : ℂ) * ((m + 1 : ℕ) : ℂ))) = 1 := by
  have hp : 0 < 2 * π * ((m + 1 : ℕ) : ℝ) := by positivity
  have hs :=
    Real.sqrt_ne_zero'.mpr hp
  have hsq := Real.sq_sqrt hp.le
  have hr : (Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ)))⁻¹ *
      ((Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ)))⁻¹ *
        (2 * π * ((m + 1 : ℕ) : ℝ))) = 1 := by
    field_simp [hs]
    gcongr
  simp only [diskHarmonicGradientScale, Complex.conj_ofReal]
  norm_cast

/-- Nonzero harmonic modes, normalized in the actual two-component
gradient Hilbert space. The left/right sectors have frequencies
`m+1` and `-(m+1)`, respectively; the zero mode is deliberately absent. -/
def diskNormalizedHarmonicGradient : ℕ ⊕ ℕ → DiskGradientSpace
  | Sum.inl m => diskHarmonicGradientScale m • diskHolomorphicGradient (m + 1)
  | Sum.inr m => diskHarmonicGradientScale m • diskAntiholomorphicGradient (m + 1)

theorem orthonormal_diskNormalizedHarmonicGradient :
    Orthonormal ℂ diskNormalizedHarmonicGradient := by
  rw [orthonormal_iff_ite]
  rintro (m | m) (n | n) <;>
    simp only [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right,
      inner_diskHolomorphicGradient, inner_diskAntiholomorphicGradient,
      inner_diskHolomorphicGradient_antiholomorphicGradient,
      inner_diskAntiholomorphicGradient_holomorphicGradient, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, ite_false, mul_zero, Nat.add_right_cancel_iff] <;>
    split_ifs with h <;> simp_all only [mul_zero]
  all_goals
    simpa only [mul_comm, mul_left_comm, mul_assoc] using diskHarmonicGradientScale_normalizes n

end PolyaNeumann

end
