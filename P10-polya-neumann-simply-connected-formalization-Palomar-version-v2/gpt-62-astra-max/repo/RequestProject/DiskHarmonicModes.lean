module

public import RequestProject.CircleAnalysisNotation

public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public import RequestProject.DiskGeometry
public import RequestProject.ReconGreen
public import RequestProject.PlanarNotation

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

variable (m : ℕ) (z v : ℂ)
include m

include z in
def diskHolomorphicMode : ℂ := z ^ m

include z in
def diskAntiholomorphicMode : ℂ := conj z ^ m

theorem contDiff_diskHolomorphicMode :
    ContDiff ℝ ∞ (diskHolomorphicMode m) :=
  contDiff_id.pow m

theorem contDiff_diskAntiholomorphicMode :
    ContDiff ℝ ∞ (diskAntiholomorphicMode m) :=
  Complex.conjCLE.contDiff.pow m

theorem fderiv_diskHolomorphicMode :
    fderiv ℝ (diskHolomorphicMode m) z v = (m : ℂ) * z ^ (m - 1) * v := by
  change fderiv ℝ (fun w : ℂ => w ^ m) z v = _
  rw [(hasFDerivAt_pow  (x := z) m).fderiv]
  simp

theorem fderiv_diskAntiholomorphicMode :
    fderiv ℝ (diskAntiholomorphicMode m) z v =
      (m : ℂ) * conj z ^ (m - 1) * conj v := by
  change fderiv ℝ (fun w : ℂ => conj w ^ m) z v = _
  have h := congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
    ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z)).pow m).fderiv
  simpa using h

end

section

variable (m : ℕ) (φ : ℂ → ℂ) (v : ℂ) (θ : ℝ) (n : ℕ) (z : ℂ)

theorem dirD_diskHolomorphicMode :
    dirD (diskHolomorphicMode m) v z = (m : ℂ) * z ^ (m - 1) * v :=
  fderiv_diskHolomorphicMode m z v

theorem dirD_diskAntiholomorphicMode :
    dirD (diskAntiholomorphicMode m) v z =
      (m : ℂ) * conj z ^ (m - 1) * conj v :=
  fderiv_diskAntiholomorphicMode m z v

private lemma disk_dirD_const_mul (a : ℂ) {φ : ℂ → ℂ} {z : ℂ}
    (hφ : DifferentiableAt ℝ φ z) (v : ℂ) :
    dirD (fun w => a * φ w) v z = a * dirD φ v z := by
  unfold dirD
  rw [fderiv_const_mul hφ a]
  rfl

theorem lap_diskHolomorphicMode :
    lap (diskHolomorphicMode m) z = 0 := by
  have h1 : dirD (diskHolomorphicMode m) 1 =
      fun w => (m : ℂ) * diskHolomorphicMode (m - 1) w := by
    funext w
    simp [dirD_diskHolomorphicMode, diskHolomorphicMode]
  have hI : dirD (diskHolomorphicMode m) Complex.I =
      fun w => ((m : ℂ) * Complex.I) * diskHolomorphicMode (m - 1) w := by
    funext w
    simp only [dirD_diskHolomorphicMode, diskHolomorphicMode]
    ring
  have hd  :=
    (contDiff_diskHolomorphicMode (m - 1)).differentiable (by simp) z
  rw [lap, h1, hI, disk_dirD_const_mul _ hd 1, disk_dirD_const_mul _ hd Complex.I]
  simp [dirD_diskHolomorphicMode]
  calc
    _ = (m * (m - 1 : ℕ) * z ^ ((m - 1) - 1)) *
        (1 + Complex.I ^ 2) := by ring
    _ = 0 := by simp

theorem lap_diskAntiholomorphicMode :
    lap (diskAntiholomorphicMode m) z = 0 := by
  have h1 : dirD (diskAntiholomorphicMode m) 1 =
      fun w => (m : ℂ) * diskAntiholomorphicMode (m - 1) w := by
    funext w
    simp [dirD_diskAntiholomorphicMode, map_one, diskAntiholomorphicMode]
  have hI : dirD (diskAntiholomorphicMode m) Complex.I =
      fun w => ((m : ℂ) * (-Complex.I)) * diskAntiholomorphicMode (m - 1) w := by
    funext w
    simp only [dirD_diskAntiholomorphicMode, Complex.conj_I, diskAntiholomorphicMode]
    ring
  have hd  :=
    (contDiff_diskAntiholomorphicMode (m - 1)).differentiable (by simp) z
  rw [lap, h1, hI, disk_dirD_const_mul _ hd 1, disk_dirD_const_mul _ hd Complex.I]
  simp only [dirD_diskAntiholomorphicMode, map_one, mul_one, Complex.conj_I]
  calc
    _ = (m * (m - 1 : ℕ) * conj z ^ ((m - 1) - 1)) *
        (1 + Complex.I ^ 2) := by ring
    _ = 0 := by simp

theorem unitCircle_conormalDirection :
    -(Complex.I * deriv unitCirclePt θ) = unitCirclePt θ := by
  rw [deriv_circleMap]
  calc
    _ = -(Complex.I * Complex.I) * unitCirclePt θ := by ring
    _ = _ := by simp

theorem conormal_diskHolomorphicMode :
    fderiv ℝ (diskHolomorphicMode m) (unitCirclePt θ)
      (-(Complex.I * deriv unitCirclePt θ)) =
      (m : ℂ) * diskHolomorphicMode m (unitCirclePt θ) := by
  rw [unitCircle_conormalDirection, fderiv_diskHolomorphicMode]
  unfold diskHolomorphicMode
  cases m with
  | zero => simp
  | succ m => grind

theorem conormal_diskAntiholomorphicMode :
    fderiv ℝ (diskAntiholomorphicMode m) (unitCirclePt θ)
      (-(Complex.I * deriv unitCirclePt θ)) =
      (m : ℂ) * diskAntiholomorphicMode m (unitCirclePt θ) := by
  rw [unitCircle_conormalDirection, fderiv_diskAntiholomorphicMode]
  unfold diskAntiholomorphicMode
  cases m with
  | zero => simp
  | succ m => grind

theorem diskHolomorphicMode_unitCircle :
    diskHolomorphicMode m (unitCirclePt θ) =
      Complex.exp ((m : ℂ) * Complex.I * θ) := by
  simp [diskHolomorphicMode, circleMap, Complex.ofReal_one]
  rw [← Complex.exp_nat_mul]
  ring

theorem diskAntiholomorphicMode_unitCircle :
    diskAntiholomorphicMode m (unitCirclePt θ) =
      Complex.exp (-((m : ℂ) * Complex.I * θ)) := by
  simp only [diskAntiholomorphicMode, circleMap, Complex.ofReal_one, one_mul, zero_add,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_nat_mul]
  ring

theorem disk_antiholomorphic_gradient_bilinear_zero :
    (∑ i : Fin 2, dirD (diskAntiholomorphicMode m) (coordDir i) z *
      dirD (diskAntiholomorphicMode n) (coordDir i) z) = 0 := by
  simp only [Fin.sum_univ_two, show coordDir 0 = (1 : ℂ) from rfl,
    show coordDir 1 = Complex.I from rfl, dirD_diskAntiholomorphicMode,
    map_one, mul_one, Complex.conj_I]
  calc
    _ = (m * conj z ^ (m - 1) * (n * conj z ^ (n - 1))) *
        (1 + Complex.I ^ 2) := by ring
    _ = 0 := by simp

/-- A fixed cutoff which equals one on the radius-two disk. -/
def diskHarmonicCutoffBump : ContDiffBump (0 : ℂ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

include z φ in
def diskHarmonicCutoff : ℂ :=
  (diskHarmonicCutoffBump z : ℂ) * φ z

theorem diskHarmonicCutoff_testFunction {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) : TestFunction univ (diskHarmonicCutoff φ) := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp diskHarmonicCutoffBump.contDiff).mul hφ, ?_,
    subset_univ _⟩
  exact (diskHarmonicCutoffBump.hasCompactSupport.comp_left
     Complex.ofReal_zero).mul_right

theorem diskHarmonicCutoff_eventuallyEq {φ : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 2) : diskHarmonicCutoff φ =ᶠ[𝓝 z] φ := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  simp [diskHarmonicCutoff, diskHarmonicCutoffBump.one_of_mem_closedBall (ball_subset_closedBall hw), Complex.ofReal_one]

theorem diskHarmonicCutoff_eq_closedDisk {z : ℂ}
    (hz : z ∈ closedDisk) : diskHarmonicCutoff φ z = φ z := by
  
  exact (diskHarmonicCutoff_eventuallyEq (closedBall_subset_ball (by norm_num) hz)).self_of_nhds

theorem fderiv_diskHarmonicCutoff_eq {φ : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 2) :
    fderiv ℝ (diskHarmonicCutoff φ) z = fderiv ℝ φ z :=
  (diskHarmonicCutoff_eventuallyEq hz).fderiv_eq

theorem dirD_diskHarmonicCutoff_eq {φ : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 2) (v : ℂ) :
    dirD (diskHarmonicCutoff φ) v z = dirD φ v z := by
  unfold dirD
  rw [fderiv_diskHarmonicCutoff_eq hz]

theorem dirD_diskHarmonicCutoff_eventuallyEq {φ : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 2) (v : ℂ) :
    dirD (diskHarmonicCutoff φ) v =ᶠ[𝓝 z] dirD φ v := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact dirD_diskHarmonicCutoff_eq hw v

theorem lap_diskHarmonicCutoff_eq {φ : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 2) :
    lap (diskHarmonicCutoff φ) z = lap φ z := by
  
  change fderiv ℝ (dirD (diskHarmonicCutoff φ) 1) z 1 +
      fderiv ℝ (dirD (diskHarmonicCutoff φ) Complex.I) z Complex.I =
    fderiv ℝ (dirD φ 1) z 1 + fderiv ℝ (dirD φ Complex.I) z Complex.I
  rw [(dirD_diskHarmonicCutoff_eventuallyEq hz 1).fderiv_eq,
    (dirD_diskHarmonicCutoff_eventuallyEq hz Complex.I).fderiv_eq]

theorem integral_disk_boundary_modes :
    (∫ₚ θ, diskHolomorphicMode m (unitCirclePt θ) *
      diskAntiholomorphicMode n (unitCirclePt θ)) =
      if m = n then (anglePeriod : ℂ) else 0 := by
  have hprod : ∀ θ : ℝ,
      diskHolomorphicMode m (unitCirclePt θ) *
        diskAntiholomorphicMode n (unitCirclePt θ) =
        Complex.exp (((m : ℂ) - (n : ℂ)) * Complex.I * θ) := by
    intro θ
    rw [diskHolomorphicMode_unitCircle, diskAntiholomorphicMode_unitCircle,
      ← Complex.exp_add]
    ring
  simp_rw [hprod]
  by_cases hmn : m = n
  · simp [*]
  · have hsub : (m : ℂ) - (n : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hmn)
    have hc  :=
      mul_ne_zero hsub Complex.I_ne_zero
    have he : Complex.exp ((((m : ℂ) - (n : ℂ)) * Complex.I) * (anglePeriod : ℝ)) = 1 := calc
        _ = Complex.exp (((((m : ℤ) - (n : ℤ)) : ℤ) : ℂ) *
            (anglePeriod * Complex.I)) := by
          congr 1
          push_cast
          ring
        _ = 1 := Complex.exp_int_mul_two_pi_mul_I ((m : ℤ) - (n : ℤ))
    rw [if_neg hmn, integral_exp_mul_complex hc]
    simp only [he, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, zero_div]

/-- Green's formula gives the actual disk gradient Gram matrix. The
integrals and the compact cutoff are physical, with ordinary area and
parameter measures. -/
theorem integral_disk_holomorphic_antiholomorphic_gradients :
    (∫ z in unitDisk, ∑ i : Fin 2,
      dirD (diskHolomorphicMode m) (coordDir i) z *
        dirD (diskAntiholomorphicMode n) (coordDir i) z) =
      if m = n then (anglePeriod : ℂ) * (n : ℂ) else 0 := by
  have hV := diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hV.2.1 hV.1 (by simp)
  
  have hgreen := doubleLayer_eq_integral unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam hK hV.2.1
     (by
       intro θ _
       exact diskHarmonicCutoff_eq_closedDisk _
         (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))
    (contDiff_diskAntiholomorphicMode n)
  calc
    _ = ∫ z in unitDisk,
        (diskHarmonicCutoff (diskHolomorphicMode m) z *
          lap (diskAntiholomorphicMode n) z +
          ∑ i : Fin 2, dirD (diskHarmonicCutoff (diskHolomorphicMode m)) (coordDir i) z *
            dirD (diskAntiholomorphicMode n) (coordDir i) z) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      
      simp only [lap_diskAntiholomorphicMode, mul_zero, zero_add,
        dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz)]
    _ = _ := hgreen.symm
    _ = n *
        (∫ θ in 0..anglePeriod, diskHolomorphicMode m (unitCirclePt θ) *
          diskAntiholomorphicMode n (unitCirclePt θ)) := by
      unfold doubleLayer
      simp_rw [conormal_diskAntiholomorphicMode]
      rw [← intervalIntegral.integral_const_mul]
      grind
    _ = _ := by
      simp [integral_disk_boundary_modes] <;> ring

theorem conj_dirD_diskHolomorphicMode :
    conj (dirD (diskHolomorphicMode m) v z) =
      dirD (diskAntiholomorphicMode m) v z := by
  simp [dirD_diskHolomorphicMode, dirD_diskAntiholomorphicMode, map_pow, map_natCast]

theorem conj_dirD_diskAntiholomorphicMode :
    conj (dirD (diskAntiholomorphicMode m) v z) =
      dirD (diskHolomorphicMode m) v z := by
  simp [dirD_diskAntiholomorphicMode, dirD_diskHolomorphicMode, map_pow, map_natCast, Complex.conj_conj]

end

/-- The actual Hilbert space of the two disk-gradient components. -/
abbrev DiskGradientSpace := PiLp 2 (fun _ : Fin 2 => L2 unitDisk)

def diskTestGradient {φ : ℂ → ℂ} (hφ : TestFunction univ φ) : DiskGradientSpace :=
  WithLp.toLp 2 (fun i : Fin 2 =>
    ((hφ.dirD (coordDir i)).memLp' 2 ).toLp
      (dirD φ (coordDir i)))

theorem diskTestGradient_ae {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (i : Fin 2) :
    ((diskTestGradient hφ i : L2 unitDisk) : ℂ → ℂ) =ᵐ[
      volume.restrict unitDisk] dirD φ (coordDir i) :=
  ((hφ.dirD (coordDir i)).memLp' 2 ).coeFn_toLp

theorem inner_diskTestGradient {φ ψ : ℂ → ℂ}
    (hφ : TestFunction univ φ) (hψ : TestFunction univ ψ) :
    ⟪diskTestGradient hφ, diskTestGradient hψ⟫_ℂ =
      ∫ z in unitDisk, ∑ i : Fin 2,
        conj (dirD φ (coordDir i) z) * dirD ψ (coordDir i) z := calc
    _ = ∑ i : Fin 2, ∫ z in unitDisk,
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

section

variable (m : ℕ) (i : Fin 2) (n : ℕ)
include m

def diskHolomorphicGradient : DiskGradientSpace :=
  diskTestGradient (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m))

def diskAntiholomorphicGradient : DiskGradientSpace :=
  diskTestGradient (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m))

theorem diskHolomorphicGradient_ae :
    ((diskHolomorphicGradient m i : L2 unitDisk) : ℂ → ℂ) =ᵐ[
      volume.restrict unitDisk] dirD (diskHolomorphicMode m) (coordDir i) := by
  filter_upwards [diskTestGradient_ae
    (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)) i,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskTestGradient
    (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)) i) z = _
  rw [hz, dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hzD)]

theorem diskAntiholomorphicGradient_ae :
    ((diskAntiholomorphicGradient m i : L2 unitDisk) : ℂ → ℂ) =ᵐ[
      volume.restrict unitDisk] dirD (diskAntiholomorphicMode m) (coordDir i) := by
  filter_upwards [diskTestGradient_ae
    (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)) i,
    ae_restrict_mem measurableSet_ball] with z hz hzD
  change (diskTestGradient
    (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)) i) z = _
  rw [hz, dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hzD)]

theorem inner_diskHolomorphicGradient :
    ⟪diskHolomorphicGradient m, diskHolomorphicGradient n⟫_ℂ =
      if m = n then (anglePeriod : ℂ) * (m : ℂ) else 0 := by
  change ⟪diskTestGradient _, diskTestGradient _⟫_ℂ = _
  rw [inner_diskTestGradient]
  calc
    _ = ∫ z in unitDisk, ∑ i : Fin 2,
        dirD (diskHolomorphicMode n) (coordDir i) z *
          dirD (diskAntiholomorphicMode m) (coordDir i) z := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      
      simp only [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz), conj_dirD_diskHolomorphicMode]
      grind
    _ = _ := by
      rw [integral_disk_holomorphic_antiholomorphic_gradients]
      simp [eq_comm]

theorem inner_diskAntiholomorphicGradient :
    ⟪diskAntiholomorphicGradient m, diskAntiholomorphicGradient n⟫_ℂ =
      if m = n then (anglePeriod : ℂ) * (m : ℂ) else 0 := by
  change ⟪diskTestGradient _, diskTestGradient _⟫_ℂ = _
  rw [inner_diskTestGradient]
  calc
    _ = ∫ z in unitDisk, ∑ i : Fin 2,
        dirD (diskHolomorphicMode m) (coordDir i) z *
          dirD (diskAntiholomorphicMode n) (coordDir i) z := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      
      simp only [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz), conj_dirD_diskAntiholomorphicMode]
    _ = _ := by
      rw [integral_disk_holomorphic_antiholomorphic_gradients]
      split_ifs with hmn
      · rw [hmn]
      · rfl

theorem inner_diskHolomorphicGradient_antiholomorphicGradient :
    ⟪diskHolomorphicGradient m, diskAntiholomorphicGradient n⟫_ℂ = 0 := by
  change ⟪diskTestGradient _, diskTestGradient _⟫_ℂ = _
  rw [inner_diskTestGradient]
  calc
    _ = ∫ _z in unitDisk, (0 : ℂ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      
      simp only [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz), conj_dirD_diskHolomorphicMode]
      exact disk_antiholomorphic_gradient_bilinear_zero m n z
    _ = 0 := by simp

theorem inner_diskAntiholomorphicGradient_holomorphicGradient :
    ⟪diskAntiholomorphicGradient m, diskHolomorphicGradient n⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_diskHolomorphicGradient_antiholomorphicGradient]
  simp

def diskHarmonicGradientScale : ℂ :=
  ((Real.sqrt (anglePeriod * ((m + 1 : ℕ) : ℝ)))⁻¹ : ℝ)

private lemma diskHarmonicGradientScale_normalizes :
    conj (diskHarmonicGradientScale m) *
      (diskHarmonicGradientScale m * ((anglePeriod : ℂ) * ((m + 1 : ℕ) : ℂ))) = 1 := by
  have hp : 0 < anglePeriod * ((m + 1 : ℕ) : ℝ) := by positivity
  have hs  :=
    Real.sqrt_ne_zero'.mpr hp
  have hsq := Real.sq_sqrt hp.le
  
  simp only [diskHarmonicGradientScale, Complex.conj_ofReal]
  exact_mod_cast (by
    field_simp [hs]
    linarith)

end

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
                  (diskHarmonicGradientScale m * ((anglePeriod : ℂ) * ((m + 1 : ℕ) : ℂ))) := by
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
                  (diskHarmonicGradientScale m * ((anglePeriod : ℂ) * ((m + 1 : ℕ) : ℂ))) := by
                    ring
              _ = 1 := diskHarmonicGradientScale_normalizes m
          · simp [diskNormalizedHarmonicGradient, inner_smul_left, inner_smul_right,
              inner_diskAntiholomorphicGradient, hmn]

end PolyaNeumann

end
