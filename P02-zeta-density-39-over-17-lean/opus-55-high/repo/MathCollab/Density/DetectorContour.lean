module
/-
Pole-removal and finite contour argument adapted from McColm TypeIICoverage,
exact pin 2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT.
X, Y and rectangle height R are independent parameters. The actual zeta
function and the existing floor-cutoff mollifier are retained.
-/
public import MathCollab.Density.DetectorMellin
public import MathCollab.Density.AbelZetaGrowth
public import MathCollab.Density.DetectorGamma
public import MathCollab.Density.RectangleResidue
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex MeasureTheory Set Filter
open MathCollab.Density.ZetaGrowth MathCollab.Density.Contour
open scoped Topology
noncomputable section
namespace MathCollab.Density

def shiftedRegularizedZeta (ρ s : ℂ) : ℂ :=
  regularizedRiemannZeta (ρ + s)

/-- The analytic quotient which removes the apparent `Γ(s)` singularity at
`s = 0` when `ζ(ρ)=0`. -/
def zetaZeroQuotient (ρ s : ℂ) : ℂ :=
  dslope (shiftedRegularizedZeta ρ) 0 s

/-- Entire numerator on the detector rectangle.  The only remaining pole
of the original contour integrand is represented explicitly by division by
`s - (1 - ρ)`. -/
def detectorContourNumerator (ρ : ℂ) (X Y : ℝ) (s : ℂ) : ℂ :=
  (Y : ℂ) ^ s * Complex.Gamma (s + 1) *
    zetaMollifier X (ρ + s) * zetaZeroQuotient ρ s

/-- The residue crossed at the zeta pole `s = 1 - ρ`. -/
def detectorResidue (ρ : ℂ) (X Y : ℝ) : ℂ :=
  (Y : ℂ) ^ (1 - ρ) * Complex.Gamma (1 - ρ) *
    zetaMollifier X 1

theorem shiftedRegularizedZeta_zero {ρ : ℂ}
    (hρOne : ρ ≠ 1) (hZero : riemannZeta ρ = 0) :
    shiftedRegularizedZeta ρ 0 = 0 := by
  rw [shiftedRegularizedZeta, add_zero, regularizedRiemannZeta,
    Function.update_of_ne hρOne, hZero, mul_zero]

theorem shiftedRegularizedZeta_eq {ρ s : ℂ}
    (hPole : ρ + s ≠ 1) :
    shiftedRegularizedZeta ρ s =
      (s - (1 - ρ)) * riemannZeta (ρ + s) := by
  rw [shiftedRegularizedZeta, regularizedRiemannZeta,
    Function.update_of_ne hPole]
  ring

/-- Away from the two removed points, the analytic numerator divided by its
explicit zeta-pole factor is exactly the original detector integrand. -/
theorem detectorContourNumerator_div_eq_integrand {ρ s : ℂ} {X Y : ℝ}
    (hρOne : ρ ≠ 1) (hZero : riemannZeta ρ = 0)
    (hsZero : s ≠ 0) (hsPole : s ≠ 1 - ρ) :
    detectorContourNumerator ρ X Y s / (s - (1 - ρ)) =
      (Y : ℂ) ^ s * Complex.Gamma s *
        zetaMollifier X (ρ + s) * riemannZeta (ρ + s) := by
  have hR0 := shiftedRegularizedZeta_zero hρOne hZero
  have hShiftPole : ρ + s ≠ 1 := by
    intro h
    apply hsPole
    linear_combination h
  have hSlope := sub_smul_dslope_of_zero hR0 s
  have hQuotient : s * zetaZeroQuotient ρ s =
      (s - (1 - ρ)) * riemannZeta (ρ + s) := by
    simpa [zetaZeroQuotient, shiftedRegularizedZeta_eq hShiftPole,
      smul_eq_mul] using hSlope
  rw [div_eq_iff (sub_ne_zero.mpr hsPole)]
  unfold detectorContourNumerator
  rw [Complex.Gamma_add_one s hsZero]
  grind

/-- Exact residue evaluation at `s = 1 - ρ`. -/
theorem detectorContourNumerator_at_pole {ρ : ℂ} {X Y : ℝ}
    (hρOne : ρ ≠ 1) (hZero : riemannZeta ρ = 0) :
    detectorContourNumerator ρ X Y (1 - ρ) = detectorResidue ρ X Y := by
  let p : ℂ := 1 - ρ
  have hpZero : p ≠ 0 := sub_ne_zero.mpr hρOne.symm
  have hR0 := shiftedRegularizedZeta_zero hρOne hZero
  have hRp : shiftedRegularizedZeta ρ p = 1 := by
    pm_6743
    rw [shiftedRegularizedZeta, hρp, regularizedRiemannZeta]
    simp
  have hSlope := sub_smul_dslope_of_zero hR0 p
  have hQuotient : p * zetaZeroQuotient ρ p = 1 := by
    aesop
  unfold detectorContourNumerator detectorResidue
  change (Y : ℂ) ^ p * Complex.Gamma (p + 1) *
      zetaMollifier X (ρ + p) * zetaZeroQuotient ρ p =
    (Y : ℂ) ^ p * Complex.Gamma p * zetaMollifier X 1
  rw [Complex.Gamma_add_one p hpZero]
  pm_6743
  rw [hρp]
  grind

theorem differentiableAt_shiftedRegularizedZeta (ρ s : ℂ) :
    DifferentiableAt ℂ (shiftedRegularizedZeta ρ) s := by
  unfold shiftedRegularizedZeta
  exact (differentiableAt_regularizedRiemannZeta (ρ + s)).comp s
    ((differentiableAt_const (𝕜 := ℂ) ρ).add differentiableAt_id)

theorem differentiableAt_zetaZeroQuotient (ρ s : ℂ) :
    DifferentiableAt ℂ (zetaZeroQuotient ρ) s := by
  have hShift : DifferentiableOn ℂ (shiftedRegularizedZeta ρ) Set.univ :=
    fun z _hz => (differentiableAt_shiftedRegularizedZeta ρ z).differentiableWithinAt
  have hSlope : DifferentiableOn ℂ
      (dslope (shiftedRegularizedZeta ρ) 0) Set.univ :=
    (Complex.differentiableOn_dslope
      (Filter.univ_mem : Set.univ ∈ nhds (0 : ℂ))).2 hShift
  exact differentiableWithinAt_univ.mp (hSlope s (Set.mem_univ s))

/-- The pole-removed numerator is holomorphic throughout the open half-plane
`Re s > -1`, which contains every rectangle used to shift from `1/2` to
`1/2 - Re ρ` in the zero-density range. -/
theorem differentiableOn_detectorContourNumerator {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) :
    DifferentiableOn ℂ (detectorContourNumerator ρ X Y)
      {s : ℂ | -(1 : ℝ) < s.re} := by
  intro s hs
  change -(1 : ℝ) < s.re at hs
  pm_146 hBase Y hY.ne'
  have hPow : DifferentiableAt ℂ (fun z : ℂ => (Y : ℂ) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl hBase)
  have hGammaNoPole : ∀ m : ℕ, s + 1 ≠ -m := by
    intro m hm
    have hRe := congrArg Complex.re hm
    pm_96 hmNonneg m
    simp at hRe
    linarith
  have hGamma : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) s :=
    (Complex.differentiableAt_Gamma (s + 1) hGammaNoPole).comp s
      (differentiableAt_id.add_const 1)
  have hMollifier : DifferentiableAt ℂ
      (fun z : ℂ => zetaMollifier X (ρ + z)) s :=
    (differentiableAt_zetaMollifier X (ρ + s)).comp s
      ((differentiableAt_const (𝕜 := ℂ) ρ).add differentiableAt_id)
  have hQuotient := differentiableAt_zetaZeroQuotient ρ s
  exact (((hPow.mul hGamma).mul hMollifier).mul hQuotient).differentiableWithinAt

set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
/-- Finite-height rectangle shift.  The apparent pole at zero has already
been removed, so the rectangle crosses exactly the zeta pole `1 - ρ`. -/
theorem detector_finite_rectangle_residue {ρ : ℂ} {X Y R : ℝ}
    (hY : 0 < Y) (hβLower : 3/4 ≤ ρ.re) (hβUpper : ρ.re < 1)
    (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral'
      (fun s => detectorContourNumerator ρ X Y s / (s - (1 - ρ)))
      ((a : ℂ) - (R : ℂ)*I) (((1/2 : ℝ) : ℂ) + (R : ℂ)*I) =
        detectorResidue ρ X Y := by
  pm_4252
  have hpInterior : Rectangle z w ∈ nhds p := by
    pm_4254
    pm_7845
    · simp [p, z, w]
      constructor <;> linarith
  have hRectSubset : Rectangle z w ⊆ {s : ℂ | -(1 : ℝ) < s.re} := by
    pm_4253
    have hzReal : z.re = a := by simp [z]
    linarith [hsBounds.1]
  pm_4251


/-- Exact finite shift for the literal kernel; both exceptional points are
strictly interior for every independently chosen R>|Im(rho)|. -/
theorem detector_finite_rectangle_kernel {ρ : ℂ} {X Y R : ℝ}
    (hY : 0 < Y) (hβLower : 3/4 ≤ ρ.re) (hβUpper : ρ.re < 1)
    (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral' (detectorKernel ρ X Y)
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        detectorResidue ρ X Y := by
  pm_8395
  pm_4256
  pm_5872
  pm_4257
  pm_8248 detector_finite_rectangle_residue
  pm_4255


end MathCollab.Density
