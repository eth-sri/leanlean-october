module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockExtensions
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullCoefficientAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import Mathlib.Analysis.Calculus.MeanValue

/-! # The extended clock coefficients satisfy the case-I setting -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped MatrixOrder

/-- The global normalized diffusion on the coefficient carrier. -/
def Clock.extendedCoefficient (c : Clock) (lam : ℝ) (a : ℝ → ℝ → ℝ) (e : Point) :
    CoefficientField 1 := fun s y _ _ => c.extendedDiffusion lam a e s (y 0)

/-- The global normalized drift on the native vector carrier. -/
def Clock.extendedVectorDrift (c : Clock) : PDE.Vec 1 → PDE.Vec 1 :=
  fun y _ => c.extendedDrift (y 0)

private theorem euclideanNorm_one (y : PDE.Vec 1) : PDE.vecEuclideanNorm y = |y 0| := by
  simp only [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Fin.sum_univ_one,
    ← pow_two, Real.sqrt_sq_eq_abs]

variable {lam Lam : ℝ} (c : Clock)

/-- The lifted drift is smooth in the native one-dimensional carrier. -/
theorem Clock.extendedVectorDrift_smooth  :
    IsSmoothDrift c.extendedVectorDrift := by
  apply contDiff_pi.mpr
  intro i
  exact c.extendedDrift_smooth.comp (contDiff_apply ℝ ℝ _)

private theorem lifted_fderiv  (y w : PDE.Vec 1) :
    fderiv ℝ c.extendedVectorDrift y w =
      fun _ => deriv c.extendedDrift (y 0) * w 0 := by
  have hd := (c.hasDerivAt_extendedDrift (y 0)).hasFDerivAt.comp y
    (ContinuousLinearMap.proj _ : PDE.Vec 1 →L[ℝ] ℝ).hasFDerivAt
  have hd' : HasFDerivAt c.extendedVectorDrift
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (ContinuousLinearMap.toSpanSingleton ℝ _).comp
          (ContinuousLinearMap.proj _ : PDE.Vec 1 →L[ℝ] ℝ)) y :=
    hasFDerivAt_pi.mpr (fun _ => hd)
  rw [hd'.fderiv, (c.hasDerivAt_extendedDrift _).deriv]
  ext i
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply]
  ring

/-- Scalar derivative bounds give the exact Euclidean transport bounds of Section Two. -/
theorem Clock.extendedVectorDrift_transportBounds  :
    HasTransportBounds (9 / 25 : ℝ) 9 c.extendedVectorDrift := by
  constructor
  · have hl : LipschitzWith (9 : NNReal) c.extendedDrift :=
      lipschitzWith_of_nnnorm_deriv_le
        (fun y => (c.hasDerivAt_extendedDrift y).differentiableAt) (fun y => by
          change |deriv c.extendedDrift y| ≤ (9)
          have hb := c.extendedDrift_deriv_bounds y
          grind)
    intro y y'
    rw [euclideanNorm_one, euclideanNorm_one]
    exact hl.norm_sub_le _ _
  · intro y w hw
    rw [euclideanNorm_one] at hw
    rw [lifted_fderiv]
    simp only [PDE.vecDot, Fin.sum_univ_one]
    have heq : w 0 * (deriv c.extendedDrift (y 0) * w 0) =
        deriv c.extendedDrift (y 0) := by
      grind
    rw [heq]
    exact (c.extendedDrift_deriv_bounds _).1

/-- The global normalized coefficient satisfies the Section Two coefficient conditions. -/
theorem Clock.extendedCoefficient_sectionTwo  (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (c : Clock) (A : SmoothAutonomous lam Lam) (e : Point) :
    IsSectionTwoCoefficient (3 * lam / 5) (3 * Lam) (c.extendedCoefficient lam A.a e) := by
  let E : SmoothAutonomous _ _ :=
    ⟨c.extendedDiffusion lam A.a e, c.extendedDiffusion_smooth A e,
      c.extendedDiffusion_bounds hlam hLam A e⟩
  refine ⟨by positivity, by linarith, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact E.smooth.comp (contDiff_fst.prodMk
      ((contDiff_apply ℝ ℝ _).comp contDiff_snd.fst))
  · intro s y
    rfl
  · intro s y
    exact (autonomousCoefficient_bounds E 0 (fun _ => s) y).1
  · intro s y
    exact (autonomousCoefficient_bounds E 0 (fun _ => s) y).2

/-- The literal global clock extensions have case-I structural constants independent of
centre, scale, starting point, and coefficient derivatives. -/
theorem Clock.extended_sourceSetting  (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (c : Clock) (A : SmoothAutonomous lam Lam) (e : Point) :
    SourceSetting (3 * lam / 5) (3 * Lam) (9 / 25) 9
      (PDE.oneDimensionalAxisBox (-3 / 4) (3 / 4))
      (c.extendedCoefficient lam A.a e) c.extendedVectorDrift := by
  refine ⟨c.extendedCoefficient_sectionTwo hlam hLam A e,
    c.extendedVectorDrift_smooth, by norm_num, by norm_num,
    c.extendedVectorDrift_transportBounds, Or.inr ?_⟩
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
