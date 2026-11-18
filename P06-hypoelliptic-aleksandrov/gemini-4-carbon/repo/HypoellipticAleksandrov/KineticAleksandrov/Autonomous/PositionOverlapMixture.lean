module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapNorm
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitCone
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapHolder
import Mathlib.MeasureTheory.Integral.Prod

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical

/-- The joint extended density of a finite kernel relative to a sigma-finite reference. -/
def positionKernelDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (k : Kernel X Y) (m : Measure Y) [SigmaFinite m] : X → Y → ℝ≥0∞ :=
  fun x y => m.toFinite.rnDeriv m y * k.rnDeriv (Kernel.const X m.toFinite) x y

/-- This chosen kernel density is jointly measurable. -/
theorem measurable_positionKernelDensity {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (k : Kernel X Y) (m : Measure Y) [SigmaFinite m] :
    Measurable (fun p : X × Y => positionKernelDensity k m p.1 p.2) :=
  ((Measure.measurable_rnDeriv m.toFinite m).comp measurable_snd).mul
    (Kernel.measurable_rnDeriv k (Kernel.const X m.toFinite))

/-- Absolute continuity identifies the joint density with each actual kernel measure. -/
theorem withDensity_positionKernelDensity {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (k : Kernel X Y) [IsFiniteKernel k] (m : Measure Y) [SigmaFinite m]
    (x : X) (hx : k x ≪ m) :
    m.withDensity (positionKernelDensity k m x) = k x := by
  let eta := Kernel.const X m.toFinite
  have hxe : k x ≪ eta x := by
    simpa only [eta, Kernel.const_apply] using
      hx.trans (absolutelyContinuous_toFinite m)
  have hk := Kernel.withDensity_rnDeriv_eq (κ := k) (η := eta) hxe
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv k eta)] at hk
  change m.toFinite.withDensity (k.rnDeriv eta x) = k x at hk
  change m.withDensity (m.toFinite.rnDeriv m * k.rnDeriv eta x) = k x
  rw [withDensity_mul m (Measure.measurable_rnDeriv m.toFinite m)
    (Kernel.measurable_rnDeriv_right k eta x),
    Measure.withDensity_rnDeriv_eq m.toFinite m (toFinite_absolutelyContinuous m)]
  exact hk


/-- The literal coordinate product makes physical spacetime second countable. -/
instance positionPoint_secondCountableTopology : SecondCountableTopology Point :=
  (HypoellipticAleksandrov.KineticPoint.homeomorphProd 1).secondCountableTopology

/-- The active Green kernel agrees with the canonical Green at every valid starting velocity. -/
theorem enlargedActiveGreenKernel_apply
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    enlargedActiveGreenKernel hH hLE hlam hLam A c e =
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e he) := by
  change (if hp : e.velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hp) else 0) = _
  rw [dite_eq_left he]

/-- Uniform quadratic mass makes the all-time physical active family a finite kernel. -/
instance enlargedActiveGreenKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) :
    IsFiniteKernel (enlargedActiveGreenKernel hH hLE hlam hLam A c) := by
  refine ⟨ENNReal.ofReal ((3 * c.r / 2) ^ 2 / (2 * lam)), ENNReal.ofReal_lt_top, ?_⟩
  intro e
  by_cases he : e.velocity 0 ∈ c.active
  · rw [enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he]
    apply (stripGreen_quadratic_mass hH hLE hlam hLam A c.activeInterval ⊤ _).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_iff_of_pos_right (by linarith : 0 < 2 * lam)).2
    change (e.velocity 0 - (c.vbar - 3 * c.r / 4)) *
      (c.vbar + 3 * c.r / 4 - e.velocity 0) ≤ (3 * c.r / 2) ^ 2
    nlinarith only [sq_nonneg (e.velocity 0 - c.vbar), sq_nonneg c.r]
  · change (if hp : e.velocity 0 ∈ c.active then
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hp)
      else 0) univ ≤ _
    rw [dite_eq_right he]
    exact zero_le


/-- The actual joint extended density of the all-time active Green kernel. -/
def positionActiveDensity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) : Point → Point → ℝ≥0∞ := by
  letI := density_volume_sigmaFinite
  exact positionKernelDensity (enlargedActiveGreenKernel hH hLE hlam hLam A c) volume

/-- The active density is jointly measurable in the physical starting and observed points. -/
theorem measurable_positionActiveDensity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) :
    Measurable (fun p : Point × Point =>
      positionActiveDensity hH hLE hlam hLam A c p.1 p.2) := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  exact measurable_positionKernelDensity
    (enlargedActiveGreenKernel hH hLE hlam hLam A c) (volume : Measure Point)

/-- The jointly measurable density represents the same canonical active kernel. -/
theorem withDensity_positionActiveDensity (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    volume.withDensity (positionActiveDensity hH hLE hlam hLam A c e) =
      enlargedActiveGreenKernel hH hLE hlam hLam A c e  := by
  have enlargedActiveGreenKernel_absolutelyContinuous :
      enlargedActiveGreenKernel hH hLE hlam hLam A c e ≪ (volume : Measure Point) := by
    by_cases he : e.velocity 0 ∈ c.active
    · obtain ⟨C, _, hd⟩ := (hpush hH hLE lam Lam hlam hLam).2 (5 / 4) (by norm_num)
      obtain ⟨G, _, _, hG, _, _⟩ := hd A c e he
      rw [enlargedActiveGreenKernel_apply hH hLE hlam hLam A c e he, hG]
      exact (withDensity_absolutelyContinuous _ _).trans
        Measure.restrict_le_self.absolutelyContinuous
    · change (if hp : e.velocity 0 ∈ c.active then
        stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c e hp)
        else 0) ≪ volume
      rw [dite_eq_right he]
      intro B _
      rfl
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  exact withDensity_positionKernelDensity
    (enlargedActiveGreenKernel hH hLE hlam hLam A c) (volume : Measure Point) e
    (enlargedActiveGreenKernel_absolutelyContinuous)


/-- Integrating the canonical joint density against a physical starting measure. -/
def positionMixtureDensity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) : Point → ℝ≥0∞ :=
  fun z => ∫⁻ e, positionActiveDensity hH hLE hlam hLam A c e z ∂nu

/-- The actual density of a finite starting mixture is measurable. -/
theorem measurable_positionMixtureDensity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [SFinite nu] :
    Measurable (positionMixtureDensity hH hLE hlam hLam A c nu) := by
  exact (measurable_positionActiveDensity hH hLE hlam hLam A c).lintegral_prod_left'

/-- Fubini identifies the actual Green mixture with its integrated joint density. -/
theorem withDensity_positionMixtureDensity (hpush : PushforwardStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) [SFinite nu] :
    volume.withDensity (positionMixtureDensity hH hLE hlam hLam A c nu) =
      enlargedActiveGreen hH hLE hlam hLam A c nu := by
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  ext B hB
  change (volume.withDensity (positionMixtureDensity hH hLE hlam hLam A c nu)) B =
    (nu.bind (enlargedActiveGreenKernel hH hLE hlam hLam A c)) B
  rw [withDensity_apply _ hB, Measure.bind_apply hB (Kernel.aemeasurable _)]
  unfold positionMixtureDensity
  rw [← lintegral_lintegral_swap (μ := nu) (ν := volume.restrict B)
    (f := positionActiveDensity hH hLE hlam hLam A c)
    (measurable_positionActiveDensity hH hLE hlam hLam A c).aemeasurable]
  apply lintegral_congr
  intro e
  rw [← withDensity_apply _ hB, withDensity_positionActiveDensity hpush hH hLE hlam hLam]

/-- A positive mixture inherits a uniform pole bound, with its total starting mass. -/
theorem positionPositiveNorm_mixture_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (nu : Measure X) [IsFiniteMeasure nu] (m : Measure Y) [SFinite m]
    (F : X → Y → ℝ≥0∞) (hF : Measurable (Function.uncurry F))
    (q : ℝ) (hq : 1 < q) (K : ℝ≥0∞)
    (hK : ∀ᵐ x ∂nu, positionPositiveNorm m q (F x) ≤ K) :
    positionPositiveNorm m q (fun y => ∫⁻ x, F x y ∂nu) ≤ nu univ * K := by
  have hpow : ∀ᵐ x ∂nu, (∫⁻ y, F x y ^ q ∂m) ≤ K ^ q := by
    filter_upwards [hK] with x hx
    simpa only [positionPositiveNorm, ← ENNReal.rpow_mul,
      one_div_mul_cancel (by linarith : q ≠ 0), ENNReal.rpow_one] using (ENNReal.rpow_le_rpow hx (by linarith : 0 ≤ q))
  have hi : (∫⁻ y, (∫⁻ x, F x y ∂nu) ^ q ∂m) ≤ (nu univ * K) ^ q := by
    calc
      _ ≤ ∫⁻ y, (nu univ) ^ (q - 1) * (∫⁻ x, F x y ^ q ∂nu) ∂m := by
        apply lintegral_mono
        intro y
        exact position_integral_rpow_le nu _ (hF.comp (measurable_id.prodMk measurable_const))
          q hq
      _ = (nu univ) ^ (q - 1) * ∫⁻ x, ∫⁻ y, F x y ^ q ∂m ∂nu := by
        have hm : Measurable (fun y => ∫⁻ x, F x y ^ q ∂nu) :=
          (hF.pow_const q).lintegral_prod_left'
        rw [lintegral_const_mul _ hm]
        exact congrArg (fun t => nu univ ^ (q - 1) * t)
          (lintegral_lintegral_swap (μ := nu) (ν := m)
            (f := fun x y => F x y ^ q) (hF.pow_const q).aemeasurable).symm
      _ ≤ (nu univ) ^ (q - 1) * (nu univ * K ^ q) := by
        gcongr
        simpa only [lintegral_const, mul_comm] using lintegral_mono_ae hpow
      _ = (nu univ * K) ^ q := by
        rw [← mul_assoc, position_rpow_sub_one_mul _ q hq.le,
          ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q)]
  unfold positionPositiveNorm
  apply (ENNReal.rpow_le_rpow hi (one_div_nonneg.mpr (by linarith))).trans_eq
  rw [← ENNReal.rpow_mul, mul_one_div_cancel (by linarith : q ≠ 0), ENNReal.rpow_one]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

