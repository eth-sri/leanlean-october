module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyAction
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Geometry
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Literal source boxes and finite real/extended occupation bridges -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- The source gauge, using the existing Bellman geometry. -/
def rho (z : Z) : ℝ := Real.rpow (z.1^2+z.2^6) (1/6)

/-- The occupation exponent selected from the barrier degree. -/
def gamma (alpha : ℝ) : ℝ := 2-alpha

/-- The singular extended weight retains infinite value at the origin. -/
def rhoWeight (g : ℝ) (z : Z) : ENNReal := (ENNReal.ofReal (rho z))^(-g)

/-- The literal position-velocity box of the source. -/
def box (A0 r Y : ℝ) : Set Z := {z | |z.1-Y| ≤ A0*r^3 ∧ |z.2| ≤ A0*r}

/-- Source boxes are Borel. -/
theorem box_measurable (A0 r Y : ℝ) : MeasurableSet (box A0 r Y) := (isClosed_le (continuous_fst.sub continuous_const).abs continuous_const |>.inter
    (isClosed_le continuous_snd.abs continuous_const)).measurableSet

variable (E : FullSpaceEvolution) (z : Z) (A0 r Y T : ℝ)

/-- The physical scalar kernel inherits the actual master sub-Markov bound. -/
theorem kernelXV_mass_le_one  (t : NNReal) (z : Z) :
    kernelXV E t z univ ≤ 1 := by
  rw [kernelXV, Measure.map_apply nativeToXV_measurable MeasurableSet.univ]
  exact E.2.mass_le_one _

/-- Nonnegative elapsed queries depend measurably on real time. -/
theorem wholeQuery_realTime_measurable  :
    Measurable (fun t : ℝ => wholeQuery (Real.toNNReal t) z) := by
  apply Measurable.subtype_mk
  fun_prop

/-- Evaluation of the actual physical kernel on any Borel set is measurable in elapsed time. -/
theorem kernelXV_realTime_measurable 
    (s : Set Z) (hs : MeasurableSet s) :
    Measurable (fun t : ℝ => kernelXV E (Real.toNNReal t) z s) := by
  have he (t : ℝ) : kernelXV E _ z s =
      E.2.master (wholeQuery (Real.toNNReal t) z) _ :=
    Measure.map_apply nativeToXV_measurable hs
  simp_rw [he]
  exact (E.2.jointlyMeasurable_apply _ (nativeToXV_measurable hs)).comp
    (wholeQuery_realTime_measurable z)

/-- Real box actions are genuinely integrable over finite time intervals. -/
theorem box_action_integrableOn  :
    IntegrableOn (fun t : ℝ => (kernelXV E (Real.toNNReal t) z (box A0 r Y)).toReal)
      (Ioc 0 T) := by
  have hm := (kernelXV_realTime_measurable E z _ (box_measurable A0 r Y)).ennreal_toReal
  have ht : volume (Ioc 0 T) ≠ ⊤ := by
    simp
  apply Integrable.mono' (integrableOn_const (C := (1)) ht) hm.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have hmass := (measure_mono (subset_univ (box A0 r Y))).trans
    (kernelXV_mass_le_one E (Real.toNNReal t) z)
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hmass

/-- The extended and source real box occupations agree, with finiteness established first. -/
theorem box_occupation_ofReal_integral  :
    ENNReal.ofReal (∫ t in Ioc 0 T,
      (kernelXV E (Real.toNNReal t) z (box A0 r Y)).toReal) =
      ∫⁻ t in Ioc 0 T, kernelXV E (Real.toNNReal t) z (box A0 r Y) := by
  rw [ofReal_integral_eq_lintegral_ofReal (box_action_integrableOn E z A0 r Y T)
    (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
  apply lintegral_congr
  intro t
  have hb := (measure_mono (subset_univ (box A0 r Y))).trans
    (kernelXV_mass_le_one E (Real.toNNReal t) z)
  aesop

/-- The source box indicator as an actual bounded Borel physical terminal datum. -/
def boxIndicatorDatum (A0 r Y : ℝ) : BoundedBorel (EvolutionAmbientState 1) := by
  let f := (box A0 r Y).indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator (box_measurable A0 r Y)
  have hm : Measurable (fun x : EvolutionAmbientState 1 => (x.1 0,x.2 0)) :=
    (measurable_pi_apply 0 |>.comp measurable_fst).prodMk
      (measurable_pi_apply 0 |>.comp measurable_snd)
  refine ⟨fun x => f (x.1 0,x.2 0), hf.comp hm, 1, zero_le_one, ?_⟩
  intro x
  by_cases hx : (x.1 0,x.2 0) ∈ box A0 r Y
  · aesop
  aesop

/-- The source semigroup indicator action is exactly the finite physical-kernel box mass. -/
theorem box_action_eq_fullSpaceAction {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (z : Z) (t : NNReal) (A0 r Y : ℝ) :
    (kernelXV E t z (box A0 r Y)).toReal =
      fullSpaceAction E (boxIndicatorDatum A0 r Y) ⟨t, fun _ => z.1, fun _ => z.2⟩ := by
  rw [fullSpaceAction_eq_zeroTime A E hE _ _ t.property]
  let f := (box A0 r Y).indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator (box_measurable A0 r Y)
  have he := integral_map nativeToXV_measurable.aemeasurable
    (hf.aestronglyMeasurable (μ := kernelXV E t z))
  change (kernelXV E t z _).toReal =
    ∫ x, f (nativeToXV x) ∂E.2.master (wholeQuery t z)
  rw [← he]
  exact (integral_indicator_one (box_measurable A0 r Y)).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
