module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsPhysicalGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxCompactTest
import Mathlib

/-! # Uniform deterministic box occupation, independent of return-time comparison -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

private theorem box_integral_eq (E : FullSpaceEvolution) (A r Y : ℝ) (z : Z) (T : ℝ) :
    (∫ t in Ioc 0 T, (kernelXV E (Real.toNNReal t) z (box A r Y)).toReal) =
      (physicalOccupationMeasure E z T).real (box A r Y) := by
  rw [measureReal_def,physicalOccupationMeasure_apply _ _ _ _ (box_measurable A r Y), ← box_occupation_ofReal_integral,
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => ENNReal.toReal_nonneg))]

/-- Integrate a pointwise generator estimate for a bounded compact test. -/
private lemma box_green_bound {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (hT : 0 < (T:ℝ)) (S : Set Z) (hS : MeasurableSet S)
    (f : Z → ℝ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (K e : ℝ) (hn : ∀ q, |f q| ≤ K)
    (hg : ∀ q, S.indicator (fun _ => (1:ℝ)) q ≤ physicalSpatialOperator A.a f q + e) :
    (physicalOccupationMeasure (fullSpaceEvolution hlam hLam A) z T).real S ≤ 2*K+T*e := by
  let E := fullSpaceEvolution hlam hLam A
  have hE := fullSpaceEvolution_spec hlam hLam A
  let μ := physicalOccupationMeasure E z T
  let : IsProbabilityMeasure (kernelXV E T z) := ⟨kernelXV_mass_one hlam A E hE T z⟩
  have hL := physicalSpatialOperator_occupation_integrable A f hf hc E z T
  have hh := integral_mono ((integrable_const (μ := μ) (1:ℝ)).indicator hS) (hL.add (integrable_const e)) hg
  change (∫ q, S.indicator (1 : Z → ℝ) q ∂μ) ≤ ∫ q, physicalSpatialOperator A.a f q + e ∂μ at hh
  have hm : μ.real univ = T := by rw [measureReal_def]; exact congrArg ENNReal.toReal (physicalOccupationMeasure_mass_eq hlam A E hE z T) |>.trans (ENNReal.toReal_ofReal hT.le)
  rw [integral_indicator_one hS,integral_add hL (integrable_const e),integral_const,
    smul_eq_mul,hm] at hh
  change μ.real S ≤ (∫ q, physicalSpatialOperator A.a f q ∂physicalOccupationMeasure E z T) + _ at hh
  rw [fullspace_physical_green_compact_c2 hlam hLam A E hE f hf hc z T hT] at hh
  have bound := norm_integral_le_of_norm_le_const (μ := kernelXV E T z) (f := f) (Filter.Eventually.of_forall hn)
  simp only [Real.norm_eq_abs,probReal_univ,mul_one] at bound
  linarith only [hh, le_abs_self (∫ x, f x ∂kernelXV E T z),bound,(abs_le.mp (hn z)).1]

/-- The literal source box occupation estimate, with its constant before all dynamic data. -/
theorem deterministic_box_occupation
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha)
    (ha1 : alpha < 1) (A0 M : ℝ) (hA0 : 0 < A0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (z : Z) (Y r : ℝ) (T : NNReal),
      0 < r → |z.2| ≤ M * Real.sqrt (T : ℝ) →
      (∫ t in Ioc 0 (T : ℝ),
        (kernelXV (fullSpaceEvolution hlam hLam A) (Real.toNNReal t) z
          (box A0 r Y)).toReal) ≤ C * r ^ (gamma alpha) * (T : ℝ) ^ (alpha / 2) := by
  obtain ⟨hlo,_,bar⟩ := exists_bellman_barrier lam Lam hlam hLam
  have ha0 := (sub_nonneg.mpr hlo).trans_lt ha
  obtain ⟨φ,c,h,hc,he⟩ := bar alpha ha ha1
  obtain ⟨B⟩ := BoxBarrier.exterior h ha0 ha1 hc he
  obtain ⟨C,hC,tests⟩ := BoxBarrier.compact_test B ha0 ha1 A0
  refine ⟨1+5*C,by positivity,fun A z Y r T hr _ => ?_⟩
  rw [box_integral_eq]
  let E := fullSpaceEvolution hlam hLam A
  let R := Real.sqrt (T:ℝ)
  have sq : R^2 = T := Real.sq_sqrt T.property
  have hg : 0 < gamma alpha := by unfold gamma; linarith
  have rat (s : ℝ) (hs : 0 < s) : s^(gamma alpha) * s^alpha = s^2 := by
    rw [← Real.rpow_add hs]; simp [gamma]
  have rt : R^alpha = (T:ℝ)^(alpha/2) := by rw [show R = (T:ℝ)^(1/2:ℝ) from Real.sqrt_eq_rpow _, ← Real.rpow_mul (x := (T:ℝ)) T.property (1/2) alpha]; ring_nf
  have c1 : 1 ≤ 1+5*C := by linarith
  have nc := Real.rpow_nonneg T.property (alpha/2)
  have mr : r^(gamma alpha) ≤ (1+5*C)*r^(gamma alpha) := le_mul_of_one_le_left (Real.rpow_nonneg hr.le _) c1
  have triv : (physicalOccupationMeasure E z T).real (box A0 r Y) ≤ T := by
    apply (measureReal_mono (subset_univ _)).trans_eq
    rw [measureReal_def,physicalOccupationMeasure_mass_eq hlam A E (fullSpaceEvolution_spec hlam hLam A)]; exact ENNReal.toReal_ofReal T.property
  by_cases hz : (T:ℝ) = 0
  · exact triv.trans (by rw [hz]; positivity)
  have ht := lt_of_le_of_ne T.property (Ne.symm hz)
  have hR : 0 < R := Real.sqrt_pos.mpr ht
  by_cases hrR : r ≤ R
  · let s := R/r
    have hs : 1 ≤ s := (one_le_div hr).mpr hrR
    have hs0 := zero_lt_one.trans_le hs
    obtain ⟨f,hf,hfC,hsize,hlower⟩ := tests r hr Y s hs
    have hi := box_green_bound hlam hLam A z T ht _ (box_measurable A0 r Y) f hf hfC _ _ hsize
      (fun q => hlower (A.a q.1 q.2) (A.bounds ..) q)
    have tm : (T:ℝ) = r^2*s^2 := by rw [← sq]; dsimp [s]; field_simp
    have pow : r^2 * s^alpha = r^(gamma alpha) * R^alpha := by
      rw [show R = r*s by dsimp [s]; field_simp,Real.mul_rpow hr.le hs0.le,← mul_assoc,rat _ hr]
    have loss : (T:ℝ)*s^(alpha-2) = r^2*s^alpha := by
      rw [tm,Real.rpow_sub hs0,Real.rpow_two]; field_simp
    calc
      _ ≤ 2*(2*C*r^2*s^alpha) + (T:ℝ)*(C*s^(alpha-2)) := hi
      _ = (5*C)*(r^(gamma alpha)*(T:ℝ)^(alpha/2)) := by rw [← rt,← pow]; linear_combination C*loss
      _ ≤ _ := by rw [← mul_assoc]; gcongr; linarith
  · apply triv.trans
    rw [← rt,← sq,← rat R hR]
    gcongr; exact (Real.rpow_le_rpow hR.le (le_of_not_ge hrR) hg.le).trans mr

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
