module

public import Mathlib

@[expose] public section

/-! Independent fair signs attached to the cells of a finite random partition.
The sign law and all of its moments are constructed here, rather than assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def fairSignValue (b : Fin 2) : ℝ := if b = 0 then 1 else -1

def fairSignLaw : Measure (Fin 2) :=
  ENNReal.ofReal (1 / 2) • Measure.dirac 0 +
    ENNReal.ofReal (1 / 2) • Measure.dirac 1

instance fairSignLaw_probability : IsProbabilityMeasure fairSignLaw := by
  constructor
  change (fairSignLaw Set.univ) = 1
  simp only [fairSignLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem fairSign_integral (f : Fin 2 → ℝ) :
    (∫ b, f b ∂fairSignLaw) = (f 0 + f 1) / 2 := by
  unfold fairSignLaw
  rw [integral_add_measure]
  · norm_num <;> linarith
  · apply MeasureTheory.Integrable.smul_measure_nnreal <;> fun_prop
  · apply MeasureTheory.Integrable.smul_measure_nnreal <;> fun_prop

theorem fairSignValue_abs (b : Fin 2) : |fairSignValue b| = 1 := by
  fin_cases b <;> norm_num [fairSignValue]

theorem fairSignValue_sq (b : Fin 2) : fairSignValue b ^ 2 = 1 := by
  fin_cases b <;> norm_num [fairSignValue]

theorem fairSign_mean : (∫ b, fairSignValue b ∂fairSignLaw) = 0 := by
  rw [fairSign_integral]
  norm_num [fairSignValue]

theorem fairSign_power_moment (k : ℕ) :
    (∫ b, fairSignValue b ^ k ∂fairSignLaw) = if Even k then 1 else 0 := by
  rw [fairSign_integral]
  simp [fairSignValue]
  aesop

section
variable (I : Type*) [Fintype I]

def cellSignLaw : Measure (I → Fin 2) :=
  Measure.pi (fun _ => fairSignLaw)

instance cellSignLaw_probability :
    IsProbabilityMeasure (cellSignLaw I) := by
  unfold cellSignLaw
  infer_instance

end

variable {I J : Type*} [Fintype I]

theorem cellSign_mean (i : I) :
    (∫ b, fairSignValue (b i) ∂cellSignLaw I) = 0 := by
  exact id (Eq.mpr (id (congrArg (fun _a => _a = 0) (integral_comp_eval AEStronglyMeasurable.of_discrete))) fairSign_mean)

theorem cellSign_covariance [DecidableEq I] (i j : I) :
    (∫ b, fairSignValue (b i) * fairSignValue (b j) ∂cellSignLaw I) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl, ← pow_two, fairSignValue_sq]
    simp
  · have hi : IndepFun (fun b => b i) (fun b => b j)
        (cellSignLaw I) := (iIndepFun_pi (fun _ => measurable_id.aemeasurable)).indepFun hij
    rw [hi.integral_fun_comp_mul_comp (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable Measurable.of_discrete.aestronglyMeasurable
      Measurable.of_discrete.aestronglyMeasurable]
    simp [cellSign_mean, hij]

theorem cellSign_product_power_moment (k : I → ℕ) :
    (∫ b, ∏ i, fairSignValue (b i) ^ k i ∂cellSignLaw I) =
      ∏ i, if Even (k i) then 1 else 0 := by
  change (∫ b, ∏ i, fairSignValue (b i) ^ k i
    ∂Measure.pi (fun _ => fairSignLaw)) = _
  rw [integral_fintype_prod_eq_prod (fun i b => fairSignValue b ^ k i)]
  simp_rw [fairSign_power_moment]

theorem cellSign_product_moment [Fintype J]
    [DecidableEq I] (p : J → I) :
    (∫ b, ∏ j, fairSignValue (b (p j)) ∂cellSignLaw I) =
      if ∀ i, Even ((Finset.univ.filter (fun j => p j = i)).card) then 1 else 0 := by
  classical
  have he (b : I → Fin 2) : (∏ j, fairSignValue (b (p j))) =
      ∏ i, fairSignValue (b i) ^ (Finset.univ.filter (fun j => p j = i)).card := by
    rw [← Finset.prod_fiberwise_of_maps_to' (fun _ _ => Finset.mem_univ _) (fun i => fairSignValue (b i))]
    simp
  simp_rw [he]
  rw [cellSign_product_power_moment, Fintype.prod_boole]

end NearlyMinimax
