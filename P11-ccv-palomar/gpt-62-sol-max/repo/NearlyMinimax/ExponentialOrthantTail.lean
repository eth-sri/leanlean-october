module

public import NearlyMinimax.GammaTailBounds

@[expose] public section

/-! Genuine product-Lebesgue exponential tails on a finite orthant. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {ι : Type*} [Fintype ι]

def exponentialOrthantMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => volume.restrict (Ici (0 : ℝ)))

instance exponentialOrthantMeasure_sigmaFinite : SigmaFinite (exponentialOrthantMeasure ι) := by
  unfold exponentialOrthantMeasure
  infer_instance

def orthantExponential (b : ℝ) (s : ι → ℝ) : ℝ := Real.exp (-(b * ∑ j, s j))

def orthantHeadTail (b A : ℝ) (s : ι → ℝ) : ℝ :=
  Real.exp (-(b * max A (∑ j, s j))) / b

theorem exponential_orthant_measure_eq_restrict :
    exponentialOrthantMeasure ι = volume.restrict (Ici (0 : ι → ℝ)) := by
  have hs : Ici (0 : ι → ℝ) = Set.univ.pi (fun _ : ι => Ici (0 : ℝ)) := by
    ext s
    tauto
  rw [hs]
  exact (Measure.restrict_pi_pi (μ := fun _ : ι => (volume : Measure ℝ)) _).symm

theorem orthant_exponential_product (b : ℝ) (s : ι → ℝ) :
    orthantExponential b s = ∏ j, Real.exp (-(b * s j)) := by
  unfold orthantExponential
  simp [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]

section
variable {b : ℝ} (hb : 0 < b)
include hb

theorem scalar_exponential_integrable :
    IntegrableOn (fun v : ℝ => Real.exp (-(b * v))) (Ici 0) := by
  simpa only [pow_zero, one_mul] using gamma_monomial_integrable hb 0

theorem scalar_exponential_tail_integral (A : ℝ) :
    (∫ v : ℝ in Ici A, Real.exp (-(b * v))) = Real.exp (-(b * A)) / b := by
  rw [integral_Ici_eq_integral_Ioi]
  simpa [neg_mul] using integral_exp_mul_Ioi (neg_lt_zero.mpr hb) A

end

theorem orthant_exponential_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (orthantExponential b : (ι → ℝ) → ℝ) (exponentialOrthantMeasure ι) := by
  change Integrable (fun s : ι → ℝ => orthantExponential b s) (exponentialOrthantMeasure ι)
  simp_rw [orthant_exponential_product]
  exact Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (_ : ι) (v : ℝ) => Real.exp (-(b * v)))
    (μ := fun _ : ι => volume.restrict (Ici (0 : ℝ)))
    (fun _ => scalar_exponential_integrable hb)

section
variable {b : ℝ} (hb : 0 < b)
include hb

/-- Exact conditional integration of the distinguished orthant coordinate. -/
theorem orthant_head_tail_scalar_integral (A S : ℝ) :
    (∫ v : ℝ in Ici 0,
      (Ici (A - S)).indicator (fun v : ℝ => Real.exp (-(b * (v + S)))) v) =
      Real.exp (-(b * max A S)) / b := by
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.Ici_inter_Ici]
  have he : (fun v : ℝ => Real.exp (-(b * (v + S)))) =
      fun v => Real.exp (-(b * S)) * Real.exp (-(b * v)) := by
    funext v
    simp [← Real.exp_add] <;> ring
  rw [he, integral_const_mul, scalar_exponential_tail_integral hb, div_eq_mul_inv, ← mul_assoc, ← Real.exp_add] <;> grind

theorem orthant_head_tail_le_exponential (A : ℝ) (s : ι → ℝ) :
    orthantHeadTail b A s ≤ orthantExponential b s / b := by
  unfold orthantHeadTail orthantExponential
  apply div_le_div_of_nonneg_right _ hb.le
  simp_all

end

theorem orthant_head_tail_integrable {b : ℝ} (hb : 0 < b) (A : ℝ) :
    Integrable (orthantHeadTail b A : (ι → ℝ) → ℝ) (exponentialOrthantMeasure ι) := by
  have hcont : Continuous (orthantHeadTail b A : (ι → ℝ) → ℝ) :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.max (continuous_finsetSum _ fun j _ => continuous_apply j))).neg).div_const b
  exact ((orthant_exponential_integrable hb).div_const b).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold orthantHeadTail; positivity)]
      exact orthant_head_tail_le_exponential hb A s)

/-- The cube part of the orthant has its actual product Lebesgue volume. -/
theorem orthant_cube_indicator_integrable (A C : ℝ) :
    Integrable ((Icc (0 : ι → ℝ) (fun _ => A)).indicator (fun _ => C))
      (exponentialOrthantMeasure ι) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  rw [IntegrableOn, exponential_orthant_measure_eq_restrict,
    Measure.restrict_restrict_of_subset (fun _ hs => hs.1)]
  exact integrableOn_const (isCompact_Icc.measure_lt_top.ne)

theorem orthant_cube_indicator_integral {A : ℝ} (hA : 0 ≤ A) (C : ℝ) :
    (∫ s : ι → ℝ, (Icc (0 : ι → ℝ) (fun _ => A)).indicator (fun _ => C) s
      ∂exponentialOrthantMeasure ι) = A ^ Fintype.card ι * C := by
  rw [integral_indicator measurableSet_Icc, exponential_orthant_measure_eq_restrict,
    Measure.restrict_restrict_of_subset (fun _ hs => hs.1), integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  have hvol := Real.volume_Icc_pi_toReal (a := (0 : ι → ℝ)) (b := fun _ => A)
    (fun _ => hA)
  simp [hvol]

/-- The product Laplace transform of orthant volume. -/
theorem orthant_exponential_integral {b : ℝ} (hb : 0 < b) :
    (∫ s : ι → ℝ, orthantExponential b s ∂exponentialOrthantMeasure ι) =
      (1 / b) ^ Fintype.card ι := by
  simp_rw [orthant_exponential_product, exponentialOrthantMeasure]
  rw [integral_fintype_prod_eq_prod (fun (_ : ι) (v : ℝ) => Real.exp (-(b * v))),
    show (∫ v : ℝ in Ici 0, Real.exp (-(b * v))) = 1 / b by
      simpa using scalar_exponential_tail_integral hb 0]
  simp

/-- A rate of order `1/(1+A)` dominates the conditional tail simultaneously
on both sides of its kink, with only one power per remaining coordinate. -/
theorem orthant_head_tail_integral_uniform {b A : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ s : ι → ℝ, orthantHeadTail b A s ∂exponentialOrthantMeasure ι) ≤
      8 ^ (Fintype.card ι + 1) * Real.exp (-(b * A)) * (1 + A) ^ Fintype.card ι := by
  let r := 1 / (2 * (1 + A))
  have hb0 : 0 < b := by positivity
  have hr : 0 < r := by positivity
  have hr2 : r ≤ 1/2 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hscale : r * A ≤ 1/2 := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  have he : Real.exp (r*A) ≤ 2 := by
    refine (Real.exp_le_exp.mpr hscale).trans ?_
    have h := Real.exp_le_two_add_div_two_sub (x := (1:ℝ)/2) (by norm_num) (by norm_num)
    linarith
  let k := Real.exp (-(b*A)) * (Real.exp (r*A) / b)
  have h := integral_mono (orthant_head_tail_integrable hb0 A)
    ((orthant_exponential_integrable (ι := ι) hr).const_mul k)
    (fun s => show orthantHeadTail b A s ≤ k * orthantExponential r s from by
      unfold orthantHeadTail orthantExponential k
      rw [show Real.exp (-(b*A)) * (Real.exp (r*A) / b) * Real.exp (-(r*∑ j, s j)) =
          Real.exp (-(b*A) + r*A - r * ∑ j, s j) / b by
        simp only [sub_eq_add_neg, Real.exp_add]
        ring]
      apply (div_le_div_iff_of_pos_right hb0).2
      apply Real.exp_le_exp.2
      have hs := mul_nonneg (sub_nonneg.mpr (hr2.trans hb)) (sub_nonneg.mpr (le_max_left A (∑ j, s j)))
      have ht := mul_nonneg hr.le (sub_nonneg.mpr (le_max_right A (∑ j, s j)))
      nlinarith)
  rw [integral_const_mul, orthant_exponential_integral hr] at h
  refine h.trans ?_
  have hk : Real.exp (r*A) / b ≤ 4 := (div_le_iff₀ hb0).2 (by linarith)
  have hpow : (2:ℝ)^Fintype.card ι ≤ 8^Fintype.card ι := by gcongr <;> norm_num
  calc
    _ ≤ Real.exp (-(b*A)) * 4 * (2*(1+A))^Fintype.card ι := by
      have heq : 1 / r = 2 * (1+A) := by simp [r]
      rw [heq]
      dsimp [k]
      gcongr
    _ ≤ _ := by
      rw [mul_pow, pow_succ]
      calc
        _ = (4 * (2:ℝ)^Fintype.card ι) * Real.exp (-(b*A)) * (1+A)^Fintype.card ι := by ring
        _ ≤ _ := by
          have hnum := mul_le_mul hpow (show (4:ℝ) ≤ 8 by norm_num) (by norm_num) (by positivity)
          rw [mul_comm (4:ℝ)]
          gcongr

/-- The actual tail integrand on a distinguished coordinate and a finite
vector of further coordinates. -/
def orthantSumTail (b A : ℝ) (z : ℝ × (ι → ℝ)) : ℝ :=
  if A ≤ z.1 + ∑ j, z.2 j then Real.exp (-(b * (z.1 + ∑ j, z.2 j))) else 0

section
variable {b : ℝ} (hb : 0 < b) (A : ℝ)
include hb

theorem orthant_sum_tail_integrable :
    Integrable (orthantSumTail b A : (ℝ × (ι → ℝ)) → ℝ)
      ((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure ι)) := by
  have hbase := (scalar_exponential_integrable hb).mul_prod (orthant_exponential_integrable (ι := ι) hb)
  have he : (fun z : ℝ × (ι → ℝ) => Real.exp (-(b * z.1)) * orthantExponential b z.2) =
      fun z => Real.exp (-(b * (z.1 + ∑ j, z.2 j))) := by
    funext z
    unfold orthantExponential
    simp [← Real.exp_add] <;> ring
  rw [he] at hbase
  have hmeas : MeasurableSet {z : ℝ × (ι → ℝ) | A ≤ z.1 + ∑ j, z.2 j} :=
    measurableSet_le measurable_const
      (measurable_fst.add (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd))
  convert hbase.indicator hmeas using 1
  rfl

theorem orthant_sum_tail_integral_eq :
    (∫ z : ℝ × (ι → ℝ), orthantSumTail b A z
      ∂((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure ι))) =
      ∫ s : ι → ℝ, orthantHeadTail b A s ∂exponentialOrthantMeasure ι := by
  rw [integral_prod_symm _ (orthant_sum_tail_integrable hb A)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    have he : (fun v : ℝ => orthantSumTail b A (v, s)) =
        fun v => (Ici (A - ∑ j, s j)).indicator
          (fun v : ℝ => Real.exp (-(b * (v + ∑ j, s j)))) v := by
      funext v
      have hh : A ≤ v + ∑ j, s j ↔ A - ∑ j, s j ≤ v := by simp
      simp only [orthantSumTail, Set.indicator, mem_Ici, hh]
    dsimp only
    rw [he, orthant_head_tail_scalar_integral hb]
    rfl

end

section
variable {m : ℕ}

/-- Separate the first coordinate before integrating a function of the sum. -/
abbrev orthantSplit (m : ℕ) := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm

theorem orthantSplit_preserving : MeasurePreserving (orthantSplit m)
    ((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m)))
    (exponentialOrthantMeasure (Fin (m + 1))) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => volume.restrict (Ici (0 : ℝ))) 0).symm

section
variable (f : ℝ → ℝ)

theorem orthant_sum_split_integral :
    (∫ s : Fin (m + 1) → ℝ, f (∑ j, s j) ∂exponentialOrthantMeasure (Fin (m + 1))) =
      ∫ z : ℝ × (Fin m → ℝ), f (z.1 + ∑ j, z.2 j)
        ∂((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))) := by
  simp [← (orthantSplit_preserving (m := m)).integral_comp']

theorem orthant_sum_split_integrable :
    Integrable (fun s : Fin (m + 1) → ℝ => f (∑ j, s j)) (exponentialOrthantMeasure (Fin (m + 1))) ↔
      Integrable (fun z : ℝ × (Fin m → ℝ) => f (z.1 + ∑ j, z.2 j))
        ((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))) := by
  simpa [Function.comp_def] using
    ((orthantSplit_preserving (m := m)).integrable_comp_emb (orthantSplit m).measurableEmbedding
      (g := fun s : Fin (m + 1) → ℝ => f (∑ j, s j))).symm

end

/-- The simplex tail written directly in the original finite vector space. -/
def finiteOrthantTail {q : ℕ} (b A : ℝ) (s : Fin q → ℝ) : ℝ :=
  if A ≤ ∑ j, s j then Real.exp (-(b * ∑ j, s j)) else 0

theorem finite_orthant_tail_integrable {b : ℝ} (hb : 0 < b) (A : ℝ) :
    Integrable (finiteOrthantTail b A : (Fin (m + 1) → ℝ) → ℝ)
      (exponentialOrthantMeasure (Fin (m + 1))) :=
  (orthant_sum_split_integrable (fun t => if A ≤ t then Real.exp (-(b*t)) else 0)).2
    (orthant_sum_tail_integrable hb A)

theorem finite_orthant_tail_integral_uniform {b A : ℝ}
    (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ s : Fin (m + 1) → ℝ, finiteOrthantTail b A s
      ∂exponentialOrthantMeasure (Fin (m + 1))) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  have h := orthant_sum_split_integral (m := m) (fun t => if A ≤ t then Real.exp (-(b*t)) else 0)
  change (∫ s : Fin (m + 1) → ℝ, finiteOrthantTail b A s ∂_) = ∫ z, orthantSumTail b A z ∂_ at h
  rw [h, orthant_sum_tail_integral_eq (by linarith : 0 < b)]
  simpa using orthant_head_tail_integral_uniform (ι := Fin m) hb hA

end
end NearlyMinimax
