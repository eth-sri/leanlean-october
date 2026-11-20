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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def exponentialOrthantMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => volume.restrict (Ici (0 : ℝ)))

instance exponentialOrthantMeasure_sigmaFinite : SigmaFinite (exponentialOrthantMeasure ι) := by
  unfold exponentialOrthantMeasure
  infer_instance

section
variable (b A : ℝ) (s : ι → ℝ)

def orthantExponential : ℝ := Real.exp (-(b * ∑ j, s j))

def orthantHeadTail : ℝ :=
  Real.exp (-(b * max A (∑ j, s j))) / b

def orthantCoordinateTail (j : ι) (s : ι → ℝ) : ℝ :=
  ∏ l, if l = j then (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) (s l)
    else Real.exp (-(b * s l))

end

theorem exponential_orthant_measure_eq_restrict :
    exponentialOrthantMeasure ι = volume.restrict (Ici (0 : ι → ℝ)) := by
  have hs : Ici 0 = Set.univ.pi (fun _ : ι => Ici (0 : ℝ)) := by
    ext s
    aesop
  rw [hs]
  exact (Measure.restrict_pi_pi (μ := fun _ : ι => volume) _).symm

theorem orthant_exponential_product (b : ℝ) (s : ι → ℝ) :
    orthantExponential b s = ∏ j, Real.exp (-(b * s j)) := by
  unfold orthantExponential
  rw [← Real.exp_sum]
  rw [Finset.mul_sum, Finset.sum_neg_distrib]

section
variable {b A : ℝ} (hb : 0 < b) (hA : 0 ≤ A) (j : ι)
include hb

theorem scalar_exponential_integrable :
    IntegrableOn (fun v : ℝ => Real.exp (-(b * v))) (Ici 0) := by
  simpa using gamma_monomial_integrable hb 0

theorem scalar_exponential_tail_integral (A : ℝ) :
    (∫ v : ℝ in Ici A, Real.exp (-(b * v))) = Real.exp (-(b * A)) / b := by
  simpa [div_eq_mul_inv] using gamma_polynomial_tail_integral hb A 0

include hA in
theorem scalar_exponential_indicator_integral :
    (∫ v : ℝ in Ici 0, (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v) =
      Real.exp (-(b * A)) / b := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hs : Ioi A ∩ Ici (0 : ℝ) = Ioi A := by
    grind
  rw [hs, ← integral_Ici_eq_integral_Ioi, scalar_exponential_tail_integral hb]

theorem orthant_exponential_integrable :
    Integrable (orthantExponential b : (ι → ℝ) → ℝ) (exponentialOrthantMeasure ι) := by
  change Integrable (fun s : ι → ℝ => orthantExponential b s) (exponentialOrthantMeasure ι)
  simp_rw [orthant_exponential_product]
  exact Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (_ : ι) (v : ℝ) => Real.exp (-(b * v)))
    (μ := fun _ : ι => volume.restrict (Ici (0 : ℝ)))
    (fun _ => scalar_exponential_integrable hb)

theorem orthant_coordinate_tail_integrable :
    Integrable (orthantCoordinateTail b A j) (exponentialOrthantMeasure ι) := by
  exact Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (l : ι) (v : ℝ) => if l = j then
      (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v else Real.exp (-(b * v)))
    (μ := fun _ : ι => volume.restrict (Ici (0 : ℝ))) (fun l => by
      split_ifs
      · exact (scalar_exponential_integrable hb).indicator measurableSet_Ioi
      · exact scalar_exponential_integrable hb)

include hA in
theorem orthant_coordinate_tail_integral :
    let expScale := Real.exp (-(b * A))
    (∫ s : ι → ℝ, orthantCoordinateTail b A j s ∂exponentialOrthantMeasure ι) =
      expScale / b ^ Fintype.card ι := by
  intro expScale
  unfold orthantCoordinateTail exponentialOrthantMeasure
  rw [integral_fintype_prod_eq_prod (fun (l : ι) (v : ℝ) => if l = j then
    (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v else Real.exp (-(b * v)))]
  have he : (fun l : ι => ∫ v : ℝ in Ici 0,
      if l = j then (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v
      else Real.exp (-(b * v))) =
      fun l => if l = j then expScale / b else 1 / b := by
    funext l
    split_ifs
    · exact scalar_exponential_indicator_integral hb hA
    · simpa using scalar_exponential_tail_integral hb (0 : ℝ)
  rw [he, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [ite_true]
  have hp : (∏ l ∈ Finset.univ.erase j,
      if l = j then expScale / b else 1 / b) =
      (1 / b) ^ (Fintype.card ι - 1) := by
    calc
      _ = _ := by
        apply Finset.prod_congr rfl
        aesop
      _ = _ := by simp
  rw [hp]
  have hc  := Fintype.card_pos_iff.mpr ⟨j⟩
  have hn : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  have hpow : b ^ Fintype.card ι = b ^ (Fintype.card ι - 1) * b := by
    conv_lhs => rw [hn]
    rfl
  rw [hpow, div_pow, one_pow]
  field_simp

end

section
variable {b : ℝ} (hb : 0 < b) (A S C : ℝ)

include hb in
/-- Exact conditional integration of the distinguished orthant coordinate. -/
theorem orthant_head_tail_scalar_integral :
    (∫ v : ℝ in Ici 0,
      (Ici (A - S)).indicator (fun v : ℝ => Real.exp (-(b * (v + S)))) v) =
      Real.exp (-(b * max A S)) / b := by
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.Ici_inter_Ici]
  have he : (fun v : ℝ => Real.exp (-(b * (v + S)))) =
      fun v => Real.exp (-(b * S)) * Real.exp (-(b * v)) := by
    funext v
    rw [← Real.exp_add]
    ring
  rw [he, integral_const_mul, scalar_exponential_tail_integral hb]
  rw [div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]
  grind

include hb in
theorem orthant_head_tail_le_constant (s : ι → ℝ) :
    orthantHeadTail b A s ≤ Real.exp (-(b * A)) / b := by
  apply div_le_div_of_nonneg_right _ hb.le
  bound

include hb in
theorem orthant_head_tail_le_exponential (s : ι → ℝ) :
    orthantHeadTail b A s ≤ orthantExponential b s / b := by
  apply div_le_div_of_nonneg_right _ hb.le
  apply Real.exp_le_exp.mpr
  have h := le_max_right A (∑ j, s j)
  nlinarith

theorem orthant_coordinate_tail_nonnegative (b A : ℝ) (j : ι) (s : ι → ℝ) :
    0 ≤ orthantCoordinateTail b A j s := by
  apply Finset.prod_nonneg
  intro l _
  split_ifs
  · exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
  · positivity

theorem orthant_coordinate_tail_eq_exponential {A : ℝ} {j : ι} {s : ι → ℝ}
    (hsj : A < s j) : orthantCoordinateTail b A j s = orthantExponential b s := by
  rw [orthant_exponential_product]
  apply Finset.prod_congr rfl
  aesop

include hb in
theorem orthant_head_tail_integrable :
    Integrable (orthantHeadTail b A : (ι → ℝ) → ℝ) (exponentialOrthantMeasure ι) := by
  have hcont : Continuous (orthantHeadTail b A : (ι → ℝ) → ℝ) :=
    (Real.continuous_exp.comp (continuous_const.mul
      (by fun_prop)).neg).div_const b
  exact ((orthant_exponential_integrable hb).div_const b).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold orthantHeadTail; positivity)]
      exact orthant_head_tail_le_exponential hb A s)

/-- The cube part of the orthant has its actual product Lebesgue volume. -/
theorem orthant_cube_indicator_integrable :
    Integrable ((Icc (0 : ι → ℝ) (fun _ => A)).indicator (fun _ => C))
      (exponentialOrthantMeasure ι) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  rw [IntegrableOn, exponential_orthant_measure_eq_restrict,
    Measure.restrict_restrict_of_subset (fun _ hs => hs.1)]
  exact integrableOn_const (isCompact_Icc.measure_lt_top.ne)

end

theorem orthant_cube_indicator_integral {A : ℝ} (hA : 0 ≤ A) (C : ℝ) :
    (∫ s : ι → ℝ, (Icc (0 : ι → ℝ) (fun _ => A)).indicator (fun _ => C) s
      ∂exponentialOrthantMeasure ι) = A ^ Fintype.card ι * C := by
  rw [integral_indicator measurableSet_Icc, exponential_orthant_measure_eq_restrict,
    Measure.restrict_restrict_of_subset (fun _ hs => hs.1), integral_const]
  simp [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  have hvol := Real.volume_Icc_pi_toReal (a := (0 : ι → ℝ)) (b := fun _ => A)
    (fun _ => hA)
  rw [hvol]
  simp

variable {m : ℕ} {b A : ℝ} (hb : 0 < b) (hA : 0 ≤ A)

include hb hA in
/-- Actual product-measure tail bound. One coordinate is integrated exactly;
inside the remaining cube the conditional integral is constant-bounded, and
outside it a finite union of scalar exponential tails suffices. -/
theorem orthant_head_tail_integral_le :
    (∫ s : ι → ℝ, orthantHeadTail b A s ∂exponentialOrthantMeasure ι) ≤
      Real.exp (-(b * A)) *
        (A ^ Fintype.card ι / b + (Fintype.card ι : ℝ) / b ^ (Fintype.card ι + 1)) := by
  let cube := Icc (0 : ι → ℝ) (fun _ => A)
  let G := fun s : ι → ℝ => cube.indicator (fun _ => Real.exp (-(b * A)) / b) s +
    (1 / b) * ∑ j, orthantCoordinateTail b A j s
  have hG : Integrable G (exponentialOrthantMeasure ι) :=
    (orthant_cube_indicator_integrable A _).add
      ((integrable_finsetSum _ fun j _ => orthant_coordinate_tail_integrable hb j).const_mul _)
  have hae : ∀ᵐ s ∂exponentialOrthantMeasure ι, s ∈ Ici 0 := by
    rw [exponential_orthant_measure_eq_restrict]
    exact ae_restrict_mem measurableSet_Ici
  have hdom : (orthantHeadTail b A : (ι → ℝ) → ℝ) ≤ᵐ[exponentialOrthantMeasure ι] G := by
    filter_upwards [hae] with s hs
    have hsum : 0 ≤ ∑ j, orthantCoordinateTail b A j s :=
      Finset.sum_nonneg fun j _ => orthant_coordinate_tail_nonnegative b A j s
    by_cases hcube : s ∈ cube
    · simp only [G, Set.indicator_of_mem hcube]
      have h := orthant_head_tail_le_constant hb A s
      nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / b) hsum]
    · have hex : ∃ j, A < s j := by
        by_contra h
        apply hcube
        refine ⟨hs, ?_⟩
        intro j
        exact le_of_not_gt (fun hj => h ⟨j, hj⟩)
      obtain ⟨j, hj⟩ := hex
      have hterm  :=
        Finset.single_le_sum (fun l _ => orthant_coordinate_tail_nonnegative b A l s)
          (Finset.mem_univ j)
      rw [orthant_coordinate_tail_eq_exponential hj] at hterm
      simp [G, Set.indicator_of_notMem hcube, zero_add]
      have h := orthant_head_tail_le_exponential hb A s
      have hm := mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ 1 / b)
      calc
        _ ≤ _ := h
        _ ≤ _ := by convert hm using 1 <;> ring
  have h := integral_mono_ae (orthant_head_tail_integrable hb A) hG hdom
  dsimp [G] at h
  rw [integral_add (orthant_cube_indicator_integrable A _)
    ((integrable_finsetSum _ fun j _ => orthant_coordinate_tail_integrable hb j).const_mul _),
    orthant_cube_indicator_integral hA, integral_const_mul,
    integral_finsetSum _ (fun j _ => orthant_coordinate_tail_integrable hb j)] at h
  simp_rw [orthant_coordinate_tail_integral hb hA] at h
  simp at h
  convert h using 1 <;> rw [pow_succ] <;> ring

/-- The actual tail integrand on a distinguished coordinate and a finite
vector of further coordinates. -/
def orthantSumTail (b A : ℝ) (z : ℝ × (ι → ℝ)) : ℝ :=
  if A ≤ z.1 + ∑ j, z.2 j then Real.exp (-(b * (z.1 + ∑ j, z.2 j))) else 0

include hb in
theorem orthant_sum_tail_integrable (A : ℝ) :
    Integrable (orthantSumTail b A : (ℝ × (ι → ℝ)) → ℝ)
      ((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure ι)) := by
  have hbase := (scalar_exponential_integrable hb).mul_prod (orthant_exponential_integrable (ι := ι) hb)
  have he : (fun z : ℝ × (ι → ℝ) => Real.exp (-(b * z.1)) * orthantExponential b z.2) =
      fun z => Real.exp (-(b * (z.1 + ∑ j, z.2 j))) := by
    funext z
    unfold orthantExponential
    rw [← Real.exp_add]
    ring
  rw [he] at hbase
  have hmeas : MeasurableSet {z : ℝ × (ι → ℝ) | A ≤ z.1 + ∑ j, z.2 j} :=
    measurableSet_le measurable_const
      (by fun_prop)
  convert hbase.indicator hmeas using 1
  rfl

include hb in
theorem orthant_sum_tail_integral_eq (A : ℝ) :
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
    dsimp
    rw [he, orthant_head_tail_scalar_integral hb]
    rfl

include hb hA in
theorem orthant_sum_tail_integral_le :
    (∫ z : ℝ × (ι → ℝ), orthantSumTail b A z
      ∂((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure ι))) ≤
      Real.exp (-(b * A)) *
        (A ^ Fintype.card ι / b + (Fintype.card ι : ℝ) / b ^ (Fintype.card ι + 1)) := by
  rw [orthant_sum_tail_integral_eq hb]
  exact orthant_head_tail_integral_le hb hA

private theorem nat_add_two_le_four_pow (m : ℕ) : (m : ℝ) + 2 ≤ (4 : ℝ) ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.cast_succ, show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ]
    nlinarith

/-- Uniform scale-simplex tail bound with the correct polynomial degree:
there is one fewer polynomial power than there are coordinates. -/
theorem orthant_sum_tail_integral_uniform (hb : (1 / 2 : ℝ) ≤ b)
    (hA : 0 ≤ A) :
    (∫ z : ℝ × (ι → ℝ), orthantSumTail b A z
      ∂((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure ι))) ≤
      8 ^ (Fintype.card ι + 1) * Real.exp (-(b * A)) * (1 + A) ^ Fintype.card ι := by
  have hbpos : 0 < b := by positivity
  have hinv : 1 / b ≤ (2 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb
  have hpow : (1 / b) ^ (Fintype.card ι + 1) ≤ (2 : ℝ) ^ (Fintype.card ι + 1) :=
    by bound
  have htwo : (2 : ℝ) ≤ 2 ^ (Fintype.card ι + 1) := by
    bound
  have hAone : 1 ≤ (1 + A) ^ Fintype.card ι := one_le_pow₀ (by linarith)
  have hApow : A ^ Fintype.card ι ≤ (1 + A) ^ Fintype.card ι :=
    by bound
  have hfirst : A ^ Fintype.card ι / b ≤
      2 ^ (Fintype.card ι + 1) * (1 + A) ^ Fintype.card ι := by
    have h := mul_le_mul hApow (hinv.trans htwo) (by positivity : 0 ≤ 1 / b)
      (by positivity : 0 ≤ (1 + A) ^ Fintype.card ι)
    convert h using 1 <;> ring
  have hsecond : (Fintype.card ι : ℝ) / b ^ (Fintype.card ι + 1) ≤
      (Fintype.card ι : ℝ) * 2 ^ (Fintype.card ι + 1) * (1 + A) ^ Fintype.card ι := by
    have h := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
    have hh := mul_le_mul_of_nonneg_left hAone
      (by positivity : 0 ≤ (Fintype.card ι : ℝ) * 2 ^ (Fintype.card ι + 1))
    rw [div_pow, one_pow] at h
    grind
  have hconst : ((Fintype.card ι : ℝ) + 1) * 2 ^ (Fintype.card ι + 1) ≤
      (8 : ℝ) ^ (Fintype.card ι + 1) := by
    have h := mul_le_mul_of_nonneg_right (nat_add_two_le_four_pow (Fintype.card ι))
      (by positivity : 0 ≤ (2 : ℝ) ^ (Fintype.card ι + 1))
    rw [← mul_pow] at h
    norm_num only at h
    nlinarith
  have hsum : A ^ Fintype.card ι / b + (Fintype.card ι : ℝ) / b ^ (Fintype.card ι + 1) ≤
      8 ^ (Fintype.card ι + 1) * (1 + A) ^ Fintype.card ι := by
    nlinarith
  have h := mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg (-(b * A)))
  calc
    _ ≤ _ := orthant_sum_tail_integral_le hbpos hA
    _ ≤ _ := by convert h using 1 <;> ring

/-- Splitting off the first coordinate of an orthant preserves both
integrability and the integral of any function of the coordinate sum. -/
theorem orthant_sum_split {m : ℕ} (f : ℝ → ℝ) :
    let g := fun s : Fin (m+1) → ℝ => f (∑ i, s i)
    let h := fun z : ℝ × (Fin m → ℝ) => f (z.1 + ∑ i, z.2 i)
    let μ := exponentialOrthantMeasure (Fin (m+1))
    let ν := (volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))
    (Integrable h ν ↔ Integrable g μ) ∧ (∫ s, g s ∂μ) = ∫ z, h z ∂ν := by
  intro g h μ ν
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
  have hp : MeasurePreserving e ν μ :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => volume.restrict (Ici (0 : ℝ))) 0).symm
  have he : g ∘ e = h := by
    funext z
    simp [g, h, e, Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.sum_univ_succ]
  rw [← he]
  exact ⟨hp.integrable_comp_emb e.measurableEmbedding, (hp.integral_comp e.measurableEmbedding g).symm⟩

/-- The simplex tail written directly in the original finite vector space. -/
def finiteOrthantTail {q : ℕ} (b A : ℝ) (s : Fin q → ℝ) : ℝ :=
  if A ≤ ∑ j, s j then Real.exp (-(b * ∑ j, s j)) else 0

theorem finite_orthant_tail_split_integral (b A : ℝ) :
    (∫ s : Fin (m + 1) → ℝ, finiteOrthantTail b A s
      ∂exponentialOrthantMeasure (Fin (m + 1))) =
      ∫ z : ℝ × (Fin m → ℝ), orthantSumTail b A z
      ∂((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))) :=
  (orthant_sum_split (fun t => if A ≤ t then Real.exp (-(b*t)) else 0)).2

include hb in
theorem finite_orthant_tail_integrable (A : ℝ) :
    Integrable (finiteOrthantTail b A : (Fin (m + 1) → ℝ) → ℝ)
      (exponentialOrthantMeasure (Fin (m + 1))) :=
  (orthant_sum_split (fun t => if A ≤ t then Real.exp (-(b*t)) else 0)).1.mp (orthant_sum_tail_integrable hb A)

end NearlyMinimax
