module

public import NearlyMinimax.FinitePartitionMoments
public import NearlyMinimax.ObservationMoments
public import NearlyMinimax.PairUStatistic

@[expose] public section

/-! Fourth-moment and row-localization estimates for the actual same-cell
pair-difference score. Responses are allowed to be unbounded. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

section Partition
variable {X B : Type*} [MeasurableSpace X] [Fintype B] [MeasurableSpace B]
  [MeasurableSingletonClass B] [MeasurableEq B]
  (μ : Measure X) [IsProbabilityMeasure μ] (label : X → B) (hlabel : Measurable label)
include hlabel

def labelLocalizedKernel (g : X → ℝ) (z : X × X) : ℝ :=
  if label z.1 = label z.2 then g z.2 else 0

theorem labelLocalizedKernel_integrable (g : X → ℝ) (hg : Integrable g μ) :
    Integrable (labelLocalizedKernel label g) (μ.prod μ) := by
  exact (hg.comp_snd μ).indicator
      (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))

omit hlabel in
theorem labelLocalizedKernel_row (g : X → ℝ) (x : X) :
    (∫ y, labelLocalizedKernel label g (x, y) ∂μ) =
      ∫ y, (label ⁻¹' {label x}).indicator g y ∂μ := by
  congr 1
  funext y
  simp [labelLocalizedKernel, Set.indicator_apply, eq_comm]

theorem partition_mass_integrable :
    Integrable (fun x => μ.real (label ⁻¹' {label x})) μ := by
  have hm :=
    (measurable_of_countable (fun c : B => μ.real (label ⁻¹' {c}))).comp hlabel
  apply (MemLp.of_bound hm.aestronglyMeasurable 1 (p := 1) ?_).integrable (by norm_num)
  simp [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]

section
variable (g : X → ℝ) (hg : Integrable g μ)
include hg

theorem labelLocalizedKernel_integral_le
    (M : ℝ) (hloc : ∀ c : B,
      (∫ x, (label ⁻¹' {c}).indicator g x ∂μ) ≤ M * μ.real (label ⁻¹' {c})) :
    (∫ z, labelLocalizedKernel label g z ∂μ.prod μ) ≤
      M * ∑ c : B, μ.real (label ⁻¹' {c}) ^ 2 := by
  rw [integral_prod _ (labelLocalizedKernel_integrable μ label hlabel g hg)]
  simp_rw [labelLocalizedKernel_row μ label g]
  have hi := (labelLocalizedKernel_integrable μ label hlabel g hg).integral_prod_left
  simp_rw [labelLocalizedKernel_row μ label g] at hi
  calc
    _ ≤ ∫ x, M * μ.real (label ⁻¹' {label x}) ∂μ := by
      apply integral_mono hi ((partition_mass_integrable μ label hlabel).const_mul M)
      tauto
    _ = _ := by
      rw [integral_const_mul,
        finite_label_integral μ label hlabel (fun c => μ.real (label ⁻¹' {c}))]
      ring

theorem labelLocalizedKernel_integral :
    (∫ z, labelLocalizedKernel label g z ∂μ.prod μ) =
      ∑ c : B, μ.real (label ⁻¹' {c}) *
        (∫ x, (label ⁻¹' {c}).indicator g x ∂μ) := by
  simpa [integral_prod _ (labelLocalizedKernel_integrable μ label hlabel g hg), labelLocalizedKernel_row μ label g] using finite_label_integral μ label hlabel
      (fun c => ∫ x, (label ⁻¹' {c}).indicator g x ∂μ)

end

omit hlabel in
theorem sameLabelKernel_mul_eq_sum (r : X → ℝ) (z : X × X) :
    sameLabelKernel label z * r z.1 * r z.2 =
      ∑ c : B, (label ⁻¹' {c}).indicator r z.1 * (label ⁻¹' {c}).indicator r z.2 := by
  rw [Finset.sum_eq_single (label z.1)]
  · by_cases he : label z.1 = label z.2
    · simp [sameLabelKernel, he]
    · simp [sameLabelKernel, he, Ne.symm he]
  · intro c hc hne
    have hn := Ne.symm hne
    simp [Set.indicator_apply, hn]
  simp_all

section
variable (r : X → ℝ) (hr : Integrable r μ)
include hr

theorem sameLabelKernel_mul_integrable :
    Integrable (fun z => sameLabelKernel label z * r z.1 * r z.2) (μ.prod μ) := by
  simp_rw [sameLabelKernel_mul_eq_sum label r]
  apply integrable_finsetSum
  intro c hc
  exact (hr.indicator ((measurableSet_singleton _).preimage hlabel)).mul_prod
    (hr.indicator ((measurableSet_singleton _).preimage hlabel))

theorem sameLabelKernel_mul_integral :
    (∫ z, sameLabelKernel label z * r z.1 * r z.2 ∂μ.prod μ) =
      ∑ c : B, (∫ x, (label ⁻¹' {c}).indicator r x ∂μ) ^ 2 := by
  simp_rw [sameLabelKernel_mul_eq_sum label r]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c hc
    rw [integral_prod_mul]
    ring
  · intro c hc
    exact (hr.indicator ((measurableSet_singleton _).preimage hlabel)).mul_prod
      (hr.indicator ((measurableSet_singleton _).preimage hlabel))

end

def pairWindowScore (r : X → ℝ) (V : ℝ) (z : X × X) : ℝ :=
  if label z.1 = label z.2 then (r z.1 - r z.2) ^ 2 / 2 - V else 0

theorem pairWindowScore_measurable (r : X → ℝ) (hr : Measurable r) (V : ℝ) :
    Measurable (pairWindowScore label r V) := by
  exact Measurable.ite
      (measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd))
      ((((hr.comp measurable_fst).sub (hr.comp measurable_snd)).pow_const 2
        |>.div_const 2).sub measurable_const) measurable_const

omit hlabel in
theorem pairWindowScore_symmetric (r : X → ℝ) (V : ℝ) (x y : X) :
    pairWindowScore label r V (x, y) = pairWindowScore label r V (y, x) := by
  unfold pairWindowScore
  grind

omit hlabel in
theorem pairWindowScore_abs_le (r : X → ℝ) (V : ℝ) (z : X × X) :
    |pairWindowScore label r V z| ≤ r z.1 ^ 2 + r z.2 ^ 2 + |V| := by
  unfold pairWindowScore
  split_ifs with h
  · calc
      _ ≤ |(r z.1 - r z.2) ^ 2 / 2| + |V| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (by positivity : 0 ≤ (r z.1 - r z.2) ^ 2 / 2)]
        nlinarith [sq_nonneg (r z.1 + r z.2)]
  · simp only [abs_zero]
    positivity

omit hlabel in
theorem pairWindowScore_sq_le (r : X → ℝ) (V : ℝ) (z : X × X) :
    pairWindowScore label r V z ^ 2 ≤
      4 * (r z.1 ^ 4 + r z.2 ^ 4) + 2 * V ^ 2 := by
  unfold pairWindowScore
  split_ifs with h
  · have h1 := add_sq_le (a := (r z.1 - r z.2) ^ 2 / 2) (b := -V)
    have h2 := (show Even (4 : ℕ) by decide).add_pow_le
      (a := r z.1) (b := -r z.2)
    norm_num at h2
    nlinarith
  simp_all <;> positivity

theorem pairWindowScore_memLp (r : X → ℝ) (hr : Measurable r) (V : ℝ)
    (h4 : Integrable (fun x => r x ^ 4) μ) :
    MemLp (pairWindowScore label r V) 2 (μ.prod μ) := by
  apply (memLp_two_iff_integrable_sq
    (pairWindowScore_measurable label hlabel r hr V).aestronglyMeasurable).mpr
  have hd : Integrable (fun z : X × X =>
      4 * (r z.1 ^ 4 + r z.2 ^ 4) + 2 * V ^ 2) (μ.prod μ) :=
    (((h4.comp_fst μ).add (h4.comp_snd μ)).const_mul 4).add (integrable_const _)
  apply hd.mono'
    ((pairWindowScore_measurable label hlabel r hr V).pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  simpa using pairWindowScore_sq_le label r V z

omit hlabel in
theorem pairWindowScore_local_sq_le (r : X → ℝ) (V : ℝ) (z : X × X) :
    pairWindowScore label r V z ^ 2 ≤
      4 * (labelLocalizedKernel label (fun x => r x ^ 4) z +
        labelLocalizedKernel label (fun x => r x ^ 4) z.swap) +
      2 * V ^ 2 * sameLabelKernel label z := by
  by_cases h : label z.1 = label z.2
  · have hb := pairWindowScore_sq_le label r V z
    simp only [pairWindowScore, labelLocalizedKernel, sameLabelKernel,
      Prod.fst_swap, Prod.snd_swap, if_pos h, if_pos h.symm] at hb ⊢
    nlinarith
  · simp [pairWindowScore, labelLocalizedKernel, sameLabelKernel, h, Ne.symm h]

section
variable (r : X → ℝ) (hr : Measurable r)
include hr

theorem pairWindowScore_energy_le (V M4 : ℝ)
    (h4 : Integrable (fun x => r x ^ 4) μ)
    (hloc : ∀ c : B, (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 4) x ∂μ) ≤
      M4 * μ.real (label ⁻¹' {c})) :
    (∫ z, pairWindowScore label r V z ^ 2 ∂μ.prod μ) ≤
      (8 * M4 + 2 * V ^ 2) * ∑ c : B, μ.real (label ⁻¹' {c}) ^ 2 := by
  let L := labelLocalizedKernel label (fun x => r x ^ 4)
  have hiL :=
    labelLocalizedKernel_integrable μ label hlabel _ h4
  have hiD := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have hd : Integrable (fun z : X × X => 4 * (L z + L z.swap) +
      2 * V ^ 2 * sameLabelKernel label z) (μ.prod μ) :=
    ((hiL.add hiL.swap).const_mul 4).add (hiD.const_mul _)
  have hb := integral_mono (pairWindowScore_memLp μ label hlabel r hr V h4).integrable_sq
    hd (pairWindowScore_local_sq_le label r V)
  rw [integral_add
      (f := fun z : X × X => 4 * (L z + L z.swap))
      (g := fun z => 2 * V ^ 2 * sameLabelKernel label z)
      ((hiL.add hiL.swap).const_mul 4) (hiD.const_mul _),
    integral_const_mul, integral_add (f := L) (g := fun z => L z.swap) hiL hiL.swap,
    integral_prod_swap L, integral_const_mul, sameLabelKernel_integral μ label hlabel] at hb
  have hL := labelLocalizedKernel_integral_le μ label hlabel _ h4 M4 hloc
  dsimp [L] at hb
  nlinarith

omit hr in
theorem pairWindowScore_integral (V : ℝ)
    (hr2 : MemLp r 2 μ) :
    (∫ z, pairWindowScore label r V z ∂μ.prod μ) =
      ∑ c : B, (μ.real (label ⁻¹' {c}) *
        (∫ x, (label ⁻¹' {c}).indicator (fun x => r x ^ 2) x ∂μ) -
        (∫ x, (label ⁻¹' {c}).indicator r x ∂μ) ^ 2 -
        V * μ.real (label ⁻¹' {c}) ^ 2) := by
  let L := labelLocalizedKernel label (fun x => r x ^ 2)
  let Q := fun z : X × X => sameLabelKernel label z * r z.1 * r z.2
  have hiL :=
    labelLocalizedKernel_integrable μ label hlabel _ hr2.integrable_sq
  have hiQ :=
    sameLabelKernel_mul_integrable μ label hlabel r (hr2.integrable (by norm_num))
  have hiD := (sameLabelKernel_memLp μ label hlabel).integrable (by norm_num)
  have heq : pairWindowScore label r V =
      (fun z : X × X => (L z + L z.swap) / 2 - Q z - V * sameLabelKernel label z) := by
    funext z
    dsimp [pairWindowScore, L, Q, labelLocalizedKernel, sameLabelKernel]
    grind
  rw [heq, integral_sub
      (f := fun z : X × X => (L z + L z.swap) / 2 - Q z)
      (g := fun z => V * sameLabelKernel label z)
      (((hiL.add hiL.swap).div_const 2).sub hiQ) (hiD.const_mul V),
    integral_sub (f := fun z : X × X => (L z + L z.swap) / 2) (g := Q)
      ((hiL.add hiL.swap).div_const 2) hiQ,
    integral_div, integral_add (f := L) (g := fun z => L z.swap) hiL hiL.swap,
    integral_prod_swap L, integral_const_mul]
  dsimp [L, Q]
  rw [labelLocalizedKernel_integral μ label hlabel _ hr2.integrable_sq,
    sameLabelKernel_mul_integral μ label hlabel r (hr2.integrable (by norm_num)),
    sameLabelKernel_integral μ label hlabel]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end

end Partition
end NearlyMinimax
