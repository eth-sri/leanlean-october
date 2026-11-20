module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Algebra.Order.Chebyshev
public import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp

/-!
# Finite-sum squared `L²` seminorm estimate

This module records the finite Cauchy estimate for the squared real `L²`
seminorm of a finite sum.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Analysis

open MeasureTheory
open scoped ENNReal

section
variable {α E : Type*}

/-- The square of the real-valued `L²` seminorm of a representative. -/
noncomputable abbrev squaredL2Seminorm [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E) : ℝ := (eLpNorm f 2 μ).toReal ^ 2

@[simp] theorem squaredL2Seminorm_nonneg [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E) : 0 ≤ squaredL2Seminorm μ f := sq_nonneg _

@[simp] theorem squaredL2Seminorm_neg [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E) : squaredL2Seminorm μ (-f) = squaredL2Seminorm μ f := by
  simp [squaredL2Seminorm]

theorem squaredL2Seminorm_mono_measure [MeasurableSpace α] [NormedAddCommGroup E]
    {μ ν : Measure α} {f : α → E} (hf : MemLp f 2 ν) (hμ : μ ≤ ν) :
    squaredL2Seminorm μ f ≤ squaredL2Seminorm ν f :=
  pow_le_pow_left₀ ENNReal.toReal_nonneg
    (ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f hμ)) 2

end

/-- An a.e. multiplier bound controls both L² membership and the squared seminorm. -/
theorem memLp_mul_squaredL2Seminorm_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {a f : α → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (ha : AEStronglyMeasurable a μ) (hf : MemLp f 2 μ) (hbound : ∀ᵐ x ∂μ, |a x| ≤ K) :
    MemLp (fun x => a x * f x) 2 μ ∧
      squaredL2Seminorm μ (fun x => a x * f x) ≤ K ^ 2 * squaredL2Seminorm μ f := by
  obtain ⟨hm, h⟩ := memLp_mul_eLpNorm_toReal_le_of_ae_abs_le hK ha hf hbound
  exact ⟨hm, by simpa only [mul_pow] using pow_le_pow_left₀ ENNReal.toReal_nonneg h 2⟩

/-- The squared real `L²` seminorm of a finite sum is bounded by the number of
terms times the sum of the squared component seminorms. -/
theorem eLpNorm_sum_toReal_sq_le_card_mul
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f : ι → α → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) :
    (ENNReal.toReal (eLpNorm (∑ i, f i) 2 μ)) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        ∑ i, (ENNReal.toReal (eLpNorm (f i) 2 μ)) ^ 2 := by
  have hnorm : eLpNorm (∑ i, f i) 2 μ ≤ ∑ i, eLpNorm (f i) 2 μ := by
    simpa only [Finset.sum_const_zero, Finset.sum_sub_distrib] using
      (eLpNorm_sum_le (s := Finset.univ)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have htop : (∑ i, eLpNorm (f i) 2 μ) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun i _ => (hf i).eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop hnorm
  rw [ENNReal.toReal_sum (fun i (_hi : i ∈ Finset.univ) =>
    (hf i).eLpNorm_ne_top)] at hreal
  calc
    (ENNReal.toReal (eLpNorm (∑ i, f i) 2 μ)) ^ 2 ≤
        (∑ i, ENNReal.toReal (eLpNorm (f i) 2 μ)) ^ 2 := by
      nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (∑ i, f i) 2 μ)]
    _ ≤ (Fintype.card ι : ℝ) *
        ∑ i, (ENNReal.toReal (eLpNorm (f i) 2 μ)) ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ)
        (f := fun i => ENNReal.toReal (eLpNorm (f i) 2 μ)))

/-- Simultaneously sum the source, principal, drift and potential terms of a residual. -/
theorem memLp_and_squaredL2Seminorm_add_terms
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    (R : α → ℝ) (A : ι → ι → α → ℝ) (B : ι → α → ℝ) (C : α → ℝ)
    (hR : MemLp R 2 μ) (hA : ∀ i j, MemLp (A i j) 2 μ)
    (hB : ∀ j, MemLp (B j) 2 μ) (hC : MemLp C 2 μ) :
    let S := fun z => R z + (∑ i, ∑ j, A i j z) + (∑ j, B j z) + C z
    MemLp S 2 μ ∧ squaredL2Seminorm μ S ≤
      ((Fintype.card ι : ℝ) ^ 2 + (Fintype.card ι : ℝ) + 2) *
        (squaredL2Seminorm μ R + (∑ i, ∑ j, squaredL2Seminorm μ (A i j)) +
          (∑ j, squaredL2Seminorm μ (B j)) + squaredL2Seminorm μ C) := by
  classical
  let I := Unit ⊕ ((ι × ι) ⊕ (ι ⊕ Unit))
  let F : I → α → ℝ
    | .inl _ => R
    | .inr (.inl (i, j)) => A i j
    | .inr (.inr (.inl j)) => B j
    | .inr (.inr (.inr _)) => C
  have hF (i : I) : MemLp (F i) 2 μ := by
    rcases i with (_ | (⟨i, j⟩ | (j | _)))
    exacts [hR, hA i j, hB j, hC]
  have hsum : (∑ i, F i) = fun z => R z + (∑ i, ∑ j, A i j z) + (∑ j, B j z) + C z := by
    ext z
    simp [I, F, Fintype.sum_prod_type]
    abel
  have hcard : (Fintype.card I : ℝ) = (Fintype.card ι : ℝ) ^ 2 + (Fintype.card ι : ℝ) + 2 := by
    simp [I]
    ring
  dsimp only
  rw [← hsum]
  refine ⟨memLp_finsetSum' _ (fun i _ => hF i), ?_⟩
  have h := eLpNorm_sum_toReal_sq_le_card_mul F hF
  rw [hcard] at h
  simpa [I, F, Fintype.sum_prod_type, add_assoc] using h

/-- Sum pointwise four-term bounds whose aggregate terms have a common energy factor. -/
theorem sum_le_mul_four_term_bound {ι : Type*} [Fintype ι]
    {W R A B C : ι → ℝ} {N CR CA CB CC E : ℝ} (hN : 0 ≤ N)
    (hW : ∀ i, W i ≤ N * (R i + A i + B i + C i))
    (hR : (∑ i, R i) ≤ CR * E) (hA : (∑ i, A i) ≤ CA * E)
    (hB : (∑ i, B i) ≤ CB * E) (hC : (∑ i, C i) ≤ CC * E) :
    (∑ i, W i) ≤ N * (CR + CA + CB + CC) * E := by
  calc
    _ ≤ ∑ i, N * (R i + A i + B i + C i) := Finset.sum_le_sum fun i _ => hW i
    _ = N * ((∑ i, R i) + (∑ i, A i) + (∑ i, B i) + (∑ i, C i)) := by
      rw [← Finset.mul_sum]; simp only [Finset.sum_add_distrib]
    _ ≤ N * (CR * E + CA * E + CB * E + CC * E) := by gcongr
    _ = _ := by ring

end HypoellipticAleksandrov.Analysis
