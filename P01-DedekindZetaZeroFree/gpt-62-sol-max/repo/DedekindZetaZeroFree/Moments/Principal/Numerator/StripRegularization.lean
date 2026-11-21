module

public import DedekindZetaZeroFree.Moments.Principal.Numerator.RightHalfPlaneBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.UniformRegularizationBoundaryBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.RegularizationStripGrowth
public import DedekindZetaZeroFree.Analysis.PhragmenLindelof.PolynomialBoundaryBounds

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalNumerator
noncomputable section
open MeasureTheory Filter
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def finiteDeletionRegularization (R : PrincipalMellin.ActualRecipe S η) (s : ℂ) : ℂ :=
  R.continuation.R s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))

theorem finiteDeletionRegularization_eq (R : PrincipalMellin.ActualRecipe S η)
    (s : ℂ) (hs : 0 < s.re) (hne : s ≠ 1) :
    finiteDeletionRegularization R s = (s - 1) * R.L s := by
  unfold finiteDeletionRegularization PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
  rw [R.continuation.regularized s hs hne]
  ring

private lemma regularization_bound (R : PrincipalMellin.ActualRecipe S η) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ 4 →
      ‖principalHeckeEntireRegularization F R.A.modulus R.target R.continuation s‖ ≤
        C * (2 + |s.im|) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces F + 1) := by
  let m := R.A.modulus
  let D := R.continuation
  have hm : m ≠ ⊥ := R.A.modulus_ne_zero
  have hF := primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  let k := 2 * NumberField.InfinitePlace.nrComplexPlaces F + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  obtain ⟨K, hK, hb⟩ := gammaC_reflected_ratio_left_bound (1/10) (by norm_num) (by norm_num)
  let H := (((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+1/10) *
    K ^ NumberField.InfinitePlace.nrComplexPlaces F * (Ideal.absNorm m : ℝ) ^ ((1:ℝ)/2+1/10) *
    idealAbsoluteSum F (1+1/10))
  let C0 := max H (4 * idealAbsoluteSum F (1+1/10)) + 1
  have hsum : 0 ≤ idealAbsoluteSum F (1+1/10) := by
    unfold idealAbsoluteSum
    exact tsum_nonneg (fun I => by unfold idealAbsoluteWeight; positivity)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  let Cp := max (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10)) + 1
  have hCp : 0 < Cp := by
    dsimp [Cp]
    have : 0 < 6 ^ k * C0 := by positivity
    grind
  have hdiff := principalHeckeEntireRegularization_differentiable F hF m hm R.target D
  obtain ⟨M, B, hM, hB, hgr⟩ :=
    principalHeckeEntireRegularization_quadratic_strip_growth F hF m hm R.target D
      (-(1/10)) (1+1/10) (by norm_num)
  have hPL : ∀ t : ℂ, -(1/10) ≤ t.re ∧ t.re ≤ 1+1/10 →
      ‖principalHeckeEntireRegularization F m R.target D t‖ ≤ 6 ^ k * C0 * (2+|t.im|)^k := by
    apply norm_le_on_closed_strip_of_polynomial_boundary (1/10) (by norm_num) (by norm_num)
      k C0 hC0.le _ hdiff.diffContOnCl
    · grind only
    · intro t ht
      rcases ht with ht | ht
      · have hl := principal_left_bound F hF m hm R.target D (1/10) K
          (by norm_num) (by norm_num) hK.le hb t ht
        change ‖principalHeckeEntireRegularization F m R.target D t‖ ≤ H * (2+|t.im|)^k at hl
        exact hl.trans (mul_le_mul_of_nonneg_right
          (by dsimp [C0]; linarith [le_max_left H (4 * idealAbsoluteSum F (1+1/10))])
          (by positivity))
      · have hr := principal_strip_bound F hF m hm R.target D (1/10) (by norm_num) t
          (by rw [ht]) (by rw [ht]; norm_num)
        have hp : 2+|t.im| ≤ (2+|t.im|)^k := by
          simpa using pow_le_pow_right₀ (by linarith [abs_nonneg t.im] : 1 ≤ 2+|t.im|) hk
        exact hr.trans (mul_le_mul
          (by dsimp [C0]; linarith [le_max_right H (4 * idealAbsoluteSum F (1+1/10))])
          hp (by positivity) hC0.le)
  refine ⟨Cp, hCp, ?_⟩
  intro t hlo hhi
  by_cases ht : t.re ≤ 1+1/10
  · exact (hPL t ⟨by linarith, ht⟩).trans (mul_le_mul_of_nonneg_right
      (by dsimp [Cp]; linarith [le_max_left (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10))])
      (by positivity))
  · have hr := principal_strip_bound F hF m hm R.target D (1/10) (by norm_num) t
      (by linarith) hhi
    have hp : 2+|t.im| ≤ (2+|t.im|)^k := by
      simpa using pow_le_pow_right₀ (by linarith [abs_nonneg t.im] : 1 ≤ 2+|t.im|) hk
    exact hr.trans (mul_le_mul
      (by dsimp [Cp]; linarith [le_max_right (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10))])
      hp (by positivity) hCp.le)

theorem stripRegularization_bound
    (R : PrincipalMellin.ActualRecipe S η) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4) :
    ∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖finiteDeletionRegularization R s‖ ≤ B * (2 + |s.im|) ^ d := by
  obtain ⟨C, hC, hCb⟩ := regularization_bound R
  let P : ℝ := 2 ^ R.A.Sf.card
  let k : ℕ := 2 * NumberField.InfinitePlace.nrComplexPlaces F + 1
  refine ⟨C * P, (k : ℝ), by positivity, by positivity, ?_⟩
  intro s ha' hb'
  have hspos : 0 < s.re := lt_of_lt_of_le ha ha'
  have hsle : s.re ≤ 4 := le_trans hb' hb
  have hF := primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  have hbridge := principalHeckeEntireRegularization_eq_bridge F hF R.A.modulus
    R.A.modulus_ne_zero R.target R.continuation s hspos
  have hreg := hCb s hspos hsle
  have hmask := finiteDeletion_mask_norm_le R hspos.le
  rw [finiteDeletionRegularization, ← hbridge, norm_mul]
  calc ‖principalHeckeEntireRegularization F R.A.modulus R.target R.continuation s‖ *
        ‖∏ v ∈ R.A.Sf,
          (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))‖
      ≤ (C * (2 + |s.im|) ^ k) * P :=
        mul_le_mul hreg hmask (norm_nonneg _) (by positivity)
    _ = C * P * (2 + |s.im|) ^ (k : ℝ) := by
        rw [Real.rpow_natCast]; ring

theorem stripNumerator_bound_away_pole
    (R : PrincipalMellin.ActualRecipe S η) (a b ρ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4) (hρ : 0 < ρ) :
    ∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ρ ≤ ‖s - 1‖ →
      ‖R.L s‖ ≤ B * (2 + |s.im|) ^ d := by
  obtain ⟨B, d, hB, hd, hbd⟩ := stripRegularization_bound R a b ha hab hb
  refine ⟨B / ρ, d, by positivity, hd, ?_⟩
  intro s ha' hb' hsep
  have hspos : 0 < s.re := lt_of_lt_of_le ha ha'
  have hsne : s ≠ 1 := by
    intro h
    rw [h] at hsep
    simp at hsep
    linarith
  have heq := finiteDeletionRegularization_eq R s hspos hsne
  have h1 := hbd s ha' hb'
  rw [heq, norm_mul] at h1
  have hkey : ‖R.L s‖ * ρ ≤ B * (2 + |s.im|) ^ d := by
    calc ‖R.L s‖ * ρ ≤ ‖R.L s‖ * ‖s - 1‖ :=
          mul_le_mul_of_nonneg_left hsep (norm_nonneg _)
      _ = ‖s - 1‖ * ‖R.L s‖ := by ring
      _ ≤ B * (2 + |s.im|) ^ d := h1
  have hsplit : (B / ρ) * (2 + |s.im|) ^ d = (B * (2 + |s.im|) ^ d) / ρ := by ring
  rw [hsplit, le_div_iff₀ hρ]
  exact hkey

end
end DedekindZetaZeroFree.PrincipalNumerator
