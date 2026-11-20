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
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

section

variable (R : PrincipalMellin.ActualRecipe S η) (s : ℂ)

def finiteDeletionRegularization : ℂ :=
  R.continuation.R s * ∏ v ∈ R.A.Sf,
    (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))

theorem finiteDeletionRegularization_eq (hs : 0 < s.re) (hne : s ≠ 1) :
    finiteDeletionRegularization R s = (s - 1) * R.L s := by
  unfold finiteDeletionRegularization PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
  rw [R.continuation.regularized s hs hne]
  ring

end

private alias principal_E_reflection := DedekindZetaZeroFree.UniformRegularizationBoundaryBounds.principal_E_reflection

private alias principal_prefactor := DedekindZetaZeroFree.UniformRegularizationBoundaryBounds.principal_prefactor

private alias completion_ratio_norm := DedekindZetaZeroFree.UniformRegularizationBoundaryBounds.completion_ratio_norm

private alias principal_left_formula := DedekindZetaZeroFree.UniformRegularizationBoundaryBounds.principal_left_formula

private alias left_ratio_bound := DedekindZetaZeroFree.UniformRegularizationBoundaryBounds.left_ratio_bound

section

variable (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F))
    (hm : m ≠ ⊥) (η : RayClassCharacter F m) (D : PrincipalRayHeckeData F m η)

include hF hm in
private lemma principal_strip_bound (δ : ℝ) (hδ : 0 < δ)
    (s : ℂ) (hs : 1+δ ≤ s.re) (hs4 : s.re ≤ 4) :
    ‖principalHeckeEntireRegularization F m η D s‖ ≤ 4*idealAbsoluteSum F (1+δ)*(2+|s.im|) := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; subst s; simp at hs; linarith
  rw [principalHeckeEntireRegularization_eq F hF m hm η D s hs0 hs1, norm_mul]
  have hn : ‖s-1‖ ≤ 4*(2+|s.im|) := by
    calc
      _ ≤ |(s-1).re|+|(s-1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
        rw [abs_of_nonneg (by linarith : 0 ≤ s.re-1)]
        nlinarith [abs_nonneg s.im]
  calc
    _ ≤ (4*(2+|s.im|))*idealAbsoluteSum F (1+δ) :=
      mul_le_mul hn (heckeDirichlet_hasSum_norm_le F (1+δ) (by linarith) m hm η s hs (D.L s)
        (D.series s (by linarith))) (norm_nonneg _) (by positivity)
    _ = _ := by ring

include hF hm in
private lemma principal_left_bound
    (δ K : ℝ) (hδ : 0 < δ) (hδu : δ ≤ 1/10) (hK : 0 ≤ K)
    (hb : ∀ s : ℂ, s.re = -δ → ‖Complex.Gammaℂ (1-s) * (Complex.Gammaℂ s)⁻¹‖ ≤ K*(2+|s.im|)^2)
    (s : ℂ) (hs : s.re = -δ) :
    ‖principalHeckeEntireRegularization F m η D s‖ ≤
      (((|NumberField.discr F| : ℤ) : ℝ) ^ ((1:ℝ)/2+δ) * K ^ NumberField.InfinitePlace.nrComplexPlaces F *
      (Ideal.absNorm m : ℝ) ^ ((1:ℝ)/2+δ) * idealAbsoluteSum F (1+δ)) * (2+|s.im|) ^ (2*NumberField.InfinitePlace.nrComplexPlaces F+1) := by
  rw [principal_left_formula F hF m η D δ hδ s hs, norm_mul, norm_mul]
  have hn : ‖s-1‖ ≤ 2+|s.im| := by
    calc
      _ ≤ |(s-1).re|+|(s-1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, hs]
        rw [abs_of_nonpos (by linarith : -δ-1 ≤ 0)]
        linarith
  calc
    _ ≤ ((2+|s.im|)*(_))*idealAbsoluteSum F (1+δ) :=
      mul_le_mul (mul_le_mul hn (left_ratio_bound F m hm δ K hδ hK hb s hs) (norm_nonneg _) (by positivity)) (heckeDirichlet_hasSum_norm_le F (1+δ) (by linarith) m hm η (1-s)
        (by simp [hs]) (D.L (1-s)) (D.series (1-s) (by simp [hs]; linarith))) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

end

variable (R : PrincipalMellin.ActualRecipe S η)

private lemma regularization_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ 4 →
      ‖principalHeckeEntireRegularization F R.A.modulus R.target R.continuation s‖ ≤
        C * (2 + |s.im|) ^ (2 * NumberField.InfinitePlace.nrComplexPlaces F + 1) := by
  let m := R.A.modulus
  let D := R.continuation
  have hm := R.A.modulus_ne_zero
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
    exact tsum_nonneg (fun I => by unfold idealAbsoluteWeight; split_ifs <;> positivity)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC0 : 0 < C0 := by dsimp [C0]; linarith [le_max_left H (4 * idealAbsoluteSum F (1+1/10))]
  let Cp := max (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10)) + 1
  have hCp : 0 < Cp := by
    dsimp [Cp]
    have : 0 < 6 ^ k * C0 := by positivity
    linarith [le_max_left (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10))]
  obtain ⟨M, B, hM, hB, hgr⟩ :=
    principalHeckeEntireRegularization_quadratic_strip_growth F hF m hm R.target D
      (-(1/10)) (1+1/10) (by norm_num)
  have hPL : ∀ t : ℂ, -(1/10) ≤ t.re ∧ t.re ≤ 1+1/10 →
      ‖principalHeckeEntireRegularization F m R.target D t‖ ≤ 6 ^ k * C0 * (2+|t.im|)^k := by
    apply norm_le_on_closed_strip_of_polynomial_boundary (1/10) (by norm_num) (by norm_num)
      k C0 hC0.le _ (principalHeckeEntireRegularization_differentiable F hF m hm R.target D).diffContOnCl
    · exact ⟨M, B, hM, hB, fun t ht => hgr t ht.1.le ht.2.le⟩
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
  · have hp : 2+|t.im| ≤ (2+|t.im|)^k := by
      simpa using pow_le_pow_right₀ (by linarith [abs_nonneg t.im] : 1 ≤ 2+|t.im|) hk
    exact (principal_strip_bound F hF m hm R.target D (1/10) (by norm_num) t
      (by linarith) hhi).trans (mul_le_mul
      (by dsimp [Cp]; linarith [le_max_right (6 ^ k * C0) (4 * idealAbsoluteSum F (1+1/10))])
      hp (by positivity) hCp.le)

private lemma finiteDeletion_mask_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ P : ℝ, 0 < P ∧ ∀ s : ℂ, a ≤ s.re →
      ‖∏ v ∈ R.A.Sf,
        (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))‖ ≤ P := by
  refine ⟨2 ^ R.A.Sf.card, by positivity, ?_⟩
  intro s hs
  have hlocal : ∀ v ∈ R.A.Sf,
      ‖1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤ 2 := by
    intro v hv
    have hQ : 1 < idealNorm v.asIdeal := by
      dsimp [idealNorm]
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hpow : ‖R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤ 1 := by
      rw [norm_mul]
      have hn := RayUnitary.ray_character_norm_le_one F R.A.modulus R.A.modulus_ne_zero
        R.target v.asIdeal
      have hp : ‖comparisonRealPower (idealNorm v.asIdeal) (-s)‖ ≤ 1 := by
        rw [MellinZeroFree.norm_comparisonRealPower, Complex.neg_re, Real.exp_le_one_iff]
        have hl := Real.log_pos hQ
        have hr : 0 < s.re := lt_of_lt_of_le ha hs
        nlinarith
      exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans (by simpa using hp)
    exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  rw [norm_prod]
  calc ∏ v ∈ R.A.Sf,
        ‖1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s)‖
      ≤ ∏ _v ∈ R.A.Sf, (2 : ℝ) :=
        Finset.prod_le_prod₀ (fun v hv => norm_nonneg _) hlocal
    _ = 2 ^ R.A.Sf.card := by simp

theorem stripRegularization_bound (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4) :
    ∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖finiteDeletionRegularization R s‖ ≤ B * (2 + |s.im|) ^ d := by
  obtain ⟨C, hC, hCb⟩ := regularization_bound R
  obtain ⟨P, hP, hPb⟩ := finiteDeletion_mask_bound R a ha
  let k := 2 * NumberField.InfinitePlace.nrComplexPlaces F + 1
  refine ⟨C * P, (k : ℝ), by positivity, by positivity, ?_⟩
  intro s ha' hb'
  have hspos := lt_of_lt_of_le ha ha'
  rw [finiteDeletionRegularization, ← (principalHeckeEntireRegularization_eq_bridge F (primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12) R.A.modulus
    R.A.modulus_ne_zero R.target R.continuation s hspos), norm_mul]
  calc ‖principalHeckeEntireRegularization F R.A.modulus R.target R.continuation s‖ *
        ‖∏ v ∈ R.A.Sf,
          (1 - R.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))‖
      ≤ (C * (2 + |s.im|) ^ k) * P :=
        mul_le_mul (hCb s hspos (le_trans hb' hb)) (hPb s ha') (norm_nonneg _) (by positivity)
    _ = C * P * (2 + |s.im|) ^ (k : ℝ) := by
        rw [Real.rpow_natCast]; ring

theorem stripNumerator_bound_away_pole (a b ρ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4) (hρ : 0 < ρ) :
    ∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → ρ ≤ ‖s - 1‖ →
      ‖R.L s‖ ≤ B * (2 + |s.im|) ^ d := by
  obtain ⟨B, d, hB, hd, hbd⟩ := stripRegularization_bound R a b ha hab hb
  refine ⟨B / ρ, d, by positivity, hd, ?_⟩
  intro s ha' hb' hsep
  have hsne : s ≠ 1 := by
    intro h
    rw [h] at hsep
    simp at hsep
    linarith
  have h1 := hbd s ha' hb'
  rw [(finiteDeletionRegularization_eq R s (lt_of_lt_of_le ha ha') hsne), norm_mul] at h1
  have hkey : ‖R.L s‖ * ρ ≤ B * (2 + |s.im|) ^ d := by
    calc _ ≤ ‖R.L s‖ * ‖s - 1‖ :=
          mul_le_mul_of_nonneg_left hsep (norm_nonneg _)
      _ = ‖s - 1‖ * ‖R.L s‖ := by ring
      _ ≤ B * (2 + |s.im|) ^ d := h1
  have hsplit : (B / ρ) * (2 + |s.im|) ^ d = (B * (2 + |s.im|) ^ d) / ρ := by ring
  rw [hsplit, le_div_iff₀ hρ]
  exact hkey

end
end DedekindZetaZeroFree.PrincipalNumerator
