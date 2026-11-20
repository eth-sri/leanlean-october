module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Convexity
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.InverseBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.GammaZeroContour

noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology

section Helpers

section

variable (X : ℝ) (f : ℂ → ℂ)

private lemma regularized_holomorphic (hX : 0 < X)
    (hf : DifferentiableOn ℂ f {v : ℂ | (-1 : ℝ) < v.re}) :
    DifferentiableOn ℂ (fun z => Gamma (z + 1) * dslope f 0 z * (X : ℂ) ^ z)
      {v : ℂ | (-1 : ℝ) < v.re} := by
  apply DifferentiableOn.mul (DifferentiableOn.mul ?_ ((Complex.differentiableOn_dslope
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).mpr hf))
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).differentiableOn
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.comp z (Complex.differentiableAt_Gamma (z + 1) ?_)
    (differentiableAt_id.add_const 1)
  intro m he
  have hh := congrArg Complex.re he
  simp only [add_re, one_re, neg_re, natCast_re] at hh
  dsimp at hz
  linarith

private lemma regularized_eq (hf0 : f 0 = 0) (z : ℂ) (hz : z ≠ 0) :
    Gamma (z + 1) * dslope f 0 z * (X : ℂ) ^ z = Gamma z * f z * (X : ℂ) ^ z := by
  rw [Gamma_add_one z hz, dslope_of_ne f hz, slope]
  simp only [sub_zero, hf0, smul_eq_mul, vsub_eq_sub]
  field_simp

end

private lemma polynomial_tail (B : ℝ) (hB : 0 ≤ B) (m : ℕ) (hm : B + 2 ≤ m)
    (t : ℝ) (ht : 1 ≤ |t|) :
    |t| ^ (-(m : ℝ)) * (2 + |t|) ^ B ≤ (3 ^ B * 4) * (1 + |t|) ^ (-2 : ℝ) := by
  have h1 : (2 + |t|) ^ B ≤ 3 ^ B * |t| ^ B := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (abs_nonneg t)]
    apply Real.rpow_le_rpow (by positivity) (by linarith) hB
  have h3 : |t| ^ (-2 : ℝ) ≤ 4 * (1 + |t|) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (abs_nonneg t), Real.rpow_two,
      Real.rpow_neg (by positivity : 0 ≤ 1 + |t|), Real.rpow_two]
    have hden : 0 < (1 + |t|) ^ 2 := by positivity
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity : 0 < |t| ^ 2) hden).2
    nlinarith [sq_nonneg (|t| - 1)]
  calc
    _ ≤ |t| ^ (-(m : ℝ)) * (3 ^ B * |t| ^ B) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (abs_nonneg t) _)
    _ = 3 ^ B * (|t| ^ (-(m : ℝ)) * |t| ^ B) := by ring
    _ ≤ 3 ^ B * |t| ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left (by
      rw [← Real.rpow_add (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)) (by positivity)
    _ ≤ 3 ^ B * (4 * (1 + |t|) ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

private alias rectangle_limits := DedekindZetaZeroFree.ComparisonShiftProof.rectangle_limits

private alias integrable_tail := DedekindZetaZeroFree.ComparisonShiftProof.integrable_tail

private alias horizontal_decay_limit := DedekindZetaZeroFree.ComparisonShiftProof.horizontal_decay_limit

end Helpers

theorem gamma_zero_contour_generic (a b X : ℝ) (f : ℂ → ℂ)
    (ha1 : -1 < a) (ha0 : a < 0) (hb : 0 < b) (hX : 0 < X)
    (hf : DifferentiableOn ℂ f {v : ℂ | (-1 : ℝ) < v.re})
    (hf0 : f 0 = 0)
    (hGrowth : ∃ M B : ℝ, 0 < M ∧ 0 ≤ B ∧
      ∀ σ : ℝ, σ ∈ Set.Icc a b → ∀ t : ℝ,
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (2 + |t|) ^ B) :
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) ∧
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma ((b : ℂ) + (t : ℂ) * Complex.I) *
        f ((b : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((b : ℂ) + (t : ℂ) * Complex.I)) ∧
    (∫ t : ℝ, Complex.Gamma ((b : ℂ) + (t : ℂ) * Complex.I) *
        f ((b : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((b : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ, Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨M, B, hM, hB, hg⟩ := hGrowth
  have hab : a ≤ b := by linarith
  let H : ℂ → ℂ := fun z => Gamma (z + 1) * dslope f 0 z * (X : ℂ) ^ z
  have hH : DifferentiableOn ℂ H {v : ℂ | (-1 : ℝ) < v.re} :=
    regularized_holomorphic X f hX hf
  have hstrip : {z : ℂ | a ≤ z.re ∧ z.re ≤ b} ⊆ {v : ℂ | (-1 : ℝ) < v.re} := by
    intro z hz
    dsimp at hz ⊢
    linarith [hz.1]
  have hHs := hH.mono hstrip
  have hHeq (z : ℂ) (hz : z ≠ 0) :
      H z = Gamma z * f z * (X : ℂ) ^ z := regularized_eq X f hf0 z hz
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := b)).bddAbove_image
    (Real.continuous_const_rpow hX.ne').continuousOn
  have hKbound (σ : ℝ) (hσ : σ ∈ Icc a b) : X ^ σ ≤ K := hK ⟨σ, hσ, rfl⟩
  have hKpos : 0 < K := lt_of_lt_of_le (Real.rpow_pos_of_pos hX a) (hKbound a ⟨le_rfl, hab⟩)
  obtain ⟨m, hm⟩ := exists_nat_gt (B + 2)
  obtain ⟨C, hC, hd⟩ := DedekindZetaZeroFree.detector_sz_gamma_decay a b hab m
  let D : ℝ := C * M * K * (3 ^ B * 4)
  have hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖H ((σ : ℂ) + (t : ℂ) * I)‖ ≤ D * (1 + |t|) ^ (-2 : ℝ) := by
    intro σ hσ t ht
    have hz : (σ : ℂ) + (t : ℂ) * I ≠ 0 := by
      intro he
      have he' : t = 0 := by simpa using congrArg Complex.im he
      norm_num [he'] at ht
    rw [hHeq _ hz, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_self, add_zero]
    calc
      ‖Gamma ((σ : ℂ) + (t : ℂ) * I)‖ * ‖f ((σ : ℂ) + (t : ℂ) * I)‖ * X ^ σ
          ≤ (C * |t| ^ (-(m : ℝ))) * (M * (2 + |t|) ^ B) * K := by
            apply mul_le_mul (mul_le_mul (hd σ hσ t ht) (hg σ hσ t) (norm_nonneg _)
              (mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg t) _)))
              (hKbound σ hσ) (Real.rpow_nonneg hX.le σ)
              (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (abs_nonneg t) _))
                (mul_nonneg hM.le (Real.rpow_nonneg (by positivity) _)))
      _ = C * M * K * (|t| ^ (-(m : ℝ)) * (2 + |t|) ^ B) := by ring
      _ ≤ C * M * K * ((3 ^ B * 4) * (1 + |t|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (polynomial_tail B hB m hm.le t ht) (by positivity)
      _ = D * (1 + |t|) ^ (-2 : ℝ) := by dsimp [D]; ring
  have hi : ∀ σ ∈ Icc a b, Integrable (fun t : ℝ => H ((σ : ℂ) + (t : ℂ) * I)) := by
    intro σ hσ
    apply integrable_tail _ D
    · apply hH.continuousOn.comp_continuous (by fun_prop)
      intro t
      apply hstrip
      simpa using hσ
    · exact hbound σ hσ
  have hia := hi a ⟨le_rfl, hab⟩
  have hib := hi b ⟨hab, le_rfl⟩
  have heqa (t : ℝ) : H ((a : ℂ) + (t : ℂ) * I) =
      Gamma ((a : ℂ) + (t : ℂ) * I) * f ((a : ℂ) + (t : ℂ) * I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * I) := by
    apply hHeq
    intro he
    have he' : a = 0 := by simpa using congrArg Complex.re he
    linarith
  have heqb (t : ℝ) : H ((b : ℂ) + (t : ℂ) * I) =
      Gamma ((b : ℂ) + (t : ℂ) * I) * f ((b : ℂ) + (t : ℂ) * I) *
        (X : ℂ) ^ ((b : ℂ) + (t : ℂ) * I) := by
    apply hHeq
    intro he
    have he' : b = 0 := by simpa using congrArg Complex.re he
    linarith
  refine ⟨by simpa only [heqa] using hia, by simpa only [heqb] using hib, ?_⟩
  have he := rectangle_limits H hab hHs
    (intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id)
    (intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id)
    (by simpa using horizontal_decay_limit H a b D (-1) hab (by norm_num) hbound)
    (by simpa using horizontal_decay_limit H a b D 1 hab (by norm_num) hbound)
  simpa only [heqa, heqb] using he.symm

section Actual

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

private lemma detector_entire_bounded (F : Type) [Field F] [NumberField F] (U : ℝ)
    (ω : Detector.PrimitiveFrequencyCharacter F) :
    Differentiable ℂ (DetectorDef.D F U ω.character) ∧
    ∃ N : ℝ, 0 < N ∧ ∀ z : ℂ, 0 ≤ z.re → ‖DetectorDef.D F U ω.character z‖ ≤ N := by
  let X := U ^ DetectorDef.qExp
  let T := (Detector.ideals_bounded_norm_finite F X).toFinset
  have he (z : ℂ) : DetectorDef.D F U ω.character z = ∑ d ∈ T,
      (if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
        (Detector.idealMoebius F d : ℂ) * ω.character d *
          (Ideal.absNorm d : ℂ) ^ (-z) else 0) := by
    unfold DetectorDef.D
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra hn
    exact hd (if_neg hn)
  have hdiff : Differentiable ℂ (DetectorDef.D F U ω.character) := by
    have := funext he
    rw [this]
    apply Differentiable.fun_sum
    intro d hd
    by_cases hn : d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X
    · simp only [if_pos hn]
      apply Differentiable.const_mul
      apply Differentiable.const_cpow differentiable_id.neg
      left
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hn.1
    · simp only [if_neg hn]
      exact differentiable_const _
  refine ⟨hdiff, (T.card : ℝ) + 1, by positivity, fun z hz => ?_⟩
  rw [he z]
  calc ‖∑ d ∈ T, (if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
        (Detector.idealMoebius F d : ℂ) * ω.character d *
          (Ideal.absNorm d : ℂ) ^ (-z) else 0)‖
      ≤ ∑ d ∈ T, ‖(if d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X then
        (Detector.idealMoebius F d : ℂ) * ω.character d *
          (Ideal.absNorm d : ℂ) ^ (-z) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ T, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hn : d ≠ ⊥ ∧ (Ideal.absNorm d : ℝ) ≤ X
        · rw [if_pos hn]
          have hnpos :=
            Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn.1)
          have hμ : ‖(Detector.idealMoebius F d : ℂ)‖ ≤ 1 := by
            unfold Detector.idealMoebius UniqueFactorizationMonoid.moebius
            split <;> simp [Int.cast_pow]
          have hpow : ‖(Ideal.absNorm d : ℂ) ^ (-z)‖ ≤ 1 := by
            rw [Complex.norm_natCast_cpow_of_pos hnpos]
            simp only [Complex.neg_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hnpos) (by linarith)
          rw [norm_mul, norm_mul]
          simpa using (mul_le_mul (mul_le_mul hμ (RayUnitary.ray_character_norm_le_one F _ ω.conductor_ne_zero ω.character d) (norm_nonneg _) zero_le_one) hpow
            (norm_nonneg _) (by norm_num))
        · rw [if_neg hn]
          simp
    _ = T.card := by simp
    _ ≤ (T.card : ℝ) + 1 := by linarith

alias GammaZeroShift.detector_entire_bounded := detector_entire_bounded

theorem gamma_zero_contour {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (D : FixedData S η) (u : D.Row)
    (hnp : ¬ (D.omega u).character.IsPrincipal)
    (U : ℝ) (hU : 2 ≤ U) (hUq : U ≤ D.q u) (hUq2 : D.q u < 2 * U)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hgs : ∀ z : ℂ, 1 < z.re → g z = Detector.idealLSeries F (D.omega u).character z)
    (β γ : ℝ) (hβ : DetectorDef.σ₀ ≤ β) (hβ1 : β ≤ 1)
    (hz : DetectorDef.IsLZero (D.omega u) ((β : ℂ) + (γ : ℂ) * Complex.I))
    (v₀ : ℝ) (hv₀ : 1 < v₀) (hv₀3 : v₀ ≤ 3) :
    let s : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I
    let f : ℂ → ℂ := fun v =>
      g (s + v) * DetectorDef.D F U (D.omega u).character (s + v)
    let X : ℝ := U ^ DetectorDef.r
    let a : ℝ := DetectorDef.c - β
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) ∧
    MeasureTheory.Integrable (fun t : ℝ =>
      Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
        f ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((v₀ : ℂ) + (t : ℂ) * Complex.I)) ∧
    (∫ t : ℝ, Complex.Gamma ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
        f ((v₀ : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((v₀ : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ, Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) *
        f ((a : ℂ) + (t : ℂ) * Complex.I) *
        (X : ℂ) ^ ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨C0, hC0, hnorm⟩ : ∃ C0 : ℝ, 0 < C0 ∧
      (Ideal.absNorm (D.omega u).conductor : ℝ) ≤ C0 * U :=
    ⟨(Ideal.absNorm (D.omega u).conductor : ℝ) + 1, by positivity, by
      have := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm (D.omega u).conductor)
      nlinarith⟩
  obtain ⟨A, hA, hbridge⟩ := detector_convexity_bridge F
    (primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12)
    C0 hC0
  obtain ⟨K, hK, hKb⟩ := hbridge 1 one_pos
  intro s f X a
  have hsre : s.re = β := by simp [s]
  have hsim : s.im = γ := by simp [s]
  have hc : DetectorDef.c = 1 / 100 := rfl
  have hσ : DetectorDef.σ₀ = 22 / 25 := rfl
  have ha1 : -1 < a := by simp only [a]; rw [hc]; linarith
  have ha0 : a < 0 := by simp only [a]; rw [hc]; rw [hσ] at hβ; linarith
  have hUp : 0 < U := by linarith
  have hXp : 0 < X := Real.rpow_pos_of_pos hUp _
  obtain ⟨hdiff, Nd, hNd, hNdb⟩ := detector_entire_bounded F U (D.omega u)
  have hgL :=
    RowHeckeBridge.entire_eq_heckeOmega D u hnp hg hgs
  have hg0 : g s = 0 := by
    obtain ⟨hre, g', hg'an, hg'ser, hg's⟩ := hz
    rw [hgL s hre, ← (RowHeckeBridge.eq_hecke_of_analyticOn D.recipe.A (D.omega u) hnp hg'an hg'ser s hre)]
    exact hg's
  have hf0 : f 0 = 0 := by
    show g (s + 0) * DetectorDef.D F U (D.omega u).character (s + 0) = 0
    rw [add_zero, hg0, zero_mul]
  have hfd :=
    (hg.comp ((differentiable_const s).add differentiable_id)).mul
      (hdiff.comp ((differentiable_const s).add differentiable_id))
  have hbound (σ : ℝ) (hσ' : σ ∈ Set.Icc a v₀) (t : ℝ) :
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (K * U ^ ((1 : ℝ) / 2 + 1) * Nd) * (2 + |γ + t|) ^ A := by
    have hre : (s + ((σ : ℂ) + (t : ℂ) * Complex.I)).re = β + σ := by simp [hsre]
    have him : (s + ((σ : ℂ) + (t : ℂ) * Complex.I)).im = γ + t := by simp [hsim]
    have hr1 : (3 / 1000 : ℝ) ≤ β + σ := by
      have := hσ'.1
      simp only [a] at this
      rw [hc] at this
      linarith
    have hkl := (hKb U hU (D.omega u).conductor (D.omega u).conductor_ne_zero
      (D.omega u).character (D.omega u).primitive hnorm
      (s + ((σ : ℂ) + (t : ℂ) * Complex.I)) (by rw [hre]; exact hr1)
      (by rw [hre]; exact (by linarith [hσ'.2]))).1 hnp (RowHeckeBridge.heckeOmega D u hnp)
    rw [him] at hkl
    calc _
        = ‖g (s + ((σ : ℂ) + (t : ℂ) * Complex.I))‖ *
          ‖DetectorDef.D F U (D.omega u).character (s + ((σ : ℂ) + (t : ℂ) * Complex.I))‖ :=
          norm_mul _ _
      _ ≤ (K * U ^ ((1 : ℝ) / 2 + 1) * (2 + |γ + t|) ^ A) * Nd :=
          mul_le_mul (by
            rw [hgL _ (by rw [hre]; linarith)]
            exact hkl) (hNdb (s + ((σ : ℂ) + (t : ℂ) * Complex.I)) (by rw [hre]; linarith)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hGrowth : ∃ M B : ℝ, 0 < M ∧ 0 ≤ B ∧
      ∀ σ : ℝ, σ ∈ Set.Icc a v₀ → ∀ t : ℝ,
        ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (2 + |t|) ^ B := by
    refine ⟨K * U ^ ((1 : ℝ) / 2 + 1) * Nd * (2 + |γ|) ^ A, A, by positivity, hA, ?_⟩
    intro σ hσ' t
    have ht : 2 + |γ + t| ≤ (2 + |γ|) * (2 + |t|) := by
      nlinarith [abs_add_le γ t, abs_nonneg γ, abs_nonneg t,
        mul_nonneg (abs_nonneg γ) (abs_nonneg t)]
    calc
      _ ≤ (K * U ^ ((1 : ℝ) / 2 + 1) * Nd) * (2 + |γ + t|) ^ A := hbound σ hσ' t
      _ ≤ (K * U ^ ((1 : ℝ) / 2 + 1) * Nd) * ((2 + |γ|) * (2 + |t|)) ^ A := by
        gcongr
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  exact gamma_zero_contour_generic a v₀ X f ha1 ha0 (by linarith) hXp hfd.differentiableOn
    hf0 hGrowth

end Actual

end

end DedekindZetaZeroFree.Quantitative.GammaZeroContour
