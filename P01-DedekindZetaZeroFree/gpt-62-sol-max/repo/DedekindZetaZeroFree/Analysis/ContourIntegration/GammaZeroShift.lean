module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Convexity
public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.InverseBound
public import DedekindZetaZeroFree.Analysis.VerticalContourShift

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.GammaZeroContour

noncomputable section

open Set Filter MeasureTheory Complex ComparisonShiftProof
open scoped Topology

section Helpers

private lemma regularized_holomorphic (X : ℝ) (f : ℂ → ℂ) (hX : 0 < X)
    (hf : DifferentiableOn ℂ f {v : ℂ | (-1 : ℝ) < v.re}) :
    DifferentiableOn ℂ (fun z => Gamma (z + 1) * dslope f 0 z * (X : ℂ) ^ z)
      {v : ℂ | (-1 : ℝ) < v.re} := by
  have ho : IsOpen {v : ℂ | (-1 : ℝ) < v.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd := (Complex.differentiableOn_dslope (c := (0 : ℂ))
    (ho.mem_nhds (by norm_num))).mpr hf
  apply DifferentiableOn.mul (DifferentiableOn.mul ?_ hd)
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

private lemma regularized_eq (X : ℝ) (f : ℂ → ℂ) (hf0 : f 0 = 0) (z : ℂ) (hz : z ≠ 0) :
    Gamma (z + 1) * dslope f 0 z * (X : ℂ) ^ z = Gamma z * f z * (X : ℂ) ^ z := by
  rw [Gamma_add_one z hz, dslope_of_ne f hz, slope]
  simp only [sub_zero, hf0, smul_eq_mul, vsub_eq_sub]
  field_simp

private lemma polynomial_tail (B : ℝ) (hB : 0 ≤ B) (m : ℕ) (hm : B + 2 ≤ m)
    (t : ℝ) (ht : 1 ≤ |t|) :
    |t| ^ (-(m : ℝ)) * (2 + |t|) ^ B ≤ (3 ^ B * 4) * (1 + |t|) ^ (-2 : ℝ) := by
  have hp : 0 < |t| := by linarith
  have h1 : (2 + |t|) ^ B ≤ 3 ^ B * |t| ^ B := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (abs_nonneg t)]
    apply Real.rpow_le_rpow (by positivity) (by linarith) hB
  have h2 : |t| ^ (-(m : ℝ)) * |t| ^ B ≤ |t| ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hp]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have h3 : |t| ^ (-2 : ℝ) ≤ 4 * (1 + |t|) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (abs_nonneg t), Real.rpow_two,
      Real.rpow_neg (by positivity : 0 ≤ 1 + |t|), Real.rpow_two]
    have hden : 0 < (1 + |t|) ^ 2 := by positivity
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity : 0 < |t| ^ 2) hden).2
    nlinarith
  calc
    _ ≤ |t| ^ (-(m : ℝ)) * (3 ^ B * |t| ^ B) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (abs_nonneg t) _)
    _ = 3 ^ B * (|t| ^ (-(m : ℝ)) * |t| ^ B) := by ring
    _ ≤ 3 ^ B * |t| ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 3 ^ B * (4 * (1 + |t|) ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

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
            gcongr
            · exact hd σ hσ t ht
            · exact hg σ hσ t
            · exact hKbound σ hσ
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
  have heq (σ : ℝ) (hσ : σ ≠ 0) (t : ℝ) :
      H ((σ : ℂ) + (t : ℂ) * I) = Gamma ((σ : ℂ) + (t : ℂ) * I) *
        f ((σ : ℂ) + (t : ℂ) * I) * (X : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) :=
    hHeq _ (fun he => hσ (by simpa using congrArg Complex.re he))
  have heqa := heq a ha0.ne
  have heqb := heq b hb.ne'
  refine ⟨by simpa only [heqa] using hia, by simpa only [heqb] using hib, ?_⟩
  have he := rectangle_limits H hab hHs
    (intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id)
    (intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id)
    (by simpa using horizontal_decay_limit H a b D (-1) hab (by norm_num) hbound)
    (by simpa using horizontal_decay_limit H a b D 1 hab (by norm_num) hbound)
  simpa only [heqa, heqb] using he.symm


end

end DedekindZetaZeroFree.Quantitative.GammaZeroContour
