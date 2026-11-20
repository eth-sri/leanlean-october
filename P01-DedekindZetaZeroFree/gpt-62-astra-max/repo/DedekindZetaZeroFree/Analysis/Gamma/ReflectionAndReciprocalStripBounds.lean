module
public import DedekindZetaZeroFree.Analysis.Gamma.ElementaryNormBounds

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

@[expose] public section

/-
Statements adapted from OpenAI's `openai/math` repository (Apache 2.0).
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean#L292-L444
-/

/-
Repository: openai/math.
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/Mellin/VerticalContourShift.lean.
-/

namespace DedekindZetaZeroFree.GammaBounds

open scoped BigOperators
open MeasureTheory

section

variable (z : ℂ)

theorem norm_Gamma_le_real (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by exact gamma_norm_le_real hz

theorem norm_sin_le_exp_abs_im :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by exact complex_sin_norm_le_exp_im z

theorem Gamma_ne_zero_of_im_ne_zero (hz : z.im ≠ 0) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n he
  apply hz
  simpa using (congrArg Complex.im he)

theorem inverse_Gamma_reflection (hz : z.im ≠ 0) :
    (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
  have hg:=Gamma_ne_zero_of_im_ne_zero z hz
  have hh:=Gamma_ne_zero_of_im_ne_zero (1-z) (by simpa using hz)
  have hs : Complex.sin (Real.pi*z)≠0 := by
    intro hs
    have he:=Complex.Gamma_mul_Gamma_one_sub z
    rw [hs,div_zero] at he
    exact (mul_ne_zero hg hh) he
  apply mul_left_cancel₀ hg
  rw [mul_inv_cancel₀ hg]
  symm
  calc
    _ = (Complex.Gamma z*Complex.Gamma (1-z))*Complex.sin (Real.pi*z)/Real.pi := by ring
    _ = 1 := by
      simp_all [Complex.Gamma_mul_Gamma_one_sub]

theorem inverse_Gamma_norm_of_left (hz : z.re < 1) (hi : z.im ≠ 0) :
    ‖(Complex.Gamma z)⁻¹‖ ≤
      (Real.Gamma (1 - z.re) / Real.pi) * Real.exp (Real.pi * |z.im|) := by
  rw [inverse_Gamma_reflection z hi,norm_div,norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le]
  have hgamma:=norm_Gamma_le_real (1-z) (by simp;linarith)
  have hsin:=norm_sin_le_exp_abs_im (Real.pi*z)
  simp only [Complex.sub_re,Complex.one_re] at hgamma
  have him : |((Real.pi:ℂ)*z).im|=Real.pi*|z.im| := by
    simp [abs_mul]
  rw [him] at hsin
  calc
    _ ≤ (Real.Gamma (1-z.re)*Real.exp (Real.pi*|z.im|))/Real.pi :=
      div_le_div_of_nonneg_right
        (mul_le_mul hgamma hsin (norm_nonneg _) (Real.Gamma_pos_of_pos (by linarith)).le)
        Real.pi_pos.le
    _ = _ := by ring

theorem inverse_Gamma_shift (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ k ∈ Finset.range n, (z + (k : ℂ))) * (Complex.Gamma (z + (n : ℂ)))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Finset.prod_range_succ]
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + (n : ℂ))]
    simp only [add_assoc, mul_assoc]

theorem inverse_Gamma_norm_le_shift_left (n : ℕ) (hi : 1 ≤ |z.im|) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ ‖(Complex.Gamma (z - (n : ℂ)))⁻¹‖ := by
  have he:=congrArg norm (inverse_Gamma_shift (z-n) n)
  simp only [sub_add_cancel,norm_mul] at he
  rw [he]
  refine le_mul_of_one_le_left (norm_nonneg _) ?_
  rw [norm_prod]
  apply Finset.one_le_prod₀
  intro k hk
  calc
    1 ≤ |z.im| := hi
    _ = |(z-(n:ℂ)+k).im| := by simp
    _ ≤ _ := Complex.abs_im_le_norm _

end

variable (a b : ℝ)

theorem real_Gamma_compact_bound (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc a b, Real.Gamma x ≤ C := by exact gamma_real_interval_bound ha

theorem inverse_Gamma_compact_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc a b, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ‖(Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤ C := by
  have hc : Continuous (fun p : ℝ×ℝ=>
      ‖(Complex.Gamma ((p.1:ℂ)+p.2*Complex.I))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)).norm
  obtain ⟨C,hC⟩:=((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))).bddAbove_image hc.continuousOn
  refine ⟨|C|+1,by positivity,?_⟩
  intro σ hσ t ht
  exact (hC ⟨(σ,t),⟨hσ,ht⟩,rfl⟩).trans (by linarith [le_abs_self C])

theorem inverse_Gamma_strip_exp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖(Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
        C * Real.exp (Real.pi * |t|) := by
  obtain ⟨n,hn⟩:=exists_nat_gt b
  obtain ⟨Cg,hCg,hg⟩:=real_Gamma_compact_bound ((n:ℝ)+1-b) ((n:ℝ)+1-a) (by linarith)
  obtain ⟨Cc,hCc,hc⟩:=inverse_Gamma_compact_strip_bound a b
  refine ⟨Cc+Cg/Real.pi,by positivity,?_⟩
  intro σ hσ t
  by_cases ht:|t|≤1
  · exact le_trans (le_trans (hc σ hσ t (abs_le.mp ht)) (le_add_of_nonneg_right (by positivity))) (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
  · have ht1 :=lt_of_not_ge ht
    let z := (σ:ℂ)+t*Complex.I
    let w := z-n
    have hw : w.re<1 := by
      dsimp [w,z]
      simp only [Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
        sub_zero,add_zero]
      linarith [hσ.2]
    have hwi : w.im≠0 := by simpa [w,z] using (by intro ht0;subst t;norm_num at ht1)
    have he : 1-w.re=(n:ℝ)+1-σ := by simp [w,z];ring
    have hi : w.im=t := by simp [w,z]
    have hbound:=inverse_Gamma_norm_of_left w hw hwi
    rw [he,hi] at hbound
    have hgbound:=hg ((n:ℝ)+1-σ) ⟨by linarith [hσ.2],by linarith [hσ.1]⟩
    calc
      _ ≤ ‖(Complex.Gamma w)⁻¹‖ :=
        inverse_Gamma_norm_le_shift_left z n (by simpa [z] using ht1.le)
      _ ≤ (Real.Gamma ((n:ℝ)+1-σ)/Real.pi)*Real.exp (Real.pi*|t|) := hbound
      _ ≤ (Cg/Real.pi)*Real.exp (Real.pi*|t|) := by gcongr
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCc.le) (Real.exp_pos _).le

theorem inverse_Gamma_strip_exp_bound_complex :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Set.Icc a b →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨C,hC,hb⟩:=inverse_Gamma_strip_exp_bound a b
  refine ⟨C,hC,?_⟩
  intro z hz
  simpa using hb z.re hz z.im

end DedekindZetaZeroFree.GammaBounds
