module

public import RequestProject.BallZarnescu
public import RequestProject.Rellich
public import RequestProject.Approximation
public import RequestProject.WeakCompact
public import RequestProject.BiLipschitz
public import RequestProject.ChainRule
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions

@[expose] public section

open scoped ComplexConjugate
open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

private lemma det_eq_of_clm (T : ℂ →L[ℝ] ℂ) :
    T.det = (T 1).re * (T Complex.I).im - (T Complex.I).re * (T 1).im := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]

private def cofMat (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![b ^ 2 + d ^ 2, -(a * b + c * d); -(a * b + c * d), a ^ 2 + c ^ 2]

private lemma norm_sq_comb_le (a c : ℝ) (P R : ℂ) :
    ‖(a : ℂ) * P - c * R‖ ^ 2 ≤ (a ^ 2 + c ^ 2) * (‖P‖ ^ 2 + ‖R‖ ^ 2) := by
  have h1 : ‖(a : ℂ) * P - c * R‖ ≤ |a| * ‖P‖ + |c| * ‖R‖ :=
    (norm_sub_le _ _).trans_eq (by simp [Complex.norm_real])
  calc ‖(a : ℂ) * P - c * R‖ ^ 2 ≤ (|a| * ‖P‖ + |c| * ‖R‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (a ^ 2 + c ^ 2) * (‖P‖ ^ 2 + ‖R‖ ^ 2) := by
      rw [← sq_abs a, ← sq_abs c]
      nlinarith [sq_nonneg (|a| * ‖R‖ - |c| * ‖P‖)]

private def bzCoef (T : ℂ →L[ℝ] ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  |T.det|⁻¹ • cofMat (T 1).re (T Complex.I).re (T 1).im (T Complex.I).im

private lemma sesq_bzCoef (T : ℂ →L[ℝ] ℂ) (ξ : Fin 2 → ℂ) :
    (∑ i, ∑ k, ((bzCoef T) i k : ℂ) * inner ℂ (ξ i) (ξ k)) =
      ((|T.det|⁻¹ * (‖(T Complex.I).im * ξ 0 - (T 1).im * ξ 1‖ ^ 2 +
        ‖(T Complex.I).re * ξ 0 - (T 1).re * ξ 1‖ ^ 2) : ℝ) : ℂ) := by
  have h (a b c d : ℝ) :
      (∑ i, ∑ k, ((cofMat a b c d) i k : ℂ) * inner ℂ (ξ i) (ξ k)) =
        ((‖d * ξ 0 - c * ξ 1‖ ^ 2 + ‖b * ξ 0 - a * ξ 1‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Fin.sum_univ_two, cofMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, RCLike.inner_apply]
    push_cast
    rw [← Complex.conj_mul', ← Complex.conj_mul']
    simp only [map_sub, map_mul, Complex.conj_ofReal]; ring
  simp only [bzCoef, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc,
    ← Finset.mul_sum, h]

private lemma sesq_bzCoef_chain (T : ℂ →L[ℝ] ℂ) (hT : T.det ≠ 0) (y : Fin 2 → ℂ) :
    (∑ i, ∑ k, ((bzCoef T) i k : ℂ) *
      inner ℂ (∑ j, (coordRe j (T (coordDir i)) : ℂ) * y j)
        (∑ j, (coordRe j (T (coordDir k)) : ℂ) * y j)) =
      ((|T.det| * ∑ j, ‖y j‖ ^ 2 : ℝ) : ℂ) := by
  have h (a b c d : ℝ) :
      (∑ i, ∑ k, ((cofMat a b c d) i k : ℂ) *
        inner ℂ (![a * y 0 + c * y 1, b * y 0 + d * y 1] i)
          (![a * y 0 + c * y 1, b * y 0 + d * y 1] k)) =
        (((a * d - b * c) ^ 2 : ℝ) : ℂ) * (conj (y 0) * y 0 + conj (y 1) * y 1) := by
    simp only [Fin.sum_univ_two, cofMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      RCLike.inner_apply, map_add, map_mul, Complex.conj_ofReal]
    push_cast; ring
  have hg : ∀ i, (∑ j, (coordRe j (T (coordDir i)) : ℂ) * y j) =
      ![(T 1).re * y 0 + (T 1).im * y 1, (T Complex.I).re * y 0 + (T Complex.I).im * y 1] i := by
    intro i; fin_cases i <;> simp [coordRe, coordDir, Fin.sum_univ_two]
  simp only [hg, bzCoef, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc,
    ← Finset.mul_sum]
  rw [h, ← det_eq_of_clm, Fin.sum_univ_two, Complex.conj_mul', Complex.conj_mul']
  have h2 : ((T.det : ℝ) : ℂ) ^ 2 = ((|T.det| : ℝ) : ℂ) ^ 2 := by exact_mod_cast (sq_abs T.det).symm
  have hδc : ((|T.det| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hT
  push_cast; rw [h2]; field_simp

private lemma re_im_sq_le_opNorm (T : ℂ →L[ℝ] ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    (T z).re ^ 2 + (T z).im ^ 2 ≤ ‖T‖ ^ 2 := by
  have h1 : ‖T z‖ ≤ ‖T‖ := by simpa [hz] using T.le_opNorm z
  have h2 := Complex.sq_norm (T z)
  rw [Complex.normSq_apply] at h2
  nlinarith [norm_nonneg (T z)]

private lemma bzCoef_ellip (T : ℂ →L[ℝ] ℂ) (hT : T.det ≠ 0) (ξ : Fin 2 → ℂ) :
    |T.det| * ∑ i, ‖ξ i‖ ^ 2 ≤
      2 * ‖T‖ ^ 2 * (∑ i, ∑ k, ((bzCoef T) i k : ℂ) * inner ℂ (ξ i) (ξ k)).re := by
  rw [sesq_bzCoef, Complex.ofReal_re, Fin.sum_univ_two]
  set a := (T 1).re; set b := (T Complex.I).re; set c := (T 1).im; set d := (T Complex.I).im
  set P := (d : ℂ) * ξ 0 - c * ξ 1; set R := (b : ℂ) * ξ 0 - a * ξ 1
  set Q := ‖P‖ ^ 2 + ‖R‖ ^ 2
  have n0 : (a * d - b * c) ^ 2 * ‖ξ 0‖ ^ 2 = ‖(a : ℂ) * P - c * R‖ ^ 2 := by
    rw [show (a : ℂ) * P - c * R = ((a * d - b * c : ℝ) : ℂ) * ξ 0 by
      simp only [P, R]; push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have n1 : (a * d - b * c) ^ 2 * ‖ξ 1‖ ^ 2 = ‖(b : ℂ) * P - d * R‖ ^ 2 := by
    rw [show (b : ℂ) * P - d * R = ((a * d - b * c : ℝ) : ℂ) * ξ 1 by
      simp only [P, R]; push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hlow : |T.det| ^ 2 * (‖ξ 0‖ ^ 2 + ‖ξ 1‖ ^ 2) ≤ (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * Q := by
    rw [sq_abs, det_eq_of_clm]
    nlinarith [norm_sq_comb_le a c P R, norm_sq_comb_le b d P R]
  have hQ : 0 ≤ Q := by positivity
  have hδ : 0 < |T.det| := abs_pos.mpr hT
  have key : |T.det| ^ 2 * (‖ξ 0‖ ^ 2 + ‖ξ 1‖ ^ 2) ≤ 2 * ‖T‖ ^ 2 * Q :=
    hlow.trans (by gcongr; linarith [re_im_sq_le_opNorm T norm_one, re_im_sq_le_opNorm T Complex.norm_I])
  rw [show 2 * ‖T‖ ^ 2 * (|T.det|⁻¹ * Q) = (2 * ‖T‖ ^ 2 * Q) / |T.det| by field_simp,
    le_div_iff₀ hδ]
  nlinarith

private lemma abs_bzCoef_le (T : ℂ →L[ℝ] ℂ) (i k : Fin 2) :
    |bzCoef T i k| ≤ 2 * ‖T‖ ^ 2 / |T.det| := by
  have h1 := re_im_sq_le_opNorm T norm_one
  have h2 := re_im_sq_le_opNorm T Complex.norm_I
  simp only [bzCoef, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_abs]
  rw [inv_mul_eq_div]; gcongr
  fin_cases i <;> fin_cases k <;>
    simp only [cofMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one] <;>
    rw [abs_le] <;> constructor <;>
    nlinarith [sq_nonneg ((T 1).re + (T Complex.I).re), sq_nonneg ((T 1).im + (T Complex.I).im),
      sq_nonneg ((T 1).re - (T Complex.I).re), sq_nonneg ((T 1).im - (T Complex.I).im),
      sq_nonneg (T 1).re, sq_nonneg (T Complex.I).re, sq_nonneg (T 1).im, sq_nonneg (T Complex.I).im]

private lemma bzCoef_id : bzCoef (ContinuousLinearMap.id ℝ ℂ) = 1 := by
  have hdet : (ContinuousLinearMap.id ℝ ℂ).det = 1 := by rw [det_eq_of_clm]; simp
  ext i k; fin_cases i <;> fin_cases k <;> simp [bzCoef, hdet, cofMat]

private lemma measurable_bzCoef (i k : Fin 2) : Measurable fun T : ℂ →L[ℝ] ℂ => bzCoef T i k := by
  have hc : Continuous fun T : ℂ →L[ℝ] ℂ =>
      cofMat (T 1).re (T Complex.I).re (T 1).im (T Complex.I).im i k := by
    fin_cases i <;> fin_cases k <;> simp [cofMat] <;> fun_prop
  simp only [bzCoef, Matrix.smul_apply, smul_eq_mul]
  exact ContinuousLinearMap.continuous_det.measurable.norm.inv.mul hc.measurable

private def coefSesq (M : Matrix (Fin 2) (Fin 2) ℝ) (ξ η : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ k, (M i k : ℂ) * inner ℂ (ξ i) (η k)

private def gradForm (Ω : Set ℂ) (M : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → L2 Ω) : ℝ :=
  (∫ w in Ω, coefSesq (M w) (fun i => (g i : ℂ → ℂ) w) (fun i => (g i : ℂ → ℂ) w)).re

private lemma bzChainRule_of_bilip {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ ≃ₜ ℂ} {K : NNReal}
    (hK : 0 < K) (hf : LipschitzOnWith K f Ω) (hg : LipschitzOnWith K f.symm (f '' Ω))
    (v : L2 (f '' Ω)) :
    let u := bilipPull hΩ hK hf hg v
    (v ∈ H1 (f '' Ω) ↔ u ∈ H1 Ω) ∧
      ∀ g : Fin 2 → L2 Ω, IsWeakGradient Ω u g →
        neumannEnergy (f '' Ω) v =
          ENNReal.ofReal (gradForm Ω (fun w => bzCoef (fderiv ℝ f w)) g) := by
  dsimp only
  set u := bilipPull hΩ hK hf hg v
  have hu := bilipPull_ae hΩ hK hf hg v
  have hΩ' : IsOpen (f '' Ω) := f.isOpenMap Ω hΩ
  have hback : u ∈ H1 Ω → v ∈ H1 (f '' Ω) := by
    rintro ⟨g, hg'⟩
    have hv : (v : ℂ → ℂ) =ᵐ[volume.restrict (f '' Ω)] fun y => (u : ℂ → ℂ) (f.symm y) :=
      ((quasiMeasurePreserving_symm_restrict hf).ae_eq hu).mono fun _ hy => by simpa using hy.symm
    obtain ⟨G, hG, -⟩ := exists_isWeakGradient_comp_bilip (f := f.symm) (Ω := f '' Ω)
      (f.symm_image_image Ω) hΩ' hK hg (by simpa using hf) hg' hv
    exact ⟨G, hG⟩
  refine ⟨⟨fun ⟨G, hG⟩ => by
      obtain ⟨g, hg', -⟩ := exists_isWeakGradient_comp_bilip rfl hΩ hK hf hg hG hu
      exact ⟨g, hg'⟩, hback⟩, fun g hgu => ?_⟩
  obtain ⟨G, hG⟩ := hback ⟨g, hgu⟩
  obtain ⟨g', hg', hg'eq⟩ := exists_isWeakGradient_comp_bilip rfl hΩ hK hf hg hG hu
  obtain rfl := hgu.unique hΩ hg'
  rw [neumannEnergy_eq_of_isWeakGradient hΩ' hG]
  have hdet : ∀ᵐ w ∂(volume.restrict Ω), (fderiv ℝ f w).det ≠ 0 :=
    (ae_inv_sq_le_abs_det hΩ hf hg).mono fun _ hw =>
      abs_pos.mp (lt_of_lt_of_le (by positivity) hw)
  have hpt : ∀ᵐ w ∂(volume.restrict Ω),
      coefSesq (bzCoef (fderiv ℝ f w)) (fun i => (g i : ℂ → ℂ) w) (fun i => (g i : ℂ → ℂ) w) =
        |(fderiv ℝ f w).det| • ∑ j, inner ℂ ((G j : ℂ → ℂ) (f w)) ((G j : ℂ → ℂ) (f w)) := by
    filter_upwards [hdet, ae_all_iff.2 hg'eq] with w hw hgw
    simp only [coefSesq, hgw, chainGrad]
    rw [sesq_bzCoef_chain _ hw]
    simp only [inner_self_eq_norm_sq_to_K, Complex.real_smul]
    push_cast; rfl
  have hform : gradForm Ω (fun w => bzCoef (fderiv ℝ f w)) g = ∑ j, ‖G j‖ ^ 2 := by
    rw [gradForm, integral_congr_ae hpt, ← integral_image_bilip hΩ hf
      (fun y => ∑ j, inner ℂ ((G j : ℂ → ℂ) y) ((G j : ℂ → ℂ) y)),
      integral_finset_sum _ (fun j _ => L2.integrable_inner (G j) (G j))]
    simp only [L2.inner_def, Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => (norm_sq_eq_re_inner (𝕜 := ℂ) (G j)).symm
  rw [hform, ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl

section GradForm

variable {Ω : Set ℂ} {M : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {C : ℝ}

private lemma coefSesq_one (ξ η : Fin 2 → ℂ) : coefSesq 1 ξ η = ∑ i, inner ℂ (ξ i) (η i) := by
  simp [coefSesq, Matrix.one_apply]

private lemma integrable_coefSesq
    (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C) (g h : Fin 2 → L2 Ω) :
    Integrable (fun w => coefSesq (M w) (fun i => (g i : ℂ → ℂ) w) (fun i => (h i : ℂ → ℂ) w))
      (volume.restrict Ω) :=
  integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ =>
    (L2.integrable_inner (g i) (h k)).bdd_mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (hMm i k))
      (hMb.mono fun w hw => by simpa [Complex.norm_real] using hw i k)

private def gradSesq (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C) :
    (Fin 2 → L2 Ω) →ₗ⋆[ℂ] (Fin 2 → L2 Ω) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun g h => ∫ w in Ω, coefSesq (M w) (fun i => (g i : ℂ → ℂ) w) (fun i => (h i : ℂ → ℂ) w))
    (fun g₁ g₂ _ => by
      rw [← integral_add (integrable_coefSesq hMm hMb _ _) (integrable_coefSesq hMm hMb _ _)]
      refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.mpr fun i => Lp.coeFn_add (g₁ i) (g₂ i)] with _ hw
      simp only [coefSesq, Pi.add_apply, hw, inner_add_left, mul_add, Finset.sum_add_distrib])
    (fun c g _ => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.mpr fun i => Lp.coeFn_smul c (g i)] with _ hw
      simp only [coefSesq, Pi.smul_apply, hw, inner_smul_left, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun _ h₁ h₂ => by
      rw [← integral_add (integrable_coefSesq hMm hMb _ _) (integrable_coefSesq hMm hMb _ _)]
      refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.mpr fun i => Lp.coeFn_add (h₁ i) (h₂ i)] with _ hw
      simp only [coefSesq, Pi.add_apply, hw, inner_add_right, mul_add, Finset.sum_add_distrib])
    (fun c _ h => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.mpr fun i => Lp.coeFn_smul c (h i)] with _ hw
      simp only [coefSesq, Pi.smul_apply, hw, inner_smul_right, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

private lemma gradForm_smul
    (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C) (c : ℂ) (g : Fin 2 → L2 Ω) :
    gradForm Ω M (c • g) = ‖c‖ ^ 2 * gradForm Ω M g := by
  change (gradSesq hMm hMb (c • g) (c • g)).re = ‖c‖ ^ 2 * (gradSesq hMm hMb g g).re
  simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
  rw [← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

private lemma gradForm_one (g : Fin 2 → L2 Ω) : gradForm Ω 1 g = ∑ i, ‖g i‖ ^ 2 := by
  unfold gradForm
  simp only [Pi.one_apply, coefSesq_one]
  rw [integral_finset_sum _ fun i _ => L2.integrable_inner (g i) (g i), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← L2.inner_def, inner_self_eq_norm_sq_to_K]; norm_cast

private lemma integral_restrict_le_gradForm
    (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C)
    (hMp : ∀ᵐ w ∂(volume.restrict Ω), ∀ ξ : Fin 2 → ℂ, 0 ≤ (coefSesq (M w) ξ ξ).re)
    (hΩ : MeasurableSet Ω) {F : Set ℂ} (hF : MeasurableSet F)
    (hMF : ∀ w ∈ Ω, w ∈ F → M w = 1) (g : Fin 2 → L2 Ω) :
    ∑ i, ∫ w in F, ‖(g i : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) ≤ gradForm Ω M g := by
  have hint : ∀ i, Integrable (fun w => ‖(g i : ℂ → ℂ) w‖ ^ 2) (volume.restrict Ω) := fun i =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp (g i))
  rw [← integral_finset_sum _ fun i _ => (hint i).integrableOn, ← integral_indicator hF, gradForm]
  refine (integral_mono_ae ((integrable_finset_sum _ fun i _ => hint i).indicator hF)
    (integrable_coefSesq hMm hMb g g).re ?_).trans_eq
    (integral_re (integrable_coefSesq hMm hMb g g))
  filter_upwards [hMp, ae_restrict_mem hΩ] with w hw hwΩ
  by_cases hwF : w ∈ F
  · rw [Set.indicator_of_mem hwF, hMF w hwΩ hwF, coefSesq_one, map_sum]
    exact le_of_eq (Finset.sum_congr rfl fun _ _ => (inner_self_eq_norm_sq _).symm)
  · rw [Set.indicator_of_notMem hwF]; exact hw _

private lemma tendsto_integral_coefSesq (M : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hMm : ∀ n i k, AEStronglyMeasurable (fun w => M n w i k) (volume.restrict Ω))
    (hMb : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M n w i k| ≤ C)
    (hev : ∀ᵐ w ∂(volume.restrict Ω), ∀ᶠ n in atTop, M n w = 1) (g h : Fin 2 → L2 Ω) :
    Tendsto (fun n => ∫ w in Ω, coefSesq (M n w) (fun i => (g i : ℂ → ℂ) w)
      (fun i => (h i : ℂ → ℂ) w)) atTop
      (𝓝 (∫ w in Ω, coefSesq 1 (fun i => (g i : ℂ → ℂ) w) (fun i => (h i : ℂ → ℂ) w))) := by
  refine tendsto_integral_of_dominated_convergence
    (fun w => C * ∑ i, ∑ k, ‖inner ℂ ((g i : ℂ → ℂ) w) ((h k : ℂ → ℂ) w)‖)
    (fun n => (integrable_coefSesq (hMm n) (hMb n) g h).aestronglyMeasurable)
    ((integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ =>
      (L2.integrable_inner (g i) (h k)).norm).const_mul C) (fun n => ?_) ?_
  · filter_upwards [hMb n] with w hw
    unfold coefSesq
    calc _ ≤ ∑ i, ∑ k, ‖((M n w i k : ℝ) : ℂ) *
          inner ℂ ((g i : ℂ → ℂ) w) ((h k : ℂ → ℂ) w)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
      _ ≤ ∑ i, ∑ k, C * ‖inner ℂ ((g i : ℂ → ℂ) w) ((h k : ℂ → ℂ) w)‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hw i k) (norm_nonneg _)
      _ = _ := by simp_rw [Finset.mul_sum]
  · filter_upwards [hev] with w hw
    exact tendsto_const_nhds.congr' (hw.mono fun _ hn => by simp only [hn])

end GradForm

private def gradOf {Ω : Set ℂ} (hΩ : IsOpen Ω) (S : Submodule ℂ (L2 Ω))
    (hS : (S : Set (L2 Ω)) ⊆ H1 Ω) : S →ₗ[ℂ] (Fin 2 → L2 Ω) where
  toFun u := (hS u.2).choose
  map_add' u v := (hS (u + v).2).choose_spec.unique hΩ (by
    simpa using (hS u.2).choose_spec.add (hS v.2).choose_spec)
  map_smul' c u := (hS (c • u).2).choose_spec.unique hΩ (by
    simpa using (hS u.2).choose_spec.smul c)

private theorem exists_common_subseq {ι : Type*} [Fintype ι] (P : ι → (ℕ → ℕ) → Prop)
    (hmono : ∀ i (θ θ' : ℕ → ℕ), P i θ → StrictMono θ' → P i (θ ∘ θ'))
    (hex : ∀ i (θ : ℕ → ℕ), StrictMono θ → ∃ θ' : ℕ → ℕ, StrictMono θ' ∧ P i (θ ∘ θ')) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i, P i θ := by
  classical
  suffices h : ∀ s : Finset ι, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i ∈ s, P i θ from
    let ⟨θ, hθ, hP⟩ := h Finset.univ; ⟨θ, hθ, fun i => hP i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert a s _ ih =>
    obtain ⟨θ, hθ, hP⟩ := ih
    obtain ⟨θ', hθ', hP'⟩ := hex a θ hθ
    exact ⟨θ ∘ θ', hθ.comp hθ', fun i hi =>
      (Finset.mem_insert.mp hi).elim (· ▸ hP') (fun hi => hmono i θ θ' (hP i hi) hθ')⟩

private lemma integral_norm_sq_eq_of {μ : Measure ℂ} (u : Lp ℂ 2 μ) :
    ∫ w, ‖(u : ℂ → ℂ) w‖ ^ 2 ∂μ = ‖u‖ ^ 2 := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) u u)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner u u)] at h
  simp_rw [inner_self_eq_norm_sq] at h
  exact h.symm

private lemma weak_lsc_restrict {Ω : Set ℂ} {x : ℕ → L2 Ω} {y : L2 Ω}
    (hx : ∀ z, Tendsto (fun n => inner ℂ z (x n)) atTop (𝓝 (inner ℂ z y))) (F : Set ℂ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∫ w in F, ‖(y : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) - ε ≤
      ∫ w in F, ‖(x n : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) := by
  intro ε hε
  set T := LpToLpRestrictCLM ℂ ℂ ℂ (volume.restrict Ω) 2 F
  have hT : ∀ v : L2 Ω, ∫ w in F, ‖(v : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) = ‖T v‖ ^ 2 := fun v => by
    rw [← integral_norm_sq_eq_of (T v)]
    refine integral_congr_ae ?_
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ F v] with w hw
    rw [hw]
  simp_rw [hT]
  have hwT : Tendsto (fun n => inner ℂ (T y) (T (x n))) atTop (𝓝 (inner ℂ (T y) (T y))) := by
    simp_rw [← ContinuousLinearMap.adjoint_inner_left]; exact hx _
  have h := (Complex.continuous_re.tendsto _).comp hwT
  rw [show (inner ℂ (T y) (T y) : ℂ).re = ‖T y‖ ^ 2 by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast] at h
  filter_upwards [h.eventually (lt_mem_nhds (show ‖T y‖ ^ 2 - ε / 2 < ‖T y‖ ^ 2 by linarith))]
    with n hn
  have h1 := re_inner_le_norm (𝕜 := ℂ) (T y) (T (x n))
  change ‖T y‖ ^ 2 - ε / 2 < RCLike.re (inner ℂ (T y) (T (x n))) at hn
  nlinarith [sq_nonneg (‖T y‖ - ‖T (x n)‖)]

private lemma isWeakGradient_of_weak_tendsto {Ω : Set ℂ} {u : ℕ → L2 Ω} {g : ℕ → Fin 2 → L2 Ω}
    {U : L2 Ω} {G : Fin 2 → L2 Ω} (hg : ∀ n, IsWeakGradient Ω (u n) (g n))
    (hu : Tendsto u atTop (𝓝 U))
    (hG : ∀ i z, Tendsto (fun n => inner ℂ z (g n i)) atTop (𝓝 (inner ℂ z (G i)))) :
    IsWeakGradient Ω U G := by
  intro φ hφ i
  have hmem : ∀ ψ : ℂ → ℂ, Continuous ψ → HasCompactSupport ψ →
      MemLp (fun w => (starRingEnd ℂ) (ψ w)) 2 (volume.restrict Ω) := fun ψ hc hs =>
    ((Complex.continuous_conj.comp hc).memLp_of_hasCompactSupport
      (hs.comp_left (map_zero _))).restrict Ω
  have key : ∀ (ψ : ℂ → ℂ) (hψ : MemLp (fun w => (starRingEnd ℂ) (ψ w)) 2 (volume.restrict Ω))
      (H : L2 Ω), ∫ w in Ω, H w * ψ w = inner ℂ (hψ.toLp _) H := fun _ hψ H => by
    rw [L2.inner_def]
    exact integral_congr_ae (hψ.coeFn_toLp.mono fun _ hw => by simp [hw])
  have hd : Continuous fun w => fderiv ℝ φ w (coordDir i) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport fun w => fderiv ℝ φ w (coordDir i) :=
    (hφ.2.1.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℂ => T (coordDir i)) rfl
  have h2 : Tendsto (fun n => -∫ w in Ω, g n i w * φ w) atTop (𝓝 (-∫ w in Ω, G i w * φ w)) := by
    simp_rw [key φ (hmem _ hφ.1.continuous hφ.2.1)]; exact (hG i _).neg
  exact tendsto_nhds_unique (tendsto_integral_mul (hmem _ hd hds) hu)
    (h2.congr fun n => (hg n φ hφ i).symm)

private lemma tendsto_weighted_inner {Ω : Set ℂ} (ρ : ℕ → ℂ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hm : ∀ n, AEStronglyMeasurable (ρ n) (volume.restrict Ω))
    (hb : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), |ρ n w| ≤ C)
    (ht : ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => ρ n w) atTop (𝓝 1))
    {x y : ℕ → L2 Ω} {X Y : L2 Ω} (hx : Tendsto x atTop (𝓝 X)) (hy : Tendsto y atTop (𝓝 Y)) :
    Tendsto (fun n => ∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((x n : ℂ → ℂ) w) ((y n : ℂ → ℂ) w))
      atTop (𝓝 (inner ℂ X Y)) := by
  have hmul_le (u v : L2 Ω) : ∫ w in Ω, ‖(u : ℂ → ℂ) w‖ * ‖(v : ℂ → ℂ) w‖ ≤ ‖u‖ * ‖v‖ := by
    have h2 : ENNReal.ofReal 2 = 2 := by simp
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict Ω) (f := (u : ℂ → ℂ))
      (g := (v : ℂ → ℂ)) Real.HolderConjugate.two_two (by rw [h2]; exact Lp.memLp u)
      (by rw [h2]; exact Lp.memLp v)
    simp_rw [Real.rpow_two] at h
    rwa [integral_norm_sq_eq_of, integral_norm_sq_eq_of, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  have hE : Tendsto (fun n => ∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w))
      atTop (𝓝 (inner ℂ X Y)) := by
    rw [L2.inner_def]
    refine tendsto_integral_of_dominated_convergence
      (fun w => C * ‖inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w)‖)
      (fun n => (integrable_weight_inner (hm n) (hb n) _ _).aestronglyMeasurable)
      ((L2.integrable_inner X Y).norm.const_mul C) (fun n => ?_) ?_
    · filter_upwards [hb n] with _ hw
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    · filter_upwards [ht] with w hw
      simpa using ((Complex.continuous_ofReal.tendsto 1).comp hw).mul_const
        (inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w))
  have hD : Tendsto (fun n => C * (‖x n - X‖ * ‖y n‖ + ‖X‖ * ‖y n - Y‖)) atTop (𝓝 0) := by
    simpa using (((tendsto_iff_norm_sub_tendsto_zero.mp hx).mul hy.norm).add
      ((tendsto_const_nhds (x := ‖X‖)).mul
        (tendsto_iff_norm_sub_tendsto_zero.mp hy))).const_mul C
  have hintL2 (u v : L2 Ω) : Integrable (fun w => ‖(u : ℂ → ℂ) w‖ * ‖(v : ℂ → ℂ) w‖)
      (volume.restrict Ω) := (Lp.memLp u).norm.integrable_mul (Lp.memLp v).norm
  have hbound : ∀ n, ‖(∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((x n : ℂ → ℂ) w) ((y n : ℂ → ℂ) w)) -
      ∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w)‖ ≤
      C * (‖x n - X‖ * ‖y n‖ + ‖X‖ * ‖y n - Y‖) := fun n => by
    rw [← integral_sub (integrable_weight_inner (hm n) (hb n) _ _)
      (integrable_weight_inner (hm n) (hb n) _ _)]
    refine (norm_integral_le_of_norm_le (((hintL2 (x n - X) (y n)).add
      (hintL2 X (y n - Y))).const_mul C) ?_).trans ?_
    · filter_upwards [hb n, Lp.coeFn_sub (x n) X, Lp.coeFn_sub (y n) Y] with w hw h1 h2
      simp only [Pi.add_apply]
      rw [h1, h2, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Pi.sub_apply, Pi.sub_apply]
      refine mul_le_mul hw ?_ (norm_nonneg _) hC
      rw [show inner ℂ ((x n : ℂ → ℂ) w) ((y n : ℂ → ℂ) w) - inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w) =
        inner ℂ ((x n : ℂ → ℂ) w - (X : ℂ → ℂ) w) ((y n : ℂ → ℂ) w) +
          inner ℂ ((X : ℂ → ℂ) w) ((y n : ℂ → ℂ) w - (Y : ℂ → ℂ) w) by
        rw [inner_sub_left, inner_sub_right]; ring]
      exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    · simp only [Pi.add_apply]
      rw [integral_const_mul, integral_add (hintL2 _ _) (hintL2 _ _)]
      exact mul_le_mul_of_nonneg_left (add_le_add (hmul_le _ _) (hmul_le _ _)) hC
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add_left (hbound n) _))
    (by simpa using hD.add (tendsto_iff_norm_sub_tendsto_zero.mp hE))

private def bzDensity {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (n : ℕ) : ℂ → ℝ :=
  fun w => |(fderiv ℝ (A.map n) w).det|

private lemma bzDensity_aestronglyMeasurable {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (n : ℕ) :
    AEStronglyMeasurable (bzDensity A n) (volume.restrict Ω) :=
  ((continuous_abs.comp ContinuousLinearMap.continuous_det).measurable.comp
    (measurable_fderiv ℝ _)).aestronglyMeasurable

private lemma bzDensity_bound {Ω : Set ℂ} (hΩ : IsOpen Ω) (A : BallZarnescuApprox Ω) (n : ℕ) :
    ∀ᵐ w ∂(volume.restrict Ω), |bzDensity A n w| ≤ (A.lip : ℝ) ^ 2 :=
  ae_restrict_of_forall_mem hΩ.measurableSet fun w hw => by
    rw [bzDensity, abs_abs]
    exact abs_det_fderiv_le hΩ ((A.lipschitz n).mono subset_closure) hw

private lemma bzDensity_tendsto {Ω : Set ℂ} (hΩ : IsOpen Ω) (A : BallZarnescuApprox Ω) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) :
    ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => bzDensity A (ψ n) w) atTop (𝓝 1) := by
  refine ae_restrict_of_forall_mem hΩ.measurableSet fun w hw => tendsto_const_nhds.congr' ?_
  filter_upwards [hψ.eventually (A.collar_shrink w hw)] with n hn
  have hloc : (A.map (ψ n) : ℂ → ℂ) =ᶠ[𝓝 w] id :=
    Filter.mem_of_superset ((A.collar_closed _).isOpen_compl.mem_nhds hn) (A.eq_self _)
  rw [bzDensity, hloc.fderiv_eq, fderiv_id, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
    LinearMap.det_id, abs_one]

private def collarFree {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (N : ℕ) : Set ℂ :=
  ⋂ m ∈ Set.Ici N, (A.collar m)ᶜ

private lemma measurableSet_collarFree {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (N : ℕ) :
    MeasurableSet (collarFree A N) :=
  MeasurableSet.biInter (Set.to_countable _) fun m _ => (A.collar_closed m).measurableSet.compl

private lemma tendsto_setIntegral_collarFree {Ω : Set ℂ} (A : BallZarnescuApprox Ω) {f : ℂ → ℝ}
    (hf : Integrable f (volume.restrict Ω)) :
    Tendsto (fun N => ∫ w in collarFree A N, f w ∂(volume.restrict Ω)) atTop
      (𝓝 (∫ w in Ω, f w)) := by
  have hmono : Monotone (collarFree A) := fun N N' hNN' w hw => by
    simp only [collarFree, Set.mem_iInter] at hw ⊢
    exact fun m hm => hw m (le_trans hNN' hm)
  have h := tendsto_setIntegral_of_monotone (μ := volume.restrict Ω)
    (measurableSet_collarFree A) hmono hf.integrableOn
  have hU : Ω ⊆ ⋃ N, collarFree A N := fun w hw =>
    let ⟨N, hN⟩ := eventually_atTop.mp (A.collar_shrink w hw)
    Set.mem_iUnion.mpr ⟨N, by simpa [collarFree] using hN⟩
  rwa [Measure.restrict_restrict (MeasurableSet.iUnion (measurableSet_collarFree A)),
    Set.inter_eq_self_of_subset_right hU] at h

/-- Eigenvalue and volume convergence along a Ball–Zarnescu smooth approximation. -/
theorem tendsto_ballZarnescu_eigen_and_volume {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (A : BallZarnescuApprox Ω) (N j : ℕ) :
    Tendsto (fun n => neumannEigenvalue (A.map (n + N) '' Ω) j) atTop
      (𝓝 (neumannEigenvalue Ω j)) ∧
    Tendsto (fun n => volume (A.map (n + N) '' Ω)) atTop (𝓝 (volume Ω)) := by
  have hΩ : IsOpen Ω := hL.1.1
  have hvolfin : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  have hmeas : ∀ n, AEStronglyMeasurable (bzDensity A n) (volume.restrict Ω) :=
    bzDensity_aestronglyMeasurable A
  have hbound : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), |bzDensity A n w| ≤ (A.lip : ℝ) ^ 2 :=
    bzDensity_bound hΩ A
  have hdt : ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => bzDensity A n w) atTop (𝓝 1) :=
    bzDensity_tendsto hΩ A tendsto_id
  have hvoldom : ∀ n, volume (A.map n '' Ω) = ENNReal.ofReal (∫ w in Ω, bzDensity A n w) :=
    fun n => by
      unfold bzDensity
      rw [volume_image_eq_lintegral hΩ ((A.lipschitz n).mono subset_closure)
        (A.map n).injective.injOn, ofReal_integral_eq_lintegral_ofReal]
      · exact Measure.integrableOn_of_bounded hvolfin
          (((continuous_abs.comp ContinuousLinearMap.continuous_det).measurable.comp
            (measurable_fderiv ℝ _)).aestronglyMeasurable)
          ((hbound n).mono fun _ hw => by rwa [Real.norm_eq_abs])
      · exact Eventually.of_forall fun _ => abs_nonneg _
  have hvol0 := tendsto_volume_of_density hvolfin (fun n => A.map n '' Ω)
    (bzDensity A) ((A.lip : ℝ) ^ 2) hmeas hbound hdt hvoldom
  set K : NNReal := max A.lip 1
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast le_max_right A.lip 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hf : ∀ n, LipschitzOnWith K (A.map n) Ω := fun n =>
    lipschitzOnWith_weaken ((A.lipschitz n).mono subset_closure) (le_max_left _ _)
  have hg : ∀ n, LipschitzOnWith K (A.map n).symm (A.map n '' Ω) := fun n =>
    lipschitzOnWith_weaken ((A.lipschitz_symm n).mono subset_closure) (le_max_left _ _)
  have hnorm : ∀ n, ∀ w ∈ Ω, ‖fderiv ℝ (A.map n) w‖ ≤ K := fun n _ hw =>
    norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) (hf n)
  let coef : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun n w => bzCoef (fderiv ℝ (A.map n) w)
  let Bcoef : ℝ := 2 * (K : ℝ) ^ 2 * (K : ℝ) ^ 2
  let ellip : ℝ := Bcoef⁻¹
  have hellip_pos : 0 < ellip := by positivity
  have hcoef_meas : ∀ n i k, AEStronglyMeasurable (fun w => coef n w i k) (volume.restrict Ω) :=
    fun n i k => ((measurable_bzCoef i k).comp (measurable_fderiv ℝ _)).aestronglyMeasurable
  have hcoef_bound : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |coef n w i k| ≤ Bcoef := fun n => by
    filter_upwards [ae_inv_sq_le_abs_det hΩ (hf n) (hg n), ae_restrict_mem hΩ.measurableSet]
      with w hw hwΩ i k
    have : 0 < ((K : ℝ) ^ 2)⁻¹ := by positivity
    calc |coef n w i k| ≤ 2 * ‖fderiv ℝ (A.map n) w‖ ^ 2 / |(fderiv ℝ (A.map n) w).det| :=
          abs_bzCoef_le _ i k
      _ ≤ 2 * (K : ℝ) ^ 2 / ((K : ℝ) ^ 2)⁻¹ := by gcongr; exact hnorm n w hwΩ
      _ = Bcoef := by dsimp [Bcoef]; field_simp
  have hcoef_ellip : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), ∀ ξ : Fin 2 → ℂ,
      ellip * ∑ i, ‖ξ i‖ ^ 2 ≤ (coefSesq (coef n w) ξ ξ).re := fun n => by
    filter_upwards [ae_inv_sq_le_abs_det hΩ (hf n) (hg n), ae_restrict_mem hΩ.measurableSet]
      with w hw hwΩ ξ
    set T := fderiv ℝ (A.map n) w
    have hpos : 0 < ((K : ℝ) ^ 2)⁻¹ := by positivity
    have e := bzCoef_ellip T (abs_pos.mp (hpos.trans_le hw)) ξ
    have hTK : ‖T‖ ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm n w hwΩ) 2
    have hsum : 0 ≤ ∑ i, ‖ξ i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    set R := (∑ i, ∑ k, ((bzCoef T) i k : ℂ) * inner ℂ (ξ i) (ξ k)).re with hR_def
    have hR : 0 ≤ R := by rw [hR_def, sesq_bzCoef, Complex.ofReal_re]; positivity
    have h1 : ((K : ℝ) ^ 2)⁻¹ * ∑ i, ‖ξ i‖ ^ 2 ≤ 2 * (K : ℝ) ^ 2 * R :=
      (mul_le_mul_of_nonneg_right hw hsum).trans (e.trans (by gcongr))
    change ellip * ∑ i, ‖ξ i‖ ^ 2 ≤ R
    dsimp [ellip, Bcoef]
    rw [inv_mul_le_iff₀ (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity)] at h1
    nlinarith
  have hcoef_one : ∀ n, ∀ w ∈ Ω, w ∉ A.collar n → coef n w = 1 := fun n w _ hwc => by
    have hev : (A.map n : ℂ → ℂ) =ᶠ[𝓝 w] id :=
      Filter.eventually_of_mem ((A.collar_closed n).isOpen_compl.mem_nhds hwc) (A.eq_self n)
    show bzCoef (fderiv ℝ (A.map n) w) = 1
    rw [hev.fderiv_eq, fderiv_id]; exact bzCoef_id
  have hdens_ge : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), ellip ≤ bzDensity A n w := fun n =>
    (ae_inv_sq_le_abs_det hΩ (hf n) (hg n)).mono fun _ hw => by
      have hK2 : 1 ≤ (K : ℝ) ^ 2 := by nlinarith
      exact (inv_anti₀ (by positivity : (0 : ℝ) < (K : ℝ) ^ 2) (by dsimp [Bcoef]; nlinarith)).trans hw
  let pull : ∀ n, L2 (A.map n '' Ω) ≃ₗ[ℂ] L2 Ω := fun n => bilipPull hΩ hK (hf n) (hg n)
  have hpull_inner : ∀ n (v w : L2 (A.map n '' Ω)), inner ℂ v w =
      ∫ x in Ω, ((bzDensity A n x : ℝ) : ℂ) * inner ℂ ((pull n v : ℂ → ℂ) x) ((pull n w : ℂ → ℂ) x) :=
    fun n v w => inner_eq_integral_bilipPull hΩ hK (hf n) (hg n) v w
  have hchain := fun n v => bzChainRule_of_bilip hΩ hK (hf n) (hg n) v
  classical
  let formQ : ℕ → L2 Ω → ℝ := fun n u => if h : u ∈ H1 Ω then gradForm Ω (coef n) h.choose else 0
  have hformQ_eq : ∀ n {u : L2 Ω} {g : Fin 2 → L2 Ω}, IsWeakGradient Ω u g →
      formQ n u = gradForm Ω (coef n) g := fun n {u g} hg' => by
    have h : u ∈ H1 Ω := ⟨g, hg'⟩
    simp only [formQ, dif_pos h, h.choose_spec.unique hΩ hg']
  have hwm_pull : ∀ n (v : L2 (A.map n '' Ω)),
      weightedMass Ω (bzDensity A n) (pull n v) = ‖v‖ ^ 2 := fun n v => by
    have h := congrArg RCLike.re (hpull_inner n v v)
    have hi : Integrable (fun x => ((bzDensity A n x : ℝ) : ℂ) *
        inner ℂ ((pull n v : ℂ → ℂ) x) ((pull n v : ℂ → ℂ) x)) (volume.restrict Ω) :=
      integrable_weight_inner (hmeas n) (hbound n) _ _
    rw [inner_self_eq_norm_sq] at h
    erw [← integral_re hi] at h
    rw [h, weightedMass]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    show bzDensity A n w * _ = RCLike.re (((bzDensity A n w : ℝ) : ℂ) * inner ℂ _ _)
    rw [RCLike.re_to_complex, Complex.re_ofReal_mul, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
  have hminmax : ∀ n (S : Submodule ℂ (L2 Ω)), Module.finrank ℂ S = j + 1 →
      (S : Set (L2 Ω)) ⊆ H1 Ω → neumannEigenvalue (A.map n '' Ω) j ≤
        ⨆ (u : L2 Ω) (_ : u ∈ S) (_ : ‖u‖ = 1),
          ENNReal.ofReal (formQ n u / weightedMass Ω (bzDensity A n) u) := fun n S hS hSH => by
    set e : L2 Ω ≃ₗ[ℂ] L2 (A.map n '' Ω) := (pull n).symm
    unfold neumannEigenvalue
    refine (iInf₂_le (S.map (e : L2 Ω →ₗ[ℂ] L2 (A.map n '' Ω)))
      ((LinearEquiv.finrank_map_eq _ _).trans hS)).trans
      (iSup₂_le fun v hv => iSup_le fun hv0 => ?_)
    obtain ⟨u, huS, rfl⟩ := Submodule.mem_map.mp hv
    have hpu : pull n (e u) = u := LinearEquiv.apply_symm_apply _ _
    obtain ⟨g, hg'⟩ := hSH huS
    have hnu : 0 < ‖u‖ := norm_pos_iff.mpr fun h => hv0 (h ▸ map_zero _)
    set c : ℂ := ((‖u‖⁻¹ : ℝ) : ℂ)
    have hc : ‖c‖ = ‖u‖⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnu)]
    have hcu : ‖c • u‖ = 1 := by rw [norm_smul, hc, inv_mul_cancel₀ hnu.ne']
    refine le_trans ?_ (le_iSup₂_of_le (c • u) (S.smul_mem c huS) (le_iSup_of_le hcu le_rfl))
    have hen : neumannEnergy (A.map n '' Ω) (e u) = ENNReal.ofReal (gradForm Ω (coef n) g) :=
      (hchain n (e u)).2 g (by rwa [show bilipPull hΩ hK (hf n) (hg n) (e u) = u from hpu])
    have hwm : weightedMass Ω (bzDensity A n) u = ‖e u‖ ^ 2 := by rw [← hwm_pull n (e u), hpu]
    have hwsmul : weightedMass Ω (bzDensity A n) (c • u) =
        ‖c‖ ^ 2 * weightedMass Ω (bzDensity A n) u := by
      unfold weightedMass; rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c u] with w hw
      rw [hw, Pi.smul_apply, smul_eq_mul, norm_mul]; ring
    have hev : 0 < ‖e u‖ := norm_pos_iff.mpr hv0
    have hq : formQ n (c • u) / weightedMass Ω (bzDensity A n) (c • u) =
        gradForm Ω (coef n) g / ‖e u‖ ^ 2 := by
      rw [hformQ_eq n (hg'.smul c), gradForm_smul (hcoef_meas n) (hcoef_bound n),
        hwsmul, hwm, mul_div_mul_left _ _ (by rw [hc]; positivity)]
    rw [hq, ENNReal.ofReal_div_of_pos (by positivity), ← hen, rayleigh,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]
    exact le_rfl
  have hformQ_t : ∀ (S : Submodule ℂ (L2 Ω)), Module.finrank ℂ S = j + 1 →
      (S : Set (L2 Ω)) ⊆ H1 Ω → TendstoUniformlyOn formQ (fun u => (neumannEnergy Ω u).toReal)
        atTop ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1) := fun S hSj hSH => by
    haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_eq_succ hSj
    have hev : ∀ᵐ w ∂(volume.restrict Ω), ∀ᶠ n in atTop, coef n w = 1 :=
      ae_restrict_of_forall_mem hΩ.measurableSet fun w hw =>
        (A.collar_shrink w hw).mono fun n hn => hcoef_one n w hw hn
    have h1m : ∀ i k, AEStronglyMeasurable
        (fun w : ℂ => (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) w i k)
        (volume.restrict Ω) := fun _ _ => aestronglyMeasurable_const
    have h1b : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k,
        |(fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) w i k| ≤ 1 :=
      Eventually.of_forall fun _ i k => by simp only [Matrix.one_apply]; split_ifs <;> simp
    set G := gradOf hΩ S hSH
    set Bn : ℕ → S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ := fun n =>
      ((gradSesq (hcoef_meas n) (hcoef_bound n)).comp G).compl₂ G
    set B : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ := ((gradSesq h1m h1b).comp G).compl₂ G
    set b := Module.finBasis ℂ S
    have hK' : Bornology.IsBounded {u : S | ‖u‖ = 1} :=
      (Metric.isBounded_closedBall (x := (0 : S)) (r := 1)).subset fun u (hu : ‖u‖ = 1) => by simp [hu]
    have hU' := Complex.uniformContinuous_re.comp_tendstoUniformlyOn
      (tendstoUniformlyOn_sesq_of_basis b Bn B
        (fun r s => tendsto_integral_coefSesq coef hcoef_meas hcoef_bound hev
          (G (b r)) (G (b s))) hK')
    intro t ht
    filter_upwards [hU' t ht] with n hn u ⟨huS, hu1⟩
    have hgu : IsWeakGradient Ω u (G ⟨u, huS⟩) := (hSH huS).choose_spec
    have eq2 : (neumannEnergy Ω u).toReal = (B ⟨u, huS⟩ ⟨u, huS⟩).re := by
      change _ = gradForm Ω (fun _ => 1) (G ⟨u, huS⟩)
      rw [neumannEnergy_eq_of_isWeakGradient hΩ hgu, ENNReal.toReal_sum fun _ _ => by simp]
      simp only [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
      exact (gradForm_one _).symm
    rw [hformQ_eq n hgu, eq2]
    exact hn ⟨u, huS⟩ (by simpa using hu1)
  have hlimits : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (lam : ENNReal), lam < ⊤ →
      Tendsto (fun n => neumannEigenvalue (A.map (φ n) '' Ω) j) atTop (𝓝 lam) →
        ∃ u : Fin (j + 1) → L2 Ω, Orthonormal ℂ u ∧ ∀ a : Fin (j + 1) → ℂ,
          neumannEnergy Ω (∑ r, a r • u r) ≤ lam * ENNReal.ofReal (∑ r, ‖a r‖ ^ 2) := by
    intro φ hφ lam hlam hlim
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hlam))
    set ψ : ℕ → ℕ := fun n => φ (n + M₀)
    have hψ : Tendsto ψ atTop atTop := hφ.tendsto_atTop.comp (tendsto_add_atTop_nat M₀)
    have halm : ∀ n, ∃ (u : Fin (j + 1) → L2 Ω) (G : Fin (j + 1) → Fin 2 → L2 Ω),
        (∀ r, IsWeakGradient Ω (u r) (G r)) ∧
        (∀ r s, ∫ w in Ω, (bzDensity A (ψ n) w : ℂ) * inner ℂ ((u r : ℂ → ℂ) w) ((u s : ℂ → ℂ) w) =
          if r = s then 1 else 0) ∧
        ∀ a : Fin (j + 1) → ℂ, gradForm Ω (coef (ψ n)) (∑ r, a r • G r) ≤
          ((neumannEigenvalue (A.map (ψ n) '' Ω) j).toReal + 1 / ((n : ℝ) + 1)) * ∑ r, ‖a r‖ ^ 2 := by
      intro n
      set D := A.map (ψ n) '' Ω
      have hμ := (hM₀ (n + M₀) (Nat.le_add_left M₀ n)).ne
      set ε : ℝ := 1 / ((n : ℝ) + 1)
      have hε : 0 < ε := by positivity
      obtain ⟨S, hS⟩ := iInf_lt_iff.mp (ENNReal.lt_add_right hμ (ENNReal.ofReal_pos.mpr hε).ne')
      obtain ⟨hSj, hsup⟩ := iInf_lt_iff.mp hS
      haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_eq_succ hSj
      set ob := (stdOrthonormalBasis ℂ S).reindex (finCongr hSj)
      have hon : Orthonormal ℂ (fun r => (ob r : L2 D)) :=
        orthonormal_iff_ite.mpr fun r s => orthonormal_iff_ite.mp ob.orthonormal r s
      have hE : ∀ a : Fin (j + 1) → ℂ, neumannEnergy D (∑ r, a r • (ob r : L2 D)) ≤
          ENNReal.ofReal (((neumannEigenvalue D j).toReal + ε) * ∑ r, ‖a r‖ ^ 2) := fun a => by
        set v := ∑ r, a r • (ob r : L2 D)
        have hvS : v ∈ S := S.sum_mem fun r _ => S.smul_mem _ (ob r).2
        have hn : ‖v‖ ^ 2 = ∑ r, ‖a r‖ ^ 2 := by
          rw [@norm_sq_eq_re_inner ℂ, hon.inner_sum]
          simp only [Complex.conj_mul', map_sum]
          exact Finset.sum_congr rfl fun _ _ => by norm_cast
        by_cases hv : v = 0
        · rw [hv]; exact (iInf₂_le 0 isWeakGradient_zero).trans (by simp)
        · have hr : rayleigh D v ≤ neumannEigenvalue D j + ENNReal.ofReal ε :=
            (le_iSup₂_of_le v hvS (le_iSup (fun _ : v ≠ 0 => rayleigh D v) hv)).trans hsup.le
          unfold rayleigh at hr
          rw [ENNReal.div_le_iff (by simpa using hv) (by simp),
            show (‖v‖₊ : ENNReal) ^ 2 = ENNReal.ofReal (∑ r, ‖a r‖ ^ 2) by
              rw [← hn, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]] at hr
          exact hr.trans_eq (by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le,
              ENNReal.ofReal_toReal hμ])
      have hH : ∀ r, pull (ψ n) (ob r : L2 D) ∈ H1 Ω := fun r => by
        refine (hchain (ψ n) _).1.mp (mem_H1_of_neumannEnergy_ne_top ?_)
        have h1 := hE (Pi.single r 1)
        simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true] at h1
        exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
      choose G hG using hH
      refine ⟨fun r => pull (ψ n) (ob r : L2 D), G, hG,
        fun r s => (hpull_inner (ψ n) _ _).symm.trans (orthonormal_iff_ite.mp hon r s), fun a => ?_⟩
      have hgrad : IsWeakGradient Ω (pull (ψ n) (∑ r, a r • (ob r : L2 D))) (∑ r, a r • G r) := by
        rw [map_sum]; simp_rw [map_smul]
        exact IsWeakGradient.sum _ _ _ fun r _ => (hG r).smul (a r)
      have h := hE a
      rw [(hchain (ψ n) _).2 _ hgrad] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    choose u G hG horth hq using halm
    set b : ℕ → ℝ := fun n => (neumannEigenvalue (A.map (ψ n) '' Ω) j).toReal + 1 / ((n : ℝ) + 1)
    have hbB : Tendsto b atTop (𝓝 lam.toReal) := by
      have h1 := ((ENNReal.tendsto_toReal hlam.ne).comp
        (hlim.comp (tendsto_add_atTop_nat M₀))).add tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [add_zero] at h1
    have hub : ∀ n r, ‖u n r‖ ≤ Real.sqrt (1 / ellip) := fun n r => by
      have hm : weightedMass Ω (bzDensity A (ψ n)) (u n r) = 1 := by
        have h1 := horth n r r
        rw [show ∫ w in Ω, (bzDensity A (ψ n) w : ℂ) * inner ℂ ((u n r : ℂ → ℂ) w) ((u n r : ℂ → ℂ) w) =
          ((weightedMass Ω (bzDensity A (ψ n)) (u n r) : ℝ) : ℂ) by
            rw [weightedMass, ← integral_complex_ofReal]
            exact integral_congr_ae (Eventually.of_forall fun _ => by
              simp only [inner_self_eq_norm_sq_to_K]; push_cast; rfl), if_pos rfl] at h1
        exact_mod_cast h1
      have hint : Integrable (fun w => ‖(u n r : ℂ → ℂ) w‖ ^ 2) (volume.restrict Ω) :=
        (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
      have hge : ellip * ‖u n r‖ ^ 2 ≤ weightedMass Ω (bzDensity A (ψ n)) (u n r) := by
        rw [← integral_norm_sq_eq_of, ← integral_const_mul, weightedMass]
        exact integral_mono_ae (hint.const_mul _)
          (hint.bdd_mul (hmeas _) ((hbound _).mono fun _ hw => by simpa [Real.norm_eq_abs] using hw))
          ((hdens_ge _).mono fun _ hw => mul_le_mul_of_nonneg_right hw (sq_nonneg _))
      rw [hm] at hge
      exact Real.le_sqrt_of_sq_le ((le_div_iff₀ hellip_pos).mpr (by linarith))
    obtain ⟨Bm, hBm⟩ := hbB.bddAbove_range
    have hGb : ∀ n r i, ‖G n r i‖ ≤ Real.sqrt (Bm / ellip) := fun n r i => by
      have h1 := hq n (Pi.single r 1)
      rw [show ∑ s, (Pi.single r (1 : ℂ) : Fin (j + 1) → ℂ) s • G n s = G n r by
          rw [Finset.sum_eq_single r (fun _ _ hs => by simp [hs]) (by simp)]; simp,
        show ∑ s, ‖(Pi.single r (1 : ℂ) : Fin (j + 1) → ℂ) s‖ ^ 2 = 1 by
          rw [Finset.sum_eq_single r (fun _ _ hs => by simp [hs]) (by simp)]; simp,
        mul_one] at h1
      have hint : ∀ k, Integrable (fun w => ‖(G n r k : ℂ → ℂ) w‖ ^ 2) (volume.restrict Ω) :=
        fun k => (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
      have h2 : ellip * ∑ k, ‖G n r k‖ ^ 2 ≤ gradForm Ω (coef (ψ n)) (G n r) := by
        rw [show ellip * ∑ k, ‖G n r k‖ ^ 2 = ∫ w in Ω, ellip * ∑ k, ‖(G n r k : ℂ → ℂ) w‖ ^ 2 by
          rw [integral_const_mul, integral_finset_sum _ fun k _ => hint k]
          simp_rw [integral_norm_sq_eq_of], gradForm]
        exact (integral_mono_ae ((integrable_finset_sum _ fun k _ => hint k).const_mul _)
          (integrable_coefSesq (hcoef_meas _) (hcoef_bound _) _ _).re
          ((hcoef_ellip _).mono fun _ hw => hw _)).trans_eq
          (integral_re (integrable_coefSesq (hcoef_meas _) (hcoef_bound _) _ _))
      have h3 : ‖G n r i‖ ^ 2 ≤ ∑ k, ‖G n r k‖ ^ 2 :=
        Finset.single_le_sum (f := fun k => ‖G n r k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      have hbn : b n ≤ Bm := hBm ⟨n, rfl⟩
      exact Real.le_sqrt_of_sq_le ((le_div_iff₀ hellip_pos).mpr (by dsimp [b] at hbn; nlinarith))
    set R := max (Real.sqrt (1 / ellip)) (Real.sqrt (Bm / ellip))
    let Pr : Fin (j + 1) ⊕ (Fin (j + 1) × Fin 2) → (ℕ → ℕ) → Prop := fun k θ =>
      Sum.elim (fun r => ∃ V, Tendsto (fun n => u (θ n) r) atTop (𝓝 V))
        (fun ri => ∃ V, ∀ z, Tendsto (fun n => inner ℂ z (G (θ n) ri.1 ri.2)) atTop (𝓝 (inner ℂ z V))) k
    obtain ⟨θ, hθ, hPr⟩ := exists_common_subseq Pr
      (fun k θ θ' hk hθ' => by
        cases k with
        | inl _ => obtain ⟨V, hV⟩ := hk; exact ⟨V, hV.comp hθ'.tendsto_atTop⟩
        | inr _ => obtain ⟨V, hV⟩ := hk; exact ⟨V, fun z => (hV z).comp hθ'.tendsto_atTop⟩)
      (fun k θ _ => by
        cases k with
        | inl r =>
          exact rellich_compact hb hL (fun n => u (θ n) r) (fun n => G (θ n) r) (fun n => hG (θ n) r)
            R (fun _ => (hub _ r).trans (le_max_left _ _))
            (fun _ i => (hGb _ r i).trans (le_max_right _ _))
        | inr ri =>
          exact exists_weak_subseq (fun n => G (θ n) ri.1 ri.2) R
            (fun _ => (hGb _ _ _).trans (le_max_right _ _)))
    choose U hU using fun r => hPr (Sum.inl r)
    choose Γ hΓ using fun ri : Fin (j + 1) × Fin 2 => hPr (Sum.inr ri)
    have hUG : ∀ r, IsWeakGradient Ω (U r) (fun i => Γ (r, i)) := fun r =>
      isWeakGradient_of_weak_tendsto (fun n => hG (θ n) r) (hU r) (fun i z => hΓ (r, i) z)
    have hψθ : Tendsto (fun n => ψ (θ n)) atTop atTop := hψ.comp hθ.tendsto_atTop
    refine ⟨U, orthonormal_iff_ite.mpr fun r s => tendsto_nhds_unique
        (tendsto_weighted_inner (fun n => bzDensity A (ψ (θ n))) (by positivity)
          (fun _ => hmeas _) (fun _ => hbound _) (bzDensity_tendsto hΩ A hψθ) (hU r) (hU s))
        (by simp_rw [horth]; exact tendsto_const_nhds), fun a => ?_⟩
    set Γa : Fin 2 → L2 Ω := ∑ r, a r • (fun i => Γ (r, i))
    have hV : IsWeakGradient Ω (∑ r, a r • U r) Γa :=
      IsWeakGradient.sum _ _ _ fun r _ => (hUG r).smul (a r)
    have hw : ∀ i z, Tendsto (fun n => inner ℂ z ((∑ r, a r • G (θ n) r) i)) atTop
        (𝓝 (inner ℂ z (Γa i))) := fun i z => by
      simp only [Γa, Finset.sum_apply, Pi.smul_apply, inner_sum, inner_smul_right]
      exact tendsto_finset_sum _ fun r _ => (hΓ (r, i) z).const_mul (a r)
    have hMp : ∀ m, ∀ᵐ w ∂(volume.restrict Ω), ∀ ξ : Fin 2 → ℂ,
        0 ≤ (coefSesq (coef m w) ξ ξ).re := fun m =>
      (hcoef_ellip m).mono fun _ hw ξ =>
        (mul_nonneg hellip_pos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans (hw ξ)
    have hlsc : ∑ i, ‖Γa i‖ ^ 2 ≤ lam.toReal * ∑ r, ‖a r‖ ^ 2 := by
      have hF : ∀ M, ∑ i, ∫ w in collarFree A M, ‖(Γa i : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) ≤
          lam.toReal * ∑ r, ‖a r‖ ^ 2 := fun M => le_of_forall_pos_le_add fun ε hε => by
        have h1 := fun i => weak_lsc_restrict (hw i) (collarFree A M) (ε / 2) (by positivity)
        have h3 : ∀ᶠ n in atTop,
            ∑ i, ∫ w in collarFree A M, ‖(Γa i : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) - ε ≤
              b (θ n) * ∑ r, ‖a r‖ ^ 2 := by
          filter_upwards [h1 0, h1 1, hψθ.eventually_ge_atTop M] with n hn0 hn1 hn2
          have hMF : ∀ w ∈ Ω, w ∈ collarFree A M → coef (ψ (θ n)) w = 1 := fun w hwΩ hwF =>
            hcoef_one _ w hwΩ (by simp only [collarFree, Set.mem_iInter] at hwF; exact hwF _ hn2)
          have h := integral_restrict_le_gradForm (hcoef_meas _) (hcoef_bound _)
            (hMp _) hΩ.measurableSet (measurableSet_collarFree A M) hMF (∑ r, a r • G (θ n) r)
          simp only [Fin.sum_univ_two] at h ⊢
          linarith [hq (θ n) a]
        linarith [ge_of_tendsto ((hbB.comp hθ.tendsto_atTop).mul_const _) h3]
      have hint : ∀ i, Integrable (fun w => ‖(Γa i : ℂ → ℂ) w‖ ^ 2) (volume.restrict Ω) := fun i =>
        (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
      exact le_of_tendsto' (tendsto_finset_sum _ fun i _ => by
        rw [← integral_norm_sq_eq_of]; exact tendsto_setIntegral_collarFree A (hint i)) hF
    refine (iInf₂_le Γa hV).trans ((le_of_eq ?_).trans ((ENNReal.ofReal_le_ofReal hlsc).trans_eq ?_))
    · rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hlam.ne]
  have hμ0 := tendsto_neumannEigenvalue j (fun n => neumannEigenvalue (A.map n '' Ω) j)
    formQ (fun n => weightedMass Ω (bzDensity A n))
    hminmax hformQ_t
    (fun S hSj _ => tendstoUniformlyOn_weightedMass _ _ hmeas hbound hdt S
      (Module.finite_of_finrank_eq_succ hSj))
    hlimits
  exact ⟨hμ0.comp (tendsto_add_atTop_nat N), hvol0.comp (tendsto_add_atTop_nat N)⟩

end PolyaNeumann

end
