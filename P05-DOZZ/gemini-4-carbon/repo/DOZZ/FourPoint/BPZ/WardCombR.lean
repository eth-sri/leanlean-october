/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardDefs

/-! # The right side of the Ward identity for the four-point combination -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {z : ℂ} {m : Measure ℂ}


variable {γ χ α₁ α₂ α₃ : ℝ}

private noncomputable def wcrH (z : ℂ) (k : ℂ → ℝ) (ℓ : ℂ →L[ℝ] ℝ) (v x y : ℂ) : ℝ :=
  (ℓ (bpzG z x) - ℓ (bpzG z y)) * (k x * k y) * bpzKern v (x - y) / 2

private noncomputable def wcrF (k : ℂ → ℝ) (γ s : ℝ) (z : ℂ) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ)
    (m : Measure ℂ) : ℝ :=
  (s + 1) * ((∫ x, k x ∂m) ^ (-(s + 1) - 1) * (γ ^ 2 * ∫ x, ∫ y, wcrH z k ℓ v x y ∂m ∂m))

private lemma wcrH_measurable (z : ℂ) {k : ℂ → ℝ} (hk : Measurable k) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    Measurable (Function.uncurry (wcrH z k ℓ v)) := by
  have hg := bpzWardG_measurable z ℓ
  exact ((((hg.comp measurable_fst).sub (hg.comp measurable_snd)).mul
    ((hk.comp measurable_fst).mul (hk.comp measurable_snd))).mul
      ((measurable_bpzKern v).comp (measurable_fst.sub measurable_snd))).div_const _

private lemma wcr_integrable_k {k : ℂ → ℝ} (hkm : Measurable k)
    (hk0 : ∀ x, 0 ≤ k x) (hgi : Integrable (fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) m) :
    Integrable k m :=
  hgi.mono' hkm.aestronglyMeasurable (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hk0 x)]
    exact le_mul_of_one_le_left (hk0 x) (by linarith [bpz_rpow_neg_two_nonneg (norm_nonneg (x - z))]))

private lemma wcr_integrable_double [IsFiniteMeasure m] {k : ℂ → ℝ}
    (hkm : Measurable k) (hk0 : ∀ x, 0 ≤ k x) (hreg : ∀ᵐ x ∂m, x ∈ bpzRegular z)
    (hgi : Integrable (fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) m)
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x ∈ bpzRegular z, ∀ y ∈ bpzRegular z,
      |(ℓ (bpzG z x) - ℓ (bpzG z y)) * bpzKern v (x - y)| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ))) :
    Integrable (fun p : ℂ × ℂ => wcrH z k ℓ v p.1 p.2) (m.prod m) ∧
      |∫ x, ∫ y, wcrH z k ℓ v x y ∂m ∂m| ≤
        A * ((∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m) * ∫ x, k x ∂m) := by
  have hki := wcr_integrable_k hkm hk0 hgi
  have hbi : Integrable (fun p : ℂ × ℂ => A / 2 * ((1 + ‖p.1 - z‖ ^ (-2 : ℝ)) * k p.1 * k p.2 +
      k p.1 * ((1 + ‖p.2 - z‖ ^ (-2 : ℝ)) * k p.2))) (m.prod m) :=
    ((hgi.mul_prod hki).add (hki.mul_prod hgi)).const_mul _
  have hbd : ∀ᵐ p ∂(m.prod m), ‖wcrH z k ℓ v p.1 p.2‖ ≤
      A / 2 * ((1 + ‖p.1 - z‖ ^ (-2 : ℝ)) * k p.1 * k p.2 +
        k p.1 * ((1 + ‖p.2 - z‖ ^ (-2 : ℝ)) * k p.2)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := m) (ν := m)).ae hreg,
      (Measure.quasiMeasurePreserving_snd (μ := m) (ν := m)).ae hreg] with p hp1 hp2
    have hkk : 0 ≤ k p.1 * k p.2 := mul_nonneg (hk0 p.1) (hk0 p.2)
    rw [Real.norm_eq_abs, show wcrH z k ℓ v p.1 p.2 =
      (ℓ (bpzG z p.1) - ℓ (bpzG z p.2)) * bpzKern v (p.1 - p.2) * (k p.1 * k p.2) / 2 by
        unfold wcrH; ring, abs_div, abs_two, abs_mul, abs_of_nonneg hkk]
    have hle := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hA p.1 hp1 p.2 hp2) hkk) zero_le_two
    nlinarith [mul_nonneg hA0 hkk]
  have hint := hbi.mono' (wcrH_measurable z hkm ℓ v).aestronglyMeasurable hbd
  refine ⟨hint, ?_⟩
  rw [← integral_prod (fun p : ℂ × ℂ => wcrH z k ℓ v p.1 p.2) hint, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hbi hbd).trans_eq ?_
  rw [integral_const_mul, integral_add (hgi.mul_prod hki) (hki.mul_prod hgi),
    integral_prod_mul (f := fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) (g := k),
    integral_prod_mul (f := k) (g := fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x)]
  ring

private lemma wcr_integral_comb {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ f₃ f₄ : α → ℝ} (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ)
    (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ) :
    (((∫ a, f₁ a ∂μ : ℝ) : ℂ) + Complex.I * ((∫ a, f₂ a ∂μ : ℝ) : ℂ) -
        Complex.I * ((∫ a, f₃ a ∂μ : ℝ) : ℂ) + ((∫ a, f₄ a ∂μ : ℝ) : ℂ)) / 2 =
      ∫ a, (((f₁ a : ℝ) : ℂ) + Complex.I * ((f₂ a : ℝ) : ℂ) -
        Complex.I * ((f₃ a : ℝ) : ℂ) + ((f₄ a : ℝ) : ℂ)) / 2 ∂μ := by
  have i₁ : Integrable (fun a => ((f₁ a : ℝ) : ℂ)) μ := h₁.ofReal
  have i₂ : Integrable (fun a => Complex.I * ((f₂ a : ℝ) : ℂ)) μ := h₂.ofReal.const_mul _
  have i₃ : Integrable (fun a => Complex.I * ((f₃ a : ℝ) : ℂ)) μ := h₃.ofReal.const_mul _
  have i₄ : Integrable (fun a => ((f₄ a : ℝ) : ℂ)) μ := h₄.ofReal
  have i₁₂ : Integrable (fun a => ((f₁ a : ℝ) : ℂ) + Complex.I * ((f₂ a : ℝ) : ℂ)) μ := i₁.add i₂
  have i₁₂₃ : Integrable (fun a => ((f₁ a : ℝ) : ℂ) + Complex.I * ((f₂ a : ℝ) : ℂ) -
      Complex.I * ((f₃ a : ℝ) : ℂ)) μ := i₁₂.sub i₃
  rw [integral_div, integral_add i₁₂₃ i₄, integral_sub i₁₂ i₃, integral_add i₁ i₂,
    integral_const_mul, integral_const_mul]
  simp only [integral_complex_ofReal]

private lemma wcr_combo [IsFiniteMeasure m] (hno : ∀ x, m {x} = 0)
    (hreg : ∀ᵐ x ∂m, x ∈ bpzRegular z) {k : ℂ → ℝ} (hki : Integrable k m)
    (hdi : Integrable (fun x => (k x : ℂ) / (z - x)) m)
    (h₁ : Integrable (fun p : ℂ × ℂ => wcrH z k Complex.reCLM 1 p.1 p.2) (m.prod m))
    (h₂ : Integrable (fun p : ℂ × ℂ => wcrH z k Complex.imCLM 1 p.1 p.2) (m.prod m))
    (h₃ : Integrable (fun p : ℂ × ℂ => wcrH z k Complex.reCLM Complex.I p.1 p.2) (m.prod m))
    (h₄ : Integrable (fun p : ℂ × ℂ => wcrH z k Complex.imCLM Complex.I p.1 p.2) (m.prod m)) :
    (((∫ x, ∫ y, wcrH z k Complex.reCLM 1 x y ∂m ∂m : ℝ) : ℂ) +
        Complex.I * ((∫ x, ∫ y, wcrH z k Complex.imCLM 1 x y ∂m ∂m : ℝ) : ℂ) -
        Complex.I * ((∫ x, ∫ y, wcrH z k Complex.reCLM Complex.I x y ∂m ∂m : ℝ) : ℂ) +
        ((∫ x, ∫ y, wcrH z k Complex.imCLM Complex.I x y ∂m ∂m : ℝ) : ℂ)) / 2 =
      ((((∫ x, k x ∂m : ℝ) : ℂ)) ^ 2 - z * (z - 1) * (∫ x, (k x : ℂ) / (z - x) ∂m) ^ 2) / 4 := by
  have hae_ne : ∀ᵐ p ∂(m.prod m), p.1 ≠ p.2 := by
    have hm : MeasurableSet {p : ℂ × ℂ | p.1 ≠ p.2} :=
      (measurableSet_eq_fun measurable_fst measurable_snd).compl
    rw [Measure.ae_prod_iff_ae_ae hm]
    exact Eventually.of_forall fun x => by
      rw [ae_iff, show {y : ℂ | ¬ (x, y).1 ≠ (x, y).2} = {x} by ext y; simp [eq_comm]]
      exact hno x
  rw [← integral_prod _ h₁, ← integral_prod _ h₂, ← integral_prod _ h₃, ← integral_prod _ h₄,
    wcr_integral_comb h₁ h₂ h₃ h₄]
  have hae : ∀ᵐ p ∂(m.prod m), (((wcrH z k Complex.reCLM 1 p.1 p.2 : ℝ) : ℂ) +
        Complex.I * ((wcrH z k Complex.imCLM 1 p.1 p.2 : ℝ) : ℂ) -
        Complex.I * ((wcrH z k Complex.reCLM Complex.I p.1 p.2 : ℝ) : ℂ) +
        ((wcrH z k Complex.imCLM Complex.I p.1 p.2 : ℝ) : ℂ)) / 2 =
      ((k p.1 : ℂ) * (k p.2 : ℂ) - z * (z - 1) *
        (((k p.1 : ℂ) / (z - p.1)) * ((k p.2 : ℂ) / (z - p.2)))) / 4 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := m) (ν := m)).ae hreg,
      (Measure.quasiMeasurePreserving_snd (μ := m) (ν := m)).ae hreg, hae_ne] with p hp1 hp2 hne
    have h1 : ((((bpzG z p.1).re - (bpzG z p.2).re) * bpzKern 1 (p.1 - p.2) : ℝ) +
        Complex.I * ((((bpzG z p.1).im - (bpzG z p.2).im) * bpzKern 1 (p.1 - p.2) : ℝ) : ℂ) -
        Complex.I * ((((bpzG z p.1).re - (bpzG z p.2).re) * bpzKern Complex.I (p.1 - p.2) : ℝ) : ℂ) +
        ((((bpzG z p.1).im - (bpzG z p.2).im) * bpzKern Complex.I (p.1 - p.2) : ℝ) : ℂ)) / 2 =
      -(bpzG z p.1 - bpzG z p.2) / (2 * (p.1 - p.2)) := bpz_g_kern_combination hne
    have h2 : (bpzG z p.1 - bpzG z p.2) / (p.1 - p.2) =
      -1 + z * (z - 1) / ((z - p.1) * (z - p.2)) := bpz_g_diff_quot hne hp1.2.2 hp2.2.2
    have hfac (a₁ a₂ a₃ a₄ w : ℝ) :
        (((a₁ * w / 2 : ℝ) : ℂ) + Complex.I * ((a₂ * w / 2 : ℝ) : ℂ) -
          Complex.I * ((a₃ * w / 2 : ℝ) : ℂ) + ((a₄ * w / 2 : ℝ) : ℂ)) / 2 =
        ((w : ℂ) / 2) * (((a₁ : ℂ) + Complex.I * (a₂ : ℂ) - Complex.I * (a₃ : ℂ) + (a₄ : ℂ)) / 2) := by
      push_cast; ring
    have hHeq (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
        wcrH z k ℓ v p.1 p.2 = (ℓ (bpzG z p.1) - ℓ (bpzG z p.2)) * bpzKern v (p.1 - p.2) * (k p.1 * k p.2) / 2 := by
      unfold wcrH; ring
    rw [hHeq, hHeq, hHeq, hHeq, hfac]
    simp only [Complex.reCLM_apply, Complex.imCLM_apply]
    rw [h1, show -(bpzG z p.1 - bpzG z p.2) / (2 * (p.1 - p.2)) =
      -((bpzG z p.1 - bpzG z p.2) / (p.1 - p.2)) / 2 by field_simp, h2]
    push_cast
    field_simp [sub_ne_zero.2 hp1.2.2.symm, sub_ne_zero.2 hp2.2.2.symm]
    ring
  have j₁ : Integrable (fun p : ℂ × ℂ => (k p.1 : ℂ) * (k p.2 : ℂ)) (m.prod m) :=
    hki.ofReal.mul_prod hki.ofReal
  have j₂ : Integrable (fun p : ℂ × ℂ => z * (z - 1) *
      (((k p.1 : ℂ) / (z - p.1)) * ((k p.2 : ℂ) / (z - p.2)))) (m.prod m) :=
    (hdi.mul_prod hdi).const_mul _
  rw [integral_congr_ae hae, integral_div, integral_sub j₁ j₂, integral_const_mul,
    integral_prod_mul (f := fun x => (k x : ℂ)) (g := fun x => (k x : ℂ)),
    integral_prod_mul (f := fun x => (k x : ℂ) / (z - x)) (g := fun x => (k x : ℂ) / (z - x)),
    integral_complex_ofReal]
  ring

/-- **The combination of the four Ward right sides.** -/
theorem bpz_wardRHS_combination {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    ((bpzWardRHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM 1 : ℂ) +
        Complex.I * (bpzWardRHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM 1 : ℂ) -
        Complex.I * (bpzWardRHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM Complex.I : ℂ) +
        (bpzWardRHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM Complex.I : ℂ)) / 2 =
      ((s + 1 : ℝ) : ℂ) * ((γ ^ 2 / 4 : ℝ) : ℂ) *
        ((bpzMomJ P M γ χ α₁ α₂ α₃ s z : ℂ) - z * (z - 1) * bpzMomD2 P M γ χ α₁ α₂ α₃ s z) := by
  let k := bpzSoftWeight γ χ α₁ α₂ α₃ 0 z
  have hq1 : 1 ≤ s + 1 := by linarith
  have hgood := bpz_singular_integrable_ae (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hχ hα₁ hα₂ hα₃ hq1 hz0 hz1
  have hdom := bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hMm hχ hα₁ hα₂ hα₃ hq1 hz0 hz1
  have hkm : Measurable k := measurable_bpzSoftWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have hk0 : ∀ x, 0 ≤ k x := bpzSoftWeight_nonneg (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have hno := gmc_noAtoms_ae P X hX γ hγ hγ2 M hM hMm
  have hreg := bpz_ae_regular P X hX hγ hγ2 M hM z
  have hpos : ∀ᵐ ω ∂P, 0 < ∫ x, k x ∂M ω := hgood.mono fun ω ⟨_, hp, hf⟩ => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hk0) hkm.aestronglyMeasurable]
    exact ENNReal.toReal_pos hp.ne' hf.ne
  have hF_int (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) {A : ℝ} (hA0 : 0 ≤ A)
      (hA : ∀ x ∈ bpzRegular z, ∀ y ∈ bpzRegular z,
        |(ℓ (bpzG z x) - ℓ (bpzG z y)) * bpzKern v (x - y)| ≤
          A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ))) :
      Integrable (fun ω => wcrF k γ s z ℓ v (M ω)) P := by
    have hm : Measurable fun ω => wcrF k γ s z ℓ v (M ω) :=
      measurable_const.mul ((((measurable_integral_measure hkm).comp hMm).pow_const _).mul
        (measurable_const.mul (bpz_measurable_double_integral hMm hM.1 hMm hM.1 _ (wcrH_measurable z hkm ℓ v))))
    refine (hdom.const_mul ((s + 1) * γ ^ 2 * A)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [hreg, hgood, hpos] with ω hr hg hp
    have := hM.1 ω
    have hd := (wcr_integrable_double hkm hk0 hr hg.1 ℓ v hA0 hA).2
    have hrpow : (∫ x, k x ∂M ω) ^ (-(s + 1)) = (∫ x, k x ∂M ω) ^ (-(s + 1) - 1) * ∫ x, k x ∂M ω := by
      rw [← Real.rpow_add_one hp.ne']; ring_nf
    rw [Real.norm_eq_abs]; dsimp only [wcrF]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ s + 1),
      abs_of_nonneg (Real.rpow_nonneg hp.le _), abs_of_nonneg (sq_nonneg γ)]
    calc (s + 1) * ((∫ x, k x ∂M ω) ^ (-(s + 1) - 1) * (γ ^ 2 * |∫ x, ∫ y, wcrH z k ℓ v x y ∂M ω ∂M ω|))
      _ ≤ (s + 1) * ((∫ x, k x ∂M ω) ^ (-(s + 1) - 1) *
          (γ ^ 2 * (A * ((∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂M ω) * ∫ x, k x ∂M ω)))) := by gcongr
      _ = (s + 1) * γ ^ 2 * A * ((∫ x, k x ∂M ω) ^ (-(s + 1)) *
          ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂M ω) := by rw [hrpow]; ring
  obtain ⟨A₁, hA₁0, hA₁⟩ := bpz_g_kern_bound hz0 hz1 Complex.reCLM 1
  obtain ⟨A₂, hA₂0, hA₂⟩ := bpz_g_kern_bound hz0 hz1 Complex.imCLM 1
  obtain ⟨A₃, hA₃0, hA₃⟩ := bpz_g_kern_bound hz0 hz1 Complex.reCLM Complex.I
  obtain ⟨A₄, hA₄0, hA₄⟩ := bpz_g_kern_bound hz0 hz1 Complex.imCLM Complex.I
  have F₁ := hF_int Complex.reCLM 1 hA₁0 hA₁
  have F₂ := hF_int Complex.imCLM 1 hA₂0 hA₂
  have F₃ := hF_int Complex.reCLM Complex.I hA₃0 hA₃
  have F₄ := hF_int Complex.imCLM Complex.I hA₄0 hA₄
  have hae : ∀ᵐ ω ∂P, (((wcrF k γ s z Complex.reCLM 1 (M ω) : ℝ) : ℂ) +
        Complex.I * ((wcrF k γ s z Complex.imCLM 1 (M ω) : ℝ) : ℂ) -
        Complex.I * ((wcrF k γ s z Complex.reCLM Complex.I (M ω) : ℝ) : ℂ) +
        ((wcrF k γ s z Complex.imCLM Complex.I (M ω) : ℝ) : ℂ)) / 2 =
      ((s + 1 : ℝ) : ℂ) * ((γ ^ 2 / 4 : ℝ) : ℂ) *
        ((((∫ x, k x ∂M ω) ^ (-s) : ℝ) : ℂ) - z * (z - 1) *
          ((((∫ x, k x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) * (∫ x, (k x : ℂ) / (z - x) ∂M ω) ^ 2)) := by
    filter_upwards [hno, hreg, hgood, hpos] with ω hnoω hr hg hp
    have := hM.1 ω
    have hdi : Integrable (fun x => (k x : ℂ) / (z - x)) (M ω) :=
      hg.1.mono' ((Complex.measurable_ofReal.comp hkm).div (measurable_const.sub measurable_id)).aestronglyMeasurable
        (hr.mono fun x hx => by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hk0 x), norm_sub_rev z x,
            Real.rpow_neg (norm_nonneg _), Real.rpow_two, div_eq_inv_mul]
          refine mul_le_mul_of_nonneg_right ?_ (hk0 x)
          rw [← inv_pow]; linarith [sq_nonneg (‖x - z‖⁻¹ - 1 / 2)])
    have hc := wcr_combo hnoω hr (wcr_integrable_k hkm hk0 hg.1) hdi
      (wcr_integrable_double hkm hk0 hr hg.1 Complex.reCLM 1 hA₁0 hA₁).1
      (wcr_integrable_double hkm hk0 hr hg.1 Complex.imCLM 1 hA₂0 hA₂).1
      (wcr_integrable_double hkm hk0 hr hg.1 Complex.reCLM Complex.I hA₃0 hA₃).1
      (wcr_integrable_double hkm hk0 hr hg.1 Complex.imCLM Complex.I hA₄0 hA₄).1
    have hrpow : (∫ x, k x ∂M ω) ^ (-s) = (∫ x, k x ∂M ω) ^ (-s - 2) * (∫ x, k x ∂M ω) ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add hp]; ring_nf
    dsimp only [wcrF]
    rw [show -(s + 1) - 1 = -s - 2 by ring, hrpow]
    push_cast at hc ⊢
    linear_combination ((s + 1 : ℂ) * (((∫ x, k x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) * (γ : ℂ) ^ 2) * hc
  have hJr : Integrable (fun ω => (∫ x, k x ∂M ω) ^ (-s)) P :=
    hdom.mono' (((measurable_integral_measure hkm).comp hMm).pow_const _).aestronglyMeasurable (by
      filter_upwards [hgood, hpos] with ω hg hp
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hp.le _),
        show (∫ x, k x ∂M ω) ^ (-s) = (∫ x, k x ∂M ω) ^ (-(s + 1)) * ∫ x, k x ∂M ω by
          rw [← Real.rpow_add_one hp.ne']; ring_nf]
      refine mul_le_mul_of_nonneg_left (integral_mono (wcr_integrable_k hkm hk0 hg.1) hg.1 fun x => ?_)
        (Real.rpow_nonneg hp.le _)
      exact le_mul_of_one_le_left (hk0 x) (by linarith [bpz_rpow_neg_two_nonneg (norm_nonneg (x - z))]))
  have hJc : Integrable (fun ω => (((∫ x, k x ∂M ω) ^ (-s) : ℝ) : ℂ)) P := hJr.ofReal
  have hc_ne : ((s + 1 : ℝ) : ℂ) * ((γ ^ 2 / 4 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) (Complex.ofReal_ne_zero.2 (by positivity))
  have hCombInt : Integrable (fun ω => (((wcrF k γ s z Complex.reCLM 1 (M ω) : ℝ) : ℂ) +
      Complex.I * ((wcrF k γ s z Complex.imCLM 1 (M ω) : ℝ) : ℂ) -
      Complex.I * ((wcrF k γ s z Complex.reCLM Complex.I (M ω) : ℝ) : ℂ) +
      ((wcrF k γ s z Complex.imCLM Complex.I (M ω) : ℝ) : ℂ)) / 2) P :=
    (((F₁.ofReal.add (F₂.ofReal.const_mul _)).sub (F₃.ofReal.const_mul _)).add F₄.ofReal).div_const _
  have hD2 : Integrable (fun ω => z * (z - 1) *
      ((((∫ x, k x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) * (∫ x, (k x : ℂ) / (z - x) ∂M ω) ^ 2)) P :=
    (hJc.sub (hCombInt.div_const _)).congr (hae.mono fun ω hω => by
      dsimp only [Pi.sub_apply]; rw [hω, mul_div_cancel_left₀ _ hc_ne]; ring)
  change (((∫ ω, wcrF k γ s z Complex.reCLM 1 (M ω) ∂P : ℝ) : ℂ) +
      Complex.I * ((∫ ω, wcrF k γ s z Complex.imCLM 1 (M ω) ∂P : ℝ) : ℂ) -
      Complex.I * ((∫ ω, wcrF k γ s z Complex.reCLM Complex.I (M ω) ∂P : ℝ) : ℂ) +
      ((∫ ω, wcrF k γ s z Complex.imCLM Complex.I (M ω) ∂P : ℝ) : ℂ)) / 2 = _
  rw [wcr_integral_comb F₁ F₂ F₃ F₄, integral_congr_ae hae, integral_const_mul,
    integral_sub hJc hD2, integral_const_mul, integral_complex_ofReal]
  rfl

end DOZZ.Proofs
