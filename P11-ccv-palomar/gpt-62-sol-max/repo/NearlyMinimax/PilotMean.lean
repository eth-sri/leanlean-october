module

public import NearlyMinimax.PilotFields


@[expose] public section

/-! Actual conditional means of two-pilot bilinear statistics. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFields
set_option backward.isDefEq.respectTransparency false

variable {Ω W H : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {μ : Measure Ω} {M : Measure W} [IsProbabilityMeasure μ] [IsFiniteMeasure M]

def pilotMean (m : W → H) (η : Ω → W → H) (B : W → H →L[ℝ] H) (z : Ω × Ω) : ℝ :=
  ∫ w, ⟪m w + η z.1 w, B w (m w + η z.2 w)⟫ ∂M

private theorem integral_add_three {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g h : X → ℝ} (hf : Integrable f ν) (hg : Integrable g ν) (hh : Integrable h ν) :
    (∫ x, f x + g x + h x ∂ν) = (∫ x, f x ∂ν) + (∫ x, g x ∂ν) + (∫ x, h x ∂ν) := by
  simpa only [Pi.add_apply, integral_add hf hg] using integral_add (hf.add hg) hh

section
variable (m : W → H) (hmm : Measurable m) (hm : MemLp m 2 M)
    {η : Ω → W → H} (hmη : Measurable (fun z : Ω × W => η z.1 z.2))
include hmm hm hmη

theorem pilotMean_sub_eq
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C : ℝ} (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    {x y : Ω} (hx : MemLp (η x) 2 M) (hy : MemLp (η y) 2 M) :
    pilotMean (M := M) m η B (x, y) - (∫ w, ⟪m w, B w (m w)⟫ ∂M) =
      test (M := M) η (fun w => B w (m w)) x + test (M := M) η (fun w => B w (m w)) y +
        bilinear (M := M) η B (x,y) := by
  have hBm := operatorField_memLp hmB hbound hmm hm
  have hmy : Measurable (η y) := hmη.comp (measurable_const.prodMk measurable_id)
  have hBy := operatorField_memLp hmB hbound hmy hy
  have h₀ := inner_integrable hm hBm
  have h₁ := inner_integrable hx hBm
  have h₂ := inner_integrable hy hBm
  have h₃ := inner_integrable hx hBy
  have he : (fun w => ⟪m w + η x w, B w (m w + η y w)⟫) =
      (fun w => ⟪m w, B w (m w)⟫ + ⟪η x w, B w (m w)⟫ +
        ⟪η y w, B w (m w)⟫ + ⟪η x w, B w (η y w)⟫) := by
    funext w
    simp [map_add, inner_add_left, inner_add_right, hsym w (m w) (η y w), real_inner_comm (B w (m w)) (η y w)] <;> ring
  simp only [pilotMean, test, bilinear]
  have hadd := integral_add ((h₀.add h₁).add h₂) h₃
  simp only [Pi.add_apply] at hadd
  rw [he, hadd, integral_add_three h₀ h₁ h₂]
  ring

variable [CompleteSpace H]
variable (hη : MemLp (fun z : Ω × W => η z.1 z.2) 2 (μ.prod M))
    (hcenter : ∀ᵐ w ∂M, (∫ x, η x w ∂μ) = 0)
    {B : W → H →L[ℝ] H} (hmB : Measurable (fun z : W × H => B z.1 z.2))
    {C lam : ℝ} (hlam : 0 ≤ lam) (hbound : ∀ w, ‖B w‖ ≤ C)
    (hsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫)
    (htest : TestEnergyBound (μ := μ) (M := M) η lam)
include hη hcenter hmB hlam hbound hsym htest

/-- Mean and variance of an observable represented by a scaled pilot integral. -/
theorem pilotMean_moments (c : ℝ) {G : Ω × Ω → ℝ}
    (he : G =ᵐ[μ.prod μ] fun z => c * pilotMean (M := M) m η B z) :
    MemLp G 2 (μ.prod μ) ∧
    (∫ z, G z ∂μ.prod μ) = c * (∫ w, ⟪m w, B w (m w)⟫ ∂M) ∧
    (∫ z, (G z - ∫ y, G y ∂μ.prod μ) ^ 2 ∂μ.prod μ) ≤
      (3 * c ^ 2) * lam * C ^ 2 * (2 * (∫ w, ‖m w‖ ^ 2 ∂M) +
        ∫ z : Ω × W, ‖η z.1 z.2‖ ^ 2 ∂μ.prod M) := by
  let v := fun w => B w (m w)
  have hv : MemLp v 2 M := operatorField_memLp hmB hbound hmm hm
  let t := test (M := M) η v
  let F := fun z : Ω × Ω => t z.1 + t z.2 + bilinear (M := M) η B z
  let a := ∫ w, ⟪m w, B w (m w)⟫ ∂M
  have hT := test_memLp_two hη hv
  have h₁ : MemLp (fun z : Ω × Ω => t z.1) 2 (μ.prod μ) :=
    hT.comp_measurePreserving measurePreserving_fst
  have h₂ : MemLp (fun z : Ω × Ω => t z.2) 2 (μ.prod μ) :=
    hT.comp_measurePreserving measurePreserving_snd
  obtain ⟨h₃, hE⟩ := bilinear_moments hmη hη hmB hlam hbound htest
  have hF : MemLp F 2 (μ.prod μ) := (h₁.add h₂).add h₃
  have h0 : (∫ z, F z ∂μ.prod μ) = 0 := by
    have h₁ := h₁.integrable (by norm_num)
    have h₂ := h₂.integrable (by norm_num)
    have h₃i := h₃.integrable (by norm_num)
    dsimp [F]
    rw [integral_add_three h₁ h₂ h₃i,
      integral_fun_fst, integral_fun_snd, bilinear_mean_zero hmη hη hmB hbound h₃ hcenter]
    simp [t, test_mean_zero hη hv hcenter]
  have hEq : G =ᵐ[μ.prod μ] fun z => c * F z + c * a := by
    filter_upwards [he,
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae (memLp_sections hη),
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae (memLp_sections hη)] with z he hx hy
    have hs : pilotMean (M := M) m η B z - a = F z :=
      pilotMean_sub_eq m hmm hm hmη hmB hbound hsym hx hy
    rw [he, ← hs]
    ring
  have hMean : (∫ z, G z ∂μ.prod μ) = c * a := by
    rw [integral_congr_ae hEq, integral_add ((hF.integrable (by norm_num)).const_mul _) (integrable_const _),
      integral_const_mul, h0]
    simp
  refine ⟨((hF.const_mul c).add (memLp_const (c * a))).ae_eq hEq.symm, hMean, ?_⟩
  rw [hMean, integral_congr_ae (hEq.mono (fun z hz => show (G z - c * a) ^ 2 = c ^ 2 * F z ^ 2 by rw [hz, add_sub_cancel_right, mul_pow])),
    integral_const_mul]
  have hFbound : (∫ z, F z ^ 2 ∂μ.prod μ) ≤
      3 * ((∫ x, t x ^ 2 ∂μ) + (∫ x, t x ^ 2 ∂μ) + (∫ z, bilinear (M := M) η B z ^ 2 ∂μ.prod μ)) := by
    have i₁ := h₁.integrable_sq
    have i₂ := h₂.integrable_sq
    have i₃ := h₃.integrable_sq
    calc
      _ ≤ ∫ z : Ω × Ω, 3 * (t z.1 ^ 2 + t z.2 ^ 2 + bilinear (M := M) η B z ^ 2) ∂μ.prod μ :=
        integral_mono hF.integrable_sq (((i₁.add i₂).add i₃).const_mul _) (fun z => by
          dsimp [F]
          nlinarith [sq_nonneg (t z.1 - t z.2),
            sq_nonneg (t z.1 - bilinear (M := M) η B z),
            sq_nonneg (t z.2 - bilinear (M := M) η B z)])
      _ = _ := by rw [integral_const_mul, integral_add_three i₁ i₂ i₃,
        integral_fun_fst (fun x => t x ^ 2), integral_fun_snd (fun x => t x ^ 2)]; simp
  have hTbound : (∫ x, t x ^ 2 ∂μ) ≤ lam * (C ^ 2 * ∫ w, ‖m w‖ ^ 2 ∂M) :=
    (htest v hv).trans (mul_le_mul_of_nonneg_left (operatorField_energy_le hmB hbound hmm hm) hlam)
  apply (mul_le_mul_of_nonneg_left hFbound (sq_nonneg c)).trans
  have h := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hTbound hTbound) hE)
    (show 0 ≤ c ^ 2 * 3 by positivity)
  convert h using 1 <;> ring

end
end NearlyMinimax.PilotFields
