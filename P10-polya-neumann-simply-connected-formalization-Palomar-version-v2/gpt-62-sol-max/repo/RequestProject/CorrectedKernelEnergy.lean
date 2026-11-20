module

public import RequestProject.CircleFourier
public import RequestProject.ObservationHSEnergy
public import RequestProject.CorrectedKernelSymm
public import RequestProject.CorrectedKernelCont
public import RequestProject.MatrixHS

/-! The normalized remainder is Hilbert–Schmidt by the first-order Fourier
energy of its Lipschitz rows and Hermitian symmetry. -/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory Topology Set
open scoped InnerProductSpace ComplexConjugate

/-- Fourier coefficients on `[0, 2π]` are bounded by the sup norm. -/
lemma norm_fourierCoeffOn_le_of_bound {f : ℝ → ℂ} {M : ℝ}
    (hM : ∀ x ∈ Icc 0 (2 * π), ‖f x‖ ≤ M) (n : ℤ) :
    ‖fourierCoeffOn two_pi_pos f n‖ ≤ M := by
  rw [fourierCoeffOn_eq_integral, norm_smul]
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) (2 * π),
      ‖fourier (-n) (x : AddCircle (2 * π - 0)) • f x‖ ≤ M := by
    intro x hx
    rw [Set.uIoc_of_le two_pi_pos.le] at hx
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    grind
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have h2 : (0 : ℝ) < 2 * π - 0 := by rw [sub_zero]; positivity
  rw [abs_of_pos h2] at this
  refine (mul_le_mul_of_nonneg_left this (norm_nonneg ((1 : ℝ) / (2 * π - 0)))).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

/-- Fourier coefficients on `[0, 2π]` are additive on integrable functions. -/
lemma fourierCoeffOn_sub_of_intervalIntegrable {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 (2 * π)) (hg : IntervalIntegrable g volume 0 (2 * π))
    (n : ℤ) :
    fourierCoeffOn two_pi_pos (fun x => f x - g x) n =
      fourierCoeffOn two_pi_pos f n - fourierCoeffOn two_pi_pos g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    ← smul_sub]
  congr 1
  have hc : ContinuousOn (fun x : ℝ => fourier (-n) (x : AddCircle (2 * π - 0))) (uIcc 0 (2 * π)) :=
    ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)).continuousOn
  simp_rw [smul_sub]
  exact intervalIntegral.integral_sub (hf.continuousOn_mul hc) (hg.continuousOn_mul hc)

/-- Double Fourier coefficients of a kernel on `[0, 2π]²`. -/
def doubleCoeff (k : ℝ → ℝ → ℂ) (p : ℤ × ℤ) : ℂ :=
  fourierCoeffOn two_pi_pos (fun θ => fourierCoeffOn two_pi_pos (k θ) p.1) p.2

private lemma boundedKernel_intervalIntegrable {k : ℝ → ℝ → ℂ} {M : ℝ}
    (hm : ∀ θ, Measurable (k θ)) (hb : ∀ θ t, ‖k θ t‖ ≤ M) (θ : ℝ) :
    IntervalIntegrable (k θ) volume 0 (2 * π) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mpr
    (Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
      (hm θ).aestronglyMeasurable (ae_of_all _ (hb θ)))

private lemma continuous_kernelCoeff {k : ℝ → ℝ → ℂ} {M : ℝ} {K : NNReal}
    (hm : ∀ θ, Measurable (k θ)) (hb : ∀ θ t, ‖k θ t‖ ≤ M)
    (hl : ∀ θ θ' t, ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|) (n : ℤ) :
    Continuous fun θ => fourierCoeffOn two_pi_pos (k θ) n :=
  (LipschitzWith.of_dist_le_mul (K := K) fun θ θ' => by
    rw [dist_eq_norm, ← fourierCoeffOn_sub_of_intervalIntegrable
      (boundedKernel_intervalIntegrable hm hb θ) (boundedKernel_intervalIntegrable hm hb θ')]
    exact norm_fourierCoeffOn_le_of_bound (fun t _ => hl θ θ' t) n).continuous

private lemma doubleCoeff_sub {k l : ℝ → ℝ → ℂ} {M N : ℝ} {K L : NNReal}
    (hkm : ∀ θ, Measurable (k θ)) (hlm : ∀ θ, Measurable (l θ))
    (hkb : ∀ θ t, ‖k θ t‖ ≤ M) (hlb : ∀ θ t, ‖l θ t‖ ≤ N)
    (hkl : ∀ θ θ' t, ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|)
    (hll : ∀ θ θ' t, ‖l θ t - l θ' t‖ ≤ L * |θ - θ'|) (p : ℤ × ℤ) :
    doubleCoeff (fun θ t => k θ t - l θ t) p = doubleCoeff k p - doubleCoeff l p := by
  unfold doubleCoeff
  simp_rw [fun θ => fourierCoeffOn_sub_of_intervalIntegrable
    (boundedKernel_intervalIntegrable hkm hkb θ) (boundedKernel_intervalIntegrable hlm hlb θ) p.1]
  exact fourierCoeffOn_sub_of_intervalIntegrable
    ((continuous_kernelCoeff hkm hkb hkl p.1).intervalIntegrable _ _)
    ((continuous_kernelCoeff hlm hlb hll p.1).intervalIntegrable _ _) p.2

variable {γ : ℝ → ℂ} {K K' : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}

section

variable (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ)
include W θ t

/-- The corrected kernel, restricted to `[0, 2π)` in `θ` and extended periodically, with `t`
clamped to `[0, 2π]`. -/
def ckPer  : ℂ :=
  periodize (fun θ' => correctedKernel W θ' (clampTwoPi t)) θ


end

lemma toIcoMod_mem_Icc_two_pi (θ : ℝ) : toIcoMod two_pi_pos 0 θ ∈ Icc 0 (2 * π) := by
  have := toIcoMod_mem_Ico two_pi_pos 0 θ
  grind

lemma measurable_ckPer (hW : IsTransport γ E W) (θ : ℝ) : Measurable (ckPer W θ) :=
  measurable_correctedKernel_clamp hW _

lemma norm_ckPer_le (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (θ t : ℝ) :
    ‖ckPer W θ t‖ ≤ 4 + ‖cutBE W‖ :=
  norm_correctedKernel_le hK hW (toIcoMod_mem_Icc_two_pi θ) (clampTwoPi_mem t)

lemma ckPer_periodic (W : ℝ → Ell2 →L[ℂ] Ell2) (θ t : ℝ) : ckPer W (θ + 2 * π) t = ckPer W θ t :=
  periodic_periodize _ θ

lemma ckPer_eq (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) {θ t : ℝ} (hθ : θ ∈ Icc 0 (2 * π))
    (ht : t ∈ Icc 0 (2 * π)) : ckPer W θ t = correctedKernel W θ t := by
  unfold ckPer
  rw [periodize_eqOn_Icc (correctedKernel_endpoint hK hW hc (clampTwoPi_mem t)) hθ,
    clampTwoPi_of_mem ht]

/-- The Lipschitz constant in `θ` of the corrected kernel. -/
def ckLip (K : NNReal) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) : NNReal :=
  ⟨Real.sqrt E * shiftConst * K * (2 + ‖cutBE W‖) + 1 / π, by
    have := shiftConst_nonneg; positivity⟩

lemma ckPer_lip (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) (θ θ' t : ℝ) :
    ‖ckPer W θ t - ckPer W θ' t‖ ≤ ckLip K E W * |θ - θ'| := by
  have hL := lipschitzWith_periodize (K := ckLip K E W)
    (fun x hx y hy => norm_correctedKernel_sub_le hK hW hx hy (clampTwoPi_mem t))
    (correctedKernel_endpoint hK hW hc (clampTwoPi_mem t))
  have := hL.dist_le_mul θ θ'
  rwa [dist_eq_norm, Real.dist_eq] at this

section

variable (hK : LipschitzWith K γ)
include hK

lemma doubleCoeff_ckPer  (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) (p : ℤ × ℤ) :
    doubleCoeff (ckPer W) p = doubleCoeff (correctedKernel W) p := by
  unfold doubleCoeff
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [Set.uIcc_of_le two_pi_pos.le] at hθ
  congr 1
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le two_pi_pos.le] at ht
  rw [ckPer_eq hK hW hc hθ ht]

end

variable {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}

lemma eventually_cutC_ne (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ)
    (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    ∀ᶠ E in 𝓝 E₀, cutC (Ws E (2 * π)) (basisVec 0) ≠ 0 :=
  (tendsto_cutC_energy hK hWs E₀).eventually_ne hc

/-- Hilbert–Schmidt matrix operators are additive in the matrix. -/
lemma hsMatrixOp_sub (a b : ℤ × ℤ → ℂ) (ha : Summable fun p => ‖a p‖ ^ 2)
    (hb : Summable fun p => ‖b p‖ ^ 2) (hab : Summable fun p => ‖a p - b p‖ ^ 2) :
    hsMatrixOp a ha - hsMatrixOp b hb = hsMatrixOp (fun p => a p - b p) hab := by
  refine ContinuousLinearMap.ext fun f => lp.ext (funext fun m => ?_)
  rw [ContinuousLinearMap.sub_apply]
  change ⟪hsRow a ha m, f⟫_ℂ - ⟪hsRow b hb m, f⟫_ℂ = ⟪hsRow (fun p => a p - b p) hab m, f⟫_ℂ
  have : hsRow (fun p => a p - b p) hab m = hsRow a ha m - hsRow b hb m :=
    lp.ext (funext fun n => by
      rw [lp.coeFn_sub, Pi.sub_apply, hsRow_apply, hsRow_apply, hsRow_apply, map_sub])
  rw [this, inner_sub_left]

/-- The Fourier matrix of the unnormalized integral operator. -/
def kernelIntegralMatrix {r : ℝ → ℝ → ℂ} (p : ℤ × ℤ) : ℂ :=
  (2 * π : ℂ) * doubleCoeff r (-p.2, p.1)

def normalizedCoeffMatrix (c : ℤ × ℤ → ℂ) (p : ℤ × ℤ) : ℂ :=
  ((sobWeight p.1 ^ (1 / 2 : ℝ) * sobWeight p.2 ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
    ((2 * π : ℂ) * c (-p.2, p.1))

/-- The two half-order weights normalize the corrected remainder on `L²`. -/
def correctedRemainderMatrix (W : ℝ → Ell2 →L[ℂ] Ell2) : ℤ × ℤ → ℂ :=
  normalizedCoeffMatrix (doubleCoeff (correctedKernel W))

lemma correctedRemainderMatrix_apply (W : ℝ → Ell2 →L[ℂ] Ell2) (p : ℤ × ℤ) :
    correctedRemainderMatrix W p =
      ((sobWeight p.1 ^ (1 / 2 : ℝ) * sobWeight p.2 ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        kernelIntegralMatrix (r := correctedKernel W) p := rfl

private lemma norm_normalizedCoeffMatrix_sq_le (c : ℤ × ℤ → ℂ) (p : ℤ × ℤ) :
    ‖normalizedCoeffMatrix c p‖ ^ 2 ≤ 2 * (2 * π) ^ 2 *
      (‖c (-p.2, p.1)‖ ^ 2 + ((-p.2 : ℤ) : ℝ) ^ 2 * ‖c (-p.2, p.1)‖ ^ 2 +
        (p.1 : ℝ) ^ 2 * ‖c (-p.2, p.1)‖ ^ 2) := by
  have hs (n : ℤ) : (sobWeight n ^ (1 / 2 : ℝ)) ^ 2 = sobWeight n := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (sobWeight_pos n).le]
  have hL : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg pi_pos.le]
    norm_num
  have hpos := mul_nonneg (Real.rpow_nonneg (sobWeight_pos p.1).le (1 / 2))
    (Real.rpow_nonneg (sobWeight_pos p.2).le (1 / 2))
  rw [normalizedCoeffMatrix, norm_mul, norm_mul, hL, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpos]
  simp only [mul_pow, hs, Int.cast_neg, neg_sq]
  suffices h : sobWeight p.1 * sobWeight p.2 ≤ 2 * (1 + (p.2 : ℝ) ^ 2 + (p.1 : ℝ) ^ 2) by
    calc _ ≤ (2 * (1 + (p.2 : ℝ) ^ 2 + (p.1 : ℝ) ^ 2)) *
        (2 ^ 2 * π ^ 2 * ‖c (-p.2, p.1)‖ ^ 2) := by gcongr
      _ = _ := by ring
  simp only [sobWeight, ← sq_abs (p.1 : ℝ), ← sq_abs (p.2 : ℝ)]
  nlinarith [sq_nonneg (|(p.1 : ℝ)| - |(p.2 : ℝ)|), sq_nonneg (|(p.1 : ℝ)| - 1),
    sq_nonneg (|(p.2 : ℝ)| - 1)]

/-- Bound the normalized matrix by the zeroth and first Fourier energies of
periodic Lipschitz rows. Symmetry exchanges the two first-order energies. -/
private theorem normalizedCoeffMatrix_energy {c : ℤ × ℤ → ℂ} {k : ℝ → ℝ → ℂ} {M : ℝ} {K : NNReal}
    (hm : ∀ θ, Measurable (k θ)) (hb : ∀ θ t, ‖k θ t‖ ≤ M)
    (hl : ∀ θ θ' t, ‖k θ t - k θ' t‖ ≤ K * |θ - θ'|)
    (hp : ∀ θ t, k (θ + 2 * π) t = k θ t)
    (he : ∀ p, doubleCoeff k p = c p)
    (hflip : ∀ p : ℤ × ℤ, c p = conj (c (-p.2, -p.1))) :
    Summable (fun p => ‖normalizedCoeffMatrix c p‖ ^ 2) ∧
      ∑' p, ‖normalizedCoeffMatrix c p‖ ^ 2 ≤ 2 * (2 * π) ^ 2 * (M ^ 2 + π ^ 2 * K ^ 2 / 2) := by
  let row := kernelRow hm hb
  have hrow : LipschitzWith K row := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm]
    exact norm_kernelRow_sub_le hm hb (fun x y t _ => hl x y t) x y
  have hper := kernelRow_periodic hm hb fun x t _ => hp x t
  let ρ : ℤ × ℤ ≃ ℤ × ℤ :=
    ⟨fun p => (p.1, -p.2), fun p => (p.1, -p.2), by intro p; simp, by intro p; simp⟩
  have e (p : ℤ × ℤ) :
      ‖fourierCoeffOn two_pi_pos (fun θ => ⟪row θ, fourierBasis p.1⟫_ℂ) p.2‖ =
        ‖c (ρ p)‖ := by
    simp only [row, inner_kernelRow_fourierBasis]
    rw [fourierCoeffOn_conj, Complex.norm_conj, ← he]
    rfl
  let a := fun p : ℤ × ℤ => ‖c p‖ ^ 2
  let y := fun p : ℤ × ℤ => (p.2 : ℝ) ^ 2 * a p
  let x := fun p : ℤ × ℤ => (p.1 : ℝ) ^ 2 * a p
  have horth := (fourierBasis (T := 2 * π)).orthonormal
  have ea : (fun p : ℤ × ℤ => ‖fourierCoeffOn two_pi_pos
      (fun θ => ⟪row θ, fourierBasis p.1⟫_ℂ) p.2‖ ^ 2) = a ∘ ρ :=
    funext fun p => by rw [e]; rfl
  have ey : (fun p : ℤ × ℤ => (p.2 : ℝ) ^ 2 * ‖fourierCoeffOn two_pi_pos
      (fun θ => ⟪row θ, fourierBasis p.1⟫_ℂ) p.2‖ ^ 2) = y ∘ ρ :=
    funext fun p => by rw [e]; simp [y, ρ, a]
  obtain ⟨ha, ha'⟩ := tsum_sq_fourierCoeff_rows_le horth hrow.continuous
    (fun θ _ => norm_kernelRow_le hm hb θ)
  have hy := summable_sq_mul_fourierCoeff horth hrow hper
  have hy' := tsum_sq_mul_fourierCoeff_le horth hrow hper
  rw [ea] at ha
  rw [ρ.summable_iff] at ha
  rw [ea] at ha'
  change (∑' p, a (ρ p)) ≤ _ at ha'
  rw [ρ.tsum_eq] at ha'
  rw [ey, ρ.summable_iff] at hy
  rw [ey] at hy'
  change (∑' p, y (ρ p)) ≤ _ at hy'
  rw [ρ.tsum_eq] at hy'
  let τ : ℤ × ℤ ≃ ℤ × ℤ :=
    ⟨fun p => (-p.2, -p.1), fun p => (-p.2, -p.1), by intro p; simp, by intro p; simp⟩
  have hτ (p : ℤ × ℤ) : y (τ p) = x p := by
    simp only [x, y, a, τ, Equiv.coe_fn_mk, Int.cast_neg, neg_sq]
    rw [hflip p, Complex.norm_conj]
  have hx := ((τ.summable_iff).mpr hy).congr hτ
  have hx' : ∑' p, x p ≤ π ^ 2 * K ^ 2 / 4 := by
    simp_rw [← hτ]
    rwa [Equiv.tsum_eq]
  let σ : ℤ × ℤ ≃ ℤ × ℤ :=
    ⟨fun p => (-p.2, p.1), fun p => (p.2, -p.1), by intro p; simp, by intro p; simp⟩
  let b := fun p => 2 * (2 * π) ^ 2 * (a p + x p + y p)
  have hb' : Summable b := ((ha.add hx).add hy).mul_left _
  have hs : Summable (b ∘ σ) := (σ.summable_iff).mpr hb'
  have hle p := norm_normalizedCoeffMatrix_sq_le c p
  have hn := hs.of_nonneg_of_le (fun _ => by positivity) hle
  refine ⟨hn, (hn.tsum_le_tsum hle hs).trans ?_⟩
  change (∑' p, b (σ p)) ≤ _
  rw [Equiv.tsum_eq σ b, show (∑' p, b p) = 2 * (2 * π) ^ 2 * (∑' p, (a p + x p + y p)) from tsum_mul_left,
    (ha.add hx).tsum_add hy, ha.tsum_add hx]
  exact mul_le_mul_of_nonneg_left (by linarith only [ha', hx', hy']) (by positivity)

theorem summable_correctedRemainderMatrix (hK : LipschitzWith K γ)
    (hW : IsTransport γ E W) (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) :
    Summable fun p => ‖correctedRemainderMatrix W p‖ ^ 2 :=
  (normalizedCoeffMatrix_energy (measurable_ckPer hW) (norm_ckPer_le hK hW)
    (ckPer_lip hK hW hc) (ckPer_periodic W) (doubleCoeff_ckPer hK hW hc)
    (fun p => correctedKernelCoeff_conj_symm hK hW p.1 p.2)).1

/-- At a nonzero cut, the normalized compact remainder varies continuously
in Hilbert–Schmidt norm. Only first-order periodic regularity is needed. -/
theorem tendsto_correctedRemainder_energy (hK : LipschitzWith K γ)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ)
    (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    (∀ᶠ E in 𝓝 E₀, Summable fun p => ‖correctedRemainderMatrix (Ws E) p‖ ^ 2) ∧
    ∀ ε > 0, ∀ᶠ E in 𝓝 E₀, ∀ (hE : Summable fun p => ‖correctedRemainderMatrix (Ws E) p‖ ^ 2),
      ‖hsMatrixOp (correctedRemainderMatrix (Ws E)) hE -
        hsMatrixOp (correctedRemainderMatrix (Ws E₀)) (summable_correctedRemainderMatrix hK (hWs E₀) hc)‖ < ε := by
  have hcE := eventually_cutC_ne hK hWs E₀ hc
  refine ⟨hcE.mono fun E h => summable_correctedRemainderMatrix hK (hWs E) h, fun ε hε => ?_⟩
  let C := 2 * (2 * π) ^ 2 * (1 + π ^ 2 / 2)
  have hC : 0 < C := by positivity
  let δ := ε / (2 * √C)
  have hδ : 0 < δ := by positivity
  have hlim : √(2 * (2 * π) ^ 2 * (δ ^ 2 + π ^ 2 * δ ^ 2 / 2)) < ε := by
    rw [show 2 * (2 * π) ^ 2 * (δ ^ 2 + π ^ 2 * δ ^ 2 / 2) = C * δ ^ 2 by ring,
      Real.sqrt_mul hC.le, Real.sqrt_sq hδ.le]
    have h : √C * δ = ε / 2 := by
      dsimp [δ]
      field_simp [(Real.sqrt_pos.2 hC).ne']
    rw [h]
    linarith
  filter_upwards [hcE, tendsto_correctedKernel_energy hK hWs E₀ hc hδ,
    tendsto_correctedKernel_lipschitz hK hWs E₀ hc hδ] with E hc' hb hl hE
  let k := fun θ t => ckPer (Ws E) θ t - ckPer (Ws E₀) θ t
  let c := fun p => doubleCoeff (correctedKernel (Ws E)) p - doubleCoeff (correctedKernel (Ws E₀)) p
  have hkl (x y t : ℝ) : ‖k x t - k y t‖ ≤ (⟨δ, hδ.le⟩ : NNReal) * |x - y| := by
    have h := lipschitzWith_periodize (K := ⟨δ, hδ.le⟩)
      (fun u hu v hv => hl u hu v hv (clampTwoPi t) (clampTwoPi_mem t)) (by
        rw [correctedKernel_endpoint hK (hWs E) hc' (clampTwoPi_mem t),
          correctedKernel_endpoint hK (hWs E₀) hc (clampTwoPi_mem t)])
    have hxy := h.dist_le_mul x y
    rwa [dist_eq_norm, Real.dist_eq] at hxy
  have he (p : ℤ × ℤ) : doubleCoeff k p = c p := by
    unfold k c
    rw [doubleCoeff_sub (measurable_ckPer (hWs E)) (measurable_ckPer (hWs E₀))
      (norm_ckPer_le hK (hWs E)) (norm_ckPer_le hK (hWs E₀)) (ckPer_lip hK (hWs E) hc')
      (ckPer_lip hK (hWs E₀) hc), doubleCoeff_ckPer hK (hWs E) hc', doubleCoeff_ckPer hK (hWs E₀) hc]
  have hflip (p : ℤ × ℤ) : c p = conj (c (-p.2, -p.1)) := by
    unfold c
    rw [map_sub]
    congr 1
    exacts [correctedKernelCoeff_conj_symm hK (hWs E) p.1 p.2,
      correctedKernelCoeff_conj_symm hK (hWs E₀) p.1 p.2]
  obtain ⟨hs, hsum⟩ := normalizedCoeffMatrix_energy (k := k) (M := δ)
    (fun θ => (measurable_ckPer (hWs E) θ).sub (measurable_ckPer (hWs E₀) θ))
    (fun θ t => (hb _ (toIcoMod_mem_Icc_two_pi θ) _ (clampTwoPi_mem t)).le) hkl
    (fun θ t => by simp  [k, ckPer_periodic]) he hflip
  have hm : (fun p => correctedRemainderMatrix (Ws E) p - correctedRemainderMatrix (Ws E₀) p) =
      normalizedCoeffMatrix c := by
    funext p
    simp  [correctedRemainderMatrix, normalizedCoeffMatrix, c, mul_sub]
  rw [hsMatrixOp_sub _ _ _ _ (hs.congr fun p =>
    congrArg (fun z : ℂ => ‖z‖ ^ 2) (congrFun hm p).symm)]
  refine (norm_hsMatrixOp_le _ _).trans_lt ?_
  simp_rw [show ∀ p, correctedRemainderMatrix (Ws E) p - correctedRemainderMatrix (Ws E₀) p =
    normalizedCoeffMatrix c p from congrFun hm]
  exact (Real.sqrt_le_sqrt hsum).trans_lt hlim

end PolyaNeumann
