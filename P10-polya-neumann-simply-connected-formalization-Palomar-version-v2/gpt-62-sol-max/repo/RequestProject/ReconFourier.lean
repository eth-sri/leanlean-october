module

public import RequestProject.ReconFourierBasic

/-!
# Solving the Helmholtz equation with a compactly supported source by Fourier transform

Let `T(φ) = ∫ (G Δφ + ∑ᵢ G'ᵢ ∂ᵢφ)` with `G, G'ᵢ ∈ L²` compactly supported, and assume that the
Fourier transform `T(e_ξ)` vanishes on the circle `4π²|ξ|² = E`. Then the `L²` solution of
`(Δ + E) u = T` exists and `u - G ∈ H¹(ℝ²)` (`exists_helmholtz_solution`).

The solution is `w = 𝓕⁻ ŵ` with `ŵ = S / (E - 4π²|ξ|²)`, where
`S(ξ) = -E Ĝ(ξ) - 2πi ∑ᵢ ⟨vᵢ, ξ⟩ Ĝ'ᵢ(ξ)`. Writing `S = N - (E - 4π²|ξ|²) Ĝ` with
`N(ξ) = T(e_ξ)`, which is locally Lipschitz and vanishes on the circle, shows that `ŵ` is bounded
near the circle; away from it `|ŵ| (1 + |ξ|) ≲ |Ĝ| + ∑ |Ĝ'ᵢ|`.
-/

@[expose] public section

open MeasureTheory Set Filter FourierTransform Metric
open scoped ComplexConjugate Real FourierTransform

noncomputable section

namespace PolyaNeumann

/-! ### Symbols -/

section

variable (i : Fin 2)
include i

/-- The coordinate `⟨vᵢ, ξ⟩` of `ξ` along `vᵢ = coordDir i`. -/
def cdir  (ξ : ℂ) : ℝ := (conj (coordDir i) * ξ).re

lemma abs_cdir_le  (ξ : ℂ) : |cdir i ξ| ≤ ‖ξ‖ := by
  unfold cdir
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj, norm_coordDir, one_mul]


lemma contDiff_cdir : ContDiff ℝ 1 (cdir i) :=
  Complex.reCLM.contDiff.comp (contDiff_const.mul contDiff_id)

end

lemma norm_two_pi_I_mul (x : ℝ) : ‖-(2 * π * Complex.I) * (x : ℂ)‖ = 2 * π * |x| := by simp

/-- `N(ξ) = -4π²|ξ|² F(ξ) - 2πi ∑ᵢ ⟨vᵢ, ξ⟩ F'ᵢ(ξ)`. -/
def symN (F : ℂ → ℂ) (F' : Fin 2 → ℂ → ℂ) (ξ : ℂ) : ℂ :=
  -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * F ξ + ∑ i, (-(2 * π * Complex.I) * cdir i ξ) * F' i ξ

section

variable (E : ℝ)
include E

/-- `S(ξ) = -E F(ξ) - 2πi ∑ᵢ ⟨vᵢ, ξ⟩ F'ᵢ(ξ)`. -/
def symS  (F : ℂ → ℂ) (F' : Fin 2 → ℂ → ℂ) (ξ : ℂ) : ℂ :=
  -(E : ℂ) * F ξ + ∑ i, (-(2 * π * Complex.I) * cdir i ξ) * F' i ξ

/-- The symbol `E - 4π²|ξ|²` of `Δ + E`. -/
def symD  (ξ : ℂ) : ℂ := ((E - 4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)

lemma symS_eq  (F : ℂ → ℂ) (F' : Fin 2 → ℂ → ℂ) (ξ : ℂ) :
    symS E F F' ξ = symN F F' ξ - symD E ξ * F ξ := by
  simp only [symS, symN, symD]; push_cast; ring

lemma norm_symD  (ξ : ℂ) : ‖symD E ξ‖ = |E - 4 * π ^ 2 * ‖ξ‖ ^ 2| := by
  rw [symD, Complex.norm_real, Real.norm_eq_abs]

end

lemma contDiff_symS {E : ℝ} {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hF' : ∀ i, ContDiff ℝ 1 (F' i)) : ContDiff ℝ 1 (symS E F F') := by
  unfold symS
  exact (contDiff_const.mul hF).add (ContDiff.sum (s := Finset.univ) fun i _ =>
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_cdir i))).mul (hF' i))

lemma exists_sphere_near {k : ℝ} (hk : 0 < k) (ξ : ℂ) :
    ∃ ξ₀ : ℂ, ‖ξ₀‖ = k ∧ ‖ξ - ξ₀‖ = |‖ξ‖ - k| := by
  by_cases h : ξ = 0
  · refine ⟨(k : ℂ), ?_, ?_⟩
    grind [Complex.norm_real, Real.norm_eq_abs]
    simp_all
  · have hn := norm_ne_zero_iff.mpr h
    have hn' : (‖ξ‖ : ℂ) ≠ 0 := by norm_cast
    refine ⟨((k / ‖ξ‖ : ℝ) : ℂ) * ξ, ?_, ?_⟩
    grind [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    · have e : ξ - ((k / ‖ξ‖ : ℝ) : ℂ) * ξ = (((‖ξ‖ - k) / ‖ξ‖ : ℝ) : ℂ) * ξ := by
        push_cast; field_simp
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm,
        div_mul_cancel₀ _ hn]

/-- The global first-order multiplier bound, using Lipschitz vanishing on the energy circle. -/
lemma symS_div_bound {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} {k E : ℝ} (hk0 : 0 < k)
    (hk : 4 * π ^ 2 * k ^ 2 = E) (hS : ContDiff ℝ 1 (symS E F F'))
    (hN : ∀ ξ, ‖ξ‖ = k → symN F F' ξ = 0) :
    ∃ M : ℝ, ∀ ξ, ‖symS E F F' ξ / symD E ξ‖ * (1 + ‖ξ‖) ≤
      M * ((closedBall (0 : ℂ) (2 * k + 1)).indicator (fun _ => (1 : ℝ)) ξ + ‖F ξ‖ +
        ∑ i, ‖F' i ξ‖) := by
  have hE := hk ▸ (by positivity : 0 ≤ 4 * π ^ 2 * k ^ 2)
  let R := 2 * k + 1
  obtain ⟨L, hL⟩ := hS.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ℂ) R) (isCompact_closedBall _ _)
  let A := E + 2 * π
  let C := L / (4 * π ^ 2 * k) * (1 + R)
  let D := 2 * A / (3 * π ^ 2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C + D, fun ξ => ?_⟩
  set r := ‖ξ‖
  set m := ‖F ξ‖ + ∑ i, ‖F' i ξ‖
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hden : ‖symD E ξ‖ = 4 * π ^ 2 * (k + r) * |k - r| := by
    rw [norm_symD, ← hk, show 4 * π ^ 2 * k ^ 2 - 4 * π ^ 2 * r ^ 2 =
      4 * π ^ 2 * (k + r) * (k - r) by ring, abs_mul, abs_of_nonneg (by positivity)]
  by_cases hξ : r ≤ R
  · have hind : ξ ∈ closedBall (0 : ℂ) R := by simpa [Metric.mem_closedBall, dist_zero_right] using hξ
    rw [indicator_of_mem hind]
    obtain ⟨η, hη, hdist⟩ := exists_sphere_near hk0 ξ
    have hz : symS E F F' η = 0 := by simp [symS_eq, hN η hη, symD, hη, hk]
    have hηR : η ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff, hη]
      dsimp [R]; linarith
    have hlip := hL.dist_le_mul ξ hind η hηR
    rw [dist_eq_norm, dist_eq_norm, hz, sub_zero, hdist, abs_sub_comm] at hlip
    have hw : ‖symS E F F' ξ / symD E ξ‖ ≤ L / (4 * π ^ 2 * k) := by
      rw [norm_div]
      refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) (hlip.trans ?_)
      rw [hden]
      calc L * |k - r| = (L / (4 * π ^ 2 * k)) * (4 * π ^ 2 * k * |k - r|) := by field_simp
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg ξ)) (by positivity))
            (abs_nonneg _)) (by positivity)
    rw [add_assoc]
    change ‖symS E F F' ξ / symD E ξ‖ * (1 + r) ≤ (C + D) * (1 + m)
    calc _ ≤ C := mul_le_mul hw (by linarith) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hC hm, mul_nonneg hD hm]
  · have hr := lt_of_not_ge hξ
    have hr1 : 1 ≤ r := by dsimp [R] at hr; linarith
    have hrk : 2 * k ≤ r := by dsimp [R] at hr; linarith
    have hr0 : 0 < r := by linarith
    have hR' : ξ ∉ closedBall (0 : ℂ) R := by simpa [Metric.mem_closedBall, dist_zero_right] using hξ
    rw [indicator_of_notMem hR', zero_add]
    have hDb : 3 * π ^ 2 * r ^ 2 ≤ ‖symD E ξ‖ := by
      rw [norm_symD]
      change 3 * π ^ 2 * r ^ 2 ≤ |E - 4 * π ^ 2 * r ^ 2|
      rw [← hk, abs_of_nonpos (sub_nonpos.mpr (by gcongr; linarith))]
      have h : 4 * k ^ 2 ≤ r ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg π)]
    have hnum : ‖symS E F F' ξ‖ ≤ A * r * m := by
      have h (i : Fin 2) : ‖(-(2 * π * Complex.I) * (cdir i ξ : ℂ)) * F' i ξ‖ ≤
          2 * π * r * ‖F' i ξ‖ := by
        rw [norm_mul, norm_two_pi_I_mul]
        gcongr
        exact abs_cdir_le i ξ
      have hs := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun i _ => h i)
      rw [← Finset.mul_sum] at hs
      unfold symS
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
      refine (add_le_add_right hs _).trans ?_
      dsimp [m]
      have he : E ≤ E * r := by nlinarith
      have hp : 0 ≤ ∑ i, ‖F' i ξ‖ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right he (norm_nonneg (F ξ)), mul_nonneg (mul_nonneg hE hr0.le) hp,
        mul_nonneg (by positivity : 0 ≤ 2 * π * r) (norm_nonneg (F ξ))]
    have hpos := lt_of_lt_of_le (by positivity) hDb
    rw [norm_div, div_mul_eq_mul_div, div_le_iff₀ hpos]
    calc ‖symS E F F' ξ‖ * (1 + r) ≤ (A * r * m) * (2 * r) := by
          gcongr; nlinarith
      _ = D * m * (3 * π ^ 2 * r ^ 2) := by dsimp [D]; field_simp
      _ ≤ (C + D) * m * ‖symD E ξ‖ := by gcongr; linarith

section

variable {f : ℂ → ℂ} (hf : Integrable f) (ξ : ℂ)
include f hf ξ

lemma integrable_ePlane_mul  :
    Integrable fun x => ePlane ξ x * f x :=
  hf.bdd_mul (c := 1) ((continuous_ePlane_prod.comp
    (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun x => (norm_ePlane ξ x).le)

end

/-- `T(e_ξ) = N(ξ)` with `F = Ĝ`, `F'ᵢ = Ĝ'ᵢ`. -/
lemma integral_helm_ePlane {G : ℂ → ℂ} {G' : Fin 2 → ℂ → ℂ} (hG : Integrable G)
    (hG' : ∀ i, Integrable (G' i)) (ξ : ℂ) :
    ∫ z, (G z * lap (ePlane ξ) z + ∑ i : Fin 2, G' i z * dirD (ePlane ξ) (coordDir i) z) =
      symN (𝓕 G) (fun i => 𝓕 (G' i)) ξ := by
  have e : ∀ z, G z * lap (ePlane ξ) z + ∑ i : Fin 2, G' i z * dirD (ePlane ξ) (coordDir i) z =
      -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * (ePlane ξ z * G z) +
        ((-(2 * π * Complex.I) * cdir 0 ξ) * (ePlane ξ z * G' 0 z) +
          (-(2 * π * Complex.I) * cdir 1 ξ) * (ePlane ξ z * G' 1 z)) := by
    intro z
    rw [lap_ePlane, Fin.sum_univ_two, dirD_ePlane, dirD_ePlane]
    simp only [cdir]
    push_cast
    ring
  simp_rw [e]
  have h0 : Integrable fun z => (-(2 * π * Complex.I) * cdir 0 ξ) * (ePlane ξ z * G' 0 z) :=
    (integrable_ePlane_mul (hG' 0) ξ).const_mul _
  have h1 : Integrable fun z => (-(2 * π * Complex.I) * cdir 1 ξ) * (ePlane ξ z * G' 1 z) :=
    (integrable_ePlane_mul (hG' 1) ξ).const_mul _
  have h01 : Integrable fun z => (-(2 * π * Complex.I) * cdir 0 ξ) * (ePlane ξ z * G' 0 z) +
      (-(2 * π * Complex.I) * cdir 1 ξ) * (ePlane ξ z * G' 1 z) := h0.add h1
  rw [integral_add ((integrable_ePlane_mul hG ξ).const_mul _) h01,
    integral_add ((integrable_ePlane_mul (hG' 0) ξ).const_mul _)
        ((integrable_ePlane_mul (hG' 1) ξ).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, ← fourier_eq_ePlane,
    ← fourier_eq_ePlane, ← fourier_eq_ePlane, symN, Fin.sum_univ_two]

/-! ### The solution -/

lemma memLp_fourierInv_test {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    MemLp (𝓕⁻ φ) 2 volume := by
  have : 𝓕⁻ φ = ((𝓕⁻ hφ.schwartz : SchwartzMap ℂ ℂ) : ℂ → ℂ) := by
    rw [SchwartzMap.fourierInv_coe]; rfl
  rw [this]; exact (𝓕⁻ hφ.schwartz).memLp 2 volume

lemma continuous_symD (E : ℝ) : Continuous (symD E) := by
  unfold symD; fun_prop

/-- On the energy circle `symD = 0` forces `symS = 0`, so `(S / D) · D = S` everywhere. -/
lemma symS_div_mul_symD {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} {k E : ℝ} (hk0 : 0 < k)
    (hk : 4 * π ^ 2 * k ^ 2 = E) (hN : ∀ ξ, ‖ξ‖ = k → symN F F' ξ = 0) (ξ : ℂ) :
    symS E F F' ξ / symD E ξ * symD E ξ = symS E F F' ξ := by
  by_cases hD : symD E ξ = 0
  · have h0 : E - 4 * π ^ 2 * ‖ξ‖ ^ 2 = 0 := by
      grind [symD, Complex.ofReal_eq_zero]
    have hsq : ‖ξ‖ ^ 2 = k ^ 2 := by
      have : (4 * π ^ 2) * (‖ξ‖ ^ 2 - k ^ 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      aesop
      · linarith
    have hn : ‖ξ‖ = k := by
      have := (sq_eq_sq₀ (norm_nonneg ξ) hk0.le).mp hsq
      assumption
    simp_all [symS_eq]
  simp_all

/-- Existence of the `L²` solution of `(Δ + E) u = T` when `T̂` vanishes on the energy circle. -/
theorem exists_helmholtz_solution {E : ℝ} (hE : 0 < E) {G : ℂ → ℂ} {G' : Fin 2 → ℂ → ℂ}
    (hG : MemLp G 2 volume) (hGc : HasCompactSupport G) (hG' : ∀ i, MemLp (G' i) 2 volume)
    (hG'c : ∀ i, HasCompactSupport (G' i))
    (hvan : ∀ ξ : ℂ, 4 * π ^ 2 * ‖ξ‖ ^ 2 = E →
      ∫ z, (G z * lap (ePlane ξ) z + ∑ i : Fin 2, G' i z * dirD (ePlane ξ) (coordDir i) z) = 0) :
    ∃ (w : ℂ → ℂ) (gw : Fin 2 → ℂ → ℂ), MemLp w 2 volume ∧ (∀ i, MemLp (gw i) 2 volume) ∧
      IsWeakGradOn univ w gw ∧
      ∀ φ : ℂ → ℂ, TestFunction univ φ →
        ∑ i : Fin 2, ∫ z, (G' i z + gw i z) * dirD φ (coordDir i) z =
          (E : ℂ) * ∫ z, (G z + w z) * φ z := by
  -- the data and their Fourier transforms
  have hG1 := integrable_of_memLp_two_hasCompactSupport hG hGc
  have hG'1 := fun i =>
    integrable_of_memLp_two_hasCompactSupport (hG' i) (hG'c i)
  let F : ℂ → ℂ := 𝓕 G
  let F' : Fin 2 → ℂ → ℂ := fun i => 𝓕 (G' i)
  have hFd : ContDiff ℝ 1 F := contDiff_fourier_of_compact hG1 hGc
  have hF'd : ∀ i, ContDiff ℝ 1 (F' i) := fun i => contDiff_fourier_of_compact (hG'1 i) (hG'c i)
  have hF2 : MemLp F 2 volume := memLp_fourier hG hG1
  have hF'2 : ∀ i, MemLp (F' i) 2 volume := fun i => memLp_fourier (hG' i) (hG'1 i)
  have hSd := contDiff_symS (E := E) hFd hF'd
  -- the radius of the energy circle
  set k := Real.sqrt E / (2 * π) with hkdef
  have hk0 : 0 < k := by positivity
  have hk : 4 * π ^ 2 * k ^ 2 = E := by
    rw [div_pow, Real.sq_sqrt hE.le]; field_simp; ring
  have hN : ∀ ξ, ‖ξ‖ = k → symN F F' ξ = 0 := fun ξ hξ => by
    rw [← integral_helm_ePlane hG1 hG'1 ξ]
    exact hvan ξ (by rw [hξ, hk])
  obtain ⟨M, hM⟩ := symS_div_bound hk0 hk hSd hN
  -- the Fourier transform of the solution and of its gradient
  set wh : ℂ → ℂ := fun ξ => symS E F F' ξ / symD E ξ with hwhdef
  set gwh : Fin 2 → ℂ → ℂ := fun i ξ => (2 * π * Complex.I * cdir i ξ) * wh ξ with hgwhdef
  set D : ℂ → ℝ := fun ξ => M * ((Metric.closedBall (0 : ℂ) (2 * k + 1)).indicator
    (fun _ => (1 : ℝ)) ξ + ‖F ξ‖ + ∑ i, ‖F' i ξ‖) with hDdef
  have hD2 : MemLp D 2 volume := by
    refine MemLp.const_mul ?_ M
    refine ((memLp_indicator_const 2 Metric.isClosed_closedBall.measurableSet (1 : ℝ)
      (Or.inr measure_closedBall_lt_top.ne)).add hF2.norm).add ?_
    exact memLp_finset_sum _ fun i _ => (hF'2 i).norm
  have hwhm : AEStronglyMeasurable wh volume :=
    (hSd.continuous.measurable.div (continuous_symD E).measurable).aestronglyMeasurable
  have hwhD := hM
  have hwh2 : MemLp wh 2 volume := by
    refine hD2.of_le hwhm (Eventually.of_forall fun ξ => ?_)
    refine le_trans ?_ (Real.le_norm_self _)
    refine le_trans ?_ (hwhD ξ)
    have := norm_nonneg (wh ξ)
    nlinarith [norm_nonneg ξ]
  have hgwh2 : ∀ i, MemLp (gwh i) 2 volume := fun i => by
    refine (hD2.const_mul (2 * π)).of_le ?_ (Eventually.of_forall fun ξ => ?_)
    · exact (((continuous_const.mul (Complex.continuous_ofReal.comp
        (contDiff_cdir i).continuous)).aestronglyMeasurable).mul hwhm)
    · refine le_trans ?_ (Real.le_norm_self _)
      simp only [hgwhdef]
      have e : (2 * π * Complex.I * (cdir i ξ : ℂ)) = -(-(2 * π * Complex.I) * (cdir i ξ : ℂ)) := by
        ring
      rw [norm_mul, e, norm_neg, norm_two_pi_I_mul]
      have h1 := abs_cdir_le i ξ
      have h2 := hwhD ξ
      have h3 := norm_nonneg (wh ξ)
      have h4 : |cdir i ξ| * ‖wh ξ‖ ≤ ‖wh ξ‖ * (1 + ‖ξ‖) := by nlinarith [norm_nonneg ξ]
      nlinarith [Real.pi_pos]
  -- the solution
  set W : Lp ℂ 2 (volume : Measure ℂ) := 𝓕⁻ (hwh2.toLp wh) with hWdef
  set GW : Fin 2 → Lp ℂ 2 (volume : Measure ℂ) := fun i => 𝓕⁻ ((hgwh2 i).toLp (gwh i))
    with hGWdef
  have hpair : ∀ (A : ℂ → ℂ) (hA : MemLp A 2 volume) {ψ : ℂ → ℂ}, TestFunction univ ψ →
      ∫ x, (𝓕⁻ (hA.toLp A) : Lp ℂ 2 (volume : Measure ℂ)) x * ψ x = ∫ ξ, A ξ * 𝓕⁻ ψ ξ :=
    fun A hA ψ hψ => by
      rw [integral_fourierInv_Lp_mul _ hψ]
      refine integral_congr_ae ?_
      filter_upwards [hA.coeFn_toLp] with ξ hξ
      tauto
  refine ⟨W, fun i => GW i, Lp.memLp _, fun i => Lp.memLp _, ?_, ?_⟩
  · -- weak gradient
    intro φ hφ i
    have h1 : ∫ z, W z * fderiv ℝ φ z (coordDir i) =
        ∫ ξ, wh ξ * 𝓕⁻ (dirD φ (coordDir i)) ξ := hpair wh hwh2 (hφ.dirD _)
    have h2 : ∫ z, GW i z * φ z = ∫ ξ, gwh i ξ * 𝓕⁻ φ ξ := hpair (gwh i) (hgwh2 i) hφ
    rw [h1, h2, ← integral_neg]
    congr 1
    funext ξ
    rw [fourierInv_dirD hφ]
    simp only [hgwhdef, cdir]
    ring
  · intro φ hφ
    have hpair_add {A B : ℂ → ℂ} (hA1 : Integrable A) (hA : MemLp A 2 volume)
        (hB : MemLp B 2 volume) {ψ : ℂ → ℂ} (hψ : TestFunction univ ψ) :
        ∫ z, (A z + (𝓕⁻ (hB.toLp B) : Lp ℂ 2 (volume : Measure ℂ)) z) * ψ z =
          ∫ ξ, (𝓕 A ξ + B ξ) * 𝓕⁻ ψ ξ := by
      simp_rw [add_mul]
      have hψ' := memLp_fourierInv_test hψ
      have hiA : Integrable (fun ξ => 𝓕 A ξ * 𝓕⁻ ψ ξ) := (memLp_fourier hA hA1).integrable_mul hψ'
      have hiB : Integrable (fun ξ => B ξ * 𝓕⁻ ψ ξ) := hB.integrable_mul hψ'
      rw [integral_add (integrable_mul_test hA hψ) (integrable_mul_test (Lp.memLp _) hψ),
        integral_add hiA hiB, hpair B hB hψ, ← integral_fourier_mul_fourierInv hA1 hψ]
    have hi (i : Fin 2) : Integrable (fun ξ => (F' i ξ + gwh i ξ) * 𝓕⁻ (dirD φ (coordDir i)) ξ) :=
      ((hF'2 i).add (hgwh2 i)).integrable_mul (memLp_fourierInv_test (hφ.dirD _))
    rw [hpair_add hG1 hG hwh2 hφ, ← integral_const_mul]
    have hs (i : Fin 2) :
        (∫ z, (G' i z + GW i z) * dirD φ (coordDir i) z) =
          ∫ ξ, (F' i ξ + gwh i ξ) * 𝓕⁻ (dirD φ (coordDir i)) ξ :=
      hpair_add (hG'1 i) (hG' i) (hgwh2 i) (hφ.dirD _)
    simp_rw [hs]
    rw [← integral_finset_sum _ fun i _ => hi i]
    refine integral_congr_ae (.of_forall fun ξ => ?_)
    have hD := symS_div_mul_symD hk0 hk hN ξ
    change wh ξ * _ = _ at hD
    have h0 : cdir 0 ξ = ξ.re := by simp [cdir, coordDir]
    have h1 : cdir 1 ξ = ξ.im := by simp [cdir, coordDir, Complex.mul_re]
    have hn : (‖ξ‖ : ℂ) ^ 2 = (ξ.re : ℂ) ^ 2 + (ξ.im : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]; push_cast; ring
    have he (i : Fin 2) : 𝓕⁻ (dirD φ (coordDir i)) ξ =
        -(2 * π * Complex.I) * cdir i ξ * 𝓕⁻ φ ξ := fourierInv_dirD hφ _ _
    simp_rw [he]
    simp only [Fin.sum_univ_two, hgwhdef, h0, h1]
    simp only [symS, symD, Fin.sum_univ_two, h0, h1] at hD
    push_cast at hD
    rw [hn] at hD
    linear_combination -𝓕⁻ φ ξ * hD - (4 * π ^ 2 * ((ξ.re : ℂ) ^ 2 + (ξ.im : ℂ) ^ 2) *
      wh ξ * 𝓕⁻ φ ξ) * Complex.I_sq

end PolyaNeumann
