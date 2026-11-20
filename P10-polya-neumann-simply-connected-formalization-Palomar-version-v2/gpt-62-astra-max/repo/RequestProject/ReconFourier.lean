module

public import RequestProject.ReconFourierBasic
public import RequestProject.PlanarNotation

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

open MeasureTheory Set Filter FourierTransform
open scoped ComplexConjugate Real FourierTransform

noncomputable section

namespace PolyaNeumann

/-! ### Symbols -/

section

variable (i : Fin 2) (E : ℝ) (F : ℂ → ℂ) (F' : Fin 2 → ℂ → ℂ) (ξ : ℂ)

include i ξ in
/-- The coordinate `⟨vᵢ, ξ⟩` of `ξ` along `vᵢ = coordDir i`. -/
def cdir : ℝ := (conj (coordDir i) * ξ).re

lemma abs_cdir_le : |cdir i ξ| ≤ ‖ξ‖ := by
  
  refine (Complex.abs_re_le_norm _).trans ?_
  simp [norm_coordDir]

lemma cdir_sub (η : ℂ) : cdir i ξ - cdir i η = cdir i (ξ - η) := by
  unfold cdir; rw [mul_sub, Complex.sub_re]

lemma continuous_cdir : Continuous (cdir i) := by
  unfold cdir; fun_prop

lemma norm_two_pi_I_mul (x : ℝ) : ‖-(anglePeriod * Complex.I) * (x : ℂ)‖ = anglePeriod * |x| := by
  norm_num

include F F' ξ in
/-- `N(ξ) = -4π²|ξ|² F(ξ) - 2πi ∑ᵢ ⟨vᵢ, ξ⟩ F'ᵢ(ξ)`. -/
def symN : ℂ :=
  -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * F ξ + ∑ i, (-(anglePeriod * Complex.I) * cdir i ξ) * F' i ξ

include E F F' ξ in
/-- `S(ξ) = -E F(ξ) - 2πi ∑ᵢ ⟨vᵢ, ξ⟩ F'ᵢ(ξ)`. -/
def symS : ℂ :=
  -(E : ℂ) * F ξ + ∑ i, (-(anglePeriod * Complex.I) * cdir i ξ) * F' i ξ

include E ξ in
/-- The symbol `E - 4π²|ξ|²` of `Δ + E`. -/
def symD : ℂ := ((E - 4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)

lemma symS_eq :
    symS E F F' ξ = symN F F' ξ - symD E ξ * F ξ := by
  simp [symS, symN, symD] <;> ring

lemma norm_symD : ‖symD E ξ‖ = |E - 4 * π ^ 2 * ‖ξ‖ ^ 2| := by
  rw [symD, Complex.norm_real, Real.norm_eq_abs]

end

lemma norm_mul_sub_mul_le {a f : ℂ → ℂ} {A B Ka Kf : ℝ} (ξ η : ℂ)
    (ha : ‖a ξ - a η‖ ≤ Ka * ‖ξ - η‖) (hf : ‖f ξ - f η‖ ≤ Kf * ‖ξ - η‖)
    (haη : ‖a η‖ ≤ A) (hfξ : ‖f ξ‖ ≤ B) :
    ‖a ξ * f ξ - a η * f η‖ ≤ (Ka * B + A * Kf) * ‖ξ - η‖ := by
  have e : a ξ * f ξ - a η * f η = (a ξ - a η) * f ξ + a η * (f ξ - f η) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1  :=
    mul_le_mul ha hfξ (norm_nonneg _) (le_trans (norm_nonneg _) ha)
  have h2  :=
    mul_le_mul haη hf (norm_nonneg _) (le_trans (norm_nonneg _) haη)
  linarith

/-- `N` is Lipschitz on balls. -/
lemma symN_lipschitz {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} {B K R : ℝ}
    (hFb : ∀ ξ, ‖F ξ‖ ≤ B) (hF'b : ∀ i ξ, ‖F' i ξ‖ ≤ B)
    (hFl : ∀ ξ η, ‖F ξ - F η‖ ≤ K * ‖ξ - η‖) (hF'l : ∀ i ξ η, ‖F' i ξ - F' i η‖ ≤ K * ‖ξ - η‖)
    {ξ η : ℂ} (hξ : ‖ξ‖ ≤ R) (hη : ‖η‖ ≤ R) :
    ‖symN F F' ξ - symN F F' η‖ ≤
      ((8 * π ^ 2 * R * B + 4 * π ^ 2 * R ^ 2 * K) + 2 * (anglePeriod * B + anglePeriod * R * K)) *
        ‖ξ - η‖ := by
  set a : ℂ → ℂ := fun ζ => -((4 * π ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ)
  set b : Fin 2 → ℂ → ℂ := fun i ζ => -(anglePeriod * Complex.I) * cdir i ζ
  
  have ha : ‖a ξ - a η‖ ≤ (8 * π ^ 2 * R) * ‖ξ - η‖ := by
    have e : a ξ - a η = ((-(4 * π ^ 2) * ((‖ξ‖ - ‖η‖) * (‖ξ‖ + ‖η‖)) : ℝ) : ℂ) := by
      simp [a] <;> ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * π ^ 2),
      abs_of_nonneg (by positivity : 0 ≤ ‖ξ‖ + ‖η‖)]
    
    have h2 : ‖ξ‖ + ‖η‖ ≤ 2 * R := by linarith
    have h3  :=
      mul_le_mul (abs_norm_sub_norm_le ξ η) h2 (by positivity) (norm_nonneg _)
    nlinarith
  have haη : ‖a η‖ ≤ 4 * π ^ 2 * R ^ 2 := by
    simp only [a]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have  := pow_le_pow_left₀ (norm_nonneg _) hη 2
    nlinarith
  have hb : ∀ i, ‖b i ξ - b i η‖ ≤ anglePeriod * ‖ξ - η‖ := fun i => by
    have e : b i ξ - b i η = -(anglePeriod * Complex.I) * (cdir i (ξ - η) : ℂ) := by
      simp only [b]; rw [← cdir_sub]; push_cast; ring
    rw [e, norm_two_pi_I_mul]
    exact mul_le_mul_of_nonneg_left (abs_cdir_le i _) (by positivity)
  have hbη : ∀ i, ‖b i η‖ ≤ anglePeriod * R := fun i => by
    
    rw [norm_two_pi_I_mul]
    exact mul_le_mul_of_nonneg_left ((abs_cdir_le i _).trans hη) (by positivity)
  have e : symN F F' ξ - symN F F' η = (a ξ * F ξ - a η * F η) +
      ((b 0 ξ * F' 0 ξ - b 0 η * F' 0 η) + (b 1 ξ * F' 1 ξ - b 1 η * F' 1 η)) := by
    simp only [symN, Fin.sum_univ_two, a, b]; ring
  rw [e]
  have t1 := norm_mul_sub_mul_le ξ η ha (hFl ξ η) haη (hFb ξ)
  have t2 := norm_mul_sub_mul_le ξ η (hb 0) (hF'l 0 ξ η) (hbη 0) (hF'b 0 ξ)
  have t3 := norm_mul_sub_mul_le ξ η (hb 1) (hF'l 1 ξ η) (hbη 1) (hF'b 1 ξ)
  refine (norm_add_le _ _).trans ((add_le_add t1 (norm_add_le _ _)).trans ?_)
  linarith

lemma exists_sphere_near {k : ℝ} (hk : 0 < k) (ξ : ℂ) :
    ∃ ξ₀ : ℂ, ‖ξ₀‖ = k ∧ ‖ξ - ξ₀‖ = |‖ξ‖ - k| := by
  by_cases h : ξ = 0
  · refine ⟨k, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
    · simp [h]
  · have hn  := norm_ne_zero_iff.mpr h
    have hn' : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hn
    refine ⟨((k / ‖ξ‖ : ℝ) : ℂ) * ξ, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hk, abs_norm,
        div_mul_cancel₀ _ hn]
    · have e : ξ - ((k / ‖ξ‖ : ℝ) : ℂ) * ξ = (((‖ξ‖ - k) / ‖ξ‖ : ℝ) : ℂ) * ξ := by
        push_cast; field_simp
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm,
        div_mul_cancel₀ _ hn]

/-- Near the circle, `N / (E - 4π²|ξ|²)` is bounded. -/
lemma norm_symN_div_symD_le {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} {B K k E : ℝ} (hk0 : 0 < k)
    (hk : 4 * π ^ 2 * k ^ 2 = E) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hFb : ∀ ξ, ‖F ξ‖ ≤ B) (hF'b : ∀ i ξ, ‖F' i ξ‖ ≤ B)
    (hFl : ∀ ξ η, ‖F ξ - F η‖ ≤ K * ‖ξ - η‖) (hF'l : ∀ i ξ η, ‖F' i ξ - F' i η‖ ≤ K * ‖ξ - η‖)
    (hN : ∀ ξ, ‖ξ‖ = k → symN F F' ξ = 0) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 2 * k) :
    ‖symN F F' ξ / symD E ξ‖ ≤
      ((8 * π ^ 2 * (2 * k) * B + 4 * π ^ 2 * (2 * k) ^ 2 * K) +
        2 * (anglePeriod * B + anglePeriod * (2 * k) * K)) / (4 * π ^ 2 * k) := by
  set L := (8 * π ^ 2 * (2 * k) * B + 4 * π ^ 2 * (2 * k) ^ 2 * K) +
        2 * (anglePeriod * B + anglePeriod * (2 * k) * K)
  obtain ⟨ξ₀, h0, hd⟩ := exists_sphere_near hk0 ξ
  have hL := symN_lipschitz (R := 2 * k) hFb hF'b hFl hF'l hξ (by rw [h0]; linarith)
  rw [hN ξ₀ h0, sub_zero, hd] at hL
  have hD : 4 * π ^ 2 * k * |‖ξ‖ - k| ≤ ‖symD E ξ‖ := by
    rw [norm_symD, ← hk]
    have e : 4 * π ^ 2 * k ^ 2 - 4 * π ^ 2 * ‖ξ‖ ^ 2 = 4 * π ^ 2 * ((k - ‖ξ‖) * (k + ‖ξ‖)) := by
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π ^ 2), abs_mul,
      abs_of_pos (by positivity : 0 < k + ‖ξ‖), abs_sub_comm k ‖ξ‖]
    have : |‖ξ‖ - k| * k ≤ |‖ξ‖ - k| * (k + ‖ξ‖) :=
      (by bound)
    have h2 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 * π ^ 2)
    linarith
  rw [norm_div]
  refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
  calc _ ≤ L * |‖ξ‖ - k| := hL
    _ = L / (4 * π ^ 2 * k) * (4 * π ^ 2 * k * |‖ξ‖ - k|) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)

/-- Away from the circle, `|S / (E - 4π²|ξ|²)| (1 + |ξ|) ≲ |F| + ∑ |F'ᵢ|`. -/
lemma norm_symS_div_symD_far {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} {k E : ℝ} (hk0 : 0 < k)
    (hk : 4 * π ^ 2 * k ^ 2 = E) {ξ : ℂ} (hξ : 2 * k < ‖ξ‖) :
    ‖symS E F F' ξ / symD E ξ‖ * (1 + ‖ξ‖) ≤
      (E / (4 * k ^ 2) + E / (2 * k) + π / k + anglePeriod) / (3 * π ^ 2) *
        (‖F ξ‖ + ∑ i, ‖F' i ξ‖) := by
  set r := ‖ξ‖ with hr
  set s := ‖F ξ‖
  set t := ‖F' 0 ξ‖ + ‖F' 1 ξ‖
  have hE : 0 < E := by rw [← hk]; positivity
  have hr0 : 0 < r := by linarith
  have hS : ‖symS E F F' ξ‖ ≤ E * s + anglePeriod * r * t := by
    simp only [symS, Fin.sum_univ_two]
    refine (norm_add_le _ _).trans ((add_le_add_right (norm_add_le _ _) _).trans ?_)
    rw [norm_mul (-(E : ℂ)), norm_mul _ (F' 0 ξ), norm_mul _ (F' 1 ξ), norm_neg,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hE, norm_two_pi_I_mul, norm_two_pi_I_mul]
    have h0 := abs_cdir_le 0 ξ
    have h1 := abs_cdir_le 1 ξ
    have := norm_nonneg (F' 0 ξ)
    have := norm_nonneg (F' 1 ξ)
    have : anglePeriod * |cdir 0 ξ| * ‖F' 0 ξ‖ ≤ anglePeriod * r * ‖F' 0 ξ‖ := by gcongr
    have : anglePeriod * |cdir 1 ξ| * ‖F' 1 ξ‖ ≤ anglePeriod * r * ‖F' 1 ξ‖ := by gcongr
    linarith
  have hD : 3 * π ^ 2 * r ^ 2 ≤ ‖symD E ξ‖ := by
    rw [norm_symD, ← hk]
    have : 4 * k ^ 2 ≤ r ^ 2 := by nlinarith
    have h2 : 4 * π ^ 2 * k ^ 2 ≤ π ^ 2 * r ^ 2 := by nlinarith [Real.pi_pos]
    grind [le_trans]
  
  
  rw [(Fin.sum_univ_two _), norm_div, div_mul_eq_mul_div, div_le_iff₀ (lt_of_lt_of_le (by positivity) hD)]
  have h1 : 1 ≤ r ^ 2 / (4 * k ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h2 : r ≤ r ^ 2 / (2 * k) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hs : 0 ≤ s := norm_nonneg _
  have ht : 0 ≤ t := by positivity
  have key : (E * s + anglePeriod * r * t) * (1 + r) ≤
      ((E / (4 * k ^ 2) + E / (2 * k)) * s + (π / k + anglePeriod) * t) * r ^ 2 := by
    have a1 : E * s * 1 ≤ E * s * (r ^ 2 / (4 * k ^ 2)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have a2 : E * s * r ≤ E * s * (r ^ 2 / (2 * k)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have a3 : anglePeriod * t * r ≤ anglePeriod * t * (r ^ 2 / (2 * k)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e1 : E * s * (r ^ 2 / (4 * k ^ 2)) + E * s * (r ^ 2 / (2 * k)) +
        anglePeriod * t * (r ^ 2 / (2 * k)) + anglePeriod * t * r ^ 2 =
        ((E / (4 * k ^ 2) + E / (2 * k)) * s + (π / k + anglePeriod) * t) * r ^ 2 := by
      field_simp; ring
    nlinarith
  
  calc _ ≤ (E * s + anglePeriod * r * t) * (1 + r) :=
        (by bound)
    _ ≤ _ := key
    _ ≤ (E / (4 * k ^ 2) + E / (2 * k) + π / k + anglePeriod) * (s + t) * r ^ 2 := by
        gcongr
        nlinarith [Real.pi_pos, show 0 ≤ E / (4 * k ^ 2) + E / (2 * k) by positivity,
          show 0 ≤ π / k + anglePeriod by positivity]
    _ = (E / (4 * k ^ 2) + E / (2 * k) + π / k + anglePeriod) / (3 * π ^ 2) * (s + t) *
          (3 * π ^ 2 * r ^ 2) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)

/-- The global bound `|ŵ(ξ)| (1 + |ξ|) ≤ M (1_{|ξ| ≤ 2k} + |F(ξ)| + ∑ |F'ᵢ(ξ)|)`. -/
lemma symS_div_bound {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} {B K k E : ℝ} (hk0 : 0 < k)
    (hk : 4 * π ^ 2 * k ^ 2 = E) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hFb : ∀ ξ, ‖F ξ‖ ≤ B) (hF'b : ∀ i ξ, ‖F' i ξ‖ ≤ B)
    (hFl : ∀ ξ η, ‖F ξ - F η‖ ≤ K * ‖ξ - η‖) (hF'l : ∀ i ξ η, ‖F' i ξ - F' i η‖ ≤ K * ‖ξ - η‖)
    (hN : ∀ ξ, ‖ξ‖ = k → symN F F' ξ = 0) :
    ∃ M : ℝ, ∀ ξ, ‖symS E F F' ξ / symD E ξ‖ * (1 + ‖ξ‖) ≤
      M * ((Metric.closedBall (0 : ℂ) (2 * k)).indicator (fun _ => (1 : ℝ)) ξ + ‖F ξ‖ +
        ∑ i, ‖F' i ξ‖) := by
  set L := (8 * π ^ 2 * (2 * k) * B + 4 * π ^ 2 * (2 * k) ^ 2 * K) +
        2 * (anglePeriod * B + anglePeriod * (2 * k) * K)
  set C1 := L / (4 * π ^ 2 * k)
  set M2 := (E / (4 * k ^ 2) + E / (2 * k) + π / k + anglePeriod) / (3 * π ^ 2)
  have hE : 0 < E := by rw [← hk]; positivity
  have hC1 : 0 ≤ C1 := by positivity
  have hM2 : 0 ≤ M2 := by positivity
  refine ⟨(1 + 2 * k) * C1 + (1 + 2 * k) + M2, fun ξ => ?_⟩
  have hs : 0 ≤ ‖F ξ‖ := norm_nonneg _
  have ht : 0 ≤ ∑ i, ‖F' i ξ‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  by_cases hξ : ‖ξ‖ ≤ 2 * k
  · 
    rw [(indicator_of_mem (by simp [*]) _)]
    have hw : ‖symS E F F' ξ / symD E ξ‖ ≤ C1 + ‖F ξ‖ := by
      by_cases hD : symD E ξ = 0
      · rw [hD, div_zero, norm_zero]; positivity
      · rw [symS_eq, sub_div, mul_div_cancel_left₀ _ hD]
        have := norm_symN_div_symD_le hk0 hk hB hK hFb hF'b hFl hF'l hN hξ
        exact (norm_sub_le _ _).trans (by linarith)
    calc _ ≤ (C1 + ‖F ξ‖) * (1 + 2 * k) :=
          mul_le_mul hw (by linarith) (by positivity) (by positivity)
      _ ≤ _ := by
        have ha : 0 ≤ 1 + 2 * k := by linarith
        have h1 := mul_nonneg (mul_nonneg ha hC1) hs
        
        have h3 := mul_nonneg ha ht
        
        nlinarith
  · push_neg at hξ
    
    rw [(indicator_of_notMem (by simp [*]) _), zero_add]
    refine (norm_symS_div_symD_far hk0 hk hξ).trans ?_
    have : 0 ≤ (1 + 2 * k) * C1 + (1 + 2 * k) := by positivity
    nlinarith

/-! ### Fourier transforms of the data -/

lemma integrable_fourierInv_test {φ : ℂ → ℂ} (hφ : TestFunction univ φ) :
    Integrable (𝓕⁻ φ) := by
  have : 𝓕⁻ φ = ((𝓕⁻ hφ.schwartz : SchwartzMap ℂ ℂ) : ℂ → ℂ) := by
    rw [SchwartzMap.fourierInv_coe]; rfl
  rw [this]; exact (𝓕⁻ hφ.schwartz).integrable

lemma integrable_conj_ePlane_mul {f : ℂ → ℂ} (hf : Integrable f) (ξ : ℂ) :
    Integrable fun x => conj (ePlane ξ x) * f x :=
  hf.bdd_mul (c := 1) ((Complex.continuous_conj.comp (continuous_ePlane_prod.comp
    (continuous_id.prodMk continuous_const))).aestronglyMeasurable)
    (Eventually.of_forall fun x => by rw [Complex.norm_conj, norm_ePlane])

lemma integrable_ePlane_mul {f : ℂ → ℂ} (hf : Integrable f) (ξ : ℂ) :
    Integrable fun x => ePlane ξ x * f x :=
  hf.bdd_mul (c := 1) ((continuous_ePlane_prod.comp
    (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun x => (norm_ePlane ξ x).le)

lemma fourierInv_helm {φ : ℂ → ℂ} (hφ : TestFunction univ φ) (E : ℝ) (ξ : ℂ) :
    𝓕⁻ (fun z => lap φ z + E * φ z) ξ = symD E ξ * 𝓕⁻ φ ξ := by
  have hi1 : Integrable (lap φ) :=
    hφ.lap.1.continuous.integrable_of_hasCompactSupport hφ.lap.2.1
  have hi2 : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have e : 𝓕⁻ (fun z => lap φ z + E * φ z) ξ = 𝓕⁻ (lap φ) ξ + E * 𝓕⁻ φ ξ := by
    rw [fourierInv_eq_ePlane, fourierInv_eq_ePlane, fourierInv_eq_ePlane, ← integral_const_mul,
      ← integral_add (integrable_conj_ePlane_mul hi1 ξ)
        ((integrable_conj_ePlane_mul hi2 ξ).const_mul _)]
    grind
  rw [e, fourierInv_lap hφ, symD]; push_cast; ring

/-- `T(e_ξ) = N(ξ)` with `F = Ĝ`, `F'ᵢ = Ĝ'ᵢ`. -/
lemma integral_helm_ePlane {G : ℂ → ℂ} {G' : Fin 2 → ℂ → ℂ} (hG : Integrable G)
    (hG' : ∀ i, Integrable (G' i)) (ξ : ℂ) :
    ∫ z, (G z * lap (ePlane ξ) z + ∑ i : Fin 2, G' i z * dirD (ePlane ξ) (coordDir i) z) =
      symN (𝓕 G) (fun i => 𝓕 (G' i)) ξ := by
  have e : ∀ z, G z * lap (ePlane ξ) z + ∑ i : Fin 2, G' i z * dirD (ePlane ξ) (coordDir i) z =
      -((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * (ePlane ξ z * G z) +
        ((-(anglePeriod * Complex.I) * cdir 0 ξ) * (ePlane ξ z * G' 0 z) +
          (-(anglePeriod * Complex.I) * cdir 1 ξ) * (ePlane ξ z * G' 1 z)) := by
    intro z
    simp [lap_ePlane, Fin.sum_univ_two, dirD_ePlane, cdir] <;> ring
  simp_rw [e]
  have h0 : Integrable fun z => (-(anglePeriod * Complex.I) * cdir 0 ξ) * (ePlane ξ z * G' 0 z) :=
    (integrable_ePlane_mul (hG' 0) ξ).const_mul _
  have h1 : Integrable fun z => (-(anglePeriod * Complex.I) * cdir 1 ξ) * (ePlane ξ z * G' 1 z) :=
    (integrable_ePlane_mul (hG' 1) ξ).const_mul _
  have h01 : Integrable fun z => (-(anglePeriod * Complex.I) * cdir 0 ξ) * (ePlane ξ z * G' 0 z) +
      (-(anglePeriod * Complex.I) * cdir 1 ξ) * (ePlane ξ z * G' 1 z) := h0.add h1
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

lemma continuous_symS {E : ℝ} {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} (hF : Continuous F)
    (hF' : ∀ i, Continuous (F' i)) : Continuous (symS E F F') := by
  
  refine (continuous_const.mul hF).add (continuous_finset_sum _ fun i _ => ?_)
  exact (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_cdir i))).mul (hF' i)

lemma continuous_symD (E : ℝ) : Continuous (symD E) := by
  unfold symD; fun_prop

/-- On the energy circle `symD = 0` forces `symS = 0`, so `(S / D) · D = S` everywhere. -/
lemma symS_div_mul_symD {F : ℂ → ℂ} {F' : Fin 2 → ℂ → ℂ} {k E : ℝ} (hk0 : 0 < k)
    (hk : 4 * π ^ 2 * k ^ 2 = E) (hN : ∀ ξ, ‖ξ‖ = k → symN F F' ξ = 0) (ξ : ℂ) :
    symS E F F' ξ / symD E ξ * symD E ξ = symS E F F' ξ := by
  by_cases hD : symD E ξ = 0
  · have h0 : E - 4 * π ^ 2 * ‖ξ‖ ^ 2 = 0 := by
      have := hD
      rw [symD, Complex.ofReal_eq_zero] at this
      exact this
    have hsq : ‖ξ‖ ^ 2 = k ^ 2 := by
      have : (4 * π ^ 2) * (‖ξ‖ ^ 2 - k ^ 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · aesop
      · linarith
    
    rw [symS_eq, hN ξ (by
      have := (sq_eq_sq₀ (norm_nonneg ξ) hk0.le).mp hsq
      exact this), hD]; simp
  · exact div_mul_cancel₀ _ hD

/-- Existence of the `L²` solution of `(Δ + E) u = T` when `T̂` vanishes on the energy circle. -/
theorem exists_helmholtz_solution {E : ℝ} (hE : 0 < E) {G : ℂ → ℂ} {G' : Fin 2 → ℂ → ℂ}
    (hG : MemLp G 2 volume) (hGc : HasCompactSupport G) (hG' : ∀ i, MemLp (G' i) 2 volume)
    (hG'c : ∀ i, HasCompactSupport (G' i))
    (hvan : ∀ ξ : ℂ, 4 * π ^ 2 * ‖ξ‖ ^ 2 = E →
      ∫ z, (G z * lap (ePlane ξ) z + ∑ i : Fin 2, G' i z * dirD (ePlane ξ) (coordDir i) z) = 0) :
    ∃ (w : ℂ → ℂ) (gw : Fin 2 → ℂ → ℂ), MemLp w 2 volume ∧ (∀ i, MemLp (gw i) 2 volume) ∧
      IsWeakGradOn univ w gw ∧
      ∀ φ : ℂ → ℂ, TestFunction univ φ →
        ∫ z, (G z + w z) * (lap φ z + E * φ z) =
          ∫ z, (G z * lap φ z + ∑ i : Fin 2, G' i z * dirD φ (coordDir i) z) := by
  -- the data and their Fourier transforms
  have hG1  := integrable_of_memLp_two_hasCompactSupport hG hGc
  have hG'1  := fun i =>
    integrable_of_memLp_two_hasCompactSupport (hG' i) (hG'c i)
  have hGm := integrable_norm_mul_of_hasCompactSupport hG1 hGc
  have hG'm := fun i => integrable_norm_mul_of_hasCompactSupport (hG'1 i) (hG'c i)
  set F : ℂ → ℂ := 𝓕 G with hFdef
  set F' : Fin 2 → ℂ → ℂ := fun i => 𝓕 (G' i) with hF'def
  have hFc  := continuous_fourier_of_moment hG1 hGm
  have hF'c  := fun i => continuous_fourier_of_moment (hG'1 i) (hG'm i)
  
  
  set B := (∫ x, ‖G x‖) + ∑ i, ∫ x, ‖G' i x‖ with hBdef
  set K := anglePeriod * ((∫ x, ‖x‖ * ‖G x‖) + ∑ i, ∫ x, ‖x‖ * ‖G' i x‖) with hKdef
  have hI0 : 0 ≤ ∫ x, ‖G x‖ := integral_nonneg fun x => norm_nonneg _
  have hI'0 : ∀ i, 0 ≤ ∫ x, ‖G' i x‖ := fun i => (by positivity)
  have hJ0 : 0 ≤ ∫ x, ‖x‖ * ‖G x‖ := integral_nonneg fun x => by positivity
  have hJ'0 : ∀ i, 0 ≤ ∫ x, ‖x‖ * ‖G' i x‖ := fun i => (by positivity)
  have hS0 : 0 ≤ ∑ i, ∫ x, ‖G' i x‖ := Finset.sum_nonneg fun i _ => hI'0 i
  have hT0 : 0 ≤ ∑ i, ∫ x, ‖x‖ * ‖G' i x‖ := Finset.sum_nonneg fun i _ => hJ'0 i
  
  
  have hFb : ∀ ξ, ‖F ξ‖ ≤ B := fun ξ => (norm_fourier_le G ξ).trans (by linarith)
  have hF'b : ∀ i ξ, ‖F' i ξ‖ ≤ B := fun i ξ => by
    refine (norm_fourier_le (G' i) ξ).trans ?_
    have := Finset.single_le_sum  (fun i _ => hI'0 i)
      (Finset.mem_univ i)
    linarith
  have hFl : ∀ ξ η, ‖F ξ - F η‖ ≤ K * ‖ξ - η‖ := fun ξ η => by
    refine (norm_fourier_sub_le hG1 hGm ξ η).trans ?_
    bound
  have hF'l : ∀ i ξ η, ‖F' i ξ - F' i η‖ ≤ K * ‖ξ - η‖ := fun i ξ η => by
    refine (norm_fourier_sub_le (hG'1 i) (hG'm i) ξ η).trans ?_
    have := Finset.single_le_sum  (fun i _ => hJ'0 i)
      (Finset.mem_univ i)
    have : anglePeriod * (∫ x, ‖x‖ * ‖G' i x‖) ≤ K := by nlinarith [Real.pi_pos]
    gcongr
  -- the radius of the energy circle
  set k := Real.sqrt E / anglePeriod with hkdef
  have hk0 : 0 < k := by positivity
  have hk : 4 * π ^ 2 * k ^ 2 = E := by
    grind
  have hN : ∀ ξ, ‖ξ‖ = k → symN F F' ξ = 0 := fun ξ hξ => by
    rw [← integral_helm_ePlane hG1 hG'1 ξ]
    grind
  obtain ⟨M, hM⟩ := symS_div_bound hk0 hk (by positivity) (by positivity) hFb hF'b hFl hF'l hN
  -- the Fourier transform of the solution and of its gradient
  set wh : ℂ → ℂ := fun ξ => symS E F F' ξ / symD E ξ with hwhdef
  set gwh : Fin 2 → ℂ → ℂ := fun i ξ => (anglePeriod * Complex.I * cdir i ξ) * wh ξ with hgwhdef
  set D : ℂ → ℝ := fun ξ => M * ((Metric.closedBall 0 (2 * k)).indicator
    (fun _ => 1) ξ + ‖F ξ‖ + ∑ i, ‖F' i ξ‖) with hDdef
  have hD2 : MemLp D 2 volume := by
    refine MemLp.const_mul ?_ M
    refine ((memLp_indicator_const 2 Metric.isClosed_closedBall.measurableSet (1 : ℝ)
      (Or.inr measure_closedBall_lt_top.ne)).add (memLp_fourier hG hG1 hGm).norm).add ?_
    exact memLp_finset_sum _ fun i _ => ((fun i => memLp_fourier (hG' i) (hG'1 i) (hG'm i)) i).norm
  have hwhm : AEStronglyMeasurable wh volume :=
    ((continuous_symS hFc hF'c).measurable.div (continuous_symD E).measurable).aestronglyMeasurable
  have hwhD  := hM
  have hwh2 : MemLp wh 2 volume := by
    refine hD2.of_le hwhm (Eventually.of_forall fun ξ => ?_)
    refine le_trans ?_ (Real.le_norm_self _)
    refine le_trans ?_ (hwhD ξ)
    have := norm_nonneg (wh ξ)
    nlinarith [norm_nonneg ξ]
  have hgwh2 : ∀ i, MemLp (gwh i) 2 volume := fun i => by
    refine (hD2.const_mul anglePeriod).of_le ?_ (Eventually.of_forall fun ξ => ?_)
    · exact (((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_cdir i))).aestronglyMeasurable).mul hwhm)
    · refine le_trans ?_ (Real.le_norm_self _)
      
      have e : (anglePeriod * Complex.I * (cdir i ξ : ℂ)) = -(-(anglePeriod * Complex.I) * (cdir i ξ : ℂ)) := by
        ring
      rw [norm_mul, e, norm_neg, norm_two_pi_I_mul]
      have h1 := abs_cdir_le i ξ
      have h2 := hwhD ξ
      have h3 := norm_nonneg (wh ξ)
      have h4 : |cdir i ξ| * ‖wh ξ‖ ≤ ‖wh ξ‖ * (1 + ‖ξ‖) := by nlinarith [norm_nonneg ξ]
      nlinarith [Real.pi_pos]
  -- the solution
  set W : Lp ℂ 2 volume := 𝓕⁻ (hwh2.toLp wh) with hWdef
  set GW : Fin 2 → Lp ℂ 2 volume := fun i => 𝓕⁻ ((hgwh2 i).toLp (gwh i))
    with hGWdef
  have hpair : ∀ (A : ℂ → ℂ) (hA : MemLp A 2 volume) {ψ : ℂ → ℂ}, TestFunction univ ψ →
      ∫ x, (𝓕⁻ (hA.toLp A) : Lp ℂ 2 (volume : Measure ℂ)) x * ψ x = ∫ ξ, A ξ * 𝓕⁻ ψ ξ :=
    fun A hA ψ hψ => by
      rw [integral_fourierInv_Lp_mul _ hψ]
      refine integral_congr_ae ?_
      filter_upwards [hA.coeFn_toLp] with ξ hξ
      rw [hξ]
  refine ⟨W, fun i => GW i, Lp.memLp _, fun i => Lp.memLp _, ?_, ?_⟩
  · -- weak gradient
    intro φ hφ i
    have h1 : ∫ z, W z * fderiv ℝ φ z (coordDir i) =
        ∫ ξ, wh ξ * 𝓕⁻ (dirD φ (coordDir i)) ξ := hpair wh hwh2 (hφ.dirD _)
    
    rw [h1, (hpair (gwh i) (hgwh2 i) hφ), ← integral_neg]
    congr 1
    funext ξ
    rw [fourierInv_dirD hφ]
    simp only [hgwhdef, cdir]
    ring
  · -- the Helmholtz equation
    intro φ hφ
    set H : ℂ → ℂ := fun z => lap φ z + E * φ z with hHdef
    have hH  := hφ.helm E
    have hFH  :=
      (integrable_fourierInv_test hH).bdd_mul (c := B) hFc.aestronglyMeasurable
        (Eventually.of_forall hFb)
    have hwH : Integrable fun ξ => wh ξ * 𝓕⁻ H ξ :=
      hwh2.integrable_mul (memLp_fourierInv_test hH)
    
    have hF'd : ∀ i, Integrable fun ξ => F' i ξ * 𝓕⁻ (dirD φ (coordDir i)) ξ := fun i =>
      (integrable_fourierInv_test (hφ.dirD _)).bdd_mul (c := B) (by fun_prop)
        (Eventually.of_forall (hF'b i))
    have hGH  := integrable_mul_test hG hH
    have hWH : Integrable fun z => W z * H z := integrable_mul_test (Lp.memLp _) hH
    
    have hG'd : ∀ i, Integrable fun z => G' i z * dirD φ (coordDir i) z := fun i =>
      integrable_mul_test (hG' i) (hφ.dirD _)
    have eL : ∫ z, (G z + W z) * H z = ∫ ξ, (F ξ * 𝓕⁻ H ξ + wh ξ * 𝓕⁻ H ξ) := by
      simp_rw [add_mul]
      rw [integral_add hGH hWH, integral_add hFH hwH, hpair wh hwh2 hH,
        ← integral_fourier_mul_fourierInv hG1 hH]
    have eR : ∫ z, (G z * lap φ z + ∑ i : Fin 2, G' i z * dirD φ (coordDir i) z) =
        ∫ ξ, (F ξ * 𝓕⁻ (lap φ) ξ + (F' 0 ξ * 𝓕⁻ (dirD φ (coordDir 0)) ξ +
          F' 1 ξ * 𝓕⁻ (dirD φ (coordDir 1)) ξ)) := by
      simp only [Fin.sum_univ_two]
      have hs1 : Integrable fun z => G' 0 z * dirD φ (coordDir 0) z +
          G' 1 z * dirD φ (coordDir 1) z := (hG'd 0).add (hG'd 1)
      have hs2 : Integrable fun ξ => F' 0 ξ * 𝓕⁻ (dirD φ (coordDir 0)) ξ +
          F' 1 ξ * 𝓕⁻ (dirD φ (coordDir 1)) ξ := (hF'd 0).add (hF'd 1)
      rw [integral_add (integrable_mul_test hG hφ.lap) hs1, integral_add (hG'd 0) (hG'd 1),
        integral_add ((integrable_fourierInv_test hφ.lap).bdd_mul (c := B) hFc.aestronglyMeasurable
          (Eventually.of_forall hFb)) hs2, integral_add (hF'd 0) (hF'd 1),
        ← integral_fourier_mul_fourierInv hG1 hφ.lap,
        ← integral_fourier_mul_fourierInv (hG'1 0) (hφ.dirD _),
        ← integral_fourier_mul_fourierInv (hG'1 1) (hφ.dirD _)]
    rw [eL, eR]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    have hwD := symS_div_mul_symD hk0 hk hN ξ
    have e1 := fourierInv_helm hφ E ξ
    simp only [hHdef] at e1 ⊢
    rw [e1, fourierInv_lap hφ, fourierInv_dirD hφ, fourierInv_dirD hφ]
    have e2 : wh ξ * (symD E ξ * 𝓕⁻ φ ξ) = symS E F F' ξ * 𝓕⁻ φ ξ := by
      rw [← mul_assoc, hwhdef]; simp only; rw [hwD]
    rw [e2, symS_eq]
    simp only [symN, symD, Fin.sum_univ_two, cdir]
    push_cast
    ring

end PolyaNeumann
