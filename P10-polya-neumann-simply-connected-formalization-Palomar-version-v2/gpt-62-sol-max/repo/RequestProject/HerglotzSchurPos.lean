module

public import RequestProject.TraceIneq
public import RequestProject.HerglotzModes
public import RequestProject.HerglotzSchurBound

/-!
# Lemma 8.5: nonnegativity of the Schur complement on Herglotz data

Fix a disc `B(z₁, r) ⊆ Ω`. For small `E = k² > 0` and every density `a` whose Herglotz wave has
zero mean over `Ω` and whose negative coefficients `F_{-j}` (`j ≥ 1`) vanish at `z₁`, the Schur
complement `C(v_a)` of the Herglotz vector is nonnegative (`herglotz_imSchur_nonneg`).

The principal part is `2k² ∫_Ω (|F₁|² + 2|F₋₁|² − 3|F₀|²) − 2k² Im ∫ conj(q) Q`, the remainder is
`O(E (∫|G − c|)²)` (`imSchur_herglotzVec_sub_principal_le`). The smallness of `F₀`, `F₋₁`, `F₋₂`
(`herglotz_modes_small`) and the trace inequality (`trace_sq_le`) bound everything except
`2k² ∫ |F₁|²` by `O(k⁴) ∫ |F₁|²`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section
namespace PolyaNeumann
variable {Ω : Set ℂ} {γ : ℝ → ℂ} {a : ℝ → ℂ}

/-- Cauchy–Schwarz on `[0, 2π]`: `(∫ |g|)² ≤ 2π ∫ |g|²`. -/
lemma sq_intervalIntegral_norm_le {g : ℝ → ℂ} (hg : Continuous g) :
    (∫ θ in (0:ℝ)..(2 * π), ‖g θ‖) ^ 2 ≤ 2 * π * ∫ θ in (0:ℝ)..(2 * π), ‖g θ‖ ^ 2 := by
  have hp : (0 : ℝ) ≤ 2 * π := by positivity
  let s := Ioc (0 : ℝ) (2 * π)
  have hvol : volume s = ENNReal.ofReal (2 * π) := by simp [s]
  haveI := isFiniteMeasure_restrict.mpr (hvol.trans_ne ENNReal.ofReal_ne_top)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * π)) hg.continuousOn
  have hm : MemLp g 2 (volume.restrict s) := MemLp.of_bound hg.aestronglyMeasurable B (by
    filter_upwards [ae_restrict_mem (s := s) measurableSet_Ioc] with x hx
    exact hB x (Ioc_subset_Icc_self hx))
  simp only [intervalIntegral.integral_of_le hp]
  simpa only [Measure.real, Measure.restrict_apply_univ, hvol, ENNReal.toReal_ofReal hp] using
    sq_integral_norm_le_of_memLp hm


section

variable (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) {K : NNReal} (hK : LipschitzWith K γ)
include ha k K hK

/-- `∫ |q| ≤ K ∫ |F₋₁ ∘ γ|`. -/
lemma integral_norm_herglotzQd_le  :
    ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖ ≤
      K * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a (-1) (γ θ)‖ := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by positivity)
    ((intervalIntegrable_herglotzQd ha k hK _ _).norm)
    ((continuous_const.mul ((continuous_herglotzCoeff ha k (-1)).comp
      hK.continuous).norm).intervalIntegrable _ _) fun θ _ => ?_
  rw [herglotzQd, norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hK) (norm_nonneg _)

lemma norm_herglotzQ_le  {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖herglotzQ k a γ θ‖ ≤ ∫ t in (0:ℝ)..(2 * π), ‖herglotzQd k a γ t‖ := by
  rw [herglotzQ]
  refine (intervalIntegral.norm_integral_le_integral_norm hθ.1).trans ?_
  refine intervalIntegral.integral_mono_interval le_rfl hθ.1 hθ.2
    (Eventually.of_forall fun t => norm_nonneg _) (intervalIntegrable_herglotzQd ha k hK _ _).norm

/-- `|∫ conj(q) Q| ≤ (∫ |q|)²`. -/
lemma norm_integral_conj_herglotzQd_mul_le  :
    ‖∫ θ in (0:ℝ)..(2 * π), conj (herglotzQd k a γ θ) * herglotzQ k a γ θ‖ ≤
      (∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖) ^ 2 := by
  rw [pow_two, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.norm_integral_le_of_norm_le Real.two_pi_pos.le
    (.of_forall fun θ hθ => ?_) ((intervalIntegrable_herglotzQd ha k hK _ _).norm.mul_const _)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (norm_herglotzQ_le ha k hK (Ioc_subset_Icc_self hθ))
    (norm_nonneg _)

/-- With `c = i h_a(0)`: `∫ |G - c| ≤ ∫ |h_a| + 2π |k| ∫ |q|`. -/
lemma integral_norm_primitive_sub_le  :
    ∫ θ in (0:ℝ)..(2 * π), ‖(∫ s in (0:ℝ)..θ, herglotzConormal k a γ s) -
        Complex.I * herglotzCoeff k a 0 (γ 0)‖ ≤
      (∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a 0 (γ θ)‖) +
        2 * π * |k| * ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖ := by
  set S := ∫ θ in (0:ℝ)..(2 * π), ‖herglotzQd k a γ θ‖
  have hGc : Continuous fun θ => ‖(∫ s in (0:ℝ)..θ, herglotzConormal k a γ s) -
      Complex.I * herglotzCoeff k a 0 (γ 0)‖ :=
    ((intervalIntegral.continuous_primitive
      (intervalIntegrable_herglotzConormal ha k hK) 0).sub continuous_const).norm
  have hh : Continuous fun θ => ‖herglotzCoeff k a 0 (γ θ)‖ :=
    ((continuous_herglotzCoeff ha k 0).comp hK.continuous).norm
  calc _ ≤ ∫ θ in (0:ℝ)..(2 * π), (‖herglotzCoeff k a 0 (γ θ)‖ + |k| * S) := by
        refine intervalIntegral.integral_mono_on (by positivity) (hGc.intervalIntegrable _ _)
          ((hh.add continuous_const).intervalIntegrable _ _) fun θ hθ => ?_
        rw [primitive_herglotzConormal_eq ha k hK θ]
        have he : -Complex.I * (herglotzCoeff k a 0 (γ θ) - herglotzCoeff k a 0 (γ 0)) +
            k * herglotzQ k a γ θ - Complex.I * herglotzCoeff k a 0 (γ 0) =
            -Complex.I * herglotzCoeff k a 0 (γ θ) + k * herglotzQ k a γ θ := by ring
        rw [he]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        simp
        simpa using mul_le_mul_of_nonneg_left (norm_herglotzQ_le ha k hK hθ) (abs_nonneg _)
    _ = _ := by
        rw [intervalIntegral.integral_add (hh.intervalIntegrable _ _) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        ring

end

/-- Trace inequality for a Herglotz coefficient. -/
theorem trace_herglotzCoeff (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, IntervalIntegrable a volume 0 (2 * π) → ∀ (k : ℝ) (m : ℤ),
      ∫ θ in (0:ℝ)..(2 * π), ‖herglotzCoeff k a m (γ θ)‖ ^ 2 ≤
        C * ((∫ z in Ω, ‖herglotzCoeff k a m z‖ ^ 2) +
          k ^ 2 / 2 * ((∫ z in Ω, ‖herglotzCoeff k a (m + 1) z‖ ^ 2) +
            ∫ z in Ω, ‖herglotzCoeff k a (m - 1) z‖ ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := trace_sq_le hb hL hγ
  refine ⟨C, hC0, fun a ha k m => ?_⟩
  obtain ⟨⟨Kf, hKf⟩, hB⟩ := herglotzCoeff_bounded_lipschitz ha k m
  have h := hC _ Kf hKf _ hB
  simp  [gradSq_herglotzCoeff ha] at h
  rwa [integral_const_mul, integral_add (integrable_herglotzCoeff_sq hb ha k _)
    (integrable_herglotzCoeff_sq hb ha k _)] at h

private def schurErrorFactor (C₁ CT CS K : ℝ) : ℝ :=
  let b₀ := CT * (2 * C₁ + 1)
  let b₁ := 2 * π * K ^ 2 * (2 * CT * C₁)
  6 * C₁ + 2 * b₁ + CS * (4 * π * b₀ + 8 * π ^ 2 * b₁) + 1

private lemma intervalIntegral_norm_nonneg (f : ℝ → ℂ) :
    0 ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖f θ‖ :=
  intervalIntegral.integral_nonneg Real.two_pi_pos.le (fun _ _ => norm_nonneg _)

/-- The numerical core of Lemma 8.5. -/
private lemma schur_numeric {E A I0 Im1 Im2 T0 T1 S G C₁ CT CS K : ℝ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hC₁ : 0 ≤ C₁) (hCT : 0 ≤ CT) (hCS : 0 ≤ CS) (hA : 0 ≤ A) (hI0 : 0 ≤ I0) (hIm1 : 0 ≤ Im1)
    (hIm2 : 0 ≤ Im2)
    (hED : E * schurErrorFactor C₁ CT CS K ≤ 1)
    (hm0 : I0 ≤ C₁ * E * A) (hm12 : Im1 + Im2 ≤ C₁ * E ^ 2 * A)
    (hT0 : T0 ≤ CT * (I0 + E / 2 * (A + Im1))) (hT1 : T1 ≤ CT * (Im1 + E / 2 * (I0 + Im2)))
    (hS : S ^ 2 ≤ K ^ 2 * (2 * π * T1)) (hG : G ^ 2 ≤ 2 * (2 * π * T0) + 2 * (4 * π ^ 2 * E * S ^ 2)) :
    0 ≤ 2 * E * A - 6 * E * I0 - 2 * E * S ^ 2 - CS * E * G ^ 2 := by
  let b₀ := CT * (2 * C₁ + 1)
  let b₁ := 2 * π * K ^ 2 * (2 * CT * C₁)
  let b₂ := 4 * π * b₀ + 8 * π ^ 2 * b₁
  have he : E ^ 2 ≤ E := by nlinarith [mul_le_mul_of_nonneg_left hE1 hE.le]
  have hIm : Im1 ≤ C₁ * A := by nlinarith [mul_le_mul_of_nonneg_right (he.trans hE1) (show 0 ≤ C₁ * A by positivity)]
  have hT₀ : T0 ≤ b₀ * E * A := hT0.trans (calc
    _ ≤ CT * ((2 * C₁ + 1) * E * A) := by
      gcongr
      linarith [mul_le_mul_of_nonneg_left hIm hE.le, mul_nonneg hE.le hA,
        show 0 ≤ C₁ * E * A by positivity]
    _ = _ := by dsimp [b₀]; ring)
  have hT₁ : T1 ≤ 2 * CT * C₁ * E ^ 2 * A := hT1.trans (calc
    _ ≤ CT * (2 * C₁ * E ^ 2 * A) := by
      gcongr
      linarith [mul_le_mul_of_nonneg_left hm0 hE.le, mul_le_mul_of_nonneg_right hE1 hIm2]
    _ = _ := by ring)
  have hS₁ : S ^ 2 ≤ b₁ * E * A := hS.trans (calc
    _ ≤ K ^ 2 * (2 * π * (2 * CT * C₁ * E ^ 2 * A)) := by gcongr
    _ = b₁ * E ^ 2 * A := by dsimp [b₁]; ring
    _ ≤ _ := by gcongr)
  have hG₁ : G ^ 2 ≤ b₂ * E * A := hG.trans (calc
    _ ≤ 2 * (2 * π * (b₀ * E * A)) + 2 * (4 * π ^ 2 * 1 * (b₁ * E * A)) := by
      have : 0 ≤ S ^ 2 := sq_nonneg _
      gcongr
    _ = _ := by dsimp [b₂]; ring)
  change E * (6 * C₁ + 2 * b₁ + CS * b₂ + 1) ≤ 1 at hED
  have hD : (6 * C₁ + 2 * b₁ + CS * b₂) * (E * A) ≤ A := by
    linarith [mul_le_mul_of_nonneg_right hED hA, mul_nonneg hE.le hA]
  have hcost : 6 * I0 + 2 * S ^ 2 + CS * G ^ 2 ≤ A := by
    have h := mul_le_mul_of_nonneg_left hG₁ hCS
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hcost hE.le, mul_nonneg hE.le hA]

/-- **Lemma 8.5 on Herglotz data.** Fix a disc `B(z₁, r) ⊆ Ω`. For small `E > 0`, the Schur
complement is nonnegative on the Herglotz vector of every density whose wave has zero mean over
`Ω` and whose negative coefficients `F_{-j}` (`j ≥ 1`) vanish at `z₁`. -/
theorem herglotz_imSchur_nonneg (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hγ : IsBoundaryParam Ω γ) {z₁ : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball z₁ r ⊆ Ω) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∀ a (ha : IsDirDensity a),
        (∀ j : ℕ, 1 ≤ j → herglotzCoeff (Real.sqrt E) a (-(j : ℤ)) z₁ = 0) →
        ∫ z in Ω, herglotzCoeff (Real.sqrt E) a 0 z = 0 →
          0 ≤ imSchur (monodromy W) (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ 0)) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨C₁, δ₁, hC₁, hδ₁, hmodes⟩ := herglotz_modes_small hb hL hr hball
  obtain ⟨CT, hCT0, htrace⟩ := trace_herglotzCoeff hb hL hγ
  obtain ⟨CS, δS, hδS, hS⟩ := imSchur_herglotzVec_sub_principal_le hb hL hγ
  let D := schurErrorFactor C₁ CT (max CS 0) Kγ
  have hD0 : 0 < D := by dsimp [D, schurErrorFactor]; positivity
  refine ⟨min (min 1 δ₁) (min δS (1 / D)), by positivity,
    fun E hE hEδ W hW a ha hz hmean => ?_⟩
  have hE1 := (hEδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hEδ₁ := (hEδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hEδS := hEδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hED : E * D ≤ 1 := by
    have := (hEδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
    rwa [le_div_iff₀ hD0] at this
  have hai := ha.intervalIntegrable
  have hk2 := Real.sq_sqrt hE.le
  have hk4 : Real.sqrt E ^ 4 = E ^ 2 := by
    rw [show Real.sqrt E ^ 4 = (Real.sqrt E ^ 2) ^ 2 by ring, hk2]
  obtain ⟨hm0, hm12⟩ := hmodes a ha (Real.sqrt E) (by rw [hk2]; assumption) hz hmean
  rw [hk2] at hm0
  rw [hk4] at hm12
  have hT0 := htrace a hai (Real.sqrt E) 0
  have hT1 := htrace a hai (Real.sqrt E) (-1)
  norm_num at hT0 hT1
  rw [hk2] at hT0 hT1
  set S := ∫ θ in (0 : ℝ)..(2 * π), ‖herglotzQd (Real.sqrt E) a γ θ‖
  set c := Complex.I * herglotzCoeff (Real.sqrt E) a 0 (γ 0)
  set G := ∫ θ in (0 : ℝ)..(2 * π), ‖(∫ s in (0 : ℝ)..θ,
    herglotzConormal (Real.sqrt E) a γ s) - c‖
  let T (m : ℤ) := ∫ θ in (0 : ℝ)..(2 * π), ‖herglotzCoeff (Real.sqrt E) a m (γ θ)‖ ^ 2
  have hCSq (m : ℤ) : (∫ θ in (0 : ℝ)..(2 * π), ‖herglotzCoeff (Real.sqrt E) a m (γ θ)‖) ^ 2 ≤
      2 * π * T m :=
    sq_intervalIntegral_norm_le ((continuous_herglotzCoeff hai _ m).comp hKγ.continuous)
  have hSq : S ^ 2 ≤ (Kγ : ℝ) ^ 2 * (2 * π * T (-1)) := by
    have h := pow_le_pow_left₀ (intervalIntegral_norm_nonneg _)
      (integral_norm_herglotzQd_le hai (Real.sqrt E) hKγ) 2
    rw [mul_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hCSq (-1)) (sq_nonneg _))
  have hGsq : G ^ 2 ≤ 2 * (2 * π * T 0) + 2 * (4 * π ^ 2 * E * S ^ 2) := by
    set H := ∫ θ in (0 : ℝ)..(2 * π), ‖herglotzCoeff (Real.sqrt E) a 0 (γ θ)‖
    have h : G ≤ H + 2 * π * Real.sqrt E * S := by
      simpa only [abs_of_nonneg (Real.sqrt_nonneg E)] using
        integral_norm_primitive_sub_le hai (Real.sqrt E) hKγ
    have h2 := pow_le_pow_left₀ (show 0 ≤ G from intervalIntegral_norm_nonneg _) h 2
    have h3 : G ^ 2 ≤ 2 * H ^ 2 + 2 * (2 * π * Real.sqrt E * S) ^ 2 := by
      nlinarith only [h2, sq_nonneg (H - 2 * π * Real.sqrt E * S)]
    rw [mul_pow, mul_pow, mul_pow, hk2] at h3
    nlinarith only [h3, show H ^ 2 ≤ 2 * π * T 0 from hCSq 0]
  let I (m : ℤ) := ∫ z in Ω, ‖herglotzCoeff (Real.sqrt E) a m z‖ ^ 2
  have hI (m : ℤ) : 0 ≤ I m := integral_nonneg fun _ => sq_nonneg _
  have hP : 2 * E * I 1 - 6 * E * I 0 - 2 * E * S ^ 2 ≤
      herglotzPrincipal Ω γ (Real.sqrt E) a := by
    unfold herglotzPrincipal
    rw [hk2, integral_herglotzCoeff_main hb hai _ 2 3]
    have him := (Complex.im_le_norm _).trans (norm_integral_conj_herglotzQd_mul_le hai (Real.sqrt E) hKγ)
    nlinarith [hI (-1)]
  have hlow := (abs_le.mp (hS E hE hEδS W hW a ha hmean c)).1
  change - (CS * E * G ^ 2) ≤ _ at hlow
  have hCS := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left CS 0) hE.le) (sq_nonneg G)
  have hnum := schur_numeric hE hE1 hC₁.le hCT0 (le_max_right CS 0) (hI 1) (hI 0)
    (hI (-1)) (hI (-2)) hED hm0 (by linarith) hT0 hT1 hSq hGsq
  linarith

end PolyaNeumann
