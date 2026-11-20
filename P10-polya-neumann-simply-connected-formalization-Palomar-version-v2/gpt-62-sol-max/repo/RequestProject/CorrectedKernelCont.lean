module

public import RequestProject.KernelIdentity

/-!
# Continuity of the corrected kernel in the energy (Lemma 6.6, continuity part)

For a family of transports `W_E` of a Lipschitz curve and an energy `E₀` with
`c_{E₀} = (V_{E₀}^* - I) e₀ ≠ 0`, the correction `B_E` depends continuously on `E` near `E₀`
(`tendsto_cutBE_energy`), and the corrected kernel `r_E` of `CorrectedKernel.lean` converges to
`r_{E₀}` uniformly on the square `[0, L]²` as `E → E₀` (`tendsto_correctedKernel_energy`).
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

/-- Continuity of `(d, c) ↦ rankOne d c`. -/
lemma tendsto_rankOne {α : Type*} {l : Filter α} {d c : α → Ell2} {d₀ c₀ : Ell2}
    (hd : Tendsto d l (𝓝 d₀)) (hc : Tendsto c l (𝓝 c₀)) :
    Tendsto (fun x => InnerProductSpace.rankOne ℂ (d x) (c x)) l
      (𝓝 (InnerProductSpace.rankOne ℂ d₀ c₀)) := by
  have h : Continuous (fun p : StrongDual ℂ Ell2 × Ell2 => p.1.smulRight p.2) :=
    (ContinuousLinearMap.smulRightL ℂ Ell2 Ell2).continuous₂
  have hc' := ((innerSL ℂ (E := Ell2)).continuous.tendsto c₀).comp hc
  simpa only [Function.comp_def, InnerProductSpace.rankOne_def] using
    (h.tendsto (innerSL ℂ c₀, d₀)).comp (hc'.prodMk_nhds hd)

/-- Continuity of the correction `cutB c d` at a point with `c ≠ 0`. -/
lemma tendsto_cutB {α : Type*} {l : Filter α} {c d : α → Ell2} {c₀ d₀ : Ell2}
    (hc : Tendsto c l (𝓝 c₀)) (hd : Tendsto d l (𝓝 d₀)) (hc₀ : c₀ ≠ 0) :
    Tendsto (fun x => cutB (c x) (d x)) l (𝓝 (cutB c₀ d₀)) := by
  have hn2 :=
    (Complex.continuous_ofReal.tendsto _).comp (hc.norm.pow 2)
  have hn4 :=
    (Complex.continuous_ofReal.tendsto _).comp (hc.norm.pow 4)
  have h2 : ((‖c₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simp_all
  have h4 : ((‖c₀‖ ^ 4 : ℝ) : ℂ) ≠ 0 := by
    simp_all
  unfold cutB
  refine ((hn2.inv₀ h2).smul ((tendsto_rankOne hd hc).add (tendsto_rankOne hc hd))).sub
    (((hc.inner hd).div hn4 h4).smul (tendsto_rankOne hc hc))

variable {γ : ℝ → ℂ} {K : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}

private lemma tendsto_endpoint_row (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ) :
    Tendsto (fun E => ContinuousLinearMap.adjoint (Ws E (2 * π)) (basisVec 0)) (𝓝 E₀)
      (𝓝 (ContinuousLinearMap.adjoint (Ws E₀ (2 * π)) (basisVec 0))) :=
  ((continuous_eval_const (basisVec 0)).tendsto _).comp
    ((ContinuousLinearMap.adjoint.continuous.tendsto _).comp
      (tendsto_transport_energy hK hWs E₀ ⟨Real.two_pi_pos.le, le_rfl⟩))

lemma tendsto_cutC_energy (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ) :
    Tendsto (fun E => cutC (Ws E (2 * π)) (basisVec 0)) (𝓝 E₀)
      (𝓝 (cutC (Ws E₀ (2 * π)) (basisVec 0))) :=
  (tendsto_endpoint_row hK hWs E₀).sub tendsto_const_nhds

/-- Continuity of `B_E` in the energy at `E₀` when `c_{E₀} ≠ 0`. -/
theorem tendsto_cutBE_energy (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E))
    (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    Tendsto (fun E => cutBE (Ws E)) (𝓝 E₀) (𝓝 (cutBE (Ws E₀))) := by
  exact tendsto_cutB (tendsto_cutC_energy hK hWs E₀)
    ((tendsto_const_nhds.add (tendsto_endpoint_row hK hWs E₀)).const_smul _) hc

local notation "T" => Ell2 →L[ℂ] Ell2
local notation "e₀" => basisVec 0

private def entry (P X Q : T) : ℂ := ⟪e₀, P (X (ContinuousLinearMap.adjoint Q e₀))⟫_ℂ

private lemma norm_entry_le (P X Q : T) : ‖entry P X Q‖ ≤ ‖P‖ * (‖X‖ * ‖Q‖) := by
  have h : ‖ContinuousLinearMap.adjoint Q e₀‖ ≤ ‖Q‖ := by
    simpa [norm_basisVec_zero] using ContinuousLinearMap.le_opNorm (ContinuousLinearMap.adjoint Q) e₀
  unfold entry
  refine (norm_inner_le_norm _ _).trans ?_
  rw [norm_basisVec_zero, one_mul]
  exact (P.le_opNorm _).trans (by gcongr; exact (X.le_opNorm _).trans (by gcongr))

private lemma norm_entry_sub_le {P P' X X' Q Q' : T} (hQ : ‖Q‖ ≤ 1) :
    ‖entry P X Q - entry P' X' Q'‖ ≤
      ‖P - P'‖ * ‖X‖ + ‖P'‖ * (‖X - X'‖ + ‖X'‖ * ‖Q - Q'‖) := by
  have h : entry P X Q - entry P' X' Q' =
      entry (P - P') X Q + entry P' (X - X') Q + entry P' X' (Q - Q') := by
    simp only [entry, map_sub, ContinuousLinearMap.sub_apply, inner_sub_right]
    abel
  rw [h]
  calc _ ≤ ‖P - P'‖ * (‖X‖ * ‖Q‖) + ‖P'‖ * (‖X - X'‖ * ‖Q‖) +
      ‖P'‖ * (‖X'‖ * ‖Q - Q'‖) :=
    norm_add₃_le.trans (add_le_add (add_le_add (norm_entry_le ..) (norm_entry_le ..)) (norm_entry_le ..))
    _ ≤ ‖P - P'‖ * (‖X‖ * 1) + ‖P'‖ * (‖X - X'‖ * 1) +
        ‖P'‖ * (‖X'‖ * ‖Q - Q'‖) := by gcongr
    _ = _ := by ring

lemma norm_inner_sandwich_sub_le {P Q P' Q' X X' : T} (hP' : ‖P'‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) :
    ‖⟪e₀, P (X (ContinuousLinearMap.adjoint Q e₀))⟫_ℂ -
        ⟪e₀, P' (X' (ContinuousLinearMap.adjoint Q' e₀))⟫_ℂ‖ ≤
      ‖P - P'‖ * ‖X‖ + ‖X - X'‖ + ‖X'‖ * ‖Q - Q'‖ := by
  refine (norm_entry_sub_le hQ).trans ?_
  have := mul_le_mul_of_nonneg_right hP'
    (show 0 ≤ ‖X - X'‖ + ‖X'‖ * ‖Q - Q'‖ by positivity)
  linarith

/-- Pointwise perturbation bound for the corrected kernel between two transports. -/
lemma norm_correctedKernel_sub_correctedKernel_le {W W' : ℝ → Ell2 →L[ℂ] Ell2} {θ t : ℝ}
    (hWθ : ‖W θ‖ ≤ 1) (hW't : ‖W' t‖ ≤ 1) :
    ‖correctedKernel W' θ t - correctedKernel W θ t‖ ≤
      (‖W' θ - W θ‖ + ‖W' t - W t‖) * (1 + ‖cutBE W'‖ + ‖cutBE W‖) +
        ‖cutBE W' - cutBE W‖ := by
  let A : T := (Complex.I * (Real.sign (θ - t) : ℂ)) • (1 : T)
  have he (U : ℝ → T) : correctedKernel U θ t = entry (U θ) (A + cutBE U) (U t) +
      (Complex.I * ((θ - t) / π) - Complex.I * (Real.sign (θ - t) : ℂ)) := by
    simp [correctedKernel, entry, A, volterraKernel, inner_add_right, inner_smul_right, mul_assoc]
    push_cast; ring
  have ha : ‖A‖ ≤ 1 := by
    dsimp [A]
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_one₀ (abs_real_sign_le _) (norm_nonneg _) ContinuousLinearMap.norm_id_le
  have hb (U : ℝ → T) : ‖A + cutBE U‖ ≤ 1 + ‖cutBE U‖ :=
    (norm_add_le _ _).trans (add_le_add_left ha _)
  rw [he W', he W, add_sub_add_right_eq_sub]
  refine (norm_inner_sandwich_sub_le (X := A + cutBE W') (X' := A + cutBE W) hWθ hW't).trans ?_
  rw [add_sub_add_left_eq_sub]
  calc _ ≤ ‖W' θ - W θ‖ * (1 + ‖cutBE W'‖) + ‖cutBE W' - cutBE W‖ +
        (1 + ‖cutBE W‖) * ‖W' t - W t‖ := by gcongr <;> apply hb
    _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg (W' θ - W θ)) (norm_nonneg (cutBE W)),
      mul_nonneg (norm_nonneg (W' t - W t)) (norm_nonneg (cutBE W'))]

/-- The uniform transport perturbation bound of `Area.lean`, as a function of the energy. -/
def transportDist (K : NNReal) (R E₀ E : ℝ) : ℝ :=
  |Real.sqrt E₀ - Real.sqrt E| * shiftConst * R *
    (1 + 2 * π * ((Real.sqrt E + Real.sqrt E₀) * shiftConst * K))

lemma tendsto_transportDist (K : NNReal) (R E₀ : ℝ) :
    Tendsto (transportDist K R E₀) (𝓝 E₀) (𝓝 0) := by
  have hc : Continuous (transportDist K R E₀) := by unfold transportDist; fun_prop
  have := hc.tendsto E₀
  grind [transportDist]

/-- **Lemma 6.6 (continuity in the energy).** If `c_{E₀} ≠ 0`, the corrected kernel `r_E`
converges to `r_{E₀}` uniformly on `[0, L]²` as `E → E₀`. -/
theorem tendsto_correctedKernel_energy (hK : LipschitzWith K γ)
    (hWs : ∀ E, IsTransport γ E (Ws E)) (E₀ : ℝ)
    (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ E in 𝓝 E₀, ∀ θ ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π),
      ‖correctedKernel (Ws E) θ t - correctedKernel (Ws E₀) θ t‖ < ε := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  have hB := tendsto_cutBE_energy hK hWs E₀ hc
  have hBn : Tendsto (fun E => ‖cutBE (Ws E) - cutBE (Ws E₀)‖) (𝓝 E₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hB
  have hD := tendsto_transportDist K R E₀
  have hlim : Tendsto (fun E => (transportDist K R E₀ E + transportDist K R E₀ E) *
      (1 + ‖cutBE (Ws E)‖ + ‖cutBE (Ws E₀)‖) + ‖cutBE (Ws E) - cutBE (Ws E₀)‖)
      (𝓝 E₀) (𝓝 0) := by
    have := ((hD.add hD).mul (((tendsto_const_nhds (x := (1 : ℝ))).add hB.norm).add
      (tendsto_const_nhds (x := ‖cutBE (Ws E₀)‖)))).add hBn
    simp_all
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with E hE θ hθ t ht
  refine lt_of_le_of_lt ?_ hE
  refine (norm_correctedKernel_sub_correctedKernel_le (norm_transport_le_one hK (hWs E₀) hθ)
    (norm_transport_le_one hK (hWs E) ht)).trans ?_
  have d1 : ‖Ws E θ - Ws E₀ θ‖ ≤ transportDist K R E₀ E :=
    norm_transport_sub_le hK hR (hWs E₀) (hWs E) hθ
  have d2 : ‖Ws E t - Ws E₀ t‖ ≤ transportDist K R E₀ E :=
    norm_transport_sub_le hK hR (hWs E₀) (hWs E) ht
  gcongr

section

variable (hK : LipschitzWith K γ) {E E' : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (hW' : IsTransport γ E' W') {d : ℝ} (hd : ∀ s ∈ Icc 0 (2 * π), ‖W' s - W s‖ ≤ d) {θ₁ θ₂ : ℝ} (h₁ : θ₁ ∈ Icc 0 (2 * π)) (h₂ : θ₂ ∈ Icc 0 (2 * π))
include hK E E' W W' hW hW' d hd θ₁ θ₂ h₁ h₂

/-- Increments of the difference of two transports: if `‖W'(s) - W(s)‖ ≤ d` on `[0, L]`, then
`‖(W' - W)(θ₁) - (W' - W)(θ₂)‖ ≤ (|√E' - √E| κ K + √E κ K d) |θ₁ - θ₂|`. -/
lemma norm_transport_diff_sub_le  :
    ‖(W' θ₁ - W θ₁) - (W' θ₂ - W θ₂)‖ ≤
      (|Real.sqrt E' - Real.sqrt E| * shiftConst * K + Real.sqrt E * shiftConst * K * d) *
        |θ₁ - θ₂| := by
  have hC := transportCoeff_aestronglyMeasurable γ E
  have hM := transportCoeff_norm_le γ E hK
  have hC' := transportCoeff_aestronglyMeasurable γ E'
  have hM' := transportCoeff_norm_le γ E' hK
  have hκ := shiftConst_nonneg
  have e : (W' θ₁ - W θ₁) - (W' θ₂ - W θ₂) = (W' θ₁ - W' θ₂) - (W θ₁ - W θ₂) := by abel
  have a1 := intervalIntegrable_mul_of_continuousOn hC hM hW.1 h₁
  have a2 := intervalIntegrable_mul_of_continuousOn hC hM hW.1 h₂
  have b1 := intervalIntegrable_mul_of_continuousOn hC' hM' hW'.1 h₁
  have b2 := intervalIntegrable_mul_of_continuousOn hC' hM' hW'.1 h₂
  rw [e, hW.2 θ₁ h₁, hW.2 θ₂ h₂, hW'.2 θ₁ h₁, hW'.2 θ₂ h₂, add_sub_add_left_eq_sub,
    add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left a1 a2,
    intervalIntegral.integral_interval_sub_left b1 b2,
    ← intervalIntegral.integral_sub (b2.symm.trans b1) (a2.symm.trans a1)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
  have ht' : t ∈ Icc 0 (2 * π) := by
    have := uIoc_subset_uIcc ht
    rw [mem_uIcc] at this
    rcases this with h | h
    · exact ⟨h₂.1.trans h.1, h.2.trans h₁.2⟩
    · exact ⟨h₁.1.trans h.1, h.2.trans h₂.2⟩
  have e2 : transportCoeff γ E' t * W' t - transportCoeff γ E t * W t =
      (transportCoeff γ E' t - transportCoeff γ E t) * W' t +
        transportCoeff γ E t * (W' t - W t) := by
    rw [sub_mul, mul_sub]; abel
  rw [e2]
  have hCC : ‖transportCoeff γ E' t - transportCoeff γ E t‖ ≤
      |Real.sqrt E' - Real.sqrt E| * shiftConst * K := by
    rw [transportCoeff_eq_coeffOf]
    refine (norm_coeffOf_sub_coeffOf_le E' E _).trans ?_
    have := norm_deriv_le_of_lipschitz hK (x₀ := t)
    gcongr
  have hW1 := norm_transport_le_one hK hW' ht'
  have hCt := norm_transportCoeff_le_const hK E t
  have hdt := hd t ht'
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_mul_le _ _).trans ?_) ((norm_mul_le _ _).trans ?_)
  · calc _ ≤ (|Real.sqrt E' - Real.sqrt E| * shiftConst * K) * 1 :=
          mul_le_mul hCC hW1 (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  gcongr

end

/-- The diagonal zero of the Volterra-kernel difference preserves the
small Lipschitz constant when multiplying by the sign. -/
private lemma norm_correctedKernel_diff_sub_le {E E' d : ℝ} {W W' : ℝ → T}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (hW' : IsTransport γ E' W')
    (hd : ∀ s ∈ Icc 0 (2 * π), ‖W' s - W s‖ ≤ d) {x y t : ℝ}
    (hx : x ∈ Icc 0 (2 * π)) (hy : y ∈ Icc 0 (2 * π)) (ht : t ∈ Icc 0 (2 * π)) :
    ‖(correctedKernel W' x t - correctedKernel W x t) -
      (correctedKernel W' y t - correctedKernel W y t)‖ ≤
      ((|Real.sqrt E' - Real.sqrt E| * shiftConst * K + Real.sqrt E * shiftConst * K * d) *
        (1 + ‖cutBE W'‖) + Real.sqrt E * shiftConst * K *
        (‖cutBE W' - cutBE W‖ + (1 + ‖cutBE W‖) * d)) * |x - y| := by
  let b := Real.sqrt E * shiftConst * K
  let l := |Real.sqrt E' - Real.sqrt E| * shiftConst * K + b * d
  have hentry (X X' : T) (u v : ℝ) (hu : u ∈ Icc 0 (2 * π)) (hv : v ∈ Icc 0 (2 * π)) :
      ‖(entry (W' u) X (W' t) - entry (W u) X' (W t)) -
        (entry (W' v) X (W' t) - entry (W v) X' (W t))‖ ≤
        (l * ‖X‖ + b * (‖X - X'‖ + ‖X'‖ * d)) * |u - v| := by
    have e : (entry (W' u) X (W' t) - entry (W u) X' (W t)) -
        (entry (W' v) X (W' t) - entry (W v) X' (W t)) =
        entry (W' u - W' v) X (W' t) - entry (W u - W v) X' (W t) := by
      simp  [entry, ContinuousLinearMap.sub_apply, inner_sub_right]
      abel
    rw [e]
    have h' : ‖(W' u - W' v) - (W u - W v)‖ ≤ l * |u - v| := by
      rw [show (W' u - W' v) - (W u - W v) = (W' u - W u) - (W' v - W v) by abel]
      exact norm_transport_diff_sub_le hK hW hW' hd hu hv
    have h := norm_transport_sub_le_lip hK hW hu hv
    calc _ ≤ _ := norm_entry_sub_le (norm_transport_le_one hK hW' ht)
      _ ≤ (l * |u - v|) * ‖X‖ + (b * |u - v|) * (‖X - X'‖ + ‖X'‖ * d) := by
        have hnn := (norm_nonneg _).trans h
        gcongr
        exact hd t ht
      _ = _ := by ring
  let g := fun u => volterraKernel W' u t - volterraKernel W u t
  have hg (u v : ℝ) (hu : u ∈ Icc 0 (2 * π)) (hv : v ∈ Icc 0 (2 * π)) :
      ‖g u - g v‖ ≤ (l + b * d) * |u - v| := by
    have h : ‖(1 : T)‖ = 1 := le_antisymm ContinuousLinearMap.norm_id_le (by
      simpa [norm_basisVec_zero] using (1 : T).le_opNorm e₀)
    simpa [g, entry, volterraKernel, h] using hentry 1 1 u v hu hv
  have hg0 : g t = 0 := by simp [g, volterraKernel_self hK hW ht, volterraKernel_self hK hW' ht]
  have hg1 (u : ℝ) (hu : u ∈ Icc 0 (2 * π)) : ‖g u‖ ≤ (l + b * d) * |u - t| := by
    simpa only [hg0, sub_zero] using hg u t hu ht
  have hsign := norm_sign_mul_sub_le (hg x y hx hy) (hg1 x hx) (hg1 y hy)
  have hB := hentry (cutBE W') (cutBE W) x y hx hy
  have he (u : ℝ) : correctedKernel W' u t - correctedKernel W u t =
      Complex.I * (Real.sign (u - t) * g u) + (entry (W' u) (cutBE W') (W' t) -
        entry (W u) (cutBE W) (W t)) := by
    simp only [correctedKernel, entry]
    ring
  simp  [he]
  rw [add_sub_add_comm, ← mul_sub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul]
  exact (add_le_add hsign hB).trans_eq (by dsimp [b]; ring)

/-- The first-variable Lipschitz constant of the kernel difference tends to zero. -/
theorem tendsto_correctedKernel_lipschitz (hK : LipschitzWith K γ) (hWs : ∀ E, IsTransport γ E (Ws E))
    (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ E in 𝓝 E₀, ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π), ∀ t ∈ Icc 0 (2 * π),
      ‖(correctedKernel (Ws E) x t - correctedKernel (Ws E₀) x t) -
        (correctedKernel (Ws E) y t - correctedKernel (Ws E₀) y t)‖ ≤ ε * |x - y| := by
  obtain ⟨R, hR⟩ := exists_curve_displacement_bound hK
  let d := transportDist K R E₀
  let b := Real.sqrt E₀ * shiftConst * K
  let l := fun E => |Real.sqrt E - Real.sqrt E₀| * shiftConst * K + b * d E
  let B := fun E => cutBE (Ws E)
  have hB := tendsto_cutBE_energy hK hWs E₀ hc
  have hd := tendsto_transportDist K R E₀
  have hl : Tendsto l (𝓝 E₀) (𝓝 0) := by
    have h : Continuous l := by unfold l d transportDist; fun_prop
    have hz : l E₀ = 0 := by simp [l, d, transportDist]
    simpa only [hz] using h.tendsto E₀
  have hlim : Tendsto (fun E => l E * (1 + ‖B E‖) + b * (‖B E - B E₀‖ + (1 + ‖B E₀‖) * d E))
      (𝓝 E₀) (𝓝 0) := by
    simpa using (hl.mul (hB.norm.const_add 1)).add
      (((tendsto_iff_norm_sub_tendsto_zero.mp hB).add (hd.const_mul (1 + ‖B E₀‖))).const_mul b)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with E hE x hx y hy t ht
  exact (norm_correctedKernel_diff_sub_le hK (hWs E₀) (hWs E)
    (d := d E) (fun s hs => norm_transport_sub_le hK hR (hWs E₀) (hWs E) hs) hx hy ht).trans
    (mul_le_mul_of_nonneg_right hE.le (abs_nonneg _))

end PolyaNeumann
