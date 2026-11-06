module

public import RequestProject.BasePoint

/-!
# Injectivity of the observation map on Lipschitz curves (Lemma 10.4)

For a Lipschitz boundary curve with `γ' ≠ 0` almost everywhere and `E > 0`, the
observation map `O_E v = ⟨e₀, W_E(·) v⟩` is injective: if `⟨e₀, W_E(θ) v⟩ = 0` for all
`θ ∈ [0, L]`, then `v = 0`.

The proof follows the paper: writing `f = W_E v`, each row of the transport equation
expresses `f_n'` through `γ' f_{n+1}` and `conj(γ') f_{n-1}`; inductively all coordinates
of `f` vanish, and `v = f(0) = 0`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {γ : ℝ → ℂ} {K : NNReal}

/-- If all primitives `∫₀^θ g`, `θ ∈ [0, L]`, of an interval integrable function vanish,
then `g = 0` almost everywhere on `(0, L)`. -/
lemma ae_eq_zero_of_primitive_eq_zero {g : ℝ → ℂ} {L : ℝ}
    (hg : IntervalIntegrable g volume 0 L)
    (h : ∀ θ ∈ Icc 0 L, ∫ s in 0..θ, g s = 0) :
    ∀ᵐ s, s ∈ Ioo 0 L → g s = 0 := by
  rcases lt_or_ge L 0 with hL | hL
  · exact Filter.Eventually.of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.mpr hL.le)
  filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable ((integrable_indicator_iff measurableSet_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mp hg)).locallyIntegrable] with x hx hxI
  have := (hx 0).unique ((hasDerivAt_const x 0).congr_of_eventuallyEq (by
    filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
    rw [← h y ⟨hy.1.le, hy.2.le⟩]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hy.1.le] at ht
    exact indicator_of_mem (show t ∈ Ioc 0 L from ⟨ht.1, ht.2.trans hy.2.le⟩) g))
  simp_all [indicator_of_mem (Ioo_subset_Ioc_self hxI)]

/-- The `n`-th coordinate of `C_E(s) g`. -/
lemma transportCoeff_apply_coord (γ : ℝ → ℂ) (E s : ℝ) (g : Ell2) (n : ℕ) :
    transportCoeff γ E s g n =
      (-(Complex.I * Real.sqrt E) / 2) *
        (deriv γ s * (shiftWeight n * g (n + 1)) +
          conj (deriv γ s) * shiftN g n) := by
  unfold transportCoeff
  rw [← shiftNAdj_eq_adjoint]
  rfl

/-- The rows of the transport equation, in integral form. -/
lemma transport_coord_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (v : Ell2) (n : ℕ)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    W θ v n = v n +
      ∫ s in 0..θ, transportCoeff γ E s (W s v) n := by
  set Φ : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
    (innerSL ℂ (basisVec n)).comp (ContinuousLinearMap.apply ℂ Ell2 v) with hΦ
  have hΦa : ∀ X : Ell2 →L[ℂ] Ell2, Φ X = X v n := fun X => by
    simp [hΦ, basisVec, inner_single]
  simp [← hΦa, hW.2 θ hθ, ← Φ.intervalIntegral_comp_comm (intervalIntegrable_mul_of_continuousOn (transportCoeff_aestronglyMeasurable γ E)     (transportCoeff_norm_le γ E hK) hW.1 hθ), hΦa]

/-- The rows of the transport equation have integrable right-hand sides. -/
lemma transport_coord_intervalIntegrable (hK : LipschitzWith K γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (v : Ell2) (n : ℕ) :
    IntervalIntegrable (fun s => transportCoeff γ E s (W s v) n) volume 0 (2 * π) := by
  set Φ : (Ell2 →L[ℂ] Ell2) →L[ℂ] ℂ :=
    (innerSL ℂ (basisVec n)).comp (ContinuousLinearMap.apply ℂ Ell2 v) with hΦ
  have hΦa : ∀ X : Ell2 →L[ℂ] Ell2, Φ X = X v n := fun X => by
    simp [hΦ, basisVec, inner_single]
  have hint := intervalIntegrable_mul_of_continuousOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1  ⟨by positivity, le_rfl⟩
  have : IntervalIntegrable (fun s => Φ (transportCoeff γ E s * W s)) volume 0 (2 * π) :=
    ⟨Φ.integrable_comp hint.1, Φ.integrable_comp hint.2⟩
  grind

/-- Lemma 10.4: injectivity of the observation map on a Lipschitz curve with nonvanishing
derivative. -/
theorem observation_injective (hK : LipschitzWith K γ)
    (hγ' : ∀ᵐ θ, deriv γ θ ≠ 0) {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (v : Ell2)
    (hv : ∀ θ ∈ Icc 0 (2 * π), inner ℂ (basisVec 0) (W θ v) = 0) : v = 0 := by
  have hπ : 0 ≤ 2 * π := by positivity
  set f : ℕ → ℝ → ℂ := fun n θ => W θ v n with hf
  have hfi : ∀ n θ, f n θ = inner ℂ (basisVec n) (W θ v) := fun n θ => by
    simp [hf, basisVec, inner_single]
  have hcont  := fun n => by
    have : ContinuousOn (fun θ => inner ℂ (basisVec n) (W θ v)) (Icc 0 (2 * π)) :=
      continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
    exact this.congr fun θ _ => hfi n θ
  have hW0 : W 0 = 1 := by simpa using hW.2 0 ⟨le_rfl, hπ⟩
  have hf0 : ∀ n, f n 0 = v n := fun n => by grind
  have ha : (-(Complex.I * Real.sqrt E) / 2) ≠ 0 := by
    have : Real.sqrt E ≠ 0 := by positivity
    simp_all
  have hw : ∀ n, shiftWeight n ≠ 0 := fun n => by
    unfold shiftWeight; split_ifs <;> simp
  have step : ∀ n, (∀ θ ∈ Icc 0 (2 * π), f n θ = 0) →
      (∀ θ ∈ Icc 0 (2 * π), shiftN (W θ v) n = 0) →
      ∀ θ ∈ Icc 0 (2 * π), f (n + 1) θ = 0 := by
    intro n hn hS
    exact Measure.eqOn_Icc_of_ae_eq volume (by positivity) (by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact (ae_restrict_iff' measurableSet_Ioo).mpr (by
      filter_upwards [(ae_eq_zero_of_primitive_eq_zero (transport_coord_intervalIntegrable hK hW v n)
      (by
      intro θ hθ
      have := transport_coord_eq hK hW v n hθ
      grind)), hγ'] with s hs hs' hsI
      simp_all [transportCoeff_apply_coord, hS s (Ioo_subset_Icc_self hsI)])) (hcont (n + 1))
      continuousOn_const
  have key : ∀ n, (∀ θ ∈ Icc 0 (2 * π), f n θ = 0) ∧ (∀ θ ∈ Icc 0 (2 * π), f (n + 1) θ = 0) := by
    intro n
    induction n with
    | zero =>
      have h0 : ∀ θ ∈ Icc 0 (2 * π), f 0 θ = 0 := fun θ hθ => by simp_all
      exact ⟨h0, step 0 h0 fun θ _ => shiftN_apply_zero _⟩
    | succ n ih =>
      simp_all
  apply lp.ext
  funext n
  simp [← hf0 n, (key n).1 0 ⟨le_rfl, hπ⟩]

/-- Lemma 10.4 for a boundary parametrization, with the observation `O_E v` vanishing in
`L²(0, L)`, i.e. almost everywhere on `[0, L]`: then `v = 0`. -/
theorem observation_injective_of_boundaryParam {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (v : Ell2)
    (hv : ∀ᵐ θ ∂(volume.restrict (Icc 0 (2 * π))), inner ℂ (basisVec 0) (W θ v) = 0) :
    v = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  refine observation_injective hK (by
    filter_upwards [hspeed] with θ hθ h0
    simp_all) hE hW v ?_
  exact Measure.eqOn_Icc_of_ae_eq volume (by positivity) hv (continuousOn_const.inner (hW.1.clm_apply continuousOn_const)) continuousOn_const

end PolyaNeumann

end
