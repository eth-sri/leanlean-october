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

/-- If all primitives `∫₀^θ g`, `θ ∈ [0, L]`, of an interval integrable function vanish,
then `g = 0` almost everywhere on `(0, L)`. -/
lemma ae_eq_zero_of_primitive_eq_zero {g : ℝ → ℂ} {L : ℝ}
    (hg : IntervalIntegrable g volume 0 L)
    (h : ∀ θ ∈ Icc 0 L, ∫ s in (0 : ℝ)..θ, g s = 0) :
    ∀ᵐ s, s ∈ Ioo 0 L → g s = 0 := by
  rcases lt_or_ge L 0 with hL | hL
  exact Filter.Eventually.of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.mpr hL.le)
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach hL hg] with x hx hm
  refine (hx hm).unique ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq ?_)
  filter_upwards [Ioo_mem_nhds hm.1 hm.2] with x; grind

/-- The `n`-th coordinate of `C_E(s) g`. -/
lemma transportCoeff_apply_coord (γ : ℝ → ℂ) (E s : ℝ) (g : Ell2) (n : ℕ) :
    (transportCoeff γ E s g : ℕ → ℂ) n =
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) *
        (deriv γ s * (shiftWeight n * (g : ℕ → ℂ) (n + 1)) +
          conj (deriv γ s) * (shiftN g : ℕ → ℂ) n) := by
  unfold transportCoeff
  simp only [← shiftNAdj_eq_adjoint, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul, shiftNAdj_apply]

local notation "evalCoord" => lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (v : Ell2) (n : ℕ)
include γ K hK E W hW v n

/-- The rows of the transport equation, in integral form. -/
lemma transport_coord_eq {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    (W θ v : ℕ → ℂ) n = (v : ℕ → ℂ) n +
      ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (W s v) : ℕ → ℂ) n := by
  let Φ := (evalCoord n).comp (ContinuousLinearMap.apply ℂ Ell2 v)
  have hint := intervalIntegrable_mul_of_continuousOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hθ
  have h := congrArg Φ (hW.2 θ hθ)
  rw [map_add, ← Φ.intervalIntegral_comp_comm hint] at h
  exact h

/-- The rows of the transport equation have integrable right-hand sides. -/
lemma transport_coord_intervalIntegrable {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    IntervalIntegrable (fun s => (transportCoeff γ E s (W s v) : ℕ → ℂ) n) volume 0 θ := by
  have hint := intervalIntegrable_transportCoeff_apply hK E (y := fun s => W s v)
     ((hW.1.clm_apply continuousOn_const).mono (uIcc_subset_Icc ⟨le_rfl, Real.two_pi_pos.le⟩ hθ))
  exact ⟨(evalCoord n).integrable_comp hint.1, (evalCoord n).integrable_comp hint.2⟩

end

/-- Lemma 10.4: injectivity of the observation map on a Lipschitz curve with nonvanishing
derivative. -/
theorem observation_injective {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hγ' : ∀ᵐ θ, deriv γ θ ≠ 0) {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (v : Ell2)
    (hv : ∀ θ ∈ Icc 0 (2 * π), inner ℂ (basisVec 0) (W θ v) = 0) : v = 0 := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  set f : ℕ → ℝ → ℂ := fun n θ => (W θ v : ℕ → ℂ) n with hf
  have hfi : ∀ n θ, f n θ = inner ℂ (basisVec n) (W θ v) := fun n θ => by
    simp [hf, basisVec, inner_single]
  have hcont (n : ℕ) : ContinuousOn (f n) (Icc 0 (2 * π)) :=
    (evalCoord n).continuous.comp_continuousOn (hW.1.clm_apply continuousOn_const)
  have hW0 : W 0 = 1 := by simpa using hW.2 0 ⟨le_rfl, hπ⟩
  have hf0 : ∀ n, f n 0 = (v : ℕ → ℂ) n := fun n => by simp [hf, hW0]
  have ha : (-(Complex.I * (Real.sqrt E : ℂ)) / 2) ≠ 0 := by
    have : (Real.sqrt E : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hE).ne'
    simp_all
  have hw : ∀ n, shiftWeight n ≠ 0 := fun n => by
    unfold shiftWeight; split_ifs <;> simp
  have step : ∀ n, (∀ θ ∈ Icc 0 (2 * π), f n θ = 0) →
      (∀ θ ∈ Icc 0 (2 * π), (shiftN (W θ v) : ℕ → ℂ) n = 0) →
      ∀ θ ∈ Icc 0 (2 * π), f (n + 1) θ = 0 := by
    intro n hn hS
    have hprim : ∀ θ ∈ Icc 0 (2 * π),
        ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (W s v) : ℕ → ℂ) n = 0 := by
      intro θ hθ
      have := transport_coord_eq hK hW v n hθ
      rw [← hf0 n] at this
      change f n θ = f n 0 + _ at this
      rw [hn θ hθ, hn 0 ⟨le_rfl, hπ⟩, zero_add] at this
      gcongr
    have hae := ae_eq_zero_of_primitive_eq_zero (transport_coord_intervalIntegrable hK hW v n ⟨hπ, le_rfl⟩)
      hprim
    have hae' : ∀ᵐ s, s ∈ Ioo 0 (2 * π) → f (n + 1) s = 0 := by
      filter_upwards [hae, hγ'] with s hs hs' hsI
      have h1 := hs hsI
      rw [transportCoeff_apply_coord, hS s (Ioo_subset_Icc_self hsI), mul_zero, add_zero] at h1
      simpa [ha, hs', hw n] using h1
    have hae'' : f (n + 1) =ᵐ[volume.restrict (Icc 0 (2 * π))] fun _ => (0 : ℂ) := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact (ae_restrict_iff' measurableSet_Ioo).mpr hae'
    exact Measure.eqOn_Icc_of_ae_eq volume (by positivity) hae'' (hcont (n + 1))
      continuousOn_const
  have key : ∀ n, (∀ θ ∈ Icc 0 (2 * π), f n θ = 0) ∧ (∀ θ ∈ Icc 0 (2 * π), f (n + 1) θ = 0) := by
    intro n
    induction n with
    | zero =>
      have h0 : ∀ θ ∈ Icc 0 (2 * π), f 0 θ = 0 := fun θ hθ => by rw [hfi]; tauto
      exact ⟨h0, step 0 h0 fun θ _ => shiftN_apply_zero _⟩
    | succ n ih =>
      refine ⟨ih.2, step (n + 1) ih.2 fun θ hθ => ?_⟩
      rw [shiftN_apply_succ]
      change shiftWeight n * f n θ = 0
      rw [ih.1 θ hθ, mul_zero]
  apply lp.ext
  funext n
  rw [← hf0 n, (key n).1 0 ⟨le_rfl, hπ⟩]
  rfl

/-- Lemma 10.4 for a boundary parametrization, with the observation `O_E v` vanishing in
`L²(0, L)`, i.e. almost everywhere on `[0, L]`: then `v = 0`. -/
theorem observation_injective_of_boundaryParam {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (v : Ell2)
    (hv : ∀ᵐ θ ∂(volume.restrict (Icc 0 (2 * π))), inner ℂ (basisVec 0) (W θ v) = 0) :
    v = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  have hγ' : ∀ᵐ θ, deriv γ θ ≠ 0 := by
    filter_upwards [hspeed] with x; aesop
  refine observation_injective hK hγ' hE hW v ?_
  have hcont : ContinuousOn (fun θ => inner ℂ (basisVec 0) (W θ v)) (Icc 0 (2 * π)) :=
    continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
  exact Measure.eqOn_Icc_of_ae_eq volume (by positivity) hv hcont continuousOn_const

end PolyaNeumann

end
