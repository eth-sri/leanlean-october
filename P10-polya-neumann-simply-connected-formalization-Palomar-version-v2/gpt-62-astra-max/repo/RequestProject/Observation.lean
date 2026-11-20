module

public import RequestProject.BasePoint
public import RequestProject.PlanarNotation

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
  · grind [Filter.Eventually.of_forall]
  set G := (Ioc 0 L).indicator g with hG
  have hGi : Integrable G volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mp hg)
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hGi.locallyIntegrable] with x hx hxI
  have hF : (fun y => ∫ t in 0..y, G t) =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
    rw [← h y ⟨hy.1.le, hy.2.le⟩]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    grind [indicator_of_mem]
  
  have := (hx 0).unique ((hasDerivAt_const x 0).congr_of_eventuallyEq hF)
  rwa [hG, indicator_of_mem (Ioo_subset_Ioc_self hxI)] at this

/-- The `n`-th coordinate of `C_E(s) g`. -/
lemma transportCoeff_apply_coord (γ : ℝ → ℂ) (E s : ℝ) (g : Ell2) (n : ℕ) :
    (transportCoeff γ E s g : ℕ → ℂ) n =
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) *
        (deriv γ s * (shiftWeight n * (g : ℕ → ℂ) (n + 1)) +
          conj (deriv γ s) * (shiftN g : ℕ → ℂ) n) := by
  unfold transportCoeff
  rw [← shiftNAdj_eq_adjoint]
  rfl

/-- The rows of the transport equation, in integral form. -/
lemma transport_coord_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W) (v : Ell2) (n : ℕ)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    (W θ v : ℕ → ℂ) n = (v : ℕ → ℂ) n +
      ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (W s v) : ℕ → ℂ) n := by
  set Φ  :=
    (innerSL ℂ (basisVec n)).comp (ContinuousLinearMap.apply ℂ Ell2 v) with hΦ
  have hΦa : ∀ X : ShiftOp, Φ X = (X v) n := fun X => by
    simp [hΦ, basisVec, inner_single]
  
  rw [← hΦa, hW.2 θ hθ, map_add, hΦa, ← Φ.intervalIntegral_comp_comm (intervalIntegrable_mul_of_continuousOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hθ)]
  simp [hΦa]

/-- The rows of the transport equation have integrable right-hand sides. -/
lemma transport_coord_intervalIntegrable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {E : ℝ} {W : TransportPath} (hW : IsTransport γ E W) (v : Ell2) (n : ℕ) :
    IntervalIntegrable (fun s => (transportCoeff γ E s (W s v) : ℕ → ℂ) n) volume 0 anglePeriod := by
  set Φ  :=
    (innerSL ℂ (basisVec n)).comp (ContinuousLinearMap.apply ℂ Ell2 v) with hΦ
  have hΦa : ∀ X : ShiftOp, Φ X = (X v) n := fun X => by
    simp [hΦ, basisVec, inner_single]
  have hint := intervalIntegrable_mul_of_continuousOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1  ⟨by positivity, le_rfl⟩
  have : IntervalIntegrable (fun s => Φ (transportCoeff γ E s * W s)) volume 0 anglePeriod :=
    ⟨Φ.integrable_comp hint.1, Φ.integrable_comp hint.2⟩
  simpa [hΦa] using this

/-- Lemma 10.4: injectivity of the observation map on a Lipschitz curve with nonvanishing
derivative. -/
theorem observation_injective {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hγ' : ∀ᵐ θ, deriv γ θ ≠ 0) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport γ E W) (v : Ell2)
    (hv : ∀ θ ∈ angleInterval, inner ℂ (basisVec 0) (W θ v) = 0) : v = 0 := by
  have hπ : 0 ≤ anglePeriod := by positivity
  set f  := fun n θ => (W θ v) n with hf
  have hfi : ∀ n θ, f n θ = inner ℂ (basisVec n) (W θ v) := fun n θ => by
    simp [hf, basisVec, inner_single]
  have hcont  := fun n => have this := ContinuousOn.inner continuousOn_const (ContinuousOn.clm_apply hW.left continuousOn_const);
ContinuousOn.congr this fun θ x => hfi n θ
  have hW0 := hW.2 0 ⟨le_rfl, hπ⟩
  have hf0 : ∀ n, f n 0 = v n := fun n => by simp [*]
  have ha : (-(Complex.I * (Real.sqrt E)) / 2) ≠ 0 := by
    have : (Real.sqrt E) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hE).ne'
    simp [*]
  have hw : ∀ n, shiftWeight n ≠ 0 := fun n => by
    unfold shiftWeight; split_ifs <;> simp
  have step : ∀ n, (∀ θ ∈ angleInterval, f n θ = 0) →
      (∀ θ ∈ angleInterval, (shiftN (W θ v)) n = 0) →
      ∀ θ ∈ angleInterval, f (n + 1) θ = 0 := by
    intro n hn hS
    
    
    have hae' : ∀ᵐ s, s ∈ angleInterior → f (n + 1) s = 0 := by
      filter_upwards [(ae_eq_zero_of_primitive_eq_zero (transport_coord_intervalIntegrable hK hW v n)
        (by
            intro θ hθ
            have := transport_coord_eq hK hW v n hθ
            rw [← hf0 n] at this
            change f n θ = f n 0 + _ at this
            rw [hn θ hθ, hn 0 ⟨le_rfl, hπ⟩, zero_add] at this
            exact this.symm)), hγ'] with s hs hs' hsI
      have h1 := hs hsI
      rw [transportCoeff_apply_coord, hS s (Ioo_subset_Icc_self hsI), mul_zero, add_zero] at h1
      simpa [ha, hs', hw n] using h1
    
    refine Measure.eqOn_Icc_of_ae_eq volume (by positivity) ?_ (hcont (n + 1))
      continuousOn_const
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact (ae_restrict_iff' measurableSet_Ioo).mpr hae'
  have key : ∀ n, (∀ θ ∈ angleInterval, f n θ = 0) ∧ (∀ θ ∈ angleInterval, f (n + 1) θ = 0) := by
    intro n
    induction n with
    | zero =>
      have h0 : ∀ θ ∈ angleInterval, f 0 θ = 0 := fun θ hθ => by rw [hfi]; exact hv θ hθ
      exact ⟨h0, step 0 h0 fun θ _ => shiftN_apply_zero _⟩
    | succ n ih =>
      refine ⟨ih.2, step (n + 1) ih.2 fun θ hθ => ?_⟩
      rw [shiftN_apply_succ]
      change shiftWeight n * f n θ = 0
      rw [ih.1 θ hθ, mul_zero]
  ext n
  rw [← hf0 n, (key n).1 0 ⟨le_rfl, hπ⟩]
  rfl

/-- Lemma 10.4 for a boundary parametrization, with the observation `O_E v` vanishing in
`L²(0, L)`, i.e. almost everywhere on `[0, L]`: then `v = 0`. -/
theorem observation_injective_of_boundaryParam {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport γ E W) (v : Ell2)
    (hv : ∀ᵐ θ ∂(volume.restrict angleInterval), inner ℂ (basisVec 0) (W θ v) = 0) :
    v = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  
  refine observation_injective hK (by
    filter_upwards [hspeed] with θ hθ h0
    rw [h0, norm_zero] at hθ
    exact hc.ne hθ) hE hW v ?_
  
  exact Measure.eqOn_Icc_of_ae_eq volume (by positivity) hv (continuousOn_const.inner (hW.1.clm_apply continuousOn_const)) continuousOn_const

end PolyaNeumann

end
