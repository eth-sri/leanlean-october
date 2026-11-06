module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

public section

open MeasureTheory Set
open scoped ComplexConjugate Real



namespace PolyaNeumann

/-- If all primitives `∫₀^θ g`, `θ ∈ [0, L]`, of an interval integrable function vanish,
then `g = 0` almost everywhere on `(0, L)`. -/
lemma ae_eq_zero_of_primitive_eq_zero {g : ComplexCurve} 
    (hg : IntervalIntegrable g volume 0 L)
    (h : ∀ θ ∈ Icc 0 L, ∫ s in (0 : ℝ)..θ, g s = 0) :
    ∀ᵐ s, s ∈ Ioo 0 L → g s = 0 := by
  rcases lt_or_ge L 0 with hL | hL
  · exact Filter.Eventually.of_forall fun s hs => absurd (hs.1.trans hs.2) (not_lt.mpr hL.le)
  set G := (Ioc 0 L).indicator g with hG
  have hGi : Integrable G volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mp hg)
  filter_upwards [ae_hasDerivAt_integral_of_locallyIntegrable hGi.locallyIntegrable] with x hx hxI
  have hF : (fun y => ∫ t in (0 : ℝ)..y, G t) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
    rw [← h y ⟨hy.1.le, hy.2.le⟩]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le hy.1.le] at ht
    exact indicator_of_mem (show t ∈ Ioc 0 L from ⟨ht.1, ht.2.trans hy.2.le⟩) g
  have h0  :=
    (hasDerivAt_const x 0).congr_of_eventuallyEq hF
  have := (hx 0).unique h0
  rwa [hG, indicator_of_mem (Ioo_subset_Ioc_self hxI)] at this

/-- The `n`-th coordinate of `C_E(s) g`. -/
lemma transportCoeff_apply_coord γ E s g n :
    (transportCoeff γ E s g : ComplexSeq) n =
      (-(Complex.I * (Real.sqrt E : ℂ)) / 2) *
        (deriv γ s * (shiftWeight n * (g : ComplexSeq) (n + 1)) +
          conj (deriv γ s) * (shiftN g : ComplexSeq) n) := by
  unfold transportCoeff
  rw [← shiftNAdj_eq_adjoint]
  rfl

section
variable {γ } {K } (hK : LipschitzWith K γ) {E } {W } (hW : IsTransport γ E W) (v : Ell2) (n : ℕ)
include γ K hK E W hW v n

/-- The rows of the transport equation, in integral form. -/
lemma transport_coord_eq
     (hθ : θ ∈ boundaryInterval) :
    (W θ v : ComplexSeq) n = (v : ComplexSeq) n +
      ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (W s v) : ComplexSeq) n := by
  set Φ : (ComplexEnd Ell2) →L[ℂ] ℂ :=
    (innerSL ℂ (basisVec n)).comp (ContinuousLinearMap.apply ℂ Ell2 v) with hΦ
  have hΦa : ∀ X : ComplexEnd Ell2, Φ X = (X v : ComplexSeq) n := fun X => by
    simp [hΦ, basisVec, inner_single]
  have hint := intervalIntegrable_mul_of_continuousOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hθ
  rw [← hΦa, hW.2 θ hθ, map_add, hΦa, ← Φ.intervalIntegral_comp_comm hint]
  simp  [hΦa]

/-- The rows of the transport equation have integrable right-hand sides. -/
lemma transport_coord_intervalIntegrable :
    IntervalIntegrable (fun s => (transportCoeff γ E s (W s v) : ComplexSeq) n) volume 0 circlePeriod := by
  set Φ : (ComplexEnd Ell2) →L[ℂ] ℂ :=
    (innerSL ℂ (basisVec n)).comp (ContinuousLinearMap.apply ℂ Ell2 v) with hΦ
  have hΦa : ∀ X : ComplexEnd Ell2, Φ X = (X v : ComplexSeq) n := fun X => by
    simp [hΦ, basisVec, inner_single]
  have hint := intervalIntegrable_mul_of_continuousOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 (θ := 2 * π) ⟨by positivity, le_rfl⟩
  have : IntervalIntegrable (fun s => Φ (transportCoeff γ E s * W s)) volume 0 circlePeriod :=
    ⟨Φ.integrable_comp hint.1, Φ.integrable_comp hint.2⟩
  simpa [hΦa] using this

end


/-- Lemma 10.4: injectivity of the observation map on a Lipschitz curve with nonvanishing
derivative. -/
theorem observation_injective   (hK : LipschitzWith K γ)
    (hγ' : ∀ᵐ θ, deriv γ θ ≠ 0)  (hE : 0 < E) 
    (hW : IsTransport γ E W) v
    (hv : ∀ θ ∈ boundaryInterval, inner ℂ (basisVec 0) (W θ v) = 0) : v = 0 := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  set f : ℕ → ComplexCurve := fun n θ => (W θ v) n with hf
  have hfi : ∀ n θ, f n θ = inner ℂ (basisVec n) (W θ v) := fun n θ => by
    simp [hf, basisVec, inner_single]
  have hcont  := fun n => by
    have : ContinuousOn (fun θ => inner ℂ (basisVec n) (W θ v)) boundaryInterval :=
      continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
    exact this.congr fun θ _ => hfi n θ
  have hW0 : W 0 = 1 := by simpa using hW.2 0 ⟨le_rfl, hπ⟩
  have hf0 : ∀ n, f n 0 = (v : ComplexSeq) n := fun n => by simp [hf, hW0]
  have ha : (-(Complex.I * (Real.sqrt E : ℂ)) / 2) ≠ 0 := by
    have : (Real.sqrt E : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hE).ne'
    simp [this, Complex.I_ne_zero]
  have hw : ∀ n, shiftWeight n ≠ 0 := fun n => by
    unfold shiftWeight; split_ifs <;> simp
  have step : ∀ n, (∀ θ ∈ boundaryInterval, f n θ = 0) →
      (∀ θ ∈ boundaryInterval, (shiftN (W θ v) : ComplexSeq) n = 0) →
      ∀ θ ∈ boundaryInterval, f (n + 1) θ = 0 := by
    intro n hn hS
    have hprim : ∀ θ ∈ boundaryInterval,
        ∫ s in (0 : ℝ)..θ, (transportCoeff γ E s (W s v) : ComplexSeq) n = 0 := by
      intro θ hθ
      have := transport_coord_eq hK hW v n hθ
      rw [← hf0 n] at this
      change f n θ = f n 0 + _ at this
      rw [hn θ hθ, hn 0 ⟨le_rfl, hπ⟩, zero_add] at this
      exact this.symm
    have hae := ae_eq_zero_of_primitive_eq_zero (transport_coord_intervalIntegrable hK hW v n)
      hprim
    have hae' : ∀ᵐ s, s ∈ Ioo 0 circlePeriod → f (n + 1) s = 0 := by
      filter_upwards [hae, hγ'] with s hs hs' hsI
      have h1 := hs hsI
      rw [transportCoeff_apply_coord, hS s (Ioo_subset_Icc_self hsI), mul_zero, add_zero] at h1
      simpa [ha, hs', hw n] using h1
    have hae'' : f (n + 1) =ᵐ[volume.restrict boundaryInterval] 0 := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact (ae_restrict_iff' measurableSet_Ioo).mpr hae'
    exact Measure.eqOn_Icc_of_ae_eq volume (by positivity) hae'' (hcont (n + 1))
      continuousOn_const
  have key : ∀ n, (∀ θ ∈ boundaryInterval, f n θ = 0) ∧ (∀ θ ∈ boundaryInterval, f (n + 1) θ = 0) := by
    intro n
    induction n with
    | zero =>
      have h0 : ∀ θ ∈ boundaryInterval, f 0 θ = 0 := fun θ hθ => by rw [hfi]; exact hv θ hθ
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
theorem observation_injective_of_boundaryParam  
    (hγ : IsBoundaryParam Ω γ)  (hE : 0 < E) 
    (hW : IsTransport γ E W) v
    (hv : ∀ᵐ θ ∂(volume.restrict boundaryInterval), inner ℂ (basisVec 0) (W θ v) = 0) :
    v = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  have hγ' : ∀ᵐ θ, deriv γ θ ≠ 0 := by
    filter_upwards [hspeed] with θ hθ h0
    simp_all
  refine observation_injective hK hγ' hE hW v ?_
  have hcont : ContinuousOn (fun θ => inner ℂ (basisVec 0) (W θ v)) boundaryInterval :=
    continuousOn_const.inner (hW.1.clm_apply continuousOn_const)
  exact Measure.eqOn_Icc_of_ae_eq volume (by positivity) hv hcont continuousOn_const

end PolyaNeumann
