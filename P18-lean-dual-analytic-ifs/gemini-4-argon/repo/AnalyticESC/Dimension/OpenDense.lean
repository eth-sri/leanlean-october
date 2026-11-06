module

public import AnalyticESC.Dimension.Rapaport
public import AnalyticESC.Generic.OpenDense

@[expose] public section

/-!
# Corollary 1.7

The systems of `𝔖_N` with equality in (1.6) contain a `d₂`-open and `d₂`-dense subset of `𝔖_N`, for
`N ≥ 2`. The open set is the open set of Theorem 1.4 intersected with the systems whose attractor
is not a singleton, which is open and dense for `N ≥ 2`; Theorem 1.6 applies to its systems.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

namespace OpenDense

/-- The triangle inequality for `d₂` on `𝔖_N`. -/
private theorem d2Sys_le_add {N : ℕ} {f g h : Fin N → ℂ → ℂ} (hf : InUnionClass f)
    (hg : InUnionClass g) (hh : InUnionClass h) : d2Sys f h ≤ d2Sys f g + d2Sys g h := by
  obtain ⟨ε, hε, hf⟩ := hf
  obtain ⟨ε', hε', hg⟩ := hg
  obtain ⟨ε'', hε'', hh⟩ := hh
  exact d2_le_add (⟨f, hε, hf⟩ : IFS N ε) (⟨g, hε', hg⟩ : IFS N ε') (⟨h, hε'', hh⟩ : IFS N ε'')

/-- Having no common fixed point in `I` is a `d₂`-open condition in `𝔖_N`: the continuous
function `∑_i |f_i(x) - x|` has a positive minimum `m` on `I`, and `d₂(f, g) < m/(N+1)` keeps
some `|g_i(x) - x|` positive at every `x ∈ I`. -/
private theorem exists_forall_d2Sys_lt_not_fixed {N : ℕ} {f : Fin N → ℂ → ℂ} (hf : InUnionClass f)
    (hfix : ¬ ∃ x ∈ I, ∀ i, (f i x).re = x) :
    ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → ¬ ∃ x ∈ I, ∀ i, (g i x).re = x := by
  obtain ⟨ε, hε, hfε⟩ := hf
  push Not at hfix
  set F : ℝ → ℝ := fun x => ∑ i, |(f i x).re - x|
  have hcont : ContinuousOn F I :=
    continuousOn_finsetSum _ fun i _ =>
      ((Complex.continuous_re.comp_continuousOn ((hfε i).differentiableOn.continuousOn.comp
        Complex.continuous_ofReal.continuousOn fun _ hx =>
        ofReal_mem_nbhd (by linarith) hx)).sub continuousOn_id).abs
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hcont
  obtain ⟨i₀, hi₀⟩ := hfix x₀ hx₀
  have hm : 0 < F x₀ := Finset.sum_pos' (fun _ _ => abs_nonneg _)
    ⟨i₀, Finset.mem_univ i₀, abs_pos.2 (sub_ne_zero.2 hi₀)⟩
  refine ⟨F x₀ / (N + 1), div_pos hm (by positivity), ?_⟩
  rintro g ⟨ε', hε', hgε⟩ hd ⟨x, hx, hgx⟩
  have hsum : F x ≤ N * d2Sys f g := by
    refine (Finset.sum_le_sum (g := fun _ => d2Sys f g) fun i _ => ?_).trans_eq (by simp)
    rw [show (f i x).re - x = (f i x - g i x).re by rw [Complex.sub_re, hgx i]]
    exact (Complex.abs_re_le_norm _).trans
      (IFS.Continuity.norm_sub_le_d2 ⟨f, hε, hfε⟩ ⟨g, hε', hgε⟩ i hx).1
  have hmx : F x₀ ≤ F x := isMinOn_iff.1 hmin x hx
  have h1 := mul_le_mul_of_nonneg_left hd.le (Nat.cast_nonneg N)
  have h2 : (N : ℝ) * (F x₀ / (N + 1)) < F x₀ := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; linarith
  linarith

/-- Having no common fixed point in `I` is a `d₂`-dense condition in `𝔖_N` for `N ≥ 2`. -/
private theorem exists_not_fixed_d2Sys_lt {N : ℕ} (hN : 2 ≤ N) {f : Fin N → ℂ → ℂ}
    (hf : InUnionClass f) {r : ℝ} (hr : 0 < r) :
    ∃ g, InUnionClass g ∧ (¬ ∃ x ∈ I, ∀ i, (g i x).re = x) ∧ d2Sys f g < r := by
  by_cases hfix : ∃ x ∈ I, ∀ i, (f i x).re = x
  swap
  · exact ⟨f, hf, hfix, by simp [d2Sys, d2Map, hr]⟩
  obtain ⟨p, hp, hfp⟩ := hfix
  obtain ⟨ε, hε, hfε⟩ := hf
  let Φ : IFS N ε := ⟨f, hε, hfε⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin N, IFS.Coincidences.slope N * p + IFS.Coincidences.offset j ≠ p := by
    by_contra! h
    linarith [IFS.Coincidences.offset_add_slope_lt_offset
      (Fin.mk_lt_mk.2 one_pos : (⟨0, by omega⟩ : Fin N) < ⟨1, by omega⟩),
      h ⟨0, by omega⟩, h ⟨1, by omega⟩, IFS.Coincidences.slope_pos (N := N)]
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 hN
  obtain ⟨k, hk⟩ := exists_ne j
  obtain ⟨t, ht0, Ψ, hΨf, hΨr, -, -⟩ := Φ.exists_noCoincidence_near (by omega) hr
  set g := Function.update f j (Ψ.f j) with hg
  refine ⟨g, ⟨ε, hε, fun i => ?_⟩, ?_, (ciSup_le fun i => ?_).trans_lt hΨr⟩
  · by_cases hi : i = j
    · simpa [hi, hg] using Ψ.inClass j
    · simpa [hi, hg] using hfε i
  · rintro ⟨x, hx, hgx⟩
    obtain rfl := Φ.eq_of_fixed (List.cons_ne_nil k []) hx hp
      (by simpa [g, Function.update_of_ne hk] using hgx k) (hfp k)
    have h := hgx j
    rw [hg, Function.update_self, hΨf, IFS.Coincidences.re_homotopy_ofReal,
      show (Φ.f j x).re = x from hfp j] at h
    have h' : t * (IFS.Coincidences.slope N * x + IFS.Coincidences.offset j - x) = 0 := by linarith
    exact hj (by linarith [(mul_eq_zero.1 h').resolve_left ht0.ne'])
  · by_cases hi : i = j
    · simpa [hi, hg] using le_ciSup (f := fun i => d2Map (Φ.f i) (Ψ.f i)) (finite_range _).bddAbove j
    · simpa [hg, Function.update_of_ne hi, d2Map] using IFS.Continuity.d2_nonneg Φ Ψ

end OpenDense

/-- Corollary 1.7. For `N ≥ 2`, the systems of `𝔖_N` with equality in (1.6) contain a subset `U` of
`𝔖_N` that is open and dense in the `𝒞²` metric. -/
theorem corollary_1_7 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) {N : ℕ}
    (hN : 2 ≤ N) :
    ∃ U : Set (Fin N → ℂ → ℂ),
      (∀ f ∈ U, ∃ ε : ℝ, ∃ Φ : IFS N ε, Φ.f = f ∧ Φ.DimEquality) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2Sys f g < r) := by
  have hN0 : 0 < N := by omega
  obtain ⟨U₁, hU₁, hU₁o, hU₁d⟩ := theorem_1_4 N
  refine ⟨U₁ ∩ {f | InUnionClass f ∧ ¬ ∃ x ∈ I, ∀ i, (f i x).re = x}, ?_, ?_, ?_⟩
  · rintro f ⟨hf₁, -, hfix⟩
    obtain ⟨ε, Φ, rfl, hΦ⟩ := hU₁ f hf₁
    exact ⟨ε, Φ, rfl, Φ.theorem_1_6 hM hS hN0
      (fun h => hfix ((Φ.exists_attractor_eq_singleton_iff hN0).1 h)) (Φ.esc_of_sesc hΦ)⟩
  · rintro f ⟨hf₁, hf, hfix⟩
    obtain ⟨r₁, hr₁, h₁⟩ := hU₁o f hf₁
    obtain ⟨r₂, hr₂, h₂⟩ := OpenDense.exists_forall_d2Sys_lt_not_fixed hf hfix
    exact ⟨min r₁ r₂, lt_min hr₁ hr₂, fun g hg hfg =>
      ⟨h₁ g hg (hfg.trans_le (min_le_left _ _)), hg, h₂ g hg (hfg.trans_le (min_le_right _ _))⟩⟩
  · intro f hf r hr
    obtain ⟨g, hg, hgfix, hfg⟩ := OpenDense.exists_not_fixed_d2Sys_lt hN hf (half_pos hr)
    obtain ⟨ρ, hρ, hgρ⟩ := OpenDense.exists_forall_d2Sys_lt_not_fixed hg hgfix
    obtain ⟨h, hh₁, hgh⟩ := hU₁d g hg (min ρ (r / 2)) (lt_min hρ (half_pos hr))
    obtain ⟨ε, Ψ, rfl, -⟩ := hU₁ h hh₁
    have hh : InUnionClass Ψ.f := ⟨ε, Ψ.ε_pos, Ψ.inClass⟩
    refine ⟨Ψ.f, ⟨hh₁, hh, hgρ Ψ.f hh (hgh.trans_le (min_le_left _ _))⟩, ?_⟩
    have := OpenDense.d2Sys_le_add hf hg hh
    linarith [hgh.trans_le (min_le_right _ _)]

end AnalyticESC
