module

public import AnalyticESC.Dimension.Rapaport
public import AnalyticESC.Generic.OpenDense

public section

set_option hygiene false
local notation "𝖀" => min_le_right _ _
local notation "𝕿" => min_le_left _ _
local notation "𝕾" => c + 1
local notation "𝕽" => N + 1
local notation "𝖇" => 4 + K

/-!
# Corollary 1.7

The systems of `𝔖_N` with equality in (1.6) contain a `d₂`-open and `d₂`-dense subset of `𝔖_N`, for
`N ≥ 2`. The open set is the open set of Theorem 1.4 intersected with the systems whose attractor
is not a singleton, which is open and dense for `N ≥ 2`; Theorem 1.6 applies to its systems.
-/

namespace AnalyticESC


open Set

namespace OpenDense

/-- The `𝒞²` distance on `I` from a map to itself vanishes. -/
theorem d2Map_self f : d2Map f f = 0 := by
  simp [d2Map]

/-- The `𝒞²` distance from a family of maps to itself vanishes. -/
theorem d2Sys_self (f : Fin N → ℂ → ℂ) : d2Sys f f = 0 := by
  simp [d2Sys, d2Map_self]

/-- The triangle inequality for `d₂` on `𝔖_N`. -/
theorem d2Sys_le_add {f g h : Fin N → ℂ → ℂ} (hf : InUnionClass f)
    (hg : InUnionClass g) (hh : InUnionClass h) : d2Sys f h ≤ d2Sys f g + d2Sys g h := by
  obtain ⟨ε, hε, hf⟩ := hf
  obtain ⟨ε', hε', hg⟩ := hg
  obtain ⟨ε'', hε'', hh⟩ := hh
  exact d2_le_add (⟨f, hε, hf⟩ : IFS N ε) (⟨g, hε', hg⟩ : IFS N ε') (⟨h, hε'', hh⟩ : IFS N ε'')

/-- Having no common fixed point in `I` is a `d₂`-open condition in `𝔖_N`: the continuous
function `∑_i |f_i(x) - x|` has a positive minimum `m` on `I`, and `d₂(f, g) < m/(N+1)` keeps
some `|g_i(x) - x|` positive at every `x ∈ I`. -/
theorem exists_forall_d2Sys_lt_not_fixed {f : Fin N → ℂ → ℂ} (hf : InUnionClass f)
    (hfix : ¬ ∃ x ∈ I, ∀ i, (f i x).re = x) :
    ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → ¬ ∃ x ∈ I, ∀ i, (g i x).re = x := by
  obtain ⟨ε, hε, hfε⟩ := hf
  push Not at hfix
  set F : ℝ → ℝ := fun x => ∑ i, |(f i x).re - x|
  have hcont : ContinuousOn F I := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    have h1 : ContinuousOn (fun x : ℝ => f i x) I :=
      (hfε i).differentiableOn.continuousOn.comp Complex.continuous_ofReal.continuousOn
        fun x hx => ofReal_mem_nbhd (by linarith) hx
    exact ((Complex.continuous_re.comp_continuousOn h1).sub continuousOn_id).abs
  have hpos : Ɐ 0 < F x := by
    intro x hx
    obtain ⟨i, hi⟩ := hfix x hx
    exact Finset.sum_pos' (fun j _ => abs_nonneg _)
      ⟨i, Finset.mem_univ i, abs_pos.2 (sub_ne_zero.2 hi)⟩
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hcont
  set m := F x₀
  have hm : 0 < m := by grind
  refine ⟨m / 𝕽, div_pos hm (by positivity), ?_⟩
  rintro g ⟨ε', hε', hgε⟩ hd ⟨x, hx, hgx⟩
  let Φ : IFS N ε := by tauto
  let Ψ : IFS N ε' := by tauto
  have hle : ∀ i, |(f i x).re - x| ≤ d2Sys f g := by
    intro i
    calc |(f i x).re - x| = |(f i x - g i x).re| := by rw [Complex.sub_re, hgx i]
      _ ≤ ‖f i x - g i x‖ := Complex.abs_re_le_norm _
      _ ≤ d2Sys f g := (IFS.Continuity.norm_sub_le_d2 Φ Ψ i hx).1
  have hsum : F x ≤ N * d2Sys f g := by
    calc F x ≤ ∑ _i : Fin N, d2Sys f g := Finset.sum_le_sum fun i _ => hle i
      _ = N * d2Sys f g := by simp
  have hmx : m ≤ F x := by aesop
  have h1 : N * d2Sys f g ≤ N * (m / 𝕽) := by nlinarith
  have h2 : N * (m / 𝕽) < m := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    linarith
  linarith

/-- Having no common fixed point in `I` is a `d₂`-dense condition in `𝔖_N` for `N ≥ 2`. If the maps
`f_i` fix a common point `p`, replace one map `f_j` by the perturbation
`f_j^t = (1 - t) f_j + t h_j` of the interpolation `IFS.exists_noCoincidence_near`, with `h_j(p) ≠ p` and small
`t > 0`. A common fixed point of the new system is fixed by some `f_k`, `k ≠ j`, so it is `p`, which
`f_j^t` moves. -/
theorem exists_not_fixed_d2Sys_lt (hN : 2 ≤ N) {f : Fin N → ℂ → ℂ}
    (hf : InUnionClass f) (hr : 0 < r) :
    ∃ g, InUnionClass g ∧ (¬ ∃ x ∈ I, ∀ i, (g i x).re = x) ∧ d2Sys f g < r := by
  by_cases hfix : ∃ x ∈ I, ∀ i, (f i x).re = x
  swap
  · exact ⟨f, hf, hfix, by rw [d2Sys_self]; exact hr⟩
  obtain ⟨p, hp, hfp⟩ := hfix
  obtain ⟨ε, hε, hfε⟩ := hf
  let Φ : IFS N ε := by tauto
  -- a map `f_j` with `h_j(p) ≠ p`, and a second map `f_k`
  obtain ⟨j, hj⟩ : ∃ j : Fin N, IFS.Coincidences.slope N * p + IFS.Coincidences.offset j ≠ p := by
    by_contra! h
    have h01 : (⟨0, by omega⟩ : Fin N) < ⟨1, by omega⟩ := Fin.mk_lt_mk.2 one_pos
    linarith [IFS.Coincidences.offset_add_slope_lt_offset h01, h ⟨0, by omega⟩,
      h ⟨1, by omega⟩, IFS.Coincidences.slope_pos (N := N)]
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 hN
  obtain ⟨k, hk⟩ := exists_ne j
  -- the parameter `t`
  set c := Φ.cmin
  have hc := Φ.cmin_pos (by omega)
  obtain ⟨K, hK, hK'⟩ := IFS.Coincidences.exists_deriv_deriv_bound Φ
  set t := min (c / 𝕾) (r / 𝖇) / 2
  have ht0 : 0 < t := half_pos (lt_min (by positivity) (by positivity))
  have ht1 : t * 𝕾 < c := (lt_div_iff₀ (by positivity)).1 ((half_lt_self (lt_min (by positivity) (by positivity))).trans_le 𝕿)
  set g := Function.update f j (IFS.Coincidences.homotopy Φ t j) with hg
  refine ⟨g, ⟨ε, hε, fun i => ?_⟩, ?_, ?_⟩
  · by_cases hi : i = j
    · rw [hi, hg, Function.update_self]
      exact IFS.Coincidences.inClass_homotopy Φ ht0 ht1 j
    · grind
  · rintro ⟨x, hx, hgx⟩
    obtain rfl := eq_of_re_eq_self hε (hfε k) hx hp (by simpa [g, Function.update_of_ne hk] using hgx k) (hfp k)
    have h := hgx j
    rw [hg, Function.update_self] at h
    rw [IFS.Coincidences.re_homotopy_ofReal, hfp j] at h
    have h' : t * (IFS.Coincidences.slope N * x + IFS.Coincidences.offset j - x) = 0 := by
      linarith
    exact hj (by grind)
  · have h : ∀ i, d2Map (f i) (g i) ≤ t * 𝖇 := by
      intro i
      by_cases hi : i = j
      · rw [hi, hg, Function.update_self]
        exact IFS.Coincidences.d2Map_homotopy_le Φ j hK (hK' j) (⟨ht0.le, by nlinarith⟩)
      · rw [hg, Function.update_of_ne hi, d2Map_self]
        positivity
    exact (Real.iSup_le h (by positivity)).trans_lt ((lt_div_iff₀ (by positivity)).1 ((half_lt_self (lt_min (by positivity) (by positivity))).trans_le 𝖀))

end OpenDense

/-- Corollary 1.7. For `N ≥ 2`, the systems of `𝔖_N` with equality in (1.6) contain a subset `U` of
`𝔖_N` that is open and dense in the `𝒞²` metric. -/
theorem corollary_1_7 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement)
    (hN : 2 ≤ N) :
    ∃ U : Set (Fin N → ℂ → ℂ),
      (∀ f ∈ U, ∃ ε, ∃ Φ : IFS N ε, Φ.f = f ∧ Φ.DimEquality) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2Sys f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2Sys f g < r) := by
  obtain ⟨U₁, hU₁, hU₁o, hU₁d⟩ := theorem_1_4 N
  -- the open set of Theorem 1.4, intersected with the systems without common fixed point
  refine ⟨U₁ ∩ {f | InUnionClass f ∧ ¬ ∃ x ∈ I, ∀ i, (f i x).re = x}, ?_, ?_, ?_⟩
  · -- Theorem 1.6, with the remark after it
    rintro f ⟨hf₁, -, hfix⟩
    obtain ⟨ε, Φ, rfl, hΦ⟩ := hU₁ f hf₁
    refine ⟨ε, Φ, rfl, Φ.theorem_1_6 (by omega) hM hS (fun h => hfix ?_) (Φ.esc_of_sesc hΦ)⟩
    exact (Φ.exists_attractor_eq_singleton_iff (by omega)).1 h
  · -- openness
    rintro f ⟨hf₁, hf, hfix⟩
    obtain ⟨r₁, hr₁, h₁⟩ := hU₁o f hf₁
    obtain ⟨r₂, hr₂, h₂⟩ := OpenDense.exists_forall_d2Sys_lt_not_fixed hf hfix
    exact ⟨min r₁ r₂, lt_min hr₁ hr₂, fun g hg hfg =>
      ⟨h₁ g hg (hfg.trans_le 𝕿), hg, h₂ g hg (hfg.trans_le 𝖀)⟩⟩
  · -- density: perturb to remove a common fixed point, then apply Theorem 1.4
    intro f hf r hr
    obtain ⟨g, hg, hgfix, hfg⟩ := OpenDense.exists_not_fixed_d2Sys_lt hN hf (half_pos hr)
    obtain ⟨ρ, hρ, hgρ⟩ := OpenDense.exists_forall_d2Sys_lt_not_fixed hg hgfix
    obtain ⟨h, hh₁, hgh⟩ := hU₁d g hg (min ρ (r / 2)) (lt_min hρ (half_pos hr))
    obtain ⟨ε, Ψ, rfl, -⟩ := hU₁ h hh₁
    have hh : InUnionClass Ψ.f := ⟨ε, Ψ.ε_pos, Ψ.inClass⟩
    refine ⟨Ψ.f, ⟨hh₁, hh, hgρ Ψ.f hh (hgh.trans_le 𝕿)⟩, ?_⟩
    have h := OpenDense.d2Sys_le_add hf hg hh
    linarith [hgh.trans_le 𝖀]

end AnalyticESC
