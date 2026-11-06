/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.HorizontalStrip
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.Order.Compact
public import DOZZ.Statements.Defs.LFun
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Topology.DiscreteSubset
public import DOZZ.Statements.Brownian.ReflectionPoleFree
public import DOZZ.DOZZAlgebra.GenericLocus
public import DOZZ.Brownian.ReflectionExponentBounds
public import Mathlib.Analysis.Meromorphic.Basic
public import DOZZ.Statements.Brownian.ReflectionR
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Analytic inputs for the identification `R = R^DOZZ`

Germ statements `=ᶠ[𝓝[≠] z]` are used throughout, so no value of a totalized function at an
isolated point is constrained.

*Quasi-periodic quotients.* A meromorphic function on a strip that is `T₁`-periodic, quasi-periodic
under `T₂` with multiplier `κ`, and positive and continuous on a real interval longer than `T₁` has
`κ = 1`. In meromorphic normal form it is analytic, positive, and bounded above and below on the
real axis, and iterating the quasi-period forces `κ = 1`. Codiscrete properties restrict to
punctured germs and are translation invariant. Meromorphic functions sharing a punctured germ at
one point of a preconnected set share it at every point, and quotients of functions with common
shift laws are (quasi-)periodic.

*The two coefficients.* `reflectionDOZZ` is meromorphic on the plane and real at real charges. It
is nonvanishing on the physical interval `(γ/2, Q)` away from the Gamma poles `p_α ∈ ℕ_{>0}`. There
the probabilistic coefficient divided by it is the explicit positive continuous ratio
`reflectionDOZZRatio`, which only involves the unit-volume moment `R̄(α)`. The poles are isolated,
and off them both coefficients are continuous along real charges.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs
section
variable {h : ℝ}

/-- Real points lie in every horizontal strip of positive height. -/
theorem ofReal_mem_horizontalStrip (hh : 0 < h) (x : ℝ) :
    (x : ℂ) ∈ horizontalStrip h := by
  simp [horizontalStrip, hh]

/-- Horizontal strips are invariant under real translations. -/
theorem add_ofReal_mem_horizontalStrip {z : ℂ} (hz : z ∈ horizontalStrip h) (t : ℝ) :
    z + (t : ℂ) ∈ horizontalStrip h := by
  simpa [horizontalStrip] using hz

end

/-- The real embedding maps punctured neighborhoods into punctured neighborhoods. -/
theorem tendsto_ofReal_nhdsNE (x : ℝ) :
    Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp_all

/-- Real translations map punctured neighborhoods into punctured neighborhoods. -/
theorem tendsto_add_const_nhdsNE (z t : ℂ) :
    Tendsto (fun w : ℂ => w + t) (𝓝[≠] z) (𝓝[≠] (z + t)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact ((continuous_id.add continuous_const).tendsto z).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    simp_all

/-- A normal-form meromorphic function that agrees, on a real punctured neighborhood, with a real
function continuous at the point is analytic there and takes that function's value. -/
theorem analyticAt_and_eq_of_eventually_eq_real {g : ℂ → ℂ} {x : ℝ}
    (hg : MeromorphicNFAt g (x : ℂ)) {E : ℝ → ℝ} (hE : ContinuousAt E x)
    (hgE : ∀ᶠ y : ℝ in 𝓝[≠] x, g (y : ℂ) = (E y : ℂ)) :
    AnalyticAt ℂ g (x : ℂ) ∧ g (x : ℂ) = (E x : ℂ) := by
  have hEt : Tendsto (fun y : ℝ => g y) (𝓝[≠] x) (𝓝 (E x : ℂ)) := by
    have h1 : Tendsto (fun y : ℝ => ((E y : ℝ) : ℂ)) (𝓝[≠] x) (𝓝 (E x : ℂ)) :=
      ((Complex.continuous_ofReal.tendsto _).comp hE.tendsto).mono_left nhdsWithin_le_nhds
    exact h1.congr' (hgE.mono fun y hy => hy.symm)
  have horder : 0 ≤ meromorphicOrderAt g x := by
    by_contra hneg
    have hreal := (tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge hneg)).comp (tendsto_ofReal_nhdsNE x)
    rw [← tendsto_norm_atTop_iff_cobounded] at hreal
    exact not_tendsto_atTop_of_tendsto_nhds hEt.norm hreal
  have han := hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder
  refine ⟨han, ?_⟩
  have hcont :=
    han.continuousAt.tendsto.comp ((tendsto_ofReal_nhdsNE x).mono_right nhdsWithin_le_nhds)
  exact tendsto_nhds_unique hcont hEt

/-- Two normal-form functions with the same punctured germ agree at the point. -/
theorem eq_of_meromorphicNFAt_of_eventuallyEq_nhdsNE {g₁ g₂ : ℂ → ℂ} {z : ℂ}
    (h₁ : MeromorphicNFAt g₁ z) (h₂ : MeromorphicNFAt g₂ z) (h : g₁ =ᶠ[𝓝[≠] z] g₂) :
    g₁ z = g₂ z :=
  ((h₁.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds h₂).1 h).eq_of_nhds
section
variable {h : ℝ}

/-- A punctured-germ translation identity transfers to the normal form on the strip. -/
theorem toMeromorphicNFOn_add_eq {f : ℂ → ℂ} (hf : MeromorphicOn f (horizontalStrip h))
    {z : ℂ} (hz : z ∈ horizontalStrip h) (T : ℝ) (c : ℂ) (hc : c ≠ 0)
    (hper : f =ᶠ[𝓝[≠] z] fun w => c * f (w + T)) :
    toMeromorphicNFOn f (horizontalStrip h) z =
      c * toMeromorphicNFOn f (horizontalStrip h) (z + T) := by
  set S := horizontalStrip h
  set g := toMeromorphicNFOn f S
  have hzT := add_ofReal_mem_horizontalStrip hz T
  have hNF := meromorphicNFOn_toMeromorphicNFOn f S
  have hgz : g =ᶠ[𝓝[≠] z] f := hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  have hgzT : g =ᶠ[𝓝[≠] (z + T)] f := hf.toMeromorphicNFOn_eq_self_on_nhdsNE hzT
  have hshift : (fun w => g (w + T)) =ᶠ[𝓝[≠] z] fun w => f (w + T) :=
    (tendsto_add_const_nhdsNE z T).eventually hgzT
  have hgerm : g =ᶠ[𝓝[≠] z] fun w => c * g (w + T) := by
    filter_upwards [hgz, hper, hshift] with w h1 h2 h3
    simp_all
  have hNFshift : MeromorphicNFAt (fun w => c * g (w + T)) z := by
    have h0 :=
      meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt.2 (hNF hzT)
    exact (meromorphicNFAt_const_smul_iff_meromorphicNFAt hc).2 h0
  exact eq_of_meromorphicNFAt_of_eventuallyEq_nhdsNE (hNF hz) hNFshift hgerm

/-- Integer iterates of a pointwise period on the strip. -/
theorem eq_add_int_mul_of_periodic {g : ℂ → ℂ} {T : ℝ}
    (hg : ∀ z ∈ horizontalStrip h, g z = g (z + T)) (z : ℂ) (hz : z ∈ horizontalStrip h)
    (n : ℤ) : g (z + (n : ℂ) * T) = g z := by
  have hnat : ∀ (m : ℕ) (w : ℂ), w ∈ horizontalStrip h → g (w + (m : ℂ) * T) = g w := by
    intro m
    induction m with
    | zero => intro w _; simp
    | succ m ih =>
      intro w hw
      have hmem : w + (m : ℂ) * T ∈ horizontalStrip h := by
        simpa using add_ofReal_mem_horizontalStrip hw ((m : ℝ) * T)
      rw [← ih w hw, hg _ hmem]
      congr 1
      push_cast
      ring
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simp_all
  · have hmem : z + ((-(m : ℤ) : ℤ) : ℂ) * T ∈ horizontalStrip h := by
      simpa using add_ofReal_mem_horizontalStrip hz (-((m : ℝ) * T))
    have h1 := hnat m _ hmem
    simp_all

/-- A quasi-period multiplier of a periodic meromorphic function on a strip that is continuous
and positive on a real interval longer than the period equals one. -/
theorem quasiPeriod_multiplier_eq_one (hh : 0 < h) {f : ℂ → ℂ}
    (hf : MeromorphicOn f (horizontalStrip h)) {T₁ T₂ : ℝ} (hT₁ : 0 < T₁)
    {κ : ℂ}
    (hp₁ : ∀ z ∈ horizontalStrip h, f =ᶠ[𝓝[≠] z] fun w => f (w + T₁))
    (hq : ∀ z ∈ horizontalStrip h, f =ᶠ[𝓝[≠] z] fun w => κ * f (w + T₂))
    {a b : ℝ} (hab : a + T₁ < b) {E : ℝ → ℝ} (hE : ContinuousOn E (Ioo a b))
    (hEpos : ∀ x ∈ Ioo a b, 0 < E x)
    (hfE : ∀ x ∈ Ioo a b, ∀ᶠ y : ℝ in 𝓝[≠] x, f (y : ℂ) = (E y : ℂ)) :
    κ = 1 := by
  set S := horizontalStrip h with hSdef
  set g := toMeromorphicNFOn f S with hgdef
  have hNF : MeromorphicNFOn g S := meromorphicNFOn_toMeromorphicNFOn f S
  have hmemR : ∀ x : ℝ, (x : ℂ) ∈ S := ofReal_mem_horizontalStrip hh
  -- the normal form is analytic and equal to `E` on the interval
  have hgE : ∀ x ∈ Ioo a b, g (x : ℂ) = (E x : ℂ) := by
    intro x hx
    have hcont : ContinuousAt E x := hE.continuousAt (Ioo_mem_nhds hx.1 hx.2)
    have hgf : ∀ᶠ y : ℝ in 𝓝[≠] x, g (y : ℂ) = f (y : ℂ) :=
      (tendsto_ofReal_nhdsNE x).eventually (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (hmemR x))
    have hgE' : ∀ᶠ y : ℝ in 𝓝[≠] x, g (y : ℂ) = (E y : ℂ) := by
      filter_upwards [hgf, hfE x hx] with y h1 h2
      simp_all
    exact (analyticAt_and_eq_of_eventually_eq_real (hNF (hmemR x)) hcont hgE').2
  -- the multiplier is nonzero, since `E` is positive
  have hκ : κ ≠ 0 := by
    intro hκ0
    set x₀ := (a + b) / 2
    have hx₀ : x₀ ∈ Ioo a b := by grind
    have hzero : ∀ᶠ y : ℝ in 𝓝[≠] x₀, f (y : ℂ) = 0 := by
      filter_upwards [(tendsto_ofReal_nhdsNE x₀).eventually (hq _ (hmemR x₀))] with y hy
      rw [hy, hκ0, zero_mul]
    have hin : ∀ᶠ y : ℝ in 𝓝[≠] x₀, y ∈ Ioo a b :=
      eventually_nhdsWithin_of_eventually_nhds (Ioo_mem_nhds hx₀.1 hx₀.2)
    obtain ⟨y, hy⟩ := (hzero.and ((hfE x₀ hx₀).and hin)).exists
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have := hEpos y hy3
    rw [hy1] at hy2
    have hE0 : E y = 0 := by exact_mod_cast hy2.symm
    linarith
  -- periodicity and quasi-periodicity of the normal form
  have hper : ∀ z ∈ S, g z = g (z + T₁) := fun z hz => by
    have := toMeromorphicNFOn_add_eq hf hz T₁ 1 one_ne_zero (by simp_all)
    simpa using this
  have hquasi : ∀ z ∈ S, g z = κ * g (z + T₂) := fun z hz =>
    toMeromorphicNFOn_add_eq hf hz T₂ κ hκ (hq z hz)
  -- every real value of the normal form is a value of `E` on one fundamental interval
  set c₀ := (a + b - T₁) / 2 with hc₀def
  have hK : Icc c₀ (c₀ + T₁) ⊆ Ioo a b := fun y hy =>
    ⟨by grind,
     by grind⟩
  have hreal : ∀ x : ℝ, ∃ y ∈ Icc c₀ (c₀ + T₁), g (x : ℂ) = (E y : ℂ) := by
    intro x
    set n := ⌊(x - c₀) / T₁⌋ with hndef
    set y := x - n * T₁ with hydef
    have hy : y ∈ Icc c₀ (c₀ + T₁) := by
      constructor
      · have : (n : ℝ) * T₁ ≤ x - c₀ := by
          have := mul_le_mul_of_nonneg_right (Int.floor_le ((x - c₀) / T₁)) hT₁.le
          rwa [div_mul_cancel₀ _ hT₁.ne'] at this
        linarith
      · have : x - c₀ < ((n : ℝ) + 1) * T₁ := by
          have := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x - c₀) / T₁)) hT₁
          rwa [div_mul_cancel₀ _ hT₁.ne'] at this
        linarith
    refine ⟨y, hy, ?_⟩
    have hit := eq_add_int_mul_of_periodic hper (y : ℂ) (hmemR y) n
    have hxy : (y : ℂ) + (n : ℂ) * T₁ = (x : ℂ) := by simp_all
    rw [hxy] at hit
    rw [hit]
    exact hgE y (hK hy)
  -- bounds of `E` on the fundamental interval
  have hKc : IsCompact (Icc c₀ (c₀ + T₁)) := isCompact_Icc
  have hKne : (Icc c₀ (c₀ + T₁)).Nonempty := nonempty_Icc.mpr (by linarith)
  obtain ⟨ymin, hymin, hmin⟩ := hKc.exists_isMinOn hKne (hE.mono hK)
  obtain ⟨ymax, hymax, hmax⟩ := hKc.exists_isMaxOn hKne (hE.mono hK)
  set m := E ymin
  set M := E ymax
  have hm : 0 < m := by tauto
  have hbounds : ∀ x : ℝ, ∃ e : ℝ, m ≤ e ∧ e ≤ M ∧ g (x : ℂ) = (e : ℂ) := by
    intro x
    obtain ⟨y, hy, he⟩ := hreal x
    exact ⟨E y, hmin hy, hmax hy, he⟩
  have hMpos : 0 < M := by tauto
  -- iterate the quasi-period along the real axis
  obtain ⟨e₀, he₀m, he₀M, he₀⟩ := hbounds c₀
  have hiter : ∀ n : ℕ, g (c₀ : ℂ) = κ ^ n * g ((c₀ + n * T₂ : ℝ) : ℂ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hpt : ((c₀ + (n : ℝ) * T₂ : ℝ) : ℂ) + (T₂ : ℂ) =
          ((c₀ + ((n + 1 : ℕ) : ℝ) * T₂ : ℝ) : ℂ) := by
        push_cast
        ring
      rw [ih, (hquasi _ (hmemR (c₀ + n * T₂))), hpt, pow_succ, mul_assoc]
  obtain ⟨e₁, he₁m, he₁M, he₁⟩ := hbounds (c₀ + ((1 : ℕ) : ℝ) * T₂)
  have hκreal : κ = ((e₀ / e₁ : ℝ) : ℂ) := by
    have h1 := hiter 1
    rw [pow_one, he₀, he₁] at h1
    have he₁0 : (e₁ : ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le hm he₁m).ne'
    push_cast
    rw [eq_div_iff he₁0, h1]
  set r := e₀ / e₁ with hrdef
  have hr : 0 < r := by bound
  have hpow : ∀ n : ℕ, m / M ≤ r ^ n ∧ r ^ n ≤ M / m := by
    intro n
    obtain ⟨eₙ, heₙm, heₙM, heₙ⟩ := hbounds (c₀ + n * T₂)
    have h := hiter n
    rw [he₀, heₙ, hκreal, ← Complex.ofReal_pow, ← Complex.ofReal_mul] at h
    have h' : e₀ = r ^ n * eₙ := by exact_mod_cast h
    have heₙpos : 0 < eₙ := lt_of_lt_of_le hm heₙm
    have hrn : r ^ n = e₀ / eₙ := by rw [h']; field_simp
    rw [hrn]
    constructor <;> bound
  have hr1 : r = 1 := by
    rcases lt_trichotomy r 1 with hlt | heq | hgt
    · have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hlt
      have hev := (ht.eventually (gt_mem_nhds (div_pos hm hMpos)))
      obtain ⟨n, hn⟩ := hev.exists
      exact absurd (hpow n).1 (not_le.mpr hn)
    · exact heq
    · have ht := tendsto_pow_atTop_atTop_of_one_lt hgt
      obtain ⟨n, hn⟩ := (ht.eventually (eventually_gt_atTop (M / m))).exists
      exact absurd (hpow n).2 (not_le.mpr hn)
  rw [hκreal, hr1, Complex.ofReal_one]

end
section
variable {P : ℂ → Prop}
section
variable (h : ∀ᶠ w in Filter.codiscrete ℂ, P w)
include h

/-- A codiscrete property holds on a punctured neighborhood of every point. -/
theorem eventually_nhdsNE_of_eventually_codiscrete (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, P w :=
  eventually_codiscrete_iff_forall_eventually_nhdsNE.1 h z

/-- Codiscrete properties are invariant under translation. -/
theorem eventually_codiscrete_comp_add (T : ℂ) :
    ∀ᶠ w in Filter.codiscrete ℂ, P (w + T) :=
  eventually_codiscrete_iff_forall_eventually_nhdsNE.2 fun x =>
    (tendsto_add_const_nhdsNE x T).eventually (eventually_nhdsNE_of_eventually_codiscrete h (x + T))

end

end

/-- Identity principle on a preconnected set: a punctured-germ equality of two meromorphic
functions at one point propagates to every point. -/
theorem eventuallyEq_nhdsNE_of_isPreconnected {U : Set ℂ} (hU : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) {x₀ : ℂ} (hx₀ : x₀ ∈ U)
    (h : f =ᶠ[𝓝[≠] x₀] g) : ∀ z ∈ U, f =ᶠ[𝓝[≠] z] g := by
  intro z hz
  have h0 : meromorphicOrderAt (f - g) x₀ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [h] with w hw
    simp_all
  have hz0 :=
    (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected hU hx₀ hz h0
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hz0] with w hw
  simpa [sub_eq_zero] using hw

/-- Meromorphic functions agreeing at every point of a real interval are germ-equal at each of
its points. -/
theorem eventuallyEq_nhdsNE_of_eq_on_Ioo {f g : ℂ → ℂ} {a b x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hf : MeromorphicAt f (x : ℂ)) (hg : MeromorphicAt g (x : ℂ))
    (h : ∀ y ∈ Set.Ioo a b, f (y : ℂ) = g (y : ℂ)) : f =ᶠ[𝓝[≠] (x : ℂ)] g := by
  rw [← hf.frequently_eq_iff_eventuallyEq hg]
  have hreal : ∃ᶠ y : ℝ in 𝓝[≠] x, f y = g y := by
    refine Eventually.frequently ?_
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)] with y hy using h y hy
  have hmap : ∃ᶠ z in Filter.map (fun y : ℝ => (y : ℂ)) (𝓝[≠] x), f z = g z :=
    Filter.frequently_map.2 hreal
  exact hmap.filter_mono (tendsto_ofReal_nhdsNE x)
section
variable {R RD D : ℂ → ℂ}

/-- The quotient of two functions obeying the same codiscrete first shift law is periodic. -/
theorem div_comp_sub_eq_of_shift {K T : ℂ} (hK : K ≠ 0)
    (hR : ∀ᶠ w in Filter.codiscrete ℂ, R (w - T) = K * R w / D w)
    (hRD : ∀ᶠ w in Filter.codiscrete ℂ, RD (w - T) = K * RD w / D w)
    (hD : ∀ᶠ w in Filter.codiscrete ℂ, D w ≠ 0) :
    ∀ᶠ w in Filter.codiscrete ℂ, R (w - T) / RD (w - T) = R w / RD w := by
  filter_upwards [hR, hRD, hD] with w h1 h2 h3
  grind

/-- The quotient of two functions obeying dual shift laws with multipliers `c₁`, `c₂` is
quasi-periodic with multiplier `c₁ / c₂`. -/
theorem div_eq_mul_div_comp_add_of_shift {c₁ c₂ T : ℂ} (hc₂ : c₂ ≠ 0)
    (hR : ∀ᶠ w in Filter.codiscrete ℂ, R w = -c₁ * R (w + T) / D w)
    (hRD : ∀ᶠ w in Filter.codiscrete ℂ, RD w = -c₂ * RD (w + T) / D w)
    (hD : ∀ᶠ w in Filter.codiscrete ℂ, D w ≠ 0) :
    ∀ᶠ w in Filter.codiscrete ℂ, R w / RD w = c₁ / c₂ * (R (w + T) / RD (w + T)) := by
  filter_upwards [hR, hRD, hD] with w h1 h2 h3
  grind

end

/-- `lFun` does not vanish off the integers. -/
theorem lFun_ne_zero_of_forall_ne_int {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) : lFun x ≠ 0 := by
  have h1 : Complex.Gamma x ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m h => hx (-m) ?_
    simp_all
  have h2 : Complex.Gamma (1 - x) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m h => hx (1 + m) ?_
    push_cast
    grind
  exact div_ne_zero h1 h2

/-- The complex Gamma function is meromorphic at every point. -/
theorem meromorphicAt_complexGamma (z : ℂ) : MeromorphicAt Complex.Gamma z := by
  have hinv :=
    (Complex.differentiable_one_div_Gamma.analyticAt z).meromorphicAt
  simpa [Pi.inv_def] using hinv.inv

/-- The DOZZ reflection coefficient is meromorphic on the whole plane. -/
theorem meromorphicOn_reflectionDOZZ (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) :
    MeromorphicOn (reflectionDOZZ γ μ) Set.univ := by
  intro z _
  have hb :=
    Complex.ofReal_mem_slitPlane.2 (dozzBase_pos hγ hγ2 hμ)
  have h1 : AnalyticAt ℂ (fun α : ℂ => γ * ((Q γ) - α) / 2) z := by fun_prop
  have h2 : AnalyticAt ℂ (fun α : ℂ => 2 * ((Q γ) - α) / γ) z := by fun_prop
  have h3 : AnalyticAt ℂ (fun α : ℂ => -(γ * ((Q γ) - α) / 2)) z := by fun_prop
  have h4 : AnalyticAt ℂ (fun α : ℂ => -(2 * ((Q γ) - α) / γ)) z := by fun_prop
  have hpow :=
    (analyticAt_const.cpow h2 hb).meromorphicAt
  have hG : ∀ w : ℂ → ℂ, AnalyticAt ℂ w z → MeromorphicAt (fun α => Complex.Gamma (w α)) z :=
    fun w hw => (meromorphicAt_complexGamma (w z)).comp_analyticAt hw
  unfold reflectionDOZZ
  fun_prop

/-- The explicit ratio `R(α)/R^DOZZ(α)`, with the unit-volume moment `Rbar`. -/
noncomputable def reflectionDOZZRatio (γ μ α Rbar : ℝ) : ℝ :=
  -(μ ^ reflectionExponent γ α) * reflectionExponent γ α * Rbar *
      Real.Gamma (reflectionExponent γ α) * Real.Gamma (γ * (Q γ - α) / 2) /
    (dozzBase γ μ ^ reflectionExponent γ α * Real.Gamma (-(γ * (Q γ - α) / 2)))

/-- At real charges the DOZZ coefficient is the real number given by real Gamma values. -/
theorem reflectionDOZZ_ofReal (γ μ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) :
    reflectionDOZZ γ μ (α : ℂ) =
      ((-(dozzBase γ μ ^ reflectionExponent γ α) *
        (Real.Gamma (-(γ * (Q γ - α) / 2)) / Real.Gamma (γ * (Q γ - α) / 2)) *
        (Real.Gamma (-reflectionExponent γ α) / Real.Gamma (reflectionExponent γ α)) : ℝ) : ℂ) := by
  have hb : 0 ≤ dozzBase γ μ := (dozzBase_pos hγ hγ2 hμ).le
  have hp : (2 * (((Q γ : ℝ) : ℂ) - (α : ℂ)) / (γ : ℂ)) =
      ((reflectionExponent γ α : ℝ) : ℂ) := by
    norm_cast
  have ht : ((γ : ℂ) * (((Q γ : ℝ) : ℂ) - (α : ℂ)) / 2) = ((γ * (Q γ - α) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold reflectionDOZZ
  rw [hp, ht, ← Complex.ofReal_neg, ← Complex.ofReal_neg, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_cpow hb]
  simp

/-- On the physical charge interval the Gamma argument `γ (Q - α) / 2` lies in `(0, 1)`. -/
theorem reflectionGammaArg_mem_Ioo {γ α : ℝ} (hγ : 0 < γ) (hα : γ / 2 < α ∧ α < Q γ) :
    0 < γ * (Q γ - α) / 2 ∧ γ * (Q γ - α) / 2 < 1 := by
  have hν := sub_pos.mpr hα.2
  have hsub : Q γ - α < 2 / γ := by
    dsimp [Q]
    linarith
  refine ⟨by positivity, ?_⟩
  have hmul := mul_lt_mul_of_pos_left hsub hγ
  grind

/-- `Γ(-t) < 0` for `0 < t < 1`, from the recursion `Γ(1 - t) = (-t) Γ(-t)`. -/
theorem realGamma_neg_neg_of_pos_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Real.Gamma (-t) < 0 := by
  have hrec :=
    Real.Gamma_add_one (neg_ne_zero.mpr h0.ne')
  have hpos : 0 < Real.Gamma (-t + 1) := Real.Gamma_pos_of_pos (by linarith)
  nlinarith

/-- Off the Gamma poles, `Γ(-p_α)` does not vanish for the positive reflection exponent. -/
theorem realGamma_neg_reflectionExponent_ne_zero {γ α : ℝ}
    (hp : 0 < reflectionExponent γ α) (hPole : ReflectionPoleFree γ α) :
    Real.Gamma (-reflectionExponent γ α) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m hm
  have hpm : reflectionExponent γ α = m := by linarith
  rcases m with _ | n
  · simp_all
  tauto

/-- On the physical interval off the Gamma poles the DOZZ coefficient does not vanish. -/
theorem reflectionDOZZ_ofReal_ne_zero (γ μ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α) :
    reflectionDOZZ γ μ (α : ℂ) ≠ 0 := by
  obtain ⟨-, hp, -⟩ := reflectionExponent_in_subcritical_range γ α hγ hα
  obtain ⟨ht0, ht1⟩ := reflectionGammaArg_mem_Ioo hγ hα
  have hbp : 0 < dozzBase γ μ ^ reflectionExponent γ α :=
    Real.rpow_pos_of_pos (dozzBase_pos hγ hγ2 hμ) _
  rw [reflectionDOZZ_ofReal γ μ α hγ hγ2 hμ, Complex.ofReal_ne_zero]
  exact mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr hbp.ne')
      (div_ne_zero (realGamma_neg_neg_of_pos_lt_one ht0 ht1).ne
        (Real.Gamma_pos_of_pos ht0).ne'))
    (div_ne_zero (realGamma_neg_reflectionExponent_ne_zero hp hPole)
      (Real.Gamma_pos_of_pos hp).ne')

/-- On the physical interval off the Gamma poles, the probabilistic coefficient divided by the
DOZZ coefficient is the explicit ratio. -/
theorem reflectionR_div_reflectionDOZZ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ μ α : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hα : γ / 2 < α ∧ α < Q γ)
    (hPole : ReflectionPoleFree γ α) :
    (reflectionR P γ μ α B Z : ℂ) / reflectionDOZZ γ μ (α : ℂ) =
      (reflectionDOZZRatio γ μ α (reflectionBarR P γ α B Z) : ℂ) := by
  obtain ⟨-, hp, -⟩ := reflectionExponent_in_subcritical_range γ α hγ hα
  obtain ⟨ht0, ht1⟩ := reflectionGammaArg_mem_Ioo hγ hα
  have hbp : dozzBase γ μ ^ reflectionExponent γ α ≠ 0 :=
    (Real.rpow_pos_of_pos (dozzBase_pos hγ hγ2 hμ) _).ne'
  have hGt := (Real.Gamma_pos_of_pos ht0).ne'
  have hGn := (realGamma_neg_neg_of_pos_lt_one ht0 ht1).ne
  have hGp := (Real.Gamma_pos_of_pos hp).ne'
  have hGnp := realGamma_neg_reflectionExponent_ne_zero hp hPole
  rw [reflectionDOZZ_ofReal γ μ α hγ hγ2 hμ, ← Complex.ofReal_div]
  congr 1
  unfold reflectionR reflectionDOZZRatio
  field_simp

/-- The explicit ratio is positive when the unit-volume moment is. -/
theorem reflectionDOZZRatio_pos (γ μ α Rbar : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hR : 0 < Rbar) :
    0 < reflectionDOZZRatio γ μ α Rbar := by
  obtain ⟨-, hp, -⟩ := reflectionExponent_in_subcritical_range γ α hγ hα
  obtain ⟨ht0, ht1⟩ := reflectionGammaArg_mem_Ioo hγ hα
  have hmu : 0 < μ ^ reflectionExponent γ α := Real.rpow_pos_of_pos hμ _
  have hbp : 0 < dozzBase γ μ ^ reflectionExponent γ α :=
    Real.rpow_pos_of_pos (dozzBase_pos hγ hγ2 hμ) _
  have hGn := realGamma_neg_neg_of_pos_lt_one ht0 ht1
  exact div_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hmu) hp) hR) (Real.Gamma_pos_of_pos hp)) (Real.Gamma_pos_of_pos ht0))
    (mul_neg_of_pos_of_neg hbp hGn)

/-- `Real.Gamma` composed with a map that is continuous on a set avoiding the Gamma poles is
continuous on that set. -/
theorem continuousOn_realGamma_comp {S : Set ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g S)
    (hpole : ∀ α ∈ S, ∀ m : ℕ, g α ≠ -m) :
    ContinuousOn (fun α => Real.Gamma (g α)) S := fun α hα =>
  (Real.differentiableAt_Gamma (hpole α hα)).continuousAt.comp_continuousWithinAt (hg α hα)

/-- The explicit ratio is continuous along a continuous moment on the physical interval. -/
theorem continuousOn_reflectionDOZZRatio (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioo (γ / 2) (Q γ))) :
    ContinuousOn (fun α => reflectionDOZZRatio γ μ α (f α)) (Set.Ioo (γ / 2) (Q γ)) := by
  have hb := dozzBase_pos hγ hγ2 hμ
  have hp : Continuous (reflectionExponent γ) := by
    unfold reflectionExponent
    fun_prop
  have ht : Continuous (fun α => γ * (Q γ - α) / 2) := by fun_prop
  have hrpow : ∀ c : ℝ, 0 < c → Continuous (fun α => c ^ reflectionExponent γ α) :=
    fun c hc => continuous_const.rpow hp (fun _ => Or.inl hc.ne')
  have hmem : ∀ α ∈ Set.Ioo (γ / 2) (Q γ),
      0 < γ * (Q γ - α) / 2 ∧ γ * (Q γ - α) / 2 < 1 :=
    fun α hα => reflectionGammaArg_mem_Ioo hγ hα
  have hGp : ContinuousOn (fun α => Real.Gamma (reflectionExponent γ α))
      (Set.Ioo (γ / 2) (Q γ)) := by
    refine continuousOn_realGamma_comp hp.continuousOn fun α hα m => ?_
    have hpos := (reflectionExponent_in_subcritical_range γ α hγ hα).2.1
    linarith
  have hGt : ContinuousOn (fun α => Real.Gamma (γ * (Q γ - α) / 2))
      (Set.Ioo (γ / 2) (Q γ)) := by
    refine continuousOn_realGamma_comp ht.continuousOn fun α hα m => ?_
    grind
  have hGn : ContinuousOn (fun α => Real.Gamma (-(γ * (Q γ - α) / 2)))
      (Set.Ioo (γ / 2) (Q γ)) := by
    refine continuousOn_realGamma_comp ht.neg.continuousOn fun α hα m hm => ?_
    have hzero := Real.Gamma_neg_nat_eq_zero m
    rw [← hm] at hzero
    exact (realGamma_neg_neg_of_pos_lt_one (hmem α hα).1 (hmem α hα).2).ne hzero
  unfold reflectionDOZZRatio
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · exact ((hrpow _ hb).continuousOn).mul hGn
  · intro α hα
    exact mul_ne_zero (Real.rpow_pos_of_pos hb _).ne'
      (realGamma_neg_neg_of_pos_lt_one (hmem α hα).1 (hmem α hα).2).ne
section
variable {γ : ℝ}
section
variable (hγ : 0 < γ)
include hγ

/-- The reflection exponent is injective in the charge. -/
theorem reflectionExponent_injective :
    Function.Injective (fun α : ℝ => reflectionExponent γ α) := by
  intro x y h
  simp only [reflectionExponent] at h
  grind

/-- Every real punctured neighborhood of a charge is free of reflection poles. -/
theorem reflectionPoleFree_eventually_nhdsNE (x : ℝ) :
    ∀ᶠ y : ℝ in 𝓝[≠] x, ReflectionPoleFree γ y := by
  have hcont : Continuous (reflectionExponent γ) := by
    unfold reflectionExponent
    fun_prop
  have hnear : ∀ᶠ y : ℝ in 𝓝[≠] x,
      |reflectionExponent γ y - reflectionExponent γ x| < 1 / 2 := by
    apply eventually_nhdsWithin_of_eventually_nhds
    exact (hcont.tendsto x).eventually
      (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))
  by_cases hbad : ∃ y₀ : ℝ, y₀ ≠ x ∧
      |reflectionExponent γ y₀ - reflectionExponent γ x| < 1 / 2 ∧ ¬ ReflectionPoleFree γ y₀
  · obtain ⟨y₀, hy₀x, hy₀near, hy₀pole⟩ := hbad
    have hne : ∀ᶠ y : ℝ in 𝓝[≠] x, y ≠ y₀ :=
      eventually_nhdsWithin_of_eventually_nhds (isOpen_ne.mem_nhds hy₀x.symm)
    filter_upwards [hnear, hne] with y hy hyy₀
    intro n hn
    unfold ReflectionPoleFree at hy₀pole
    push Not at hy₀pole
    obtain ⟨n₀, hn₀⟩ := hy₀pole
    have hclose : |((n + 1 : ℕ) : ℝ) - ((n₀ + 1 : ℕ) : ℝ)| < 1 := by
      grind
    have hnn : n = n₀ := by
      have h' : |((n : ℤ) : ℝ) - ((n₀ : ℤ) : ℝ)| < 1 := by
        simp_all
      have h'' : |n - (n₀ : ℤ)| < 1 := by exact_mod_cast h'
      grind
    subst hnn
    exact hyy₀ (reflectionExponent_injective hγ (hn.trans hn₀.symm))
  · push Not at hbad
    filter_upwards [hnear, self_mem_nhdsWithin] with y hy hyx
    simp_all

end

end
section
variable {γ μ α : ℝ}
section
variable (hγ : 0 < γ)
include hγ

/-- Off the poles, the probabilistic coefficient formula is continuous wherever the unit-volume
moment is. -/
theorem continuousAt_reflectionR_formula (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α) {rb : ℝ → ℝ}
    (hrb : ContinuousAt rb α) :
    ContinuousAt (fun y : ℝ => μ ^ (reflectionExponent γ y) *
      Real.Gamma (-(reflectionExponent γ y)) * reflectionExponent γ y * rb y) α := by
  have hp : ContinuousAt (reflectionExponent γ) α := by
    unfold reflectionExponent
    fun_prop
  have hpos := (reflectionExponent_in_subcritical_range γ α hγ hα).2.1
  have hGamma : ContinuousAt (fun y => Real.Gamma (-(reflectionExponent γ y))) α := by
    have hs : ∀ m : ℕ, -(reflectionExponent γ α) ≠ -m := by
      intro m hm
      have hpm : reflectionExponent γ α = m := by linarith
      rcases Nat.eq_zero_or_pos m with h0 | hm0
      · simp_all
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm0
        tauto
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt hp.neg
  have hpow :=
    (Real.continuousAt_const_rpow hμ.ne').comp hp
  fun_prop

/-- Off the poles, the DOZZ coefficient is continuous along real charges. -/
theorem continuousAt_reflectionDOZZ_ofReal (hγ2 : γ < 2)
    (hμ : 0 < μ) (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α) :
    ContinuousAt (fun y : ℝ => reflectionDOZZ γ μ (y : ℂ)) α := by
  have heq : (fun y : ℝ => reflectionDOZZ γ μ y) = fun y : ℝ =>
      ((-(dozzBase γ μ ^ reflectionExponent γ y) *
        (Real.Gamma _ / Real.Gamma _) *
        (Real.Gamma _ / Real.Gamma _) : ℝ) : ℂ) :=
    funext fun y => reflectionDOZZ_ofReal γ μ y hγ hγ2 hμ
  rw [heq]
  apply Complex.continuous_ofReal.continuousAt.comp
  have hp : ContinuousAt (reflectionExponent γ) α := by
    unfold reflectionExponent
    fun_prop
  have ht : ContinuousAt (fun y => γ * (Q γ - y) / 2) α := by fun_prop
  have hpos := (reflectionExponent_in_subcritical_range γ α hγ hα).2.1
  have htα := reflectionGammaArg_mem_Ioo hγ hα
  have hbase := dozzBase_pos hγ hγ2 hμ
  have hG1 : ContinuousAt (fun y => Real.Gamma (-(γ * (Q γ - y) / 2))) α := by
    have hs : ∀ m : ℕ, -(γ * (Q γ - α) / 2) ≠ -m := by
      intro m hm
      have hm' : γ * (Q γ - α) / 2 = m := by linarith
      aesop
    have hneg := ht.neg
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt hneg
  have hG2 : ContinuousAt (fun y => Real.Gamma (γ * (Q γ - y) / 2)) α := by
    have hs : ∀ m : ℕ, γ * (Q γ - α) / 2 ≠ -m := by
      intro m hm
      have : 0 ≤ m := Nat.cast_nonneg m
      linarith
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt ht
  have hG3 : ContinuousAt (fun y => Real.Gamma (-reflectionExponent γ y)) α := by
    have hs : ∀ m : ℕ, -(reflectionExponent γ α) ≠ -m := by
      intro m hm
      have hpm : reflectionExponent γ α = m := by linarith
      rcases Nat.eq_zero_or_pos m with h0 | hm0
      · simp_all
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm0
        tauto
    have hneg := hp.neg
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt hneg
  have hG4 : ContinuousAt (fun y => Real.Gamma (reflectionExponent γ y)) α := by
    have hs : ∀ m : ℕ, reflectionExponent γ α ≠ -m := by
      intro m hm
      have : 0 ≤ m := Nat.cast_nonneg m
      linarith
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt hp
  have hpowb :=
    (Real.continuousAt_const_rpow hbase.ne').comp hp
  have hne2 := (Real.Gamma_pos_of_pos htα.1).ne'
  have hne4 := (Real.Gamma_pos_of_pos hpos).ne'
  exact (hpowb.neg.mul (hG1.div hG2 hne2)).mul (hG3.div hG4 hne4)

end

end

end DOZZ.Proofs

end
