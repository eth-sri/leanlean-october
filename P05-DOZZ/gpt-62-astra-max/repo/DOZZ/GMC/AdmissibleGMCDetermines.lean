/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.AdmissibleGMCCountableTests
public import DOZZ.GMC.AdmissibleGMCRestriction
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.Algebra.Support

/-! Countable dense compact tests determine locally finite measures carried by an open chart. -/

@[expose] public section

open MeasureTheory Set Topology
open scoped Topology CompactlySupported ENNReal

namespace DOZZ.Proofs

/-- A countable family of locally dense compactly supported tests determines locally finite
measures carried by an open planar chart. -/
theorem admissible_countable_tests_determine_chart_measures
    (U : Set ℂ) (hU : IsOpen U) (μ ν : Measure ℂ)
    (hμsupp : μ Uᶜ = 0) (hνsupp : ν Uᶜ = 0)
    (hμfin : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ∞)
    (hνfin : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ν K < ∞)
    (K : ℕ → Set ℂ)
    (hKcompact : ∀ n, IsCompact (K n)) (hKU : ∀ n, K n ⊆ U)
    (hKcofinal : ∀ L, IsCompact L → L ⊆ U → ∃ n, L ⊆ K n)
    (f : ℕ × ℕ → BoundedContinuousFunction ℂ ℝ)
    (hfK : ∀ n m, HasCompactSupport (f (n, m) : ℂ → ℝ) ∧
      tsupport (f (n, m) : ℂ → ℝ) ⊆ K n)
    (hdense : ∀ n (g : C(ℂ, ℝ)), HasCompactSupport g → tsupport g ⊆ K n →
      ∀ δ : ℝ, 0 < δ → ∃ m, ∀ x, ‖f (n, m) x - g x‖ < δ)
    (hfamily : ∀ n m, ∫ x, f (n, m) x ∂μ = ∫ x, f (n, m) x ∂ν) :
    μ = ν := by
  have : LocallyCompactSpace (↥U) := hU.locallyCompactSpace
  have : SigmaCompactSpace (↥U) := inferInstance
  have : BorelSpace (↥U) := inferInstance
  let μU : Measure (↥U) := μ.comap Subtype.val
  let νU : Measure (↥U) := ν.comap Subtype.val
  let e := MeasurableEmbedding.subtype_coe hU.measurableSet
  have hμUfinite : IsFiniteMeasureOnCompacts μU := by
    constructor
    intro S hS
    rw [e.comap_apply]
    apply hμfin (Subtype.val '' S) (hS.image continuous_subtype_val)
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hνUfinite : IsFiniteMeasureOnCompacts νU := by
    constructor
    intro S hS
    rw [e.comap_apply]
    apply hνfin (Subtype.val '' S) (hS.image continuous_subtype_val)
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have : IsFiniteMeasureOnCompacts μU := hμUfinite
  have : IsFiniteMeasureOnCompacts νU := hνUfinite
  have : μU.Regular := inferInstance
  have : νU.Regular := inferInstance
  have hUintegrals : ∀ g : C_c(↥U, ℝ), ∫ x, g x ∂μU = ∫ x, g x ∂νU := by
    intro g
    let gext  := Subtype.val.extend (g) 0
    have hgextval (x : ↥U) : gext x = g x := by
      simp [gext]
    have hgextCompact  :=
      g.hasCompactSupport'.extend_zero continuous_subtype_val
    have hgextSupport : tsupport gext ⊆ U := by
      exact (g.hasCompactSupport'.tsupport_extend_zero_subset continuous_subtype_val).trans
        (by simp)
    let gC : C(ℂ, ℝ) := ⟨gext, (HasCompactSupport.continuous_extend_zero hU g.continuous g.hasCompactSupport')⟩
    obtain ⟨n, hgnK⟩ := hKcofinal (tsupport gext) hgextCompact.isCompact hgextSupport
    let W : Set (↥U) := Subtype.val ⁻¹' K n
    have hWcompact : IsCompact W := by
      have : CompactSpace (↥(K n)) := isCompact_iff_compactSpace.mp (hKcompact n)
      let j : ↥(K n) → ↥U := fun x => ⟨x.1, hKU n x.2⟩
      have hrange : Set.range j = W := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact y.property
        · intro hx
          refine ⟨⟨x.1, hx⟩, ?_⟩
          exact Subtype.ext rfl
      rw [← hrange]
      refine isCompact_range ?_
      fun_prop
    have hWμ : μU W < ∞ := by
      rw [e.comap_apply]
      have himage : Subtype.val '' W = K n := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hKU n hx⟩, hx, rfl⟩
      rw [himage]
      exact hμfin (K n) (hKcompact n) (hKU n)
    have hWν : νU W < ∞ := by
      rw [e.comap_apply]
      have himage : Subtype.val '' W = K n := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hKU n hx⟩, hx, rfl⟩
      rw [himage]
      exact hνfin (K n) (hKcompact n) (hKU n)
    have hWmeas : MeasurableSet W := by
      change MeasurableSet (Subtype.val ⁻¹' K n)
      exact (hKcompact n).isClosed.measurableSet.preimage continuous_subtype_val.measurable
    let gCc : C_c(ℂ, ℝ) := ⟨gC, hgextCompact⟩
    let qg  := gCc.toBoundedContinuousFunction
    have hlift (lam : Measure ℂ) (lamU : Measure (↥U))
        (hlam : lamU = lam.comap Subtype.val) (q : BoundedContinuousFunction ℂ ℝ)
        (hq : tsupport (q) ⊆ U) :
        ∫ x : ↥U, q x ∂lamU = ∫ x, q x ∂lam := by
      rw [hlam, integral_subtype_comap hU.measurableSet]
      exact integral_restrict_eq_integral_of_zero_on_compl lam U hU.measurableSet q
        (boundedContinuousFunction_eq_zero_off_tsupport_subset q U hq)
    have hfamilyU (m : ℕ) :
        ∫ x : ↥U, f (n, m) x ∂μU = ∫ x : ↥U, f (n, m) x ∂νU := by
      calc
        _ = ∫ x, f (n, m) x ∂μ := (hlift μ μU rfl (f (n, m)) ((hfK n m).2.trans (hKU n)))
        _ = ∫ x, f (n, m) x ∂ν := hfamily n m
        _ = _ := (hlift ν νU rfl (f (n, m)) ((hfK n m).2.trans (hKU n))).symm
    have hclose (lamU : Measure (↥U)) (hlamfin : IsFiniteMeasureOnCompacts lamU)
        (hlamW : lamU W < ∞) (q : BoundedContinuousFunction ℂ ℝ)
        (hqK : tsupport (q) ⊆ K n) (δ : ℝ) (hδ : 0 < δ)
        (happrox : ∀ x, ‖q x - gC x‖ < δ) :
        ‖∫ x : ↥U, g x ∂lamU - ∫ x : ↥U, q x ∂lamU‖ ≤ δ * lamU.real W := by
      have : IsFiniteMeasureOnCompacts lamU := hlamfin
      have hgint : Integrable g lamU :=
        g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport'
      have hqUzero : ∀ x, x ∉ W → q x = 0 := by
        intro x hx
        have hxK : (x : ℂ) ∉ K n := hx
        exact image_eq_zero_of_notMem_tsupport (fun hs => hxK (hqK hs))
      have hqint : Integrable (fun x : ↥U => q x) lamU :=
        (q.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hWcompact
            (Function.support_subset_iff'.mpr fun x hx => hqUzero x hx))
      let d  := fun x => g x - q x
      have hdcont : Continuous d := by fun_prop
      have hdzero : ∀ x, x ∉ W → d x = 0 := by
        intro x hxW
        have hxK  := hxW
        have hgzero : g x = 0 := by
          rw [← hgextval x]
          exact image_eq_zero_of_notMem_tsupport (fun hs => hxK (hgnK hs))
        simp [d, hgzero, (image_eq_zero_of_notMem_tsupport (fun hs => hxK (hqK hs)))]
      have hmono := integral_mono (hdcont.integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hWcompact
        (Function.support_subset_iff'.mpr hdzero))).norm ((integrableOn_const hlamW.ne).integrable_indicator hWcompact.measurableSet) (by
        intro x
        by_cases hx : x ∈ W
        · simp [Set.indicator, hx, d]
          have h := happrox x.1
          have hcg : gC x.1 = g x := by simpa [gC] using hgextval x
          rw [hcg] at h
          rw [abs_sub_comm]
          exact h.le
        · have hzero := hdzero x hx
          simp [Set.indicator, hx, hzero])
      calc
        _ = ‖∫ x : ↥U, d x ∂lamU‖ := by
          rw [integral_sub hgint hqint]
        _ ≤ ∫ x : ↥U, ‖d x‖ ∂lamU := norm_integral_le_integral_norm _
        _ ≤ ∫ x : ↥U, W.indicator (fun _ : ↥U => δ) x ∂lamU := hmono
        _ = _ := by
          rw [integral_indicator_const δ hWmeas]
          simp [smul_eq_mul, mul_comm]
    have hpoint (lamU : Measure (↥U)) (hlamfin : IsFiniteMeasureOnCompacts lamU)
        (hlamW : lamU W < ∞) (δ : ℝ) (hδ : 0 < δ) :
        ∀ m, (∀ x, ‖f (n, m) x - gC x‖ < δ) →
          ‖∫ x : ↥U, g x ∂lamU - ∫ x : ↥U, f (n, m) x ∂lamU‖ ≤ δ * lamU.real W := by
      intro m happrox
      exact hclose lamU hlamfin hlamW (f (n, m)) (hfK n m).2 δ hδ happrox
    let Mμ : ℝ := μU.real W
    let Mν : ℝ := νU.real W
    by_contra hne
    have hD  := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    let a := (∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, g x ∂νU
    let δ : ℝ := ‖a‖ /
      (2 * (Mμ + Mν + 1))
    have hδ : 0 < δ := by positivity
    obtain ⟨m, happrox⟩ := hdense n gC hgextCompact hgnK δ hδ
    have hμclose :
        ‖∫ x : ↥U, g x ∂μU - ∫ x : ↥U, f (n, m) x ∂μU‖ ≤ δ * Mμ := by
      simpa [Mμ] using hpoint μU hμUfinite hWμ δ hδ m happrox
    have hνclose :
        ‖∫ x : ↥U, g x ∂νU - ∫ x : ↥U, f (n, m) x ∂νU‖ ≤ δ * Mν := by
      simpa [Mν] using hpoint νU hνUfinite hWν δ hδ m happrox
    have hdecomp :
        a =
          ((∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, f (n, m) x ∂μU) +
            ((∫ x : ↥U, f (n, m) x ∂νU) - ∫ x : ↥U, g x ∂νU) := by
      rw [hfamilyU m]
      ring
    have hDle :
        ‖a‖ ≤ δ * Mμ + δ * Mν := by
      rw [hdecomp]
      calc
        _ ≤
            ‖(∫ x : ↥U, g x ∂μU) - ∫ x : ↥U, f (n, m) x ∂μU‖ +
              ‖(∫ x : ↥U, f (n, m) x ∂νU) - ∫ x : ↥U, g x ∂νU‖ := norm_add_le _ _
        _ ≤ _ := by
          apply add_le_add hμclose
          simpa [norm_sub_rev] using hνclose
    refine (not_lt_of_ge hDle) ?_
    calc
      δ * Mμ + δ * Mν =
          ‖a‖ *
            ((Mμ + Mν) / (2 * (Mμ + Mν + 1))) := by
        ring
      _ <
        ‖a‖ * 1 :=
        mul_lt_mul_of_pos_left (by
          apply (div_lt_one (by positivity)).2
          nlinarith) hD
      _ = ‖a‖ := by ring
  have hμae  := hμsupp
  have hνae  := hνsupp
  have hrange : Set.range (Subtype.val : ↥U → ℂ) = U := by
    ext x
    constructor
    · simp
    · simp
  have hmapμ : μU.map Subtype.val = μ.restrict U := by
    rw [e.map_comap μ, hrange]
  have hmapν : νU.map Subtype.val = ν.restrict U := by
    rw [e.map_comap ν, hrange]
  rw [(Measure.restrict_eq_self_of_ae_mem hμae).symm, hmapμ.symm, congrArg (fun lam : Measure (↥U) => lam.map Subtype.val) <|
      Measure.ext_of_integral_eq_on_compactlySupported hUintegrals, hmapν, Measure.restrict_eq_self_of_ae_mem hνae]


end DOZZ.Proofs
