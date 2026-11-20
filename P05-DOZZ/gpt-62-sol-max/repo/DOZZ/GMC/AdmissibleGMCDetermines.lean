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
  let := hU.locallyCompactSpace
  let e := MeasurableEmbedding.subtype_coe hU.measurableSet
  let chart (m₀ : Measure ℂ) := m₀.comap (Subtype.val : U → ℂ)
  have hc (m₀ : Measure ℂ) (hm₀ : ∀ K, IsCompact K → K ⊆ U → m₀ K < ⊤) :
      IsFiniteMeasureOnCompacts (chart m₀) :=
    ⟨fun S hS => by
      change m₀.comap Subtype.val S < ⊤
      rw [e.comap_apply]
      exact hm₀ _ (hS.image continuous_subtype_val) (fun _ ⟨x, _, hx⟩ => hx ▸ x.2)⟩
  let := hc μ hμfin
  let := hc ν hνfin
  have hm (m₀ : Measure ℂ) (hm₀ : m₀ Uᶜ = 0) : (chart m₀).map Subtype.val = m₀ := by
    change (m₀.comap Subtype.val).map Subtype.val = m₀
    rw [e.map_comap, Subtype.range_coe, Measure.restrict_eq_self_of_ae_mem hm₀]
  suffices chart μ = chart ν from (hm μ hμsupp).symm.trans ((congrArg (Measure.map Subtype.val) this).trans
    (hm ν hνsupp))
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  let G := Subtype.val.extend (g : U → ℝ) 0
  have hG : Continuous G :=
    HasCompactSupport.continuous_extend_zero hU g.continuous g.hasCompactSupport'
  have hGc : HasCompactSupport G := g.hasCompactSupport'.extend_zero continuous_subtype_val
  have hGU : tsupport G ⊆ U :=
    g.hasCompactSupport'.tsupport_extend_zero_subset continuous_subtype_val |>.trans (by simp)
  have heval (m₀ : Measure ℂ) (hm₀ : m₀ Uᶜ = 0) :
      (∫ x, G x ∂m₀) = ∫ x, g x ∂chart m₀ := by
    calc
      _ = (∫ x, G x ∂(chart m₀).map Subtype.val) := congrArg (fun ν => ∫ x, G x ∂ν) (hm m₀ hm₀).symm
      _ = _ := by
        rw [integral_map e.measurable.aemeasurable hG.aestronglyMeasurable]
        exact integral_congr_ae (ae_of_all _ fun x => by dsimp only; simp [G])
  rw [← heval μ hμsupp, ← heval ν hνsupp]
  obtain ⟨n, hGK⟩ := hKcofinal (tsupport G) hGc.isCompact hGU
  let K₀ := K n
  let A (m₀ : Measure ℂ) := ∫ x, G x ∂m₀
  let B (m : ℕ) (m₀ : Measure ℂ) := ∫ x, f (n,m) x ∂m₀
  change A μ = A ν
  by_contra hne
  let d := dist (A μ) (A ν)
  let t := μ.real K₀ + ν.real K₀ + 1
  let δ := d / t
  have hd : 0 < d := dist_pos.mpr hne
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨m, happrox⟩ := hdense n ⟨G, hG⟩ hGc hGK δ (div_pos hd ht)
  have hclose (m₀ : Measure ℂ) (hm₀ : m₀ K₀ < ⊤) : dist (B m m₀) (A m₀) ≤ δ * m₀.real K₀ := by
    let : IsFiniteMeasure (m₀.restrict K₀) := ⟨by rwa [Measure.restrict_apply_univ]⟩
    let F := (⟨⟨G, hG⟩, hGc⟩ : C_c(ℂ, ℝ)).toBoundedContinuousFunction
    have hmeas : MeasurableSet K₀ := (hKcompact n).measurableSet
    have hq := boundedContinuousFunction_eq_zero_off_tsupport_subset (f (n,m)) K₀ (hfK n m).2
    have hz : ∀ x, x ∉ K₀ → G x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun hx' => hx (hGK hx'))
    have hi : Integrable G (m₀.restrict K₀) := F.integrable _
    dsimp only [A, B]
    rw [← integral_restrict_eq_integral_of_zero_on_compl m₀ K₀ hmeas _ hq,
      ← integral_restrict_eq_integral_of_zero_on_compl m₀ K₀ hmeas _ hz, dist_eq_norm,
      ← integral_sub ((f (n,m)).integrable _) hi]
    simpa only [Measure.real_def, Measure.restrict_apply_univ] using
      (norm_integral_le_of_norm_le_const (μ := m₀.restrict K₀)
        (ae_of_all _ fun x => (show ‖f (n,m) x - G x‖ ≤ δ from (happrox x).le)))
  have h : d ≤ δ * μ.real K₀ + δ * ν.real K₀ := by
    calc
      d ≤ dist (A μ) (B m μ) + dist (B m μ) (A ν) := dist_triangle ..
      _ = dist (B m μ) (A μ) + dist (B m ν) (A ν) := by
        rw [dist_comm (A μ)]
        exact congrArg (fun a => _ + dist a (A ν)) (hfamily n m)
      _ ≤ _ := add_le_add (hclose μ (hμfin _ (hKcompact n) (hKU n)))
        (hclose ν (hνfin _ (hKcompact n) (hKU n)))
  have hδ := div_pos hd ht
  have he := div_mul_cancel₀ d ht.ne'
  change δ * t = d at he
  dsimp only [t] at he
  linarith

end DOZZ.Proofs
