/- Q20 and compact feasible recovery. -/
module
public import Glennie.Compact.NativeQFamilyLedger
public import Glennie.Compact.LocalOrbitQuotientR01
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact

@[expose] public section
namespace Glennie.Compact.NativeQ20AdapterR01
noncomputable section
open Glennie.Compact.Affine20
open Glennie.Compact.NativeQFamilyLedger
open Glennie.Compact.NearbyOrbits
open Glennie.Compact.Sections
open Glennie.Compact.LocalOrbitQuotientR01

/-- Drop exactly the six single observations. No injectivity on arbitrary arrays. -/
def dropSingles (a : Fin 26 → ℝ) : Fin 20 → ℝ :=
  fun i => a ⟨i.val + 6, by omega⟩

/-- The twelve pair values and eight triple values, in inherited script order. -/
def q20 (T : Triple) : Fin 20 → ℝ := dropSingles (q26 T)

/-- The six removed observations are fixed only under actual-frame hypotheses. -/
theorem q26_eq_of_q20_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a))
    (h : q20 T = q20 S) : q26 T = q26 S := by simp_all [funext_iff, Fin.forall_fin_succ, q20, dropSingles, q26, qSingle_frame]

/-- Actual ordered frame feasibility is indispensable to this equivalence. -/
theorem q20_eq_iff_ledger54_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ ledger54 T = ledger54 S :=
  (⟨q26_eq_of_q20_eq T S hT hS, congrArg dropSingles⟩ : _ ↔ _).trans (q26_eq_iff_ledger54_eq T S hT hS)

/-- Branch representative with both feasible input coordinates certified by d.V. -/
def branchSection (d : LocalData) (b : d.V) (s : Bool) : Triple :=
  if s then d.pos b.1 else d.neg b.1

theorem continuous_section (d : LocalData) (s : Bool) :
    Continuous (fun b => branchSection d b s) := by
  cases s
  exacts [d.contNeg.domRestrict, d.contPos.domRestrict]

/-- Whole admitted fibres select the branchSection orbit by their actual sign. -/
theorem mem_section_orbit (d : LocalData) (T : Admitted d) :
    T.1 ∈ Glennie.Compact.FlatOrbit.autOrbit (branchSection d (chart d T) (sheet d T)) := by
  cases hs : sheet d T
  · simpa [branchSection, hs] using
      mem_neg_of_phi_neg d T ((sheet_false_iff d T).1 hs)
  · simpa [branchSection, hs] using
      mem_pos_of_phi_pos d T ((sheet_true_iff d T).1 hs)

/-- The existing full product-and-trace automorphism preserves the raw native norm. -/
theorem norm_automorphism (g : CompactAutomorphism) (x : Albert) :
    ‖g.equiv x‖ = ‖x‖ := by
  have hsq : ‖g.equiv x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [native_norm_sq, native_norm_sq, g.inner_map]
  nlinarith [norm_nonneg (g.equiv x), norm_nonneg x]

/-- Pi's norm on Triple is the maximum atom norm, using the native raw trace norm. -/
theorem norm_mapAtoms_sub (g : CompactAutomorphism) (T S : Triple) :
    ‖mapAtoms g T - mapAtoms g S‖ = ‖T - S‖ := by
  have hnn (x : Albert) : ‖g.equiv x‖₊ = ‖x‖₊ := by
    apply NNReal.eq
    exact norm_automorphism g x
  simp [Pi.norm_def, Pi.nnnorm_def, mapAtoms, Pi.sub_apply, ← map_sub, hnn]

/-- Feasible uncertain chart recovery, modulo an actual simultaneous automorphism.
Both chart points must lie in the compact region; no array projection is supplied. -/
theorem compact_feasible_recovery (d : LocalData) (K : Set d.V) (hK : IsCompact K)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ η > 0, ∀ T : Admitted d, chart d T ∈ K → ∀ b : d.V, b ∈ K →
      dist (chart d T) b < η → ∃ g : CompactAutomorphism,
        ‖T.1 - mapAtoms g (branchSection d b (sheet d T))‖ < ζ := by
  have hu (s : Bool) := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (continuous_section d s).continuousOn) ζ hζ
  obtain ⟨ηp, hηp, hp⟩ := hu true
  obtain ⟨ηn, hηn, hn⟩ := hu false
  refine ⟨min ηp ηn, lt_min hηp hηn, fun T hT b hb hdist => ?_⟩
  obtain ⟨g, hg⟩ := mem_section_orbit d T
  refine ⟨g, ?_⟩
  rw [← hg, norm_mapAtoms_sub, ← dist_eq_norm]
  cases sheet d T
  · simp_all
  · simp_all

/-- The compact response margin covers every actual fibre member.
No equality of the two branch magnitudes is assumed. -/
theorem compact_response_margin (d : LocalData) (K : Set d.V) (hK : IsCompact K) :
    ∃ m > 0, ∀ T : Admitted d, chart d T ∈ K → m ≤ |phiOf T.1| := by
  let fPos := fun b => |(phiOf ∘ d.V.domRestrict d.pos) b|
  let fNeg := fun b => |(phiOf ∘ d.V.domRestrict d.neg) b|
  have hcPos := (continuous_phiOf.comp d.contPos.domRestrict).abs
  have hcNeg := (continuous_phiOf.comp d.contNeg.domRestrict).abs
  have hp0 : ∀ b ∈ K, 0 < fPos b := by
    intro b _
    simpa [fPos, Function.comp_apply, Set.domRestrict_apply] using
      (abs_pos.mpr (ne_of_gt (d.phiPos b.1 b.2)))
  have hn0 : ∀ b ∈ K, 0 < fNeg b := by
    intro b _
    simpa [fNeg, Function.comp_apply, Set.domRestrict_apply] using
      (abs_pos.mpr (ne_of_lt (d.phiNeg b.1 b.2)))
  obtain ⟨mp, hmp, hp⟩ := hK.exists_forall_le' hcPos.continuousOn hp0
  obtain ⟨mn, hmn, hn⟩ := hK.exists_forall_le' hcNeg.continuousOn hn0
  refine ⟨min mp mn, lt_min hmp hmn, ?_⟩
  intro T hT
  have heq := phiOf_eq_of_mem_autOrbit (mem_section_orbit d T)
  rw [heq]
  cases hs : sheet d T
  · have h := (min_le_right mp mn).trans (hn (chart d T) hT)
    simpa [branchSection, fNeg] using h
  · have h := (min_le_left mp mn).trans (hp (chart d T) hT)
    simpa [branchSection, fPos] using h

end
end Glennie.Compact.NativeQ20AdapterR01
