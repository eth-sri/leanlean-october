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
open Glennie Glennie.Compact.Affine20
open Glennie.Compact.NativeQFamilyLedger
open Glennie.Compact.NearbyOrbits
open Glennie.Compact.Sections
open Glennie.Compact.LocalOrbitQuotientR01
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Drop exactly the six single observations. No injectivity on arbitrary arrays. -/
def dropSingles (a : Fin 26 → ℝ) : Fin 20 → ℝ :=
  fun i => a ⟨i.val + 6, by omega⟩

export _root_.Glennie.SubmissionR03 (q20)

theorem q20_eq_of_q26_eq (T S : Triple) (h : q26 T = q26 S) :
    q20 T = q20 S := congrArg dropSingles h

/-- The six removed observations are fixed only under actual-frame hypotheses. -/
theorem q26_eq_of_q20_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a))
    (h : q20 T = q20 S) : q26 T = q26 S := by
  have hs (v : Fin 3) (s : Fin 2) : qSingle T v s = qSingle S v s := by
    rw [qSingle_frame T hT, qSingle_frame S hS]
  have head (i : Fin 6) : q26 T ⟨i, by omega⟩ = q26 S ⟨i, by omega⟩ := by
    fin_cases i <;> simp [q26, hs]
  funext n
  by_cases hn : n.val < 6
  · exact head ⟨n, hn⟩
  · let i : Fin 20 := ⟨n.val-6, by omega⟩
    have e : (⟨i.val+6, by omega⟩ : Fin 26) = n := Fin.ext (by dsimp [i]; omega)
    simpa only [q20, dropSingles, e] using congrFun h i

theorem q20_eq_iff_q26_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ q26 T = q26 S :=
  ⟨q26_eq_of_q20_eq T S hT hS, q20_eq_of_q26_eq T S⟩

/-- Actual ordered frame feasibility is indispensable to this equivalence. -/
theorem q20_eq_iff_ledger54_eq (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a)) :
    q20 T = q20 S ↔ fullLedger T = fullLedger S := by
  exact (q20_eq_iff_q26_eq T S hT hS).trans (q26_eq_iff_ledger54_eq T S hT hS)

/-- Branch representative with both feasible input coordinates certified by d.V. -/
def branchSection (d : LocalData) (b : d.V) (s : Bool) : Triple :=
  (select d (b,s)).1

theorem continuous_section (d : LocalData) (s : Bool) :
    Continuous (fun b : d.V => branchSection d b s) :=
  continuous_subtype_val.comp ((continuous_select d).comp (continuous_id.prodMk continuous_const))

/-- Whole admitted fibres select the branchSection orbit by their actual sign. -/
theorem mem_section_orbit (d : LocalData) (T : Admitted d) :
    T.1 ∈ Glennie.Compact.FlatOrbit.autOrbit (branchSection d (chart d T) (sheet d T)) := select_rel d T

/-- The existing full product-and-trace automorphism preserves the raw native norm. -/
theorem norm_automorphism (g : CompactAutomorphism) (x : Albert) :
    ‖g.equiv x‖ = ‖x‖ := by
  have hsq : ‖g.equiv x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp [native_norm_sq, g.inner_map]
  simp_all

/-- Pi's norm on Triple is the maximum atom norm, using the native raw trace norm. -/
theorem norm_mapAtoms_sub (g : CompactAutomorphism) (T S : Triple) :
    ‖mapAtoms g T - mapAtoms g S‖ = ‖T - S‖ := by
  have hnn (x : Albert) : ‖g.equiv x‖₊ = ‖x‖₊ := by
    apply NNReal.eq
    exact norm_automorphism g x
  simp [Pi.norm_def, Pi.nnnorm_def, mapAtoms, ← map_sub, hnn]

/-- Uniform branchSection recovery on compact feasible chart points, for either sign. -/
theorem compact_section_tolerance (d : LocalData) (K : Set d.V) (hK : IsCompact K)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ η > 0, ∀ b ∈ K, ∀ c ∈ K, ∀ s : Bool,
      dist b c < η → ‖branchSection d b s - branchSection d c s‖ < ζ := by
  have hp := hK.uniformContinuousOn_of_continuous (continuous_section d true).continuousOn
  have hn := hK.uniformContinuousOn_of_continuous (continuous_section d false).continuousOn
  obtain ⟨ηp, hηp, hp⟩ := Metric.uniformContinuousOn_iff.mp hp ζ hζ
  obtain ⟨ηn, hηn, hn⟩ := Metric.uniformContinuousOn_iff.mp hn ζ hζ
  refine ⟨min ηp ηn, lt_min hηp hηn, ?_⟩
  simp_all [dist_eq_norm]

/-- Feasible uncertain chart recovery, modulo an actual simultaneous automorphism.
Both chart points must lie in the compact region; no array projection is supplied. -/
theorem compact_feasible_recovery (d : LocalData) (K : Set d.V) (hK : IsCompact K)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ η > 0, ∀ T : Admitted d, chart d T ∈ K → ∀ b : d.V, b ∈ K →
      dist (chart d T) b < η → ∃ g : CompactAutomorphism,
        ‖T.1 - mapAtoms g (branchSection d b (sheet d T))‖ < ζ := by
  obtain ⟨η, hη, ht⟩ := compact_section_tolerance d K hK ζ hζ
  refine ⟨η, hη, ?_⟩
  intro T hT b hb hdist
  obtain ⟨g, hg⟩ := mem_section_orbit d T
  refine ⟨g, ?_⟩
  rw [← hg, norm_mapAtoms_sub]
  grind

end
end Glennie.Compact.NativeQ20AdapterR01
