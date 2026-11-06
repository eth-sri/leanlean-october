/- Q20 and compact feasible recovery. -/
module
public import Mathlib.Tactic.IntervalCases
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
/-- Drop exactly the six single observations. No injectivity on arbitrary arrays. -/
def dropSingles (a : Fin 26 → ℝ) : Fin 20 → ℝ :=
  fun i => a ⟨i.val + 6, by omega⟩

/-- The twelve pair values and eight triple values, in inherited script order. -/
def q20 (T : Triple) : Fin 20 → ℝ := dropSingles (q26 T)

theorem q20_eq_of_q26_eq (T S : Triple) (h : q26 T = q26 S) :
    q20 T = q20 S := congrArg dropSingles h

variable (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a))

include T S hT hS in
/-- The six removed observations are fixed only under actual-frame hypotheses. -/
theorem q26_eq_of_q20_eq
    (h : q20 T = q20 S) : q26 T = q26 S := by
  have hs (v : Fin 3) (s : Fin 2) : qSingle T v s = qSingle S v s := by
    rw [qSingle_frame T hT, qSingle_frame S hS]
  funext n
  rcases n with ⟨n, hlt⟩
  by_cases hn : n < 6
  · interval_cases n <;> simp [q26, Glennie.SubmissionR04Intrinsic.Local.q26, hs]
  · have hidx : (⟨n - 6 + 6, by omega⟩ : Fin 26) = ⟨n, hlt⟩ := by
      apply Fin.ext
      dsimp
      omega
    simpa only [q20, dropSingles, hidx] using congrFun h ⟨n - 6, by omega⟩

include T S hT hS in
theorem q20_eq_iff_q26_eq  :
    q20 T = q20 S ↔ q26 T = q26 S :=
  ⟨q26_eq_of_q20_eq T S hT hS, q20_eq_of_q26_eq T S⟩

include T S hT hS in
/-- Actual ordered frame feasibility is indispensable to this equivalence. -/
theorem q20_eq_iff_ledger54_eq  :
    q20 T = q20 S ↔ ledger54 T = ledger54 S :=
  (q20_eq_iff_q26_eq T S hT hS).trans (q26_eq_iff_ledger54_eq T S hT hS)

/-- Branch representative with both feasible input coordinates certified by d.V. -/
def branchSection (d : LocalData) (b : d.V) (s : Bool) : Triple :=
  (sectionPoint d b s).1

theorem continuous_section (d : LocalData) (s : Bool) :
    Continuous (fun b : d.V => branchSection d b s) :=
  continuous_subtype_val.comp (continuous_sectionPoint d s)

/-- Every admitted triple lies in its invariant's representative orbit. -/
theorem mem_section_orbit (d : LocalData) (T : Admitted d) :
    T.1 ∈ Glennie.Compact.FlatOrbit.autOrbit (branchSection d (chart d T) (sheet d T)) :=
  Quotient.exact (inverse_forward d (Quotient.mk' T))

/-- Pi's norm on Triple is the maximum atom norm, using the native raw trace norm. -/
theorem norm_mapAtoms_sub (g : CompactAutomorphism) (T S : Triple) :
    ‖mapAtoms g T - mapAtoms g S‖ = ‖T - S‖ := by
  have hnn (x : Albert) : ‖g.equiv x‖₊ = ‖x‖₊ := by
    apply NNReal.eq
    exact g.norm_map x
  simp only [Pi.norm_def, Pi.nnnorm_def, mapAtoms, Pi.sub_apply, ← map_sub, hnn]

/-- Uniform branchSection recovery on compact feasible chart points, for either sign. -/
theorem compact_section_tolerance (d : LocalData) (K : Set d.V) (hK : IsCompact K)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ η > 0, ∀ b ∈ K, ∀ c ∈ K, ∀ s : Bool,
      dist b c < η → ‖branchSection d b s - branchSection d c s‖ < ζ := by
  let f : d.V → (Bool → Triple) := fun b s => branchSection d b s
  have hc : Continuous f := by
    apply continuous_pi
    exact continuous_section d
  have hu : UniformContinuousOn f K := hK.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuousOn_iff.mp hu ζ hζ
  refine ⟨η, hη, ?_⟩
  intro b hb c hc s hbc
  have hlt : ‖f b - f c‖ < ζ := by simpa only [dist_eq_norm] using h b hb c hc hbc
  exact (norm_le_pi_norm (f b - f c) s).trans_lt hlt

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
  exact ht (chart d T) hT b hb (sheet d T) hdist

/-- The compact response margin covers every actual fibre member.
No equality of the two branch magnitudes is assumed. -/
theorem compact_response_margin (d : LocalData) (K : Set d.V) (hK : IsCompact K) :
    ∃ m > 0, ∀ T : Admitted d, chart d T ∈ K → m ≤ |phiOf T.1| := by
  let f : Bool → d.V → ℝ := fun s b => |phiOf (branchSection d b s)|
  have hc (s : Bool) : Continuous (f s) := by
    simpa only [f, Function.comp_def] using
      (continuous_phiOf.comp (continuous_section d s)).abs
  have hp (s : Bool) (b : d.V) : 0 < f s b := by
    cases s
    · exact abs_pos.mpr (ne_of_lt (d.phiNeg b.1 b.2))
    · exact abs_pos.mpr (ne_of_gt (d.phiPos b.1 b.2))
  obtain ⟨m, hm, h⟩ := hK.exists_forall_le' ((hc false).min (hc true)).continuousOn
    (fun b _ => lt_min (hp false b) (hp true b))
  refine ⟨m, hm, ?_⟩
  intro T hT
  rw [phiOf_eq_of_mem_autOrbit (mem_section_orbit d T)]
  have hb := le_min_iff.mp (h (chart d T) hT)
  cases sheet d T
  · exact hb.1
  · exact hb.2

end
end Glennie.Compact.NativeQ20AdapterR01
