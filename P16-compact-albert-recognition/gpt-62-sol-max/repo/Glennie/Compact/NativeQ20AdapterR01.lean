/- Q20 and compact feasible recovery. -/
module
public import Glennie.Compact.NativeQFamilyLedger
public import Glennie.Compact.LocalOrbitQuotientR01
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact
@[expose] public section

namespace Glennie.SubmissionR03
noncomputable section
open Glennie.Compact.Affine20

/-- Q20 is the final twenty Q26 readings; the first six are fixed on actual frames. -/
def q20 (T : Triple) : Fin 20 → ℝ :=
  fun i => q26 T ⟨i.val + 6, Nat.add_lt_add_right i.2 6⟩

end
end Glennie.SubmissionR03

namespace Glennie.Compact.NativeQ20AdapterR01
noncomputable section
open Glennie Glennie.Compact.Affine20
open Glennie.Compact.NativeQFamilyLedger
open Glennie.Compact.NearbyOrbits
open Glennie.Compact.Sections
open Glennie.Compact.LocalOrbitQuotientR01 Glennie.Compact.NearbyOrbitsClosed
set_option autoImplicit false
set_option maxHeartbeats 2000000

export Glennie.SubmissionR03 (q20)

theorem q20_eq_iff_q26_eq (T S : Triple) (hT : IsFrameTriple T)
    (hS : IsFrameTriple S) : q20 T = q20 S ↔ q26 T = q26 S := by
  refine ⟨fun h => ?_, congrArg (fun w => w ∘ (Fin.addNat · 6))⟩
  funext n
  refine Fin.addCases (m := 6) (n := 20) (motive := fun n => q26 T n = q26 S n) ?_ ?_ n
  · intro i
    fin_cases i <;> simp [q26, qSingle_frame T hT, qSingle_frame S hS]
  · intro i
    simpa [q20, Fin.natAdd, Nat.add_comm] using congrFun h i

/-- Actual ordered frame feasibility is indispensable to this equivalence. -/
theorem _root_.Glennie.SubmissionR03.q20_eq_iff_fullLedger_eq (T S : Triple)
    (hT : IsFrameTriple T) (hS : IsFrameTriple S) :
    q20 T = q20 S ↔ SubmissionR03.fullLedger T = SubmissionR03.fullLedger S :=
  (q20_eq_iff_q26_eq T S hT hS).trans (SubmissionR03.q26_eq_iff_fullLedger_eq T S hT hS)

/-- Branch representative with both feasible input coordinates certified by d.V. -/
abbrev branchSection (d : LocalData) (b : d.V) (s : Bool) : Triple := (branch d b s).1

@[simp] theorem branchSection_apply (d : LocalData) (b : d.V) (s : Bool) :
    branchSection d b s = if s then d.pos b else d.neg b := by cases s <;> rfl

theorem continuous_section (d : LocalData) (s : Bool) : Continuous (fun b => branchSection d b s) :=
  (continuous_branch d s).subtype_val

theorem admitted_mem_branch (d : LocalData) (T : Admitted d) :
    T.1 ∈ Glennie.Compact.FlatOrbit.autOrbit (branchSection d (chart d T) (sheet d T)) :=
  branch_rel d T

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
  have hc : Continuous (fun b : d.V => branchSection d b) := continuous_pi (continuous_section d)
  obtain ⟨η,hη,H⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hc.continuousOn) ζ hζ
  refine ⟨η, hη, fun b hb c hc s hbc => ?_⟩
  simpa only [dist_eq_norm, Pi.sub_apply] using
    (norm_le_pi_norm (branchSection d b - branchSection d c) s).trans_lt
      (by simpa only [dist_eq_norm] using H b hb c hc hbc)

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
  obtain ⟨g, hg⟩ := admitted_mem_branch d T
  refine ⟨g, ?_⟩
  rw [← hg, norm_mapAtoms_sub]
  exact ht (chart d T) hT b hb (sheet d T) hdist

end
end Glennie.Compact.NativeQ20AdapterR01
