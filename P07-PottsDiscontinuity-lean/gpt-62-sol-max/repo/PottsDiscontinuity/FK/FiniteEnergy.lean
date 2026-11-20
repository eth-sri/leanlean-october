/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Generalized open bounds: p/(p+(1-p)q) and p; closed bounds: 1-p and 1-p/(p+(1-p)q). -/
module

public import PottsDiscontinuity.FK.SingleEdgeLaw
public import PottsDiscontinuity.Infra.PairedMass
public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.FK.WiredRemoval
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance finiteEnergyEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
local instance finiteEnergyEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance finiteEnergyRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

def edgeRemovedBoolEquiv (e : G.edgeSet) :
    RemovedConfiguration G ({e} : Configuration G) ≃ Bool where
  toFun B := decide (e ∈ B.val)
  invFun b := if b then ⟨{e}, by simp⟩ else ⟨∅, by simp⟩
  left_inv B := by
    aesop
  right_inv b := by grind

def configurationEdgeStateEquiv (e : G.edgeSet) :
    Configuration G ≃ RemainingConfiguration G ({e} : Configuration G) × Bool :=
  (configurationSplitEquiv G ({e} : Configuration G)).trans
    (Equiv.prodCongr (Equiv.refl _) (edgeRemovedBoolEquiv e))

omit [Finite V] in
@[simp] private theorem configurationEdgeStateEquiv_symm_apply_false (e : G.edgeSet)
    (A : RemainingConfiguration G ({e} : Configuration G)) :
    (configurationEdgeStateEquiv e).symm (A, false) = A.val := by
  simp [configurationEdgeStateEquiv, configurationSplitEquiv_symm_apply,
    edgeRemovedBoolEquiv]

omit [Finite V] in
@[simp] private theorem configurationEdgeStateEquiv_symm_apply_true (e : G.edgeSet)
    (A : RemainingConfiguration G ({e} : Configuration G)) :
    (configurationEdgeStateEquiv e).symm (A, true) = insert e A.val := by
  simp [configurationEdgeStateEquiv, configurationSplitEquiv_symm_apply,
    edgeRemovedBoolEquiv]

/-- For an event invariant under toggling one original edge, its open-edge mass
lies between the FK single-edge conditional weights times its total mass. -/
theorem configurationProbability_edge_finite_energy
    (q : Parameters) (ξ : BoundaryCondition V) (s : Set (Configuration G))
    {u v : V} (huv : G.Adj u v)
    (hstable : ∀ A, A ∈ s ↔ A.erase ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ ∈ s) :
    (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) * (measure G q ξ s).toReal ≤
        (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ A})).toReal ∧
      (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ A})).toReal ≤
        edgeParameter q * (measure G q ξ s).toReal := by
  classical
  let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
  let P := configurationProbability G q ξ
  have habsent (A : RemainingConfiguration G {e}) : e ∉ A.val := by
    intro he
    exact (Finset.disjoint_left.mp A.property he) (by simp)
  have hs (A : RemainingConfiguration G {e}) : insert e A.val ∈ s ↔ A.val ∈ s := by
    simpa [e, habsent A] using hstable (insert e A.val)
  simp only [measure_toReal_eq_indicator_sum, ← Set.indicator_mul_right, mul_one]
  apply pairedMass_bounds (configurationEdgeStateEquiv e) P s {A | e ∈ A} true
  · simpa only [configurationEdgeStateEquiv_symm_apply_false,
      configurationEdgeStateEquiv_symm_apply_true] using hs
  · intro A i
    cases i <;> simp [habsent]
  · intro A
    simp only [configurationEdgeStateEquiv_symm_apply_false, configurationEdgeStateEquiv_symm_apply_true]
    have h := configurationProbability_pair_ratio_bounds q ξ A.val huv (habsent A)
    have hden := add_pos (configurationProbability_pos G q ξ A.val)
      (configurationProbability_pos G q ξ (insert e A.val))
    exact ⟨(le_div_iff₀ hden).mp h.1, (div_le_iff₀ hden).mp h.2⟩

/-- Prescribing a common edge state costs one finite-energy factor per edge. -/
theorem measure_prescribed_edges_lower_bound (q : Parameters) (ξ : BoundaryCondition V)
    (b : Bool) (s : Configuration G) :
    (if b then edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)
      else 1 - edgeParameter q) ^ s.card ≤
      (measure G q ξ {A | ∀ e ∈ s, (e ∈ A ↔ b = true)}).toReal := by
  classical
  let c := if b then edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)
    else 1 - edgeParameter q
  have hc : 0 ≤ c := by
    cases b
    · exact (one_sub_edgeParameter_pos q).le
    · exact div_nonneg (edgeParameter_pos q).le (edge_conditional_denominator_pos q).le
  change c ^ s.card ≤ _
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    obtain ⟨u,v,huv,rfl⟩ : ∃ u v, ∃ h : G.Adj u v, e = ⟨s(u,v), G.mem_edgeSet.mpr h⟩ := by
      rcases e with ⟨e, h⟩
      induction e using Sym2.inductionOn with
      | hf u v => exact ⟨u,v,G.mem_edgeSet.mp h,rfl⟩
    let e : G.edgeSet := ⟨s(u,v), G.mem_edgeSet.mpr huv⟩
    let T : Set (Configuration G) := {A | ∀ f ∈ s, (f ∈ A ↔ b = true)}
    have hs : ∀ A, A ∈ T ↔ A.erase e ∈ T := by
      simp only [T, Set.mem_ofPred_eq, Finset.mem_erase]
      grind
    have hf := configurationProbability_edge_finite_energy q ξ T huv hs
    rw [Finset.card_insert_of_notMem he, pow_succ, mul_comm]
    refine (mul_le_mul_of_nonneg_left ih hc).trans ?_
    simp only [Finset.forall_mem_insert, Set.ofPred_and]
    rw [Set.inter_comm]
    cases b
    · have hpart : (measure G q ξ (T ∩ {A | e ∈ A})).toReal +
          (measure G q ξ (T ∩ {A | e ∉ A})).toReal = (measure G q ξ T).toReal :=
        MeasureTheory.measureReal_inter_add_sdiff (t := {A | e ∈ A}) (by trivial)
      have h : (1 - edgeParameter q) * (measure G q ξ T).toReal ≤
          (measure G q ξ (T ∩ {A | e ∉ A})).toReal := by linarith [hf.2]
      simpa only [c, T, Bool.false_eq_true, iff_false, ↓reduceIte] using h
    · simpa only [c, T, iff_true, ↓reduceIte] using hf.1

end
end PottsDiscontinuity.FK
