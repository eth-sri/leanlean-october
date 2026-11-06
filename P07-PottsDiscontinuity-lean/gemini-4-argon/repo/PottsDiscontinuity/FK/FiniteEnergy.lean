/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Generalized open bounds: p/(p+(1-p)q) and p; closed bounds: 1-p and 1-p/(p+(1-p)q). -/
module

public import PottsDiscontinuity.FK.SingleEdgeLaw
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
local instance finiteEnergyRemovedFintype (R : Configuration G) :
    Fintype (RemovedConfiguration G R) := Fintype.ofFinite _

def edgeRemovedBoolEquiv (e : G.edgeSet) :
    RemovedConfiguration G ({e} : Configuration G) ≃ Bool where
  toFun B := decide (e ∈ B.val)
  invFun b := if b then ⟨{e}, by simp⟩ else ⟨∅, by simp⟩
  left_inv B := Subtype.ext <| by
    rcases Finset.subset_singleton_iff.mp B.property with h | h <;> simp [h]
  right_inv b := by cases b <;> simp

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

private theorem configurationProbability_edgeState_sum (q : Parameters)
    (ξ : BoundaryCondition V) (e : G.edgeSet) (f : Configuration G → ℝ) :
    (∑ C : Configuration G, configurationProbability G q ξ C * f C) =
      ∑ A : RemainingConfiguration G ({e} : Configuration G),
        (configurationProbability G q ξ A.val * f A.val +
          configurationProbability G q ξ (insert e A.val) * f (insert e A.val)) := by
  classical
  rw [← (configurationEdgeStateEquiv e).symm.sum_comp, Fintype.sum_prod_type]
  simp only [configurationEdgeStateEquiv_symm_apply_false,
    configurationEdgeStateEquiv_symm_apply_true, Fintype.sum_bool]
  exact Finset.sum_congr rfl fun _ _ => by ring

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
  let P : Configuration G → ℝ := configurationProbability G q ξ
  have habsent (A : RemainingConfiguration G {e}) : e ∉ A.val :=
    fun heA => (Finset.disjoint_left.mp A.property heA) (by simp)
  have hstableInsert (A : RemainingConfiguration G {e}) :
      insert e A.val ∈ s ↔ A.val ∈ s := by
    simpa [e, habsent A] using hstable (insert e A.val)
  have hmass : (measure G q ξ s).toReal =
      ∑ A : RemainingConfiguration G {e},
        if A.val ∈ s then P A.val + P (insert e A.val) else 0 := by
    rw [measure_toReal_eq_indicator_sum,
      configurationProbability_edgeState_sum q ξ e (s.indicator fun _ => (1 : ℝ))]
    exact Finset.sum_congr rfl fun A _ => by
      by_cases hsA : A.val ∈ s <;> simp [P, hstableInsert, hsA]
  have hopen :
      (measure G q ξ (s ∩ {A | e ∈ A})).toReal =
        ∑ A : RemainingConfiguration G {e},
          if A.val ∈ s then P (insert e A.val) else 0 := by
    rw [measure_toReal_eq_indicator_sum,
      configurationProbability_edgeState_sum q ξ e ((s ∩ {A | e ∈ A}).indicator fun _ => (1 : ℝ))]
    simp [P, Set.indicator, habsent, hstableInsert]
  rw [hmass, hopen, Finset.mul_sum, Finset.mul_sum]
  refine ⟨Finset.sum_le_sum fun A _ => ?_, Finset.sum_le_sum fun A _ => ?_⟩ <;>
    by_cases hA : A.val ∈ s <;> simp only [hA, ↓reduceIte, mul_zero, le_refl]
  · exact (le_div_iff₀ (add_pos (configurationProbability_pos G q ξ A.val)
      (configurationProbability_pos G q ξ (insert e A.val)))).mp
      (configurationProbability_pair_ratio_bounds q ξ A.val huv (habsent A)).1
  · exact (div_le_iff₀ (add_pos (configurationProbability_pos G q ξ A.val)
      (configurationProbability_pos G q ξ (insert e A.val)))).mp
      (configurationProbability_pair_ratio_bounds q ξ A.val huv (habsent A)).2

/-- For an event invariant under toggling one original edge, its closed-edge mass
lies between the FK single-edge conditional weights times its total mass. -/
theorem configurationProbability_edge_finite_energy_closed
    (q : Parameters) (ξ : BoundaryCondition V) (s : Set (Configuration G))
    {u v : V} (huv : G.Adj u v)
    (hstable : ∀ A, A ∈ s ↔ A.erase ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ ∈ s) :
    (1 - edgeParameter q) * (measure G q ξ s).toReal ≤
        (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A})).toReal ∧
      (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A})).toReal ≤
        (1 - (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val))) * (measure G q ξ s).toReal := by
  classical
  let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
  let opened : Set (Configuration G) := {A | e ∈ A}
  have hopen := configurationProbability_edge_finite_energy q ξ s huv hstable
  have hpartition :
      (measure G q ξ (s ∩ opened)).toReal +
        (measure G q ξ (s ∩ {A | e ∉ A})).toReal =
          (measure G q ξ s).toReal := by
    rw [show s ∩ {A | e ∉ A} = s \ opened by ext; simp [opened]]
    exact MeasureTheory.measureReal_inter_add_sdiff (μ := measure G q ξ) (s := s)
      (t := opened) (by simp [opened])
  constructor <;> nlinarith [hpartition, hopen.1, hopen.2]

end
end PottsDiscontinuity.FK
