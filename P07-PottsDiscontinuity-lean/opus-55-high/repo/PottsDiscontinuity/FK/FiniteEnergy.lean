/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Generalized open bounds: p/(p+(1-p)q) and p; closed bounds: 1-p and 1-p/(p+(1-p)q). -/
module

public import PottsDiscontinuity.FK.SingleEdgeLaw
public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.FK.WiredRemoval
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Measure.Real

public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance finiteEnergyEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
local instance finiteEnergyEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance finiteEnergyRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

section
variable (e : G.edgeSet)
def edgeRemovedBoolEquiv  :
    RemovedConfiguration G ({e} : Configuration G) ≃ Bool where
  toFun B := decide (e ∈ B.val)
  invFun b := if b then ⟨{e}, by simp⟩ else ⟨∅, by simp⟩
  left_inv B := by
    aesop
  right_inv b := by grind

def configurationEdgeStateEquiv  :
    Configuration G ≃ RemainingConfiguration G ({e} : Configuration G) × Bool :=
  (configurationSplitEquiv G ({e} : Configuration G)).trans
    (Equiv.prodCongr (Equiv.refl _) (edgeRemovedBoolEquiv e))
end

omit [Finite V] in
@[simp] theorem configurationEdgeStateEquiv_symm_apply_false (e : G.edgeSet)
    (A : RemainingConfiguration G ({e} : Configuration G)) :
    (configurationEdgeStateEquiv e).symm (A, false) = A.val := by
  simp [configurationEdgeStateEquiv, configurationSplitEquiv_symm_apply,
    edgeRemovedBoolEquiv]

omit [Finite V] in
@[simp] theorem configurationEdgeStateEquiv_symm_apply_true (e : G.edgeSet)
    (A : RemainingConfiguration G ({e} : Configuration G)) :
    (configurationEdgeStateEquiv e).symm (A, true) = insert e A.val := by
  simp [configurationEdgeStateEquiv, configurationSplitEquiv_symm_apply,
    edgeRemovedBoolEquiv]

theorem configurationProbability_edgeState_sum (q : Parameters)
    (ξ : BoundaryCondition V) (e : G.edgeSet) (f : Configuration G → ℝ) :
    (∑ C : Configuration G, configurationProbability G q ξ C * f C) =
      ∑ A : RemainingConfiguration G ({e} : Configuration G),
        (configurationProbability G q ξ A.val * f A.val +
          configurationProbability G q ξ (insert e A.val) * f (insert e A.val)) := by
  rw [← (configurationEdgeStateEquiv e).symm.sum_comp, Fintype.sum_prod_type]
  simp
  apply Finset.sum_congr rfl
  intro A hA
  ring

section
variable (q : Parameters) (ξ : BoundaryCondition V) (s : Set (Configuration G)) {u v : V} (huv : G.Adj u v) (hstable : ∀ A, A ∈ s ↔ A.erase ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ ∈ s)
include huv hstable
/-- For an event invariant under toggling one original edge, its open-edge mass
lies between the FK single-edge conditional weights times its total mass. -/
theorem configurationProbability_edge_finite_energy
     :
    (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) * (measure G q ξ s).toReal ≤
        (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ A})).toReal ∧
      (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ A})).toReal ≤
        edgeParameter q * (measure G q ξ s).toReal := by
  classical
  let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
  let P := configurationProbability G q ξ
  let eventIndicator (t : Set (Configuration G)) :=
    t.indicator (fun _ => (1 : ℝ))
  have habsent (A : RemainingConfiguration G {e}) : e ∉ A.val := by
    intro heA
    exact (Finset.disjoint_left.mp A.property heA) (by simp)
  have hstableInsert (A : RemainingConfiguration G {e}) :
      insert e A.val ∈ s ↔ A.val ∈ s := by
    simpa [e, habsent A] using (hstable (insert e A.val))
  have hbaseIndicator (A : RemainingConfiguration G {e}) :
      eventIndicator s A.val = if A.val ∈ s then 1 else 0 := by
    rfl
  have hinsertIndicator (A : RemainingConfiguration G {e}) :
      eventIndicator s (insert e A.val) = if A.val ∈ s then 1 else 0 := by
    grind [Set.indicator]
  have hmass : (measure G q ξ s).toReal =
      ∑ A : RemainingConfiguration G {e},
        if A.val ∈ s then P A.val + P (insert e A.val) else 0 := by
    rw [measure_toReal_eq_indicator_sum, configurationProbability_edgeState_sum q ξ e (eventIndicator s)]
    apply Finset.sum_congr rfl
    intro A hA
    grind
  have hopen :
      (measure G q ξ (s ∩ {A | e ∈ A})).toReal =
        ∑ A : RemainingConfiguration G {e},
          if A.val ∈ s then P (insert e A.val) else 0 := by
    rw [measure_toReal_eq_indicator_sum, configurationProbability_edgeState_sum q ξ e (eventIndicator (s ∩ {A | e ∈ A}))]
    simp [P, eventIndicator, Set.indicator, habsent, hstableInsert]
  have htermLower (A : RemainingConfiguration G {e}) :
      (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) *
          (if A.val ∈ s then P A.val + P (insert e A.val) else 0) ≤
        (if A.val ∈ s then P (insert e A.val) else 0) := by
    by_cases hA : A.val ∈ s
    · simp only [ite_eq_left hA]
      have hr := configurationProbability_pair_ratio_bounds q ξ A.val huv
        (by grind)
      have hden :=
        add_pos (configurationProbability_pos G q ξ A.val)
          (configurationProbability_pos G q ξ (insert e A.val))
      have h := (le_div_iff₀ hden).mp hr.1
      omega
    · simp [hA]
  have htermUpper (A : RemainingConfiguration G {e}) :
      (if A.val ∈ s then P (insert e A.val) else 0) ≤
        edgeParameter q *
          (if A.val ∈ s then P A.val + P (insert e A.val) else 0) := by
    by_cases hA : A.val ∈ s
    · simp only [ite_eq_left hA]
      have hr := configurationProbability_pair_ratio_bounds q ξ A.val huv
        (by grind)
      have hden :=
        add_pos (configurationProbability_pos G q ξ A.val)
          (configurationProbability_pos G q ξ (insert e A.val))
      have h := (div_le_iff₀ hden).mp hr.2
      omega
    · simp [hA]
  constructor
  · rw [hmass, hopen]
    calc
      (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) *
          (∑ A : RemainingConfiguration G {e},
            if A.val ∈ s then P A.val + P (insert e A.val) else 0) =
        ∑ A : RemainingConfiguration G {e},
          (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) *
            (if A.val ∈ s then P A.val + P (insert e A.val) else 0) := by
              rw [Finset.mul_sum]
      _ ≤ ∑ A : RemainingConfiguration G {e},
          (if A.val ∈ s then P (insert e A.val) else 0) :=
        Finset.sum_le_sum (fun A _ => htermLower A)
  · rw [hmass, hopen]
    calc
      (∑ A : RemainingConfiguration G {e},
          (if A.val ∈ s then P (insert e A.val) else 0) ) ≤
        ∑ A : RemainingConfiguration G {e},
          edgeParameter q *
            (if A.val ∈ s then P A.val + P (insert e A.val) else 0) :=
        Finset.sum_le_sum (fun A _ => htermUpper A)
      _ = edgeParameter q *
          (∑ A : RemainingConfiguration G {e},
            if A.val ∈ s then P A.val + P (insert e A.val) else 0) := by
              rw [Finset.mul_sum]


/-- For an event invariant under toggling one original edge, its closed-edge mass
lies between the FK single-edge conditional weights times its total mass. -/
theorem configurationProbability_edge_finite_energy_closed
     :
    (1 - edgeParameter q) * (measure G q ξ s).toReal ≤
        (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A})).toReal ∧
      (measure G q ξ (s ∩ {A | (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A})).toReal ≤
        (1 - (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val))) * (measure G q ξ s).toReal := by
  let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
  let opened : Set (Configuration G) := {A | e ∈ A}
  have hopen := configurationProbability_edge_finite_energy q ξ s huv hstable
  have hpartition :
      (measure G q ξ (s ∩ opened)).toReal +
        (measure G q ξ (s ∩ {A | e ∉ A})).toReal =
          (measure G q ξ s).toReal := by
    have h := MeasureTheory.measureReal_inter_add_sdiff (μ := measure G q ξ)
      (t := opened) (by simp)
    tauto
  have hopen' :
      (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) * (measure G q ξ s).toReal ≤
        (measure G q ξ (s ∩ opened)).toReal ∧
      (measure G q ξ (s ∩ opened)).toReal ≤
        edgeParameter q * (measure G q ξ s).toReal := by
    omega
  constructor <;> nlinarith [hpartition, hopen'.1, hopen'.2]
end

end
end PottsDiscontinuity.FK
