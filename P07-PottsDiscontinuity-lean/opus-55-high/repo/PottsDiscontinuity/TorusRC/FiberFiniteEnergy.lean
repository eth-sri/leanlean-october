module

public import PottsDiscontinuity.TorusRC.CylinderFiberComparison
public import PottsDiscontinuity.FK.FiniteEnergy

/-! # Finite-energy factors for prescribed retained open edges -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open MeasureTheory

variable {V : Type*} [Finite V] (G : SimpleGraph V)

noncomputable local instance fiberEnergyEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
noncomputable local instance fiberEnergyEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

noncomputable section

section
variable (θ : FK.Parameters)
/-- The FK lower single-edge opening probability. -/
def fkOpenEnergy  : ℝ :=
  FK.edgeParameter θ / (FK.edgeParameter θ + (1 - FK.edgeParameter θ) * θ.val)

theorem fkOpenEnergy_pos  : 0 < fkOpenEnergy θ :=
  div_pos (FK.edgeParameter_pos θ) (FK.edge_conditional_denominator_pos θ)

theorem fkOpenEnergy_le_one  : fkOpenEnergy θ ≤ 1 :=
  (FK.lower_edge_conditional_le_parameter θ).trans
    (by have h := FK.one_sub_edgeParameter_pos θ; linarith)
end

section
variable (θ : FK.Parameters) (ξ : FK.BoundaryCondition V) (s : FK.Configuration G)
/-- Prescribing finitely many original edges open costs at most one lower
single-edge factor per edge, for every boundary condition. -/
theorem fk_allOpen_probability_ge  :
    fkOpenEnergy θ ^ s.card ≤ (FK.measure G θ ξ {A | s ⊆ A}).toReal := by
  have hc0 :=
    div_nonneg (FK.edgeParameter_pos θ).le (FK.edge_conditional_denominator_pos θ).le
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s hes ih =>
    have hrepr : ∃ u v : V, ∃ huv : G.Adj u v,
        e = ⟨s(u,v), G.mem_edgeSet.mpr huv⟩ := by
      obtain ⟨uv, huv⟩ := e
      induction uv using Sym2.inductionOn with
      | hf u v => tauto
    obtain ⟨u,v,huv,rfl⟩ := hrepr
    let e : G.edgeSet := ⟨s(u,v), G.mem_edgeSet.mpr huv⟩
    have hstable : ∀ A : FK.Configuration G, s ⊆ A ↔ s ⊆ A.erase e := by
      grind
    have henergy := (FK.configurationProbability_edge_finite_energy θ ξ
      {A | s ⊆ A} huv hstable).1
    have hevent : ({A : FK.Configuration G | s ⊆ A} ∩ {A | e ∈ A}) =
        {A | insert e s ⊆ A} := by
      grind
    rw [hevent] at henergy
    rw [Finset.card_insert_of_notMem hes, pow_succ, mul_comm]
    exact (mul_le_mul_of_nonneg_left ih hc0).trans henergy

/-- Expectation form of the finite-set opening bound. -/
theorem fk_allOpen_eventProbability_ge  :
    fkOpenEnergy θ ^ s.card ≤ torusRCFiberEventProbability (FK.law G θ ξ) {A | s ⊆ A} := by
  have heq : (FK.measure G θ ξ {A | s ⊆ A}).toReal =
      torusRCFiberEventProbability (FK.law G θ ξ) {A | s ⊆ A} := by
    rw [FK.measure_toReal_eq_indicator_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [FK.law_apply, ENNReal.toReal_ofReal (FK.configurationProbability_pos G θ ξ A).le]
  grind [fk_allOpen_probability_ge]
end

noncomputable local instance fiberEnergyRemainingFintype (R : FK.Configuration G) :
    Fintype (FK.RemainingConfiguration G R) := Fintype.ofFinite _
noncomputable local instance fiberEnergyDeletedEdgeFintype (R : FK.Configuration G) :
    Fintype (FK.edgeRestriction G R).edgeSet := Fintype.ofFinite _

/-- The same opening bound on a graph with a prescribed set of removed edges.
The event only prescribes actual retained edges; it adds no boundary wiring. -/
theorem fk_remaining_allOpen_eventProbability_ge (θ : FK.Parameters)
    (ξ : FK.BoundaryCondition V) (R : FK.Configuration G)
    (s : FK.Configuration (FK.edgeRestriction G R)) :
    fkOpenEnergy θ ^ s.card ≤ torusRCFiberEventProbability (FK.remainingLaw G θ ξ R)
      {A | (FK.edgeRestrictionConfigurationEquiv G R s).val ⊆ A.val} := by
  have heq : torusRCFiberEventProbability (FK.remainingLaw G θ ξ R)
      {A | (FK.edgeRestrictionConfigurationEquiv G R s).val ⊆ A.val} =
      torusRCFiberEventProbability (FK.law (FK.edgeRestriction G R) θ ξ) {A | s ⊆ A} := by
    unfold torusRCFiberEventProbability
    rw [← FK.law_edgeRestriction_map, FK.FiniteProbability.expectation_map]
    simp [FK.FiniteProbability.expectation, Set.indicator]
  grind [fk_allOpen_eventProbability_ge, FK.edgeRestriction]

end

end PottsDiscontinuity.TorusRC
