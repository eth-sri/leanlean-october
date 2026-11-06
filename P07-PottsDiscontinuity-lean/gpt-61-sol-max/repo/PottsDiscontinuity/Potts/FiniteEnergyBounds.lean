module
public import Mathlib

public import PottsDiscontinuity.FK.FiniteEnergy

/-!
# Finite-energy lower bounds for closed edge sets

The FK single-edge finite-energy estimate iterates to a uniform lower bound
for every prescribed finite set of edges to be closed. In particular, four
specified edges have closed probability at least `(1 - p)^4`.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- Configurations in which every edge in `F` is closed. -/
def allClosedEdges (F : Finset G.edgeSet) : Set (FK.Configuration G) :=
  {A | Disjoint F A}

/-- In any finite FK measure, each prescribed finite set of edges is closed
with probability at least `(1-p)` to the power of its cardinality. -/
theorem measure_allClosedEdges_lower_bound (q : FK.Parameters)
    (ξ : FK.BoundaryCondition V) (F : Finset G.edgeSet) :
    (1 - FK.edgeParameter q) ^ F.card ≤
      (FK.measure G q ξ (allClosedEdges F)).toReal := by
  
  let : DecidableEq G.edgeSet := Classical.decEq _
  induction F using Finset.induction_on with
  | empty =>
      simp [allClosedEdges]
  | @insert e F he ih =>
      have hrepr (z : Sym2 V) : z ∈ G.edgeSet →
          ∃ u v, ∃ huv : G.Adj u v, z = s(u, v) := by
        refine Sym2.inductionOn z ?_
        aesop
      obtain ⟨u, v, huv, hev⟩ := hrepr e.1 e.2
      have heq : e = ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ := Subtype.ext hev
      subst e
      
      have hFE := FK.configurationProbability_edge_finite_energy_closed q ξ
        (allClosedEdges F) huv  fun A =>
                                  {
                                    mp := fun h =>
                                      Finset.disjoint_left.mpr fun ⦃a⦄ haF haErase => Finset.disjoint_left.mp h haF (Finset.mem_of_mem_erase haErase),
                                    mpr := fun h =>
                                      Finset.disjoint_left.mpr fun ⦃a⦄ haF haA =>
                                        Finset.disjoint_left.mp h haF
                                          (Finset.mem_erase.mpr
                                            ⟨fun hEq =>
                                              Eq.ndrec (motive := fun ⦃a⦄ => a ∈ F → a ∈ A → False) (fun haF haA => he haF) (Eq.symm hEq) haF haA,
                                              haA⟩) } 
      have hEvent : allClosedEdges F ∩
          {A |  ⟨s(u, v), G.mem_edgeSet.mpr huv⟩  ∉ A} =
            allClosedEdges (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ F) := by
        ext A
        change  Disjoint F A ∧
           ⟨s(u, v), G.mem_edgeSet.mpr huv⟩  ∉ A  ↔
            Disjoint (insert ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ F) A
        all_goals grind
      rw [hEvent] at hFE
      
      have hpow : (1 - FK.edgeParameter q) ^ (insert ⟨s(u, v),
          G.mem_edgeSet.mpr huv⟩ F).card =
            (1 - FK.edgeParameter q) * (1 - FK.edgeParameter q) ^ F.card := by
        grind
      rw [hpow]
      exact (mul_le_mul_of_nonneg_left ih  (FK.one_sub_edgeParameter_pos q).le ).trans hFE.1

end

end PottsDiscontinuity.Potts
