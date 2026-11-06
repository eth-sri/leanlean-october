/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import PottsDiscontinuity.FK.ComponentSupermodular

/-!
# Positive association of the actual finite FK law

The component count is the original wired quotient count, including isolated
vertices. Its proved supermodularity gives the lattice condition for the exact
FK weights. The complete mathlib four-functions/FKG theorem then yields
positive association, without introducing any probabilistic assumption.
-/

@[expose] public section

namespace PottsDiscontinuity.FK


noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance positiveAssociationEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveAssociationEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

section

variable (q : Parameters) (ξ : BoundaryCondition V)
include q ξ

theorem weight_lattice_condition 
    (A B : Configuration G) :
    weight G q ξ A * weight G q ξ B ≤
      weight G q ξ (A ∩ B) * weight G q ξ (A ∪ B) := by
  
  
  have hc (C : Configuration G)  := Finset.card_le_natCard C
  have hclosed :  Nat.card G.edgeSet - A.card  + (Nat.card G.edgeSet - B.card) =
       Nat.card G.edgeSet - (A ∩ B).card  +
        (Nat.card G.edgeSet - (A ∪ B).card) := by
    grind
  have hproduct (C D : Configuration G) :
      weight G q ξ C * weight G q ξ D =
         edgeParameter q ^ (C.card+D.card) *
          (1-edgeParameter q) ^ ( Nat.card G.edgeSet-C.card +(Nat.card G.edgeSet-D.card))  *
            q.val ^ (componentCount G ξ C + componentCount G ξ D) := by
    simp only [weight]
    ring
  rw [hproduct A B, hproduct (A ∩ B) (A ∪ B), ←  Finset.card_inter_add_card_union A B , hclosed]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ q.property (componentCount_supermodular ξ A B))
    (mul_nonneg (pow_nonneg (edgeParameter_pos q).le _)
      (pow_nonneg (one_sub_edgeParameter_pos q).le _))

theorem configurationProbability_lattice_condition  (A B : Configuration G) :
    configurationProbability G q ξ A * configurationProbability G q ξ B ≤
      configurationProbability G q ξ (A ∩ B) *
        configurationProbability G q ξ (A ∪ B) := by
  
  simp only [configurationProbability, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right
    (mul_pos (partitionFunction_pos G q ξ) (partitionFunction_pos G q ξ))).mpr
      (weight_lattice_condition q ξ A B)

/-- Increasing nonnegative functions are positively correlated under the exact
normalized configuration probabilities of equation (1.2). -/
theorem configurationProbability_positive_association  (f g : Configuration G → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ A, configurationProbability G q ξ A * f A) *
       ∑ A, configurationProbability G q ξ A * g A  ≤
        ∑ A, configurationProbability G q ξ A * (f A * g A) := by
  
  
  simpa only [sum_configurationProbability, one_mul] using  _root_.fkg (μ := configurationProbability G q ξ)
                                                              (f := f) (g := g) (fun A => (configurationProbability_pos G q ξ A).le)
                                                              hf0 hg0 hf hg (configurationProbability_lattice_condition q ξ) 

end

end
end PottsDiscontinuity.FK
