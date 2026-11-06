/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.ComponentMerge
public import PottsDiscontinuity.FK.FrozenBridge

/-!
# Comparison under coarser boundary wiring

The cross lattice condition is proved from the same actual component-merging
calculation for two boundary partitions. Mathlib's complete Holley theorem then
compares the normalized finite FK laws on every increasing nonnegative function.
-/

public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance boundaryComparisonEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance boundaryComparisonEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

omit [Finite V] in
theorem componentSetoid_mono_edges_boundary (ξ η : BoundaryCondition V)
    (hξη : ξ.partition ≤ η.partition) (A B : Configuration G) (hAB : A ⊆ B) :
    componentSetoid G ξ A ≤ componentSetoid G η B := by
  apply componentSetoid_le
  · intro x y h
    exact actualConnected_component G η B (actualConnected_mono hAB h)
  · exact le_trans hξη le_sup_right

section
variable (ξ η : BoundaryCondition V) (hξη : ξ.partition ≤ η.partition) (A B : Configuration G)
include hξη
theorem componentCount_insert_increment_mono_boundary (hAB : A ⊆ B)
    (e : G.edgeSet) :
    componentCount G ξ (insert e A) + componentCount G η B ≤
      componentCount G η (insert e B) + componentCount G ξ A := by
  obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective e.val
  have huv : G.Adj u v := by aesop
  have he' : e = ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ := Subtype.ext he.symm
  subst e
  by_cases hA : (componentSetoid G ξ A).r u v
  · rw [componentCount_insert_eq_of_related ξ A huv hA,
      componentCount_insert_eq_of_related η B huv
        (componentSetoid_mono_edges_boundary ξ η hξη A B hAB hA)]
    omega
  · have ha := componentCount_insert_of_not_related ξ A huv hA
    by_cases hB : (componentSetoid G η B).r u v
    · rw [componentCount_insert_eq_of_related η B huv hB]
      omega
    · have hb := componentCount_insert_of_not_related η B huv hB
      omega

theorem componentCount_union_increment_mono_boundary (hAB : A ⊆ B)
    (C : Configuration G) :
    componentCount G ξ (A ∪ C) + componentCount G η B ≤
      componentCount G η (B ∪ C) + componentCount G ξ A := by
  induction C using Finset.induction_on with
  | empty => simp [add_comm]
  | @insert e C he ih =>
    have hi := componentCount_insert_increment_mono_boundary ξ η hξη (A ∪ C) (B ∪ C) (Finset.union_subset_union_left hAB) e
    grind

theorem componentCount_cross_supermodular  :
    componentCount G ξ A + componentCount G η B ≤
      componentCount G ξ (A ∩ B) + componentCount G η (A ∪ B) := by
  have h := componentCount_union_increment_mono_boundary ξ η hξη (A ∩ B) B
    Finset.inter_subset_right A
  have hi : A ∩ B ∪ A = A := Finset.union_eq_right.mpr Finset.inter_subset_left
  grind
end

section
variable (q : Parameters) (ξ η : BoundaryCondition V) (hξη : ξ.partition ≤ η.partition)
include hξη
theorem weight_cross_lattice_condition (A B : Configuration G) :
    weight G q ξ A * weight G q η B ≤
      weight G q ξ (A ∩ B) * weight G q η (A ∪ B) := by
  have hc (C : Configuration G) : C.card ≤ Nat.card G.edgeSet := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ C
  have hclosed : (Nat.card G.edgeSet - A.card) + (Nat.card G.edgeSet - B.card) =
      (Nat.card G.edgeSet - (A ∩ B).card) +
        (Nat.card G.edgeSet - (A ∪ B).card) := by
    grind
  have hproduct (C D : Configuration G) :
      weight G q ξ C * weight G q η D =
        (edgeParameter q ^ (C.card+D.card) *
          (1-edgeParameter q) ^ ((Nat.card G.edgeSet-C.card)+(Nat.card G.edgeSet-D.card))) *
            q.val ^ (componentCount G ξ C + componentCount G η D) := by
    grind [weight]
  rw [hproduct A B, hproduct (A ∩ B) (A ∪ B), ← (Finset.card_inter_add_card_union A B), hclosed]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ q.property (componentCount_cross_supermodular ξ η hξη A B))
    (mul_nonneg (pow_nonneg (edgeParameter_pos q).le _)
      (pow_nonneg (one_sub_edgeParameter_pos q).le _))

theorem configurationProbability_cross_lattice_condition (A B : Configuration G) :
    configurationProbability G q ξ A * configurationProbability G q η B ≤
      configurationProbability G q ξ (A ∩ B) * configurationProbability G q η (A ∪ B) := by
  simp only [configurationProbability, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right
    (mul_pos (partitionFunction_pos G q ξ) (partitionFunction_pos G q η))).mpr
      (weight_cross_lattice_condition q ξ η hξη A B)

/-- Coarser wiring increases every increasing nonnegative observable under the
actual normalized finite FK laws, at the same parameters. -/
theorem configurationProbability_boundary_comparison (f : Configuration G → ℝ) (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    (∑ A, f A * configurationProbability G q ξ A) ≤
      ∑ A, f A * configurationProbability G q η A :=
  _root_.holley (μ := f) (f := configurationProbability G q ξ)
    (g := configurationProbability G q η) hf0
    (fun A => (configurationProbability_pos G q ξ A).le)
    (fun A => (configurationProbability_pos G q η A).le) hf
    (by rw [sum_configurationProbability, sum_configurationProbability])
    (configurationProbability_cross_lattice_condition q ξ η hξη)
end

end
end PottsDiscontinuity.FK
