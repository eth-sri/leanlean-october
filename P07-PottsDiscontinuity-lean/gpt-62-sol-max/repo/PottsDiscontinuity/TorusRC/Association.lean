module

public import PottsDiscontinuity.TorusRC.IndexedFK
public import PottsDiscontinuity.TorusRC.RectanglePairs
public import PottsDiscontinuity.FK.PositiveAssociation

/-! # FKG association for the critical indexed torus law -/

@[expose] public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

def openIndexSet (A : RCConfig N M) : Finset (Fin N × Fin M) :=
  univ.filter fun v => A v = true

section

variable (A B : RCConfig N M)

private theorem openIndexSet_inf :
    openIndexSet (A ⊓ B) = openIndexSet A ∩ openIndexSet B := by
  ext v
  simp only [openIndexSet, mem_filter, mem_univ, true_and, mem_inter]
  simp

private theorem openIndexSet_sup :
    openIndexSet (A ⊔ B) = openIndexSet A ∪ openIndexSet B := by
  ext v
  simp only [openIndexSet, mem_filter, mem_univ, true_and, mem_union]
  simp

private theorem openCount_lattice :
    openCount (A ⊓ B) + openCount (A ⊔ B) = openCount A + openCount B := by
  unfold openCount
  change (openIndexSet (A ⊓ B)).card + (openIndexSet (A ⊔ B)).card =
    (openIndexSet A).card + (openIndexSet B).card
  rw [openIndexSet_inf, openIndexSet_sup, card_inter_add_card_union]

private theorem closedCount_lattice :
    closedCount (A ⊓ B) + closedCount (A ⊔ B) = closedCount A + closedCount B := by
  grind [openCount_lattice, openCount_add_closedCount]

end

section

variable
  (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ))

theorem torusRCWeight_lattice_condition (A B : RCConfig N M) :
    torusRCWeight hN hM q A * torusRCWeight hN hM q B ≤
      torusRCWeight hN hM q (A ⊓ B) * torusRCWeight hN hM q (A ⊔ B) := by
  let p : ℝ := (rcCriticalParameter q).val
  have hprod (C D : RCConfig N M) :
      torusRCWeight hN hM q C * torusRCWeight hN hM q D =
        (p ^ (openCount C + openCount D) *
          (1 - p) ^ (closedCount C + closedCount D)) *
            q.val ^ (clusterCount hN hM true C + clusterCount hN hM true D) := by
    have hp : (rcCriticalParameter q).val = p := rfl
    simp only [torusRCWeight, hp, pow_add]
    ring
  rw [hprod A B, hprod (A ⊓ B) (A ⊔ B), ← openCount_lattice A B,
    ← closedCount_lattice A B]
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_right₀ q.property (clusterCount_supermodular hN hM A B)
  · exact mul_nonneg (pow_nonneg (criticalParameter_pos q).le _)
      (pow_nonneg (sub_nonneg.mpr (criticalParameter_lt_one q).le) _)

theorem torusRCMass_lattice_condition (A B : RCConfig N M) :
    torusRCMass hN hM q A * torusRCMass hN hM q B ≤
      torusRCMass hN hM q (A ⊓ B) * torusRCMass hN hM q (A ⊔ B) := by
  simp only [torusRCMass]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right
    (mul_pos (torusRCPartition_pos hN hM q) (torusRCPartition_pos hN hM q))).2
      (torusRCWeight_lattice_condition hN hM q A B)

/-- Increasing events are positively associated under the normalized torus law. -/
theorem torusRCProbability_inter_ge_mul (E F : Set (RCConfig N M))
    (hE : ∀ ⦃A B⦄, A ≤ B → A ∈ E → B ∈ E)
    (hF : ∀ ⦃A B⦄, A ≤ B → A ∈ F → B ∈ F) :
    torusRCProbability hN hM q E * torusRCProbability hN hM q F ≤
      torusRCProbability hN hM q (E ∩ F) := by
  simp only [torusRCProbability_eq_sum]
  exact FK.fkg_events _ (fun A => (torusRCMass_pos hN hM q A).le) (sum_torusRCMass hN hM q)
    (torusRCMass_lattice_condition hN hM q) E F hE hF

end

/-- Iteration of positive association for a normalized event probability. -/
theorem event_product_le_inter {α ι : Type*} [Preorder α] [DecidableEq ι]
    (P : Set α → ℝ) (h₁ : P Set.univ = 1) (h₀ : ∀ E, 0 ≤ P E)
    (h : ∀ E F, IsUpperSet E → IsUpperSet F → P E * P F ≤ P (E ∩ F))
    (s : Finset ι) (E : ι → Set α) (hE : ∀ i, IsUpperSet (E i)) :
    (∏ i ∈ s, P (E i)) ≤ P {A | ∀ i ∈ s, A ∈ E i} := by
  induction s using Finset.induction_on with
  | empty => simp [h₁]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine (mul_le_mul_of_nonneg_left ih (h₀ _)).trans ?_
    rw [show {A | ∀ i ∈ insert a s, A ∈ E i} = E a ∩ {A | ∀ i ∈ s, A ∈ E i} from
      Set.ext fun A => Finset.forall_mem_insert a s (fun i => A ∈ E i)]
    exact h _ _ (hE a) (fun {_ _} hAB hA i hi => hE i hAB (hA i hi))

/-- A finite intersection of increasing torus events has probability at least
the product of the individual probabilities. -/
theorem torusRCProbability_finset_inter_ge_prod
    {ι : Type*} [DecidableEq ι] (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (s : Finset ι)
    (E : ι → Set (RCConfig N M))
    (hE : ∀ i ⦃A B⦄, A ≤ B → A ∈ E i → B ∈ E i) :
    (∏ i ∈ s, torusRCProbability hN hM q (E i)) ≤
      torusRCProbability hN hM q {A | ∀ i ∈ s, A ∈ E i} :=
  event_product_le_inter _ (torusRCProbability_univ hN hM q) (torusRCProbability_nonneg hN hM q)
    (torusRCProbability_inter_ge_mul hN hM q) s E hE

end PottsDiscontinuity.TorusRC
