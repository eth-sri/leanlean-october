module

public import Erdos821.S2.AbsoluteRootTask
public import Erdos821.P3Tail.MemoryTail

/-! Absolute bounds for the closed residue paths. -/

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Root

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

theorem visitQ_nonneg (F : FixedData) (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ visitQ F.q n i := by
  unfold visitQ
  split_ifs
  · simp
  · exact F.q_pos.le

theorem residueExpectation_visitQ_nonneg {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} {A : Model F P J m} (Q : ResiduePath A n) :
    0 ≤ P.residueExpectation n (visitQ F.q n) Q.offset Q.active := by
  have hpath (y : P.Residues) :
      0 ≤ P.residuePathFactor n (visitQ F.q n) Q.offset Q.active y := by
    unfold PrimeGroups.residuePathFactor
    apply Finset.prod_nonneg
    intro p hp
    apply Finset.prod_nonneg
    intro i hi
    by_cases ha : p.val ∈ Q.active i
    · grind
    · simp only [ite_eq_right ha]
      by_cases hd : (p.val : ℤ) ∣ (y p).val + Q.offset i
      · simp only [ite_eq_left hd]
        exact visitQ_nonneg F n i
      simp_all
  unfold PrimeGroups.residueExpectation
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (by grind)


end Erdos821.S2Root
