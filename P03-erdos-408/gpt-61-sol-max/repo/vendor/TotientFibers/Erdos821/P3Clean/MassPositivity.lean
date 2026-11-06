module
public import Mathlib.Tactic

public import Erdos821.P3Clean.RawNormAssembly
public import Erdos821.P3Clean.Baseline

/-! Positivity of the between-map measure once all big baselines are positive. -/

@[expose] public section

section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

section
variable (F : FixedData) (P : PrimeGroups) (n : ℕ)

theorem tiltedMu_pos        g   p 
    (hb : 0 < baselinePrime F n p.val) : 0 < tiltedMu F P n g p := by
  rw [tiltedMu_eq_mu_mul]
  exact mul_pos (mu_pos g p) (inv_pos.mpr hb)

theorem groupMemoryMass_nonneg      
     g  (hb : ∀ p : P.Prime g, 0 < baselinePrime F n p.val)  z  :
    0 ≤ P.groupMemoryMass F n g z := by
  classical
  unfold PrimeGroups.groupMemoryMass
  apply div_nonneg
  · apply Multiset.prod_nonneg
    intro r hr
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hr
    exact (tiltedMu_pos F P n g p.1 (hb p.1)).le
  · positivity

theorem betweenMass_nonneg      
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    {M B : ℕ} (a : BetweenState P M B) : 0 ≤ betweenMass F n a := by
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro g _
    apply Finset.prod_nonneg
    grind [tiltedMu_pos]
  · unfold pendingMass
    apply mul_nonneg
    · positivity
    · apply Finset.prod_nonneg
      solve_by_elim [groupMemoryMass_nonneg]

end


end Erdos821.P3Clean
