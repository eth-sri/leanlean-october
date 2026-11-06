module
public import Mathlib.Tactic

public import Erdos821.S2High.PivotMoments

@[expose] public section

noncomputable section

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

def birthAddressGroup {P : PrimeGroups} {M n B : ℕ} :
    Erdos821.S2Core.BirthAddress P M n B → P.BigGroup
  | .inl (g, _) => g
  | .inr (.inl (_, g, _)) => g
  | .inr (.inr (_, g, _)) => g

theorem addressValue_mem_group {F : FixedData} {P : PrimeGroups} {J m n B : ℕ}
    {A : Model F P J m} (H : Erdos821.S2Core.MemoryHistory A n)
     a 
    (hperf : H.addressPerformed B a) :
    H.addressValue B a ∈ P.primes (birthAddressGroup a).val := by
  cases a with
  | inl gh =>
      rcases gh with ⟨g, h⟩
      exact (H.before 0).2.1 g.val h |>.property
  | inr tail =>
      cases tail with
      | inl igh =>
          rcases igh with ⟨i, g, h⟩
          exact ((permuteActive (H.edge i).2.1 (H.before i.succ)).2.1 g.val h).property
      | inr igh =>
          rcases igh with ⟨i, g, h⟩
          have hh : h.val < ((H.ghost i).2.1 g).val := hperf
          simp [Erdos821.S2Core.MemoryHistory.addressValue, hh, birthAddressGroup]

theorem big_groups_eq_of_common_prime {P : PrimeGroups} (g h : P.BigGroup) (p : ℕ)
    (hg : p ∈ P.primes g.val) (hh : p ∈ P.primes h.val) : g = h := Decidable.byContradiction fun hne => Finset.disjoint_left.mp (P.disjoint ↑g ↑h fun he => hne (Subtype.ext he)) hg hh


end Erdos821.S2High
