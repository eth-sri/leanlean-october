module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Nat.Defs

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def detourConflicts {I R : Type*} (S : Finset I)
    (support : I → Finset R) (i : I) : Finset I :=
  (S.erase i).filter (fun j => ¬ Disjoint (support i) (support j))

theorem exists_disjoint_detours {I R : Type*} (S : Finset I) (support : I → Finset R)
    (hsize : ∀ i ∈ S, (support i).card ≤ 2)
    (huse : ∀ r, (S.filter (fun j => r ∈ support j)).card ≤ 3) :
    ∃ T ⊆ S, (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) ∧
      S.card ≤ 5*T.card := by
  let family := S.powerset.filter fun T =>
    decide (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) = true
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image family Finset.card ⟨∅, by simp [family]⟩
  obtain ⟨hTS, hdisBool⟩ := Finset.mem_filter.mp hT
  have hdis := of_decide_eq_true hdisBool
  have hsub : T ⊆ S := Finset.mem_powerset.mp hTS
  refine ⟨T, hsub, hdis, (Finset.card_le_card (t := T.biUnion fun j => insert j (detourConflicts S support j))
    fun i hi => ?_).trans (Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g := fun _ => 5) fun j hj => ?_).trans
      (by simp [Nat.mul_comm])))⟩
  · by_cases hiT : i ∈ T
    · exact Finset.mem_biUnion.mpr ⟨i, hiT, Finset.mem_insert_self _ _⟩
    · by_contra hno
      have hn : ∀ j ∈ T, Disjoint (support i) (support j) := fun j hj => by
        by_contra hij
        exact hno <| Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_insert_of_mem <| Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨fun he => hiT (he ▸ hj), hi⟩, fun h => hij h.symm⟩⟩
      have hnew : insert i T ∈ family := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hsub),
        decide_eq_true fun j hj k hk hne => by
          rcases Finset.mem_insert.mp hj with rfl | hjT <;> rcases Finset.mem_insert.mp hk with rfl | hkT
          · exact (hne rfl).elim
          · exact hn k hkT
          · exact (hn j hjT).symm
          · exact hdis j hjT k hkT hne⟩
      have hc := hmax (insert i T) hnew
      rw [Finset.card_insert_of_notMem hiT] at hc; omega
  · have hconf : (detourConflicts S support j).card ≤ 4 := by
      refine (Finset.card_le_card (t := (support j).biUnion fun r => (S.filter fun k => r ∈ support k).erase j)
        fun k hk => ?_).trans (Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g := fun _ => 2) fun r hr => ?_).trans
          (by have := hsize j (hsub hj); simp; omega)))
      · obtain ⟨hkS, hnot⟩ := Finset.mem_filter.mp hk
        obtain ⟨r, hrj, hrk⟩ := Finset.not_disjoint_iff.mp hnot
        exact Finset.mem_biUnion.mpr ⟨r, hrj, Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hkS).1, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hkS).2, hrk⟩⟩⟩
      · have := Finset.card_erase_add_one (s := S.filter fun k => r ∈ support k) (Finset.mem_filter.mpr ⟨hsub hj, hr⟩)
        have := huse r; omega
    exact (Finset.card_insert_le _ _).trans (by omega)

end HordijkSteelThreshold
