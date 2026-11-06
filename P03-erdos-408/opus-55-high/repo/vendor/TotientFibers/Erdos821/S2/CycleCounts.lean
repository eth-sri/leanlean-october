module

public import Erdos821.S2.CycleBlocks
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-! Counting cycles on a prescribed support by fixing their first address. -/

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

variable {α : Type*} [Fintype α] [DecidableEq α]

def cyclesOn (B : Finset α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun c => c.IsCycle ∧ c.support = B)

def tailOrders (B : Finset α) (x : α) : Finset (List α) :=
  (B.erase x).toList.permutations.toFinset

omit [Fintype α] in
lemma tailOrders_properties (B : Finset α) (x : α) (hx : x ∈ B)
    (l : List α) (hl : l ∈ tailOrders B x) :
    l.Nodup ∧ x ∉ l ∧ l.toFinset = B.erase x ∧ l.length = B.card - 1 := by
  have hp := List.mem_permutations.mp (List.mem_toFinset.mp hl)
  have hn := hp.nodup_iff.mpr (B.erase x).nodup_toList
  have hs : l.toFinset = B.erase x := by
    ext y
    simpa only [List.mem_toFinset, Finset.mem_toList] using
      (hp.mem_iff : y ∈ l ↔ y ∈ (B.erase x).toList)
  refine ⟨hn, ?_, hs, ?_⟩
  · intro hxl
    have hxm := List.mem_toFinset.mpr hxl
    simp_all
  · rw [hp.length_eq, Finset.length_toList, Finset.card_erase_of_mem hx]

lemma anchoredCycle_properties (B : Finset α) (x : α) (hx : x ∈ B)
    (hB : 2 ≤ B.card) (l : List α) (hl : l ∈ tailOrders B x) :
    (x :: l).Nodup ∧ 2 ≤ (x :: l).length ∧
      (x :: l).formPerm.IsCycle ∧ (x :: l).formPerm.support = B ∧
      (x :: l).formPerm.toList x = x :: l := by
  obtain ⟨hn, hxl, hs, hlen⟩ := tailOrders_properties B x hx l hl
  have hn' := List.nodup_cons.mpr ⟨hxl, hn⟩
  have hlen' : 2 ≤ (x :: l).length := by simp only [List.length_cons, hlen]; omega
  have hs' : (x :: l).toFinset = B := by
    simp only [List.toFinset_cons, hs, Finset.insert_erase hx]
  refine ⟨hn', hlen', List.isCycle_formPerm hn' hlen', ?_, ?_⟩
  · rw [List.support_formPerm_of_nodup _ hn', hs']
    grind
  · simpa using Equiv.Perm.toList_formPerm_nontrivial (x :: l) hlen' hn'

lemma anchoredCycle_image (B : Finset α) (x : α) (hx : x ∈ B)
    (hB : 2 ≤ B.card) :
    (tailOrders B x).image (fun l => (x :: l).formPerm) = cyclesOn B := by
  ext c
  constructor
  · intro hc
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
    have hp := anchoredCycle_properties B x hx hB l hl
    exact Finset.mem_filter.mpr (by grind)
  · intro hc
    obtain ⟨_, hcyc, hs⟩ := Finset.mem_filter.mp hc
    have hx' : x ∈ c.support := by simpa only [hs] using hx
    have hlist : (c.toList x).toFinset = B := by
      rw [← hs]
      ext y
      simp only [List.mem_toFinset, Equiv.Perm.mem_toList_iff]
      constructor
      · rintro ⟨hxy, _⟩
        exact hxy.mem_support_iff.mp hx'
      · intro hy
        exact ⟨hcyc.sameCycle (Equiv.Perm.mem_support.mp hx')
          (Equiv.Perm.mem_support.mp hy), hx'⟩
    cases heq : c.toList x with
    | nil =>
      simp_all
    | cons y l =>
      have hy : y = x := by
        simpa only [heq, List.getElem_cons_zero] using c.toList_getElem_zero x hx'
      subst y
      have hnodup : (x :: l).Nodup := by simpa only [heq] using c.nodup_toList x
      have hn := (List.nodup_cons.mp hnodup).2
      have hxl := (List.nodup_cons.mp hnodup).1
      have hs' : insert x l.toFinset = B := by
        simpa only [heq, List.toFinset_cons] using hlist
      have htail : l.toFinset = B.erase x := by
        rw [← hs']
        simp only [Finset.erase_insert_eq_erase]
        exact (Finset.erase_eq_of_notMem (by simp_all)).symm
      have hl : l ∈ tailOrders B x := by
        apply List.mem_toFinset.mpr
        apply List.mem_permutations.mpr
        apply List.perm_of_nodup_nodup_toFinset_eq hn (B.erase x).nodup_toList
        simpa only [Finset.toList_toFinset] using htail
      have hcform : (x :: l).formPerm = c := by
        rw [← heq, Equiv.Perm.formPerm_toList, hcyc.cycleOf_eq (Equiv.Perm.mem_support.mp hx')]
      grind

lemma anchoredCycle_injective (B : Finset α) (x : α) (hx : x ∈ B)
    (hB : 2 ≤ B.card) :
    Set.InjOn (fun l : List α => (x :: l).formPerm) (tailOrders B x) := by
  intro l hl l' hl' h
  have h1 := (anchoredCycle_properties B x hx hB l hl).2.2.2.2
  have h2 := (anchoredCycle_properties B x hx hB l' hl').2.2.2.2
  simp_all

/-- There are (|B|-1)! cycles with prescribed support B. -/
theorem cyclesOn_card (B : Finset α) (hB : 2 ≤ B.card) :
    (cyclesOn B).card = (B.card - 1).factorial := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by positivity)
  rw [← anchoredCycle_image B x hx hB,
    Finset.card_image_of_injOn (anchoredCycle_injective B x hx hB)]
  unfold tailOrders
  rw [List.toFinset_card_of_nodup (List.nodup_permutations _ (B.erase x).nodup_toList),
    List.length_permutations, Finset.length_toList, Finset.card_erase_of_mem hx]


end Erdos821.S2
