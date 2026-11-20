module

public import RequestProject.CutSurfaceSpine

@[expose] public section

/-! Chosen free faces of geometric collapses, retained alongside their chain retractions. -/

namespace FiniteChains.Collapse
variable {T F : Type*} [DecidableEq T] (inc : F → Finset T)

/-- Each pair records the actual free face at the time its top cell is removed. -/
def IsPairCollapse : List (T × F) → Finset T → Prop
  | [], S => S = ∅
  | (t, f) :: lp, S => t ∈ S ∧ IsFree inc S f t ∧ IsPairCollapse lp (S.erase t)

variable {inc}

/-- The actual top cells left after deleting a prefix of recorded cell pairs. -/
def remainingTops : Finset T → List (T × F) → Finset T
  | S, [] => S
  | S, p :: lp => remainingTops (S.erase p.1) lp

theorem mem_remainingTops (S : Finset T) (lp : List (T × F)) (t : T) :
    t ∈ remainingTops S lp ↔ t ∈ S ∧ t ∉ lp.map Prod.fst := by
  induction lp generalizing S with
  | nil => simp [remainingTops]
  | cons p lp ih =>
    simp only [remainingTops, ih, Finset.mem_erase, List.map_cons, List.mem_cons]
    tauto

theorem IsPairCollapse.suffix {left right : List _} {S : Finset T}
    (h : IsPairCollapse inc (left ++ right) S) :
    IsPairCollapse inc right (remainingTops S left) := by
  induction left generalizing S with
  | nil => exact h
  | cons p left ih => exact ih h.2.2

section

variable {lp : List (T × F)} {S : Finset T} (h : IsPairCollapse inc lp S)
include S h

theorem IsPairCollapse.top_mem {p : T × F} (hp : p ∈ lp) : p.1 ∈ S := by
  induction lp generalizing S with
  | nil => simp_all
  | cons q lp ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact Finset.mem_of_mem_erase (ih h.2.2 hp)

theorem IsPairCollapse.map_fst : IsCollapse inc (lp.map Prod.fst) S := by
  induction lp generalizing S with
  | nil => exact h
  | cons p lp ih => exact ⟨h.1, ⟨p.2, h.2.1⟩, ih h.2.2⟩

theorem IsPairCollapse.pair_inc {p : T × F} (hp : p ∈ lp) : p.1 ∈ inc p.2 := by
  induction lp generalizing S with
  | nil => simp_all
  | cons q lp ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · have hm : p.1 ∈ inc p.2 ∩ S := by
        rw [h.2.1]
        exact Finset.mem_singleton_self _
      simp_all
    · exact ih h.2.2 hp

end

/-- No later top cell meets the face deleted by the first elementary collapse. -/
theorem IsPairCollapse.later_top_not_inc {t : T} {f : F} {lp : List _}
    {S : Finset T} (h : IsPairCollapse inc ((t, f) :: lp) S)
    {p : T × F} (hp : p ∈ lp) : p.1 ∉ inc f := by
  intro hi
  have hs := h.2.2.top_mem hp
  have hm := Finset.mem_inter.mpr ⟨hi, Finset.mem_of_mem_erase hs⟩
  rw [h.2.1] at hm <;> simp_all

/-- Earlier deleted faces never occur on the boundary of any later top cell. -/
theorem IsPairCollapse.prefix_faces_avoid_suffix_tops {left right : List _}
    {S : Finset T} (h : IsPairCollapse inc (left ++ right) S)
    {p r : T × F} (hp : p ∈ left) (hr : r ∈ right) : r.1 ∉ inc p.2 := by
  induction left generalizing S with
  | nil => simp_all
  | cons a left ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.later_top_not_inc (List.mem_append.mpr (Or.inr hr))
    · exact ih h.2.2 hp

theorem IsPairCollapse.covers {lp : List _} {S : Finset T}
    (h : IsPairCollapse inc lp S) {t : T} (ht : t ∈ S) : ∃ f, (t, f) ∈ lp := by
  have hm := mem_list_of_isCollapse h.map_fst t ht
  grind

/-- Choose the free faces without losing their geometric certificates. -/
theorem exists_pairCollapse {l : List T} {S : Finset T} (h : IsCollapse inc l S) :
    ∃ lp : List _, IsPairCollapse inc lp S := by
  induction l generalizing S with
  | nil => exact ⟨[], h⟩
  | cons t l ih =>
    obtain ⟨ht, ⟨f, hf⟩, hr⟩ := h
    obtain ⟨lp, hp⟩ := ih hr
    exact ⟨(t, f) :: lp, ht, hf, hp⟩

/-- A genuine free-face collapse is also an oriented chain collapse whenever the
differential has unit incidences and vanishes outside actual face incidences. -/
theorem IsPairCollapse.chainCollapse {R : Type*} [Ring R]
    {d : T → F → R} {tops S : Finset T} {lp : List _}
    (hunit : ∀ t ∈ tops, ∀ f, t ∈ inc f → IsUnit (d t f))
    (hzero : ∀ t ∈ tops, ∀ f, t ∉ inc f → d t f = 0)
    (hS : S ⊆ tops) (h : IsPairCollapse inc lp S) : CollapseChain.IsChainCollapse d lp := by
  induction lp generalizing S with
  | nil => trivial
  | cons p lp ih =>
    have hpinc : p.1 ∈ inc p.2 := by
      have hm : p.1 ∈ inc p.2 ∩ S := by
        rw [h.2.1]
        exact Finset.mem_singleton_self _
      simp_all
    refine ⟨hunit p.1 (hS h.1) p.2 hpinc, ?_,
      ih (fun t ht => hS (Finset.mem_of_mem_erase ht)) h.2.2⟩
    intro q hq
    have hqS := h.2.2.top_mem hq
    apply hzero q.1 (hS (Finset.mem_of_mem_erase hqS)) p.2
    intro hqi
    have hqt : q.1 = p.1 := by
      have hm :=
        Finset.mem_inter.mpr ⟨hqi, Finset.mem_of_mem_erase hqS⟩
      rw [h.2.1] at hm
      exact Finset.mem_singleton.mp hm
    simp_all

end FiniteChains.Collapse
