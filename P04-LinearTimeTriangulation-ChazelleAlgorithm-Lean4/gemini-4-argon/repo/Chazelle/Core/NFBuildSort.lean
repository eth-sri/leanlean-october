module

public import Chazelle.Core.NFBuildStack
public import Chazelle.Chain.Sides

/-!
# WP-C (BuildNF): the sorted attachment events form a parenthesis word

`BuildNF` sorts the `2K` attachment events of the chords by key, ties broken by the tie rule.  An
event is a triple `(i, k, o)`: the chord index, the key of this end, the key of the other end.
The **tie rule**: at equal keys, the event whose other end is cyclically *farther* along the walk
comes first (`cycDist n k o`, the distance from `k` to `o` going up the walk, cyclically).

## Results

* `sideInArc_iff_cycDist`: for three distinct keys in `[0, n)`, `x` is strictly between `k` and
  `y` iff `x` is cyclically closer to `k` than `y`.  With `Model.TieDown`/`Model.TieUp`
  (`Chazelle.Core.FactsTie`) this identifies the tie rule with the direction rule used by the
  machine (at a vertex whose leaving edge goes down, the west chord's event comes first; up: the
  east chord's).
* `noCross_of_sorted`: if the chords do not cross (the geometric `WalkAx.no_cross`), distinct
  chords have distinct key pairs, and the event list is sorted by key and the tie rule, then the
  chord word of the event list is a parenthesis word (`BuildStack.NoCross`, `BuildStack.Twice`),
  so the stack pass of `Chazelle.Core.NFBuildStack` applies.
-/

namespace Chazelle.Core.BuildSort

@[expose] public section

open List
open Chazelle.Chain (sideInArc)

/-- The cyclic distance from the key `k` up to the key `x` on a walk of length `n`. -/
noncomputable def cycDist (n k x : ℝ) : ℝ := if k < x then x - k else x - k + n

/-- **Cyclic betweenness is comparison of cyclic distances.** -/
theorem sideInArc_iff_cycDist {n k x y : ℝ} (_hk : 0 ≤ k ∧ k < n) (hx : 0 ≤ x ∧ x < n)
    (hy : 0 ≤ y ∧ y < n) (hkx : k ≠ x) (hky : k ≠ y) :
    sideInArc k y x ↔ cycDist n k x < cycDist n k y := by
  unfold sideInArc cycDist
  rcases lt_or_gt_of_ne hkx with h1 | h1 <;> rcases lt_or_gt_of_ne hky with h2 | h2
  · rw [ite_eq_left h2, ite_eq_left h1, ite_eq_left h2]
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; exact ⟨h1, by linarith⟩
  · rw [ite_eq_right (not_lt.2 h2.le), ite_eq_left h1, ite_eq_right (not_lt.2 h2.le)]
    exact ⟨fun _ => by linarith [hy.1, hx.2], fun _ => Or.inl h1⟩
  · rw [ite_eq_left h2, ite_eq_right (not_lt.2 h1.le), ite_eq_left h2]
    constructor
    · rintro ⟨h, -⟩; linarith
    · intro h; linarith [hx.1, hy.2]
  · rw [ite_eq_right (not_lt.2 h2.le), ite_eq_right (not_lt.2 h1.le), ite_eq_right (not_lt.2 h2.le)]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h; exact Or.inr (by linarith)

/-- An attachment event: chord index, key of this end, key of the other end. -/
abbrev Ev := ℕ × ℝ × ℝ

/-- **The sort order of events**: by key, and at equal keys the event whose other end is
cyclically farther first. -/
def EvLe (n : ℝ) (e f : Ev) : Prop :=
  e.2.1 < f.2.1 ∨ (e.2.1 = f.2.1 ∧ cycDist n f.2.1 f.2.2 ≤ cycDist n e.2.1 e.2.2)

/-- The chord index occurs in the chord word as often as its events in the list. -/
theorem count_map_fst (L : List Ev) (i : ℕ) :
    (L.map Prod.fst).count i = (L.filter (fun e => e.1 == i)).length := by
  rw [count_eq_countP, countP_map, countP_eq_length_filter]
  rfl

/-- **The two events of a chord**: in a list where every event's partner (other end first) is
present and every chord has exactly two events, two events of one chord at two positions are
partners. -/
theorem partner_of_sublist {L : List Ev} (hkey : ∀ e ∈ L, e.2.1 ≠ e.2.2)
    (hpair : ∀ e ∈ L, (e.1, e.2.2, e.2.1) ∈ L)
    (htwice : ∀ e ∈ L, (L.map Prod.fst).count e.1 = 2) {e₁ e₂ : Ev} (h : [e₁, e₂] <+ L)
    (hi : e₁.1 = e₂.1) : e₂ = (e₁.1, e₁.2.2, e₁.2.1) := by
  have he₁ : e₁ ∈ L := h.subset (by simp)
  set F := L.filter (fun e => e.1 == e₁.1) with hF
  have hlen : F.length = 2 := by rw [hF, ← count_map_fst]; exact htwice e₁ he₁
  have hsub : [e₁, e₂] <+ F := by
    rw [hF, sublist_filter_iff]
    refine ⟨[e₁, e₂], h, ?_⟩
    simp [hi]
  have heq : [e₁, e₂] = F := hsub.eq_of_length (by rw [hlen]; rfl)
  have hp : (e₁.1, e₁.2.2, e₁.2.1) ∈ F := by
    rw [hF, mem_filter]
    exact ⟨hpair e₁ he₁, by simp⟩
  rw [← heq] at hp
  rcases mem_cons.1 hp with hp | hp
  · exfalso
    apply hkey e₁ he₁
    have := congrArg (fun e : Ev => e.2.1) hp
    simpa using this.symm
  · rw [mem_singleton] at hp
    exact hp.symm

/-- **The sorted events form a parenthesis word.** -/
theorem noCross_of_sorted {n : ℝ} {L : List Ev}
    (hkey : ∀ e ∈ L, 0 ≤ e.2.1 ∧ e.2.1 < n ∧ 0 ≤ e.2.2 ∧ e.2.2 < n ∧ e.2.1 ≠ e.2.2)
    (hpair : ∀ e ∈ L, (e.1, e.2.2, e.2.1) ∈ L)
    (htwice : ∀ e ∈ L, (L.map Prod.fst).count e.1 = 2)
    (hcross : ∀ e ∈ L, ∀ f ∈ L, e.1 ≠ f.1 →
      ¬ (sideInArc e.2.1 e.2.2 f.2.1 ∧ sideInArc e.2.2 e.2.1 f.2.2))
    (hsame : ∀ e ∈ L, ∀ f ∈ L, e.2 = f.2 → e.1 = f.1)
    (hsorted : L.Pairwise (EvLe n)) :
    BuildStack.NoCross (L.map Prod.fst) ∧ BuildStack.Twice (L.map Prod.fst) := by
  refine ⟨fun i j hij hsub => ?_, fun x hx => ?_⟩
  · obtain ⟨l', hl', hmap⟩ := sublist_map_iff.1 hsub
    rcases l' with _ | ⟨e₁, _ | ⟨f₁, _ | ⟨e₂, _ | ⟨f₂, _ | ⟨g, l'⟩⟩⟩⟩⟩ <;> simp at hmap
    obtain ⟨h1, h2, h3, h4⟩ := hmap
    have hmem : ∀ e ∈ [e₁, f₁, e₂, f₂], e ∈ L := fun e he => hl'.subset he
    have hne : ∀ e ∈ L, e.2.1 ≠ e.2.2 := fun e he => (hkey e he).2.2.2.2
    -- the partners
    have he₂ : e₂ = (e₁.1, e₁.2.2, e₁.2.1) := partner_of_sublist hne hpair htwice
      ((by simp : [e₁, e₂] <+ [e₁, f₁, e₂, f₂]).trans hl') (by rw [← h1, ← h3])
    have hf₂ : f₂ = (f₁.1, f₁.2.2, f₁.2.1) := partner_of_sublist hne hpair htwice
      ((by simp : [f₁, f₂] <+ [e₁, f₁, e₂, f₂]).trans hl') (by rw [← h2, ← h4])
    -- the order
    have hpr : ∀ x y : Ev, [x, y] <+ [e₁, f₁, e₂, f₂] → EvLe n x y := fun x y h =>
      pairwise_pair.1 (hsorted.sublist (h.trans hl'))
    have hef := hpr e₁ f₁ (by simp)
    have hfe := hpr f₁ e₂ (by simp)
    have hff := hpr e₂ f₂ (by simp)
    set a := e₁.2.1
    set b := e₁.2.2
    set c := f₁.2.1
    set d := f₁.2.2
    obtain ⟨ha0, han, hb0, hbn, hab⟩ := hkey e₁ (hmem e₁ (by simp))
    obtain ⟨hc0, hcn, hd0, hdn, hcd⟩ := hkey f₁ (hmem f₁ (by simp))
    rw [he₂] at hfe hff
    rw [hf₂] at hff
    unfold EvLe at hef hfe hff
    simp only at hef hfe hff
    have hij' : e₁.1 ≠ f₁.1 := by rwa [← h1, ← h2]
    have hX := hcross e₁ (hmem e₁ (by simp)) f₁ (hmem f₁ (by simp)) hij'
    have hsame' : ¬ (a = c ∧ b = d) := fun ⟨h5, h6⟩ =>
      hij' (hsame e₁ (hmem e₁ (by simp)) f₁ (hmem f₁ (by simp)) (Prod.ext h5 h6))
    -- `a ≤ c ≤ b ≤ d`
    have hac : a ≤ c := by rcases hef with h | h; exact h.le; exact h.1.le
    have hcb : c ≤ b := by rcases hfe with h | h; exact h.le; exact h.1.le
    have hbd : b ≤ d := by rcases hff with h | h; exact h.le; exact h.1.le
    have hab' : a < b := lt_of_le_of_ne (hac.trans hcb) hab
    rcases hac.lt_or_eq with hac | hac
    · rcases hcb.lt_or_eq with hcb | hcb
      · rcases hbd.lt_or_eq with hbd | hbd
        · -- all strict: a crossing
          apply hX
          unfold sideInArc
          rw [ite_eq_left hab', ite_eq_right (not_lt.2 hab'.le)]
          exact ⟨⟨hac, hcb⟩, Or.inl hbd⟩
        · -- tie at `b = d` between `e₂` and `f₂`
          rcases hff with h | ⟨-, h⟩
          · linarith
          · unfold cycDist at h
            rw [ite_eq_right (not_lt.2 hab'.le), ite_eq_right (not_lt.2 (show c ≤ d by linarith))] at h
            linarith
      · -- tie at `c = b` between `f₁` and `e₂`
        rcases hfe with h | ⟨-, h⟩
        · linarith
        · have hcd' : c < d := lt_of_le_of_ne (hcb ▸ hbd) hcd
          unfold cycDist at h
          rw [ite_eq_right (not_lt.2 hab'.le), ite_eq_left hcd'] at h
          linarith
    · -- tie at `a = c` between `e₁` and `f₁`
      rcases hef with h | ⟨-, h⟩
      · linarith
      · have hcd' : c < d := by linarith
        unfold cycDist at h
        rw [ite_eq_left hcd', ite_eq_left hab'] at h
        exact hsame' ⟨hac, by linarith⟩
  · rw [mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact htwice e he

end

end Chazelle.Core.BuildSort
