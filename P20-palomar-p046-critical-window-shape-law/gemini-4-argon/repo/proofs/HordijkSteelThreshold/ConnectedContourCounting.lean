module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

theorem finite_connected_covering_tour (C : Finset V) (r : V) (hr : r ∈ C)
    (hcross : ∀ S : Finset V, S ⊆ C → r ∈ S → S ≠ C →
      ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ G.Adj u v) :
    ∃ p : G.Walk r r, p.support.toFinset = C ∧ p.length = 2 * (C.card - 1) := by
  suffices ∀ k (p : G.Walk r r), p.support.toFinset ⊆ C →
      p.length = 2 * (p.support.toFinset.card - 1) → (C \ p.support.toFinset).card = k →
      ∃ q : G.Walk r r, q.support.toFinset = C ∧ q.length = 2 * (C.card - 1) from
    this _ Walk.nil (by simpa using hr) (by simp) rfl
  intro k; induction k using Nat.strong_induction_on with | h k ih =>
  intro p hp hl hk
  by_cases he : p.support.toFinset = C
  · exact ⟨p, he, he ▸ hl⟩
  · have hrp : r ∈ p.support.toFinset := List.mem_toFinset.mpr p.start_mem_support
    obtain ⟨u, hu, v, hv, hvs, huv⟩ := hcross _ hp hrp he
    have hu' := List.mem_toFinset.mp hu
    let q := (p.takeUntil u hu').append
      ((Walk.cons huv (Walk.cons huv.symm Walk.nil)).append (p.dropUntil u hu'))
    have hql : q.length = p.length + 2 := by
      have h := congrArg Walk.length (p.take_spec hu')
      simp only [q, Walk.length_append, Walk.length_cons, Walk.length_nil] at h ⊢; omega
    have hqs : q.support.toFinset = insert v p.support.toFinset := by
      ext x
      have h : x ∈ p.support ↔ x ∈ (p.takeUntil u hu').support ∨ x ∈ (p.dropUntil u hu').support := by
        conv_lhs => rw [← p.take_spec hu']
        exact Walk.mem_support_append_iff _ _
      simp only [q, List.mem_toFinset, Finset.mem_insert, Walk.mem_support_append_iff,
        Walk.support_cons, Walk.support_nil, List.mem_cons]
      have : u ∈ (p.takeUntil u hu').support := Walk.end_mem_support _
      grind
    have hqsub : q.support.toFinset ⊆ C := hqs ▸ Finset.insert_subset hv hp
    have hc : q.support.toFinset.card = p.support.toFinset.card + 1 := by
      rw [hqs, Finset.card_insert_of_notMem hvs]
    have := Finset.card_pos.mpr ⟨r, hrp⟩
    have := Finset.card_sdiff_add_card_eq_card hp
    have := Finset.card_sdiff_add_card_eq_card hqsub
    exact ih _ (by omega) q hqsub (by omega) rfl

variable [Fintype V] [DecidableRel G.Adj]

theorem card_connected_contours_le (d b : ℕ)
    (hd : ∀ v, (G.neighborFinset v).card ≤ d) (r : V)
    (family : Finset (Finset V))
    (hfamily : ∀ C ∈ family, C.card = b ∧ r ∈ C ∧
      ∀ S : Finset V, S ⊆ C → r ∈ S → S ≠ C →
        ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ G.Adj u v) :
    family.card ≤ d ^ (2 * (b - 1)) := by
  have hwalks (n : ℕ) (u v : V) : (G.finsetWalkLength n u v).card ≤ d ^ n := by
    induction n generalizing u v with
    | zero => simp only [finsetWalkLength]; split <;> [ (rename_i h; subst h; simp); simp]
    | succ n ih =>
      simp only [finsetWalkLength]
      exact Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g := fun _ => d ^ n) fun w _ => by simpa using ih w v).trans
        (by simpa [SimpleGraph.neighborFinset, pow_succ'] using Nat.mul_le_mul_right (d ^ n) (hd u)))
  refine (Finset.card_le_card (t := (G.finsetWalkLength (2 * (b - 1)) r r).image fun p => p.support.toFinset)
    fun C hC => ?_).trans (Finset.card_image_le.trans (hwalks _ r r))
  obtain ⟨hb, hr, hc⟩ := hfamily C hC
  obtain ⟨p, hp, hl⟩ := finite_connected_covering_tour G C r hr hc
  exact Finset.mem_image.mpr ⟨p, mem_finsetWalkLength_iff.mpr (hb ▸ hl), hp⟩

end HordijkSteelThreshold
