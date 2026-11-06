module

public import Chazelle.Core.SweepAnswer3
public import Chazelle.Core.SweepWalk
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# The sweep (WP-D), part 17: the abstract machine, generic walk facts

The abstract machine of the sweep (design `design-merge-v2.md` §9) moves along the walk of a model
from key to key.  Its state is anchored at an event key `K` (a walk position `(pK, tK)`): the
region faced **just after** `K` (`AfterFaces`) carries the current label, and every non-cut
position up to the next cut faces that region.  This file proves the generic facts, for any good
model `M` and a base `g` of the offsets:

* `off_add_small`, `eq_of_off_small`: offsets along one walk edge;
* `after_region_exists`: some region is faced just after every key, and no cut lies just after it;
* `faces_after_gap`: a non-cut position after `K` with no cut in between faces the region faced
  just after `K`;
* `before_region_exists`, `faces_before_gap`: the same just before a key.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft freeIn regionsIn)
open WalkEmbed

namespace Sweep

/-- Offsets along one walk edge. -/
theorem off_add_small {n g : ℕ} (_hg : g < n) {p : ℕ} (_hp : p < n) {t s : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ s) (hts : t + s < 1) :
    off n g ((p : ℝ) + (t + s)) = off n g ((p : ℝ) + t) + s := by
  unfold off
  have hgp : (g : ℝ) ≤ p ∨ (p : ℝ) + 1 ≤ g := by
    rcases le_or_gt g p with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  rcases hgp with h | h
  · rwring [ite_eq_left (by linarith), ite_eq_left (by linarith)]
  · rwring [ite_eq_right (by linarith), ite_eq_right (by linarith)]

/-- A key whose offset is slightly above that of `(p, t)` (on the same edge) is the key
`p + t + u`. -/
theorem eq_of_off_small {n g : ℕ} (hg : g < n) {p : ℕ} (hp : p < n) {t u x : ℝ} (ht : 0 ≤ t)
    (hu : 0 ≤ u) (htu : t + u < 1) (hx0 : 0 ≤ x) (hxn : x < n)
    (h : off n g x = off n g ((p : ℝ) + t) + u) : x = (p : ℝ) + t + u := by
  have hpn : (p : ℝ) + 1 ≤ n := by exact_mod_cast hp
  have hgn : (g : ℝ) < n := by exact_mod_cast hg
  unfold off at h
  have hgp : (g : ℝ) ≤ p ∨ (p : ℝ) + 1 ≤ g := by
    rcases le_or_gt g p with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  split_ifs at h with h1 h2 h2 <;> rcases hgp with h3 | h3 <;> linarith

variable {M : Model}

/-- **The region faced just after a key**, and a cut-free stretch after it. -/
theorem after_region_exists (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {g : ℕ} (hg : g < M.W.n) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    ∃ δ > (0 : ℝ), t + δ ≤ 1 ∧ (∀ s ∈ Ioo (0 : ℝ) δ, ¬ M.IsCut F ((p : ℝ) + (t + s))) ∧
      ∃ G ∈ M.regions F, AfterFaces M p t G := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_not_cut_after hM hF hfin ((p : ℝ) + t))
  have hδ₀' : (0 : ℝ) < δ₀ := hδ₀
  set δ := min δ₀ (1 - t) with hδ
  have hδ0 : 0 < δ := lt_min hδ₀' (by linarith)
  have hδ1 : δ ≤ δ₀ := min_le_left _ _
  have hδ2 : δ ≤ 1 - t := min_le_right _ _
  have hnc : ∀ s ∈ Ioo (0 : ℝ) δ, ¬ M.IsCut F ((p : ℝ) + (t + s)) := by
    intro s hs
    have := hsub ⟨hs.1, lt_of_lt_of_le hs.2 hδ1⟩
    rw [Set.mem_ofPred_eq, add_assoc] at this
    exact this
  refine ⟨δ, hδ0, by linarith, hnc, ?_⟩
  obtain ⟨U, hU, hfU⟩ := hM.exists_faces_of_not_cut hF hfin hp
    (t := t + δ / 2) ⟨by linarith, by linarith⟩ (hnc (δ / 2) ⟨by linarith, by linarith⟩)
  refine ⟨U, hU, δ, hδ0, fun s hs0 hs1 hs2 => ?_⟩
  have hcs  := hnc s ⟨hs0, hs1⟩
  obtain ⟨U', hU', hfU'⟩ := hM.exists_faces_of_not_cut hF hfin hp (t := t + s)
    ⟨by linarith, hs2⟩ hcs
  suffices U' = U by rwx [← this]
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg _
  have hgn : (g : ℝ) < M.W.n := by exact_mod_cast hg
  -- positions of the cut-free stretch face one region
  have key : ∀ a b : ℝ, 0 < a → a < b → b < δ → ∀ A B : Set Point, A ∈ M.regions F →
      B ∈ M.regions F → M.Faces p (t + a) A → M.Faces p (t + b) B → A = B := by
    intro a b ha hab hb A B hA hB hfA hfB
    refine same_region_of_gap hM hF hfin hg0 hgn hA hB hp hp ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (hnc a ⟨ha, by linarith⟩)
      (hnc b ⟨by linarith, hb⟩) hfA hfB ?_ ?_
    · rw [off_add_small hg hp ht0 ha.le (by linarith),
        off_add_small hg hp ht0 (by linarith) (by linarith)]
      linarith
    · intro x hx hx0 hxn ⟨h1, h2⟩
      rw [off_add_small hg hp ht0 ha.le (by linarith)] at h1
      rw [off_add_small hg hp ht0 (by linarith) (by linarith)] at h2
      set u := off M.W.n g x - off M.W.n g ((p : ℝ) + t) with hu
      have hxe := eq_of_off_small hg hp ht0 (u := u) (by linarith) (by linarith) hx0 hxn
        (by rwring [hu])
      exact hnc u ⟨by linarith, by linarith⟩ (by rw [hxe, add_assoc] at hx; exact hx)
  rcases lt_trichotomy s (δ / 2) with h | h | h
  · exact key s (δ / 2) hs0 h (by linarith) U' U hU' hU hfU' hfU
  · subst h; exact WalkAx.faces_unique hU' hU hfU' hfU
  · exact (key (δ / 2) s (by linarith) h hs1 U U' hU hU' hfU hfU').symm

end Sweep

end

end Chazelle.Core
