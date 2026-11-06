module

public import Chazelle.Golf

public import Chazelle.Core.RestoreNodeMath

/-!
# WP-E, the search: the witness offset of a node

The tests at the ends of a node chord in the open stretch `(0, L)` leave the offsets satisfying
`GEnd` (one side of the arrival `α`, which is the other end when it is in the open stretch).  If
the good vertex at the integer offset `x` passes (`WOK`), so does one of the integer offsets
`1`, `⌊da⌋ + 1`, `⌊db⌋ + 1` (the first offset after the last end before `x`), and every offset
that passes is on the side of the node chord of `x` (`witness_side_ok`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sideInArc)

/-- The condition the test at an end leaves, in offsets. -/
def GEnd (L d α : ℝ) (s : Prop) (v : ℝ) : Prop := (0 < d ∧ d < L) → (sideInArc d α v ↔ s)

/-- An offset passing both end tests. -/
def WOK (L da db αa αb : ℝ) (sa sb : Prop) (v : ℝ) : Prop :=
  0 < v ∧ v < L ∧ v ≠ da ∧ v ≠ db ∧ GEnd L da αa sa v ∧ GEnd L db αb sb v

/-- Without an end of the interval in `[u, x]`, the side is the same at `u` and `x`. -/
theorem side_same {a b u x : ℝ} (hux : u ≤ x) (ha : a < u ∨ x < a) (hb : b < u ∨ x < b) :
    sideInArc a b u ↔ sideInArc a b x := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> unfold sideInArc <;>
    split_ifs with h <;> constructor <;> intro h' <;>
    first
    | (left; linarith)
    | (right; linarith)
    | (exact ⟨⟡, ⟡⟩)
    | (exfalso; rcases h' with h' | h' <;> linarith)

variable {L da db αa αb : ℝ} {sa sb : Prop}

theorem gend_transfer {d d' α : ℝ} {s : Prop} (hα0 : 0 ≤ α) (hα : 0 < α → α < L → α = d')
    {ℓ u x : ℝ} (hℓ : 0 ≤ ℓ) (hℓu : ℓ < u) (hux : u ≤ x) (hxL : x < L)
    (hd : ¬ (ℓ < d ∧ d ≤ x)) (hd' : ¬ (ℓ < d' ∧ d' ≤ x)) (hx : GEnd L d α s x) :
    GEnd L d α s u := by
  intro hdL
  refine (side_same hux ?_ ?_).trans (hx hdL)
  · by_cases h : d ≤ ℓ
    · left; linarith
    · right; push Not at h; by_contra h'; push Not at h'; exact hd ⟨h, h'⟩
  · by_cases hin : 0 < α ∧ α < L
    · Ξ hα hin.1 hin.2
      by_cases h : d' ≤ ℓ
      · left; linarith
      · right; push Not at h; by_contra h'; push Not at h'; exact hd' ⟨h, h'⟩
    · rcases out_of hα0 hin with h | h
      · left; rw [h]; linarith
      · right; linarith

/-- **Transfer of the test conditions** from `x` to an offset `u ≤ x` with no end in
`(ℓ, x]`. -/
theorem wok_transfer (hαa0 : 0 ≤ αa) (hαa : 0 < αa → αa < L → αa = db) (hαb0 : 0 ≤ αb)
    (hαb : 0 < αb → αb < L → αb = da) {ℓ u x : ℝ} (hℓ : 0 ≤ ℓ) (hℓu : ℓ < u) (hux : u ≤ x)
    (hda : ¬ (ℓ < da ∧ da ≤ x)) (hdb : ¬ (ℓ < db ∧ db ≤ x))
    (hx : WOK L da db αa αb sa sb x) : WOK L da db αa αb sa sb u := by
  obtain ⟨hx0, hxL, -, -, ga, gb⟩ := hx
  refine ⟨⟡, ⟡, fun h => hda ⟨by rw [← h]; exact hℓu, by rw [← h]; exact hux⟩,
    fun h => hdb ⟨by rw [← h]; exact hℓu, by rw [← h]; exact hux⟩,
    gend_transfer hαa0 hαa hℓ hℓu hux hxL hda hdb ga,
    gend_transfer hαb0 hαb hℓ hℓu hux hxL hdb hda gb⟩

/-- **A witness offset exists among `1`, `⌊da⌋ + 1`, `⌊db⌋ + 1`.** -/
theorem witness_exists (hαa0 : 0 ≤ αa) (hαa : 0 < αa → αa < L → αa = db) (hαb0 : 0 ≤ αb)
    (hαb : 0 < αb → αb < L → αb = da) (hda0 : 0 ≤ da) (hdb0 : 0 ≤ db) {x : ℕ}
    (hx : WOK L da db αa αb sa sb x) :
    WOK L da db αa αb sa sb 1 ∨ (0 < da ∧ da < L ∧ WOK L da db αa αb sa sb (⌊da⌋₊ + 1 : ℕ)) ∨
      (0 < db ∧ db < L ∧ WOK L da db αa αb sa sb (⌊db⌋₊ + 1 : ℕ)) := by
  obtain ⟨hx0, hxL, hxa, hxb, ga, gb⟩ := hx
  have hx1 : (1 : ℝ) ≤ x := by
    have : 0 < x := by exact_mod_cast hx0
    exact_mod_cast this
  have fl : ∀ d : ℝ, 0 ≤ d → d < x → (d < ((⌊d⌋₊ + 1 : ℕ) : ℝ) ∧ ((⌊d⌋₊ + 1 : ℕ) : ℝ) ≤ x) :=
    fun d hd hdx => by
      refine ⟨by push_cast; exact Nat.lt_floor_add_one d, ?_⟩
      have : ⌊d⌋₊ < x := (Nat.floor_lt hd).2 hdx
      exact_mod_cast this
  by_cases hA : 0 < da ∧ da < x
  · by_cases hB : 0 < db ∧ db < x ∧ da < db
    · obtain ⟨h1, h2⟩ := fl db hdb0 hB.2.1
      exact Or.inr (Or.inr ⟨hB.1, ⟡, wok_transfer hαa0 hαa hαb0 hαb hdb0 h1 h2
        (fun h => by linarith [h.1, hB.2.2]) (fun h => by linarith [h.1]) ⟨hx0, hxL, hxa, hxb,
          ga, gb⟩⟩)
    · obtain ⟨h1, h2⟩ := fl da hda0 hA.2
      refine Or.inr (Or.inl ⟨hA.1, ⟡, wok_transfer hαa0 hαa hαb0 hαb hda0 h1 h2
        (fun h => by linarith [h.1]) (fun h => ?_) ⟨hx0, hxL, hxa, hxb, ga, gb⟩⟩)
      exact hB ⟨by linarith [h.1], lt_of_le_of_ne h.2 (Ne.symm hxb), by linarith [h.1]⟩
  · by_cases hB : 0 < db ∧ db < x
    · obtain ⟨h1, h2⟩ := fl db hdb0 hB.2
      refine Or.inr (Or.inr ⟨hB.1, ⟡, wok_transfer hαa0 hαa hαb0 hαb hdb0 h1 h2
        (fun h => ?_) (fun h => by linarith [h.1]) ⟨hx0, hxL, hxa, hxb, ga, gb⟩⟩)
      exact hA ⟨by linarith [h.1], lt_of_le_of_ne h.2 (Ne.symm hxa)⟩
    · refine Or.inl (wok_transfer hαa0 hαa hαb0 hαb le_rfl zero_lt_one hx1 (fun h => ?_)
        (fun h => ?_) ⟨hx0, hxL, hxa, hxb, ga, gb⟩)
      · exact hA ⟨h.1, lt_of_le_of_ne h.2 (Ne.symm hxa)⟩
      · exact hB ⟨h.1, lt_of_le_of_ne h.2 (Ne.symm hxb)⟩

/-- **Every passing offset is on the side of the good vertex.** -/
theorem witness_side_ok (hαa0 : 0 ≤ αa) (hαa : 0 < αa → αa < L → αa = db) (hαb0 : 0 ≤ αb)
    (hαb : 0 < αb → αb < L → αb = da) (hda0 : 0 ≤ da) (hdb0 : 0 ≤ db) (hne : da ≠ db)
    {u x : ℝ} (hu : WOK L da db αa αb sa sb u) (hx : WOK L da db αa αb sa sb x) :
    sideInArc da db u ↔ sideInArc da db x := by
  obtain ⟨hu0, huL, hua, hub, gau, gbu⟩ := hu
  obtain ⟨hx0, hxL, hxa, hxb, gax, gbx⟩ := hx
  exact stretch_side hda0 hdb0 hne (GA := GEnd L da αa sa) (GB := GEnd L db αb sb)
    (fun h1 h2 => ⟨αa, sa, hαa0, hαa, fun v => ⟨fun h => h ⟨h1, h2⟩, fun h _ => h⟩⟩)
    (fun h1 h2 => ⟨αb, sb, hαb0, hαb, fun v => ⟨fun h => h ⟨h1, h2⟩, fun h _ => h⟩⟩)
    hu0 huL hx0 hxL hua hub hxa hxb gau gax gbu gbx

end

end Restore

end Chazelle.Core
