module

public import Chazelle.Core.RestoreStretch

/-!
# WP-E, the search: what a failed test at a node chord end tells

`side_after`: just after a key `k`, the side of an interval `(a, b)` is `k = a ∨ k ∈ (a, b)`.

`end_side`: if the test at a position `a` strictly inside the arc `Aᵢ` gave a chord `aa'` that
fails `CountOK`, the good vertex `X` (whose chord succeeds, from `Aᵢ` to `Aⱼ`) is on the side
of `(ka, ka')` that contains the points just after the start `aⱼ` of `Aⱼ` (`prune`): it is in
`(ka, ka')` iff `aⱼ = ka ∨ aⱼ ∈ (ka, ka')`.  The search computes this bit with key comparisons.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)

theorem lt_after (a k : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (a < k + ε ↔ a ≤ k) := by
  by_cases h : a ≤ k
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ⟨fun _ => h, fun _ => by have : (0 : ℝ) < ε := hε; linarith⟩
  · push Not at h
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < a - k by linarith)] with ε hε
    exact ⟨fun h' => by linarith [hε.2], fun h' => by linarith⟩

theorem after_lt (b k : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (k + ε < b ↔ k < b) := by
  by_cases h : k < b
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < b - k by linarith)] with ε hε
    exact ⟨fun _ => h, fun _ => by linarith [hε.2]⟩
  · push Not at h
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ⟨fun h' => by have : (0 : ℝ) < ε := hε; linarith, fun h' => by linarith⟩

/-- **The side just after a key.** -/
theorem side_after {a b : ℝ} (hab : a ≠ b) (k : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (sideInArc a b (k + ε) ↔ (k = a ∨ sideInArc a b k)) := by
  filter_upwards [lt_after a k, after_lt b k] with ε h1 h2
  unfold sideInArc
  split_ifs with h
  · rw [h1, h2]
    constructor
    · rintro ⟨h3, h4⟩
      rcases h3.lt_or_eq with h3 | h3
      · exact Or.inr ⟨h3, h4⟩
      · exact Or.inl h3.symm
    · rintro (rfl | ⟨h3, h4⟩)
      · exact ⟨le_rfl, h⟩
      · exact ⟨h3.le, h4⟩
  · rw [h1, h2]
    have hba  := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hab)
    constructor
    · rintro (h3 | h3)
      · rcases h3.lt_or_eq with h3 | h3
        · exact Or.inr (Or.inl h3)
        · exact Or.inl h3.symm
      · exact Or.inr (Or.inr h3)
    · rintro (rfl | h3 | h3)
      · exact Or.inl le_rfl
      · exact Or.inl h3.le
      · exact Or.inr h3

/-- Just after its start, a key interval contains the keys. -/
theorem after_start (a b : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b (a + ε) := by
  by_cases hab : a = b
  · subst hab
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    unfold sideInArc; rw [ite_eq_right (lt_irrefl a)]; left; linarith
  · filter_upwards [side_after hab a] with ε h
    exact h.2 (Or.inl rfl)

/-- **The side of the good vertex** after a failed test at `a`, from `prune`. -/
theorem end_side {ka kf kx aj bj : ℝ} (hakf : ka ≠ kf)
    (hpr : ∀ y, sideInArc aj bj y → (sideInArc ka kf kx ↔ sideInArc ka kf y)) :
    sideInArc ka kf kx ↔ (aj = ka ∨ sideInArc ka kf aj) := by
  obtain ⟨ε, h1, h2⟩ := ((after_start aj bj).and (side_after hakf aj)).exists
  exact (hpr _ h1).trans h2

/-- **The side of the good vertex after a failed test**, in the terms of `prune`. -/
theorem prune_side {M : Model} (hM : WalkAx M) {S : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) (hne : S.Nonempty) {R : Set Point} {ai bi aj bj : ℝ}
    (hAi : M.IsArc S R ai bi) (hAj : M.IsArc S R aj bj) (hij : ai ≠ aj)
    {ea : Set Point} (hea : ea ∈ M.Adm) {pa pa' : ℕ} {ta ta' : ℝ}
    (hA : SideAttach M.W ea pa ta) (hA' : SideAttach M.W ea pa' ta')
    (hAA' : sidePt M.W pa ta ≠ sidePt M.W pa' ta') (hka : sideInArc ai bi (pa + ta))
    {ex : Set Point} (hex : ex ∈ M.Adm) {px px' : ℕ} {tx tx' : ℝ}
    (hX : SideAttach M.W ex px tx) (hX' : SideAttach M.W ex px' tx')
    (hXX' : sidePt M.W px tx ≠ sidePt M.W px' tx') (hkx : ClosedArc ai bi (px + tx))
    (hkx' : ClosedArc aj bj (px' + tx'))
    (hgood : CountOK M S R (px + tx) (px' + tx')) (hbad : ¬ CountOK M S R (pa + ta) (pa' + ta'))
    (hxa : (px : ℝ) + tx ≠ pa + ta) (hxa' : (px : ℝ) + tx ≠ pa' + ta') :
    sideInArc (pa + ta) (pa' + ta') (px + tx) ↔
      (aj = pa + ta ∨ sideInArc (pa + ta) (pa' + ta') aj) :=
  end_side (WalkAx.key_ne_of_pt_ne hA hA' hAA') (prune hM hS hfin hne hAi hAj hij hea hA hA' hAA' hka
    hex hX hX' hXX' hkx hkx' hgood hbad hxa hxa').2

end

end Restore

end Chazelle.Core
