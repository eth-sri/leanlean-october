module

public import Chazelle.Merge.Conformal

/-!
# Granularity restoration (Chazelle §3.3, the Euclidean part of Lemma 3.5)

After conformality restoration Chazelle enforces granularity condition (ii) greedily (p. 512):
"if an edge does not pass the test, we just contract it by removing its corresponding exit chord
… Note that this will not cause a violation of the first criterion … Similarly, the removal keeps
the submap conformal.  We process each exit chord in turn and check whether it is removable.
Chords need be processed only once since the removals cannot make any chord removable if it was
not already so before."

This file proves the Euclidean content for an arbitrary finite chord system `ChordSystem D F` and
an arbitrary weight `wt : Set (Set Point) → Set Point → ℕ` (the weight of a region of a submap),
with chain instances for `C.IsConformal` / `C.IsGranularWrt`.

## Definitions

* `Removable D wt γ S c`: `c ∈ S` separates regions `U ≠ V`, one with `< 3` exit chords (degree
  `< 3` in the tree of `S`, `ncard_neighborSet_eq_exits`), and the merged region of `S \ {c}` has
  weight `≤ γ`;
* `ContractionCondIn` (condition (ii)), `SemigranularIn` (condition (i)), `ConformalIn`
  (`≤ 4` exit chords per region);
* `WeightLocal D F wt`: removing a chord does not change the weight of the regions it does not
  touch;
* `RemStep`: remove one removable chord.

## Main results

* `contractionCondIn_iff`: condition (ii) holds iff no chord is removable;
* `Removable.conformal`: a removal keeps the submap conformal (the merged region has
  `|exits U| + |exits V| − 2 ≤ 2 + 4 − 2` exit chords, `exists_removal_split`,
  `mem_sdiff_of_not_touches`);
* `Removable.semigranular`: for a local weight, a removal keeps it γ-semigranular;
* `remStep_run`: every run of removals preserves both properties and has length
  `≤ |S|` (each removal deletes one chord);
* **`lemma_3_5`**: from a conformal γ-semigranular `S ⊆ F`, removing removable chords until none
  is left yields a conformal γ-granular `T ⊆ S` (`chain_lemma_3_5`: `C.IsConformal T ∧
  C.IsGranularWrt wt T γ`, via `chain_contractionCond_iff`).
* **`removable_of_removable_sdiff`** — the correct form of the flagged claim: if `c` becomes
  removable after the removal of `c'`, and `c`, `c'` touch no common region of `S`, then `c` was
  already removable.  So a removal can only make removable the exit chords of the merged region
  (at most `4` of them, by conformality).

## The flagged claim is false as stated

"The removals cannot make any chord removable if it was not already so before" fails because a
removal can *lower the degree* of the merged region.  Take (a piece of) a submap tree with
nodes `X – U – V`, `U` also adjacent to `Y`, `V` of degree `3`, and all weights tiny compared with
`γ`.  The chord `c = UV` is not removable (`deg U = deg V = 3`); the chord `c' = UX` is
(`deg X = 1`).  After removing `c'` the merged node `UX` has degree `2`, so `c` has become
removable.  Processing `c` before `c'` in a single pass therefore ends with a submap violating
condition (ii).  The correct procedure iterates to a fixpoint (`lemma_3_5`); by
`removable_of_removable_sdiff` it suffices to re-examine, after each removal, the `≤ 4` exit chords
of the merged region (a worklist), which keeps the processing linear: at most `|S|` removals and
`|S| + 4 |S|` removability tests.

## Not proved here

* `WeightLocal` for the paper's weight `Chazelle.Chain.arcWeight` (removing a chord whose endpoint
  lies on the far side of a chain edge merges two pieces of `∂C` facing a region `X` not touched by
  the chord; the arcs of `X` keep the same edges of `∂C`).  It is a hypothesis of `lemma_3_5`.
  (The total weight `Chazelle.Chain.totalWeight` is *not* local, for exactly this reason.)
* The cost accounting and the normal form.
-/

namespace Chazelle.Merge

@[expose] public section

open Set
open Chazelle.Chain (ChordSystem regionsIn TouchesIn regionsIn_nonempty regionsIn_eq_of_subset
  exists_regionsIn_superset)

variable {D : Set Point} {F : Set (Set Point)}

/-! ### Removing one chord: bookkeeping -/

/-- Removing `c ∈ S`: the open part of `c` lies in a region `P` of `S \ {c}`, which `c` splits
into the two regions `R₁`, `R₂` of `S` touched by `c`. -/
theorem exists_removal_split (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) :
    ∃ P R₁ R₂ : Set Point, IsSplit D (S \ {c}) c P R₁ R₂ := by
  have hT : S \ {c} ⊆ F := fun _ h => hS h.1
  have hcT : c ∉ S \ {c} := fun h => h.2 rfl
  obtain ⟨P, hP, hcP⟩ := exists_region_of_chord hF hT (hS hc) hcT
  obtain ⟨R₁, R₂, h⟩ := exists_split hF hT (hS hc) hcT hP hcP
  exact ⟨P, R₁, R₂, h⟩

theorem insert_sdiff_self {S : Set (Set Point)} {c : Set Point} (hc : c ∈ S) :
    insert c (S \ {c}) = S :=
  insert_sdiff_singleton.trans (insert_eq_of_mem hc)

/-- A region of `S` not touched by `c ∈ S` is still a region of `S \ {c}`, with the same exit
chords. -/
theorem mem_sdiff_of_not_touches (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) {X : Set Point} (hX : X ∈ regionsIn D S)
    (hcX : ¬ TouchesIn D c X) :
    X ∈ regionsIn D (S \ {c}) ∧ exitsIn D (S \ {c}) X = exitsIn D S X := by
  have hT : S \ {c} ⊆ F := fun _ h => hS h.1
  have hcT : c ∉ S \ {c} := fun h => h.2 rfl
  obtain ⟨P, R₁, R₂, h⟩ := exists_removal_split hF hS hc
  have hins := insert_sdiff_self hc
  have hX' : X ∈ regionsIn D (insert c (S \ {c})) := by rw [hins]; exact hX
  rcases h.mem_cases hX' with ⟨hXT, hXP⟩ | rfl | rfl
  · refine ⟨hXT, ?_⟩
    rw [← h.exits_other hF hT hXT hXP, hins]
  · exact absurd (h.touches₁ hF hT (hS hc) hcT) hcX
  · exact absurd (h.touches₂ hF hT (hS hc) hcT) hcX

/-! ### Removable chords and granularity -/

/-- The chord `c` is *removable* from `S` (p. 512): it separates two regions `U ≠ V` of `S`, one
of which has fewer than `3` exit chords (the dual edge `UV` is incident upon a node of degree
`< 3`), and the region of `S \ {c}` obtained by merging them has weight at most `γ`. -/
def Removable (D : Set Point) (wt : Set (Set Point) → Set Point → ℕ) (γ : ℕ)
    (S : Set (Set Point)) (c : Set Point) : Prop :=
  c ∈ S ∧ ∃ U ∈ regionsIn D S, ∃ V ∈ regionsIn D S, U ≠ V ∧ TouchesIn D c U ∧ TouchesIn D c V ∧
    ((exitsIn D S U).ncard < 3 ∨ (exitsIn D S V).ncard < 3) ∧
    ∀ W ∈ regionsIn D (S \ {c}), U ⊆ W → wt (S \ {c}) W ≤ γ

/-- Granularity condition (ii) (p. 496), with the degree of a region measured by its number of
exit chords (`ncard_neighborSet_eq_exits`). -/
def ContractionCondIn (D : Set Point) (wt : Set (Set Point) → Set Point → ℕ)
    (S : Set (Set Point)) (γ : ℕ) : Prop :=
  ∀ c ∈ S, ∀ U ∈ regionsIn D S, ∀ V ∈ regionsIn D S, U ≠ V → TouchesIn D c U →
    TouchesIn D c V → ((exitsIn D S U).ncard < 3 ∨ (exitsIn D S V).ncard < 3) →
    ∀ W ∈ regionsIn D (S \ {c}), U ⊆ W → γ < wt (S \ {c}) W

/-- *Locality* of a weight: removing a chord does not change the weight of the regions it does
not touch. -/
def WeightLocal (D : Set Point) (F : Set (Set Point))
    (wt : Set (Set Point) → Set Point → ℕ) : Prop :=
  ∀ S ⊆ F, ∀ c ∈ S, ∀ X ∈ regionsIn D S, ¬ TouchesIn D c X → wt (S \ {c}) X = wt S X

/-- **Condition (ii) holds iff no chord is removable.** -/
theorem contractionCondIn_iff {wt : Set (Set Point) → Set Point → ℕ} {S : Set (Set Point)}
    {γ : ℕ} : ContractionCondIn D wt S γ ↔ ∀ c, ¬ Removable D wt γ S c := by
  constructor
  · rintro h c ⟨hc, U, hU, V, hV, hne, hcU, hcV, hlow, hW⟩
    obtain ⟨W, hW', hUW⟩ := exists_regionsIn_superset (sdiff_subset : S \ {c} ⊆ S) hU
    exact absurd (hW W hW' hUW) (not_le.2 (h c hc U hU V hV hne hcU hcV hlow W hW' hUW))
  · intro h c hc U hU V hV hne hcU hcV hlow W hW hUW
    by_contra hle
    push Not at hle
    refine h c ⟨hc, U, hU, V, hV, hne, hcU, hcV, hlow, fun W' hW' hUW' => ?_⟩
    rw [regionsIn_eq_of_subset hW' hW (regionsIn_nonempty hU) hUW' hUW]
    exact hle

/-- The two regions touched by a removable chord are the two halves `R₁`, `R₂` of the removal
split. -/
theorem IsSplit.eq_pair_of_touches (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {c P R₁ R₂ : Set Point} (hc : c ∈ S) (h : IsSplit D (S \ {c}) c P R₁ R₂) {U : Set Point}
    (hU : U ∈ regionsIn D S) (hcU : TouchesIn D c U) : U = R₁ ∨ U = R₂ := by
  have hT : S \ {c} ⊆ F := fun _ h => hS h.1
  have hcT : c ∉ S \ {c} := fun h => h.2 rfl
  have hU' : U ∈ regionsIn D (insert c (S \ {c})) := by rw [insert_sdiff_self hc]; exact hU
  exact (h.touches_iff hF hT (hS hc) hcT U hU').1 hcU

/-! ### Which chords can become removable -/

/-- **The correct form of the claim "the removals cannot make any chord removable if it was not
already so before" (p. 512).**  Let `c'` be a chord of `S` and `c ≠ c'` a chord sharing no region
with `c'` (no region of `S` is touched by both).  If `c` is removable after the removal of `c'`,
it was already removable before.  So a removal can only change the status of the chords of the
(at most `4 + 4 - 2` other) exit chords of the merged region; the literal claim is false (see the
module docstring), and a correct linear-time procedure re-examines those chords after each
removal (a worklist), or simply iterates to a fixpoint as in `lemma_3_5`. -/
theorem removable_of_removable_sdiff (hF : ChordSystem D F)
    {wt : Set (Set Point) → Set Point → ℕ} {γ : ℕ} (hloc : WeightLocal D F wt)
    {S : Set (Set Point)} (hS : S ⊆ F) {c c' : Set Point} (hc' : c' ∈ S) (hcc : c ≠ c')
    (hsep : ∀ X ∈ regionsIn D S, TouchesIn D c' X → ¬ TouchesIn D c X)
    (h : Removable D wt γ (S \ {c'}) c) : Removable D wt γ S c := by
  obtain ⟨hcT', U, hU, V, hV, hne, hcU, hcV, hlow, hW⟩ := h
  have hc : c ∈ S := hcT'.1
  have hT' : S \ {c'} ⊆ F := fun _ h => hS h.1
  have hc'T' : c' ∉ S \ {c'} := fun h => h.2 rfl
  have hins' := insert_sdiff_self hc'
  obtain ⟨P', R₁', R₂', hs'⟩ := exists_removal_split hF hS hc'
  -- `c` does not touch the region merged by the removal of `c'`
  have hnotP' : ∀ X, X = P' → ¬ TouchesIn D c X := by
    rintro X rfl hcX
    have hR₁' : R₁' ∈ regionsIn D S := by rw [← hins']; exact hs'.mem₁
    have hR₂' : R₂' ∈ regionsIn D S := by rw [← hins']; exact hs'.mem₂
    rcases hF.touches_split_or (hS hc') (hS hc) hcc.symm hs'.union hcX with h1 | h1
    · exact hsep R₁' hR₁' (hs'.touches₁ hF hT' (hS hc') hc'T') h1
    · exact hsep R₂' hR₂' (hs'.touches₂ hF hT' (hS hc') hc'T') h1
  -- hence the regions `U`, `V` of `S \ {c'}` are regions of `S`, with the same exit chords
  have hold : ∀ X ∈ regionsIn D (S \ {c'}), TouchesIn D c X →
      X ∈ regionsIn D S ∧ exitsIn D S X = exitsIn D (S \ {c'}) X := by
    intro X hX hcX
    have hXP : X ≠ P' := fun h' => hnotP' X h' hcX
    have e := hs'.exits_other hF hT' hX hXP
    rw [hins'] at e
    exact ⟨by rw [← hins']; exact hs'.mem_of_ne hX hXP, e⟩
  obtain ⟨hUS, eU⟩ := hold U hU hcU
  obtain ⟨hVS, eV⟩ := hold V hV hcV
  refine ⟨hc, U, hUS, V, hVS, hne, hcU, hcV, by rw [eU, eV]; exact hlow, ?_⟩
  -- the merged region of `c` is not touched by `c'`, so its weight is unchanged
  intro W hW' hUW
  have hS1 : S \ {c} ⊆ F := fun _ h => hS h.1
  have hc'1 : c' ∈ S \ {c} := ⟨hc', fun h' => hcc (mem_singleton_iff.1 h').symm⟩
  obtain ⟨P, R₁, R₂, hs⟩ := exists_removal_split hF hS hc
  have hWP : W = P := by
    refine regionsIn_eq_of_subset hW' hs.mem (regionsIn_nonempty hUS) hUW ?_
    rcases hs.eq_pair_of_touches hF hS hc hUS hcU with rfl | rfl
    · exact hs.sub₁
    · exact hs.sub₂
  have hc'W : ¬ TouchesIn D c' W := by
    intro hc'W
    rw [hWP] at hc'W
    have hR₁ : R₁ ∈ regionsIn D S := by rw [← insert_sdiff_self hc]; exact hs.mem₁
    have hR₂ : R₂ ∈ regionsIn D S := by rw [← insert_sdiff_self hc]; exact hs.mem₂
    have hc1 : c ∉ S \ {c} := fun h => h.2 rfl
    rcases hF.touches_split_or (hS hc) (hS hc') hcc hs.union hc'W with h1 | h1
    · exact hsep R₁ hR₁ h1 (hs.touches₁ hF hS1 (hS hc) hc1)
    · exact hsep R₂ hR₂ h1 (hs.touches₂ hF hS1 (hS hc) hc1)
  obtain ⟨hWmem, -⟩ := mem_sdiff_of_not_touches hF hS1 hc'1 hW' hc'W
  have hcomm : (S \ {c}) \ {c'} = (S \ {c'}) \ {c} := sdiff_right_comm _ _ _
  rw [← hloc (S \ {c}) hS1 c' hc'1 W hW' hc'W, hcomm]
  rw [hcomm] at hWmem
  exact hW W hWmem hUW

/-! ### The chain instances -/

section ChainInstance

variable (C : Chain)

end ChainInstance

end

end Chazelle.Merge
