module

public import Chazelle.Core.GranRemove
public import Chazelle.Core.FactsInterior

/-!
# WP-E, part 1: the mathematics of conformality restoration (Lemmas 3.3, 3.4) for disk models

`RestoreSpec` (`Chazelle.Core.SpecMerge`) asks, from a γ-semigranular submap `S` of a good model
`M` whose full augmented maps have degree `≤ D` (`M.FullDegLe Q D`), for a finer submap `T ⊇ S`
of degree `≤ D` that is still γ-semigranular.  This file proves the mathematics of that step in
the language of the disk models (`Model`), on top of the Euclidean library
`Chazelle.Merge.Conformal` (`lemma_3_3`, `lemma_3_4`, the excess `potential`) and the arc/weight
facts of WP-F (`Chazelle.Core.GranRemove`).

## Results

* `semigranular_insert`, `semigranular_mono`: **adding chords never increases weights**: a
  γ-semigranular admissible family stays γ-semigranular when admissible chords are added (the
  two halves of a split region weigh at most the region, `Gran.weight_le_merged₁`, and the other
  regions keep their arcs, `Gran.weight_other`).
* `full_subset_adm`, `full_finite`, `fullSystem`: the full map of a good model is a finite
  admissible family, so `M.Full ∪ S` is a chord system of the domain for every finite admissible
  `S`.
* `exists_step` (**Lemma 3.3**): if a region `R` of the chord family `S` has more than `D` exit
  chords, some chord `e ∈ M.Full \ S` lies inside `R` and **splits it well**
  (`SplitsWell`: each of the two new regions keeps at least two exit chords of `R`).
* `potential_step`: **every** admissible chord that splits a region of degree `> D` well (not
  only the vertex chords of Lemma 3.3: Lemma 3.2 finds a point of one arc seeing another, which
  need not be a vertex) lowers the excess `Merge.potential M.D D S = Σ_R (deg R - D)` by at least
  one (`D ≥ 3`).
* `potential_le_two_mul`: the excess of `S` is at most `2 |S|`; `degLe_iff_potential_eq_zero`.
* `run_bound`: a run of `k` good steps from `S` has `k ≤ potential S ≤ 2 |S|`, stays admissible
  and γ-semigranular.
* `restore_exists` (**Lemma 3.4**): some `T` with `S ⊆ T ⊆ M.Full ∪ S`, `M.DegLe T D`,
  `M.Semigranular T γ` and `|T \ S| ≤ 2 |S|`; `restore_exists_family`: `T` is a chord family
  when the full map lies at vertex heights of `Q` (`FullHeights`, proved for the interior model
  of `Q`: `fullHeights_interior`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (ChordSystem regionsIn TouchesIn)
open Chazelle.Merge (exitsIn potential IsSplit)

variable {M : Model}

/-! ## Degrees as exit-chord counts -/

/-! ## Adding chords keeps semigranularity -/

/-- **Adding one admissible chord keeps γ-semigranularity**: the region split by the chord is
replaced by two regions whose arcs lie inside its arcs, and the other regions keep their arcs. -/
theorem semigranular_insert (hM : WalkAx M) {S : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) {γ : ℕ}
    (h : M.Semigranular S γ) : M.Semigranular (insert e S) γ := by
  have hT : insert e S ⊆ M.Adm := insert_subset he hS
  have hTfin : (insert e S).Finite := hfin.insert e
  have hsys := hM.sys _ hT hTfin
  have heT : e ∈ insert e S := mem_insert e S
  have hsd : insert e S \ {e} = S := insert_sdiff_self_of_notMem heS
  obtain ⟨P, hP, heP⟩ := Merge.exists_region_of_chord hsys (subset_insert e S) heT heS
  obtain ⟨R₁, R₂, hs⟩ := Merge.exists_split hsys (subset_insert e S) heT heS hP heP
  have hs' : IsSplit M.D (insert e S \ {e}) e P R₁ R₂ := by rwa [hsd]
  have hPγ : M.weight (insert e S \ {e}) P ≤ γ := by rw [hsd]; exact h P hP
  intro U hU
  rcases Gran.split_cases heT hs' hU with rfl | rfl | ⟨hU', hUP⟩
  · exact (Gran.weight_le_merged₁ hM hT hTfin heT hs').trans hPγ
  · exact (Gran.weight_le_merged₂ hM hT hTfin heT hs').trans hPγ
  · have h1 : U ≠ R₁ := hs'.ne_of_mem_old hU' hUP
    have h2 : U ≠ R₂ := hs'.symm.ne_of_mem_old hU' hUP
    rw [← Gran.weight_other hM hT hTfin heT hs' hU h1 h2]
    rw [hsd] at hU' ⊢
    exact h U hU'

/-- **Adding any finite set of admissible chords keeps γ-semigranularity.** -/
theorem semigranular_mono (hM : WalkAx M) {S T : Set (Set Point)} (hST : S ⊆ T)
    (hT : T ⊆ M.Adm) (hTfin : T.Finite) {γ : ℕ} (h : M.Semigranular S γ) :
    M.Semigranular T γ := by
  suffices key : ∀ k, ∀ S : Set (Set Point), S ⊆ T → (T \ S).ncard ≤ k →
      M.Semigranular S γ → M.Semigranular T γ from key _ S hST le_rfl h
  intro k
  induction k with
  | zero =>
    intro S hST hk hS
    have he : T \ S = ∅ :=
      (ncard_eq_zero (hTfin.subset sdiff_subset)).1 (Nat.le_zero.1 hk)
    have : T = S := Subset.antisymm (sdiff_eq_empty.1 he) hST
    rwa [this]
  | succ k ih =>
    intro S hST hk hS
    by_cases he : (T \ S).Nonempty
    · obtain ⟨e, heT, heS⟩ := he
      have hins : insert e S ⊆ T := insert_subset heT hST
      refine ih (insert e S) hins ?_ ?_
      · have hsub : T \ insert e S ⊆ (T \ S) \ {e} := by
          rintro x ⟨hxT, hx⟩
          exact ⟨⟨hxT, fun h' => hx (Or.inr h')⟩, fun h' => hx (Or.inl h')⟩
        have h1 := ncard_le_ncard hsub ((hTfin.subset sdiff_subset).sdiff)
        have h2 := ncard_sdiff_singleton_add_one (show e ∈ T \ S from ⟨heT, heS⟩)
          (hTfin.subset sdiff_subset)
        omega
      · exact semigranular_insert hM (hST.trans hT) (hTfin.subset hST) (hT heT) heS hS
    · rw [not_nonempty_iff_eq_empty] at he
      have : T = S := Subset.antisymm (sdiff_eq_empty.1 he) hST
      rwa [this]

/-! ## The full map of a good model -/

/-- A vertex chord of a simple polygon is an admissible chord of its interior model. -/
theorem chords_subset_interiorAdm {Q : Polygon} (hQ : Q.Simple) :
    Visibility.chords Q ⊆ (interiorModel Q).Adm := by
  intro c hc
  obtain ⟨i, σ, -, -, -, rfl, hch⟩ := Visibility.chords_spec hQ hc
  refine ⟨_, _, _, ⟨hch.lt, fun h => h.2 hch.left_mem, fun h => h.2 hch.right_mem,
    fun x h1 h2 => hch.open_int x h1 h2⟩, Visibility.chordSet_eq_hseg Q i σ⟩

/-- **The full map of a good model is admissible.** -/
theorem full_subset_adm (hG : GoodModel M) : M.Full ⊆ M.Adm := by
  rcases hG with ⟨C, -, rfl⟩ | ⟨Q, hQ, rfl⟩
  · exact Merge.chords_subset_augChords C
  · exact chords_subset_interiorAdm hQ

/-- **The full map of a good model is finite.** -/
theorem full_finite (hG : GoodModel M) : M.Full.Finite := by
  rcases hG with ⟨C, -, rfl⟩ | ⟨Q, -, rfl⟩
  · exact C.chords_finite
  · exact Visibility.chords_finite Q

/-- For a finite admissible `S`, the augmented full map `M.Full ∪ S` is a chord system. -/
theorem fullSystem (hG : GoodModel M) {S : Set (Set Point)} (hS : S ⊆ M.Adm) (hfin : S.Finite) :
    ChordSystem M.D (M.Full ∪ S) :=
  (walkAx_of_goodModel hG).sys _ (union_subset (full_subset_adm hG) hS)
    ((full_finite hG).union hfin)

/-! ## Good splitting steps -/

/-- **The chord `e` splits the region `R` of `S` well**: `e` is a new chord whose open part lies
in `R`, and each of the two regions of `insert e S` inside `R` is touched by at least two exit
chords of `R` (in the paper's words, `e` joins two nonconsecutive arcs of `R`). -/
def SplitsWell (M : Model) (S : Set (Set Point)) (R e : Set Point) : Prop :=
  e ∉ S ∧ e ∩ M.D ⊆ R ∧ ∀ P ∈ regionsIn M.D (insert e S), P ⊆ R → 2 ≤ (exitsIn M.D S P).ncard

/-- **Lemma 3.3 for good models.**  If a region `R` of the chord family `S` has more than `D`
exit chords while the augmented full maps have degree `≤ D`, then a chord of the full map splits
`R` well. -/
theorem exists_step (hG : GoodModel M) {Q : Polygon} {D : ℕ} (hfull : M.FullDegLe Q D)
    {S : Set (Set Point)} (hS : M.ChordFamily Q S) {R : Set Point} (hR : R ∈ regionsIn M.D S)
    (hdeg : D < (exitsIn M.D S R).ncard) : ∃ e ∈ M.Full, SplitsWell M S R e := by
  obtain ⟨e, he, heS, heR, hsplit⟩ := Merge.lemma_3_3 (fullSystem hG hS.2.1 hS.1)
    subset_union_right hR (fun U hU _ => hfull S hS U hU) hdeg
  exact ⟨e, he.resolve_right heS, heS, heR, hsplit⟩

/-- **The two halves of a good split** have at least `3` and fewer than `deg R` exit chords. -/
theorem splitsWell_degrees (hM : WalkAx M) {S : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ regionsIn M.D S) {e : Set Point}
    (he : e ∈ M.Adm) (hw : SplitsWell M S R e) :
    ∀ P ∈ regionsIn M.D (insert e S), P ⊆ R →
      3 ≤ (exitsIn M.D (insert e S) P).ncard ∧
        (exitsIn M.D (insert e S) P).ncard < (exitsIn M.D S R).ncard := by
  obtain ⟨heS, heR, hsplit⟩ := hw
  have hF := hM.sys _ (insert_subset he hS) (hfin.insert e)
  have hSF : S ⊆ insert e S := subset_insert e S
  have heF : e ∈ insert e S := mem_insert e S
  intro P hP hPR
  obtain ⟨R₁, R₂, h⟩ := Merge.exists_split hF hSF heF heS hR heR
  have e0 := h.ncard_exits hF hSF heF heS (subset_refl S)
  have e1 := h.exits_insert₁ hF hSF heF heS
  have e2 := h.exits_insert₂ hF hSF heF heS
  have b1 := hsplit R₁ h.mem₁ h.sub₁
  have b2 := hsplit R₂ h.mem₂ h.sub₂
  rcases h.eq_of_subset hP hPR with rfl | rfl <;> omega

/-! ## Runs of good steps (Lemma 3.4) -/

end

end Restore

end Chazelle.Core
