module

public import Chazelle.Core.RestoreLink

/-!
# WP-E, part 5: one round of the restoration driver

In one round the driver adds, to every region `R` of `S` with more than `D` exit chords, one chord
`e_R` that splits `R` well (`SplitsWell`).  With `E` the set of added chords, at most one per
region (`round_classify`), every region of `S ∪ E` is

* an old region of `S` containing no chord of `E`, with the same exit chords; or
* a part of a split region `R`, with at least `3` and fewer than `deg R` exit chords.

Hence (`round_degLe`) if `S` has degree `≤ d` and every region of degree `> D` received a chord,
`S ∪ E` has degree `≤ max D (d - 1)`: after `d` rounds the degree is `≤ D`.

Helper facts: `region_of_subset_free` (a region of `S` avoiding the new chords is a region of the
larger family), `half_old` (the two halves of a region cut by `e` do not depend on chords outside
the region), `splitsWell_mono`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (ChordSystem regionsIn TouchesIn freeIn freeIn_anti regionsIn_subset
  regionsIn_isPreconnected regionsIn_nonempty mem_regionsIn regionsIn_eq_component)
open Chazelle.Merge (exitsIn IsSplit)

variable {M : Model}

/-- **A region of `S` inside the free set of `T ⊇ S` is a region of `T`.** -/
theorem region_of_subset_free {S T : Set (Set Point)} (hST : S ⊆ T) {R : Set Point}
    (hR : R ∈ regionsIn M.D S) (hfree : R ⊆ freeIn M.D T) : R ∈ regionsIn M.D T := by
  obtain ⟨z, hz⟩ := regionsIn_nonempty hR
  have hzT := hfree hz
  refine ⟨z, hzT, Subset.antisymm ?_ ?_⟩
  · exact (regionsIn_isPreconnected hR).subset_connectedComponentIn hz hfree
  · rw [regionsIn_eq_component hR hz]
    exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn
      (mem_connectedComponentIn hzT)
      ((connectedComponentIn_subset _ _).trans (freeIn_anti M.D hST))

/-- **The halves do not depend on the chords outside the region**: a region of `insert e T`
inside `R` is a region of `insert e S`, for `S ⊆ T` finite admissible families of which `R` is a
common region, and `e` a new admissible chord inside `R`. -/
theorem half_old (hM : WalkAx M) {S T : Set (Set Point)} (hST : S ⊆ T) (hT : T ⊆ M.Adm)
    (hTfin : T.Finite) {R : Set Point} (hRS : R ∈ regionsIn M.D S) (hRT : R ∈ regionsIn M.D T)
    {e : Set Point} (he : e ∈ M.Adm) (heT : e ∉ T) (heR : e ∩ M.D ⊆ R) {P : Set Point}
    (hP : P ∈ regionsIn M.D (insert e T)) (hPR : P ⊆ R) : P ∈ regionsIn M.D (insert e S) := by
  have hFT := hM.sys _ (insert_subset he hT) (hTfin.insert e)
  have heS : e ∉ S := fun h => heT (hST h)
  have hSF : insert e S ⊆ insert e T := insert_subset_insert hST
  obtain ⟨R₁, R₂, hs⟩ := Merge.exists_split hFT (subset_insert e T) (mem_insert e T) heT hRT heR
  obtain ⟨R₁', R₂', hs'⟩ := Merge.exists_split hFT (hST.trans (subset_insert e T))
    (mem_insert e T) heS hRS heR
  -- the halves in `S` are open and disjoint, and cover `R \ e`
  have ho₁ := hFT.regionsIn_open hSF hs'.mem₁
  have ho₂ := hFT.regionsIn_open hSF hs'.mem₂
  have hd : Disjoint R₁' R₂' :=
    Chazelle.Chain.regionsIn_disjoint_of_ne hs'.mem₁ hs'.mem₂ hs'.ne
  have hPsub : P ⊆ R \ e := fun z hz => ⟨hPR hz, fun hze => (regionsIn_subset hP hz).2
    ⟨e, mem_insert e T, hze⟩⟩
  rw [← hs'.union] at hPsub
  rcases (regionsIn_isPreconnected hP).subset_or_subset ho₁ ho₂ hd hPsub with h | h
  · -- `P ⊆ R₁'`, and conversely `R₁'` lies in a region of `insert e T`, which must be `P`
    have hR₁ : R₁' ⊆ freeIn M.D (insert e T) := by
      intro z hz
      refine ⟨(regionsIn_subset hs'.mem₁ hz).1, ?_⟩
      rintro ⟨c, hc, hzc⟩
      rcases hc with rfl | hcT
      · exact (regionsIn_subset hs'.mem₁ hz).2 ⟨c, mem_insert c S, hzc⟩
      · have hzR : z ∈ R := hs'.sub₁ hz
        have := regionsIn_subset hRT hzR
        exact this.2 ⟨c, hcT, hzc⟩
    obtain ⟨z, hz⟩ := regionsIn_nonempty hP
    have hPe : P = connectedComponentIn (freeIn M.D (insert e T)) z :=
      regionsIn_eq_component hP hz
    have : R₁' ⊆ P := by
      rw [hPe]
      exact (regionsIn_isPreconnected hs'.mem₁).subset_connectedComponentIn (h hz) hR₁
    rw [Subset.antisymm h this]; exact hs'.mem₁
  · have hR₂ : R₂' ⊆ freeIn M.D (insert e T) := by
      intro z hz
      refine ⟨(regionsIn_subset hs'.mem₂ hz).1, ?_⟩
      rintro ⟨c, hc, hzc⟩
      rcases hc with rfl | hcT
      · exact (regionsIn_subset hs'.mem₂ hz).2 ⟨c, mem_insert c S, hzc⟩
      · have hzR : z ∈ R := hs'.sub₂ hz
        have := regionsIn_subset hRT hzR
        exact this.2 ⟨c, hcT, hzc⟩
    obtain ⟨z, hz⟩ := regionsIn_nonempty hP
    have hPe : P = connectedComponentIn (freeIn M.D (insert e T)) z :=
      regionsIn_eq_component hP hz
    have : R₂' ⊆ P := by
      rw [hPe]
      exact (regionsIn_isPreconnected hs'.mem₂).subset_connectedComponentIn (h hz) hR₂
    rw [Subset.antisymm h this]; exact hs'.mem₂

/-- **Good splits survive more chords outside the region.** -/
theorem splitsWell_mono (hM : WalkAx M) {S T : Set (Set Point)} (hST : S ⊆ T) (hT : T ⊆ M.Adm)
    (hTfin : T.Finite) {R : Set Point} (hRS : R ∈ regionsIn M.D S) (hRT : R ∈ regionsIn M.D T)
    {e : Set Point} (he : e ∈ M.Adm) (heT : e ∉ T) (hw : SplitsWell M S R e) :
    SplitsWell M T R e := by
  refine ⟨heT, hw.2.1, fun P hP hPR => ?_⟩
  have h1 := hw.2.2 P (half_old hM hST hT hTfin hRS hRT he heT hw.2.1 hP hPR) hPR
  exact h1.trans (ncard_le_ncard (Merge.exitsIn_mono hST P)
    (hTfin.subset (Merge.exitsIn_subset T P)))

/-- The data of a round: new admissible chords, each splitting a region of `S` well, at most one
per region. -/
structure RoundData (M : Model) (S E : Set (Set Point)) : Prop where
  adm : E ⊆ M.Adm
  fin : E.Finite
  split : ∀ e ∈ E, ∃ R ∈ regionsIn M.D S, SplitsWell M S R e
  uniq : ∀ e ∈ E, ∀ e' ∈ E, ∀ R ∈ regionsIn M.D S, SplitsWell M S R e →
    SplitsWell M S R e' → e = e'

/-- The classification of the regions after a round (see the module docstring). -/
def Classified (M : Model) (S E : Set (Set Point)) (U : Set Point) : Prop :=
  (U ∈ regionsIn M.D S ∧ exitsIn M.D (S ∪ E) U = exitsIn M.D S U ∧
      ∀ e ∈ E, ¬ (e ∩ M.D ⊆ U)) ∨
    (∃ R ∈ regionsIn M.D S, ∃ e ∈ E, SplitsWell M S R e ∧ U ⊆ R ∧
      3 ≤ (exitsIn M.D (S ∪ E) U).ncard ∧
      (exitsIn M.D (S ∪ E) U).ncard < (exitsIn M.D S R).ncard)

theorem inter_nonempty_of_adm (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) :
    (e ∩ M.D).Nonempty :=
  ((hM.sys {e} (singleton_subset_iff.2 he) (finite_singleton e)).chord_inter_nonempty_isPreconnected
    (mem_singleton e)).1

/-- **The regions after a round.** -/
theorem round_classify (hM : WalkAx M) {S E : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) (hE : RoundData M S E) :
    ∀ U ∈ regionsIn M.D (S ∪ E), Classified M S E U := by
  suffices key : ∀ E₀ : Set (Set Point), E₀.Finite → E₀ ⊆ E →
      ∀ U ∈ regionsIn M.D (S ∪ E₀), Classified M S E₀ U from key E hE.fin subset_rfl
  intro E₀ hE₀
  induction E₀, hE₀ using Set.Finite.induction_on with
  | empty =>
    intro _ U hU
    rw [union_empty] at hU
    left
    exact ⟨hU, by rw [union_empty], fun e he => absurd he (notMem_empty e)⟩
  | @insert e E₀ heE₀ hE₀fin ih =>
    intro hsub U hU
    have hE₀sub : E₀ ⊆ E := (subset_insert e E₀).trans hsub
    have heE : e ∈ E := hsub (mem_insert e E₀)
    set T := S ∪ E₀ with hTd
    have hT : T ⊆ M.Adm := union_subset hS (hE₀sub.trans hE.adm)
    have hTfin : T.Finite := hfin.union hE₀fin
    have hTe : S ∪ insert e E₀ = insert e T := by
      rw [hTd]; ext x; simp only [mem_union, mem_insert_iff]; tauto
    obtain ⟨R, hR, hw⟩ := hE.split e heE
    have he := hE.adm heE
    have heS : e ∉ S := hw.1
    have heT : e ∉ T := by
      rintro (h | h)
      · exact heS h
      · exact heE₀ h
    -- the chords of `E₀` avoid `R`
    have hE₀R : ∀ e₀ ∈ E₀, ∀ z ∈ e₀, z ∉ closure R ∨ z ∉ M.D := by
      intro e₀ he₀ z hz
      by_contra hcon
      push Not at hcon
      obtain ⟨hzR, hzD⟩ := hcon
      obtain ⟨R₀, hR₀, hw₀⟩ := hE.split e₀ (hE₀sub he₀)
      have hzR₀ : z ∈ R₀ := hw₀.2.1 ⟨hz, hzD⟩
      have hopen : IsOpen R₀ := (hM.sys S hS hfin).regionsIn_open subset_rfl hR₀
      obtain ⟨y, hyR₀, hyR⟩ := mem_closure_iff.1 hzR R₀ hopen hzR₀
      have hRR₀ : R = R₀ := by
        rw [regionsIn_eq_component hR hyR, regionsIn_eq_component hR₀ hyR₀]
      subst hRR₀
      exact heE₀ (hE.uniq e heE e₀ (hE₀sub he₀) R hR hw hw₀ ▸ he₀)
    have hRfree : R ⊆ freeIn M.D T := by
      intro z hz
      refine ⟨(regionsIn_subset hR hz).1, ?_⟩
      rintro ⟨c, hc, hzc⟩
      rcases hc with hcS | hcE
      · exact (regionsIn_subset hR hz).2 ⟨c, hcS, hzc⟩
      · rcases hE₀R c hcE z hzc with h | h
        · exact h (subset_closure hz)
        · exact h (regionsIn_subset hR hz).1
    have hRT : R ∈ regionsIn M.D T := region_of_subset_free subset_union_left hR hRfree
    have hexR : exitsIn M.D T R = exitsIn M.D S R := by
      ext c
      refine ⟨fun ⟨hcT, hcR⟩ => ⟨?_, hcR⟩, fun ⟨hcS, hcR⟩ => ⟨Or.inl hcS, hcR⟩⟩
      rcases hcT with hcS | hcE
      · exact hcS
      · exfalso
        obtain ⟨z, ⟨hz, hzD⟩, hzR⟩ := hcR
        rcases hE₀R c hcE z hz with h | h
        · exact h hzR
        · exact h hzD
    have hwT : SplitsWell M T R e :=
      splitsWell_mono hM subset_union_left hT hTfin hR hRT he heT hw
    have hFT := hM.sys _ (insert_subset he hT) (hTfin.insert e)
    obtain ⟨R₁, R₂, hs⟩ := Merge.exists_split hFT (subset_insert e T) (mem_insert e T) heT hRT
      hw.2.1
    rw [hTe] at hU
    unfold Classified
    rw [hTe]
    rcases hs.mem_cases hU with ⟨hUT, hUR⟩ | hU12
    · -- an old region of `T` other than `R`
      have hex := hs.exits_other hFT (subset_insert e T) hUT hUR
      rcases ih hE₀sub U hUT with ⟨hUS, hexS, hno⟩ | ⟨R', hR', e', he', hw', hUR', h3, hlt⟩
      · left
        refine ⟨hUS, by rw [hex, hexS], fun e'' he'' => ?_⟩
        rcases he'' with rfl | he''
        · intro hsub'
          obtain ⟨z, hz⟩ := inter_nonempty_of_adm hM he
          have hzU := hsub' hz
          have hzR := hw.2.1 hz
          have : U = R := by
            rw [regionsIn_eq_component hUS hzU, regionsIn_eq_component hR hzR]
          exact hUR this
        · exact hno e'' he''
      · right
        exact ⟨R', hR', e', mem_insert_of_mem e he', hw', hUR', by rw [hex]; exact h3,
          by rw [hex]; exact hlt⟩
    · -- a half of `R`
      right
      have hUsub : U ⊆ R := by rcases hU12 with rfl | rfl; exacts [hs.sub₁, hs.sub₂]
      obtain ⟨h3, hlt⟩ := splitsWell_degrees hM hT hTfin hRT he hwT U hU hUsub
      exact ⟨R, hR, e, mem_insert e E₀, hw, hUsub, h3, by rw [← hexR]; exact hlt⟩

/-- **The degree after a round.**  If `S` has degree `≤ d` and every region of `S` with more
than `D` exit chords received a chord of `E`, then `S ∪ E` has degree `≤ max D (d - 1)`. -/
theorem round_degLe (hM : WalkAx M) {S E : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) (hE : RoundData M S E) {d D : ℕ} (hd : M.DegLe S d)
    (hall : ∀ R ∈ regionsIn M.D S, D < (exitsIn M.D S R).ncard → ∃ e ∈ E, SplitsWell M S R e) :
    M.DegLe (S ∪ E) (max D (d - 1)) := by
  intro U hU
  rcases round_classify hM hS hfin hE U hU with ⟨hUS, hex, hno⟩ | ⟨R, hR, e, he, hw, -, -, hlt⟩
  · show (exitsIn M.D (S ∪ E) U).ncard ≤ _
    rw [hex]
    by_contra hcon
    push Not at hcon
    obtain ⟨e, he, hw⟩ := hall U hUS (lt_of_le_of_lt (le_max_left _ _) hcon)
    exact hno e he hw.2.1
  · show (exitsIn M.D (S ∪ E) U).ncard ≤ _
    have := hd R hR
    change (exitsIn M.D S R).ncard ≤ d at this
    omega

end

end Restore

end Chazelle.Core
