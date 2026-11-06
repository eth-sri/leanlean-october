module

public import Chazelle.Golf

public import Chazelle.Core.RestoreLink

/-!
# WP-E, Lemma 3.2 part 1: the pruning lemma

The search of Lemma 3.2 restricts the candidate points of an arc `Aᵢ` by chords of the host model
`M`: a chord `e` shot from a point of `Aᵢ` splits the walk into two cyclic key intervals, and a
chord `s` (the seeing segment of a candidate) that is disjoint from `e` in the domain has both of
its attachments on one side.

* `same_side`: if one attachment of an admissible chord `s ≠ e` lies strictly on one side of
  the admissible chord `e`, no attachment of `s` lies strictly on the other side.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (ChordSystem SideAttach sideInArc sidePt SideSectorIn)

variable {M : Model}

/-- **The pruning lemma.**  Two distinct admissible chords do not cross on the walk: if `s` is
attached strictly inside the key interval `(ka, kb)` cut by the attachments of `e`, it is not
attached strictly inside `(kb, ka)`. -/
theorem same_side (hM : WalkAx M) {e s : Set Point} (he : e ∈ M.Adm) (hs : s ∈ M.Adm)
    (hes : s ≠ e) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W e pa ta)
    (hB : SideAttach M.W e pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    {pv pw : ℕ} {tv tw : ℝ} (hv : SideAttach M.W s pv tv) (hw : SideAttach M.W s pw tw)
    (hvin : sideInArc (pa + ta) (pb + tb) (pv + tv)) :
    ¬ sideInArc (pb + tb) (pa + ta) (pw + tw) := by
  intro hwin
  obtain ⟨K₁, K₂, hK, ⟨c₁, rfl⟩, ⟨c₂, rfl⟩, hsec₁, hsec₂⟩ := hM.split he hA hB hAB
  have hF : ChordSystem M.D {e, s} :=
    hM.sys _ (insert_subset he (singleton_subset_iff.2 hs)) (toFinite _)
  obtain ⟨hvp, hv0, hv1, -⟩ := id hv
  obtain ⟨hwp, hw0, hw1, -⟩ := id hw
  obtain ⟨x₁, hx₁, hxK₁⟩ := exists_near_attach hM hs hv (hsec₁ pv hvp tv hv0 hv1 hvin)
  obtain ⟨x₂, hx₂, hxK₂⟩ := exists_near_attach hM hs hw (hsec₂ pw hwp tw hw0 hw1 hwin)
  have hsD : s ∩ M.D ⊆ M.D \ e := fun z hz =>
    ⟨hz.2, fun hze => hF.inter_subset_compl (Or.inr rfl) (Or.inl rfl) hes ⟨hz.1, hze⟩ hz.2⟩
  have hsub := (hF.chord_inter_nonempty_isPreconnected (Or.inr rfl : s ∈ ({e, s} : Set _))).2
    |>.subset_connectedComponentIn hx₁ hsD
  have e1 := connectedComponentIn_eq hxK₁
  have e2 := connectedComponentIn_eq hxK₂
  exact hK (e1.trans ((connectedComponentIn_eq (hsub hx₂)).trans e2.symm))

/-- **An admissible chord has one attachment per endpoint**: two attachments of `e` with the
same point are the same position. -/
theorem attach_unique (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {p p' : ℕ} {t t' : ℝ}
    (hA : SideAttach M.W e p t) (hA' : SideAttach M.W e p' t')
    (hpt : sidePt M.W p t = sidePt M.W p' t') : p = p' ∧ t = t' := by
  obtain ⟨a, b, hab, rfl, -, hopen, hEa, hEb⟩ := hM.ends e he
  by_contra hne
  have hne' : p = p' → t ≠ t' := fun h1 h2 => hne ⟨h1, h2⟩
  obtain ⟨hp, ht0, ht1, hmem, r, hr, hsec⟩ := hA
  obtain ⟨hp', ht0', ht1', -, r', hr', hsec'⟩ := hA'
  have key : ∀ u v : Point, u ≠ v → (∀ s ∈ Set.Ioo (0 : ℝ) 1, Geometry.lerp u v s ∈ M.D) →
      Chazelle.segment u v = Chazelle.segment a b → WalkEnd M.W (Chazelle.segment a b) u →
      sidePt M.W p t = u → False := by
    intro u v huv hop hseg hE hu
    obtain ⟨ρ, hρ, hdisj⟩ := hE.2 p p' t t' hp ht0 ht1 hp' ht0' ht1' hne' hu (hpt ▸ hu)
    obtain ⟨s, hs0, hs1, hsne, hsd⟩ := exists_lerp_near huv (lt_min hρ (lt_min hr hr'))
    have hx : Geometry.lerp u v s ∈ Chazelle.segment a b := by
      rw [← hseg]; exact Geometry.lerp_mem_segment _ _ hs0.le hs1.le
    have h1 := hsec _ hx (by rw [hu]; exact hsne)
      (by rw [hu]; exact lt_of_lt_of_le hsd ((min_le_right _ _).trans (min_le_left _ _)))
    have h2 := hsec' _ hx (by rw [← hpt, hu]; exact hsne)
      (by rw [← hpt, hu]; exact lt_of_lt_of_le hsd ((min_le_right _ _).trans (min_le_right _ _)))
    exact hdisj _ (by rw [Metric.mem_ball]; exact lt_of_lt_of_le hsd (min_le_left _ _)) h1 h2
  rcases hM.attach_endpoint hopen ⟨hp, ht0, ht1, hmem, r, hr, hsec⟩ with h | h
  · exact key a b hab hopen rfl hEa h
  · exact key b a hab.symm (WalkAx.open_rev hopen) (Geometry.segment_comm _ _) hEb h

theorem not_sideInArc_left (a b : ℝ) : ¬ sideInArc a b a := by
  unfold sideInArc; split_ifs with hab
  · intro h; linarith [h.1]
  · intro h; rcases h with h | h
    · linarith
    · exact hab h

theorem not_sideInArc_right (a b : ℝ) : ¬ sideInArc a b b := by
  unfold sideInArc; split_ifs with hab
  · intro h; linarith [h.2]
  · intro h; rcases h with h | h
    · exact hab h
    · linarith

/-- An admissible chord is attached strictly inside a side of itself at no position. -/
theorem not_attach_strict (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {p : ℕ} {t : ℝ} (hat : SideAttach M.W e p t)
    (hin : sideInArc (pa + ta) (pb + tb) (p + t) ∨ sideInArc (pb + tb) (pa + ta) (p + t)) :
    False := by
  obtain ⟨hseg, -, hopen, -, -⟩ := hM.attach_seg he hA hB hAB
  have hat' := hat
  rw [hseg] at hat'
  rcases hM.attach_endpoint hopen hat' with h | h
  · obtain ⟨rfl, rfl⟩ := attach_unique hM he hat hA h
    rcases hin with h' | h'
    · exact not_sideInArc_left _ _ h'
    · exact not_sideInArc_right _ _ h'
  · obtain ⟨rfl, rfl⟩ := attach_unique hM he hat hB h
    rcases hin with h' | h'
    · exact not_sideInArc_right _ _ h'
    · exact not_sideInArc_left _ _ h'

/-- **Counting decides a good split.**  An admissible chord `e`, attached at two positions with
distinct points, with at least two exit chords of the region `R` attached strictly on each side,
is not a chord of `S`, lies in `R`, and splits `R` well. -/
theorem splitsWell_of_counts (hM : WalkAx M) {S : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ Chazelle.Chain.regionsIn M.D S) {e : Set Point}
    (he : e ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (h1 : 2 ≤ (sideExits M S R (pa + ta) (pb + tb)).ncard)
    (h2 : 2 ≤ (sideExits M S R (pb + tb) (pa + ta)).ncard) : SplitsWell M S R e := by
  obtain ⟨K₁, K₂, hK, ⟨c₁', rfl⟩, ⟨c₂', rfl⟩, hsec₁, hsec₂⟩ := hM.split he hA hB hAB
  obtain ⟨d₁, hd₁⟩ := Set.nonempty_of_ncard_ne_zero
    (show (sideExits M S R (pa + ta) (pb + tb)).ncard ≠ 0 by omega)
  obtain ⟨d₂, hd₂⟩ := Set.nonempty_of_ncard_ne_zero
    (show (sideExits M S R (pb + tb) (pa + ta)).ncard ≠ 0 by omega)
  -- a side exit touches `R` and has points of the domain in the component of its side
  have side : ∀ (c₀ : Point) (k₁ k₂ : ℝ), (k₁ = pa + ta ∧ k₂ = pb + tb ∨ k₁ = pb + tb ∧ k₂ = pa + ta) →
      (∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc k₁ k₂ (p + t) →
        SideSectorIn M.W (connectedComponentIn (M.D \ e) c₀) p t) →
      ∀ d ∈ sideExits M S R k₁ k₂, d ≠ e ∧ ∃ x ∈ d ∩ M.D, x ∈ connectedComponentIn (M.D \ e) c₀ := by
    rintro c₀ k₁ k₂ hk hsec d ⟨⟨hdS, -⟩, p, t, hat, hin⟩
    have hdne : d ≠ e := by
      rintro rfl
      refine not_attach_strict hM he hA hB hAB hat ?_
      rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hin
      · exact Or.inr hin
    obtain ⟨hp, ht0, ht1, -⟩ := id hat
    exact ⟨hdne, exists_near_attach hM (hS hdS) hat (hsec p hp t ht0 ht1 hin)⟩
  obtain ⟨hne1, x₁, hx₁, hxK₁⟩ := side c₁' _ _ (Or.inl ⟨rfl, rfl⟩) hsec₁ d₁ hd₁
  obtain ⟨hne2, x₂, hx₂, hxK₂⟩ := side c₂' _ _ (Or.inr ⟨rfl, rfl⟩) hsec₂ d₂ hd₂
  have hdisj := components_disjoint hK
  -- `e ∉ S` and `e ∩ D ⊆ R`: otherwise `R` avoids `e` and lies in both components
  have key : e ∉ S ∧ e ∩ M.D ⊆ R := by
    by_contra hcon
    have hRe : R ⊆ M.D \ e := by
      intro z hz
      refine ⟨(Chazelle.Chain.regionsIn_subset hR hz).1, fun hze => ?_⟩
      by_cases heS : e ∈ S
      · exact (Chazelle.Chain.regionsIn_subset hR hz).2 ⟨e, heS, hze⟩
      · have hF := hM.sys _ (insert_subset he hS) (hfin.insert e)
        obtain ⟨R', hR', heR'⟩ := Merge.exists_region_of_chord hF (subset_insert e S)
          (mem_insert e S) heS
        have hRR : R = R' := by
          rw [Chazelle.Chain.regionsIn_eq_component hR hz,
            Chazelle.Chain.regionsIn_eq_component hR' (heR' ⟨hze, (Chazelle.Chain.regionsIn_subset hR hz).1⟩)]
        subst hRR
        exact hcon ⟨heS, heR'⟩
    have hF₁ := hM.sys {d₁, e} (insert_subset (hS hd₁.1.1) (singleton_subset_iff.2 he)) (toFinite _)
    have hF₂ := hM.sys {d₂, e} (insert_subset (hS hd₂.1.1) (singleton_subset_iff.2 he)) (toFinite _)
    have hR1 := subset_component_of_touches hM.isOpen hF₁ (Or.inl rfl) (Or.inr rfl) hne1 hx₁ hxK₁
      hRe (Chazelle.Chain.regionsIn_isPreconnected hR) hd₁.1.2
    have hR2 := subset_component_of_touches hM.isOpen hF₂ (Or.inl rfl) (Or.inr rfl) hne2 hx₂ hxK₂
      hRe (Chazelle.Chain.regionsIn_isPreconnected hR) hd₂.1.2
    obtain ⟨z, hz⟩ := Chazelle.Chain.regionsIn_nonempty hR
    exact hdisj.notMem_of_mem_left (hR1 hz) (hR2 hz)
  exact splitsWell_of_sideExits hM hS hfin hR he key.1 key.2 hA hB hAB h1 h2

end

end Restore

end Chazelle.Core
