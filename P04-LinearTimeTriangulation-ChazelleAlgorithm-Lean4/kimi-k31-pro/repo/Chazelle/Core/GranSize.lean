module

public import Chazelle.Core.GranNd

/-!
# WP-F, init part 5: sizes and static facts of a valid normal form

For a valid normal form `N` of a model with the walk axioms:

* `nRegions_eq`: `R = K + 1` (a chord system with `K` chords has `K + 1` regions);
* `arcs_le`: `A ≤ 2 K` for a nonempty submap (the start keys of the arcs are distinct cut keys,
  and each chord has two attachment keys);
* `chords_le`: every region has at most `D` exit chords if the degrees are at most `D`;
* `edge_lt`, `lpos_proper`, `lkey_cut` (and the right-hand versions): the positions the
  initialisation reads are on the walk proper, and chord ends are cut keys.
-/

namespace Chazelle.Core

namespace Gran

open Set
open Chazelle.Chain (SideAttach)

@[expose] public section

variable {M : Model} {Q : Polygon} {N : NF}

theorem ncard_F (hN : IsNF M Q N) : (N.F M Q).ncard = N.nChords := by
  have e : N.F M Q = (fun i => cs M Q N i) '' {i | i < N.nChords} := by
    ext c
    rw [mem_F_iff]
    simp [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  have hinj : Set.InjOn (fun i => cs M Q N i) {i | i < N.nChords} :=
    fun i hi i' hi' h => cs_inj hN hi hi' h
  rw [e, hinj.ncard_image, show {i | i < N.nChords} = ((Finset.range N.nChords : Finset ℕ) :
    Set ℕ) by ext; simp, Set.ncard_coe_finset, Finset.card_range]

/-- **A valid normal form has `K + 1` regions.** -/
theorem nRegions_eq (hN : IsNF M Q N) (hM : WalkAx M) : N.nRegions = N.nChords + 1 := by
  obtain ⟨-, -, -, reg, hRC, -⟩ := id hN
  have hsys := hM.sys _ (F_adm hN) (F_finite hN)
  have hcard := hsys.ncard_regionsIn hM.preconn hM.nonempty (subset_refl _)
  rw [ncard_F hN] at hcard
  have e : M.regions (N.F M Q) = reg '' {r | r < N.nRegions} := by
    ext U
    simp [mem_image, mem_ofPred_eq]
    constructor
    · intro hU
      obtain ⟨r, hr, rfl⟩ := hRC.2.2 U hU
      exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩; exact hRC.1 r hr
  have hinj : Set.InjOn reg {r | r < N.nRegions} := fun r hr r' hr' h => hRC.2.1 r r' hr hr' h
  have : (M.regions (N.F M Q)).ncard = N.nRegions := by
    rw [e, hinj.ncard_image, show {r | r < N.nRegions} = ((Finset.range N.nRegions : Finset ℕ) :
      Set ℕ) by ext; simp, Set.ncard_coe_finset, Finset.card_range]
  unfold Model.regions at this
  omega

/-- **At most two arcs per chord.** -/
theorem arcs_le (hN : IsNF M Q N) (hM : WalkAx M) (hne : (N.F M Q).Nonempty) :
    N.arcs.length ≤ 2 * N.nChords := by
  classical
  set A := N.arcs.length
  set K := N.nChords
  have hsub : (Finset.range A).image (pk M Q N) ⊆
      (Finset.range K).image (fun i => M.key Q (N.chord i).lpos) ∪
        (Finset.range K).image (fun i => M.key Q (N.chord i).rpos) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
    have hcut := pk_cut hN hne (Finset.mem_range.1 hj)
    rw [← fam_univ, isCut_fam_iff hN hM] at hcut
    obtain ⟨i, -, hi, h | h⟩ := hcut
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, h.symm⟩)
  have h1 : ((Finset.range A).image (pk M Q N)).card = A := by
    rw [Finset.card_image_of_injOn fun j hj j' hj' h =>
      pk_inj hN hne (Finset.mem_range.1 hj) (Finset.mem_range.1 hj') h, Finset.card_range]
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.card_union_le ((Finset.range K).image (fun i => M.key Q (N.chord i).lpos))
    ((Finset.range K).image (fun i => M.key Q (N.chord i).rpos))
  have h4 := Finset.card_image_le (s := Finset.range K) (f := fun i => M.key Q (N.chord i).lpos)
  have h5 := Finset.card_image_le (s := Finset.range K) (f := fun i => M.key Q (N.chord i).rpos)
  rw [Finset.card_range] at h4 h5
  omega

/-- The regions of a normal form with degrees `≤ D` have at most `D` exit chords. -/
theorem chords_le {reg : ℕ → Set Point} (hN : IsNF M Q N) (hRC : RegionCorr M Q N reg)
    (hRO : RegionsOK M Q N reg) {D : ℕ} (hD : M.DegLe (N.F M Q) D) {r : ℕ}
    (hr : r < N.nRegions) : (N.region r).chords.length ≤ D := by
  rw [← deg_region hN hRC hRO hr]
  exact hD _ (hRC.1 r hr)

/-- The left end of a chord record is a position of the walk proper. -/
theorem lpos_proper (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    ProperPos M Q Q.n (N.chord i).lpos := by
  obtain ⟨-, h0, h1, -⟩ := attach_l hN hi
  obtain ⟨-, -, -, -, -, -, -, -, -, hh, -⟩ := hN
  exact ⟨h0, h1, by have := hh i hi; show (N.chord i).h + 1 ≤ Q.n; omega⟩

theorem rpos_proper (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    ProperPos M Q Q.n (N.chord i).rpos := by
  obtain ⟨-, h0, h1, -⟩ := attach_r hN hi
  obtain ⟨-, -, -, -, -, -, -, -, -, hh, -⟩ := hN
  exact ⟨h0, h1, by have := hh i hi; show (N.chord i).h + 1 ≤ Q.n; omega⟩

/-- The ends of a chord record are cut keys. -/
theorem lkey_cut (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    M.IsCut (N.F M Q) (M.key Q (N.chord i).lpos) :=
  ⟨cs M Q N i, cs_mem hi, _, _, attach_l hN hi, rfl⟩

theorem rkey_cut (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    M.IsCut (N.F M Q) (M.key Q (N.chord i).rpos) :=
  ⟨cs M Q N i, cs_mem hi, _, _, attach_r hN hi, rfl⟩

/-- The start of a listed arc lies on a walk edge. -/
theorem edge_lt' (hN : IsNF M Q N) (hne : (N.F M Q).Nonempty) {j : ℕ} (hj : j < N.arcs.length) :
    (N.arc (N.seq.getD j 0)).s.edge < M.W.n := by
  have hcut := pk_cut hN hne hj
  obtain ⟨c, -, p, t, hA, hk⟩ := hcut
  obtain ⟨hp, ht0, ht1, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpp⟩ := id hN
  obtain ⟨hs0, hs1, -⟩ := (hpp _ (NFLoc.seq_lt hN hj)).1
  unfold pk Model.key at hk
  have hfl : ((N.arc (N.seq.getD j 0)).s.edge : ℝ) < p + 1 := by linarith
  have : (N.arc (N.seq.getD j 0)).s.edge < p + 1 := by exact_mod_cast hfl
  omega

end

end Gran

end Chazelle.Core
