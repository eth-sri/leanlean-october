module

public meta import Chazelle.Arithmetic

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

section
variable (hN : IsNF M Q N)
include hN
theorem ncard_F : (N.F M Q).ncard = N.nChords := by
  have e : N.F M Q = (fun i => cs M Q N i) '' {i | i < N.nChords} := by
    grind [mem_F_iff, mem_image, mem_ofPred_eq]
  have hinj : Set.InjOn (fun i => cs M Q N i) {i | i < N.nChords} :=
    fun i hi i' hi' h => cs_inj hN hi hi' h
  rw [e, hinj.ncard_image, show {i | i < N.nChords} = ((Finset.range N.nChords : Finset ℕ) :
    Set ℕ) by ext; simp, Set.ncard_coe_finset, Finset.card_range]

section
variable (hM : WalkAx M)
include hM
/-- **A valid normal form has `K + 1` regions.** -/
theorem nRegions_eq : N.nRegions = N.nChords + 1 := by
  obtain ⟨-, -, -, reg, hRC, -⟩ := id hN
  have hsys := hM.sys _ (F_adm hN) (F_finite hN)
  have hcard := hsys.ncard_regionsIn hM.preconn hM.nonempty (subset_refl _)
  rw [ncard_F hN] at hcard
  have e : M.regions (N.F M Q) = reg '' {r | r < N.nRegions} := by
    ext U
    ram_grind
  have hinj : Set.InjOn reg {r | r < N.nRegions} := fun r hr r' hr' h => hRC.2.1 r r' hr hr' h
  have : (M.regions (N.F M Q)).ncard = N.nRegions := by
    rw [e, hinj.ncard_image, show {r | r < N.nRegions} = ((Finset.range N.nRegions : Finset ℕ) :
      Set ℕ) by ext; simp, Set.ncard_coe_finset, Finset.card_range]
  grind [Model.regions]

/-- **At most two arcs per chord.** -/
theorem arcs_le (hne : (N.F M Q).Nonempty) :
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
    grind
  have h1 : ((Finset.range A).image (pk M Q N)).card = A := by
    rw [Finset.card_image_of_injOn fun j hj j' hj' h =>
      pk_inj hN hne (Finset.mem_range.1 hj) (Finset.mem_range.1 hj') h, Finset.card_range]
  have h2 := Finset.card_le_card hsub
  grind [Finset.card_range]



end

end

/-- The regions of a normal form with degrees `≤ D` have at most `D` exit chords. -/
theorem chords_le {reg : ℕ → Set Point} (hN : IsNF M Q N) (hRC : RegionCorr M Q N reg)
    (hRO : RegionsOK M Q N reg) {D : ℕ} (hD : M.DegLe (N.F M Q) D) {r : ℕ}
    (hr : r < N.nRegions) : (N.region r).chords.length ≤ D := by
  rw [← deg_region hN hRC hRO hr]
  exact hD _ (hRC.1 r hr)

section
variable (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords)
include hN hi
/-- The left end of a chord record is a position of the walk proper. -/
theorem lpos_proper :
    ProperPos M Q Q.n (N.chord i).lpos := by
  obtain ⟨-, h0, h1, -⟩ := attach_l hN hi
  obtain ⟨-, -, -, -, -, -, -, -, -, hh, -⟩ := hN
  exact ⟨h0, h1, by aesop⟩

theorem rpos_proper :
    ProperPos M Q Q.n (N.chord i).rpos := by
  obtain ⟨-, h0, h1, -⟩ := attach_r hN hi
  obtain ⟨-, -, -, -, -, -, -, -, -, hh, -⟩ := hN
  exact ⟨h0, h1, by aesop⟩

/-- The ends of a chord record are cut keys. -/
theorem lkey_cut :
    M.IsCut (N.F M Q) (M.key Q (N.chord i).lpos) :=
  ⟨cs M Q N i, cs_mem hi, _, _, attach_l hN hi, rfl⟩

theorem rkey_cut :
    M.IsCut (N.F M Q) (M.key Q (N.chord i).rpos) :=
  ⟨cs M Q N i, cs_mem hi, _, _, attach_r hN hi, rfl⟩


end

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
