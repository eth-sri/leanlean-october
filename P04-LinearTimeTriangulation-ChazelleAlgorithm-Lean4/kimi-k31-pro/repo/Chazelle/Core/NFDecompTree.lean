module

public import Chazelle.Core.FactsTree
public import Chazelle.Core.SpecRam
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# Tree decomposition (WP-C), part 0: the record tree of a normal form

`RecTree N D`: the combinatorial facts about the chord and region records of a valid normal form
that the decomposition needs — every chord record joins two distinct regions `up`, `dn`; the
exit-chord list of a region lists exactly the chords with an endpoint there, without repetition,
at most `D` of them; there is one more region than chords; the record graph is connected.

`recTree_of` derives them from `IsNF` for a good model with the WP-B facts `chordSides` and the
region tree (`ChordSystem.dualGraph_reachable`), and `DegLe`.

`nf_eq_of_nfAt`: two valid normal forms stored at the same handle have the same chords, arcs,
regions, sequence, decomposition and root.
-/

namespace Chazelle.Core

namespace Dec

@[expose] public section

open Relation Set Filter Topology
open Chazelle.Chain (TouchesIn regionsIn DualAdjIn)

/-- Two regions are joined by a chord record. -/
def RecAdj (N : NF) (a b : ℕ) : Prop :=
  ∃ i, i < N.nChords ∧ ((N.chord i).up = a ∧ (N.chord i).dn = b ∨ (N.chord i).up = b ∧ (N.chord i).dn = a)

/-- **The record tree** of a normal form, with degree cap `D`. -/
structure RecTree (N : NF) (D : ℕ) : Prop where
  ends_lt : ∀ i, i < N.nChords → (N.chord i).up < N.nRegions ∧ (N.chord i).dn < N.nRegions
  ends_ne : ∀ i, i < N.nChords → (N.chord i).up ≠ (N.chord i).dn
  lists : ∀ r, r < N.nRegions → ∀ i,
    i ∈ (N.region r).chords ↔ i < N.nChords ∧ ((N.chord i).up = r ∨ (N.chord i).dn = r)
  nodup : ∀ r, r < N.nRegions → (N.region r).chords.Nodup
  count : N.nRegions = N.nChords + 1
  conn : ∀ r s, r < N.nRegions → s < N.nRegions → ReflTransGen (RecAdj N) r s
  deg : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ D

theorem getD_of_lt {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  rwr [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem chord_mem {N : NF} {i : ℕ} (hi : i < N.nChords) : N.chord i ∈ N.chords := by
  unfold NF.chord
  rw [getD_of_lt hi]
  exact List.getElem_mem hi

/-- The region graph of a good model, with regions as intermediate nodes. -/
theorem regions_reach {M : Model} {Q : Polygon} {F : Set (Set Point)} (hM : GoodModel M)
    (hF : M.ChordFamily Q F) {U V : Set Point} (hU : U ∈ M.regions F) (hV : V ∈ M.regions F) :
    ReflTransGen (DualAdjIn M.D F) U V := by
  have hW := walkAx_of_goodModel hM
  have hsys := hW.sys F hF.2.1 hF.1
  have h := hsys.dualGraph_reachable hW.preconn hW.nonempty subset_rfl U hU V hV
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  exact h

section tree

variable {M : Model} {Q : Polygon} {N : NF} {D : ℕ}

/-- The regions of a chord record: the region above and the region below, distinct, and the only
regions the chord touches. -/
theorem chord_regions (hM : GoodModel M) (hN : IsNF M Q N) {reg : ℕ → Set Point}
    (hcorr : RegionCorr M Q N reg) (hsides : ChordSidesOK M Q N reg) {i : ℕ} (hi : i < N.nChords) :
    reg (N.chord i).up ≠ reg (N.chord i).dn ∧
      ∀ W ∈ M.regions (N.F M Q), TouchesIn M.D ((N.chord i).toSet M Q) W ↔
        W = reg (N.chord i).up ∨ W = reg (N.chord i).dn := by
  have hc : (N.chord i).toSet M Q ∈ N.F M Q := ⟨N.chord i, chord_mem hi, rfl⟩
  obtain ⟨U, V, hU, hV, hUV, hev, htouch⟩ := chordSides M Q (N.F M Q) hM hN.1 _ hc
  obtain ⟨z, ⟨hzc, hzD⟩, -⟩ := (htouch U hU).2 (Or.inl rfl)
  obtain ⟨hup, hdn, hs⟩ := hsides i hi
  obtain ⟨ε₀, hε₀, hε⟩ := hs z hzc hzD
  have hev' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < ε₀ := by
    have : Set.Iio ε₀ ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε₀)
    exact this
  have hev0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, ⟨hUV', hδε⟩, hδ0⟩ := ((hev z hzc hzD).and hev').and hev0 |>.exists
  obtain ⟨ha, hb⟩ := hε δ hδ0 hδε
  have hregU := hcorr.1 _ hup
  have hregV := hcorr.1 _ hdn
  have e1 : reg (N.chord i).up = U := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hregU hU with e | e
    · exact e
    · exact absurd (Set.disjoint_left.1 e ha) (not_not.2 hUV'.1)
  have e2 : reg (N.chord i).dn = V := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hregV hV with e | e
    · exact e
    · exact absurd (Set.disjoint_left.1 e hb) (not_not.2 hUV'.2)
  rw [e1, e2]
  exact ⟨hUV, htouch⟩

/-- **The record tree of a valid normal form** of a good model with degree cap `D`. -/
theorem recTree_of (hM : GoodModel M) (hN : IsNF M Q N) (hD : M.DegLe (N.F M Q) D) :
    RecTree N D := by
  obtain ⟨hfam, hinj, -, reg, hcorr, hsides, -, hregs, -, -, -⟩ := id hN
  have hcr := fun i (hi : i < N.nChords) => chord_regions hM hN hcorr hsides hi
  have hregInj  := hcorr.2.1
  -- the touching regions of a chord, as indices
  have htouchIdx : ∀ i, i < N.nChords → ∀ r, r < N.nRegions →
      (TouchesIn M.D ((N.chord i).toSet M Q) (reg r) ↔ (N.chord i).up = r ∨ (N.chord i).dn = r) := by
    intro i hi r hr
    obtain ⟨hup, hdn, -⟩ := hsides i hi
    rw [(hcr i hi).2 _ (hcorr.1 r hr)]
    constructor
    · rintro (e | e)
      · exact Or.inl (hregInj _ _ hup hr e.symm)
      · exact Or.inr (hregInj _ _ hdn hr e.symm)
    · rintro (e | e)
      · exact Or.inl (by rw [e])
      · exact Or.inr (by rw [e])
  have hlists : ∀ r, r < N.nRegions → ∀ i,
      i ∈ (N.region r).chords ↔ i < N.nChords ∧ ((N.chord i).up = r ∨ (N.chord i).dn = r) := by
    intro r hr i
    rw [((hregs r hr).1 i)]
    constructor
    · rintro ⟨hi, ht⟩; exact ⟨hi, (htouchIdx i hi r hr).1 ht⟩
    · rintro ⟨hi, ht⟩; exact ⟨hi, (htouchIdx i hi r hr).2 ht⟩
  -- the chord map is injective and onto the family
  have hF : N.F M Q = (fun i => (N.chord i).toSet M Q) '' Set.Iio N.nChords := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      refine ⟨i, hi, ?_⟩
      simp only [NF.chord, getD_of_lt hi]
    · rintro ⟨i, hi, rfl⟩
      exact ⟨N.chord i, chord_mem hi, rfl⟩
  have hFcard : (N.F M Q).ncard = N.nChords := by
    have hio : Set.InjOn (fun i => (N.chord i).toSet M Q) (Set.Iio N.nChords) :=
      fun a ha b hb e => hinj a b ha hb e
    rw [hF, hio.ncard_image, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  have hRcard : (M.regions (N.F M Q)).ncard = N.nRegions := by
    have : M.regions (N.F M Q) = reg '' Set.Iio N.nRegions := by
      ext U
      constructor
      · intro hU
        obtain ⟨r, hr, e⟩ := hcorr.2.2 U hU
        exact ⟨r, hr, e⟩
      · rintro ⟨r, hr, rfl⟩
        exact hcorr.1 r hr
    have hio : Set.InjOn reg (Set.Iio N.nRegions) := fun a ha b hb e => hregInj a b ha hb e
    rw [this, hio.ncard_image, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  obtain ⟨-, hcount, -⟩ := regionTree M Q (N.F M Q) hM hfam
  refine ⟨fun i hi => ⟨(hsides i hi).1, (hsides i hi).2.1⟩,
    fun i hi e => (hcr i hi).1 (by rw [e]), hlists, fun r hr => (hregs r hr).2.1,
    by rwx [← hRcard, ← hFcard], ?_, ?_⟩
  · -- connectivity
    intro r s hr hs
    have hpath := regions_reach hM hfam (hcorr.1 r hr) (hcorr.1 s hs)
    have key : ∀ W, ReflTransGen (DualAdjIn M.D (N.F M Q)) (reg r) W → W ∈ M.regions (N.F M Q) →
        ∃ b, b < N.nRegions ∧ reg b = W ∧ ReflTransGen (RecAdj N) r b := by
      intro W hW
      induction hW with
      | refl => intro _; exact ⟨r, hr, rfl, ReflTransGen.refl⟩
      | tail hAB hBC ih =>
        rename_i B C
        intro _
        obtain ⟨hB, hC, hne, c, hc, h1, h2⟩ := hBC
        obtain ⟨b, hb, rfl, hpb⟩ := ih hB
        obtain ⟨a, ha, rfl⟩ := hcorr.2.2 C hC
        obtain ⟨x, hx, rfl⟩ := hc
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        have hci : N.chords[i] = N.chord i := by simp only [NF.chord, getD_of_lt hi]
        rw [hci] at h1 h2
        have t1 := (htouchIdx i hi b hb).1 h1
        have t2 := (htouchIdx i hi a ha).1 h2
        have hab : b ≠ a := fun e => hne (by rw [e])
        refine ⟨a, ha, rfl, hpb.tail ⟨i, hi, ?_⟩⟩
        have hne' := (hcr i hi).1
        rcases t1 with e1 | e1 <;> rcases t2 with e2 | e2
        · exact absurd (e1.symm.trans e2) hab
        · exact Or.inl ⟨e1, e2⟩
        · exact Or.inr ⟨e2, e1⟩
        · exact absurd (e1.symm.trans e2) hab
    obtain ⟨b, hb, e, hp⟩ := key _ hpath (hcorr.1 s hs)
    rw [hregInj _ _ hb hs e] at hp
    exact hp
  · -- the degree
    intro r hr
    classical
    have hnd := (hregs r hr).2.1
    have hsub : ((N.region r).chords.toFinset.image fun i => (N.chord i).toSet M Q : Set (Set Point)) ⊆
        {c | c ∈ N.F M Q ∧ TouchesIn M.D c (reg r)} := by
      intro c hc
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, List.mem_toFinset] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      rw [(hregs r hr).1 i] at hi
      exact ⟨⟨N.chord i, chord_mem hi.1, rfl⟩, hi.2⟩
    have hfin : {c | c ∈ N.F M Q ∧ TouchesIn M.D c (reg r)}.Finite :=
      hfam.1.subset fun c hc => hc.1
    have h1 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd] at h1
    · exact h1.trans (hD _ (hcorr.1 r hr))
    · intro a ha b hb e
      simp only [Finset.mem_coe, List.mem_toFinset] at ha hb
      rw [(hregs r hr).1 a] at ha
      rw [(hregs r hr).1 b] at hb
      exact hinj a b ha.1 hb.1 e

end tree

end

end Dec

end Chazelle.Core
