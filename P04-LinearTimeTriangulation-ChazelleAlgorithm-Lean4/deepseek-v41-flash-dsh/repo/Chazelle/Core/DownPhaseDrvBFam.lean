module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvBEmit

/-!
# Down-phase base (D9): the new chord list of the base case

For the current interior normal form `N = buildNF I Q L E` (`K = |L| > 0`), the base emits, region
by region, the records `regList` of the missing vertex chords (`newL`); for `K = 0` the whole
interior walk is the only region (`newL0`).

* `newL_ok`: `L ++ newL` is a valid chord list (`ChordTriplesOK`): the new chords are vertex chords
  of `Q` not in `S`, distinct within a region (`regList_nodup`) and across regions (their domain
  parts lie in distinct regions);
* `newL_full`: every vertex chord of `Q` is a chord of `L ++ newL` (B-M1 `full_in_region` and the
  completeness of the regions);
* `newL_length`: at most `2 n` new chords (they are distinct vertex chords);
* the same for `newL0` (`K = 0`).
-/

namespace Chazelle.Core

namespace DrvB

@[expose] public section

open Set
open Chazelle.Visibility (DirInterior chordEnd chordSet chords OpenEdgePt)
open DrvR (ivB qE walkItems regHost)
open BuildNF (buildNF codeLe)

/-! ## The family of a chord list -/

/-- The chords of a list of triples. -/
def famL (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) : Set (Set Point) :=
  {c | ∃ x ∈ L, c = (recOf x).toSet M Q}

theorem famL_append (M : Model) (Q : Polygon) (L L₂ : List (ℕ × ℕ × ℕ)) :
    famL M Q (L ++ L₂) = famL M Q L ∪ famL M Q L₂ := by
  ext c; Θ famL, or_and_right, exists_or

/-- **The chords of `buildNF` are those of its list.** -/
theorem F_build (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) :
    (buildNF M Q L E).F M Q = famL M Q L := by
  ext c
  ϴ NF.F, BuildNF.buildNF, List.mem_map, List.mem_range, famL
  constructor
  · rintro ⟨r, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨_, BuildOrder.getD_mem hi, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
    have : L.getD i (0, 0, 0) = L[i] := by
      Ξ List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some
    unfold BuildNF.chordRec
    Ξ this
    rfl

/-- A vertex chord meets the interior. -/
theorem chord_dom_nonempty {Q : Polygon} (hQ : Q.Simple) {c : Set Point} (hc : c ∈ chords Q) :
    (c ∩ (interiorModel Q).D).Nonempty := by
  obtain ⟨i, σ, hi, hσ, hdir, rfl⟩ := hc
  have hpos := Visibility.chordParam_pos hQ hi hdir
  refine ⟨Visibility.rayPt (Q.vtx i) σ (Visibility.chordParam Q i σ / 2), ?_, ?_⟩
  · Ξ Visibility.chordSet_eq_image hQ hi hdir
    exact ⟨_, ⟨⟡, ⟡⟩, rfl⟩
  · exact (Visibility.chord_spec hQ hi hdir).2.2 _ (⟡) (⟡)

/-- The chords of `Q` are admissible chords of its interior model, at vertex heights. -/
theorem chords_family {Q : Polygon} (hQ : Q.Simple) {c : Set Point} (hc : c ∈ chords Q) :
    c ∈ (interiorModel Q).Adm := FullDegInt.hc_full hQ hc

/-! ## Points of a well-formed host -/

theorem host_pts_lt {n : ℕ} (hn : 0 < n) {H : Host} (hH : HostWF n H) :
    ∀ s ∈ H.pts n, s.Lt n := by
  intro s hs
  ϴ' Host.pts, List.mem_flatMap at hs
  obtain ⟨it, hit, hs⟩ := hs
  have hwf := hH it hit
  cases it with
  | run a ℓ =>
    ϴ' HostItem.pts, List.mem_map, List.mem_range at hs
    obtain ⟨k, -, rfl⟩ := hs
    exact Nat.mod_lt _ hn
  | pt x =>
    ϴ' HostItem.pts, List.mem_singleton at hs
    subst hs; exact hwf

theorem wlist_mem {li : Bool} {pts : List SymPt} {s : SymPt} (h : s ∈ wlist li pts) : s ∈ pts := by
  unfold wlist at h; split_ifs at h
  · exact h
  · exact List.mem_reverse.1 h

/-! ## The new chords (`K > 0`) -/

/-- The walk-order points of the host of region `r`. -/
noncomputable def regPts (li : Bool) (n : ℕ) (N : NF) (r : ℕ) : List SymPt :=
  wlist li ((regHost li n N r).pts n)

/-- **The new chords of the base case** (`K > 0`): the records emitted by the regions. -/
noncomputable def newL (li : Bool) (Q : Polygon) (N : NF) : List (ℕ × ℕ × ℕ) :=
  (List.range N.nRegions).flatMap fun r => regList li Q (regPts li Q.n N r)

section K

variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {li : Bool}

/-- The facts of one region. -/
theorem region_facts {r : ℕ} (X : DownMath.RegCtx Q L E reg r) (hli : li = true ↔ Mountain.LeftInside Q) :
    RegOK Q ((buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) (reg r)
      (polyOf Q (regPts li Q.n (buildNF (interiorModel Q) Q L E) r)) ∧
      ∀ s ∈ regPts li Q.n (buildNF (interiorModel Q) Q L E) r, s.Lt Q.n := by
  refine ⟨regOK_host X hli, fun s hs => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, hwf⟩ := DownMath.walk_rep X hli
  have hn : 0 < Q.n := by have := X.hQ.1; omega
  have hwf' : HostWF Q.n (regHost li Q.n (buildNF (interiorModel Q) Q L E) r) := by
    unfold regHost; split_ifs
    · exact hwf
    · intro it hit; exact hwf it (List.mem_reverse.1 hit)
  exact host_pts_lt hn hwf' s (wlist_mem hs)

/-- The context of the base case (`K > 0`). -/
structure BaseCtx (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (reg : ℕ → Set Point)
    (li : Bool) : Prop where
  hQ : Q.Simple
  hdh : DistinctHeights Q
  hL : ChordTriplesOK (interiorModel Q) Q L
  hperm : E.Perm (List.range (2 * L.length))
  hsort : E.Pairwise (codeLe (interiorModel Q) Q L)
  hK : 0 < L.length
  hregs : Restore.NFRegs (interiorModel Q) Q (buildNF (interiorModel Q) Q L E) reg
  hli : li = true ↔ Mountain.LeftInside Q

theorem BaseCtx.rc (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (buildNF (interiorModel Q) Q L E).nRegions) : DownMath.RegCtx Q L E reg r :=
  ⟨B.hQ, B.hdh, B.hL, B.hperm, B.hsort, B.hK, B.hregs, hr⟩

theorem BaseCtx.fam (B : BaseCtx Q L E reg li) :
    (interiorModel Q).ChordFamily Q ((buildNF (interiorModel Q) Q L E).F (interiorModel Q) Q) :=
  (DownMath.isNF_build B.hQ B.hL B.hperm B.hsort).1


/-- The facts of a new chord. -/
theorem newL_mem (B : BaseCtx Q L E reg li) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ newL li Q (buildNF (interiorModel Q) Q L E)) :
    ∃ r, r < (buildNF (interiorModel Q) Q L E).nRegions ∧
      x ∈ regList li Q (regPts li Q.n (buildNF (interiorModel Q) Q L E) r) ∧
      (recOf x).toSet (interiorModel Q) Q ∈ chords Q ∧
      (recOf x).toSet (interiorModel Q) Q ∉ famL (interiorModel Q) Q L ∧
      (recOf x).toSet (interiorModel Q) Q ∩ (interiorModel Q).D ⊆ reg r ∧
      (recOf x).Attached (interiorModel Q) Q ∧
      ProperPos (interiorModel Q) Q Q.n (recOf x).lpos ∧
      ProperPos (interiorModel Q) Q Q.n (recOf x).rpos ∧ x.1 < Q.n := by
  unfold newL at hx
  obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
  Ξ' List.mem_range at hr
  obtain ⟨hR, hl⟩ := region_facts (B.rc hr) B.hli
  have := regList_sound B.hQ B.hdh B.hli B.fam hR hl hxr
  Ξ' F_build at this
  exact ⟨r, hr, hxr, this⟩

/-- **The new chord list is valid** with the old one. -/
theorem newL_ok (B : BaseCtx Q L E reg li) :
    ChordTriplesOK (interiorModel Q) Q (L ++ newL li Q (buildNF (interiorModel Q) Q L E)) := by
  have hL := B.hL
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- finite
    have : {c | ∃ x ∈ L ++ newL li Q (buildNF (interiorModel Q) Q L E), c = (recOf x).toSet (interiorModel Q) Q} =
        (fun x => (recOf x).toSet (interiorModel Q) Q) '' {x | x ∈ L ++ newL li Q (buildNF (interiorModel Q) Q L E)} := by
      ext c; Θ eq_comm
    Ξ this
    exact (List.finite_toSet _).image _
  · rintro c ⟨x, hx, rfl⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact hL.1.2.1 ⟨x, hx, rfl⟩
    · obtain ⟨-, -, -, h, -⟩ := newL_mem B hx
      exact chords_family B.hQ h
  · rintro c ⟨x, hx, rfl⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact hL.1.2.2 _ ⟨x, hx, rfl⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := newL_mem B hx
      exact ⟨x.1, h, _, _, rfl⟩
  · -- distinct
    Ξ List.map_append, List.nodup_append
    refine ⟨hL.2.1, ?_, ?_⟩
    · unfold newL
      Ξ List.map_flatMap, List.nodup_flatMap
      refine ⟨fun r hr => ?_, ?_⟩
      · Ξ' List.mem_range at hr
        obtain ⟨hR, hl⟩ := region_facts (B.rc hr) B.hli
        exact regList_nodup B.hQ B.hdh B.hli B.fam hR hl
      · refine List.nodup_range.pairwise_of_forall_ne fun r hr r' hr' hrr => ?_
        Ξ' List.mem_range at hr hr'
        refine List.disjoint_left.2 fun c hc hc' => hrr ?_
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
        obtain ⟨x', hx', hxx⟩ := List.mem_map.1 hc'
        obtain ⟨hR, hl⟩ := region_facts (B.rc hr) B.hli
        obtain ⟨hR', hl'⟩ := region_facts (B.rc hr') B.hli
        obtain ⟨hcQ, -, hcR, -⟩ := regList_sound B.hQ B.hdh B.hli B.fam hR hl hx
        obtain ⟨-, -, hcR', -⟩ := regList_sound B.hQ B.hdh B.hli B.fam hR' hl' hx'
        Ξ' hxx at hcR'
        obtain ⟨z, hz⟩ := chord_dom_nonempty B.hQ hcQ
        have hreg := B.hregs.1
        rcases Chazelle.Chain.regionsIn_eq_or_disjoint (hreg.1 r hr) (hreg.1 r' hr') with h | h
        · exact hreg.2.1 r r' hr hr' h
        · exact absurd (h.le_bot ⟨hcR hz, hcR' hz⟩) (✓)
    · intro c hc c' hc' hcc
      subst hcc
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
      obtain ⟨x', hx', hxx⟩ := List.mem_map.1 hc'
      obtain ⟨-, -, -, -, h, -⟩ := newL_mem B hx'
      exact h ⟨x, hx, hxx⟩
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hL.2.2.1 x hx
    · obtain ⟨-, -, -, -, -, -, h, -⟩ := newL_mem B hx
      exact h
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hL.2.2.2 x hx
    · obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := newL_mem B hx
      exact h

/-- **Every vertex chord of `Q` is a chord of the completed list.** -/
theorem newL_full (B : BaseCtx Q L E reg li) :
    chords Q ⊆ famL (interiorModel Q) Q (L ++ newL li Q (buildNF (interiorModel Q) Q L E)) := by
  intro c hc
  Ξ famL_append
  by_cases hcS : c ∈ famL (interiorModel Q) Q L
  · exact Or.inl hcS
  right
  have hFam := B.fam
  Ξ' F_build at hFam
  obtain ⟨R, hR, hcR, -⟩ := DownDrv.full_in_region B.hQ hFam hc hcS
  Ξ' ← F_build (E := E) at hR
  obtain ⟨r, hr, rfl⟩ := B.hregs.1.2.2 R hR
  obtain ⟨hRo, hl⟩ := region_facts (B.rc hr) B.hli
  Ξ' F_build at hRo
  obtain ⟨x, hx, hxc⟩ := regList_complete B.hQ B.hdh B.hli hRo hl hc hcS hcR
  exact ⟨x, List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, hx⟩, hxc.symm⟩

end K

/-! ## The new chords (`K = 0`) -/

/-- **The new chords of the base case** (`K = 0`): the records emitted by the whole walk. -/
noncomputable def newL0 (li : Bool) (Q : Polygon) : List (ℕ × ℕ × ℕ) :=
  regList li Q (wlist li (Host.pts Q.n [HostItem.run 0 (Q.n - 1)]))

section K0

variable {Q : Polygon} {li : Bool}

theorem run_pts_lt (hQ : Q.Simple) :
    ∀ s ∈ wlist li (Host.pts Q.n [HostItem.run 0 (Q.n - 1)]), s.Lt Q.n := by
  intro s hs
  have hn : 0 < Q.n := by have := hQ.1; omega
  refine host_pts_lt hn ?_ s (wlist_mem hs)
  intro it hit
  ϴ' List.mem_singleton at hit
  subst hit
  exact ⟨⋄, ⋄⟩

theorem regOK0 (hQ : Q.Simple) (hli : li = true ↔ Mountain.LeftInside Q) :
    RegOK Q ∅ (interiorModel Q).D (polyOf Q (wlist li (Host.pts Q.n [HostItem.run 0 (Q.n - 1)]))) := by
  rw [polyOf_wlist_run hQ hli]; exact regOK_empty hQ hli

/-- **The new chord list is valid** (`K = 0`). -/
theorem newL0_ok (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) :
    ChordTriplesOK (interiorModel Q) Q (newL0 li Q) := by
  have hFam : (interiorModel Q).ChordFamily Q (∅ : Set (Set Point)) :=
    ⟨finite_empty, empty_subset _, fun c hc => absurd hc (notMem_empty c)⟩
  have hR := regOK0 hQ hli
  have hl := run_pts_lt (li := li) hQ
  refine ⟨⟨?_, ?_, ?_⟩, regList_nodup hQ hDH hli hFam hR hl, fun x hx => ?_, fun x hx => ?_⟩
  · have : {c | ∃ x ∈ newL0 li Q, c = (recOf x).toSet (interiorModel Q) Q} =
        (fun x => (recOf x).toSet (interiorModel Q) Q) '' {x | x ∈ newL0 li Q} := by
      ext c; simp [eq_comm]
    Ξ this
    exact (List.finite_toSet _).image _
  · rintro c ⟨x, hx, rfl⟩
    exact chords_family hQ (regList_sound hQ hDH hli hFam hR hl hx).1
  · rintro c ⟨x, hx, rfl⟩
    exact ⟨x.1, (regList_sound hQ hDH hli hFam hR hl hx).2.2.2.2.2.2, _, _, rfl⟩
  · exact (regList_sound hQ hDH hli hFam hR hl hx).2.2.2.1
  · exact (regList_sound hQ hDH hli hFam hR hl hx).2.2.2.2.2.2

/-- **Every vertex chord of `Q` is emitted** (`K = 0`). -/
theorem newL0_full (hQ : Q.Simple) (hDH : DistinctHeights Q)
    (hli : li = true ↔ Mountain.LeftInside Q) :
    chords Q ⊆ famL (interiorModel Q) Q (newL0 li Q) := by
  intro c hc
  obtain ⟨x, hx, hxc⟩ := regList_complete hQ hDH hli (regOK0 hQ hli) (run_pts_lt hQ) hc
    (notMem_empty c) (fun z hz => hz.2)
  exact ⟨x, hx, hxc.symm⟩

end K0

/-! ## The number of new chords -/

/-- **A valid list of vertex chords has at most `2 n` chords.** -/
theorem length_le_of_chords {Q : Polygon} {L₂ : List (ℕ × ℕ × ℕ)}
    (hnd : (L₂.map fun x => (recOf x).toSet (interiorModel Q) Q).Nodup)
    (hc : ∀ x ∈ L₂, (recOf x).toSet (interiorModel Q) Q ∈ chords Q) : L₂.length ≤ 2 * Q.n := by
  have h1 : (L₂.map fun x => (recOf x).toSet (interiorModel Q) Q).toFinset.card = L₂.length := by
    Ξ List.toFinset_card_of_nodup hnd, List.length_map
  have h2 : ((L₂.map fun x => (recOf x).toSet (interiorModel Q) Q).toFinset : Set (Set Point)) ⊆
      chords Q := by
    intro c hc'
    ϴ' List.coe_toFinset, mem_ofPred_eq, List.mem_map at hc'
    obtain ⟨x, hx, rfl⟩ := hc'
    exact hc x hx
  have h3 := Set.ncard_le_ncard h2 (Visibility.chords_finite Q)
  Ξ' Set.ncard_coe_finset, h1 at h3
  exact h3.trans (Visibility.chords_ncard_le Q)

end

end DrvB

end Chazelle.Core
