module

public import Chazelle.Core.RestoreTPos
public import Chazelle.Rwx
public import Chazelle.SimpTactics

/-!
# WP-E, the candidate test on the RAM, part 7: the validity bit

The validity bit of the candidate test, as a proposition about the stored normal form
(`ValidB`): the region has an exit chord, the direction points into the left sector at the
candidate, and either the candidate's key is strictly inside one of the region's arcs (`FIn`),
or the candidate is a walk vertex, an arc of the region begins (`FS`) there and the direction is
strictly counterclockwise from the next walk edge, or an arc ends there (`FE`) and the direction
is strictly clockwise from the previous edge, and no exit chord of the region leaves the vertex
in the direction (`Clear`).

* `valid_sound`: the validity bit puts the initial part of the ray into the region
  (`valid_inside`, `valid_after`, `valid_before`, `exit_avoid`).
* `valid_compl`: good chords pass the validity checks (`valid_complete`, `valid_complete_int`,
  `exit_block`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross TouchesIn)
open Chazelle.Visibility (rayPt)

variable (M : Model) (P : Polygon) (N : NF) (r : ℕ) (x : WPos) (σb : ℕ)

/-- Some arc of region `r` has the candidate's key strictly inside. -/
def FIn : Prop := ∃ j ∈ (N.region r).arcs,
  sideInArc (M.key (Qof P) (N.arc j).s) (M.key (Qof P) (N.arc j).e)
    (M.key (Qof P) x)

/-- Some arc of region `r` begins at the candidate's key. -/
def FS : Prop := ∃ j ∈ (N.region r).arcs,
  M.key (Qof P) (N.arc j).s = M.key (Qof P) x

/-- Some arc of region `r` ends at the candidate's key. -/
def FE : Prop := ∃ j ∈ (N.region r).arcs,
  M.key (Qof P) (N.arc j).e = M.key (Qof P) x

/-- No exit chord of region `r` leaves the candidate in the direction. -/
def Clear : Prop := ∀ i ∈ (N.region r).chords,
  (σb = 1 → M.key (Qof P) (N.chord i).lpos ≠ M.key (Qof P) x) ∧
  (σb ≠ 1 → M.key (Qof P) (N.chord i).rpos ≠ M.key (Qof P) x)

/-- The direction points into the left sector at the candidate. -/
def LeftB : Prop := sideLeft M.W x.edge (M.param (Qof P) x)
  (rayPt (M.pos (Qof P) x) (dirOf σb) 1)

/-- The turn from the next walk edge is positive. -/
def TurnNB : Prop := 0 < sideCross (M.W.vtx ((x.edge + 1) % M.W.n) -
  M.W.vtx x.edge) ((dirOf σb, 0) : Point)

/-- The turn to the previous walk edge is positive. -/
def TurnPB : Prop := 0 < sideCross ((dirOf σb, 0) : Point)
  (M.W.vtx ((x.edge + M.W.n - 1) % M.W.n) -
    M.W.vtx x.edge)

/-- **The validity bit.** -/
def ValidB : Prop :=
  (N.region r).chords ≠ [] ∧ LeftB M P x σb ∧
    (FIn M P N r x ∨ (M.param (Qof P) x = 0 ∧
      ((FS M P N r x ∧ TurnNB M x σb) ∨ (FE M P N r x ∧ TurnPB M x σb)) ∧ Clear M P N r x σb))

variable {M P N r x σb}

theorem dirOf_pm (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  unfold dirOf; split_ifs <;> simp

theorem dirOf_eq_one {v : ℕ} : dirOf v = 1 ↔ v = 1 := by
  unfold dirOf; split_ifs with h <;> simp [h]; norm_num

/-- A chord of the family of a normal form is a chord record. -/
theorem mem_F_iff {M : Model} {Q : Polygon} {c : Set Point} (hc : c ∈ N.F M Q) :
    ∃ i, i < N.nChords ∧ c = (N.chord i).toSet M Q := by
  obtain ⟨rr, hrr, rfl⟩ := hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrr
  refine ⟨i, hi, ?_⟩
  unfold NF.chord
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- The ends of the chord records are proper positions. -/
theorem chord_proper {M : Model} (hNF : IsNF M (Qof P) N) {i : ℕ} (hi : i < N.nChords) :
    ProperPos M (Qof P) P.n (N.chord i).lpos ∧ ProperPos M (Qof P) P.n (N.chord i).rpos := by
  obtain ⟨-, -, hat, reg, -, -, -, -, -, hh, -⟩ := hNF
  have hQ : (Qof P).n = P.n := shear_n _ _
  have hhn : (N.chord i).h + 1 ≤ P.n := by have := hh i hi; omega
  exact ⟨⟨(hat i hi).1.2.1, (hat i hi).1.2.2.1, hhn⟩, ⟨(hat i hi).2.2.1, (hat i hi).2.2.2.1, hhn⟩⟩

theorem chord_toSet_mem' {M : Model} {Q : Polygon} {i : ℕ} (hi : i < N.nChords) :
    (N.chord i).toSet M Q ∈ N.F M Q :=
  ⟨N.chord i, chord_mem_list hi, rfl⟩

/-- **Soundness of the validity bit.** -/
theorem valid_sound (hGM : GoodModel M) (hNF : IsNF M (Qof P) N)
    {reg : ℕ → Set Point} (hregs : NFRegs M (Qof P) N reg) (hr : r < N.nRegions)
    (hx : ProperPos M (Qof P) P.n x) (hxe : x.edge < M.W.n)
    (hv : ValidB M P N r x σb) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (M.pos (Qof P) x) (dirOf σb) s ∈ reg r := by
  set Q := Qof P
  obtain ⟨hcorr, -, harcs, hregsOK⟩ := hregs
  have hFam := hNF.1
  have hU : reg r ∈ M.regions (N.F M Q) := hcorr.1 r hr
  obtain ⟨-, hL, hcase⟩ := hv
  have hpos : M.pos Q x = sidePt M.W x.edge (M.param Q x) := rfl
  have hτ := dirOf_pm σb
  have arcOf : ∀ j ∈ (N.region r).arcs,
      M.IsArc (N.F M Q) (reg r) (M.key Q (N.arc j).s) (M.key Q (N.arc j).e) := by
    intro j hj
    obtain ⟨hjl, hjr⟩ := (harcs.2.2.2 r hr j).1 hj
    have := (harcs.1 j hjl).2
    rwa [hjr] at this
  rw [hpos]
  rcases hcase with ⟨j, hj, hin⟩ | ⟨h0, hc, hcl⟩
  · exact valid_inside hGM hFam hU hxe hx.1 hx.2.1 (arcOf j hj) hin hτ hL
  · have hkx : M.key Q x = (x.edge : ℝ) + 0 := by unfold Model.key; rw [h0]
    have e0 : M.param (Qof P) x = 0 := h0
    have hL' : sideLeft M.W x.edge 0 (rayPt (sidePt M.W x.edge 0) (dirOf σb) 1) := by
      have := hL
      unfold LeftB at this
      rw [show M.pos (Qof P) x = sidePt M.W x.edge 0 by rw [SweepPrim.pos_eq_sidePt, e0], e0]
        at this
      exact this
    rw [e0]
    -- the exit scan
    have hex : ∀ c ∈ N.F M Q, TouchesIn M.D c (reg r) →
        ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W x.edge 0) (dirOf σb) s ∉ c := by
      intro c hc ht
      obtain ⟨i, hi, rfl⟩ := mem_F_iff hc
      have hmem : i ∈ (N.region r).chords := ((hregsOK r hr).1 i).2 ⟨hi, ht⟩
      obtain ⟨hcl1, hcl2⟩ := hcl i hmem
      refine exit_avoid hGM hFam hc (hNF.2.2.1 i hi) hxe hτ hL' ?_ ?_
      · intro h1 ⟨hlp, hl0⟩
        apply hcl1 (dirOf_eq_one.1 h1)
        rw [hkx]; unfold Model.key; rw [hl0]; simp [CRec.lpos, hlp]
      · intro h1 ⟨hrp, hr0⟩
        refine hcl2 (fun h => ?_) ?_
        · rw [h] at h1; unfold dirOf at h1; norm_num at h1
        · rw [hkx]; unfold Model.key; rw [hr0]; simp [CRec.rpos, hrp]
    rcases hc with ⟨⟨j, hj, hk⟩, htn⟩ | ⟨⟨j, hj, hk⟩, htp⟩
    · have harc := arcOf j hj
      rw [hk, hkx] at harc
      exact valid_after hGM hFam hU hxe harc hτ hL' htn hex
    · have harc := arcOf j hj
      rw [hk, hkx] at harc
      exact valid_before hGM hFam hU hxe harc hτ hL' htp hex

/-- **Completeness of the validity bit**: the validity checks accept an admissible chord outside
the family from the candidate, in its left sector, whose open part lies in the region. -/
theorem valid_compl (hGM : GoodModel M) (hNF : IsNF M (Qof P) N)
    {reg : ℕ → Set Point} (hregs : NFRegs M (Qof P) N reg) (hr : r < N.nRegions)
    (hx : ProperPos M (Qof P) P.n x) (hxe : x.edge < M.W.n)
    (hex : (N.region r).chords ≠ []) (hL : LeftB M P x σb) {T : ℝ} (hT : 0 < T)
    (hdom : ∀ t, 0 < t → t < T →
      rayPt (M.pos (Qof P) x) (dirOf σb) t ∈ M.D)
    (hadm : chordOf (M.pos (Qof P) x) (dirOf σb) T ∈ M.Adm)
    (hnF : chordOf (M.pos (Qof P) x) (dirOf σb) T ∉ N.F M (Qof P))
    (hsub : chordOf (M.pos (Qof P) x) (dirOf σb) T ∩ M.D ⊆ reg r) :
    ValidB M P N r x σb := by
  set Q := Qof P
  have hM := walkAx_of_goodModel hGM
  obtain ⟨hcorr, -, harcs, hregsOK⟩ := hregs
  have hFam := hNF.1
  have hU : reg r ∈ M.regions (N.F M Q) := hcorr.1 r hr
  have hτ := dirOf_pm σb
  have hpos : M.pos Q x = sidePt M.W x.edge (M.param Q x) := rfl
  -- the family is nonempty
  obtain ⟨i₀, hi₀⟩ : ∃ i, i ∈ (N.region r).chords := by
    rcases hl : (N.region r).chords with _ | ⟨a, l⟩
    · exact absurd hl hex
    · exact ⟨a, by simp⟩
  have hne : (N.F M Q).Nonempty := by
    have := (((hregsOK r hr).1 i₀).1 hi₀).1
    exact ⟨_, chord_toSet_mem' this⟩
  -- an arc of the region is listed
  have listed : ∀ a b, M.IsArc (N.F M Q) (reg r) a b →
      ∃ j ∈ (N.region r).arcs, M.key Q (N.arc j).s = a ∧ M.key Q (N.arc j).e = b := by
    intro a b hab
    obtain ⟨j, hj, hjr, ha, hb⟩ := harcs.2.2.1 r hr a b hab
    exact ⟨j, (harcs.2.2.2 r hr j).2 ⟨hj, hjr⟩, ha, hb⟩
  refine ⟨hex, hL, ?_⟩
  rcases hx.1.lt_or_eq with ht0 | ht0
  · -- inside a walk edge
    rw [hpos] at hdom hadm hnF hsub
    obtain ⟨a, b, hab, hin⟩ := valid_complete_int hGM hFam hne hU hadm hnF hsub hxe ht0 hx.2.1
      hτ hL hT rfl hdom
    obtain ⟨j, hj, ha, hb⟩ := listed a b hab
    exact Or.inl ⟨j, hj, by rwx [ha, hb]⟩
  · -- at a walk vertex
    have h0 : M.param Q x = 0 := ht0.symm
    have hkx : M.key Q x = (x.edge : ℝ) + 0 := by unfold Model.key; rw [h0]
    rw [hpos, h0] at hdom hadm hnF hsub
    have hL' := hL
    unfold LeftB at hL'
    rw [hpos, h0] at hL'
    obtain ⟨hnot, hcase⟩ := valid_complete hGM hFam hne hU hadm hnF hsub hxe hτ hL' hT rfl hdom
    have hcl : Clear M P N r x σb := by
      intro i hi
      have hi' := (((hregsOK r hr).1 i).1 hi).1
      have hcF : (N.chord i).toSet M Q ∈ N.F M Q := chord_toSet_mem' hi'
      have hadmi := hFam.2.1 hcF
      have hat := hNF.2.2.1 i hi'
      have hav : ∀ᶠ s in 𝓝[>] (0 : ℝ),
          rayPt (sidePt M.W x.edge 0) (dirOf σb) s ∉ (N.chord i).toSet M Q := by
        filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hT] with s hs hsT
        exact hnot _ hcF s hs hsT.2
      have hlpos : ProperPos M Q P.n (N.chord i).lpos ∧ ProperPos M Q P.n (N.chord i).rpos :=
        chord_proper hNF hi'
      refine ⟨fun h1 hk => ?_, fun h1 hk => ?_⟩
      · rw [hkx] at hk
        unfold Model.key at hk
        obtain ⟨e1, e2⟩ := Chazelle.Chain.sideKey_inj hlpos.1.1 hlpos.1.2.1 le_rfl one_pos hk
        exact exit_block hM hadmi hat hτ (Or.inl ⟨dirOf_eq_one.2 h1, e1, e2⟩) hav
      · rw [hkx] at hk
        unfold Model.key at hk
        obtain ⟨e1, e2⟩ := Chazelle.Chain.sideKey_inj hlpos.2.1 hlpos.2.2.1 le_rfl one_pos hk
        have hm : dirOf σb = -1 := by unfold dirOf; rw [ite_eq_right h1]
        exact exit_block hM hadmi hat hτ (Or.inr ⟨hm, e1, e2⟩) hav
    rcases hcase with ⟨a, b, hab, hin⟩ | ⟨b, hab, hcr⟩ | ⟨a, hab, hcr⟩
    · obtain ⟨j, hj, ha, hb⟩ := listed a b hab
      exact Or.inl ⟨j, hj, by rwx [ha, hb, hkx]⟩
    · obtain ⟨j, hj, ha, -⟩ := listed _ b hab
      exact Or.inr ⟨h0, Or.inl ⟨⟨j, hj, by rw [ha, hkx]⟩, hcr⟩, hcl⟩
    · obtain ⟨j, hj, -, hb⟩ := listed a _ hab
      exact Or.inr ⟨h0, Or.inr ⟨⟨j, hj, by rw [hb, hkx]⟩, hcr⟩, hcl⟩

end

end Restore

end Chazelle.Core
