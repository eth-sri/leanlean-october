module

public import Chazelle.MacT
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.GranInitL3
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.ShootCutCore2
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.ShootCutShPt
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.GranWt
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.NFBuildRegFill

namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open Chazelle.Visibility (rayPt)
open Sweep

/-- The points of an admissible chord of a chain model are strictly inside the height band of
the box. -/
theorem chord_height_lt {C : Chain} (hP : C.P.Simple) {c : Set Point}
    (hc : c ∈ (chainModel C).Adm) {z : Point} (hz : z ∈ c) : |z.2| < C.radius := by
  zuoj
  obtain ⟨y, a, b, hH, rfl⟩ := adm_hchord hGM hc
  have hy : ztlbm := hz.1
  have hm : (ztwsj : Point) ∈ (chainModel C).D :=
    hH.open_mem _ ztbzj ztbzj
  have := (C.dom_subset_box hm).2
  simp_all

/-- **A position at which an admissible chord is attached** is a valid input of `offCmp`. -/
theorem posOK_of_attach {C : Chain} (hP : C.P.Simple) {Q : Polygon} {n : ℕ} {x : WPos}
    {c : Set Point} (hc : c ∈ (chainModel C).Adm)
    (hA : SideAttach (chainModel C).W c x.edge ztuy) (hh : x.hgt ≤ n) :
    PosOK C Q n x :=
  posOK_of hA.1 ⟨hA.2.1, hA.2.2.1, hh⟩ (chord_height_lt hP hc hA.2.2.2.1)
variable {C : Chain} {P : Polygon} {N : NF}
theorem chord_mem_list {i : ℕ} (hi : i < N.nChords) : N.chord i ∈ N.chords := by
  zudly
  zucpl
  grind

/-- **The ends of the chord records** are valid inputs of `offCmp`. -/
theorem chord_posOK (hP : C.P.Simple) (hNF : IsNF ztc zta N) {i : ℕ}
    (hi : i < N.nChords) :
    PosOK C zta P.n (N.chord i).lpos ∧ PosOK C zta P.n (N.chord i).rpos := by
  obtain ⟨hFam, -, hat, reg, -, -, -, -, -, hh, -⟩ := hNF
  zusu
  have hadm : (N.chord i).toSet ztc zta ∈ (chainModel C).Adm :=
    hFam.2.1 ⟨_, chord_mem_list hi, rfl⟩
  zukck
  exact ⟨posOK_of_attach hP hadm (hat i hi).1 hhn, posOK_of_attach hP hadm (hat i hi).2 hhn⟩

/-- **The ends of the arc records** of a nonempty family are valid inputs of `offCmp`. -/
theorem arc_posOK (hP : C.P.Simple) (hNF : IsNF ztc zta N)
    (hne : (N.F ztc zta).Nonempty) {j : ℕ} (hj : j < N.arcs.length) :
    PosOK C zta P.n (N.arc j).s ∧ PosOK C zta P.n (N.arc j).e := by
  zubua
  zusu
  zuls

  zufjs
  have key : ∀ x : WPos, ProperPos ztc zta (Qof P).n x →
      (chainModel C).IsCut ztwjq ztwol →
      PosOK C zta P.n x := by
    zucse

    obtain ⟨hpp, htt⟩ := sideKey_inj hx.1 hx.2.1 hA.2.1 hA.2.2.1 hk
    zugxu
    exact posOK_of_attach hP ztvtb hA (by zvnoq; exact hx.2.2)
  simp_all
variable {M : Model}
/-- **The left end of an attached admissible record is left of its right end.** -/
theorem endpoints_lt (hM : WalkAx M) {Q : Polygon} {r : CRec}
    (hadm : r.toSet M Q ∈ M.Adm) (hr : r.Attached M Q) :
    (M.pos Q r.lpos).1 < (M.pos Q r.rpos).1 := by
  zubjj

  have hpA : sidePt M.W r.lp ztfog = M.pos Q r.lpos := rfl
  zuduk

  zuks

  have hsub : ztiem := by
    zugti

  zubfz

/-- **The exit scan is complete**: an attached admissible record whose left end is the walk vertex
`(p, 0)` contains ray points arbitrarily close to the vertex in direction `1`; one whose right end
is the vertex, in direction `-1`. -/
theorem exit_block (hM : WalkAx M) {Q : Polygon} {cr : CRec}
    (hadm : cr.toSet M Q ∈ M.Adm) (hat : cr.Attached M Q) {p : ℕ} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hend : (σ = 1 ∧ cr.lp = p ∧ M.param Q cr.lpos = 0) ∨
      (σ = -1 ∧ cr.rp = p ∧ M.param Q cr.rpos = 0))
    (hav : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztfs σ s ∉ cr.toSet M Q) : False := by
  have hlt := endpoints_lt hM hadm hat
  have epl : sidePt M.W cr.lp zttaa = M.pos Q cr.lpos := rfl
  have epr : sidePt M.W cr.rp zttab = M.pos Q cr.rpos := rfl
  rcases hend with ⟨rfl, hl, h0⟩ | ⟨rfl, hl, h0⟩
  · have hA := hat.1
    zubsl

    obtain ⟨s, hs0, -, hx⟩ := hall _ hat.2.2.2.2.1
    rw [epr] at hx
    have e1 : (M.pos Q cr.rpos).1 = (sidePt M.W p 0).1 - s := by
      zvnly; simp only [Visibility.rayPt]; ring
    grind
  · have hA := hat.2
    zubsl

    obtain ⟨s, hs0, -, hx⟩ := hall _ hat.1.2.2.2.1
    rw [epl] at hx
    have e1 : (M.pos Q cr.lpos).1 = (sidePt M.W p 0).1 + s := by
      simp_all
    grind
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross TouchesIn)
open Chazelle.Visibility (rayPt)
variable (M : Model) (P : Polygon) (N : NF) (r : ℕ) (x : WPos) (σb : ℕ)

/-- Some arc of region `r` has the candidate's key strictly inside. -/
def FIn : Prop := ∃ j ∈ (N.region r).arcs,
  sideInArc (M.key zta (N.arc j).s) (M.key zta (N.arc j).e)
    ztwzj

/-- Some arc of region `r` begins at the candidate's key. -/
def FS : Prop := ∃ j ∈ (N.region r).arcs,
  M.key zta (N.arc j).s = M.key zta x

/-- Some arc of region `r` ends at the candidate's key. -/
def FE : Prop := ∃ j ∈ (N.region r).arcs,
  M.key zta (N.arc j).e = M.key zta x

/-- No exit chord of region `r` leaves the candidate in the direction. -/
def Clear : Prop := ∀ i ∈ (N.region r).chords,
  (σb = 1 → M.key zta (N.chord i).lpos ≠ M.key zta x) ∧
  (σb ≠ 1 → M.key zta (N.chord i).rpos ≠ M.key zta x)

/-- The direction points into the left sector at the candidate. -/
def LeftB : Prop := sideLeft M.W x.edge ztxkg
  (rayPt ztwlu ztbem 1)

/-- The turn from the next walk edge is positive. -/
def TurnNB : Prop := 0 < sideCross (M.W.vtx ztxyn -
  M.W.vtx x.edge) ((dirOf σb, 0) : Point)

/-- The turn to the previous walk edge is positive. -/
def TurnPB : Prop := 0 < sideCross ((dirOf σb, 0) : Point)
  (M.W.vtx ztdkc -
    M.W.vtx x.edge)

/-- **The validity bit.** -/
def ValidB : Prop :=
  (N.region r).chords ≠ [] ∧ LeftB M P x σb ∧
    (FIn M P N r x ∨ (M.param zta x = 0 ∧
      ((FS M P N r x ∧ TurnNB M x σb) ∨ (FE M P N r x ∧ TurnPB M x σb)) ∧ Clear M P N r x σb))
variable {M P N r x σb}
theorem dirOf_pm (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  zubqi
theorem dirOf_eq_one {v : ℕ} : dirOf v = 1 ↔ v = 1 := by
  zubqi

/-- A chord of the family of a normal form is a chord record. -/
theorem mem_F_iff {M : Model} {Q : Polygon} {c : Set Point} (hc : c ∈ N.F M Q) :
    ∃ i, i < N.nChords ∧ c = (N.chord i).toSet M Q := by
  obtain ⟨rr, hrr, rfl⟩ := hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrr
  zuifc
  zudly
  simp_all

/-- The ends of the chord records are proper positions. -/
theorem chord_proper {M : Model} (hNF : IsNF M zta N) {i : ℕ} (hi : i < N.nChords) :
    ProperPos M zta P.n (N.chord i).lpos ∧ ProperPos M zta P.n (N.chord i).rpos := by
  obtain ⟨-, -, hat, reg, -, -, -, -, -, hh, -⟩ := hNF
  zusu
  zukck
  exact ⟨⟨(hat i hi).1.2.1, (hat i hi).1.2.2.1, hhn⟩, ⟨(hat i hi).2.2.1, (hat i hi).2.2.2.1, hhn⟩⟩
theorem chord_toSet_mem' {M : Model} {Q : Polygon} {i : ℕ} (hi : i < N.nChords) :
    (N.chord i).toSet M Q ∈ N.F M Q :=
  ⟨N.chord i, chord_mem_list hi, rfl⟩

/-- **Soundness of the validity bit.** -/
theorem valid_sound (hGM : GoodModel M) (hNF : IsNF M zta N)
    {reg : ℕ → Set Point} (hregs : NFRegs M zta N reg) (hr : r < N.nRegions)
    (hx : ProperPos M zta P.n x) (hxe : x.edge < M.W.n)
    (hv : ValidB M P N r x σb) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztwlu ztbem s ∈ reg r := by
  zubep
  zucbm

  obtain ⟨-, hL, hcase⟩ := hv
  zuket
  zullz
  have arcOf : ∀ j ∈ (N.region r).arcs,
      M.IsArc ztdu ztcz ztbpl ztdfq := by
    zun
    obtain ⟨hjl, hjr⟩ := (harcs.2.2.2 r hr j).1 hj
    have := (harcs.1 j hjl).2
    simp_all
  zudul
  rcases hcase with ⟨j, hj, hin⟩ | ⟨h0, hc, hcl⟩
  · exact valid_inside hGM hFam hU hxe hx.1 hx.2.1 (arcOf j hj) hin hτ hL
  · zuerc
    have e0 : M.param zta x = 0 := h0
    have hL' : sideLeft M.W x.edge 0 (rayPt ztltm ztbem 1) := by
      have := hL
      unfold LeftB at this
      grind
    zujhv
    -- the exit scan
    have hex : ∀ c ∈ N.F M Q, TouchesIn M.D c ztcz →
        ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt ztltm ztbem s ∉ c := by
      intro c hc ht
      obtain ⟨i, hi, rfl⟩ := mem_F_iff hc
      have hmem : i ∈ (N.region r).chords := ((hregsOK r hr).1 i).2 ztoog
      obtain ⟨hcl1, hcl2⟩ := hcl i hmem
      refine exit_avoid hGM hFam hc (hNF.2.2.1 i hi) hxe hτ hL' ?_ ?_
      · intro h1 ⟨hlp, hl0⟩
        apply hcl1 (dirOf_eq_one.1 h1)
        zuofz; unfold Model.key; rw [hl0]; simp [CRec.lpos, hlp]
      · intro h1 ⟨hrp, hr0⟩
        refine hcl2 ztep ?_
        · zvmwc at h1; unfold dirOf at h1; grind
        · zuofz; unfold Model.key; rw [hr0]; simp [CRec.rpos, hrp]
    rcases hc with ⟨⟨j, hj, hk⟩, htn⟩ | ⟨⟨j, hj, hk⟩, htp⟩
    · zuegt

      exact valid_after hGM hFam hU hxe harc hτ hL' htn hex
    · zuegt

      exact valid_before hGM hFam hU hxe harc hτ hL' htp hex

/-- **Completeness of the validity bit**: the validity checks accept an admissible chord outside
the family from the candidate, in its left sector, whose open part lies in the region. -/
theorem valid_compl (hGM : GoodModel M) (hNF : IsNF M zta N)
    {reg : ℕ → Set Point} (hregs : NFRegs M zta N reg) (hr : r < N.nRegions)
    (hx : ProperPos M zta P.n x) (hxe : x.edge < M.W.n)
    (hex : (N.region r).chords ≠ []) (hL : LeftB M P x σb) {T : ℝ} (hT : 0 < T)
    (hdom : ∀ t, 0 < t → t < T →
      rayPt ztwlu ztbem t ∈ M.D)
    (hadm : chordOf ztwlu ztbem T ∈ M.Adm)
    (hnF : chordOf ztwlu ztbem T ∉ N.F M zta)
    (hsub : chordOf ztwlu ztbem T ∩ M.D ⊆ reg r) :
    ValidB M P N r x σb := by
  zubep
  zubm
  zucbm

  zullz
  zuket
  -- the family is nonempty
  obtain ⟨i₀, hi₀⟩ : ∃ i, i ∈ (N.region r).chords := by
    rcases hl : (N.region r).chords with _ | ⟨a, l⟩
    · simp_all
    simp
  have hne : (N.F M Q).Nonempty := by
    have := (((hregsOK r hr).1 i₀).1 hi₀).1
    exact ⟨_, chord_toSet_mem' this⟩
  -- an arc of the region is listed
  have listed : ∀ a b, M.IsArc ztdu ztcz a b →
      ∃ j ∈ (N.region r).arcs, M.key Q (N.arc j).s = a ∧ M.key Q (N.arc j).e = b := by
    zujat
    obtain ⟨j, hj, hjr, ha, hb⟩ := harcs.2.2.1 r hr a b hab
    exact ⟨j, (harcs.2.2.2 r hr j).2 zthnb, ha, hb⟩
  refine ⟨hex, hL, ?_⟩
  rcases hx.1.lt_or_eq with ht0 | ht0
  · -- inside a walk edge
    zvnbl at hdom hadm hnF hsub
    obtain ⟨a, b, hab, hin⟩ := valid_complete_int hGM hFam hne hU hadm hnF hsub hxe ht0 hx.2.1
      hτ hL hT rfl hdom
    zuebh
    exact Or.inl ⟨j, hj, by rw [ha, hb]; tauto⟩
  · -- at a walk vertex
    have h0 : ztmtm := ht0.symm
    zuerc
    rw [hpos, h0] at hdom hadm hnF hsub
    zumbx
    unfold LeftB at hL'
    rw [hpos, h0] at hL'
    obtain ⟨hnot, hcase⟩ := valid_complete hGM hFam hne hU hadm hnF hsub hxe hτ hL' hT rfl hdom
    have hcl : Clear M P N r x σb := by
      zug
      have hi' := (((hregsOK r hr).1 i).1 hi).1
      have hcF : ztdjo := chord_toSet_mem' hi'
      have hadmi := hFam.2.1 hcF
      have hat := hNF.2.2.1 i hi'
      have hav : ∀ᶠ s in 𝓝[>] (0 : ℝ),
          rayPt ztltm ztbem s ∉ (N.chord i).toSet M Q := by
        zumy
        exact hnot _ hcF s hs hsT.2
      have hlpos : ProperPos M Q P.n (N.chord i).lpos ∧ ProperPos M Q P.n (N.chord i).rpos :=
        chord_proper hNF hi'
      refine ⟨fun h1 hk => ?_, fun h1 hk => ?_⟩
      · zukut
        zuckv
        obtain ⟨e1, e2⟩ := Chazelle.Chain.sideKey_inj hlpos.1.1 hlpos.1.2.1 le_rfl one_pos hk
        exact exit_block hM hadmi hat hτ (Or.inl ⟨dirOf_eq_one.2 h1, e1, e2⟩) hav
      · zukut
        zuckv
        obtain ⟨e1, e2⟩ := Chazelle.Chain.sideKey_inj hlpos.2.1 hlpos.2.2.1 le_rfl one_pos hk
        have hm : ztshy := by unfold dirOf; grind
        exact exit_block hM hadmi hat hτ (Or.inr ⟨hm, e1, e2⟩) hav
    rcases hcase with ⟨a, b, hab, hin⟩ | ⟨b, hab, hcr⟩ | ⟨a, hab, hcr⟩
    · zuebh
      exact Or.inl ztgpb
    · obtain ⟨j, hj, ha, -⟩ := listed _ b hab
      exact Or.inr ⟨h0, Or.inl ztbabm, hcl⟩
    · obtain ⟨j, hj, -, hb⟩ := listed a _ hab
      exact Or.inr ⟨h0, Or.inr ztbabm, hcl⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Chazelle.Chain (sideLeft sideLeftOf sideCcw sideCross sideDot sidePt sideLeft_zero)
open Chazelle.Visibility (rayPt)
open Chazelle.Geometry (point_ext)

/-- **The corner sector for a horizontal direction.** -/
theorem sector_horiz {a v b : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hb : b.2 ≠ v.2)
    (ha : a.2 ≠ v.2) :
    sideLeftOf a v b ztczx ↔
      (0 < sideCross ztfd ztgg ∧ 0 < sideCross ztfd (ztwn : Point) ∧
        0 < sideCross (ztwn : Point) ztgg) ∨
      (¬ 0 < sideCross ztfd ztgg ∧ (0 < sideCross ztfd (ztwn : Point) ∨
        0 < sideCross (ztwn : Point) ztgg)) := by
  have hX : rayPt v σ 1 - v = (ztwn : Point) := by
    zueob
  zueez
  zuexv
  obtain ⟨b1, b2⟩ := b
  obtain ⟨a1, a2⟩ := a
  zuide
  simp only [sideCross, sideDot, Prod.fst_sub, Prod.snd_sub, ne_eq] at hb ha ⊢
  have hB : b2 - v2 ≠ 0 := sub_ne_zero.2 hb
  have hA : a2 - v2 ≠ 0 := sub_ne_zero.2 ha
  set B1 := b1 - v1
  set B2 := b2 - v2
  set A1 := a1 - v1
  set A2 := a2 - v2
  have hS : 0 < A1 ^ 2 + A2 ^ 2 := by_positivity
  have hA2 : 0 < A2 ^ 2 := by_positivity
  have hBA : B2 * A2 ≠ 0 := mul_ne_zero hB hA
  rcases lt_trichotomy (B1 * A2 - B2 * A1) 0 with hd | hd | hd
  · -- reflex
    grind
  · -- collinear
    have hcol : B1 * A2 = B2 * A1 := by_linarith
    have hdot : (B1 * A1 + B2 * A2) * A2 ^ 2 = B2 * A2 * ztniu := by
      grind
    have hdpos : 0 < B1 * A1 + B2 * A2 ↔ 0 < B2 * A2 := by
      constructor
      · intro h; have := mul_pos h hA2; simp_all
      · intro h; have := mul_pos h hS; rw [← hdot] at this
        exact (mul_pos_iff_of_pos_right hA2).1 this
    have hdneg : B1 * A1 + B2 * A2 < 0 ↔ B2 * A2 < 0 := by
      constructor
      · grind
      · zuq
        have : B2 * A2 * ztniu < 0 := mul_neg_of_neg_of_pos h hS
        rw [← hdot] at this
        zuca
        exact absurd this (not_lt.2 (mul_nonneg hc hA2.le))
    rcases hσ with rfl | rfl <;>
    · constructor
      · zubjr
        · linarith
        · linarith
        · simp_all
        · refine Or.inr ztkix
          have hp := hdpos.1 h2
          rcases lt_or_gt_of_ne hB with hb' | hb' <;> rcases lt_or_gt_of_ne hA with ha' | ha' <;>
            first | (left; nlinarith) | (right; nlinarith)
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · linarith
        · rcases lt_or_gt_of_ne (show B2 * A2 ≠ 0 from hBA) with hn | hp
          · refine Or.inr (Or.inr (Or.inl ⟨by_linarith, hdneg.2 hn, ?_⟩))
            rcases lt_or_gt_of_ne hB with hb' | hb' <;> rcases lt_or_gt_of_ne hA with ha' | ha' <;>
              rcases h2 with h2 | h2 <;> first | linarith | nlinarith
          simp_all
  grind
variable {M : Model} {P : Polygon} {x : WPos} {σb : ℕ}
/-- **Inside a walk edge** the sector test is the turn from the edge. -/
theorem left_inside_iff
    (h0 : 0 < M.param zta x) (h1 : M.param zta x < 1) :
    LeftB M P x σb ↔ TurnNB M x σb := by
  unfold LeftB TurnNB
  have hne := SweepPrim.ne_of_param_pos h0
  rw [SweepPrim.pos_eq_sidePt, SweepPrim.sideLeft_interior h0 h1 hne]
  zuhax

/-- **At a walk vertex** whose neighbours are at other heights the sector test is decided by the
orientation of the corner and the two turns. -/
theorem left_vertex_iff
    (h0 : M.param zta x = 0)
    (hb : (M.W.vtx ztxyn).2 ≠ (M.W.vtx x.edge).2)
    (ha : (M.W.vtx ztdkc).2 ≠ (M.W.vtx x.edge).2) :
    LeftB M P x σb ↔
      (0 < sideCross ztbapc
          ztzcc ∧
        TurnNB M x σb ∧ TurnPB M x σb) ∨
      (¬ 0 < sideCross ztbapc
          ztzcc ∧
        (TurnNB M x σb ∨ TurnPB M x σb)) := by
  unfold LeftB TurnNB TurnPB
  rw [SweepPrim.pos_eq_sidePt, h0, sideLeft_zero, Chazelle.Chain.sidePt_zero]
  exact sector_horiz (dirOf_pm σb) hb ha
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim

/-- **A position the tests compare**: on the walk proper, not a box vertex of a chain model. -/
def PosG (M : Model) (Q : Polygon) (n : ℕ) (x : WPos) : Prop :=
  x.edge < M.W.n ∧ ProperPos M Q n x ∧ ∀ C : Chain, M = chainModel C → x.hgt = 0 → 6 ≤ x.edge

/-- The candidate position of a run started in `c₀`. -/
def xOf (c₀ : Config) : WPos := ztxt
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ : Config}

/-- The chain of a chain model of the run is simple. -/
theorem TGood.chain_simple (hE : TGood P W M N c₀) {C : Chain} (hM : M = chainModel C) :
    ∃ C' : Chain, C'.P.Simple ∧ M = chainModel C' := by
  rcases hE.hkind with ⟨H, C', -, -, -, hs, hM'⟩ | hI
  · grind
  · exact absurd ztmkt (chainModel_ne_interior C zta)

/-- **The candidate is a position the tests compare.** -/
theorem TGood.xPosG (hE : TGood P W M N c₀) : PosG M zta P.n ztfy := by
  refine ⟨hE.hxe, hE.hxp, fun C hM => ?_⟩
  have hy : |(M.pos zta ztfy).2| < C.radius :=
    lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set ztjxg).2 C.coordBound_lt_radius
  zulas
  exact (posOK_of hE.hxe hE.hxp hy).2.2

/-- **The ends of the chord records** are positions the tests compare. -/
theorem TGood.chordPosG (hE : TGood P W M N c₀) {i : ℕ} (hi : i < N.nChords) :
    PosG M zta P.n (N.chord i).lpos ∧ PosG M zta P.n (N.chord i).rpos := by
  have hp := chord_proper hE.hNF hi
  have hat := hE.hNF.2.2.1 i hi
  refine ⟨⟨hat.1.1, hp.1, fun C hM => ?_⟩, ⟨hat.2.1, hp.2, fun C hM => ?_⟩⟩ <;>
  · tauto

/-- **The ends of the arc records** of a nonempty family are positions the tests compare. -/
theorem TGood.arcPosG (hE : TGood P W M N c₀) (hne : (N.F M zta).Nonempty) {j : ℕ}
    (hj : j < N.arcs.length) :
    PosG M zta P.n (N.arc j).s ∧ PosG M zta P.n (N.arc j).e := by
  zusu
  obtain ⟨hFam, -, -, reg, -, -, harcs, -, -, -, hpp⟩ := hE.hNF
  zuls

  have hn := harc.2.1
  have hn' := harc.2.2.2.1
  have e1 : (N.arc j).s.edge < M.W.n := by
    have : ((N.arc j).s.edge : ℝ) < M.W.n := by
      have := hs.1; unfold Model.key at hn; linarith
    simp_all
  have e2 : (N.arc j).e.edge < M.W.n := by
    have : ((N.arc j).e.edge : ℝ) < M.W.n := by
      have := he.1; unfold Model.key at hn'; linarith
    simp_all
  refine ⟨⟨e1, by_simp_all, fun C hM => ?_⟩, ⟨e2, by_simp_all, fun C hM => ?_⟩⟩
  all_goals
    obtain ⟨C', hsC, hM'⟩ := hE.chain_simple hM
    zucly

    have := arc_posOK hsC hNF hne hj
    first | exact this.1.2.2 | exact this.2.2.2

/-- **Contract of a key comparison.** -/
def KeyOK (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (K : ℕ) : Prop :=
  ∀ a b d e, InR a → InR b → InR d → InR e →
  ∀ (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ c : Config), TGood P W M N c₀ →
    TInv W c₀ c → PosG M zta P.n ztel →
    PosG M zta P.n ztge → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W ztjzj c c' k ∧ k ≤ K ∧
      BitIs c' 50210 ztxkf ∧
      BitIs c' 50211 ztypi ∧
      TStep W c₀ c c' k

/-- **Contract of the sector test** at the candidate. -/
def LeftOK (ls : Stmt) (K : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ c : Config), TGood P W M N c₀ →
    TInv W c₀ c → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W ls c c' k ∧ k ≤ K ∧
      BitIs c' 50210 ztxgd ∧ TStep W c₀ c c' k

/-- **Contract of the turning tests** at the candidate vertex. -/
def TurnOK (tn tp : Stmt) (K : ℕ) : Prop :=
  (∀ (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ c : Config), TGood P W M N c₀ →
    TInv W c₀ c → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W tn c c' k ∧ k ≤ K ∧
      (c'.nreg 50210 = 1 ↔ TurnNB M ztfy ztbkn) ∧ TStep W c₀ c c' k) ∧
  (∀ (P : Polygon) (W : ℕ) (M : Model) (N : NF) (c₀ c : Config), TGood P W M N c₀ →
    TInv W c₀ c → c₀.nreg 83006 = 0 → c.nreg ALLOC + K ≤ W →
    ∃ c' k, Exec P W tp c c' k ∧ k ≤ K ∧
      (c'.nreg 50210 = 1 ↔ TurnPB M ztfy ztbkn) ∧ TStep W c₀ c c' k)
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The copies of the sector test. -/
def lsL : List ztw := [ztgzg, ztnhh, ztnhj, ztstn]

/-- **The sector test at the candidate** (chain model). -/
def tLeft : Stmt := .seq (block (copies lsL)) leftSec
theorem tLeft_exec (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {C : Chain}
    (hM : M = chainModel C) (hroom : c.nreg ALLOC + 17400 ≤ W) :
    ∃ c' k, Exec P W tLeft c c' k ∧ k ≤ 17404 ∧
      BitIs c' 50210 ztxgd ∧ TStep W c₀ c c' k := by
  zuqq
  zucwv
  zuess
  zuest
  have hxe : c₀.nreg 83005 < (chainModel C').W.n := by zuosx; exact hE.hxe
  have hxp : ProperPos ztbmo zta P.n ztxt := by
    zuosx; exact hE.hxp
  have hy : |((chainModel C').pos zta ⟨c₀.nreg 83005, c₀.nreg 83006⟩).2| < C'.radius := by
    have hx := hE.hxC C' hM'
    rw [hM'] at hx
    exact lt_of_le_of_lt (C'.abs_le_coordBound_of_mem_set hx).2 C'.coordBound_lt_radius
  obtain ⟨c₁, c', k, h1, -, -, ex, hk, hout, hf⟩ := callPrim leftSec_meets lsL
    by_decide
    by_decide by_decide (src := 83020) by_decide hI.hw hE.hG hE.hW
    hwf hC (fun c₁ h1 _ _ => by
      zufhq

      zuhqe
      refine ztram
      grind) hroom
  zufhq

  have q3 := h1 ztstn by_decide
  zulan
  refine ⟨c', k, ex, by_tauto, ?_, hI.prim ex.wb_right hf⟩
  have := hout
  unfold LeftOut at this
  rw [q1, q2, q3, i5, i6, i8] at this
  rw [hM']
  tauto
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The registers the turning tests write: those of `locDir`, `50000`, `50002`, `50203`,
`50210`. -/
def Bturn (r : ℕ) : Bool := Bdir r || r == 50000 || r == 50002 || r == 50203 || r == 50210
theorem Bturn_band (r : ℕ) (h : Bturn r = true) : bandOf r ∈ primBands ∧ r ≠ ALLOC := by
  unfold Bturn at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · have := Bdir_band r h
    zubye

  all_goals
    subst h
    exact ztkp

/-- The tail of a turning test: `50210 := turnCode (10502) σ`. -/
def turnTail : Stmt := .seq (block [.copyN 50203 83008, .constN 50032 1]) turnOut

/-- **The turn after the candidate vertex.** -/
def tTurnN : Stmt :=
  .seq ztkse (.seq locDir turnTail)

/-- **The turn before the candidate vertex** (the previous edge is `p - 1`, or `n - 1` for
`p = 0`, which only happens in the interior model, where `n` is the input size). -/
def tTurnP : Stmt :=
  .seq (.seq ztceu
    (.ifLtN 83005 83023 ztdcb
      ztejt)) (.seq locDir turnTail)
theorem wr_tTurnN : wr Bturn tTurnN = true := by_decide
theorem wr_tTurnP : wr Bturn tTurnP = true := by_decide

/-- The direction procedure's precondition in a run. -/
theorem locDPre_of (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {c₁ : Config}
    (h00 : c₁.nreg 50000 = c.nreg 83000) (hm : c₁.nmem = c.nmem)
    (_hA : c₁.nreg ALLOC = c.nreg ALLOC) (he : c₁.nreg 50002 < M.W.n) :
    LocDPre P W c₁ := by
  zubxo
  zuki
  obtain ⟨h6, hloc⟩ := locChainWF_of hwf hAW hE.hW
  refine ⟨hE.hG, by have := hE.hW; unfold hostWords at this; omega, by_omega,
    by simp_all, M, by_simp_all, he⟩

/-- The turn code is `1` iff the turn is positive. -/
theorem sgnCode_eq_one {x : ℝ} : sgnCode x = 1 ↔ 0 < x := by
  unfold sgnCode; grind

/-- **The turning tests meet their contract.** -/
theorem turn_ok : TurnOK tTurnN tTurnP 5200 := by
  refine ⟨fun P W M N c₀ c hE hI hroom => ?_, fun P W M N c₀ c hE hI hv hroom => ?_⟩
  · zubod
    obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W
        ztkse c c₁ k₁ ∧ k₁ = 2 ∧
        (c₁.nreg 50000 = c.nreg 83000 ∧ c₁.nreg 50002 = c.nreg 83005 ∧ c₁.nmem = c.nmem ∧
          c₁.nreg ALLOC = c.nreg ALLOC ∧ c₁.nreg 83008 = c.nreg 83008) := by
      exec_block
      tauto
    zuejg
    zucwv
    zuest
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, d₂⟩ := locDir_ok P W c₁ e₁.wb_right
      (locDPre_of hE hI q00 qm qA (by rw [q02, i5]; exact hE.hxe))
    have hMD : ztzow := by
      zuezc
    zukbp
    rw [q02, i5] at hd
    zue
    obtain ⟨c₃, k₃, e₃, hk₃, q3⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50203 83008,
        .constN 50032 1]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 50203 = c₂.nreg 83008 ∧
        c₃.nreg 50032 = 1 ∧ c₃.nreg 10502 = c₂.nreg 10502) := by
      exec_block
      · omega
      simp
    zugqp
    obtain ⟨c₄, k₄, e₄, hk₄, o₄, -⟩ := turnOut_exec (P := P) c₃ e₃.wb_right by_omega q3b
      ztirv
    have ex : Exec P W tTurnN c c₄ ztwwh := .seq e₁ ztcb
    have hfr : ztukt := exec_frameB ex wr_tTurnN
    refine ztfzg
    have e08 : ztshd := by
      zugug
    rw [o₄, q3c, q3a, hd, e08, ← sgnCode_turnNext, sgnCode_eq_one]
    rfl
  · zubod
    zucwv
    zuest
    zueqd
    have hxe := hE.hxe
    have hn : ∀ C : Chain, M = chainModel C → 6 ≤ c₀.nreg 83005 := fun C hM =>
      hE.xPosG.2.2 C hM hv
    -- the previous edge
    zugys
    have hpe : ∃ pe, pe = (c₀.nreg 83005 + n - 1) % n ∧ pe < n ∧
        (c₀.nreg 83005 = 0 → pe = P.n - 1) ∧ (0 < c₀.nreg 83005 → pe = c₀.nreg 83005 - 1) := by
      refine ⟨_, rfl, Nat.mod_lt _ by_omega, fun h0 => ?_, fun h0 => ?_⟩
      · rcases hE.hkind with ⟨H, C, -, -, -, -, hM⟩ | hI'
        · grind
        · have : n = P.n := by
            simp only [n, hI', interiorModel, NFLoc.interiorWalk_n]; exact shear_n _ _
          simp_all
      · rw [show c₀.nreg 83005 + n - 1 = (c₀.nreg 83005 - 1) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt by_omega]
    obtain ⟨pe, hpe, hpen, hp0, hp1⟩ := hpe
    obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W
        (.seq ztceu
          (.ifLtN 83005 83023 ztdcb
            ztejt)) c c₁ k₁ ∧ k₁ ≤ 6 ∧
        (c₁.nreg 50000 = c.nreg 83000 ∧ c₁.nreg 50002 = pe ∧ c₁.nmem = c.nmem ∧
          c₁.nreg ALLOC = c.nreg ALLOC ∧ c₁.nreg 83008 = c.nreg 83008) := by
      zujl
      obtain ⟨c', k', e', hk', q'⟩ : ∃ c' k', Exec P W (block [.copyN 50000 83000,
          .constN 50032 1]) c c' k' ∧ k' = 2 ∧ (c'.nreg 50000 = c.nreg 83000 ∧
          c'.nreg 50032 = 1 ∧ c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
          c'.nreg 83008 = c.nreg 83008 ∧ c'.nreg 83005 = c.nreg 83005 ∧
          c'.nreg 83023 = c.nreg 83023) := by
        exec_block
        · omega
        trivial
      obtain ⟨p00, p32, pm, pA, p08, p05, p23⟩ := q'
      zueki

      · zujfh
        exec_block
        · have := hE.hW; unfold hostWords at this; omega
        · refine ⟨by_omega, by_tauto, ?_, pm, by_tauto,
            by tauto⟩
          config_simp
          omega
      · zumjn
        refine ⟨by_omega, by_tauto, ?_, pm, by_tauto,
          by tauto⟩
        config_simp
        omega
    zuejg
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, d₂⟩ := locDir_ok P W c₁ e₁.wb_right
      (locDPre_of hE hI q00 qm qA by_omega)
    have hMD : ztzow := by
      zuezc
    zukbp
    rw [q02] at hd
    zue
    zujuq
    obtain ⟨c₃, k₃, e₃, hk₃, q3⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 50203 83008,
        .constN 50032 1]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 50203 = c₂.nreg 83008 ∧
        c₃.nreg 50032 = 1 ∧ c₃.nreg 10502 = c₂.nreg 10502) := by
      exec_block
      · omega
      simp
    zugqp
    obtain ⟨c₄, k₄, e₄, hk₄, o₄, -⟩ := turnOut_exec (P := P) c₃ e₃.wb_right by_omega q3b
      ztirv
    have ex : Exec P W tTurnP c c₄ ztwwh := .seq e₁ ztcb
    have hfr : ztukt := exec_frameB ex wr_tTurnP
    refine ztfzg
    have e08 : ztshd := by
      zugug
    rw [o₄, q3c, q3a, hd, e08, hpe, ← sgnCode_turnPrev M hxe, sgnCode_eq_one]
    rfl
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim

/-- **A run step**: `s` runs from `c` in at most `K` steps to a configuration of the run
satisfying `Q`. -/
def RS (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ TInv W c₀ c' ∧ RF dBands ztdq c c' k ∧ Q c'
theorem bit01 {c : Config} {r : ℕ} {p : Prop} (h : BitIs c r p) :
    (c.nreg r = 0 ∧ ¬ p) ∨ (c.nreg r = 1 ∧ p) := by
  zubkx
  grind
variable {f : ℕ → ℕ} {s : Stmt} {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
theorem upd_eq {r v : ℕ} : upd f r v r = v := by_simp
theorem upd_ne {r v q : ℕ} (h : q ≠ r) : upd f r v q = f q := by_simp_all
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem RS.mono {K K' : ℕ} {Q Q' : Config → Prop} (h : RS P W c₀ s c K Q)
    (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : RS P W c₀ s c K' Q' := by
  zuw
  exact zthmo
theorem RS.seq {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop} (h₁ : RS P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, TInv W c₀ c₁ → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ → Q₁ c₁ →
      RS P W c₀ t c₁ K₂ Q₂) : RS P W c₀ (.seq s t) c (K₁ + K₂) Q₂ := by
  zudf
theorem RS.ifT
    (ht : c.nreg a < c.nreg b) (h : RS P W c₀ t c K Q) : RS P W c₀ ztva c ztnu Q := by
  zuw
  exact ztcou
theorem RS.ifF
    (ht : ¬ c.nreg a < c.nreg b) (h : RS P W c₀ e c K Q) :
    RS P W c₀ ztva c ztnu Q := by
  zuw
  exact ztcov
theorem RS.skip (hI : TInv W c₀ c) (hq : Q c) :
    RS P W c₀ .skip c K Q :=
  ⟨c, 0, .skip hI.hw, by_omega, hI, RF.refl c 0, hq⟩

/-- **A step of a model operation.** -/
theorem RS.op
    (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ Q c' ∧ TStep W c₀ c c' k) :
    RS P W c₀ s c K (fun c' => Q c' ∧ ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c.nreg q) := by
  obtain ⟨c', k, ex, hk, hq, hI, hrf, h8⟩ := h
  exact ⟨c', k, ex, hk, hI, hrf, hq, h8⟩

/-- A scratch or output register of the test (band `bRestore` from `83010` on, off the constants
`83020 … 83023`). -/
def Scr (r : ℕ) : Prop := 83010 ≤ r ∧ r < 90000 ∧ (r < 83020 ∨ 83024 ≤ r)

/-- **One register instruction** on a scratch register. -/
theorem RS.reg {i : Instr} {r v : ℕ} (hI : TInv W c₀ c) (hr : Scr r)
    (hex : Exec P W ztbgj c { c with nreg := upd c.nreg r v } 1) :
    RS P W c₀ ztbgj c 1 ztlny := by
  unfold Scr at hr
  obtain ⟨hI', hrf⟩ := hI.regs (c' := { c with nreg := upd c.nreg r v }) (k := 1) hex.wb_right
    (fun q hq => by zvmwf; grind) rfl rfl rfl rfl
  exact ztinj
theorem RS.const (hI : TInv W c₀ c) {r v : ℕ} (hr : Scr r) (hv : v ≤ W) :
    RS P W c₀ ztcyq c 1 ztlny :=
  RS.reg hI hr ztjik
theorem RS.copy (hI : TInv W c₀ c) {r a : ℕ} (hr : Scr r) :
    RS P W c₀ ztdsf c 1 (fun c' => c'.nreg = upd c.nreg r ztcux) :=
  RS.reg hI hr zthqx
theorem RS.add (hI : TInv W c₀ c) {r a b : ℕ} (hr : Scr r) (hab : c.nreg a + c.nreg b ≤ W) :
    RS P W c₀ ztder c 1 (fun c' => c'.nreg = upd c.nreg r ztqio) :=
  RS.reg hI hr (Exec.addN hI.hw r a b hab)

/-- **A loop**: an invariant `I` and a measure `μ`; each iteration costs at most `Kb` and lowers
`μ`.  The allocator must leave room for all iterations. -/
theorem RS.while {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ)
    (hpos : ∀ c, I c → c.nreg a < c.nreg b → 0 < μ c)
    (hbody : ∀ c, TInv W c₀ c → I c → c.nreg a < c.nreg b → c.nreg ALLOC + Kb ≤ W →
      RS P W c₀ body c Kb ztesi)
    (hI : TInv W c₀ c) (hc : I c) (hroom : c.nreg ALLOC + ztkq * μ c ≤ W) :
    RS P W c₀ ztpx c ztxrk
      ztcpy := by
  induction hn : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · have hμ : ztphw := hpos c hc ht
      obtain ⟨c₁, k₁, e₁, hk₁, hI₁, hrf₁, hc₁, hμ₁⟩ := hbody c hI hc ht (by
        zuhdn
        omega)
      zumbn
      have hroom₁ : ztxiw := by
        zudxq

      zucbf
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht e₁ e₂, ?_, hI',
        (hrf₁.trans hrf₂).mono subset_rfl by_omega, hq⟩
      zucfy

    · exact ztfwc
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK WalkKey

/-! ## Mathematics -/

/-- **The lexicographic order of keys** of proper positions. -/
theorem key_lt_lex {M : Model} {Q : Polygon} {n : ℕ} {x y : WPos} (hx : ProperPos M Q n x)
    (hy : ProperPos M Q n y) :
    M.key Q x < M.key Q y ↔ x.edge < y.edge ∨ ztkhe := by
  zuhqn
  zugpv
  obtain ⟨hy0, hy1, -⟩ := hy
  constructor
  · zuq
    rcases lt_trichotomy x.edge y.edge with h' | h' | h'
    · omega
    · simp_all
    · exfalso
      have : ztddy := by exact_mod_cast h'
      linarith
  · zuczb
    · zuepg
      linarith
    simp_all

/-- The index in `Q` of vertex `e` of the interior walk, for the orientation bit `bit`. -/
def iIdx (bit n e : ℕ) : ℕ := if bit = 1 then e else n - 1 - e

/-- The index of the vertex of `Q` at the height of a position of the interior walk. -/
def hIdx (bit n : ℕ) (x : WPos) : ℕ := if x.hgt = 0 then iIdx bit n x.edge else x.hgt - 1
variable {P : Polygon}
variable {bit : ℕ} {a b : ℝ} {c : Config}
theorem interior_wa (hbit : bit = 1 ↔ Mountain.LeftInside zta) {e : ℕ}
    (he : e < P.n) :
    (interiorModel zta).wa e = (Qof P).vtx (iIdx bit P.n e) := by
  zubp
  zujpz
  zunwq
  rw [interiorWalk_vtx _ by_omega, hn]
  unfold iIdx
  grind
theorem interior_hgtY (hbit : bit = 1 ↔ Mountain.LeftInside zta) {x : WPos}
    (he : x.edge < P.n) :
    (interiorModel zta).hgtY zta x = ((Qof P).vtx (hIdx bit P.n x)).2 := by
  rcases x with ⟨e, _ | h⟩
  · simp only [Model.hgtY, hIdx]
    rw [interior_wa hbit he]
    simp
  rfl
theorem iIdx_lt {bit n e : ℕ} (he : e < n) : iIdx bit n e < n := by
  zumsv
theorem hIdx_lt {bit n : ℕ} {x : WPos} (he : x.edge < n) (hh : x.hgt ≤ n) : hIdx bit n x < n := by
  unfold hIdx; split_ifs with h
  · exact iIdx_lt he
  · omega
theorem interior_wb (hbit : bit = 1 ↔ Mountain.LeftInside zta) {e : ℕ}
    (he : e < P.n) :
    (interiorModel zta).wb e = (Qof P).vtx (iIdx bit P.n ztwmy) := by
  zubp
  have hW : (interiorModel zta).W.n = P.n := by
    zunwq; rw [interiorWalk_n, hn]
  zumrf
  zugus
  have := interior_wa hbit (e := ztda % P.n) ztcv
  tauto
theorem dirOf_one : NFLoc.dirOf a b = 1 ↔ a < b := by
  zujqd
theorem dirOf_two : NFLoc.dirOf a b = 2 ↔ b < a := by
  zujqd
theorem dirOf_le (a b : ℝ) : NFLoc.dirOf a b ≤ 2 := by
  zujqd

/-! ## The machine -/

/-- Set a bit register. -/
def setB (r : ℕ) : Stmt := .instr ztnaa

/-- The height index: `dst := 50121` (the start vertex of the edge) for the code `0`, else
`code - 1`. -/
def hSel (src dst : ℕ) : Stmt :=
  .ifLtN src 50032 (.instr (.copyN dst 50121)) (.instr (.subN dst src 50032))

/-- The bits from the direction code `50120` and the height comparison `10502`. -/
def iDecide : Stmt :=
  .ifLtN 50120 50032 .skip
    (.ifLtN 50032 50120
      (.ifLtN 10502 50032 .skip (.ifLtN 50032 10502 ztiaq ztqwb))
      (.ifLtN 10502 50032 .skip (.ifLtN 50032 10502 ztqwb ztiaq)))

/-- The start of the comparison on one edge: its direction code into `50120`, the index of its
start vertex into `50121`. -/
def iEdge (a : ℕ) : Stmt :=
  .seq ztksf (.seq intIdx
    (.seq zthtg (.seq dirTail
      ztksh)))

/-- The comparison of two positions on one edge. -/
def iSame (a b _d e : ℕ) : Stmt :=
  .seq ztqrf (.seq (hSel b 50122) (.seq (hSel e 50123)
    (.seq ztfxw
      (.seq dirTail (.seq ztfeq iDecide)))))

/-- **The key comparison of the interior model.** -/
def iKey (a b d e : ℕ) : Stmt :=
  .seq ztkrh
    (.ifLtN a d ztiaq (.ifLtN d a ztqwb ztqrg))

/-- The registers `iKey` writes. -/
def Bik (r : ℕ) : Bool :=
  Bdir r || r == 50000 || r == 50002 || (50120 ≤ r && r < 50124) || r == 50210 || r == 50211
theorem wr_intIdx : wr Bdir intIdx = true := by_decide
theorem wr_iKey (a b d e : ℕ) : wr Bik ztjyp = true := by
  rfl
variable {W : ℕ}
theorem iEdge_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {a bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside zta)
    (hmd : c.nmem ztcms = bit) (hD : c.nreg 83000 + 1 ≤ W) (ha : c.nreg a < P.n)
    (ha8 : 80000 ≤ a ∧ a < 90000) :
    ∃ c' k, Exec P W ztqrf c c' k ∧ k ≤ 1100 ∧
      c'.nreg 50120 = dirCode ztwiq ztcux ∧
      c'.nreg 50121 = iIdx bit P.n ztcux ∧ c'.nreg 50032 = 1 := by
  obtain ⟨c₁, k₁, e₁, hk₁, q01, q02, hm₁⟩ : ∃ c₁ k₁, Exec P W
      ztksf c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 50000 = c.nreg 83000 ∧ c₁.nreg 50002 = c.nreg a ∧ c₁.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, by config_simp, ?_, rfl⟩
    config_simp
    rw [upd_ne by_omega]
  obtain ⟨c₂, k₂, e₂, hk₂, r41, r44⟩ := intIdx_exec (P := P) hW c₁ e₁.wb_right
    by_omega by_omega
  rw [q01, q02, hm₁, hmd] at r41 r44
  obtain ⟨c₃, k₃, e₃, hk₃, s40, s41, s43, s44, s121⟩ : ∃ c₃ k₃, Exec P W
      zthtg c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 50040 = 0 ∧ c₃.nreg 50041 = c₂.nreg 50041 ∧ c₃.nreg 50043 = 0 ∧
      c₃.nreg 50044 = c₂.nreg 50044 ∧ c₃.nreg 50121 = c₂.nreg 50041 := by
    zue
    exec_block
    · omega
    · omega
    simp
  zuiz
  have hia : iIdx bit P.n _ < P.n := iIdx_lt ha
  have hib : iIdx bit P.n ztbaar < P.n := iIdx_lt zthp
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, d₄⟩ := dirTail_exec (P := P) hG hW c₃ e₃.wb_right
    (sa := .vtx (iIdx bit P.n ztcux)) (sb := .vtx (iIdx bit P.n ztbaar))
    hia hib ⟨s40, by rw [s41, r41]; rfl⟩ ⟨s43, by rw [s44, r44]; rfl⟩
  have g121 := f₄.1 50121 by_decide
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, t32⟩ : ∃ c₅ k₅, Exec P W
      ztksh c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg 50120 = c₄.nreg 10502 ∧ c₅.nreg 50121 = c₄.nreg 50121 ∧ c₅.nreg 50032 = 1 := by
    zucc
    exec_block
    · omega
    simp
  refine ⟨c₅, _, .seq e₁ ztbq, by_omega, ?_, ?_, t32⟩
  · rw [t120, d₄, dirCode_eq]
    simp only [SymPt.eval]
    rw [interior_wa hbit ha, interior_wb hbit ha]
  · rw [t121, g121, s121, r41]; rfl

/-- The decision on the direction code `dv` and the height comparison `cv`. -/
theorem iDecide_exec (hw : WordsBounded W c) (hW : 1 ≤ W)
    (h32 : c.nreg 50032 = 1) (h10 : c.nreg 50210 = 0) (h11 : c.nreg 50211 = 0)
    (hd : c.nreg 50120 ≤ 2) (hc : c.nreg 10502 ≤ 2) :
    ∃ c' k, Exec P W iDecide c c' k ∧ k ≤ 9 ∧ c'.nreg 50210 ≤ 1 ∧ c'.nreg 50211 ≤ 1 ∧
      (c'.nreg 50210 = 1 ↔ (c.nreg 50120 = 1 ∧ c.nreg 10502 = 1) ∨
        (c.nreg 50120 = 2 ∧ c.nreg 10502 = 2)) ∧
      (c'.nreg 50211 = 1 ↔ (c.nreg 50120 = 1 ∧ c.nreg 10502 = 2) ∨
        (c.nreg 50120 = 2 ∧ c.nreg 10502 = 1)) := by
  unfold iDecide setB
  rcases (show c.nreg 50120 = 0 ∨ c.nreg 50120 = 1 ∨ c.nreg 50120 = 2 by omega) with d | d | d <;>
  rcases (show c.nreg 10502 = 0 ∨ c.nreg 10502 = 1 ∨ c.nreg 10502 = 2 by omega) with v | v | v
  all_goals
    repeat (first
      | (refine spec_ifLtN_true by_omega ?_)
      | (refine spec_ifLtN_false by_omega ?_))
  all_goals first
    | exact spec_skip hw by_omega
    | exact spec_instr (Exec.constN hw _ _ hW) by_simp_all

/-- The registers `iEdge` writes. -/
def BiE (r : ℕ) : Bool := Bdir r || r == 50000 || r == 50002 || r == 50120 || r == 50121
theorem wr_iEdge (a : ℕ) : wr BiE ztqrf = true := by
  rfl

/-- The height index selection. -/
theorem hSel_exec (hw : WordsBounded W c) {src dst : ℕ} (h32 : c.nreg 50032 = 1)
    (_hdst : dst ≠ src) :
    ∃ c' k, Exec P W (hSel src dst) c c' k ∧ k ≤ 3 ∧
      c'.nreg dst = (if c.nreg src = 0 then c.nreg 50121 else c.nreg src - 1) ∧
      ∀ r, r ≠ dst → c'.nreg r = c.nreg r := by
  unfold hSel
  by_cases h : c.nreg src < c.nreg 50032
  · refine spec_ifLtN_true h (spec_instr ztbim fun _ => ztss)
    · simp_all
    simp_all
  · refine spec_ifLtN_false h (spec_instr ztbbq fun _ => ztss)
    · simp_all
    simp_all

/-- **The comparison on one edge** (interior model). -/
theorem iSame_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {a b d e bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside zta)
    (hmd : c.nmem ztcms = bit) (hD : c.nreg 83000 + 1 ≤ W)
    (h8 : ∀ r ∈ [a, b, d, e], 80000 ≤ r ∧ r < 90000)
    (h10 : c.nreg 50210 = 0) (h11 : c.nreg 50211 = 0) (hsame : c.nreg a = c.nreg d)
    (hx : ProperPos ztwiq zta P.n ztel)
    (hy : ProperPos ztwiq zta P.n ztge)
    (hxe : c.nreg a < P.n) :
    ∃ c' k, Exec P W ztqrg c c' k ∧ k ≤ 2200 ∧
      BitIs c' 50210 ((interiorModel zta).key zta ztel <
        (interiorModel zta).key zta ztge) ∧
      BitIs c' 50211 ((interiorModel zta).key zta ztge <
        (interiorModel zta).key zta ztel) := by
  set M := interiorModel zta
  zufgj

  zukbv
  obtain ⟨c₁, k₁, e₁, hk₁, d120, d121, d32⟩ := iEdge_exec hG hW hw hbit hmd hD hxe ha8
  have f₁ : FrameB BiE c c₁ := exec_frameB e₁ (rfl)
  have g₁ : zthpl := fun r h1 h2 =>
    f₁.1 r (by simp [BiE, Bdir]; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, v122, o₂⟩ := hSel_exec (P := P) e₁.wb_right (src := b) (dst := 50122)
    d32 by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, v123, o₃⟩ := hSel_exec (P := P) e₂.wb_right (src := e) (dst := 50123)
    by_simp_all by_omega
  -- the height indices
  have hIx : c₃.nreg 50122 = hIdx bit P.n ztel := by
    rw [o₃ _ by_decide, v122, g₁ b hb8.1 hb8.2, d121]
    rfl
  have hIy : c₃.nreg 50123 = hIdx bit P.n ztge := by
    rw [v123, o₂ _ by_omega, g₁ e he8.1 he8.2, o₂ _ by_decide, d121, ← hsame]
    rfl
  obtain ⟨c₄, k₄, e₄, hk₄, s40, s41, s43, s44, r₄⟩ : ∃ c₄ k₄, Exec P W
      ztfxw c₃ c₄ k₄ ∧
      k₄ = 4 ∧ c₄.nreg 50040 = 0 ∧ c₄.nreg 50041 = c₃.nreg 50122 ∧ c₄.nreg 50043 = 0 ∧
      c₄.nreg 50044 = c₃.nreg 50123 ∧
      ∀ r, r ≠ 50040 → r ≠ 50041 → r ≠ 50043 → r ≠ 50044 → c₄.nreg r = c₃.nreg r := by
    zubj
    exec_block
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, ?_⟩
      zufxp
      simp [upd, h1, h2, h3, h4]
  have hn := hxe
  have hhx : hIdx bit P.n ztel < P.n := hIdx_lt hxe hx.2.2
  have hhy : hIdx bit P.n ztge < P.n := hIdx_lt by_grind hy.2.2
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, d₅⟩ := dirTail_exec (P := P) hG hW c₄ e₄.wb_right
    (sa := .vtx ztzme)
    (sb := .vtx ztzmf) hhx hhy
    ⟨s40, by_grind⟩ ⟨s43, by_grind⟩
  zuef
  zuepw
  zueei
  have p120 : c₆.nreg 50120 = dirCode M ztcux := by
    show upd c₅.nreg 50032 1 50120 = _
    rw [upd_ne by_decide, f₅.1 50120 by_decide, r₄ _ by_decide by_decide by_decide
      by_decide, o₃ _ by_decide, o₂ _ by_decide, d120]
  have p10 : c₆.nreg 50210 = 0 := by
    show upd c₅.nreg 50032 1 50210 = _
    rw [upd_ne by_decide, f₅.1 50210 by_decide, r₄ _ by_decide by_decide by_decide
      by_decide, o₃ _ by_decide, o₂ _ by_decide, f₁.1 50210 by_decide, h10]
  have p11 : c₆.nreg 50211 = 0 := by
    show upd c₅.nreg 50032 1 50211 = _
    rw [upd_ne by_decide, f₅.1 50211 by_decide, r₄ _ by_decide by_decide by_decide
      by_decide, o₃ _ by_decide, o₂ _ by_decide, f₁.1 50211 by_decide, h11]
  have p02 : c₆.nreg 10502 = NFLoc.dirOf ((Qof P).vtx ztzme).2
      ((Qof P).vtx ztzmf).2 := by
    show upd c₅.nreg 50032 1 10502 = _
    rw [upd_ne by_decide, d₅]; rfl
  obtain ⟨c₇, k₇, e₇, hk₇, b1, b2, i1, i2⟩ := iDecide_exec (P := P) e₆.wb_right by_omega
    by_rfl p10 p11
    (by rw [p120]; exact dirCode_le_two _ _) (by rw [p02]; exact dirOf_le _ _)
  refine ⟨c₇, k₁ + ztcnu,
    .seq e₁ ztfc, by_omega, ztufx, ⟨b2, ?_⟩⟩
  · rw [i1, p120, p02, dirOf_one, dirOf_two, key_lt_lex hx hy]
    have hbase := param_lt_iff_same_edge M zta (x := ztel)
      (y := ztge) hsame
    rw [interior_hgtY hbit hxe, interior_hgtY hbit by_grind] at hbase
    grind
  · rw [i2, p120, p02, dirOf_one, dirOf_two, key_lt_lex hy hx]
    have hbase := param_lt_iff_same_edge M zta (x := ztge)
      (y := ztel) hsame.symm
    rw [interior_hgtY hbit by_grind, interior_hgtY hbit hxe] at hbase
    grind

/-- **The key comparison of the interior model.** -/
theorem iKey_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {a b d e bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside zta)
    (hmd : c.nmem ztcms = bit) (hD : c.nreg 83000 + 1 ≤ W)
    (h8 : ∀ r ∈ [a, b, d, e], 80000 ≤ r ∧ r < 90000)
    (hx : ProperPos ztwiq zta P.n ztel)
    (hy : ProperPos ztwiq zta P.n ztge)
    (hxe : c.nreg a < P.n) (_hye : c.nreg d < P.n) :
    ∃ c' k, Exec P W ztjyp c c' k ∧ k ≤ 2210 ∧
      BitIs c' 50210 ((interiorModel zta).key zta ztel <
        (interiorModel zta).key zta ztge) ∧
      BitIs c' 50211 ((interiorModel zta).key zta ztge <
        (interiorModel zta).key zta ztel) := by
  zufgj

  have hd8 := h8 d by_simp
  zukbv
  obtain ⟨c₁, k₁, e₁, hk₁, q10, q11, g₁, hm₁⟩ : ∃ c₁ k₁, Exec P W
      ztkrh c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 50210 = 0 ∧
      c₁.nreg 50211 = 0 ∧ ztgse ∧
      c₁.nmem = c.nmem := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => ?_, rfl⟩
      simp [upd, show r ≠ 50210 by omega, show r ≠ 50211 by omega]
  zud
  have ea := (g₁ a ha8.1 ha8.2).symm
  have eb := (g₁ b hb8.1 hb8.2).symm
  have ed := (g₁ d hd8.1 hd8.2).symm
  have ee := (g₁ e he8.1 he8.2).symm
  simp only [ea, eb, ed, ee] at hx hy hxe _hye ⊢
  have hmd' : c₁.nmem ztroc = bit := by
    simp_all
  have hD' : c₁.nreg 83000 + 1 ≤ W := by_simp_all
  unfold iKey
  zugar
  by_cases t1 : c₁.nreg a < c₁.nreg d
  · refine spec_ifLtN_true t1 (spec_instr ztcta fun _ =>
      ⟨by_omega, ⟨by_simp, ?_⟩, ⟨by_simp_all, ?_⟩⟩)
    · zufcc
      exact (key_lt_lex hx hy).2 (Or.inl t1)
    · simp only [upd_ne (show (50211 : ℕ) ≠ 50210 by decide), q11]
      constructor
      · simp
      · zuq
        rcases (key_lt_lex hy hx).1 h with h' | ⟨h', -⟩ <;> simp only at h' <;> omega
  · by_cases t2 : c₁.nreg d < c₁.nreg a
    · refine spec_ifLtN_false t1 (spec_ifLtN_true t2 (spec_instr ztcta
        fun _ => ⟨by_omega, ztbjy, zthml⟩))
      · simp only [upd_ne (show (50210 : ℕ) ≠ 50211 by decide), q10]
        constructor
        · simp
        · zuq
          rcases (key_lt_lex hx hy).1 h with h' | ⟨h', -⟩ <;> simp only at h' <;> omega
      · zufcc
        exact (key_lt_lex hy hx).2 ztvcd
    · have hsame : c₁.nreg a = c₁.nreg d := by_omega
      refine spec_ifLtN_false t1 (spec_ifLtN_false t2 ?_)
      obtain ⟨c', k, ex, hk, b1, b2⟩ := iSame_exec hG hW w₁ hbit hmd' hD' h8 q10 q11
        hsame hx hy hxe
      grind
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- **The model kind of a run**: a chain model with header `0`, or the interior model with header
`1` and its orientation bit. -/
theorem TGood.kind (hE : TGood P W M N c₀) :
    (c₀.nmem ztchn = 0 ∧ ∃ C : Chain, M = chainModel C) ∨
    (c₀.nmem ztchn = 1 ∧ M = interiorModel zta ∧
      (c₀.nmem ztbvw = 1 ↔ Mountain.LeftInside zta)) := by
  rcases hE.hMD with ⟨h0, H, C, -, hM⟩ | ⟨h1, hbit, hM⟩
  · simp_all
  simp_all

/-- The walk of the interior model has `n` vertices. -/
theorem interior_n : (interiorModel zta).W.n = P.n := by
  zunwq; zuouj; exact shear_n _ _
theorem Bik_band (r : ℕ) (h : Bik r = true) : bandOf r ∈ primBands ∧ r ≠ ALLOC := by
  unfold Bik at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · have := Bdir_band r h
    zubye

  all_goals first
    | (subst h; exact ⟨by_decide, by_decide⟩)
    | exact ⟨by simp only [primBands, bandOf, bLocate, bSign, Finset.mem_insert,
        Finset.mem_singleton]; omega, by unfold ALLOC; omega⟩

/-- **The key comparison of both models.** -/
def gKey (a b d e : ℕ) : Stmt := .ifLtN 83021 83023 ztjzm ztjyp
theorem gKey_ok : KeyOK gKey 11010 := by
  intro a b d e ha hb hd he P W M N c₀ c hE hI hx hy hroom
  zuivj
  zueqd
  zuizz
  unfold InR at ha hb hd he
  zubbz
  · -- a chain model
    zuqq
    have hx' : PosOK C' zta P.n ztel := by
      subst hM'; exact ⟨hx.1, hx.2.1, hx.2.2 C' rfl⟩
    have hy' : PosOK C' zta P.n ztge := by
      subst hM'; exact ⟨hy.1, hy.2.1, hy.2.2 C' rfl⟩
    obtain ⟨c', k, ex, hk, b1, b2, hf⟩ := keyCmp_exec by_tauto by_tauto
      by_tauto by_tauto hI.hw hE.hG hE.hW hwf hC hI.h22 hx' hy'
      (hE.hWm C' hM') by_omega
    obtain ⟨hI', hrf, h8⟩ := hI.prim ex.wb_right hf
    refine ⟨c', k + 1, .ifLtN_true by_omega ex, by_omega, ?_, ?_,
      hI', hrf.mono subset_rfl by_omega, h8⟩
    · simp_all
    simp_all
  · -- the interior model
    zugih

    zubxo
    have hD : c.nreg 83000 + 1 ≤ W := by have := hwf.1; grind
    have hmd : c.nmem ztcms = c₀.nmem ztbvw := by
      rw [i0, hI.hm _ (by have := hE.hwfMD.1; omega)]
    obtain ⟨c', k, ex, hk, b1, b2⟩ := iKey_exec (P := P) (a := a) (b := b) (d := d) (e := e)
      hE.hG (by have := hE.hW; unfold hostWords at this; omega) hI.hw hbit hmd hD
      by_simp_all
      hx.2.1 hy.2.1 (by zvocr; exact hx.1) (by zvocr; exact hy.1)
    have hfr : FrameB Bik c c' := exec_frameB ex ztqys
    obtain ⟨hI', hrf, h8⟩ := hI.prim ex.wb_right (frame_of_frameB hfr Bik_band k)
    refine ⟨c', k + 2, .ifLtN_false by_omega ex, by_omega, b1, b2,
      hI', hrf.mono subset_rfl by_omega, h8⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideCross)
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- Copy the bit `50210 = 1` into `r`. -/
def copyBit (r : ℕ) : Stmt :=
  .seq ztdsd (.ifLtN 50210 83023 .skip (.ifLtN 83023 50210 .skip (setB r)))
variable {r : ℕ}
theorem copyBit_exec (hr : 50100 ≤ r ∧ r < 50200) {p : Prop} (hI : TInv W c₀ c)
    (hp : c.nreg 50210 = 1 ↔ p) :
    ∃ c' k, Exec P W ztvlr c c' k ∧ k ≤ 6 ∧ c'.nreg r ≤ 1 ∧ ztiiz ∧
      TStep W c₀ c c' k ∧ FrameB ztpbs c c' := by
  zubod
  zueqd
  have hW1 : ztbla := by have := hw.1 83023; omega
  have e₁ := Exec.constN (P := P) hw r 0 by_omega
  set c₁ : Config := { c with nreg := upd c.nreg r 0 }
  zud
  have q10 : c₁.nreg 50210 = c.nreg 50210 := upd_ne by_omega
  have q23 : ztlxx := by
    rw [show c₁.nreg 83023 = c.nreg 83023 from upd_ne by_omega]; omega
  have fin : ∀ c' k, Exec P W _ c c' k → c'.nreg r ≤ 1 → ztiiz →
      k ≤ 6 → ∃ c' k, Exec P W ztvlr c c' k ∧ k ≤ 6 ∧ c'.nreg r ≤ 1 ∧
        ztiiz ∧ TStep W c₀ c c' k ∧ FrameB ztpbs c c' :=
    fun c' k ex h1 h2 hk =>
    ⟨c', k, ex, hk, h1, h2, hI.stepB ex.wb_right (B := fun q => q == r)
      (exec_frameB ex ztjqm) (fun q hq => by
        simp only [beq_iff_eq] at hq; subst hq
        exact ⟨by simp only [primBands, bandOf, bLocate, bSign, Finset.mem_insert,
          Finset.mem_singleton]; omega, by unfold ALLOC; omega⟩) k,
      exec_frameB ex ztjqm⟩
  unfold copyBit
  by_cases a : c₁.nreg 50210 < c₁.nreg 83023
  · refine fin _ _ (.seq e₁ (.ifLtN_true a ztwd)) ztnus ?_ by_omega
    zufpp

  · by_cases b : c₁.nreg 83023 < c₁.nreg 50210
    · refine fin _ _ (.seq e₁ (.ifLtN_false a (.ifLtN_true b ztwd))) ztnus ?_
        by_omega
      zufpp

    · refine fin _ _ (.seq e₁ (.ifLtN_false a (.ifLtN_false b (Exec.constN w₁ r 1 hW1))))
        by_simp ?_ by_omega
      zufcc
      grind

/-! ## The corner -/

/-- The three vertices of `Q` at the candidate vertex `p` of the interior walk (previous, `p`,
next) as symbolic points in `50140`, `50143`, `50146`. -/
def cornerS : Stmt :=
  .seq (.seq ztceu
    (.ifLtN 83005 83023 ztdcb
      ztejt))
    (.seq intIdx (.seq zthth
      (.seq intIdx (block [.copyN 50147 50044, .constN 50140 0, .constN 50143 0,
        .constN 50146 0]))))

/-- The registers `cornerS` writes. -/
def Bcor (r : ℕ) : Bool :=
  Bdir r || r == 50000 || r == 50002 || r == 50140 || r == 50141 || r == 50143 || r == 50144 ||
    r == 50146 || r == 50147
theorem wr_cornerS : wr Bcor cornerS = true := by
  rfl

/-- The previous vertex index. -/
theorem prev_succ {p n : ℕ} (hp : p < n) : ztxhn % n = p := by
  zuqi
  zujdb
  · rw [Nat.zero_add, Nat.mod_eq_of_lt ztmod, Nat.sub_add_cancel hn,
      Nat.mod_self]
  · rw [show p + n - 1 = ztoq + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt ztmoe, Nat.sub_add_cancel h0, Nat.mod_eq_of_lt hp]
theorem cornerS_exec (_hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {bit : ℕ} (hmd : c.nmem ztcms = bit) (hD : c.nreg 83000 + 1 ≤ W)
    (hp : c.nreg 83005 < P.n) (h23 : c.nreg 83023 = 1) :
    ∃ c' k, Exec P W cornerS c c' k ∧ k ≤ 50 ∧
      SymPtIn c' 50140 (.vtx (iIdx bit P.n ((c.nreg 83005 + P.n - 1) % P.n))) ∧
      SymPtIn c' 50143 (.vtx (iIdx bit P.n ztviy)) ∧
      SymPtIn c' 50146 (.vtx (iIdx bit P.n (ztlle % P.n))) := by
  set p := c.nreg 83005
  zuiz
  set pe := ztqul % P.n with hpe
  have hpeL : pe < P.n := Nat.mod_lt _ hn
  obtain ⟨c₁, k₁, e₁, hk₁, q1⟩ : ∃ c₁ k₁, Exec P W
      (.seq ztceu
        (.ifLtN 83005 83023 ztdcb
          ztejt)) c c₁ k₁ ∧ k₁ ≤ 6 ∧
      (c₁.nreg 50000 = c.nreg 83000 ∧ c₁.nreg 50002 = pe ∧ c₁.nmem = c.nmem ∧
        c₁.nreg 83005 = p) := by
    zujl
    obtain ⟨c', k', e', hk', p00, p32, pm, p05, p23⟩ : ∃ c' k', Exec P W
        ztceu c c' k' ∧ k' = 2 ∧
        c'.nreg 50000 = c.nreg 83000 ∧ c'.nreg 50032 = 1 ∧ c'.nmem = c.nmem ∧
        c'.nreg 83005 = c.nreg 83005 ∧ c'.nreg 83023 = c.nreg 83023 := by
      exec_block
      · omega
      simp
    zueki

    · zujfh
      zuken
      exec_block
      · omega
      simp_all
    · zumjn
      have hp1 : 0 < p := by_omega
      refine ⟨by_omega, by_simp_all, ?_, pm, by_tauto⟩
      config_simp
      rw [p32, p05, hpe, show p + P.n - 1 = ztoq + P.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt by_omega]
  obtain ⟨q00, q02, qm, q05⟩ := q1
  obtain ⟨c₂, k₂, e₂, hk₂, r41, r44⟩ := intIdx_exec (P := P) hW c₁ e₁.wb_right
    by_omega by_omega
  rw [q00, q02, qm, hmd] at r41 r44
  zue
  have f₂ := exec_frameB e₂ wr_intIdx
  have q05' : c₂.nreg 83005 = p := by rw [f₂.1 83005 by_decide, q05]
  have q00' : c₂.nreg 50000 = c.nreg 83000 := by
    rw [f₂.1 50000 by_decide, q00]
  have qm' : ztckc := by zungj
  obtain ⟨c₃, k₃, e₃, hk₃, s141, s144, s02, s00, sm⟩ : ∃ c₃ k₃, Exec P W
      zthth c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 50141 = c₂.nreg 50041 ∧ c₃.nreg 50144 = c₂.nreg 50044 ∧
      c₃.nreg 50002 = c₂.nreg 83005 ∧ c₃.nreg 50000 = c₂.nreg 50000 ∧ c₃.nmem = c₂.nmem := by
    exec_block
    simp
  obtain ⟨c₄, k₄, e₄, hk₄, t41, t44⟩ := intIdx_exec (P := P) hW c₃ e₃.wb_right
    by_omega by_omega
  rw [s00, q00', sm, qm', hmd, s02, q05'] at t41 t44
  have f₄ := exec_frameB e₄ wr_intIdx
  obtain ⟨c₅, k₅, e₅, hk₅, u147, u140, u143, u146, u141, u144⟩ : ∃ c₅ k₅, Exec P W
      (block [.copyN 50147 50044, .constN 50140 0, .constN 50143 0, .constN 50146 0]) c₄ c₅ k₅ ∧
      k₅ = 4 ∧ c₅.nreg 50147 = c₄.nreg 50044 ∧ c₅.nreg 50140 = 0 ∧ c₅.nreg 50143 = 0 ∧
      c₅.nreg 50146 = 0 ∧ c₅.nreg 50141 = c₄.nreg 50141 ∧ c₅.nreg 50144 = c₄.nreg 50144 := by
    zucc
    exec_block
    · omega
    · omega
    · omega
    simp
  refine ⟨c₅, _, .seq e₁ ztbq, by_omega, ⟨u140, ?_⟩, ⟨u143, ?_⟩,
    ⟨u146, ?_⟩⟩
  · rw [u141, f₄.1 50141 by_decide, s141, r41]; rfl
  · rw [u144, f₄.1 50144 by_decide, s144, r44, prev_succ hp]; rfl
  · rw [u147, t44]; rfl

/-! ## Combining -/

/-- `50210 := (o ∧ n ∧ p) ∨ (¬ o ∧ (n ∨ p))` for the bits `o = 50150`, `n = 50130`,
`p = 50131`. -/
def combineS : Stmt :=
  .seq ztbki (.ifLtN 50150 83023
    (.ifLtN 50130 83023 ztzad ztiaq)
    (.ifLtN 50130 83023 .skip ztzad))
theorem combineS_exec {c : Config} (hw : WordsBounded W c) (hW1 : 1 ≤ W) (h23 : c.nreg 83023 = 1)
    {po pn pp : Prop} (ho : BitIs c 50150 po) (hn : BitIs c 50130 pn) (hp : BitIs c 50131 pp) :
    ∃ c' k, Exec P W combineS c c' k ∧ k ≤ 8 ∧
      BitIs c' 50210 ((po ∧ pn ∧ pp) ∨ (¬ po ∧ (pn ∨ pp))) ∧
      ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := by
  have e₁ := Exec.constN (P := P) hw 50210 0 by_omega
  set c₁ : Config := { c with nreg := upd c.nreg 50210 0 }
  zud
  have g : ∀ r, r ≠ 50210 → c₁.nreg r = c.nreg r := fun r hr => upd_ne hr
  have ho' := ho.of_eq (g 50150 by_decide)
  have hn' := hn.of_eq (g 50130 by_decide)
  have hp' := hp.of_eq (g 50131 by_decide)
  have h23' : ztlxx := by_simp_all
  have h10 : ztuqj := by_rfl
  unfold combineS
  refine spec_seq ⟨c₁, 1, e₁, ?_⟩
  rcases bit01 ho' with ⟨qo, no⟩ | ⟨qo, no⟩ <;>
  rcases bit01 hn' with ⟨qn, nn⟩ | ⟨qn, nn⟩ <;>
  rcases bit01 hp' with ⟨qp, np⟩ | ⟨qp, np⟩
  all_goals
    repeat (first
      | (refine spec_ifLtN_true by_omega ?_)
      | (refine spec_ifLtN_false by_omega ?_))
  all_goals first
    | exact spec_skip w₁ ⟨by_omega, ⟨by_omega, by_simp_all⟩,
        by omega⟩
    | exact spec_instr (Exec.constN w₁ _ _ hW1) fun _ => ⟨by_omega, ⟨by_simp,
        by simp_all⟩, by_simp_all⟩

/-! ## The sector test -/
theorem primReg (h : ztdew ∨ ztdfc) :
    bandOf r ∈ primBands ∧ r ≠ ALLOC := by
  zudfh

/-- Reset a turn code other than `1` to `0`. -/
def fixBit : Stmt := .ifLtN 83023 50210 ztbki .skip

/-- The vertex case of the interior sector test. -/
def iVertexLeft : Stmt :=
  .seq tTurnN (.seq (copyBit 50130) (.seq tTurnP (.seq (copyBit 50131) (.seq cornerS
    (.seq (kbit 50140 50143 50146 2 50150) combineS)))))

/-- **The sector test of the interior model.** -/
def iLeft : Stmt := .ifLtN 83006 83023 iVertexLeft ztsqj
theorem interior_vtx {bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside zta) {q : ℕ}
    (hq : q < P.n) : (interiorModel zta).W.vtx q = (Qof P).vtx (iIdx bit P.n q) :=
  interior_wa hbit hq
theorem iIdx_inj {bit n p q : ℕ} (hp : p < n) (hq : q < n) (h : iIdx bit n p = iIdx bit n q) :
    p = q := by
  unfold iIdx at h; grind
theorem wr_combineS : wr ztijs combineS = true := by_decide
theorem iLeft_ok_vertex (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hM : M = interiorModel zta) (hbit : c₀.nmem ztbvw = 1 ↔
      Mountain.LeftInside zta) (hv : c₀.nreg 83006 = 0)
    (hroom : c.nreg ALLOC + 11000 ≤ W) :
    ∃ c' k, Exec P W iVertexLeft c c' k ∧ k ≤ 11000 ∧
      BitIs c' 50210 ztxgd ∧ TStep W c₀ c c' k := by
  zucvu
  have hWn : ztmd := by have := hE.hW; unfold hostWords at this; omega
  zucgu
  zuc
  have hn : M.W.n = P.n := by zvmzx; exact interior_n
  have hp : c₀.nreg 83005 < P.n := by zvocr; exact hE.hxe
  set bit := c₀.nmem ztbvw
  have hbit' : bit = 1 ↔ Mountain.LeftInside _ := hbit
  -- the next turn
  zubxk
  have f₁ := exec_frameB e₁ wr_tTurnN
  obtain ⟨c₂, k₂, e₂, hk₂, b₂0, b₂, s₂, f₂⟩ := copyBit_exec (P := P) (r := 50130) by_omega
    s₁.1 t₁
  -- the previous turn
  obtain ⟨c₃, k₃, e₃, hk₃, t₃, s₃⟩ := turn_ok.2 P W M N c₀ c₂ hE s₂.1 hv
    (by have := s₁.2.1.2.2.2.2.2.2; have := s₂.2.1.2.2.2.2.2.2; omega)
  have f₃ := exec_frameB e₃ wr_tTurnP
  obtain ⟨c₄, k₄, e₄, hk₄, b₄0, b₄, s₄, f₄⟩ := copyBit_exec (P := P) (r := 50131) by_omega
    s₃.1 t₃
  have hA₄ : c₄.nreg ALLOC ≤ c.nreg ALLOC + (k₁ + k₂ + k₃ + k₄) := by
    have := s₁.2.1.2.2.2.2.2.2; have := s₂.2.1.2.2.2.2.2.2; have := s₃.2.1.2.2.2.2.2.2
    have := s₄.2.1.2.2.2.2.2.2; omega
  have n30 : c₄.nreg 50130 = c₂.nreg 50130 := by
    rw [f₄.1 50130 by_decide, f₃.1 50130 by_decide]
  -- the corner
  have hI₄ := s₄.1
  have i0 := hI₄.hin 83000 by_norm_num by_norm_num
  have i5 := hI₄.hin 83005 by_norm_num by_norm_num
  have hmd : c₄.nmem (c₄.nreg 83000 + 1) = bit := by
    rw [i0, hI₄.hm _ (by have := hE.hwfMD.1; omega)]
  have hD : c₄.nreg 83000 + 1 ≤ W := by
    have := (hI₄.modelDesc hE).2.1; grind
  obtain ⟨c₅, k₅, e₅, hk₅, y40, y43, y46⟩ := cornerS_exec (P := P) hG hWn hI₄.hw hmd hD
    by_omega hI₄.h23
  rw [i5] at y40 y43 y46
  have f₅ := exec_frameB e₅ wr_cornerS
  have s₅ := hI₄.stepB e₅.wb_right f₅ (fun r hr => primReg (by
    simp only [Bcor, Bdir, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr; omega)) k₅
  -- the orientation
  set p := c₀.nreg 83005
  set pe := ztqul % P.n
  set pb := ztr % P.n
  have hpe : pe < P.n := Nat.mod_lt _ by_omega
  have hpb : pb < P.n := Nat.mod_lt _ by_omega
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, o₆0, o₆⟩ := kbit_exec (P := P) hG hWn c₅ e₅.wb_right
    (a := 50140) (b := 50143) (d := 50146) (op := 2) (dst := 50150)
    (sa := .vtx zthyd) (sb := .vtx ztfsp) (sd := .vtx zthyc)
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
    (show zthyd < P.n from iIdx_lt hpe) (show ztfsp < P.n from iIdx_lt hp)
    (show zthyc < P.n from iIdx_lt hpb) y40 y43 y46
  have s₆ := s₅.1.stepB e₆.wb_right f₆ (fun r hr => primReg (by
    simp only [Bkb, WalkKey.Bk, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr; omega)) k₆
  -- the combination
  have g30 : c₆.nreg 50130 = c₂.nreg 50130 := by
    rw [f₆.1 50130 by_decide, f₅.1 50130 by_decide, n30]
  have g31 : c₆.nreg 50131 = c₄.nreg 50131 := by
    rw [f₆.1 50131 by_decide, f₅.1 50131 by_decide]
  obtain ⟨c₇, k₇, e₇, hk₇, bit₇, -⟩ := combineS_exec (P := P) e₆.wb_right by_omega
    s₆.1.h23 ⟨o₆0, o₆⟩ (BitIs.of_eq ⟨b₂0, b₂⟩ g30) (BitIs.of_eq ⟨b₄0, b₄⟩ g31)
  have f₇ := exec_frameB e₇ wr_combineS
  have s₇ := s₆.1.stepB e₇.wb_right f₇ (fun r hr => primReg (by
    simp_all)) k₇
  refine ⟨c₇, k₁ + ztxkw,
    .seq e₁ ztfc, by_omega, ?_,
    s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans s₇)))))⟩
  refine ⟨bit₇.1, bit₇.2.trans ?_⟩
  -- the corner in terms of the walk
  have hx0 : M.param zta ztfy = 0 := WalkKey.param_of_code_zero hv
  have wv : M.W.vtx p = (Qof P).vtx ztfsp := by zvmzx; exact interior_vtx hbit' hp
  have wb : M.W.vtx ztwjk = (Qof P).vtx zthyc := by
    zuong; exact interior_vtx hbit' hpb
  have wa : M.W.vtx ztcm = (Qof P).vtx zthyd := by
    zuong; exact interior_vtx hbit' hpe
  have hD' := distinct_Qof hG
  have hne : ∀ q, q < P.n → q ≠ p → ((Qof P).vtx _).2 ≠
      ((Qof P).vtx ztfsp).2 := fun q hq hqp => hD' _ _ (by zvmxg; exact iIdx_lt hq)
    (by zvmxg; exact iIdx_lt hp) (fun h => hqp (iIdx_inj hq hp h))
  have hbp : pb ≠ p := by
    zuq
    simp only [pb] at h
    rcases Nat.lt_or_ge ztr P.n with h1 | h1
    · zuhkh
    · have : p + 1 = P.n := by_omega
      rw [this, Nat.mod_self] at h; omega
  have hep : pe ≠ p := by
    zuq
    have h2 := prev_succ hp
    grind
  have hcross : sideCross ztbajf
      ztwll =
      det ((Qof P).vtx zthyd) ((Qof P).vtx ztfsp)
        ((Qof P).vtx zthyc) := by
    rw [wb, wv, wa, Chazelle.Chain.sideCross_corner]
  have hb' : (M.W.vtx (((xOf c₀).edge + 1) % M.W.n)).2 ≠ (M.W.vtx (xOf c₀).edge).2 := by
    show (M.W.vtx ztwjk).2 ≠ (M.W.vtx p).2
    rw [wb, wv]; exact hne _ hpb hbp
  have ha' : (M.W.vtx (((xOf c₀).edge + M.W.n - 1) % M.W.n)).2 ≠ (M.W.vtx (xOf c₀).edge).2 := by
    show (M.W.vtx ztcm).2 ≠ (M.W.vtx p).2
    rw [wa, wv]; exact hne _ hpe hep
  rw [left_vertex_iff hx0 hb' ha']
  show _ ↔ (0 < sideCross ztbajf
      ztwll ∧ _) ∨
    (¬ 0 < sideCross ztbajf
      ztwll ∧ _)
  rw [hcross]
  rfl
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}
theorem wr_fixBit : wr ztijs fixBit = true := by_decide

/-- The edge case of the interior sector test. -/
theorem iLeft_ok_edge (hE : TGood P W M N c₀) (hI : TInv W c₀ c) (hv : c₀.nreg 83006 ≠ 0)
    (hroom : c.nreg ALLOC + 5300 ≤ W) :
    ∃ c' k, Exec P W ztsqj c c' k ∧ k ≤ 5300 ∧
      BitIs c' 50210 ztxgd ∧ TStep W c₀ c c' k := by
  zubxk
  have hI₁ := s₁.1
  have h23 := hI₁.h23
  have hw₁ := hI₁.hw
  zudk
  have hpos : 0 < M.param zta ztfy := by
    zufzq
    · omega
    positivity
  have hleft := left_inside_iff (σb := c₀.nreg 83008) hpos hE.hxp.2.1
  unfold fixBit
  by_cases h2 : c₁.nreg 83023 < c₁.nreg 50210
  · have e₂ := Exec.constN (P := P) hw₁ 50210 0 by_omega
    have ex := Exec.seq e₁ (Exec.ifLtN_true (e := .skip) h2 e₂)
    have f₂ : FrameB ztijs c₁ { c₁ with nreg := upd c₁.nreg 50210 0 } :=
      exec_frameB (Exec.ifLtN_true (e := .skip) h2 e₂) wr_fixBit
    refine ⟨_, _, ex, by_omega, zthml, s₁.trans (hI₁.stepB e₂.wb_right f₂
      (fun r hr => Restore.primReg by_simp_all) _)⟩
    simp only [upd_eq, zero_ne_one, false_iff]
    grind
  · have ex := Exec.seq e₁ (Exec.ifLtN_false (t := .instr ztsot) h2 ztekd)
    refine ⟨_, _, ex, by_omega, zteh, s₁.mono by_omega⟩
    simp_all

/-- **The sector test of both models.** -/
def gLeft : Stmt := .ifLtN 83021 83023 tLeft iLeft
theorem gLeft_ok : LeftOK gLeft 20000 := by
  intro P W M N c₀ c hE hI hroom
  zuivj
  zueqd
  zubbz
  · obtain ⟨c', k, ex, hk, b, s⟩ := tLeft_exec hE hI hM by_omega
    exact ⟨c', k + 1, .ifLtN_true by_omega ex, by_omega, b,
      s.mono by_omega⟩
  · zuess
    by_cases hv : c.nreg 83006 < c.nreg 83023
    · obtain ⟨c', k, ex, hk, b, s⟩ := iLeft_ok_vertex hE hI hMi hbit by_omega by_omega
      exact ⟨c', k + 1 + 2, .ifLtN_false by_omega (.ifLtN_true hv ex),
        by omega, b, s.mono by_omega⟩
    · obtain ⟨c', k, ex, hk, b, s⟩ := iLeft_ok_edge hE hI by_omega by_omega
      exact ⟨c', k + 2 + 2, .ifLtN_false by_omega (.ifLtN_false hv ex),
        by omega, b, s.mono by_omega⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
variable {P : Polygon} {W : ℕ}

/-! ## Mathematics -/

/-- The index of the edge of `Q` carrying the edge `e` of the interior walk. -/
def iEdgeIdx (bit n e : ℕ) : ℕ := if bit = 1 then e else if e + 1 < n then n - 2 - e else n - 1

/-- The symbolic point of the position `⟨e, h⟩` of the interior walk. -/
def iSym (bit n e h : ℕ) : SymPt :=
  if h = 0 then .vtx ztlpx else .onEdge (iEdgeIdx bit n e) zthhn
variable {bit n e : ℕ}
theorem iEdgeIdx_lt (hn : 3 ≤ n) (he : e < n) : iEdgeIdx bit n e < n := by
  unfold iEdgeIdx; grind
theorem iSym_lt {bit n e h : ℕ} (hn : 3 ≤ n) (he : e < n) (hh : h ≤ n) : (iSym bit n e h).Lt n := by
  unfold iSym; split_ifs with h0
  · exact iIdx_lt he
  · exact ⟨iEdgeIdx_lt hn he, by_omega⟩

/-- The walk edge `e` joins consecutive vertices of `Q`. -/
theorem iIdx_edgeOK (hn : 3 ≤ n) (he : e < n) :
    HostEdgeOK n ztbado ztxui := by
  simp only [HostEdgeOK, iIdx]
  zuidt
  · zudjt
    split_ifs
    · left; zvnnn
    · right; zvmyc; omega
  · have : e + 1 = n := by_omega
    rw [this, Nat.mod_self]
    split_ifs
    · simp_all
    · right; rw [show n - 1 - 0 + 1 = n by omega, Nat.mod_self]; omega
theorem iIdx_ne (hn : 3 ≤ n) (he : e < n) :
    iIdx bit n e ≠ iIdx bit n (ztda % n) := by
  unfold iIdx
  zuidt
  · zvnnn; grind
  · zunkv; grind

/-- **The edge of `Q` carrying the walk edge** is `iEdgeIdx`. -/
theorem edgeOf_iIdx (hn : 3 ≤ n) (he : e < n) :
    ShootCut.edgeOf n ztbado ztxui = iEdgeIdx bit n e := by
  have hmod : ztda % n = if e + 1 < n then e + 1 else 0 := by
    zus
    · zubql
    · zunkv
  by_cases hb : bit = 1
  · simp [ShootCut.edgeOf, iEdgeIdx, iIdx, hb]
  · have hne : n - 1 - ztda % n ≠ (n - 1 - e + 1) % n := by
      zugvd
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; rw [ite_eq_left by_omega, show n - 1 - 0 + 1 = n by omega, Nat.mod_self]; omega
      · rw [Nat.mod_eq_of_lt by_grind]; grind
    simp only [ShootCut.edgeOf, iEdgeIdx, iIdx, hb, ite_false, ite_eq_right hne]
    grind

/-- **The point of a position of the interior walk** is its symbolic point. -/
theorem interior_pos_sym (hG : GoodEnv P) {bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside zta)
    {e h : ℕ} (he : e < P.n) :
    (interiorModel zta).pos zta ztcq = (iSym bit P.n e h).eval zta := by
  zubp
  zucgu
  zukkl
  · simp only [Model.pos, Model.param, iSym, ite_true, SymPt.eval, Geometry.lerp_zero]
    exact interior_wa hbit he
  · have hD := ShootCut.goodEnv_distinct hG
    zucgo

    have hj := iIdx_lt (bit := bit) (Nat.mod_lt ztda ztdwe)
    have := ShootCut.pos_eq_onEdge _ hD by_omega (h := k) (sp₁ := .vtx _) (sp₂ := .vtx _)
      ha hb ztnum ztnum
      (by zvmxq; exact iIdx_edgeOK hn3 he)
      (by rw [ha, hb]; exact hD _ _ by_omega by_omega (iIdx_ne hn3 he))
    rw [this, hn, edgeOf_iIdx hn3 he]
    rfl

/-- **The abscissa of a proper position of the interior walk** is below `coordBound Q + 1`. -/
theorem interior_abs_lt (hG : GoodEnv P) {bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside zta)
    {x : WPos} (he : x.edge < P.n) (hp : ProperPos ztwiq zta P.n x) :
    |((interiorModel (Qof P)).pos (Qof P) x).1| < Jordan.coordBound (Qof P) + 1 := by
  zubp
  zucgo

  have hj := iIdx_lt (bit := bit) (Nat.mod_lt ztbfa (show 0 < P.n by
    have := hG.1.1; omega))
  have b1 := Jordan.abs_fst_vtx_le_coordBound zta (i := iIdx bit P.n x.edge) by_omega
  have b2 := Jordan.abs_fst_vtx_le_coordBound zta (i := iIdx bit P.n ztzyp)
    by_omega
  obtain ⟨t0, t1, -⟩ := hp
  simp only [Model.pos, Geometry.lerp_fst]
  zucpu
  set t := (interiorModel zta).param zta x
  set u := ((Qof P).vtx (iIdx bit P.n x.edge)).1
  set v := ((Qof P).vtx (iIdx bit P.n ztzyp)).1
  have : u + t * ztbnr = ztca * u + t * v := by_ring
  zubk
  have h1 : |ztca * u + t * v| ≤ ztca * |u| + t * |v| := by
    calc |ztca * u + t * v| ≤ |ztca * u| + |t * v| := abs_add_le _ _
      _ = ztca * |u| + t * |v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg by_grind, abs_of_nonneg t0]
  have h2 : ztca * |u| + t * |v| ≤ Jordan.coordBound zta := by
    have := mul_le_mul_of_nonneg_left b1 (by linarith : (0 : ℝ) ≤ 1 - t)
    have := mul_le_mul_of_nonneg_left b2 t0
    nlinarith
  linarith

/-! ## The machine -/

/-- The edge index for the reversed orientation: `n - 2 - e`, or `n - 1` at the last edge. -/
def iNxt (a : ℕ) : Stmt :=
  .seq (.instr (.addN 50217 a 50216))
    (.ifLtN 50217 50215 (block [.subN 50212 50215 50217, .subN 50212 50212 50216])
      (.instr (.subN 50212 50215 50216)))

/-- The index for the reversed orientation (`bit ≠ 1`). -/
def iFix (a b : ℕ) : Stmt :=
  .ifLtN 83022 b ztmll (block [.subN 50212 50215 50216, .subN 50212 50212 a])

/-- **The abscissa record of an interior position** `(a, b)` into `50210 … 50213`. -/
def iRec (a b : ℕ) : Stmt :=
  .seq (block [.loadN 50214 83020, .inputSize 50215, .constN 50216 1, .constN 50210 1,
      .copyN 50212 a, .constN 50211 0])
    (.seq ztgbp
      (.ifLtN 50214 50216 zthhs (.ifLtN 50216 50214 zthhs .skip)))

/-- The registers written by `iRec`. -/
def BiR (r : ℕ) : Bool := decide (50210 ≤ r ∧ r < 50218)
theorem wr_iRec (a b : ℕ) : wr BiR ztjyq = true := by
  rfl

/-- The registers written by `iFix`. -/
def Bfx (r : ℕ) : Bool := r == 50212 || r == 50217
theorem bfx_sub {r : ℕ} (h : Bfx r = true) : BiR r = true := by
  simp only [Bfx, Bool.or_eq_true, beq_iff_eq] at h
  simp only [BiR, decide_eq_true_eq]; omega

/-- **The reversed index**: `iFix` puts `n - 1 - e` (vertex) or `iEdgeIdx` (edge) into `50212`. -/
theorem iFix_exec {c : Config} (hw : WordsBounded W c) {a b : ℕ} (hW : P.n + 3 ≤ W)
    (h15 : c.nreg 50215 = P.n) (h16 : c.nreg 50216 = 1) (h22 : c.nreg 83022 = 0)
    (ha : c.nreg a < P.n) (_hn3 : 3 ≤ P.n) (hab : a ≠ 50212 ∧ a ≠ 50217) :
    ∃ c' k, Exec P W zthhs c c' k ∧ k ≤ 6 ∧
      c'.nreg 50212 = (if c.nreg b = 0 then P.n - 1 - c.nreg a
        else if c.nreg a + 1 < P.n then P.n - 2 - c.nreg a else P.n - 1) ∧
      FrameB Bfx c c' := by
  unfold iFix
  by_cases hb : c.nreg 83022 < c.nreg b
  · have hb0 : c.nreg b ≠ 0 := by_omega
    have e₁ := Exec.addN (P := P) hw 50217 a 50216 by_omega
    set c₁ : Config := { c with nreg := upd c.nreg 50217 _ } with hc₁
    zud
    have v17 : c₁.nreg 50217 = c.nreg a + 1 := by_simp_all
    have v15 : c₁.nreg 50215 = P.n := by_simp_all
    have v16 : c₁.nreg 50216 = 1 := by_simp_all
    by_cases hl : c₁.nreg 50217 < c₁.nreg 50215
    · obtain ⟨c', k, e, hk, v12, fr⟩ : ∃ c' k, Exec P W
          _ c₁ c' k ∧ k = 2 ∧
          c'.nreg 50212 = c₁.nreg 50215 - c₁.nreg 50217 - c₁.nreg 50216 ∧
          FrameB Bfx c₁ c' := by
        have ea := Exec.subN (P := P) w₁ 50212 50215 50217
        have eb := Exec.subN (P := P) ea.wb_right 50212 50212 50216
        refine ⟨_, _, Exec.block_cons ea ztbws, rfl,
          ?_, ?_⟩
        · simp
        · exact exec_frameB ztyos
            by_rfl
      have ex : Exec P W (.ifLtN 83022 b ztmll (block [.subN 50212 50215 50216,
          .subN 50212 50212 a])) c c' _ := .ifLtN_true hb (.seq e₁ (.ifLtN_true hl e))
      refine ⟨c', _, ex, by_omega, ?_, exec_frameB ex (by
        rfl)⟩
      grind
    · have e₂ := Exec.subN (P := P) w₁ 50212 50215 50216
      have ex : Exec P W (.ifLtN 83022 b ztmll (block [.subN 50212 50215 50216,
          .subN 50212 50212 a])) c _ _ := .ifLtN_true hb (.seq e₁ (.ifLtN_false hl e₂))
      refine ⟨_, _, ex, by_omega, ?_, exec_frameB ex (by
        rfl)⟩
      simp_all
  · have hb0 : ztuoq := by_omega
    have ea := Exec.subN (P := P) hw 50212 50215 50216
    have eb := Exec.subN (P := P) ea.wb_right 50212 50212 a
    have ex : Exec P W (.ifLtN 83022 b ztmll _) c _ _ :=
      .ifLtN_false hb ztyos
    refine ⟨_, _, ex, by_omega, ?_, exec_frameB ex (by
      rfl)⟩
    simp_all

/-- **The abscissa record of an interior position.** -/
theorem iRec_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {a b bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside zta)
    (hmd : c.nmem ztdms = bit) (h22 : c.nreg 83022 = 0)
    (ha8 : 80000 ≤ a ∧ a < 90000) (hb8 : 80000 ≤ b ∧ b < 90000)
    (hp : ProperPos ztwiq zta P.n ztel)
    (he : c.nreg a < P.n) :
    ∃ c' k, Exec P W ztjyq c c' k ∧ k ≤ 20 ∧
      AbsRec P c' 50210 ((interiorModel zta).pos zta ztel).1
        (Jordan.coordBound zta + 1) ∧ FrameB BiR c c' := by
  zucgu
  have hbn := hp.2.2
  set e := c.nreg a with he_def
  set h := c.nreg b with hh_def
  -- the head
  obtain ⟨c₁, k₁, e₁, hk₁, q14, q15, q16, q10, q12, q11, g₁, hm₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.loadN 50214 83020, .inputSize 50215, .constN 50216 1, .constN 50210 1,
        .copyN 50212 a, .constN 50211 0]) c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 50214 = bit ∧
      c₁.nreg 50215 = P.n ∧ c₁.nreg 50216 = 1 ∧ c₁.nreg 50210 = 1 ∧ c₁.nreg 50212 = e ∧
      c₁.nreg 50211 = 0 ∧ ztgse ∧
      c₁.nmem = c.nmem := by
    exec_block
    · omega
    · omega
    · omega
    · omega
    · refine ⟨rfl, ?_, by config_simp, by config_simp, by config_simp, ?_, by config_simp,
        fun r h1 h2 => ?_, rfl⟩
      · simp_all
      · simp [upd, he_def, show a ≠ 50214 by omega, show a ≠ 50215 by omega,
          show a ≠ 50216 by omega, show a ≠ 50210 by omega]
      · simp [upd, show r ≠ 50210 by omega, show r ≠ 50211 by omega, show r ≠ 50212 by omega,
          show r ≠ 50214 by omega, show r ≠ 50215 by omega, show r ≠ 50216 by omega]
  zud
  have ga := g₁ a ha8.1 ha8.2
  have gb := g₁ b hb8.1 hb8.2
  have g22 := g₁ 83022 by_norm_num by_norm_num
  have F₁ : FrameB BiR c c₁ := exec_frameB e₁ by_rfl
  -- the kind of the symbolic point
  obtain ⟨c₂, k₂, e₂, hk₂, r10, r11, r13, r12, r14, r15, r16, g₂, F₂⟩ : ∃ c₂ k₂, Exec P W
      ztgbp c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg 50210 = 1 ∧ c₂.nreg 50211 = ztmlq ∧
      (h ≠ 0 → c₂.nreg 50213 = h - 1) ∧ c₂.nreg 50212 = e ∧ c₂.nreg 50214 = bit ∧
      c₂.nreg 50215 = P.n ∧ c₂.nreg 50216 = 1 ∧
      (∀ r, 80000 ≤ r → r < 90000 → c₂.nreg r = c.nreg r) ∧ FrameB BiR c₁ c₂ := by
    by_cases hb : c₁.nreg 83022 < c₁.nreg b
    · have h0 : h ≠ 0 := by_omega
      have ea := Exec.constN (P := P) w₁ 50211 1 by_omega
      have eb := Exec.subN (P := P) ea.wb_right 50213 b 50216
      have ex := Exec.block_cons ea ztbws
      refine ⟨_, _, .ifLtN_true hb ex, by_omega, ?_, ?_, fun _ => ?_, ?_, ?_, ?_, ?_,
        fun r h1 h2 => ?_, exec_frameB ex by_rfl⟩
      all_goals zvmwf
      all_goals try simp only [show (50210 : ℕ) ≠ 50213 by norm_num,
        show (50210 : ℕ) ≠ 50211 by norm_num, ite_false]
      · omega
      · simp_all
      · grind
      · simp_all
      · simp_all
      · simp_all
      · simp_all
      grind
    · have h0 : ztsiu := by_omega
      refine ⟨c₁, _, .ifLtN_false hb ztwd, by_omega, q10, by_simp_all,
        by omega, q12, q14, q15, q16, g₁, FrameB.refl _ _⟩
  zue
  have ga2 := g₂ a ha8.1 ha8.2
  have gb2 := g₂ b hb8.1 hb8.2
  have g222 := g₂ 83022 by_norm_num by_norm_num
  -- the index
  have hidx : ∃ c' k, Exec P W (.ifLtN 50214 50216 zthhs (.ifLtN 50216 50214 zthhs
      .skip)) c₂ c' k ∧ k ≤ 10 ∧ c'.nreg 50212 = (if h = 0 then iIdx bit P.n e
        else iEdgeIdx bit P.n e) ∧ FrameB Bfx c₂ c' := by
    have fix := iFix_exec w₂ (a := a) (b := b) hW r15 r16 by_omega
      by_omega hn3 by_omega
    rw [ga2, gb2] at fix
    obtain ⟨c', k, ex, hk, v12, fr⟩ := fix
    have val : bit ≠ 1 → c'.nreg 50212 = (if h = 0 then iIdx bit P.n e
        else iEdgeIdx bit P.n e) := fun hb1 => by
      rw [v12, ← he_def, ← hh_def]; unfold iIdx iEdgeIdx; grind
    by_cases g1 : c₂.nreg 50214 < c₂.nreg 50216
    · exact ⟨c', _, .ifLtN_true g1 ex, by_omega, by_omega, fr⟩
    by_cases g2 : c₂.nreg 50216 < c₂.nreg 50214
    · exact ⟨c', _, .ifLtN_false g1 ztsph, by_omega,
        by omega, fr⟩
    · zuhya
      refine ⟨c₂, _, .ifLtN_false g1 (.ifLtN_false g2 ztbun), by_omega, ?_, FrameB.refl _ _⟩
      zupax; unfold iIdx iEdgeIdx; grind
  obtain ⟨c₃, k₃, e₃, hk₃, v12, F₃⟩ := hidx
  have k3 := F₃.1
  have ex : Exec P W ztjyq c c₃ _ := .seq e₁ ztcr
  refine ⟨c₃, _, ex, by_omega, ?_,
    F₁.trans (F₂.trans (frameB_mono F₃ (fun r hr => bfx_sub hr)))⟩
  have v10 : c₃.nreg 50210 = 1 := by rw [k3 _ by_decide, r10]
  have v11 : c₃.nreg 50211 = ztmlq := by rw [k3 _ by_decide, r11]
  have v13 : h ≠ 0 → c₃.nreg 50213 = h - 1 := fun h0 => by rw [k3 _ by_decide, r13 h0]
  have hpos := interior_pos_sym hG hbit (h := h) he
  refine ⟨by
    have : 0 ≤ Jordan.coordBound zta :=
      Finset.sum_nonneg by_grind
    linarith, Or.inr (Or.inr
    ⟨v10, interior_abs_lt hG hbit he hp, iSym bit P.n e h, ?_,
      iSym_lt hn3 he hbn, by_simp_all⟩)⟩
  unfold iSym
  by_cases h0 : h = 0
  · simp only [h0, ite_true] at v11 v12 ⊢
    exact ⟨v11, v12⟩
  · simp only [h0, ite_false] at v11 v12 ⊢
    exact ⟨v11, v12, v13 h0⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}
theorem chainModel_n' (C : Chain) : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _

/-- **The walk of a chain model fits the word bound.** -/
theorem walk_le_W {m : ℕ → ℕ} {MD A : ℕ} (hMD : ModelDescAt m MD zta M)
    (hwf : ModelDescWF P A m MD) (hW : hostWords P.n ≤ W) {C : Chain} (hM : M = chainModel C) :
    2 * C.m + 7 ≤ W := by
  zudrm
  obtain ⟨hl, hHW, -, -⟩ := (hwf.2 hz).2 H C' hC
  zuftr

  have e : C.m = C'.m := by
    have := congrArg (fun M : Model => M.W.n) ztqpm
    simp only [chainModel_n'] at this
    omega
  zumsu
  omega

/-- **The fixed data of a run** from the precondition of `TestOK`. -/
theorem tgood_of (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hMD : ModelDescAt c₀.nmem ztchn zta M)
    (hwf : ModelDescWF P ztdq c₀.nmem ztchn)
    (hreg : c₀.nmem ztchn = 0 → ∀ H C,
      ChainDescAt c₀.nmem ztbvw zta H C → HostRegular (Qof P).n H)
    (hsimp : c₀.nmem ztchn = 0 → ∀ H C,
      ChainDescAt c₀.nmem ztbvw zta H C → C.P.Simple)
    (hkind : OkModel P M ∨ M = interiorModel zta) (hGM : GoodModel M)
    (hN : NFWithin c₀.nmem ztvmg ztdq N) (hNF : IsNF M zta N)
    (hr : c₀.nreg 83002 < N.nRegions) (hxe : c₀.nreg 83005 < M.W.n)
    (hxp : ProperPos M zta P.n ztxt)
    (hxc : c₀.nreg 83006 = 0 ∨ 0 < M.param zta ztxt)
    (hxC : ∀ C : Chain, M = chainModel C → M.pos zta ztxt ∈ C.set)
    (hh : c₀.nreg 83007 < P.n)
    (hy : ((Qof P).vtx ztvmh).2 = (M.pos zta ztxt).2)
    (hσ : c₀.nreg 83008 ≤ 1) : TGood P W M N c₀ :=
  ⟨hG, hW, hMD, hwf, hreg, hsimp, hkind, hGM, fun _C hM => walk_le_W hMD hwf hW hM, hN, hNF, hr, hxe,
    hxp, hxc, hxC, hh, hy, hσ⟩

/-- **The constants of a run.** -/
def tSetup : Stmt :=
  block [.constN 83022 0, .constN 83023 1, .addN 83020 83000 83023, .loadN 83021 83000]
theorem tSetup_exec (hw : WordsBounded W c) (hMD : c.nreg 83000 + 6 ≤ c.nreg ALLOC) :
    ∃ c' k, Exec P W tSetup c c' k ∧ k = 4 ∧ TInv W c c' ∧ RF dBands ztm c c' k := by
  zueqh
  obtain ⟨c', k, ex, hk, q22, q23, q20, q21, hr, hrr, hm, hrm, ho⟩ : ∃ c' k, Exec P W tSetup c c' k ∧
      k = 4 ∧ c'.nreg 83022 = 0 ∧ c'.nreg 83023 = 1 ∧ c'.nreg 83020 = c.nreg 83000 + 1 ∧
      c'.nreg 83021 = c.nmem ztdcs ∧
      (∀ r, r ≠ 83020 → r ≠ 83021 → r ≠ 83022 → r ≠ 83023 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    unfold tSetup
    exec_block
    · omega
    · omega
    · config_simp; omega
    simp_all
  have hA : ztble := hr ALLOC by_decide
    by_decide by_decide by_decide
  refine ⟨c', k, ex, hk, ⟨ex.wb_right, fun q h1 h2 => hr q by_omega by_omega by_omega
    by_omega, by_omega, fun a _ => by zvmwi, q20, q21, q22, q23⟩, ?_⟩
  exact rf_of_regs (fun r hr' => hr r by_omega by_omega by_omega by_omega) hrr hm hrm ho
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace DrvH
@[expose] public section
open DrvR

/-- **The facts about region `r` of `N`** used by the host RAM. -/
structure HFacts (n : ℕ) (N : NF) (r : ℕ) : Prop where
  hr : r < N.nRegions
  hA : (N.region r).arcs.length ≤ 5
  hK : (N.region r).chords.length ≤ 4
  harc : ∀ j ∈ (N.region r).arcs, j < N.arcs.length ∧ (N.arc j).s.edge < n ∧
    (N.arc j).s.hgt ≤ n ∧ (N.arc j).e.edge < n ∧ (N.arc j).e.hgt ≤ n
  hch : ∀ i ∈ (N.region r).chords, i < N.nChords ∧ (N.chord i).lp < n ∧ (N.chord i).rp < n ∧
    (N.chord i).h + 1 ≤ n

/-- **A region lists at most five arcs** (degree `≤ 4`; any model satisfying the walk axioms). -/
theorem region_arcs_le_of {M : Model} {Q : Polygon} {N : NF} (hM : WalkAx M) (hN : IsNF M Q N)
    (hdeg : M.DegLe ztdu 4) {r : ℕ} (hr : r < N.regions.length) :
    (N.region r).arcs.length ≤ 5 := by
  classical
  obtain ⟨hF, -, -, reg, hR, -, hA, hRs, -⟩ := hN
  have hU : ztylu := hR.1 r hr
  zudhx

  zufaj
  zudht
  have hinj : ztmtv := by
    zukjn
    zuxm

    zuhud
  have hsub : f '' {j | j ∈ L} ⊆ {ab : ℝ × ℝ | M.IsArc ztdu ztcz ab.1 ab.2} := by
    zuczd

    have := (hA.1 j h1).2
    grind
  zufye
  have hdg := hdeg _ hU
  have hL : ztidp := by
    rw [show ({j | j ∈ L} : Set ℕ) = ↑L.toFinset by ext; simp, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hnd]
  have h1 : zteea :=
    (Set.InjOn.ncard_image hinj).symm
  zuivh

/-- **The facts about region `r`** of the interior normal form `buildNF I Q L E`. -/
theorem hfacts_of {Q : Polygon} (hQ : Q.Simple) {L : List zte} {E : List ℕ}
    (hLne : L ≠ []) (hL : ChordTriplesOK ztd Q L)
    (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztwxw)
    (hdeg : (interiorModel Q).DegLe
      ztwjn 4) {r : ℕ}
    (hr : r < (BuildNF.buildNF ztd Q L E).nRegions) :
    HFacts Q.n ztwjp r := by
  set N := BuildNF.buildNF ztd Q L E with hNdef
  zueqj
  have hN : ztyyf := DownMath.isNF_build hQ hL hperm hsort
  zuok
  have hpos : ∀ x : WPos, DownMath.ChordPos N x → x.edge < Q.n ∧ x.hgt ≤ Q.n := by
    zuh
    zucxv
    obtain ⟨-, hA, -, eh, hh, -⟩ := DownMath.chordPos_attach hN hi hxi
    exact ⟨DownMath.walk_n Q ▸ hA.1, by_omega⟩
  obtain ⟨-, -, -, reg, hRC, -, hAO, hRO, -, hh, -⟩ := id hN
  refine ⟨hr, region_arcs_le_of hM hN hdeg hr, ?_, fun j hj => ?_, fun i hi => ?_⟩
  · zuhnt
    exact hdeg _ ztdhm
  · have hj' := ((hAO.2.2.2 r hr j).1 hj).1
    obtain ⟨hs, he⟩ := DownMath.arc_pos hQ hL hperm hsort hK hj'
    simp_all
  · have hi' := ((hRO r hr).1 i).1 hi |>.1
    have h1 := hpos _ ⟨i, hi', Or.inl rfl⟩
    have h2 := hpos _ ⟨i, hi', Or.inr rfl⟩
    tauto
def encK : HostItem → ℕ
  | .run _ _ => 0
  | .pt (.vtx _) => 1
  | .pt (.onEdge _ _) => 2

/-- The first argument word of an item. -/
def encA : HostItem → ℕ
  | .run a _ => a
  | .pt (.vtx j) => j
  | .pt (.onEdge e _) => e

/-- The second argument word of an item. -/
def encB : HostItem → ℕ
  | .run _ ℓ => ℓ
  | .pt (.vtx _) => 0
  | .pt (.onEdge _ h) => h

/-- **Items in memory**: item `i` of `xs` at `T + 3 i` (kind, two arguments). -/
def ItemsAt (m : ℕ → ℕ) (T : ℕ) (xs : List HostItem) : Prop :=
  ∀ i, i < xs.length →
    m (T + 3 * i) = encK ztysf ∧ m (T + 3 * i + 1) = encA ztysf ∧
      m (T + 3 * i + 2) = encB ztysf

/-- Write three words. -/
def wr3 (m : ℕ → ℕ) (p a b c : ℕ) : ℕ → ℕ := upd (upd (upd m p a) ztr b) ztcao c
variable {m : ℕ → ℕ} (n : ℕ) (li : Bool)
theorem wr3_lt {p a b c x : ℕ} (hx : x < p) : wr3 m p a b c x = m x := by
  unfold wr3
  rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
    Machine.upd_other _ _ _ by_omega]
theorem ItemsAt.nil (m : ℕ → ℕ) (T : ℕ) : ItemsAt m T [] := fun i hi => by_simp_all

/-- **Appending an item** written at the end. -/
theorem ItemsAt.snoc {T : ℕ} {xs : List HostItem} (h : ItemsAt m T xs)
    (it : HostItem) :
    ItemsAt (wr3 m ztjnd (encK it) (encA it) (encB it)) T (xs ++ [it]) := by
  zug
  zucjh
  unfold wr3
  rcases Nat.lt_or_ge i xs.length with h1 | h1
  · zunvf
    obtain ⟨a1, a2, a3⟩ := h i h1
    zusk
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, a1]
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, a2]
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, a3]
  · have hi' : i = xs.length := by_omega
    simp_all

/-- Items survive a change of the memory outside their words. -/
theorem ItemsAt.congr {m m' : ℕ → ℕ} {T : ℕ} {xs : List HostItem} (h : ItemsAt m T xs)
    (hm : ∀ a, T ≤ a → a < T + 3 * xs.length → m' a = m a) : ItemsAt m' T xs := by
  zug
  zurw
  grind

/-- **The host layout** is the count word followed by the items. -/
theorem hostAt_of {B : ℕ} {H : Host} (h0 : m B = H.length) (h : ItemsAt m ztvf H) :
    HostAt m B H := by
  refine ⟨h0, fun i hi => ?_⟩
  zurw
  rw [show B + 1 + 3 * i + 1 = B + 2 + 3 * i by ring,
    show B + 1 + 3 * i + 2 = B + 3 + 3 * i by ring] at *
  generalize H.getD i ztmn = it at a1 a2 a3
  rcases it with ⟨a, l⟩ | ⟨j⟩ | ⟨e, hh⟩
  · tauto
  · tauto
  tauto

/-- The reversal of items, read one by one. -/
theorem getD_reverse_items {xs : List HostItem} {i : ℕ} (hi : i < xs.length) :
    xs.reverse.getD i ztmn = xs.getD (xs.length - 1 - i) ztmn := by
  grind

/-! ## Point counts -/

/-- The number of symbolic points of a list of items. -/
def ptsLen (n : ℕ) (xs : List HostItem) : ℕ := (Host.pts n xs).length
theorem ptsLen_nil : ptsLen n [] = 0 := rfl
theorem ptsLen_append (xs ys : List HostItem) :
    ptsLen n (xs ++ ys) = ptsLen n xs + ptsLen n ys := by
  simp [ptsLen, Host.pts, List.flatMap_append]
theorem ptsLen_pt (x : SymPt) : ptsLen n [.pt x] = 1 := by
  rfl
theorem ptsLen_run (n a l : ℕ) : ptsLen n [.run a l] = l + 1 := by
  simp [ptsLen, Host.pts, HostItem.pts]
theorem ptsLen_reverse (xs : List HostItem) : ptsLen n xs.reverse = ptsLen n xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, ptsLen_append, ih, show x :: xs = [x] ++ xs from rfl, ptsLen_append]
    omega

/-! ## The points written by the RAM -/

/-- The host point written by the RAM: edge `qE li n e`, height `h - 1`. -/
def ptE (li : Bool) (n e h : ℕ) : HostItem := .pt (.onEdge ztlsa zthhn)

/-! ## The prefixes of the walk items -/

/-- The items of the arc loop's iteration `t` (arc `arcs[t]` and its successor). -/
def arcIt (li : Bool) (n : ℕ) (N : NF) (r t : ℕ) : List HostItem :=
  arcItems li n N r ztml
    ztwjr

/-- The items written by the first `t` iterations of the arc loop. -/
def pre (li : Bool) (n : ℕ) (N : NF) (r t : ℕ) : List HostItem :=
  (List.range t).flatMap (arcIt li n N r)
theorem pre_succ (n : ℕ) (N : NF) (r t : ℕ) :
    pre li n N r ztbx = pre li n N r t ++ arcIt li n N r t := by
  simp [pre, List.range_succ, List.flatMap_append]
theorem pre_full (n : ℕ) (N : NF) (r : ℕ) :
    pre li n N r (N.region r).arcs.length = walkItems li n N r := rfl
theorem runItems_length_le (n : ℕ) (s e : WPos) : (runItems li n s e).length ≤ 1 := by
  zulcc
theorem arcItems_length_le (n : ℕ) (N : NF) (r jp j : ℕ) :
    (arcItems li n N r jp j).length ≤ 4 := by
  zumrp
  have := runItems_length_le li n (N.arc j).s (N.arc j).e
  grind
theorem pre_length_le (n : ℕ) (N : NF) (r t : ℕ) :
    (pre li n N r t).length ≤ 4 * t := by
  induction t with
  | zero => zuotz
  | succ t ih =>
    rw [pre_succ, List.length_append]
    have := arcItems_length_le li n N r ztml
      ztwjr
    unfold arcIt
    omega
theorem runCnt_lt {n : ℕ} (hn : 0 < n) (s e : WPos) : runCnt li n s e < n :=
  Nat.mod_lt _ hn
theorem ptsLen_runItems {n : ℕ} (_hn : 0 < n) (s e : WPos) :
    ptsLen n (runItems li n s e) = runCnt li n s e := by
  unfold runItems
  zumpw
  · tauto
  · zukyi
  · zukyi
theorem ptsLen_arcItems_le {n : ℕ} (hn : 0 < n) (N : NF) (r jp j : ℕ) :
    ptsLen n (arcItems li n N r jp j) ≤ n + 3 := by
  zumrp
  have h1 := ptsLen_runItems li hn (N.arc j).s (N.arc j).e
  have h2 := runCnt_lt li hn (N.arc j).s (N.arc j).e
  have h3 : ∀ x b, ptsLen n [ptI li n x b] = 1 := fun x b => ptsLen_pt n _
  split_ifs <;> simp only [ptsLen_append, h3, List.nil_append] <;> omega
theorem ptsLen_pre_le {n : ℕ} (hn : 0 < n) (N : NF) (r t : ℕ) :
    ptsLen n ztilu ≤ ztkbe * t := by
  induction t with
  | zero => simp [pre, ptsLen_nil]
  | succ t ih =>
    rw [pre_succ, ptsLen_append]
    have := ptsLen_arcItems_le li hn N r ztml
      ztwjr
    unfold arcIt
    zuewu
end
end DrvH
end Chazelle.Core
namespace Chazelle.Core
namespace DrvH
open Machine Machine.Stmt
@[expose] public section
def setupS : Stmt := block [
  .constN 215020 1, .inputSize 215021, .constN 215022 0, .constN 215023 3, .constN 215024 2,
  .constN 215033 3, .addN 215033 215000 215033, .loadN 215025 215033,
  .constN 215033 4, .addN 215033 215000 215033, .loadN 215026 215033,
  .constN 215033 5, .addN 215033 215000 215033, .loadN 215034 215033,
  .constN 215033 7, .addN 215033 215000 215033, .loadN 215027 215033,
  .addN 215033 215001 215001, .addN 215033 215033 215033, .addN 215033 215033 215001,
  .addN 215035 215034 215033, .loadN 215030 215035,
  .addN 215033 215035 215020, .loadN 215028 215033,
  .addN 215033 215033 215020, .loadN 215031 215033,
  .addN 215033 215033 215020, .loadN 215029 215033,
  .copyN 215032 9999, .copyN 215040 9999, .constN 215011 0, .constN 215012 0,
  .constN 215041 0]

/-! ## Emitting a point -/

/-- `215066 := qE li n e` for `e` in `215064`. -/
def qES : Stmt :=
  .ifLtN 215022 215002 (block [.copyN 215066 215064])
    (.seq (block [.addN 215069 215064 215020])
      (.ifLtN 215069 215021 (block [.subN 215066 215021 215064, .subN 215066 215066 215024])
        (block [.subN 215066 215021 215020])))

/-- Write the point item `(2, r215066, r215065 - 1)` at the write pointer. -/
def wrPt : Stmt := block [.subN 215068 215065 215020, .storeN 215040 215024,
  .addN 215069 215040 215020, .storeN 215069 215066, .addN 215069 215069 215020,
  .storeN 215069 215068, .addN 215040 215040 215023, .addN 215011 215011 215020,
  .addN 215012 215012 215020]

/-- **Emit the point** `ptE li n e h` (`e` in `215064`, `h` in `215065`). -/
def emitS : Stmt := .seq qES wrPt

/-! ## The run of an arc -/

/-- `215070 := ivB li n e.edge`. -/
def ivS : Stmt := .ifLtN 215022 215002 (block [.copyN 215070 215050])
  (block [.subN 215070 215021 215020, .subN 215070 215070 215050])

/-- `215071 := 0` if `atVtx` else `1`; `215072 :=` the edge of the end point. -/
def atS : Stmt := .seq (block [.subN 215076 215051 215020, .subN 215063 215076 215070,
    .subN 215076 215070 215076, .addN 215063 215063 215076])
  (.ifLtN 215063 215020
    (.seq (block [.constN 215071 0])
      (.ifLtN 215050 215020 (block [.subN 215072 215021 215020])
        (block [.subN 215072 215050 215020])))
    (block [.constN 215071 1, .copyN 215072 215050]))

/-- `215073 := runCnt`. -/
def rcS : Stmt := .seq (block [.addN 215073 215050 215071, .addN 215073 215073 215021,
    .subN 215073 215073 215020, .subN 215073 215073 215048])
  (.ifLtN 215073 215021 .skip (block [.subN 215073 215073 215021]))

/-- `215074 :=` the first vertex of the run. -/
def rsS : Stmt := .ifLtN 215022 215002
  (.seq (block [.addN 215074 215048 215020])
    (.ifLtN 215074 215021 .skip (block [.constN 215074 0])))
  (.seq (block [.addN 215074 215048 215073])
    (.seq (.ifLtN 215074 215021 .skip (block [.subN 215074 215074 215021]))
      (block [.subN 215076 215021 215020, .subN 215074 215076 215074])))

/-- Write the run item `(0, r215074, r215073 - 1)`. -/
def wrRun : Stmt := block [.subN 215075 215073 215020, .storeN 215040 215022,
  .addN 215069 215040 215020, .storeN 215069 215074, .addN 215069 215069 215020,
  .storeN 215069 215075, .addN 215040 215040 215023, .addN 215011 215011 215020,
  .addN 215012 215012 215073]

/-- **The run items** of the arc from `s` (`215048`) to `e` (`215050`, `215051`). -/
def runS : Stmt := .seq ivS (.seq atS (.seq rcS (.ifLtN 215073 215020 .skip (.seq rsS wrRun))))

/-! ## The partner of the end of the previous arc -/

/-- Test the chord at position `r215055` of the region's chord list. -/
def chTest : Stmt := .seq (block [
    .addN 215045 215029 215055, .addN 215045 215027 215045, .loadN 215056 215045,
    .addN 215045 215056 215056, .addN 215045 215045 215045, .addN 215045 215045 215056,
    .addN 215045 215025 215045,
    .loadN 215057 215045, .addN 215057 215057 215020,
    .addN 215045 215045 215020, .loadN 215058 215045, .addN 215045 215045 215020,
    .loadN 215059 215045,
    .subN 215060 215057 215047, .subN 215063 215047 215057, .addN 215060 215060 215063,
    .subN 215061 215058 215046, .subN 215063 215046 215058, .addN 215061 215061 215063,
    .addN 215061 215061 215060,
    .subN 215062 215059 215046, .subN 215063 215046 215059, .addN 215062 215062 215063,
    .addN 215062 215062 215060])
  (.ifLtN 215061 215020 (block [.copyN 215052 215059, .copyN 215053 215057, .constN 215054 1])
    (.ifLtN 215062 215020 (block [.copyN 215052 215058, .copyN 215053 215057, .constN 215054 1])
      .skip))

/-- One step of the partner search. -/
def chBody : Stmt := .seq (.ifLtN 215054 215020 chTest .skip) (block [.addN 215055 215055 215020])

/-- **The partner search**: `215052`, `215053` := `partner N r x` for `x` in `215046`, `215047`. -/
def partS : Stmt := .seq (block [.copyN 215052 215046, .copyN 215053 215047, .constN 215054 0,
  .constN 215055 0]) (.whileLtN 215055 215031 chBody)

/-! ## One arc -/

/-- Load the arcs `jp = arcs[t]`, `j = arcs[(t + 1) mod A]` and their ends. -/
def ldS : Stmt := .seq (block [.addN 215045 215028 215041, .addN 215045 215027 215045,
    .loadN 215043 215045, .addN 215042 215041 215020])
  (.seq (.ifLtN 215042 215030 .skip (block [.constN 215042 0]))
    (block [.addN 215045 215028 215042, .addN 215045 215027 215045, .loadN 215044 215045,
      .addN 215045 215043 215043, .addN 215045 215045 215045, .addN 215045 215045 215043,
      .addN 215045 215026 215045, .addN 215045 215045 215023, .loadN 215046 215045,
      .addN 215045 215045 215020, .loadN 215047 215045,
      .addN 215045 215044 215044, .addN 215045 215045 215045, .addN 215045 215045 215044,
      .addN 215045 215026 215045, .addN 215045 215045 215020, .loadN 215048 215045,
      .addN 215045 215045 215020, .loadN 215049 215045, .addN 215045 215045 215020,
      .loadN 215050 215045, .addN 215045 215045 215020, .loadN 215051 215045]))

/-- The junction point (if the partner is not the start of `j`). -/
def junS : Stmt := .seq (block [.subN 215060 215052 215048, .subN 215063 215048 215052,
    .addN 215060 215060 215063, .subN 215061 215053 215049, .subN 215063 215049 215053,
    .addN 215061 215061 215063, .addN 215060 215060 215061])
  (.ifLtN 215060 215020 .skip (.seq (block [.copyN 215064 215052, .copyN 215065 215053]) emitS))

/-- The start point of `j`. -/
def stS : Stmt := .seq (block [.copyN 215064 215048, .copyN 215065 215049]) emitS

/-- The end point of `j`. -/
def enS : Stmt := .seq (block [.copyN 215064 215072, .copyN 215065 215051]) emitS

/-- **One iteration of the arc loop.** -/
def arcBody : Stmt :=
  .seq ldS (.seq partS (.seq junS (.seq stS (.seq runS (.seq enS
    (block [.addN 215041 215041 215020]))))))

/-- **The arc loop.** -/
def arcLoop : Stmt := .whileLtN 215041 215030 arcBody

/-! ## The host -/

/-- The host handle after the buffer, the count word, the copy arguments. -/
def finS : Stmt := .seq (block [.copyN 215010 215040, .storeN 215010 215011,
    .addN 215082 215010 215020, .constN 215080 0])
  (.ifLtN 215022 215002 (block [.copyN 215081 215032, .copyN 215083 215023, .constN 215084 0])
    (block [.subN 215081 215040 215023, .constN 215083 0, .copyN 215084 215023]))

/-- Copy one item. -/
def cpyBody : Stmt := block [.loadN 215085 215081, .storeN 215082 215085,
  .addN 215086 215081 215020, .loadN 215085 215086, .addN 215086 215082 215020,
  .storeN 215086 215085,
  .addN 215086 215081 215024, .loadN 215085 215086, .addN 215086 215082 215024,
  .storeN 215086 215085,
  .addN 215082 215082 215023, .addN 215081 215081 215083, .subN 215081 215081 215084,
  .addN 215080 215080 215020]

/-- **The copy of the items** (reversed when `li = 0`). -/
def cpyLoop : Stmt := .whileLtN 215080 215011 cpyBody

/-- Raise the allocator to the end of the host. -/
def padLoopH : Stmt := .whileLtN 9999 215082 (block [.addN 9999 9999 215020])

/-- **The host RAM.** -/
def hostS : Stmt := .seq setupS (.seq arcLoop (.seq finS (.seq cpyLoop padLoopH)))

/-! ## Write sets -/
open BuildRam

/-- The registers of the host RAM (and the allocator). -/
def Ball (q : ℕ) : Bool := decide (215000 ≤ q ∧ q < 216000) || decide zttwz

/-- The registers written after the setup by the arc loop. -/
def Bdyn (q : ℕ) : Bool := decide ztkcs || decide ztkct ||
  decide ztnfs

/-- The registers `emitS` writes. -/
def Bem (q : ℕ) : Bool := decide ztkcs || decide ztkct || decide ztofc ||
  decide (215066 ≤ q ∧ q ≤ 215069)

/-- The registers `runS` writes. -/
def Brun (q : ℕ) : Bool := decide ztkcs || decide ztkct || decide ztofc ||
  decide ztofd || decide (215069 ≤ q ∧ q ≤ 215076)

/-- The registers `partS` writes. -/
def Bpart (q : ℕ) : Bool := decide zttwu || decide (215052 ≤ q ∧ q ≤ 215063)

/-- The registers `junS`, `stS`, `enS` write. -/
def Bjun (q : ℕ) : Bool := Bem q || decide (215060 ≤ q ∧ q ≤ 215065)

/-- The registers `ldS` writes. -/
def Bld (q : ℕ) : Bool := decide (215042 ≤ q ∧ q ≤ 215051)
theorem wrM_setupS : wrM Ball setupS = true := by_decide
theorem wrM_chBody : wrM Bpart chBody = true := by_decide
theorem wrM_ldS : wrM Bld ldS = true := by_decide
theorem wrM_hostS : wrM Ball hostS = true := by_decide
theorem wrM2_hostS : wrM2 Ball ztczi hostS = true := by_decide
open Programs DrvR
structure Kst (n : ℕ) (li : Bool) (d : Config) : Prop where
  one : d.nreg 215020 = 1
  nn : d.nreg 215021 = n
  zero : d.nreg 215022 = 0
  three : d.nreg 215023 = 3
  two : d.nreg 215024 = 2
  li : d.nreg 215002 = if li then 1 else 0
section exec
variable {P : Polygon} {W : ℕ}
variable (d : Config)
theorem qES_exec (hw : WordsBounded W d) {li : Bool} {n e : ℕ} (hK : Kst n li d)
    (h64 : d.nreg 215064 = e) (hW : e + 1 ≤ W) :
    ∃ d' k, Exec P W qES d d' k ∧ k ≤ 6 ∧ d'.nreg 215066 = qE li n e ∧ d'.nmem = d.nmem ∧
      FrameM (fun q => decide (q = 215066) || decide zttwx) d d' := by
  obtain ⟨d', k, ex, hk, h66, hm⟩ : ∃ d' k, Exec P W qES d d' k ∧ k ≤ 6 ∧
      d'.nreg 215066 = qE li n e ∧ d'.nmem = d.nmem := by
    unfold qES
    cases li with
    | true =>
      zujfi
      exec_block
      refine ztbcd
      config_simp
      rw [h64]; rfl
    | false =>
      zujff
      refine spec_seq ?_
      exec_block
      · rw [h64, hK.one]; omega
      by_cases hlt : e + 1 < n
      · refine spec_ifLtN_true (by config_simp; rw [h64, hK.one, hK.nn]; omega) ?_
        exec_block
        refine ztbcd
        config_simp
        rw [hK.nn, h64, hK.two]
        simp only [qE, hlt, ↓reduceIte, Bool.false_eq_true, ↓reduceIte]
        omega
      · refine spec_ifLtN_false (by config_simp; rw [h64, hK.one, hK.nn]; omega) ?_
        exec_block
        refine ztbcd
        config_simp
        rw [hK.nn, hK.one]
        simp only [qE, hlt, ↓reduceIte, Bool.false_eq_true]
  exact ⟨d', k, ex, hk, h66, hm, exec_frameM ex by_decide⟩

/-- The buffer: items `xs` at `T`, the write pointer after them, the item and point counts. -/
def Buf (n T : ℕ) (xs : List HostItem) (d : Config) : Prop :=
  ItemsAt d.nmem T xs ∧ d.nreg 215040 = T + 3 * xs.length ∧ d.nreg 215011 = xs.length ∧
    d.nreg 215012 = ptsLen n xs
theorem emitS_exec (hw : WordsBounded W d) {li : Bool} {n e h T : ℕ}
    {xs : List HostItem} (hK : Kst n li d) (h64 : d.nreg 215064 = e) (h65 : d.nreg 215065 = h)
    (hB : Buf n T xs d) (hW1 : T + 3 * xs.length + 3 ≤ W) (hW2 : ptsLen n xs + 1 ≤ W)
    (hW3 : e + 1 ≤ W) :
    ∃ d' k, Exec P W emitS d d' k ∧ k ≤ 15 ∧ Buf n T ztkya d' ∧
      ztgrz ∧ FrameM Bem d d' := by
  zufjf
  obtain ⟨d₁, k₁, e₁, hk₁, q66, qm, qf⟩ := qES_exec (P := P) d hw hK h64 hW3
  have g : ∀ q, (decide _ || decide _) = false → d₁.nreg q = d.nreg q :=
    qf.1
  have r20 : d₁.nreg 215020 = 1 := by rw [g _ by_decide, hK.one]
  have r24 : d₁.nreg 215024 = 2 := by rw [g _ by_decide, hK.two]
  have r23 : d₁.nreg 215023 = 3 := by rw [g _ by_decide, hK.three]
  have r65 : d₁.nreg 215065 = h := by_simp_all
  have r40 : d₁.nreg 215040 = T + 3 * xs.length := by_simp_all
  have r11 : d₁.nreg 215011 = xs.length := by_simp_all
  have r12 : d₁.nreg 215012 = ptsLen n xs := by_simp_all
  zuka
  obtain ⟨d', k₂, e₂, hk₂, hm', p40, p11, p12⟩ : ∃ d' k₂, Exec P W wrPt d₁ d' k₂ ∧ k₂ = 9 ∧
      d'.nmem = wr3 d₁.nmem ztjnd 2 ztlsa zthhn ∧
      d'.nreg 215040 = T + 3 * xs.length + 3 ∧ d'.nreg 215011 = xs.length + 1 ∧
      d'.nreg 215012 = ptsLen n xs + 1 := by
    unfold wrPt
    exec_block
    all_goals try (config_simp; (try zundm); omega)
    refine ztboc <;> config_simp <;>
      zundm
    rfl
  refine ⟨d', k₁ + k₂, .seq e₁ e₂, by_omega, ztfh, fun a ha => ?_, ?_⟩
  · rw [hm', qm]
    exact hI.snoc _
  · grind
  · simp_all
  · rw [p12, ptsLen_append, ptE, ptsLen_pt]
  · rw [hm', wr3_lt ha, qm]
  · exact (qf.mono (fun q hq => by simp only [Bem, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega)).trans
      (exec_frameM e₂ by_decide)
theorem mod_prev {e n : ℕ} (he : e < n) : (e + n - 1) % n = if e < 1 then n - 1 else e - 1 := by
  zus
  · simp_all
  · rw [show e + n - 1 = (e - 1) + n by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt by_omega
theorem mod_once {v n : ℕ} (hv : v < 2 * n) : v % n = if v < n then v else v - n := by
  zus
  · zubql
  · rw [Nat.mod_eq_sub_mod by_omega]; exact Nat.mod_eq_of_lt by_omega
theorem ivS_exec (hw : WordsBounded W d) {li : Bool} {n ee : ℕ} (hK : Kst n li d)
    (h50 : d.nreg 215050 = ee) :
    ∃ d' k, Exec P W ivS d d' k ∧ k ≤ 4 ∧ d'.nreg 215070 = ivB li n ee ∧ d'.nmem = d.nmem ∧
      FrameM (fun q => decide (q = 215070)) d d' := by
  obtain ⟨d', k, ex, hk, h1, hm⟩ : ∃ d' k, Exec P W ivS d d' k ∧ k ≤ 4 ∧
      d'.nreg 215070 = ivB li n ee ∧ d'.nmem = d.nmem := by
    unfold ivS
    cases li with
    | true =>
      zujfi
      exec_block
      refine ztbcd
      config_simp; zunjx; rfl
    | false =>
      zujff
      exec_block
      refine ztbcd
      config_simp; rw [hK.nn, hK.one, h50]; rfl
  exact ztdjd
theorem atS_exec (hw : WordsBounded W d) {li : Bool} {n ee eh iv : ℕ}
    (hK : Kst n li d) (h50 : d.nreg 215050 = ee) (h51 : d.nreg 215051 = eh)
    (h70 : d.nreg 215070 = iv) :
    ∃ d' k, Exec P W atS d d' k ∧ k ≤ 10 ∧
      d'.nreg 215071 = ztkwm ∧
      d'.nreg 215072 = zteto ∧
      d'.nmem = d.nmem ∧
      FrameM (fun q => decide ztofd || decide (q = 215071) || decide (q = 215072) ||
        decide zttwy) d d' := by
  have b51 := hw.1 215051
  have b70 := hw.1 215070
  obtain ⟨d', k, ex, hk, h1, h2, hm⟩ : ∃ d' k, Exec P W atS d d' k ∧ k ≤ 10 ∧
      d'.nreg 215071 = ztkwm ∧
      d'.nreg 215072 = zteto ∧
      d'.nmem = d.nmem := by
    unfold atS
    refine spec_seq ?_
    exec_block
    · config_simp; omega
    by_cases hv : eh - 1 = iv
    · refine spec_ifLtN_true (by config_simp; rw [h51, hK.one, h70]; omega) ?_
      refine spec_seq ?_
      exec_block
      · omega
      by_cases h0 : ee < 1
      · refine spec_ifLtN_true (by config_simp; rw [h50, hK.one]; omega) ?_
        exec_block
        refine zthmk <;> config_simp <;> simp only [hv, h0, ↓reduceIte, hK.nn, hK.one]
      · refine spec_ifLtN_false (by config_simp; rw [h50, hK.one]; omega) ?_
        exec_block
        refine zthmk <;> config_simp <;>
          simp only [hv, h0, ↓reduceIte, ↓reduceIte, hK.one, h50]
    · refine spec_ifLtN_false (by config_simp; rw [h51, hK.one, h70]; omega) ?_
      exec_block
      · omega
      refine zthmk <;> config_simp <;> simp only [hv, ↓reduceIte, h50]
  exact ⟨d', k, ex, hk, h1, h2, hm, exec_frameM ex by_decide⟩
theorem rcS_exec (hw : WordsBounded W d) {li : Bool} {n ee se δ : ℕ}
    (hK : Kst n li d) (h50 : d.nreg 215050 = ee) (h71 : d.nreg 215071 = δ)
    (h48 : d.nreg 215048 = se) (hee : ee < n) (hse : se < n) (hδ : δ ≤ 1) (hW : 2 * n + 1 ≤ W) :
    ∃ d' k, Exec P W rcS d d' k ∧ k ≤ 7 ∧ d'.nreg 215073 = ztlnl % n ∧
      d'.nmem = d.nmem ∧ FrameM (fun q => decide (q = 215073)) d d' := by
  obtain ⟨d', k, ex, hk, h1, hm⟩ : ∃ d' k, Exec P W rcS d d' k ∧ k ≤ 7 ∧
      d'.nreg 215073 = ztlnl % n ∧ d'.nmem = d.nmem := by
    have hm := mod_once (v := ee + δ + n - 1 - se) (n := n) by_omega
    unfold rcS
    refine spec_seq ?_
    exec_block
    · omega
    · config_simp; rw [h50, h71, hK.nn]; omega
    by_cases hv : ee + δ + n - 1 - se < n
    · refine spec_ifLtN_true (by config_simp; rw [h50, h71, hK.nn, hK.one, h48]; exact hv) ?_
      zugas
      config_simp; simp only [h50, h71, hK.nn, hK.one, h48, hm, hv, ↓reduceIte]
    · refine spec_ifLtN_false (by config_simp; rw [h50, h71, hK.nn, hK.one, h48]; exact hv) ?_
      exec_block
      refine ztbcd
      config_simp; simp only [h50, h71, hK.nn, hK.one, h48, hm, hv, ↓reduceIte]
  exact ztdjd
theorem rsS_exec (hw : WordsBounded W d) {li : Bool} {n se rc : ℕ}
    (hK : Kst n li d) (h48 : d.nreg 215048 = se) (h73 : d.nreg 215073 = rc) (hse : se < n)
    (hrc : rc < n) (hW : 2 * n + 1 ≤ W) :
    ∃ d' k, Exec P W rsS d d' k ∧ k ≤ 9 ∧
      d'.nreg 215074 = ztezv ∧
      d'.nmem = d.nmem ∧ FrameM (fun q => decide (q = 215074) || decide zttwy) d d' := by
  obtain ⟨d', k, ex, hk, h1, hm⟩ : ∃ d' k, Exec P W rsS d d' k ∧ k ≤ 9 ∧
      d'.nreg 215074 = ztezv ∧ d'.nmem = d.nmem := by
    unfold rsS
    cases li with
    | true =>
      zujfi
      refine spec_seq ?_
      exec_block
      · rw [h48, hK.one]; omega
      by_cases hv : se + 1 < n
      · refine spec_ifLtN_true (by config_simp; rw [h48, hK.one, hK.nn]; exact hv) ?_
        zugas
        config_simp; simp only [h48, hK.one, ↓reduceIte, Nat.mod_eq_of_lt hv]
      · refine spec_ifLtN_false (by config_simp; rw [h48, hK.one, hK.nn]; exact hv) ?_
        exec_block
        · omega
        refine ztbcd
        config_simp; simp only [↓reduceIte, show se + 1 = n by omega, Nat.mod_self]
    | false =>
      have hm := mod_once (v := se + rc) (n := n) by_omega
      zujff
      refine spec_seq ?_
      exec_block
      · omega
      zujl
      by_cases hv : se + rc < n
      · refine spec_ifLtN_true (by config_simp; rw [h48, h73, hK.nn]; exact hv) ?_
        zurc
        exec_block
        refine ztbcd
        config_simp; simp only [h48, h73, hK.nn, hK.one, Bool.false_eq_true, ↓reduceIte, hm, hv]
      · refine spec_ifLtN_false (by config_simp; rw [h48, h73, hK.nn]; exact hv) ?_
        exec_block
        refine ztbcd
        config_simp; simp only [h48, h73, hK.nn, hK.one, Bool.false_eq_true, ↓reduceIte, hm, hv]
  exact ztdjd
theorem Kst.frame {n : ℕ} {li : Bool} {d d' : Config} (h : Kst n li d) {B : ℕ → Bool}
    (hf : FrameM B d d')
    (hB : B 215002 = false ∧ B 215020 = false ∧ B 215021 = false ∧ B 215022 = false ∧
      B 215023 = false ∧ B 215024 = false) : Kst n li d' :=
  ⟨(hf.1 _ hB.2.1).trans h.one, (hf.1 _ hB.2.2.1).trans h.nn, (hf.1 _ hB.2.2.2.1).trans h.zero,
    (hf.1 _ hB.2.2.2.2.1).trans h.three, (hf.1 _ hB.2.2.2.2.2).trans h.two,
    (hf.1 _ hB.1).trans h.li⟩
theorem Buf.frame {n T : ℕ} {xs : List HostItem} {d d' : Config} (h : Buf n T xs d)
    {B : ℕ → Bool} (hf : FrameM B d d')
    (hB : B 215040 = false ∧ B 215011 = false ∧ B 215012 = false) (hm : d'.nmem = d.nmem) :
    Buf n T xs d' :=
  ⟨hm ▸ h.1, (hf.1 _ hB.1).trans h.2.1, (hf.1 _ hB.2.1).trans h.2.2.1,
    (hf.1 _ hB.2.2).trans h.2.2.2⟩
theorem wrRun_exec (hw : WordsBounded W d) {li : Bool} {n a rc T : ℕ}
    {xs : List HostItem} (hK : Kst n li d) (h73 : d.nreg 215073 = rc) (h74 : d.nreg 215074 = a)
    (hrc : 1 ≤ rc) (hB : Buf n T xs d) (hW1 : T + 3 * xs.length + 3 ≤ W)
    (hW2 : ptsLen n xs + rc ≤ W) :
    ∃ d' k, Exec P W wrRun d d' k ∧ k = 9 ∧ Buf n T (xs ++ [.run a zttyi]) d' ∧
      ztdbg ∧
      FrameM (fun q => decide ztkcs || decide ztkct || decide ztofc ||
        decide zttwx || decide (q = 215075)) d d' := by
  zufjf
  obtain ⟨d', k, ex, hk, hm', p40, p11, p12⟩ : ∃ d' k, Exec P W wrRun d d' k ∧ k = 9 ∧
      d'.nmem = wr3 d.nmem ztjnd 0 a zttyi ∧
      d'.nreg 215040 = T + 3 * xs.length + 3 ∧ d'.nreg 215011 = xs.length + 1 ∧
      d'.nreg 215012 = ptsLen n xs + rc := by
    unfold wrRun
    exec_block
    all_goals
      try (config_simp; (try zundn); omega)
    refine ztboc <;> config_simp <;>
      zundn
    rfl
  refine ⟨d', k, ex, hk, ztfh, fun x hx => ?_, exec_frameM ex by_decide⟩
  · rw [hm']; exact hI.snoc _
  · grind
  · simp_all
  · rw [p12, ptsLen_append, ptsLen_run]; omega
  · rw [hm', wr3_lt hx]
theorem runItems_of_ne {li : Bool} {n : ℕ} {s e : WPos} (h : runCnt li n s e ≠ 0) :
    runItems li n s e = [.run (if li then zttzp % n
      else n - 1 - ztohl % n) (runCnt li n s e - 1)] := by
  unfold runItems; grind
theorem runCnt_eq (li : Bool) (n : ℕ) (s e : WPos) :
    runCnt li n s e = (e.edge + (if e.hgt - 1 = ivB li n e.edge then 0 else 1) + n - 1 - s.edge) % n := by
  unfold runCnt atVtx; simp
theorem runS_exec (hw : WordsBounded W d) {li : Bool} {n T : ℕ} {s e : WPos}
    {xs : List HostItem} (hK : Kst n li d) (h48 : d.nreg 215048 = s.edge)
    (h50 : d.nreg 215050 = e.edge) (h51 : d.nreg 215051 = e.hgt) (hs : s.edge < n)
    (he : e.edge < n) (hB : Buf n T xs d) (hW1 : T + 3 * xs.length + 3 ≤ W)
    (hW2 : ptsLen n xs + n ≤ W) (hW3 : 2 * n + 1 ≤ W) :
    ∃ d' k, Exec P W runS d d' k ∧ k ≤ 45 ∧ Buf n T (xs ++ runItems li n s e) d' ∧
      d'.nreg 215072 = ztgkj ∧
      ztgrz ∧ FrameM Brun d d' := by
  zuqi
  obtain ⟨d₁, k₁, e₁, hk₁, v70, m₁, f₁⟩ := ivS_exec (P := P) d hw hK h50
  zujwc
  zuepl
  obtain ⟨d₂, k₂, e₂, hk₂, v71, v72, m₂, f₂⟩ := atS_exec (P := P) d₁ e₁.wb_right K₁
    (by rw [f₁.1 _ by_decide, h50]) (by rw [f₁.1 _ by_decide, h51]) v70
  zuepm

  obtain ⟨d₃, k₃, e₃, hk₃, v73, m₃, f₃⟩ := rcS_exec (P := P) d₂ e₂.wb_right K₂
    (by rw [f₂.1 _ by_decide, f₁.1 _ by_decide, h50]) v71
    (by rw [f₂.1 _ by_decide, f₁.1 _ by_decide, h48]) he hs (by split_ifs <;> omega) hW3
  zujwd
  have B₃ := B₂.frame f₃ by_decide m₃
  rw [← runCnt_eq] at v73
  have hrc := runCnt_lt li hn s e
  have v72' : d₃.nreg 215072 = ztgkj := by
    rw [f₃.1 _ by_decide, v72, mod_prev he]
    unfold atVtx; simp
  have f₁₃ : FrameM Brun d d₃ := ((f₁.mono (fun q hq => by
    simp only [Brun, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega)).trans (f₂.mono
    ztcnh)).trans
    (f₃.mono ztcnh)
  have hm₁₃ : ztpoi := by_simp_all
  by_cases h0 : runCnt li n s e = 0
  · have hr : runItems li n s e = [] := by unfold runItems; simp_all
    refine ⟨d₃, k₁ + (k₂ + (k₃ + ztbgo)), .seq e₁ (.seq e₂ (.seq e₃
      (.ifLtN_true (by rw [v73, K₃.one, h0]; omega) ztjdx))), by_omega,
      by simp_all, v72', by_simp_all, f₁₃⟩
  · obtain ⟨d₄, k₄, e₄, hk₄, v74, m₄, f₄⟩ := rsS_exec d₃ e₃.wb_right K₃
      (by rw [f₃.1 _ by_decide, f₂.1 _ by_decide, f₁.1 _ by_decide, h48]) v73 hs hrc hW3
    zujwe
    have B₄ := B₃.frame f₄ by_decide m₄
    obtain ⟨d₅, k₅, e₅, hk₅, B₅, m₅, f₅⟩ := wrRun_exec d₄ e₄.wb_right K₄
      (by rw [f₄.1 _ by_decide, v73]) v74 by_omega B₄ hW1 by_omega
    refine ⟨d₅, k₁ + (k₂ + (k₃ + (ztjzr + 2))), .seq e₁ (.seq e₂ (.seq e₃
      (.ifLtN_false (by rw [v73, K₃.one]; omega) ztgxe))), by_omega, ?_, ?_,
      fun a ha => ?_, ?_⟩
    · rw [runItems_of_ne h0]; exact B₅
    · rw [f₅.1 _ by_decide, f₄.1 _ by_decide, v72']
    · grind
    · exact (f₁₃.trans (f₄.mono (fun q hq => by
        simp only [Brun, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega))).trans
        (f₅.mono ztcnh)
end exec
end
end DrvH
end Chazelle.Core
namespace Chazelle.Core
namespace DrvH
open Machine Machine.Stmt Programs BuildRam DrvR
@[expose] public section
section exec
variable {P : Polygon} {W : ℕ}
theorem lpos_eq_iff {c : CRec} {x : WPos} : c.lpos = x ↔ c.lp = x.edge ∧ c.h + 1 = x.hgt := by
  cases x; zuovm
theorem rpos_eq_iff {c : CRec} {x : WPos} : c.rpos = x ↔ c.rp = x.edge ∧ c.h + 1 = x.hgt := by
  cases x; zuovn
variable (d : Config)
theorem chTest_exec (hw : WordsBounded W d) {li : Bool} {n : ℕ} {N : NF} {x : WPos}
    {i v : ℕ} (hK : Kst n li d) (h46 : d.nreg 215046 = x.edge) (h47 : d.nreg 215047 = x.hgt)
    (h55 : d.nreg 215055 = v) (hi : d.nmem ztyen = i)
    (hiW : d.nreg 215027 + zteew ≤ W)
    (hh : d.nmem ztijd = (N.chord i).h)
    (hlp : d.nmem ztgie = (N.chord i).lp)
    (hrp : d.nmem ztgif = (N.chord i).rp)
    (hcW : d.nreg 215025 + 5 * i + 2 ≤ W) (hxe : x.edge < n) (hxh : x.hgt ≤ n)
    (hl : (N.chord i).lp < n) (hr : (N.chord i).rp < n) (hhn : (N.chord i).h + 1 ≤ n)
    (hW : 4 * n + 4 ≤ W) :
    ∃ d' k, Exec P W chTest d d' k ∧ k ≤ 30 ∧
      (if (N.chord i).lpos = x then
        d'.nreg 215052 = (N.chord i).rpos.edge ∧ d'.nreg 215053 = (N.chord i).rpos.hgt ∧
          d'.nreg 215054 = 1
      else if (N.chord i).rpos = x then
        d'.nreg 215052 = (N.chord i).lpos.edge ∧ d'.nreg 215053 = (N.chord i).lpos.hgt ∧
          d'.nreg 215054 = 1
      else d'.nreg 215052 = d.nreg 215052 ∧ d'.nreg 215053 = d.nreg 215053 ∧
        d'.nreg 215054 = d.nreg 215054) ∧
      d'.nmem = d.nmem ∧ FrameM (fun q => decide zttwu || decide (215052 ≤ q ∧ q ≤ 215054) ||
        decide (215056 ≤ q ∧ q ≤ 215063)) d d' := by

  have e5 : ∀ a b : ℕ, a + ztjoc = a + 5 * b := fun a b => by_ring
  obtain ⟨d', k, ex, hk, hpost, hm⟩ : ∃ d' k, Exec P W chTest d d' k ∧ k ≤ 30 ∧
      (if (N.chord i).lpos = x then
        d'.nreg 215052 = (N.chord i).rpos.edge ∧ d'.nreg 215053 = (N.chord i).rpos.hgt ∧
          d'.nreg 215054 = 1
      else if (N.chord i).rpos = x then
        d'.nreg 215052 = (N.chord i).lpos.edge ∧ d'.nreg 215053 = (N.chord i).lpos.hgt ∧
          d'.nreg 215054 = 1
      else d'.nreg 215052 = d.nreg 215052 ∧ d'.nreg 215053 = d.nreg 215053 ∧
        d'.nreg 215054 = d.nreg 215054) ∧ d'.nmem = d.nmem := by
    unfold chTest
    refine spec_seq ?_
    exec_block
    all_goals try (config_simp; (try simp only [h55, hi, hK.one, e5, hh, hlp, hrp, h46, h47]); omega)
    by_cases hL : (N.chord i).lpos = x
    · have hL' := lpos_eq_iff.1 hL
      refine spec_ifLtN_true (by config_simp; simp only [h55, hi, hK.one, e5, hh, hlp, h46, h47]; omega) ?_
      exec_block
      · omega
      refine ztbcd
      zuckr
      refine ztcg <;> config_simp <;>
        (try simp only [h55, hi, hK.one, e5, hh, hrp]) <;> rfl
    · have hL' : ¬ ((N.chord i).lp = x.edge ∧ (N.chord i).h + 1 = x.hgt) := fun h => hL (lpos_eq_iff.2 h)
      refine spec_ifLtN_false (by config_simp; simp only [h55, hi, hK.one, e5, hh, hlp, h46, h47]; omega) ?_
      by_cases hR : (N.chord i).rpos = x
      · have hR' := rpos_eq_iff.1 hR
        refine spec_ifLtN_true (by config_simp; simp only [h55, hi, hK.one, e5, hh, hrp, h46, h47]; omega) ?_
        exec_block
        · omega
        refine ztbcd
        zugzi
        refine ztcg <;> config_simp <;>
          (try simp only [h55, hi, hK.one, e5, hh, hlp]) <;> rfl
      · have hR' : ¬ ((N.chord i).rp = x.edge ∧ (N.chord i).h + 1 = x.hgt) := fun h => hR (rpos_eq_iff.2 h)
        refine spec_ifLtN_false (by config_simp; simp only [h55, hi, hK.one, e5, hh, hrp, h46, h47]; omega) ?_
        zugas
        zugzi
        simp
  exact ⟨d', k, ex, hk, hpost, hm, exec_frameM ex by_decide⟩

/-- The search predicate of `partner`. -/
def pmatch (N : NF) (x : WPos) (i : ℕ) : Bool := decide ztdee

/-- The result of the partner search for a search outcome. -/
def resOf (N : NF) (x : WPos) : Option ℕ → WPos
  | some i => if (N.chord i).lpos = x then (N.chord i).rpos else (N.chord i).lpos
  | none => x
theorem partner_eq (N : NF) (r : ℕ) (x : WPos) :
    partner N r x = resOf N x ((N.region r).chords.find? ztdvq) := by
  rfl
theorem find_take_succ {l : List ℕ} {p : ℕ → Bool} {v : ℕ} (hv : v < l.length) :
    (l.take ztsp).find? p =
      ((l.take v).find? p).or (if p zttrq then some zttrq else none) := by
  rw [List.take_add_one, List.find?_append, List.getElem?_eq_getElem hv, Option.toList_some,
    List.find?_singleton, List.getD_eq_getElem _ _ hv]
set_option maxHeartbeats 1000000 in
/-- **The partner search.** -/
theorem partS_exec (hw : WordsBounded W d) {li : Bool} {n : ℕ} {N : NF} {r : ℕ}
    {x : WPos} (hK : Kst n li d) (hF : HFacts n N r)
    (h46 : d.nreg 215046 = x.edge) (h47 : d.nreg 215047 = x.hgt) (hxe : x.edge < n)
    (hxh : x.hgt ≤ n) (h31 : d.nreg 215031 = (N.region r).chords.length)
    (hch : ∀ v, v < (N.region r).chords.length →
      d.nmem ztyen = (N.region r).chords.getD v 0 ∧
      d.nreg 215027 + zteew ≤ W)
    (hrec : ∀ i, i < N.nChords → d.nmem ztijd = (N.chord i).h ∧
      d.nmem ztgie = (N.chord i).lp ∧
      d.nmem ztgif = (N.chord i).rp ∧ d.nreg 215025 + 5 * i + 2 ≤ W)
    (hW : 4 * n + 4 ≤ W) :
    ∃ d' k, Exec P W partS d d' k ∧ k ≤ 150 ∧ d'.nreg 215052 = (partner N r x).edge ∧
      d'.nreg 215053 = (partner N r x).hgt ∧ d'.nmem = d.nmem ∧ FrameM Bpart d d' := by
  set cs := (N.region r).chords with hcs
  have hKc : cs.length ≤ 4 := hF.hK
  -- initialisation
  obtain ⟨d₀, k₀, e₀, hk₀, a52, a53, a54, a55, m₀, f₀⟩ : ∃ d₀ k₀, Exec P W
      ztfxx
      d d₀ k₀ ∧ k₀ = 4 ∧ d₀.nreg 215052 = x.edge ∧ d₀.nreg 215053 = x.hgt ∧ d₀.nreg 215054 = 0 ∧
      d₀.nreg 215055 = 0 ∧ d₀.nmem = d.nmem ∧ FrameM Bpart d d₀ := by
    obtain ⟨d₀, k₀, e₀, hk₀, a52, a53, a54, a55, m₀⟩ : ∃ d₀ k₀, Exec P W
        ztfxx
        d d₀ k₀ ∧ k₀ = 4 ∧ d₀.nreg 215052 = x.edge ∧ d₀.nreg 215053 = x.hgt ∧
        d₀.nreg 215054 = 0 ∧ d₀.nreg 215055 = 0 ∧ d₀.nmem = d.nmem := by
      exec_block
      · omega
      · omega
      simp_all
    exact ⟨d₀, k₀, e₀, hk₀, a52, a53, a54, a55, m₀, exec_frameM e₀ by_decide⟩
  -- the loop
  let Inv : ℕ → Config → Prop := fun v e => WordsBounded W e ∧ e.nreg 215055 = v ∧
    e.nreg 215031 = cs.length ∧
    e.nreg 215052 = (resOf N x ztynl).edge ∧
    e.nreg 215053 = (resOf N x ztynl).hgt ∧
    e.nreg 215054 = (if ((cs.take v).find? ztdvq).isSome then 1 else 0) ∧
    FrameM Bpart d e ∧ e.nmem = d.nmem
  obtain ⟨d', k, ex, ⟨w', -, -, v52, v53, -, f', m'⟩, hk⟩ := DrvR.forLoop (P := P) (W := W)
    (ir := 215055) (nr := 215031) Inv 33 cs.length
    (fun v e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun v e hv ⟨hwe, e55, e31, e52, e53, e54, fe, me⟩ => by
      have g : ∀ q, Bpart q = false → e.nreg q = d.nreg q := fe.1
      have Ke : Kst n li e := hK.frame fe by_decide
      have hfs := find_take_succ (p := pmatch N x) hv
      have hmem : cs.getD v 0 ∈ cs := by
        simp_all
      obtain ⟨hi1, hil, hir, hih⟩ := hF.hch _ hmem
      have Ke' : e.nreg 215020 = 1 := Ke.one
      obtain ⟨e', k, ex, hk, p55, p52, p53, p54, pm⟩ : ∃ e' k, Exec P W chBody e e' k ∧ k ≤ 33 ∧
          e'.nreg 215055 = v + 1 ∧
          e'.nreg 215052 = (resOf N x ztynm).edge ∧
          e'.nreg 215053 = (resOf N x ztynm).hgt ∧
          e'.nreg 215054 = (if ((cs.take ztsp).find? ztdvq).isSome then 1 else 0) ∧
          e'.nmem = e.nmem := by
        unfold chBody
        zujl
        cases hfound : (cs.take v).find? ztdvq with
        | some i₀ =>
          zuiju
          simp only [Option.isSome_some, ↓reduceIte] at e54
          zubv
          refine spec_skip hwe ?_
          exec_block
          · omega
          rw [hfs, hfound, Option.some_or]
          refine ⟨by_omega, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp
          · omega
          · omega
          · omega
          · simp_all
        | none =>
          zuiju
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, resOf] at e52 e53 e54
          zudd
          set i := cs.getD v 0 with hidef
          obtain ⟨r1, r2, r3, r4⟩ := hrec i hi1
          obtain ⟨c1, c2⟩ := hch v hv
          have t46 : e.nreg 215046 = x.edge := by rw [g _ by_decide, h46]
          have t47 : e.nreg 215047 = x.hgt := by rw [g _ by_decide, h47]
          have t27 : e.nreg 215027 = d.nreg 215027 := g _ by_decide
          have t29 : e.nreg 215029 = d.nreg 215029 := g _ by_decide
          have t25 : e.nreg 215025 = d.nreg 215025 := g _ by_decide
          have ti : e.nmem (e.nreg 215027 + ztroy) = i := by_simp_all
          have tiW : e.nreg 215027 + ztroy ≤ W := by_omega
          have th : e.nmem (e.nreg 215025 + 5 * i) = (N.chord i).h := by_simp_all
          have tl : e.nmem (e.nreg 215025 + 5 * i + 1) = (N.chord i).lp := by_simp_all
          have tr : e.nmem (e.nreg 215025 + 5 * i + 2) = (N.chord i).rp := by_simp_all
          have tW : e.nreg 215025 + 5 * i + 2 ≤ W := by_omega
          refine spec_use (chTest_exec (P := P) e hwe Ke t46 t47 e55 ti tiW th tl tr tW hxe hxh
            hil hir hih hW) ?_
          intro c₁ k₁ hk₁ hw₁ ⟨hpost, hm₁, hf₁⟩
          have q55 : c₁.nreg 215055 = v := by rw [hf₁.1 _ by_decide, e55]
          have q20 : c₁.nreg 215020 = 1 := by rw [hf₁.1 _ by_decide, Ke']
          exec_block
          · omega
          rw [hfs, hfound, Option.none_or]
          refine ztbfj <;> config_simp
          · omega
          all_goals by_cases hL : (N.chord i).lpos = x <;> by_cases hR : (N.chord i).rpos = x <;>
            simp only [hL, hR, ↓reduceIte] at hpost <;>
            simp only [pmatch, hL, hR, or_true, or_false, decide_true, decide_false,
              ↓reduceIte, resOf, Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
              hpost.1, hpost.2.1, hpost.2.2, e52, e53, e54, hm₁]
      have fe' := exec_frameM ex wrM_chBody
      exact ⟨e', k, ex, ⟨ex.wb_right, p55, by rw [fe'.1 _ by_decide, e31], p52, p53, p54,
        fe.trans fe', pm.trans me⟩, hk⟩)
    (j := 0) ⟨e₀.wb_right, a55, by rw [f₀.1 _ by_decide, h31], by_tauto,
      by tauto, by_simp_all, f₀, m₀⟩ (Nat.zero_le _)
  refine ⟨d', k₀ + k, .seq e₀ ex, by_omega, ?_, ?_, m', f'⟩
  · rw [v52, List.take_length, partner_eq]
  · rw [v53, List.take_length, partner_eq]
