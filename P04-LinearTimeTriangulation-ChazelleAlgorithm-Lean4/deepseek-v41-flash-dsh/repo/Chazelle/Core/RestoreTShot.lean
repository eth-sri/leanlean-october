module

public import Chazelle.Golf

public import Chazelle.Core.RestoreTHoles
public import Chazelle.Core.RestoreTXCmp
public import Chazelle.Core.DownPhaseOracleHit
public import Chazelle.Core.SweepPrimArr
public import Chazelle.Core.RestoreTChainLeft
public import Chazelle.Core.DownPhaseDropWt
public import Chazelle.Core.ShotListGMain

/-!
# WP-E, the candidate test on the RAM: the shot

The candidate test shoots from the candidate `x` with the model-generic wrapper
`ShotListG.shotListG gKey xcR sh RS0` over the arc array of the region (`arcBuild`), cut by the
holes of the candidate (`holeS`).  This file establishes the wrapper's precondition `ShotPreG`
from the run state.

* `innerPt_mi_edge`: a point strictly inside an edge of the interior walk of a polygon with
  distinct heights is an inner point of the interior model.
* `tArr_rs`: the arrival step.  The shooter returns *some* proper position of the hit point; in a
  chain model a point of the chain has a position on each side of the chain, and the chord of the
  test is attached only at the one whose left sector the ray arrives in.  In a chain model the
  test replaces the returned position by the arrival position (the primitive
  `SweepPrim.arrivalPos`); in the interior model (a simple walk) the position is unique.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK NFLoc ShotList ShotListG
open Chazelle.Geometry (lerp)

/-! ## Inner points of the interior model -/

theorem iv_inj {Q : Polygon} {p q : ℕ} (hp : p < Q.n) (hq : q < Q.n) (h : IOrc.iv Q p = IOrc.iv Q q) :
    p = q := by
  unfold IOrc.iv at h; split_ifs at h <;> omega

/-- **A point strictly inside an edge of the interior walk is an inner point** of the interior
model, when `Q` has distinct heights: its height is strictly between the heights of the edge's
ends, and its abscissa between theirs. -/
theorem innerPt_mi_edge {Q : Polygon} (hD : DistinctHeights Q) (hn : 3 ≤ Q.n) {p h : ℕ}
    (hp : p < Q.n) (h0 : 0 < (interiorModel Q).param Q ⟨p, h⟩)
    (h1 : (interiorModel Q).param Q ⟨p, h⟩ < 1) :
    (interiorModel Q).InnerPt ((interiorModel Q).pos Q ⟨p, h⟩) := by
  set t := (interiorModel Q).param Q ⟨p, h⟩
  have hq : (p + 1) % Q.n < Q.n := Nat.mod_lt _ (⋄)
  have hne : p ≠ (p + 1) % Q.n := succ_ne (⋄) hp
  have hn' : (interiorModel Q).W.n = Q.n := IOrc.mi_n
  have va : (interiorModel Q).W.vtx p = Q.vtx (IOrc.iv Q p) := IOrc.iw_vtx hp
  have vb : (interiorModel Q).W.vtx ((p + 1) % Q.n) = Q.vtx (IOrc.iv Q ((p + 1) % Q.n)) :=
    IOrc.iw_vtx hq
  have hy : (Q.vtx (IOrc.iv Q p)).2 ≠ (Q.vtx (IOrc.iv Q ((p + 1) % Q.n))).2 :=
    hD _ _ (IOrc.iv_lt hp) (IOrc.iv_lt hq) (fun e => hne (iv_inj hp hq e))
  have hz : (interiorModel Q).pos Q ⟨p, h⟩ =
      lerp (Q.vtx (IOrc.iv Q p)) (Q.vtx (IOrc.iv Q ((p + 1) % Q.n))) t := by
    unfold Model.pos
    simp only
    Ξ IOrc.mi_wa hp, IOrc.mi_wb hp
  Ξ hz
  set a := Q.vtx (IOrc.iv Q p)
  set b := Q.vtx (IOrc.iv Q ((p + 1) % Q.n))
  unfold Model.InnerPt
  ϴ Geometry.lerp_fst, Geometry.lerp_snd
  refine ⟨?_, ?_⟩
  · rcases lt_or_gt_of_ne hy with hab | hab
    · refine ⟨p, (p + 1) % Q.n, by rw [hn']; exact hp, by rw [hn']; exact hq, ?_, ?_⟩
      · rw [va]; nlinarith
      · rw [vb]; nlinarith
    · refine ⟨(p + 1) % Q.n, p, by rw [hn']; exact hq, by rw [hn']; exact hp, ?_, ?_⟩
      · rw [vb]; nlinarith
      · rw [va]; nlinarith
  · rcases le_total a.1 b.1 with hab | hab
    · refine ⟨p, (p + 1) % Q.n, by rw [hn']; exact hp, by rw [hn']; exact hq, ?_, ?_⟩
      · rw [va]; nlinarith
      · rw [vb]; nlinarith
    · refine ⟨(p + 1) % Q.n, p, by rw [hn']; exact hq, by rw [hn']; exact hp, ?_, ?_⟩
      · rw [vb]; nlinarith
      · rw [va]; nlinarith


/-! ## Walk points of a chain model lie between the vertical sides of the box -/

theorem chain_vtx_abs_fst (C : Chain) {p : ℕ} (hp : p < (chainModel C).W.n) :
    |((chainModel C).W.vtx p).1| ≤ C.radius := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hR := C.coordBound_lt_radius
  have htop : |C.top.1| ≤ C.radius := (C.abs_le_coordBound_of_mem_set C.top_mem_set).1.trans hR.le
  have hRp : 0 ≤ C.radius := (abs_nonneg _).trans htop
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  Ξ hW
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ 6 ≤ p) with
    rfl | rfl | rfl | rfl | rfl | rfl | h6
  · rw [C.sideWalk_vtx_zero]; exact htop
  · rw [C.sideWalk_vtx_one]; simp only [abs_neg]; exact (abs_of_nonneg hRp).le
  · rw [C.sideWalk_vtx_two]; simp only [abs_neg]; exact (abs_of_nonneg hRp).le
  · rw [C.sideWalk_vtx_three]; exact (abs_of_nonneg hRp).le
  · rw [C.sideWalk_vtx_four]; exact (abs_of_nonneg hRp).le
  · rw [C.sideWalk_vtx_five]; exact htop
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + 6 := ⟨p - 6, ⋄⟩
    Ξ C.sideWalk_vtx_tour _ (⋄), Chain.sideTour
    exact (C.abs_le_coordBound_of_mem_set (C.vertex_mem_set (C.sideIdx_le _ _))).1.trans hR.le

/-- **A point of the walk of a chain model is within the vertical sides of the box.** -/
theorem chain_pos_abs_fst (C : Chain) (Q : Polygon) {x : WPos}
    (he : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x ≤ 1) : |((chainModel C).pos Q x).1| ≤ C.radius := by
  have hn : 0 < (chainModel C).W.n := ⋄
  unfold Model.pos
  ϴ Model.wa, Model.wb, Geometry.lerp_fst
  have ha := abs_le.1 (chain_vtx_abs_fst C he)
  have hb := abs_le.1 (chain_vtx_abs_fst C (Nat.mod_lt (x.edge + 1) hn))
  Ξ abs_le
  constructor <;> nlinarith

/-- **An inner point of a chain model**: a point of the walk strictly inside the height band of
the box. -/
theorem innerPt_chain_walk (C : Chain) (Q : Polygon) {x : WPos}
    (he : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x ≤ 1) (hy : |((chainModel C).pos Q x).2| < C.radius) :
    (chainModel C).InnerPt ((chainModel C).pos Q x) := by
  have hx := abs_le.1 (chain_pos_abs_fst C Q he h0 h1)
  have hy' := abs_lt.1 hy
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have v1 : (chainModel C).W.vtx 1 = (-C.radius, C.radius) := rfl
  have v2 : (chainModel C).W.vtx 2 = (-C.radius, -C.radius) := rfl
  have v3 : (chainModel C).W.vtx 3 = (C.radius, -C.radius) := rfl
  refine ⟨⟨2, 1, ⋄, ⋄, ?_, ?_⟩, ⟨1, 3, ⋄, ⋄, ?_, ?_⟩⟩
  · rw [v2]; simp only; linarith
  · rw [v1]; simp only; linarith
  · rw [v1]; simp only; linarith
  · rw [v3]; simp only; linarith

/-- **The box vertices are on the boundary of the height band**: walk vertices `0 … 5` of a
chain model are at height `± radius`. -/
theorem chain_box_vtx_abs (C : Chain) {p : ℕ} (hp : p < 6) :
    |((chainModel C).W.vtx p).2| = C.radius := by
  have hR : 0 ≤ C.radius := (abs_nonneg _).trans
    ((C.abs_le_coordBound_of_mem_set C.top_mem_set).1.trans C.coordBound_lt_radius.le)
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  Ξ hW
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · rw [C.sideWalk_vtx_zero]; exact abs_of_nonneg hR
  · rw [C.sideWalk_vtx_one]; exact abs_of_nonneg hR
  · rw [C.sideWalk_vtx_two]; simp only [abs_neg]; exact abs_of_nonneg hR
  · rw [C.sideWalk_vtx_three]; simp only [abs_neg]; exact abs_of_nonneg hR
  · rw [C.sideWalk_vtx_four]; exact abs_of_nonneg hR
  · rw [C.sideWalk_vtx_five]; exact abs_of_nonneg hR

/-- **A position the tests compare**: a proper position inside the height band of the box (for
a chain model). -/
theorem posG_of_band {M : Model} {Q : Polygon} {n : ℕ} {x : WPos} (he : x.edge < M.W.n)
    (hp : ProperPos M Q n x)
    (hy : ∀ C : Chain, M = chainModel C → |(M.pos Q x).2| < C.radius) : PosG M Q n x := by
  refine ⟨he, hp, fun C hM h0 => ?_⟩
  by_contra h6
  have hv : M.pos Q x = M.W.vtx x.edge := by
    obtain ⟨e, g⟩ := x
    simp only at h0
    subst h0
    show Geometry.lerp (M.wa e) (M.wb e) 0 = _
    Θ Geometry.lerp, Model.wa
  have := hy C hM
  Ξ' hv, hM, chain_box_vtx_abs C (⋄) at this
  exact lt_irrefl _ this

/-! ## The arcs of the region are pieces of the shot -/

section arcs

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ : Config}

/-- **One end of an arc record**, normalised: a normalised position on a walk edge, a vertex or
an inner point. -/
theorem TGood.end_ok (hE : TGood P W M N c₀) {x : WPos}
    (hx : ProperPos M (Qof P) (Qof P).n x) (hk : M.key (Qof P) x < M.W.n)
    (hy : ∀ C : Chain, M = chainModel C → |(M.pos (Qof P) x).2| < C.radius) :
    NormPos M (Qof P) P.n (normOf M (Qof P) x) ∧ (normOf M (Qof P) x).edge < M.W.n ∧
      ((normOf M (Qof P) x).hgt = 0 ∨ M.InnerPt (M.pos (Qof P) (normOf M (Qof P) x))) := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  Ξ' hQn at hx
  obtain ⟨hN, he, hpos, -, hcase⟩ := normOf_facts hx
  have hkey : M.key (Qof P) x = x.edge + M.param (Qof P) x := rfl
  have hxe : x.edge < M.W.n := by
    have : (x.edge : ℝ) < M.W.n := by linarith [hx.1]
    exact_mod_cast this
  refine ⟨hN, by rw [he]; exact hxe, ?_⟩
  rcases hcase with h0 | hp
  · exact Or.inl h0
  right
  Ξ hpos
  have hp' : 0 < M.param (Qof P) x := by
    unfold normOf at hp; split_ifs at hp with hz
    · simp at hp
    · exact hp
  rcases hE.kind with ⟨-, C, hM⟩ | ⟨-, hM, -⟩
  · subst hM
    exact innerPt_chain_walk C (Qof P) hxe hx.1 hx.2.1.le (hy C rfl)
  · subst hM
    have hn3 : 3 ≤ (Qof P).n := by rw [hQn]; exact hE.hG.1.1
    obtain ⟨e, h⟩ := x
    exact innerPt_mi_edge (ShootCut.goodEnv_distinct hE.hG) hn3
      (by rw [IOrc.mi_n] at hxe; exact hxe) hp' hx.2.1

/-- **The arcs of the region are pieces of the shot** of weight at most `γ`. -/
theorem TGood.arc_piece (hE : TGood P W M N c₀) (hne : (N.F M (Qof P)).Nonempty) {γ : ℕ}
    (hsg : M.Semigranular (N.F M (Qof P)) γ) {t : ℕ}
    (ht : t < (N.region (c₀.nreg 83002)).arcs.length) :
    PieceOK M (Qof P) P.n (nArc M (Qof P) N (c₀.nreg 83002) t) ∧
      M.arcWt (M.key (Qof P) (nArc M (Qof P) N (c₀.nreg 83002) t).1)
        (M.key (Qof P) (nArc M (Qof P) N (c₀.nreg 83002) t).2) ≤ γ := by
  set r := c₀.nreg 83002
  have hr := hE.hr
  obtain ⟨-, -, -, reg, hRC, -, hArcs, -, -, -, hpp⟩ := hE.hNF
  set j := arcAt N r t with hjdef
  have hjm : j ∈ (N.region r).arcs := by
    Ξ hjdef, arcAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some
    exact List.getElem_mem ht
  obtain ⟨hj, -⟩ := (hArcs.2.2.2 r hr j).1 hjm
  obtain ⟨hjr, harc⟩ := hArcs.1 j hj
  have hU := hRC.1 _ hjr
  obtain ⟨-, ha, -, hb, -⟩ := harc
  have hs := hE.end_ok (hpp j hj).1 ha (hE.arc_abs hne hj).1
  have he := hE.end_ok (hpp j hj).2 hb (hE.arc_abs hne hj).2
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hps : ProperPos M (Qof P) P.n (N.arc j).s := by rw [← hQn]; exact (hpp j hj).1
  have hpe : ProperPos M (Qof P) P.n (N.arc j).e := by rw [← hQn]; exact (hpp j hj).2
  have hks := (normOf_facts hps).2.2.2.1
  have hke := (normOf_facts hpe).2.2.2.1
  refine ⟨⟨hs.1, he.1, hs.2.1, he.2.1, hs.2.2, he.2.2⟩, ?_⟩
  ϴ nArc
  Ξ hks, hke
  exact (BoxT.arcWt_le_weight (hArcs.1 j hj).2).trans (hsg _ hU)

end arcs

/-! ## The shot block -/

section shot

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The copies into the shot block `RS0 = 84000`: model descriptor, arc array (address, count),
origin (edge, height code), direction, weight bound, context. -/
def shL : List (ℕ × ℕ) := [(84000, 83000), (84001, 83081), (84002, 83031), (84004, 83005),
  (84005, 83006), (84006, 83008), (84007, 83003), (84008, 83004)]

/-- **Filling the shot block** (the origin kind `2`: a walk position). -/
def shPrep : Stmt := .seq (block (SweepPrim.copies shL)) (.instr (.constN 84003 2))

/-- The registers `shPrep` writes. -/
def shW : List ℕ := [84000, 84001, 84002, 84003, 84004, 84005, 84006, 84007, 84008]

theorem shW_scr : ∀ r ∈ shW, Scr r := by
  intro r hr; ϴ' shW, List.mem_cons, List.not_mem_nil, or_false at hr; unfold Scr; omega

theorem shPrep_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    RS P W c₀ shPrep c 9 (fun c' => (∀ p ∈ shL, c'.nreg p.1 = c.nreg p.2) ∧
      c'.nreg 84003 = 2 ∧ Out c c' shW) := by
  obtain ⟨c₁, e₁, h1, h2, h3, h4, h5, h6⟩ := SweepPrim.copies_exec (P := P) shL c hI.hw
    (by simp only [shL, List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp)
    (by simp [shL])
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.constN e₁.wb_right 84003 2 (by
    have := hE.hW; unfold hostWords at this; omega))
  have o₁ : Out c c₁ shW := ⟨fun r hr => h2 r (by
    simp only [shW, shL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢; omega), h3, h4, h5, h6⟩
  have ho : Out c c₂ shW := (o₁.trans o₂).mono (fun r hr => by
    simp only [shW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; omega)
  refine RS.out hI shW_scr (.seq e₁ e₂) (by simp [shL]) ho ⟨fun p hp => ?_, v₂, ho⟩
  have hp1 : p.1 ≠ 84003 := by
    simp only [shL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rw [o₂.1 _ (by simpa using hp1), h1 p hp]

/-- **The precondition of the shot wrapper** at a configuration of the run whose shot block is
filled: model descriptor, arc array of the region (`arcBuild`), origin the candidate, direction,
weight bound, context (`shPrep`), and the holes of the candidate (`holeS`). -/
theorem shotPre_of {X : MemCtx} {Ok : Polygon → Model → Prop} (hE : TGood P W M N c₀)
    (hI : TInv W c₀ c) (hX : X.holds P c₀.nmem (c₀.nreg 83004) (c₀.nreg ALLOC))
    (hcap : c₀.nreg 83003 ≤ X.cap P c₀.nmem (c₀.nreg 83004)) (hXl : X.CapLocal) (hOk : Ok P M)
    (hne : (N.F M (Qof P)).Nonempty) (hsg : M.Semigranular (N.F M (Qof P)) (c₀.nreg 83003))
    {B : ℕ} (h00 : c.nreg 84000 = c₀.nreg 83000) (h01 : c.nreg 84001 = B)
    (h02 : c.nreg 84002 = (N.region (c₀.nreg 83002)).arcs.length) (h03 : c.nreg 84003 = 2)
    (h04 : c.nreg 84004 = c₀.nreg 83005) (h05 : c.nreg 84005 = c₀.nreg 83006)
    (h07 : c.nreg 84007 = c₀.nreg 83003) (h08 : c.nreg 84008 = c₀.nreg 83004)
    (hB : B + 4 * (N.region (c₀.nreg 83002)).arcs.length ≤ c.nreg ALLOC)
    (harr : ∀ j, j < (N.region (c₀.nreg 83002)).arcs.length →
      ShotList.arcAt c.nmem B j = nArc M (Qof P) N (c₀.nreg 83002) j)
    (hho : HoleOut M (Qof P) c (M.pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩)) :
    ShotPreG X Ok RS0 P W M (TInv W c₀) (YR M) c := by
  have hm := hI.hm
  have hA := hI.hA
  have i00 : c.nreg 83000 = c₀.nreg 83000 := hI.hin _ (⊛) (⊛)
  obtain ⟨hMD, hwf⟩ := hI.modelDesc hE
  Ξ' i00 at hMD hwf
  have hX' : X.holds P c.nmem (c₀.nreg 83004) (c.nreg ALLOC) :=
    X.mono _ _ _ _ _ hA (X.local_ _ _ _ _ _ (fun a ha => (hm a ha).symm) hX)
  have hcap' : X.cap P c.nmem (c₀.nreg 83004) = X.cap P c₀.nmem (c₀.nreg 83004) :=
    hXl _ _ _ _ _ hm hX
  have hreg : HReg P c.nmem (c₀.nreg 83000) :=
    hreg_keep hE.hwfMD hE.hMD hE.hreg hm
  set x : WPos := ⟨c₀.nreg 83005, c₀.nreg 83006⟩ with hxdef
  have hyR : YR M (M.pos (Qof P) x).2 := fun C hM =>
    lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set (hE.hxC C hM)).2 C.coordBound_lt_radius
  -- the origin is a vertex or an inner point
  have horig : (∃ q, Origin.walk x = .walk ⟨q, 0⟩) ∨ (M.InnerPt ((Origin.walk x).eval M (Qof P)) ∧
      ∀ y, Origin.walk x = .walk y → ProperPos M (Qof P) P.n y) := by
    rcases hE.hxc with h0 | hp
    · exact Or.inl ⟨c₀.nreg 83005, Ρ hxdef, h0⟩
    right
    refine ⟨?_, fun y hy => by cases hy; exact hE.hxp⟩
    show M.InnerPt (M.pos (Qof P) x)
    rcases hE.kind with ⟨-, C, hM⟩ | ⟨-, hM, -⟩
    · subst hM
      exact innerPt_chain_walk C (Qof P) hE.hxe hE.hxp.1 hE.hxp.2.1.le (hyR C rfl)
    · subst hM
      have hQn : (Qof P).n = P.n := shear_n _ _
      have hn3 : 3 ≤ (Qof P).n := by rw [hQn]; exact hE.hG.1.1
      have he := hE.hxe
      Ξ' IOrc.mi_n at he
      exact innerPt_mi_edge (ShootCut.goodEnv_distinct hE.hG) hn3 he hp hE.hxp.2.1
  -- the holes
  obtain ⟨h9, hhl, hcov, -⟩ := hho
  have hv : ∀ g ∈ ShotList.holeList c 84000, g.1.hgt = 0 ∧ g.1.edge < M.W.n := by
    intro g hg
    ϴ' ShotList.holeList, List.mem_map, List.mem_range at hg
    obtain ⟨j, hj, rfl⟩ := hg
    exact ⟨rfl, (hhl j (by have : j < min (c.nreg 84009) 3 := hj; omega)).1⟩
  refine ⟨hE.hG, hE.hW, ?_, ?_, ?_, ?_, ?_, hI, hOk, ?_, h9, ?_, hhl, Origin.walk x,
    ⟨h03, h04, h05⟩, ⟨hE.hxe, hE.hxp.2.2⟩, horig, hyR, ?_⟩
  · show X.holds P c.nmem (c.nreg 84008) (c.nreg ALLOC); rw [h08]; exact hX'
  · show c.nreg 84007 ≤ X.cap P c.nmem (c.nreg 84008); rw [h07, h08, hcap']; exact hcap
  · show ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg 84000); rw [h00]; exact hwf
  · show ModelDescAt c.nmem (c.nreg 84000) (Qof P) M; rw [h00]; exact hMD
  · show HReg P c.nmem (c.nreg 84000); rw [h00]; exact hreg
  · show c.nreg 84001 + 4 * c.nreg 84002 ≤ c.nreg ALLOC; rw [h01, h02]; exact hB
  · intro j hj
    change j < c.nreg 84002 at hj
    Ξ' h02 at hj
    show PieceOK M (Qof P) P.n (ShotList.arcAt c.nmem (c.nreg 84001) j) ∧
      M.arcWt (M.key (Qof P) (ShotList.arcAt c.nmem (c.nreg 84001) j).1)
        (M.key (Qof P) (ShotList.arcAt c.nmem (c.nreg 84001) j).2) ≤ c.nreg 84007
    Ξ h01, harr j hj, h07
    exact hE.arc_piece hne hsg hj
  · exact avoid_of_cover hcov hv _ _ _

end shot

/-! ## The arrival step -/

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The copies of the arrival step: descriptor, returned position, reversed direction code. -/
def arrL : List (ℕ × ℕ) := [(50200, 83020), (50201, 83012), (50202, 83013), (50203, 83120)]

/-- The arrival step in a chain model. -/
def tArrC : Stmt := .seq (.instr (.subN 83120 83023 83008)) (.seq (.seq (block (copies arrL))
  SweepPrim.arrivalPos) (.seq (.instr (.copyN 83012 50211)) (.instr (.copyN 83013 50212))))

/-- **The arrival step**: in a chain model, the arrival position of the hit point. -/
def tArr : Stmt := .ifLtN 83021 83023 tArrC .skip

theorem rho_dir {v : ℕ} (hv : v ≤ 1) : -dirOf (1 - v) = dirOf v := by
  have : 1 - v = if v = 1 then 0 else 1 := by split_ifs <;> omega
  Ξ this, SweepPrim.neg_dirOf_flip

/-- **The arrival step.**  From a proper position `f` (registers `83012`, `83013`) of a point at
which, in a chain model, an arrival position of the ray exists: in a chain model the registers
hold an arrival position of the same point afterwards; in the interior model they are unchanged.
Only `83012`, `83013`, `83120` of band `bRestore` change. -/
theorem tArr_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hp : ProperPos M (Qof P) P.n ⟨c.nreg 83012, c.nreg 83013⟩) (he : c.nreg 83012 < M.W.n)
    (hy : ∀ C : Chain, M = chainModel C →
      |(M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩).2| < C.radius)
    (hex : ∀ C : Chain, M = chainModel C → ∃ p t, Sweep.Arrival M.W
      (M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩) (dirOf (c₀.nreg 83008)) p t)
    (hroom : c.nreg ALLOC + 35000 ≤ W) :
    RS P W c₀ tArr c 35012 (fun c' =>
      ProperPos M (Qof P) P.n ⟨c'.nreg 83012, c'.nreg 83013⟩ ∧ c'.nreg 83012 < M.W.n ∧
      M.pos (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩ = M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩ ∧
      (∀ C : Chain, M = chainModel C → Sweep.Arrival M.W
        (M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩) (dirOf (c₀.nreg 83008)) (c'.nreg 83012)
        (M.param (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩)) ∧
      (M = interiorModel (Qof P) → c'.nreg 83012 = c.nreg 83012 ∧ c'.nreg 83013 = c.nreg 83013) ∧
      Agr c c' [83012, 83013, 83120]) := by
  rcases hE.kind with ⟨h0, C₀, hM₀⟩ | ⟨h1, hMi, -⟩
  · -- a chain model
    have g21 : c.nreg 83021 < c.nreg 83023 := by rw [hI.h21, hI.h23, h0]; omega
    obtain ⟨H, C, hC, hM, hwf, hsimp, -⟩ := hI.chainS hE hM₀
    subst hM
    have h8 : c.nreg 83008 = c₀.nreg 83008 := hI.hin _ (by norm_num) (by norm_num)
    have hσ := hE.hσ
    -- ρ = 1 - σb
    obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hI.hw 83120 83023 83008)
    obtain ⟨hI₁, rf₁⟩ := hI.regs e₁.wb_right (fun r hr => o₁.1 r (by
      simp only [List.mem_singleton]; omega)) o₁.2.1 o₁.2.2.1 o₁.2.2.2.1 o₁.2.2.2.2 (k := 1)
    have k₁ : ∀ r, r ≠ 83120 → c₁.nreg r = c.nreg r := fun r hr => o₁.1 r (by simpa using hr)
    have r120 : c₁.nreg 83120 = 1 - c₀.nreg 83008 := by rw [v₁, hI.h23, h8]
    have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := k₁ _ (by unfold ALLOC; omega)
    have hC₁ : ChainDescAt c₁.nmem (c₁.nreg 83020) (Qof P) H C := by
      rw [o₁.2.2.1, k₁ 83020 (by norm_num)]; exact hC
    have hwf₁ : ChainWF P (c₁.nreg ALLOC) c₁.nmem (c₁.nreg 83020) := by
      rw [hA₁, o₁.2.2.1, k₁ 83020 (by norm_num)]; exact hwf
    have f12 : c₁.nreg 83012 = c.nreg 83012 := k₁ _ (by omega)
    have f13 : c₁.nreg 83013 = c.nreg 83013 := k₁ _ (by omega)
    obtain ⟨c₂', c₂, k₂, q, -, -, ex₂, hk₂, hout, hf₂⟩ := callPrim SweepPrim.arrivalPos_meets arrL
      (by simp only [arrL, List.mem_cons, List.not_mem_nil, or_false]
          rintro q (rfl | rfl | rfl | rfl) r (rfl | rfl | rfl | rfl) <;> simp)
      (by simp [arrL]) (by simp [arrL]) (src := 83020) (by simp [arrL]) e₁.wb_right hE.hG hE.hW
      hwf₁ hC₁ (fun c' h1 _ _ => by
        have q1 := h1 (50201, 83012) (by simp [arrL])
        have q2 := h1 (50202, 83013) (by simp [arrL])
        simp only at q1 q2
        refine ⟨⟨by rw [q1, f12]; exact he, by rw [q1, q2, f12, f13]; exact hp, ?_⟩, ?_, ?_⟩
        · rw [q1, q2, f12, f13]; exact hy C rfl
        · exact hsimp
        · exact hE.hWm C rfl) (by rw [hA₁]; omega)
    have q1 := q (50201, 83012) (by simp [arrL])
    have q2 := q (50202, 83013) (by simp [arrL])
    have q3 := q (50203, 83120) (by simp [arrL])
    simp only at q1 q2 q3
    unfold SweepPrim.ArrOut SweepPrim.ArrRes at hout
    rw [q1, q2, q3, f12, f13, r120, rho_dir hσ] at hout
    obtain ⟨hfl, hyes, hno⟩ := hout
    have hflag : c₂.nreg 50210 = 1 := by
      by_contra hne
      obtain ⟨p', t', ha⟩ := hex C rfl
      exact hno hne p' t' ha
    obtain ⟨hpe, hpp, harr⟩ := hyes hflag
    have T₂ := hI₁.prim ex₂.wb_right hf₂
    -- copy the arrival position back
    obtain ⟨c₃, e₃, v₃, o₃⟩ := out_instr (P := P) (Exec.copyN ex₂.wb_right 83012 50211)
    obtain ⟨hI₃, rf₃⟩ := T₂.1.regs e₃.wb_right (fun r hr => o₃.1 r (by
      simp only [List.mem_singleton]; omega)) o₃.2.1 o₃.2.2.1 o₃.2.2.2.1 o₃.2.2.2.2 (k := 1)
    obtain ⟨c₄, e₄, v₄, o₄⟩ := out_instr (P := P) (Exec.copyN e₃.wb_right 83013 50212)
    obtain ⟨hI₄, rf₄⟩ := hI₃.regs e₄.wb_right (fun r hr => o₄.1 r (by
      simp only [List.mem_singleton]; omega)) o₄.2.1 o₄.2.2.1 o₄.2.2.2.1 o₄.2.2.2.2 (k := 1)
    have w12 : c₄.nreg 83012 = c₂.nreg 50211 := by rw [o₄.1 _ (by simp), v₃]
    have w13 : c₄.nreg 83013 = c₂.nreg 50212 := by rw [v₄, o₃.1 _ (by simp)]
    refine ⟨c₄, 1 + (k₂ + (1 + 1)) + 1,
      .ifLtN_true g21 (.seq e₁ (.seq ex₂ (.seq e₃ e₄))), ?_, hI₄,
      ((rf₁.trans (T₂.2.1.trans (rf₃.trans rf₄)))).mono subset_rfl (by omega), ?_⟩
    · simp [arrL] at hk₂; omega
    show _ ∧ _
    rw [w12, w13]
    refine ⟨hpp, hpe, harr.2.2.2.1, fun _ _ => harr, fun h => absurd h
      (chainModel_ne_interior C (Qof P)), fun r h1 h2 hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₄.1 r (by simpa using hr.2.1), o₃.1 r (by simpa using hr.1),
      T₂.2.2 r h1 h2, k₁ r hr.2.2]
  · -- the interior model: nothing to do
    have g21 : ¬ c.nreg 83021 < c.nreg 83023 := by rw [hI.h21, hI.h23, h1]; omega
    refine RS.ifF g21 (RS.skip (K := 0) hI ⟨hp, he, rfl, fun C hC => absurd (hC.symm.trans hMi)
      (chainModel_ne_interior C (Qof P)), fun _ => ⟨rfl, rfl⟩, Agr.refl _ _⟩) |>.mono
      (by omega) (fun _ h => h)

end

end Restore

end Chazelle.Core
