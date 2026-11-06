module

public import Chazelle.MacT
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.BruteRam3
public import Chazelle.Core.DownPhaseRegionBox
public import Chazelle.Jordan.SegmentFacts
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.OracleQuery
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.OracleBook
public import Chazelle.Core.SpecNF
public import Chazelle.Core.GranRamBody
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.SweepPrimKer
public import Chazelle.Core.ShootCutDyDn

namespace Chazelle.Core
namespace DrvR
@[expose] public section
open Machine

/-- **The bucket of a walk position** for the splice into `N`: `2 · #{arc starts with a smaller
key} + [some arc start has the same key]`. -/
noncomputable def keyBkt (Q : Polygon) (N : NF) (x : WPos) : ℕ := by
  classical
  exact 2 * ((List.range N.arcs.length).filter fun j =>
      decide ztblk).length +
    if ∃ j, j < N.arcs.length ∧ (interiorModel Q).key Q (N.arc j).s = (interiorModel Q).key Q x
    then 1 else 0

/-- The position lies on the closure of arc `j` of `N` (cyclically, by keys). -/
def OnArcKey (Q : Polygon) (N : NF) (j : ℕ) (x : WPos) : Prop :=
  (interiorModel Q).key Q x = (interiorModel Q).key Q (N.arc j).s ∨
    (interiorModel Q).key Q x = (interiorModel Q).key Q (N.arc j).e ∨
    Chazelle.Chain.sideInArc ztejb
      zteja ztgwc

/-- The two end positions of a chord triple (`q` even: left end). -/
def endPos (Lx : List zte) (q : ℕ) : WPos :=
  if q % 2 = 0 then (recOf ztztv).lpos
  else (recOf ztztv).rpos

/-- **The contract of the extraction (D6).** -/
def ExtractRamSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), Meets s {bDownDrv, bSign, bLocate, bBuild, bSort}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ c.nreg 217002 ≤ 1 ∧
      ztxkt ∧
      ∃ (L : List zte) (E : List ℕ) (C : Chain) (NR : NF), L ≠ [] ∧
        ChordTriplesOK ztwiq zta L ∧ E.Perm ztct ∧
        E.Pairwise ztbajk ∧
        (interiorModel zta).DegLe
          ((BuildNF.buildNF ztwiq zta L E).F ztwiq
            zta) 4 ∧
        NFWithin c.nmem zthup ztm
          ztbaja ∧
        c.nreg 217001 < (BuildNF.buildNF ztwiq zta L E).nRegions ∧
        Robust ztm c.nmem (fun m => HostAt m ztmga
          (regHost ztgm (Qof P).n
            ztbaja ztos)) ∧
        c.nreg 217003 + 3 * (regHost ztgm (Qof P).n
            ztbaja ztos).length + 1 ≤
          c.nreg ALLOC ∧
        c.nreg 217004 = ((regHost ztgm (Qof P).n
          ztbaja ztos).pts
            (Qof P).n).length ∧
        C.P = (regHost ztgm (Qof P).n
          ztbaja ztos).poly (Qof P) ∧
        C.s = 0 ∧ C.m + 1 = C.P.n ∧
        ModelDescWF P ztm c.nmem ztghe ∧
        Robust ztm c.nmem (fun m => ModelDescAt m ztghe zta
          ztc) ∧
        Robust ztm c.nmem (fun m => ChainDescAt m ztlkt zta
          (regHost ztgm (Qof P).n
            ztbaja ztos) C) ∧
        NFWithin c.nmem ztchk ztm NR ∧ IsNF ztc zta NR)
    (fun P c c' =>
      ztcbj ∧
      ∀ (L : List zte) (E : List ℕ) (C : Chain) (NR : NF) (reg : ℕ → Set Point),
        L ≠ [] → ChordTriplesOK ztwiq zta L →
        E.Perm ztct →
        E.Pairwise ztbajk →
        NFAt c.nmem zthup ztbaja →
        Restore.NFRegs ztwiq zta
          ztbaja reg →
        C.P = (regHost ztgm (Qof P).n
          ztbaja ztos).poly (Qof P) →
        C.s = 0 → C.m + 1 = C.P.n → NFAt c.nmem ztchk NR →
        IsNF ztc zta NR →
        ∃ Lx : List zte,
          c.nreg ALLOC ≤ c'.nreg 217010 ∧ c'.nreg 217010 + 3 * Lx.length ≤ c'.nreg ALLOC ∧
          c.nreg ALLOC ≤ c'.nreg 217012 ∧ c'.nreg 217012 + 2 * Lx.length ≤ c'.nreg ALLOC ∧
          c'.nreg 217011 = Lx.length ∧ ChordListAt c'.nmem ztqha Lx ∧
          {x | ∃ y ∈ Lx, x = (recOf y).toSet ztwiq zta} =
            Extract.kept ztbaio ztxki ∧
          (Lx.map fun y => (recOf y).toSet ztwiq zta).Nodup ∧
          ztbaji ∧
          ∀ q, q < 2 * Lx.length →
            c'.nmem ztlkg = keyBkt zta
              ztbaja ztdui ∧
            ∃ j ∈ ((BuildNF.buildNF ztwiq zta L E).region
                ztos).arcs,
              OnArcKey zta ztbaja j
                ztdui)
    ztbanv
end
end DrvR
namespace DownDrv
@[expose] public section
open BuildNF (codeLe wposOf tieBit buildNF gapStarts arcRec arcList)
variable {M : Model} {Q : Polygon} {L L₂ : List (ℕ × ℕ × ℕ)} {E E₂ : List ℕ}

/-! ## S-M1 -/

/-- **The arcs of `buildNF` are the gaps of the event list, in order.** -/
theorem buildNF_arcs (hK : 0 < L.length) :
    (buildNF M Q L E).arcs = (gapStarts M Q L E).map ztgfc := by
  show arcList M Q L E = _
  unfold arcList
  grind

/-- Arc `j` runs from the event at `gapStarts j` to the next event. -/
theorem buildNF_arc (hK : 0 < L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    (buildNF M Q L E).arcs.getD j ztgp =
      { reg := (arcRec M Q L E ztbhi).reg,
        s := wposOf L (E.getD ztbhi 0),
        e := wposOf L (E.getD (((gapStarts M Q L E).getD j 0 + 1) % E.length) 0) } := by
  rw [buildNF_arcs hK, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some,
    show ztdon[j] = (gapStarts M Q L E).getD j 0 by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]]
  rfl

/-- The arc sequence of `buildNF` is the identity order. -/
theorem buildNF_seq : (buildNF M Q L E).seq = List.range (buildNF M Q L E).arcs.length := rfl

/-! ## S-M2 -/
variable {c : ℕ}
theorem getD_append_left (hc : c < 2 * L.length) :
    (L ++ L₂).getD ztbek ztt = L.getD ztbek ztt := by
  grind

/-- **Old event codes name the same walk positions after appending chords.** -/
theorem wposOf_append (hc : c < 2 * L.length) : wposOf ztfi c = wposOf L c := by
  zulci
  zulrn
  grind
theorem tieBit_append (hc : c < 2 * L.length) : tieBit M ztfi c = tieBit M L c := by
  unfold tieBit
  rw [wposOf_append hc]
theorem codeLe_append {c c' : ℕ} (hc : c < 2 * L.length) (hc' : c' < 2 * L.length) :
    codeLe M Q ztfi c c' ↔ codeLe M Q L c c' := by
  zului
  rw [wposOf_append hc, wposOf_append hc', tieBit_append hc, tieBit_append hc']
open Classical in
/-- The comparator as a Boolean function. -/
noncomputable def codeLeB (M : Model) (Q : Polygon) (L : List zte) (a b : ℕ) : Bool :=
  decide ztpaf
theorem codeLeB_iff (a b : ℕ) : codeLeB M Q L a b = true ↔ codeLe M Q L a b := by
  unfold codeLeB; simp

/-- **The spliced event list.** -/
noncomputable def splice (M : Model) (Q : Polygon) (L : List zte) (E E₂ : List ℕ) :
    List ℕ :=
  List.merge E E₂ (codeLeB M Q L)

/-- **S-M2: splicing gives a valid sorted event list for the extended chord list.** -/
theorem splice_ok (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztxi)
    (hperm₂ : E₂.Perm ztgqh)
    (hsort₂ : E₂.Pairwise ztzlf) :
    (splice M Q ztfi E E₂).Perm ztiqa ∧
      (splice M Q ztfi E E₂).Pairwise ztzlf := by
  constructor
  · unfold splice
    refine (List.merge_perm_append (le := codeLeB M Q ztfi)).trans ?_
    rw [List.length_append, Nat.mul_add, List.range_add]
    grind
  · have hE : E.Pairwise ztxse := by
      zuflt
      zuglw

      rw [codeLeB_iff, codeLe_append ha' hb']
      omega
    have hE₂ : E₂.Pairwise ztxse :=
      hsort₂.imp fun h => (codeLeB_iff _ _).2 h
    have h := List.pairwise_merge (le := codeLeB M Q ztfi)
      (fun a b c h1 h2 => by
        rw [codeLeB_iff] at h1 h2 ⊢
        exact BuildNF.codeLe_trans M Q ztfi h1 h2)
      (fun a b => by
        rcases BuildNF.codeLe_total M Q ztfi a b with h | h
        · rw [(codeLeB_iff a b).2 h]; rfl
        · rw [(codeLeB_iff b a).2 h, Bool.or_true])
      E E₂ hE hE₂
    unfold splice
    exact h.imp fun h' => (codeLeB_iff _ _).1 h'
end
end DownDrv
namespace DownMath
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- The index before `i`, cyclically modulo `N`. -/
def prevIdx (N i : ℕ) : ℕ := ztqra % N
variable {N i : ℕ} {li : Bool}
theorem prevIdx_succ (hi : i < N) : prevIdx N ztxan = i := by
  zulcb
  by_cases h : i + 1 < N
  · rw [Nat.mod_eq_of_lt h, show i + 1 + N - 1 = i + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  · rw [show i + 1 = N by omega, Nat.mod_self, show 0 + N - 1 = i by omega, Nat.mod_eq_of_lt hi]
theorem prevIdx_lt (hN : 0 < N) : prevIdx N i < N := Nat.mod_lt _ hN
theorem succ_prevIdx (hi : i < N) : (prevIdx N i + 1) % N = i := by
  zulcb
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · zujwz
    rw [e, Nat.sub_add_cancel by_grind, Nat.mod_self]
  · have e : ztqra % N = i - 1 := by
      rw [show i + N - 1 = ztei + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    rw [e, Nat.sub_add_cancel h0, Nat.mod_eq_of_lt hi]

/-! ## Walk and polygon indices -/
open DrvR (ivB qE)
theorem ivB_lt (li : Bool) {n p : ℕ} (hp : p < n) : ivB li n p < n := by
  zujqn
theorem qE_lt (li : Bool) {n p : ℕ} (hp : p < n) : qE li n p < n := by
  unfold qE; grind

/-- **The ends of a walk edge**: walk edge `p` joins the vertices `ivB p`, `ivB (p + 1)` of `Q`,
which are the ends of the edge `qE p` of `Q` (in one order or the other). -/
theorem edge_ends (li : Bool) {n p : ℕ} (hn : 2 ≤ n) (hp : p < n) :
    (ivB li n p = qE li n p ∧ ivB li n ztxlu = ztpdb % n) ∨
      (ivB li n p = ztpdb % n ∧ ivB li n ztxlu = qE li n p) := by
  unfold ivB qE
  cases li with
  | false =>
    right
    zuma
    zuhsi
    · rw [ite_eq_left h, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt by_grind]
      omega
    · have hp' : ztskv := by_omega
      subst hp'
      rw [ite_eq_right h, Nat.sub_add_cancel by_grind, Nat.mod_self]
      omega
  | true =>
    left
    simp

/-- Consecutive walk vertices are consecutive vertices of `Q`. -/
theorem ivB_succ (li : Bool) {n p : ℕ} (hn : 2 ≤ n) (hp : p < n) :
    ivB li n ztxlu = (ivB li n p + 1) % n ∨ ivB li n p = (ivB li n ztxlu + 1) % n := by
  rcases edge_ends li hn hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp_all
  simp_all
theorem ivB_inj (li : Bool) {n p q : ℕ} (hp : p < n) (hq : q < n) (h : ivB li n p = ivB li n q) :
    p = q := by
  unfold ivB at h; grind

/-- The interior walk lists the vertices of `Q` in the order `ivB`. -/
theorem walk_vtx (hli : li = true ↔ Mountain.LeftInside Q) {k : ℕ} (hk : k < Q.n) :
    (interiorWalk Q).vtx k = Q.vtx (ivB li Q.n k) := by
  classical
  unfold interiorWalk ivB
  zucla
  · simp_all
  · have : ztppd := by_simp_all
    rw [ite_eq_right hL, this]
    zuled
theorem walk_n (Q : Polygon) : (interiorWalk Q).n = Q.n := Mir.interiorWalk_n Q
theorem xAt_comm' {u w : Point} (h : u.2 ≠ w.2) (y : ℝ) :
    Visibility.xAt w u y = Visibility.xAt u w y := by
  zugle

  unfold Visibility.xAt; grind

/-- **The symbolic point of a position on a walk edge**: `.onEdge (qE p) h` evaluates to the
point of walk edge `p` at the height of `h`. -/
theorem eval_onEdge (hli : li = true ↔ Mountain.LeftInside Q) (hn : 3 ≤ Q.n)
    (hdh : DistinctHeights Q) {p : ℕ} (hp : p < Q.n) (t : ℝ) {h : ℕ}
    (hy : (Q.vtx h).2 = (sidePt ztkb p t).2) :
    (SymPt.onEdge zthzi h).eval Q = sidePt ztkb p t := by
  zuhzr
  have hv0 := walk_vtx hli hp
  have hv1 := walk_vtx hli hp1
  have hne : ivB li Q.n p ≠ ivB li Q.n ztwqx := by
    zuhgj
    have := ivB_inj li hp hp1 h'
    zuhso
    · zufu
    · zudko
  have hd : ztkyy :=
    hdh _ _ ztjyy zttpt hne
  have hxat : Visibility.edgeX Q zthzi (Q.vtx h).2 =
      Visibility.xAt ztbafh (Q.vtx ztbamy) (Q.vtx h).2 := by
    unfold Visibility.edgeX
    rcases edge_ends li by_omega hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp_all
    · zunyn; exact xAt_comm' hd _
  have hW : sidePt ztkb p t =
      Geometry.lerp ztbafh (Q.vtx ztbamy) t := by
    unfold sidePt; rw [walk_n, hv0, hv1]
  zujim
  show ((edgeXAt Q _ h, (Q.vtx h).2) : Point) = _
  unfold edgeXAt
  rw [hxat, hy, Visibility.xAt_lerp hd]

/-- **The symbolic point of an arc end at a walk vertex**: `.onEdge (qE (p - 1)) h` evaluates to
walk vertex `p`. -/
theorem eval_onEdge_prev (hli : li = true ↔ Mountain.LeftInside Q) (hn : 3 ≤ Q.n)
    (hdh : DistinctHeights Q) {p : ℕ} (hp : p < Q.n) {h : ℕ}
    (hy : (Q.vtx h).2 = ((interiorWalk Q).vtx p).2) :
    (SymPt.onEdge (qE li Q.n ztbaao) h).eval Q = (interiorWalk Q).vtx p := by
  have hq : ztkbu % Q.n < Q.n := Nat.mod_lt _ by_omega
  have hs : sidePt ztkb ztbaao 1 = (interiorWalk Q).vtx p := by
    have e := succ_prevIdx hp
    unfold prevIdx at e
    rw [sidePt_one, walk_n, e]
  rw [← hs] at hy ⊢
  exact eval_onEdge hli hn hdh hq 1 hy

/-! ## Representing host keys -/

/-- **The symbolic point `s` represents the host key `hk i` of `R`** (`li` the `LeftInside` bit;
see the module doc): a vertex key `k` as `.vtx (ivB k)`, an exit key `p + t` as
`.onEdge (qE e) h` with `h` at the height of the point and `e = p`, or `e = p - 1` for a vertex
key (`t = 0`) that ends an arc gap. -/
def RepPt (li : Bool) (Q : Polygon) (S : Set ztf) (R : Set Point) (i : ℕ) (s : SymPt) :
    Prop :=
  (hk ztd S R i ∈ vtxKeys ztd S R ∧
      s = .vtx (ivB li Q.n ⌊hk ztd S R i⌋₊)) ∨
    (hk ztd S R i ∈ exitKeys ztd S R ∧ ∃ h, h < Q.n ∧
      (Q.vtx h).2 = (hostPt (interiorModel Q).W ztwln).2 ∧
      ((hk ztd S R i = ⌊hk ztd S R i⌋₊ ∧
          ArcGap ztd S R ztbajx ∧
          s = .onEdge (qE li Q.n ((⌊hk ztd S R i⌋₊ + Q.n - 1) % Q.n)) h) ∨
        (¬ (hk ztd S R i = ⌊hk ztd S R i⌋₊ ∧
            ArcGap ztd S R ztbajx) ∧
          s = .onEdge (qE li Q.n ⌊hk ztd S R i⌋₊) h)))

/-! ## Keys -/

/-- A vertex key is a walk vertex. -/
theorem vtxKey_nat {M : Model} {F : Set ztf} {U : Set Point} {x : ℝ}
    (hx : x ∈ vtxKeys M F U) : x = ⌊x⌋₊ := by
  obtain ⟨k, -, rfl, -⟩ := hx
  simp

/-- **Keys with no walk vertex strictly between them** (cyclically): the second one is on the
walk edge of the first one, after it, or it is the next walk vertex. -/
theorem noInt_cases {n : ℕ} {x y : ℝ} (hx0 : 0 ≤ x) (hxn : x < n) (hy0 : 0 ≤ y) (hyn : y < n)
    (hxy : x ≠ y) (h : ∀ k : ℕ, k < n → ¬ sideInArc x y k) :
    (x < y ∧ ⌊y⌋₊ = ⌊x⌋₊) ∨ y = ((ztpew % n : ℕ) : ℝ) := by
  set p := ⌊x⌋₊ with hp
  have hpx := Nat.floor_le hx0
  have hxp := Nat.lt_floor_add_one x
  have hpn : ztsks := by
    zujvr

  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · -- `x < y`
    by_cases hfl : ⌊y⌋₊ = p
    · simp_all
    · right
      have hpy : p + 1 ≤ ⌊y⌋₊ := by
        have  := Nat.floor_le_floor hlt.le
        omega
      have hpy' : ((p + 1 : ℕ) : ℝ) ≤ y :=
        le_trans (by exact_mod_cast hpy) (Nat.floor_le hy0)
      have hp1n : ztsko := by
        have : ztiwp := by_grind
        zufc
      rcases hpy'.lt_or_eq with h1 | h1
      · exfalso
        apply h _ hp1n
        zuxb
      · rw [Nat.mod_eq_of_lt hp1n, h1]
  · -- `y < x`: the interval wraps
    right
    by_cases hp1 : p + 1 < n
    · exfalso
      apply h _ hp1
      zujv
    · have hpn1 : p + 1 = n := by_omega
      rw [hpn1, Nat.mod_self]
      push_cast
      rcases hy0.lt_or_eq with h0 | h0
      · exfalso
        apply h 0 by_omega
        zujv
      simp_all
section
variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR
variable {i : ℕ}
/-- **An exit key does not both end an arc gap and start one**: the exit chord attached there
gives a chord gap on one of the two sides. -/
theorem not_arcGap_both (hi : i < nk ztd S R)
    (hx : hk ztd S R i ∈ exitKeys ztd S R)
    (hA : ArcGap ztd S R i)
    (hB : ArcGap ztd S R ztbajx) : False := by
  zuceu

  zulk
  zubl

  zubnm
  obtain ⟨c, hc, htouch, p, t, hAt, hxe⟩ := hx
  obtain ⟨j, hj, pa, pb, ta, tb, hAa, hAb, ea, eb, hne', -⟩ :=
    exit_chordGap hM hF hfin hR by_omega hc htouch
  zuddf

  zuiaj
  zuhfb
  have hxa : ztmvu := ⟨p, t, hAt, hxe⟩
  zuffr

  have hcases : ztbakj := by
    zuqk

    all_goals first
      | exact Or.inl (e0.trans e1.symm)
      | exact Or.inr (e0.trans e2.symm)
      | exact by_grind
  zukld
  · have := hk_inj hM hF hfin hi hj e
    zumo
    exact not_arc_and_chord hM hF hfin by_omega hj hA hgap
  · have := hk_inj hM hF hfin hi hsj e
    rw [this, prevIdx_succ hj] at hB
    exact not_arc_and_chord hM hF hfin by_omega hj hB hgap

/-- In an arc gap, no walk vertex lies strictly between the two keys. -/
theorem arcGap_noInt (hi : i < nk ztd S R)
    (hA : ArcGap ztd S R i) (k : ℕ) (hkn : k < (interiorModel Q).W.n) :
    ¬ sideInArc ztwln
      ztbakh k := by
  zubwf
  zukh
  zulmv
  obtain ⟨a, b, harc, hsub⟩ := hA
  refine hk_gap hM hFam.2.1 hFam.1 by_omega hi
    (Or.inr ⟨k, hkn, rfl, a, b, harc, by_simp_all⟩) hin
omit hQ hFam hne hR in
/-- **H-R1, one point**: a representing symbolic point evaluates to the host point. -/
theorem rep_eval (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (_hne : S.Nonempty)
    (_hR : R ∈ (interiorModel Q).regions S) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q)
    (hdh : DistinctHeights Q)
    {i : ℕ} (hi : i < nk ztd S R) {s : SymPt} (hs : RepPt li Q S R i s) :
    s.eval Q = hostPt (interiorModel Q).W ztwln := by
  zubwf
  zudhw
  have hb := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hi)
  zucmb
  zuijj
  zugus
  rcases hs with ⟨hv, rfl⟩ | ⟨-, h, -, hy, (⟨hint, -, rfl⟩ | ⟨-, rfl⟩)⟩
  · obtain ⟨k, hk, hxk, -⟩ := hv
    rw [hxk, Nat.floor_natCast]
    rw [hW, walk_n] at hk
    show Q.vtx _ = _
    rw [← walk_vtx hli hk]
    unfold hostPt
    rw [Nat.floor_natCast, sub_self, Chazelle.Chain.sidePt_zero]
  · zuiom
    have hp : ztrhq := by
      have : (⌊x⌋₊ : ℝ) < Q.n := by_grind
      zufc
    have hpt : hostPt ztkb x = (interiorWalk Q).vtx ⌊x⌋₊ := by
      unfold hostPt; rw [← hint, sub_self, Chazelle.Chain.sidePt_zero]
    rw [hW, hpt] at hy
    zubil
    exact eval_onEdge_prev hli hn3 hdh hp hy
  · zuiom
    have hp : ztrhq := by
      zuepf
      simp_all
    exact eval_onEdge hli hn3 hdh hp _ hy

/-- **H-R2, one host edge**: consecutive representing points satisfy `HostEdgeOK`. -/
theorem rep_edgeOK {li : Bool} (hdh : DistinctHeights Q) {i : ℕ}
    (hi : i < nk ztd S R) {s s' : SymPt} (hs : RepPt li Q S R i s)
    (hs' : RepPt li Q S R ztwkg s') : HostEdgeOK Q.n s s' := by
  zuhm
  zuhoe
  zulk
  zubl

  zudhw
  zubnm
  have hsi : ztzrc := Nat.mod_lt _ by_omega
  zudhk

  zvnux at hbx hby
  set x := hk I S R i with hx
  set y := hk I S R ztxan with hy
  have hprev : prevIdx N _ = i := prevIdx_succ hi
  rcases gap_cases hM hF hfin hne hR by_omega hi with hA | hC
  · -- an arc gap: the two keys are on one walk edge, or the second is the next walk vertex
    have hnoint : ∀ k : ℕ, k < Q.n → ¬ sideInArc x y k := fun k hk =>
      arcGap_noInt hQ hFam hne hR hi hA k by_simp_all
    have hxy := hk_succ_ne hM hF hfin by_omega hi
    set p := ⌊x⌋₊ with hpdef
    have hp : p < Q.n := by
      have  := lt_of_le_of_lt (Nat.floor_le hbx.1) hbx.2
      simp_all
    -- the first point is `.vtx (ivB p)` or `.onEdge (qE p) _`
    have hs1 : s = .vtx ztlqj ∨ ∃ h, s = .onEdge zthzi h := by
      rcases hs with ⟨-, rfl⟩ | ⟨hxe, h, -, -, (⟨-, hB, -⟩ | ⟨-, rfl⟩)⟩
      · simp_all
      · exact (not_arcGap_both hQ hFam hne hR hi hxe hA hB).elim
      simp_all
    have hE := edge_ends li by_omega hp
    rcases noInt_cases hbx.1 hbx.2 hby.1 hby.2 hxy hnoint with ⟨hlt, hfl⟩ | hyv
    · -- same walk edge: `y` is not a vertex, so `s' = .onEdge (qE p) _`
      have hyni : y ≠ ⌊y⌋₊ := by
        intro h; rw [hfl] at h
        zuman
        linarith
      obtain ⟨h', rfl⟩ : ∃ h', s' = .onEdge (qE li Q.n p) h' := by
        rcases hs' with ⟨hv, -⟩ | ⟨-, h', -, -, (⟨hint, -, -⟩ | ⟨-, rfl⟩)⟩
        · exact absurd (vtxKey_nat hv) hyni
        · simp_all
        simp_all
      rcases hs1 with rfl | ⟨h, rfl⟩
      · show ivB li Q.n p = qE li Q.n p ∨ ivB li Q.n p = ztilv % Q.n
        omega
      · exact Or.inr rfl
    · -- `y` is the next walk vertex
      have hyfl : ⌊y⌋₊ = ztr % Q.n := by rw [hyv, Nat.floor_natCast]
      have hyint : y = ⌊y⌋₊ := by_simp_all
      have hpm : (ztr % Q.n + Q.n - 1) % Q.n = p := by
        have := prevIdx_succ hp
        tauto
      have hs2 : s' = .vtx ztbamy ∨ ∃ h', s' = .onEdge zthzi h' := by
        rcases hs' with ⟨-, rfl⟩ | ⟨-, h', -, -, (⟨-, -, rfl⟩ | ⟨hn', -⟩)⟩
        · grind
        · right; exact ⟨h', by_grind⟩
        grind
      rcases hs1 with rfl | ⟨h, rfl⟩ <;> rcases hs2 with rfl | ⟨h', rfl⟩
      · show ivB li Q.n _ = (ivB li Q.n p + 1) % Q.n ∨
          ivB li Q.n p = (ivB li Q.n _ + 1) % Q.n
        exact ivB_succ li by_omega hp
      · show ivB li Q.n p = qE li Q.n p ∨ ivB li Q.n p = ztilv % Q.n
        omega
      · show ivB li Q.n _ = qE li Q.n p ∨
          ivB li Q.n _ = ztilv % Q.n
        omega
      · exact Or.inr rfl
  · -- a chord gap: both points are on the chord, at its height
    obtain ⟨c, hc, p, p', t, t', hAt, hAt', ex, ey, -⟩ := hC
    have hcutx : I.IsCut S x := ⟨c, hc, p, t, hAt, ex⟩
    have hcuty : I.IsCut S y := ⟨c, hc, p', t', hAt', ey⟩
    have hpx : hostPt I.W x = sidePt I.W p t := by rw [hx, ex, hostPt_eq _ hAt.2.1 hAt.2.2.1]
    have hpy : hostPt I.W y = sidePt I.W p' t' := by rw [hy, ey, hostPt_eq _ hAt'.2.1 hAt'.2.2.1]
    obtain ⟨h0, -, a, b, hcab⟩ := hFam.2.2 c hc
    have hY : (hostPt I.W x).2 = (hostPt I.W y).2 := by
      rw [hpx, hpy]
      have h1 := hAt.2.2.2.1
      have h2 := hAt'.2.2.2.1
      zvmyh at h1 h2
      exact h1.1.trans h2.1.symm
    have key : ∀ (j : ℕ) (u : SymPt), RepPt li Q S R j u → I.IsCut S ztqqg →
        ∃ e h, u = .onEdge e h ∧ h < Q.n ∧ (Q.vtx h).2 = (hostPt I.W ztqqg).2 := by
      intro j u hu hcut
      rcases hu with ⟨hv, -⟩ | ⟨-, h, hh, hyh, (⟨-, -, rfl⟩ | ⟨-, rfl⟩)⟩
      · obtain ⟨k, -, hk', a, b, harc, hin⟩ := hv
        exact absurd by_simp_all (harc.2.2.2.2.2.1 _ hin)
      · grind
      simp_all
    obtain ⟨e, h, rfl, hh, hyh⟩ := key i s hs hcutx
    obtain ⟨e', h', rfl, hh', hyh'⟩ := key _ s' hs' hcuty
    left
    zuirz
    exact hdh h h' hh hh' hne' by_grind
end
theorem poly_eq_of_vtx {P P' : Polygon} (hn : P.n = P'.n)
    (hv : ∀ i, i < P.n → P.vtx i = P'.vtx i) : P = P' := by
  cases P with
  | mk l =>
    cases P' with
    | mk l' =>
      zucr
      have hn' : l.length = l'.length := hn
      refine List.ext_getElem hn' fun i h1 h2 => ?_
      have := hv i h1
      simp only [Polygon.vtx] at this
      rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- `HostEdgeOK` is symmetric. -/
theorem hostEdgeOK_symm {n : ℕ} {s s' : SymPt} (h : HostEdgeOK n s s') : HostEdgeOK n s' s := by
  cases s <;> cases s' <;> simp only [HostEdgeOK] at h ⊢ <;> tauto
section
variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR
variable {li : Bool}
/-- **H-R1 (list level)**: a list representing the host keys from index `i0` on evaluates to the
host polygon rotated by `i0`. -/
theorem poly_of_rep (hli : li = true ↔ Mountain.LeftInside Q)
    (hdh : DistinctHeights Q) {L : List SymPt} {i0 : ℕ}
    (hL : L.length = nk ztd S R)
    (hrep : ∀ j, j < nk ztd S R →
      RepPt li Q S R ztyxm ztxkc) :
    (⟨L.map ztbzb⟩ : Polygon) = (hostPoly Q S R).rotate i0 := by
  zukh
  apply poly_eq_of_vtx
  · show (L.map ztbzb).length = ((hostPoly Q S R).rotate i0).n
    rw [Existence.n_rotate, hostPoly_n, List.length_map, hL]
  · zun
    have hj' : j < nk ztd S R := by simpa [Polygon.n, hL] using hj
    zukcu
    have hlt : ztdhp % nk ztd S R < nk ztd S R :=
      Nat.mod_lt _ by_omega
    rw [Existence.vtx_rotate _ _ zthew, hostPoly_n,
      hostPoly_vtx hlt, ← rep_eval hQ hFam hne hR hli hdh hlt (hrep j hj')]
    zulrw
    simp_all

/-- **H-R2 (list level)**: consecutive points of a representing list satisfy `HostEdgeOK`. -/
theorem edgeOK_of_rep (hdh : DistinctHeights Q) {L : List SymPt} {i0 : ℕ}
    (hL : L.length = nk ztd S R)
    (hrep : ∀ j, j < nk ztd S R →
      RepPt li Q S R ztyxm ztxkc) :
    ∀ j, j < L.length →
      HostEdgeOK Q.n ztxkc ztyou := by
  zukh
  zujmr
  zun
  zvnlm at hj ⊢
  have hidx : (i0 + ztl % N) % N = (ztdhp % N + 1) % N := by
    grind
  have h2 := hrep ztwwp ztcv
  rw [hidx] at h2
  exact rep_edgeOK hQ hFam hne hR hdh ztcv (hrep j hj) h2
end
variable {n : ℕ}
/-- **Regularity of a host whose points form a regular cyclic list.** -/
theorem hostRegular_of_list {H : Host}
    (h : ∀ j, j < (H.pts n).length →
      HostEdgeOK n ((H.pts n).getD j ztga)
        ((H.pts n).getD (ztl % (H.pts n).length) ztga)) : HostRegular n H := h

/-- **Regularity is invariant under reversal of the point list.** -/
theorem regular_reverse {L : List SymPt}
    (h : ∀ j, j < L.length → HostEdgeOK n ztxkc ztyou) :
    ∀ j, j < L.reverse.length →
      HostEdgeOK n (L.reverse.getD j ztga) (L.reverse.getD (ztl % L.reverse.length) ztga) := by
  zun
  rw [List.length_reverse] at hj ⊢
  set m := L.length
  have hrev : ∀ k, k < m → L.reverse.getD k ztga = L.getD (m - 1 - k) ztga := by
    grind
  have hj1 : ztl % m < m := Nat.mod_lt _ by_omega
  rw [hrev j hj, hrev _ hj1]
  -- the pair is the reversed pair at index `m - 1 - (j + 1) % m`
  set k := m - 1 - ztl % m with hk
  have hkm : k < m := by_omega
  have hk1 : zts % m = m - 1 - j := by
    by_cases h1 : j + 1 < m
    · zvnnn at hk
      rw [hk, Nat.mod_eq_of_lt by_omega]; omega
    · have : j + 1 = m := by_omega
      rw [this, Nat.mod_self] at hk
      rw [hk, show m - 1 - 0 + 1 = m by omega, Nat.mod_self]; omega
  have := h k hkm
  rw [hk1] at this
  exact hostEdgeOK_symm this

/-! ## Geometric facts of rotated and reversed host polygons -/

/-- The facts the driver consumes about the polygon of its host description. -/
def PolyFacts (Q : Polygon) (S : Set ztf) (R : Set Point) (P : Polygon) : Prop :=
  P.Simple ∧ P.filled \ P.boundary = R ∧ P.boundary ⊆ Q.boundary ∪ ⋃₀ S ∧
    ∀ j, j < (hostPoly Q S R).n → ∃ j', j' < P.n ∧ P.vtx j' = (hostPoly Q S R).vtx j
section
variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR
variable (i0 : ℕ)
/-- The facts for a rotation of the host polygon. -/
theorem polyFacts_rotate : PolyFacts Q S R ((hostPoly Q S R).rotate i0) := by
  have hs := hostPts_simple hQ hFam hne hR
  have hint := DownDrv.region_eq_intHost hQ hFam hne hR
  have hbd := DownDrv.hostPoly_bd_sub hQ hFam hne hR
  zukh
  refine ⟨Existence.simple_rotate _ _ hs, ?_, ?_, ?_⟩
  · rw [Existence.filled_rotate, Existence.boundary_rotate]; grind
  · rw [Existence.boundary_rotate]; omega
  · zun
    have hn : 0 < (hostPoly Q S R).n := by_omega
    obtain ⟨i, hi, hij⟩ := Existence.exists_rot_index hn i0 j hj
    exact ⟨i, by zunrt; exact hi, by rw [Existence.vtx_rotate _ _ hi, hij]⟩

/-- The facts for a reversal of a rotation of the host polygon. -/
theorem polyFacts_rev {P : Polygon} (hn : P.n = ((hostPoly Q S R).rotate i0).n)
    (hv : ∀ k, k < ((hostPoly Q S R).rotate i0).n →
      P.vtx k = ((hostPoly Q S R).rotate i0).vtx (((hostPoly Q S R).rotate i0).n - 1 - k)) :
    PolyFacts Q S R P := by
  zudiw
  have hbd' := Mountain.rev_boundary hn hv
  refine ⟨Mountain.rev_simple hn hv hs, ?_, ?_, ?_⟩
  · rw [Mountain.rev_filled hn hv, hbd']; omega
  · simp_all
  · zun
    obtain ⟨j', hj', e⟩ := hvx j hj
    set m := ((hostPoly Q S R).rotate i0).n
    refine ⟨m - 1 - j', by_omega, ?_⟩
    grind
end
end
end DownMath
namespace DrvB
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (DirInterior rayPt chordEnd chordSet chordParam chords hseg OpenEdgePt
  edgeX edgeBot edgeTop NonHoriz)
open Chazelle.Jordan (simple_three_le simple_vtx_ne simple_vtx_succ_ne)
open DrvR (ivB qE)

/-- The direction of the code `d`: `1` for `d = 0`, `-1` otherwise. -/
def sgnD (d : ℕ) : ℝ := if d = 0 then 1 else -1
variable (d : ℕ) {q i : ℕ} {li : Bool}
theorem sgnD_cases : sgnD d = 1 ∨ sgnD d = -1 := by
  unfold sgnD; grind
theorem sgnD_mul_self : sgnD d * sgnD d = 1 := by
  rcases sgnD_cases d with h | h <;> zvmwc <;> norm_num

/-! ## Candidates -/
variable {Q : Polygon}

/-- Edge `q` of `Q` straddles the height of vertex `i` strictly. -/
def Strad (Q : Polygon) (q i : ℕ) : Prop :=
  ((Q.vtx q).2 < (Q.vtx i).2 ∧ (Q.vtx i).2 < (Q.vtx ztxam).2) ∨
    ((Q.vtx ztxam).2 < (Q.vtx i).2 ∧ (Q.vtx i).2 < (Q.vtx q).2)

/-- **A candidate** for the far end of the chord of vertex `i` in direction `σ`: edge `q`
straddles the height of `v_i` strictly and crosses it strictly on the side `σ`. -/
def Cand (Q : Polygon) (i : ℕ) (σ : ℝ) (q : ℕ) : Prop :=
  q < Q.n ∧ Strad Q q i ∧ 0 < σ * ztkvu
theorem strad_nonHoriz (h : Strad Q q i) : NonHoriz Q q := by
  unfold NonHoriz; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> intro e <;> linarith

/-- A straddling edge crosses the height of `v_i` in its open part. -/
theorem strad_open (h : Strad Q q i) :
    OpenEdgePt Q q ((edgeXAt Q q i, (Q.vtx i).2) : Point) := by
  rw [Visibility.openEdgePt_iff_edgeX (strad_nonHoriz h)]
  refine ztolz
  unfold edgeBot edgeTop
  zuwr
  · simp_all
  simp_all

/-- A point of the open part of edge `q` is in no other open edge part. -/
theorem openEdge_unique (hQ : Q.Simple) {q q' : ℕ} (hq : q < Q.n) (hq' : q' < Q.n) {z : Point}
    (h : OpenEdgePt Q q z) (h' : OpenEdgePt Q q' z) : q = q' := by
  zuct
  zubpj
  exact Chazelle.Jordan.simple_openEdge_not_mem_other hQ hq ht hq' ztnr h'.mem_edge

/-- The ray point at the crossing abscissa. -/
theorem rayPt_cross {v : Point} {σ x : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    rayPt v σ (σ * (x - v.1)) = (ztudy : Point) := by
  zubgl
  ext
  · simp only [Visibility.rayPt_fst]; grind
  simp

/-- **No candidate crossing is strictly before the far end.** -/
theorem cand_le (hQ : Q.Simple) {i : ℕ} (hi : i < Q.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hdir : DirInterior Q i σ) {q : ℕ} (hc : Cand Q i σ q) :
    σ * (chordEnd Q i σ).1 ≤ σ * edgeXAt Q q i := by
  obtain ⟨hq, hs, hside⟩ := hc
  zubgl
  have hX :=
    (strad_open hs).mem_boundary hq
  have hle : chordParam Q i σ ≤ σ * ztkvu := by
    zube

    have := (Visibility.chord_spec hQ hi hdir).2.2 _ hside hlt
    rw [rayPt_cross hσ] at this
    simp_all
  have e : σ * (chordEnd Q i σ).1 = σ * (Q.vtx i).1 + chordParam Q i σ := by
    rw [Visibility.chordEnd_fst, mul_add, ← mul_assoc, hσσ, one_mul]
  grind

/-- **The far end is a candidate crossing**, in the open part of its edge. -/
theorem far_cand (hQ : Q.Simple) (hDH : DistinctHeights Q) {i : ℕ} (hi : i < Q.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hdir : DirInterior Q i σ) :
    ∃ q, Cand Q i σ q ∧ edgeXAt Q q i = (chordEnd Q i σ).1 ∧ OpenEdgePt Q q zthvp := by
  zubgl
  set z := chordEnd Q i σ with hz
  zuizt
  have hnv : ∀ j, j < Q.n → z ≠ Q.vtx j := by
    intro j hj e
    have hy : (Q.vtx j).2 = (Q.vtx i).2 := by_simp_all
    have hji : ztsjr := by
      zuisa
    zultb
    exact Visibility.chordEnd_ne_vtx hQ hi hdir e
  obtain ⟨q, hq, t, ht, hzt⟩ := Chazelle.Jordan.exists_openEdge_of_mem_boundary Q hzb hnv
  have hop : OpenEdgePt Q q z := ⟨t, ht, hzt⟩
  zueru
  have hNH : NonHoriz Q q := by
    unfold NonHoriz
    refine hDH _ _ hq ztcv ?_
    zuchf
    by_cases h : q + 1 < Q.n
    · zvnnm at e; omega
    · rw [show q + 1 = Q.n by omega, Nat.mod_self] at e; omega
  obtain ⟨⟨hb, ht'⟩, hx⟩ := (Visibility.openEdgePt_iff_edgeX hNH).1 hop
  zukhi
  rw [hz2] at hb ht' hx
  have hxq : edgeXAt Q q i = z.1 := hx.symm
  refine ⟨q, ⟨hq, ?_, ?_⟩, hxq, hop⟩
  · unfold edgeBot at hb
    unfold edgeTop at ht'
    rcases le_total (Q.vtx q).2 (Q.vtx _).2 with h | h
    · rw [min_eq_left h] at hb; rw [max_eq_right h] at ht'
      zudxj
    · rw [min_eq_right h] at hb; rw [max_eq_left h] at ht'
      tauto
  · rw [hxq, hz, Visibility.chordEnd_fst, add_sub_cancel_left, ← mul_assoc, hσσ, one_mul]
    exact Visibility.chordParam_pos hQ hi hdir

/-- **A candidate not after the far end carries it.** -/
theorem cand_min (hQ : Q.Simple) {i : ℕ} (hi : i < Q.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hdir : DirInterior Q i σ) {q : ℕ} (hc : Cand Q i σ q)
    (hmin : σ * edgeXAt Q q i ≤ σ * (chordEnd Q i σ).1) :
    OpenEdgePt Q q zthvp := by
  have h1 := cand_le hQ hi hσ hdir hc
  zubat
  have hx : edgeXAt Q q i = (chordEnd Q i σ).1 :=
    mul_left_cancel₀ hσ0 by_grind
  have := strad_open hc.2.1
  zvnly at this
  tauto

/-! ## Walk edges -/

/-- `qE` on walk edges is injective. -/
theorem qE_inj {n w w' : ℕ} (hw : w < n) (hw' : w' < n) (h : qE li n w = qE li n w') :
    w = w' := by
  unfold qE at h; grind

/-- The walk edge of an edge of `Q`. -/
def qEi (li : Bool) (n q : ℕ) : ℕ := if li then q else if q + 1 < n then n - 2 - q else n - 1
theorem qEi_lt (li : Bool) {n q : ℕ} (hq : q < n) : qEi li n q < n := by
  unfold qEi; grind
theorem qE_qEi (li : Bool) {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) : qE li n (qEi li n q) = q := by
  unfold qE qEi; grind

/-- **A σ-nearest candidate among walk edges** (a set `ES` containing a walk edge whose edge of
`Q` carries the far end) carries the far end. -/
theorem scan_min (hQ : Q.Simple) (hDH : DistinctHeights Q) {i : ℕ} (hi : i < Q.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hdir : DirInterior Q i σ) {li : Bool} {ES : ℕ → Prop} {w₀ w : ℕ}
    (hw₀ : w₀ < Q.n) (hw₀E : ES w₀) (hz₀ : OpenEdgePt Q (qE li Q.n w₀) zthvp)
    (_hwE : ES w) (hc : Cand Q i σ ztczw)
    (hmin : ∀ w', ES w' → w' < Q.n → Cand Q i σ ztrur →
      σ * edgeXAt Q ztczw i ≤ σ * edgeXAt Q ztrur i) :
    OpenEdgePt Q ztczw zthvp := by
  obtain ⟨q, hcq, hxq, hoq⟩ := far_cand hQ hDH hi hσ hdir
  have hq₀ :=
    openEdge_unique hQ hcq.1 (DownMath.qE_lt li hw₀) hoq hz₀
  subst hq₀
  have := hmin w₀ hw₀E hw₀ hcq
  rw [hxq] at this
  exact cand_min hQ hi hσ hdir hc this

/-! ## The record of a vertex chord -/

/-- **The record of the vertex chord** of `i` in direction `sgnD d` whose far end is on walk edge
`w`: height vertex `i`, the walk edge starting at `v_i` and `w`, as (left end, right end). -/
def vtrip (li : Bool) (n i d w : ℕ) : ℕ × ℕ × ℕ :=
  if d = 0 then (i, ivB li n i, w) else (i, w, ivB li n i)
theorem ivB_ivB (li : Bool) {n i : ℕ} (hi : i < n) : ivB li n (ivB li n i) = i := by
  zujqn
theorem wStart_eq_ivB (li : Bool) (n p : ℕ) : DownBase.wStart li n p = ivB li n p := rfl

/-- A point of the open part of edge `qE w` of `Q` is a point of walk edge `w` at a parameter in
`(0, 1)`. -/
theorem openEdge_walk (hli : li = true ↔ Mountain.LeftInside Q) (hn : 3 ≤ Q.n)
    {w : ℕ} (hw : w < Q.n) {z : Point} (hz : OpenEdgePt Q ztczw z) :
    ∃ t ∈ Ioo (0 : ℝ) 1, sidePt ztkb w t = z := by
  obtain ⟨s, hs, rfl⟩ := hz
  have hw1 : zthkx % Q.n < Q.n := Nat.mod_lt _ by_omega
  have hv0 := DownMath.walk_vtx hli hw
  have hv1 := DownMath.walk_vtx hli hw1
  zulji
  rcases DownMath.edge_ends li by_omega hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨s, hs, ?_⟩
    zujrb
  · refine ⟨1 - s, by_simp_all, ?_⟩
    unfold sidePt; rw [hWn, hv0, hv1, h1, h2, ← Geometry.lerp_symm]

/-- **The record of a vertex chord.**  If the far end of the chord of vertex `i` in direction
`sgnD d` lies in the open part of edge `qE w` of `Q`, the record `vtrip li n i d w` describes the
chord, is attached at both ends, and both of its ends are proper positions. -/
theorem vtrip_ok (hQ : Q.Simple) (hDH : DistinctHeights Q) {li : Bool}
    (hli : li = true ↔ Mountain.LeftInside Q) {i d w : ℕ} (hi : i < Q.n) (_hd : d ≤ 1)
    (hdir : DirInterior Q i ztbgl) (hw : w < Q.n)
    (hz : OpenEdgePt Q ztczw ztxdy) :
    (recOf ztfiy).toSet ztd Q = chordSet Q i ztbgl ∧
      (recOf ztfiy).Attached ztd Q ∧
      ProperPos ztd Q Q.n (recOf ztfiy).lpos ∧
      ProperPos ztd Q Q.n (recOf ztfiy).rpos ∧
      (vtrip li Q.n i d w).1 < Q.n := by
  zuhm
  set W := interiorWalk Q with hWdef
  set σ := sgnD d with hσdef
  have hσ := sgnD_cases d
  zueru
  zulji
  zudyr
  set wv := ivB li Q.n i with hwv
  have hwvn : wv < Q.n := DownMath.ivB_lt li hi
  -- the vertex end
  have hWv : W.vtx wv = Q.vtx i := by
    rw [hWdef, DownMath.walk_vtx hli hwvn, hwv, ivB_ivB li hi]
  have hst : i = DownBase.wStart li Q.n wv := by rw [wStart_eq_ivB, hwv, ivB_ivB li hi]
  have hposv := DownBase.pos_start hQ hDH hli hwvn hst
  have hparv : I.param Q ztdqz = 0 := by
    rw [DownBase.param_eq hQ hDH hli hwvn, DownBase.wa_eq hQ hDH hli hwvn, ← hst, sub_self,
      zero_div]
  -- the far end
  set z := chordEnd Q i σ with hzdef
  obtain ⟨t, ht, hzt⟩ := openEdge_walk hli hn3 hw hz
  have hne := DownBase.wa_wb_snd_ne hQ hDH hli hw
  have hd0 := sub_ne_zero.2 hne.symm
  have hzt' : Geometry.lerp (I.wa w) (I.wb w) t = z := hzt
  have hpart : I.param Q ztcyi = t := by
    rw [DownBase.param_eq hQ hDH hli hw]
    have hy := congrArg Prod.snd hzt'
    zufav
    zukhi
    grind
  have hposz : I.pos Q ztcyi = z := by
    zunuw; grind
  -- the chord as a segment between its two ends
  zukbh
  zujzi
  have hadm := hHC
  zubdo
  obtain ⟨A, B, hAB, hcAB, -, hopen, hWA, hWB⟩ := hM.ends _ hadm
  have hσσ := sgnD_mul_self d
  zuiyw
  have hvb : Q.vtx i ∈ Q.boundary := zteyp
  zuizt
  have hD : I.D = Q.filled \ Q.boundary := rfl
  have hend : ∀ x ∈ chordSet Q i σ, x ∈ Q.boundary → x = A ∨ x = B := by
    intro x hx hxb
    rw [hcAB] at hx
    obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hx
    zunm
    · zuji
      · grind
      · right; rw [hs, hs1, Geometry.lerp_one]
    · zufxr
  have hvA := hend _ ztdte hvb
  have hzA := hend _ ztsxu hzb
  have hvz := (Visibility.chordEnd_ne_vtx hQ hi hdir).symm
  have hWEv : WalkEnd I.W zthvr ztdli := by
    grind
  have hWEz : WalkEnd I.W zthvr z := by
    grind
  -- the attachments
  have hIW : I.W = W := rfl
  have attv : SideAttach W zthvr wv 0 := by
    obtain ⟨p, s, hA, hps⟩ := hWEv.1
    zuctp

    have := FactsInterior.pos_unique hWs hp (by zvnux; exact hwvn) hs0 hs1 le_rfl one_pos
      (by rw [hps, Chazelle.Chain.sidePt_zero, hWv])
    zugqr

  have attz : SideAttach W zthvr w t := by
    obtain ⟨p, s, hA, hps⟩ := hWEz.1
    zuctp

    have := FactsInterior.pos_unique hWs hp (by zvnux; exact hw) hs0 hs1 ht.1.le ht.2
      (by rw [hps, hzt])
    zugqr

  have pv : ProperPos I Q Q.n ztdqz := ⟨by_grind, by_grind, hi⟩
  have pz : ProperPos I Q Q.n ztcyi := ⟨by_grind,
    by grind, hi⟩
  have hv1 : (Q.vtx i).1 = ((Q.vtx i).1, (Q.vtx i).2).1 := rfl
  -- the two directions
  unfold vtrip
  by_cases hd0 : d = 0
  · rw [ite_eq_left hd0]
    have hσ1 : ztgbc := by rw [hσdef, hd0]; rfl
    have hlt : (Q.vtx i).1 < z.1 := by
      rw [hzdef, Visibility.chordEnd_fst,
        show σ * chordParam Q i σ = chordParam Q i σ by rw [hσ1, one_mul]]
      linarith
    have hset : (recOf (i, wv, w)).toSet I Q = chordSet Q i σ := by
      show hseg (Q.vtx i).2 (I.pos Q ztdqz).1 (I.pos Q ztcyi).1 = _
      rw [hposv, hposz, Visibility.chordSet_eq_hseg, ← hzdef, min_eq_left hlt.le,
        max_eq_right hlt.le]
    refine ⟨hset, ?_, pv, pz, hi⟩
    unfold CRec.Attached
    zucju
    zujx
    · show SideAttach W _ wv ztzto; grind
    · show SideAttach W _ w ztztn; grind
  · rw [ite_eq_right hd0]
    have hσ1 : ztgbb := by rw [hσdef]; unfold sgnD; grind
    have hlt : z.1 < (Q.vtx i).1 := by
      rw [hzdef, Visibility.chordEnd_fst,
        show σ * chordParam Q i σ = -chordParam Q i σ by rw [hσ1, neg_one_mul]]
      linarith
    have hset : (recOf (i, w, wv)).toSet I Q = chordSet Q i σ := by
      show hseg (Q.vtx i).2 (I.pos Q ztcyi).1 (I.pos Q ztdqz).1 = _
      rw [hposv, hposz, Visibility.chordSet_eq_hseg, ← hzdef, min_eq_right hlt.le,
        max_eq_left hlt.le]
    refine ⟨hset, ?_, pz, pv, hi⟩
    unfold CRec.Attached
    zucju
    zujx
    · show SideAttach W _ w ztztn; grind
    · show SideAttach W _ wv ztzto; grind
end
end DrvB
namespace BuildRam
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
@[expose] public section
def dirR : Stmt := Stmt.ren σ locDir

/-- The key decision in band `bBuild`. -/
def cmpR : Stmt := Stmt.ren σ cmpPos

/-- The registers `dirR` writes. -/
def BdirR (r : ℕ) : Bool := Bdir ztewy
theorem σ_10502 : σ 10502 = 10502 := by_decide
variable {P : Polygon} {W : ℕ} {r : ℕ}
/-- **The direction procedure in band `bBuild`.** -/
theorem dirR_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (d : Config)
    (hw : WordsBounded W d) (hDW : d.nreg 40000 + 6 ≤ W)
    (hCW : LocChainWF P W d.nmem ztmik) {M : Model}
    (hM : ModelDescAt d.nmem ztmik zta M) (he : d.nreg 40002 < M.W.n) :
    ∃ d' k, Exec P W dirR d d' k ∧ k ≤ 5100 ∧ FrameB BdirR d d' ∧
      d'.nreg 10502 = dirCode M (d.nreg 40002) := by
  zucdh
  obtain ⟨c', k, ex, hk, hfr, hdir⟩ := locDir_ok P W ztfql hw'
    ⟨hG, hW, hDW, hCW, M, hM, he⟩
  refine ⟨cfgRen σ c', k, exec_of_ren σ_σ ex, hk, ⟨fun r hr => ?_, fun r hr => ?_, hfr.2.2.1,
    hfr.2.2.2.1, hfr.2.2.2.2⟩, ?_⟩
  · have := hfr.1 ztewy hr
    zughj

  · have := hfr.2.1 ztewy hr
    zughi

  tauto

/-- The registers `cmpR` writes. -/
def BcmpR (r : ℕ) : Bool := decide ztcko || decide (r = 40102)
theorem wr_cmpPos' : wr (fun r => BcmpR ztewy) cmpPos = true := by_decide
theorem wr_cmpR : wr BcmpR cmpR = true := by
  rfl

/-- **The key decision in band `bBuild`.** -/
theorem cmpR_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (d : Config)
    (hw : WordsBounded W d) (h1 : d.nreg 40102 = 1) (hxn : d.nreg 10501 ≤ P.n) :
    ∃ d' k, Exec P W cmpR d d' k ∧ k ≤ 260 ∧ FrameB BcmpR d d' ∧
      d'.nreg 40102 = (if keyDec zta P.n ⟨d.nreg 10500, d.nreg 10501⟩ (d.nreg 10502)
        ⟨d.nreg 10011, d.nreg 10012⟩ then 1 else 0) := by
  zucdh
  obtain ⟨c', k, ex, hk, hr⟩ := cmpPos_exec (P := P) hG hW ztfql hw' h1 hxn
  have ex' := exec_of_ren σ_σ ex
  refine ⟨cfgRen σ c', k, ex', hk, exec_frameB ex' wr_cmpR, ?_⟩
  tauto

/-! ## Write sets -/
theorem σ_cases (r : ℕ) : (40000 ≤ r ∧ r < 41000 ∧ σ r = r + 10000) ∨
    (50000 ≤ r ∧ r < 51000 ∧ σ r = r - 10000) ∨ (41000 ≤ r ∧ r < 42000 ∧ σ r = r + 49000) ∨
    (90000 ≤ r ∧ r < 91000 ∧ σ r = r - 49000) ∨
    ((r < 40000 ∨ (42000 ≤ r ∧ r < 50000) ∨ (51000 ≤ r ∧ r < 90000) ∨ 91000 ≤ r) ∧ σ r = r) := by
  zumvp
theorem BdirR_true (h : BdirR r = true) :
    ztdev ∨ (40030 ≤ r ∧ r < 40100) := by
  unfold BdirR Bdir at h
  zubzj
  rcases σ_cases r with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ <;>
    zvncq at h <;> omega
theorem BcmpR_true (h : BcmpR r = true) : ztcko ∨ r = 40102 := by
  unfold BcmpR at h; simp_all
theorem wr_dirR : wr BdirR dirR = true := by
  rw [dirR, wr_ren σ_σ]
  rfl

/-! ## One half of the comparison -/

/-- Direction of the query edge `qe`, then the decision of the position `(se, sh)` against the
query `(qe, qh)`: the direction code into `dd`, the decision bit into `dst`. -/
def halfS (qe qh se sh dd dst : ℕ) : Stmt :=
  .seq (.instr (.copyN 40002 qe))
    (.seq dirR (.seq (block [.copyN dd 10502, .copyN 10500 qe, .copyN 10501 qh, .copyN 10011 se,
      .copyN 10012 sh, .constN 40102 1]) (.seq cmpR (.instr (.copyN dst 40102)))))

/-- The registers `halfS` writes (outside its two outputs). -/
def Bhalf (r : ℕ) : Bool :=
  decide ztdev || decide ztngj

/-- The registers `halfS` writes. -/
def BhalfS (dd dst r : ℕ) : Bool := Bhalf r || decide (r = dd) || decide ztogo

/-- The write set of `halfS`. -/
theorem wr_halfS {qe qh se sh dd dst : ℕ} : wr ztjgv ztdhn = true := by
  have h1 : wr ztjgv dirR = true :=
    wr_mono (fun r hr => by
      rcases BdirR_true hr with h | h <;> zunpl <;> omega) wr_dirR
  have h2 : wr ztjgv cmpR = true :=
    wr_mono (fun r hr => by
      rcases BcmpR_true hr with h | h <;> zunpl <;> omega) wr_cmpR
  simp only [halfS, wr, block, wrOK, h1, h2, Bool.and_true, Bool.true_and]
  zunpl

/-- **One half of the comparison.**  The registers `qe, qh, se, sh, dd, dst` lie in
`42100 … 42199`, the outputs are distinct from each other and from the inputs. -/
theorem halfS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (d : Config)
    (hw : WordsBounded W d) {qe qh se sh dd dst : ℕ}
    (hr : ∀ x ∈ [qe, qh, se, sh, dd, dst], 42100 ≤ x ∧ x < 42200)
    (hdd : dd ∉ [qe, qh, se, sh, dst]) (hdst : dst ∉ [qe, qh, se, sh])
    (hDW : d.nreg 40000 + 6 ≤ W) (hCW : LocChainWF P W d.nmem ztmik) {M : Model}
    (hM : ModelDescAt d.nmem ztmik zta M) (he : d.nreg qe < M.W.n)
    (hqh : d.nreg qh ≤ P.n) :
    ∃ d' k, Exec P W ztdhn d d' k ∧ k ≤ 5400 ∧
      d'.nreg dd = dirCode M ztmip ∧
      d'.nreg dst = (if keyDec zta P.n ⟨d.nreg qe, d.nreg qh⟩ (dirCode M ztmip)
        ⟨d.nreg se, d.nreg sh⟩ then 1 else 0) ∧
      FrameB ztjgv d d' := by
  zvmwt at hr
  zvnvw at hdd hdst
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨e1, e2⟩, ⟨f1, f2⟩⟩ := hr
  obtain ⟨n1, n2, n3, n4, n5⟩ := hdd
  obtain ⟨m1, m2, m3, m4⟩ := hdst
  -- the edge
  have x₁ := Exec.copyN (P := P) hw 40002 qe
  set d₁ : Config := { d with nreg := upd d.nreg 40002 (d.nreg qe) } with hd₁
  have w₁ : WordsBounded W d₁ := x₁.wb_right
  have r₁ : ∀ r, r ≠ 40002 → d₁.nreg r = d.nreg r := fun r hr => by_simp_all
  obtain ⟨d₂, k₂, x₂, hk₂, f₂, dir₂⟩ := dirR_exec (P := P) hG hW d₁ w₁
    by_simp_all by_simp_all
    (M := M) by_simp_all by_simp_all
  have r₂ : ∀ r, BdirR r = false → d₂.nreg r = d₁.nreg r := f₂.1
  have nb : ∀ r, 42100 ≤ r → BdirR r = false := fun r hr => by
    by_contra h; have := BdirR_true (Bool.not_eq_false _ ▸ h); omega
  zuboj
  have v : ∀ r, 42100 ≤ r → r < 42200 → d₂.nreg r = d.nreg r := fun r h1 h2 => by
    grind
  rw [show d₁.nreg 40002 = d.nreg qe by rw [hd₁]; simp] at dir₂
  -- the loads
  obtain ⟨d₃, k₃, x₃, hk₃, q⟩ : ∃ d₃ k₃, Exec P W (block [.copyN dd 10502, .copyN 10500 qe,
      .copyN 10501 qh, .copyN 10011 se, .copyN 10012 sh, .constN 40102 1]) d₂ d₃ k₃ ∧ k₃ = 6 ∧
      (d₃.nreg dd = dirCode M ztmip ∧ d₃.nreg 10500 = d.nreg qe ∧
        d₃.nreg 10501 = d.nreg qh ∧ d₃.nreg 10011 = d.nreg se ∧ d₃.nreg 10012 = d.nreg sh ∧
        d₃.nreg 40102 = 1 ∧ d₃.nreg 10502 = dirCode M ztmip ∧
        ∀ r, r ≠ dd → r ≠ 10500 → r ≠ 10501 → r ≠ 10011 → r ≠ 10012 → r ≠ 40102 →
          d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem := by
    exec_block
    · omega
    · refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_⟩, rfl⟩ <;>
        simp (disch := omega) only [upd_same, upd_other]
      all_goals first
        | exact dir₂
        | (rw [v _ by_omega by_omega])
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := q.1
  zuchd
  obtain ⟨d₄, k₄, x₄, hk₄, f₄, bit₄⟩ := cmpR_exec (P := P) hG hW d₃ w₃ q6 by_omega
  rw [q2, q3, q4, q5, q7] at bit₄
  zujah
  have ex : Exec P W ztdhn d
      { d₄ with nreg := upd d₄.nreg dst (d₄.nreg 40102) } (1 + (k₂ + (k₃ + (k₄ + 1)))) :=
    x₁.seq (x₂.seq (x₃.seq (x₄.seq (Exec.copyN w₄ dst 40102))))
  have hwr := wr_halfS (qe := qe) (qh := qh) (se := se) (sh := sh) (dd := dd) (dst := dst)
  refine ⟨_, _, ex, by_omega, ?_, ?_, exec_frameB ex hwr⟩
  · simp only [upd_other _ _ _ n5]
    rw [f₄.1 _ (by
      unfold BcmpR; grind), q1]
  · zufb
    omega

/-! ## Descriptors survive changes of memory above them -/

/-- A host layout depends only on the memory below its end. -/
theorem hostAt_agree {m m' : ℕ → ℕ} {B E : ℕ} {H : Host} (h : HostAt m B H)
    (hE : B + 3 * H.length + 4 ≤ E) (hm : ∀ a, a < E → m' a = m a) : HostAt m' B H := by
  zuko

/-- **A well-formed model descriptor survives every change of memory at or above its bound.** -/
theorem desc_agree {E : ℕ} {m m' : ℕ → ℕ} {D : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hM : ModelDescAt m D zta M)
    (hm : ∀ a, a < E → m' a = m a) : ModelDescAt m' D zta M ∧ ModelDescWF P E m' D := by
  zuglm

  zutl
  · zuqs

    have hH' : ztyye := by
      zvmxy; exact hostAt_agree hH by_omega hm
    have hC' : ChainDescAt m' ztef zta H C :=
      ⟨hH', hP, by_grind, by_grind,
        by grind, by_grind⟩
    refine ⟨Or.inl ⟨by_omega, H, C, hC', rfl⟩, hD, fun _ => ztmqm⟩
    have hHH := hostAt_unique hC''.1 hC'.1
    zular
    have hCC := chain_eq_of_desc hC'' hC'
    simp_all
  · refine ⟨Or.inr ⟨by_omega, by_grind, rfl⟩, hD,
      fun h0 => absurd (e0.symm.trans h0) by_omega⟩
def wtF (lo hi ea eb pz lt : ℕ) : ℕ :=
  if lt = 1 then min zttjp hi - max ea lo else ztcw - (min ea hi - max zttjp lo)
variable {lo hi ea eb pz lt : ℕ} {P : Polygon} {W : ℕ} (d : Config)
/-- **The parameter bit replaces the ceiling** (off the counted interval the ceiling does not
matter). -/
theorem arcWtNat_eq_wtF {fa fb : ℝ} {counted : ℕ → Prop}
    (hc : counted eb ↔ lo ≤ eb ∧ eb < hi) (hpz : pz = 1 ↔ counted eb ∧ fb ≠ 0) (hpz1 : pz ≤ 1)
    (hlt : lt = 1 ↔ (ea : ℝ) + fa < eb + fb) :
    arcWtNat lo hi ea fa eb fb = wtF lo hi ea eb pz lt := by
  unfold arcWtNat wtF keyCeil
  by_cases hl : (ea : ℝ) + fa < eb + fb
  · grind
  · rw [ite_eq_right hl, ite_eq_right (fun h => hl (hlt.1 h))]
    by_cases hcb : counted eb
    · grind
    · have : pz = 0 := by_grind
      rw [this, Nat.add_zero]
      grind

/-- The counted interval of a described model. -/
def loOf (m : ℕ → ℕ) (D : ℕ) : ℕ := if m D = 0 then 6 else 0

/-- The end of the counted interval of a described model. -/
def hiOf (m : ℕ → ℕ) (D n : ℕ) : ℕ := if m D = 0 then 2 * m ztclg + 6 else n

/-- **The counted edges of a described model** form `[loOf, hiOf)`, within the walk. -/
theorem countedIv {m : ℕ → ℕ} {D : ℕ} {P : Polygon} {M : Model}
    (hM : ModelDescAt m D zta M) :
    (∀ p, p < M.W.n → (M.counted p ↔ loOf m D ≤ p ∧ p < hiOf m D P.n)) ∧
      hiOf m D P.n ≤ M.W.n := by
  rcases hM with ⟨h0, H, C, hC, rfl⟩ | ⟨h1, -, rfl⟩
  · zukdn
    unfold loOf hiOf
    rw [ite_eq_left h0, ite_eq_left h0, show D + 3 = D + 1 + 2 by omega, hm, chainModel_n]
    exact ⟨fun p hp => chainModel_counted_iff C p (by rw [chainModel_n]; exact hp), by_omega⟩
  · zubp
    unfold loOf hiOf
    rw [ite_eq_right by_omega, ite_eq_right by_omega, interiorModel_n, hn]
    refine ⟨fun p hp => ?_, le_rfl⟩
    rw [interiorModel_counted_iff _ p (by rw [interiorModel_n, hn]; exact hp), hn]

/-! ## The counted interval on the machine -/

/-- The length of the counted interval of a described model. -/
def hdOf (m : ℕ → ℕ) (D n : ℕ) : ℕ := if m D = 0 then 2 * m ztclg else n
theorem hdOf_eq (m : ℕ → ℕ) (D n : ℕ) : hdOf m D n = hiOf m D n - loOf m D := by
  unfold hdOf hiOf loOf; grind

/-- The counted interval: `r44020 = lo`, `r44021 = hi - lo`; also `r41023` the model kind and
`r41019 = 1` (the parameter test reads them). -/
def lohiS : Stmt :=
  .seq (block [.loadN 41023 40000, .constN 41019 1])
    (.ifLtN 41023 41019
      (block [.constN 44020 6, .constN 44022 3, .addN 44022 44022 40000, .loadN 44021 44022,
        .addN 44021 44021 44021])
      (block [.constN 44020 0, .inputSize 44021]))
theorem wr_lohiS : wr (fun r => decide (r = 41023 ∨ r = 41019 ∨ r = 44020 ∨ r = 44021 ∨
    r = 44022)) lohiS = true := by_decide

/-- **The counted interval on the machine.** -/
theorem lohiS_exec (hw : WordsBounded W d) {D : ℕ}
    (hD : d.nreg 40000 = D) (hW : d.nmem D = 0 → 2 * d.nmem ztclg ≤ W)
    (hDW : D + 3 ≤ W) (hn : P.n ≤ W) (h6 : 6 ≤ W) :
    ∃ d' k, Exec P W lohiS d d' k ∧ k ≤ 12 ∧
      d'.nreg 44020 = loOf d.nmem D ∧ d'.nreg 44021 = hdOf d.nmem D P.n ∧
      d'.nreg 41023 = d.nmem D ∧ d'.nreg 41019 = 1 ∧
      FrameB (fun r => decide (r = 41023 ∨ r = 41019 ∨ r = 44020 ∨ r = 44021 ∨ r = 44022)) d d' := by
  suffices H : ∃ d' k, Exec P W lohiS d d' k ∧ k ≤ 12 ∧
      d'.nreg 44020 = loOf d.nmem D ∧ d'.nreg 44021 = hdOf d.nmem D P.n ∧
      d'.nreg 41023 = d.nmem D ∧ d'.nreg 41019 = 1 by
    obtain ⟨d', k, x, hk, h1, h2, h3, h4⟩ := H
    exact ⟨d', k, x, hk, h1, h2, h3, h4, exec_frameB x wr_lohiS⟩
  unfold lohiS
  refine spec_seq ?_
  exec_block
  · omega
  by_cases h0 : d.nmem D = 0
  · have hW' := hW h0
    zuek
    exec_block
    · omega
    · omega
    · config_simp; omega
    · config_simp; grind
    · refine ztcot <;> config_simp
      · zumtj
      · unfold hdOf; grind
      simp_all
  · zudx
    exec_block
    · omega
    · omega
    · refine ztcot <;> config_simp
      · zumtj
      · unfold hdOf; simp_all
      simp_all

/-! ## The parameter test in band `bBuild` -/

/-- `Gran.pzStmt` renamed into band `bBuild` (`r41110`, `r41111` in, `r41112` out). -/
def pzR : Stmt := Stmt.ren σ Gran.pzStmt

/-- The registers `pzR` writes. -/
def BpzR (r : ℕ) : Bool := Gran.Bpz ztewy
theorem wr_pzR : wr BpzR pzR = true := by
  rfl
theorem BpzR_true {r : ℕ} (h : BpzR r = true) :
    ztdev ∨ (40000 < r ∧ r < 40100) ∨ (41110 ≤ r ∧ r < 41120) := by
  simp only [BpzR, Gran.Bpz, Bdir, Bool.or_eq_true, decide_eq_true_eq] at h
  unfold σ at h
  grind

/-- **The parameter test**: `r41112 = 1` iff the edge `r41110` is counted and the position
`⟨r41110, r41111⟩` has a nonzero parameter. -/
theorem pzR_exec {M : Model} (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (d : Config) (hw : WordsBounded W d) {D e h : ℕ} (h40 : d.nreg 40000 = D)
    (hM : ModelDescAt d.nmem D zta M) (h23 : d.nreg 41023 = d.nmem D)
    (h19 : d.nreg 41019 = 1) (h110 : d.nreg 41110 = e) (h111 : d.nreg 41111 = h)
    (he : e < M.W.n) (hh : h ≤ P.n) (hDW : D + 6 ≤ W) (hCW : LocChainWF P W d.nmem D) :
    ∃ d' k, Exec P W pzR d d' k ∧ k ≤ 6000 ∧ FrameB BpzR d d' ∧ d'.nreg 41112 ≤ 1 ∧
      (d'.nreg 41112 = 1 ↔ M.counted e ∧ M.param zta ztcq ≠ 0) := by
  zucdh
  obtain ⟨c', k, ex, hk, hfr, h1, h2⟩ := Gran.pz_exec (P := P) (W := W) hG hW ztfql hw'
    (MD := D) (e := e) (h := h) h40 hM h23 h19 h110 h111 he hh hDW hCW
  refine ⟨cfgRen σ c', k, exec_of_ren σ_σ ex, hk, ⟨fun r hr => ?_, fun r hr => ?_, hfr.2.2.1,
    hfr.2.2.2.1, hfr.2.2.2.2⟩, h1, h2⟩
  · have := hfr.1 ztewy hr
    zughj

  · have := hfr.2.1 ztewy hr
    zughi

/-! ## The weight on the machine -/

/-- The weight in coordinates shifted by `lo` (`h = hi - lo`), so that no value exceeds the
counted interval. -/
def wtG (lo h ea eb pz lt : ℕ) : ℕ :=
  if lt = 1 then min ztqmj h - zttjo else h - (min zttjo h - ztqmj)

/-- The shifted form. -/
theorem wtF_eq_wtG (hlh : lo ≤ hi) (hpz : pz = 1 → lo ≤ eb)
    (hpz1 : pz ≤ 1) : wtF lo hi ea eb pz lt = wtG lo ztcw ea eb pz lt := by
  unfold wtF wtG
  have : pz = 0 ∨ pz = 1 := by_omega
  rcases this with rfl | rfl
  · split_ifs <;> simp only [Nat.min_def, Nat.max_def] <;> split_ifs <;> omega
  grind

/-- `wtG` of `lo = r44020`, `h = r44021`, `ea = r42110`, `eb = r42113`, `pz = r41112`,
`lt = r43120` into `r43121`. -/
def wtS : Stmt :=
  .seq (block [.subN 43122 42113 44020, .addN 43122 43122 41112, .subN 43127 42110 44020])
    (.ifLtN 43120 43011
      (.seq (.ifLtN 43127 44021 (.instr (.copyN 43123 43127)) ztovi)
        (block [.subN 43125 43123 43122, .subN 43121 44021 43125]))
      (.seq (.ifLtN 43122 44021 (.instr (.copyN 43123 43122)) ztovi)
        (.instr (.subN 43121 43123 43127))))
theorem wr_wtS : wr ztzfr wtS = true := by_decide

/-- **The weight on the machine.** -/
theorem wtS_exec (hw : WordsBounded W d)
    (h1 : d.nreg 43011 = 1) (hlt : d.nreg 43120 ≤ 1)
    (hs : d.nreg 42113 - d.nreg 44020 + d.nreg 41112 ≤ W) :
    ∃ d' k, Exec P W wtS d d' k ∧ k ≤ 12 ∧
      d'.nreg 43121 = wtG ztmim ztmin zthwg ztgig
        ztvop ztqlq ∧
      FrameB ztzfr d d' := by
  suffices H : ∃ d' k, Exec P W wtS d d' k ∧ k ≤ 12 ∧
      d'.nreg 43121 = wtG ztmim ztmin zthwg ztgig
        ztvop ztqlq by
    zuwp
    exact ⟨d', k, x, hk, hv, exec_frameB x wr_wtS⟩
  unfold wtS wtG
  refine spec_seq ?_
  exec_block
  · simp_all
  set t := d.nreg 42113 - d.nreg 44020 + d.nreg 41112 with ht
  set u := d.nreg 42110 - d.nreg 44020 with hu
  by_cases hl : d.nreg 43120 < 1
  · zuek
    zufa
    zujl
    by_cases a1 : u < d.nreg 44021
    · refine spec_ifLtN_true by_simp_all
        ztcjb
      exec_block
      zubsc
      config_simp
      omega
    · refine spec_ifLtN_false by_simp_all
        ztcjb
      exec_block
      zubsc
      config_simp
      omega
  · zudx
    zubek
    zujl
    by_cases a1 : t < d.nreg 44021
    · refine spec_ifLtN_true by_simp_all
        ztcjb
      zujfn
      config_simp
      omega
    · refine spec_ifLtN_false by_simp_all
        ztcjb
      zujfn
      simp_all
end
end BuildRam
namespace Restore
open Machine Machine.Stmt Programs
@[expose] public section
def headS : Stmt := block [.loadN 80013 80012, .addN 80036 80012 80021, .loadN 80014 80036,
  .addN 80036 80012 80022, .loadN 80015 80036, .addN 80036 80036 80021, .loadN 80016 80036,
  .copyN 80017 ALLOC, .copyN 80031 80015, .constN 80030 0]

/-- Copy one chord triple to the allocator, bumping it by `3`. -/
def copyBody : Stmt := block [.loadN 80033 80031, .storeN ALLOC 80033, .addN ALLOC ALLOC 80020,
  .addN 80031 80031 80020, .loadN 80033 80031, .storeN ALLOC 80033, .addN ALLOC ALLOC 80020,
  .addN 80031 80031 80020, .loadN 80033 80031, .storeN ALLOC 80033, .addN ALLOC ALLOC 80020,
  .addN 80031 80031 80022, .addN 80030 80030 80020]

/-- The copy loop. -/
def copyS : Stmt := .whileLtN 80030 80013 copyBody

/-- Set up the reservation. -/
def midS : Stmt := block [.copyN 80018 80013, .copyN 80043 ALLOC, .constN 80034 0]

/-- Reserve three words (one per step). -/
def resBody : Stmt := block [.addN ALLOC ALLOC 80020, .addN ALLOC ALLOC 80020,
  .addN ALLOC ALLOC 80020, .addN 80034 80034 80020]

/-- The reservation loop (`3 R` words). -/
def resS : Stmt := .whileLtN 80034 80014 resBody

/-- Set up the region loop. -/
def preRegS : Stmt := block [.constN 80040 0, .addN 80041 80016 80021]

/-- The arguments of the splitting step. -/
def argS : Stmt := block [.copyN 81000 80000, .copyN 81001 80012, .copyN 81002 80040,
  .copyN 81003 80004, .copyN 81004 80006, .copyN 81005 80019, .copyN 81006 80003]

/-- Append the returned chord triple. -/
def appS : Stmt := block [.storeN 80043 81008, .addN 80043 80043 80020, .storeN 80043 81009,
  .addN 80043 80043 80020, .storeN 80043 81010, .addN 80043 80043 80020,
  .addN 80018 80018 80020]

/-- Call the splitting step and append its chord if it found one. -/
def callS (sF : Stmt) : Stmt := .seq argS (.seq sF ztprt)

/-- The step of the region loop. -/
def regBody (sF : Stmt) : Stmt :=
  .seq ztozd (.seq (.ifLtN 80003 80042 ztvkx .skip)
    ztiqs)

/-- The region loop. -/
def regS (sF : Stmt) : Stmt := .whileLtN 80040 80014 ztwcn

/-- Build the normal form of the list. -/
def buildS (sB : Stmt) : Stmt :=
  .seq zthtf
    (.seq sB (block [.copyN 80012 40003]))

/-- One round. -/
def roundBody (sF sB : Stmt) : Stmt :=
  .seq headS (.seq copyS (.seq midS (.seq resS (.seq preRegS (.seq ztwcq
    (.seq (buildS sB) ztnse))))))

/-- Initialisation. -/
def initS : Stmt := block [.constN 80020 1, .constN 80021 2, .constN 80022 3, .constN 80023 5,
  .constN 80024 0, .copyN 80012 80001, .constN 80010 0, .addN 80011 80002 80020,
  .addN 80019 80002 80003]

/-- **The restoration driver.** -/
def restoreStmt (sF sB : Stmt) : Stmt :=
  .seq initS (.seq (.whileLtN 80010 80011 zttyy) (block [.copyN 80005 80012]))

/-! ## The frame relative to a fixed base -/

/-- **The frame of the driver relative to the base `A₀`**: registers outside the bands
unchanged (except the allocator), memory below `A₀` unchanged, nothing emitted, the allocator
nondecreasing and raised by at most the step count. -/
def RF (bands : Finset ℕ) (A₀ : ℕ) (c c' : Config) (k : ℕ) : Prop :=
  ztgni ∧
    ztimw ∧
    ztpt ∧
    (∀ a, a < A₀ → c'.rmem a = c.rmem a) ∧
    c'.output = c.output ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k
variable {B : Finset ℕ} {A₀ : ℕ} {c c' : Config} {k : ℕ}
theorem RF.trans {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : RF B A₀ c c₁ k₁)
    (h₂ : RF B A₀ c₁ c₂ k₂) : RF B A₀ c c₂ ztbct := by
  zugj

  exact ⟨fun r hr hra => (r₂ r hr hra).trans (r₁ r hr hra), fun r hr => (rr₂ r hr).trans (rr₁ r hr),
    fun a ha => (m₂ a ha).trans (m₁ a ha), fun a ha => (rm₂ a ha).trans (rm₁ a ha),
    o₂.trans o₁, a₁.trans a₂, by_omega⟩
theorem RF.mono {B B' : Finset ℕ} {A₀ : ℕ} {c c' : Config} {k k' : ℕ} (h : RF B A₀ c c' k)
    (hB : B ⊆ B') (hk : k ≤ k') : RF B' A₀ c c' k' := by
  zugw
  exact ⟨fun r hr hra => r₁ r ztdzv hra, fun r hr => rr₁ r ztdzv,
    m₁, rm₁, o₁, a₁, by_omega⟩
theorem RF.of_frame (h : Frame B c c' k)
    (hA : A₀ ≤ c.nreg ALLOC) : RF B A₀ c c' k := by
  zugw
  exact ztedy
theorem RF.to_frame (h : RF B ztm c c' k) :
    Frame B c c' k := h

/-- The bands of the driver. -/
def dBands : Finset ℕ := restoreBands ∪ oracleBands
theorem band8 {r : ℕ} (h1 : 80000 ≤ r) (h2 : r < 90000) : bandOf r = bRestore := by
  unfold bandOf bRestore; omega
theorem mem_dBands_8 : bRestore ∈ dBands := by_decide
theorem alloc_notin : bandOf ALLOC ∉ dBands := by_decide

/-- A register-only change within band `8` is an `RF` step. -/
theorem rf_of_regs
    (hr : ∀ r, (r < 80000 ∨ 90000 ≤ r) → c'.nreg r = c.nreg r) (hrr : c'.rreg = c.rreg)
    (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    RF dBands A₀ c c' k := by
  zucgg
  refine ⟨fun r hr' _ => hr r ?_, fun r _ => by zvnhk, fun a _ => by zvmwi,
    fun a _ => by zvnmc, ho, by_omega, by_omega⟩
  zuho

  exact hr' (band8 hcon.1 hcon.2 ▸ mem_dBands_8)
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
open Machine Machine.Stmt Programs
@[expose] public section

/-- A register-only change within the bands of the driver is an `RF` step. -/
theorem rf_of_regs' {A₀ : ℕ} {c c' : Config} {k : ℕ}
    (hr : ∀ r, bandOf r ∉ dBands → c'.nreg r = c.nreg r) (hrr : c'.rreg = c.rreg)
    (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    RF dBands A₀ c c' k := by
  have hA : ztble := hr ALLOC alloc_notin
  exact ⟨fun r hr' _ => hr r hr', fun r _ => by zvnhk, fun a _ => by zvmwi,
    fun a _ => by zvnmc, ho, by_omega, by_omega⟩
theorem RF.refl {B : Finset ℕ} {A₀ : ℕ} (c : Config) (k : ℕ) : RF B A₀ c c k :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, le_rfl, by_omega⟩

/-- **A loop with a bounded body keeps the relative frame.** -/
theorem whileLtN_frame {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt} {B : Finset ℕ} {A₀ : ℕ}
    (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ RF B A₀ c c' k ∧ k ≤ Kb ∧ μ c' < μ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      RF B A₀ c c' k ∧ k ≤ ztkq * μ c + 2 := by
  induction hn : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · obtain ⟨c₁, k₁, hb, hI₁, hF₁, hk₁, hμ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hF₂, hk₂⟩ := ih ztgne by_omega hI₁ rfl
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht',
        (hF₁.trans hF₂).mono subset_rfl by_omega, ?_⟩
      zucfy

    · exact ⟨c, 2, .whileLtN_false ht ztoai, hc, ht, RF.refl c 2, by_omega⟩
structure CopyI (W K CB LB : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 80030 ≤ K
  src : c.nreg 80031 = CB + 5 * c.nreg 80030
  alloc : c.nreg ALLOC = LB + 3 * c.nreg 80030
  regs : ∀ r, r ≠ 80030 → r ≠ 80031 → r ≠ 80033 → r ≠ ALLOC → c.nreg r = c₀.nreg r
  low : ∀ a, a < LB → c.nmem a = c₀.nmem a
  copied : ∀ i, i < c.nreg 80030 → ∀ j, j < 3 → c.nmem ztnmf = c₀.nmem ztemd
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
set_option maxHeartbeats 4000000 in
theorem copyBody_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {s a : ℕ}
    (h31 : c.nreg 80031 = s) (hA : c.nreg ALLOC = a) (h20 : c.nreg 80020 = 1)
    (h22 : c.nreg 80022 = 3) (hs : s + 5 ≤ W) (ha : a + 3 ≤ W) (hi : c.nreg 80030 + 1 ≤ W)
    (hsa : s + 2 < a) :
    ∃ c' k, Exec P W copyBody c c' k ∧ k = 13 ∧ c'.nreg 80031 = s + 5 ∧ c'.nreg ALLOC = a + 3 ∧
      c'.nreg 80030 = c.nreg 80030 + 1 ∧
      c'.nmem = upd (upd (upd c.nmem a (c.nmem s)) ztdf (c.nmem ztbk)) ztvj
        (c.nmem ztfp) ∧
      (∀ r, r ≠ 80030 → r ≠ 80031 → r ≠ 80033 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold copyBody
  zubtg
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, h31, hA', h20, h22, ALLOC]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl⟩
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h31, hA',
      h20, h22, ALLOC]
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h31, hA',
      h20, h22, ALLOC]
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h31, hA',
      h20, h22, ALLOC]
  · simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h31, hA', h20, ALLOC]
  · zujwo
    zup
set_option maxHeartbeats 2000000 in
theorem copyBody_step {P : Polygon} {W K CB LB : ℕ} {c₀ c : Config}
    (hI : CopyI W K CB LB c₀ c) (ht : c.nreg 80030 < K) (h20 : c₀.nreg 80020 = 1)
    (h22 : c₀.nreg 80022 = 3) (hCB : ∀ i, i < K → CB + 5 * i + 4 < LB)
    (hW : LB + 3 * K ≤ W) (hWK : K + 1 ≤ W) :
    ∃ c' k, Exec P W copyBody c c' k ∧ CopyI W K CB LB c₀ c' ∧ k = 13 ∧
      c'.nreg 80030 = c.nreg 80030 + 1 := by
  obtain ⟨i, hi⟩ : ∃ i, c.nreg 80030 = i := zths
  rw [hi] at ht
  have hCBi := hCB i ht
  have hsrc : c.nreg 80031 = CB + 5 * i := by rw [hI.src, hi]
  have hal : c.nreg ALLOC = LB + 3 * i := by zuoks
  obtain ⟨c', k, e, hk, r31, rA, r30, hm, R, rr, rm, ro⟩ := copyBody_exec (P := P) c hI.wb hsrc
    hal (by rw [hI.regs _ by_decide by_decide by_decide by_decide, h20])
    (by rw [hI.regs _ by_decide by_decide by_decide by_decide, h22])
    by_omega by_omega by_omega by_omega
  rw [hi] at r30
  refine ⟨c', k, e, ⟨e.wb_right, by_omega, by_omega, by_omega,
    fun r a1 a2 a3 a4 => ?_, fun a ha => ?_, fun i' hi' j hj => ?_, by zuokt,
    by zuoku, by zuokv⟩, hk, by_omega⟩
  · rw [R r a1 a2 a3 a4, hI.regs r a1 a2 a3 a4]
  · rw [hm, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, hI.low a ha]
  · rw [r30] at hi'
    have hs : ∀ j, j < 3 → c.nmem ztemd = c₀.nmem ztemd :=
      fun j hj => hI.low _ by_omega
    zuidn
    · have hold := hI.copied i' by_omega j hj
      rw [hm, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, hold]
    · zugml

      have e0 := hs 0 by_omega
      have e1 := hs 1 by_omega
      have e2 := hs 2 by_omega
      simp only [add_zero] at e0
      zucjq
      interval_cases j
      · simp_all
      · simp_all
      simp_all

/-- **The copy loop.** -/
theorem copy_exec {P : Polygon} {W K CB LB A₀ : ℕ} {c₀ : Config} (hw : WordsBounded W c₀)
    (h13 : c₀.nreg 80013 = K) (h30 : c₀.nreg 80030 = 0) (h31 : c₀.nreg 80031 = CB)
    (hA : c₀.nreg ALLOC = LB) (h20 : c₀.nreg 80020 = 1) (h22 : c₀.nreg 80022 = 3)
    (hCB : ∀ i, i < K → CB + 5 * i + 4 < LB) (hW : LB + 3 * K ≤ W) (hWK : K + 1 ≤ W)
    (hA₀ : A₀ ≤ LB) :
    ∃ c' k, Exec P W copyS c₀ c' k ∧ k ≤ 15 * K + 2 ∧ c'.nreg ALLOC = LB + 3 * K ∧
      c'.nreg 80030 = K ∧
      (∀ r, r ≠ 80030 → r ≠ 80031 → r ≠ 80033 → r ≠ ALLOC → c'.nreg r = c₀.nreg r) ∧
      (∀ a, a < LB → c'.nmem a = c₀.nmem a) ∧
      (∀ i, i < K → ∀ j, j < 3 → c'.nmem ztnmf = c₀.nmem ztemd) ∧
      RF dBands A₀ c₀ c' k := by
  have I0 : CopyI W K CB LB c₀ c₀ := ⟨hw, by_omega, by_omega,
    by omega, fun _ _ _ _ _ => rfl, fun _ _ => rfl,
    fun i hi => by_omega, rfl, rfl, rfl⟩
  obtain ⟨c', k, e, I', hx, RFl, hk⟩ := whileLtN_frame (P := P) (W := W) (a := 80030)
    (b := 80013) (body := copyBody) (B := dBands) (A₀ := A₀)
    (CopyI W K CB LB c₀) (fun c => K - c.nreg 80030) 13
    ztpf
    (fun c I ht => by
      have t : c.nreg 80030 < K := by
        rw [I.regs 80013 by_decide by_decide by_decide by_decide, h13] at ht; exact ht
      obtain ⟨c', k, e, I', hk, hi⟩ := copyBody_step (P := P) I t h20 h22 hCB hW hWK
      refine ⟨c', k, e, I', ?_, by_omega, by_omega⟩
      -- the frame of one step
      have hb : ∀ r, bandOf r ∉ dBands → r ≠ 80030 ∧ r ≠ 80031 ∧ r ≠ 80033 := fun r hr =>
        ⟨fun h => hr ztepw,
         fun h => hr ztepw,
         fun h => hr ztepw⟩
      refine ⟨fun r hr hra => ?_, fun r _ => by rw [I'.rr, I.rr], fun a ha => ?_,
        fun a _ => by rw [I'.rm, I.rm], by rw [I'.out, I.out], ?_, ?_⟩
      · obtain ⟨h1, h2, h3⟩ := hb r hr
        rw [I'.regs r h1 h2 h3 hra, I.regs r h1 h2 h3 hra]
      · rw [I'.low a by_omega, I.low a by_omega]
      · rw [I'.alloc, I.alloc]; omega
      · rw [I'.alloc, I.alloc, hi, hk]; omega) I0
  have hK' : c'.nreg 80030 = K := by
    rw [I'.regs 80013 by_decide by_decide by_decide by_decide, h13] at hx
    have := I'.i_le; omega
  refine ⟨c', k, e, ?_, by rw [I'.alloc, hK'], hK', I'.regs, I'.low,
    fun i hi j hj => I'.copied i by_omega j hj, RFl⟩
  omega

/-- The reservation-loop invariant. -/
structure ResI (W R A : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  j_le : c.nreg 80034 ≤ R
  alloc : c.nreg ALLOC = A + 3 * c.nreg 80034
  regs : ∀ r, r ≠ 80034 → r ≠ ALLOC → c.nreg r = c₀.nreg r
  mem : c.nmem = c₀.nmem
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
set_option maxHeartbeats 2000000 in
theorem resBody_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {a : ℕ}
    (hA : c.nreg ALLOC = a) (h20 : c.nreg 80020 = 1) (ha : a + 3 ≤ W)
    (hj : c.nreg 80034 + 1 ≤ W) :
    ∃ c' k, Exec P W resBody c c' k ∧ k = 4 ∧ c'.nreg ALLOC = a + 3 ∧
      c'.nreg 80034 = c.nreg 80034 + 1 ∧
      (∀ r, r ≠ 80034 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zubtg
  unfold resBody
  exec_block
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA', h20, ALLOC]; omega)
  zuloy
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hA', h20,
      ALLOC]
  · simp (disch := omega) only [Machine.upd_same, Machine.upd_other, h20, ALLOC]
  simp_all

/-- **The reservation loop.** -/
theorem res_exec {P : Polygon} {W R A A₀ : ℕ} {c₀ : Config} (hw : WordsBounded W c₀)
    (h14 : c₀.nreg 80014 = R) (h34 : c₀.nreg 80034 = 0) (hA : c₀.nreg ALLOC = A)
    (h20 : c₀.nreg 80020 = 1) (hW : A + 3 * R ≤ W) (hWR : R + 1 ≤ W) :
    ∃ c' k, Exec P W resS c₀ c' k ∧ k ≤ 6 * R + 2 ∧ c'.nreg ALLOC = A + 3 * R ∧
      (∀ r, r ≠ 80034 → r ≠ ALLOC → c'.nreg r = c₀.nreg r) ∧ c'.nmem = c₀.nmem ∧
      RF dBands A₀ c₀ c' k := by
  have I0 : ResI W R A c₀ c₀ := ⟨hw, by_omega, by_omega, fun _ _ _ => rfl, rfl,
    rfl, rfl, rfl⟩
  obtain ⟨c', k, e, I', hx, RFl, hk⟩ := whileLtN_frame (P := P) (W := W) (a := 80034)
    (b := 80014) (body := resBody) (B := dBands) (A₀ := A₀)
    (ResI W R A c₀) (fun c => R - c.nreg 80034) 4
    ztpf
    (fun c I ht => by
      have t : c.nreg 80034 < R := by
        rw [I.regs 80014 by_decide by_decide, h14] at ht; exact ht
      have c20 : ztpma := by rw [I.regs _ by_decide by_decide, h20]
      obtain ⟨c', k, e, hk, qa, qj, qr, qm, qrr, qrm, qo⟩ := resBody_exec (P := P) c I.wb
        I.alloc c20 by_omega by_omega
      have b34 : bandOf 80034 ∈ dBands := by
        decide
      refine ⟨c', k, e, ⟨e.wb_right, by_omega, by_omega,
        fun r a1 a2 => by rw [qr r a1 a2, I.regs r a1 a2], by rw [qm, I.mem],
        by rw [qrr, I.rr], by rw [qrm, I.rm], by rw [qo, I.out]⟩,
        ⟨fun r hr hra => qr r (fun h => hr (h ▸ b34)) hra, fun r _ => by zuoey,
          fun a _ => by zunsl, fun a _ => by zuoer, qo, by rw [qa, I.alloc]; omega,
          by rw [qa, I.alloc, hk]; omega⟩,
        by omega, by_omega⟩) I0
  have hR' : c'.nreg 80034 = R := by
    rw [I'.regs 80014 by_decide by_decide, h14] at hx
    have := I'.j_le; omega
  refine ⟨c', k, e, ?_, by rw [I'.alloc, hR'], I'.regs, I'.mem, RFl⟩
  omega
open Chazelle.Chain (sideInArc)
open DownHost ArcT
variable {n a b : ℝ} {q : ℕ} {s e : ℕ → ℝ}

/-- The hypotheses of a tiling. -/
structure Tile (n a b : ℝ) (q : ℕ) (s e : ℕ → ℝ) : Prop where
  ha : 0 ≤ a ∧ a < n
  hb : 0 ≤ b ∧ b < n
  hab : a ≠ b
  hq : 1 ≤ q
  hs : ∀ i, i < q → 0 ≤ s i ∧ s i < n
  he : ∀ i, i < q → 0 ≤ e i ∧ e i < n
  s0 : s 0 = a
  eq : e ztcfe = b
  hse : ∀ i, i + 1 < q → e i = s ztg
  hin : ∀ i, i + 1 < q → sideInArc ztciy b ztfhe
theorem unwrap_b (h : Tile n a b q s e) : a < unwrapK n a b := by
  have := unwrapK_bounds h.ha h.hb
  unfold unwrapK at *
  zuhqh
  · exact lt_of_le_of_ne h1 h.hab
  · linarith [h.ha.2, h.hb.1]

/-- **The unwrapped piece starts increase** and stay below the arc's end. -/
theorem tile_mono (h : Tile n a b q s e) :
    ∀ i, i < q → a ≤ unwrapK n a ztciy ∧ unwrapK n a ztciy < unwrapK n a b ∧
      unwrapK n a ztciy < unwrapK n a ztfhe ∧ unwrapK n a ztfhe ≤ unwrapK n a b := by
  zullm
  have hlast : ∀ i, i < q → a ≤ unwrapK n a ztciy → unwrapK n a ztciy < unwrapK n a b →
      unwrapK n a ztciy < unwrapK n a ztfhe ∧ unwrapK n a ztfhe ≤ unwrapK n a b := by
    intro i hi h1 h2
    zuhtc
    · have := (cyc_unwrap h.ha zttln h.hb zttlm h2).1 (h.hin i hl)
      grind
    · zulgu
      zumo
      rw [h.eq]; simp_all
  zuibw
  induction i with
  | zero =>
    zulmu
    have h0 : unwrapK n a (s 0) = a := by zuonb
    refine ⟨by zvmzn, by_simp_all, ?_⟩
    exact hlast 0 hi ztqev by_simp_all
  | succ i ih =>
    zulmu
    obtain ⟨h1, h2, h3, -⟩ := ih by_omega
    have hn := (cyc_unwrap h.ha (h.hs i by_omega) h.hb (h.he i by_omega) h2).1
      (h.hin i hi)
    rw [← h.hse i hi]
    refine ⟨by_linarith, hn.2, ?_⟩
    have := hlast ztg hi (by rw [← h.hse i hi]; linarith) (by rw [← h.hse i hi]; simp_all)
    rw [← h.hse i hi] at this
    zufep

/-- **Every key of the closed arc lies in a closed piece.** -/
theorem tile_cover (h : Tile n a b q s e) {x : ℝ} (_hx : 0 ≤ x ∧ x < n)
    (hxa : a ≤ unwrapK n a x) (hxb : unwrapK n a x ≤ unwrapK n a b) :
    ∃ i, i < q ∧ unwrapK n a ztciy ≤ unwrapK n a x ∧ unwrapK n a x ≤ unwrapK n a ztfhe := by
  have hm := tile_mono h
  -- the last piece starting at or before `x`
  classical
  have hex : ∃ i, i < q ∧ unwrapK n a ztciy ≤ unwrapK n a x := ⟨0, h.hq, by
    zuonb; omega⟩
  let i := Nat.findGreatest (fun i => i < q ∧ unwrapK n a ztciy ≤ unwrapK n a x) q
  have hi : i < q ∧ unwrapK n a ztciy ≤ unwrapK n a x := by
    obtain ⟨j, hj, hj'⟩ := hex
    exact Nat.findGreatest_spec (P := fun i => i < q ∧ unwrapK n a ztciy ≤ unwrapK n a x)
      hj.le ⟨hj, hj'⟩
  refine ⟨i, hi.1, hi.2, ?_⟩
  zux

  zuhtc
  · have hmax := Nat.le_findGreatest (P := fun i => i < q ∧ unwrapK n a ztciy ≤ unwrapK n a x)
      (m := i + 1) hl.le ⟨hl, by rw [← h.hse i hl]; grind⟩
    omega
  · zulgu
    have he' : e i = b := by rw [this, h.eq]
    grind

/-- **A key strictly inside a piece is strictly inside the arc.** -/
theorem tile_inner (h : Tile n a b q s e) {i : ℕ} (hi : i < q) {y : ℝ} (hy : 0 ≤ y ∧ y < n)
    (hiy : sideInArc ztciy ztfhe y) : sideInArc a b y := by
  obtain ⟨h1, -, h3, h4⟩ := tile_mono h i hi
  zullm
  have := (cyc_unwrap h.ha zttln zttlm hy h3).1 hiy
  have ha0 : unwrapK n a a = a := unwrapK_self
  exact (cyc_unwrap h.ha h.ha h.hb hy by_simp_all).2
    ⟨by_grind, by_grind⟩
theorem region_arc {M : Model} {Q : Polygon} {N : NF} {reg : ℕ → Set Point}
    (hM : WalkAx M) (hN : IsNF M Q N) (hregs : NFRegs M Q N reg)
    (hne : (N.F M Q).Nonempty) {r : ℕ} (hr : r < N.nRegions) :
    0 < (N.region r).arcs.length ∧ (N.region r).arcs.getD 0 0 < N.arcs.length ∧
      (N.arc ztdeg).reg = r := by
  have hF : N.F M Q ⊆ M.Adm := hN.1.2.1
  have hfin : (N.F M Q).Finite := hN.1.1
  have hR := hregs.1.1 r hr
  obtain ⟨p, t, hp, ht0, ht1, hnc, hf⟩ := DownHost.exists_faces_nc hM hF hfin hR
  obtain ⟨X, hX, l, r', harc, hin⟩ := hM.arc_around hF hfin hne hnc
  have hfX : M.Faces p t X := harc.2.2.2.2.2.2 p t hp ht0 ht1 hin
  have hXR : X = reg r := WalkAx.faces_unique hX hR hfX hf
  zuktl
  obtain ⟨j, hj, hjr, -, -⟩ := hregs.2.2.1.2.2.1 r hr l r' harc
  have hmem : ztgav := ((hregs.2.2.1.2.2.2 r hr j).2 zthnb)
  have hlen : ztphk := List.length_pos_of_mem hmem
  have h0 : ztixc := by
    simp_all
  obtain ⟨a, b⟩ := (hregs.2.2.1.2.2.2 r hr _).1 h0
  omega
end
end Restore
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
def sgPc (c : ℕ) : Pc := ⟨ztexx, ztrax, 0, 0, 0, 0, 0⟩
variable {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop} {I : List Pc → Config → Prop}
/-- **A single edge** handed to `emit`. -/
theorem single_exec
 (hE : EmitOK P W emit A₀ Pv I K) {ps : List Pc}
    (d : Config) (hw : WordsBounded W d) {c : ℕ} (h40 : d.nreg 150040 = c)
    (h91 : d.nreg 150091 = 1) (hcW : c + 1 ≤ W) (hI : I ps d) (hpv : Pv ztmnp) :
    ∃ d' k, Exec P W ztfiq d d' k ∧ k ≤ K + 7 ∧ I (ps ++ [sgPc c]) d' ∧
      d'.nreg 150040 = c + 1 ∧ ztcbk ∧
      ztno := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W pcSingle d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = c ∧ d₁.nreg 150051 = 0 ∧ d₁.nreg 150052 = c + 1 ∧
      d₁.nreg 150053 = 0 ∧ d₁.nreg 150054 = 0 ∧
      ztbcv ∧ d₁.nmem = d.nmem := by
    unfold pcSingle
    exec_block
    all_goals first | omega | (config_simp; zuooa; omega) | skip
    refine ztfww
    all_goals first | (config_simp; zuooa; done) | (config_simp; rw [h40]; done) |
      (config_simp; done) | skip
    zubd
  zucga
  have hR : PcRegs d₁ ztmnp := ztbod
  obtain ⟨d₂, k₂, e₂, hk₂, hI₂, kp, mem₂⟩ := hE.run _ ztmnp d₁ e₁.wb_right ztczr hR hpv
  have q40 : ztutx := by
    rw [kp _ ztii, r₁ _ by_omega, h40]
  have q91 : ztlyj := by
    rw [kp _ ztii, r₁ _ by_omega, h91]
  have e₃ := Exec.addN (P := P) e₂.wb_right 150040 150040 150091 by_omega
  refine ⟨_, k₁ + ztcaj, .seq e₁ ztcr, by_omega,
    hE.stable _ _ _ hI₂ ztduk, by_simp_all,
    fun r hr h1 => ?_, fun a ha => ?_⟩
  · config_simp
    rw [upd_other _ _ _ h1, kp r hr, r₁ r ztbpy]
  simp_all

/-- **`150071 := min 150071 r`.** -/
theorem minTo_exec {W : ℕ} (d : Config) (hw : WordsBounded W d) (r : ℕ) :
    ∃ d' k, Exec P W (minTo r) d d' k ∧ k ≤ 2 ∧
      d'.nreg 150071 = min (d.nreg 150071) ztvot ∧
      ztivx ∧ d'.nmem = d.nmem := by
  unfold minTo
  by_cases h : d.nreg r < d.nreg 150071
  · refine spec_ifLtN_true h (spec_instr ztbim fun _ => ⟨by_omega, ?_,
      by simp_all, rfl⟩)
    config_simp; omega
  · refine spec_ifLtN_false h ztevs

/-- The straight part of a climbing stretch: `L` into `150071`. -/
theorem upLen_exec {W : ℕ} (d : Config) (hw : WordsBounded W d) {mC J ℓ t n q lim : ℕ}
    (h23 : d.nreg 150023 = mC) (h61 : d.nreg 150061 = J) (h69 : d.nreg 150069 = ℓ)
    (h66 : d.nreg 150066 = t) (h27 : d.nreg 150027 = n) (h70 : d.nreg 150070 = q)
    (h72 : d.nreg 150072 = lim) (h91 : d.nreg 150091 = 1) :
    ∃ d' k, Exec P W upLen d d' k ∧ k ≤ 10 ∧
      d'.nreg 150071 = min (min (min (mC - J) (ℓ - t)) (n - q - 1)) lim ∧
      (∀ x, x ≠ 150071 → x ≠ 150075 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  obtain ⟨d₁, k₁, e₁, hk₁, o71, o75, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
      ztird d d₁ k₁ ∧ k₁ = 2 ∧
      d₁.nreg 150071 = mC - J ∧ d₁.nreg 150075 = ℓ - t ∧
      (∀ x, x ≠ 150071 → x ≠ 150075 → d₁.nreg x = d.nreg x) ∧ d₁.nmem = d.nmem := by
    exec_block
    simp_all
  obtain ⟨d₂, k₂, e₂, hk₂, o71', r₂, m₂⟩ := minTo_exec (P := P) d₁ e₁.wb_right 150075
  obtain ⟨d₃, k₃, e₃, hk₃, o75', r₃, m₃⟩ : ∃ d₃ k₃, Exec P W
      ztire d₂ d₃ k₃ ∧ k₃ = 2 ∧
      d₃.nreg 150075 = n - q - 1 ∧ (∀ x, x ≠ 150075 → d₃.nreg x = d₂.nreg x) ∧
      d₃.nmem = d₂.nmem := by
    have a27 : d₂.nreg 150027 = n := by_simp_all
    have a70 : d₂.nreg 150070 = q := by_simp_all
    have a91 : ztlyj := by_simp_all
    zue
    exec_block
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl⟩
    · simp_all
    · zvmwf; simp_all
  obtain ⟨d₄, k₄, e₄, hk₄, o71'', r₄, m₄⟩ := minTo_exec (P := P) d₃ e₃.wb_right 150075
  obtain ⟨d₅, k₅, e₅, hk₅, o71''', r₅, m₅⟩ := minTo_exec (P := P) d₄ e₄.wb_right 150072
  refine ⟨d₅, k₁ + ztwqm, .seq e₁ ztbq, by_omega,
    ?_, fun x h1 h2 => ?_, by_grind⟩
  · grind
  grind

/-- The straight part of a descending stretch: `L` into `150071`. -/
theorem dnLen_exec {W : ℕ} (d : Config) (hw : WordsBounded W d) {m2 J t q lim : ℕ}
    (h29 : d.nreg 150029 = m2) (h61 : d.nreg 150061 = J) (h66 : d.nreg 150066 = t)
    (h70 : d.nreg 150070 = q) (h72 : d.nreg 150072 = lim) :
    ∃ d' k, Exec P W dnLen d d' k ∧ k ≤ 7 ∧
      d'.nreg 150071 = min ztbnf lim ∧
      ztivx ∧ d'.nmem = d.nmem := by
  have e₁ := Exec.subN (P := P) hw 150071 150029 150061
  set d₁ := ({ d with nreg := upd d.nreg 150071 _ } : Config)
    with hd₁
  have r₁ : ∀ x, x ≠ 150071 → d₁.nreg x = d.nreg x := by_simp_all
  have o71 : d₁.nreg 150071 = m2 - J := by_simp_all
  obtain ⟨d₂, k₂, e₂, hk₂, o₂, r₂, m₂⟩ := minTo_exec (P := P) d₁ e₁.wb_right 150066
  obtain ⟨d₃, k₃, e₃, hk₃, o₃, r₃, m₃⟩ := minTo_exec (P := P) d₂ e₂.wb_right 150070
  obtain ⟨d₄, k₄, e₄, hk₄, o₄, r₄, m₄⟩ := minTo_exec (P := P) d₃ e₃.wb_right 150072
  refine ⟨d₄, 1 + zttk, .seq e₁ ztcb, by_omega, ?_,
    by grind, by_grind⟩
  grind

/-- **The constants.** -/
theorem cInit_exec {W : ℕ} (d : Config) (hw : WordsBounded W d) (hW : 6 ≤ W) :
    ∃ d' k, Exec P W cInit d d' k ∧ k = 5 ∧ d'.nreg 150090 = 0 ∧ d'.nreg 150091 = 1 ∧
      d'.nreg 150092 = 2 ∧ d'.nreg 150093 = 3 ∧ d'.nreg 150096 = 6 ∧
      (∀ r, r ≠ 150090 → r ≠ 150091 → r ≠ 150092 → r ≠ 150093 → r ≠ 150096 →
        d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem := by
  unfold cInit
  exec_block
  all_goals first | omega | skip
  simp_all

/-- **A climbing stretch** on the RAM: its length `L` and its upward cover. -/
theorem upStretch_exec
 (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg : ℕ} (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) {ps₀ : List Pc} (d : Config)
    (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    {mC J ℓ t q lim c : ℕ} (h90 : d.nreg 150090 = 0) (h91 : d.nreg 150091 = 1)
    (h34 : d.nreg 150034 = Tb) (h35 : d.nreg 150035 = Hb) (h36 : d.nreg 150036 = Pb)
    (h23 : d.nreg 150023 = mC) (h61 : d.nreg 150061 = J) (h69 : d.nreg 150069 = ℓ)
    (h66 : d.nreg 150066 = t) (h27 : d.nreg 150027 = P.n) (h70 : d.nreg 150070 = q)
    (h72 : d.nreg 150072 = lim) (h40 : d.nreg 150040 = c) (hI : I ps₀ d)
    (hqn : q + 1 < P.n) (hJ : J < mC) (ht : t < ℓ) (htg : P.n - 1 ≤ 2 ^ tg)
    (hW : c + lim + 2 ≤ W) (hW' : 5 * P.n + 6 ≤ W)
    (hblk : UpBlocks Pv m₀ W A₀ Tb c q (min ztyb lim)) :
    ∃ d' k ps', Exec P W ztqxx d d' k ∧
      k ≤ ztlu * ztydx
        + 40 ∧
      I ztcdl d' ∧
      Chained ztexx ps' ⟨c + min ztyb lim, 0⟩ ∧
      ztbqq ∧
      ps'.length ≤ 2 * ztydx ∧
      d'.nreg 150040 = c + min ztyb lim ∧
      ztfjk ∧
      d'.nreg 150090 = 0 ∧ d'.nreg 150091 = 1 ∧ d'.nreg 150092 = 2 ∧ d'.nreg 150093 = 3 ∧
      d'.nreg 150096 = 6 ∧ WordsBounded W d' ∧ ztcqe := by
  zuinw
  obtain ⟨d₁, k₁, e₁, hk₁, o71, r₁, m₁⟩ := upLen_exec (P := P) d hw h23 h61 h69 h66 h27 h70 h72 h91
  zucga
  zugnr
  obtain ⟨d₂, k₂, ps', e₂, hk₂, hI₂, hch, hv, hlen, o40, r₂, a90, a91, m₂⟩ :=
    dyUp_exec hE (ps₀ := ps₀) (q₀ := q) (L := L) (c₀ := c) d₁ env hblk by_omega
      by_grind by_omega by_omega e₁.wb_right
      ztxl
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      o71 by_grind ztczr
  obtain ⟨d₃, k₃, e₃, hk₃, b90, b91, b92, b93, b96, r₃, m₃⟩ :=
    cInit_exec (P := P) d₂ e₂.wb_right by_omega
  refine ⟨d₃, k₁ + zttl, ps', .seq e₁ ztcr, by_omega,
    hE.stable _ _ _ hI₂ ztduk, hch, hv, hlen,
    by grind,
    fun r h1 h2 h3 => ?_, b90, b91, b92, b93, b96, e₃.wb_right,
    fun a ha => by_grind⟩
  rw [r₃ _ by_omega by_omega by_omega by_omega by_omega, r₂ r h1 h2 h3,
    k₁' r by_omega by_omega]

/-- **A descending stretch** on the RAM: its length `L` and its downward cover. -/
theorem dnStretch_exec
 (hE : EmitOK P W emit A₀ Pv I K) {m₀ : ℕ → ℕ}
    {Tb Hb Pb tg : ℕ} (env : SwEnv P.n W A₀ Tb Hb Pb tg m₀) {ps₀ : List Pc} (d : Config)
    (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    {m2 J t q lim c : ℕ} (h90 : d.nreg 150090 = 0) (h91 : d.nreg 150091 = 1)
    (h34 : d.nreg 150034 = Tb) (h35 : d.nreg 150035 = Hb) (h36 : d.nreg 150036 = Pb)
    (h29 : d.nreg 150029 = m2) (h61 : d.nreg 150061 = J)
    (h66 : d.nreg 150066 = t) (h70 : d.nreg 150070 = q)
    (h72 : d.nreg 150072 = lim) (h40 : d.nreg 150040 = c) (hI : I ps₀ d)
    (hq : q < P.n) (htg : P.n - 1 ≤ 2 ^ tg)
    (hW : c + lim + 2 ≤ W) (hW' : 5 * P.n + 6 ≤ W)
    (hblk : DnBlocks Pv m₀ W A₀ Tb c q (min ztbnf lim)) :
    ∃ d' k ps', Exec P W ztqmd d d' k ∧
      k ≤ ztlu * ztydw + 40 ∧
      I ztcdl d' ∧
      Chained ztexx ps' ⟨c + min ztbnf lim, 0⟩ ∧
      ztbqq ∧
      ps'.length ≤ 2 * ztydw ∧
      d'.nreg 150040 = c + min ztbnf lim ∧
      ztfjk ∧
      d'.nreg 150090 = 0 ∧ d'.nreg 150091 = 1 ∧ d'.nreg 150092 = 2 ∧ d'.nreg 150093 = 3 ∧
      d'.nreg 150096 = 6 ∧ WordsBounded W d' ∧ ztcqe := by
  zuinw
  obtain ⟨d₁, k₁, e₁, hk₁, o71, r₁, m₁⟩ := dnLen_exec (P := P) d hw h29 h61 h66 h70 h72
  zucga
  zugnr
  obtain ⟨d₂, k₂, ps', e₂, hk₂, hI₂, hch, hv, hlen, o40, r₂, a90, a91, m₂⟩ :=
    dyDn_exec hE (ps₀ := ps₀) (q₀ := q) (L := L) (c₀ := c) d₁ env hblk by_omega
      by_omega by_omega by_omega by_omega e₁.wb_right
      ztxl
      by_grind by_grind
      by_grind by_grind
      by_grind by_grind
      o71 by_grind ztczr
  obtain ⟨d₃, k₃, e₃, hk₃, b90, b91, b92, b93, b96, r₃, m₃⟩ :=
    cInit_exec (P := P) d₂ e₂.wb_right by_omega
  refine ⟨d₃, k₁ + zttl, ps', .seq e₁ ztcr, by_omega,
    hE.stable _ _ _ hI₂ ztduk, hch, hv, hlen,
    by grind,
    fun r h1 h2 h3 => ?_, b90, b91, b92, b93, b96, e₃.wb_right,
    by grind⟩
  rw [r₃ _ by_omega by_omega by_omega by_omega by_omega, r₂ r h1 h2 h3,
    k₁' r by_omega]
open Chazelle.Chain (sideE)
structure SEnv (O : OracleIface) (P : Polygon) (C : Chain) (H : Host) (Hh h γ : ℕ)
    (m₀ : ℕ → ℕ) (A₀ W : ℕ) : Prop where
  hP : C.P = H.poly zta
  hH : HostAt m₀ Hh H
  hHA : Hh + 3 * H.length + 4 ≤ A₀
  hwf : HostWF P.n H
  hlen : H.length ≤ 64
  hs : C.s < C.P.n
  hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀
  hcap : γ ≤ 2 ^ ztczu
  hAW : A₀ ≤ W
  hW : hostWords P.n ≤ W
  hn : 2 ≤ P.n
  hG : GoodEnv P
variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}
theorem SEnv.hQn (_S : SEnv O P C H Hh h γ m₀ A₀ W) : (Qof P).n = P.n := shear_n _ _
theorem SEnv.hN (S : SEnv O P C H Hh h γ m₀ A₀ W) : C.P.n = (H.pts P.n).length := by
  rw [S.hP, ← S.hQn]; zunoo
theorem SEnv.hNn (S : SEnv O P C H Hh h γ m₀ A₀ W) : (H.pts P.n).length ≤ 64 * P.n := by
  have := Host.pts_length_le S.hwf
  have := S.hlen
  nlinarith
theorem SEnv.hm2' (S : SEnv O P C H Hh h γ m₀ A₀ W) : 2 * C.m + 9 ≤ 128 * P.n + 8 := by
  have := C.m_lt
  have := S.hNn
  rw [S.hN] at *
  omega
theorem SEnv.hm2 (S : SEnv O P C H Hh h γ m₀ A₀ W) : 2 * C.m + 9 ≤ hostWords P.n := by
  have := S.hm2'
  unfold hostWords; omega

/-- **The tables of the sweeps.** -/
theorem swEnv_of (S : SEnv O P C H Hh h γ m₀ A₀ W) :
    SwEnv P.n W A₀ ztzgo (m₀ ztbba) (m₀ ztgn + 2) ztcdz m₀ := by
  have hG := S.hR.holds
  obtain ⟨-, hpow, hhalf⟩ := grade_low S.hR
  refine ⟨fun x hx => ⟨hG.2.2.1 x hx, by_simp_all⟩, fun j hj => ztdwy, S.hAW⟩
  have := (hG.2.1.2.2.1 j hj).1
  omega
theorem tg_ok (_hn : 2 ≤ P.n) : P.n - 1 ≤ 2 ^ topGrade P.n := Nat.le_pow_clog by_norm_num _

/-- **The outcome of a step** from the walk vertex `c` (pieces `ps'`, length `L`). -/
structure StepPost (Pv : Pc → Prop) (I : List Pc → Config → Prop) (ps : List Pc) (A₀ W : ℕ)
    (m₀ : ℕ → ℕ) (B : ℕ → Prop) (c lim : ℕ) (d d' : Config) (ps' : List Pc) (L : ℕ) : Prop where
  hI : I (ps ++ ps') d'
  ch : Chained ztexx ps' ⟨c + L, 0⟩
  pv : ∀ pc ∈ ps', Pv pc
  len : ps'.length ≤ 2 * ztbdz
  L1 : 1 ≤ L
  Llim : L ≤ lim
  brk : L = lim ∨ B ztqgu ∨ (L = 1 ∧ B ztbzp)
  r40 : d'.nreg 150040 = c + L
  keep : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → d'.nreg r = d.nreg r
  k90 : d'.nreg 150090 = 0
  k91 : d'.nreg 150091 = 1
  k92 : d'.nreg 150092 = 2
  k93 : d'.nreg 150093 = 3
  k96 : d'.nreg 150096 = 6
  wb : WordsBounded W d'
  mem : ∀ a, a < A₀ → d'.nmem a = m₀ a

/-- **A single edge from a breakpoint.** -/
theorem single_post (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztwp I K)
    {B : ℕ → Prop} {ps : List Pc} (d e : Config) (hw : WordsBounded W e)
    (hm : ∀ a, a < A₀ → e.nmem a = m₀ a) {c lim : ℕ} (h40 : e.nreg 150040 = c)
    (h90 : e.nreg 150090 = 0) (h91 : e.nreg 150091 = 1) (h92 : e.nreg 150092 = 2)
    (h93 : e.nreg 150093 = 3) (h96 : e.nreg 150096 = 6)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e.nreg r = d.nreg r)
    (hc : c < 2 * C.m + 6) (hlim : 1 ≤ lim) (hb : B ztbzp) (hI : I ps e) :
    ∃ d' k, Exec P W ztfiq e d' k ∧ k ≤ K + 7 ∧
      StepPost ztwp I ps A₀ W m₀ B c lim d d' [sgPc c] 1 := by
  have hWc : c + 1 ≤ W := by have := S.hm2; have := S.hW; omega
  have hpv : VPc P C m₀ h γ ztmnp :=
    ⟨single_ok 0 0 0 0 by_omega,
      rfl, rfl, by_tauto⟩
  obtain ⟨d', k, ex, hk', hI', o40, kp, mem'⟩ := single_exec hE e hw h40 h91 hWc hI hpv
  have kk := fun r h1 h2 =>
    kp r ztbh by_omega
  refine ⟨d', k, ex, hk', ⟨hI', ztrh, by_simp_all, by_simp, le_rfl, hlim,
    by simp_all, o40, fun r h1 h2 h3 => (kp r ztec h3).trans
      by_simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all, by_simp_all,
    ex.wb_right, by_simp_all⟩⟩
variable {n a t q L : ℕ}
/-- `(a + t + L) mod n` from `q = (a + t) mod n` without wrap. -/
theorem mod_add_of (hq : ztne % n = q) (hqL : q + L < n) :
    (a + ztubq) % n = q + L := by
  rw [← Nat.add_assoc, Nat.add_mod, hq, Nat.mod_eq_of_lt (show L < n by omega),
    Nat.mod_eq_of_lt hqL]

/-- `(a + t - L) mod n` from `q = (a + t) mod n`, `L ≤ q`, `L ≤ t`. -/
theorem mod_sub_of (hn : 0 < n) (hq : ztne % n = q) (hLq : L ≤ q)
    (hLt : L ≤ t) : (a + ztubu) % n = q - L := by
  have e := Nat.div_add_mod ztne n
  zukvu
  have e2 : a + ztubu = n * (ztne / n) + (q - L) := by_omega
  zudfq

/-- **A climbing stretch** from the walk vertex `c` (tour position `i = c - 6`, host point in the
run `H[r] = run a ℓ` at offset `t < ℓ`, `q = (a + t) mod n`). -/
theorem up_post (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztwp I K)
    {ps : List Pc} (d e : Config) (hw : WordsBounded W e)
    (hm : ∀ a, a < A₀ → e.nmem a = m₀ a) {c lim J r a ℓ t q : ℕ} (h40 : e.nreg 150040 = c)
    (h90 : e.nreg 150090 = 0) (h91 : e.nreg 150091 = 1)
    (h34 : e.nreg 150034 = m₀ zteu) (h35 : e.nreg 150035 = m₀ ztbba)
    (h36 : e.nreg 150036 = m₀ ztgn + 2)
    (h23 : e.nreg 150023 = C.m) (h61 : e.nreg 150061 = J) (h69 : e.nreg 150069 = ℓ)
    (h66 : e.nreg 150066 = t) (h27 : e.nreg 150027 = P.n) (h70 : e.nreg 150070 = q)
    (h72 : e.nreg 150072 = lim)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e.nreg r = d.nreg r)
    (hc6 : 6 ≤ c) (hlim1 : 1 ≤ lim) (hlim : c + lim ≤ 2 * C.m + 6) (hlimγ : lim ≤ γ)
    (hJ : tJ C ztbzp = J) (hJm : J < C.m) (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : uOf C ztbzp = NFLoc.preLen (Qof P).n H r + t) (ht : t < ℓ)
    (hq : ztne % (Qof P).n = q) (hq1 : q + 1 < P.n) (hI : I ps e) :
    ∃ d' k L ps', Exec P W ztqxx e d' k ∧
      k ≤ ztlu * ztir + 40 ∧
      StepPost ztwp I ps A₀ W m₀ ztccg c lim d d' ps' L := by
  zueqp
  set L := min (min zteub ztjky) lim with hL
  zudnp

  have hi : c - 6 + L ≤ 2 * C.m := by_omega
  have hwalk : ∀ d, d ≤ L → (chainModel C).W.vtx ztjrg = (Qof P).vtx zttwp := by
    zuip
    have := run_up C S.hP (d := d) by_omega by_omega hr hrun hu by_omega
      by_omega
    zuckb

  have hblk := upBlocks_of S.hR S.hAW hwalk hc6 by_omega by_omega
    by_omega S.hcap
  zubfy

  obtain ⟨d', k, ps', ex, hk', hI', hch, hv, hlen, o40, kp, a90, a91, a92, a93, a96, w', m'⟩ :=
    upStretch_exec ztpcb ztwgn e hw hm h90 h91 h34 h35 h36 h23 h61
      h69 h66 h27 h70 h72 h40 hI hq1 hJm ht ztwgr hcW hW' hblk
  zueql

  refine ⟨d', k, L, ps', ex, le_trans hk'' (by
      have := Nat.mul_le_mul_left ztlu zttar; omega),
    ⟨hI', hch, hv, hlen, hL1, hLl, ?_, o40, fun r h1 h2 h3 => (kp r h1 h2 h3).trans by_grind,
      a90, a91, a92, a93, a96, w', m'⟩⟩
  -- the breakpoint
  zujsm
  · omega
  zuhl
  have hlt : min zteub ztjky < lim := by_omega
  have hLe : L = min zteub ztjky := by_omega
  rcases (show L = C.m - J ∨ L = ℓ - t ∨ L = P.n - q - 1 by omega) with h2 | h2 | h2
  · zuhl
    rw [tJ_add C by_omega, hJ]; omega
  · zudpk
    exact brk_run C hr hrun hu' by_omega by_grind
  · zudpk
    refine brk_run C hr hrun hu' by_omega (Or.inr ztbaez)
    rw [mod_add_of hq by_omega, hQn]; omega

/-- **A descending stretch** from the walk vertex `c` (host point in the run `H[r] = run a ℓ` at
offset `0 < t`, `0 < q = (a + t) mod n`). -/
theorem dn_post (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztwp I K)
    {ps : List Pc} (d e : Config) (hw : WordsBounded W e)
    (hm : ∀ a, a < A₀ → e.nmem a = m₀ a) {c lim J r a ℓ t q : ℕ} (h40 : e.nreg 150040 = c)
    (h90 : e.nreg 150090 = 0) (h91 : e.nreg 150091 = 1)
    (h34 : e.nreg 150034 = m₀ zteu) (h35 : e.nreg 150035 = m₀ ztbba)
    (h36 : e.nreg 150036 = m₀ ztgn + 2)
    (h29 : e.nreg 150029 = 2 * C.m) (h61 : e.nreg 150061 = J)
    (h66 : e.nreg 150066 = t) (h70 : e.nreg 150070 = q)
    (h72 : e.nreg 150072 = lim)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e.nreg r = d.nreg r)
    (hc6 : 6 ≤ c) (hlim1 : 1 ≤ lim) (hlim : c + lim ≤ 2 * C.m + 6) (hlimγ : lim ≤ γ)
    (hJ : tJ C ztbzp = J) (hJm : C.m ≤ J) (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : uOf C ztbzp = NFLoc.preLen (Qof P).n H r + t) (ht : t ≤ ℓ) (ht0 : 0 < t)
    (hq : ztne % (Qof P).n = q) (hq0 : 0 < q) (hI : I ps e) :
    ∃ d' k L ps', Exec P W ztqmd e d' k ∧
      k ≤ ztlu * ztir + 40 ∧
      StepPost ztwp I ps A₀ W m₀ ztccg c lim d d' ps' L := by
  zueqp
  have hn : ztfzz := by zvmxg; have := S.hn; omega
  have hqn : q < P.n := by rw [← hQn, ← hq]; exact Nat.mod_lt _ hn
  have hJlt : J < 2 * C.m := by rw [← hJ]; exact tJ_lt C _
  set L := min (min (min (2 * C.m - J) t) q) lim with hL
  zudnp

  have hwalk : ∀ d, d ≤ L → (chainModel C).W.vtx ztjrg = (Qof P).vtx zttwr := by
    zuip
    have := run_down C S.hP (d := d) by_omega by_omega by_omega hr hrun hu
      ht by_omega by_omega hn
    zuckb

  have hblk := dnBlocks_of S.hR S.hAW hwalk hc6 by_omega hqn by_omega
    by_omega S.hcap
  zubfy

  obtain ⟨d', k, ps', ex, hk', hI', hch, hv, hlen, o40, kp, a90, a91, a92, a93, a96, w', m'⟩ :=
    dnStretch_exec ztpcb ztwgn e hw hm h90 h91 h34 h35 h36 h29 h61
      h66 h70 h72 h40 hI hqn ztwgr hcW hW' hblk
  zueql

  refine ⟨d', k, L, ps', ex, le_trans hk'' (by
      have := Nat.mul_le_mul_left ztlu zttar; omega),
    ⟨hI', hch, hv, hlen, hL1, hLl, ?_, o40, fun r h1 h2 h3 => (kp r h1 h2 h3).trans by_grind,
      a90, a91, a92, a93, a96, w', m'⟩⟩
  zujsm
  · omega
  zuhl
  rcases (show L = 2 * C.m - J ∨ L = t ∨ L = q by omega) with h2 | h2 | h2
  · left
    have e1 : tJ C ztqgu = (tJ C ztbzp + L) % ztbb := by
      zumve
    rw [e1, hJ, show J + L = 2 * C.m by omega, Nat.mod_self]
  · have hu' := uOf_down C S.hP (d := L) by_omega by_omega hr hrun hu ht
      by_omega
    exact brk_run C hr hrun hu' by_omega by_omega
  · have hu' := uOf_down C S.hP (d := L) by_omega by_omega hr hrun hu ht
      by_omega
    refine brk_run C hr hrun hu' by_omega (Or.inr (Or.inr ztenp))
    rw [mod_sub_of hn hq by_omega by_omega]; omega
def limOf (C : Chain) (c f : ℕ) : ℕ := if f < c then 2 * C.m + 6 - c else f - c

/-- `q = (a + t) mod n` by one conditional subtraction. -/
theorem qOf_exec {P : Polygon} {W : ℕ} (e : Config) (hw : WordsBounded W e) {a t n : ℕ}
    (h68 : e.nreg 150068 = a) (h66 : e.nreg 150066 = t) (h27 : e.nreg 150027 = n)
    (hat : a + t < 2 * n) (hW : a + t ≤ W) :
    ∃ e' k, Exec P W (.seq ztdeq
      (.ifLtN 150075 150027 ztovf
        ztnbj)) e e' k ∧ k ≤ 4 ∧
      e'.nreg 150070 = ztne % n ∧
      (∀ x, x ≠ 150070 → x ≠ 150075 → e'.nreg x = e.nreg x) ∧ e'.nmem = e.nmem := by
  refine spec_seq (spec_instr ztowt fun w' => ?_)
  by_cases hlt : a + t < n
  · refine spec_ifLtN_true by_simp_all
      (spec_instr ztlej fun _ => ⟨by_omega, ?_, by_simp_all,
        rfl⟩)
    config_simp; rw [h68, h66, Nat.mod_eq_of_lt hlt]
  · refine spec_ifLtN_false by_simp_all
      (spec_instr ztemo fun _ => ⟨by_omega, ?_, by_simp_all,
        rfl⟩)
    config_simp; rw [h68, h66, h27, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]

/-- **A step at a run point.** -/
theorem runStep_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztwp I K)
    {ps : List Pc} (d e : Config) (hw : WordsBounded W e)
    (hm : ∀ a, a < A₀ → e.nmem a = m₀ a) {c lim J r a ℓ t : ℕ} (h40 : e.nreg 150040 = c)
    (h90 : e.nreg 150090 = 0) (h91 : e.nreg 150091 = 1) (h92 : e.nreg 150092 = 2)
    (h93 : e.nreg 150093 = 3) (h96 : e.nreg 150096 = 6)
    (h34 : e.nreg 150034 = m₀ zteu) (h35 : e.nreg 150035 = m₀ ztbba)
    (h36 : e.nreg 150036 = m₀ ztgn + 2) (h23 : e.nreg 150023 = C.m)
    (h27 : e.nreg 150027 = P.n) (h29 : e.nreg 150029 = 2 * C.m) (h61 : e.nreg 150061 = J)
    (h63 : e.nreg 150063 = 1 ↔ J < C.m) (h63' : e.nreg 150063 ≤ 1)
    (h66 : e.nreg 150066 = t) (h68 : e.nreg 150068 = a) (h69 : e.nreg 150069 = ℓ)
    (h72 : e.nreg 150072 = lim)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e.nreg r = d.nreg r)
    (hc6 : 6 ≤ c) (hc : c < 2 * C.m + 6) (hlim1 : 1 ≤ lim) (hlim : c + lim ≤ 2 * C.m + 6)
    (hlimγ : lim ≤ γ) (hJ : tJ C ztbzp = J) (hr : r < H.length) (hrun : H[r] = .run a ℓ)
    (hu : uOf C ztbzp = NFLoc.preLen (Qof P).n H r + t) (ht : t ≤ ℓ) (ha : a < P.n)
    (hℓ : ℓ < P.n) (hI : I ps e) :
    ∃ d' k L ps', Exec P W ztqvq e d' k ∧
      k ≤ ztlu * ztir + 60 ∧
      StepPost ztwp I ps A₀ W m₀ ztccg c lim d d' ps' L := by
  zueqp
  zuiyo
  zudn

  obtain ⟨e₂, k₂, ex₂, hk₂, o70, r₂, m₂⟩ := qOf_exec (P := P) e hw h68 h66 h27 by_omega
    by_omega
  set q := ztne % P.n with hqdef
  have hq : ztne % (Qof P).n = q := by zvmxg
  have hqn : q < P.n := Nat.mod_lt _ by_omega
  zujag
  have fr₂ : FrameB Scr e e₂ := exec_frameB ex₂ by_decide
  have g := r₂
  have hm₂ : ∀ a, a < A₀ → e₂.nmem a = m₀ a := fun a ha => by_grind
  have hk₂' : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e₂.nreg r = d.nreg r :=
    fun r h1 h2 h3 => (g r by_omega by_omega).trans by_grind
  have hI₂ := hE.stable _ _ _ hI fr₂
  have hC : ∀ {K' : ℕ}, Brk C (Qof P).n H _ → ∃ d' k, Exec P W _ e₂ d' k ∧
      k ≤ K + 7 ∧ StepPost _ I ps A₀ W m₀ _ c lim d d'
        [sgPc c] 1 := fun hb =>
    single_post S hE d e₂ w₂ hm₂ by_grind
      by_grind by_grind
      by_grind by_grind
      by_grind hk₂' hc hlim1 hb hI₂
  have hcost : ztyyh := by
    grind
  have e63 : e₂.nreg 150063 = e.nreg 150063 := by_grind
  have e91 : e₂.nreg 150091 = 1 := by_grind
  have e90 : e₂.nreg 150090 = 0 := by_grind
  have e66 : e₂.nreg 150066 = t := by_grind
  have e69 : e₂.nreg 150069 = ℓ := by_grind
  have e27 : e₂.nreg 150027 = P.n := by_grind
  unfold runStep
  by_cases hb : e₂.nreg 150063 < e₂.nreg 150091
  · -- descending
    have hJm : C.m ≤ J := by
      omega
    by_cases ht0 : e₂.nreg 150090 < e₂.nreg 150066
    · by_cases hq0 : e₂.nreg 150090 < e₂.nreg 150070
      · obtain ⟨d', k, L, ps', ex, hk', post⟩ := dn_post S hE d e₂ w₂ hm₂
          by_grind e90 e91
          by_grind by_grind
          by_grind by_grind
          by_grind e66 o70
          by_grind hk₂' hc6 hlim1 hlim hlimγ hJ hJm hr hrun
          hu ht by_omega hq by_omega hI₂
        exact ⟨d', _, L, ps', .seq ex₂ (.ifLtN_true hb (.ifLtN_true ht0 (.ifLtN_true hq0 ex))),
          by omega, post⟩
      · obtain ⟨d', k, ex, hk', post⟩ := hC (K' := 0) (brk_run C hr hrun hu ht
          by_omega)
        exact ⟨d', _, 1, _, .seq ex₂ (.ifLtN_true hb (.ifLtN_true ht0 (.ifLtN_false hq0 ex))),
          by omega, post⟩
    · obtain ⟨d', k, ex, hk', post⟩ := hC (K' := 0) (brk_run C hr hrun hu ht
        by_omega)
      exact ⟨d', _, 1, _, .seq ex₂ (.ifLtN_true hb (.ifLtN_false ht0 ex)), by_omega, post⟩
  · -- climbing
    have hJm : J < C.m := by
      omega
    by_cases htl : e₂.nreg 150066 < e₂.nreg 150069
    · rw [e66, e69] at htl
      have e₃ := Exec.addN (P := P) w₂ 150075 150070 150091 by_omega
      set e₃c := ({ e₂ with nreg := upd e₂.nreg 150075 _ } :
        Config) with he₃c
      have g₃ : ∀ x, x ≠ 150075 → e₃c.nreg x = e₂.nreg x := fun x hx => by simp [he₃c, upd, hx]
      have o75 : e₃c.nreg 150075 = q + 1 := by simp [he₃c, upd, o70, e91]
      zubj
      have fr₃ : FrameB Scr e₂ e₃c := exec_frameB e₃ by_decide
      have hI₃ := hE.stable _ _ _ hI₂ fr₃
      have g' : ∀ x, x ≠ 150070 → x ≠ 150075 → e₃c.nreg x = e.nreg x := fun x h1 h2 =>
        (g₃ x h2).trans by_grind
      have hm₃ : ∀ a, a < A₀ → e₃c.nmem a = m₀ a := by_omega
      have hk₃ : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → e₃c.nreg r = d.nreg r :=
        fun r h1 h2 h3 => (g' r by_omega by_omega).trans by_grind
      by_cases hq1 : e₃c.nreg 150075 < e₃c.nreg 150027
      · obtain ⟨d', k, L, ps', ex, hk', post⟩ := up_post S hE d e₃c w₃ hm₃
          ztksv ztksw
          ztksx
          (by rw [g' _ by_omega by_omega, h34]) (by rw [g' _ by_omega by_omega, h35])
          (by rw [g' _ by_omega by_omega, h36]) (by rw [g' _ by_omega by_omega, h23])
          (by rw [g' _ by_omega by_omega, h61]) (by rw [g' _ by_omega by_omega, h69])
          (by rw [g' _ by_omega by_omega, h66]) (by rw [g' _ by_omega by_omega, h27])
          (by rw [g₃ _ by_omega, o70]) (by rw [g' _ by_omega by_omega, h72]) hk₃ hc6
          hlim1 hlim hlimγ hJ hJm hr hrun hu htl hq
          (by rw [o75, g' _ by_omega by_omega, h27] at hq1; omega) hI₃
        exact ⟨d', _, L, ps', .seq ex₂ (.ifLtN_false hb (.ifLtN_true by_omega
          (.seq e₃ (.ifLtN_true hq1 ex)))), by_omega, post⟩
      · have hq1' : q + 1 = P.n := by
          rw [o75, g' _ by_omega by_omega, h27] at hq1; omega
        obtain ⟨d', k, ex, hk', post⟩ := single_post S hE d e₃c w₃ hm₃
          ztksv ztksw
          ztksx (by rw [g' _ by_omega by_omega, h92])
          (by rw [g' _ by_omega by_omega, h93]) (by rw [g' _ by_omega by_omega, h96])
          hk₃ hc hlim1 (brk_run C hr hrun hu ht
            by_omega) hI₃
        exact ⟨d', _, 1, _, .seq ex₂ (.ifLtN_false hb (.ifLtN_true by_omega
          (.seq e₃ (.ifLtN_false hq1 ex)))), by_omega, post⟩
    · obtain ⟨d', k, ex, hk', post⟩ := hC (K' := 0) (brk_run C hr hrun hu ht
        by_omega)
      exact ⟨d', _, 1, _, .seq ex₂ (.ifLtN_false hb (.ifLtN_false htl ex)), by_omega, post⟩
theorem bloc_false {r : ℕ} (h : r < 150060 ∨ 150080 ≤ r) : Bloc r = false := by
  unfold Bloc Bl; simp; omega

/-- A host layout depends only on the memory below its end. -/
theorem hostAt_agree' {m m' : ℕ → ℕ} {B E : ℕ} {H : Host} (h : HostAt m B H)
    (hE : B + 3 * H.length + 4 ≤ E) (hm : ∀ a, a < E → m' a = m a) : HostAt m' B H := by
  zuko

/-- **A step on the double boundary** from the walk vertex `c ≠ f`. -/
theorem cStep_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztwp I K)
    {ps : List Pc} {MD mode : ℕ} {s e : WPos} (d : Config) (hw : WordsBounded W d)
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    {c f : ℕ} (h40 : d.nreg 150040 = c) (h41 : d.nreg 150041 = f) (hc6 : 6 ≤ c)
    (hc : c < 2 * C.m + 6) (hf : f ≤ 2 * C.m + 5) (hcf : c ≠ f) (hlimγ : limOf C c f ≤ γ)
    (hI : I ps d) :
    ∃ d' k L ps', Exec P W ztvkw d d' k ∧
      k ≤ ztlu * ztir + 1600 ∧
      StepPost ztwp I ps A₀ W m₀ ztccg c ztlqy d d' ps' L := by
  zueqp
  zucgk

  zudn

  zubnw
  zucwo

  -- `44 := c`
  have e₀ := Exec.copyN (P := P) hw 150044 150040
  set d₀ := ({ d with nreg := upd d.nreg 150044 _ } : Config) with hd₀
  have g₀ : ∀ x, x ≠ 150044 → d₀.nreg x = d.nreg x := by_simp_all
  have R₀ : ChainRegs C (H.pts P.n).length Hh d₀ := R.chain.of_frame by_simp_all
  have hH₀ := hostAt_agree' S.hH hHA by_omega
  obtain ⟨d₁, k₁, ex₁, hk₁, fr₁, o60, o61, o62, o63, o63', o64, found⟩ :=
    locV_exec (P := P) (W := W) (v := c) d₀ e₀.wb_right rfl hH₀ R₀
      by_simp_all hc6 by_omega hsN hmN by_omega by_omega
  have g₁ := fun x hx =>
    fr₁.1 x ztvfb
  have m₁ := fr₁.2.2.1
  -- the limit
  obtain ⟨d₂, k₂, ex₂, hk₂, o72, g₂, m₂⟩ : ∃ d₂ k₂, Exec P W (.ifLtN 150041 150040
      ztnbk ztnbl) d₁ d₂ k₂ ∧
      k₂ ≤ 3 ∧ d₂.nreg 150072 = limOf C c f ∧ (∀ x, x ≠ 150072 → d₂.nreg x = d₁.nreg x) ∧
      d₂.nmem = d₁.nmem := by
    have a41 : d₁.nreg 150041 = f := by_simp_all
    have a40 : d₁.nreg 150040 = c := by_simp_all
    have a32 : ztorb := by rw [g₁ _ by_omega, g₀ _ by_omega, R.h32]
    zugnx
    unfold limOf
    zujtj
    · refine spec_ifLtN_true by_omega (spec_instr ztbly
        fun _ => ⟨by_omega, ?_, fun x hx => by zupbb, rfl⟩)
      config_simp; grind
    · refine spec_ifLtN_false by_omega (spec_instr ztbly
        fun _ => ztext)
      config_simp; grind
  zujag
  have g : ∀ x, (x < 150060 ∨ 150080 ≤ x) → x ≠ 150072 → x ≠ 150044 → d₂.nreg x = d.nreg x :=
    by simp_all
  have fr : FrameB Scr d d₂ :=
    (exec_frameB e₀ by_decide).trans ((exec_frameB ex₁ by_decide).trans
      ztnya)
  have hI₂ := hE.stable _ _ _ hI fr
  have hm₂ : ztkob := by_simp_all
  have hk₂' : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → d₂.nreg r = d.nreg r :=
    fun r h1 h2 _ => g r by_omega by_omega by_omega
  have b40 : ztutx := by rw [g _ by_omega by_omega by_omega, h40]
  have b90 : ztpog := by rw [g _ by_omega by_omega by_omega, R.h90]
  have b91 : ztlyj := by rw [g _ by_omega by_omega by_omega, R.chain.h91]
  have b92 : d₂.nreg 150092 = 2 := by rw [g _ by_omega by_omega by_omega, R.h92]
  have b93 : d₂.nreg 150093 = 3 := by rw [g _ by_omega by_omega by_omega, R.chain.h93]
  have b96 : ztpoh := by rw [g _ by_omega by_omega by_omega, R.chain.h96]
  -- the item
  have hS2 := C.sideS_lt C.sideBeta
  have hJ : tJ C ztbzp = jOf ztboi ztbzp ztbb := by
    unfold tJ; rw [jOf_eq hS2 by_omega]
  have hlim1 : 1 ≤ limOf C c f := by unfold limOf; split_ifs <;> omega
  have hlim : ztknm := by unfold limOf; split_ifs <;> omega
  zubfg

  have huOf : uOf C ztbzp = u := by
    unfold uOf tJ; grind
  zukdc
  have e67 : d₂.nreg 150067 = m₀ ztcln := by
    rw [g₂ _ by_omega, h67, show d₀.nmem = d.nmem from rfl, hm _ by_omega]
  have e68 : d₂.nreg 150068 = m₀ ztbyi := by
    rw [g₂ _ by_omega, h68, show d₀.nmem = d.nmem from rfl, hm _ by_omega]
  have e69 : d₂.nreg 150069 = m₀ ztclo := by
    rw [g₂ _ by_omega, h69, show d₀.nmem = d.nmem from rfl, hm _ by_omega]
  obtain ⟨hit, -⟩ := NFLoc.hostAt_item S.hH hr
  zuizi
  have hcost : ztyyh := by
    grind
  have hcore : ∀ (d' : Config) (k k' : ℕ) (L : ℕ) (ps' : List Pc),
      Exec P W ztyzs d₂ d' k' →
      k' ≤ ztlu * ztir + 62 → k = 1 + (k₁ + (k₂ + k')) →
      StepPost ztwp I ps A₀ W m₀ ztccg c ztlqy d d' ps' L →
      ∃ d' k L ps', Exec P W ztvkw d d' k ∧
        k ≤ ztlu * ztir + 1600 ∧
        StepPost ztwp I ps A₀ W m₀ ztccg c ztlqy d d' ps'
          L := by
    intro d' k k' L ps' ex hk' hk post
    refine ⟨d', k, L, ps', ?_, ?_, post⟩
    · rw [hk]; exact .seq e₀ (.seq ex₁ (.seq ex₂ ex))
    · have := S.hlen; omega
  by_cases hcode : d₂.nreg 150067 < d₂.nreg 150091
  · -- a run
    have hc0 : ztbadd := by_omega
    zugyn

    have hrun : ztoql := by rw [hit, hc0]; rfl
    zukgs
    rw [hrun] at hwf hsucc
    zubiq
    zueaw
    obtain ⟨d', k', L, ps', ex, hk', post⟩ := runStep_exec S hE d d₂ w₂ hm₂ b40 b90 b91 b92 b93 b96
      (by rw [g _ by_omega by_omega by_omega, R.h34])
      (by rw [g _ by_omega by_omega by_omega, R.h35])
      (by rw [g _ by_omega by_omega by_omega, R.h36])
      (by rw [g _ by_omega by_omega by_omega, R.chain.h23])
      (by rw [g _ by_omega by_omega by_omega, R.h27])
      (by rw [g _ by_omega by_omega by_omega, R.chain.h29])
      (by rw [g₂ _ by_omega, o61]) ztlhi
      ztlhi (by rw [g₂ _ by_omega, h66]) e68 e69 o72 hk₂'
      hc6 hc hlim1 hlim hlimγ hJ hr hrun by_grind by_omega ha hℓ hI₂
    exact hcore d' _ _ L ps' (.ifLtN_true hcode ex) by_omega rfl post
  · -- a point item: a breakpoint
    have hpt : ∃ x, H[r] = .pt x := by
      rw [hit]; unfold NFLoc.itemOf
      rw [b91, e67] at hcode
      zufa
      split_ifs <;> exact by_grind
    obtain ⟨x, hx⟩ := hpt
    have hb : Brk C (Qof P).n H ztbzp := brk_pt C hr hx by_grind
      by_grind
    obtain ⟨d', k', ex, hk', post⟩ := single_post S hE d d₂ w₂ hm₂ b40 b90
      b91 b92 b93 b96 hk₂' hc hlim1 hb hI₂
    exact hcore d' _ _ 1 _ (.ifLtN_false hcode ex) by_omega rfl post
end
end ShootCut
@[expose] public section
namespace ShootCut
def UPath (n : ℕ) : ℕ → List Pc → ℕ → Prop
  | u, [], u' => u = u'
  | u, pc :: ps, u' => pc.s = ⟨u % n, 0⟩ ∧ ∃ u₁, u < u₁ ∧ pc.e = ⟨u₁ % n, 0⟩ ∧ UPath n u₁ ps u'
variable {n : ℕ} {U U' F : ℕ}
theorem UPath.append : ∀ {u : ℕ} {ps : List Pc} {v : ℕ}, UPath n u ps v →
    ∀ (qs : List Pc) {w : ℕ}, UPath n v qs w → UPath n u ztlrt w
  | _, [], _, h, _, _, hq => by simp only [UPath] at h; simp_all
  | _, _ :: _, _, ⟨h1, u₁, h2, h3, h4⟩, qs, _, hq => ⟨h1, u₁, h2, h3, UPath.append h4 qs hq⟩
theorem mod_shift {n U c x : ℕ} (hU : U % n = c) (hcx : c ≤ x) (hx : x < n) :
    (U + ztudq) % n = x := by
  have e := Nat.div_add_mod U n
  rw [hU] at e
  rw [show U + ztudq = n * (U / n) + x by omega, Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
theorem chained_le : ∀ {ps : List Pc} {c c' : ℕ}, Chained ztexx ps ztugg →
    ztgsa → c ≤ c'
  | [], c, c', h, _ => by
    simp only [Chained, WPos.mk.injEq, and_true] at h; omega
  | pc :: ps, c, c', ⟨h1, h2⟩, hv => by
    zubgv

    have := chained_le h2 (fun q hq => hv q by_grind)
    grind

/-- **A chained list of vertex pieces** without wrap is a path. -/
theorem chained_upath : ∀ {ps : List Pc} {c c' : ℕ}, Chained ztexx ps ztugg →
    ztgsa → c' < n →
    ∀ U, U % n = c → UPath n U ps (U + (c' - c))
  | [], c, c', h, _, _, U, _ => by
    simp only [Chained, WPos.mk.injEq, and_true] at h
    subst h; simp [UPath]
  | pc :: ps, c, c', ⟨h1, h2⟩, hv, hc', U, hU => by
    zubgv

    have hv' : ∀ q ∈ ps, q.s.hgt = 0 ∧ q.e.hgt = 0 ∧ q.s.edge < q.e.edge :=
      fun q hq => hv q by_grind
    have hle := chained_le h2 hv'
    zvmwp at hlt
    zumps
    have hm := mod_shift hU hlt.le (show pc.e.edge < n by omega)
    have hp := chained_upath h2 hv' hc' (U + zttwb) hm
    refine ⟨by_grind, U + zttwb, by_omega, by_grind, ?_⟩
    grind

/-! ## Breakpoints and the potential -/
variable (C : Chain) (nQ : ℕ) (H : Host)

/-- A residue of the walk is a breakpoint: the top `2m + 6`, or a breakpoint of the tour. -/
def BrkRes (ρ : ℕ) : Prop :=
  ρ = 2 * C.m + 6 ∨ (6 ≤ ρ ∧ ρ < 2 * C.m + 6 ∧ Brk C nQ H (ρ - 6))

/-- An unwrapped breakpoint. -/
def BrkU (x : ℕ) : Prop := BrkRes C nQ H (x % ztz)
noncomputable instance : DecidablePred ztblt := Classical.decPred _

/-- **The potential** of the main loop at the unwrapped position `U` (final position `F`). -/
noncomputable def mu (F U : ℕ) : ℕ :=
  2 * ((Finset.Ico U F).filter ztblt).card + if U < F ∧ ¬ BrkU C nQ H U then 1 else 0
variable {C nQ H}
theorem card_Ico_sub (h : U ≤ U') :
    ((Finset.Ico U' F).filter ztblt).card ≤
      ((Finset.Ico U F).filter ztblt).card :=
  Finset.card_le_card fun x hx => by
    grind
theorem card_Ico_succ (h : U < U') (hU : U < F) (hb : BrkU C nQ H U) :
    ((Finset.Ico U' F).filter ztblt).card + 1 ≤
      ((Finset.Ico U F).filter ztblt).card := by
  have hsub : insert U ((Finset.Ico U' F).filter ztblt) ⊆
      (Finset.Ico U F).filter ztblt := by
    grind
  have hnot : U ∉ (Finset.Ico U' F).filter ztblt := by
    simp_all
  have := Finset.card_le_card hsub
  simp_all

/-- **The potential decreases** along a step `U → U'` that starts or stops at a breakpoint or
stops at `F`. -/
theorem mu_lt {F U U' : ℕ} (h : U < U') (hF : U' ≤ F)
    (hb : BrkU C nQ H U ∨ U' = F ∨ BrkU C nQ H U') : mu C nQ H F U' < mu C nQ H F U := by
  have h1 := card_Ico_sub (C := C) (nQ := nQ) (H := H) (F := F) h.le
  rcases hb with hb | hb | hb
  · unfold mu
    have := card_Ico_succ (F := F) h by_omega hb
    grind
  · zulsy
    have hz : mu C nQ H U' U' = 0 := by unfold mu; simp
    zudur
    zuhas

    · have := card_Ico_succ (F := U') h h hU
      omega
    simp_all
  · zuhas

    · have := card_Ico_succ (F := F) h by_omega hU
      simp_all
    grind

/-- The potential is at most `2 · #breakpoints + 1`. -/
theorem mu_le (F U : ℕ) :
    mu C nQ H F U ≤ 2 * ((Finset.Ico U F).filter ztblt).card + 1 := by
  unfold mu; grind

/-- **Few breakpoints within one lap.** -/
theorem card_brkU_le (hn : 0 < nQ) (hwf : HostWF nQ H) {U F : ℕ}
    (hUF : F ≤ U + ztz) :
    ((Finset.Ico U F).filter ztblt).card ≤ 3 + 8 * H.length := by
  classical
  have hinj : Set.InjOn ztywg ((Finset.Ico U F).filter ztblt : Set ℕ) := by
    zuvc
    simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_ofPred_eq] at hx hy
    zumpu
    have hN : 0 < 2 * C.m + 7 := by_omega
    rcases Nat.lt_or_ge x y with h | h
    · exfalso
      have : ztz ∣ y - x := (Nat.modEq_iff_dvd' h.le).1 hxy
      have := Nat.le_of_dvd by_omega this
      omega
    · zubuf
      · exfalso
        have : ztz ∣ x - y := (Nat.modEq_iff_dvd' h.le).1 hxy.symm
        have := Nat.le_of_dvd by_omega this
        omega
      omega
  have himg : ((Finset.Ico U F).filter ztblt).image ztywg ⊆
      insert ztcc ztyaf := by
    intro ρ hρ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ
    simp only [Finset.mem_filter] at hx
    rcases hx.2 with h | ⟨h6, hlt, hb⟩
    · simp_all
    · refine Finset.mem_insert.2 (Or.inr (Finset.mem_image.2 ⟨x % ztz - 6, ?_,
        by omega⟩))
      grind
  have h1 := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj] at h1
  have h2 := Finset.card_insert_le ztcc
    ztyaf
  have h3 := Finset.card_image_le (s := (Finset.range ztbb).filter zthqs)
    (f := ztokq)
  have h4 := card_brk_le C hn hwf
  have h4' : ((Finset.range ztbb).filter zthqs).card ≤ 2 + 8 * H.length :=
    le_trans (Finset.card_le_card fun i hi => by
      simp only [Finset.mem_filter] at hi ⊢; tauto) h4
  omega
end ShootCut
end
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
def Uof (U₀ n c : ℕ) : ℕ := U₀ + zthgc % n
theorem add_mod_split {n U D : ℕ} (hn : 0 < n) (hD : D < n) :
    (U + D) % n = if U % n + D < n then U % n + D else U % n + D - n := by
  have hU := Nat.mod_lt U hn
  rw [Nat.add_mod, Nat.mod_eq_of_lt hD]
  zus
  · zubql
  · zul
theorem Uof_eq {U₀ n U : ℕ} (hn : 0 < n) (h0 : U₀ ≤ U) (h1 : U < U₀ + n) :
    Uof U₀ n (U % n) = U := by
  unfold Uof
  have e := add_mod_split (U := U₀) hn (show U - U₀ < n by omega)
  rw [show U₀ + ztjnk = U by omega] at e
  zui
  zukaw
  zus
  · rw [show U₀ % n + ztjnk + n - U₀ % n = ztjnk + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_omega]; omega
  · rw [show U₀ % n + ztjnk - n + n - U₀ % n = U - U₀ by omega, Nat.mod_eq_of_lt by_omega]
    omega

/-- **The gap between two positions** less than a lap apart. -/
theorem resid_gap {n U F : ℕ} (hn : 0 < n) (hU : U < F) (hF : F < U + n) :
    U % n ≠ F % n ∧
      F = U + (if U % n < F % n then F % n - U % n else n - U % n + F % n) := by
  have e := add_mod_split (U := U) hn (show F - U < n by omega)
  rw [show U + (F - U) = F by omega] at e
  have ha := Nat.mod_lt U hn
  grind

/-! ## The piece through the uncounted block -/

/-- The piece from the top `2m + 6` through the uncounted block to the walk vertex `6`. -/
def uPc (m : ℕ) : Pc := ⟨⟨2 * m + 6, 0⟩, ztbcw, 0, 0, 0, 0, 0⟩
theorem uPc_ok (P : Polygon) (C : Chain) (m₀ : ℕ → ℕ) (h γ : ℕ) : PcOK P C m₀ h γ (uPc C.m) := by
  refine ⟨proper_vtx' P C _, proper_vtx' P C _, by_tauto, by simp [uPc],
    Or.inl rfl, fun _ => ?_, fun h1 => by_tauto⟩
  have := wt_U_to_six C zta (n := P.n) (x := zthlx) (proper_vtx' P C _)
    ztbt
  simp only [uPc, key_hgt0] at this ⊢
  omega
variable {P : Polygon}
/-- **The step through the uncounted block.** -/
theorem uStep_exec {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {ps : List Pc} {m : ℕ}
    (d : Config) (hw : WordsBounded W d) (h32 : d.nreg 150032 = 2 * m + 6)
    (h96 : d.nreg 150096 = 6) (hI : I ps d) (hpv : Pv ztqxv) :
    ∃ d' k, Exec P W (uStep emit) d d' k ∧ k ≤ K + 7 ∧ I (ps ++ [uPc m]) d' ∧
      d'.nreg 150040 = 6 ∧ ztcbk ∧
      ztno := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.copyN 150050 150032, .constN 150051 0, .copyN 150052 150096, .constN 150053 0,
        .constN 150054 0]) d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = 2 * m + 6 ∧ d₁.nreg 150051 = 0 ∧ d₁.nreg 150052 = 6 ∧
      d₁.nreg 150053 = 0 ∧ d₁.nreg 150054 = 0 ∧
      ztbcv ∧ d₁.nmem = d.nmem := by
    exec_block
    all_goals first | omega | skip
    refine ztfww
    all_goals first | (config_simp; rw [h32]; done) | (config_simp; rw [h96]; done) |
      (config_simp; done) | skip
    zubd
  zucga
  have hR : PcRegs d₁ ztqxv := ztbod
  obtain ⟨d₂, k₂, e₂, hk₂, hI₂, kp, mem₂⟩ := hE.run _ ztqxv d₁ e₁.wb_right ztczr hR hpv
  have q96 : ztpoh := by
    rw [kp _ ztii, r₁ _ by_omega, h96]
  have e₃ := Exec.copyN (P := P) e₂.wb_right 150040 150096
  refine ⟨_, k₁ + ztcaj, .seq e₁ ztcr, by_omega,
    hE.stable _ _ _ hI₂ ztduk, by_simp_all,
    fun r hr h1 => ?_, fun a ha => ?_⟩
  · config_simp
    rw [upd_other _ _ _ h1, kp r hr, r₁ r ztbpy]
  simp_all

/-- **The loop flag**: `150042 := [c ≠ f]`. -/
theorem setFlag_exec {W : ℕ} (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W setFlag d d' k ∧ k ≤ 5 ∧
      d'.nreg 150042 = (if d.nreg 150040 = d.nreg 150041 then 0 else 1) ∧
      (∀ x, x ≠ 150042 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  unfold setFlag
  by_cases h1 : d.nreg 150040 < d.nreg 150041
  · refine spec_ifLtN_true h1 (spec_instr ztbbp fun _ =>
      ⟨by_omega, ?_, fun x hx => by_simp_all, rfl⟩)
    config_simp; grind
  · by_cases h2 : d.nreg 150041 < d.nreg 150040
    · refine spec_ifLtN_false h1 (spec_ifLtN_true h2 (spec_instr ztbbp
        fun _ => ⟨by_omega, ?_, fun x hx => by_simp_all, rfl⟩))
      config_simp; grind
    · refine spec_ifLtN_false h1 (spec_ifLtN_false h2 (spec_instr (Exec.constN hw _ _
        by_omega) fun _ => ⟨by_omega, ?_, fun x hx => by_simp_all, rfl⟩))
      config_simp; grind
theorem CoreRegs.of_frame' {C : Chain} {H : Host} {Hh MD h γ mode : ℕ}
    {s e : WPos} {m₀ : ℕ → ℕ} {c c' : Config} (R : CoreRegs P C H Hh MD h γ mode s e m₀ c)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → r ≠ 150042 → c'.nreg r = c.nreg r)
    (h90 : c'.nreg 150090 = 0) (h91 : c'.nreg 150091 = 1) (h92 : c'.nreg 150092 = 2)
    (h93 : c'.nreg 150093 = 3) (h96 : c'.nreg 150096 = 6) :
    CoreRegs P C H Hh MD h γ mode s e m₀ c' := by
  have k : ∀ r, 150000 ≤ r → r < 150040 ∨ (150042 < r ∧ r < 150044) ∨ r = 150041 →
      c'.nreg r = c.nreg r := fun r h1 h2 => hk r h1 by_omega by_omega by_omega
  exact ⟨⟨(k _ by_norm_num by_norm_num).trans R.chain.h21,
      (k _ by_norm_num by_norm_num).trans R.chain.h22,
      (k _ by_norm_num by_norm_num).trans R.chain.h23,
      (k _ by_norm_num by_norm_num).trans R.chain.h26,
      (k _ by_norm_num by_norm_num).trans R.chain.h28,
      (k _ by_norm_num by_norm_num).trans R.chain.h29, h91, h93, h96⟩,
    (k _ by_norm_num by_norm_num).trans R.h00, (k _ by_norm_num by_norm_num).trans R.h01,
    (k _ by_norm_num by_norm_num).trans R.h02, (k _ by_norm_num by_norm_num).trans R.h03,
    (k _ by_norm_num by_norm_num).trans R.h04, (k _ by_norm_num by_norm_num).trans R.h09,
    (k _ by_norm_num by_norm_num).trans R.h13, (k _ by_norm_num by_norm_num).trans R.h20,
    (k _ by_norm_num by_norm_num).trans R.h27, (k _ by_norm_num by_norm_num).trans R.h31,
    (k _ by_norm_num by_norm_num).trans R.h32, (k _ by_norm_num by_norm_num).trans R.h33,
    (k _ by_norm_num by_norm_num).trans R.h34, (k _ by_norm_num by_norm_num).trans R.h35,
    (k _ by_norm_num by_norm_num).trans R.h36, h90, h92⟩
