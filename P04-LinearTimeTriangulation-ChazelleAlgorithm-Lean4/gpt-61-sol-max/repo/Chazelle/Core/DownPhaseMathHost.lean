module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseExitEdge
public import Chazelle.Core.DownPhaseDrvCount
public import Chazelle.Core.DownPhaseHostChain
public import Chazelle.Core.DownPhaseDrvRObl

/-!
# Down phase, math (H-R1, H-R2): host descriptions of a region

The driver writes, for a region `R` of the interior family `S` of a counterclockwise polygon `Q`
(`LeftInside Q`, so the interior walk is `Q` itself), a host description `H` whose points, in
order, are the host keys `hk 0 < hk 1 < … < hk (nk - 1)` of `R` (design
`docs/design-downphase-driver.md` §4.2 (c)), each written as a symbolic point:

* a walk vertex `k` strictly inside an arc of `R` as `.vtx k`;
* an attachment key `p + t` of an exit chord of `R` (walk edge `p`, parameter `t ∈ [0, 1)`) as
  `.onEdge e h`, with `h` a vertex at the height of the chord and `e = p`, except at a vertex
  (`t = 0`) that ends an arc of `R`, where `e = p - 1 (mod n)` (the edge the arc arrives on).

This is `RepPt` (one point) and `HostRep` (the whole list).  Then (`DistinctHeights Q`):

* **H-R1** `hostPoly_of_rep`: `H.poly Q = hostPoly Q S R` (so a chain `⟨H.poly Q, (g + 1) % nk,
  nk - 1⟩` is `hostChain Q S R g`);
* **H-R2** `hostRegular_of_rep`: `HostRegular Q.n H`.

The clockwise case is the counterclockwise one for `Q.mir`, `mirF S`, `mir '' R`
(`DownDrv.hostPoly_desc_mir`, `DownDrv.extractOK_cw`).

Tools for the driver: `exitKey_not_vtxKey`, `not_arcGap_both` (an exit key does not both end
and start an arc gap), `arcGap_of_isArc_start`, `isArc_start_of_arcGap`, `arcGap_prev_of_isArc_end`,
`isArc_end_of_arcGap_prev` (arc gaps at an exit key are the arcs of `R` starting or ending there).
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- The index before `i`, cyclically modulo `N`. -/
def prevIdx (N i : ℕ) : ℕ := (i + N - 1) % N

section
variable {N i : ℕ}
theorem prevIdx_succ (hi : i < N) : prevIdx N ((i + 1) % N) = i := by
  unfold prevIdx
  by_cases h : i + 1 < N
  · rw [Nat.mod_eq_of_lt h, show i + 1 + N - 1 = i + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  · rw [show i + 1 = N by omega, Nat.mod_self, show 0 + N - 1 = i by omega, Nat.mod_eq_of_lt hi]

theorem prevIdx_lt (hN : 0 < N) : prevIdx N i < N := Nat.mod_lt _ hN

theorem succ_prevIdx (hi : i < N) : (prevIdx N i + 1) % N = i := by
  unfold prevIdx
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · simp_all +arith
  · have e : (i + N - 1) % N = i - 1 := by
      rw [show i + N - 1 = (i - 1) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e, Nat.sub_add_cancel h0, Nat.mod_eq_of_lt hi]

/-! ## Walk and polygon indices -/


end

open DrvR (ivB qE)

section
variable (li : Bool) {n p : ℕ} (hp : p < n)
include hp
theorem ivB_lt : ivB li n p < n := by
  core_grind

theorem qE_lt : qE li n p < n := by
  grind [qE]


end

section
variable (li : Bool) {n p : ℕ} (hn : 2 ≤ n) (hp : p < n)
include hn hp
/-- **The ends of a walk edge**: walk edge `p` joins the vertices `ivB p`, `ivB (p + 1)` of `Q`,
which are the ends of the edge `qE p` of `Q` (in one order or the other). -/
theorem edge_ends :
    (ivB li n p = qE li n p ∧ ivB li n ((p + 1) % n) = (qE li n p + 1) % n) ∨
      (ivB li n p = (qE li n p + 1) % n ∧ ivB li n ((p + 1) % n) = qE li n p) := by
  unfold ivB qE
  cases li with
  | false =>
    right
    simp only [Bool.false_eq_true, ite_false]
    by_cases h : p + 1 < n
    · rw [ite_eq_left h, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show n - 2 - p + 1 < n by omega)]
      omega
    grind [Nat.mod_self]
  | true =>
    simp_all

/-- Consecutive walk vertices are consecutive vertices of `Q`. -/
theorem ivB_succ :
    ivB li n ((p + 1) % n) = (ivB li n p + 1) % n ∨ ivB li n p = (ivB li n ((p + 1) % n) + 1) % n := by
  rcases edge_ends li hn hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals simp_all


end

theorem ivB_inj (li : Bool) {n p q : ℕ} (hp : p < n) (hq : q < n) (h : ivB li n p = ivB li n q) :
    p = q := by
  core_grind

/-- The interior walk lists the vertices of `Q` in the order `ivB`. -/
theorem walk_vtx {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) {k : ℕ} (hk : k < Q.n) :
    (interiorWalk Q).vtx k = Q.vtx (ivB li Q.n k) := by
  classical
  unfold interiorWalk ivB
  by_cases hL : Mountain.LeftInside Q
  · simp_all
  · have : li = false := by simp_all
    rw [ite_eq_right hL, this]
    exact FactsInterior.rev_vtx Q k hk

theorem walk_n (Q : Polygon) : (interiorWalk Q).n = Q.n := Mir.interiorWalk_n Q

theorem xAt_comm' {u w : Point} (h : u.2 ≠ w.2) (y : ℝ) :
    Visibility.xAt w u y = Visibility.xAt u w y := by
  core_grind

section
variable {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) (hn : 3 ≤ Q.n) (hdh : DistinctHeights Q) {p : ℕ} (hp : p < Q.n)
include hli hn hdh hp
/-- **The symbolic point of a position on a walk edge**: `.onEdge (qE p) h` evaluates to the
point of walk edge `p` at the height of `h`. -/
theorem eval_onEdge (t : ℝ) {h : ℕ}
    (hy : (Q.vtx h).2 = (sidePt (interiorWalk Q) p t).2) :
    (SymPt.onEdge (qE li Q.n p) h).eval Q = sidePt (interiorWalk Q) p t := by
  have hp1 : (p + 1) % Q.n < Q.n := Nat.mod_lt _ (by omega)
  have hv0 := walk_vtx hli hp
  have hv1 := walk_vtx hli hp1
  have hne : ivB li Q.n p ≠ ivB li Q.n ((p + 1) % Q.n) := by
    intro h'
    have := ivB_inj li hp hp1 h'
    by_cases h1 : p + 1 < Q.n
    · rw [Nat.mod_eq_of_lt h1] at this; omega
    grind [Nat.mod_self]
  have hd : (Q.vtx (ivB li Q.n p)).2 ≠ (Q.vtx (ivB li Q.n ((p + 1) % Q.n))).2 :=
    hdh _ _ (ivB_lt li hp) (ivB_lt li hp1) hne
  have hxat : Visibility.edgeX Q (qE li Q.n p) (Q.vtx h).2 =
      Visibility.xAt (Q.vtx (ivB li Q.n p)) (Q.vtx (ivB li Q.n ((p + 1) % Q.n))) (Q.vtx h).2 := by
    unfold Visibility.edgeX
    rcases edge_ends li (by omega) hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp_all
    · rw [← h1, ← h2]; exact xAt_comm' hd _
  have hW : sidePt (interiorWalk Q) p t =
      Geometry.lerp (Q.vtx (ivB li Q.n p)) (Q.vtx (ivB li Q.n ((p + 1) % Q.n))) t := by
    grind [sidePt, walk_n]
  rw [hW] at hy ⊢
  show ((edgeXAt Q (qE li Q.n p) h, (Q.vtx h).2) : Point) = _
  unfold edgeXAt
  rw [hxat, hy, Visibility.xAt_lerp hd]

/-- **The symbolic point of an arc end at a walk vertex**: `.onEdge (qE (p - 1)) h` evaluates to
walk vertex `p`. -/
theorem eval_onEdge_prev {h : ℕ}
    (hy : (Q.vtx h).2 = ((interiorWalk Q).vtx p).2) :
    (SymPt.onEdge (qE li Q.n ((p + Q.n - 1) % Q.n)) h).eval Q = (interiorWalk Q).vtx p := by
  have hq : (p + Q.n - 1) % Q.n < Q.n := Nat.mod_lt _ (by omega)
  have hs : sidePt (interiorWalk Q) ((p + Q.n - 1) % Q.n) 1 = (interiorWalk Q).vtx p := by
    have e := succ_prevIdx (N := Q.n) hp
    grind [prevIdx, sidePt_one, walk_n]
  rw [← hs] at hy ⊢
  exact eval_onEdge hli hn hdh hq 1 hy

/-! ## Representing host keys -/


end

/-- **The symbolic point `s` represents the host key `hk i` of `R`** (`li` the `LeftInside` bit;
see the module doc): a vertex key `k` as `.vtx (ivB k)`, an exit key `p + t` as
`.onEdge (qE e) h` with `h` at the height of the point and `e = p`, or `e = p - 1` for a vertex
key (`t = 0`) that ends an arc gap. -/
def RepPt (li : Bool) (Q : Polygon) (S : Set (Set Point)) (R : Set Point) (i : ℕ) (s : SymPt) :
    Prop :=
  (hk (interiorModel Q) S R i ∈ vtxKeys (interiorModel Q) S R ∧
      s = .vtx (ivB li Q.n ⌊hk (interiorModel Q) S R i⌋₊)) ∨
    (hk (interiorModel Q) S R i ∈ exitKeys (interiorModel Q) S R ∧ ∃ h, h < Q.n ∧
      (Q.vtx h).2 = (hostPt (interiorModel Q).W (hk (interiorModel Q) S R i)).2 ∧
      ((hk (interiorModel Q) S R i = ⌊hk (interiorModel Q) S R i⌋₊ ∧
          ArcGap (interiorModel Q) S R (prevIdx (nk (interiorModel Q) S R) i) ∧
          s = .onEdge (qE li Q.n ((⌊hk (interiorModel Q) S R i⌋₊ + Q.n - 1) % Q.n)) h) ∨
        (¬ (hk (interiorModel Q) S R i = ⌊hk (interiorModel Q) S R i⌋₊ ∧
            ArcGap (interiorModel Q) S R (prevIdx (nk (interiorModel Q) S R) i)) ∧
          s = .onEdge (qE li Q.n ⌊hk (interiorModel Q) S R i⌋₊) h)))

/-! ## Keys -/

/-- A vertex key is a walk vertex. -/
theorem vtxKey_nat {M : Model} {F : Set (Set Point)} {U : Set Point} {x : ℝ}
    (hx : x ∈ vtxKeys M F U) : x = ⌊x⌋₊ := by
  obtain ⟨k, -, rfl, -⟩ := hx
  simp_all

/-- **Keys with no walk vertex strictly between them** (cyclically): the second one is on the
walk edge of the first one, after it, or it is the next walk vertex. -/
theorem noInt_cases {n : ℕ} {x y : ℝ} (hx0 : 0 ≤ x) (hxn : x < n) (hy0 : 0 ≤ y) (hyn : y < n)
    (hxy : x ≠ y) (h : ∀ k : ℕ, k < n → ¬ sideInArc x y k) :
    (x < y ∧ ⌊y⌋₊ = ⌊x⌋₊) ∨ y = (((⌊x⌋₊ + 1) % n : ℕ) : ℝ) := by
  set p := ⌊x⌋₊ with hp
  have hpx : (p : ℝ) ≤ x := Nat.floor_le hx0
  have hxp : x < p + 1 := Nat.lt_floor_add_one x
  have hpn : p < n := by
    have : (p : ℝ) < n := lt_of_le_of_lt hpx hxn
    simp_all
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · -- `x < y`
    by_cases hfl : ⌊y⌋₊ = p
    · simp_all
    · right
      have hpy : p + 1 ≤ ⌊y⌋₊ := by
        have : p ≤ ⌊y⌋₊ := Nat.floor_le_floor hlt.le
        omega
      have hpy' : ((p + 1 : ℕ) : ℝ) ≤ y :=
        le_trans (by exact_mod_cast hpy) (Nat.floor_le hy0)
      have hp1n : p + 1 < n := by
        have : ((p + 1 : ℕ) : ℝ) < n := lt_of_le_of_lt hpy' hyn
        exact_mod_cast this
      rcases hpy'.lt_or_eq with h1 | h1
      · grind [sideInArc]
      · rw [Nat.mod_eq_of_lt hp1n, h1]
  · -- `y < x`: the interval wraps
    right
    by_cases hp1 : p + 1 < n
    · grind [sideInArc]
    · have hpn1 : p + 1 = n := by omega
      rw [hpn1, Nat.mod_self]
      push_cast
      rcases hy0.lt_or_eq with h0 | h0
      · exfalso
        apply h 0 (by omega)
        core_grind
      simp_all

section

variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR

section
variable {i : ℕ} (hi : i < nk (interiorModel Q) S R)
include hi
/-- **An exit key does not both end an arc gap and start one**: the exit chord attached there
gives a chord gap on one of the two sides. -/
theorem not_arcGap_both
    (hx : hk (interiorModel Q) S R i ∈ exitKeys (interiorModel Q) S R)
    (hA : ArcGap (interiorModel Q) S R i)
    (hB : ArcGap (interiorModel Q) S R (prevIdx (nk (interiorModel Q) S R) i)) : False := by
  set I := interiorModel Q
  set N := nk I S R
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3 : 3 ≤ N := three_le_nk hQ hFam hne hR
  obtain ⟨c, hc, htouch, p, t, hAt, hxe⟩ := hx
  obtain ⟨j, hj, pa, pb, ta, tb, hAa, hAb, ea, eb, hne', -⟩ :=
    exit_chordGap hM hF hfin hR (by omega) hc htouch
  have hgap : ChordGap I S R j := ⟨c, hc, pa, pb, ta, tb, hAa, hAb, ea, eb, hne'⟩
  obtain ⟨k₁, k₂, hsub⟩ := DownDrv.attachKeys_sub hM (hF hc)
  have hsj : (j + 1) % N < N := Nat.mod_lt _ (by omega)
  have hkne := hk_succ_ne hM hF hfin (by omega : 2 ≤ N) hj
  have hxa : hk I S R i ∈ DownDrv.attachKeys I c := ⟨p, t, hAt, hxe⟩
  have h1 : hk I S R j ∈ DownDrv.attachKeys I c := ⟨pa, ta, hAa, ea⟩
  have h2 : hk I S R ((j + 1) % N) ∈ DownDrv.attachKeys I c := ⟨pb, tb, hAb, eb⟩
  have hcases : hk I S R i = hk I S R j ∨ hk I S R i = hk I S R ((j + 1) % N) := by
    have m0 := hsub hxa
    have m1 := hsub h1
    have m2 := hsub h2
    simp only [mem_insert_iff, mem_singleton_iff] at m0 m1 m2
    rcases m0 with e0 | e0 <;> grind <;> rcases m2 with e2 | e2
    all_goals first
      | exact Or.inl (e0.trans e1.symm)
      | exact Or.inr (e0.trans e2.symm)
      | exact absurd (e1.trans e2.symm) hkne
  rcases hcases with e | e
  · have := hk_inj hM hF hfin hi hj e
    subst this
    exact not_arc_and_chord hM hF hfin (by omega) hj hA hgap
  · have := hk_inj hM hF hfin hi hsj e
    rw [this, prevIdx_succ hj] at hB
    exact not_arc_and_chord hM hF hfin (by omega) hj hB hgap

/-- In an arc gap, no walk vertex lies strictly between the two keys. -/
theorem arcGap_noInt
    (hA : ArcGap (interiorModel Q) S R i) (k : ℕ) (hkn : k < (interiorModel Q).W.n) :
    ¬ sideInArc (hk (interiorModel Q) S R i)
      (hk (interiorModel Q) S R ((i + 1) % nk (interiorModel Q) S R)) k := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  have h3 := three_le_nk hQ hFam hne hR
  intro hin
  obtain ⟨a, b, harc, hsub⟩ := hA
  refine hk_gap hM hFam.2.1 hFam.1 (by omega) hi
    (Or.inr ⟨k, hkn, rfl, a, b, harc, hsub k (Nat.cast_nonneg k) (by simp_all) hin⟩) hin


end

omit hQ hFam hne hR in
/-- **H-R1, one point**: a representing symbolic point evaluates to the host point. -/
theorem rep_eval (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (_hne : S.Nonempty)
    (_hR : R ∈ (interiorModel Q).regions S) {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q)
    (hdh : DistinctHeights Q)
    {i : ℕ} (hi : i < nk (interiorModel Q) S R) {s : SymPt} (hs : RepPt li Q S R i s) :
    s.eval Q = hostPt (interiorModel Q).W (hk (interiorModel Q) S R i) := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  have hn3 : 3 ≤ Q.n := Chazelle.Jordan.simple_three_le hQ
  have hb := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hi)
  have hW : (interiorModel Q).W = interiorWalk Q := rfl
  rw [hW, walk_n] at hb
  rw [hW]
  rcases hs with ⟨hv, rfl⟩ | ⟨-, h, -, hy, (⟨hint, -, rfl⟩ | ⟨-, rfl⟩)⟩
  · obtain ⟨k, hk, hxk, -⟩ := hv
    rw [hxk, Nat.floor_natCast]
    rw [hW, walk_n] at hk
    show Q.vtx (ivB li Q.n k) = _
    rw [← walk_vtx hli hk]
    unfold hostPt
    rw [Nat.floor_natCast, sub_self, Chazelle.Chain.sidePt_zero]
  · set x := hk (interiorModel Q) S R i
    have hp : ⌊x⌋₊ < Q.n := by
      have : (⌊x⌋₊ : ℝ) < Q.n := lt_of_le_of_lt (Nat.floor_le hb.1) hb.2
      exact_mod_cast this
    have hpt : hostPt (interiorWalk Q) x = (interiorWalk Q).vtx ⌊x⌋₊ := by
      grind [hostPt, sub_self, Chazelle.Chain.sidePt_zero]
    rw [hW, hpt] at hy
    rw [hpt]
    exact eval_onEdge_prev hli hn3 hdh hp hy
  · set x := hk (interiorModel Q) S R i
    have hp : ⌊x⌋₊ < Q.n := by
      have : (⌊x⌋₊ : ℝ) < Q.n := lt_of_le_of_lt (Nat.floor_le hb.1) hb.2
      simp_all
    exact eval_onEdge hli hn3 hdh hp _ hy

/-- **H-R2, one host edge**: consecutive representing points satisfy `HostEdgeOK`. -/
theorem rep_edgeOK {li : Bool} (hdh : DistinctHeights Q) {i : ℕ}
    (hi : i < nk (interiorModel Q) S R) {s s' : SymPt} (hs : RepPt li Q S R i s)
    (hs' : RepPt li Q S R ((i + 1) % nk (interiorModel Q) S R) s') : HostEdgeOK Q.n s s' := by
  set I := interiorModel Q with hI
  set N := nk I S R with hN
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have hn3 : 3 ≤ Q.n := Chazelle.Jordan.simple_three_le hQ
  have h3 : 3 ≤ N := three_le_nk hQ hFam hne hR
  have hsi : (i + 1) % N < N := Nat.mod_lt _ (by omega)
  have hWn : I.W.n = Q.n := walk_n Q
  have hbx := hostKeys_bounds (hk_mem hM hF hfin hi)
  have hby := hostKeys_bounds (hk_mem hM hF hfin hsi)
  rw [hWn] at hbx hby
  set x := hk I S R i with hx
  set y := hk I S R ((i + 1) % N) with hy
  have hprev : prevIdx N ((i + 1) % N) = i := prevIdx_succ hi
  rcases gap_cases hM hF hfin hne hR (by omega) hi with hA | hC
  · -- an arc gap: the two keys are on one walk edge, or the second is the next walk vertex
    have hnoint : ∀ k : ℕ, k < Q.n → ¬ sideInArc x y k := fun k hk =>
      arcGap_noInt hQ hFam hne hR hi hA k (by simp_all)
    have hxy : x ≠ y := hk_succ_ne hM hF hfin (by omega) hi
    set p := ⌊x⌋₊ with hpdef
    have hp : p < Q.n := by
      have : (p : ℝ) < Q.n := lt_of_le_of_lt (Nat.floor_le hbx.1) hbx.2
      simp_all
    -- the first point is `.vtx (ivB p)` or `.onEdge (qE p) _`
    have hs1 : s = .vtx (ivB li Q.n p) ∨ ∃ h, s = .onEdge (qE li Q.n p) h := by
      rcases hs with ⟨-, rfl⟩ | ⟨hxe, h, -, -, (⟨-, hB, -⟩ | ⟨-, rfl⟩)⟩
      · simp_all
      · exact (not_arcGap_both hQ hFam hne hR hi hxe hA hB).elim
      simp_all
    have hE := edge_ends li (by omega) hp
    rcases noInt_cases hbx.1 hbx.2 hby.1 hby.2 hxy hnoint with ⟨hlt, hfl⟩ | hyv
    · -- same walk edge: `y` is not a vertex, so `s' = .onEdge (qE p) _`
      have hyni : y ≠ ⌊y⌋₊ := by
        intro h; rw [hfl] at h
        have : (p : ℝ) ≤ x := Nat.floor_le hbx.1
        linarith
      obtain ⟨h', rfl⟩ : ∃ h', s' = .onEdge (qE li Q.n p) h' := by
        rcases hs' with ⟨hv, -⟩ | ⟨-, h', -, -, (⟨hint, -, -⟩ | ⟨-, rfl⟩)⟩
        · exact absurd (vtxKey_nat hv) hyni
        · grind
        · exact ⟨h', by rw [hfl]⟩
      rcases hs1 with rfl | ⟨h, rfl⟩
      · show ivB li Q.n p = qE li Q.n p ∨ ivB li Q.n p = (qE li Q.n p + 1) % Q.n
        omega
      · exact Or.inr rfl
    · -- `y` is the next walk vertex
      have hyfl : ⌊y⌋₊ = (p + 1) % Q.n := by rw [hyv, Nat.floor_natCast]
      have hyint : y = ⌊y⌋₊ := by grind
      have hpm : ((p + 1) % Q.n + Q.n - 1) % Q.n = p := by
        have := prevIdx_succ (N := Q.n) hp
        unfold prevIdx at this; exact this
      have hs2 : s' = .vtx (ivB li Q.n ((p + 1) % Q.n)) ∨ ∃ h', s' = .onEdge (qE li Q.n p) h' := by
        rcases hs' with ⟨-, rfl⟩ | ⟨-, h', -, -, (⟨-, -, rfl⟩ | ⟨hn', -⟩)⟩
        · grind
        · right; exact ⟨h', by grind⟩
        grind
      rcases hs1 with rfl | ⟨h, rfl⟩ <;> rcases hs2 with rfl | ⟨h', rfl⟩
      · show ivB li Q.n ((p + 1) % Q.n) = (ivB li Q.n p + 1) % Q.n ∨
          ivB li Q.n p = (ivB li Q.n ((p + 1) % Q.n) + 1) % Q.n
        exact ivB_succ li (by omega) hp
      · show ivB li Q.n p = qE li Q.n p ∨ ivB li Q.n p = (qE li Q.n p + 1) % Q.n
        omega
      · show ivB li Q.n ((p + 1) % Q.n) = qE li Q.n p ∨
          ivB li Q.n ((p + 1) % Q.n) = (qE li Q.n p + 1) % Q.n
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
      rw [hcab] at h1 h2
      exact h1.1.trans h2.1.symm
    have key : ∀ (j : ℕ) (u : SymPt), RepPt li Q S R j u → I.IsCut S (hk I S R j) →
        ∃ e h, u = .onEdge e h ∧ h < Q.n ∧ (Q.vtx h).2 = (hostPt I.W (hk I S R j)).2 := by
      intro j u hu hcut
      rcases hu with ⟨hv, -⟩ | ⟨-, h, hh, hyh, (⟨-, -, rfl⟩ | ⟨-, rfl⟩)⟩
      · obtain ⟨k, -, hk', a, b, harc, hin⟩ := hv
        exact absurd (hk' ▸ hcut) (harc.2.2.2.2.2.1 _ hin)
      all_goals grind
    obtain ⟨e, h, rfl, hh, hyh⟩ := key i s hs hcutx
    obtain ⟨e', h', rfl, hh', hyh'⟩ := key _ s' hs' hcuty
    left
    by_contra hne'
    exact hdh h h' hh hh' hne' (by grind)

end

end

end DownMath

end Chazelle.Core
