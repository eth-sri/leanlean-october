module

public import Chazelle.Core.DownPhaseDrvTEnd

/-!
# Down-phase transition (D2), part 3: the piece of one chord record (T-R1, T-R2)

The RAM filter of the transition reads the chord records `(h, lp, rp)` of the canonical normal
form of the top chain `C` (chain model) and decides, by index arithmetic only:

* `innerE`: an end at chain walk edge `p` is **inner** if `c₀ ≤ p < c₀ + m` and it is not the
  interior walk vertex `w₀` (`p = c₀` with height vertex `h = idxI 0`);
* `keepT`: a record is kept iff one of its ends is inner;
* `mapE`: an end is mapped to the interior walk edge `p - c₀` (on the inner run) or to the last
  edge `m` (the edge `e_{n-1}`, which the chord crosses, or the vertex `w_m`);
* `trT`: the mapped triple `(h, mapE lp, mapE rp)`.

**`rec_kept`**: the mapped triple of a kept record describes an interior chord of `Q` inside the
chain chord (its piece, `Trans.pieces`), correctly attached.  **`rec_dropped`**: a dropped
record contains no interior chord.

Proof: an inner end is attached on the interior walk at the shifted position
(`Trans.Shift.sec_eq`), so it carries a piece (`Trans.piece_of_attach`, `piece_at_inner`); the
other end of the piece is the other end of the chord or a point of the open last edge
(`Trans.Top.boundary_dom`), and the mapped position has exactly that point (`other_end`, with
`inner_of_interior` for the ends of the chord that see the interior); attachment at a position
with the right point follows from the uniqueness of positions of the simple interior walk
(`attach_int`).
-/

namespace Chazelle.Core

namespace DrvT

@[expose] public section

open Set Metric
open Chazelle.Chain (SideAttach sidePt sideLeft IsHChordIn)
open Chazelle.Visibility (hseg)
open Chazelle.Geometry (lerp)

/-! ## The index functions of the filter -/

/-- An end at chain walk edge `p` (height vertex `h`) is an inner end. -/
def innerE (li : Bool) (n c₀ h p : ℕ) : Bool :=
  decide (c₀ ≤ p ∧ p < c₀ + (n - 1) ∧ ¬ (p = c₀ ∧ h = idxI li n 0))

/-- The interior walk edge of an end. -/
def mapE (n c₀ p : ℕ) : ℕ := if c₀ ≤ p ∧ p < c₀ + (n - 1) then p - c₀ else n - 1

/-- A record is kept iff one of its ends is inner. -/
def keepT (li : Bool) (n c₀ : ℕ) (x : ℕ × ℕ × ℕ) : Bool :=
  innerE li n c₀ x.1 x.2.1 || innerE li n c₀ x.1 x.2.2

/-- The mapped triple. -/
def trT (n c₀ : ℕ) (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (x.1, mapE n c₀ x.2.1, mapE n c₀ x.2.2)

/-! ## Parameters and points -/

theorem paramI_succ (Q : Polygon) (q h : ℕ) :
    (interiorModel Q).param Q ⟨q, h + 1⟩ =
      if ((interiorWalk Q).vtx q).2 = ((interiorWalk Q).vtx ((q + 1) % (interiorWalk Q).n)).2
      then 0
      else ((Q.vtx h).2 - ((interiorWalk Q).vtx q).2) /
        (((interiorWalk Q).vtx ((q + 1) % (interiorWalk Q).n)).2 - ((interiorWalk Q).vtx q).2) :=
  rfl

theorem paramC_succ (C : Chain) (Q : Polygon) (q h : ℕ) :
    (chainModel C).param Q ⟨q, h + 1⟩ =
      if ((C.sideWalk C.sideBeta).vtx q).2 =
          ((C.sideWalk C.sideBeta).vtx ((q + 1) % (C.sideWalk C.sideBeta).n)).2 then 0
      else ((Q.vtx h).2 - ((C.sideWalk C.sideBeta).vtx q).2) /
        (((C.sideWalk C.sideBeta).vtx ((q + 1) % (C.sideWalk C.sideBeta).n)).2 -
          ((C.sideWalk C.sideBeta).vtx q).2) :=
  rfl

/-- The chord of a triple, in terms of the walk points. -/
theorem toSet_recOf (M : Model) (Q : Polygon) (x : ℕ × ℕ × ℕ) :
    (recOf x).toSet M Q = hseg (Q.vtx x.1).2 (sidePt M.W x.2.1 (M.param Q ⟨x.2.1, x.1 + 1⟩)).1
      (sidePt M.W x.2.2 (M.param Q ⟨x.2.2, x.1 + 1⟩)).1 := rfl

/-- The parameter of a point of a non-horizontal walk edge at a vertex height. -/
theorem param_of_lerp (M : Model) (Q : Polygon) {q h : ℕ} {s : ℝ}
    (hne : (M.W.vtx q).2 ≠ (M.W.vtx ((q + 1) % M.W.n)).2)
    (hy : (lerp (M.W.vtx q) (M.W.vtx ((q + 1) % M.W.n)) s).2 = (Q.vtx h).2) :
    M.param Q ⟨q, h + 1⟩ = s := by
  show (if (M.W.vtx q).2 = (M.W.vtx ((q + 1) % M.W.n)).2 then 0
      else ((Q.vtx h).2 - (M.W.vtx q).2) /
        ((M.W.vtx ((q + 1) % M.W.n)).2 - (M.W.vtx q).2)) = s
  rw [ite_eq_right hne, ← hy, Chazelle.Geometry.lerp_snd]
  have hd : (M.W.vtx ((q + 1) % M.W.n)).2 - (M.W.vtx q).2 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  rw [show (M.W.vtx q).2 + s * ((M.W.vtx ((q + 1) % M.W.n)).2 - (M.W.vtx q).2) -
      (M.W.vtx q).2 = s * ((M.W.vtx ((q + 1) % M.W.n)).2 - (M.W.vtx q).2) by ring,
    mul_div_assoc, div_self hd, mul_one]

/-- A horizontal segment inside another. -/
theorem hseg_sub {y a b y' a' b' : ℝ} (hab' : a' ≤ b') (h : hseg y' a' b' ⊆ hseg y a b) :
    y' = y ∧ a ≤ a' ∧ b' ≤ b := by
  have h1 := h (show ((a', y') : Point) ∈ hseg y' a' b' from ⟨rfl, le_rfl, hab'⟩)
  have h2 := h (show ((b', y') : Point) ∈ hseg y' a' b' from ⟨rfl, hab', le_rfl⟩)
  exact ⟨h1.1, h1.2.1, h2.2.2⟩

/-- A point of a horizontal segment off its open part is an end. -/
theorem hseg_end {D : Set Point} {y a b : ℝ} (h : IsHChordIn D y a b) {e : Point}
    (he : e ∈ hseg y a b) (heD : e ∉ D) : e = ((a, y) : Point) ∨ e = ((b, y) : Point) := by
  obtain ⟨hy, ha, hb⟩ := he
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · exfalso; apply heD
      rw [show e = ((e.1, y) : Point) from Prod.ext rfl hy]
      exact h.open_mem _ ha' hb'
    · right; exact Prod.ext hb' hy
  · left; exact Prod.ext ha'.symm hy

/-- **Attachment of an interior chord at a position with the right point.** -/
theorem attach_int {Q : Polygon} (hQ : Q.Simple) {y a b : ℝ}
    (h : IsHChordIn (Q.filled \ Q.boundary) y a b) {q : ℕ} {u : ℝ} (hq : q < Q.n)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hpt : sidePt (interiorWalk Q) q u = ((a, y) : Point) ∨
      sidePt (interiorWalk Q) q u = ((b, y) : Point)) :
    SideAttach (interiorWalk Q) (hseg y a b) q u := by
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec hQ
  have hIn : (interiorWalk Q).n = Q.n := Trans.iw_n
  have h' : IsHChordIn ((interiorWalk Q).filled \ (interiorWalk Q).boundary) y a b := by
    rw [hWf, hWb]; exact h
  obtain ⟨ha, hb⟩ := FactsInterior.hchord_end_mem_boundary h'
  have hopen := FactsInterior.hchord_open h'
  have hab : ((a, y) : Point) ≠ (b, y) := fun e => h.lt.ne (congrArg Prod.fst e)
  have hseg_eq := FactsChain.hseg_eq_segment (y := y) h.lt.le
  have key : ∀ {e e' : Point}, WalkEnd (interiorWalk Q) (hseg y a b) e →
      sidePt (interiorWalk Q) q u = e → SideAttach (interiorWalk Q) (hseg y a b) q u := by
    intro e e' hE hqe
    obtain ⟨p, t, hAt, hpt'⟩ := hE.1
    obtain ⟨hp, ht0, ht1, -⟩ := id hAt
    obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique hWs hp (by rw [hIn]; exact hq) ht0 ht1 hu0 hu1
      (hpt'.trans hqe.symm)
    exact hAt
  rcases hpt with hpt | hpt
  · refine key (e' := ((b, y) : Point)) ?_ hpt
    rw [hseg_eq]; exact FactsInterior.walkEnd hWs hWo hab ha hopen
  · refine key (e' := ((a, y) : Point)) ?_ hpt
    rw [hseg_eq, Chazelle.Geometry.segment_comm]
    exact FactsInterior.walkEnd hWs hWo hab.symm hb (WalkAx.open_rev hopen)

variable {Q : Polygon} {C : Chain}

variable (hQ : Q.Simple) (T : Trans.Top Q C) (hD : Trans.DistinctH Q) {li : Bool}
  (hli : li = true ↔ Mountain.LeftInside Q)
include hQ T hD hli

omit hQ T hD hli in
/-- The interior walk vertices `0` and `m` are the ends of the last edge. -/
theorem iw_ends (_hQ : Q.Simple) (T : Trans.Top Q C) (_hD : Trans.DistinctH Q)
    (hli : li = true ↔ Mountain.LeftInside Q) :
    ((interiorWalk Q).vtx 0 = Q.vtx 0 ∨ (interiorWalk Q).vtx 0 = Q.vtx C.m) ∧
      ((interiorWalk Q).vtx C.m = Q.vtx 0 ∨ (interiorWalk Q).vtx C.m = Q.vtx C.m) := by
  have hmn := T.hm
  rw [iw_vtx_idx hli (by omega), iw_vtx_idx hli (by omega)]
  unfold idxI
  by_cases h : li = true
  · rw [ite_eq_left h, ite_eq_left h]; exact ⟨Or.inl rfl, Or.inr rfl⟩
  · rw [ite_eq_right h, ite_eq_right h, show Q.n - 1 - 0 = C.m by omega, show Q.n - 1 - C.m = 0 by omega]
    exact ⟨Or.inr rfl, Or.inl rfl⟩

/-- **(E1) On the inner run** the interior parameter and point are the chain ones. -/
theorem inner_param {h p : ℕ} (hp1 : c0 C li ≤ p) (hp2 : p < c0 C li + C.m) :
    (interiorModel Q).param Q ⟨p - c0 C li, h + 1⟩ = (chainModel C).param Q ⟨p, h + 1⟩ ∧
      sidePt (interiorWalk Q) (p - c0 C li) ((chainModel C).param Q ⟨p, h + 1⟩) =
        sidePt (C.sideWalk C.sideBeta) p ((chainModel C).param Q ⟨p, h + 1⟩) := by
  have hmn := T.hm
  have H := shift_c0 hQ T hD hli
  have hle := i0_le hQ T hD hli
  have hIn : (interiorWalk Q).n = Q.n := Trans.iw_n
  have hWn : (C.sideWalk C.sideBeta).n = 2 * C.m + 7 := Chain.sideWalk_n _ _
  set j := p - c0 C li with hj
  have hjm : j < C.m := by omega
  have hpj : p = j + c0 C li := by omega
  have e1 : (C.sideWalk C.sideBeta).vtx p = (interiorWalk Q).vtx j := by
    rw [hpj]; exact vtx_c0 hQ T hD hli hjm.le
  have e2 : (C.sideWalk C.sideBeta).vtx ((p + 1) % (C.sideWalk C.sideBeta).n) =
      (interiorWalk Q).vtx ((j + 1) % (interiorWalk Q).n) := by
    rw [hWn, Nat.mod_eq_of_lt (by unfold c0 at *; omega), hIn, Nat.mod_eq_of_lt (by omega),
      show p + 1 = (j + 1) + c0 C li by omega]
    exact vtx_c0 hQ T hD hli hjm
  refine ⟨?_, ?_⟩
  · rw [paramI_succ, paramC_succ, e1, e2]
  · rw [hpj, H.pt_eq T hjm]

/-- The interior walk edges are not horizontal. -/
theorem iw_edge_ne {q : ℕ} (hq : q < Q.n) :
    ((interiorWalk Q).vtx q).2 ≠ ((interiorWalk Q).vtx ((q + 1) % (interiorWalk Q).n)).2 := by
  have hn3 := hQ.1
  have hIn : (interiorWalk Q).n = Q.n := Trans.iw_n
  rw [hIn]
  refine iw_snd_ne hQ T hD hli hq (Nat.mod_lt _ (by omega)) ?_
  intro h
  rcases (show q + 1 < Q.n ∨ q + 1 = Q.n by omega) with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h; omega
  · rw [h1, Nat.mod_self] at h; omega

/-- **The `w₀` test**: the chain parameter at `c₀` vanishes iff the height vertex is `w₀`. -/
theorem paramC_c0_zero_iff {h : ℕ} (hh : h < Q.n) :
    (chainModel C).param Q ⟨c0 C li, h + 1⟩ = 0 ↔ h = idxI li Q.n 0 := by
  have hmn := T.hm
  have hm1 := C.one_le
  have hIn : (interiorWalk Q).n = Q.n := Trans.iw_n
  obtain ⟨e1, -⟩ := inner_param hQ T hD hli (h := h) (p := c0 C li) le_rfl (by omega)
  rw [← e1, Nat.sub_self, paramI_succ, ite_eq_right (iw_edge_ne hQ T hD hli (by omega))]
  have hd : ((interiorWalk Q).vtx ((0 + 1) % (interiorWalk Q).n)).2 -
      ((interiorWalk Q).vtx 0).2 ≠ 0 :=
    sub_ne_zero.2 (Ne.symm (iw_edge_ne hQ T hD hli (by omega)))
  rw [div_eq_zero_iff, or_iff_left hd, sub_eq_zero, iw_vtx_idx hli (j := 0) (by omega)]
  constructor
  · intro h'
    by_contra hne
    exact hD _ _ hh (idxI_lt (by omega)) hne h'
  · intro h'; rw [h']

/-- **The test of the filter**: an inner end in geometric terms. -/
theorem innerE_iff {h p : ℕ} (hh : h < Q.n) :
    innerE li Q.n (c0 C li) h p = true ↔
      (c0 C li ≤ p ∧ p < c0 C li + C.m ∧
        ¬ (p = c0 C li ∧ (chainModel C).param Q ⟨p, h + 1⟩ = 0)) := by
  have hmn := T.hm
  unfold innerE
  rw [decide_eq_true_iff, show Q.n - 1 = C.m by omega]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun ⟨h4, h5⟩ => h3 ⟨h4, ?_⟩⟩
    rw [h4] at h5
    exact (paramC_c0_zero_iff hQ T hD hli hh).1 h5
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun ⟨h4, h5⟩ => h3 ⟨h4, ?_⟩⟩
    rw [h4]
    exact (paramC_c0_zero_iff hQ T hD hli hh).2 h5

omit hQ T hD hli in
theorem mapE_eq (_hQ : Q.Simple) (T : Trans.Top Q C) (_hD : Trans.DistinctH Q)
    (_hli : li = true ↔ Mountain.LeftInside Q) (p : ℕ) :
    mapE Q.n (c0 C li) p = if c0 C li ≤ p ∧ p < c0 C li + C.m then p - c0 C li else C.m := by
  have hmn := T.hm
  unfold mapE
  rw [show Q.n - 1 = C.m by omega]

/-- **A piece at an inner end.** -/
theorem piece_at_inner {c : Set Point} (hc : c ∈ (chainModel C).Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach (C.sideWalk C.sideBeta) c p t) (hp1 : c0 C li ≤ p)
    (hp2 : p < c0 C li + C.m) (hp3 : ¬ (p = c0 C li ∧ t = 0)) :
    ∃ y a b, IsHChordIn (Q.filled \ Q.boundary) y a b ∧ hseg y a b ⊆ c ∧
      (sidePt (C.sideWalk C.sideBeta) p t = ((a, y) : Point) ∨
        sidePt (C.sideWalk C.sideBeta) p t = ((b, y) : Point)) := by
  have hP : C.P.Simple := by rw [T.hP]; exact hQ
  have hMC := walkAx_chainModel hP
  have hmn := T.hm
  have H := shift_c0 hQ T hD hli
  have hle := i0_le hQ T hD hli
  have hIn : (interiorWalk Q).n = Q.n := Trans.iw_n
  set j := p - c0 C li with hj
  have hjm : j < C.m := by omega
  have hpj : p = j + c0 C li := by omega
  obtain ⟨hp, ht0, ht1, -⟩ := id hA
  have hsj : t = 0 → 1 ≤ j := fun h0 => by
    by_contra h1; exact hp3 ⟨by omega, h0⟩
  have hpt : sidePt (interiorWalk Q) j t = sidePt (C.sideWalk C.sideBeta) p t := by
    rw [hpj, H.pt_eq T hjm]
  have hAI : SideAttach (interiorWalk Q) c j t := by
    refine ExtG.attach_of_sector hpt (fun x hx => ?_) (by rw [hIn]; omega) ht0 ht1 hA
    rw [hpj] at hx
    exact (H.sec_eq T hQ hjm ht0 ht1 hsj x).1 hx
  have hnD : sidePt (interiorWalk Q) j t ∉ C.dom := by
    rw [hpt]; exact hMC.trace p hp t ht0 ht1.le
  obtain ⟨d, ⟨⟨y, a, b, hch, rfl⟩, c', hc', hdc⟩, hAd⟩ :=
    Trans.piece_of_attach hQ T (F₀ := {c}) (fun _ h => by rw [mem_singleton_iff.1 h]; exact hc)
      (mem_singleton c) hAI hnD
  rw [mem_singleton_iff.1 hc'] at hdc
  refine ⟨y, a, b, hch, hdc, ?_⟩
  rw [← hpt]
  exact hseg_end hch hAd.2.2.2.1 (fun h => hnD (T.interior_sub_dom hQ h))

/-- **The ends of the chord that see the interior but are not inner** are `w₀` or `w_m`. -/
theorem special_end {c : Set Point} (hc : c ∈ (chainModel C).Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach (C.sideWalk C.sideBeta) c p t)
    (hnear : ∃ r > 0, ∀ x ∈ c, x ≠ sidePt (C.sideWalk C.sideBeta) p t →
      dist x (sidePt (C.sideWalk C.sideBeta) p t) < r → x ∈ Q.filled \ Q.boundary)
    (hnI : ¬ (c0 C li ≤ p ∧ p < c0 C li + C.m ∧ ¬ (p = c0 C li ∧ t = 0))) :
    (p = c0 C li ∧ t = 0 ∧ sidePt (C.sideWalk C.sideBeta) p t = (interiorWalk Q).vtx 0) ∨
      (p = c0 C li + C.m ∧ t = 0 ∧
        sidePt (C.sideWalk C.sideBeta) p t = (interiorWalk Q).vtx C.m) := by
  obtain ⟨h1, h2, h3⟩ := inner_of_interior hQ T hD hli hc hA hnear
  rcases h2.lt_or_eq with h2 | h2
  · have h4 : p = c0 C li ∧ t = 0 := by
      by_contra h5; exact hnI ⟨h1, h2, h5⟩
    obtain ⟨rfl, rfl⟩ := h4
    left
    refine ⟨rfl, rfl, ?_⟩
    rw [Chazelle.Chain.sidePt_zero]
    have := vtx_c0 hQ T hD hli (j := 0) (Nat.zero_le _)
    rwa [zero_add] at this
  · have ht := h3 h2
    subst ht
    right
    refine ⟨h2, rfl, ?_⟩
    rw [Chazelle.Chain.sidePt_zero, h2]
    have := vtx_c0 hQ T hD hli (j := C.m) le_rfl
    rwa [add_comm] at this

/-- **The point of the open last edge** at a vertex height is at the mapped position `m`. -/
theorem last_edge_pt {h : ℕ} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hy : (lerp (Q.vtx C.m) (Q.vtx 0) s).2 = (Q.vtx h).2) :
    0 ≤ (interiorModel Q).param Q ⟨C.m, h + 1⟩ ∧ (interiorModel Q).param Q ⟨C.m, h + 1⟩ < 1 ∧
      sidePt (interiorWalk Q) C.m ((interiorModel Q).param Q ⟨C.m, h + 1⟩) =
        lerp (Q.vtx C.m) (Q.vtx 0) s := by
  have hmn := T.hm
  have hIn : (interiorWalk Q).n = Q.n := Trans.iw_n
  have hwrap : (C.m + 1) % (interiorWalk Q).n = 0 := by rw [hIn, ← hmn, Nat.mod_self]
  have hne := iw_edge_ne hQ T hD hli (q := C.m) (by omega)
  have hv0 := iw_vtx_idx hli (Q := Q) (j := 0) (by omega)
  have hvm := iw_vtx_idx hli (Q := Q) (j := C.m) (by omega)
  unfold idxI at hv0 hvm
  by_cases hl : li = true
  · rw [ite_eq_left hl] at hv0 hvm
    have hpar : (interiorModel Q).param Q ⟨C.m, h + 1⟩ = s := by
      refine param_of_lerp (interiorModel Q) Q hne ?_
      show (lerp ((interiorWalk Q).vtx C.m) ((interiorWalk Q).vtx ((C.m + 1) %
        (interiorWalk Q).n)) s).2 = _
      rw [hwrap, hvm, hv0]; exact hy
    rw [hpar]
    refine ⟨hs.1.le, hs.2, ?_⟩
    unfold sidePt; rw [hwrap, hvm, hv0]
  · rw [ite_eq_right hl, show Q.n - 1 - 0 = C.m by omega] at hv0
    rw [ite_eq_right hl, show Q.n - 1 - C.m = 0 by omega] at hvm
    have hrev : lerp (Q.vtx C.m) (Q.vtx 0) s = lerp (Q.vtx 0) (Q.vtx C.m) (1 - s) := by
      apply Prod.ext <;> simp [Chazelle.Geometry.lerp] <;> ring
    have hpar : (interiorModel Q).param Q ⟨C.m, h + 1⟩ = 1 - s := by
      refine param_of_lerp (interiorModel Q) Q hne ?_
      show (lerp ((interiorWalk Q).vtx C.m) ((interiorWalk Q).vtx ((C.m + 1) %
        (interiorWalk Q).n)) (1 - s)).2 = _
      rw [hwrap, hvm, hv0, ← hrev]; exact hy
    rw [hpar]
    refine ⟨by linarith [hs.2], by linarith [hs.1], ?_⟩
    unfold sidePt; rw [hwrap, hvm, hv0, hrev]

/-- **The mapped position of an end that is not inner** has the point of the corresponding
end of the piece: the end of the chord itself (if the chord sees the interior there) or the
crossing with the open last edge. -/
theorem other_end {y a b : ℝ} (hc : hseg y a b ∈ (chainModel C).Adm) {h : ℕ} (_hh : h < Q.n)
    (hy : (Q.vtx h).2 = y) {p : ℕ}
    (hA : SideAttach (C.sideWalk C.sideBeta) (hseg y a b) p ((chainModel C).param Q ⟨p, h + 1⟩))
    (hnI : ¬ (c0 C li ≤ p ∧ p < c0 C li + C.m ∧
      ¬ (p = c0 C li ∧ (chainModel C).param Q ⟨p, h + 1⟩ = 0)))
    {z : Point} (hzy : z.2 = y)
    (hcase : (z = sidePt (C.sideWalk C.sideBeta) p ((chainModel C).param Q ⟨p, h + 1⟩) ∧
        ∃ r > 0, ∀ x ∈ hseg y a b, x ≠ z → dist x z < r → x ∈ Q.filled \ Q.boundary) ∨
      (z ∈ C.dom ∧ z ∈ Q.boundary)) :
    0 ≤ (interiorModel Q).param Q ⟨mapE Q.n (c0 C li) p, h + 1⟩ ∧
      (interiorModel Q).param Q ⟨mapE Q.n (c0 C li) p, h + 1⟩ < 1 ∧
      sidePt (interiorWalk Q) (mapE Q.n (c0 C li) p)
        ((interiorModel Q).param Q ⟨mapE Q.n (c0 C li) p, h + 1⟩) = z := by
  have hmn := T.hm
  have hm1 := C.one_le
  have hIn : (interiorWalk Q).n = Q.n := Trans.iw_n
  rw [mapE_eq hQ T hD hli]
  set t := (chainModel C).param Q ⟨p, h + 1⟩ with ht
  have hA' := hA
  obtain ⟨hp, ht0, ht1, hmem, -⟩ := hA'
  rcases hcase with ⟨rfl, hnear⟩ | ⟨hzD, hzb⟩
  · rcases special_end hQ T hD hli hc hA hnear hnI with ⟨rfl, -, hpt⟩ | ⟨rfl, ht0', hpt⟩
    · rw [ite_eq_left ⟨le_rfl, by omega⟩]
      obtain ⟨e1, e2⟩ := inner_param hQ T hD hli (h := h) (p := c0 C li) le_rfl (by omega)
      rw [e1]
      exact ⟨ht0, ht1, e2⟩
    · rw [ite_eq_right (by omega)]
      have hwrap : (C.m + 1) % (interiorWalk Q).n = 0 := by rw [hIn, ← hmn, Nat.mod_self]
      have hpar : (interiorModel Q).param Q ⟨C.m, h + 1⟩ = 0 := by
        refine param_of_lerp (interiorModel Q) Q (iw_edge_ne hQ T hD hli (by omega)) ?_
        show (lerp ((interiorWalk Q).vtx C.m) ((interiorWalk Q).vtx ((C.m + 1) %
          (interiorWalk Q).n)) 0).2 = _
        rw [Chazelle.Geometry.lerp_zero, hy, ← hpt]
        exact hmem.1
      rw [hpar, Chazelle.Chain.sidePt_zero, ← hpt]
      exact ⟨le_rfl, one_pos, rfl⟩
  · obtain ⟨s, hs, rfl⟩ := T.boundary_dom hzb hzD
    have hh' : (Q.vtx C.m).2 ≠ (Q.vtx 0).2 := hD C.m 0 (by omega) (by omega) (by omega)
    obtain ⟨hne1, hne2, -⟩ := lerp_snd_ne hh' hs
    have hJ : ¬ (c0 C li ≤ p ∧ p < c0 C li + C.m) := by
      rintro ⟨h1, h2⟩
      have h3 : p = c0 C li ∧ t = 0 := by
        by_contra h4; exact hnI ⟨h1, h2, h4⟩
      obtain ⟨rfl, ht0'⟩ := h3
      have hpt : sidePt (C.sideWalk C.sideBeta) (c0 C li) t = (interiorWalk Q).vtx 0 := by
        rw [ht0', Chazelle.Chain.sidePt_zero]
        have := vtx_c0 hQ T hD hli (j := 0) (Nat.zero_le _)
        rwa [zero_add] at this
      have hy0 : ((interiorWalk Q).vtx 0).2 = y := by rw [← hpt]; exact hmem.1
      rcases (iw_ends hQ T hD hli).1 with e | e <;> rw [e] at hy0
      · exact hne2 (by rw [hzy, hy0])
      · exact hne1 (by rw [hzy, hy0])
    rw [ite_eq_right hJ]
    exact last_edge_pt hQ T hD hli hs (by rw [hzy, hy])

omit hQ T hD hli in
/-- The piece of a chord of the chain model, as a horizontal segment. -/
theorem piece_bounds (_hQ : Q.Simple) (_T : Trans.Top Q C) (_hD : Trans.DistinctH Q)
    (_hli : li = true ↔ Mountain.LeftInside Q) {y a b y' a' b' : ℝ}
    (hch' : IsHChordIn (Q.filled \ Q.boundary) y' a' b')
    (hsub : hseg y' a' b' ⊆ hseg y a b) : y' = y ∧ a ≤ a' ∧ b' ≤ b :=
  hseg_sub hch'.lt.le hsub

omit hQ T hD in
omit hli in
/-- The end of a piece is a boundary point of `Q`. -/
theorem piece_ends_bd (_hQ : Q.Simple) (_T : Trans.Top Q C) (_hD : Trans.DistinctH Q) {y a b : ℝ}
    (hch : IsHChordIn (Q.filled \ Q.boundary) y a b) :
    ((a, y) : Point) ∈ Q.boundary ∧ ((b, y) : Point) ∈ Q.boundary :=
  FactsInterior.hchord_end_mem_boundary hch

/-- **The mapped end of a record**: for a piece `[a', b'] × {y}` of the chord of a record and
an end of the record, the mapped position has the point of the corresponding end of the
piece.  `hcorr` says which end: the end `e` of the chord and the end `z` of the piece, with the
part of the chord between them outside the piece. -/
theorem mapped_end {y a b : ℝ} (hc : hseg y a b ∈ (chainModel C).Adm)
    (hch : IsHChordIn C.dom y a b) {h : ℕ} (hh : h < Q.n) (hy : (Q.vtx h).2 = y) {p : ℕ}
    (hA : SideAttach (C.sideWalk C.sideBeta) (hseg y a b) p ((chainModel C).param Q ⟨p, h + 1⟩))
    {a' b' : ℝ} (hch' : IsHChordIn (Q.filled \ Q.boundary) y a' b')
    (hsub : hseg y a' b' ⊆ hseg y a b) {z : Point}
    (hz : z = ((a', y) : Point) ∧ sidePt (C.sideWalk C.sideBeta) p
        ((chainModel C).param Q ⟨p, h + 1⟩) = ((a, y) : Point) ∨
      z = ((b', y) : Point) ∧ sidePt (C.sideWalk C.sideBeta) p
        ((chainModel C).param Q ⟨p, h + 1⟩) = ((b, y) : Point)) :
    0 ≤ (interiorModel Q).param Q ⟨mapE Q.n (c0 C li) p, h + 1⟩ ∧
      (interiorModel Q).param Q ⟨mapE Q.n (c0 C li) p, h + 1⟩ < 1 ∧
      sidePt (interiorWalk Q) (mapE Q.n (c0 C li) p)
        ((interiorModel Q).param Q ⟨mapE Q.n (c0 C li) p, h + 1⟩) = z := by
  have hmn := T.hm
  have hm1 := C.one_le
  have hh' : (Q.vtx C.m).2 ≠ (Q.vtx 0).2 := hD C.m 0 (by omega) (by omega) (by omega)
  obtain ⟨-, ha', hb'⟩ := piece_bounds hQ T hD hli hch' hsub
  have hlt' := hch'.lt
  obtain ⟨hzbA, hzbB⟩ := piece_ends_bd hQ T hD hch'
  set t := (chainModel C).param Q ⟨p, h + 1⟩ with ht
  have hA' := hA
  obtain ⟨hp, ht0, ht1, -⟩ := hA'
  by_cases hI : c0 C li ≤ p ∧ p < c0 C li + C.m ∧ ¬ (p = c0 C li ∧ t = 0)
  · -- an inner end: the piece there is this piece
    obtain ⟨h1, h2, h3⟩ := hI
    obtain ⟨y'', a'', b'', hch'', hsub'', hend⟩ := piece_at_inner hQ T hD hli hc hA h1 h2 h3
    have heq := Trans.one_piece hQ T hh' hch ⟨y'', a'', b'', hch'', rfl⟩ ⟨y, a', b', hch', rfl⟩
      hsub'' hsub
    obtain ⟨rfl, rfl, rfl⟩ := Merge.hseg_inj hch''.lt.le heq
    rw [mapE_eq hQ T hD hli, ite_eq_left ⟨h1, h2⟩]
    obtain ⟨e1, e2⟩ := inner_param hQ T hD hli (h := h) h1 h2
    rw [e1, e2]
    refine ⟨ht0, ht1, ?_⟩
    rcases hz with ⟨rfl, hpt⟩ | ⟨rfl, hpt⟩
    · rcases hend with h4 | h4
      · exact h4
      · exfalso
        have := congrArg Prod.fst (h4.symm.trans hpt)
        simp only at this
        linarith
    · rcases hend with h4 | h4
      · exfalso
        have := congrArg Prod.fst (h4.symm.trans hpt)
        simp only at this
        linarith
      · exact h4
  · -- not inner: the chord's end or the crossing with the last edge
    refine other_end hQ T hD hli hc hh hy hA hI ?_ ?_
    · rcases hz with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
    rcases hz with ⟨rfl, hpt⟩ | ⟨rfl, hpt⟩
    · rcases ha'.lt_or_eq with hlt | heq
      · right
        exact ⟨hch.open_mem a' hlt (by linarith), hzbA⟩
      · left
        subst heq
        refine ⟨hpt.symm, b' - a, by linarith, fun x hx hxe hxd => ?_⟩
        obtain ⟨hxy, hxa, -⟩ := hx
        have hx1 : x.1 ≠ a := fun e => hxe (Prod.ext e hxy)
        have hd : |x.1 - a| < b' - a := by
          have := hxd
          rw [Prod.dist_eq, Real.dist_eq] at this
          exact lt_of_le_of_lt (le_max_left _ _) this
        rw [abs_of_nonneg (by linarith)] at hd
        rw [show x = ((x.1, y) : Point) from Prod.ext rfl hxy]
        exact hch'.open_mem _ (lt_of_le_of_ne hxa (Ne.symm hx1)) (by linarith)
    · rcases hb'.lt_or_eq with hlt | heq
      · right
        exact ⟨hch.open_mem b' (by linarith) hlt, hzbB⟩
      · left
        subst heq
        refine ⟨hpt.symm, b' - a', by linarith, fun x hx hxe hxd => ?_⟩
        obtain ⟨hxy, -, hxb⟩ := hx
        have hx1 : x.1 ≠ b' := fun e => hxe (Prod.ext e hxy)
        have hd : |x.1 - b'| < b' - a' := by
          have := hxd
          rw [Prod.dist_eq, Real.dist_eq] at this
          exact lt_of_le_of_lt (le_max_left _ _) this
        rw [abs_of_nonpos (by linarith)] at hd
        rw [show x = ((x.1, y) : Point) from Prod.ext rfl hxy]
        exact hch'.open_mem _ (by linarith) (lt_of_le_of_ne hxb hx1)

omit hQ T hD hli in
/-- The chord of a record of the chain model, with its two ends. -/
theorem rec_chord {x : ℕ × ℕ × ℕ}
    (hcA : (recOf x).toSet (chainModel C) Q ∈ (chainModel C).Adm)
    (hatt : (recOf x).Attached (chainModel C) Q) :
    ∃ y a b, IsHChordIn C.dom y a b ∧ (recOf x).toSet (chainModel C) Q = hseg y a b ∧
      (Q.vtx x.1).2 = y ∧
      sidePt (C.sideWalk C.sideBeta) x.2.1 ((chainModel C).param Q ⟨x.2.1, x.1 + 1⟩) =
        ((a, y) : Point) ∧
      sidePt (C.sideWalk C.sideBeta) x.2.2 ((chainModel C).param Q ⟨x.2.2, x.1 + 1⟩) =
        ((b, y) : Point) := by
  obtain ⟨y, a, b, hch, -, hcab⟩ := hcA
  have hcab' := hcab
  rw [toSet_recOf] at hcab'
  obtain ⟨hy, ha, hb⟩ := Merge.hseg_inj hch.lt.le hcab'.symm
  obtain ⟨⟨-, -, -, hmL, -⟩, ⟨-, -, -, hmR, -⟩⟩ := hatt
  rw [hcab] at hmL hmR
  refine ⟨y, a, b, hch, hcab, hy.symm, Prod.ext ha.symm hmL.1, Prod.ext hb.symm hmR.1⟩

/-- **A kept record**: its mapped triple is a correctly attached interior chord inside its
chord. -/
theorem rec_kept {x : ℕ × ℕ × ℕ} (hx : x.1 < Q.n)
    (hcA : (recOf x).toSet (chainModel C) Q ∈ (chainModel C).Adm)
    (hatt : (recOf x).Attached (chainModel C) Q) (hk : keepT li Q.n (c0 C li) x = true) :
    (recOf (trT Q.n (c0 C li) x)).toSet (interiorModel Q) Q ∈ (interiorModel Q).Adm ∧
      (recOf (trT Q.n (c0 C li) x)).toSet (interiorModel Q) Q ⊆
        (recOf x).toSet (chainModel C) Q ∧
      (recOf (trT Q.n (c0 C li) x)).Attached (interiorModel Q) Q := by
  obtain ⟨y, a, b, hch, hcab, hy, heL, heR⟩ := rec_chord hcA hatt
  obtain ⟨hAL, hAR⟩ := hatt
  rw [hcab] at hAL hAR hcA
  -- a piece, at an inner end
  have hpiece : ∃ a' b', IsHChordIn (Q.filled \ Q.boundary) y a' b' ∧
      hseg y a' b' ⊆ hseg y a b := by
    have hk' : innerE li Q.n (c0 C li) x.1 x.2.1 = true ∨
        innerE li Q.n (c0 C li) x.1 x.2.2 = true := by
      unfold keepT at hk; simpa [Bool.or_eq_true] using hk
    rcases hk' with hk' | hk'
    · obtain ⟨h1, h2, h3⟩ := (innerE_iff hQ T hD hli hx).1 hk'
      obtain ⟨y', a', b', hch', hsub, -⟩ := piece_at_inner hQ T hD hli hcA hAL h1 h2 h3
      obtain ⟨rfl, -, -⟩ := piece_bounds hQ T hD hli hch' hsub
      exact ⟨a', b', hch', hsub⟩
    · obtain ⟨h1, h2, h3⟩ := (innerE_iff hQ T hD hli hx).1 hk'
      obtain ⟨y', a', b', hch', hsub, -⟩ := piece_at_inner hQ T hD hli hcA hAR h1 h2 h3
      obtain ⟨rfl, -, -⟩ := piece_bounds hQ T hD hli hch' hsub
      exact ⟨a', b', hch', hsub⟩
  obtain ⟨a', b', hch', hsub⟩ := hpiece
  obtain ⟨hl0, hl1, hlpt⟩ := mapped_end hQ T hD hli hcA hch hx hy (p := x.2.1) hAL hch' hsub
    (Or.inl ⟨rfl, heL⟩)
  obtain ⟨hr0, hr1, hrpt⟩ := mapped_end hQ T hD hli hcA hch hx hy (p := x.2.2) hAR hch' hsub
    (Or.inr ⟨rfl, heR⟩)
  have hset : (recOf (trT Q.n (c0 C li) x)).toSet (interiorModel Q) Q = hseg y a' b' := by
    rw [toSet_recOf]
    show hseg (Q.vtx x.1).2 (sidePt (interiorWalk Q) (mapE Q.n (c0 C li) x.2.1)
      ((interiorModel Q).param Q ⟨mapE Q.n (c0 C li) x.2.1, x.1 + 1⟩)).1
      (sidePt (interiorWalk Q) (mapE Q.n (c0 C li) x.2.2)
      ((interiorModel Q).param Q ⟨mapE Q.n (c0 C li) x.2.2, x.1 + 1⟩)).1 = _
    rw [hlpt, hrpt, hy]
  have hmapLt : ∀ p, mapE Q.n (c0 C li) p < Q.n := fun p => by
    have := T.hm
    unfold mapE; split_ifs <;> omega
  refine ⟨by rw [hset]; exact ⟨y, a', b', hch', rfl⟩, by rw [hset, hcab]; exact hsub, ?_, ?_⟩
  · show SideAttach (interiorWalk Q) _ _ _
    rw [hset]
    exact attach_int hQ hch' (hmapLt _) hl0 hl1 (Or.inl hlpt)
  · show SideAttach (interiorWalk Q) _ _ _
    rw [hset]
    exact attach_int hQ hch' (hmapLt _) hr0 hr1 (Or.inr hrpt)

/-- **A dropped record** contains no interior chord. -/
theorem rec_dropped {x : ℕ × ℕ × ℕ} (hx : x.1 < Q.n)
    (hcA : (recOf x).toSet (chainModel C) Q ∈ (chainModel C).Adm)
    (hatt : (recOf x).Attached (chainModel C) Q) (hk : keepT li Q.n (c0 C li) x = false)
    {d : Set Point} (hd : d ∈ (interiorModel Q).Adm)
    (hdc : d ⊆ (recOf x).toSet (chainModel C) Q) : False := by
  have hmn := T.hm
  have hm1 := C.one_le
  have hh' : (Q.vtx C.m).2 ≠ (Q.vtx 0).2 := hD C.m 0 (by omega) (by omega) (by omega)
  obtain ⟨y, a, b, hch, hcab, hy, heL, heR⟩ := rec_chord hcA hatt
  obtain ⟨hAL, hAR⟩ := hatt
  rw [hcab] at hAL hAR hcA hdc
  replace hAL : SideAttach (C.sideWalk C.sideBeta) (hseg y a b) x.2.1
      ((chainModel C).param Q ⟨x.2.1, x.1 + 1⟩) := hAL
  replace hAR : SideAttach (C.sideWalk C.sideBeta) (hseg y a b) x.2.2
      ((chainModel C).param Q ⟨x.2.2, x.1 + 1⟩) := hAR
  obtain ⟨y', a', b', hch', rfl⟩ := hd
  obtain ⟨hyy, ha', hb'⟩ := piece_bounds hQ T hD hli hch' hdc
  rw [hyy] at hch' hdc
  have hlt' := hch'.lt
  obtain ⟨hzbA, hzbB⟩ := piece_ends_bd hQ T hD hch'
  have hkL : ¬ (c0 C li ≤ x.2.1 ∧ x.2.1 < c0 C li + C.m ∧
      ¬ (x.2.1 = c0 C li ∧ (chainModel C).param Q ⟨x.2.1, x.1 + 1⟩ = 0)) := by
    rw [← innerE_iff hQ T hD hli hx]
    unfold keepT at hk; simp only [Bool.or_eq_false_iff] at hk; rw [hk.1]; simp
  have hkR : ¬ (c0 C li ≤ x.2.2 ∧ x.2.2 < c0 C li + C.m ∧
      ¬ (x.2.2 = c0 C li ∧ (chainModel C).param Q ⟨x.2.2, x.1 + 1⟩ = 0)) := by
    rw [← innerE_iff hQ T hD hli hx]
    unfold keepT at hk; simp only [Bool.or_eq_false_iff] at hk; rw [hk.2]; simp
  -- an end of the piece inside the chord is on the open last edge
  have hlast : ∀ e : ℝ, a < e → e < b → ((e, y) : Point) ∈ Q.boundary →
      ∃ s ∈ Ioo (0 : ℝ) 1, ((e, y) : Point) = lerp (Q.vtx C.m) (Q.vtx 0) s :=
    fun e h1 h2 hb => T.boundary_dom hb (hch.open_mem e h1 h2)
  -- an end of the piece at an end of the chord is `w₀` or `w_m`
  have hvL : a' = a → ((a, y) : Point) = (interiorWalk Q).vtx 0 ∨
      ((a, y) : Point) = (interiorWalk Q).vtx C.m := by
    intro heq
    subst heq
    have hnear : ∃ r > 0, ∀ z ∈ hseg y a' b, z ≠ sidePt (C.sideWalk C.sideBeta) x.2.1
        ((chainModel C).param Q ⟨x.2.1, x.1 + 1⟩) →
        dist z (sidePt (C.sideWalk C.sideBeta) x.2.1
          ((chainModel C).param Q ⟨x.2.1, x.1 + 1⟩)) < r → z ∈ Q.filled \ Q.boundary := by
      rw [heL]
      refine ⟨b' - a', by linarith, fun z hz hze hzd => ?_⟩
      obtain ⟨hzy, hza, -⟩ := hz
      have hz1 : z.1 ≠ a' := fun e => hze (Prod.ext e hzy)
      have hd : |z.1 - a'| < b' - a' := by
        rw [Prod.dist_eq, Real.dist_eq] at hzd
        exact lt_of_le_of_lt (le_max_left _ _) hzd
      rw [abs_of_nonneg (by linarith)] at hd
      rw [show z = ((z.1, y) : Point) from Prod.ext rfl hzy]
      exact hch'.open_mem _ (lt_of_le_of_ne hza (Ne.symm hz1)) (by linarith)
    rcases special_end hQ T hD hli hcA (p := x.2.1) hAL hnear hkL with ⟨-, -, hpt⟩ | ⟨-, -, hpt⟩
    · left; rw [← heL, hpt]
    · right; rw [← heL, hpt]
  have hvR : b' = b → ((b, y) : Point) = (interiorWalk Q).vtx 0 ∨
      ((b, y) : Point) = (interiorWalk Q).vtx C.m := by
    intro heq
    subst heq
    have hnear : ∃ r > 0, ∀ z ∈ hseg y a b', z ≠ sidePt (C.sideWalk C.sideBeta) x.2.2
        ((chainModel C).param Q ⟨x.2.2, x.1 + 1⟩) →
        dist z (sidePt (C.sideWalk C.sideBeta) x.2.2
          ((chainModel C).param Q ⟨x.2.2, x.1 + 1⟩)) < r → z ∈ Q.filled \ Q.boundary := by
      rw [heR]
      refine ⟨b' - a', by linarith, fun z hz hze hzd => ?_⟩
      obtain ⟨hzy, -, hzb⟩ := hz
      have hz1 : z.1 ≠ b' := fun e => hze (Prod.ext e hzy)
      have hd : |z.1 - b'| < b' - a' := by
        rw [Prod.dist_eq, Real.dist_eq] at hzd
        exact lt_of_le_of_lt (le_max_left _ _) hzd
      rw [abs_of_nonpos (by linarith)] at hd
      rw [show z = ((z.1, y) : Point) from Prod.ext rfl hzy]
      exact hch'.open_mem _ (by linarith) (lt_of_le_of_ne hzb hz1)
    rcases special_end hQ T hD hli hcA (p := x.2.2) hAR hnear hkR with ⟨-, -, hpt⟩ | ⟨-, -, hpt⟩
    · left; rw [← heR, hpt]
    · right; rw [← heR, hpt]
  -- heights
  have hends := iw_ends hQ T hD hli
  have hyv : ∀ v : Point, (v = (interiorWalk Q).vtx 0 ∨ v = (interiorWalk Q).vtx C.m) →
      v.2 = (Q.vtx 0).2 ∨ v.2 = (Q.vtx C.m).2 := by
    rintro v (rfl | rfl)
    · rcases hends.1 with e | e <;> rw [e]
      · left; rfl
      · right; rfl
    · rcases hends.2 with e | e <;> rw [e]
      · left; rfl
      · right; rfl
  have hnot : ∀ e : ℝ, a < e → e < b → ((e, y) : Point) ∈ Q.boundary →
      y ≠ (Q.vtx 0).2 ∧ y ≠ (Q.vtx C.m).2 := by
    intro e h1 h2 hb
    obtain ⟨s, hs, hes⟩ := hlast e h1 h2 hb
    obtain ⟨hn1, hn2, -⟩ := lerp_snd_ne hh' hs
    have hy' : y = (lerp (Q.vtx C.m) (Q.vtx 0) s).2 := by rw [← hes]
    exact ⟨by rw [hy']; exact hn2, by rw [hy']; exact hn1⟩
  rcases ha'.lt_or_eq with haL | haL <;> rcases hb'.lt_or_eq with hbR | hbR
  · -- both ends of the piece on the open last edge: the same point
    obtain ⟨s, hs, hes⟩ := hlast a' haL (by linarith) hzbA
    obtain ⟨s', hs', hes'⟩ := hlast b' (by linarith) hbR hzbB
    have h2 := congrArg Prod.snd hes
    have h2' := congrArg Prod.snd hes'
    simp only [Chazelle.Geometry.lerp_snd] at h2 h2'
    have hss : s = s' := by
      have : (s - s') * ((Q.vtx 0).2 - (Q.vtx C.m).2) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd (sub_eq_zero.1 h) (Ne.symm hh')
    subst hss
    have h1 := congrArg Prod.fst hes
    have h1' := congrArg Prod.fst hes'
    simp only at h1 h1'
    linarith
  · -- the piece reaches the right end only
    have hv := hyv _ (hvR hbR)
    obtain ⟨n1, n2⟩ := hnot a' haL (by linarith) hzbA
    rcases hv with hv | hv <;> simp only at hv
    · exact n1 hv
    · exact n2 hv
  · have hv := hyv _ (hvL haL.symm)
    obtain ⟨n1, n2⟩ := hnot b' (by linarith) hbR hzbB
    rcases hv with hv | hv <;> simp only at hv
    · exact n1 hv
    · exact n2 hv
  · -- both ends of the chord are `w₀` or `w_m`
    have hL := hvL haL.symm
    have hR := hvR hbR
    have hab : ((a, y) : Point) ≠ (b, y) := fun e => hch.lt.ne (congrArg Prod.fst e)
    have hsn := iw_snd_ne hQ T hD hli (j := 0) (k := C.m) (by omega) (by omega) (by omega)
    rcases hL with hL | hL <;> rcases hR with hR | hR
    · exact hab (hL.trans hR.symm)
    · apply hsn; rw [← hL, ← hR]
    · apply hsn; rw [← hL, ← hR]
    · exact hab (hL.trans hR.symm)

end

end DrvT

end Chazelle.Core
