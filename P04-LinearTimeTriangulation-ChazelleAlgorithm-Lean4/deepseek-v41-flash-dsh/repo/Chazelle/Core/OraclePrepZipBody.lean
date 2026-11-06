module

public import Chazelle.Golf

public import Chazelle.Core.OraclePrepZipPieces

/-!
# Lemma 3.6 (WP-H), preprocessing part 10: one step of the zipper

For the spine position `x` (`110299`) and a side `d` (`true`: the start of the arc, `false`: its
end), `zipBody d` analyses the end of the arc, and if its key lies in the open halves of the tour
range, locates the mirror of the key, takes the arc just before (`d`) or after (`¬ d`) it, and
leaves the normalised pair with `x` (`110290 … 110292`).  `zipBody_exec`: its result is
`zipSk x` (`d`) or `zipEk x` (`¬ d`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- An end of the arc at a spine position: the start (`true`) or the end (`false`). -/
def endPos (N : NF) (d : Bool) (p : ℕ) : WPos :=
  if d then (N.arc (sj N p)).s else (N.arc (sj N p)).e

theorem key_endPos (C : Chain) (Q : Polygon) (N : NF) (d : Bool) (p : ℕ) :
    (chainModel C).key Q (endPos N d p) =
      if d then sk (chainModel C) Q N p else ek (chainModel C) Q N p := by
  unfold endPos sk ek; cases d <;> rfl

/-- The register holding the offset of the end in an arc record. -/
def offR (d : Bool) : ℕ := if d then 120011 else 110205

/-- **The environment of the zipper.** -/
structure ZEnv (P : Polygon) (W lo : ℕ) (C : Chain) (N : NF) (V : QV) (c : Config) : Prop where
  good : GoodEnv P
  hW : 8 * P.n + 32 ≤ W
  CQ : C.P = Qof P
  simple : C.P.Simple
  s_lt : C.s < P.n
  isNF : IsNF (chainModel C) (Qof P) N
  loc : Robust lo c.nmem fun m => LocMemOK P V m W (chainModel C) N ∧ m (V.NB + 4) = V.AB ∧
    m (V.NB + 6) = V.SB
  pk : PosK P.n C.s C.m (C.sideS C.sideBeta) (rT C) c
  rMD : c.nreg 120040 = V.MD
  rNB : c.nreg 120014 = V.NB
  rTB : c.nreg 120041 = V.TB
  rL : c.nreg 120042 = V.L
  rA : c.nreg 120030 = V.A
  rAB : c.nreg 120044 = V.AB
  rSB : c.nreg 120046 = V.SB
  r3 : c.nreg 110205 = 3

/-- The registers the zipper environment reads. -/
def ZKeep (r : ℕ) : Bool :=
  decide (120010 ≤ r ∧ r ≤ 120049) || decide (110050 ≤ r ∧ r ≤ 110054) || decide (r = 110205)

theorem ZEnv.stable {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c c' : Config}
    (h : ZEnv P W lo C N V c) (hr : ∀ r, ZKeep r = true → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < lo → c'.nmem a = c.nmem a) : ZEnv P W lo C N V c' where
  good := h.good
  hW := h.hW
  CQ := h.CQ
  simple := h.simple
  s_lt := h.s_lt
  isNF := h.isNF
  loc := h.loc.transport hm
  pk := h.pk.congr fun r hr' => hr r (by
    simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq]; omega)
  rMD := by rw [hr _ (⌖)]; exact h.rMD
  rNB := by rw [hr _ (⌖)]; exact h.rNB
  rTB := by rw [hr _ (⌖)]; exact h.rTB
  rL := by rw [hr _ (⌖)]; exact h.rL
  rA := by rw [hr _ (⌖)]; exact h.rA
  rAB := by rw [hr _ (⌖)]; exact h.rAB
  rSB := by rw [hr _ (⌖)]; exact h.rSB
  r3 := by rw [hr _ (⌖)]; exact h.r3

section Facts

variable {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}

theorem ZEnv.mem (h : ZEnv P W lo C N V c) :
    LocMemOK P V c.nmem W (chainModel C) N ∧ c.nmem (V.NB + 4) = V.AB ∧
      c.nmem (V.NB + 6) = V.SB := h.loc.holds

theorem ZEnv.Qn (h : ZEnv P W lo C N V c) : C.P.n = P.n := by
  rw [h.CQ]; exact shear_n _ _

theorem ZEnv.m_lt (h : ZEnv P W lo C N V c) : C.m < P.n := by
  have := C.m_lt; Ξ' h.Qn at this; exact this

theorem ZEnv.hD (h : ZEnv P W lo C N V c) : DistinctHeights C.P := by
  rw [h.CQ]; exact distinctHeights_of_goodEnv h.good

/-- The ends of an arc are proper walk positions on the walk. -/
theorem ZEnv.arcEnd (h : ZEnv P W lo C N V c) {j : ℕ} (hj : j < N.arcs.length) (d : Bool) :
    let x := if d then (N.arc j).s else (N.arc j).e
    x.edge < 2 * C.m + 7 ∧ x.hgt ≤ C.P.n ∧ 0 ≤ (chainModel C).param C.P x ∧
      (chainModel C).param C.P x < 1 := by
  have hN := h.isNF
  obtain ⟨reg, -, hA, -⟩ := NFLoc.isNF_arcs hN
  obtain ⟨-, harc⟩ := hA.1 j hj
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hprop⟩ := id hN
  obtain ⟨hs, he⟩ := hprop j hj
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  have hkey : ∀ (w : WPos), ProperPos (chainModel C) (Qof P) (Qof P).n w →
      (chainModel C).key (Qof P) w < (chainModel C).W.n → w.edge < 2 * C.m + 7 := by
    intro w hw hk
    have : (w.edge : ℝ) < (chainModel C).W.n := by
      have := hw.1
      unfold Model.key at hk
      linarith
    Ξ' hnW at this
    exact_mod_cast this
  Ξ h.CQ
  cases d
  · exact ⟨hkey _ he harc.2.2.2.1, he.2.2, he.1, he.2.1⟩
  · exact ⟨hkey _ hs harc.2.1, hs.2.2, hs.1, hs.2.1⟩

end Facts

/-! ## The analysis of the end of the arc -/

/-- Copy the position and the offset, load the end, analyse it. -/
def prepS (d : Bool) : Stmt :=
  .seq (block [.copyN 110203 110299, .copyN 110204 (offR d)]) (.seq arcPosS posA)

/-- The registers written by `prepS`. -/
def BPR (r : ℕ) : Bool := decide (110100 ≤ r ∧ r ≤ 110108) || decide (110200 ≤ r ∧ r ≤ 110204)

theorem wr_prepS (d : Bool) : wr BPR (prepS d) = true := by cases d <;> decide

/-- The end of an arc read from memory. -/
theorem ZEnv.endPos_mem {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (h : ZEnv P W lo C N V c) {x : ℕ} (hx : x < V.A) (d : Bool) :
    c.nmem (V.SB + x) = sj N x ∧ sj N x < V.A ∧
      c.nmem (V.AB + 5 * c.nmem (V.SB + x) + (if d then 1 else 3)) = (endPos N d x).edge ∧
      c.nmem (V.AB + 5 * c.nmem (V.SB + x) + (if d then 1 else 3) + 1) = (endPos N d x).hgt := by
  obtain ⟨hL, hAB, hSB⟩ := h.mem
  have hA := hL.A
  have hN := h.isNF
  have hnf := hL.nf
  have hlen := NFLoc.seq_length hN
  have hsq : c.nmem (V.SB + x) = sj N x := by
    rw [← hSB]; exact hnf.2.2.2.2.2.2.2.2.1 x (by rw [hlen, ← hA]; exact hx)
  have hjl : sj N x < V.A := by rw [hA]; exact NFLoc.seq_lt hN (by rw [← hA]; exact hx)
  obtain ⟨-, a1, a2, a3, a4⟩ := hnf.2.2.2.2.2.2.1 (sj N x) (by rw [← hA]; exact hjl)
  refine ⟨hsq, hjl, ?_, ?_⟩ <;> rw [hsq, ← hAB] <;> cases d
  · simpa [endPos] using a3
  · simpa [endPos] using a1
  · simpa [endPos, Nat.add_assoc] using a4
  · simpa [endPos, Nat.add_assoc] using a2

open Classical in
theorem prepS_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {x : ℕ} (hx : c.nreg 110299 = x)
    (hxA : x < V.A) (d : Bool) :
    ∃ c' k, Exec P W (prepS d) c c' k ∧ k ≤ 80 ∧ FrameB BPR c c' ∧
      c'.nreg 110204 = (if d then 1 else 3) ∧ c'.nreg 110203 = x ∧
      c'.nreg 110104 = (if InI C ((chainModel C).key C.P (endPos N d x)) then 1 else 0) ∧
      (c'.nreg 110105, c'.nreg 110106) =
        ((mirPos C (endPos N d x).edge (endPos N d x).hgt).edge,
          (mirPos C (endPos N d x).edge (endPos N d x).hgt).hgt) := by
  obtain ⟨hL, -, -⟩ := h.mem
  have hk := h.pk
  -- the copies
  obtain ⟨c₀, e₀, v03, v04, r₀⟩ : ∃ c₀, Exec P W (block [.copyN 110203 110299,
      .copyN 110204 (offR d)]) c c₀ 2 ∧ c₀.nreg 110203 = x ∧
      c₀.nreg 110204 = (if d then 1 else 3) ∧ FrameB BPR c c₀ := by
    have hwr : wr BPR (block [.copyN 110203 110299, .copyN 110204 (offR d)]) = true := by
      cases d <;> decide
    suffices H : ∃ c₀ k, Exec P W (block [.copyN 110203 110299, .copyN 110204 (offR d)]) c c₀ k ∧
        k = 2 ∧ c₀.nreg 110203 = x ∧ c₀.nreg 110204 = (if d then 1 else 3) by
      obtain ⟨c₀, k, e, hk', a, b⟩ := H
      subst hk'
      exact ⟨c₀, e, a, b, exec_frameB e hwr⟩
    cases d
    · ϴ offR, Bool.false_eq_true, ite_false
      exec_block
      refine ⟨rfl, ?_, ?_⟩ <;> config_simp
      · exact hx
      · exact h.r3
    · ϴ offR, ite_true
      exec_block
      refine ⟨rfl, ?_, ?_⟩ <;> config_simp
      · exact hx
      · exact hk.one
  have h₀ : ZEnv P W lo C N V c₀ := h.stable (fun r hr => r₀.1 r (by
    ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at hr
    simp only [BPR, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
    (fun a _ => Ρ r₀.2.2.1)
  obtain ⟨hsq, hjl, hwv, hhv⟩ := h₀.endPos_mem hxA d
  have hTB := hL.TB_le
  have hSBl := hL.SB_le
  have hABl := hL.AB_le
  obtain ⟨-, hAB', hSB'⟩ := h.mem
  Ξ' hSB' at hSBl
  Ξ' hAB' at hABl
  have hA := hL.A
  -- the load
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, v₁, v₁'⟩ := arcPosS_exec (P := P) e₀.wb_right (AB := V.AB)
    (SB := V.SB) (A := V.A) (p := x) (o := if d then 1 else 3) h₀.rAB h₀.rSB h₀.pk.one v03 hxA v04
    (by split_ifs <;> omega) (by rw [hsq]; exact hjl) (⋄) (⋄)
  Ξ' hwv at v₁; Ξ' hhv at v₁'
  have h₁ : ZEnv P W lo C N V c₁ := h₀.stable (fun r hr => f₁.1 r (by
    ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at hr; simp; omega))
    (fun a _ => Ρ f₁.2.2.1)
  -- the analysis
  have hm1 := C.one_le
  have hmn := h.m_lt
  have hS := C.sideS_lt C.sideBeta
  have hR := rT_lt C
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, fl₂, rest₂⟩ := posA_exec (P := P) e₁.wb_right h₁.pk hm1 hmn h.s_lt hS
    hR (by have := h.hW; omega)
  set w := (endPos N d x).edge
  set hc := (endPos N d x).hgt
  obtain ⟨hw7, hh, hp0, hp1⟩ := h₀.arcEnd (j := sj N x) (by rw [← hA]; exact hjl) d
  have hwe : (if d then (N.arc (sj N x)).s else (N.arc (sj N x)).e) = endPos N d x := by
    unfold endPos; rfl
  Ξ' hwe at hw7 hh hp0 hp1
  Ξ' v₁ at fl₂ rest₂
  obtain ⟨z₁, z₂, z₃⟩ := rest₂ (⋄)
  Ξ' v₁' at z₂ z₃
  have hz : c₂.nreg 110103 = nz C w hc := Ρ z₂, ← nzN_eq, h.Qn
  have ex : Exec P W (prepS d) c c₂ _ := .seq e₀ (.seq e₁ e₂)
  refine ⟨c₂, _, ex, ⋄, exec_frameB ex (wr_prepS d), ?_, ?_, ?_, ?_⟩
  · Ξ f₂.1 _ (⌖), f₁.1 _ (⌖), v04
  · Ξ f₂.1 _ (⌖), f₁.1 _ (⌖), v03
  · Ξ fl₂, hz
    have hiff := inI_iff C h.hD (w := w) (hc := hc) hw7 hh ⟨hp0, hp1⟩
    have : (chainModel C).key C.P (endPos N d x) = (chainModel C).key C.P ⟨w, hc⟩ := rfl
    Ξ this
    by_cases hI : InI C ((chainModel C).key C.P ⟨w, hc⟩)
    · Ξ ite_eq_left hI, ite_eq_left ((inT_eq C _ _).2 (hiff.1 hI))
    · Ξ ite_eq_right hI, ite_eq_right (fun h' => hI (hiff.2 ((inT_eq C _ _).1 h')))
  · Ξ z₃, hz, mirN_eq

/-! ## The located part -/

/-- Locate the mirror, test the end of the located arc, adjust, normalise. -/
def locS (d : Bool) : Stmt :=
  .seq (block [.copyN 110210 110105, .copyN 110211 110106, .copyN 50000 120040,
      .copyN 50001 120014, .copyN 50002 110105, .copyN 50003 110106])
    (.seq myLoc (.seq (.instr (.copyN 110203 120170)) (.seq arcPosS
      (.seq (block [.copyN 110212 110100, .copyN 110100 110210])
        (.seq posA (.seq eqS (.seq (adjS d) normS)))))))

/-- The registers written by `locS`. -/
def BLS (r : ℕ) : Bool :=
  BL r || decide (110100 ≤ r ∧ r ≤ 110108) || decide (110200 ≤ r ∧ r ≤ 110204) ||
    decide (110210 ≤ r ∧ r ≤ 110215) ||
    decide (110290 ≤ r ∧ r ≤ 110292) || decide (50000 ≤ r ∧ r ≤ 50003)

theorem inTest_range {C : Chain} {z w : ℕ} (h : inTest C z w) : 6 ≤ w ∧ w < 2 * C.m + 6 := by
  have := rT_lt C
  unfold inTest at h; split_ifs at h <;> omega

theorem BL_keep {r : ℕ} (h : ZKeep r = true ∨ r = 110204 ∨ r = 110299 ∨ (110210 ≤ r ∧ r ≤ 110212)
    ∨ (110293 ≤ r ∧ r ≤ 110299)) : BL r = false := by
  ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at h
  ϴ BL, Bdir, Bloc, Bcmp, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not
  omega

open Classical in
theorem locS_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {x : ℕ} (hx : c.nreg 110299 = x)
    (hxA : x < V.A) (d : Bool) (ho : c.nreg 110204 = if d then 1 else 3)
    (hI : InI C ((chainModel C).key C.P (endPos N d x)))
    (hmir : (c.nreg 110105, c.nreg 110106) =
        ((mirPos C (endPos N d x).edge (endPos N d x).hgt).edge,
          (mirPos C (endPos N d x).edge (endPos N d x).hgt).hgt)) :
    ∃ c' k, Exec P W (locS d) c c' k ∧ k ≤ 5500 * (V.L + 1) + 300 ∧ FrameB BLS c c' ∧
      ∃ q, q < V.A ∧ ((N.F (chainModel C) (Qof P)).Nonempty →
        (if d then Before C (Qof P) N q (mk C ((chainModel C).key (Qof P) (endPos N d x)))
          else After C (Qof P) N q (mk C ((chainModel C).key (Qof P) (endPos N d x))))) ∧
      (normP x q = none → c'.nreg 110290 = 0) ∧
      ∀ z, normP x q = some z → c'.nreg 110290 = 1 ∧ c'.nreg 110291 = z.1 ∧ c'.nreg 110292 = z.2 := by
  obtain ⟨hL, hAB', hSB'⟩ := h.mem
  have hQ := h.CQ
  have hD := h.hD
  have hA := hL.A
  set w := (endPos N d x).edge with hwdef
  set hc := (endPos N d x).hgt with hcdef
  set Y := mirPos C w hc with hYdef
  -- the end and its mirror
  obtain ⟨hsq, hjl, -, -⟩ := h.endPos_mem hxA d
  obtain ⟨hw7, hh, hp0, hp1⟩ := h.arcEnd (j := sj N x) (by rw [← hA]; exact hjl) d
  have hwe : (if d then (N.arc (sj N x)).s else (N.arc (sj N x)).e) = endPos N d x := by
    unfold endPos; rfl
  Ξ' hwe at hw7 hh hp0 hp1
  have hkey : (chainModel C).key C.P (endPos N d x) = (chainModel C).key C.P ⟨w, hc⟩ := rfl
  Ξ' hkey at hI
  have hrange := inTest_range ((inI_iff C hD (w := w) (hc := hc) hw7 hh ⟨hp0, hp1⟩).1 hI)
  obtain ⟨hYk, hYp0, hYp1, hYh, hY6, hY7, -⟩ := mir_key C hD hrange.1 hrange.2 hh ⟨hp0, hp1⟩
  have hYnz := nz_mir C hD hrange.1 hrange.2 hh ⟨hp0, hp1⟩
  Ξ' ← hYdef at hYk hYp0 hYp1 hYh hY6 hY7 hYnz
  ϴ' Prod.mk.injEq at hmir
  obtain ⟨m5, m6⟩ := hmir
  -- 1. the copies
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, mm₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110210 110105,
      .copyN 110211 110106, .copyN 50000 120040, .copyN 50001 120014, .copyN 50002 110105,
      .copyN 50003 110106]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 110210 Y.edge) 110211 Y.hgt) 50000 V.MD)
        50001 V.NB) 50002 Y.edge) 50003 Y.hgt ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
    config_simp; Ξ m5, m6, h.rMD, h.rNB
  have R₁ : ∀ r, r ≠ 110210 → r ≠ 110211 → (r < 50000 ∨ 50003 < r) → c₁.nreg r = c.nreg r :=
    fun r a b c' => by rw [n₁]; simp only [upd]; split_ifs <;> first | omega
  have h₁ : ZEnv P W lo C N V c₁ := h.stable (fun r hr => R₁ r (by
      ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at hr; omega) (by
      ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at hr; omega) (by
      ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at hr; omega))
    (fun a _ => Ρ mm₁)
  have w₁ := e₁.wb_right
  -- 2. the double identification
  have hTB := hL.TB_le
  have hPW := h.hW
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hx50 : ProperPos (chainModel C) (Qof P) P.n ⟨c₁.nreg 50002, c₁.nreg 50003⟩ := by
    rw [n₁]; config_simp; Ξ ← hQ
    exact ⟨hYp0, hYp1, by rw [← h.Qn]; exact hYh⟩
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hq₂, loc1, loc2⟩ := myLoc_exec arcCover (P := P) (W := W) (c := c₁)
    w₁ ⟨h.good, ⋄, by rw [n₁]; config_simp; have := hL.md_le; omega,
      by rw [n₁, mm₁]; config_simp; exact hL.chwf, chainModel C,
      by rw [n₁, mm₁]; config_simp; exact hL.md, by rw [n₁]; config_simp; rw [hnW]; omega⟩
    h.good (⋄) (by rw [n₁, mm₁]; config_simp; exact hL.md) hL.good
    (by rw [n₁, mm₁]; config_simp; exact hL.nf) h.isNF hx50 hL.st
    (by rw [R₁ _ (⌖) (⌖) (⌖)]; exact h.rTB)
    (by rw [R₁ _ (⌖) (⌖) (⌖)]; exact h.rL) h₁.pk.zero h₁.pk.one
    (by rw [mm₁]; exact hL.tab) (by rw [← hA]; exact hL.A_lt)
    (by rw [n₁]; config_simp; exact hL.NB_le) (by rw [n₁, mm₁]; config_simp; rw [← hA]; exact hL.AB_le)
    (by rw [n₁, mm₁]; config_simp; rw [← hA]; exact hL.SB_le) hTB
  have g50 : c₁.nreg 50002 = Y.edge ∧ c₁.nreg 50003 = Y.hgt := by
    rw [n₁]; constructor <;> config_simp
  Ξ' g50.1, g50.2 at loc1 loc2
  obtain ⟨q0, hq0d⟩ : ∃ q0, c₂.nreg 120170 = q0 := ⟨_, rfl⟩
  Ξ' hq0d at hq₂ loc1 loc2
  have hq0A : q0 < V.A := by rw [hA]; exact hq₂
  have R₂ := f₂.1
  have h₂ : ZEnv P W lo C N V c₂ := h₁.stable (fun r hr => R₂ r (BL_keep (Or.inl hr)))
    (fun a _ => Ρ f₂.2.2.1)
  have mm₂ : c₂.nmem = c.nmem := f₂.2.2.1.trans mm₁
  -- 3.–4. the end of the located arc
  have e₃ := Exec.copyN (P := P) e₂.wb_right 110203 120170
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 110203 (c₂.nreg 120170) } with hc₃
  have R₃ : ∀ r, r ≠ 110203 → c₃.nreg r = c₂.nreg r := fun r hr => by
    rw [hc₃]; exact upd_other _ _ _ hr
  have h₃ : ZEnv P W lo C N V c₃ := h₂.stable (fun r hr => R₃ r (by
    ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at hr; omega)) (fun _ _ => rfl)
  obtain ⟨hsq', hjl', hwv', hhv'⟩ := h.endPos_mem hq0A d
  have o₃ : c₃.nreg 110204 = if d then 1 else 3 := by
    rw [R₃ _ (⌖), R₂ _ (BL_keep (Or.inr (Or.inl rfl))), R₁ _ (⌖) (⌖)
      (⌖), ho]
  obtain ⟨hL₃, -, -⟩ := h₃.mem
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, v₄, v₄'⟩ := arcPosS_exec (P := P) e₃.wb_right (AB := V.AB)
    (SB := V.SB) (A := V.A) (p := q0) (o := if d then 1 else 3) h₃.rAB h₃.rSB h₃.pk.one
    (by rw [hc₃]; config_simp; exact hq0d) hq0A o₃ (by split_ifs <;> omega)
    (by rw [show c₃.nmem = c.nmem from mm₂, hsq']; exact hjl')
    (by have := hL₃.SB_le; have := hL₃.TB_le; Ξ' h₃.mem.2.2 at *; omega)
    (by have := hL₃.AB_le; have := hL₃.TB_le; Ξ' h₃.mem.2.1 at *; omega)
  Ξ' show c₃.nmem = c.nmem from mm₂, hwv' at v₄
  Ξ' show c₃.nmem = c.nmem from mm₂, hhv' at v₄'
  set w2 := (endPos N d q0).edge
  set hc2 := (endPos N d q0).hgt
  have h₄ : ZEnv P W lo C N V c₄ := h₃.stable (fun r hr => f₄.1 r (by
    ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at hr; simp; omega))
    (fun a _ => Ρ f₄.2.2.1)
  -- 5. the copies
  have y210 : c₄.nreg 110210 = Y.edge := by
    rw [f₄.1 _ (⌖), R₃ _ (⌖), R₂ _ (BL_keep (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⊛, ⊛⟩))))), n₁]; config_simp
  have y211 : c₄.nreg 110211 = Y.hgt := by
    rw [f₄.1 _ (⌖), R₃ _ (⌖), R₂ _ (BL_keep (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⊛, ⊛⟩))))), n₁]; config_simp
  obtain ⟨c₅, k₅, e₅, hk₅, n₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 110212 110100,
      .copyN 110100 110210]) c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg = upd (upd c₄.nreg 110212 w2) 110100 Y.edge := by
    have w₄ := e₄.wb_right
    exec_block
    refine ⟨rfl, ?_⟩
    config_simp; Ξ v₄, y210
  have hm₅ : c₅.nmem = c₄.nmem :=
    (exec_frameB e₅ (B := fun r => decide (r = 110212 ∨ r = 110100)) (⌖)).2.2.1
  have R₅ : ∀ r, r ≠ 110212 → r ≠ 110100 → c₅.nreg r = c₄.nreg r := fun r a b => by
    Ξ n₅, upd_other _ _ _ b, upd_other _ _ _ a
  have h₅ : ZEnv P W lo C N V c₅ := h₄.stable (fun r hr => R₅ r (by
      ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at hr; omega) (by
      ϴ' ZKeep, Bool.or_eq_true, decide_eq_true_eq at hr; omega))
    (fun a _ => Ρ hm₅)
  -- 6. the normalised code of the end at the mirror's walk edge
  have hm1 := C.one_le
  have hmn := h.m_lt
  have hS := C.sideS_lt C.sideBeta
  have hR := rT_lt C
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, -, rest₆⟩ := posA_exec (P := P) e₅.wb_right h₅.pk hm1 hmn h.s_lt hS hR
    (⋄)
  have x100 : c₅.nreg 110100 = Y.edge := by rw [n₅]; config_simp
  have x101 : c₅.nreg 110101 = hc2 := Ρ R₅ _ (⌖) (⌖), v₄'
  Ξ' x100, x101 at rest₆
  obtain ⟨-, z₆, -⟩ := rest₆ hY7
  have z₆' : c₆.nreg 110103 = nz C Y.edge hc2 := Ρ z₆, ← nzN_eq, h.Qn
  -- 7. the flag of equal keys
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, v₇⟩ := eqS_exec (P := P) e₆.wb_right (⋄)
  have x212 : c₆.nreg 110212 = w2 := by rw [f₆.1 _ (⌖), n₅]; config_simp
  have x210 : c₆.nreg 110210 = Y.edge := by
    Ξ f₆.1 _ (⌖), R₅ _ (⌖) (⌖), y210
  have x211 : c₆.nreg 110211 = Y.hgt := by
    Ξ f₆.1 _ (⌖), R₅ _ (⌖) (⌖), y211
  Ξ' x212, x210, z₆', x211 at v₇
  -- 8. the adjusted arc
  have g170 : c₇.nreg 120170 = q0 := by
    rw [f₇.1 _ (⌖), f₆.1 _ (⌖), R₅ _ (⌖) (⌖),
      f₄.1 _ (⌖), R₃ _ (⌖), hq0d]
  have h₇ : ZEnv P W lo C N V c₇ := h₅.stable (fun r hr => by
      rw [f₇.1 r (by simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr; simp; omega),
        f₆.1 r (by simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr; simp [BPA]; omega)])
    (fun a _ => Ρ f₇.2.2.1, f₆.2.2.1)
  have hAW : V.A + 1 ≤ W := by
    have a := hL.SB_le; have b := hL.TB_le; have c' := hL.A_lt
    rcases Nat.eq_zero_or_pos V.L with h0 | h0
    · Ξ' h0, pow_zero at c'; have := h.hW; omega
    · omega
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, v₈⟩ := adjS_exec (P := P) e₇.wb_right d h₇.pk.one h₇.pk.zero h₇.rA
    (by rw [g170]; exact hq0A) hAW
  Ξ' g170, v₇ at v₈
  -- 9. the normalised pair
  have x299 : c₈.nreg 110299 = x := by
    rw [f₈.1 _ (⌖), f₇.1 _ (⌖), f₆.1 _ (⌖), R₅ _ (⌖) (⌖),
      f₄.1 _ (⌖), R₃ _ (⌖), R₂ _ (BL_keep (Or.inr (Or.inr (Or.inl rfl)))),
      R₁ _ (⌖) (⌖) (⌖), hx]
  have h1₈ : c₈.nreg 120011 = 1 := by rw [f₈.1 _ (⌖)]; exact h₇.pk.one
  set q := adjN d V.A q0 (if w2 = Y.edge ∧ nz C Y.edge hc2 = Y.hgt then 1 else 0) with hqdef
  have hqA : q < V.A := by
    rw [hqdef]; unfold adjN
    split_ifs <;> first | exact predP_lt hq0A | exact succP_lt hq0A | exact hq0A
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, n₉, s₉⟩ := normS_exec (P := P) e₈.wb_right h1₈
    (by rw [x299]; omega) (by rw [v₈]; omega)
  Ξ' x299, v₈ at n₉ s₉
  have ex : Exec P W (locS d) c c₉ _ :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉)))))))
  refine ⟨c₉, _, ex, ⋄, ?_, q, hqA, fun hne => ?_, n₉, s₉⟩
  · -- the frame
    have fr₁ : FrameB BLS c c₁ := exec_frameB e₁ (⌖)
    have fr₃ : FrameB BLS c₂ c₃ := exec_frameB e₃ (⌖)
    have fr₅ : FrameB BLS c₄ c₅ := exec_frameB e₅ (⌖)
    refine fr₁.trans ((FrameB.mono f₂ fun r hr => ⊚ BLS, hr).trans (fr₃.trans
      ((FrameB.mono f₄ fun r hr => ?_).trans (fr₅.trans ((FrameB.mono f₆ fun r hr => ?_).trans
      ((FrameB.mono f₇ fun r hr => ?_).trans ((FrameB.mono f₈ fun r hr => ?_).trans
      (FrameB.mono f₉ fun r hr => ?_))))))))
    all_goals
      ϴ' BPA, Bool.or_eq_true, decide_eq_true_eq at hr
      ϴ BLS, Bool.or_eq_true, decide_eq_true_eq
      omega
  · -- the semantics
    have hN := h.isNF
    have hP := h.simple
    have hkY : (chainModel C).key (Qof P) ⟨Y.edge, Y.hgt⟩ =
        mk C ((chainModel C).key (Qof P) (endPos N d x)) := by
      have := hYk; Ξ' hQ at this; exact this
    Ξ' hkY at loc1 loc2
    have hq0N := hq₂
    have hkeq : (chainModel C).key (Qof P) (endPos N d q0) =
        mk C ((chainModel C).key (Qof P) (endPos N d x)) ↔
        (w2 = Y.edge ∧ nz C Y.edge hc2 = Y.hgt) := by
      obtain ⟨hw72, hh2, hp02, hp12⟩ := h.arcEnd (j := sj N q0) (by rw [← hA]; exact hjl') d
      have hwe2 : (if d then (N.arc (sj N q0)).s else (N.arc (sj N q0)).e) = endPos N d q0 := by
        unfold endPos; rfl
      Ξ' hwe2 at hw72 hh2 hp02 hp12
      have := key_eq_iff C hD (w := Y.edge) (hc := Y.hgt) (w2 := w2) (hc2 := hc2) hY6 hY7 hYh
        hh2 ⟨hYp0, hYp1⟩ ⟨hp02, hp12⟩
      Ξ' hYnz at this
      Ξ ← hkY, ← this
      Ξ hQ
    have hl1 : ¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P))
        (mk C ((chainModel C).key (Qof P) (endPos N d x))) →
        sideInArc (sk (chainModel C) (Qof P) N q0) (ek (chainModel C) (Qof P) N q0)
          (mk C ((chainModel C).key (Qof P) (endPos N d x))) := fun hc' => by
      rcases loc1 hc' with h0 | h0
      · exact absurd h0 (Set.nonempty_iff_ne_empty.1 hne)
      · exact h0
    cases d
    · -- the end: the arc just after
      ϴ Bool.false_eq_true, ite_false
      have := after_of_loc hN hP hne hq0N hl1 loc2
      have hek : ek (chainModel C) (Qof P) N q0 = (chainModel C).key (Qof P) (endPos N false q0) := by
        rw [key_endPos]; rfl
      Ξ' hek at this
      convert this using 1
      rw [hqdef]; unfold adjN
      by_cases he : (chainModel C).key (Qof P) (endPos N false q0) =
          mk C ((chainModel C).key (Qof P) (endPos N false x))
      · rw [ite_eq_left he, ite_eq_left (hkeq.1 he)]; Θ hA
      · rw [ite_eq_right he, ite_eq_right (fun h' => he (hkeq.2 h'))]; simp
    · ϴ ite_true
      have := before_of_loc hN hP hne hq0N hl1 loc2
      have hsk : sk (chainModel C) (Qof P) N q0 = (chainModel C).key (Qof P) (endPos N true q0) := by
        rw [key_endPos]; rfl
      Ξ' hsk at this
      convert this using 1
      rw [hqdef]; unfold adjN
      by_cases he : (chainModel C).key (Qof P) (endPos N true q0) =
          mk C ((chainModel C).key (Qof P) (endPos N true x))
      · rw [ite_eq_left he, ite_eq_left (hkeq.1 he)]; Θ hA
      · rw [ite_eq_right he, ite_eq_right (fun h' => he (hkeq.2 h'))]; simp

end

end OracleR

end Chazelle.Core
