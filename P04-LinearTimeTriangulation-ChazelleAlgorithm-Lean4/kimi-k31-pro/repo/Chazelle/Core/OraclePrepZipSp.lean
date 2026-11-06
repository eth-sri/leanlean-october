module

public import Chazelle.Core.OraclePrepZip
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ConfigTactics

/-!
# Lemma 3.6 (WP-H), preprocessing part 12: the special zipper pairs

* `locZ`: double identification of the walk position in `50002`, `50003` (`locZ_exec`);
* `tstS d`: the flag of the key of an end of the located arc being that of a reference position
  (`110210`, `110211`), and the adjusted arc (`tstS_exec`);
* `kiS`: for the walk vertex `X` (`110220`), the located arc `j` (`110227`), the arc before
  (`110223`), the arc after (`110224`), and the sum of the two end flags (`110228`, zero iff `X`
  lies inside the arc `j`) (`kiS_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- Double identification of the position in `50002`, `50003`. -/
def locZ : Stmt := .seq (block [.copyN 50000 120040, .copyN 50001 120014]) myLoc

/-- The registers written by `locZ`. -/
def BLZ (r : ℕ) : Bool := BL r || decide (50000 ≤ r ∧ r ≤ 50003)

theorem locZ_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {pw ph : ℕ} (h2 : c.nreg 50002 = pw)
    (h3 : c.nreg 50003 = ph) (hpw : pw ≤ 2 * C.m + 6)
    (hp : ProperPos (chainModel C) (Qof P) P.n ⟨pw, ph⟩) :
    ∃ c' k, Exec P W locZ c c' k ∧ k ≤ 5500 * (V.L + 1) + 2 ∧ FrameB BLZ c c' ∧
      c'.nreg 120170 < V.A ∧
      (¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P)) ((chainModel C).key (Qof P) ⟨pw, ph⟩) →
        N.F (chainModel C) (Qof P) = ∅ ∨
          sideInArc (sk (chainModel C) (Qof P) N (c'.nreg 120170))
            (ek (chainModel C) (Qof P) N (c'.nreg 120170)) ((chainModel C).key (Qof P) ⟨pw, ph⟩)) ∧
      ((chainModel C).IsCut (N.F (chainModel C) (Qof P)) ((chainModel C).key (Qof P) ⟨pw, ph⟩) →
        sk (chainModel C) (Qof P) N (c'.nreg 120170) = (chainModel C).key (Qof P) ⟨pw, ph⟩ ∨
          ek (chainModel C) (Qof P) N (c'.nreg 120170) = (chainModel C).key (Qof P) ⟨pw, ph⟩) := by
  obtain ⟨hL, -, -⟩ := h.mem
  have hA := hL.A
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, mm₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50000 120040,
      .copyN 50001 120014]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg = upd (upd c.nreg 50000 V.MD) 50001 V.NB ∧ c₁.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, ?_, rfl⟩
    config_simp; rw [h.rMD, h.rNB]
  have R₁ : ∀ r, (r < 50000 ∨ 50001 < r) → c₁.nreg r = c.nreg r :=
    fun r a => by rw [n₁]; simp [upd]; split_ifs <;> first | omega
  have h₁ : ZEnv P W lo C N V c₁ := h.stable (fun r hr => R₁ r (by
      sio only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr))
    (fun a _ => by rw [mm₁])
  have hTB := hL.TB_le
  have hPW := h.hW
  have hnW  := walk_n C
  have g2 : c₁.nreg 50002 = pw := by rw [R₁ _ (by omega), h2]
  have g3 : c₁.nreg 50003 = ph := by rw [R₁ _ (by omega), h3]
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hq₂, loc1, loc2⟩ := myLoc_exec arcCover (P := P) (W := W) (c := c₁)
    e₁.wb_right ⟨h.good, by omega, by rw [n₁]; config_simp; have := hL.md_le; omega,
      by rw [n₁, mm₁]; config_simp; exact hL.chwf, chainModel C,
      by rw [n₁, mm₁]; config_simp; exact hL.md, by rwo [g2, hnW]⟩
    h.good (by omega) (by rw [n₁, mm₁]; config_simp; exact hL.md) hL.good
    (by rw [n₁, mm₁]; config_simp; exact hL.nf) h.isNF (by rwx [g2, g3]) hL.st
    h₁.rTB h₁.rL h₁.pk.zero h₁.pk.one
    (by rw [mm₁]; exact hL.tab) (by rw [← hA]; exact hL.A_lt)
    (by rw [n₁]; config_simp; exact hL.NB_le) (by rw [n₁, mm₁]; config_simp; rw [← hA]; exact hL.AB_le)
    (by rw [n₁, mm₁]; config_simp; rw [← hA]; exact hL.SB_le) hTB
  rw [g2, g3] at loc1 loc2
  have fr₁ : FrameB BLZ c c₁ := exec_frameB e₁ (by decide)
  exact ⟨c₂, _, .seq e₁ e₂, by omega, fr₁.trans (FrameB.mono f₂ fun r hr => by simp [BLZ, hr]),
    by rwx [hA], loc1, loc2⟩

/-- Test the end of the located arc against the reference position, adjust. -/
def tstS (d : Bool) : Stmt :=
  .seq arcPosS (.seq (block [.copyN 110212 110100, .copyN 110100 110210])
    (.seq posA (.seq eqS (adjS d))))

/-- The registers written by `tstS`. -/
def BTS (r : ℕ) : Bool :=
  decide (110100 ≤ r ∧ r ≤ 110108) || decide (110200 ≤ r ∧ r ≤ 110202) ||
    decide (110212 ≤ r ∧ r ≤ 110214)

open Classical in
theorem tstS_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) (d : Bool) {q0 : ℕ}
    (h03 : c.nreg 110203 = q0) (hq0A : q0 < V.A) (h170 : c.nreg 120170 = q0)
    (ho : c.nreg 110204 = if d then 1 else 3) {Yw Yz : ℕ} (h10 : c.nreg 110210 = Yw)
    (h11 : c.nreg 110211 = Yz) (hY6 : 6 ≤ Yw) (hY7 : Yw ≤ 2 * C.m + 6) (hYh : Yz ≤ C.P.n)
    (hYp : 0 ≤ (chainModel C).param C.P ⟨Yw, Yz⟩ ∧ (chainModel C).param C.P ⟨Yw, Yz⟩ < 1)
    (hYnz : nz C Yw Yz = Yz) :
    ∃ c' k, Exec P W (tstS d) c c' k ∧ k ≤ 100 ∧ FrameB BTS c c' ∧
      c'.nreg 110213 = (if (chainModel C).key (Qof P) (endPos N d q0) =
        (chainModel C).key (Qof P) ⟨Yw, Yz⟩ then 1 else 0) ∧
      c'.nreg 110214 = adjN d V.A q0 (c'.nreg 110213) := by
  obtain ⟨hL, -, -⟩ := h.mem
  have hA := hL.A
  have hQ := h.CQ
  have hD := h.hD
  obtain ⟨hsq', hjl', hwv', hhv'⟩ := h.endPos_mem hq0A d
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, v₄, v₄'⟩ := arcPosS_exec (P := P) hw (AB := V.AB)
    (SB := V.SB) (A := V.A) (p := q0) (o := if d then 1 else 3) h.rAB h.rSB h.pk.one
    h03 hq0A ho (by splao) (by rwx [hsq'])
    (by have := hL.SB_le; have := hL.TB_le; rwo [h.mem.2.2] at *)
    (by have := hL.AB_le; have := hL.TB_le; rwo [h.mem.2.1] at *)
  rw [hwv'] at v₄
  rw [hhv'] at v₄'
  set w2 := (endPos N d q0).edge
  set hc2 := (endPos N d q0).hgt
  have h₄ : ZEnv P W lo C N V c₄ := h.stable (fun r hr => f₄.1 r (by
    sis only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr; omega))
    (fun a _ => by rw [f₄.2.2.1])
  have y210 : c₄.nreg 110210 = Yw := by rw [f₄.1 _ (by decide), h10]
  have y211 : c₄.nreg 110211 = Yz := by rw [f₄.1 _ (by decide), h11]
  obtain ⟨c₅, k₅, e₅, hk₅, n₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 110212 110100,
      .copyN 110100 110210]) c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg = upd (upd c₄.nreg 110212 w2) 110100 Yw := by
    have w₄ := e₄.wb_right
    exec_block
    refine ⟨rfl, ?_⟩
    config_simp; rw [v₄, y210]
  have hm₅ : c₅.nmem = c₄.nmem :=
    (exec_frameB e₅ (B := fun r => decide (r = 110212 ∨ r = 110100)) (by decide)).2.2.1
  have R₅ : ∀ r, r ≠ 110212 → r ≠ 110100 → c₅.nreg r = c₄.nreg r := fun r a b => by
    rw [n₅, upd_other _ _ _ b, upd_other _ _ _ a]
  have h₅ : ZEnv P W lo C N V c₅ := h₄.stable (fun r hr => R₅ r (by
      sio only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr) (by
      sio only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr))
    (fun a _ => by rw [hm₅])
  have hm1 := C.one_le
  have hmn := h.m_lt
  have hS := C.sideS_lt C.sideBeta
  have hR := rT_lt C
  have hPW := h.hW
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, -, rest₆⟩ := posA_exec (P := P) e₅.wb_right h₅.pk hm1 hmn h.s_lt hS hR
    (by omega)
  have x100 : c₅.nreg 110100 = Yw := by rw [n₅]; config_simp
  have x101 : c₅.nreg 110101 = hc2 := by rw [R₅ _ (by decide) (by decide), v₄']
  rw [x100, x101] at rest₆
  obtain ⟨-, z₆, -⟩ := rest₆ hY7
  have z₆' : c₆.nreg 110103 = nz C Yw hc2 := by rw [z₆, ← nzN_eq, h.Qn]
  obtain ⟨c₇, k₇, e₇, hk₇, f₇, v₇⟩ := eqS_exec (P := P) e₆.wb_right (by omega)
  have x212 : c₆.nreg 110212 = w2 := by rw [f₆.1 _ (by decide), n₅]; config_simp
  have x210 : c₆.nreg 110210 = Yw := by
    rw [f₆.1 _ (by decide), R₅ _ (by decide) (by decide), y210]
  have x211 : c₆.nreg 110211 = Yz := by
    rw [f₆.1 _ (by decide), R₅ _ (by decide) (by decide), y211]
  rw [x212, x210, z₆', x211] at v₇
  have g170 : c₇.nreg 120170 = q0 := by
    rw [f₇.1 _ (by decide), f₆.1 _ (by decide), R₅ _ (by decide) (by decide),
      f₄.1 _ (by decide), h170]
  have h₇ : ZEnv P W lo C N V c₇ := h₅.stable (fun r hr => by
      rw [f₇.1 r (by sis only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr; omega),
        f₆.1 r (by simp [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr; sio [BPA])])
    (fun a _ => by rw [f₇.2.2.1, f₆.2.2.1])
  have hAW : V.A + 1 ≤ W := by
    have a := hL.SB_le; have b := hL.TB_le; have c' := hL.A_lt
    rcases Nat.eq_zero_or_pos V.L with h0 | h0
    · rwo [h0, pow_zero] at c'
    · omega
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, v₈⟩ := adjS_exec (P := P) e₇.wb_right d h₇.pk.one h₇.pk.zero h₇.rA
    (by rwx [g170]) hAW
  rw [g170] at v₈
  -- the key test
  have hkeq : (chainModel C).key (Qof P) (endPos N d q0) = (chainModel C).key (Qof P) ⟨Yw, Yz⟩ ↔
      (w2 = Yw ∧ nz C Yw hc2 = Yz) := by
    obtain ⟨hw72, hh2, hp02, hp12⟩ := h.arcEnd (j := sj N q0) (by rwx [← hA]) d
    have hwe2 : (if d then (N.arc (sj N q0)).s else (N.arc (sj N q0)).e) = endPos N d q0 := by
      ufr endPos
    rw [hwe2] at hw72 hh2 hp02 hp12
    have := key_eq_iff C hD (w := Yw) (hc := Yz) (w2 := w2) (hc2 := hc2) hY6 hY7 hYh
      hh2 hYp ⟨hp02, hp12⟩
    rw [hYnz] at this
    rw [← this, ← hQ]
  have e13 : c₈.nreg 110213 = c₇.nreg 110213 := f₈.1 _ (by decide)
  have ex : Exec P W (tstS d) c c₈ _ := .seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))
  refine ⟨c₈, _, ex, by omega, ?_, ?_, ?_⟩
  · have fr₅ : FrameB BTS c₄ c₅ := exec_frameB e₅ (by decide)
    refine (FrameB.mono f₄ fun r hr => ?_).trans (fr₅.trans ((FrameB.mono f₆ fun r hr => ?_).trans
      ((FrameB.mono f₇ fun r hr => ?_).trans (FrameB.mono f₈ fun r hr => ?_))))
    all_goals
      simp [BPA, decide_eq_true_eq] at hr
      simp [BTS, Bool.or_eq_true, decide_eq_true_eq]
      omega
  · rw [e13, v₇]
    by_cases he : (chainModel C).key (Qof P) (endPos N d q0) = (chainModel C).key (Qof P) ⟨Yw, Yz⟩
    · rw [ite_eq_left (hkeq.1 he), ite_eq_left he]
    · rw [ite_eq_right (fun h' => he (hkeq.2 h')), ite_eq_right he]
  · rw [v₈, e13]

theorem sideInArc_ne {s e x : ℝ} (h : sideInArc s e x) : x ≠ s ∧ x ≠ e := by
  unfold sideInArc at h
  split_ifs at h with hse
  · exact ⟨fun h' => by rw [h'] at h; linarith [h.1], fun h' => by rw [h'] at h; linarith [h.2]⟩
  · refine ⟨fun h' => ?_, fun h' => ?_⟩ <;> rw [h'] at h <;> rcases h with h | h <;> linarith

/-- **The analysis of a walk vertex `X`** (in `110220`). -/
def kiS : Stmt :=
  .seq (block [.copyN 50002 110220, .constN 50003 0, .copyN 110210 110220, .constN 110211 0])
    (.seq locZ (.seq (block [.copyN 110203 120170, .copyN 110204 120011])
      (.seq (tstS true) (.seq (block [.copyN 110223 110214, .copyN 110225 110213,
          .copyN 110204 110205])
        (.seq (tstS false) (block [.copyN 110224 110214, .addN 110228 110225 110213,
          .copyN 110227 120170]))))))

/-- The registers written by `kiS`. -/
def BKI (r : ℕ) : Bool := BLZ r || BTS r || decide (110203 ≤ r ∧ r ≤ 110204) ||
  decide (110210 ≤ r ∧ r ≤ 110211) || decide (110223 ≤ r ∧ r ≤ 110228)

theorem BKI_keep {r : ℕ} (h : ZKeep r = true ∨ (110229 ≤ r ∧ r ≤ 110299)) : BKI r = false := by
  simp [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at h
  simp [BKI, BLZ, BTS, BL, Bdir, Bloc, Bcmp, Bk]
  omega

open Classical in
theorem kiS_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {X : ℕ} (hX : c.nreg 110220 = X)
    (h6 : 6 ≤ X) (h7 : X ≤ 2 * C.m + 6) :
    ∃ c' k, Exec P W kiS c c' k ∧ k ≤ 5500 * (V.L + 1) + 250 ∧ FrameB BKI c c' ∧
      c'.nreg 110227 < V.A ∧ c'.nreg 110223 < V.A ∧ c'.nreg 110224 < V.A ∧
      c'.nreg 110228 ≤ 2 ∧ ((N.F (chainModel C) (Qof P)).Nonempty →
        Before C (Qof P) N (c'.nreg 110223) X ∧ After C (Qof P) N (c'.nreg 110224) X ∧
        (c'.nreg 110228 = 0 ↔ sideInArc (sk (chainModel C) (Qof P) N (c'.nreg 110227))
          (ek (chainModel C) (Qof P) N (c'.nreg 110227)) X) ∧
        ∀ q, q < V.A → sideInArc (sk (chainModel C) (Qof P) N q) (ek (chainModel C) (Qof P) N q) X →
          q = c'.nreg 110227) := by
  obtain ⟨hL, -, -⟩ := h.mem
  have hA := hL.A
  have hQ := h.CQ
  have hkX : (chainModel C).key (Qof P) ⟨X, 0⟩ = X := by rw [← hQ]; exact key_zero C X
  have hp0 : (chainModel C).param C.P ⟨X, 0⟩ = 0 := by simp [Model.param]
  -- 1. the copies
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, mm₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50002 110220,
      .constN 50003 0, .copyN 110210 110220, .constN 110211 0]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 50002 X) 50003 0) 110210 X) 110211 0 ∧
      c₁.nmem = c.nmem := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, ?_, rfl⟩
      config_simp; rw [hX]
  have fr₁ : FrameB BKI c c₁ := exec_frameB e₁ (by decide)
  have h₁ : ZEnv P W lo C N V c₁ := h.stable (fun r hr => fr₁.1 r (BKI_keep (Or.inl hr)))
    (fun a _ => by rw [mm₁])
  -- 2. the double identification
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hq₂, loc1, loc2⟩ := locZ_exec e₁.wb_right h₁ (pw := X) (ph := 0)
    (by rw [n₁]; config_simp) (by rw [n₁]; config_simp) h7
    ⟨by rw [← hQ, hp0], by rwn [← hQ, hp0], Nat.zero_le _⟩
  rw [hkX] at loc1 loc2
  obtain ⟨q0, hq0d⟩ : ∃ q0, c₂.nreg 120170 = q0 := ⟨_, rfl⟩
  rw [hq0d] at hq₂ loc1 loc2
  have h₂ : ZEnv P W lo C N V c₂ := h₁.stable (fun r hr => f₂.1 r (by
      have := BKI_keep (Or.inl hr); simp [BKI, Bool.or_eq_false_iff] at this; exact this.1.1.1.1))
    (fun a _ => by rw [f₂.2.2.1])
  -- 3. the copies
  obtain ⟨c₃, k₃, e₃, hk₃, n₃⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 110203 120170,
      .copyN 110204 120011]) c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg = upd (upd c₂.nreg 110203 q0) 110204 1 := by
    have w₂ := e₂.wb_right
    exec_block
    refine ⟨rfl, ?_⟩
    config_simp; rw [hq0d, h₂.pk.one]
  have fr₃ : FrameB BKI c₂ c₃ := exec_frameB e₃ (by decide)
  have h₃ : ZEnv P W lo C N V c₃ := h₂.stable (fun r hr => fr₃.1 r (BKI_keep (Or.inl hr)))
    (fun a _ => by rw [fr₃.2.2.1])
  have R₂₃ : ∀ r, r ≠ 110203 → r ≠ 110204 → c₃.nreg r = c₂.nreg r := fun r a b => by
    rw [n₃, upd_other _ _ _ b, upd_other _ _ _ a]
  have R₁₂  := f₂.1
  have g10 : c₃.nreg 110210 = X := by
    rw [R₂₃ _ (by decide) (by decide), R₁₂ _ (by simp [BLZ, BL, Bdir, Bloc, Bcmp, Bk]), n₁]
    config_simp
  have g11 : c₃.nreg 110211 = 0 := by
    rw [R₂₃ _ (by decide) (by decide), R₁₂ _ (by simp [BLZ, BL, Bdir, Bloc, Bcmp, Bk]), n₁]
    config_simp
  have hq0A  := hq₂
  have hnz0 : nz C X 0 = 0 := by ufs nz
  -- 4. the start
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, s₄, a₄⟩ := tstS_exec e₃.wb_right h₃ true (q0 := q0)
    (by rw [n₃]; config_simp) hq0A (by rw [R₂₃ _ (by decide) (by decide), hq0d])
    (by rw [n₃]; simp [upd]) g10 g11 h6 h7 (Nat.zero_le _) ⟨by rw [hp0], by rwn [hp0]⟩
    hnz0
  rw [hkX] at s₄
  have h₄ : ZEnv P W lo C N V c₄ := h₃.stable (fun r hr => f₄.1 r (by
      have := BKI_keep (Or.inl hr); simp [BKI, Bool.or_eq_false_iff] at this; exact this.1.1.1.2))
    (fun a _ => by rw [f₄.2.2.1])
  -- 5. the copies
  obtain ⟨c₅, k₅, e₅, hk₅, n₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 110223 110214,
      .copyN 110225 110213, .copyN 110204 110205]) c₄ c₅ k₅ ∧ k₅ = 3 ∧
      c₅.nreg = upd (upd (upd c₄.nreg 110223 (c₄.nreg 110214)) 110225 (c₄.nreg 110213)) 110204 3 := by
    have w₄ := e₄.wb_right
    exec_block
    refine ⟨rfl, ?_⟩
    config_simp; rw [h₄.r3]
  have fr₅ : FrameB BKI c₄ c₅ := exec_frameB e₅ (by decide)
  have h₅ : ZEnv P W lo C N V c₅ := h₄.stable (fun r hr => fr₅.1 r (BKI_keep (Or.inl hr)))
    (fun a _ => by rw [fr₅.2.2.1])
  have R₄₅ : ∀ r, r ≠ 110223 → r ≠ 110225 → r ≠ 110204 → c₅.nreg r = c₄.nreg r := fun r a b c' => by
    rw [n₅, upd_other _ _ _ c', upd_other _ _ _ b, upd_other _ _ _ a]
  -- 6. the end
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, s₆, a₆⟩ := tstS_exec e₅.wb_right h₅ false (q0 := q0)
    (by rw [R₄₅ _ (by decide) (by decide) (by decide), f₄.1 _ (by decide), n₃]; config_simp)
    hq0A (by rw [R₄₅ _ (by decide) (by decide) (by decide), f₄.1 _ (by decide),
      R₂₃ _ (by decide) (by decide), hq0d])
    (by rw [n₅]; simp [upd])
    (by rw [R₄₅ _ (by decide) (by decide) (by decide), f₄.1 _ (by decide), g10])
    (by rw [R₄₅ _ (by decide) (by decide) (by decide), f₄.1 _ (by decide), g11])
    h6 h7 (Nat.zero_le _) ⟨by rw [hp0], by rwn [hp0]⟩ hnz0
  rw [hkX] at s₆
  -- 7. the results
  obtain ⟨c₇, k₇, e₇, hk₇, n₇⟩ : ∃ c₇ k₇, Exec P W (block [.copyN 110224 110214,
      .addN 110228 110225 110213, .copyN 110227 120170]) c₆ c₇ k₇ ∧ k₇ = 3 ∧
      c₇.nreg = upd (upd (upd c₆.nreg 110224 (c₆.nreg 110214)) 110228
        (c₆.nreg 110225 + c₆.nreg 110213)) 110227 (c₆.nreg 120170) := by
    have w₆ := e₆.wb_right
    have b1 : c₆.nreg 110225 ≤ 1 := by
      rw [f₆.1 _ (by decide), n₅]; config_simp; rw [s₄]; splao
    have b2 : c₆.nreg 110213 ≤ 1 := by rw [s₆]; splao
    have hWW := h.hW
    exec_block
    · cso
    · exact ⟨rfl, rfl⟩
  have ex : Exec P W kiS c c₇ _ :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  have fr₇ : FrameB BKI c₆ c₇ := exec_frameB e₇ (by decide)
  have g170 : c₆.nreg 120170 = q0 := by
    rw [f₆.1 _ (by decide), R₄₅ _ (by decide) (by decide) (by decide), f₄.1 _ (by decide),
      R₂₃ _ (by decide) (by decide), hq0d]
  have v227 : c₇.nreg 110227 = q0 := by rw [n₇]; config_simp; exact g170
  have v223 : c₇.nreg 110223 = adjN true V.A q0 (c₄.nreg 110213) := by
    rw [n₇]; config_simp; rw [f₆.1 _ (by decide), n₅]; config_simp; exact a₄
  have v224 : c₇.nreg 110224 = adjN false V.A q0 (c₆.nreg 110213) := by
    rw [n₇]; config_simp; exact a₆
  have v228 : c₇.nreg 110228 = c₄.nreg 110213 + c₆.nreg 110213 := by
    rw [n₇]; config_simp; rw [f₆.1 _ (by decide), n₅]; config_simp
  have hadjlt : ∀ d e, adjN d V.A q0 e < V.A := fun d e => by
    unfold adjN; split_ifs
    · exact predP_lt hq0A
    · exact succP_lt hq0A
    · exact hq0A
  have v228b : c₇.nreg 110228 ≤ 2 := by
    rw [v228, s₄, s₆]; splao
  refine ⟨c₇, _, ex, by omega, ?_, by rwx [v227], by rw [v223]; exact hadjlt _ _,
    by rw [v224]; exact hadjlt _ _, v228b, fun hne => ?_⟩
  · refine fr₁.trans ((FrameB.mono f₂ fun r hr => by simp [BKI, hr]).trans (fr₃.trans
      ((FrameB.mono f₄ fun r hr => by simp [BKI, hr]).trans (fr₅.trans
      ((FrameB.mono f₆ fun r hr => by simp [BKI, hr]).trans fr₇)))))
  · have hN := h.isNF
    have hP := h.simple
    have hq0N : q0 < N.arcs.length := by rwx [← hA]
    have hl1 : ¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P)) (X : ℝ) →
        sideInArc (sk (chainModel C) (Qof P) N q0) (ek (chainModel C) (Qof P) N q0) X :=
      fun hc' => by
        rcases loc1 hc' with h0 | h0
        · exact absurd h0 (Set.nonempty_iff_ne_empty.1 hne)
        · exact h0
    have hsk : (chainModel C).key (Qof P) (endPos N true q0) = sk (chainModel C) (Qof P) N q0 := by
      rwr [key_endPos]
    have hek : (chainModel C).key (Qof P) (endPos N false q0) = ek (chainModel C) (Qof P) N q0 := by
      rwr [key_endPos]
    rw [hsk] at s₄
    rw [hek] at s₆
    refine ⟨?_, ?_, ?_, fun q hq hin => ?_⟩
    · rw [v223, s₄]
      convert before_of_loc hN hP hne hq0N hl1 loc2 using 1
      unfold adjN
      by_cases he : sk (chainModel C) (Qof P) N q0 = X
      · rw [ite_eq_left he, ite_eq_left he]; simp [hA]
      · rws [ite_eq_right he, ite_eq_right he]
    · rw [v224, s₆]
      convert after_of_loc hN hP hne hq0N hl1 loc2 using 1
      unfold adjN
      by_cases he : ek (chainModel C) (Qof P) N q0 = X
      · rw [ite_eq_left he, ite_eq_left he]; simp [hA]
      · rws [ite_eq_right he, ite_eq_right he]
    · rw [v228, v227, s₄, s₆]
      constructor
      · intro h0
        have a : ¬ sk (chainModel C) (Qof P) N q0 = X := fun he => by rwo [ite_eq_left he] at h0
        have b : ¬ ek (chainModel C) (Qof P) N q0 = X := fun he => by rwo [ite_eq_left he] at h0
        by_cases hc' : (chainModel C).IsCut (N.F (chainModel C) (Qof P)) (X : ℝ)
        · rcases loc2 hc' with e | e
          · exact absurd e a
          · exact absurd e b
        · exact hl1 hc'
      · intro hin
        obtain ⟨a, b⟩ := sideInArc_ne hin
        rw [ite_eq_right (fun e => a e.symm), ite_eq_right (fun e => b e.symm)]
    · have hqN : q < N.arcs.length := by rwx [← hA]
      have hnc := not_cut_of_int hN hne hqN hin
      rw [v227]
      exact interior_unique hN (Or.inl ⟨C, hP, rfl⟩) hne hqN hq0N hin (hl1 hnc)

end

end OracleR

end Chazelle.Core
