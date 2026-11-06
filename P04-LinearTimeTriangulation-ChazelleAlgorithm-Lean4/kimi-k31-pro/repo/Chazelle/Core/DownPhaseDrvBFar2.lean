module

public import Chazelle.Core.DownPhaseDrvBFar1
public import Chazelle.Core.DownPhaseDrvRLib
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 4000000

/-!
# Down-phase base (D9), RAM: the far-end scan

The far end of the vertex chord of `i = r212070` in direction code `d = r212086` is found by a
scan over walk-edge ranges `t < r212034`: range `t` holds the walk edges `(st + u) mod n`,
`u < cnt`, with `(st, cnt)` loaded by `ldRange` (`K = r212012`):

* `K = 0`: the whole walk, `st = 0`, `cnt = n`;
* `K > 0`: arc `j = mem[lp + t]` of the region (`lp = r212033`, arc records at `AB = r216014`):
  `st = s.edge`, `cnt = (e.edge + n - s.edge) mod n + 1`.

`BestOK`: the running σ-nearest candidate over the visited walk edges (`bestOK_step`).
`farS_exec`: after the scan, `BestOK` over all ranges.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey
open DrvR (qE)

@[expose] public section

/-! ## The running minimum -/

/-- **The running σ-nearest candidate** over the walk edges `ES` (of a walk of `n` edges): flag
`f`, best walk edge `bw` and its edge `bq` of `Q`. -/
def BestOK (Q : Polygon) (n i : ℕ) (σ : ℝ) (li : Bool) (ES : ℕ → Prop) (f bw bq : ℕ) : Prop :=
  f ≤ 1 ∧
  (f = 1 → bw < n ∧ ES bw ∧ bq = qE li n bw ∧ Cand Q i σ bq ∧
    ∀ w, ES w → w < n → Cand Q i σ (qE li n w) →
      σ * edgeXAt Q bq i ≤ σ * edgeXAt Q (qE li n w) i) ∧
  (f = 0 → ∀ w, ES w → w < n → ¬ Cand Q i σ (qE li n w))

theorem BestOK.congr {Q : Polygon} {n i : ℕ} {σ : ℝ} {li : Bool} {ES ES' : ℕ → Prop}
    (h : ∀ w, ES w ↔ ES' w) {f bw bq : ℕ} (hb : BestOK Q n i σ li ES f bw bq) :
    BestOK Q n i σ li ES' f bw bq := by
  obtain ⟨h1, h2, h3⟩ := hb
  refine ⟨h1, fun hf => ?_, fun hf w hw => h3 hf w ((h w).2 hw)⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := h2 hf
  exact ⟨a1, (h bw).1 a2, a3, a4, fun w hw => a5 w ((h w).2 hw)⟩

/-- **One visited walk edge** `w'`: a candidate replaces the best if there is none or if it is
strictly nearer. -/
theorem bestOK_step {Q : Polygon} {n i : ℕ} {σ : ℝ} {li : Bool} {ES : ℕ → Prop} {f bw bq : ℕ}
    (hb : BestOK Q n i σ li ES f bw bq) {w' : ℕ} (hw' : w' < n) {f' bw' bq' : ℕ}
    (hup : Cand Q i σ (qE li n w') ∧ (f = 0 ∨
        σ * edgeXAt Q (qE li n w') i < σ * edgeXAt Q bq i) →
      bw' = w' ∧ bq' = qE li n w' ∧ f' = 1)
    (hkeep : ¬ (Cand Q i σ (qE li n w') ∧ (f = 0 ∨
        σ * edgeXAt Q (qE li n w') i < σ * edgeXAt Q bq i)) →
      bw' = bw ∧ bq' = bq ∧ f' = f) :
    BestOK Q n i σ li (fun w => ES w ∨ w = w') f' bw' bq' := by
  obtain ⟨h1, h2, h3⟩ := hb
  by_cases hu : Cand Q i σ (qE li n w') ∧ (f = 0 ∨
      σ * edgeXAt Q (qE li n w') i < σ * edgeXAt Q bq i)
  · obtain ⟨e1, e2, e3⟩ := hup hu
    subst e1 e2 e3
    refine ⟨le_rfl, fun _ => ⟨hw', Or.inr rfl, rfl, hu.1, fun w hw hwn hc => ?_⟩,
      fun h => absurd h (by omega)⟩
    rcases hw with hw | rfl
    · rcases hu.2 with h0 | hlt
      · exact absurd hc (h3 h0 w hw hwn)
      · have hf1 : f = 1 := by
          rcases (by omega : f = 0 ∨ f = 1) with h0 | h0
          · exact absurd hc (h3 h0 w hw hwn)
          · exact h0
        have := (h2 hf1).2.2.2.2 w hw hwn hc
        linarith
    · exact le_rfl
  · obtain ⟨e1, e2, e3⟩ := hkeep hu
    subst e1 e2 e3
    refine ⟨h1, fun hf => ?_, fun hf w hw hwn hc => ?_⟩
    · obtain ⟨a1, a2, a3, a4, a5⟩ := h2 hf
      refine ⟨a1, Or.inl a2, a3, a4, fun w hw hwn hc => ?_⟩
      rcases hw with hw | rfl
      · exact a5 w hw hwn hc
      · by_contra hlt
        push Not at hlt
        exact hu ⟨hc, Or.inr hlt⟩
    · rcases hw with hw | rfl
      · exact h3 hf w hw hwn hc
      · exact hu ⟨hc, Or.inl hf⟩

/-- The walk edges of the ranges before `t` and the first `u` walk edges of range `t`. -/
def ESr (n : ℕ) (stF cntF : ℕ → ℕ) (t u w : ℕ) : Prop :=
  (∃ t', t' < t ∧ ∃ u', u' < cntF t' ∧ w = (stF t' + u') % n) ∨
    (∃ u', u' < u ∧ w = (stF t + u') % n)

theorem ESr_succ (n : ℕ) (stF cntF : ℕ → ℕ) (t u w : ℕ) :
    ESr n stF cntF t (u + 1) w ↔ ESr n stF cntF t u w ∨ w = (stF t + u) % n := by
  unfold ESr
  constructor
  · rintro (h | ⟨u', hu', rfl⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hu' with h | rfl
      · exact Or.inl (Or.inr ⟨u', h, rfl⟩)
      · exact Or.inr rfl
  · rintro ((h | ⟨u', hu', rfl⟩) | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨u', by omega, rfl⟩
    · exact Or.inr ⟨u, by omega, rfl⟩

theorem ESr_next (n : ℕ) (stF cntF : ℕ → ℕ) (t w : ℕ) :
    ESr n stF cntF t (cntF t) w ↔ ESr n stF cntF (t + 1) 0 w := by
  unfold ESr
  constructor
  · rintro (⟨t', ht', h⟩ | h)
    · exact Or.inl ⟨t', by omega, h⟩
    · exact Or.inl ⟨t, by omega, h⟩
  · rintro (⟨t', ht', h⟩ | ⟨u', hu', -⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h' | rfl
      · exact Or.inl ⟨t', h', h⟩
      · exact Or.inr h
    · omega

theorem ESr_zero (n : ℕ) (stF cntF : ℕ → ℕ) (w : ℕ) : ¬ ESr n stF cntF 0 0 w := by
  unfold ESr; rintro (⟨t', ht', -⟩ | ⟨u', hu', -⟩) <;> omega

/-! ## The program -/

/-- Range loader, `K = 0`: the whole walk. -/
def ldAll : Stmt := block [.constN 212093 0, .copyN 212092 212010]

/-- Range loader, `K > 0`: arc `j = mem[lp + t]`, `st = s.edge`, `cnt = arcCnt`. -/
def ldArcR : Stmt :=
  .seq (block [.addN 212037 212033 212036, .loadN 212037 212037,
    .addN 212038 212037 212037, .addN 212038 212038 212038, .addN 212038 212038 212037,
    .addN 212038 212038 216014, .addN 212038 212038 212000, .loadN 212093 212038,
    .addN 212038 212038 212002, .loadN 212092 212038, .addN 212092 212092 212010,
    .subN 212092 212092 212093])
  (.seq (.ifLtN 212092 212010 .skip (.instr (.subN 212092 212092 212010)))
    (.instr (.addN 212092 212092 212000)))

/-- The range loader. -/
def ldRange : Stmt := .ifLtN 212001 212012 ldArcR ldAll

/-- One range of the scan. -/
def rangeB : Stmt :=
  .seq ldRange (.seq (.instr (.constN 212091 0)) (.seq (.whileLtN 212091 212092 visitS)
    (.instr (.addN 212036 212036 212000))))

/-- **The far-end scan.** -/
def farS : Stmt :=
  .seq (block [.constN 212099 0, .constN 212036 0]) (.whileLtN 212036 212034 rangeB)

/-- The registers the scan writes. -/
def Bfar (r : ℕ) : Bool := Bk r || decide (212036 ≤ r ∧ r ≤ 212038) || decide (212091 ≤ r ∧ r ≤ 212112)

theorem bfar_vis (r : ℕ) (h : Bvis r = true) : Bfar r = true := by
  unfold Bvis at h; unfold Bfar
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

theorem bfar_of {r : ℕ} (h : (212036 ≤ r ∧ r ≤ 212038) ∨ (212091 ≤ r ∧ r ≤ 212112)) :
    Bfar r = true := by
  unfold Bfar; simp only [Bool.or_eq_true, decide_eq_true_eq]; tauto

theorem wr_ldRange : wr (fun r => decide (r = 212037) || decide (r = 212038) ||
    decide (r = 212092) || decide (r = 212093)) ldRange = true := by decide

/-- The data of range `t`: the whole walk (`K = 0`) or arc `mem[lp + t]` of the region. -/
def LdOK (c : Config) (n t st cnt : ℕ) : Prop :=
  (c.nreg 212012 = 0 ∧ st = 0 ∧ cnt = n) ∨
  (0 < c.nreg 212012 ∧ st = c.nmem (c.nreg 216014 + 5 * c.nmem (c.nreg 212033 + t) + 1) ∧
    st < n ∧ c.nmem (c.nreg 216014 + 5 * c.nmem (c.nreg 212033 + t) + 3) < n ∧
    cnt = (c.nmem (c.nreg 216014 + 5 * c.nmem (c.nreg 212033 + t) + 3) + n - st) % n + 1)

theorem LdOK.st_lt {c : Config} {n t st cnt : ℕ} (h : LdOK c n t st cnt) (hn : 0 < n) : st < n := by
  rcases h with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ <;> omega

theorem LdOK.cnt_le {c : Config} {n t st cnt : ℕ} (h : LdOK c n t st cnt) (hn : 0 < n) :
    cnt ≤ n := by
  rcases h with ⟨-, -, h⟩ | ⟨-, -, -, -, h⟩
  · omega
  · rw [h]; have := Nat.mod_lt (c.nmem (c.nreg 216014 + 5 * c.nmem (c.nreg 212033 + t) + 3) + n - st) hn
    omega

section exec

variable {P : Polygon} {W : ℕ}

/-- **The range loader.** -/
theorem ldRange_exec (c : Config) (hw : WordsBounded W c) {n t st cnt : ℕ}
    (hn : c.nreg 212010 = n) (hn0 : 0 < n) (ht : c.nreg 212036 = t) (hld : LdOK c n t st cnt)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2)
    (hW : 2 * n + 1 ≤ W)
    (hAB : 0 < c.nreg 212012 → c.nreg 216014 + 5 * c.nmem (c.nreg 212033 + t) + 3 ≤ W)
    (hlp : 0 < c.nreg 212012 → c.nreg 212033 + t ≤ W) :
    ∃ c' k, Exec P W ldRange c c' k ∧ k ≤ 18 ∧ c'.nreg 212093 = st ∧ c'.nreg 212092 = cnt ∧
      FrameB (fun r => decide (r = 212037) || decide (r = 212038) || decide (r = 212092) ||
        decide (r = 212093)) c c' := by
  rcases hld with ⟨hK, hs, hc⟩ | ⟨hK, hs, hsn, hen, hc⟩
  · obtain ⟨c', k, ex, hk, v1, v2⟩ : ∃ c' k, Exec P W ldAll c c' k ∧ k = 2 ∧
        c'.nreg 212093 = st ∧ c'.nreg 212092 = cnt := by
      unfold ldAll
      exec_block
      · omega
      · refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> simp only [hn, hs, hc]
    have ex' : Exec P W ldRange c c' _ := .ifLtN_false (by rwo [c1, hK]) ex
    exact ⟨c', _, ex', by omega, v1, v2, exec_frameB ex' wr_ldRange⟩
  · have hAB := hAB hK
    have hlp := hlp hK
    set j := c.nmem (c.nreg 212033 + t) with hj
    set e := c.nmem (c.nreg 216014 + 5 * j + 3) with he
    obtain ⟨c₁, k₁, e₁, hk₁, v1, v2, v38⟩ : ∃ c₁ k₁, Exec P W (block [.addN 212037 212033 212036,
        .loadN 212037 212037, .addN 212038 212037 212037, .addN 212038 212038 212038,
        .addN 212038 212038 212037, .addN 212038 212038 216014, .addN 212038 212038 212000,
        .loadN 212093 212038, .addN 212038 212038 212002, .loadN 212092 212038,
        .addN 212092 212092 212010, .subN 212092 212092 212093]) c c₁ k₁ ∧ k₁ = 12 ∧
        c₁.nreg 212093 = st ∧ c₁.nreg 212092 = e + n - st ∧ c₁.nreg 212010 = n := by
      have hj5 : 5 * j ≤ W := by omega
      have hA1 : c.nmem (j + j + (j + j) + j + c.nreg 216014 + 1) = st := by
        rw [hs]; congr 1; omega
      have hA3 : c.nmem (j + j + (j + j) + j + c.nreg 216014 + 1 + 2) = e := by
        rw [he]; congr 1; omega
      exec_block
      all_goals try (config_simp; (try simp only [hn, ht, c0, c2]); omega)
      all_goals (config_simp; simp only [hn, ht, c0, c2, ← hj])
      · rwo [hA3]
      · exact ⟨hA1, by rw [hA1, hA3], trivial⟩
    have w₁ := e₁.wb_right
    have f₁ : FrameB (fun r => decide (r = 212037) || decide (r = 212038) ||
        decide (r = 212092) || decide (r = 212093)) c c₁ := exec_frameB e₁ (by decide)
    have c0' : c₁.nreg 212000 = 1 := by rw [f₁.1 _ (by decide), c0]
    by_cases hlt : e + n - st < n
    · have e₂ := Exec.addN (P := P) w₁ 212092 212092 212000 (by rwo [v2, c0'])
      have ex : Exec P W ldArcR c _ (k₁ + ((0 + 1) + 1)) :=
        .seq e₁ (.seq (.ifLtN_true (by rwx [v2, v38]) (.skip w₁)) e₂)
      have ex' : Exec P W ldRange c _ _ := .ifLtN_true (by rwx [c1]) ex
      refine ⟨_, _, ex', by omega, ?_, ?_, exec_frameB ex' wr_ldRange⟩
      · dsimp only; rw [Machine.upd_other _ _ _ (by norm_num), v1]
      · simp only [Machine.upd_same]; rw [v2, c0', hc, Nat.mod_eq_of_lt hlt]
    · have e₂ := Exec.subN (P := P) w₁ 212092 212092 212010
      have w₂ := e₂.wb_right
      have e₃ := Exec.addN (P := P) w₂ 212092 212092 212000 (by
        simp only [Machine.upd_same]
        rwo [Machine.upd_other _ _ _ (by norm_num), v2, v38, c0'])
      have ex : Exec P W ldArcR c _ (k₁ + ((1 + 2) + 1)) :=
        .seq e₁ (.seq (.ifLtN_false (by rwx [v2, v38]) e₂) e₃)
      have ex' : Exec P W ldRange c _ _ := .ifLtN_true (by rwx [c1]) ex
      refine ⟨_, _, ex', by omega, ?_, ?_, exec_frameB ex' wr_ldRange⟩
      · dsimp only
        rw [Machine.upd_other _ _ _ (by norm_num), Machine.upd_other _ _ _ (by norm_num), v1]
      · simp only [Machine.upd_same]
        rw [Machine.upd_other _ _ _ (by norm_num), v2, v38, c0', hc,
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]


/-- **The walk edges of one range.** -/
theorem visLoop_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hW2 : 2 * P.n + 2 ≤ W) (c : Config)
    (hw : WordsBounded W c) {stF cntF : ℕ → ℕ} {t i d : ℕ} {li : Bool}
    (hn : c.nreg 212010 = P.n) (hst : c.nreg 212093 = stF t) (hcnt : c.nreg 212092 = cntF t)
    (hu : c.nreg 212091 = 0) (hsn : stF t < P.n) (hcn : cntF t ≤ P.n)
    (hli : c.nreg 212011 = if li then 1 else 0) (hi : c.nreg 212070 = i) (hin : i < P.n)
    (hd : c.nreg 212086 = d) (hd1 : d ≤ 1)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2)
    (hb : BestOK (Qof P) P.n i (sgnD d) li (ESr P.n stF cntF t 0)
      (c.nreg 212099) (c.nreg 212097) (c.nreg 212098)) :
    ∃ c' k, Exec P W (.whileLtN 212091 212092 visitS) c c' k ∧ k ≤ (visK + 2) * cntF t + 2 ∧
      FrameB Bvis c c' ∧
      BestOK (Qof P) P.n i (sgnD d) li (ESr P.n stF cntF (t + 1) 0)
        (c'.nreg 212099) (c'.nreg 212097) (c'.nreg 212098) := by
  let Inv : ℕ → Config → Prop := fun u e => WordsBounded W e ∧ e.nreg 212091 = u ∧
    e.nreg 212092 = cntF t ∧ FrameB Bvis c e ∧
    BestOK (Qof P) P.n i (sgnD d) li (ESr P.n stF cntF t u)
      (e.nreg 212099) (e.nreg 212097) (e.nreg 212098)
  have I0 : Inv 0 c := ⟨hw, hu, hcnt, FrameB.refl _ _, hb⟩
  obtain ⟨c', k, ex, ⟨-, -, -, hf, hb'⟩, hk⟩ := DrvR.forLoop (P := P) (W := W) (ir := 212091)
    (nr := 212092) Inv visK (cntF t) (fun j e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun u e hu ⟨hw, h1, h2, hf, hbe⟩ => by
      have g  := hf.1
      obtain ⟨hb1, hb2, hb3⟩ := id hbe
      obtain ⟨e', k, ex, hk, hf', v91, u1, u2⟩ := visitS_exec (P := P) hG hW hW2 e hw
        (st := stF t) (u := u) (i := i) (d := d) (li := li)
        (by rw [g _ (by decide), hn]) (by rw [g _ (by decide), hst]) h1 hsn (by omega)
        (by rw [g _ (by decide), hli]) (by rw [g _ (by decide), hi]) hin
        (by rw [g _ (by decide), hd]) hd1 (by rw [g _ (by decide), c0])
        (by rw [g _ (by decide), c1]) (by rw [g _ (by decide), c2]) hb1
        (fun h => by obtain ⟨a1, -, a3, -⟩ := hb2 h; rw [a3]; exact DownMath.qE_lt li a1)
      refine ⟨e', k, ex, ⟨ex.wb_right, v91, by rw [hf'.1 _ (by decide), h2], hf.trans hf', ?_⟩,
        hk⟩
      refine (bestOK_step hbe (w' := (stF t + u) % P.n) (Nat.mod_lt _ (by omega))
        (fun h => ?_) (fun h => ?_)).congr (fun w => (ESr_succ P.n stF cntF t u w).symm)
      · obtain ⟨a1, a2, a3⟩ := u1 h; exact ⟨a1, a2, a3⟩
      · obtain ⟨a1, a2, a3⟩ := u2 h; exact ⟨a1, a2, a3⟩)
    I0 (Nat.zero_le _)
  exact ⟨c', k, ex, by omega, hf, hb'.congr (ESr_next P.n stF cntF t)⟩


theorem LdOK.congr {c e : Config} {n t st cnt : ℕ} (h : LdOK c n t st cnt)
    (h12 : e.nreg 212012 = c.nreg 212012) (h14 : e.nreg 216014 = c.nreg 216014)
    (h33 : e.nreg 212033 = c.nreg 212033) (hm : e.nmem = c.nmem) : LdOK e n t st cnt := by
  unfold LdOK; rwx [h12, h14, h33, hm]

/-- **The far-end scan**: the σ-nearest candidate over the walk edges of all ranges. -/
theorem farS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hW2 : 2 * P.n + 2 ≤ W) (c : Config)
    (hw : WordsBounded W c) {stF cntF : ℕ → ℕ} {nR i d Cm : ℕ} {li : Bool}
    (hn : c.nreg 212010 = P.n) (hnR : c.nreg 212034 = nR)
    (hld : ∀ t, t < nR → LdOK c P.n t (stF t) (cntF t)) (hCm : ∀ t, t < nR → cntF t ≤ Cm)
    (hAB : ∀ t, t < nR → 0 < c.nreg 212012 →
      c.nreg 216014 + 5 * c.nmem (c.nreg 212033 + t) + 3 ≤ W)
    (hlp : 0 < c.nreg 212012 → c.nreg 212033 + nR ≤ W)
    (hli : c.nreg 212011 = if li then 1 else 0) (hi : c.nreg 212070 = i) (hin : i < P.n)
    (hd : c.nreg 212086 = d) (hd1 : d ≤ 1)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2) :
    ∃ c' k, Exec P W farS c c' k ∧ k ≤ ((visK + 2) * Cm + 24) * nR + 4 ∧ FrameB Bfar c c' ∧
      BestOK (Qof P) P.n i (sgnD d) li (ESr P.n stF cntF nR 0)
        (c'.nreg 212099) (c'.nreg 212097) (c'.nreg 212098) := by
  have hn0 : 0 < P.n := by have := hG.1.1; omega
  -- the initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, v99, v36⟩ : ∃ c₁ k₁, Exec P W (block [.constN 212099 0,
      .constN 212036 0]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 212099 = 0 ∧ c₁.nreg 212036 = 0 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_⟩ <;> config_simp
  have f₁ : FrameB Bfar c c₁ := exec_frameB e₁ (by decide)
  have g₁  := f₁.1
  let Inv : ℕ → Config → Prop := fun t e => WordsBounded W e ∧ e.nreg 212036 = t ∧
    e.nreg 212034 = nR ∧ FrameB Bfar c e ∧
    BestOK (Qof P) P.n i (sgnD d) li (ESr P.n stF cntF t 0)
      (e.nreg 212099) (e.nreg 212097) (e.nreg 212098)
  have I0 : Inv 0 c₁ := ⟨e₁.wb_right, v36, by rw [g₁ _ (by decide), hnR], f₁,
    ⟨by rwo [v99], fun h => absurd h (by rwo [v99]),
      fun _ w hw => absurd hw (ESr_zero P.n stF cntF w)⟩⟩
  obtain ⟨c', k, ex, ⟨-, -, -, hf, hb'⟩, hk⟩ := DrvR.forLoop (P := P) (W := W) (ir := 212036)
    (nr := 212034) (body := rangeB) Inv ((visK + 2) * Cm + 22) nR (fun j e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun t e ht ⟨hw, h1, h2, hf, hbe⟩ => by
      have g  := hf.1
      have hld' := (hld t ht).congr (g _ (by decide)) (g _ (by decide)) (g _ (by decide))
        hf.2.2.1
      have hsn := (hld t ht).st_lt hn0
      have hcn := (hld t ht).cnt_le hn0
      -- the range
      obtain ⟨e₁, k₁, x₁, hk₁, s₁, s₂, f₁⟩ := ldRange_exec (P := P) e hw
        (by rw [g _ (by decide), hn]) hn0 h1 hld' (by rw [g _ (by decide), c0])
        (by rw [g _ (by decide), c1]) (by rw [g _ (by decide), c2]) (by omega)
        (fun hK => by
          rw [g _ (by decide), g _ (by decide), hf.2.2.1]
          exact hAB t ht (by rwa [g _ (by decide)] at hK))
        (fun hK => by
          rw [g _ (by decide)]
          have := hlp (by rwa [g _ (by decide)] at hK); omega)
      have g₁ : ∀ r, r ≠ 212037 → r ≠ 212038 → r ≠ 212092 → r ≠ 212093 →
          e₁.nreg r = e.nreg r := fun r a b c d => f₁.1 r (by
            sio only [Bool.or_eq_false_iff, decide_eq_false_iff_not])
      -- the counter
      have x₂ := Exec.constN (P := P) x₁.wb_right 212091 0 (Nat.zero_le _)
      set e₂ : Config := { e₁ with nreg := upd e₁.nreg 212091 0 } with he₂
      have g₂ : ∀ r, r ≠ 212091 → e₂.nreg r = e₁.nreg r := fun r h => by
        rw [he₂]; simp [h]
      have G : ∀ r, Bfar r = false → e₂.nreg r = c.nreg r := fun r h => by
        have h' := h
        simp only [Bfar, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h'
        rw [g₂ r (by omega), g₁ r (by omega) (by omega) (by omega) (by omega), g r h]
      -- the walk edges
      obtain ⟨e₃, k₃, x₃, hk₃, f₃, hb₃⟩ := visLoop_exec (P := P) hG hW hW2 e₂ x₂.wb_right
        (stF := stF) (cntF := cntF) (t := t) (i := i) (d := d) (li := li)
        (by rw [G _ (by decide), hn]) (by rw [g₂ _ (by decide), s₁])
        (by rw [g₂ _ (by decide), s₂]) (by rws [he₂]) hsn hcn
        (by rw [G _ (by decide), hli]) (by rw [G _ (by decide), hi]) hin
        (by rw [G _ (by decide), hd]) hd1 (by rw [G _ (by decide), c0])
        (by rw [G _ (by decide), c1]) (by rw [G _ (by decide), c2])
        (by rw [g₂ _ (by decide), g₂ _ (by decide), g₂ _ (by decide),
          g₁ _ (by decide) (by decide) (by decide) (by decide),
          g₁ _ (by decide) (by decide) (by decide) (by decide),
          g₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hbe)
      -- the range counter
      have v36 : e₃.nreg 212036 = t := by
        rw [f₃.1 _ (by decide), g₂ _ (by decide),
          g₁ _ (by decide) (by decide) (by decide) (by decide), h1]
      have v00 : e₃.nreg 212000 = 1 := by rw [f₃.1 _ (by decide), G _ (by decide), c0]
      have hnRW : nR ≤ W := by have := hw.1 212034; rw [h2] at this; exact this
      have x₄ := Exec.addN (P := P) x₃.wb_right 212036 212036 212000 (by rwo [v36, v00])
      have f₄ : FrameB (fun r => decide (r = 212036)) e₃ _ := exec_frameB x₄ (by decide)
      have ex : Exec P W rangeB e _ (k₁ + (1 + (k₃ + 1))) := .seq x₁ (.seq x₂ (.seq x₃ x₄))
      have hk₃' : k₃ ≤ (visK + 2) * Cm + 2 := by
        have := Nat.mul_le_mul_left (visK + 2) (hCm t ht); omega
      refine ⟨_, _, ex, ⟨x₄.wb_right, ?_, ?_, ?_, ?_⟩, by omega⟩
      · simp only [Machine.upd_same, v36, v00]
      · rw [f₄.1 _ (by decide), f₃.1 _ (by decide), G _ (by decide), hnR]
      · refine hf.trans ((fbMono f₁ fun r h => ?_).trans ((fbMono (exec_frameB x₂ (by decide :
          wr (fun r => decide (r = 212091)) (.instr (.constN 212091 0)) = true)) fun r h => ?_).trans
          ((fbMono f₃ bfar_vis).trans (fbMono f₄ fun r h => ?_))))
        · simp only [Bool.or_eq_true, decide_eq_true_eq] at h; exact bfar_of (by omega)
        · simp only [decide_eq_true_eq] at h; exact bfar_of (by omega)
        · simp only [decide_eq_true_eq] at h; exact bfar_of (by omega)
      · have e99 : ∀ r, r ≠ 212036 → (upd e₃.nreg 212036 (e₃.nreg 212036 + e₃.nreg 212000)) r =
            e₃.nreg r := fun r h => Machine.upd_other _ _ _ h
        dsimp only
        rw [e99 _ (by norm_num), e99 _ (by norm_num), e99 _ (by norm_num)]
        exact hb₃)
    I0 (Nat.zero_le _)
  have e : ((visK + 2) * Cm + 22 + 2) * (nR - 0) = ((visK + 2) * Cm + 24) * nR := by
    rw [Nat.sub_zero]
  refine ⟨c', _, .seq e₁ ex, by omega, hf, hb'⟩

end exec

end

end DrvB

end Chazelle.Core
