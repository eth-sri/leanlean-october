module

public import Chazelle.Core.GranRamRm

/-!
# WP-F, RAM part 7: the removal, second half

* `wbStmt`: the gathered exit list is written to the exit slots of `X` and pushed on the
  worklist (`wbStmt_exec`);
* `tailStmt`: the degree and weight of `X`, the death of `c`, `top` and `nlive`
  (`tailStmt_exec`);
* `ringStmt`: the dying positions of `c` are unlinked from the ring and the counts drop
  (`ringStmt_exec`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## Writing back -/

/-- The state with the first `t` entries of `L` written to the exit slots of `X` and to the
worklist from `top1` on. -/
def St.wb (st : St) (X top1 : ℕ) (L : List ℕ) (t : ℕ) : St :=
  { st with
    ex := fun x u => if x = X ∧ u < t then L.getD u 0 else st.ex x u
    stk := fun u => if top1 ≤ u ∧ u < top1 + t then L.getD (u - top1) 0 else st.stk u }

/-- One step: `v := tmp[t]`; `ex X t := v`; `stk (top1 + t) := v`; `t := t + 1`. -/
def wbBody : Stmt := block [.addN 90105 90044 90101, .loadN 90102 90105, .addN 90105 90103 90101,
  .storeN 90105 90102, .addN 90105 90043 90108, .addN 90105 90105 90101, .storeN 90105 90102,
  .addN 90101 90101 90019]

/-- The write-back loop (`r108 := top - 1`). -/
def wbStmt : Stmt :=
  .seq (block [.constN 90101 0, .subN 90108 90050 90019]) (.whileLtN 90101 90100 wbBody)

theorem wrS_wb : wrS Brm wbStmt = true := by decide

/-- The facts the write-back loop keeps. -/
structure WbI (W : ℕ) (d : Dm) (S : St) (X top1 : ℕ) (L : List ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  t_le : c.nreg 90101 ≤ L.length
  enc : Enc c.nmem d (S.wb X top1 L (c.nreg 90101))
  regs : ∀ r, r ≠ 90101 → r ≠ 90102 → r ≠ 90105 → c.nreg r = c₀.nreg r
  mem : ∀ a, (a < d.b0 + d.oEx ∨ d.b0 + d.oTmp ≤ a) → c.nmem a = c₀.nmem a

theorem wbStmt_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {S : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {X top : ℕ} {L : List ℕ} (hX : X < E.R) (hL : L.length ≤ E.D)
    (hcap : top - 1 + L.length ≤ d.cap)
    (h100 : c.nreg 90100 = L.length) (h103 : c.nreg 90103 = d.b0 + d.oEx + d.D * X)
    (h50 : c.nreg 90050 = top)
    (htmp : ∀ i, i < L.length → c.nmem (d.b0 + d.oTmp + i) = L.getD i 0) :
    ∃ c' k, Exec P W wbStmt c c' k ∧ k ≤ 10 * E.D + 5 ∧
      Enc c'.nmem d (S.wb X (top - 1) L L.length) ∧ c'.nreg 90108 = top - 1 ∧
      (∀ r, r ≠ 90101 → r ≠ 90102 → r ≠ 90105 → r ≠ 90108 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 + d.oEx ∨ d.b0 + d.oTmp ≤ a) → c'.nmem a = c.nmem a) ∧
      FrameS Brm c c' := by
  suffices hh : ∃ c' k, Exec P W wbStmt c c' k ∧ k ≤ 10 * E.D + 5 ∧
      Enc c'.nmem d (S.wb X (top - 1) L L.length) ∧ c'.nreg 90108 = top - 1 ∧
      (∀ r, r ≠ 90101 → r ≠ 90102 → r ≠ 90105 → r ≠ 90108 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 + d.oEx ∨ d.b0 + d.oTmp ≤ a) → c'.nmem a = c.nmem a) by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5⟩ := hh
    exact ⟨c', k, e, h1, h2, h3, h4, h5, exec_frameS e wrS_wb⟩
  have hb := hD.base
  have hW3 := hD.W1
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  rw [← hD.R] at hX
  rw [← hD.D] at hL
  -- the head
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90101 0,
      .subN 90108 90050 90019]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 90101 = 0 ∧
      c₁.nreg 90108 = top - 1 ∧ (∀ r, r ≠ 90101 → r ≠ 90108 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem) := by
    exec_block
    · omega
    · refine ⟨rfl, ?_, ?_, fun r a1 a2 => by simp [upd, a1, a2], rfl⟩ <;> config_simp
      rw [h50, hC.one]
  obtain ⟨q101, q108, qr, qm⟩ := q
  have I0 : WbI W d S X (top - 1) L c₁ c₁ := by
    refine ⟨e₁.wb_right, by omega, ?_, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    rw [q101, qm]
    refine henc.st_congr (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun x t _ _ => ?_) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun t _ => ?_) <;>
      simp [St.wb]
  have k44 : c₁.nreg 90044 = d.b0 + d.oTmp := by rw [qr _ (by decide) (by decide), hC.bTmp]
  have k43 : c₁.nreg 90043 = d.b0 + d.oStk := by rw [qr _ (by decide) (by decide), hC.bStk]
  have k19 : c₁.nreg 90019 = 1 := by rw [qr _ (by decide) (by decide), hC.one]
  have k100 : c₁.nreg 90100 = L.length := by rw [qr _ (by decide) (by decide), h100]
  have k103 : c₁.nreg 90103 = d.b0 + d.oEx + d.D * X := by
    rw [qr _ (by decide) (by decide), h103]
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90101) (b := 90100)
    (body := wbBody) (WbI W d S X (top - 1) L c₁) (fun d' => L.length - d'.nreg 90101) 8
    (fun _ h => h.wb)
    (fun c₂ I ht => by
      obtain ⟨hw₂, ht₂, henc₂, hr₂, hm₂⟩ := I
      rw [hr₂ 90100 (by decide) (by decide) (by decide), k100] at ht
      generalize htdef : c₂.nreg 90101 = t at ht ht₂ henc₂
      have s := slot_lt (R := d.R) (D := d.D) hX (show t < d.D by omega)
      have r44 : c₂.nreg 90044 = d.b0 + d.oTmp := by
        rw [hr₂ _ (by decide) (by decide) (by decide), k44]
      have r43 : c₂.nreg 90043 = d.b0 + d.oStk := by
        rw [hr₂ _ (by decide) (by decide) (by decide), k43]
      have r19 : c₂.nreg 90019 = 1 := by rw [hr₂ _ (by decide) (by decide) (by decide), k19]
      have r103 : c₂.nreg 90103 = d.b0 + d.oEx + d.D * X := by
        rw [hr₂ _ (by decide) (by decide) (by decide), k103]
      have r108 : c₂.nreg 90108 = top - 1 := by
        rw [hr₂ _ (by decide) (by decide) (by decide), q108]
      have vt : c₂.nmem (d.b0 + d.oTmp + t) = L.getD t 0 := by
        rw [hm₂ _ (by right; omega), qm, htmp t ht]
      unfold wbBody
      exec_block
      · rw [r44]; omega
      · config_simp; rw [r103]; omega
      · config_simp; rw [r43, r108]; omega
      · config_simp; rw [r43, r108]; omega
      · config_simp; rw [r19]; omega
      · refine ⟨⟨by assumption, ?_, ?_, ?_, ?_⟩, by omega, ?_⟩
        · config_simp; rw [r19]; omega
        · config_simp
          rw [r44, r103, r43, r108, r19, htdef, vt]
          have E1 := henc₂.set_ex hX (show t < d.D by omega) (L.getD t 0)
          have E2 := E1.set_stk (show top - 1 + t < d.cap by omega) (L.getD t 0)
          rw [show d.b0 + d.oStk + (top - 1) + t = d.b0 + d.oStk + (top - 1 + t) by omega,
            show d.b0 + d.oEx + d.D * X + t = d.b0 + d.oEx + d.D * X + t from rfl]
          refine E2.st_congr (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun x u _ _ => ?_)
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
            (fun u _ => ?_)
          · simp only [St.wb]
            by_cases hx' : x = X
            · simp only [hx', true_and]
              by_cases hu : u = t
              · rw [ite_eq_left (by omega), ite_eq_left hu, hu]
              · rw [ite_eq_right hu]
                by_cases hu' : u < t
                · rw [ite_eq_left (by omega), ite_eq_left hu']
                · rw [ite_eq_right (by omega), ite_eq_right hu']
            · simp [hx']
          · simp only [St.wb, Function.update_apply]
            by_cases hu : u = top - 1 + t
            · rw [ite_eq_left hu, ite_eq_left ⟨by omega, by omega⟩, hu]
              congr 1; omega
            · rw [ite_eq_right hu]
              by_cases hu' : top - 1 ≤ u ∧ u < top - 1 + t
              · rw [ite_eq_left hu', ite_eq_left ⟨hu'.1, by omega⟩]
              · rw [ite_eq_right hu', ite_eq_right (by omega)]
        · intro r a1 a2 a3
          config_simp
          simp only [upd, a1, a2, a3, ite_false]
          exact hr₂ r a1 a2 a3
        · intro a ha
          config_simp
          simp only [upd]
          rw [ite_eq_right (by rw [r43, r108]; omega), ite_eq_right (by rw [r103]; omega)]
          exact hm₂ a ha
        · config_simp; rw [r19]; omega) I0
  obtain ⟨hw', ht', henc', hr', hm'⟩ := I'
  rw [hr' 90100 (by decide) (by decide) (by decide), k100] at hx
  have hfull : c'.nreg 90101 = L.length := by omega
  rw [hfull] at henc'
  refine ⟨c', _, .seq e₁ e, ?_, henc', ?_, fun r a1 a2 a3 a4 => ?_, fun a ha => ?_⟩
  · rw [q101] at hk
    rw [← hD.D]
    have : 10 * L.length ≤ 10 * d.D := Nat.mul_le_mul_left _ hL
    omega
  · rw [hr' _ (by decide) (by decide) (by decide), q108]
  · rw [hr' r a1 a2 a3, qr r a1 a4]
  · rw [hm' a ha, qm]

/-! ## The tail -/

/-- The class `X` gets the merged degree and weight, and `c` dies. -/
def St.tl (S : St) (cc X len μ : ℕ) : St :=
  { S with
    live := Function.update S.live cc 0
    deg := Function.update S.deg X len
    wt := Function.update S.wt X μ }

/-- `deg X := len`; `wt X := μ`; `live c := 0`; `top := top1 + len`; `nlive := nlive - 1`. -/
def tailStmt : Stmt := block [.addN 90105 90035 90064, .storeN 90105 90100,
  .addN 90105 90036 90064, .storeN 90105 90078, .addN 90105 90030 90062, .constN 90106 0,
  .storeN 90105 90106, .addN 90050 90108 90100, .subN 90051 90051 90019]

theorem tailStmt_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {S : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {cc X len μ top1 : ℕ} (hX : X < E.R) (hcc : cc < E.K) (hcap : top1 + len ≤ d.cap)
    (h62 : c.nreg 90062 = cc) (h64 : c.nreg 90064 = X) (h100 : c.nreg 90100 = len)
    (h78 : c.nreg 90078 = μ) (h108 : c.nreg 90108 = top1) :
    ∃ c' k, Exec P W tailStmt c c' k ∧ k = 9 ∧ Enc c'.nmem d (S.tl cc X len μ) ∧
      c'.nreg 90050 = top1 + len ∧ c'.nreg 90051 = c.nreg 90051 - 1 ∧
      (∀ r, r ≠ 90050 → r ≠ 90051 → r ≠ 90105 → r ≠ 90106 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 ∨ d.b0 + d.oEx ≤ a) → c'.nmem a = c.nmem a) := by
  have hb := hD.base
  have hW3 := hD.W1
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  rw [← hD.R] at hX
  rw [← hD.K] at hcc
  unfold tailStmt
  exec_block
  · rw [hC.bDeg, h64]; omega
  · config_simp; rw [hC.bWt, h64]; omega
  · config_simp; rw [hC.bLive, h62]; omega
  · omega
  · config_simp; rw [h108, h100]; omega
  · refine ⟨rfl, ?_, ?_, ?_, fun r a1 a2 a3 a4 => by simp [upd, a1, a2, a3, a4], ?_⟩ <;>
      config_simp
    · rw [hC.bDeg, h64, hC.bWt, hC.bLive, h62, h100, h78]
      exact ((henc.set_deg hX len).set_wt hX μ).set_live hcc 0
    · rw [h108, h100]
    · rw [hC.one]
    · intro a ha
      rw [hC.bDeg, h64, hC.bWt, hC.bLive, h62]
      simp only [upd]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## The ring -/

/-- Unlink the position `r rn` from the ring. -/
def unlinkS (rn : ℕ) : Stmt := block [.addN 90105 90040 rn, .loadN 90106 90105,
  .addN 90105 90039 rn, .loadN 90107 90105, .addN 90105 90039 90106, .storeN 90105 90107,
  .addN 90105 90040 90107, .storeN 90105 90106]

/-- Unlink position `j` if `b`. -/
def St.optUnl (S : St) (b : Bool) (j : ℕ) : St :=
  if b then { S with nxt := (St.unl (S.nxt, S.prv) j).1, prv := (St.unl (S.nxt, S.prv) j).2 }
  else S

theorem unlinkS_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {S : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {rn j : ℕ} (h5 : rn ≠ 90105) (h6 : rn ≠ 90106) (_h7 : rn ≠ 90107) (hj : c.nreg rn = j)
    (hjA : j < d.A) (hp : S.prv j < d.A) (hn : S.nxt j < d.A) :
    ∃ c' k, Exec P W (unlinkS rn) c c' k ∧ k = 8 ∧ Enc c'.nmem d (S.optUnl true j) ∧
      (∀ r, r ≠ 90105 → r ≠ 90106 → r ≠ 90107 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 + d.oNxt ∨ d.b0 + d.oEg ≤ a) → c'.nmem a = c.nmem a) := by
  have hb := hD.base
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  have ep : c.nmem (d.b0 + d.oPrv + j) = S.prv j := henc.prv j hjA
  have en : c.nmem (d.b0 + d.oNxt + j) = S.nxt j := henc.nxt j hjA
  unfold unlinkS
  exec_block
  · rw [hC.bPrv, hj]; omega
  · config_simp; simp (config := { failIfUnchanged := false }) only [Machine.upd_other _ _ _ h5, Machine.upd_other _ _ _ h6]; rw [hC.bNxt, hj]; omega
  · config_simp; rw [hC.bNxt, hC.bPrv, hj, ep]; omega
  · config_simp; simp (config := { failIfUnchanged := false }) only [Machine.upd_other _ _ _ h5, Machine.upd_other _ _ _ h6]; rw [hC.bPrv, hC.bNxt, hj, en]; omega
  · refine ⟨rfl, ?_, fun r a1 a2 a3 => by simp [upd, a1, a2, a3], ?_⟩ <;> config_simp <;>
      simp (config := { failIfUnchanged := false }) only [Machine.upd_other _ _ _ h5, Machine.upd_other _ _ _ h6]
    · rw [hC.bPrv, hC.bNxt, hj, ep, en]
      exact (henc.set_nxt hp (S.nxt j)).set_prv hn (S.prv j)
    · intro a ha
      rw [hC.bPrv, hC.bNxt, hj, ep, en]
      simp only [upd]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Decrement the count at position `r rn`. -/
def decS (rn : ℕ) : Stmt := block [.addN 90105 90038 rn, .loadN 90106 90105,
  .subN 90106 90106 90019, .storeN 90105 90106]

theorem decS_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {S : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {rn j : ℕ} (_h5 : rn ≠ 90105) (_h6 : rn ≠ 90106) (hj : c.nreg rn = j) (hjA : j < d.A) :
    ∃ c' k, Exec P W (decS rn) c c' k ∧ k = 4 ∧
      Enc c'.nmem d { S with cnt := Function.update S.cnt j (S.cnt j - 1) } ∧
      (∀ r, r ≠ 90105 → r ≠ 90106 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 + d.oCnt ∨ d.b0 + d.oNxt ≤ a) → c'.nmem a = c.nmem a) := by
  have hb := hD.base
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  have ec : c.nmem (d.b0 + d.oCnt + j) = S.cnt j := henc.cnt j hjA
  unfold decS
  exec_block
  · rw [hC.bCnt, hj]; omega
  · refine ⟨rfl, ?_, fun r a1 a2 => by simp [upd, a1, a2], ?_⟩ <;> config_simp
    · rw [hC.bCnt, hj, ec, hC.one]
      exact henc.set_cnt hjA _
    · intro a ha
      rw [hC.bCnt, hj]
      simp only [upd]
      rw [ite_eq_right (by omega)]

/-- Unlink position `r rn` iff the bit `r rb` is set. -/
theorem optUnl_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {S : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {rb rn j : ℕ} {b : Bool} (h5 : rn ≠ 90105) (h6 : rn ≠ 90106) (h7 : rn ≠ 90107)
    (hj : c.nreg rn = j) (hbit : c.nreg rb = bit b)
    (hjA : j < d.A) (hp : S.prv j < d.A) (hn : S.nxt j < d.A) :
    ∃ c' k, Exec P W (.ifLtN rb 90019 .skip (unlinkS rn)) c c' k ∧ k ≤ 10 ∧
      Enc c'.nmem d (S.optUnl b j) ∧
      (∀ r, r ≠ 90105 → r ≠ 90106 → r ≠ 90107 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 + d.oNxt ∨ d.b0 + d.oEg ≤ a) → c'.nmem a = c.nmem a) := by
  cases b with
  | false =>
    exact ⟨c, _, .ifLtN_true (by rw [hbit, hC.one]; decide) (.skip hw), by omega, henc,
      fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | true =>
    obtain ⟨c', k, e, hk, h1, h2, h3⟩ := unlinkS_exec (P := P) hw hC henc hD h5 h6 h7 hj hjA hp hn
    exact ⟨c', _, .ifLtN_false (by rw [hbit, hC.one]; decide) e, by omega, h1, h2, h3⟩

/-- Unlink the dying positions and decrement the counts. -/
def ringStmt : Stmt :=
  .seq (.ifLtN 90072 90019 .skip (unlinkS 90068))
    (.seq (.ifLtN 90073 90019 .skip (unlinkS 90069)) (.seq (decS 90068) (decS 90069)))

/-- The state after `ringStmt`. -/
def St.rg (S : St) (n1 n2 : ℕ) : St :=
  let S3 := (S.optUnl (decide (S.cnt n1 = 1)) n1).optUnl (decide (S.cnt n2 = 1)) n2
  { S3 with cnt := Function.update (Function.update S.cnt n1 (S.cnt n1 - 1)) n2 (S.cnt n2 - 1) }

theorem optUnl_cnt (S : St) (b : Bool) (j : ℕ) : (S.optUnl b j).cnt = S.cnt := by
  unfold St.optUnl; split_ifs <;> rfl

theorem optUnl_bound {S : St} {A : ℕ} (b : Bool) {j j' : ℕ} (hn : S.nxt j < A) (hp : S.prv j < A)
    (hn' : S.nxt j' < A) (hp' : S.prv j' < A) :
    (S.optUnl b j).nxt j' < A ∧ (S.optUnl b j).prv j' < A := by
  unfold St.optUnl St.unl
  split_ifs
  · simp only [Function.update_apply]
    constructor <;> split_ifs <;> assumption
  · exact ⟨hn', hp'⟩

theorem ringStmt_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {S : St} {c : Config}
    (hw : WordsBounded W c) (hC : Cst c E d) (henc : Enc c.nmem d S) (hD : DimOK E d W)
    {n1 n2 : ℕ} (h68 : c.nreg 90068 = n1) (h69 : c.nreg 90069 = n2)
    (h72 : c.nreg 90072 = bit (decide (S.cnt n1 = 1)))
    (h73 : c.nreg 90073 = bit (decide (S.cnt n2 = 1)))
    (hn1 : n1 < d.A) (hn2 : n2 < d.A) (hne : n1 ≠ n2)
    (b1 : S.nxt n1 < d.A ∧ S.prv n1 < d.A) (b2 : S.nxt n2 < d.A ∧ S.prv n2 < d.A) :
    ∃ c' k, Exec P W ringStmt c c' k ∧ k ≤ 28 ∧ Enc c'.nmem d (S.rg n1 n2) ∧
      (∀ r, r ≠ 90105 → r ≠ 90106 → r ≠ 90107 → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < d.b0 + d.oCnt ∨ d.b0 + d.oEg ≤ a) → c'.nmem a = c.nmem a) := by
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  obtain ⟨c₁, k₁, e₁, hk₁, E₁, r₁, m₁⟩ := optUnl_exec (P := P) (rb := 90072) (rn := 90068)
    (b := decide (S.cnt n1 = 1)) hw hC henc hD (by decide) (by decide) (by decide) h68 h72 hn1
    b1.2 b1.1
  have hC₁ : Cst c₁ E d := hC.frame fun r hr _ => r₁ r (by omega) (by omega) (by omega)
  have bb := optUnl_bound (S := S) (decide (S.cnt n1 = 1)) (j := n1) b1.1 b1.2 b2.1 b2.2
  obtain ⟨c₂, k₂, e₂, hk₂, E₂, r₂, m₂⟩ := optUnl_exec (P := P) (rb := 90073) (rn := 90069)
    (b := decide (S.cnt n2 = 1)) e₁.wb_right hC₁ E₁ hD (by decide) (by decide) (by decide)
    (by rw [r₁ _ (by decide) (by decide) (by decide), h69])
    (by rw [r₁ _ (by decide) (by decide) (by decide), h73]) hn2 bb.2 bb.1
  have hC₂ : Cst c₂ E d := hC₁.frame fun r hr _ => r₂ r (by omega) (by omega) (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, E₃, r₃, m₃⟩ := decS_exec (P := P) (rn := 90068) e₂.wb_right hC₂ E₂ hD
    (by decide) (by decide)
    (by rw [r₂ _ (by decide) (by decide) (by decide), r₁ _ (by decide) (by decide) (by decide),
      h68]) hn1
  have hC₃ : Cst c₃ E d := hC₂.frame fun r hr _ => r₃ r (by omega) (by omega)
  obtain ⟨c₄, k₄, e₄, hk₄, E₄, r₄, m₄⟩ := decS_exec (P := P) (rn := 90069) e₃.wb_right hC₃ E₃ hD
    (by decide) (by decide)
    (by rw [r₃ _ (by decide) (by decide), r₂ _ (by decide) (by decide) (by decide),
      r₁ _ (by decide) (by decide) (by decide), h69]) hn2
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_, ?_, ?_⟩
  · refine E₄.st_congr (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun j _ => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    simp only [St.rg, optUnl_cnt, Function.update_apply, ite_eq_right (Ne.symm hne)]
  · intro r a1 a2 a3
    rw [r₄ r a1 a2, r₃ r a1 a2, r₂ r a1 a2 a3, r₁ r a1 a2 a3]
  · intro a ha
    rw [m₄ a (by omega), m₃ a (by omega), m₂ a (by omega), m₁ a (by omega)]

end

end Gran

end Chazelle.Core
