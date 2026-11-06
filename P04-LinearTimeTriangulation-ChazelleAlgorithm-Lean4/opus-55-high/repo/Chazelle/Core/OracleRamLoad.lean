module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvRPlB
public import Chazelle.Core.ShootCutCore2
public import Chazelle.Core.NFBuildRegFill
public import Chazelle.Core.ShootCutShK1M
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.Lemma41Cover

namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
def qLoadA : Stmt :=
  block [.inputSize 120010, .constN 120011 1, .constN 120012 0, .constN 120048 2,
    .constN 120028 6, .copyN 120190 120000, .loadN 120013 120190, .addN 120190 120190 120011,
    .loadN 120014 120190, .addN 120190 120190 120011, .addN 120190 120190 120011,
    .addN 120190 120190 120011, .loadN 120030 120190, .addN 120190 120190 120011,
    .loadN 120031 120190, .addN 120190 120190 120011, .loadN 120032 120190,
    .addN 120190 120190 120011, .loadN 120033 120190, .addN 120190 120190 120011,
    .loadN 120034 120190, .addN 120190 120190 120011, .loadN 120035 120190,
    .addN 120190 120190 120011, .loadN 120036 120190, .addN 120190 120190 120011,
    .loadN 120037 120190, .addN 120190 120190 120011, .loadN 120038 120190,
    .addN 120190 120190 120011, .loadN 120039 120190, .addN 120190 120190 120011,
    .loadN 120040 120190, .addN 120190 120190 120011, .loadN 120041 120190,
    .addN 120190 120190 120011, .loadN 120042 120190, .addN 120190 120190 120011,
    .loadN 120049 120190]

/-- The chain descriptor and the areas of the normal form. -/
def qLoadB : Stmt :=
  block [.copyN 120190 120013, .addN 120190 120190 120011, .loadN 120015 120190,
    .addN 120190 120190 120011, .loadN 120016 120190, .addN 120190 120190 120011,
    .loadN 120017 120190, .addN 120190 120190 120011, .loadN 120018 120190,
    .addN 120019 120016 120016, .constN 120191 7, .addN 120020 120019 120191,
    .constN 120191 6, .addN 120029 120019 120191, .constN 120191 3,
    .addN 120190 120014 120191, .loadN 120043 120190, .addN 120190 120190 120011,
    .loadN 120044 120190, .addN 120190 120190 120011, .loadN 120045 120190,
    .addN 120190 120190 120011, .loadN 120046 120190, .addN 120190 120190 120011,
    .loadN 120047 120190]

/-- The derived constants: `sideS`, the top vertex, the height vertex, the direction bit, the
origin. -/
def qLoadC : Stmt :=
  .seq ztzge
    (.seq ztnal
      (.seq ztttn
        (.seq (ifEq 120001 120011 ztouu ztout)
          (.seq (ifEq 120004 120011 ztotg ztotf)
            zthsq))))

/-- **Loading the constants of the query.** -/
def qLoad : Stmt := .seq qLoadA (.seq qLoadB qLoadC)

/-- The registers written by `qLoad`. -/
def BLd (r : ℕ) : Bool := decide ztgxn || decide ztgxq
theorem wr_qLoad : wr BLd qLoad = true := by_decide
variable {P : Polygon} {W : ℕ} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF} {B : OracleBook.BookData} {k : ℕ}
/-- The values loaded by `qLoadA`. -/
theorem qLoadA_exec
 (hA : QAt P m O E V H C N B k) (hEW : E ≤ W)
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (hO : c.nreg 120000 = O)
    (hW : P.n + 8 ≤ W) :
    ∃ c' k, Exec P W qLoadA c c' k ∧ k = 39 ∧
      c'.nreg 120010 = P.n ∧ c'.nreg 120011 = 1 ∧ c'.nreg 120012 = 0 ∧ c'.nreg 120048 = 2 ∧
      c'.nreg 120028 = 6 ∧ c'.nreg 120013 = V.D ∧ c'.nreg 120014 = V.NB ∧
      c'.nreg 120030 = V.A ∧ c'.nreg 120031 = V.POS ∧ c'.nreg 120032 = V.FL ∧
      c'.nreg 120033 = V.LAB ∧ c'.nreg 120034 = V.DL ∧ c'.nreg 120035 = V.nD ∧
      c'.nreg 120036 = V.ORD ∧ c'.nreg 120037 = V.RK ∧ c'.nreg 120038 = V.CH ∧
      c'.nreg 120039 = V.K ∧ c'.nreg 120040 = V.MD ∧ c'.nreg 120041 = V.TB ∧
      c'.nreg 120042 = V.L ∧ c'.nreg 120049 = V.μ := by
  have hOE := hA.O_le
  unfold qLoadA
  exec_block
  all_goals (config_simp; (try simp only [hO, hm, Nat.add_assoc] at *); (try norm_num); (try omega))
  exact ⟨hA.lD, hA.lNB, hA.lA, hA.lPOS, hA.lFL, hA.lLAB, hA.lDL, hA.lnD, hA.lORD, hA.lRK, hA.lCH,
    hA.lK, hA.lMD, hA.lTB, hA.lL, hA.lμ⟩

/-- The registers written by `qLoadB`. -/
def BLdB (r : ℕ) : Bool :=
  decide (120015 ≤ r ∧ r ≤ 120020) || decide (r = 120029) || decide (120043 ≤ r ∧ r ≤ 120047) ||
    decide ztgxq
theorem wr_qLoadB : wr BLdB qLoadB = true := by_decide

/-- The values loaded by `qLoadB`. -/
theorem qLoadB_exec
 (hA : QAt P m O E V H C N B k) (hEW : E ≤ W)
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (h11 : c.nreg 120011 = 1)
    (h13 : c.nreg 120013 = V.D) (h14 : c.nreg 120014 = V.NB) (hmW : 2 * V.m + 7 ≤ W) :
    ∃ c' k, Exec P W qLoadB c c' k ∧ k = 25 ∧
      c'.nreg 120015 = V.s ∧ c'.nreg 120016 = V.m ∧ c'.nreg 120017 = V.tIdx ∧
      c'.nreg 120018 = V.β ∧ c'.nreg 120019 = 2 * V.m ∧ c'.nreg 120020 = 2 * V.m + 7 ∧
      c'.nreg 120029 = 2 * V.m + 6 ∧ c'.nreg 120043 = V.CB ∧ c'.nreg 120044 = V.AB ∧
      c'.nreg 120045 = V.RB ∧ c'.nreg 120046 = V.SB ∧ c'.nreg 120047 = V.LB := by
  have hD := hA.D_le
  have hNB := hA.NB_TB
  have hTB := hA.TB_le
  unfold qLoadB
  exec_block
  all_goals (config_simp; (try simp only [h11, h13, h14, hm, hA.dm, Nat.add_assoc] at *); (try norm_num); (try omega))
  exact ⟨hA.ds, hA.dt, hA.dβ, by_ring, hA.nCB, hA.nAB, hA.nRB, hA.nSB, hA.nLB⟩

/-- The height vertex of a query origin. -/
def qhzOf : QOrigin → ℕ
  | .sym (.vtx i) => i
  | .sym (.onEdge _ h) => h
  | .box h => h

/-- The origin data of a query origin (`none`: a box origin). -/
noncomputable def qzoOf (Q : Polygon) : QOrigin → Option Point
  | .sym p => some (p.eval Q)
  | .box _ => none

/-- The direction bit of a direction word. -/
def σbOf (v : ℕ) : ℕ := if v = 1 then 1 else 0

/-- The registers written by `qLoadC`. -/
def BLdC (r : ℕ) : Bool := decide (120021 ≤ r ∧ r ≤ 120027)
theorem wr_qLoadC : wr BLdC qLoadC = true := by_decide

/-- The derived constants of `qLoadC`. -/
theorem qLoadC_exec (c : Config) (hw : WordsBounded W c) {n s m t β : ℕ}
    (hn : c.nreg 120010 = n) (h11 : c.nreg 120011 = 1) (hs : c.nreg 120015 = s)
    (ht : c.nreg 120017 = t) (hβ : c.nreg 120018 = β) (h19 : c.nreg 120019 = 2 * m)
    (hst : s + t < 2 * n) (hsW : s + t ≤ W) (hW : 1 ≤ W) {o : QOrigin}
    (ho : QOriginIn c ztdtv o) :
    ∃ c' k, Exec P W qLoadC c c' k ∧ k ≤ 30 ∧ FrameB BLdC c c' ∧
      c'.nreg 120021 = ztitc ∧ c'.nreg 120022 = ztohj % n ∧
      c'.nreg 120023 = qhzOf o ∧ c'.nreg 120024 = σbOf ztfgo ∧
      c'.nreg 120025 = c.nreg 120001 ∧ c'.nreg 120026 = c.nreg 120002 ∧
      c'.nreg 120027 = c.nreg 120003 := by
  -- 1. sideS
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, r₁⟩ : ∃ c₁ k₁, Exec P W (ifEq 120018 120011
      ztfet ztejs) c c₁ k₁ ∧ k₁ ≤ 5 ∧
      c₁.nreg 120021 = ztitc ∧
      (∀ r, r ≠ 120021 → c₁.nreg r = c.nreg r) := by
    by_cases hb : β = 1
    · obtain ⟨c₁, e₁, v₁, r₁⟩ := copy_exec hw 120021 120017
      exact ⟨c₁, _, ifEq_eq_exec by_omega e₁, by_omega,
        by simp_all, r₁⟩
    · obtain ⟨k', e', hk'⟩ := ifEq_ne_exec
        (show c.nreg 120018 ≠ c.nreg 120011 by rw [hβ, h11]; exact hb)
        (Exec.subN hw 120021 120019 120017)
      refine zthmf
      · simp_all
      simp_all
  zud
  -- 2. the top vertex
  obtain ⟨c₂, e₂, v₂, r₂, -⟩ := add_exec (P := P) w₁ 120022 120015 120017 (by
    simp_all)
  rw [r₁ _ by_decide, r₁ _ by_decide, hs, ht] at v₂
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, r₃, -⟩ := modSub_exec (P := P) (r := 120022) (nr := 120010)
    by_decide c₂ e₂.wb_right by_simp_all
  rw [v₂, r₂ _ by_decide, r₁ _ by_decide, hn] at v₃
  have R₃ : ∀ r, r ≠ 120021 → r ≠ 120022 → c₃.nreg r = c.nreg r := by_simp_all
  zubj
  -- 3. the height vertex
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, r₄⟩ : ∃ c₄ k₄, Exec P W (ifEq 120001 120011
      ztouu ztout) c₃ c₄ k₄ ∧ k₄ ≤ 5 ∧
      c₄.nreg 120023 = qhzOf o ∧ (∀ r, r ≠ 120023 → c₄.nreg r = c₃.nreg r) := by
    obtain ⟨cA, eA, vA, rA⟩ := copy_exec (P := P) w₃ 120023 120003
    obtain ⟨cB, eB, vB, rB⟩ := copy_exec (P := P) w₃ 120023 120002
    have g1 : zthos := by_simp_all
    have g := fun r a b =>
      R₃ r by_omega by_omega
    zuvr

    · zuidb
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec
        (show c₃.nreg 120001 ≠ c₃.nreg 120011 by
          zunwn;  omega) eB
      zuekh

    · zugqi
      refine ⟨cA, _, ifEq_eq_exec (by
        simp_all) eA,
        by omega, ?_, rA⟩
      rw [vA, g _ by_norm_num by_norm_num]; exact o3
    · zuidb
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec
        (show c₃.nreg 120001 ≠ c₃.nreg 120011 by
          zunwn;  omega) eB
      zuekh

  zucc
  -- 4. the direction bit
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅⟩ : ∃ c₅ k₅, Exec P W (ifEq 120004 120011
      ztotg ztotf) c₄ c₅ k₅ ∧ k₅ ≤ 5 ∧
      c₅.nreg 120024 = σbOf ztfgo ∧ (∀ r, r ≠ 120024 → c₅.nreg r = c₄.nreg r) := by
    have g1 : ztpnq := by_simp_all
    have g4 : c₄.nreg 120004 = c.nreg 120004 := by
      simp_all
    by_cases hd : c.nreg 120004 = 1
    · obtain ⟨cA, eA, vA, rA⟩ := const_exec w₄ 120024 1 hW
      exact ⟨cA, _, ifEq_eq_exec by_omega eA, by_omega,
        by rw [vA]; unfold σbOf; simp_all, rA⟩
    · obtain ⟨cB, eB, vB, rB⟩ := const_exec w₄ 120024 0 by_omega
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec
        (show c₄.nreg 120004 ≠ c₄.nreg 120011 by rw [g1, g4]; exact hd) eB
      exact ⟨cB, k', e', by_omega, by rw [vB]; unfold σbOf; simp_all, rB⟩
  zuef
  -- 5. the origin
  obtain ⟨c₆, k₆, e₆, hk₆, v₆⟩ : ∃ c₆ k₆, Exec P W
      zthsq c₅ c₆ k₆ ∧
      k₆ = 3 ∧ (c₆.nreg 120025 = c₅.nreg 120001 ∧ c₆.nreg 120026 = c₅.nreg 120002 ∧
        c₆.nreg 120027 = c₅.nreg 120003 ∧ ∀ r, r < 120025 ∨ 120027 < r → c₆.nreg r = c₅.nreg r) := by
    exec_block
    exact ⟨rfl, by config_simp, by config_simp, by config_simp, fun r hr => by
      config_simp; upd_solve⟩
  obtain ⟨v25, v26, v27, r₆⟩ := v₆
  have ex : Exec P W qLoadC c c₆ _ := .seq e₁ ztfv
  have G : ∀ r, 120001 ≤ r → r ≤ 120004 → c₅.nreg r = c.nreg r := fun r a b => by
    rw [r₅ r by_omega, r₄ r by_omega, R₃ r by_omega by_omega]
  refine ⟨c₆, _, ex, by_omega, exec_frameB ex wr_qLoadC, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₆ _ by_omega, r₅ _ by_decide, r₄ _ by_decide, r₃ _ by_decide,
      r₂ _ by_decide]; exact v₁
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-- The values of the query: the structure's, with the origin and the direction. -/
noncomputable def qV (V : QV) (P : Polygon) (o : QOrigin) (d : ℕ) : QV :=
  { V with hz := qhzOf o, σb := σbOf d, zo := qzoOf (Qof P) o }
theorem wr_qLoadA : wr BLd qLoadA = true := by_decide

/-- **Loading the constants of the query.** -/
theorem qLoad_exec
 (hA : QAt P m O E V H C N B k) (hEW : E ≤ W)
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (hO : c.nreg 120000 = O)
    (hW : 8 * P.n + 32 ≤ W) {o : QOrigin} (ho : QOriginIn c ztdtv o)
    (hol : o.Lt P.n) :
    ∃ c' k, Exec P W qLoad c c' k ∧ k ≤ 100 ∧ FrameB BLd c c' ∧
      QConst P ztcdm c' := by
  zuc
  obtain ⟨-, -, hd1, hd2, hd3, -⟩ := hA.desc
  have hVm : ztplg := by zuofu
  have hVs : V.s = C.s := by zunkn
  have hVt : V.tIdx = C.topIdx := by rw [← hA.dt, hd3]
  have hmn : ztgaj := by have := C.m_lt; rw [hA.CQ, hQn] at this; omega
  zucrx
  zumex
  obtain ⟨c₁, k₁, e₁, hk₁, a10, a11, a12, a48, a28, a13, a14, a30, a31, a32, a33, a34, a35, a36,
    a37, a38, a39, a40, a41, a42, a49⟩ := qLoadA_exec hA hEW c hw hm hO by_omega
  have f₁ := exec_frameB e₁ wr_qLoadA
  obtain ⟨c₂, k₂, e₂, hk₂, b15, b16, b17, b18, b19, b20, b29, b43, b44, b45, b46, b47⟩ :=
    qLoadB_exec hA hEW c₁ e₁.wb_right (by zunok) a11 a13 a14 by_omega
  have f₂ := exec_frameB e₂ wr_qLoadB
  zucgb
  have ho₂ : QOriginIn c₂ ztdtv o := by
    have hr : ∀ r, 120001 ≤ r → r ≤ 120004 → c₂.nreg r = c.nreg r := fun r a b => by
      zugui
    rw [show bandReg bOQuery 1 = 120001 from rfl] at ho ⊢
    rcases o with (i | ⟨e, h⟩) | h <;> simp only [QOriginIn, SymPtIn] at ho ⊢ <;>
      norm_num at ho ⊢ <;> simp only [hr 120001 by_norm_num by_norm_num, hr 120002 by_norm_num by_norm_num, hr 120003 by_norm_num by_norm_num] <;> exact ho
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, v21, v22, v23, v24, v25, v26, v27⟩ := qLoadC_exec (P := P) c₂
    e₂.wb_right (n := P.n) (s := V.s) (m := V.m) (t := V.tIdx) (β := V.β)
    ztlhh ztlhh b15 b17 b18 b19
    by_omega by_omega by_omega ho₂
  have ex : Exec P W qLoad c c₃ _ := .seq e₁ ztcr
  have f := exec_frameB ex wr_qLoad
  -- the values after all three phases
  have K2 := f₃.1
  have K1 : ∀ r, BLdC r = false → BLdB r = false → c₃.nreg r = c₁.nreg r := by_simp_all
  have hd4 : c₂.nreg 120004 = c.nreg 120004 := by
    rw [g₂ _ by_decide, f₁.1 _ by_decide]
  have hr0 : ∀ r, 120001 ≤ r → r ≤ 120003 → c₂.nreg r = c.nreg r := fun r a b => by
    zugui
  refine ⟨c₃, _, ex, by_omega, f, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [K1 _ by_decide by_decide]; assumption)
    | (rw [K2 _ by_decide]; assumption)
    | skip
  · zunry; exact hA.sS.symm
  · zuodg; exact hA.tv.symm
  · exact v23
  · rw [v24, hd4]; rfl
  · rw [hr0 _ by_norm_num by_norm_num] at v25 v26 v27
    zuvr

    · exact Or.inr ⟨by_omega, .vtx i, hol,
        ⟨by_omega, by_simp_all⟩, rfl⟩
    · exact Or.inr ⟨by_omega, .onEdge e h, hol,
        ⟨by_omega, by_simp_all, by_simp_all⟩, rfl⟩
    · exact Or.inl ⟨by_omega, rfl⟩

/-- The structure facts do not read the origin and direction of the values. -/
theorem QAt.withQ
 (hA : QAt P m O E V H C N B k) (o : QOrigin)
    (d : ℕ) : QAt P m O E ztkdc H C N B k := { hA with }

/-- The value facts of the query. -/
theorem QAt.qvok
 (hA : QAt P m O E V H C N B k) {o : QOrigin}
    (hol : o.Lt P.n) (d : ℕ) : QVOK P C ztkdc := by
  zuc
  obtain ⟨-, -, hd1, hd2, hd3, hd4⟩ := hA.desc
  zucrx
  refine ⟨hA.CQ, by show V.s = C.s; zunkn, by show V.m = C.m; zuofu,
    ?_, ?_, ?_, by show V.s < P.n; zunkn; omega⟩
  · show V.sS = C.sideS C.sideBeta
    rw [hA.sS, ← hA.dβ, ← hA.dt, hd3, ← hA.dm, hd2]
    unfold Chain.sideS
    simp_all
  · show qhzOf o < P.n
    rcases o with (i | ⟨e, h⟩) | h
    · tauto
    · exact hol.2
    tauto
  · show σbOf d ≤ 1
    unfold σbOf; grind
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
open Chazelle.Visibility (rayPt hseg)
@[expose] public section
open Classical in
/-- **The abscissa of the end `(w, h + 1)`** by its class. -/
noncomputable def xv (P : Polygon) (C : Chain) (V : QV) (w h : ℕ) : ℝ :=
  if xpClass w = 0 then -C.radius else if xpClass w = 2 then C.radius else xpX P C V w h

/-- The chain data of the values. -/
structure TopOK (P : Polygon) (C : Chain) (V : QV) : Prop where
  hv : QVOK P C V
  top : (Qof P).vtx V.tv = C.top
  tv_lt : V.tv < P.n
  hD : DistinctHeights zta
variable {P : Polygon} {C : Chain} {V : QV}
theorem vtx_snd_lt_radius (hCQ : C.P = Qof P) {h : ℕ} (hh : h < P.n) :
    |((Qof P).vtx h).2| < C.radius := by
  have hn : h < C.P.n := by rw [hCQ, show (Qof P).n = P.n from shear_n _ _]; exact hh
  have := Chazelle.Jordan.abs_snd_vtx_le_coordBound C.P hn
  rw [hCQ] at this
  have := C.coordBound_lt_radius
  grind
theorem abs_fst_lt_radius_of_mem {p : Point} (hp : p ∈ C.set) : |p.1| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).1 C.coordBound_lt_radius

/-- The chain edge `ci` is the edge `eIdx n s ci` of `Q`. -/
theorem chainEdge_eq_edge (hv : QVOK P C V) (ci : ℕ) :
    C.chainEdge ci = (Qof P).edge (eIdx P.n V.s ci) := by
  unfold Chain.chainEdge Chain.edgeIdx eIdx
  zudaf

/-- The edges of `Q` are not horizontal. -/
theorem edge_nonhoriz (hD : DistinctHeights zta) {e : ℕ} (he : e < P.n) (hn : 2 ≤ P.n) :
    ((Qof P).vtx e).2 ≠ ((Qof P).vtx (ztda % (Qof P).n)).2 := by
  zuc
  refine hD _ _ by_omega ztcv ?_
  zujih
  zuq
  rcases Nat.lt_or_ge ztda P.n with h' | h'
  · zupe
  · rw [show e + 1 = P.n by omega, Nat.mod_self] at h; omega

/-- **The ends by class.** -/
theorem end_class (hT : TopOK P C V) {w h : ℕ} (hw : w < 2 * C.m + 7) (hh : h < P.n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hy : (Geometry.lerp ztdrs
      ztwvt t).2 = ((Qof P).vtx h).2)
    (hyt : ((Qof P).vtx h).2 ≤ C.top.2) :
    Geometry.lerp ztdrs
        ztwvt t =
      ztgry ∧
    (xpClass w = 1 → Geometry.lerp ztdrs
        ztwvt t ∈ C.set ∧
      symIdx ztfiz < P.n ∧
      Geometry.lerp ztdrs
        ztwvt t ∈
          (Qof P).edge ztbait) ∧
    (xpClass w ≠ 1 → Geometry.lerp ztdrs
        ztwvt t ∉ C.set) := by
  zudpl
  zubo
  have hyR := vtx_snd_lt_radius hv.CQ hh
  zvncj at hyR
  have htopR := C.top_snd_lt_radius
  zuru
  zubb
  zuc
  have hn2 : ztmss := by
    have := C.add_one_le; rw [hv.CQ, hQn] at this; omega
  set y := ((Qof P).vtx h).2 with hydef
  -- the box and slit edges
  have hW : ∀ i, (chainModel C).W.vtx i = (C.sideWalk C.sideBeta).vtx i := fun _ => rfl
  rw [hnW] at hy ⊢
  simp only [hW] at hy ⊢
  have notset : ∀ p : Point, |p.1| = C.radius → p ∉ C.set := fun p hp hm => by
    have := abs_fst_lt_radius_of_mem hm; linarith
  rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ (6 ≤ w ∧ w < 2 * C.m + 6) ∨
      w = 2 * C.m + 6) with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h6, h6'⟩ | rfl
  · exfalso
    zugci
    zugyw
  · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_one, C.sideWalk_vtx_two] at hy ⊢
    have hx : xpClass 1 = 0 := rfl
    refine ztkyf
    · ext
      · zuior
      omega
    · simp [Geometry.lerp, abs_of_neg (neg_lt_zero.2 hR)]
  · exfalso
    zufmo

  · rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hy ⊢
    have hx : xpClass 3 = 2 := rfl
    refine ztkyf
    · ext
      · zuior
      omega
    · simp [Geometry.lerp, abs_of_pos hR]
  · exfalso
    zugch
    zugyw
  · exfalso
    rw [Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_five, C.sideWalk_vtx_six] at hy
    zuhpc
    nlinarith
  · -- a tour edge
    zucxw
    rw [Nat.mod_eq_of_lt by_omega, show i + 6 + 1 = ztg + 6 by ring,
      C.sideWalk_vtx_tour _ by_omega, C.sideWalk_vtx_tour _ by_omega] at hy ⊢
    have hseg : Geometry.lerp ztnjy ztyoq t ∈
        C.chainEdge ztoiu := by
      zunkl; exact ⟨t, ht0, ht1.le, rfl⟩
    have hcls : xpClass ztcy = 1 := by_rfl
    have hsym : xpSym C V P.n ztcy h = .onEdge (eIdx P.n V.s ztoiu) h := by
      unfold xpSym; rw [ite_eq_left ztdgt, show i + 6 - 6 = i by omega]
    have hci := tci_lt C i
    set e := eIdx P.n V.s _ with he
    zuhyn
    have hedge := hseg
    rw [chainEdge_eq_edge hv] at hedge
    set p := Geometry.lerp _ _ t
    have hx : p.1 = xe zta e h := by
      have := (rayPt_mem_edge_iff _ (edge_nonhoriz hT.hD hen hn2) hy ztp
        0).1 by_simp_all
      grind
    refine ⟨?_, fun _ => ⟨⟨_, hci, hseg⟩, by zunta; tauto, by zunta; tauto⟩,
      by omega⟩
    ext
    · show p.1 = xv P C V ztcy h
      zvnly; unfold xv xpX; zuntb; rfl
    omega
  · -- up the slit: the top vertex
    rw [show ztbjc % ztz = 0 by
      rw [show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self],
      show 2 * C.m + 6 = 2 * C.m + 6 from rfl, C.sideWalk_vtx_tour _ le_rfl,
      C.sideTour_two_m, C.sideWalk_vtx_zero] at hy ⊢
    zuhpc
    have ht : ztbhh := by_nlinarith
    zucfb
    have hcls : xpClass ztcc = 1 := by_rfl
    have hsym : xpSym C V P.n ztcc h = .vtx V.tv := by
      unfold xpSym; rw [ite_eq_right ztdgt]
    zumlh
    refine ⟨?_, fun _ => ⟨C.top_mem_set, by zunta; exact hT.tv_lt, ?_⟩,
      by omega⟩
    · ext
      · unfold xv xpX; zuntb
        show C.top.1 = ((Qof P).vtx V.tv).1; zuozo
      simp_all
    · zunta; show C.top ∈ Polygon.edge _ V.tv
      rw [← hT.top]; exact ztolk

/-- Two horizontal segments with `a < b` are equal only if their data are. -/
theorem hseg_inj {y a b y' a' b' : ℝ} (hab : a < b) (ha'b' : a' ≤ b')
    (h : hseg y a b = hseg y' a' b') : y = y' ∧ a = a' ∧ b = b' := by
  have m1 : ztygh := by zvmzi; exact ztgpm
  have m2 : (ztdy : Point) ∈ hseg y' a' b' := by zvmzi; exact ztgpl
  have e1 := m1.1
  zumpy
  have m3 : ztygi := by zvmwc; trivial
  have m4 : ztygj := by zvmwc; trivial
  exact ⟨rfl, le_antisymm m3.2.1 m1.2.1, le_antisymm m2.2.2 m4.2.2⟩

/-- The facts of one end of a chord. -/
def EndFacts (P : Polygon) (C : Chain) (V : QV) (w h : ℕ) : Prop :=
  (chainModel C).pos zta ztboe = ztgry ∧
    (xpClass w = 1 → (chainModel C).pos zta ztboe ∈ C.set ∧
      symIdx ztfiz < P.n ∧
      (chainModel C).pos zta ztboe ∈ (Qof P).edge ztbait) ∧
    (xpClass w ≠ 1 → (chainModel C).pos zta ztboe ∉ C.set) ∧
    (w < 2 * C.m + 7 ∧ 0 ≤ (chainModel C).param zta ztboe ∧
      (chainModel C).param zta ztboe < 1)

/-- **A chord record is the horizontal chord of the domain between its two ends.** -/
theorem chord_facts (hT : TopOK P C V) {N : NF} (hN : IsNF ztc zta N) {i : ℕ}
    (hi : i < N.chords.length) :
    (N.chord i).h < P.n ∧ ((Qof P).vtx (N.chord i).h).2 ≤ C.top.2 ∧
    Chazelle.Chain.IsHChordIn C.dom ((Qof P).vtx (N.chord i).h).2
      ztibs ztibt ∧
    (N.chord i).toSet ztc zta = hseg ((Qof P).vtx (N.chord i).h).2
      ztibs ztibt ∧
    EndFacts P C V (N.chord i).lp (N.chord i).h ∧ EndFacts P C V (N.chord i).rp (N.chord i).h := by
  zuc
  obtain ⟨hFam, -, hAtt, reg, -, -, -, -, -, hh, -⟩ := hN
  set ch := N.chord i with hch
  have hhn : ch.h < P.n := by have := hh i hi; simp_all
  have hmem : ch.toSet _ _ ∈ N.F ztc zta :=
    ⟨ch, by rw [hch]; unfold NF.chord; simp_all,
      rfl⟩
  obtain ⟨y', a, b, hH, hyt, hset⟩ := hFam.2.1 hmem
  obtain ⟨⟨hl1, hl2, hl3, hl4, -⟩, ⟨hr1, hr2, hr3, hr4, -⟩⟩ := hAtt i hi
  -- the two ends lie on the chord
  have hl : (chainModel C).pos _ ch.lpos ∈ hseg ((Qof P).vtx ch.h).2
      ((chainModel C).pos _ ch.lpos).1 ((chainModel C).pos _ ch.rpos).1 := hl4
  have hr : (chainModel C).pos _ ch.rpos ∈ hseg ((Qof P).vtx ch.h).2
      ((chainModel C).pos _ ch.lpos).1 ((chainModel C).pos _ ch.rpos).1 := hr4
  have hle : ((chainModel C).pos _ ch.lpos).1 ≤ ((chainModel C).pos _ ch.rpos).1 :=
    hl.2.2
  obtain ⟨ey, ea, eb⟩ := hseg_inj hH.lt hle hset.symm
  have hyt' : ((Qof P).vtx ch.h).2 ≤ C.top.2 := by_simp_all
  zuru
  have EL := end_class hT (w := ch.lp) by_simp_all hhn hl2 hl3 hl.1 hyt'
  have ER := end_class hT (w := ch.rp) by_simp_all hhn hr2 hr3 hr.1 hyt'
  have xl : ((chainModel C).pos zta ch.lpos).1 = xv P C V ch.lp ch.h := by
    have := congrArg Prod.fst EL.1; tauto
  have xr : ((chainModel C).pos zta ch.rpos).1 = xv P C V ch.rp ch.h := by
    have := congrArg Prod.fst ER.1; tauto
  refine ⟨hhn, hyt', ?_, ?_, ⟨EL.1, EL.2.1, EL.2.2, by_grind, hl2, hl3⟩,
    ⟨ER.1, ER.2.1, ER.2.2, by_grind, hr2, hr3⟩⟩
  · grind
  grind

/-! ## The comparisons of the program, geometrically -/
open Classical in
/-- **The effective origin**: the point where the ray enters the closed box (the origin itself if
it is in the box). -/
noncomputable def ζOf (C : Chain) (V : QV) (z : Point) : ℝ :=
  if V.σb = 1 then max z.1 (-C.radius) else min z.1 C.radius

/-- The origin is not past the box in the direction of the ray. -/
def NotPast (C : Chain) (V : QV) (z : Point) : Prop :=
  (V.σb = 1 → z.1 < C.radius) ∧ (V.σb ≠ 1 → -C.radius < z.1)

/-- A class-`1` end is strictly inside the box. -/
def EndGood (P : Polygon) (C : Chain) (V : QV) (w h : ℕ) : Prop :=
  xpClass w = 1 → |xpX P C V w h| < C.radius
theorem xpClass_cases (w : ℕ) : xpClass w = 0 ∨ xpClass w = 1 ∨ xpClass w = 2 := by
  unfold xpClass; grind
variable {z : Point} {eD w h : ℕ}
theorem endGtZ_iff (hσ : V.σb = 1) (hz : ZoOK C zthx z V.zo)
    (hnp : NotPast C V z) {w h : ℕ} (he : EndGood P C V w h) :
    EndGtZ P C V w h ↔ ζOf C V z < xv P C V w h := by
  zubo
  have hs : sgnOf V.σb = 1 := by unfold sgnOf; simp_all
  zulls
  unfold EndGtZ ζOf xv; zvnpq
  zupa
  · simp_all
  · zullp
    zvmwp; simp only [show ¬ (1 : ℕ) = 0 by omega, show ¬ (1 : ℕ) = 2 by omega, ite_false,
      true_and, false_or]
    zugry
    · simp_all
    simp_all
  simp_all
theorem endLtZ_iff (hσ : V.σb ≠ 1) (hz : ZoOK C zthx z V.zo)
    (hnp : NotPast C V z) {w h : ℕ} (he : EndGood P C V w h) :
    EndLtZ P C V w h ↔ xv P C V w h < ζOf C V z := by
  zubo
  have hs : sgnOf V.σb = -1 := by unfold sgnOf; simp_all
  zullt
  unfold EndLtZ ζOf xv; zvnpr
  zupa
  · simp_all
  · zullp
    zvmwp; simp only [show ¬ (1 : ℕ) = 0 by omega, show ¬ (1 : ℕ) = 2 by omega, ite_false,
      true_and, false_or]
    zugry
    · simp_all
    simp_all
  simp_all
theorem endLtD_iff (_he : EndGood P C V w h)
    (hD : |xe zta eD V.hz| < C.radius) :
    EndLtD P C V eD w h ↔ xv P C V w h < xe zta eD V.hz := by
  zullo
  unfold EndLtD xv
  zupa
  · simp_all
  · simp_all
  grind
theorem endGtD_iff (_he : EndGood P C V w h)
    (hD : |xe zta eD V.hz| < C.radius) :
    EndGtD P C V eD w h ↔ xe zta eD V.hz < xv P C V w h := by
  zullo
  unfold EndGtD xv
  zupa
  · grind
  · simp_all
  simp_all

/-- The ends of a chord are good. -/
theorem EndFacts.good {w h : ℕ} (hE : EndFacts P C V w h) : EndGood P C V w h := by
  zudqd
  obtain ⟨hpos, hc, -, -⟩ := hE
  have hm := (hc h1).1
  zvnbl at hm
  have := abs_fst_lt_radius_of_mem hm
  unfold xv at this; simp_all
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
open Chazelle.Visibility (rayPt hseg)
@[expose] public section
variable {P : Polygon} {C : Chain} {V : QV}

/-- **The chord records in memory.** -/
structure ChordRecOK (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (N : NF) : Prop where
  hT : TopOK P C V
  hN : IsNF ztc zta N
  nf : NFAt m V.NB N
  CB : m zttdu = V.CB
  K : V.K = N.chords.length
  lt : ∀ q, q < V.K → chAt m V q < V.K
  inj : ∀ q q', q < V.K → q' < V.K → chAt m V q = chAt m V q' → q = q'
  sorted : ∀ q q', q ≤ q' → q' < V.K → ChLe P C V m ztlly (chAt m V q')
variable {m : ℕ → ℕ} {N : NF}
theorem ChordRecOK.recs (h : ChordRecOK P C V m N) {i : ℕ} (hi : i < V.K) :
    chH m V i = (N.chord i).h ∧ chL m V i = (N.chord i).lp ∧ chR m V i = (N.chord i).rp := by
  have := h.nf.2.2.2.2.2.1 i ztljd
  rw [h.CB] at this
  tauto

/-- The facts of the chord record `i` in memory. -/
theorem ChordRecOK.facts (h : ChordRecOK P C V m N) {i : ℕ} (hi : i < V.K) :
    chH m V i < P.n ∧ ((Qof P).vtx ztccz).2 ≤ C.top.2 ∧
    Chazelle.Chain.IsHChordIn C.dom ((Qof P).vtx ztccz).2
      ztyxj ztyxk ∧
    (N.chord i).toSet ztc zta = hseg ((Qof P).vtx ztccz).2
      ztyxj ztyxk ∧
    EndFacts P C V ztbdb ztccz ∧ EndFacts P C V ztbrg ztccz := by
  obtain ⟨e1, e2, e3⟩ := h.recs hi
  zuihm
  exact chord_facts h.hT h.hN ztljd
variable {w h : ℕ}
theorem xv_c0 (hc : xpClass w = 0) : xv P C V w h = -C.radius := by
  zucai
theorem xv_c1 (hc : xpClass w = 1) : xv P C V w h = xpX P C V w h := by
  zucai
theorem xv_c2 (hc : xpClass w = 2) : xv P C V w h = C.radius := by
  zucai
theorem xv_ge (P : Polygon) (C : Chain) (V : QV) {w h : ℕ} (he : EndGood P C V w h) :
    -C.radius ≤ xv P C V w h := by
  zubo
  unfold xv
  zupa
  · simp_all
  · zvmyn; exact (abs_lt.1 ztjxr).1.le
  grind
theorem xv_le (P : Polygon) (C : Chain) (V : QV) {w h : ℕ} (he : EndGood P C V w h) :
    xv P C V w h ≤ C.radius := by
  zubo
  unfold xv
  zupa
  · grind
  · zvmyn; exact (abs_lt.1 ztjxr).2.le
  simp_all

/-- The order of the table on the left ends is the order of their abscissae. -/
theorem chLe_xv {a b : ℕ} (ha : EndGood P C V zteeu ztcmt)
    (hb : EndGood P C V ztbvv zthvo) (hle : ChLe P C V m a b)
    (hh : chH m V a = chH m V b) :
    xv P C V zteeu ztcmt ≤ xv P C V ztbvv zthvo := by
  rcases hle with hlt | ⟨-, hcl | ⟨hce, hx⟩⟩
  · omega
  · zuhin
    · rw [xv_c0 h0]; exact xv_ge P C V hb
    · have hb2 : xpClass ztbvv = 2 := by have := xpClass_le ztbvv; omega
      rw [xv_c2 hb2]; exact xv_le P C V ha
    · have := xpClass_le ztbvv; omega
  · zuhin
    · rw [xv_c0 h0, xv_c0 (show xpClass ztbvv = 0 by omega)]
    · rw [xv_c1 h1, xv_c1 (show xpClass ztbvv = 1 by omega)]; tauto
    · rw [xv_c2 h2, xv_c2 (show xpClass ztbvv = 2 by omega)]

/-- **Two chords at one height do not overlap**: with the left end of `a` not after the left end
of `b`, the right end of `a` is not after the left end of `b`. -/
theorem chord_disjoint (h : ChordRecOK P C V m N) {a b : ℕ} (ha : a < V.K) (hb : b < V.K)
    (hab : a ≠ b) (hh : chH m V a = chH m V b)
    (hl : xv P C V zteeu ztcmt ≤ xv P C V ztbvv zthvo) :
    xv P C V ztrni ztcmt ≤ xv P C V ztbvv zthvo := by
  obtain ⟨-, -, Ha, Sa, -, -⟩ := h.facts ha
  obtain ⟨-, -, Hb, Sb, -, -⟩ := h.facts hb
  rw [← hh] at Hb Sb hl ⊢
  set y := ((Qof P).vtx ztcmt).2
  set la := xv P C V zteeu ztcmt
  set ra := xv P C V ztrni ztcmt
  set lb := xv P C V ztbvv ztcmt
  set rb := xv P C V (chR m V b) ztcmt
  zux

  have hab' := Ha.lt
  have hbb := Hb.lt
  -- a point inside both
  set x := (lb + min ra rb) / 2 with hx
  have hmin : lb < min ra rb := lt_min hc hbb
  have hx1 : lb < x := by_grind
  have hx2 : x < min ra rb := by_grind
  have hxa : (ztjw : Point) ∈ hseg y la ra :=
    ⟨rfl, by_grind, by_grind⟩
  have hxb : (ztjw : Point) ∈ hseg y lb rb :=
    ⟨rfl, by_grind, by_grind⟩
  rcases Chazelle.Chain.hchordIn_inter Ha Hb hxa hxb with ⟨-, e1, e2⟩ | ⟨-, hp⟩
  · -- the same chord
    have hs : (N.chord a).toSet ztc zta = (N.chord b).toSet ztc zta := by
      simp_all
    obtain ⟨-, hinj, -⟩ := h.hN
    exact hab (hinj a b (show a < N.chords.length by zuosj; exact ha)
      (show b < N.chords.length by zuosj; exact hb) hs)
  grind

/-- `EndGtZ` is upward closed along good ends. -/
theorem endGtZ_mono {w h w' h' : ℕ} (he : EndGood P C V w h) (he' : EndGood P C V w' h')
    (hle : xv P C V w h ≤ xv P C V w' h') (hg : EndGtZ P C V w h) : EndGtZ P C V w' h' := by
  zubo
  have c1 : zteed := fun hc => by
    zucai
  have c2 : ztfll := fun hc => by
    zucai
  have c0 : ztfdy := fun hc => by
    zucai
  unfold EndGtZ at hg ⊢
  rcases xpClass_cases w' with h0 | h1 | h2
  · exfalso
    rw [c0 h0] at hle
    zugru
    · grind
    · rw [c1 hg1] at hle; linarith [(abs_lt.1 (he hg1)).1]
  · zuekm

    · exfalso; rw [c2 hg, c1 h1] at hle; linarith [(abs_lt.1 (he' h1)).2]
    grind
  omega

/-- `EndLtZ` is downward closed along good ends. -/
theorem endLtZ_mono {w h w' h' : ℕ} (he : EndGood P C V w h) (he' : EndGood P C V w' h')
    (hle : xv P C V w h ≤ xv P C V w' h') (hg : EndLtZ P C V w' h') : EndLtZ P C V w h := by
  zubo
  have c1 : zteed := fun hc => by
    zucai
  have c2 : ztfll := fun hc => by
    zucai
  have c0 : ztfdy := fun hc => by
    zucai
  unfold EndLtZ at hg ⊢
  zupa
  · omega
  · zuekm

    · exfalso; rw [c0 hg, c1 h1] at hle; linarith [(abs_lt.1 ztjxr).1]
    grind
  · exfalso
    rw [c2 h2] at hle
    zugru
    · grind
    · rw [c1 hg1] at hle; linarith [(abs_lt.1 (he' hg1)).2]

/-- **The search predicate holds on a prefix of the table.** -/
theorem chPr_iff (x : ℕ) : chPr P C V m x = true ↔ (x < V.K ∧ (chH m V x < V.hz ∨
    (chH m V x = V.hz ∧ ((V.σb = 1 → ¬ EndGtZ P C V (chR m V x) V.hz) ∧
      (V.σb ≠ 1 → EndLtZ P C V (chL m V x) V.hz))))) := by
  classical
  unfold chPr
  zummd
  zuqe
  · simp_all
  · simp_all
theorem chPr_mono (h : ChordRecOK P C V m N) :
    ∀ i j, i ≤ j → j < V.K → chPr P C V m ztrne = true →
      chPr P C V m (chAt m V i) = true := by
  intro i j hij hj hpj
  have hi : i < V.K := by_omega
  have hle := h.sorted i j hij hj
  obtain ⟨a, hadef⟩ : ∃ a, chAt m V i = a := zths
  obtain ⟨b, hbdef⟩ : ∃ b, chAt m V j = b := zths
  have ha : a < V.K := hadef ▸ h.lt i hi
  have hb : b < V.K := hbdef ▸ h.lt j hj
  rw [hadef, hbdef] at hle
  rw [hbdef] at hpj
  rw [hadef]
  obtain ⟨-, -, -, -, ELa, ERa⟩ := h.facts ha
  obtain ⟨-, -, Hb, -, ELb, ERb⟩ := h.facts hb
  rw [chPr_iff] at hpj ⊢
  refine ⟨ha, ?_⟩
  obtain ⟨-, hpj⟩ := hpj
  have hle' := hle
  zucys
  · omega
  rcases hpj with h1 | ⟨h1, h2, h3⟩
  · omega
  right
  have hx := chLe_xv ELa.good ELb.good hle' hh
  have hA' : chH m V a = V.hz := by_omega
  rw [hA'] at ELa ERa hx
  zvmwp at ELb ERb hx Hb
  refine ⟨hA', ?_, ?_⟩
  · intro hσ hg
    apply h2 hσ
    zufqx
    · simp_all
    have hd := chord_disjoint h ha hb hab hh by_simp_all
    rw [hA', h1] at hd
    exact endGtZ_mono ERa.good ERb.good (by linarith [Hb.lt]) hg
  · intro hσ
    exact endLtZ_mono ELa.good ELb.good hx (h3 hσ)
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
open Chazelle.Chain (sideInArc)
@[expose] public section
def Bcut (r : ℕ) : Bool :=
  decide ztgll || decide ztglm || decide ztqvb ||
    decide zteuv || decide ztyc
theorem wrM_cutter : BuildRam.wrM Bcut cutter = true := by_decide

/-- The real registers the arc-cutter writes: bands `1, 5, 14, 15`. -/
def BcutR (r : ℕ) : Bool :=
  decide ztgll || decide ztglm || decide ztqvb ||
    decide zteuv
theorem wrM2_cutter : BuildRam.wrM2 Bcut BcutR cutter = true := by_decide
variable {r : ℕ} {m : ℕ → ℕ} {B : ℕ} {Q : Polygon}
theorem BcutR_false (hr : bandOf r ∉ oracleBands) : BcutR r = false := by
  zuli

  unfold BcutR
  grind
theorem chainModel_ne_interior' (C : Chain) (Q : Polygon) : chainModel C ≠ interiorModel Q := by
  zuq
  have := congrArg (fun M : Model => M.counted 0) h
  zuckl

/-- The model descriptor of a chain model holds a chain descriptor. -/
theorem modelDesc_chain {M : Model} {C : Chain}
    (h : ModelDescAt m B Q M) (hM : M = chainModel C) :
    m B = 0 ∧ ∃ H C', ChainDescAt m ztvf Q H C' ∧ M = chainModel C' := by
  zucim
  · grind
  · exact absurd ztmkt (chainModel_ne_interior' C Q)

/-- **A chain descriptor determines the chain.** -/
theorem chainDesc_unique {H H' : Host} {C C' : Chain}
    (h : ChainDescAt m B Q H C) (h' : ChainDescAt m B Q H' C') : C = C' := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  obtain ⟨h1', h2', h3', h4', -⟩ := h'
  have hH : H = H' := NFLoc.hostAt_unique h1 h1'
  zulsw
  zubkt

/-- The constant of the arc-cutter. -/
def κc : ℕ := 2500000
theorem Bcut_false (hr : bandOf r ∉ oracleBands) (ha : r ≠ ALLOC) : Bcut r = false := by
  zuli

  unfold Bcut
  have a1 : ztmwk := fun h => hr (h ▸ h1)
  have a5 : ztmwn := fun h => hr (h ▸ h5)
  have a14 : ztslk := fun h => hr (h ▸ h14)
  have a15 : ztmwl := fun h => hr (h ▸ h15)
  zujwp
  simp_all

/-- **The arc-cutter meets `CutterOK`.** -/
theorem cutter_ok (O : OracleIface) :
    CutterOK cutter oracleBands (fun γ => κc * ztxd) cutGran ztsy
      OkModel := by
  zulq
  obtain ⟨hG, hHW, hX, hcap, hMDWF, M, hMD, hOk, hsP, heP, hs1, he1, -, hin2, hwt⟩ := hpre
  -- the inputs
  set MD := c.nreg 150000 with hMDd
  set γ := c.nreg 150009 with hγd
  set h := c.nreg 150013 with hhd
  zuce
  zudvs
  set s : WPos := ⟨c.nreg 150001, c.nreg 150002⟩ with hsd
  set e : WPos := ⟨c.nreg 150003, c.nreg 150004⟩ with hed
  zublq

  zure

  zucpf

  replace hcost : A₀ + κc * ztxd ≤ W := hcost
  -- the chain
  zush

  obtain ⟨hD5, hwfC⟩ := hwf6 h0
  obtain ⟨hlen, hHwf, hHA, hsC⟩ := hwfC H C hD
  zuers
  zuhwi
  zucwl
  zujjm
  have S : SEnv O P C H (m₀ ztki) h γ m₀ A₀ W :=
    ⟨hD.2.1, hD.1, hHA, hHwf, hlen, hsC, hX, hcap, hAW, hHW, by_omega, hG⟩
  have hin : e.hgt = 0 ∨ (chainModel C).InnerPt ztwyx := hin2
  -- `2 γ ≤ W`
  have hγW : ztsac := by
    zubjc

    grind
  zukdd
  have hκ : κc = 2500000 := rfl
  -- the set-up
  obtain ⟨c₁, k₁, Nmax, e₁, hk₁, hI₁, hlt, fr₁, m₁⟩ := cutInit_exec (P := P) c hw (m₀ := m₀)
    ztcve rfl rfl hγW by_grind
  have g₁ : ∀ x, 150000 ≤ x → x < 150100 → c₁.nreg x = c.nreg x := fun x h1 h2 =>
    fr₁ x by_omega
  -- the core
  obtain ⟨c₂, k₂, ps, e₂, hk₂, hI₂, arc, hok, hl, hm₂⟩ := core_exec S (cutEmit_ok S _)
    (ps₀ := []) (MD := MD) (mode := c.nreg 150020) (s := s) (e := e) hD
    by_omega rfl c₁ e₁.wb_right ztfrk ztczq
    ztczq ztczq ztczq
    ztczq ztczq ztczq
    ztczq hI₁ hsP heP hs1 he1 hin hwt
  rw [List.nil_append] at hI₂
  zuhzz
  -- the finish
  obtain ⟨c₃, k₃, e₃, hk₃, o10, om, omo, oA, oAk, or₃, orr, orm, oo⟩ :=
    cutFin_exec (P := P) c₂ e₂.wb_right hI₂ hq
  have ex : Exec P W cutter c c₃ ztxee := by
    unfold cutter; exact .seq e₁ ztcr
  have fM := BuildRam.exec_frameM ex wrM_cutter
  have fR := BuildRam.exec_frameM2 ex wrM2_cutter
  have hA₂ : ztlyc := hI₂.alloc
  have hrec := hI₂.recs
  rw [List.take_of_length_le hq] at hrec
  have hne := arc.ne
  have hpos : 0 < ps.length := List.length_pos_of_ne_nil hne
  refine ⟨c₃, k₁ + zttl, ex, ?_, ?_, ?_⟩
  · -- the cost
    show k₁ + zttl ≤ κc * ztxd
    unfold coreCost genCost at hk₂
    grind
  · -- the pieces
    intro M' hM'
    have hM'C : ztulm := by
      zuctl
      · zuijb
      omega
    subst hM'C
    have hL : rd c₃ bCut 10 = A₀ := o10
    have hq3 : c₃.nmem A₀ = ps.length := om
    have hpc : ∀ a, A₀ < a → c₃.nmem a = c₂.nmem a := fun a ha => omo a by_omega
    have hm₃ : ∀ a, a < A₀ → c₃.nmem a = m₀ a := fun a ha => by
      grind
    -- the words of the records
    have w0 : ∀ i (hi : i < ps.length), c₃.nmem ztldw = (ps[i]'hi).s.edge :=
      fun i hi => by rw [hpc _ by_omega, Nat.add_zero]; exact (hrec i hi).1
    have w1 : ∀ i (hi : i < ps.length), c₃.nmem ztldx = (ps[i]'hi).s.hgt :=
      fun i hi => by zungu; exact (hrec i hi).2.1
    have w2 : ∀ i (hi : i < ps.length), c₃.nmem ztldy = (ps[i]'hi).e.edge :=
      fun i hi => by zungu; exact (hrec i hi).2.2.1
    have w3 : ∀ i (hi : i < ps.length), c₃.nmem ztldz = (ps[i]'hi).e.hgt :=
      fun i hi => by zungu; exact (hrec i hi).2.2.2.1
    have w4 : ∀ i (hi : i < ps.length), c₃.nmem (A₀ + 1 + 7 * i + 4) = (ps[i]'hi).kind :=
      fun i hi => by zungu; exact (hrec i hi).2.2.2.2.1
    have w56 : ∀ i (hi : i < ps.length), (ps[i]'hi).kind = 1 →
        c₃.nmem ztlea = c₃.nmem (ps[i]'hi).entry ∧
        c₃.nmem ztleb = c₃.nmem ztfau := fun i hi hk => by
      have he := entry_lt S ztzwc hk
      obtain ⟨b5, b6⟩ := (hrec i hi).2.2.2.2.2 hk
      rw [hpc ztlea by_omega, hpc ztleb by_omega, b5, b6,
        hm₃ (ps[i]'hi).entry by_omega, hm₃ ztfau by_omega]
      omega
    have kS : ∀ i (hi : i < ps.length), (chainModel C).key zta
        ⟨c₃.nmem ztldw, c₃.nmem ztldx⟩ =
        (chainModel C).key zta (ps[i]'hi).s := fun i hi => by rw [w0 i hi, w1 i hi]
    have kE : ∀ i (hi : i < ps.length), (chainModel C).key zta
        ⟨c₃.nmem ztldy, c₃.nmem ztldz⟩ =
        (chainModel C).key zta (ps[i]'hi).e := fun i hi => by rw [w2 i hi, w3 i hi]
    zubvt
    rw [hL, hq3]
    refine ⟨le_rfl, by rw [oA], ?_, hpos, ?_, ?_, fun i hi => ?_, fun i hi => ?_,
      fun i hi hk => ?_, fun i hi hk => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · show ps.length ≤ κc * ztxd
      rw [hκ]; linarith
    · rw [kS 0 hpos]
      have : (ps[0]'hpos) = ps.head hne := (List.head_eq_getElem hne).symm
      rw [this, arc.hs]; rfl
    · rw [kE _ by_omega]
      have : (ps[ps.length - 1]' by_omega) = ps.getLast hne := (List.getLast_eq_getElem hne).symm
      rw [this, arc.he]; rfl
    · rw [kE i by_omega, kS ztg hi, arc.ch i hi]
    · rw [kS i by_omega, kE i by_omega]
      exact arc.e6 i hi
    · rw [kS i hi, kE i hi]
      have hk' : (ps[i]'hi).kind = 0 := by zuogf; exact hk
      exact (hok _ ztdyp).2.2.2.2.2.1 hk'
    · have hk' : (ps[i]'hi).kind = 1 := by zuogf; exact hk
      obtain ⟨b5, b6⟩ := w56 i hi hk'
      rw [kS i hi, kE i hi, b5, b6, w0 i hi, w1 i hi, w2 i hi, w3 i hi]
      have := kind1_facts ztzwc hk' hX hm₃ (A' := c₃.nreg ALLOC)
        by_omega
      zufep
    · have hp := hok _ ztdyp
      rw [w0 i hi, w1 i hi, w2 i hi, w3 i hi, hnW]
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
    · rw [w4 i hi]
      rcases (hok _ ztdyp).2.2.2.2.1 with h | h <;> omega
  · -- the frame
    refine ⟨fun r hr ha => fM.1 r (Bcut_false hr ha), fun r hr => fR r (BcutR_false hr),
      fun a ha => ?_, fun a _ => by rw [fM.2.2.1], fM.2.2.2, by_omega, ?_⟩
    · grind
    grind
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
def shPro : Stmt := block (copies [ztsrw, ztsry, ztsrz,
  ztssa, ztssb, ztssc, ztsse])

/-- The piece records. -/
def shPh : Stmt := .seq shInit (.seq (core shEmit) shFin)

/-- The answer. -/
def shEpi : Stmt := block [.copyN 140010 140210, .copyN 140011 140215, .copyN 140012 140216]

/-- **The ray-shooter.** -/
def shooter (query : Stmt) : Stmt :=
  .seq shPro (.seq orig (.seq shPh (.seq (shLoop query) shEpi)))

/-- The registers written by the piece records: bands `1, 5, 15`, the record registers and the
allocator. -/
def Bph (r : ℕ) : Bool :=
  decide ztgll || decide ztglm || decide zteuv ||
    decide (140100 ≤ r ∧ r < 140110) || decide ztyc
theorem wrM_shPh : BuildRam.wrM Bph shPh = true := by_decide

/-- The real registers written by the piece records: bands `1, 5, 15`. -/
def BphR (r : ℕ) : Bool :=
  decide ztgll || decide ztglm || decide zteuv
theorem wrM2_shPh : BuildRam.wrM2 Bph BphR shPh = true := by_decide
variable {r : ℕ}
theorem BphR_false (hr : bandOf r ∉ oracleBands) : BphR r = false := by
  have h1 : ztfzq := by_decide
  have h5 : ztfzs := by_decide
  have h15 : ztfzr := by_decide
  unfold bandOf at hr
  zufew

  zujwm
  simp only [BphR, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

/-! ## Small facts -/
theorem originIn_unique {c : Config} {r : ℕ} {o o' : Origin} (h : OriginIn c r o)
    (h' : OriginIn c r o') : o = o' := by
  cases o with
  | sym s =>
    cases o' with
    | sym s' =>
      cases s with
      | vtx i =>
        cases s' with
        | vtx i' => obtain ⟨a, b⟩ := h; obtain ⟨a', b'⟩ := h'; rw [← b, ← b']
        | onEdge e' h'' => obtain ⟨a, -⟩ := h; obtain ⟨a', -⟩ := h'; omega
      | onEdge e hh =>
        cases s' with
        | vtx i' => obtain ⟨a, -⟩ := h; obtain ⟨a', -⟩ := h'; omega
        | onEdge e' h'' =>
          obtain ⟨-, b, d⟩ := h; obtain ⟨-, b', d'⟩ := h'; zuniy
    | walk x =>
      obtain ⟨a', -⟩ := h'
      cases s with
      | vtx i => obtain ⟨a, -⟩ := h; omega
      | onEdge e hh => obtain ⟨a, -⟩ := h; omega
  | walk x =>
    cases o' with
    | sym s' =>
      obtain ⟨a, -⟩ := h
      cases s' with
      | vtx i => obtain ⟨a', -⟩ := h'; omega
      | onEdge e hh => obtain ⟨a', -⟩ := h'; omega
    | walk x' =>
      obtain ⟨-, b, d⟩ := h; obtain ⟨-, b', d'⟩ := h'
      zuebn
      obtain ⟨xe', xh'⟩ := x'
      simp only at b d b' d'
      zuniy
theorem one_le_rpowCeil (γ : ℕ) : 1 ≤ rpowCeil ztwku ztby := by
  have h1 : ztujx := by
    zumsg

  have h2 : ztytw := by_grind
  zuluv

/-- The constant of the ray-shooter. -/
def κs (O : OracleIface) : ℕ := 18900 * ztgcf + 3000000

/-- The step bound of the loop. -/
theorem loop_budget {κO T R q : ℕ} (hR : 1 ≤ R) (hqT : q ≤ 2100 * T) :
    9 * q * ztyth ≤ 18900 * ztdkm * zthcq := by
  have hKR : ztycz := by
    zuhvh

  have := Nat.mul_le_mul zttaz hKR
  grind

/-- **The step bound of the ray-shooter.** -/
theorem shooter_cost {κO T L R q k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℕ} (hR : 1 ≤ R) (hLT : L + 1 ≤ T)
    (hq : q ≤ 2100 * ztgt) (h1 : k₁ ≤ 7) (h2 : k₂ ≤ 16000) (h3 : k₃ ≤ 5 * ztnpt + 20)
    (h4 : k₄ ≤ 1100 * ((2 * 30 + 90) * ztgt + 1702) + 2 * 30 + 20000 + 30 + 20000)
    (h5 : k₅ ≤ 3 * (1 + 9 * q) + 2)
    (h6 : k₆ ≤ 9 * q * ztyth + 20) (h7 : k₇ ≤ 3) :
    k₁ + (k₂ + (k₃ + ztjzr + ztjzs)) ≤
      ztzas * T * R + ztzas := by
  have hKR : ztycz := by
    zuhvh

  have hqT : ztsli := by_omega
  have h6' : k₆ ≤ 9 * (2100 * T) * (ztdkm * R) + 20 := by
    have := Nat.mul_le_mul zttaz hKR
    omega
  have hTR : ztscp := Nat.le_mul_of_pos_right _ hR
  grind
theorem originIn_of_eq {c c' : Config} {r : ℕ} {o : Origin} (h : OriginIn c r o)
    (he : ∀ j, r ≤ j → j < r + 3 → c'.nreg j = c.nreg j) : OriginIn c' r o := by
  cases o with
  | sym s => exact symPtIn_of_eq h he
  | walk x =>
    obtain ⟨a, b, d⟩ := h
    exact ⟨by_simp_all, by_simp_all,
      by simp_all⟩
theorem Borg_ob (r : ℕ) (h : Borg r = true) :
    ztbav ∧ r ≠ ALLOC := by
  simp only [Borg, Bld, Bprim, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  zuhai
theorem Bph_false (hr : bandOf r ∉ oracleBands) (ha : r ≠ ALLOC) : Bph r = false := by
  zuli

  zufew

  have a14 : ztslk := by_grind
  zujwm
  zujwp
  zunwv
  omega

/-- **The ray-shooter meets `ShooterOK`.** -/
theorem shooter_ok {O : OracleIface} (hV : O.Valid) :
    ShooterOK ztwdu oracleBands
      (fun γ => κs O * ztxd * rpowCeil ztwku ztby +
        κs O) (gradeCtx O) OkModel := by
  zulq
  obtain ⟨hG, hHW, hX, hcap, hMDWF, hG10, M, hMD, hOk, hsP, heP, hs1, he1, hin1, hin2, hwt, o,
    hoLt, hoIn, hoK, hzA⟩ := hpre
  set MD := c.nreg 140000 with hMDd
  set γ := c.nreg 140009 with hγd
  set h := c.nreg 140013 with hhd
  zuce
  zudvs
  set s : WPos := ⟨c.nreg 140001, c.nreg 140002⟩ with hsd
  set e : WPos := ⟨c.nreg 140003, c.nreg 140004⟩ with hed
  set R := rpowCeil ztwku ztby with hRd
  set σ := dirOf ztghb with hσd
  zublq

  replace hG10 : m₀ MD = 0 → ∀ H C, ChainDescAt m₀ ztki zta H C →
      HostRegular (Qof P).n H := hG10
  zure

  replace hin1 : s.hgt = 0 ∨ M.InnerPt (M.pos zta s) := hin1
  zucpf

  replace hoIn : OriginIn c 140005 o := hoIn
  replace hzA : o.eval M zta ∉ M.arcSet ztypg ztypd := hzA
  replace hcost : A₀ + (κs O * ztxd * R + κs O) ≤ W := hcost
  -- the chain
  zush

  have hwfC := hwf6 h0
  obtain ⟨hlen, hHwf, hHA, hsC⟩ := hwfC.2 H C hD
  have hn3 := Chazelle.Jordan.simple_three_le hG.1
  zuhwi
  zulkt
  zujjm
  have S : SEnv O P C H _ h γ m₀ A₀ W :=
    ⟨hD.2.1, hD.1, hHA, hHwf, hlen, hsC, hX, hcap, hAW, hHW, by_omega, hG⟩
  zuerk
  zuc
  have hreg : ∀ H', HostAt m₀ _ H' → HostRegular P.n H' := fun H' hH' => by
    have := NFLoc.hostAt_unique hD.1 hH'
    grind
  have hγW : ztsac := by
    zubjc

    omega
  zukdd
  have hR1 := one_le_rpowCeil γ
  set T := Nat.clog 2 γ + 1 with hT
  have hTR : ztscp := Nat.le_mul_of_pos_right _ hR1
  have hκ : κs O = 18900 * ztgcf + 3000000 := rfl
  have hbig : 3000000 * T ≤ κs O * T * R := by
    have a : 3000000 * T ≤ κs O * T := Nat.mul_le_mul_right _ by_omega
    have b : κs O * T ≤ κs O * T * R := Nat.le_mul_of_pos_right _ hR1
    omega
  have hκ3 : 3000000 ≤ κs O := by_omega
  -- the inputs of the core
  obtain ⟨c₁, e₁, v₁, k₁, rr₁, m₁, rm₁, o₁⟩ := copies_exec (P := P) (W := W)
    [ztsrw, ztsry, ztsrz, ztssa, ztssb,
      ztssc, ztsse] c hw by_decide
      by_simp
  zutx
  obtain ⟨v00, v01, v02, v03, v04, v09, v13⟩ := v₁
  have g₁ := fun r hr =>
    k₁ r ztbaw
  have ex₁ := e₁
  have fb₁ : FrameB (fun r => decide zteuv) c c₁ :=
    ⟨fun r hr => g₁ r by_grind, fun r _ => by zunkd, m₁, rm₁, o₁⟩
  -- the origin
  have hoIn₁ : OriginIn c₁ 140005 o :=
    originIn_of_eq hoIn fun j h1 h2 => g₁ j by_omega
  have q00 : c₁.nreg 140000 = MD := by_grind
  have qA := g₁ ALLOC by_decide
  have hD₁ : ChainDescAt c₁.nmem ztlml zta H C := by_grind
  have hwf₁ : ChainWF P ztbmq c₁.nmem ztlml := by
    grind
  have hreg₁ : ∀ H', HostAt c₁.nmem (c₁.nmem ztlml) H' → HostRegular P.n H' := by
    grind
  have hroom₁ : c₁.nreg ALLOC + 15800 ≤ W := by_omega
  have hMD₁ : c₁.nreg 140000 + 1 ≤ W := by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, E₂, Og₂, f₂, h403⟩ := orig_exec (P := P) (W := W) (H := H) (C := C)
    c₁ e₁.wb_right hG hHW hD₁ hwf₁ hreg₁ hoIn₁ hoLt hoK hroom₁ hMD₁
  rw [g₁ _ by_norm_num] at E₂ Og₂
  have k₂' := f₂.1
  have mem₂ : c₂.nmem = m₀ := by zunoe
  have A₂ : ztlyc := by rw [k₂' _ by_decide, g₁ ALLOC by_decide]
  -- the set-up of the records
  obtain ⟨c₃, k₃, Nmax, e₃, hk₃, hI₃, hNmax, r₃, m₃, rr₃, rm₃, o₃⟩ := shInit_exec (P := P) c₂
    e₂.wb_right (m₀ := m₀) ztqnh (by rw [k₂' _ by_decide, v09]) A₂ hγW
    (by
      omega)
  have g₃ : ∀ r, 150000 ≤ r → r < 150100 → c₃.nreg r = c₁.nreg r := fun r a b => by
    rw [r₃ r by_omega]
    have hb : Borg r = false := by
      simp only [Borg, Bld, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne]; omega
    grind
  -- the core
  obtain ⟨c₄, k₄, ps, e₄, hk₄, hI₄, arc, hok, hl, hm₄⟩ := core_exec S
    (shEmit_ok (c₀ := c₂) ztbwt Nmax) (ps₀ := []) (MD := MD)
    (mode := c₃.nreg 150020) (s := s) (e := e) hD by_omega rfl c₃ e₃.wb_right
    ztqnh by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind rfl hI₃ hsP heP hs1 he1 hin2 hwt
  rw [List.nil_append] at hI₄
  zuhzz
  -- the finish of the records
  obtain ⟨c₅, k₅, e₅, hk₅, a₅, aψ, r₅, m₅⟩ := shFin_exec (P := P) c₄ e₄.wb_right hI₄ hq
  have mem₅ : ztpnw := by zunjy
  have exph : Exec P W shPh c₂ c₅ ztlg := by unfold shPh; exact .seq e₃ ztgxe
  have FM := BuildRam.exec_frameM exph wrM_shPh
  have hA₄ := hI₄.alloc
  have hmem₅ : ztknz := fun a ha => by zupbl; exact hm₄ a ha
  have Fph : Frame oracleBands c₂ c₅ ztlg :=
    ⟨fun r hr ha => FM.1 r (Bph_false hr ha),
      fun r hr => BuildRam.exec_frameM2 exph wrM2_shPh r (BphR_false hr), fun a ha => by zuobd,
      fun a _ => by rw [FM.2.2.1], FM.2.2.2, by_omega, by_omega⟩
  -- the loop
  set q := ps.length with hqd
  set K := O.κ * ztza + 600500 with hKd
  have hlq : ztsli := by_omega
  have hlb : 9 * q * ztnu ≤ 18900 * ztgcf * zthcq :=
    loop_budget hR1 hlq
  have hsplit : κs O * T * R = 18900 * ztgcf * zthcq + 3000000 * zthcq := by
    grind
  have hTR' : 1 + 9 * q ≤ 3000000 * zthcq := by
    omega
  zufgc
  have hsin : s.hgt = 0 ∨ |((chainModel C).pos zta s).2| < C.radius := by
    rcases hin1 with h' | h'
    · omega
    · zuhtz
  have hein : e.hgt = 0 ∨ |((chainModel C).pos zta e).2| < C.radius := by
    rcases hin2 with h' | h'
    · omega
    · zuhtz
  have X : LpCtx O P W C _ m₀ h γ A₀ s e ps :=
    ⟨hV, arc, hok, hsP, heP, hs1, he1, hsin, hein, hwt, hzA, hX, hQs, by
      unfold hostWords at hHW; omega⟩
  have kph := FM.1
  have kenv : ∀ r, envR r → r ≠ ALLOC → c₅.nreg r = c₂.nreg r := fun r hr ha => by
    have hb : ztukg := by
      unfold envR at hr; unfold ALLOC at ha
      simp only [Bph, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega
    zulzd
  have E₅ : ShEnv P W H C _ σ c₅ := E₂.of_agree kenv
    (fun a ha => by zuobd) by_omega
  have korg : ∀ r, 140234 ≤ r → r < 140241 → c₅.nreg r = c₂.nreg r := fun r a b => by
    have hb : ztukg := by
      zunwv; omega
    zulzd
  have Og₅ := Og₂.keep korg
  have h08₅ : dirOf (c₅.nreg 140008) = σ := by
    rw [kph _ by_decide, k₂' _ by_decide, g₁ _ by_norm_num]
  obtain ⟨c₆, k₆, e₆, hk₆, hB₆, F₆, E₆⟩ := shLoop_exec (H := H) (σ := σ) (K := K) X le_rfl c₅
    e₅.wb_right E₅ Og₅ h08₅
    (by rw [r₅ _ by_decide, hI₄.ptr, min_eq_left hq])
    (by rw [r₅ _ by_decide]; exact hI₄.base)
    (by zupbl; have := hI₄.recs; rwa [List.take_of_length_le hq] at this)
    hmem₅ (by zuoxy) by_grind
  -- the answer
  obtain ⟨c₇, k₇, e₇, hk₇, u10, u11, u12, r₇, m₇⟩ : ∃ c₇ k₇, Exec P W shEpi c₆ c₇ k₇ ∧ k₇ = 3 ∧
      c₇.nreg 140010 = c₆.nreg 140210 ∧ c₇.nreg 140011 = c₆.nreg 140215 ∧
      c₇.nreg 140012 = c₆.nreg 140216 ∧
      (∀ r, r ≠ 140010 → r ≠ 140011 → r ≠ 140012 → c₇.nreg r = c₆.nreg r) ∧
      c₇ = { c₆ with nreg := c₇.nreg } := by
    zujb
    unfold shEpi
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, fun r h1 h2 h3 => ?_, rfl⟩
    zufcb
  have F₇ : Frame oracleBands c₆ c₇ k₇ := by
    refine ⟨fun r hr ha => r₇ r ?_ ?_ ?_, fun r _ => by zungk, fun a _ => by zungk,
      fun a _ => by zungk, by zungk, by zuobe,
      by zuobe; omega⟩
    all_goals intro hr'; subst hr'; exact hr by_decide
  have ex : Exec P W ztwdu c c₇ (7 + ztyrg) := by
    unfold shooter; exact .seq ex₁ (.seq e₂ (.seq exph (.seq e₆ e₇)))
  have hkt : 7 + ztyrg ≤ κs O * T * R + κs O := by
    have := shooter_cost (T := T) (k₃ := k₃) (k₄ := k₄) (k₇ := k₇) hR1
      by_omega hl le_rfl hk₂ by_omega (by unfold coreCost genCost at hk₄; omega)
      hk₅ by_omega by_omega
    zukwq
  refine ⟨c₇, _, ex, hkt, ?_, ?_⟩
  · -- the answer
    intro M' o' hM' hO'
    have hM'C : ztulm := by
      zuctl
      · zuijb
      omega
    subst hM'C
    have ho := originIn_unique hO' hoIn
    subst ho
    have hAeq : psSet C _ ps = (chainModel C).arcSet _
        _ :=
      (arcSet_pieces arc zttqx zttqw
        (fun q hq => pcOK_keys (hok q hq))).symm
    rw [hAeq] at hB₆
    obtain ⟨-, hb1, hb2⟩ := hB₆
    refine ⟨fun hf => ?_, fun hf => hb1 (by zuotb; exact hf)⟩
    have hf' : c₆.nreg 140210 = 1 := by zuotb; exact hf
    obtain ⟨x, -, hF, hpp, hlt, hpos⟩ := hb2 hf'
    refine ⟨σ * (x - (o'.eval _ _).1), hF, ?_, ?_, ?_⟩
    · show ProperPos _ _ P.n ztrcb
      rw [u11, u12]; omega
    · show c₇.nreg 140011 < (chainModel C).W.n
      rw [u11]; omega
    · show (chainModel C).pos _ ztrcb =
        Visibility.rayPt _ σ
          _
      rw [u11, u12, hpos]
      have hσ' : ztim := E₂.hσ
      ext
      · simp only [Visibility.rayPt_fst]
        rcases hσ' with hs | hs <;> zvmyz <;> ring
      simp
  · -- the frame
    have F₁ : Frame oracleBands c c₁ 7 := frame_of_frameB fb₁ (fun r hr =>
      ⟨by simp at hr; unfold bandOf; zvnel; decide, by simp at hr; unfold ALLOC; omega⟩) 7
    have F₂ := frame_of_frameB f₂ (fun r hr =>
      ⟨oracleBands_mem r (by have := (Borg_ob r hr).1; omega), (Borg_ob r hr).2⟩) k₂
    have F := F₁.trans (F₂.trans (Fph.trans ztuyw))
    zujnn
    exact F
theorem cutterOK_mono {cu : Stmt} {B : Finset ℕ} {G G' H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hc : CutterOK cu B G H X Ok) (hG : ∀ γ, G γ ≤ G' γ) :
    CutterOK cu B G' H X Ok := by
  zulq
  obtain ⟨c', k, ex, hk, post, fr⟩ := hc P W c hw hpre (by
    grind)
  refine ⟨c', k, ex, le_trans hk ztmkr, fun M hM => ?_, fr⟩
  obtain ⟨a, b, c3, rest⟩ := post M hM
  exact ⟨a, b, le_trans c3 ztmkr, rest⟩

/-- **WP-G.** -/
theorem shootCutSpec (O : OracleIface) (hV : O.Valid) : ShootCutSpec O := by
  refine ⟨shooter O.query, cutter, κs O, shooter_ok hV, cutterOK_mono (cutter_ok O) ?_⟩
  intro γ
  have : κc ≤ κs O := by unfold κc κs; omega
  simp_all
end
end ShootCut
end Chazelle.Core
section
set_option hygiene false
local macro "zqbml" : tactic => `(tactic| exact ⟨d', k, ex, hI, by_omega⟩)
local macro "zqbmm" : tactic => `(tactic| (refine ⟨d', k, ex, ⟨ex.wb_right, hR.body hf, h38', fun a => ?_⟩, by_omega⟩
                                           rw [hm', Machine.upd_apply, hm]))
set_option hygiene true

/-!
# Down-phase driver (RAM side): the bucket distribution (a counting sort)

`bktS` distributes the `n` new event codes `base + q` (`q < n`) by their buckets
`bk q = m (BB + q) ≤ A` (a counting sort, `O(n + A)` steps).  Registers (band `bDownDrv`):
inputs `210022` (`BB`), `210031` (`n`), `210032` (`A`), `210033` (`base`); constants `210034`
(`1`), `210035` (`0`), `210039` (`A + 1`); the fresh arrays `C = 210036` (`A + 1` counters, at
the entry allocator `A₀`), `S = 210037` (`A + 1` bucket starts), `R = 210048` (`n` codes); the
counter `210038`, the running sum `210044`, scratch `210040 … 210047`.

**`bktS_exec`**: `seg R n = bktList bk n A base` (`DownPhaseDrvRBktM`), `S[b] = bstart b`,
`C[b] = bstart (b + 1)`, memory below `A₀` unchanged, cost `≤ 21 (A + 1) + 21 n + 30`.
-/
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam
@[expose] public section
def bkInit : Stmt :=
  block [.constN 210034 1, .constN 210035 0, .copyN 210036 9999, .addN 210039 210032 210034,
    .addN 210037 210036 210039, .addN 210048 210037 210039, .addN 9999 210048 210031,
    .constN 210038 0]

/-- Clear the counters. -/
def bkL1 : Stmt :=
  .whileLtN 210038 210039
    ztgqs

/-- Count. -/
def bkL2 : Stmt :=
  .whileLtN 210038 210031
    (block [.addN 210040 210022 210038, .loadN 210041 210040, .addN 210042 210036 210041,
      .loadN 210043 210042, .addN 210043 210043 210034, .storeN 210042 210043,
      .addN 210038 210038 210034])

/-- Prefix sums: `C[b] := S[b] := s`, `s := s + count`. -/
def bkL3 : Stmt :=
  .whileLtN 210038 210039
    (block [.addN 210040 210036 210038, .loadN 210041 210040, .storeN 210040 210044,
      .addN 210042 210037 210038, .storeN 210042 210044, .addN 210044 210044 210041,
      .addN 210038 210038 210034])

/-- Place: `R[C[bk q]] := base + q`, `C[bk q] += 1`. -/
def bkL4 : Stmt :=
  .whileLtN 210038 210031
    (block [.addN 210040 210022 210038, .loadN 210041 210040, .addN 210042 210036 210041,
      .loadN 210043 210042, .addN 210046 210048 210043, .addN 210047 210033 210038,
      .storeN 210046 210047, .addN 210043 210043 210034, .storeN 210042 210043,
      .addN 210038 210038 210034])

/-- **The bucket distribution.** -/
def bktS : Stmt :=
  .seq bkInit (.seq bkL1 (.seq ztifw (.seq bkL2
    (.seq ztfbj (.seq bkL3
      (.seq ztifw bkL4))))))

/-- The registers the loop bodies write. -/
def Bbody (r : ℕ) : Bool := decide (r = 210038) || decide (210040 ≤ r ∧ r ≤ 210047)

/-- The registers `bktS` writes. -/
def Bbkt (r : ℕ) : Bool := decide (210034 ≤ r ∧ r ≤ 210048) || decide ztyc

/-! ## The invariants -/

/-- The registers during the loops (relative to the entry configuration `c₀`). -/
structure BkR (c₀ : Config) (BB n A base A₀ : ℕ) (d : Config) : Prop where
  r22 : d.nreg 210022 = BB
  r31 : d.nreg 210031 = n
  r32 : d.nreg 210032 = A
  r33 : d.nreg 210033 = base
  r34 : d.nreg 210034 = 1
  r35 : d.nreg 210035 = 0
  r36 : d.nreg 210036 = A₀
  r37 : d.nreg 210037 = A₀ + ztbo
  r39 : d.nreg 210039 = A + 1
  r48 : d.nreg 210048 = A₀ + ztbo + ztbo
  fr : ∀ r, Bbkt r = false → d.nreg r = c₀.nreg r
  alloc : d.nreg ALLOC = A₀ + ztbo + ztbo + n
  rr : ∀ r, Bbkt r = false → d.rreg r = c₀.rreg r
  rm : d.rmem = c₀.rmem
  out : d.output = c₀.output
theorem Bbody_imp {r : ℕ} (h : Bbody r = true) : Bbkt r = true := by
  simp only [Bbody, Bbkt, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega

/-- The register facts survive a body (its writes are in `Bbody`). -/
theorem BkR.body {c₀ d d' : Config} {BB n A base A₀ : ℕ} (h : BkR c₀ BB n A base A₀ d)
    (hf : FrameM Bbody d d') : BkR c₀ BB n A base A₀ d' := by
  have e := hf.1
  refine ⟨(e _ by_decide).trans h.r22, (e _ by_decide).trans h.r31,
    (e _ by_decide).trans h.r32, (e _ by_decide).trans h.r33, (e _ by_decide).trans h.r34,
    (e _ by_decide).trans h.r35, (e _ by_decide).trans h.r36, (e _ by_decide).trans h.r37,
    (e _ by_decide).trans h.r39, (e _ by_decide).trans h.r48, fun r hr => ?_,
    (e _ by_decide).trans h.alloc, fun r hr => ?_, hf.2.2.1.trans h.rm, hf.2.2.2.trans h.out⟩
  · have hb : ztuke := by
      cases hh : Bbody r
      · rfl
      · zuhju
    exact (e r hb).trans (h.fr r hr)
  · have hb : ztuke := by
      cases hh : Bbody r
      · rfl
      · zuhju
    exact (hf.2.1 r hb).trans (h.rr r hr)
theorem wrM_L1 : wrM Bbody
    ztgqs =
      true := by_decide
theorem wrM_L2 : wrM Bbody
    (block [.addN 210040 210022 210038, .loadN 210041 210040, .addN 210042 210036 210041,
      .loadN 210043 210042, .addN 210043 210043 210034, .storeN 210042 210043,
      .addN 210038 210038 210034]) = true := by_decide
theorem wrM_L3 : wrM Bbody
    (block [.addN 210040 210036 210038, .loadN 210041 210040, .storeN 210040 210044,
      .addN 210042 210037 210038, .storeN 210042 210044, .addN 210044 210044 210041,
      .addN 210038 210038 210034]) = true := by_decide
theorem wrM_L4 : wrM Bbody
    (block [.addN 210040 210022 210038, .loadN 210041 210040, .addN 210042 210036 210041,
      .loadN 210043 210042, .addN 210046 210048 210043, .addN 210047 210033 210038,
      .storeN 210046 210047, .addN 210043 210043 210034, .storeN 210042 210043,
      .addN 210038 210038 210034]) = true := by_decide

/-! ## The bodies -/
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
theorem body1_exec (d : Config) (hw : WordsBounded W d) {j Cb : ℕ} (h36 : d.nreg 210036 = Cb)
    (h38 : d.nreg 210038 = j) (h34 : d.nreg 210034 = 1) (h35 : d.nreg 210035 = 0)
    (hW : Cb + j + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210040 210036 210038, .storeN 210040 210035,
      .addN 210038 210038 210034]) d d' k ∧ k = 3 ∧ d'.nreg 210038 = j + 1 ∧
      d'.nmem = upd d.nmem ztfng 0 ∧ FrameM Bbody d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W (block [.addN 210040 210036 210038,
      .storeN 210040 210035, .addN 210038 210038 210034]) d d' k ∧ k = 3 ∧
      d'.nreg 210038 = j + 1 ∧ d'.nmem = upd d.nmem ztfng 0 := by
    exec_block
    · omega
    · config_simp; omega
    simp_all
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_L1⟩
set_option maxHeartbeats 1000000 in
theorem body2_exec (d : Config) (hw : WordsBounded W d) {j Cb BB x v : ℕ}
    (h36 : d.nreg 210036 = Cb) (h22 : d.nreg 210022 = BB) (h38 : d.nreg 210038 = j)
    (h34 : d.nreg 210034 = 1) (hx : d.nmem ztjgt = x) (hv : d.nmem ztfnh = v)
    (hW1 : BB + j ≤ W) (hW2 : Cb + x ≤ W) (hW3 : v + 1 ≤ W) (hW4 : j + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210040 210022 210038, .loadN 210041 210040,
      .addN 210042 210036 210041, .loadN 210043 210042, .addN 210043 210043 210034,
      .storeN 210042 210043, .addN 210038 210038 210034]) d d' k ∧ k = 7 ∧
      d'.nreg 210038 = j + 1 ∧ d'.nmem = upd d.nmem ztfnh ztsp ∧ FrameM Bbody d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W (block [.addN 210040 210022 210038,
      .loadN 210041 210040, .addN 210042 210036 210041, .loadN 210043 210042,
      .addN 210043 210043 210034, .storeN 210042 210043, .addN 210038 210038 210034]) d d' k ∧
      k = 7 ∧ d'.nreg 210038 = j + 1 ∧ d'.nmem = upd d.nmem ztfnh ztsp := by
    exec_block
    all_goals try (config_simp; simp only [h22, h38, h36, h34, hx, hv]; omega)
    simp_all
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_L2⟩
set_option maxHeartbeats 1000000 in
theorem body3_exec (d : Config) (hw : WordsBounded W d) {j Cb Sb sv t : ℕ}
    (h36 : d.nreg 210036 = Cb) (h37 : d.nreg 210037 = Sb) (h38 : d.nreg 210038 = j)
    (h34 : d.nreg 210034 = 1) (h44 : d.nreg 210044 = sv) (ht : d.nmem ztfng = t)
    (_hne : Cb + j ≠ Sb + j)
    (hW1 : Cb + j ≤ W) (hW2 : Sb + j ≤ W) (hW3 : sv + t ≤ W) (hW4 : j + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210040 210036 210038, .loadN 210041 210040,
      .storeN 210040 210044, .addN 210042 210037 210038, .storeN 210042 210044,
      .addN 210044 210044 210041, .addN 210038 210038 210034]) d d' k ∧ k = 7 ∧
      d'.nreg 210038 = j + 1 ∧ d'.nreg 210044 = sv + t ∧
      d'.nmem = upd ztzoa zttcx sv ∧ FrameM Bbody d d' := by
  obtain ⟨d', k, ex, hk, h1, h2, h3⟩ : ∃ d' k, Exec P W (block [.addN 210040 210036 210038,
      .loadN 210041 210040, .storeN 210040 210044, .addN 210042 210037 210038,
      .storeN 210042 210044, .addN 210044 210044 210041, .addN 210038 210038 210034]) d d' k ∧
      k = 7 ∧ d'.nreg 210038 = j + 1 ∧ d'.nreg 210044 = sv + t ∧
      d'.nmem = upd ztzoa zttcx sv := by
    exec_block
    all_goals try (config_simp; simp only [h36, h37, h38, h34, h44, ht]; omega)
    simp_all
  exact ⟨d', k, ex, hk, h1, h2, h3, exec_frameM ex wrM_L3⟩
set_option maxHeartbeats 1000000 in
theorem body4_exec (d : Config) (hw : WordsBounded W d) {j Cb BB Rb base x v : ℕ}
    (h36 : d.nreg 210036 = Cb) (h22 : d.nreg 210022 = BB) (h38 : d.nreg 210038 = j)
    (h48 : d.nreg 210048 = Rb) (h33 : d.nreg 210033 = base)
    (h34 : d.nreg 210034 = 1) (hx : d.nmem ztjgt = x) (hv : d.nmem ztfnh = v)
    (_hne : Rb + v ≠ Cb + x)
    (hW1 : BB + j ≤ W) (hW2 : Cb + x ≤ W) (hW3 : Rb + v + 1 ≤ W) (hW4 : base + j ≤ W)
    (hW5 : j + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210040 210022 210038, .loadN 210041 210040,
      .addN 210042 210036 210041, .loadN 210043 210042, .addN 210046 210048 210043,
      .addN 210047 210033 210038, .storeN 210046 210047, .addN 210043 210043 210034,
      .storeN 210042 210043, .addN 210038 210038 210034]) d d' k ∧ k = 10 ∧
      d'.nreg 210038 = j + 1 ∧
      d'.nmem = upd ztity ztfnh ztsp ∧ FrameM Bbody d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W (block [.addN 210040 210022 210038,
      .loadN 210041 210040, .addN 210042 210036 210041, .loadN 210043 210042,
      .addN 210046 210048 210043, .addN 210047 210033 210038, .storeN 210046 210047,
      .addN 210043 210043 210034, .storeN 210042 210043, .addN 210038 210038 210034]) d d' k ∧
      k = 10 ∧ d'.nreg 210038 = j + 1 ∧
      d'.nmem = upd ztity ztfnh ztsp := by
    exec_block
    all_goals try (config_simp; simp only [h22, h38, h36, h34, h48, h33, hx, hv]; omega)
    simp_all
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_L4⟩

/-! ## The memory during the loops -/

/-- After the first `j` iterations of the first loop. -/
def mem1 (m₀ : ℕ → ℕ) (A₀ j a : ℕ) : ℕ := if A₀ ≤ a ∧ a < A₀ + j then 0 else m₀ a

/-- During the second loop. -/
def mem2 (m₀ bk : ℕ → ℕ) (A₀ A j a : ℕ) : ℕ :=
  if A₀ ≤ a ∧ a < A₀ + ztbo then bcnt bk j zthdi else m₀ a

/-- During the third loop. -/
def mem3 (m₀ bk : ℕ → ℕ) (n A₀ A j a : ℕ) : ℕ :=
  if A₀ ≤ a ∧ a < A₀ + ztbo then
    (if a - A₀ < j then bstart bk n zthdi else bcnt bk n zthdi)
  else if A₀ + ztbo ≤ a ∧ a < A₀ + ztbo + j then bstart bk n ztyqa
  else m₀ a

/-- The two arrays during the fourth loop. -/
def memCS (m₀ bk : ℕ → ℕ) (n A₀ A j a : ℕ) : ℕ :=
  if A₀ ≤ a ∧ a < A₀ + ztbo then bstart bk n zthdi + bcnt bk j zthdi
  else if A₀ + ztbo ≤ a ∧ a < A₀ + ztbo + ztbo then bstart bk n ztyqa
  else m₀ a
theorem bcnt_le (bk : ℕ → ℕ) (q b : ℕ) : bcnt bk q b ≤ q := by
  zuluf
  grind
theorem bstart_le {bk : ℕ → ℕ} {n A b : ℕ} (hA : ∀ q, q < n → bk q ≤ A) (hb : b ≤ A + 1) :
    bstart bk n b ≤ n := by
  have := bstart_mono (bk := bk) n hb
  rw [bstart_all hA] at this; omega

/-! ## The loops -/

/-- The loop invariant of the first loop. -/
def I1 (W : ℕ) (c₀ : Config) (BB n A base A₀ : ℕ) (m₀ : ℕ → ℕ) (j : ℕ) (d : Config) : Prop :=
  WordsBounded W d ∧ BkR c₀ BB n A base A₀ d ∧ d.nreg 210038 = j ∧ ∀ a, d.nmem a = mem1 m₀ A₀ j a
variable {c₀ d : Config} {BB n A base A₀ : ℕ} {m₀ bk : ℕ → ℕ}
theorem loop1_exec {m₀ : ℕ → ℕ}
    (hroom : A₀ + ztbo + 1 ≤ W) (h : I1 W c₀ BB n A base A₀ m₀ 0 d) :
    ∃ d' k, Exec P W bkL1 d d' k ∧ I1 W c₀ BB n A base A₀ m₀ ztbo d' ∧
      k ≤ 5 * ztbo + 2 := by
  obtain ⟨d', k, ex, hI, hk⟩ := forLoop (P := P) (W := W) (ir := 210038) (nr := 210039)
    (I1 W c₀ BB n A base A₀ m₀) 3 ztbo
    ztfhk
    (fun j d hj ⟨hw, hR, h38, hm⟩ => by
      obtain ⟨d', k, ex, hk, h38', hm', hf⟩ := body1_exec (P := P) d hw hR.r36 h38 hR.r34 hR.r35
        by_omega
      zqbmm
      zulby
      grind) h (Nat.zero_le _)
  zqbml

/-- The loop invariant of the second loop. -/
def I2 (W : ℕ) (c₀ : Config) (BB n A base A₀ : ℕ) (m₀ bk : ℕ → ℕ) (j : ℕ) (d : Config) :
    Prop :=
  WordsBounded W d ∧ BkR c₀ BB n A base A₀ d ∧ d.nreg 210038 = j ∧
    ∀ a, d.nmem a = mem2 m₀ bk A₀ A j a
theorem loop2_exec (hBB : BB + n ≤ A₀)
    (hbkd : ∀ q, q < n → m₀ ztgzy = bk q)
    (hbk : ∀ q, q < n → bk q ≤ A) (hroom : A₀ + ztbo + n + 1 ≤ W)
    (h : I2 W c₀ BB n A base A₀ m₀ bk 0 d) :
    ∃ d' k, Exec P W bkL2 d d' k ∧ I2 W c₀ BB n A base A₀ m₀ bk n d' ∧ k ≤ 9 * n + 2 := by
  obtain ⟨d', k, ex, hI, hk⟩ := forLoop (P := P) (W := W) (ir := 210038) (nr := 210031)
    (I2 W c₀ BB n A base A₀ m₀ bk) 7 n
    ztfhj
    (fun j d hj ⟨hw, hR, h38, hm⟩ => by
      have hx : ztzqc := by
        zvmwi; unfold mem2; grind
      zukgy
      have hv : d.nmem ztrin = bcnt bk j ztvez := by
        zvmwi; unfold mem2; simp_all
      have hvb := bcnt_le bk j ztvez
      obtain ⟨d', k, ex, hk, h38', hm', hf⟩ := body2_exec (P := P) d hw hR.r36 hR.r22 h38 hR.r34
        hx hv by_omega by_omega by_omega by_omega
      zqbmm
      zulbz
      by_cases ha : a = A₀ + bk j
      · rw [ite_eq_left ha, ite_eq_left by_omega, show a - A₀ = bk j by omega, bcnt_succ, ite_eq_left rfl]
      · zuhmm
        zudlu
        · rw [bcnt_succ, ite_eq_right by_omega, Nat.add_zero]
        · rfl) h (Nat.zero_le _)
  zqbml

/-- The loop invariant of the third loop. -/
def I3 (W : ℕ) (c₀ : Config) (BB n A base A₀ : ℕ) (m₀ bk : ℕ → ℕ) (j : ℕ) (d : Config) :
    Prop :=
  WordsBounded W d ∧ BkR c₀ BB n A base A₀ d ∧ d.nreg 210038 = j ∧
    d.nreg 210044 = bstart bk n j ∧ ∀ a, d.nmem a = mem3 m₀ bk n A₀ A j a
theorem loop3_exec
    (hbk : ∀ q, q < n → bk q ≤ A) (hroom : A₀ + ztbo + ztbo + n + 1 ≤ W)
    (h : I3 W c₀ BB n A base A₀ m₀ bk 0 d) :
    ∃ d' k, Exec P W bkL3 d d' k ∧ I3 W c₀ BB n A base A₀ m₀ bk ztbo d' ∧
      k ≤ 9 * ztbo + 2 := by
  obtain ⟨d', k, ex, hI, hk⟩ := forLoop (P := P) (W := W) (ir := 210038) (nr := 210039)
    (I3 W c₀ BB n A base A₀ m₀ bk) 7 ztbo
    ztfhk
    (fun j d hj ⟨hw, hR, h38, h44, hm⟩ => by
      have ht : d.nmem ztdst = bcnt bk n j := by
        zvmwi; unfold mem3; simp_all
      have hs := bstart_le (bk := bk) hbk ztmoa
      have hs1 := bstart_le (bk := bk) hbk ztkxq
      rw [bstart_succ] at hs1
      obtain ⟨d', k, ex, hk, h38', h44', hm', hf⟩ := body3_exec (P := P) d hw hR.r36 hR.r37 h38
        hR.r34 h44 ht by_omega by_omega by_omega by_omega by_omega
      refine ⟨d', k, ex, ⟨ex.wb_right, hR.body hf, h38', by rw [h44', bstart_succ], fun a => ?_⟩,
        by omega⟩
      rw [hm', Machine.upd_apply, Machine.upd_apply, hm]
      unfold mem3
      grind) h (Nat.zero_le _)
  zqbml

/-- The loop invariant of the fourth loop. -/
def I4 (W : ℕ) (c₀ : Config) (BB n A base A₀ : ℕ) (m₀ bk : ℕ → ℕ) (j : ℕ) (d : Config) :
    Prop :=
  WordsBounded W d ∧ BkR c₀ BB n A base A₀ d ∧ d.nreg 210038 = j ∧
    (∀ a, a < A₀ + ztbo + ztbo → d.nmem a = memCS m₀ bk n A₀ A j a) ∧
    ∀ q, q < j → d.nmem (A₀ + ztbo + ztbo + slot bk n q) = base + q
theorem loop4_exec (hBB : BB + n ≤ A₀)
    (hbkd : ∀ q, q < n → m₀ ztgzy = bk q)
    (hbk : ∀ q, q < n → bk q ≤ A) (hroom : A₀ + ztbo + ztbo + n + 1 ≤ W)
    (hbase : base + n ≤ W) (h : I4 W c₀ BB n A base A₀ m₀ bk 0 d) :
    ∃ d' k, Exec P W bkL4 d d' k ∧ I4 W c₀ BB n A base A₀ m₀ bk n d' ∧ k ≤ 12 * n + 2 := by
  obtain ⟨d', k, ex, hI, hk⟩ := forLoop (P := P) (W := W) (ir := 210038) (nr := 210031)
    (I4 W c₀ BB n A base A₀ m₀ bk) 10 n
    ztfhj
    (fun j d hj ⟨hw, hR, h38, hm, hq⟩ => by
      have hx : ztzqc := by
        zvmzz; unfold memCS; grind
      zukgy
      have hv : d.nmem ztrin = slot bk n j := by
        zvmzz; unfold memCS; zunab
        unfold slot; simp
      have hsl := slot_lt (bk := bk) hj hbk
      obtain ⟨d', k, ex, hk, h38', hm', hf⟩ := body4_exec (P := P) d hw hR.r36 hR.r22 h38 hR.r48
        hR.r33 hR.r34 hx hv by_omega by_omega by_omega by_omega by_omega by_omega
      refine ⟨d', k, ex, ⟨ex.wb_right, hR.body hf, h38', fun a ha => ?_, fun q hq' => ?_⟩, by_omega⟩
      · zuikb
        by_cases hb : a = A₀ + bk j
        · rw [ite_eq_left hb]
          unfold memCS
          rw [ite_eq_left by_omega, show a - A₀ = bk j by omega, bcnt_succ, ite_eq_left rfl]
          rfl
        · rw [ite_eq_right hb, ite_eq_right by_omega, hm _ ha]
          unfold memCS
          zudlu
          all_goals first | rfl | rw [bcnt_succ, ite_eq_right by_omega, Nat.add_zero]
      · have hqn : q < n := by_omega
        have hsq := slot_lt hqn hbk
        zuikb
        zufa
        by_cases hqj : q = j
        · simp_all
        · have hne : slot bk n q ≠ slot bk n j := fun h' => hqj (slot_inj hqn hj h')
          grind) h (Nat.zero_le _)
  zqbml
theorem wrM_init : wrM Bbkt bkInit = true := by_decide
theorem wrM_reset1 : wrM Bbody ztifw = true := by_decide
theorem wrM_reset2 : wrM Bbody ztfbj = true := by_decide
set_option maxHeartbeats 2000000 in
/-- **The bucket distribution.** -/
theorem bktS_exec (c : Config) (hw : WordsBounded W c) {BB n A base : ℕ} {bk : ℕ → ℕ}
    (h22 : c.nreg 210022 = BB) (h31 : c.nreg 210031 = n) (h32 : c.nreg 210032 = A)
    (h33 : c.nreg 210033 = base) (hBB : BB + n ≤ c.nreg ALLOC)
    (hbkd : ∀ q, q < n → c.nmem (BB + q) = bk q) (hbk : ∀ q, q < n → bk q ≤ A)
    (hroom : c.nreg ALLOC + (A + 1) + (A + 1) + n + 1 ≤ W) (hbase : base + n ≤ W) :
    ∃ c' k, Exec P W bktS c c' k ∧ k ≤ 21 * (A + 1) + 21 * n + 30 ∧
      c'.nreg 210036 = c.nreg ALLOC ∧ c'.nreg 210037 = c.nreg ALLOC + (A + 1) ∧
      c'.nreg 210048 = c.nreg ALLOC + (A + 1) + (A + 1) ∧
      c'.nreg ALLOC = c.nreg ALLOC + (A + 1) + (A + 1) + n ∧
      c'.nreg 210034 = 1 ∧ c'.nreg 210039 = A + 1 ∧
      seg c'.nmem (c.nreg ALLOC + (A + 1) + (A + 1)) n = bktList bk n A base ∧
      (∀ b, b ≤ A → c'.nmem (c.nreg ALLOC + (A + 1) + b) = bstart bk n b) ∧
      (∀ b, b ≤ A → c'.nmem (c.nreg ALLOC + b) = bstart bk n (b + 1)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bbkt r = false → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set A₀ := c.nreg ALLOC with hA₀
  -- the initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, v34, v35, v36, v39, v37, v48, vA, v38, hm₁⟩ : ∃ c₁ k₁,
      Exec P W bkInit c c₁ k₁ ∧ k₁ = 8 ∧ c₁.nreg 210034 = 1 ∧ c₁.nreg 210035 = 0 ∧
      c₁.nreg 210036 = A₀ ∧ c₁.nreg 210039 = A + 1 ∧ c₁.nreg 210037 = A₀ + (A + 1) ∧
      c₁.nreg 210048 = A₀ + (A + 1) + (A + 1) ∧ c₁.nreg ALLOC = A₀ + (A + 1) + (A + 1) + n ∧
      c₁.nreg 210038 = 0 ∧ c₁.nmem = c.nmem := by
    unfold bkInit
    exec_block
    all_goals try (config_simp; (try simp only [h32, h31, show c.nreg 9999 = A₀ from rfl]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      (try simp only [show ALLOC = 9999 from rfl]) <;> config_simp <;>
      (try simp only [h32, h31, show c.nreg 9999 = A₀ from rfl])
  have f₁ := exec_frameM e₁ wrM_init
  have hR₁ : BkR c BB n A base A₀ c₁ :=
    { r22 := (f₁.1 _ (by decide)).trans h22, r31 := (f₁.1 _ (by decide)).trans h31,
      r32 := (f₁.1 _ (by decide)).trans h32, r33 := (f₁.1 _ (by decide)).trans h33,
      r34 := v34, r35 := v35, r36 := v36, r37 := v37, r39 := v39, r48 := v48, fr := f₁.1,
      alloc := vA, rr := f₁.2.1, rm := f₁.2.2.1, out := f₁.2.2.2 }
  have w₁ := e₁.wb_right
  -- the first loop
  obtain ⟨c₂, k₂, e₂, ⟨w₂, hR₂, h38₂, hm₂⟩, hk₂⟩ := loop1_exec (P := P) (m₀ := c.nmem)
    (by omega) ⟨w₁, hR₁, v38, fun a => by rw [hm₁]; unfold mem1; simp⟩
  -- reset
  have e₃ := Exec.constN (P := P) w₂ 210038 0 (Nat.zero_le _)
  have f₃ := exec_frameM e₃ wrM_reset1
  have hR₃ := hR₂.body f₃
  -- the second loop
  obtain ⟨c₄, k₄, e₄, ⟨w₄, hR₄, h38₄, hm₄⟩, hk₄⟩ := loop2_exec (P := P) (m₀ := c.nmem)
    (bk := bk) (by omega) hbkd hbk (by omega)
    ⟨e₃.wb_right, hR₃, by simp, fun a => by
      show c₂.nmem a = _
      rw [hm₂]; rfl⟩
  -- reset
  obtain ⟨c₅, k₅, e₅, hk₅, v38₅, v44₅, hm₅⟩ : ∃ c₅ k₅,
      Exec P W (block [.constN 210038 0, .constN 210044 0]) c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg 210038 = 0 ∧ c₅.nreg 210044 = 0 ∧ c₅.nmem = c₄.nmem := by
    exec_block
    · omega
    · omega
    simp
  have f₅ := exec_frameM e₅ wrM_reset2
  have hR₅ := hR₄.body f₅
  -- the third loop
  obtain ⟨c₆, k₆, e₆, ⟨w₆, hR₆, h38₆, h44₆, hm₆⟩, hk₆⟩ := loop3_exec (P := P) (m₀ := c.nmem)
    (bk := bk) hbk (by omega)
    ⟨e₅.wb_right, hR₅, v38₅, by rw [v44₅]; rfl, fun a => by
      rw [hm₅, hm₄]; unfold mem2 mem3; grind⟩
  -- reset
  have e₇ := Exec.constN (P := P) w₆ 210038 0 (Nat.zero_le _)
  have f₇ := exec_frameM e₇ wrM_reset1
  have hR₇ := hR₆.body f₇
  -- the fourth loop
  obtain ⟨c₈, k₈, e₈, ⟨w₈, hR₈, h38₈, hm₈, hq₈⟩, hk₈⟩ := loop4_exec (P := P) (m₀ := c.nmem)
    (bk := bk) (by omega) hbkd hbk (by omega) hbase
    ⟨e₇.wb_right, hR₇, by simp, fun a ha => by
      show c₆.nmem a = _
      rw [hm₆]; unfold mem3 memCS
      split_ifs <;> first | rfl | omega, fun q hq => absurd hq (by omega)⟩
  refine ⟨c₈, k₁ + (k₂ + (1 + (k₄ + (k₅ + (k₆ + (1 + k₈)))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))), by omega,
    hR₈.r36, hR₈.r37, hR₈.r48, hR₈.alloc, hR₈.r34, hR₈.r39, ?_, fun b hb => ?_, fun b hb => ?_,
    fun a ha => ?_,
    hR₈.fr, ?_, hR₈.rm, hR₈.out⟩
  · exact seg_eq_bktList hbk (by omega)
  · rw [hm₈ _ (by omega)]; unfold memCS
    grind
  · rw [hm₈ _ (by omega)]; unfold memCS
    rw [ite_eq_left (by omega), show c.nreg ALLOC + b - A₀ = b by omega, bstart_succ]
  · rw [hm₈ _ (by omega)]; unfold memCS; grind
  · funext r
    exact exec_frameM2 (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))))
      (BN := Bbkt) (BR := fun _ => false) (by decide) r rfl
end exec
end
end DrvR
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbka" : tactic => `(tactic| refine ⟨by_omega, p1, by_grind, by_grind⟩)
local macro "zqbkb" : tactic => `(tactic| (rw [Nat.mod_eq_of_lt h2] at hv
                                           refine ⟨p + 1, 0, h2, le_rfl, one_pos, by_simp, ?_⟩
                                           simp_all))
local macro "zqbkc" : tactic => `(tactic| rw [show p + 1 = 2 * C.m + 7 by omega, Nat.mod_self] at hv)
local macro "zqbkd" : tactic => `(tactic| refine ⟨fun k hk => ?_, fun p t hp ht0 ht1 hpt => ?_⟩)
local macro "zqbke" : tactic => `(tactic| exact ⟨p, t, hp, ht0, h1, rfl, by_simp_all⟩)
set_option hygiene true

/-!
# Lemma 3.6 (WP-H), part 18: the walk positions of a stopping point

The main phase of the query stops the ray at a point `X` of a chain edge `c` (at the height of
the ray) and locates the walk positions of `X`: `wAOf c` on the tour edge running along `c`
forwards, `wBOf c` on the tour edge running backwards, and at the top vertex also the two ends
`6`, `2 m + 6` of the tour (`posOf`).  This file shows that these are proper walk positions with
point `X` (`fwd_pos`, `bwd_pos`), and that every walk key whose point is `X` is one of their
keys (`keys_of_stop`).
-/
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
open Chazelle.Visibility (rayPt hseg)
open Chazelle.Chain (sidePt sideE)
@[expose] public section
variable {P : Polygon} {C : Chain} {V : QV}
theorem mod_shift {a b M : ℕ} (hb : b ≤ M) : (b + ztqdj % M) % M = a % M := by
  rw [Nat.add_mod_mod, show b + ztqdj = a + M by omega, Nat.add_mod_right]

/-- The walk edge `i + 6` runs from the chain vertex `sideE (tj i)` to `sideE (tj i + 1)`. -/
theorem tour_ends {i : ℕ} (hi : i < 2 * C.m) :
    (chainModel C).W.vtx ztcy = C.vertex (sideE C.m (tj C i)) ∧
      (chainModel C).W.vtx ztysm =
        C.vertex (sideE C.m ztkfu) := by
  zujx
  · show (C.sideWalk C.sideBeta).vtx _ = _
    rw [C.sideWalk_vtx_tour _ hi.le]; rfl
  · show (C.sideWalk C.sideBeta).vtx ztysl = _
    rw [C.sideWalk_next_tour _ hi, C.sideWalk_vtx_tour _ by_omega]
    unfold Chain.sideTour; rw [C.sideIdx_succ]; rfl
variable {m j : ℕ} {w hz : ℕ} {p : ℕ}
theorem sideE_lo (hj : j ≤ m) : sideE m j = j := by unfold sideE; simp_all
theorem sideE_hi (hj : m ≤ j) : sideE m j = 2 * m - j := by
  zudma

/-- The chain vertex `k` is the vertex `(s + k) mod n` of `Q`. -/
theorem vertex_eq (hv : QVOK P C V) (k : ℕ) : C.vertex k = (Qof P).vtx ((V.s + k) % P.n) := by
  zugil
  zudaf

/-- The walk position facts. -/
def PosFacts (P : Polygon) (C : Chain) (hz w : ℕ) (X : Point) (κ : ℝ) : Prop :=
  w < 2 * C.m + 7 ∧ ProperPos ztc zta P.n ztxv ∧
    (chainModel C).pos zta ztxv = X ∧ (chainModel C).key zta ztxv = κ

/-- A walk position inside a non-horizontal walk edge. -/
theorem edge_pos {a b : Point} (ha : (chainModel C).W.vtx w = a)
    (hb : (chainModel C).W.vtx ztuz = b) (hne : a.2 ≠ b.2)
    (ht0 : 0 ≤ ztbxg / ztti)
    (ht1 : ztbxg / ztti < 1) (hh : hz < P.n) :
    ProperPos ztc zta P.n ztxv ∧
      (chainModel C).pos zta ztxv =
        Geometry.lerp a b (ztbxg / ztti) ∧
      (chainModel C).key zta ztxv = w + ztbxg / ztti := by
  have hp : (chainModel C).param zta ztxv =
      ztbxg / ztti := by
    zujpx
    simp_all
  refine ⟨⟨by_simp_all, by_simp_all, by_simp_all⟩, ?_, ?_⟩
  · zulbf
  · unfold Model.key; zvohk

/-- A walk position at the start vertex of its walk edge. -/
theorem vertex_pos {a : Point} (ha : (chainModel C).W.vtx w = a)
    (hy : a.2 = ((Qof P).vtx hz).2) (hh : hz < P.n) :
    ProperPos ztc zta P.n ztxv ∧
      (chainModel C).pos zta ztxv = a ∧
      (chainModel C).key zta ztxv = w := by
  have hp : (chainModel C).param zta ztxv = 0 := by
    unfold Model.param Model.wa
    simp_all
  refine ⟨⟨by zvohk, by_simp_all, by_simp_all⟩, ?_, ?_⟩
  · unfold Model.pos Model.wa; simp_all
  · unfold Model.key; simp_all
theorem heights_ne (hT : TopOK P C V) {i j : ℕ} (hi : i < P.n) (hj : j < P.n) :
    ((Qof P).vtx i).2 = ((Qof P).vtx j).2 ↔ i = j := by
  zuc
  constructor
  · intro h; by_contra hne; exact hT.hD i j by_omega by_omega hne h
  simp_all

/-- **The walk positions of a point of a chain edge.** -/
theorem fwd_bwd_pos (hT : TopOK P C V) {c : ℕ} (hc : c < C.m) {X : Point}
    (hX : X ∈ C.chainEdge c) (hy : X.2 = ((Qof P).vtx V.hz).2) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧
      PosFacts P C V.hz ztlum X
        (6 + (ztdze % ztbb : ℕ) + τ) ∧
      PosFacts P C V.hz ztryf X
        (6 + (ztccf % ztbb : ℕ) + ztcsf) := by
  zudpl
  zuc
  zubb
  have hmn : ztgaj := by have := C.m_lt; rw [hv.CQ, hQn] at this; omega
  have hn2 : ztmss := by_omega
  zuec
  zuizu
  zuru
  zubad
  set e := zthdd % P.n with he
  set e1 := ztqde % P.n with he1
  zuhyn
  have he1n : e1 < P.n := Nat.mod_lt _ by_omega
  have hvc := vertex_eq hv c
  have hvc1 : C.vertex zthga = (Qof P).vtx e1 := by zuosl; rfl
  have hee1 : e ≠ e1 := by
    zuq
    have hx := Nat.add_mod zthdd 1 P.n
    rw [Nat.mod_eq_of_lt (show 1 < P.n by omega)] at hx
    have hlt := by_omega
    rw [he, he1, hx] at h
    rcases Nat.lt_or_ge (zthdd % P.n + 1) P.n with h' | h'
    · zupe
    · rw [show zthdd % P.n + 1 = P.n by omega, Nat.mod_self] at h; omega
  have hne := fun h =>
    hee1 ((heights_ne hT hen he1n).1 h)
  -- the parameter on the chain edge
  rw [C.chainEdge_eq] at hX
  obtain ⟨τ, hτ0, hτ1, hXe⟩ := hX
  rw [hvc, hvc1] at hXe
  have hXl : X = Geometry.lerp _ _ τ := hXe
  zueng
  have hyτ : y = ((Qof P).vtx e).2 + τ * ztflm := by
    simp_all
  have hd : ((Qof P).vtx e1).2 - ((Qof P).vtx e).2 ≠ 0 := sub_ne_zero.2 ztnr
  have hτ : τ = (y - ((Qof P).vtx e).2) / ztflm := by
    grind
  have hτ' : 1 - τ = (y - ((Qof P).vtx e1).2) / (((Qof P).vtx e).2 - ((Qof P).vtx e1).2) := by
    grind
  have hy1 : V.hz = e1 ↔ τ = 1 := by
    rw [← heights_ne hT hzn he1n, ← hydef, hyτ]
    grind
  have hy0 : V.hz = e ↔ τ = 0 := by
    rw [← heights_ne hT hzn hen, ← hydef, hyτ]
    grind
  refine ⟨τ, hτ0, hτ1, ?_, ?_⟩
  · -- forwards
    set i := (c + 2 * C.m - S) % ztbb with hi
    zuhyr
    have htj : tj C i = c := by
      zufdt
    zuhhk
    simp only [htj, sideE_lo hc.le, sideE_lo (by omega : c + 1 ≤ C.m), hvc, hvc1, hnW,
      Nat.mod_eq_of_lt (by omega : i + 6 + 1 < 2 * C.m + 7)] at ea eb
    have hw : wAOf V P.n c = i + 6 + (if V.hz = e1 then 1 else 0) := by
      unfold wAOf; zuomd
    by_cases h1 : V.hz = e1
    · have ht := hy1.1 h1
      rw [hw, ite_eq_left h1]
      obtain ⟨p1, p2, p3⟩ := vertex_pos eb
        (by zvmwp) hzn
      zqbka
    · have ht : ztsoh := by_grind
      rw [hw, ite_eq_right h1, Nat.add_zero]
      obtain ⟨p1, p2, p3⟩ := edge_pos ea
        ztjqc hne by_grind
        by_grind hzn
      rw [← hτ] at p2 p3
      zqbka
  · -- backwards
    set i := (2 * C.m - 1 - c + 2 * C.m - S) % ztbb with hi
    zuhyr
    have htj : tj C i = 2 * C.m - 1 - c := by
      zufdt
    zuhhk
    simp only [htj, sideE_hi (by omega : C.m ≤ 2 * C.m - 1 - c),
      sideE_hi (by omega : C.m ≤ 2 * C.m - 1 - c + 1),
      show 2 * C.m - (2 * C.m - 1 - c) = c + 1 by omega,
      show 2 * C.m - (2 * C.m - 1 - c + 1) = c by omega, hvc, hvc1, hnW,
      Nat.mod_eq_of_lt (by omega : i + 6 + 1 < 2 * C.m + 7)] at ea eb
    have hw : wBOf V P.n c = i + 6 + (if V.hz = e then 1 else 0) := by
      unfold wBOf; zuomd
    by_cases h0 : V.hz = e
    · have ht := hy0.1 h0
      rw [hw, ite_eq_left h0]
      obtain ⟨p1, p2, p3⟩ := vertex_pos eb
        ztqev hzn
      zqbka
    · have ht : ztrzs := by_grind
      rw [hw, ite_eq_right h0, Nat.add_zero]
      obtain ⟨p1, p2, p3⟩ := edge_pos ea
        ztjqc ztnr
        by_grind by_grind hzn
      rw [← hτ'] at p2 p3
      refine ⟨by_omega, p1, ?_, by_grind⟩
      rw [p2, hXl]
      zudxm
theorem nat_add_frac_eq {p k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (h : (p : ℝ) + t = k) :
    p = k ∧ t = 0 := by
  have h1 : (p : ℝ) ≤ k := by_linarith
  zujyk
  have h1' : p ≤ k := by_simp_all
  zucgf
  grind

/-- The key of a walk position whose point is on the chain is in `[6, 2 m + 6]`. -/
theorem key_range_chain (hp : p < 2 * C.m + 7) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hx : sidePt ztcs p t ∈ C.set) :
    (6 : ℝ) ≤ p + t ∧ (p : ℝ) + t ≤ 2 * C.m + 6 := by
  rcases pos_on_chain C hp ht0 ht1 hx with ⟨h1, h2⟩ | ⟨rfl, rfl⟩
  · zudxr

  simp

/-- A walk position with key `6` or `2 m + 6` is the top. -/
theorem top_of_key {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h : (p : ℝ) + t = 6 ∨ (p : ℝ) + t = 2 * C.m + 6) :
    sidePt ztcs p t = C.top := by
  zuy
  · obtain ⟨rfl, rfl⟩ := nat_add_frac_eq ht0 ht1 by_omega
    rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_six]
  · obtain ⟨rfl, rfl⟩ := nat_add_frac_eq (k := 2 * C.m + 6) ht0 ht1 (by zvmwc; simp)
    rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour _ le_rfl, Chain.sideTour_two_m]

/-- **Every walk key of a point of a chain edge** is the key of its forward or backward
position, or (at the top) one of the two ends `6`, `2 m + 6` of the tour. -/
theorem keys_of_stop (hT : TopOK P C V) (hP : C.P.Simple) {c : ℕ} (hc : c < C.m) {X : Point}
    (hX : X ∈ C.chainEdge c) (hy : X.2 = ((Qof P).vtx V.hz).2) {p : ℕ} (hp : p < 2 * C.m + 7)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hpt : Geometry.lerp ztdrr ztbakk
      t = X) :
    (p : ℝ) + t = (chainModel C).key zta ztgpt ∨
      (p : ℝ) + t = (chainModel C).key zta ztgpu ∨
      (V.hz = V.tv ∧ ((p : ℝ) + t = 6 ∨ (p : ℝ) + t = 2 * C.m + 6)) := by
  have hXs : X ∈ C.set := ⟨c, hc, hX⟩
  zuru
  zuec
  zubb
  have hsp : ∀ q u, sidePt ztcs q u = Geometry.lerp ztosk
      ztxmq u := fun _ _ => rfl
  -- normalise `t = 1`
  obtain ⟨p', t', hp', ht0', ht1', hk, hpt'⟩ : ∃ p' : ℕ, ∃ t' : ℝ, p' < 2 * C.m + 7 ∧ 0 ≤ t' ∧
      t' < 1 ∧ (p' : ℝ) + t' = p + t ∧ sidePt ztcs p' t' = X := by
    zucyq
    · zucuj
      have hv : ztbaoi := by
        simp_all
      zuemg

      · zqbkb
      · exfalso
        zqbkc
        have := (C.sideWalk_box_pt C.sideBeta (p := 0) by_omega le_rfl
          one_pos).1
        simp_all
    · zqbke
  zulrb
  obtain ⟨τ, hτ0, hτ1, ⟨wa, ⟨pa0, pa1, -⟩, pax, pak⟩, ⟨wb, ⟨pb0, pb1, -⟩, pbx, pbk⟩⟩ :=
    fwd_bwd_pos hT hc hX hy
  set κA := (chainModel C).key zta ztgpt
  set κB := (chainModel C).key zta ztgpu
  set τA := (chainModel C).param zta ztgpt
  set τB := (chainModel C).param zta ztgpu
  have hκA : κA = (wAOf V P.n c : ℝ) + τA := rfl
  have hκB : κB = (wBOf V P.n c : ℝ) + τB := rfl
  have hA : sidePt ztcs ztlum τA = X := pax
  have hB : sidePt ztcs ztryf τB = X := pbx
  -- the top
  have htop : ∀ q : ℕ, ∀ u : ℝ, 0 ≤ u → u < 1 → sidePt ztcs q u = X →
      ((q : ℝ) + u = 6 ∨ (q : ℝ) + u = 2 * C.m + 6) → V.hz = V.tv := by
    intro q u hu0 hu1 hq hk6
    have e := top_of_key hu0 hu1 hk6
    zukvu
    rw [← hT.top] at e
    have := congrArg Prod.snd e
    rw [hy] at this
    exact (heights_ne hT hT.hv.hz_lt hT.tv_lt).1 this
  by_cases hA' : (p' : ℝ) + t' = κA
  · grind
  by_cases hB' : (p' : ℝ) + t' = κB
  · grind
  zulw
  have hXA : sidePt ztcs ztlum τA ∈ C.set := by_grind
  rcases mirror_sum C hP wa hp' pa0 pa1 ht0' ht1' hXA (hA.trans hpt'.symm)
      by_grind with ⟨n1, hn1⟩ | ⟨h6, h26⟩ | ⟨h26, h6⟩
  · -- the mirror of `κA` is `κB`, up to `2 m`
    have hAB : ∃ n2 : ℤ, κA + κB = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * n2 := by
      rw [pak, pbk]
      set iA := ztdze % ztbb
      set iB := ztccf % ztbb
      have e1 := Nat.mod_add_div ztdze ztbb
      have e2 := Nat.mod_add_div ztccf ztbb
      set qa := ztdze / ztbb
      set qb := ztccf / ztbb
      have e1' : iA + 2 * C.m * qa + C.sideS C.sideBeta = c + 2 * C.m := by
        omega
      have e2' : iB + 2 * C.m * qb + C.sideS C.sideBeta + c + 1 = 4 * C.m := by
        omega
      have e1r : (iA : ℝ) + 2 * C.m * qa + C.sideS C.sideBeta = c + 2 * C.m := by
        exact_mod_cast e1'
      have e2r : (iB : ℝ) + 2 * C.m * qb + C.sideS C.sideBeta + c + 1 = 4 * C.m := by
        exact_mod_cast e2'
      refine ⟨3 - qa - qb, ?_⟩
      push_cast; linarith
    obtain ⟨n2, hn2⟩ := hAB
    have hdiff : (p' : ℝ) + t' - κB = 2 * C.m * ((n1 : ℝ) - n2) := by
      grind
    have r1 := key_range_chain hp' ht0' ht1' by_grind
    have r2 := key_range_chain wb pb0 pb1 by_grind
    rw [← hκB] at r2
    zufvl
    have hlt : (n1 : ℝ) - n2 < 2 := by_nlinarith
    have hgt : -2 < (n1 : ℝ) - n2 := by_nlinarith
    have hne0 : (n1 : ℝ) - n2 ≠ 0 := by_grind
    have hz1 : (n1 : ℤ) - n2 < 2 := by exact_mod_cast hlt
    have hz2 : -2 < (n1 : ℤ) - n2 := by exact_mod_cast hgt
    have hz3 : (n1 : ℤ) - n2 ≠ 0 := by_grind
    have hk6 : (p' : ℝ) + t' = 6 ∨ (p' : ℝ) + t' = 2 * C.m + 6 := by
      rcases (by omega : (n1 : ℤ) - n2 = 1 ∨ (n1 : ℤ) - n2 = -1) with h | h
      · have h' : (n1 : ℝ) - n2 = 1 := by exact_mod_cast h
        right; zvmxl at hdiff; linarith
      · have h' : (n1 : ℝ) - n2 = -1 := by exact_mod_cast h
        left; zvmxl at hdiff; linarith
    exact ⟨htop p' t' ht0' ht1' hpt' hk6, hk6⟩
  · exact ⟨htop p' t' ht0' ht1' hpt' (Or.inr h26), Or.inr h26⟩
  · exact ⟨htop p' t' ht0' ht1' hpt' ztqbd, Or.inl h6⟩

/-- **The walk keys of a point of a side of the box** at a vertex height. -/
theorem keys_of_box (hT : TopOK P C V) {hz : ℕ} (hh : hz < P.n) {X : Point}
    (hy : X.2 = ((Qof P).vtx hz).2) (hX : |X.1| = C.radius) {p : ℕ} (hp : p < 2 * C.m + 7)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hpt : Geometry.lerp ztdrr ztbakk
      t = X) :
    (X.1 = C.radius → (p : ℝ) + t = (chainModel C).key zta ⟨3, hz + 1⟩) ∧
      (X.1 = -C.radius → (p : ℝ) + t = (chainModel C).key zta ⟨1, hz + 1⟩) := by
  zubo
  have hyR := abs_lt.1 (vtx_snd_lt_radius hT.hv.CQ hh)
  zuru
  have htx := abs_lt.1 C.abs_top_fst_lt_radius
  zubnz
  have hsp : ∀ q u, sidePt ztcs q u = Geometry.lerp ztosk
      ztxmq u := fun _ _ => rfl
  -- normalise `t = 1`
  obtain ⟨p', t', hp', ht0', ht1', hk, hpt'⟩ : ∃ p' : ℕ, ∃ t' : ℝ, p' < 2 * C.m + 7 ∧ 0 ≤ t' ∧
      t' < 1 ∧ (p' : ℝ) + t' = p + t ∧ sidePt ztcs p' t' = X := by
    zucyq
    · zucuj
      have hv : ztbaoi := by
        simp_all
      zuemg

      · zqbkb
      · exfalso
        zqbkc
        have h0 := (C.sidePt_box C.sideBeta 0).1
        simp_all
    · zqbke
  zulrb
  -- the edge is a side of the box
  have hp3 : p' = 3 ∨ p' = 1 := by
    by_cases hb : p' ≤ 5 ∨ (p' = 2 * C.m + 6 ∧ 0 < t')
    · have := (C.sideWalk_box_pt C.sideBeta hb ht0' ht1').2 by_simp_all
        by_grind
      omega
    · exfalso
      zumij
      have hmem : X ∈ C.set := by
        rcases (by omega : (6 ≤ p' ∧ p' < 2 * C.m + 6) ∨ p' = 2 * C.m + 6) with ⟨h6, h6'⟩ | h6
        · obtain ⟨i, rfl⟩ : ∃ i, p' = i + 6 := ⟨p' - 6, by_omega⟩
          rw [← hpt', C.sidePt_tour C.sideBeta by_omega]
          refine ztlwp
          zunkl; exact ⟨t', ht0', ht1'.le, rfl⟩
        · have ht0'' : ztmwy := by_grind
          subst h6 ht0''
          rw [← hpt', Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour _ le_rfl,
            Chain.sideTour_two_m]
          exact C.top_mem_set
      have := abs_fst_lt_radius_of_mem hmem
      simp_all
  constructor
  · zuetb
    zuklx
    · zugbm
      zuglh

      rw [key_box_right, hy] at *
      grind
    · zugbl
      grind
  · zuetb
    zuklx
    · zugbm
      grind
    · zugbl
      zuglh

      rw [key_box_left]
      grind

/-- The positions of a stopping point are proper, and cover its keys. -/
def StopOK (P : Polygon) (C : Chain) (V : QV) (q : ℕ × ℕ × ℕ × ℕ) (X : Point) : Prop :=
  (∀ k, k < 4 → posK q k < 2 * C.m + 7 ∧ ProperPos ztc zta P.n ztope) ∧
  ∀ p : ℕ, ∀ t : ℝ, p < 2 * C.m + 7 → 0 ≤ t → t ≤ 1 →
    Geometry.lerp ztdrr ztbakk t = X →
      ∃ k, k < 4 ∧ (p : ℝ) + t = (chainModel C).key zta ztope

/-- **The stopping point on a chain edge.** -/
theorem stop_chain (hT : TopOK P C V) (hP : C.P.Simple) {c : ℕ} (hc : c < C.m) {X : Point}
    (hX : X ∈ C.chainEdge c) (hy : X.2 = ((Qof P).vtx V.hz).2) :
    StopOK P C V (posOf V P.n ztsqn) X := by
  zudpl
  obtain ⟨τ, -, -, ⟨wa, pa, -, -⟩, ⟨wb, pb, -, -⟩⟩ := fwd_bwd_pos hT hc hX hy
  have htop : ((Qof P).vtx V.tv).2 = C.top.2 := by zuozo
  have hW6 : ztidg := C.sideWalk_vtx_six _
  have hWl : ztyto := by
    show (C.sideWalk C.sideBeta).vtx _ = _
    rw [C.sideWalk_vtx_tour _ le_rfl, Chain.sideTour_two_m]
  have v6 : ∀ hz, hz = V.tv → hz < P.n → ProperPos ztc zta P.n ztqzz ∧
      (chainModel C).key zta ztqzz = 6 := fun hz e hh => by
    obtain ⟨a, -, b⟩ := vertex_pos (C := C) (P := P) (w := 6) (hz := hz) hW6
      by_simp_all hh
    simp_all
  have vl : ∀ hz, hz = V.tv → hz < P.n →
      ProperPos ztc zta P.n ztlvb ∧
      (chainModel C).key zta ztlvb = 2 * C.m + 6 := fun hz e hh => by
    obtain ⟨a, -, b⟩ := vertex_pos (C := C) (P := P) (w := 2 * C.m + 6) (hz := hz) hWl
      by_simp_all hh
    simp_all
  zuizu
  zqbkd
  · unfold posOf
    zuwa
    zublf
    · tauto
    · tauto
    · show posK ztnqn 2 < _ ∧ _
      zulsg
      grind
    · show posK ztnqn 3 < _ ∧ _
      zulsg
      zus
      · rw [hv.m]; simp_all
      simp_all
  · rcases keys_of_stop hT hP hc hX hy hp ht0 ht1 hpt with h | h | ⟨he, h | h⟩
    · exact ⟨0, by_omega, by_tauto⟩
    · exact ⟨1, by_omega, by_tauto⟩
    · refine ⟨2, by_omega, ?_⟩
      zufdl
      simp_all
    · refine ⟨3, by_omega, ?_⟩
      zufdl
      rw [hv.m, (vl _ he hzn).2]; exact h

/-- **The stopping point on a side of the box.** -/
theorem stop_box (hT : TopOK P C V) {w : ℕ} (hw : w = 1 ∨ w = 3) {X : Point}
    (hX : X = (if w = 3 then C.radius else -C.radius, ((Qof P).vtx V.hz).2)) :
    StopOK P C V ztmnb X := by
  zudpl
  zuizu
  zubo
  have hyR := abs_lt.1 (vtx_snd_lt_radius hv.CQ hzn)
  zubb
  zuru
  have hq : ∀ k, posK ztmnb k = w := fun k => by
    unfold posOf; simp only [show ¬ (1 : ℕ) = 0 by omega, ite_false]
    rcases k with _ | _ | _ | _ <;> rfl
  zqbkd
  · zugvl
    zubsc
    zukmo
    · refine (edge_pos
        (b := ztru) (C.sideWalk_vtx_one _)
        by_rfl
        by_grind ?_ ?_ hzn).1
      · simp only; apply div_nonneg_of_nonpos <;> linarith
      · simp only; zuosm; linarith
    · refine (edge_pos
        (b := ztbjg) (C.sideWalk_vtx_three _)
        by_rfl
        by_grind ?_ ?_ hzn).1
      · simp only; apply div_nonneg <;> linarith
      · simp only; zuosn; linarith
  · have hy : X.2 = ((Qof P).vtx V.hz).2 := by rw [hX]
    have hx : |X.1| = C.radius := by
      grind
    obtain ⟨k3, k1⟩ := keys_of_box hT hzn hy hx hp ht0 ht1 hpt
    refine ⟨0, by_omega, ?_⟩
    grind

/-- **The near end of a chord on the chain** gives a chain edge through its point. -/
theorem near_stop (hv : QVOK P C V) {w h : ℕ} (hE : EndFacts P C V w h) (h1 : xpClass w = 1) :
    ∃ c, c < C.m ∧ chordSel C V w = ztsqn ∧ (chainModel C).pos zta ztboe ∈ C.chainEdge c := by
  obtain ⟨-, hc, -, hw, hp0, hp1⟩ := hE
  have hmem := (hc h1).1
  zubb
  have hpos : (chainModel C).pos _ ztboe =
      sidePt ztcs w ((chainModel C).param zta ztboe) := rfl
  zvnbl at hmem ⊢
  rcases pos_on_chain C hw hp0 hp1 hmem with ⟨h6, h6'⟩ | ⟨rfl, h0⟩
  · refine ⟨tci C ztvu, tci_lt C _, ?_, ?_⟩
    · unfold chordSel; rw [ite_eq_left ztdgt]
    · zucxw
      rw [C.sidePt_tour C.sideBeta by_omega, show i + 6 - 6 = i by omega, ← tour_seg C i]
      exact ⟨_, hp0, hp1.le, rfl⟩
  · refine ⟨tci C ztdl, tci_lt C _, ?_, ?_⟩
    · unfold chordSel; rw [ite_eq_right ztdgt, ite_eq_left (by rw [hv.m]), hv.m]
    · rw [h0, Chazelle.Chain.sidePt_zero, ← tour_seg C _,
        C.sideWalk_vtx_tour _ le_rfl, show 2 * C.m - 1 + 1 = 2 * C.m by omega]
      exact ⟨1, zero_le_one, le_rfl, by_simp⟩
end
end OracleR
end Chazelle.Core
end
namespace Chazelle.Core
namespace OracleR
open OracleQ
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
@[expose] public section
variable {A : Set Point} {z : Point} {σ d : ℝ} {R : ℝ}

/-- First hits from the entry point. -/
theorem firstHitOpt_shift (hA : A ⊆ Chain.box R) (hd : 0 ≤ d)
    (hout : ∀ s, 0 < s → s ≤ d → rayPt z σ s ∉ Chain.box R) {o : Option ℝ}
    (h : Sweep.FirstHitOpt A z σ o) :
    Sweep.FirstHitOpt A ztlsg σ (o.map (· - d)) := by
  cases o with
  | none =>
    zumhm
    rw [rayPt_rayPt] at hm
    exact h ztbcr by_linarith hm
  | some v =>
    obtain ⟨hv, hm, hfirst⟩ := h
    have hdv : d < v := by
      grind
    refine ⟨by_simp_all, ?_, fun t ht hlt hm' => ?_⟩
    · zubi
      rw [rayPt_rayPt, show d + (v - d) = v by ring]; exact hm
    · rw [rayPt_rayPt] at hm'
      grind

/-- A first hit from the entry point is a first hit from the origin. -/
theorem firstHit_unshift (hA : A ⊆ Chain.box R) (hd : 0 ≤ d)
    (hout : ∀ s, 0 < s → s ≤ d → rayPt z σ s ∉ Chain.box R) {t : ℝ}
    (h : FirstHit A ztlsg σ t) : FirstHit A z σ zthkq := by
  obtain ⟨ht, hm, hfirst⟩ := h
  refine ⟨by_linarith, by rw [rayPt_rayPt, add_comm] at hm; exact hm, fun s hs hlt hm' => ?_⟩
  zujtx
  · grind
  · zumit
    refine hfirst ztkej by_linarith by_linarith ?_
    zunko; omega

/-- No hit from the entry point is no hit from the origin. -/
theorem noHit_unshift (hA : A ⊆ Chain.box R) (_hd : 0 ≤ d)
    (hout : ∀ s, 0 < s → s ≤ d → rayPt z σ s ∉ Chain.box R) (h : NoHit A ztlsg σ) :
    NoHit A z σ := by
  zumhj
  zujtx
  · grind
  · zumit
    refine h ztkej by_linarith ?_
    zunko; exact hm

/-- **An origin past the box**: the ray never meets the box. -/
theorem noHit_past (hA : A ⊆ Chain.box R) (hσ : σ = 1 ∨ σ = -1) (hpast : R ≤ σ * z.1) :
    NoHit A z σ := by
  zumhj
  have := (abs_lt.1 (hA hm).1)
  zudv
  zur
  · grind
  grind
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open OracleQ
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
@[expose] public section
def Answer (P : Polygon) (C : Chain) (z : Point) (σ : ℝ) (flag edge : ℕ) : Prop :=
  (flag = 1 → ∃ t, FirstHit C.set z σ t ∧ edge < P.n ∧ rayPt z σ t ∈ (Qof P).edge edge) ∧
    (flag ≠ 1 → NoHit C.set z σ)
variable {P : Polygon} {C : Chain} {V : QV}
theorem not_mem_set_of_abs {x y : ℝ} (hx : C.radius ≤ |x|) : (ztjw : Point) ∉ C.set :=
  fun hm => by have := abs_fst_lt_radius_of_mem hm; grind
theorem not_mem_set_of_chord {y a b x : ℝ} (h : Chazelle.Chain.IsHChordIn C.dom y a b)
    (hax : a < x) (hxb : x < b) : (ztjw : Point) ∉ C.set := fun hm =>
  (h.open_mem x hax hxb).2 (Or.inl hm)
variable {b : ℕ} (z : Point) (t : ℝ)
theorem sgnOf_one (h : b = 1) : sgnOf b = 1 := by unfold sgnOf; simp_all
theorem sgnOf_ne (h : b ≠ 1) : sgnOf b = -1 := by unfold sgnOf; simp_all
theorem rayPt_right : rayPt z 1 t = ((z.1 + t, z.2) : Point) := by
  zvnap; simp
theorem rayPt_left : rayPt z (-1) t = ((z.1 - t, z.2) : Point) := by
  zufbw

/-- **The answer of a degenerate start.** -/
theorem deg_answer {m : ℕ → ℕ} {N : NF} (h : ChordRecOK P C V m N) {z : Point}
    (hs : SemOK P C V z) {t : ℕ} (hpart : PartC P C V m t) (hf : FoundC V m t)
    (hdeg : DegC P C V m t) {flag edge : ℕ}
    (h1 : xpClass zteey = 1 → flag = 1 ∧ edge = symIdx ztyxi)
    (h0 : xpClass zteey ≠ 1 → flag = 0) :
    Answer P C z zthx flag edge := by
  zubo
  zugpt
  zuicl
  have hcs : C.set ⊆ Chain.box C.radius := C.set_subset_box
  zuqe
  · -- rightwards: the chord `CH[t]`
    have hσ1 := sgnOf_one hσ
    zvnpq at hK
    have hj : ztsjw := by unfold jCOf; simp_all
    zuhaa

    rw [hj, ite_eq_left hσ] at hdeg h1 h0
    zvnpq at hdeg
    zukuj
    set i := chAt m V t
    have hi := h.lt t hK
    zubxd

    have hgt : EndGtZ P C V ztbrg V.hz := by
      have := hpost hK
      rw [← Bool.not_eq_true, chPr_iff] at this
      grind
    zugnk

    by_cases hp : C.radius ≤ z.1
    · -- past the box
      have hnh := noHit_past hcs ztp by_simp_all (A := C.set) (z := z)
      have hc2 : ztbadi := by
        intro hc1
        rcases hgt with h2 | ⟨-, hz⟩
        · omega
        · have hx := abs_lt.1 (ER.good hc1)
          zugrw
          · grind
          · rw [hσ1] at hz1; linarith
      exact ztklc
    have hnp : ztulu := ⟨fun _ => by_simp_all, fun h' => absurd hσ h'⟩
    have hb := (endGtZ_iff hσ hs.zo hnp ER.good).1 hgt
    have ha := not_lt.1 (fun h' => hdeg ((endGtZ_iff hσ hs.zo hnp EL.good).2 h'))
    unfold ζOf at hb ha; zvnpq at hb ha
    zudgj

    have hza := le_max_left z.1 (-C.radius)
    have hRa := le_max_right z.1 (-C.radius)
    -- no chain point strictly between the origin and the far end
    have hfree : ∀ s, 0 < s → z.1 + s < b → rayPt z 1 s ∉ C.set := by
      intro s hs0 hsb
      zuomb
      by_cases hx : z.1 + s ≤ -C.radius
      · zuitr
      · zumix
        exact not_mem_set_of_chord hC (by
          grind) hsb
    have hpos := ER.1
    refine ztlvw
    · have hc1 : xpClass ztbrg = 1 := by
        omega
      zuhhe
      obtain ⟨hmem, hlt, hedge⟩ := ER.2.1 hc1
      zujjt
      have hpt : rayPt z 1 zttfl = ((b, ((Qof P).vtx V.hz).2) : Point) := by
        zuomb; ring_nf
      refine ⟨b - z.1, ⟨by_linarith, by_grind, fun s hs0 hsl => hfree s hs0 (by
        linarith)⟩, by_grind, by_grind⟩
    · have hc : ztbadi := fun hc1 => hf1 (h1 hc1).1
      have hbR : b = C.radius := by
        have hb2 : xpClass ztbrg = 2 := by
          rcases xpClass_cases ztbrg with e | e | e
          · exfalso; have := xv_c0 (P := P) (C := C) (V := V) (h := V.hz) e; linarith
          · omega
          omega
        exact xv_c2 hb2
      intro s hs0
      by_cases hsb : z.1 + s < b
      · simp_all
      · zuozp
        zuitr
  · -- leftwards: the chord `CH[t - 1]`
    have hσ1 := sgnOf_ne hσ
    zvnpr at hK
    have hj : ztpoz := by unfold jCOf; simp_all
    zuhaa

    rw [hj, ite_eq_right hσ] at hdeg h1 h0
    zvnpr at hdeg
    zukuj
    set i := chAt m V ztso
    have hi := h.lt ztso by_omega
    zubxd

    have hlt' : EndLtZ P C V ztbdb V.hz := by
      have := hpre ztso by_omega
      zukqj
      grind
    zugnk

    by_cases hp : z.1 ≤ -C.radius
    · have hnh := noHit_past hcs ztbt by_linarith (A := C.set) (z := z)
      have hc2 : ztbadh := by
        intro hc1
        rcases hlt' with h2 | ⟨-, hz⟩
        · omega
        · have hx := abs_lt.1 (EL.good hc1)
          zugrw
          · grind
          grind
      exact ztklc
    have hnp : ztulu := ⟨fun h' => absurd h' hσ, fun _ => by_simp_all⟩
    have ha := (endLtZ_iff hσ hs.zo hnp EL.good).1 hlt'
    have hb := not_lt.1 (fun h' => hdeg ((endLtZ_iff hσ hs.zo hnp ER.good).2 h'))
    unfold ζOf at hb ha; zvnpr at hb ha
    zudgj

    have hza := min_le_left z.1 C.radius
    have hRa := min_le_right z.1 C.radius
    have hfree : ∀ s, 0 < s → a < z.1 - s → rayPt z (-1) s ∉ C.set := by
      intro s hs0 hsa
      zuomc
      by_cases hx : C.radius ≤ z.1 - s
      · zuitr
      · zumix
        exact not_mem_set_of_chord hC hsa (by
          grind)
    have hpos := EL.1
    refine ztlvw
    · have hc1 : xpClass ztbdb = 1 := by
        omega
      zuhhe
      obtain ⟨hmem, hlt, hedge⟩ := EL.2.1 hc1
      zujjt
      have hpt : rayPt z (-1) ztueu = ((a, ((Qof P).vtx V.hz).2) : Point) := by
        zuomc; ring_nf
      refine ⟨z.1 - a, ⟨by_linarith, by_grind, fun s hs0 hsl => hfree s hs0 (by
        linarith)⟩, by_grind, by_grind⟩
    · have hc : ztbadh := fun hc1 => hf1 (h1 hc1).1
      have haR : a = -C.radius := by
        have hb0 : xpClass ztbdb = 0 := by
          rcases xpClass_cases ztbdb with e | e | e
          · zulez
          · omega
          · exfalso; have := xv_c2 (P := P) (C := C) (V := V) (h := V.hz) e; linarith
        exact xv_c0 hb0
      intro s hs0
      by_cases hsa : a < z.1 - s
      · simp_all
      · rw [rayPt_left]
        zuitr
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open OracleQ
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
@[expose] public section
variable {P : Polygon} {C : Chain} {V : QV} {m : ℕ → ℕ} {N : NF}

/-- **The chord table lists every chord.** -/
theorem ChordRecOK.surj (h : ChordRecOK P C V m N) {i : ℕ} (hi : i < V.K) :
    ∃ q, q < V.K ∧ chAt m V q = i := by
  classical
  have hsub : (Finset.range V.K).image ztnwy ⊆ Finset.range V.K := by
    zuh
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (h.lt q (Finset.mem_range.1 hq))
  have hcard : ((Finset.range V.K).image ztnwy).card = V.K := by
    zugbx
    zubtp
    exact h.inj a b ztpyu ztpyv hab
  zukbw
  have : i ∈ (Finset.range V.K).image ztnwy := by_simp_all
  obtain ⟨q, hq, hqi⟩ := Finset.mem_image.1 this
  zubfo

/-- **No chord before the stopping point.** -/
theorem chord_free (h : ChordRecOK P C V m N) {z : Point} (hs : SemOK P C V z)
    (hnp : NotPast C V z) {t : ℕ} (hpart : PartC P C V m t) {x : ℝ}
    (h1 : 0 < sgnOf V.σb * (x - ζOf C V z))
    (h2 : FoundC V m t → sgnOf V.σb * (x - xv P C V ztbbb V.hz) < 0) :
    ((x, ((Qof P).vtx V.hz).2) : Point) ∉ ⋃₀ N.F ztc zta := by
  rintro ⟨c, ⟨r, hr, rfl⟩, hmem⟩
  zuep
  have hiK : i < V.K := by rw [h.K]; exact hi
  have hrec : ztiym := by unfold NF.chord; simp_all
  rw [hrec] at hmem
  obtain ⟨q, hq, rfl⟩ := h.surj hiK
  obtain ⟨hhn, -, hC, hS, EL, ER⟩ := h.facts (h.lt q hq)
  zvojf at hmem
  obtain ⟨hy, hxa, hxb⟩ := hmem
  simp only at hy hxa hxb
  have hhz : chH m V _ = V.hz :=
    ((heights_ne h.hT hhn hs.hv.hz_lt).1 hy.symm)
  rw [hhz] at hxa hxb EL ER hC
  zugpt
  zuqe
  · rw [sgnOf_one hσ, one_mul] at h1
    rw [sgnOf_one hσ, one_mul] at h2
    by_cases hqt : q < t
    · -- behind the origin: the right end is not ahead
      have := hpre q hqt
      zukqj
      rcases this.2 with h' | ⟨-, h', -⟩
      · omega
      · have hb := not_lt.1 (fun hh => h' hσ ((endGtZ_iff hσ hs.zo hnp ER.good).2 hh))
        linarith
    · -- ahead: the chord at `t` is found, and its left end is not after ours
      zumir
      have htK : t < V.K := by_omega
      have hle := h.sorted t q hqt hq
      have hnot := hpost htK
      zuhns
      have hHt : chH m V ztrnf = V.hz := by
        zucys
        · zuct
          exact hnot ⟨h.lt t htK, by_omega⟩
        omega
      have hf : ztukp := by
        zulos
        zumtc
      zulkv
      unfold nearC jCOf at hnear; rw [ite_eq_left hσ, ite_eq_left hσ] at hnear
      obtain ⟨-, -, -, -, ELt, -⟩ := h.facts (h.lt t htK)
      have hx := chLe_xv ELt.good ztmdq hle by_omega
      grind
  · rw [sgnOf_ne hσ] at h1 h2
    by_cases hqt : t ≤ q
    · -- behind the origin: the left end is not ahead (the predicate fails from `t` on)
      have hnot : chPr P C V m ztlly = false := by
        zukr
        rw [Bool.not_eq_false] at hc
        have := chPr_mono h t q hqt hq hc
        grind
      zuhns
      have ha : ¬ EndLtZ P C V _ V.hz := fun hh =>
        hnot ⟨by_omega, Or.inr ⟨hhz, by_omega, fun _ => hh⟩⟩
      have ha' := not_lt.1 (fun hh => ha ((endLtZ_iff hσ hs.zo hnp EL.good).2 hh))
      linarith
    · zumir
      have hle := h.sorted q ztso by_omega by_omega
      have hpt := hpre ztso by_omega
      rw [chPr_iff] at hpt
      have hHt : chH m V ztzlb = V.hz := by
        zucys
        · omega
        omega
      have hf : ztukp := by
        zuevy
        zumtc
      zulkv
      unfold nearC jCOf at hnear; rw [ite_eq_right hσ, ite_eq_right hσ] at hnear
      obtain ⟨-, -, hCt, -, ELt, ERt⟩ := h.facts (h.lt ztso by_omega)
      rw [hHt] at ELt ERt hCt
      have hx := chLe_xv ztmdq (by rw [hHt]; exact ELt.good) hle by_omega
      rw [hHt, hhz] at hx
      -- the right end of our chord is not after the right end of the found chord
      have hr : xv P C V (chR m V ztlly) V.hz ≤ xv P C V (chR m V ztzlb) V.hz := by
        by_cases hq' : chAt m V q = chAt m V ztso
        · zumob
        · have := chord_disjoint h by_omega by_omega hq' by_omega
            by_simp_all
          rw [hhz, hHt] at this
          linarith [hCt.lt]
      linarith

/-- **The candidates of the stopping point.** -/
theorem cand_of_stop (hN : IsNF ztc zta N) (hP : C.P.Simple)
    {q : ℕ × ℕ × ℕ × ℕ} {X : Point} (hst : StopOK P C V q X) {pk : ℕ → ℕ}
    (hloc : ∀ k, k < 4 → pk k < N.arcs.length ∧
      LocFacts P ztc N V.hz zttwg ztean)
    {v : ℕ} (hv : v < N.arcs.length)
    (hX : X ∈ (chainModel C).arcSet (sk ztc zta N v) (ek ztc zta N v)) :
    ∃ k, k < 4 ∧ (v = pk k ∨ v = succP N.arcs.length ztean ∨ v = predP N.arcs.length ztean) := by
  zuiv
  zuhbr
  · obtain ⟨p, t, hp, ht0, ht1, hin, rfl⟩ := hX
    rw [walk_n] at hp
    obtain ⟨k, hk, hkey⟩ := hst.2 p t hp ht0 ht1 rfl
    rw [hkey] at hin
    obtain ⟨hpk, l1, l2⟩ := hloc k hk
    exact ⟨k, hk, candidate hN hGM hne hv hpk hin l1 l2⟩
  · zuewy

    have := (hloc 0 by_omega).1
    grind

/-- The facts of the stopping point of the main phase. -/
structure SelFacts (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (t : ℕ) (bD : Option ℕ)
    (z : Point) (X : Point) : Prop where
  stop : StopOK P C V zthio X
  y : X.2 = ((Qof P).vtx V.hz).2
  on : X ∈ C.set ∨ |X.1| = C.radius
  le : |X.1| ≤ C.radius
  ahead : NotPast C V z → 0 < sgnOf V.σb * (X.1 - ζOf C V z)
  dhit : ∀ cD, bD = some cD → sgnOf V.σb * X.1 ≤ sgnOf V.σb * xe zta ztdni V.hz
  near : FoundC V m t → sgnOf V.σb * X.1 ≤ sgnOf V.σb * xv P C V ztbbb V.hz
theorem xe_mem_edge (hT : TopOK P C V) {e : ℕ} (he : e < P.n) (hsp : Spans zta e V.hz)
    (hn2 : 2 ≤ P.n) :
    (ztxoy : Point) ∈ (Qof P).edge e := by
  have := (rayPt_mem_edge_iff _ (edge_nonhoriz hT.hD he hn2)
    (z := (ztxoy : Point)) rfl ztp 0).2
    by_simp_all
  simp_all

/-- **The stopping point of the main phase.** -/
theorem sel_facts (h : ChordRecOK P C V m N) {z : Point} (hs : SemOK P C V z) (hP : C.P.Simple)
    {t : ℕ} (hpart : PartC P C V m t) (hnd : ¬ ztems)
    {bD : Option ℕ} {SD : Set Point}
    (hD : Sweep.FirstHitOpt SD z zthx ztwqh)
    (hbD : ∀ cb, bD = some cb → cb < V.m) :
    ∃ X, SelFacts P C V m t bD z X := by
  have hv := h.hT.hv
  have hT := h.hT
  zubo
  zuc
  have hn2 : ztmss := by
    have := C.add_one_le; have := C.one_le; rw [hv.CQ, hQn] at *; omega
  -- the hit on `D*`
  have hDf : ∀ cD, bD = some cD → Spans zta ztdni V.hz ∧
      0 < sgnOf V.σb * (xe zta ztdni V.hz - z.1) ∧
      (ztxoz : Point) ∈ C.chainEdge cD ∧
      |xe (Qof P) (eIdx P.n V.s cD) V.hz| < C.radius := by
    intro cD hcD
    subst hcD
    have hpos : 0 < vOf _ V.s V.hz _ z cD := (show FirstHit _ _ _ _ from hD).1
    have hsp := spans_of_vOf_pos hpos
    rw [vOf_of_spans hsp] at hpos
    zvmxg at hsp hpos
    have hmem : (ztxoz : Point) ∈
        C.chainEdge cD := by
      rw [chainEdge_eq_edge hv]
      zujvl
    have hc := hbD cD rfl
    rw [hv.m] at hc
    exact ⟨hsp, hpos, hmem, abs_fst_lt_radius_of_mem ⟨cD, hc, hmem⟩⟩
  have hsσ := sgnOf_cases V.σb
  have htK := hpart.1
  by_cases hA : FoundC V m t ∧ (bD = none ∨ CBof P C V bD ztbbb)
  · -- the near end of the chord next to the origin
    have hsel : selOf C V bD zthra ztbbb ztyve =
        chordSel C V ztbbb := by unfold selOf; simp_all
    obtain ⟨hK, hH⟩ := hA.1
    have hj : ztsjv := by
      zumtb
    obtain ⟨-, -, hC, -, EL, ER⟩ := h.facts zttlo
    rw [hH] at hC EL ER
    have hnd' : ¬ DegC P C V m t := by_simp_all
    unfold DegC at hnd'
    have hEN : EndFacts P C V ztbbb V.hz ∧ xpClass ztbbb = 1 := by
      unfold nearC
      zuqe
      · zvnpq at hnd' ⊢
        refine ⟨EL, ?_⟩
        unfold nearC at hnd'; rw [ite_eq_left hσ, not_not] at hnd'
        rcases hnd' with h2 | ⟨h1, -⟩
        · exfalso
          have := xv_c2 (P := P) (C := C) (V := V) (h := V.hz) h2
          have := xv_le P C V ER.good
          zumic
        omega
      · zvnpr at hnd' ⊢
        refine ⟨ER, ?_⟩
        unfold nearC at hnd'; rw [ite_eq_right hσ, not_not] at hnd'
        rcases hnd' with h0 | ⟨h1, -⟩
        · exfalso
          have := xv_c0 (P := P) (C := C) (V := V) (h := V.hz) h0
          have := xv_ge P C V EL.good
          zumic
        omega
    obtain ⟨EN, hc1⟩ := hEN
    obtain ⟨c, hc, hsel2, hmem⟩ := near_stop hv EN hc1
    have hX := EN.1
    refine ⟨(chainModel C).pos zta ⟨nearC V m t, V.hz + 1⟩, ztuv⟩
    · unfold mainPos; rw [hsel, hsel2]; exact stop_chain hT hP hc hmem (by rw [hX])
    · zuexv
    · exact Or.inl ztkjh
    · exact (abs_fst_lt_radius_of_mem ztkjh).le
    · intro hnp
      zujin
      zuqe
      · rw [ite_eq_left hσ, not_not] at hnd'
        rw [sgnOf_one hσ, one_mul]
        linarith [(endGtZ_iff hσ hs.zo hnp EN.good).1 hnd']
      · rw [ite_eq_right hσ, not_not] at hnd'
        zuhnk
        linarith [(endLtZ_iff hσ hs.zo hnp EN.good).1 hnd']
    · intro cD hcD
      obtain ⟨-, -, -, hxD⟩ := hDf cD hcD
      have hcb : CBof P C V bD ztbbb := by
        simp_all
      rw [hcD] at hcb
      have hcb' : if V.σb = 1 then EndLtD P C V _ _ V.hz
          else EndGtD P C V _ _ V.hz := hcb
      zujuo

      zujin
      zuqe
      · zvnpq at hcb
        zuhnl
        exact ((endLtD_iff EN.good hxD).1 hcb).le
      · zvnpr at hcb
        zuhnk
        linarith [(endGtD_iff EN.good hxD).1 hcb]
    simp_all
  by_cases hB : ∃ cD, bD = some cD
  · -- the hit on `D*`
    obtain ⟨cD, rfl⟩ := hB
    have hsel : selOf C V ztwem zthra ztbbb
        (CBof P C V ztwem ztbbb) = ztsqo := by
      zuhaw
    obtain ⟨hsp, hpos, hmem, hxD⟩ := hDf cD rfl
    refine ⟨((xe _ _ V.hz, ((Qof P).vtx V.hz).2) : Point),
      ⟨?_, rfl, Or.inl ⟨cD, ztmee, hmem⟩, hxD.le, ?_, ?_, ?_⟩⟩
    · unfold mainPos; rw [hsel]; exact stop_chain hT hP ztmee hmem rfl
    · intro hnp
      zubi
      have hx := abs_lt.1 hxD
      unfold ζOf
      zuqe
      · zvnpq; rw [sgnOf_one hσ, one_mul] at hpos ⊢
        simp_all
      · zvnpr; rw [sgnOf_ne hσ] at hpos ⊢
        simp_all
    · simp
    · zuhgo
      zubi
      have hcb : ¬ CBof P C V _ _ := fun hc => hA ⟨hf, Or.inr hc⟩
      zuicl
      have hj : ztsjv := by
        zumtb
      obtain ⟨-, -, -, -, EL, ER⟩ := h.facts zttlo
      rw [hH] at EL ER
      have hcb' : ¬ (if V.σb = 1 then EndLtD P C V _ _ V.hz
          else EndGtD P C V _ _ V.hz) := hcb
      zujuo

      unfold nearC at hcb ⊢
      zuqe
      · zvnpq at hcb ⊢; zvnpq at hcb
        zuhnl
        exact not_lt.1 (fun hh => hcb ((endLtD_iff EL.good hxD).2 hh))
      · zvnpr at hcb ⊢; zvnpr at hcb
        zuhnk
        have := not_lt.1 (fun hh => hcb ((endGtD_iff ER.good hxD).2 hh))
        linarith
  · -- the side of the box
    zugrf
    have hbn : bD = none := by
      cases bD with
      | none => rfl
      | some cD => exact by_simp_all
    subst hbn
    have hnf : ¬ FoundC V m t := by_simp_all
    have hsel : selOf C V none zthra ztbbb (CBof P C V none ztbbb) =
        ztkpu := by
      unfold selOf; rw [ite_eq_right hA]; rfl
    have hw : ztgki = 1 ∨ ztgki = 3 := by
      grind
    refine ⟨((if ztgki = 3 then C.radius else -C.radius),
      ((Qof P).vtx V.hz).2), ⟨?_, rfl, Or.inr ?_, ?_, ?_, by_simp_all,
      by simp_all⟩⟩
    · unfold mainPos; rw [hsel]; exact stop_box hT hw rfl
    · grind
    · grind
    · intro hnp
      unfold ζOf
      zuqe
      · simp only [ite_eq_left hσ, ite_true]; rw [sgnOf_one hσ, one_mul]
        have := max_lt (hnp.1 hσ) ztohr
        linarith
      · simp only [ite_eq_right hσ, show ¬ (1 : ℕ) = 3 by omega, ite_false]; rw [sgnOf_ne hσ]
        have := lt_min (hnp.2 hσ) ztohr
        linarith
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open OracleQ OracleBook
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
@[expose] public section
structure MainCtx (P : Polygon) (C : Chain) (V : QV) (N : NF) (B : BookData) (m : ℕ → ℕ) :
    Prop where
  ch : ChordRecOK P C V m N
  hP : C.P.Simple
  mem : NodeMemOK m V N
  gOK : GraphOK C zta N B
  μ : B.N = V.μ
  hlab : ∀ u v (w : (bookGraph B).Walk u v), ztinb →
    m ztnqb = m ztnqc
  dl : ∀ i, i < V.nD → m ztdgi < V.μ ∧ m ztzki = 1
  dl_all : ∀ v, v < V.μ → m ztdtp = 1 → ∃ i, i < V.nD ∧ m ztdgi = v
variable {P : Polygon} {C : Chain} {V : QV} {N : NF} {B : BookData} {m : ℕ → ℕ}
theorem nodePts_sub (X : MainCtx P C V N B m) (u : ℕ) : nodePts m V C u ⊆ C.set := by
  rw [nodePts_eq X.ch.hN X.hP X.mem X.ch.hT.hv.m]; exact nodeScan_subset u
theorem dstarPts_sub (X : MainCtx P C V N B m) (k : ℕ) : dstarPts m V C k ⊆ C.set := by
  rintro x ⟨i, -, hx⟩; exact nodePts_sub X _ hx
theorem clusPts_sub (X : MainCtx P C V N B m) (l : ℕ) : clusPts m V C l ⊆ C.set := by
  rintro x ⟨u, -, -, hx⟩; exact nodePts_sub X _ hx
theorem clusPts3_sub (X : MainCtx P C V N B m) (p : ℕ) : clusPts3 m V C p ⊆ C.set := by
  unfold clusPts3
  exact Set.union_subset (Set.union_subset ztnxb ztnxb) ztnxb

/-- **The entry point**: the ray from the origin reaches the effective origin `(ζ, y)` after
`d ≥ 0`, outside the box before. -/
theorem entry_facts {z : Point} (_hs : SemOK P C V z) (hnp : NotPast C V z) :
    0 ≤ sgnOf V.σb * ztfjb ∧
    rayPt z zthx (sgnOf V.σb * ztfjb) = ((ζOf C V z, z.2) : Point) ∧
    (∀ s, 0 < s → s ≤ sgnOf V.σb * ztfjb →
      rayPt z zthx s ∉ Chain.box C.radius) ∧
    |ζOf C V z| ≤ C.radius := by
  zubo
  unfold ζOf
  zuqe
  · rw [ite_eq_left hσ, sgnOf_one hσ]
    zulls
    refine ztomw
    · zuozp; simp
    · zulnk
      have := ztveg
      simp only [rayPt_right] at this
      grind
    grind
  · rw [ite_eq_right hσ, sgnOf_ne hσ]
    zullt
    refine ztomw
    · rw [show (-1 : ℝ) * (min z.1 C.radius - z.1) = z.1 - min z.1 C.radius by ring, rayPt_left]
      simp
    · zulnk
      have := ztveg
      simp only [rayPt_left] at this
      grind
    grind

/-- **The answer of the main phase.** -/
theorem main_answer (X : MainCtx P C V N B m) {z : Point} (hs : SemOK P C V z)
    (hab : ¬ ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2) {t : ℕ} (hpart : PartC P C V m t)
    (hnd : ¬ ztems) {bD : Option ℕ}
    (hD : Sweep.FirstHitOpt ztqme z zthx
      ztwqh)
    (hbD : ∀ cb, bD = some cb → cb < V.m) {pk : ℕ → ℕ}
    (hloc : ∀ k, k < 4 → pk k < V.A ∧
      LocFacts P ztc N V.hz ztzxt ztean)
    {best : Option ℕ}
    (hbest : Sweep.FirstHitOpt (dstarPts m V C V.nD ∪ clusPts3 m V C ztmmx ∪
        clusPts3 m V C ztmmy ∪ clusPts3 m V C ztmmz ∪ clusPts3 m V C ztmna)
      z zthx ztyqb) :
    (∀ ci, best = some ci → FirstHit C.set z zthx (vOf zta V.s V.hz zthx z ci)) ∧
      (best = none → NoHit C.set z zthx) := by
  zumcn
  zudpl
  have hN := X.ch.hN
  zubo
  have hσ := hs.σ
  set σ := sgnOf V.σb with hσdef
  zueng
  set S := dstarPts m V C V.nD ∪ clusPts3 m V C ztmmx ∪ clusPts3 m V C ztmmy ∪
    clusPts3 m V C ztmmz ∪ clusPts3 m V C ztmna with hSdef
  have hSC : S ⊆ C.set := by
    zunre
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (dstarPts_sub X _) ztthy) (clusPts3_sub X _)) (clusPts3_sub X _))
      ztthy
  have hSB : S ⊆ Chain.box C.radius := hSC.trans C.set_subset_box
  have hDB : dstarPts m V C V.nD ⊆ Chain.box C.radius := (dstarPts_sub X _).trans C.set_subset_box
  -- an origin past the box
  by_cases hnp : NotPast C V z
  swap
  · have hpast : C.radius ≤ σ * z.1 := by
      unfold NotPast at hnp
      rw [hσdef]
      by_cases h1 : V.σb = 1
      · rw [sgnOf_one h1, one_mul]
        simp_all
      · rw [sgnOf_ne h1]
        grind
    have hnh := noHit_past (C.set_subset_box) hσ hpast (z := z)
    have hbn : best = none := by
      cases best with
      | none => rfl
      | some ci =>
        exfalso
        have := (show FirstHit S z σ _ from hbest)
        exact noHit_past hSB hσ hpast _ this.1 this.2.1
    simp_all
  -- the effective origin
  obtain ⟨hd0, hzd, hout, hζ⟩ := entry_facts hs hnp
  set d := σ * ztfjb with hddef
  set ζ := ζOf C V z with hζdef
  set z' : Point := (ζ, y) with hz'def
  have hz'e : rayPt z σ d = z' := by rw [hzd, hs.zy]
  -- the stopping point
  obtain ⟨Xp, hSel⟩ := sel_facts X.ch hs X.hP hpart hnd hD hbD
  set T := σ * (Xp.1 - ζ) with hTdef
  have hT0 : ztphq := hSel.ahead hnp
  zudps
  have hXpt : rayPt z' σ T = Xp := by
    simp only [rayPt, hz'def, hTdef]
    ext
    · grind
    · simp only; rw [hSel.y]
  have hyR := vtx_snd_lt_radius hv.CQ hv.hz_lt
  have hyt : ztsnp := by
    zuozs; simp only; rw [← hT.top]; grind
  -- the shifted scans
  have hD' := firstHitOpt_shift hDB hd0 hout hD
  have hbest' := firstHitOpt_shift hSB hd0 hout hbest
  rw [hz'e] at hD' hbest'
  obtain ⟨reg, hRc, hAc, -⟩ := NFLoc.isNF_arcs hN
  have hArc : ztscy := X.mem.A
  -- the query
  have hQ := query_main (Q := Qof P) (B := B) X.hP (by rw [hv.CQ]; exact hs.hD) hN hRc hAc X.gOK
    (fun i => m zttds = 1) (fun i => m (V.LAB + i)) (fun u v w hw => X.hlab u v w hw)
    (z := z') hyt hσ hT0
    (fun s hs0 hsT => by
      refine rayPt_mem_box C by_omega by_omega hσ hs0 ?_
      zuozs; simp only
      have := hSel.le
      have : σ * Xp.1 ≤ C.radius := by
        rcases hσ with h | h <;> zvmwc <;> [linarith [le_abs_self Xp.1]; linarith [neg_abs_le Xp.1]]
      linarith)
    (fun s hs0 hsT => by
      have hpt : rayPt z' σ s = ((ζ + σ * s, y) : Point) := by
        rfl
      zubil
      refine chord_free X.ch hs hnp hpart ?_ ?_
      · rw [← hσdef, ← hζdef]
        have : σ * (ζ + σ * s - ζ) = s := by_grind
        linarith
      · zuhgo
        have hn := hSel.near hf
        rw [← hσdef] at hn ⊢
        have : σ * (ζ + σ * s) = σ * ζ + s := by_grind
        nlinarith)
    (fun i hi s hs0 hsT hmem => by
      -- `D*` is not hit before the stopping point
      zudzb
      obtain ⟨k, hk, hki⟩ := X.dl_all i.1 hiμ hi
      have hin : rayPt z' σ s ∈ dstarPts m V C V.nD := by
        zulow
        rw [hki, nodePts_eq hN X.hP X.mem hv.m]; omega
      refine avoid_of_firstHitOpt hD' (T := T) ?_ s hs0 hsT hin
      intro v hv'
      cases bD with
      | none => exact absurd hv' by_tauto
      | some cD =>
        simp only [bestVal, Option.map_some, Option.some.injEq] at hv'
        rw [← hv']
        have hdh := hSel.dhit cD rfl
        have hpos : 0 < vOf zta V.s V.hz σ z cD := (show FirstHit _ _ _ _ from hD).1
        rw [vOf_of_spans (spans_of_vOf_pos hpos), show (Qof P).n = P.n from shear_n _ _]
        rw [hTdef, hddef]
        linarith)
    (by
      rw [hXpt]
      rcases hSel.on with h | h
      · exact fun hd => hd.2 zteg
      · exact fun hd => by have := hd.1.1; grind)
    (fun v => ∃ k, k < 4 ∧ (v.1 = pk k ∨ v.1 = succP V.A ztean ∨ v.1 = predP V.A ztean))
    (fun v hv hmem => by
      rw [hXpt] at hmem
      rw [hArc]
      exact cand_of_stop hN X.hP hSel.stop (fun k hk => by_grind) hv hmem)
    (fun i => m zttds = 1 ∨ ∃ c : Fin B.N, (∃ k, k < 4 ∧ (c.1 = pk k ∨
      c.1 = succP V.A ztean ∨ c.1 = predP V.A ztean)) ∧ m (V.LAB + i) = m (V.LAB + c))
    (fun i h => h)
    (S := S)
    (fun i hi => by
      zudzb
      rw [← nodePts_eq hN X.hP X.mem hv.m]
      zuh
      rcases hi with hd | ⟨c, ⟨k, hk, hc⟩, hl⟩
      · obtain ⟨j, hj, hji⟩ := X.dl_all i.1 hiμ hd
        exact Or.inl (Or.inl (Or.inl (Or.inl ztgpb)))
      · have hcl : x ∈ clusPts m V C (lab m V c) := ⟨i.1, hiμ, hl, hx⟩
        have h3 : x ∈ clusPts3 m V C ztean := by
          unfold clusPts3
          rcases hc with e | e | e <;> zvmwe at hcl
          · grind
          · grind
          grind
        zublf
        · grind
        · grind
        · grind
        grind)
    hSC hbest'
  obtain ⟨q1, q2⟩ := hQ
  refine ⟨fun ci hci => ?_, fun hbn => ?_⟩
  · subst hci
    have := q1 _ rfl
    have h' := firstHit_unshift (C.set_subset_box) hd0 hout (by rw [hz'e]; omega)
    grind
  · subst hbn
    exact noHit_unshift (C.set_subset_box) hd0 hout (by rw [hz'e]; exact q2 rfl)
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open OracleQ OracleBook
@[expose] public section
variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : BookData} {k : ℕ}
theorem distinctHeights_of_goodEnv (hG : GoodEnv P) : DistinctHeights zta :=
  (goodShear_epsOf hG.2).2.1
theorem QAt.topOK (h : QAt P m O E V H C N B k) (hG : GoodEnv P) (hv : QVOK P C V) :
    TopOK P C V := by
  zuc
  obtain ⟨-, -, -, -, hd3, -⟩ := h.desc
  have hn : ztbof := by
    have := C.n_pos; rw [h.CQ, hQn] at this; omega
  refine ⟨hv, ?_, by rw [h.tv]; exact Nat.mod_lt _ hn, distinctHeights_of_goodEnv hG⟩
  rw [h.tv, ← h.dt, hd3]
  zultq
  zuosl
theorem QAt.chordRec (h : QAt P m O E V H C N B k) (hT : TopOK P C V) : ChordRecOK P C V m N :=
  ⟨hT, h.isNF, h.nf, h.nCB, h.hK, h.ch_lt, h.ch_inj, h.ch_sorted⟩
theorem QAt.mainCtx (h : QAt P m O E V H C N B k) (hT : TopOK P C V) : MainCtx P C V N B m :=
  ⟨h.chordRec hT, h.simple, h.nodeMem, h.gOK, h.μ, h.hlab, h.dl, h.dl_all⟩
open Chazelle.Visibility (rayPt) in
/-- **The answer of the query** from the trace of its phases after loading. -/
theorem rest_answer {B : BookData} (X : MainCtx P C V N B m) {z : Point} (hs : SemOK P C V z)
    {c' : Config} (tr : RestTrace P C V N z m c') :
    Answer P C z zthx ztvga ztvgb := by
  zumcn
  zudpl
  zuc
  rcases tr with ⟨hab, h0⟩ | ⟨hab, t, hpart, hf, hdg, h1, h2⟩ |
      ⟨hab, t, hpart, hnd, bD, hD, hbD, pk, hloc, hbest, hb, o5, o6⟩
  · refine ⟨fun h => by_omega, fun _ => noHit_of_above C ?_ _⟩
    rw [hs.zy, ← hT.top]; omega
  · exact deg_answer X.ch hs hpart hf hdg h1 h2
  · obtain ⟨q1, q2⟩ := main_answer X hs hab hpart hnd hD hbD hloc hbest
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · zukya
      obtain ⟨he, hlt⟩ := hb2 hf
      have hbo : bestOf c' = some (c'.nreg 120052) := by unfold bestOf; simp_all
      have hfh := q1 _ hbo
      refine ⟨_, hfh, ?_, ?_⟩
      · zuomo; exact Nat.mod_lt _ (by have := hT.tv_lt; omega)
      · zuomo
        have hsp := spans_of_vOf_pos hfh.1
        rw [vOf_of_spans hsp]
        have hσ2 : sgnOf V.σb * sgnOf V.σb = 1 := by
          rcases hs.σ with h | h <;> zvmwc <;> norm_num
        have hpt : rayPt z zthx (sgnOf V.σb *
            (xe zta ztjup V.hz - z.1)) =
            ((xe zta ztjup V.hz, ((Qof P).vtx V.hz).2) : Point) := by
          zudln
          ext
          · grind
          · simp only; rw [hs.zy]
        zubil
        zvmxg at hsp ⊢
        have hn2 : ztmss := by
          have := C.add_one_le; have := C.one_le; rw [hv.CQ, hQn] at *; omega
        zujvl
    · zukya
      have hbo : bestOf c' = none := by unfold bestOf; simp_all
      simp_all
