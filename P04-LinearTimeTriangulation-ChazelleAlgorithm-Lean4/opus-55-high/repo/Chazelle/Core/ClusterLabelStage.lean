module

public import Chazelle.MacT
public import Chazelle.Core.ClusterStageC1
public import Chazelle.Programs.Tactics
public import Chazelle.Core.OracleBook
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.SpecNF
public import Chazelle.Core.FactsAttach

namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs Chazelle.Separator
@[expose] public section
def labLay (g : GV) : Lay := ⟨g.bO, g.bR, g.bV, g.base 0, g.base 1, g.base 48, g.base 2,
  g.base 3, g.base 4, g.base 5, g.μ, g.N⟩
theorem labLay_good {g : GV} {W : ℕ} (hμ : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0)
    (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) :
    (labLay g).Good W := by
  zuny

  have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b2 := g.base_eq 2; have b3 := g.base_eq 3
  have b4 := g.base_eq 4; have b5 := g.base_eq 5; have b48 := g.base_eq 48
  refine ztbij
  all_goals simp only [labLay, Disj] at *
  · grind
  zuiqs

/-- The layout registers of the labelling. -/
def labCopies : List ztw :=
  [(130100, 130021), (130101, 130022), (130102, 130023), (130103, 130030), (130104, 130031),
   (130105, 130078), (130106, 130032), (130107, 130033), (130108, 130034), (130109, 130035),
   (130110, 130011)]

/-- **The labelling.** -/
def labS : Stmt := .seq (copies labCopies) labelStmt

/-- The registers written by `labS`. -/
def LabRG (r : ℕ) : Prop := (130100 ≤ r ∧ r ≤ 130142)
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
theorem labS_exec {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M)
    (hF : ∀ u, u < g.μ → c.nmem ztrk < g.N ∧ c.nmem ztzlw = u)
    (hzero : ∀ d, d < g.N → c.nmem ztefe = 0)
    (hμ : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W labS c c' k ∧ k ≤ 120 * g.μ + 50 * g.N + 30 ∧ WordsBounded W c' ∧
      (∀ r, ¬ LabRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧
      (∀ a, ¬ (g.base 2 ≤ a ∧ a < g.base 6) → c'.nmem a = c.nmem a) ∧
      ∀ x y, x < g.μ → y < g.μ → c.nmem (g.base 48 + x) ≠ 1 → c.nmem (g.base 48 + y) ≠ 1 →
        (c'.nmem (g.base 2 + x) = c'.nmem (g.base 2 + y) ↔
          (primalEnv c.nmem g.bO g.bR g.bV ztmkd zteac ztjwz g.μ g.N).Reach x y) := by
  zuuv
  have b2 := g.base_eq 2; have b6 := g.base_eq 6; have b5 := g.base_eq 5
  have b3 := g.base_eq 3; have b4 := g.base_eq 4
  set Y := labLay g with hY
  have hYg : Y.Good W := labLay_good hμ hO hR hV hW
  unfold labS
  obtain ⟨c1, e1, hw1, h1, h2, hm1, hr1, hrm1, ho1⟩ := copies_exec (P := P) hw labCopies
    (b := 130090) by_decide by_decide
  have g1 : ∀ r, (r < 130100 ∨ 130110 < r) → c1.nreg r = c.nreg r := fun r hr =>
    h2 r (fun p hp h => by
      have := (show ∀ p ∈ labCopies, 130100 ≤ p.1 ∧ p.1 ≤ 130110 by decide) p hp; omega)
  have hG1 : ztido := hG.frame ztyqs
  have cp : ∀ d s, ztfqw ∈ labCopies → c1.nreg d = c.nreg s := fun d s h => h1 _ h
  have hR0 : Regs0 Y c1 := ⟨hG1.one,
    by rw [cp 130100 130021 by_decide]; exact hG.rO,
    by rw [cp 130101 130022 by_decide]; exact hG.rR,
    by rw [cp 130102 130023 by_decide]; exact hG.rV,
    by rw [cp 130103 130030 by_decide]; exact hG.rbase 0 by_omega,
    by rw [cp 130104 130031 by_decide]; exact hG.rbase 1 by_omega,
    by rw [cp 130105 130078 by_decide]; exact hG.rbase 48 by_omega,
    by rw [cp 130106 130032 by_decide]; exact hG.rbase 2 by_omega,
    by rw [cp 130107 130033 by_decide]; exact hG.rbase 3 by_omega,
    by rw [cp 130108 130034 by_decide]; exact hG.rbase 4 by_omega,
    by rw [cp 130109 130035 by_decide]; exact hG.rbase 5 by_omega,
    by rw [cp 130110 130011 by_decide]; exact hG.rμ⟩
  have henv : Y.env c1.nmem =
      primalEnv c.nmem g.bO g.bR g.bV ztmkd zteac ztjwz g.μ g.N := by
    tauto
  have hok : ztrzc := by rw [henv]; exact primalEnv_ok hmap hF
  have hsym : (Y.env c1.nmem).Sym := by
    rw [henv]
    refine primalEnv_sym hmap ztbzy
    have ho : c.nmem zttkx < g.N := by zunxo; omega
    grind
  obtain ⟨c', k, e, hk, hw', hfr, hlt, hlab⟩ := labelStmt_exec (P := P) hYg hw1 hR0 hok hsym
  have hnv : Y.nv = g.μ := rfl
  have hYN : Y.N = g.N := rfl
  refine ⟨c', labCopies.length + k, .seq e1 e, by rw [show labCopies.length = 11 from rfl]; omega, hw', fun r hr => ?_, by rw [hfr.2.1, hr1],
    by rw [hfr.2.2.1, hrm1], by rw [hfr.2.2.2.1, ho1], fun a ha => ?_, fun x y hx hy h1x h1y => ?_⟩
  · rw [hfr.1 r (by unfold LScr Scr; unfold LabRG at hr; omega)]
    exact g1 r (by unfold LabRG at hr; omega)
  · rw [hfr.2.2.2.2 a (by
      simp only [Lay.Written, hY, labLay]
      grind), hm1]
  · have hx' : (Y.env c1.nmem).vb x ≠ 1 := by
      show view c1.nmem ztjwz g.μ x ≠ 1
      rw [view_lt hx, hm1]; omega
    have hy' : (Y.env c1.nmem).vb y ≠ 1 := by
      show view c1.nmem ztjwz g.μ y ≠ 1
      rw [view_lt hy, hm1]; omega
    have := hlab x y by_omega by_omega hx' hy'
    rw [henv] at this
    simp only [labV, hY, labLay, view_lt hx, view_lt hy] at this
    omega
end proofs
def bumpS : Stmt := .whileLtN ALLOC 130086 (.instr ztrhv)

/-- The outputs. -/
def outS : Stmt := block [.copyN 130004 130078, .copyN 130005 130032]
section proofs
variable {P : Polygon} {W : ℕ}
theorem bumpS_exec {c : Config} (hw : WordsBounded W c) {E : ℕ} (h1 : c.nreg 130001 = 1)
    (hE : c.nreg 130086 = E) (hA : c.nreg ALLOC ≤ E) (hEW : E ≤ W) :
    ∃ c' k, Exec P W bumpS c c' k ∧ k ≤ 3 * (E - c.nreg ALLOC) + 2 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = E ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      ztjn ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  obtain ⟨c', k, e, ⟨hw', hA', hr', hm', hrr', hrm', ho'⟩, htest, hk, hψ⟩ :=
    SortR.whileLtN_potential_lb (P := P) (W := W) (a := ALLOC) (b := 130086)
    (body := .instr ztrhv)
    (fun c' => WordsBounded W c' ∧ c'.nreg ALLOC ≤ E ∧ ztjn ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output)
    (fun c' => 3 * (E - c'.nreg ALLOC)) ztcht ztbms
    (fun c1 ⟨hw1, hA1, hr1, hm1, hrr1, hrm1, ho1⟩ htest => by
      have e1 : ztpmk := by_simp_all
      have e2 : c1.nreg 130086 = E := by_simp_all
      zukqv
      have ex := Exec.addN (P := P) hw1 ALLOC ALLOC 130001 by_omega
      refine ⟨_, 1, ex, ⟨ex.wb_right, ?_, fun r hr => ?_, hm1, hrr1, hrm1, ho1⟩, ?_, ?_⟩
      · simp_all
      · simp_all
      · zudbz
      simp_all)
    ⟨hw, hA, fun r _ => rfl, rfl, rfl, rfl, rfl⟩
  have e2 : c'.nreg 130086 = E := by_simp_all
  zukqv
  exact ⟨c', k, e, hk, hw', by_omega, hψ, hr', hm', hrr', hrm', ho'⟩
end proofs
open Chazelle.Separator.CombMap
def phase1 : Stmt := .seq setupStmt (.seq stageA (.seq stageB1 (.seq stageB2 (.seq stageC stageD))))

/-- The cost bound of the first phase. -/
def cost1 (g : GV) : ℕ := (7 * g.μ + 8 * g.L + 100) +
  ((62 * g.N + 84 * g.μ + 12 * g.μ * g.L + 7 * g.L + 72) + ((172 * g.N + 11 * g.μ + 150) +
  ((280 * g.N + 12 * g.N * g.L + 7 * g.L + 120) + ((80 * g.μ + 6 * g.L + 60) +
  (40 * zttld + 40)))))

/-- The block of a vertex, read from memory. -/
def boOf (g : GV) (m : ℕ → ℕ) : ℕ → ℕ :=
  blkOf g.μ ztwnn ztuq ztup

/-- The key of a vertex, read from memory. -/
def keyOf' (g : GV) (m : ℕ → ℕ) : ℕ → ℕ := fun v => m ztzfz

/-- **The facts after the first phase.** -/
structure PostD (g : GV) {F : Type} [Fintype F] [DecidableEq F]
    (M : CombMap ztbry F ztbrx) (T : SpanTree M) (a : F → Fin g.N)
    (ha : ∀ f, M.face ztdbz = f) (C : CoTree ztqc) (R : BTree)
    (first : Fin g.μ → Fin g.N) (preE slot : ℕ → ℕ) (ρ : ℕ) (W : ℕ) (m : ℕ → ℕ) : Prop where
  sf : SFacts M T a ha C R first preE slot ztqxy g.k' ztdom ztmol g.A0 g.U W m
  head : ∀ d : Fin g.N, T.level ztbyq ≤ T.level ztbmc + 1
  lv : ∀ l, l < g.μ → LvOK g m ztdom l
  ρ_lt : ρ < g.k'
  rmin : ∀ r, r < g.k' → cntBelow ztyqy g.μ ρ ≤
    cntBelow ztyqy g.μ r
  cnt : ∀ b, b < g.μ → m ztys = cntLt ztnsn g.μ ztds
  pos : ∀ v, v < g.μ → m ztczp =
    if boOf g m v < g.μ then plPos g.μ ztnsn zttqu v else g.μ
  act : ∀ v, v < g.μ → boOf g m v < g.μ → m (g.base 43 + plPos g.μ ztnsn zttqu v) = v
  df : ∀ v, v < g.μ → m ztvz = 0
  map : MapArrays m g.bO g.bR g.bV g.μ g.N M
  firstF : ∀ u, u < g.μ → m ztrk < g.N ∧ m ztzly = u
  zero : ∀ d, d < g.N → m ztefe = 0
theorem B2F.congr {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face ztdbz = f} {C : CoTree ztqc} {R : BTree} {preE slot : ℕ → ℕ}
    {m m' : ℕ → ℕ} (h : B2F g C R preE slot m)
    (he : ∀ x, (g.base 26 ≤ x ∧ x < g.base 30) ∨
      (g.A0 + 54 * g.U + g.L * g.U ≤ x ∧ x < g.A0 + 54 * g.U + 2 * ztesx) → m' x = m x) :
    B2F g C R preE slot m' := by
  zueqs
  have b26 := g.base_eq 26; have b28 := g.base_eq 28; have b29 := g.base_eq 29
  have b30 := g.base_eq 30
  have hLN : ∀ j, j < g.L → ∀ x, x < g.N → j * g.N + x < g.L * g.U := fun j hj x hx => by
    have : ztl * g.N ≤ g.L * g.U := Nat.mul_le_mul by_omega by_omega
    grind
  refine ⟨fun x hx => ?_, fun x hx => ?_, h.r0, fun x hx => ?_, fun x hx => ?_, h.R_ok, h.R_n,
    h.R_up, h.R_root, h.R_pre, fun j hj x hx => ?_⟩
  · have := x.2; zunfr; exact h.fpar x hx
  · zunfr; exact h.fpar_lt x hx
  · zunfr; exact h.pre x hx
  · zunfr; exact h.sz x hx
  · have := hLN j hj x hx
    rw [he _ ztxgk]; exact h.up_tab j hj x hx

/-- The block of a light-free level is a block index. -/
theorem shift_div_lt {l cs k μ : ℕ} (hk : 0 < k) (hcs : cs < k) (_hkμ : k ≤ μ) (hl : l < μ) :
    ztetu / k < μ := by
  zulph
  obtain ⟨t, ht⟩ : ∃ t, μ = t + 1 := ⟨μ - 1, by_omega⟩
  zukwh
  have : t ≤ t * k := Nat.le_mul_of_pos_right _ hk
  omega
variable {f f' : ℕ → ℕ}
theorem cntBelow_congr {n r : ℕ} (h : ∀ v, v < n → f v = f' v) :
    cntBelow f n r = cntBelow f' n r := by
  unfold cntBelow; congr 1
  grind
theorem cntLt_congr {n j : ℕ} (h : ∀ v, v < n → f v = f' v) :
    cntLt f n j = cntLt f' n j := by
  unfold cntLt; congr 1
  grind
theorem plPos_congr {μ : ℕ} {bo bo' key key' : ℕ → ℕ} (hb : ∀ w, w < μ → bo w = bo' w)
    (hk : ∀ w, w < μ → key w = key' w) {v : ℕ} (hv : v < μ) :
    plPos μ bo key v = plPos μ bo' key' v := by
  unfold plPos rk
  rw [cntLt_congr hb, hb v hv]
  zugjz
  grind
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
open Classical in
/-- **The first phase.** -/
theorem phase1_exec {c : Config} (hw : WordsBounded W c) {g : GV} (hg : gOf c = g)
    {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} (hpl : M.Planar)
    (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M)
    (hμ : 0 < g.μ) (hμN : g.μ ≤ g.N) (hB2 : c.nreg 130000 + 2 ≤ W)
    (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0)
    (hV : g.bV + g.N ≤ g.A0) (hk : 1 ≤ g.k)
    (hEND : g.END ≤ W) :
    ∃ c' k, Exec P W phase1 c c' k ∧ k ≤ cost1 g ∧ WordsBounded W c' ∧ GR g c' ∧
      ztfvt ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ (∀ a, a < g.A0 → c'.nmem a = c.nmem a) ∧
      ∃ (T : SpanTree M) (a : F → Fin g.N) (ha : ∀ f, M.face ztdbz = f)
        (C : CoTree ztqc) (R : BTree) (first : Fin g.μ → Fin g.N)
        (preE slot : ℕ → ℕ) (ρ : ℕ), PostD g M T a ha C R first preE slot ρ W c'.nmem := by
  have hU := g.U_ge; have hE := g.END_eq; have hLU := g.L_le_U; have hP := g.two_pow_L
  have hL : 0 < g.L := by
    grind
  zucar

  have hN : 0 < g.N := by_omega
  have b37 := g.base_eq 37; have b38 := g.base_eq 38; have b39 := g.base_eq 39
  have b40 := g.base_eq 40; have b0 := g.base_eq 0; have b1 := g.base_eq 1; have b2 := g.base_eq 2; have b3 := g.base_eq 3; have b5 := g.base_eq 5; have b6 := g.base_eq 6; have b7 := g.base_eq 7; have b24 := g.base_eq 24; have b26 := g.base_eq 26; have b29 := g.base_eq 29
  have b30 := g.base_eq 30; have b32 := g.base_eq 32; have b33 := g.base_eq 33; have b35 := g.base_eq 35; have b36 := g.base_eq 36; have b41 := g.base_eq 41; have b42 := g.base_eq 42; have b45 := g.base_eq 45; have b48 := g.base_eq 48; have b49 := g.base_eq 49
  unfold phase1
  -- setup
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hG1, hr1, hrr1, hrm1, ho1⟩ :=
    setupStmt_exec (P := P) hw hB2 (hg ▸ hEND)
  rw [hg] at hk1 hG1
  -- stage A
  obtain ⟨c2, k2, e2, hk2, hw2, hG2, hf2, T, hA2⟩ := stageA_exec (P := P) hw1 hG1
    by_simp_all hpl.1 hμ hμN hO hR hV hL hEND
  -- stage B1
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, a, ha, hB3⟩ := stageB1_exec (P := P) hw2 hG2 hA2 hμ hO hR
    hV hEND
  have hG3 : ztkzy := hG2.frame (fun r hr => hf3.1 r ztdcl)
  have hA3 : AF g M T c3.nmem := hA2.congr zteyj (fun x hx => hf3.2.2.2.2 x (by
    unfold KeepA at hx; omega))
  -- stage B2
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, C, R, preE, slot, hB4⟩ := stageB2_exec (P := P) hw3 hG3 hA3
    hB3 hpl.1 hN hL hO hR hV hEND
  have hG4 : ztsbn := hG3.frame (fun r hr => hf4.1 r ztdcl)
  have hLU' : g.L * g.U ≥ 0 := Nat.zero_le _
  have hA4 : AF g M T c4.nmem := hA3.congr zteyj (fun x hx => hf4.2.2.2.2 x (by
    unfold KeepA at hx; omega))
  have hB14 : B1F g M T a ha c4.nmem := hB3.congr (fun x h1 h2 => hf4.2.2.2.2 x by_omega)
  -- stage C
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, hhalf5, hpow5, ρ, hρ, hlv5, hmin5⟩ := stageC_exec (P := P)
    hw4 hG4 hk' hkμ (lev := fun v => c4.nmem ztjc) ztqoh
    (fun v hv => by have := hA4.lev ztbbl; have := hA4.lev_lt ztbbl; simp_all) hEND
  have hG5 : GR g c5 := hG4.frame (fun r hr => hf5.1 r ztdcm)
  have k45 : ∀ x, ¬ CMem g x → c5.nmem x = c4.nmem x := fun x hx => hf5.2.2.2.2 x hx
  have hA5 : AF g M T c5.nmem := hA4.congr zteyj (fun x hx => k45 x (by
    unfold KeepA at hx; unfold CMem; omega))
  have hB15 : B1F g M T a ha c5.nmem := hB14.congr (fun x h1 h2 => k45 x ztggk)
  have hB25 : B2F g C R preE slot c5.nmem := hB4.congr (fun x hx => k45 x (by
    unfold CMem; omega))
  have hlev5 : ∀ v, v < g.μ → c5.nmem ztjc = c4.nmem ztjc := fun v hv =>
    k45 _ ztggk
  -- stage D
  have hRn := hB25.R_n
  have hpre_lt : ∀ i, i < g.N → c5.nmem ztfsb < g.N := fun i hi => by
    rw [hB25.pre i hi, ← hRn]; exact hB25.R_pre.pre_lt hB25.R_ok by_omega
  have hpre_inj : ∀ i j, i < g.N → j < g.N → c5.nmem ztfsb = c5.nmem ztrqs →
      i = j := fun i j hi hj h => by
    rw [hB25.pre i hi, hB25.pre j hj] at h
    exact BTree.PreInv.pre_inj hB25.R_ok hB25.R_pre by_omega by_omega h
  have hlvx : ∀ l, l < g.μ → LvOK g c5.nmem ztdom l := hlv5
  obtain ⟨c6, k6, e6, hk6, hw6, hf6, hcnt6, hpos6, hact6, hdf6⟩ := stageD_exec (P := P) hw5 hG5
    (lev := fun v => c5.nmem ztjc) (hl := fun l => c5.nmem ztcnm)
    (blk := fun l => c5.nmem ztcdg) hpre_lt hpre_inj
    (fun v hv => hA5.first_lt v hv) (fun v hv => hA5.first_v v hv)
    (fun i hi => by rw [(hA5.map ztoot).2.2]; omega) hV
    ztqoh (fun v hv => by have := hA5.lev ztbbl; have := hA5.lev_lt ztbbl; simp_all)
    ztqnz
    (fun l hl => by obtain ⟨-, -, -, h36⟩ := hlvx l hl; rw [h36]; split_ifs <;> omega)
    ztqnz
    (fun l hl hne => by
      obtain ⟨-, -, h35, h36⟩ := hlvx l hl
      rw [h35]
      rw [h36] at hne
      exact shift_div_lt hk' by_omega hkμ hl) hEND
  have hG6 : GR g c6 := hG5.frame (fun r hr => hf6.1 r ztun)
  have k56 : ∀ x, ¬ DMem g x → c6.nmem x = c5.nmem x := fun x hx => hf6.2.2.2.2 x hx
  have hA6 : AF g M T c6.nmem := hA5.congr zteyj (fun x hx => k56 x (by
    unfold KeepA at hx; unfold DMem; omega))
  have hB16 : B1F g M T a ha c6.nmem := hB15.congr (fun x h1 h2 => k56 x ztxg)
  have hB26 : B2F g C R preE slot c6.nmem := hB25.congr (fun x hx => k56 x (by
    unfold DMem; omega))
  have hlv6 : ∀ l, l < g.μ → LvOK g c6.nmem ztdom l := fun l hl => by
    obtain ⟨h1, h2, h3, h4⟩ := hlvx l hl
    zudfi
    · zunas; exact h1
    · zunas; exact h2
    · zunas; exact h3
    · zunas; exact h4
  have hSF := sfacts_of (W := W) hA6 hB16 hB26 hpl hμN hO hV hEND hL
    (fun w hw' => by zunas; exact hhalf5 w hw')
    (fun j hj => by zunas; exact hpow5 j hj) hk' hlv6
  have hbo : ∀ w, w < g.μ → blkOf g.μ (fun v => c5.nmem ztjc)
      (fun l => c5.nmem ztcnm) (fun l => c5.nmem ztcdg) w =
      boOf g c6.nmem w := fun w hw => by
    have hl := hA5.lev_lt ztdxo; have e := hA5.lev ztdxo
    zujpc
    have hlw : c5.nmem ztcnl < g.μ := by_omega
    zujog
    rw [k56 ztcnl ztxg, k56 (g.base 36 + c5.nmem ztcnl)
      ztxg, k56 (g.base 35 + c5.nmem ztcnl) ztxg]
  have hkey : ∀ w, w < g.μ → c5.nmem ztzfy =
      keyOf' g c6.nmem w := fun w hw => by
    have := hA5.first_lt w hw
    zulse
    rw [k56 ztfrz ztxg, k56 ztzfy
      ztxg]
  have hm06 : ∀ x, x < g.A0 → c6.nmem x = c.nmem x := fun x hx => by
    rw [k56 x ztxg, k45 x ztggk,
      hf4.2.2.2.2 x by_omega, hf3.2.2.2.2 x by_omega, hf2.2.2.2.2 x zteqo, hm1]
  refine ⟨c6, k1 + ztrd,
    .seq e1 ztvb, by unfold cost1; omega, hw6, hG6,
    fun r hr => ?_, by rw [hf6.2.1, hf5.2.1, hf4.2.1, hf3.2.1, hf2.2.1, hrr1],
    by rw [hf6.2.2.1, hf5.2.2.1, hf4.2.2.1, hf3.2.2.1, hf2.2.2.1, hrm1],
    by rw [hf6.2.2.2.1, hf5.2.2.2.1, hf4.2.2.2.1, hf3.2.2.2.1, hf2.2.2.2.1, ho1], hm06,
    T, a, ha, C, R, _, preE, slot, ρ, ⟨hSF, hA6.head_le, hlv6, hρ, fun r hr => ?_,
    fun b hb => ?_, fun v hv => ?_, fun v hv hbv => ?_, hdf6, hA6.map,
    fun u hu => ⟨hA6.first_lt u hu, hA6.first_v u hu⟩, hA6.zero⟩⟩
  · rw [hf6.1 r (by unfold StDRG; omega), hf5.1 r (by unfold StCRG; omega),
      hf4.1 r ztggp, hf3.1 r ztggp,
      hf2.1 r (by unfold StARG; omega), hr1 r ztqgh]
  · have h1 : ∀ v, v < g.μ → c6.nmem ztjc % g.k' = c4.nmem ztjc % g.k' :=
      fun v hv => by rw [k56 _ ztxg, hlev5 v hv]
    rw [cntBelow_congr h1, cntBelow_congr h1]; exact hmin5 r hr
  · rw [hcnt6 b hb]; exact cntLt_congr hbo
  · rw [hpos6 v hv, hbo v hv, plPos_congr hbo hkey hv]
  · have := hact6 v hv (by rw [hbo v hv]; omega)
    rw [plPos_congr hbo hkey hv] at this; omega
end proofs
def RegsR (r : ℕ) : Prop := r = 130001 ∨ r = 130009 ∨ (130320 ≤ r ∧ r ≤ 130345) ∨
  (130601 ≤ r ∧ r ≤ 130620) ∨ (130632 ≤ r ∧ r ≤ 130655) ∨ (130674 ≤ r ∧ r ≤ 130700)
theorem SS.Regs.of_frameR {S : SS} {c c' : Config} (h : S.Regs c)
    (hr : ∀ r, RegsR r → c'.nreg r = c.nreg r) : S.Regs c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43, h44⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ (by unfold RegsR; omega)]; assumption)

/-- **The potential of the initial stack.** -/
theorem segPot_segL {s μ L : ℕ} {bo : ℕ → ℕ} (hL : ∀ b, cntBelow bo μ b < 2 ^ L) (j : ℕ) :
    segPot (segL s μ bo j) ≤ L * cntLt bo μ j := by
  induction j with
  | zero => simp [segL, segPot]
  | succ j ih =>
    zumma
    simp only [segL, segPot, List.map_append, List.sum_append] at ih ⊢
    have hlen : ztxix := len_seg j
    have hsz : Nat.size ztrnp ≤ L := Nat.size_le.mpr (hL j)
    have : cntBelow bo μ j * Nat.size ztrnp ≤ L * cntBelow bo μ j := by
      rw [Nat.mul_comm L]; exact Nat.mul_le_mul_left _ hsz
    unfold optSeg; split_ifs
    · grind
    · grind

/-- The stored graph only reads the map. -/
theorem memGraph_congr {m m' : ℕ → ℕ} {B μ E A : ℕ} (hA : ∀ a, a < A → m' a = m a)
    (hB : B + 2 < A) (hO : m B + 2 * E ≤ A) (hV : m zthb + 2 * E ≤ A)
    (hopp : ∀ d, d < 2 * E → m ztlrc < 2 * E) :
    memGraph m' B μ E = memGraph m B μ E := by
  have eB : m' B = m B := hA _ by_omega
  have eB2 : m' zthb = m zthb := hA _ by_omega
  have hmd : ∀ u v, MemDart m' B E u v ↔ MemDart m B E u v := fun u v => by
    unfold MemDart
    grind
  ext u v
  simp only [memGraph, hmd]
theorem segL_congr {s μ : ℕ} {bo bo' : ℕ → ℕ} (h : ∀ w, w < μ → bo w = bo' w) (j : ℕ) :
    segL s μ bo j = segL s μ bo' j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [segL, ih, cntLt_congr h]
def phase2a : Stmt := .seq regsS (.seq stkS (.seq driverStmt flagS))

/-- Its cost bound. -/
def cost2a (g : GV) : ℕ := (5 * g.L + 50) + ((20 * g.μ + 5) +
  ((120 * zttkv + splitC g.L g.k' * ztptw + 2) + (14 * g.μ + 3)))
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
theorem phase2a_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {F : Type} [Fintype F] [DecidableEq F] {M : CombMap ztbry F ztbrx} {T : SpanTree M}
    {a : F → Fin g.N} {ha : ∀ f, M.face ztdbz = f} {C : CoTree ztqc} {R : BTree}
    {first : Fin g.μ → Fin g.N} {preE slot : ℕ → ℕ} {ρ : ℕ}
    (hD : PostD g M T a ha C R first preE slot ρ W c.nmem)
    (hk : 1 ≤ g.k) (hμ : 0 < g.μ) (hμk : g.μ ≤ g.k ^ 3) (hEND : g.END ≤ W) :
    ∃ c' k, Exec P W phase2a c c' k ∧ k ≤ cost2a g ∧ WordsBounded W c' ∧ GR g c' ∧
      ztfvt ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ a, (a < g.base 43 ∨ g.base 49 ≤ a) → c'.nmem a = c.nmem a) ∧
      ((Finset.range g.μ).filter (fun v => c'.nmem ztvz = 1)).card ≤ 7 * g.k ^ 2 ∧
      ∃ (H D : Finset ℕ) (fin : Finset ztw) (nsp : ℕ),
        (∃ act, SInv g.μ g.k' g.s H (slabN T ztdom g.k') ztuwi act [] fin D nsp) ∧
        ∀ v, v < g.μ → (c'.nmem ztvz = 1 ↔ v ∈ D ∨ v ∈ H) := by
  zuuv
  have b43 := g.base_eq 43; have b46 := g.base_eq 46; have b48 := g.base_eq 48
  have b49 := g.base_eq 49; have b3 := g.base_eq 3; have b36 := g.base_eq 36
  have b0 := g.base_eq 0; have b29 := g.base_eq 29; have b35 := g.base_eq 35
  have b37 := g.base_eq 37; have b38 := g.base_eq 38; have b44 := g.base_eq 44
  zucar

  have hs : 0 < g.s := by
    show 0 < min zttla g.μ; simp_all
  zuiwr
  set cs := g.k' - 1 - ρ with hcs
  unfold phase2a
  -- registers
  obtain ⟨c1, k1, e1, hk1, hw1, hR1, h704, hr1, hm1, hrr1, hrm1, ho1⟩ :=
    regsS_exec (P := P) hw hG hEND
  have hG1 : ztido := hG.frame (fun r hr => hr1 r (by unfold GRReg at hr; unfold RegRG; omega))
  -- stack
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, htp2, hstk2⟩ := stkS_exec (P := P) hw1 hG1
    (s := g.s) (bo := boOf g c.nmem) hR1.rs hR1.rSTK
    (fun b hb => by zvmxz; exact hD.cnt b hb) hEND
  have hR2 : (ssOf g).Regs c2 := hR1.of_frameR (fun r hr => hf2.1 r (by
    unfold RegsR at hr; unfold StkRG; omega))
  have hG2 : ztsbm := hG1.frame (fun r hr => hf2.1 r ztkve)
  have hst2 : StaticEq g.A0 g.U c.nmem c2.nmem := fun x hx => by
    rw [hf2.2.2.2.2 x by_omega, hm1]
  have k2m : ∀ x, ¬ (g.base 46 ≤ x ∧ x < g.base 46 + 2 * g.μ) → c2.nmem x = c.nmem x :=
    fun x hx => by rw [hf2.2.2.2.2 x hx, hm1]
  have hSF2 := hD.sf.of_static hst2
  -- the initial invariant
  have hlevc : ∀ w (hw : w < g.μ), c.nmem ztcnl = T.level ztdxo :=
    fun w hw => hD.sf.lev ztdxo
  have hlevlt : ∀ w, w < g.μ → c.nmem ztcnl < g.μ := fun w hw => by
    rw [hlevc w hw]; exact hD.sf.lev_lt ztdxo
  have hbo2 : ∀ w, w < g.μ → boOf g c2.nmem w = boOf g c.nmem w := fun w hw => by
    have := hlevlt w hw
    zujog
    rw [k2m ztcnl by_omega, k2m (g.base 36 + c.nmem ztcnl) by_omega,
      k2m (g.base 35 + c.nmem ztcnl) by_omega]
  have hkey2 : ∀ w, w < g.μ → keyOf' g c2.nmem w = keyOf' g c.nmem w := fun w hw => by
    have := (hD.firstF w hw).1
    zulse
    rw [k2m ztfrz by_omega, k2m (g.base 29 + c.nmem ztfrz) by_omega]
  have hstk' : segL g.s g.μ ztcty g.μ = stkList c2.nmem ztmkh
      (segL g.s g.μ ztcty g.μ).length := by
    zujlj
  have hlv2 : ∀ l, l < g.μ → LvOK g c2.nmem cs l := fun l hl => by
    obtain ⟨h1, h2, h3, h4⟩ := hD.lv l hl
    zudfi
    · zunco; exact h1
    · zunco; exact h2
    · zunco; exact h3
    · zunco; exact h4
  have hpc : ∀ v, v < g.μ → plPos g.μ ztcty ztocf v =
      plPos g.μ (boOf g c.nmem) (keyOf' g c.nmem) v := fun v hv => plPos_congr hbo2 hkey2 hv
  have hI := dinv_init (W := W) hSF2 hD.head hk' by_omega hkμ hlv2
    (fun v hv => by
      show c2.nmem ztczp = if boOf g c2.nmem v < g.μ then
        plPos g.μ ztcty ztocf v else g.μ
      rw [k2m _ by_omega, hD.pos v hv, hbo2 v hv, hpc v hv])
    (fun v hv hb => by
      show c2.nmem (g.base 43 + plPos g.μ ztcty ztocf v) = v
      change boOf g c2.nmem v < g.μ at hb
      rw [hbo2 v hv] at hb
      have := plPos_lt_μ (key := keyOf' g c.nmem) hv hb
      rw [hpc v hv, k2m _ by_omega]; exact hD.act v hv hb)
    (fun v hv => by zunco; exact hD.df v hv) hstk'
  have htp2' : c2.nreg 130701 = 2 * (segL g.s g.μ ztcty g.μ).length := by
    zujlj
  have hnsp2 : c2.nreg 130704 = 0 := by rw [hf2.1 _ ztbsl]; omega
  -- the driver
  obtain ⟨c3, K, e3, hK, hw3, hR3, ⟨fin, D, nsp, hI3⟩, htp3, hst3, hr3, hrr3, hrm3, ho3⟩ :=
    driver_exec (P := P) hw2 hR2 hSF2 hI htp2' hnsp2 hk' hs
  have hG3 : ztkzy := hG2.frame (fun r hr => hr3 r (by unfold GRReg at hr; unfold SplitRG; omega)
    ztdgy ztdgy)
  have hst03 : StaticEq g.A0 g.U c.nmem c3.nmem := hst2.trans hst3
  have hsp : segPot (segL g.s g.μ ztcty g.μ) ≤ g.L * g.μ := by
    have x1 := segPot_segL (s := g.s) (μ := g.μ) (L := g.L) (bo := boOf g c2.nmem)
      (fun b => by have := cntBelow_le ztcty g.μ b; omega) g.μ
    have x2 := cntLt_le ztcty g.μ g.μ
    calc _ ≤ g.L * cntLt ztcty g.μ g.μ := x1
      _ ≤ g.L * g.μ := Nat.mul_le_mul_left _ x2
  -- the flags
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hdf4⟩ := flagS_exec (P := P) hw3 hG3
    (fun v hv => by rw [hst03 _ by_omega]; grind) hEND
  have hG4 : ztsbn := hG3.frame (fun r hr => hf4.1 r ztkvd)
  set H := Hset T cs g.k' with hH
  have hflag : ∀ v, v < g.μ → (c4.nmem ztvz = 1 ↔ v ∈ D ∨ v ∈ H) := fun v hv => by
    rw [hdf4 v hv, hst03 ztjc by_omega, hlevc v hv]
    have hl := hD.sf.lev_lt ztbbl
    obtain ⟨-, -, -, h36⟩ := hD.lv _ hl
    rw [hst03 (g.base 36 + T.level ztbbl) by_omega, h36]
    have hdf := hI3.df v hv
    have hmod := Nat.mod_lt ztwul hk'
    have hHv : v ∈ H ↔ ztwul % g.k' = g.k' - 1 := by
      simp only [hH, Hset, Finset.mem_filter, Finset.mem_range]
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hv, hv, h⟩⟩
    rw [hHv]
    rw [show (ssOf g).bDF = g.base 48 from rfl] at hdf
    by_cases hm : ztwul % g.k' < g.k' - 1
    · rw [ite_eq_left hm, ite_eq_left (show (0 : ℕ) < 1 by norm_num), hdf]
      constructor
      · grind
      grind
    · rw [ite_eq_right hm, ite_eq_right (show ¬ (1 : ℕ) < 1 by norm_num)]
      omega
  -- the size of `D*`
  have hHcard : g.k' * H.card ≤ g.μ := by
    have e : H.card = cntBelow (fun v => c.nmem ztjc % g.k') g.μ ρ := by
      simp only [hH, Hset, cntBelow]
      zucr
      refine Finset.filter_congr ztest
      have hv' := Finset.mem_range.mp hv
      rw [hlevc v hv']
      constructor
      · rintro ⟨_, h⟩; exact (mod_light hk' hD.ρ_lt).mp h
      · intro h; exact ⟨hv', (mod_light hk' hD.ρ_lt).mpr h⟩
    zui
    exact minres_card hk' (fun v _ => Nat.mod_lt _ hk') hD.rmin
  have hDcard : g.s * D.card ≤ 6 * g.k' * g.μ := by
    have := hI3.sinv.pot; simp at this; exact this
  have hsub : (Finset.range g.μ).filter (fun v => c4.nmem ztvz = 1) ⊆ D ∪ H :=
    fun v hv => by
      zuhpa
      grind
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le D H)
  have hb := dstar_bound (k := g.k) (k' := g.k') (s := g.s) hk hμ hμk rfl rfl hDcard hHcard
  refine ⟨c4, k1 + (k2 + (K + k4)), .seq e1 ztbal, ?_, hw4, hG4,
    fun r hr => ?_, by rw [hf4.2.1, hrr3, hf2.2.1, hrr1], by rw [hf4.2.2.1, hrm3, hf2.2.2.1, hrm1],
    by rw [hf4.2.2.2.1, ho3, hf2.2.2.2.1, ho1], fun x hx => ?_, by_omega,
    H, D, fin, nsp, ⟨_, hI3.sinv⟩, hflag⟩
  · unfold cost2a
    have hK' : K ≤ 120 * zttkv + splitC g.L g.k' * ztptw + 2 :=
      le_trans hK (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 120 hsp)
        (le_of_eq by_rfl)) 2)
    omega
  · rw [hf4.1 r ztcul, hr3 r ztbmk by_omega by_omega,
      hf2.1 r ztbsl, hr1 r (by unfold RegRG; omega)]
  · rw [hf4.2.2.2.2 x by_omega]; exact hst03 x by_omega
end proofs
def clusterK : ℕ := 200000
theorem GV.two_pow_L_le (g : GV) (hμ : 0 < g.μ) : 2 ^ g.L ≤ 2 * ztgju := by
  have h := Nat.pow_pred_clog_lt_self (b := 2) by_norm_num (x := g.N + g.μ + 1) by_omega
  have hL : 0 < g.L := by
    zuiwr
    grind
  have e : 2 ^ g.L = 2 * 2 ^ zttkw := by
    zufac
  change 2 ^ (Nat.clog 2 ztgju).pred < g.N + g.μ + 1 at h
  change 2 ^ g.L ≤ 2 * ztgju
  zui
  have : 2 ^ zttkw < g.N + g.μ + 1 := h
  omega
theorem GV.L_le (g : GV) (hμ : 0 < g.μ) :
    g.L ≤ Nat.clog 2 ztfsc + 2 := by
  zudwq
  have := Nat.le_pow_clog (b := 2) by_norm_num ztfsc
  zujlg
  show 2 * g.E + g.μ + 1 ≤ 2 ^ Nat.clog 2 ztfsc * 2 ^ 2
  omega
theorem cube_le (L : ℕ) : zttz ^ 3 ≤ 64 * 2 ^ L := by
  induction L with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · grind
    · have h2 := Nat.mul_le_mul h h
      have h3 := Nat.mul_le_mul h2 h
      have : (n + 1 + 2) ^ 3 ≤ 2 * ztttu ^ 3 := by ring_nf; nlinarith
      omega

/-- The number of split steps times their cost. -/
theorem q_bounds {μ k k' s L : ℕ} (hk : 1 ≤ k) (hμ : 0 < μ) (hμk : μ ≤ k ^ 3)
    (hk' : k' = min k μ) (hs : s = min ztjzf μ) :
    2 * μ / s * k' ≤ 2 * μ ∧ 2 * μ / s ≤ 2 * μ ∧
      2 * μ / s * zttz ≤ 2 * μ + 2 * zttz ^ 2 := by
  have hk'1 : 1 ≤ k' := by_omega
  have hk'μ : k' ≤ μ := by_omega
  have hs1 : k' ≤ s := by
    zvmyz; refine le_min ?_ hk'μ; nlinarith
  have hqs : 2 * μ / s * s ≤ 2 * μ := Nat.div_mul_le_self _ _
  refine ⟨le_trans zttbb hqs, Nat.div_le_self _ _, ?_⟩
  by_cases h : μ ≤ k' * k'
  · have e : s = μ := by_omega
    have : 2 * μ / s = 2 := by_simp_all
    grind
  · zubpo
    have e : s = k' * k' := by_omega
    have hkk : ztskb := by
      omega
    rcases Nat.le_total zttz s with h3 | h3
    · have := Nat.mul_le_mul_left (2 * μ / s) h3; omega
    · have hq : 2 * μ / s ≤ 2 * k := by
        apply Nat.div_le_of_le_mul
        rw [e, hkk]
        grind
      have hkL : k ≤ L + 2 := by
        omega
      calc 2 * μ / s * zttz ≤ 2 * k * zttz := Nat.mul_le_mul_right _ hq
        _ ≤ 2 * zttz * zttz := by_nlinarith
        _ ≤ 2 * μ + 2 * zttz ^ 2 := by_nlinarith

/-- The total cost of the procedure (steps of the phases, the labelling, the outputs and the
raise of the allocator). -/
def totalCost (g : GV) : ℕ := cost1 g + (cost2a g + ((120 * g.μ + 50 * g.N + 30) +
  (2 + (3 * zttku + 2))))
set_option maxHeartbeats 4000000 in
theorem totalCost_le (g : GV) (hμ : 0 < g.μ) (hE : 0 < g.E) (hk : 1 ≤ g.k)
    (hμk : g.μ ≤ g.k ^ 3) :
    totalCost g ≤ clusterK * (ztfsc * (Nat.clog 2 ztfsc + 1) + 1) := by
  unfold totalCost cost1 cost2a clusterK
  set Λ := Nat.clog 2 ztfsc + 1 with hΛ
  set X := g.μ + g.E with hX
  have hΛ1 : 1 ≤ Λ := by_omega
  set Pp := X * Λ with hPp
  have hXP : X ≤ Pp := Nat.le_mul_of_pos_right _ hΛ1
  have hΛP : Λ ≤ Pp := Nat.le_mul_of_pos_left _ by_omega
  have hN : ztsip := rfl
  have hLl := g.L_le hμ
  have hL3 : g.L ≤ 3 * Λ := by_omega
  have h2L := g.two_pow_L_le hμ
  have hU : ztlax := rfl
  have hU8 : g.U ≤ 8 * X := by_omega
  have hEND : g.END - g.A0 = 54 * g.U + 2 * ztesx := by
    have := g.END_eq; omega
  have T1 : g.μ * g.L ≤ 3 * Pp := by
    calc g.μ * g.L ≤ X * ztngd := Nat.mul_le_mul by_omega hL3
      _ = 3 * Pp := by_grind
  have T2 : g.N * g.L ≤ 6 * Pp := by
    calc g.N * g.L ≤ ztssi * ztngd := Nat.mul_le_mul by_omega hL3
      _ = 6 * Pp := by_grind
  have T3 : g.L * g.U ≤ 24 * Pp := by
    calc g.L * g.U ≤ ztngd * (8 * X) := Nat.mul_le_mul hL3 hU8
      _ = 24 * Pp := by_grind
  obtain ⟨hq1, hq2, hq3⟩ := q_bounds (L := g.L) (k' := g.k') (s := g.s) hk hμ hμk rfl rfl
  set q := 2 * g.μ / g.s with hq
  have C3 : ztbqf ^ 3 ≤ 384 * X := by
    have := cube_le g.L; omega
  have C2 : ztbqf ^ 2 ≤ ztbqf ^ 3 := Nat.pow_le_pow_right by_omega by_omega
  have S1 : ztpui * ztbqf * q ≤ 34 * ztyrm * ztbqf := by
    grind
  have S2 : 34 * ztyrm * ztbqf ≤
      34 * ztydn * ztbqf :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq3)
  have S3 : 34 * ztydn * ztbqf =
      68 * (g.μ * g.L) + 136 * g.μ + 68 * ztbqf ^ 3 := by_ring
  have S4 : 36 * g.L * q ≤ 36 * ztyrm := by
    grind
  have S5 : splitC g.L g.k' * q = ztpui * ztbqf * q + 36 * g.L * q +
      36 * (q * g.k') + 340 * q := by unfold splitC; ring
  grind
def clusterProg : Stmt := .seq phase1 (.seq phase2a (.seq labS (.seq outS bumpS)))

/-- A filter over `Fin n` counts like the filter over `range n`. -/
theorem card_fin_filter {n : ℕ} (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun v : Fin n => p v)).card = ((Finset.range n).filter p).card := by
  zugfo
  zucr
  zumx
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · grind
  · rintro ⟨hx, hp⟩; exact ⟨⟨x, hx⟩, hp, rfl⟩
end
end Chazelle.Core.Cluster
namespace Chazelle.Core
open Machine Machine.Stmt Programs Chazelle.Separator Chazelle.Separator.CombMap
open Chazelle.Core.Cluster
@[expose] public section
set_option maxHeartbeats 16000000 in
open Classical in
/-- **The cluster decomposition meets its specification.** -/
theorem clusterProg_meets : Meets clusterProg {bCluster}
    (fun P W c => P.n + 3 ≤ W ∧ 1 ≤ rd c bCluster 3 ∧ rd c bCluster 1 ≤ rd c bCluster 3 ^ 3 ∧
      Robust ztm c.nmem
        (fun m => PlanarMapAt m zthzq zthzr zthzs))
    (fun _ c c' =>
      c.nreg ALLOC ≤ rd c' bCluster 4 ∧ c.nreg ALLOC ≤ rd c' bCluster 5 ∧
      rd c' bCluster 4 + rd c bCluster 1 ≤ c'.nreg ALLOC ∧
      rd c' bCluster 5 + rd c bCluster 1 ≤ c'.nreg ALLOC ∧
      (Finset.univ.filter (fun v : Fin (rd c bCluster 1) =>
        c'.nmem ztpdf = 1)).card ≤ 7 * rd c bCluster 3 ^ 2 ∧
      (∀ u v (w : (memGraph c.nmem zthzq zthzr zthzs).Walk u v),
        (∀ x ∈ w.support, c'.nmem (rd c' bCluster 4 + x) ≠ 1) →
          c'.nmem (rd c' bCluster 5 + u) = c'.nmem ztpdg) ∧
      (∀ l, (Finset.univ.filter (fun v : Fin (rd c bCluster 1) =>
        c'.nmem ztpdf ≠ 1 ∧ c'.nmem ztpdg = l)).card ≤
          rd c bCluster 3 ^ 2))
    (fun _ c => clusterK * (ztlsh *
      (Nat.clog 2 ztlsh + 1) + 1)) := by
  intro P W c hw ⟨hPn, hk, hμk, hrob⟩ hbud
  beta_reduce at hbud
  have e0 : rd c bCluster 0 = c.nreg 130000 := rfl
  have e1 : rd c bCluster 1 = (gOf c).μ := rfl
  have e2 : rd c bCluster 2 = (gOf c).E := rfl
  have e3 : rd c bCluster 3 = (gOf c).k := rfl
  have eA : c.nreg ALLOC = (gOf c).A0 := rfl
  obtain ⟨F, iF, dF, M, hpl, hmap, hμ, hE, hμN, hB2, hO, hR, hV⟩ := inputFacts hrob
  rw [e1, e3] at hμk; zvnak at hk
  have hcost := totalCost_le ztvre hμ hE hk hμk
  zujmx
  have hcb : c.nreg ALLOC + totalCost g ≤ W := by
    grind
  have hEND : g.END ≤ W := by
    have h1 : g.END - g.A0 ≤ totalCost g := by unfold totalCost; omega
    omega
  have hU := g.U_ge; have hEe := g.END_eq
  -- phase 1
  obtain ⟨c1, k1, x1, hk1, hw1, hG1, hr1, hrr1, hrm1, ho1, hm1, T, a, ha, C, R, first, preE, slot,
    ρ, hD1⟩ := phase1_exec (P := P) hw (g := g) rfl (M := M) hpl hmap hμ hμN
      by_omega hO hR hV hk hEND
  -- phase 2a
  obtain ⟨c2, k2, x2, hk2, hw2, hG2, hr2, hrr2, hrm2, ho2, hm2, hcard2, H, D, fin, nsp,
    ⟨act, hI2⟩, hflag2⟩ := phase2a_exec (P := P) hw1 hG1 hD1 hk hμ hμk hEND
  have hO' : g.bO + g.N ≤ g.A0 := hO
  have hR' : g.bR + g.N ≤ g.A0 := hR
  have hV' : g.bV + g.N ≤ g.A0 := hV
  have b2 := g.base_eq 2; have b6 := g.base_eq 6; have b48 := g.base_eq 48
  have b43 := g.base_eq 43; have b49 := g.base_eq 49; have b0 := g.base_eq 0
  have b1 := g.base_eq 1
  have hm12 : ∀ x, x < g.A0 → c2.nmem x = c.nmem x := fun x hx => by
    grind
  have hmap2 : ztoqn := fun d => by
    have := d.2
    rw [hm2 _ by_omega, hm2 _ by_omega, hm2 _ by_omega]; exact hD1.map d
  have hF2 : ∀ u, u < g.μ → c2.nmem ztrk < g.N ∧
      c2.nmem (g.bV + c2.nmem ztrk) = u := fun u hu => by
    have h := hD1.firstF u hu
    rw [hm2 ztrk by_omega, hm2 ztzlx by_omega]; exact h
  have hz2 : ∀ d, d < g.N → c2.nmem ztefe = 0 := fun d hd => by
    rw [hm2 _ by_omega]; exact hD1.zero d hd
  -- the labels
  obtain ⟨c3, k3, x3, hk3, hw3, hr3, hrr3, hrm3, ho3, hm3, hlab3⟩ := labS_exec (P := P) hw2 hG2
    (M := M) hmap2 hF2 hz2 hμN hO hR hV hEND
  have hG3 : ztkzy := hG2.frame (fun r hr => hr3 r (by unfold GRReg at hr; unfold LabRG; omega))
  -- the outputs
  obtain ⟨c4, k4, x4, hk4, hw4, h04, h05, hr4, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W outS c3 c4 k4 ∧
      k4 = 2 ∧ WordsBounded W c4 ∧ c4.nreg 130004 = g.base 48 ∧ c4.nreg 130005 = g.base 2 ∧
      (∀ r, r ≠ 130004 → r ≠ 130005 → c4.nreg r = c3.nreg r) ∧ c4.nmem = c3.nmem ∧
      c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
    zumtv
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; exact hG3.rbase 48 by_omega,
      by config_simp; exact hG3.rbase 2 by_omega, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    rw [Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h1]
  zuk
  have hA4 : c4.nreg ALLOC = c.nreg ALLOC := by
    rw [hr4 _ by_omega by_omega, hr3 _ ztqga,
      hr2 _ by_omega, hr1 _ by_omega]
  -- the allocator
  obtain ⟨c5, k5, x5, hk5, hw5, hA5, hA5k, hr5, hm5, hrr5, hrm5, ho5⟩ := bumpS_exec (P := P) hw4
    (E := g.END) (by zuocp; exact hG3.one)
    (by zuocp; exact hG3.rEND)
    by_grind hEND
  have hA4' : c4.nreg ALLOC = g.A0 := by_grind
  have r4 : c5.nreg 130004 = g.base 48 := by zuoid; omega
  have r5 : c5.nreg 130005 = g.base 2 := by zuoid; omega
  have hrd4 : rd c5 bCluster 4 = g.base 48 := r4
  have hrd5 : rd c5 bCluster 5 = g.base 2 := r5
  have hDF : ∀ v, v < g.μ → c5.nmem ztvz = c2.nmem ztvz := fun v hv => by
    rw [hm5, hm4, hm3 _ by_omega]
  have hLAB : ∀ v, c5.nmem ztdol = c3.nmem ztdol := fun v => by_grind
  have hstep : ∀ u w, (primalEnv c2.nmem g.bO g.bR g.bV ztmkd zteac ztjwz g.μ
      g.N).Step u w → AdjN M u w ∧ u ∉ H ∧ u ∉ D ∧ w ∉ H ∧ w ∉ D := by
    rintro u w ⟨d, hd, -, hv, hh, hu, hw'⟩
    replace hd : d < g.N := hd
    have ho : c2.nmem zttkx < g.N := by rw [(hmap2 ztpw).1]; omega
    simp only [primalEnv] at hv
    rw [view_lt hd] at hv
    simp only [Env.head, primalEnv] at hh
    rw [view_lt hd, view_lt ho] at hh
    rw [(hmap2 ztpw).2.2] at hv
    rw [(hmap2 ztpw).1] at hh
    replace hh : (M.vert ztbaek : ℕ) = w := (hmap2 ztbaek).2.2.symm.trans hh
    have huμ : u < g.μ := by_omega
    have hwμ : w < g.μ := by_omega
    simp only [primalEnv] at hu hw'
    rw [view_lt huμ] at hu
    rw [view_lt hwμ] at hw'
    have hu' := (hflag2 u huμ).not.mp hu
    have hw'' := (hflag2 w hwμ).not.mp hw'
    push Not at hu' hw''
    exact ⟨⟨ztpw, hv, hh⟩, hu'.2, hu'.1, hw''.2, hw''.1⟩
  refine ⟨c5, k1 + ztvs,
    .seq x1 ztekb, ?_, ztuv, ?_⟩
  · -- cost
    have : k5 ≤ 3 * zttku + 2 := by rw [hA4'] at hk5; omega
    have hT : k1 + ztvs ≤ totalCost g := by unfold totalCost; omega
    exact le_trans hT hcost
  · rw [hrd4, eA]; omega
  · rw [hrd5, eA]; omega
  · rw [hrd4, hA5, e1]; omega
  · rw [hrd5, hA5, e1]; omega
  · rw [e1, e3, hrd4, card_fin_filter (p := fun v => c5.nmem ztvz = 1)]
    rw [Finset.filter_congr (fun v hv => by rw [hDF v ztuyp])]
    exact hcard2
  · intro u v w hw'
    rw [hrd4] at hw'
    rw [hrd5, hLAB, hLAB]
    have hBl : rd c bCluster 0 + 2 < g.A0 := hB2
    have hgraph : memGraph c.nmem zthzq zthzr zthzs =
        memGraph c2.nmem zthzq zthzr zthzs :=
      (memGraph_congr (A := g.A0) hm12 hB2 hO hV (fun d hd => by
        zunxo; omega)).symm
    have hreach := reach_of_walk (m := c2.nmem) (bF := g.base 0) (bDB := g.base 1)
      (bVB := g.base 48) hmap2 (fun d hd => by rw [hz2 d hd]; omega)
      (B := rd c bCluster 0) (E := rd c bCluster 2) ztlhx
      ztlhx rfl (w.mapLe (le_of_eq hgraph)) (fun x hx => by
        have hx' : x ∈ w.support := by
          have e := SimpleGraph.Walk.support_mapLe_eq_support (h := le_of_eq hgraph) (p := w)
          exact cast (congrArg (x ∈ ·) e) hx
        rw [← hDF x x.2]; exact hw' x hx')
    exact (hlab3 u v u.2 v.2 (by rw [← hDF u u.2]; exact hw' u w.start_mem_support)
      (by rw [← hDF v v.2]; exact hw' v w.end_mem_support)).mpr hreach
  · intro l
    rw [e1, e3, hrd4, hrd5,
      card_fin_filter (p := fun v => c5.nmem ztvz ≠ 1 ∧ c5.nmem ztdol = l)]
    have heq : (Finset.range g.μ).filter (fun v => c5.nmem ztvz ≠ 1 ∧
        c5.nmem ztdol = l) = ((Finset.range g.μ).filter
        ztyqx).filter (fun v => c3.nmem (g.base 2 + v) = l) := by
      zuepb
      zuiou

      · rintro ⟨hv, h1, h2⟩; exact ⟨⟨hv, by rw [← hDF v hv]; exact h1⟩, by rw [← hLAB]; exact h2⟩
      · rintro ⟨⟨hv, h1⟩, h2⟩; exact ⟨hv, by rw [hDF v hv]; exact h1, by rw [hLAB]; exact h2⟩
    zudab
    have hc := class_card hI2 hstep (lab := fun v => c3.nmem ztdol)
      (X := (Finset.range g.μ).filter ztyqx)
      (fun v hv => by
        zuhpa
        have := (hflag2 v hv.1).not.mp hv.2; push Not at this
        exact ⟨hv.1, this.2, this.1⟩)
      (fun x hx y hy h => by
        simp only [Finset.mem_filter, Finset.mem_range] at hx hy
        exact (hlab3 x y hx.1 hy.1 hx.2 hy.2).mp h) l
    exact le_trans hc (s_le_sq rfl rfl)
  · -- the frame
    refine ⟨fun r hr hra => ?_, fun r _ => by zunlr,
      fun x hx => ?_, fun x _ => by zunls,
      by zunlt, by rw [hA5, eA]; omega, by rw [hA5]; omega⟩
    · have : r < 130000 ∨ 140000 ≤ r := by
        simp only [Finset.mem_singleton, bandOf, bCluster] at hr; omega
      rw [hr5 r hra, hr4 r by_omega by_omega, hr3 r ztqga,
        hr2 r by_omega, hr1 r by_omega]
    · rw [hm5, hm4, hm3 _ (by rw [eA] at hx; omega)]; exact hm12 x hx
end
namespace SearchR
open SortL SortR
@[expose] public section
def lr (i : ℕ) : ℕ := 50000 + i

/-- Constants: `one`, `p := 1`, `L := 0`, table base `T := ALLOC`, `pos := 0`, `n + 1`, `0`. -/
def srchInit : Stmt := block [.constN 50106 1, .constN 50107 1, .constN 50108 0, .copyN 50109 9999,
  .constN 50105 0, .addN 50114 50104 50106, .constN 50115 0]

/-- `T[L] := p`, `L := L + 1`, `ALLOC := ALLOC + 1`; `p := 2 p` if `2 p ≤ n`, else `p := n + 1`. -/
def tabBody : Stmt :=
  .seq (block [.addN 50110 50109 50108, .storeN 50110 50107, .addN 50108 50108 50106,
      .addN 9999 9999 50106, .subN 50116 50104 50107])
    (.ifLtN 50116 50107 ztovn ztnas)

/-- The table of the powers `2 ^ j ≤ n`. -/
def tabLoop : Stmt := .whileLtN 50107 50114 tabBody

/-- Probe `A[pos + step - 1]`; move `pos` to `pos + step` if the predicate holds there. -/
def probe (cmp : Stmt) : Stmt :=
  .seq (block [.addN 50113 50105 50111, .subN 50110 50113 50106, .addN 50110 50103 50110,
      .loadN 50100 50110])
    (.seq cmp (.ifLtN 50102 50106 .skip (.instr (.copyN 50105 50113))))

/-- `i := i - 1`, `step := T[i]`; probe if `pos + step ≤ n`. -/
def liftBody (cmp : Stmt) : Stmt :=
  .seq (block [.subN 50112 50112 50106, .addN 50110 50109 50112, .loadN 50111 50110,
      .subN 50116 50104 50105])
    (.ifLtN 50116 50111 .skip (probe cmp))

/-- The binary lifting, `i = L, …, 1`. -/
def liftLoop (cmp : Stmt) : Stmt := .whileLtN 50115 50112 ztvyh

/-- **The search.** -/
def searchStmt (cmp : Stmt) : Stmt :=
  .seq srchInit (.seq tabLoop (.seq (.instr (.copyN 50112 50108)) ztqtb))

/-- The cost bound of the search for a predicate procedure of cost `≤ κ`. -/
def searchCost (κ n : ℕ) : ℕ := (κ + 37) * ztcgv

/-! ## Contracts and frames -/

/-- **Contract of a predicate procedure**: from every word-bounded configuration satisfying `J`,
`cmp` runs in at most `κ` steps, keeps `J`, writes into `lr 102` the bit `pr (lr 100)`, and changes
no natural register except `lr 100 … lr 102` and those of the bands `Bc` (never `ALLOC`), no real
register outside `Bc`, no memory and no output. -/
def PredOK (P : Polygon) (W : ℕ) (cmp : Stmt) (Bc : Finset ℕ) (J : Config → Prop)
    (pr : ℕ → Bool) (κ : ℕ) : Prop :=
  ∀ c, WordsBounded W c → J c →
    ∃ c' k, Exec P W cmp c c' k ∧ k ≤ κ ∧ J c' ∧
      c'.nreg 50102 = (if pr (c.nreg 50100) then 1 else 0) ∧
      (∀ r, r ≠ 50100 → r ≠ 50101 → r ≠ 50102 → ztdyw →
        c'.nreg r = c.nreg r) ∧
      ztimt ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- `J` is insensitive to the writes of the search itself (registers of band `bLocate`, the
allocator, memory from `A₀` on). -/
def JStableL (J : Config → Prop) (A₀ : ℕ) : Prop :=
  ∀ c c', J c → ztgnk →
    c'.rreg = c.rreg → ztpt → c'.rmem = c.rmem →
      c'.output = c.output → J c'

/-- A step of the search itself. -/
def SLL (A₀ : ℕ) (c c' : Config) : Prop :=
  ztgnk ∧ c'.rreg = c.rreg ∧
    ztpt ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- The global frame of the search relative to its entry configuration `c₀`. -/
def LocL (Bc : Finset ℕ) (A₀ : ℕ) (c₀ c : Config) : Prop :=
  (∀ r, bandOf r ∉ Bc → bandOf r ≠ bLocate → r ≠ ALLOC → c.nreg r = c₀.nreg r) ∧
    ztimu ∧ ztiue ∧
    c.rmem = c₀.rmem ∧ c.output = c₀.output

/-- The entry configuration is within the frame. -/
theorem LocL.refl (Bc : Finset ℕ) (A₀ : ℕ) (c : Config) : LocL Bc A₀ c c :=
  ⟨by_omega, by_simp_all, by_omega, rfl, rfl⟩

/-- A step of the search keeps the global frame. -/
theorem LocL.sl {Bc : Finset ℕ} {A₀ : ℕ} {c₀ c c' : Config} (h : LocL Bc A₀ c₀ c)
    (h' : SLL A₀ c c') : LocL Bc A₀ c₀ c' :=
  ⟨fun r h1 h2 h3 => (h'.1 r h2 h3).trans ztgjx,
    fun r h1 => by zuozm; exact h.2.1 r h1,
    fun a ha => (h'.2.2.1 a ha).trans zttlk, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- The band of a register outside the band `bLocate`. -/
theorem bandOf_loc {r : ℕ} (h : bandOf r ≠ bLocate) : r < 50000 ∨ 60000 ≤ r := by
  unfold bandOf bLocate at h
  omega

/-- The predicate procedure keeps the global frame. -/
theorem LocL.cmp {Bc : Finset ℕ} {A₀ : ℕ} {c₀ c c' : Config} (h : LocL Bc A₀ c₀ c)
    (hr : ∀ r, r ≠ 50100 → r ≠ 50101 → r ≠ 50102 → ztdyw →
      c'.nreg r = c.nreg r)
    (hrr : ∀ r, bandOf r ∉ Bc → c'.rreg r = c.rreg r) (hm : c'.nmem = c.nmem)
    (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) : LocL Bc A₀ c₀ c' := by
  refine ⟨fun r h1 h2 h3 => ?_, fun r h1 => (hrr r h1).trans zttlj,
    fun a ha => by zvmwi; exact h.2.2.1 a ha, hrm.trans h.2.2.2.1, ho.trans h.2.2.2.2⟩
  have := bandOf_loc h2
  zufsa

/-! ## The table of powers -/
section tab
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The invariant of the table loop**, relative to the entry configuration `c₀`. -/
structure TabInv (W : ℕ) (J : Config → Prop) (Bc : Finset ℕ) (A₀ : ℕ) (c₀ : Config) (A n : ℕ)
    (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : LocL Bc A₀ c₀ c
  rA : c.nreg 50103 = A
  rn : c.nreg 50104 = n
  pos0 : c.nreg 50105 = 0
  one : c.nreg 50106 = 1
  rT : c.nreg 50109 = A₀
  rn1 : c.nreg 50114 = n + 1
  zero : c.nreg 50115 = 0
  alloc : c.nreg ALLOC = A₀ + c.nreg 50108
  tab : ∀ j, j < c.nreg 50108 → c.nmem ztdst = 2 ^ j
  pow : c.nreg 50107 ≤ n → c.nreg 50107 = 2 ^ c.nreg 50108
  big : n < c.nreg 50107 → n < 2 ^ c.nreg 50108
  pn1 : c.nreg 50107 ≤ n + 1
  lb : c.nreg 50108 = 0 ∨ 2 ^ (c.nreg 50108 - 1) ≤ n
  bW : A₀ + Nat.clog 2 n + 2 ≤ W
  bn : n + 1 ≤ W
variable {c₀ : Config} {A n : ℕ}

/-- The length of the table is at most `⌈log₂ n⌉ + 1`. -/
theorem tab_len_le {L : ℕ} (h : L = 0 ∨ 2 ^ ztszb ≤ n) : L ≤ Nat.clog 2 n + 1 := by
  zuy
  · omega
  · have h1 := Nat.le_log_of_pow_le by_norm_num h
    zuivg

/-- **The table loop**: the table of the powers `2 ^ j < 2 n` (`j < L`), `n < 2 ^ L`; cost
`≤ 10 (⌈log₂ n⌉ + 1) + 2`; the allocator grows by at most the cost. -/
theorem tabLoop_inv (hJs : JStableL J A₀) {c : Config} (h : TabInv W J Bc A₀ c₀ A n c)
    (hL0 : c.nreg 50108 = 0) :
    ∃ c' k, Exec P W tabLoop c c' k ∧ TabInv W J Bc A₀ c₀ A n c' ∧ n < 2 ^ c'.nreg 50108 ∧
      k ≤ 10 * ztcgv + 2 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨c', k, e, I', hex, hk, hψ⟩ := whileLtN_potential_lb (P := P) (a := 50107) (b := 50114)
    (TabInv W J Bc A₀ c₀ A n) (fun d => 10 * (Nat.clog 2 n + 1 - d.nreg 50108))
    ztqnp ztpf (fun d hd ht => by
      have hn1 := hd.rn1
      rw [hn1] at ht
      have hp := hd.pow by_omega
      have hlog : d.nreg 50108 ≤ Nat.clog 2 n := by
        have h1 := Nat.le_log_of_pow_le by_norm_num (show 2 ^ d.nreg 50108 ≤ n by omega)
        zuivg

      have hbW := hd.bW
      have hbn := hd.bn
      have hal := hd.alloc
      have hL2 : d.nreg 50108 < 2 ^ d.nreg 50108 := Nat.lt_two_pow_self
      -- the straight-line part
      obtain ⟨d₁, k₁, e₁, hk₁, q⟩ : ∃ d₁ k₁, Exec P W (block [.addN 50110 50109 50108,
          .storeN 50110 50107, .addN 50108 50108 50106, .addN 9999 9999 50106,
          .subN 50116 50104 50107]) d d₁ k₁ ∧ k₁ = 5 ∧
          (d₁.nmem = upd d.nmem (A₀ + d.nreg 50108) (d.nreg 50107) ∧
            d₁.nreg 50108 = d.nreg 50108 + 1 ∧ d₁.nreg 9999 = d.nreg 9999 + 1 ∧
            d₁.nreg 50116 = n - d.nreg 50107 ∧
            (∀ r, r ≠ 50110 → r ≠ 50108 → r ≠ 9999 → r ≠ 50116 → d₁.nreg r = d.nreg r) ∧
            d₁.rreg = d.rreg ∧ d₁.rmem = d.rmem ∧ d₁.output = d.output) := by
        have hw := hd.wb
        exec_block
        · zuozn; omega
        · config_simp; zunsz; omega
        · config_simp; rw [hd.one, show (9999 : ℕ) = ALLOC from rfl, hal]; omega
        · zubee
          refine ⟨by config_simp; zuozn, by config_simp; zunsz,
            by config_simp; zunsz, by config_simp; rw [hd.rn], fun r h1 h2 h3 h4 => ?_,
            rfl, rfl, rfl⟩
          simp_all
      obtain ⟨m₁, l₁, a₁, s₁, r₁, rr₁, rm₁, o₁⟩ := q
      zud
      have p₁ : d₁.nreg 50107 = d.nreg 50107 := r₁ _ by_omega by_omega by_omega by_omega
      have n1₁ := (r₁ _ by_omega by_omega by_omega by_omega).trans hn1
      -- the doubling or the exit
      obtain ⟨d₂, k₂, e₂, hk₂, hp₂, r₂, m₂, rr₂, rm₂, o₂⟩ : ∃ d₂ k₂,
          Exec P W (.ifLtN 50116 50107 ztovn
            ztnas) d₁ d₂ k₂ ∧ k₂ ≤ 3 ∧
          (d₂.nreg 50107 = if n - d.nreg 50107 < d.nreg 50107 then n + 1
            else d.nreg 50107 + d.nreg 50107) ∧
          (∀ r, r ≠ 50107 → d₂.nreg r = d₁.nreg r) ∧ d₂.nmem = d₁.nmem ∧ d₂.rreg = d₁.rreg ∧
          d₂.rmem = d₁.rmem ∧ d₂.output = d₁.output := by
        by_cases hc : n - d.nreg 50107 < d.nreg 50107
        · obtain ⟨d₂, e₂, n₂, m₂, rr₂, rm₂, o₂⟩ := copyN_char w₁ 50107 50114
          refine ⟨d₂, _, .ifLtN_true by_omega e₂, by_omega, ?_,
            by simp_all, m₂, rr₂, rm₂, o₂⟩
          simp_all
        · obtain ⟨d₂, e₂, n₂, m₂, rr₂, rm₂, o₂⟩ := addN_char w₁ 50107 50107 50107
            by_omega
          refine ⟨d₂, _, .ifLtN_false by_omega e₂, by_omega, ?_,
            by simp_all, m₂, rr₂, rm₂, o₂⟩
          simp_all
      have R := fun r h1 h2 h3 h4 h5 => (r₂ r h1).trans (r₁ r h2 h3 h4 h5)
      have L₂ := (r₂ _ by_omega).trans l₁
      have hsl : SLL A₀ d d₂ := ⟨fun r hb ha => by
          have := bandOf_loc hb
          exact R r by_omega by_omega by_omega ha by_omega, rr₂.trans rr₁,
        fun x hx => by
          rw [m₂, m₁, Machine.upd_other _ _ _ by_omega], rm₂.trans rm₁, o₂.trans o₁⟩
      refine ⟨d₂, _, .seq e₁ e₂, ?_, by_omega, by
        show d₂.nreg 9999 ≤ d.nreg 9999 + ztbct
        grind⟩
      exact
      { wb := e₂.wb_right, hJ := hJs d d₂ hd.hJ hsl.1 hsl.2.1 hsl.2.2.1 hsl.2.2.2.1 hsl.2.2.2.2,
        loc := hd.loc.sl hsl,
        rA := (R _ by_omega by_omega by_omega by_omega by_omega).trans hd.rA,
        rn := (R _ by_omega by_omega by_omega by_omega by_omega).trans hd.rn,
        pos0 := (R _ by_omega by_omega by_omega by_omega by_omega).trans hd.pos0,
        one := (R _ by_omega by_omega by_omega by_omega by_omega).trans hd.one,
        rT := (R _ by_omega by_omega by_omega by_omega by_omega).trans hd.rT,
        rn1 := by_simp_all,
        zero := (R _ by_omega by_omega by_omega by_omega by_omega).trans hd.zero,
        alloc := by
          show d₂.nreg 9999 = _
          rw [r₂ _ by_omega, a₁, L₂, show (9999 : ℕ) = ALLOC from rfl, hal]; omega,
        tab := fun j hj => by
          rw [L₂] at hj
          rw [m₂, m₁, Machine.upd_apply]
          by_cases hjj : j = d.nreg 50108
          · grind
          · zvmyd; exact hd.tab j by_omega,
        pow := fun h' => by
          grind,
        big := fun h' => by
          grind,
        pn1 := by
          grind,
        lb := by_grind,
        bW := hbW, bn := hbn }) h
  have hL := tab_len_le I'.lb
  have hn1 := I'.rn1
  rw [hn1] at hex
  refine ⟨c', k, e, I', I'.big by_omega, by_omega, hψ⟩
end tab

/-! ## The binary lifting -/
section lift
variable {P : Polygon} {W : ℕ} {J : Config → Prop} {Bc : Finset ℕ} {A₀ : ℕ}

/-- **The invariant of the lifting loop**, relative to the entry configuration `c₀` and the
configuration `cT` after the table: the predicate holds below `pos`, fails at
`pos + 2 ^ i - 1` (if in range). -/
structure LiftInv (W : ℕ) (J : Config → Prop) (Bc : Finset ℕ) (A₀ : ℕ) (c₀ cT : Config)
    (pr : ℕ → Bool) (A n L : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  hJ : J c
  loc : LocL Bc A₀ c₀ c
  rA : c.nreg 50103 = A
  rn : c.nreg 50104 = n
  one : c.nreg 50106 = 1
  rT : c.nreg 50109 = A₀
  zero : c.nreg 50115 = 0
  mem : c.nmem = cT.nmem
  alloc : c.nreg ALLOC = cT.nreg ALLOC
  iL : c.nreg 50112 ≤ L
  posn : c.nreg 50105 ≤ n
  tab : ∀ j, j < L → cT.nmem ztdst = 2 ^ j
  bA : A + n ≤ A₀
  bT : A₀ + L ≤ W
  pre : ∀ j, j < c.nreg 50105 → pr ztzef = true
  post : c.nreg 50105 + 2 ^ c.nreg 50112 ≤ n →
    pr (c₀.nmem (A + (c.nreg 50105 + 2 ^ c.nreg 50112 - 1))) = false
variable {c₀ cT : Config} {pr : ℕ → Bool} {A n L : ℕ}
variable {cmp : Stmt} {κ : ℕ}
/-- **One lifting step** (cost `≤ κ + 13`). -/
theorem liftBody_inv (hcmp : PredOK P W cmp Bc J pr κ)
    (hJs : JStableL J A₀) (hB : bLocate ∉ Bc)
    (hmono : ∀ i j, i ≤ j → j < n → pr ztzef = true → pr ztbagx = true)
    {c : Config} (h : LiftInv W J Bc A₀ c₀ cT pr A n L c) (ht : c.nreg 50115 < c.nreg 50112) :
    ∃ c' k, Exec P W ztvyh c c' k ∧ LiftInv W J Bc A₀ c₀ cT pr A n L c' ∧
      k ≤ κ + 13 ∧ c'.nreg 50112 < c.nreg 50112 := by
  rw [h.zero] at ht
  have hiL := h.iL
  have hbT := h.bT
  have hbA := h.bA
  have hpn := h.posn
  set i := c.nreg 50112 with hi
  set pos := c.nreg 50105 with hpos
  have hstep : c.nmem (A₀ + ztei) = 2 ^ ztei := by rw [h.mem]; exact h.tab _ by_omega
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.subN 50112 50112 50106,
      .addN 50110 50109 50112, .loadN 50111 50110, .subN 50116 50104 50105]) c c₁ k₁ ∧ k₁ = 4 ∧
      (c₁.nreg 50112 = i - 1 ∧ c₁.nreg 50111 = 2 ^ ztei ∧ c₁.nreg 50116 = n - pos ∧
        (∀ r, r ≠ 50112 → r ≠ 50110 → r ≠ 50111 → r ≠ 50116 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    zuesn
    exec_block
    · config_simp; zuolz; omega
    · refine ⟨rfl, by config_simp; rw [h.one], by config_simp; zuolz; omega,
        by config_simp; rw [h.rn], fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
      simp_all
  obtain ⟨i₁, s₁, m₁, r₁, mm₁, rr₁, rm₁, o₁⟩ := q
  zud
  have sl₁ : ztumg := ⟨fun r hb _ => by
      have := bandOf_loc hb; grind, rr₁,
    by simp_all, rm₁, o₁⟩
  have hJ₁ := hJs c c₁ h.hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2
  have pos₁ : c₁.nreg 50105 = pos := by_simp_all
  -- the common part of the new invariant
  have h2p : 0 < 2 ^ ztei := Nat.two_pow_pos _
  have hpow : 2 ^ i = 2 ^ ztei + 2 ^ ztei := by
    simp_all
  by_cases hc : n - pos < 2 ^ ztei
  · -- no probe
    refine ⟨c₁, _, .seq e₁ ztxdi, ?_, by_omega,
      by omega⟩
    exact
    { wb := w₁, hJ := hJ₁, loc := h.loc.sl sl₁,
      rA := (r₁ _ by_omega by_omega by_omega by_omega).trans h.rA,
      rn := (r₁ _ by_omega by_omega by_omega by_omega).trans h.rn,
      one := (r₁ _ by_omega by_omega by_omega by_omega).trans h.one,
      rT := (r₁ _ by_omega by_omega by_omega by_omega).trans h.rT,
      zero := (r₁ _ by_omega by_omega by_omega by_omega).trans h.zero,
      mem := mm₁.trans h.mem,
      alloc := (r₁ _ by_decide by_decide by_decide by_decide).trans h.alloc,
      iL := by_omega, posn := by_omega, tab := h.tab, bA := hbA, bT := hbT,
      pre := by rw [pos₁]; exact h.pre,
      post := by_grind }
  · -- the probe
    have hle : pos + 2 ^ ztei ≤ n := by_omega
    obtain ⟨c₂, k₂, e₂, hk₂, q⟩ : ∃ c₂ k₂, Exec P W (block [.addN 50113 50105 50111,
        .subN 50110 50113 50106, .addN 50110 50103 50110, .loadN 50100 50110]) c₁ c₂ k₂ ∧
        k₂ = 4 ∧
        (c₂.nreg 50113 = pos + 2 ^ ztei ∧
          c₂.nreg 50100 = c.nmem _ ∧
          (∀ r, r ≠ 50113 → r ≠ 50110 → r ≠ 50100 → c₂.nreg r = c₁.nreg r) ∧
          c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output) := by
      exec_block
      · omega
      · config_simp; rw [(r₁ _ by_omega by_omega by_omega by_omega).trans h.rA,
          (r₁ _ by_omega by_omega by_omega by_omega).trans h.one, pos₁, s₁]; omega
      · refine ⟨rfl, by config_simp; omega, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp
          rw [(r₁ _ by_omega by_omega by_omega by_omega).trans h.rA,
            (r₁ _ by_omega by_omega by_omega by_omega).trans h.one, pos₁, s₁, mm₁]
        · zubmk
    obtain ⟨t₂, x₂, r₂, mm₂, rr₂, rm₂, o₂⟩ := q
    zue
    have sl₂ : SLL A₀ c₁ c₂ := ⟨fun r hb _ => by
        have := bandOf_loc hb; exact r₂ r by_omega by_omega by_omega, rr₂,
      by grind, rm₂, o₂⟩
    have hJ₂ := hJs c₁ c₂ hJ₁ sl₂.1 sl₂.2.1 sl₂.2.2.1 sl₂.2.2.2.1 sl₂.2.2.2.2
    -- the item read is the array entry
    have hx : c.nmem _ = c₀.nmem ztxus :=
      h.loc.2.2.1 _ by_omega
    obtain ⟨c₃, k₃, e₃, hk₃, hJ₃, bit₃, r₃, rr₃, m₃, rm₃, o₃⟩ := hcmp c₂ w₂ hJ₂
    rw [x₂, hx] at bit₃
    have R₃ : ∀ r, bandOf r = bLocate → r ≠ 50100 → r ≠ 50101 → r ≠ 50102 →
        c₃.nreg r = c₂.nreg r := by_grind
    have bl : ∀ r, 50000 ≤ r → r < 60000 → bandOf r = bLocate := fun r h1 h2 => by
      zulue
    have loc₃ := ((h.loc.sl sl₁).sl sl₂).cmp r₃ rr₃ m₃ rm₃ o₃
    -- registers after the comparator, in terms of `c`
    have K₃ : ∀ r, 50000 ≤ r → r < 60000 → r ≠ 50100 → r ≠ 50101 → r ≠ 50102 → r ≠ 50110 →
        r ≠ 50111 → r ≠ 50112 → r ≠ 50113 → r ≠ 50116 → c₃.nreg r = c.nreg r :=
      fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
        (R₃ r by_grind h3 h4 h5).trans by_grind
    have i₃ : c₃.nreg 50112 = i - 1 := by
      rw [R₃ _ by_grind by_omega by_omega by_omega,
        r₂ _ by_omega by_omega by_omega, i₁]
    have t₃ : c₃.nreg 50113 = pos + 2 ^ ztei := by
      rw [R₃ _ by_grind by_omega by_omega by_omega, t₂]
    have al₃ : ztcke := by
      rw [r₃ _ by_decide by_decide by_decide ztbt, r₂ _ by_decide by_decide
        by_decide, r₁ _ by_decide by_decide by_decide by_decide]
    have mem₃ : c₃.nmem = cT.nmem := by rw [m₃, mm₂, mm₁, h.mem]
    have one₃ :=
      (K₃ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega by_omega).trans h.one
    -- the common fields
    have base : ∀ c' : Config, WordsBounded W c' → J c' → LocL Bc A₀ c₀ c' →
        c'.nmem = cT.nmem → c'.nreg ALLOC = c.nreg ALLOC →
        (∀ r, 50000 ≤ r → r < 60000 → r ≠ 50100 → r ≠ 50101 → r ≠ 50102 → r ≠ 50105 →
          r ≠ 50110 → r ≠ 50111 → r ≠ 50112 → r ≠ 50113 → r ≠ 50116 → c'.nreg r = c.nreg r) →
        c'.nreg 50112 = i - 1 → c'.nreg 50105 ≤ n →
        (∀ j, j < c'.nreg 50105 → pr _ = true) →
        (c'.nreg 50105 + 2 ^ c'.nreg 50112 ≤ n →
          pr _ = false) →
        LiftInv W J Bc A₀ c₀ cT pr A n L c' :=
      fun c' hw hJ hl hm ha hr hi' hp hpre hpost =>
        { wb := hw, hJ := hJ, loc := hl,
          rA := (hr _ by_omega by_omega by_omega by_omega by_omega by_omega
            by_omega by_omega by_omega by_omega by_omega).trans h.rA,
          rn := (hr _ by_omega by_omega by_omega by_omega by_omega by_omega
            by_omega by_omega by_omega by_omega by_omega).trans h.rn,
          one := (hr _ by_omega by_omega by_omega by_omega by_omega by_omega
            by_omega by_omega by_omega by_omega by_omega).trans h.one,
          rT := (hr _ by_omega by_omega by_omega by_omega by_omega by_omega
            by_omega by_omega by_omega by_omega by_omega).trans h.rT,
          zero := (hr _ by_omega by_omega by_omega by_omega by_omega by_omega
            by_omega by_omega by_omega by_omega by_omega).trans h.zero,
          mem := hm, alloc := ha.trans h.alloc, iL := by_omega, posn := hp,
          tab := h.tab, bA := hbA, bT := hbT, pre := hpre, post := hpost }
    by_cases hp : pr (c₀.nmem ztxus) = true
    · -- move
      rw [ite_eq_left hp] at bit₃
      obtain ⟨c₄, e₄, n₄, m₄, rr₄, rm₄, o₄⟩ := copyN_char e₃.wb_right 50105 50113
      have R₄ : ∀ r, r ≠ 50105 → c₄.nreg r = c₃.nreg r := fun r hr => by
        rw [n₄, Machine.upd_other _ _ _ hr]
      have p₄ : c₄.nreg 50105 = pos + 2 ^ ztei := by rw [n₄, Machine.upd_same, t₃]
      have sl₄ : SLL A₀ c₃ c₄ := ⟨fun r hb _ => by
          have := bandOf_loc hb; exact R₄ r by_omega, rr₄, by_grind, rm₄, o₄⟩
      refine ⟨c₄, _, .seq e₁ (.ifLtN_false by_omega (.seq e₂ (.seq e₃
        ztsow))), ?_, by_omega,
        by zunzo; omega⟩
      refine base c₄ e₄.wb_right (hJs c₃ c₄ hJ₃ sl₄.1 sl₄.2.1 sl₄.2.2.1 sl₄.2.2.2.1 sl₄.2.2.2.2)
        (loc₃.sl sl₄) by_grind (by rw [R₄ _ by_decide, al₃])
        (fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => (R₄ r h6).trans
          (K₃ r h1 h2 h3 h4 h5 h7 h8 h9 h10 h11))
        (by zunzo) by_omega ?_ ?_
      · rw [p₄]
        zun
        by_cases hj' : j < pos
        · exact h.pre j hj'
        · exact hmono j _ by_omega by_omega hp
      · rw [p₄, R₄ _ by_omega, i₃]
        zuhgj
        have := h.post by_grind
        grind
    · -- stay
      rw [ite_eq_right hp] at bit₃
      refine ⟨c₃, _, .seq e₁ (.ifLtN_false by_omega (.seq e₂ (.seq e₃
        (.ifLtN_true by_omega ztjdx)))), ?_, by_omega,
        by omega⟩
      have p₃ : c₃.nreg 50105 = pos :=
        (K₃ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
          by_omega by_omega by_omega)
      refine base c₃ e₃.wb_right hJ₃ loc₃ mem₃ al₃
        (fun r h1 h2 h3 h4 h5 _ h7 h8 h9 h10 h11 => K₃ r h1 h2 h3 h4 h5 h7 h8 h9 h10 h11)
        i₃ by_omega (by rw [p₃]; exact h.pre) ?_
      grind

/-- **The lifting loop**: at the end `pos` is the partition point; cost `≤ (κ + 15) i + 2`. -/
theorem liftLoop_inv (hcmp : PredOK P W cmp Bc J pr κ)
    (hJs : JStableL J A₀) (hB : bLocate ∉ Bc)
    (hmono : ∀ i j, i ≤ j → j < n → pr ztzef = true → pr ztbagx = true)
    {c : Config} (h : LiftInv W J Bc A₀ c₀ cT pr A n L c) :
    ∃ c' k, Exec P W ztqtb c c' k ∧ LiftInv W J Bc A₀ c₀ cT pr A n L c' ∧
      k ≤ zthlp * c.nreg 50112 + 2 ∧
      (c'.nreg 50105 < n → pr (c₀.nmem (A + c'.nreg 50105)) = false) := by
  obtain ⟨c', k, e, I', hex, hk⟩ := Exec.whileLtN_bounded (a := 50115) (b := 50112)
    (LiftInv W J Bc A₀ c₀ cT pr A n L) (fun d => d.nreg 50112) (κ + 13) ztpf
    (fun d hd ht => by
      obtain ⟨d', k, e, I, hk, hi⟩ := liftBody_inv (P := P) hcmp hJs hB hmono hd ht
      exact ztkkp) h
  refine ⟨c', k, e, I', hk, fun hlt => ?_⟩
  have hz := I'.zero
  zvncr at hex
  have := I'.post by_simp_all
  simp_all
end lift

/-! ## The search -/

/-- The cost bound dominates the cost of the phases. -/
theorem searchCost_ge (κ n : ℕ) :
    7 + (10 * ztcgv + 2) + 1 + (zthlp * ztcgv + 2) ≤
      searchCost κ n := by
  unfold searchCost
  nlinarith

/-- **The search meets its specification** (at the level of executions).  From a word-bounded
configuration `c` satisfying `J`, with an array of `n = lr 104` items at `A = lr 103` below the
allocator, on which `pr` is monotone (true on a prefix), and room for `searchCost κ n` cells,
`searchStmt cmp` runs in at most `searchCost κ n` steps and leaves in `lr 105` the partition point
`t ≤ n`: `pr` holds at `A[j]` for `j < t` and fails at `A[t]` if `t < n`.  It keeps `J` and
respects `Frame (insert bLocate Bc)`. -/
theorem searchStmt_exec {P : Polygon} {W : ℕ} {cmp : Stmt} {Bc : Finset ℕ} {J : Config → Prop}
    {pr : ℕ → Bool} {κ : ℕ} (hcmp : PredOK P W cmp Bc J pr κ) (hB : bLocate ∉ Bc)
    {c : Config} (hw : WordsBounded W c) (hJ : J c) (hJs : JStableL J ztm)
    (hA : c.nreg 50103 + c.nreg 50104 ≤ c.nreg ALLOC)
    (hmono : ∀ i j, i ≤ j → j < c.nreg 50104 → pr ztequ = true →
      pr ztnwq = true)
    (hroom : c.nreg ALLOC + searchCost κ ztvij ≤ W) :
    ∃ c' k, Exec P W (searchStmt cmp) c c' k ∧ k ≤ searchCost κ ztvij ∧ J c' ∧
      Frame (insert bLocate Bc) c c' k ∧ c'.nreg 50105 ≤ c.nreg 50104 ∧
      ztxsn ∧
      (c'.nreg 50105 < c.nreg 50104 → pr (c.nmem (c.nreg 50103 + c'.nreg 50105)) = false) := by
  zuce
  zuemw

  have hc0 : 37 * ztcgv ≤ searchCost κ n := by
    unfold searchCost; simp
  have hcost := searchCost_ge κ n
  -- initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W srchInit c c₁ k₁ ∧ k₁ = 7 ∧
      (c₁.nreg 50106 = 1 ∧ c₁.nreg 50107 = 1 ∧ c₁.nreg 50108 = 0 ∧ c₁.nreg 50109 = A₀ ∧
        c₁.nreg 50105 = 0 ∧ c₁.nreg 50114 = n + 1 ∧ c₁.nreg 50115 = 0 ∧
        (∀ r, r ≠ 50106 → r ≠ 50107 → r ≠ 50108 → r ≠ 50109 → r ≠ 50105 → r ≠ 50114 →
          r ≠ 50115 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold srchInit
    exec_block
    · omega
    · omega
    · omega
    · omega
    · config_simp; omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, by_rfl,
        by config_simp, by_rfl, by config_simp,
        fun r h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl, rfl⟩
      simp_all
  obtain ⟨o₁, p₁, l₁, t₁, s₁, n₁, z₁, r₁, m₁, rr₁, rm₁, out₁⟩ := q
  have sl₁ : ztumg := ⟨fun r hb _ => by
      have := bandOf_loc hb
      grind,
    rr₁, by_grind, rm₁, out₁⟩
  have T₁ : TabInv W J Bc A₀ c A n c₁ :=
    { wb := e₁.wb_right, hJ := hJs c c₁ hJ sl₁.1 sl₁.2.1 sl₁.2.2.1 sl₁.2.2.2.1 sl₁.2.2.2.2,
      loc := (LocL.refl Bc A₀ c).sl sl₁,
      rA := by_grind,
      rn := by_grind,
      pos0 := s₁, one := o₁, rT := t₁, rn1 := n₁, zero := z₁,
      alloc := by
        rw [l₁, r₁ _ by_decide by_decide by_decide by_decide by_decide by_decide
          by_decide]; omega,
      tab := by_grind,
      pow := by_grind, big := fun h' => by_grind,
      pn1 := by_omega, lb := Or.inl l₁, bW := by_omega, bn := by_omega }
  -- the table
  obtain ⟨c₂, k₂, e₂, T₂, hbig, hk₂, ha₂⟩ := tabLoop_inv (P := P) (hJs := hJs) T₁ l₁
  have hL := tab_len_le T₂.lb
  -- `i := L`
  obtain ⟨c₃, e₃, n₃, m₃, rr₃, rm₃, out₃⟩ := copyN_char (P := P) T₂.wb 50112 50108
  have R₃ : ∀ r, r ≠ 50112 → c₃.nreg r = c₂.nreg r := fun r hr => by
    rw [n₃, Machine.upd_other _ _ _ hr]
  have sl₃ : SLL A₀ c₂ c₃ := ⟨fun r hb _ => by
      have := bandOf_loc hb; grind, rr₃, by_grind, rm₃, out₃⟩
  have i₃ : c₃.nreg 50112 = c₂.nreg 50108 := by zuoma
  have I₃ : LiftInv W J Bc A₀ c c₃ pr A n _ c₃ :=
    { wb := e₃.wb_right, hJ := hJs c₂ c₃ T₂.hJ sl₃.1 sl₃.2.1 sl₃.2.2.1 sl₃.2.2.2.1 sl₃.2.2.2.2,
      loc := T₂.loc.sl sl₃, rA := (R₃ _ by_omega).trans T₂.rA,
      rn := (R₃ _ by_omega).trans T₂.rn, one := (R₃ _ by_omega).trans T₂.one,
      rT := (R₃ _ by_omega).trans T₂.rT, zero := (R₃ _ by_omega).trans T₂.zero, mem := rfl,
      alloc := rfl, iL := by rw [i₃], posn := by rw [(R₃ _ by_omega).trans T₂.pos0]; omega,
      tab := fun j hj => by zumzp; exact T₂.tab j hj, bA := hA, bT := by_omega,
      pre := fun j hj => by rw [(R₃ _ by_omega).trans T₂.pos0] at hj; omega,
      post := by_grind }
  -- the lifting
  obtain ⟨c₄, k₄, e₄, I₄, hk₄, hfin⟩ := liftLoop_inv (P := P) hcmp hJs hB hmono I₃
  rw [i₃] at hk₄
  have loc₄ := I₄.loc
  have al₄ : c₄.nreg ALLOC = c₂.nreg ALLOC := by rw [I₄.alloc, R₃ _ by_decide]
  have al₂ := T₂.alloc
  have al₁ := T₁.alloc
  refine ⟨c₄, _, .seq e₁ ztcb, ?_, I₄.hJ, ?_, I₄.posn, I₄.pre, hfin⟩
  · have : zthlp * c₂.nreg 50108 ≤ zthlp * ztcgv :=
      Nat.mul_le_mul_left _ hL
    omega
  · refine ⟨fun r hr ha => ?_, fun r hr => ?_, loc₄.2.2.1,
      fun a _ => by rw [loc₄.2.2.2.1], loc₄.2.2.2.2, by_omega, ?_⟩
    · zucjg
      exact loc₄.1 r hr.2 hr.1 ha
    · zucjg
      exact loc₄.2.1 r hr.2
    omega
end
end SearchR
namespace WalkKey
open SignK SearchR
@[expose] public section
def Bk (r : ℕ) : Bool := decide ztcko
variable {P : Polygon} {W : ℕ} {M : Model} {Q : Polygon}
/-- **The sign kernel** as an execution lemma with the explicit frame `Bk` (no allocator, no
memory): three symbolic points in `10000 …`, `10003 …`, `10006 …`, the test in `10009`, the
answer bit in `10010`. -/
theorem sig_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : P.n + 3 ≤ W) (hop : c.nreg 10009 ≤ 3) {s₁ s₂ s₃ : SymPt} (hl₁ : s₁.Lt P.n)
    (hl₂ : s₂.Lt P.n) (hl₃ : s₃.Lt P.n) (hi₁ : SymPtIn c 10000 s₁) (hi₂ : SymPtIn c 10003 s₂)
    (hi₃ : SymPtIn c 10006 s₃) :
    ∃ c' k, Exec P W signProg c c' k ∧ k ≤ 230 ∧ FrameB Bk c c' ∧ c'.nreg 10010 ≤ 1 ∧
      (c'.nreg 10010 = 1 ↔
        SignTest ztqhi ztykc ztyke ztykg) := by
  have hW' : ztfku := by_omega
  obtain ⟨c1, k1, e1, hk1, p1n, p11, p12, p13, p1z⟩ := prelude_spec (P := P) c hw hW
  have f1 := exec_frameB e1 (B := Bpre) by_decide
  obtain ⟨c2, k2, e2, hk2, hr1⟩ := loadPt_spec 10000 10100 ztwzn c1 e1.wb_right
    p1n p11 p1z hW' s₁ hl₁
    (symPtIn_of_eq hi₁ fun j h1 h2 => f1.1 j zthff)
  have f2 := exec_frameB e2 (B := Bload 10100) by_decide
  obtain ⟨c3, k3, e3, hk3, hr2⟩ := loadPt_spec 10003 10110 (Or.inr ztwzn) c2
    e2.wb_right ztmyu ztgvv
    ztgvw hW' s₂ hl₂
    (symPtIn_of_eq hi₂ fun j h1 h2 =>
      (f2.1 j ztcmi).trans ztzvp)
  have f3 := exec_frameB e3 (B := Bload 10110) by_decide
  obtain ⟨c4, k4, e4, hk4, hr3⟩ := loadPt_spec 10006 10120 (Or.inr ztxch) c3
    e3.wb_right ((f3.1 _ by_decide).trans ztmyu)
    ztynn
    ztyno hW' s₃ hl₃
    (symPtIn_of_eq hi₃ fun j h1 h2 =>
      (f3.1 j ztcmi).trans
        ((f2.1 j ztcmi).trans ztzvp))
  have f4 := exec_frameB e4 (B := Bload 10120) by_decide
  obtain ⟨c5, k5, e5, hk5, hx, hy, hd⟩ := polyStmt_spec (P := P) c4 e4.wb_right
    (repAt_of_eq hr1 fun j h1 h2 =>
      (f4.2.1 j ztcmi).trans (f3.2.1 j ztcmi))
    (repAt_of_eq hr2 fun j h1 h2 => f4.2.1 j ztcmi) hr3
  have f5 := exec_frameB e5 (B := Bpoly) by_decide
  have n21 := (f5.1 _ by_decide).trans ((f4.1 _ by_decide).trans
    ztynn)
  have n22 := (f5.1 _ by_decide).trans ((f4.1 _ by_decide).trans
    ((f3.1 _ by_decide).trans ((f2.1 _ by_decide).trans p12)))
  have n23 := (f5.1 _ by_decide).trans ((f4.1 _ by_decide).trans
    ((f3.1 _ by_decide).trans ((f2.1 _ by_decide).trans p13)))
  have z5 := (f5.2.1 _ by_decide).trans ((f4.2.1 _ by_decide).trans
    ztyno)
  have o5 : c5.nreg 10009 = c.nreg 10009 := (f5.1 _ by_decide).trans ((f4.1 _ by_decide).trans
    ((f3.1 _ by_decide).trans ((f2.1 _ by_decide).trans (f1.1 _ by_decide))))
  obtain ⟨c6, k6, e6, hk6, hsel⟩ := selStmt_spec (P := P) c5 e5.wb_right n21 n22 hx hy hd
  have f6 := exec_frameB e6 (B := Bsel) by_decide
  obtain ⟨c7, k7, e7, hk7, hb1, hb2, hpos, hzero⟩ :=
    lexStmt_spec (P := P) 10020 10410 10411 by_decide by_omega
      [10400, 10401, 10402, 10403, 10404] c6 e6.wb_right ((f6.2.1 _ by_decide).trans z5)
  have f7 := exec_frameB e7 (B := Blex) by_decide
  obtain ⟨c8, k8, e8, hk8, hf1, hf2⟩ := finStmt_spec (P := P) c7 e7.wb_right
    ((f7.1 _ by_decide).trans ((f6.1 _ by_decide).trans n23))
  have o7 :=
    (f7.1 _ by_decide).trans ((f6.1 _ by_decide).trans o5)
  rw [o7] at hf1 hf2
  rw [hsel, o5] at hpos hzero
  have ex := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  have fb := exec_frameB ex (B := Bk) by_decide
  refine ⟨c8, _, ex, by_grind, fb, ?_, ?_⟩
  · omega
  · have hm := signTest_iff_lex P hG.2 s₁ s₂ s₃ hl₁ hl₂ hl₃ ztqhi
    grind

/-! ## The mathematics of the comparison -/

/-- **The direction code** of walk edge `e`: `1` upward, `2` downward, `0` horizontal. -/
noncomputable def dirCode (M : Model) (e : ℕ) : ℕ :=
  if (M.wa e).2 < (M.wb e).2 then 1 else if (M.wb e).2 < (M.wa e).2 then 2 else 0

/-- **The search predicate** for the query `x`: the position `s` lies strictly before `x` (if `x`
has height code `0`) or not after `x` (otherwise). -/
def KeyPred (M : Model) (Q : Polygon) (x s : WPos) : Prop :=
  if x.hgt = 0 then M.key Q s < M.key Q x else M.key Q s ≤ M.key Q x

/-- The predicate is monotone in the key of `s`. -/
theorem KeyPred.mono {x s s' : WPos} (h : KeyPred M Q x s)
    (hle : M.key Q s' ≤ M.key Q s) : KeyPred M Q x s' := by
  unfold KeyPred at h ⊢
  grind

/-- **The decision computed by the machine**, for any positions (the guard `n < s.hgt` keeps
the sign kernel in range). -/
noncomputable def keyDec (Q : Polygon) (n : ℕ) (x : WPos) (d : ℕ) (s : WPos) : Bool :=
  if s.edge < x.edge then true
  else if x.edge < s.edge then false
  else if x.hgt < 1 then false
  else if d < 1 then true
  else if s.hgt < 1 then true
  else if n < s.hgt then false
  else if d < 2 then !decide ((Q.vtx ztzs).2 < (Q.vtx zttzs).2)
  else !decide ((Q.vtx zttzs).2 < (Q.vtx ztzs).2)

/-- The height of a position with a nonzero code. -/
theorem hgtY_of_pos {M : Model} {Q : Polygon} {x : WPos} (h : 1 ≤ x.hgt) :
    M.hgtY Q x = (Q.vtx ztzs).2 := by
  rcases x with ⟨e, _ | k⟩
  · simp_all
  · rfl

/-- A position with code `0` has parameter `0`. -/
theorem param_of_code_zero {M : Model} {Q : Polygon} {x : WPos} (h : x.hgt = 0) :
    M.param Q x = 0 := by
  rcases x with ⟨e, k⟩
  simp only at h
  zubst
  rfl

/-- **The machine decision is the search predicate** for positions of the walk proper, with the
direction code of the query edge. -/
theorem keyDec_iff {n : ℕ} {x s : WPos} (hx : ProperPos M Q n x)
    (hs : ProperPos M Q n s) :
    keyDec Q n x ztjtx s = true ↔ KeyPred M Q x s := by
  zugpv
  obtain ⟨hs0, hs1, hsn⟩ := hs
  have kx : ztehv := rfl
  have ks : M.key Q s = s.edge + M.param Q s := rfl
  unfold keyDec KeyPred
  by_cases h1 : s.edge < x.edge
  · have : (s.edge : ℝ) + 1 ≤ x.edge := by exact_mod_cast h1
    grind
  zubmd
  by_cases h2 : x.edge < s.edge
  · have : (x.edge : ℝ) + 1 ≤ s.edge := by exact_mod_cast h2
    grind
  zulqb
  have he : s.edge = x.edge := by_omega
  have heR : (s.edge : ℝ) = x.edge := by_simp_all
  by_cases h3 : x.hgt < 1
  · have hx0' : x.hgt = 0 := by_omega
    rw [ite_eq_left h3, ite_eq_left hx0']
    simp only [Bool.false_eq_true, false_iff, not_lt]
    rw [kx, ks, param_of_code_zero hx0']
    linarith
  rw [ite_eq_right h3, ite_eq_right (by omega : ¬ x.hgt = 0)]
  by_cases h4 : dirCode M x.edge < 1
  · rw [ite_eq_left h4]
    zuhqc
    have hh : ztdjn := by
      zumsk
      grind
    have e1 := Model.key_eq_of_horizontal (Q := Q) hh
    have e2 := Model.key_eq_of_horizontal (Q := Q) (by zvmxm; exact hh)
    simp_all
  rw [ite_eq_right h4]
  have hnh : ztkyu := by
    zujba
    zumsk
    simp_all
  by_cases h5 : s.hgt < 1
  · rw [ite_eq_left h5]
    zuhqc
    rw [kx, ks, param_of_code_zero by_simp_all]
    linarith
  rw [ite_eq_right h5, ite_eq_right by_simp_all]
  have hlt := Model.key_lt_key_iff_of_same_edge (Q := Q) he.symm hnh
  rw [hgtY_of_pos by_omega, hgtY_of_pos by_omega] at hlt
  have hle : M.key Q s ≤ M.key Q x ↔ ¬ M.key Q x < M.key Q s := not_lt.symm
  rw [hle, hlt]
  by_cases h6 : dirCode M x.edge < 2
  · have hup : (M.wa x.edge).2 < (M.wb x.edge).2 := by
      zulbp

    grind
  · have hdn : (M.wb x.edge).2 < (M.wa x.edge).2 := by
      zulbp

    grind

/-! ## The comparison procedure -/

/-- The height test: `vtx (x.hgt - 1)` against `vtx (s.hgt - 1)` (upward edge) or the reverse
(downward edge), test `1` (ordinate order); the answer is `1 - bit`. -/
def kerPart : Stmt :=
  .seq (block [.constN 10013 2, .constN 10000 0, .constN 10003 0, .constN 10006 0,
      .constN 10009 1, .subN 10015 10501 50102, .subN 10016 10012 50102, .copyN 10007 10015])
    (.seq (.ifLtN 10502 10013 ztkrl
        ztkrm)
      (.seq signProg (.instr (.subN 50102 50102 10010))))

/-- The decision on a loaded start position (`10011`: edge, `10012`: code); `lr 102` holds `1`
on entry. -/
def cmpPos : Stmt :=
  .ifLtN 10011 10500 .skip
    (.ifLtN 10500 10011 ztcyo
      (.ifLtN 10501 50102 ztcyo
        (.ifLtN 10502 50102 .skip
          (.ifLtN 10012 50102 .skip
            (.seq (.instr (.inputSize 10014))
              (.ifLtN 10014 10012 ztcyo kerPart))))))

/-- Load the start of arc `lr 100` from the arc area at `10503`. -/
def loadPos : Stmt := block [.addN 50101 50100 50100, .addN 50101 50101 50101,
  .addN 50101 50101 50100, .addN 50101 50101 10503, .addN 50101 50101 50102, .loadN 10011 50101,
  .addN 50101 50101 50102, .loadN 10012 50101]

/-- **The comparison procedure** (answer `0` for items out of range). -/
def keyCmp : Stmt :=
  .seq ztouc
    (.ifLtN 50100 10504 (.seq loadPos cmpPos) ztcyo)

/-- The instruction writes a real register only if it is accepted by `B` (natural registers
are unrestricted), and is not a store, an `emit` or a control instruction. -/
def wrROK (B : ℕ → Bool) : Instr → Bool
  | .inputSize _ | .constN _ _ | .copyN _ _ | .addN _ _ _ | .subN _ _ _ | .loadN _ _ => true
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _ => B r
  | .loadR r _ | .readX r _ | .readY r _ => B r
  | _ => false

/-- Every instruction of the statement satisfies `wrROK B`. -/
def wrR (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrROK B i
  | .seq s t => wrR B s && wrR B t
  | .ifLtN _ _ t e => wrR B t && wrR B e
  | .ifLtR _ _ t e => wrR B t && wrR B e
  | .whileLtN _ _ b => wrR B b
  | .whileLtR _ _ b => wrR B b

/-- **Real-register frame**: a statement whose real writes are accepted by `B` changes no other
real register. -/
theorem exec_rframe {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrR B s = true) : ∀ r, B r = false → c'.rreg r = c.rreg r := by
  induction h with
  | skip _ => exact by_simp_all
  | @instr ins c c' _ he _ _ =>
    simp only [wrR] at hs
    cases ins <;> simp only [wrROK, Bool.false_eq_true] at hs <;>
      zvncw at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      intro j hj <;>
      first
      | rfl
      | (zvmwf; split_ifs with hh
         · simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wrR, Bool.and_eq_true] at hs
    zufeo
  | ifLtN_true _ _ ih =>
    zufcm
  | ifLtN_false _ _ ih =>
    zufcn
  | ifLtR_true _ _ ih =>
    zufcm
  | ifLtR_false _ _ ih =>
    zufcn
  | whileLtN_false _ _ => exact by_simp_all
  | whileLtN_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans ztefj
  | whileLtR_false _ _ => exact by_simp_all
  | whileLtR_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans ztefj
theorem wrR_keyCmp : wrR Bk keyCmp = true := by_decide

/-- The registers written by `keyCmp`. -/
def Bcmp (r : ℕ) : Bool := decide (r = 50101) || decide zttxt || Bk r
theorem wr_keyCmp : wr Bcmp keyCmp = true := by_decide

/-- The kernel part answers the height test. -/
theorem kerPart_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) (h1 : c.nreg 50102 = 1) (hx1 : 1 ≤ c.nreg 10501)
    (hxn : c.nreg 10501 ≤ P.n) (hs1 : 1 ≤ c.nreg 10012) (hsn : c.nreg 10012 ≤ P.n) :
    ∃ c' k, Exec P W kerPart c c' k ∧ k ≤ 245 ∧
      c'.nreg 50102 = (if (if c.nreg 10502 < 2 then
          !decide (((Qof P).vtx ztlkk).2 < ((Qof P).vtx ztrlj).2)
        else !decide (((Qof P).vtx ztrlj).2 < ((Qof P).vtx ztlkk).2))
        then 1 else 0) := by
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 10013 2, .constN 10000 0,
      .constN 10003 0, .constN 10006 0, .constN 10009 1, .subN 10015 10501 50102,
      .subN 10016 10012 50102, .copyN 10007 10015]) c c₁ k₁ ∧ k₁ = 8 ∧
      (c₁.nreg 10013 = 2 ∧ c₁.nreg 10000 = 0 ∧ c₁.nreg 10003 = 0 ∧ c₁.nreg 10006 = 0 ∧
        c₁.nreg 10009 = 1 ∧ c₁.nreg 10015 = c.nreg 10501 - 1 ∧
        c₁.nreg 10016 = c.nreg 10012 - 1 ∧ c₁.nreg 10007 = c.nreg 10501 - 1 ∧
        c₁.nreg 50102 = 1 ∧ c₁.nreg 10502 = c.nreg 10502) := by
    exec_block
    · omega
    · omega
    · omega
    · omega
    · omega
    simp_all
  obtain ⟨q13, q0, q3, q6, q9, q15, q16, q7, q102, q502⟩ := q
  zud
  -- the two orders
  obtain ⟨c₂, k₂, e₂, hk₂, a₁, a₄, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 10502 10013
      ztkrl
      ztkrm) c₁ c₂ k₂ ∧ k₂ ≤ 4 ∧
      c₂.nreg 10001 = zthhw ∧
      c₂.nreg 10004 = zthhv ∧
      (∀ r, r ≠ 10001 → r ≠ 10004 → c₂.nreg r = c₁.nreg r) := by
    by_cases hd : c.nreg 10502 < 2
    · zudd
      exec_block
      simp_all
    · zubv
      exec_block
      simp_all
  zue
  set a := zthhw with ha
  set b := zthhv with hb
  have hal : a < P.n := by_grind
  have hbl : b < P.n := by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, bit₃, sig₃⟩ := sig_exec (P := P) c₂ w₂ hG hW
    (s₁ := .vtx a) (s₂ := .vtx b) (s₃ := .vtx ztlkk)
    by_grind hal hbl (show c.nreg 10501 - 1 < P.n by omega)
    ⟨by_grind, a₁⟩ ⟨by_grind, a₄⟩
    ⟨by_grind, by_grind⟩
  zubj
  have n102 : c₃.nreg 50102 = 1 := by
    rw [f₃.1 _ by_decide, r₂ _ by_omega by_omega, q102]
  have op : c₂.nreg 10009 = 1 := by_grind
  rw [op] at sig₃
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ (Exec.subN w₃ 50102 50102 10010))), by_omega, ?_⟩
  config_simp
  rw [n102]
  simp only [SignTest, SymPt.eval] at sig₃
  grind

/-- The decision on a loaded position. -/
theorem cmpPos_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) (h1 : c.nreg 50102 = 1) (hxn : c.nreg 10501 ≤ P.n) :
    ∃ c' k, Exec P W cmpPos c c' k ∧ k ≤ 260 ∧
      c'.nreg 50102 = (if keyDec zta P.n ztrbi ztggz
        ⟨c.nreg 10011, c.nreg 10012⟩ then 1 else 0) := by
  unfold cmpPos keyDec
  zubi
  by_cases t1 : c.nreg 10011 < c.nreg 10500
  · rw [ite_eq_left t1]
    exact spec_ifLtN_true t1 ztevs
  rw [ite_eq_right t1]
  refine spec_ifLtN_false t1 ?_
  by_cases t2 : c.nreg 10500 < c.nreg 10011
  · rw [ite_eq_left t2]
    refine spec_ifLtN_true t2 ztywo
    simp
  rw [ite_eq_right t2]
  refine spec_ifLtN_false t2 ?_
  by_cases t3 : c.nreg 10501 < 1
  · rw [ite_eq_left t3]
    refine spec_ifLtN_true by_omega
      ztywo
    simp
  rw [ite_eq_right t3]
  zubv
  by_cases t4 : c.nreg 10502 < 1
  · rw [ite_eq_left t4]
    zulzv
  rw [ite_eq_right t4]
  zubv
  by_cases t5 : c.nreg 10012 < 1
  · rw [ite_eq_left t5]
    zulzv
  rw [ite_eq_right t5]
  zubv
  zukdx
  refine spec_seq ⟨_, _, Exec.inputSize hw 10014 hn, ?_⟩
  have w₁ := WordsBounded.upd_nreg hw hn c.pc (r := 10014)
  by_cases t6 : P.n < c.nreg 10012
  · rw [ite_eq_left t6]
    refine spec_ifLtN_true by_simp_all
      (spec_instr ztcta fun _ => ?_)
    simp
  rw [ite_eq_right t6]
  zudx
  obtain ⟨c', k, e, hk, hr⟩ := kerPart_exec (P := P) hG hW _ w₁ by_simp_all
    (by config_simp; omega) by_simp_all (by config_simp; omega)
    by_simp_all
  refine ⟨c', k, e, by_omega, ?_⟩
  tauto

/-- **The comparison procedure** computes the bit of `cmpPrC`: the decision on the start of arc
`lr 100` (`0` out of range). -/
theorem keyCmp_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) (hxn : c.nreg 10501 ≤ P.n)
    (hAB : c.nreg 10503 + 5 * c.nreg 10504 ≤ W) :
    ∃ c' k, Exec P W keyCmp c c' k ∧ k ≤ 275 ∧
      c'.nreg 50102 = (if (if c.nreg 50100 < c.nreg 10504 then
        keyDec zta P.n ztrbi ztggz
          ⟨c.nmem ztlkl,
            c.nmem ztlkm⟩ else false) then 1 else 0) := by
  have w₀ := WordsBounded.upd_nreg hw (show 1 ≤ W by omega) c.pc (r := 50102)
  refine spec_seq ⟨_, _, Exec.constN hw 50102 1 by_omega, ?_⟩
  by_cases hj : c.nreg 50100 < c.nreg 10504
  · zuhmf
    zuek
    obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W loadPos
        { c with nreg := upd c.nreg 50102 1 } c₁ k₁ ∧ k₁ = 8 ∧
        (c₁.nreg 10011 = c.nmem ztlkl ∧
          c₁.nreg 10012 = c.nmem ztlkm ∧
          c₁.nreg 50102 = 1 ∧ c₁.nreg 10500 = c.nreg 10500 ∧ c₁.nreg 10501 = c.nreg 10501 ∧
          c₁.nreg 10502 = c.nreg 10502) := by
      unfold loadPos
      exec_block
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · zubee
        config_simp
        grind
    obtain ⟨q11, q12, q102, q500, q501, q502⟩ := q
    obtain ⟨c₂, k₂, e₂, hk₂, hr⟩ := cmpPos_exec hG hW c₁ e₁.wb_right q102
      by_omega
    refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by_omega, ?_⟩
    simp_all
  · zulqh
    refine spec_ifLtN_false by_simp_all
      (spec_instr (Exec.constN w₀ _ _ by_omega) fun _ => ?_)
    simp

/-! ## The contract of the search -/

/-- **The invariant of the search** for the query `x`, direction code `d`, arc area `AB` with
`A` arcs, memory `m₀` below `A₀`; register `10505` carries a value `SB` across the search. -/
def CmpJ (x : WPos) (d AB A SB A₀ : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop :=
  c.nreg 10500 = x.edge ∧ c.nreg 10501 = x.hgt ∧ c.nreg 10502 = d ∧ c.nreg 10503 = AB ∧
    c.nreg 10504 = A ∧ c.nreg 10505 = SB ∧ ∀ a, a < A₀ → c.nmem a = m₀ a

/-- **The predicate of the search**: the machine decision on the start of arc `j`. -/
noncomputable def cmpPr (P : Polygon) (x : WPos) (d AB A : ℕ) (m₀ : ℕ → ℕ) (j : ℕ) : Bool :=
  if j < A then keyDec zta P.n x d ⟨m₀ ztbph, m₀ ztbpi⟩ else false

/-- The invariant is insensitive to the writes of the search. -/
theorem cmpJ_stable (x : WPos) (d AB A SB A₀ : ℕ) (m₀ : ℕ → ℕ) :
    JStableL ztmao A₀ := by
  zuhgf
  obtain ⟨h0, h1, h2, h3, h4, h6, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by_simp_all⟩
  · rw [hr _ by_decide by_decide, h0]
  · zuhlv
  · zuhlw
  · zuhlx
  · rw [hr _ by_decide by_decide, h4]
  · rw [hr _ by_decide by_decide, h6]

/-- **Target 1: the comparison procedure meets the contract of the binary search**, with the
invariant `CmpJ` and the predicate `cmpPr`, in at most `275` steps, writing only `lr 101`,
`lr 102` and the band `bSign`. -/
theorem keyCmp_predOK (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (x : WPos)
    (hx : x.hgt ≤ P.n) (d AB A SB A₀ : ℕ) (m₀ : ℕ → ℕ) (hAB : AB + 5 * A ≤ A₀) (hA₀ : A₀ ≤ W) :
    PredOK P W keyCmp {bSign} ztmao (cmpPr P x d AB A m₀) 275 := by
  zumgl
  obtain ⟨h0, h1, h2, h3, h4, h6, h5⟩ := hJ
  obtain ⟨c', k, e, hk, hr⟩ := keyCmp_exec (P := P) hG hW c hw by_omega
    by_omega
  have fb := exec_frameB e wr_keyCmp
  have hB := fb.1
  refine ⟨c', k, e, hk, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha => by zuodf; simp_all⟩, ?_,
    ?_, ?_, fb.2.2.1, fb.2.2.2.1, fb.2.2.2.2⟩
  · rw [hB _ by_decide, h0]
  · rw [hB _ by_decide, h1]
  · rw [hB _ by_decide, h2]
  · rw [hB _ by_decide, h3]
  · rw [hB _ by_decide, h4]
  · rw [hB _ by_decide, h6]
  · rw [hr, h0, h1, h2, h3, h4]
    unfold cmpPr
    by_cases hj : c.nreg 50100 < A
    · rw [ite_eq_left hj, ite_eq_left hj, h5 _ by_omega, h5 _ by_omega]
    grind
  · intro r r0 r1 r2 hb
    apply hB
    unfold Bcmp Bk
    zucor
    · zufat

    · subst hb; decide
  · intro r hb
    apply exec_rframe e wrR_keyCmp
    unfold Bk
    zufat
end
end WalkKey
namespace NFLoc
open Chazelle.Chain (sideInArc)
@[expose] public section
theorem getD_of_lt {α : Type*} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp_all

/-- **Cyclic order**: if `q` is not strictly inside the cyclic interval `(a, b)` and the three
keys are distinct, then `b` is strictly inside `(a, q)`. -/
theorem sideInArc_swap {a b q : ℝ} (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (h : ¬ sideInArc a b q) : sideInArc a q b := by
  zusg
  grind
variable {M : Model} {Q : Polygon} {N : NF} {x s : WPos}
/-- The unpacked validity of a normal form: its region correspondence and arc records. -/
theorem isNF_arcs (h : IsNF M Q N) :
    ∃ reg : ℕ → Set Point, RegionCorr M Q N reg ∧ ArcsOK M Q N reg ∧ SeqOK M Q N :=
  let ⟨_, _, _, reg, hR, _, hA, _, hS, _⟩ := h
  ⟨reg, hR, hA, hS⟩

/-- In a valid normal form, **every arc of every region is listed**. -/
theorem listed_of_isArc (h : IsNF M Q N) {U : Set Point}
    (hU : U ∈ M.regions ztdu) {a b : ℝ} (hab : M.IsArc ztdu U a b) :
    ∃ j, j < N.arcs.length ∧ M.key Q (N.arc j).s = a ∧ M.key Q (N.arc j).e = b := by
  obtain ⟨reg, hR, hA, -⟩ := isNF_arcs h
  obtain ⟨r, hr, rfl⟩ := hR.2.2 U hU
  obtain ⟨j, hj, -, h1, h2⟩ := hA.2.2.1 r hr a b hab
  grind

/-- In a valid normal form, **every listed arc is an arc** of the submap. -/
theorem isArc_of_listed (h : IsNF M Q N) {j : ℕ}
    (hj : j < N.arcs.length) :
    ∃ U, M.IsArc ztdu U ztbpl ztdfq := by
  obtain ⟨reg, -, hA, -⟩ := isNF_arcs h
  exact ⟨_, (hA.1 j hj).2⟩

/-- The arc-sequence table is a permutation of the arc indices. -/
theorem seq_length (h : IsNF M Q N) :
    N.seq.length = N.arcs.length := by
  zuze
  zukte

/-- Entries of the arc-sequence table are arc indices. -/
theorem seq_lt (h : IsNF M Q N) {i : ℕ}
    (hi : i < N.arcs.length) : N.seq.getD i 0 < N.arcs.length := by
  zuze
  zuhff
  rw [getD_of_lt 0 by_omega]
  have hm : N.seq[i]' by_omega ∈ List.range N.arcs.length := hS.1.subset ztdbx
  simp_all

/-- Every arc index occurs in the arc-sequence table. -/
theorem seq_surj (h : IsNF M Q N) {j : ℕ}
    (hj : j < N.arcs.length) : ∃ i, i < N.arcs.length ∧ N.seq.getD i 0 = j := by
  zuze
  zuhff
  have hm : j ∈ N.seq := hS.1.symm.subset (List.mem_range.2 hj)
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hm
  exact ⟨i, by_omega, by_grind⟩

/-- **The table is sorted** by start keys. -/
theorem seq_sorted (h : IsNF M Q N) {i i' : ℕ} (hii : i ≤ i')
    (hi' : i' < N.arcs.length) :
    M.key Q (N.arc ztdfs).s ≤ M.key Q (N.arc (N.seq.getD i' 0)).s := by
  zuze
  zuhff
  rcases lt_or_eq_of_le hii with hlt | rfl
  · rw [getD_of_lt 0 by_omega, getD_of_lt 0 by_omega]
    exact List.pairwise_iff_getElem.1 hS.2 i i' by_omega by_omega hlt
  simp

/-- `KeyPred` bounds the key from above, its negation from below. -/
theorem keyPred_le (h : WalkKey.KeyPred M Q x s) :
    M.key Q s ≤ M.key Q x := by
  zulty
theorem le_of_not_keyPred
    (h : ¬ WalkKey.KeyPred M Q x s) : M.key Q x ≤ M.key Q s := by
  zulty

/-- **The gap property of the chosen position** `p* = t - 1` (or the last position if `t = 0`)
of the partition point `t`: the start `a` of its arc is the query key, or no start key lies in
the open cyclic interval from `a` to the query key. -/
theorem pick_gap (h : IsNF M Q N) (x : WPos) {t : ℕ}
    (hA : 0 < N.arcs.length) (ht : t ≤ N.arcs.length)
    (hpre : ∀ i, i < t → WalkKey.KeyPred M Q x (N.arc ztdfs).s)
    (hpost : t < N.arcs.length → ¬ WalkKey.KeyPred M Q x (N.arc ztnnf).s) :
    M.key Q (N.arc ztzuj).s =
        M.key Q x ∨
      ∀ j, j < N.arcs.length → ¬ sideInArc
        (M.key Q (N.arc ztzuj).s)
        ztbys ztbpl := by
  zukzw
  zujsg
  · zuhmd
    set a := M.key Q (N.arc (N.seq.getD ztso 0)).s
    have haq : a ≤ q := keyPred_le (hpre ztso by_omega)
    rcases eq_or_lt_of_le haq with he | hlt
    · simp_all
    zulpa

    zubix
    rw [ite_eq_left hlt] at hin
    zufkc
    by_cases hit : i < t
    · have := seq_sorted h (show i ≤ t - 1 by omega) by_omega
      grind
    · have hk := le_of_not_keyPred (hpost by_omega)
      have := seq_sorted h (show t ≤ i by omega) hi
      grind
  · zucqa
    have ht0 : ztbhh := by_omega
    zudlw
    set a := M.key Q (N.arc (N.seq.getD ztdfr 0)).s
    have hall : ∀ i, i < N.arcs.length → q ≤ M.key Q (N.arc ztdfs).s := fun i hi =>
      (le_of_not_keyPred (hpost hA)).trans (seq_sorted h (Nat.zero_le i) hi)
    have hqa : q ≤ a := hall _ by_omega
    rcases eq_or_lt_of_le hqa with he | hlt
    · simp_all
    zulpa

    zubix
    rw [ite_eq_right ztqud] at hin
    zufkc
    have h1 := hall i hi
    have h2 := seq_sorted h (show i ≤ N.arcs.length - 1 by omega) by_omega
    grind

/-- **Correctness of the pick** (the post of `LocateSpec` for the model and normal form of the
precondition), from the partition point `t` of the search. -/
theorem locate_pick (hcov : ∀ y : ℝ, M.IsCut ztdu y →
      ∃ U ∈ M.regions ztdu, ∃ b : ℝ, M.IsArc ztdu U y b)
    (h : IsNF M Q N) (x : WPos) {t : ℕ} (hA : 0 < N.arcs.length) (ht : t ≤ N.arcs.length)
    (hpre : ∀ i, i < t → WalkKey.KeyPred M Q x (N.arc ztdfs).s)
    (hpost : t < N.arcs.length → ¬ WalkKey.KeyPred M Q x (N.arc ztnnf).s) :
    let j := N.seq.getD ztcpz 0
    j < N.arcs.length ∧
      (¬ M.IsCut ztdu ztbys →
        N.F M Q = ∅ ∨ sideInArc ztbpl ztdfq ztbys) ∧
      (M.IsCut ztdu ztbys →
        M.key Q (N.arc j).s = M.key Q x ∨ M.key Q (N.arc j).e = M.key Q x) := by
  zujbf
  have hpos : ztcpz < N.arcs.length := by
    grind
  have hj : ztsjo := seq_lt h hpos
  refine ⟨hj, ?_⟩
  have hgap := pick_gap h x hA ht hpre hpost
  obtain ⟨U, hU⟩ := isArc_of_listed h hj
  set a := M.key Q (N.arc j).s
  set b := M.key Q (N.arc j).e
  zukzw
  by_cases hF : N.F M Q = ∅
  · refine ⟨fun _ => Or.inl hF, fun hc => ?_⟩
    obtain ⟨c, hc, -⟩ := hc
    simp_all
  -- the chosen arc is a genuine arc between two distinct cuts
  obtain ⟨-, -, -, -, hends, hno, -⟩ := hU
  obtain ⟨hca, hcb, hab⟩ : M.IsCut (N.F M Q) a ∧ M.IsCut (N.F M Q) b ∧ a ≠ b := by
    simp_all
  -- the key claim
  have claim : sideInArc a b q ∨ b = q ∨ a = q := by
    by_cases haq : a = q
    · simp_all
    have hgap' := hgap.resolve_left haq
    zubqk
    rw [not_or, not_or] at hcon
    have hin := sideInArc_swap hab haq hcon.2.1 hcon.1
    obtain ⟨V, hV, b', hb'⟩ := hcov b hcb
    obtain ⟨j', hj', hs', -⟩ := listed_of_isArc h hV hb'
    grind
  grind
open SignK SearchR WalkKey
theorem frame_of_frameB {B : ℕ → Bool} {S : Finset ℕ} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → bandOf r ∈ S ∧ r ≠ ALLOC) (k : ℕ) : Frame S c c' k := by
  have hA : B ALLOC = false := by
    grind
  have hal := h.1 ALLOC hA
  refine ⟨fun r hr _ => h.1 r ?_, fun r hr => h.2.1 r ?_, fun a _ => by zunrv,
    fun a _ => by zuoxl, h.2.2.2.2, by zuozi, by_omega⟩
  · grind
  grind

/-! ## The direction procedure -/

/-- The registers a direction procedure may write: `10000 … 10502` (the sign kernel and the
answer) and `lr 30 … lr 99`. -/
def Bdir (r : ℕ) : Bool := decide ztdev || decide ztngu

/-- **Contract of a direction procedure** under the precondition `DPre`: at most `κd` steps,
writes only `Bdir`, and leaves in `10502` the direction code of the query edge `lr 2` of the model
described at `lr 0`. -/
def DirOK (dirS : Stmt) (κd : ℕ) (DPre : Polygon → ℕ → Config → Prop) : Prop :=
  ∀ P W c, WordsBounded W c → DPre P W c →
    ∃ c' k, Exec P W dirS c c' k ∧ k ≤ κd ∧ FrameB Bdir c c' ∧
      ∀ M, ModelDescAt c.nmem zthut zta M →
        c'.nreg 10502 = dirCode M ztmgd

/-! ## The program -/

/-- Copy the query, read the header of the normal form. -/
def locSetup : Stmt := block [.copyN 10500 50002, .copyN 10501 50003, .constN 50020 1,
  .addN 50021 50001 50020, .loadN 10504 50021, .addN 50021 50021 50020, .addN 50021 50021 50020,
  .addN 50021 50021 50020, .loadN 10503 50021, .addN 50021 50021 50020, .addN 50021 50021 50020,
  .loadN 10505 50021, .copyN 50103 10505, .copyN 50104 10504]

/-- The cost bound: `(κd + 340) (⌈log₂ A⌉ + 1)`. -/
def locCost (κd A : ℕ) : ℕ := (κd + 340) * ztgef

/-- The registers written by `locSetup` and `locFinish`. -/
def Bloc (r : ℕ) : Bool :=
  decide (10500 ≤ r ∧ r < 10506) || decide (50000 ≤ r ∧ r < 50030) ||
    decide (50100 ≤ r ∧ r < 50117)
theorem wr_locSetup : wr Bloc locSetup = true := by_decide
variable (r : ℕ) {m : ℕ → ℕ} {B : ℕ} {N N' : NF}
theorem Bloc_band (h : Bloc r = true) : bandOf r ∈ ({bLocate, bSign} : Finset ℕ) ∧
    r ≠ ALLOC := by
  unfold Bloc at h
  zubzj
  zulbh
theorem Bdir_band (h : Bdir r = true) : bandOf r ∈ ({bLocate, bSign} : Finset ℕ) ∧
    r ≠ ALLOC := by
  unfold Bdir at h
  zubzj
  zulbh

/-! ## Uniqueness of what the layout determines -/
theorem aRec_ext {a b : ARec} (h1 : a.reg = b.reg) (h2 : a.s.edge = b.s.edge)
    (h3 : a.s.hgt = b.s.hgt) (h4 : a.e.edge = b.e.edge) (h5 : a.e.hgt = b.e.hgt) : a = b := by
  zucxj
theorem cRec_ext {a b : CRec} (h1 : a.h = b.h) (h2 : a.lp = b.lp) (h3 : a.rp = b.rp)
    (h4 : a.up = b.up) (h5 : a.dn = b.dn) : a = b := by
  zueak

/-- The layout determines the arc records. -/
theorem nfAt_arcs_eq (h : NFAt m B N) (h' : NFAt m B N') :
    N'.arcs = N.arcs := by
  zubnu

  have a1 : ztpkr := getD_of_lt _ hj'
  have a2 : ztpkp := getD_of_lt _ hj
  zubmi
  exact aRec_ext ztjui ztjuj ztjuk
    ztmiw ztmix

/-- The layout determines the chord records. -/
theorem nfAt_chords_eq (h : NFAt m B N) (h' : NFAt m B N') :
    N'.chords = N.chords := by
  zubnv

  have a1 : ztpkt := getD_of_lt _ hj'
  have a2 : ztpkq := getD_of_lt _ hj
  zubmi
  exact cRec_ext ztjui ztjuj ztjuk
    ztmiw ztmix

/-! ## Correctness of the procedure -/

/-- On table entries, the predicate of the search is `KeyPred`. -/
theorem cmpPr_eq {P : Polygon} {M : Model} {N : NF} {m : ℕ → ℕ} {B : ℕ} (hN : NFAt m B N)
    (x : WPos) (hx : ProperPos M zta P.n x)
    (hst : ∀ j, j < N.arcs.length → ProperPos M zta P.n (N.arc j).s) {j : ℕ}
    (hj : j < N.arcs.length) :
    cmpPr P x ztjtx ztbaie N.arcs.length m j = true ↔
      KeyPred M zta x (N.arc j).s := by
  unfold cmpPr
  zuhmf
  obtain ⟨-, e1, e2, -⟩ := hN.2.2.2.2.2.2.1 j hj
  have hs : (⟨m ztyjo, m ztyjp⟩ : WPos) = (N.arc j).s := by
    simp_all
  zubqb
  exact keyDec_iff hx (hst j hj)
noncomputable def dirOf (a b : ℝ) : ℕ := if a < b then 1 else if b < a then 2 else 0
theorem dirCode_eq (M : Model) (e : ℕ) : dirCode M e = dirOf (M.wa e).2 (M.wb e).2 := rfl

/-- Load the points of `lr 40` (first and third) and `lr 43` (second) into the kernel, test `1`. -/
def kerLoad (a b : ℕ) : Stmt := block [.copyN 10000 a, .copyN 10001 ztdf, .copyN 10002 ztvj,
  .copyN 10003 b, .copyN 10004 ztds, .copyN 10005 ztub, .copyN 10006 a,
  .copyN 10007 ztdf, .copyN 10008 ztvj, .constN 10009 1]

/-- **The height comparison**: `10502 := dirOf y(lr 40) y(lr 43)`. -/
def dirTail : Stmt :=
  .seq zttqs (.seq signProg (.seq (.instr (.copyN 50037 10010))
    (.seq zttqt (.seq signProg (.seq ztfeq
      (.ifLtN 50037 50032
        ztfmb
        ztotc))))))
theorem wr_dirTail : wr Bdir dirTail = true := by_decide

/-- A symbolic point in three registers is copied by three copies. -/
theorem symPtIn_copy {c c' : Config} {r r' : ℕ} {s : SymPt} (h : SymPtIn c r s)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) : SymPtIn c' r' s := by
  cases s with
  | vtx i => exact ⟨h0.trans h.1, h1.trans h.2⟩
  | onEdge e hh => exact ⟨h0.trans h.1, h1.trans h.2.1, h2.trans h.2.2⟩
variable {P : Polygon} {W : ℕ} (Q : Polygon)
/-- Loading the kernel. -/
theorem kerLoad_exec_ab (hW : 1 ≤ W) (c : Config) (hw : WordsBounded W c)
    {sa sb : SymPt} (hsa : SymPtIn c 50040 sa) (hsb : SymPtIn c 50043 sb) :
    ∃ c' k, Exec P W zttqs c c' k ∧ k = 10 ∧ SymPtIn c' 10000 sa ∧
      SymPtIn c' 10003 sb ∧ SymPtIn c' 10006 sa ∧ c'.nreg 10009 = 1 ∧
      ztfyr := by
  unfold kerLoad
  exec_block
  all_goals try exact hW
  refine ⟨rfl, ?_, ?_, ?_, by config_simp, fun r hr => ?_⟩
  · tauto
  · tauto
  · tauto
  · zuby
    zudck

/-- Loading the kernel, the other order. -/
theorem kerLoad_exec_ba (hW : 1 ≤ W) (c : Config) (hw : WordsBounded W c)
    {sa sb : SymPt} (hsa : SymPtIn c 50043 sa) (hsb : SymPtIn c 50040 sb) :
    ∃ c' k, Exec P W zttqt c c' k ∧ k = 10 ∧ SymPtIn c' 10000 sa ∧
      SymPtIn c' 10003 sb ∧ SymPtIn c' 10006 sa ∧ c'.nreg 10009 = 1 ∧
      ztfyr := by
  unfold kerLoad
  exec_block
  all_goals try exact hW
  refine ⟨rfl, ?_, ?_, ?_, by config_simp, fun r hr => ?_⟩
  · tauto
  · tauto
  · tauto
  · zuby
    zudck

/-- **The height comparison of two symbolic points** (at most `490` steps). -/
theorem dirTail_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {sa sb : SymPt} (hla : sa.Lt P.n) (hlb : sb.Lt P.n)
    (hsa : SymPtIn c 50040 sa) (hsb : SymPtIn c 50043 sb) :
    ∃ c' k, Exec P W dirTail c c' k ∧ k ≤ 490 ∧ FrameB Bdir c c' ∧
      c'.nreg 10502 = dirOf (sa.eval zta).2 (sb.eval zta).2 := by
  obtain ⟨c₁, k₁, e₁, hk₁, i1, i2, i3, o1, r1⟩ := kerLoad_exec_ab (P := P) by_omega c hw
    hsa hsb
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, bit₂, sig₂⟩ := sig_exec (P := P) c₁ e₁.wb_right hG hW
    by_omega hla hlb hla i1 i2 i3
  rw [o1] at sig₂
  zvnhd at sig₂
  zue
  have e₃ := Exec.copyN (P := P) w₂ 50037 10010
  zubj
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50037 (c₂.nreg 10010) }
  have k2 : ∀ r, ztcu → c₂.nreg r = c₁.nreg r := fun r hr =>
    f₂.1 r ztggj
  have sa₃ : SymPtIn c₃ 50040 sa := symPtIn_copy hsa
    ztbrf
    ztbrf
    ztbrf
  have sb₃ : SymPtIn c₃ 50043 sb := symPtIn_copy hsb
    ztbrf
    ztbrf
    ztbrf
  have up₃ : c₃.nreg 50037 = c₂.nreg 10010 := by_rfl
  obtain ⟨c₄, k₄, e₄, hk₄, j1, j2, j3, o4, r4⟩ := kerLoad_exec_ba (P := P) by_omega c₃ w₃
    sb₃ sa₃
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, bit₅, sig₅⟩ := sig_exec (P := P) c₄ e₄.wb_right hG hW
    by_omega hlb hla hlb j1 j2 j3
  rw [o4] at sig₅
  zvnhd at sig₅
  zuef
  have up₅ : c₅.nreg 50037 = c₂.nreg 10010 := by
    rw [f₅.1 _ by_decide, r4 _ by_omega, up₃]
  zuepw
  zujb
  zueei
  have h6a : c₆.nreg 50037 = c₂.nreg 10010 := by simp [c₆, up₅]
  have h6b : c₆.nreg 10010 = c₅.nreg 10010 := by_rfl
  have h6c : c₆.nreg 50032 = 1 := by_rfl
  set ya := (sa.eval zta).2
  set yb := (sb.eval zta).2
  obtain ⟨c₇, k₇, e₇, hk₇, r₇⟩ : ∃ c₇ k₇, Exec P W (.ifLtN 50037 50032
      ztfmb
      ztotc) c₆ c₇ k₇ ∧ k₇ ≤ 4 ∧ c₇.nreg 10502 = dirOf ya yb := by
    unfold dirOf
    by_cases hab : ya < yb
    · have  := sig₂.2 hab
      refine spec_ifLtN_false by_omega
        ztxrg
      simp_all
    · have h0 : c₂.nreg 10010 = 0 := by_grind
      zudd
      by_cases hba : yb < ya
      · have  := sig₅.2 hba
        refine spec_ifLtN_false by_omega
          ztxrg
        simp_all
      · have h0' : c₅.nreg 10010 = 0 := by_grind
        refine spec_ifLtN_true by_omega
          ztxrg
        simp [hab, hba]
  have ex : Exec P W dirTail c c₇ _ :=
    .seq e₁ ztfc
  exact ⟨c₇, _, ex, by_omega, exec_frameB ex wr_dirTail, r₇⟩

/-! ## The interior model -/

/-- The walk of the interior model has `n` vertices. -/
theorem interiorWalk_n : (interiorWalk Q).n = Q.n := by
  zugiq

  · rfl
  · zufan
open Classical in
/-- **The vertices of the interior walk**: vertex `p < n` is vertex `p` of `Q` (orientation bit
set) or vertex `n - 1 - p`. -/
theorem interiorWalk_vtx {p : ℕ} (hp : p < Q.n) :
    (interiorWalk Q).vtx p = if Mountain.LeftInside Q then Q.vtx p else Q.vtx ztqbp := by
  zumsz
  zus
  · rfl
  · unfold Polygon.vtx Polygon.n at *
    grind

/-- The indices of the interior model: bit, `(e + 1) mod n`, and the two vertex indices. -/
def intIdx : Stmt :=
  .seq (block [.inputSize 50030, .constN 50032 1, .addN 50031 50002 50032,
      .addN 50033 50000 50032, .loadN 50033 50033])
    (.seq ztipt
      (.ifLtN 50033 50032 (block [.subN 50036 50030 50032, .subN 50041 50036 50002,
          .subN 50044 50036 50031])
        (.ifLtN 50032 50033 (block [.subN 50036 50030 50032, .subN 50041 50036 50002,
            .subN 50044 50036 50031])
          ztksg)))

/-- **The direction procedure of the interior model.** -/
def intDir : Stmt :=
  .seq intIdx (.seq ztkrg dirTail)
theorem wr_intDir : wr Bdir intDir = true := by_decide

/-- The indices computed by `intIdx`. -/
theorem intIdx_exec (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    (he : c.nreg 50002 < P.n) (hD : c.nreg 50000 + 1 ≤ W) :
    ∃ c' k, Exec P W intIdx c c' k ∧ k ≤ 14 ∧
      c'.nreg 50041 = (if c.nmem ztcct = 1 then c.nreg 50002
        else P.n - 1 - c.nreg 50002) ∧
      c'.nreg 50044 = (if c.nmem ztcct = 1 then zthuu % P.n
        else P.n - 1 - zthuu % P.n) := by
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.inputSize 50030, .constN 50032 1,
      .addN 50031 50002 50032, .addN 50033 50000 50032, .loadN 50033 50033]) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 50030 = P.n ∧ c₁.nreg 50032 = 1 ∧ c₁.nreg 50031 = c.nreg 50002 + 1 ∧
        c₁.nreg 50033 = c.nmem ztcct ∧ c₁.nreg 50002 = c.nreg 50002) := by
    exec_block
    · omega
    · omega
    · config_simp; omega
    · simp_all
    simp
  obtain ⟨q30, q32, q31, q33, q02⟩ := q
  zud
  obtain ⟨c₂, k₂, e₂, hk₂, s31, s30, s32, s33, s02⟩ : ∃ c₂ k₂, Exec P W
      ztipt c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 50031 = zthuu % P.n ∧ c₂.nreg 50030 = P.n ∧ c₂.nreg 50032 = 1 ∧
      c₂.nreg 50033 = c.nmem ztcct ∧ c₂.nreg 50002 = c.nreg 50002 := by
    by_cases h : c.nreg 50002 + 1 < P.n
    · refine spec_ifLtN_true by_omega (spec_skip w₁ zteh)
      rw [q31, Nat.mod_eq_of_lt h]
      omega
    · refine spec_ifLtN_false by_omega
        (spec_instr ztcta fun _ => zteh)
      have : c.nreg 50002 + 1 = P.n := by_omega
      simp_all
  zue
  set b := c.nmem ztcct
  zulrk
  set e1 := zthuu % P.n
  have hrev : ∀ (d : Config) , WordsBounded W d → d.nreg 50030 = P.n → d.nreg 50032 = 1 →
      d.nreg 50002 = e → d.nreg 50031 = e1 →
      ∃ c' k, Exec P W (block [.subN 50036 50030 50032, .subN 50041 50036 50002,
        .subN 50044 50036 50031]) d c' k ∧ k = 3 ∧ c'.nreg 50041 = P.n - 1 - e ∧
        c'.nreg 50044 = P.n - 1 - e1 := by
    intro d hd a b' c'' d''
    exec_block
    simp_all
  obtain ⟨c₃, k₃, e₃, hk₃, r41, r44⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 50033 50032
      (block [.subN 50036 50030 50032, .subN 50041 50036 50002, .subN 50044 50036 50031])
      (.ifLtN 50032 50033 (block [.subN 50036 50030 50032, .subN 50041 50036 50002,
          .subN 50044 50036 50031])
        ztksg)) c₂ c₃ k₃ ∧ k₃ ≤ 6 ∧
      c₃.nreg 50041 = (if b = 1 then e else P.n - 1 - e) ∧
      c₃.nreg 50044 = (if b = 1 then e1 else P.n - 1 - e1) := by
    zufqs
    · zuchp
      refine ⟨c', k + 1, .ifLtN_true by_omega ex, by_omega, ?_, ?_⟩
      · grind
      grind
    · zujsp
      · zuchp
        refine ⟨c', k + 1 + 2, .ifLtN_false by_omega
          ztcrz, by_omega, ?_, ?_⟩
        · grind
        grind
      · zukbe
        refine spec_ifLtN_false by_omega
          ztkfj
        exec_block
        refine ztss <;> config_simp <;> rw [ite_eq_left hb1]
        · omega
        omega
  exact ⟨c₃, _, .seq e₁ ztcr, by_omega, r41, r44⟩

/-- **The direction procedure of the interior model** (at most `510` steps). -/
theorem intDir_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) (he : c.nreg 50002 < P.n) (hD : c.nreg 50000 + 1 ≤ W)
    (hbit : c.nmem ztcct = 1 ↔ Mountain.LeftInside zta) :
    ∃ c' k, Exec P W intDir c c' k ∧ k ≤ 510 ∧ FrameB Bdir c c' ∧
      c'.nreg 10502 = dirCode ztwiq ztmgd := by
  obtain ⟨c₁, k₁, e₁, hk₁, r41, r44⟩ := intIdx_exec (P := P) hW c hw he hD
  zud
  obtain ⟨c₂, k₂, e₂, hk₂, a, b, x41, x44⟩ : ∃ c₂ k₂, Exec P W
      ztkrg c₁ c₂ k₂ ∧ k₂ = 2 ∧ c₂.nreg 50040 = 0 ∧
      c₂.nreg 50043 = 0 ∧ c₂.nreg 50041 = c₁.nreg 50041 ∧ c₂.nreg 50044 = c₁.nreg 50044 := by
    exec_block
    · omega
    · omega
    simp
  zudzj
  zufvs
  zulrk
  set ia := (if c.nmem ztcct = 1 then e else P.n - 1 - e)
  set ib := (if c.nmem ztcct = 1 then ztda % P.n else P.n - 1 - ztda % P.n)
  have hia : ia < P.n := by_grind
  have hib : ib < P.n := by
    have := Nat.mod_lt ztda hn0
    grind
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, d₃⟩ := dirTail_exec (P := P) hG hW c₂ e₂.wb_right
    (sa := .vtx ia) (sb := .vtx ib) hia hib ⟨a, by_simp_all⟩ ⟨b, by_simp_all⟩
  have ex : Exec P W intDir c c₃ _ := .seq e₁ ztcr
  refine ⟨c₃, _, ex, by_omega, exec_frameB ex wr_intDir, ?_⟩
  rw [d₃, dirCode_eq]
  simp only [SymPt.eval, Model.wa, Model.wb, interiorModel]
  rw [interiorWalk_n, hn, interiorWalk_vtx _ by_omega,
    interiorWalk_vtx _ (by zvmxq; exact Nat.mod_lt _ hn0), hn]
  grind
end
end NFLoc
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt SideFaces freeIn regionsIn TouchesIn
  sideArc_split)
open Chazelle.Jordan (offset nrm)
open Chazelle.Geometry (lerp point_ext lerp_mem_segment)

/-! ## C9: the arc cover -/

/-- **WP-B (finding C9): the arc cover.**  Every chord family of a good model has an arc, and
every cut key is the start of an arc. -/
theorem arcCover : NFLoc.ArcCoverSpec := by
  zufxh
  zugc

  have hstart : ∀ y : ℝ, M.IsCut F y → ∃ U ∈ M.regions F, ∃ b : ℝ, M.IsArc F U y b := by
    rintro y ⟨c, hc, p, t, hA, rfl⟩
    obtain ⟨U, -, -, r, hU, -, -, harc, -⟩ := hW.attach_face hAdm hfin hc hA
    grind
  refine ⟨?_, hstart⟩
  zuqx
  · obtain ⟨z, hz⟩ := hW.nonempty
    have hfree : freeIn M.D ∅ = M.D := by zunjh
    have hall : ∀ U ∈ M.regions (∅ : Set ztf), U = M.D := by
      rintro U ⟨z', hz', rfl⟩
      rw [hfree] at hz' ⊢
      exact hW.preconn.connectedComponentIn hz'
    have hU : connectedComponentIn M.D z ∈ M.regions (∅ : Set ztf) :=
      ⟨z, by_simp_all, by_simp_all⟩
    have hnocut : ztprb := fun x ⟨c, hc, _⟩ => hc
    obtain ⟨p₀, t₀, hp₀, -, -, -⟩ := hW.exists_faces ztzi finite_empty hU
    have hn : ztcfu := by exact_mod_cast (Nat.zero_lt_of_lt hp₀)
    refine ⟨_, hU, 0, 0, le_rfl, hn, le_rfl, hn, Or.inr ztrei,
      fun x _ => hnocut x, fun p t hp ht0 ht1 _ => ?_⟩
    obtain ⟨U', hU', hf⟩ :=
      hW.exists_faces_of_not_cut ztzi finite_empty hp ztcoy ztvvs
    grind
  · zuice
    obtain ⟨-, -, -, -, -, -, ⟨⟨p, t, hA, -⟩, -⟩, -⟩ := hW.ends c ztqpc
    obtain ⟨U, hU, b, harc⟩ := hstart _ ztcxr
    grind

/-! ## C10: which side the walk faces after an attachment -/

/-- Rescaling a right-neighbourhood of `0` by a positive factor. -/
theorem eventually_mul_pos {P : ℝ → Prop} (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P ε) {w : ℝ} (hw : 0 < w) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), P (δ * w) := by
  have ht : Tendsto (fun δ : ℝ => δ * w) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    zujx
    · have : Tendsto (fun δ : ℝ => δ * w) (𝓝 (0 : ℝ)) (𝓝 (0 * w)) :=
        (continuous_id.mul continuous_const).tendsto 0
      zudvn
      zuhv
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      simp_all
  tauto

/-- The offsets of the midpoint of a horizontal segment. -/
theorem offset_mid_ab {a b : Point} (hy : a.2 = b.2) (δ : ℝ) :
    offset a b ztcn δ = ztxdf := by
  zueoa
namespace WalkAx
variable {M : Model}

/-- **The side faced after an attachment** (walk-axiom form).  Let `c ∈ F` be attached at `A`
(point `a`) and at `B` (point `b ≠ a`).  If a region `U` faces the walk at a position strictly
between `A` and `B` (inside a walk edge), then `U` does not contain the points just on the left of
`a → b` at the midpoint of `c` (equivalently: those points are on the other side of `c`). -/
theorem not_left_of_after (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {c : Set Point} (hc : c ∈ F) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hin : sideInArc ztbf ztbd ztk) (hf : M.Faces p t U) :
    ¬ ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset ztiay ztiaz ztcn δ ∈ U := by
  intro hleft
  have hcA := hF hc
  obtain ⟨hcab, hy, hopen, hEA, hEB⟩ := hM.attach_seg hcA hA hB hAB
  zucgh
  zuftk

  have hsep := hM.hsep hcA hcab hAB hy hopen
  obtain ⟨K₁, K₂, -, ⟨c₁, hK₁⟩, -, hsec₁, -, hF₁, -⟩ := sideArc_split M.W hM.isOpen hAB hM.nd
    hM.trace hM.clean hopen hA' rfl hB' rfl
    (fun p hp t ht ht1 hne' heq => hEA.2 pa p ta t hA.1 hA.2.1 hA.2.2.1 hp ht ht1
      ztdny rfl heq)
    (fun p hp t ht ht1 hne' heq => hEB.2 pb p tb t hB.1 hB.2.1 hB.2.2.1 hp ht ht1
      ztdny rfl heq)
    hsep
  rw [← hcab] at hK₁
  subst hK₁
  have hsub : U ⊆ connectedComponentIn ztjq c₁ :=
    hM.region_subset_of_sector hc hU hp ht hf (hsec₁ p hp t ht.1.le ht.2 hin)
  obtain ⟨δ, h1, h2, h3⟩ := (hleft.and (hF₁.and hsep)).exists
  rw [← hcab] at h3
  apply h3
  rw [← connectedComponentIn_eq (hsub h1), ← connectedComponentIn_eq h2]
end WalkAx

/-- **WP-B (finding C10): the side faced after an attachment.** -/
theorem upSide : UpSideSpec := by
  zudib

  have hAdm := hF.2.1
  obtain ⟨U, V, hU, hV, hUV, hcU, hcV, δ, hδ, hfac⟩ := attachFaceNC M Q F hM hF c hc p t hA hsole
  obtain ⟨Up, Dn, hUp, hDn, hUD, hside, htouch⟩ := chordSides M Q F hM hF c hc
  have hU2 := (htouch U hU).1 hcU
  have hV2 := (htouch V hV).1 hcV
  -- the other attachment
  obtain ⟨pb, tb, hB, hBne⟩ := hW.other_attach ztqpc hA
  have hAB : sidePt M.W p t ≠ sidePt M.W pb tb := Ne.symm hBne
  obtain ⟨hcab, hy, hopen, -, -⟩ := hW.attach_seg ztqpc hA hB hAB
  have hkne : (p : ℝ) + t ≠ pb + tb := WalkAx.key_ne_of_pt_ne hA hB hAB
  -- a position just after `A`, facing `U`
  obtain ⟨ε, hε1, hε2, hε3⟩ := ((WalkAx.exists_pos_after hA.2.1 hA.2.2.1).and
    ((WalkAx.eventually_after_start hkne).and (Ioo_mem_nhdsGT hδ))).exists
  have hin : sideInArc ztk ztbd ztzxl := by_grind
  have hfU : M.Faces p zthkr U := (hfac p zthkr hA.1 hε1.1 hε1.2).1
    (Or.inl ztsr)
  have hnot := hW.not_left_of_after hAdm hc hA hB hAB hU hA.1 hε1 hin hfU
  -- the midpoint of the chord
  set a := sidePt M.W p t with ha
  set b := sidePt M.W pb tb with hb
  have hmid : ztxmn := by
    zubij
  have hmidD : lerp a b ztcn ∈ M.D := hopen _ ztfm
  have hsm := hside _ hmid hmidD
  have hbc : b ∈ c := by zvmyh; exact Geometry.right_mem_segment _ _
  have hne1 : ztsdk := fun h => hAB (point_ext h hy)
  have hpt : lerp ztpr ztoa t = a := rfl
  have hBelow : M.BelowOf c Dn := fun z hz hzD => (hside z hz hzD).mono fun _ h => h.2
  have hAbove : M.AboveOf c Up := fun z hz hzD => (hside z hz hzD).mono fun _ h => h.1
  refine ⟨U, V, hU, hV, hUV, ⟨δ, hδ, hfac⟩, fun hleft => ?_, fun hright => ?_⟩
  · -- `a` is the left endpoint: `U` is below
    have hlt : a.1 < b.1 := lt_of_le_of_ne (hpt ▸ hleft b hbc) hne1
    have hUDn : U = Dn := by
      zukku
      · exfalso
        zulvs
        have := eventually_mul_pos (hsm.mono fun _ h => h.1) zteau
        zuzx
        zuflu

        zuclh
      omega
    grind
  · -- `a` is the right endpoint: `U` is above
    have hlt : b.1 < a.1 := lt_of_le_of_ne (hpt ▸ hright b hbc) (Ne.symm hne1)
    have hUUp : U = Up := by
      zukku
      · zubh
      · exfalso
        zulvs
        have := eventually_mul_pos (hsm.mono fun _ h => h.2) zteau
        zuzx
        zuflu

        grind
    grind
