module

public import Chazelle.MacT
public import Chazelle.Core.NFDecompRamRound

namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
@[expose] public section
def StCRG (r : ℕ) : Prop := ztbxr ∨ (130820 ≤ r ∧ r ≤ 130869)

/-- The registers of the halving step. -/
def HRG (r : ℕ) : Prop := 130820 ≤ r ∧ r ≤ 130823

/-- One entry of the halving table. -/
def halfBody : Stmt := .seq ztjot
  (.seq (.ifLtN 130822 130001 ztoto
    ztepl)
    (.instr (.addN 130820 130820 130001)))

/-- **The halving table.** -/
def halfS : Stmt := .seq (block [.constN 130820 0, .constN 130821 0, .constN 130822 0,
  .addN 130824 130011 130001]) (.whileLtN 130820 130824 halfBody)

/-- One power of two. -/
def powBody : Stmt := block [.addN 130827 130070 130825, .storeN 130827 130826,
  .addN 130826 130826 130826, .addN 130825 130825 130001]

/-- **The powers of two.** -/
def powS : Stmt := .seq ztkqs
  (.whileLtN 130825 130017 powBody)

/-- One residue. -/
def resBody : Stmt := .seq (block [.addN 130830 130063 130828, .storeN 130830 130829,
  .addN 130829 130829 130001])
  (.seq ztipm
    (.instr (.addN 130828 130828 130001)))

/-- **The residues.** -/
def resS : Stmt := .seq ztkqt
  (.whileLtN 130828 130011 resBody)
section proofs
variable {P : Polygon} {W : ℕ}
variable {g : GV} {c : Config}
theorem halfS_exec (hw : WordsBounded W c) (hG : GR g c)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W halfS c c' k ∧ k ≤ 11 * g.μ + 20 ∧ WordsBounded W c' ∧
      PFr StCRG ztcqv c c' ∧
      ∀ w, w ≤ g.μ → c'.nmem zthxm = w / 2 := by
  have hU := g.U_ge; have hE := g.END_eq; have b39 := g.base_eq 39
  unfold halfS
  obtain ⟨c1, k1, e1, hk1, hw1, h20, h21, h22, h24, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 130820 0, .constN 130821 0, .constN 130822 0, .addN 130824 130011 130001])
      c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 130820 = 0 ∧ c1.nreg 130821 = 0 ∧
      c1.nreg 130822 = 0 ∧ c1.nreg 130824 = g.μ + 1 ∧
      PFr StCRG ztcqv c c1 := by
    exec_block
    all_goals try (config_simp; rw [hG.rμ, hG.one]; omega)
    zubqj
    refine ⟨rfl, by_omega, by config_simp, by config_simp, by config_simp,
      by config_simp; zuoih, ztrg⟩
    zucad
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  obtain ⟨c', k, e, hk, hw', hi', hn', h21', h22', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130820) (rn := 130824) (body := halfBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130820 = j ∧ c'.nreg 130824 = g.μ + 1 ∧
      c'.nreg 130821 = j / 2 ∧ c'.nreg 130822 = j % 2 ∧
      PFr StCRG ztcqv c c' ∧
      ∀ w, w < j → c'.nmem zthxm = w / 2)
    zttlc 7 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, hh2, hp2, hf2, hm2⟩ => by
      have hG2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      have r69 := hG2.rbase 39 by_omega
      zudqb
      set Am : ℕ → Prop := fun a => g.base 39 ≤ a ∧ a < g.base 39 + zttlc with hAm
      obtain ⟨c3, k3, e3, hk3, hw3, hf3, hm3, h20, h21, h22, h1⟩ : ∃ c3 k3, Exec P W
          ztjot c2 c3 k3 ∧ k3 = 2 ∧
          WordsBounded W c3 ∧ PFr HRG Am c2 c3 ∧
          c3.nmem = upd c2.nmem (g.base 39 + j) ztwm ∧
          c3.nreg 130820 = j ∧ c3.nreg 130821 = j / 2 ∧ c3.nreg 130822 = j % 2 ∧
          c3.nreg 130001 = 1 := by
        exec_block
        · grind
        · refine ⟨rfl, by_omega, ztsu, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [Machine.upd_other _ _ _ (show r ≠ 130823 by
              unfold HRG at hr; omega)]
          · config_simp; rw [r69, hi2, Machine.upd_other _ _ _ by_omega]
          · simp_all
          · simp_all
          · simp_all
          · simp_all
          simp_all
      -- the parity step
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, hm4, h20', h21', h22', h1'⟩ : ∃ c4 k4, Exec P W
          (.ifLtN 130822 130001 ztoto
            ztepl) c3 c4 k4 ∧ k4 ≤ 4 ∧
          WordsBounded W c4 ∧ PFr HRG Am c3 c4 ∧ c4.nmem = c3.nmem ∧ c4.nreg 130820 = j ∧
          c4.nreg 130821 = ztl / 2 ∧ c4.nreg 130822 = ztl % 2 ∧
          c4.nreg 130001 = 1 := by
        by_cases hp : c3.nreg 130822 < c3.nreg 130001
        · have e := Exec.constN (P := P) hw3 130822 1 by_omega
          zuiih
          refine ⟨_, 1 + 1, .ifLtN_true by_omega e, by_omega, e.wb_right,
            ⟨fun r hr => ?_, rfl, rfl, rfl, by_simp_all⟩, rfl, ?_, ?_, ?_, ?_⟩
          · simp only [Machine.upd_other _ _ _ (show r ≠ 130822 by
              unfold HRG at hr; omega)]
          all_goals config_simp
          · omega
          · omega
          · omega
          omega
        · zuiih
          obtain ⟨c5, k5, e5, hk5, hw5, hf5, hm5, h5a, h5b, h5c, h5d⟩ : ∃ c5 k5, Exec P W
              ztepl c3 c5 k5 ∧ k5 = 2 ∧
              WordsBounded W c5 ∧ PFr HRG Am c3 c5 ∧ c5.nmem = c3.nmem ∧
              c5.nreg 130820 = j ∧ c5.nreg 130821 = ztl / 2 ∧ c5.nreg 130822 = ztl % 2 ∧
              c5.nreg 130001 = 1 := by
            exec_block
            · omega
            · config_simp; omega
            · refine ⟨rfl, by_omega, ztrg, rfl, ?_, ?_, ?_,
                ?_⟩
              · simp only [Machine.upd_other _ _ _ (show r ≠ 130822 by
                  unfold HRG at hr; omega), Machine.upd_other _ _ _ (show r ≠ 130821 by
                  unfold HRG at hr; omega)]
              all_goals config_simp
              · omega
              · omega
              · omega
              omega
          exact ⟨c5, k5 + 2, .ifLtN_false by_omega e5, by_omega, hw5, hf5, hm5,
            h5a, h5b, h5c, h5d⟩
      have e6 := Exec.addN (P := P) hw4 130820 130820 130001 by_omega
      have hf6 : PFr HRG Am c4 { c4 with nreg := upd c4.nreg 130820 (c4.nreg 130820 +
          c4.nreg 130001) } := ⟨fun r hr => by
            simp only [Machine.upd_other _ _ _ (show r ≠ 130820 by
              unfold HRG at hr; omega)], rfl, rfl, rfl, by_simp_all⟩
      refine ⟨_, k3 + ztfsx, .seq e3 ztgxa, by_omega, e6.wb_right, ?_, ?_, ?_, ?_,
        hf2.trans ((hf3.trans ztjxt).mono (fun r h => by
          simp only [HRG, StCRG] at h ⊢; omega) by_omega), fun w hw => ?_⟩
      · simp_all
      · rw [(hf3.trans ztjxt).1 130824 (by unfold HRG; omega)]; omega
      · simp_all
      · simp_all
      · show c4.nmem _ = _
        zuedf
        grind)
    (j₀ := 0) ⟨hw1, h20, h24, by zuouf, by zuoug, hf1, fun w hw => by_omega⟩
    ztbg
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw', hf', by_simp_all⟩

/-- The residue after a step. -/
theorem mod_succ_step {k : ℕ} (hk : 0 < k) (j : ℕ) :
    ztl % k = (if j % k + 1 < k then j % k + 1 else 0) ∧
    ztl / k = (if j % k + 1 < k then j / k else j / k + 1) := by
  have h := Nat.div_add_mod j k
  have hr := Nat.mod_lt j hk
  by_cases h1 : j % k + 1 < k
  · rw [ite_eq_left h1, ite_eq_left h1]
    have e : j + 1 = (j % k + 1) + k * (j / k) := by_omega
    constructor
    · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
    · rw [e, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt h1]; omega
  · rw [ite_eq_right h1, ite_eq_right h1]
    have e : j + 1 = k * (j / k + 1) := by_grind
    simp_all
theorem powS_exec (hw : WordsBounded W c) (hG : GR g c)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W powS c c' k ∧ k ≤ 6 * g.L + 4 ∧ WordsBounded W c' ∧
      PFr StCRG ztdno c c' ∧
      ∀ j, j < g.L → c'.nmem ztlpe = 2 ^ j := by
  have hU := g.U_ge; have hE := g.END_eq; have b40 := g.base_eq 40
  have hPU := g.P_le_U; have hLU := g.L_le_U
  unfold powS
  obtain ⟨c1, k1, e1, hk1, hw1, h25, h26, hf1⟩ : ∃ c1 k1, Exec P W
      ztkqs c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧
      c1.nreg 130825 = 0 ∧ c1.nreg 130826 = 1 ∧
      PFr StCRG ztdno c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, by_omega, by config_simp, by config_simp, ⟨fun r hr => ?_, rfl, rfl, rfl,
      by simp_all⟩⟩
    zucad
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hL1 := (hG.frame (fun r hr => hf1.1 r (by
    unfold GRReg at hr; unfold StCRG; omega))).rL
  obtain ⟨c', k, e, hk, hw', hi', hn', h26', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130825) (rn := 130017) (body := powBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130825 = j ∧ c'.nreg 130017 = g.L ∧
      c'.nreg 130826 = 2 ^ j ∧
      PFr StCRG ztdno c c' ∧
      ∀ i, i < j → c'.nmem (g.base 40 + i) = 2 ^ i)
    g.L 4 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, hp2, hf2, hm2⟩ => by
      have hG2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      have r70 := hG2.rbase 40 by_omega
      zudqb
      have hpj : 2 ^ ztl ≤ 2 ^ g.L := Nat.pow_le_pow_right by_omega hj
      have hpj' : ztycf := by_ring
      unfold powBody
      exec_block
      · grind
      · config_simp; omega
      · config_simp; omega
      · refine ⟨le_refl _, by omega, by simp_all, by simp_all,
          by simp_all, hf2.trans ⟨fun r hr => ?_, rfl, rfl, rfl,
          fun a ha => ?_⟩, fun i hi => ?_⟩
        · simp only; simp only [StCRG] at hr ⊢
          repeat (rw [Machine.upd_other _ _ _ (by omega)])
        · config_simp; rw [r70, hi2, Machine.upd_other _ _ _ by_omega]
        · config_simp; rw [r70, hi2, hp2, Machine.upd_apply]
          grind)
    (j₀ := 0) ⟨hw1, h25, hL1, by_omega, hf1, fun i hi => by_omega⟩ ztbg
  exact ztcxq

/-- The registers of the residue step. -/
def RRG (r : ℕ) : Prop := 130828 ≤ r ∧ r ≤ 130830
theorem resS_exec (hw : WordsBounded W c) (hG : GR g c) (hk : 0 < g.k')
    (hkμ : g.k' ≤ g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W resS c c' k ∧ k ≤ 9 * g.μ + 4 ∧ WordsBounded W c' ∧
      PFr StCRG ztdnn c c' ∧
      ∀ l, l < g.μ → c'.nmem ztlpc = l % g.k' := by
  have hU := g.U_ge; have hE := g.END_eq; have b33 := g.base_eq 33
  unfold resS
  obtain ⟨c1, k1, e1, hk1, hw1, h28, h29, hf1⟩ : ∃ c1 k1, Exec P W
      ztkqt c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧
      c1.nreg 130828 = 0 ∧ c1.nreg 130829 = 0 ∧
      PFr StCRG ztdnn c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, by_omega, by config_simp, by config_simp, ⟨fun r hr => ?_, rfl, rfl, rfl,
      by simp_all⟩⟩
    zucad
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hμ1 := (hG.frame (fun r hr => hf1.1 r (by
    unfold GRReg at hr; unfold StCRG; omega))).rμ
  obtain ⟨c', k, e, hk', hw', hi', hn', h29', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130828) (rn := 130011) (body := resBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130828 = j ∧ c'.nreg 130011 = g.μ ∧
      c'.nreg 130829 = j % g.k' ∧
      PFr StCRG ztdnn c c' ∧
      ∀ l, l < j → c'.nmem ztlpc = l % g.k')
    g.μ 7 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, hr2, hf2, hm2⟩ => by
      have hG2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      have r63 := hG2.rbase 33 by_omega
      zudqb
      have rk := hG2.rk'
      have hrl : j % g.k' < g.k' := Nat.mod_lt _ hk
      obtain ⟨hmod, -⟩ := mod_succ_step hk j
      set Am : ℕ → Prop := fun a => g.base 33 ≤ a ∧ a < g.base 33 + g.μ with hAm
      obtain ⟨c3, k3, e3, hk3, hw3, hf3, hm3, h28, h29, h1, hk3'⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130830 130063 130828, .storeN 130830 130829, .addN 130829 130829 130001])
          c2 c3 k3 ∧ k3 = 3 ∧ WordsBounded W c3 ∧ PFr RRG Am c2 c3 ∧
          c3.nmem = upd c2.nmem (g.base 33 + j) (j % g.k') ∧
          c3.nreg 130828 = j ∧ c3.nreg 130829 = j % g.k' + 1 ∧
          c3.nreg 130001 = 1 ∧ c3.nreg 130015 = g.k' := by
        exec_block
        · grind
        · config_simp; omega
        · refine ⟨rfl, by omega, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
          · simp only; unfold RRG at hr
            repeat (rw [Machine.upd_other _ _ _ (by omega)])
          · config_simp; rw [r63, hi2, Machine.upd_other _ _ _ by_omega]
          · simp_all
          · simp_all
          · simp_all
          · simp_all
          simp_all
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, hm4, h28', h29', h1'⟩ : ∃ c4 k4, Exec P W
          ztipm c3 c4 k4 ∧ k4 ≤ 3 ∧
          WordsBounded W c4 ∧ PFr RRG Am c3 c4 ∧ c4.nmem = c3.nmem ∧ c4.nreg 130828 = j ∧
          c4.nreg 130829 = ztl % g.k' ∧ c4.nreg 130001 = 1 := by
        by_cases hp : c3.nreg 130829 < c3.nreg 130015
        · refine ⟨c3, 0 + 1, .ifLtN_true hp ztdyd, by_omega, hw3, PFr.refl c3, rfl, h28,
            ?_, h1⟩
          simp_all
        · have e := Exec.constN (P := P) hw3 130829 0 by_omega
          refine ⟨_, 1 + 2, .ifLtN_false hp e, by_omega, e.wb_right,
            ⟨fun r hr => ?_, rfl, rfl, rfl, by_simp_all⟩, rfl, ?_, ?_, ?_⟩
          · simp only [Machine.upd_other _ _ _ (show r ≠ 130829 by
              unfold RRG at hr; omega)]
          all_goals config_simp
          · omega
          · simp_all
          omega
      have e6 := Exec.addN (P := P) hw4 130828 130828 130001 by_omega
      have hf6 : PFr RRG Am c4 { c4 with nreg := upd c4.nreg 130828 (c4.nreg 130828 +
          c4.nreg 130001) } := ⟨fun r hr => by
            simp only [Machine.upd_other _ _ _ (show r ≠ 130828 by
              unfold RRG at hr; omega)], rfl, rfl, rfl, by_grind⟩
      refine ⟨_, k3 + ztfsx, .seq e3 ztgxa, by_omega, e6.wb_right, ?_, ?_, ?_,
        hf2.trans ((hf3.trans ztjxt).mono (fun r h => by
          simp only [RRG, StCRG] at h ⊢; omega) by_omega), fun l hl => ?_⟩
      · simp_all
      · rw [(hf3.trans ztjxt).1 130011 (by unfold RRG; omega)]; omega
      · simp_all
      · show c4.nmem _ = _
        zuedf
        grind)
    (j₀ := 0) ⟨hw1, h28, hμ1, by_simp_all, hf1, fun l hl => by_omega⟩ ztbg
  exact ztcxq
end proofs
def rcBody : Stmt := block [.addN 130832 130033 130831, .loadN 130832 130832,
  .addN 130832 130063 130832, .loadN 130832 130832, .addN 130832 130064 130832,
  .loadN 130833 130832, .addN 130833 130833 130001, .storeN 130832 130833,
  .addN 130831 130831 130001]

/-- **The residue counts.** -/
def rcS : Stmt := .seq (fillWith 130064 130015 130009)
  (.seq (.instr (.constN 130831 0)) (.whileLtN 130831 130011 rcBody))

/-- The number of vertices below `j` whose value `f` is `r`. -/
noncomputable def cntBelow (f : ℕ → ℕ) (j r : ℕ) : ℕ :=
  ((Finset.range j).filter (fun v => f v = r)).card
variable (f : ℕ → ℕ) (j r : ℕ)
theorem cntBelow_succ :
    cntBelow f ztl r = cntBelow f j r + if f j = r then 1 else 0 := by
  zujqi
  zuewn
theorem cntBelow_le : cntBelow f j r ≤ j := by
  zujqi
  grind

/-- One residue of the minimum search. -/
def argBody : Stmt := .seq ztjou
  (.seq ztyzp
    (.instr (.addN 130834 130834 130001)))

/-- **The lightest residue** `ρ` (register `130836`). -/
def argS : Stmt := .seq zthdy
  (.whileLtN 130834 130015 argBody)

/-- The registers of the minimum search. -/
def ARG (r : ℕ) : Prop := 130834 ≤ r ∧ r ≤ 130837
section proofs
variable {P : Polygon} {W : ℕ}
variable {g : GV} {c : Config}
theorem rcS_exec (hw : WordsBounded W c) (hG : GR g c) (hk : 0 < g.k')
    (hkμ : g.k' ≤ g.μ) {lev : ℕ → ℕ} (hlev : ∀ v, v < g.μ → c.nmem ztjc = lev v)
    (hlt : ∀ v, v < g.μ → lev v < g.μ)
    (hres : ∀ l, l < g.μ → c.nmem ztlpc = l % g.k') (hW : g.END ≤ W) :
    ∃ c' k, Exec P W rcS c c' k ∧ k ≤ 11 * g.μ + 5 * g.k' + 12 ∧ WordsBounded W c' ∧
      PFr StCRG ztcdd c c' ∧
      ∀ r, r < g.k' → c'.nmem ztlpd = cntBelow ztdhh g.μ r := by
  have hU := g.U_ge; have hE := g.END_eq; have b33 := g.base_eq 33; have b34 := g.base_eq 34
  have b3 := g.base_eq 3
  unfold rcS
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hz1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 34 by_omega) hG.rk' hG.zero ztpc ztpc
    ztpc by_omega by_omega
  have f1 : PFr StCRG ztcdd c c1 :=
    hf1.mono (fun r h => by unfold FillRG at h; unfold StCRG; omega) by_omega
  have e2 := Exec.constN (P := P) hw1 130831 0 by_omega
  set c2 := { c1 with nreg := upd c1.nreg 130831 0 } with hc2
  have f2 : PFr StCRG ztcdd c c2 :=
    f1.trans ⟨fun r hr => by simp only [c2, Machine.upd_other _ _ _ (show r ≠ 130831 by
      unfold StCRG at hr; omega)], rfl, rfl, rfl, by_simp_all⟩
  have hG2 := hG.frame (fun r hr => f2.1 r ztdcm)
  obtain ⟨c', k, e, hk', hw', hi', hn', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130831) (rn := 130011) (body := rcBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130831 = j ∧ c'.nreg 130011 = g.μ ∧
      PFr StCRG ztcdd c c' ∧
      ∀ r, r < g.k' → c'.nmem ztlpd = cntBelow ztdhh j r)
    g.μ 9 zthd
    (fun j c3 hj ⟨hw3, hi3, hn3, hf3, hm3⟩ => by
      have hG3 := hG.frame (fun r hr => hf3.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      have r33 := hG3.rbase 3 by_omega
      have r63 := hG3.rbase 33 by_omega
      have r64 := hG3.rbase 34 by_omega
      zumfp
      zufvi
      have ml : ztzpj := by
        zubbh
      have mr : c3.nmem (g.base 33 + lev j) = lev j % g.k' := by
        zubbh
      have hrk : lev j % g.k' < g.k' := Nat.mod_lt _ hk
      have hcnt := hm3 _ hrk
      have hcle := cntBelow_le ztdhh j (lev j % g.k')
      unfold rcBody
      exec_block
      · grind
      · config_simp; rw [r63, r33, hi3, ml]; omega
      · config_simp; rw [r64, r63, r33, hi3, ml, mr]; omega
      · config_simp; rw [r64, r63, r33, hi3, ml, mr, hcnt, r1]; omega
      · config_simp; omega
      · refine ⟨le_refl _, by omega, by config_simp; omega, by config_simp; omega,
          hf3.trans ztsu, fun r hr => ?_⟩
        · simp only; simp only [StCRG] at hr ⊢
          repeat (rw [Machine.upd_other _ _ _ (by omega)])
        · config_simp; rw [r64, r63, r33, hi3, ml, mr, Machine.upd_other _ _ _ by_omega]
        · config_simp
          rw [r64, r63, r33, hi3, ml, mr, hcnt, r1, Machine.upd_apply, cntBelow_succ]
          zudlv
          · grind
          · omega
          · omega
          grind)
    (j₀ := 0) ⟨e2.wb_right, by_rfl, by rw [hG2.rμ], f2, fun r hr => by
      rw [show c2.nmem = c1.nmem from rfl, hz1 r hr]; rfl⟩ (Nat.zero_le _)
  exact ztedp
theorem argS_exec (hw : WordsBounded W c) (hG : GR g c) (hk : 0 < g.k')
    (hkμ : g.k' ≤ g.μ) {cnt : ℕ → ℕ} (hcnt : ∀ r, r < g.k' → c.nmem ztlpd = cnt r)
    (hcle : ∀ r, r < g.k' → cnt r ≤ g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W argS c c' k ∧ k ≤ 9 * g.k' + 5 ∧ WordsBounded W c' ∧
      PFr StCRG ztbvx c c' ∧ c'.nreg 130836 < g.k' ∧
      ∀ r, r < g.k' → cnt ztvgd ≤ cnt r := by
  have hU := g.U_ge; have hE := g.END_eq; have b34 := g.base_eq 34
  unfold argS
  obtain ⟨c1, k1, e1, hk1, hw1, h34, h35, h36, hf1⟩ : ∃ c1 k1, Exec P W
      zthdy c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130834 = 0 ∧ c1.nreg 130835 = g.μ + 1 ∧
      c1.nreg 130836 = 0 ∧ PFr StCRG ztbvx c c1 := by
    exec_block
    all_goals try (config_simp; rw [hG.rμ, hG.one]; omega)
    zubqj
    refine ⟨rfl, by_omega, by config_simp, by config_simp; zuoih, by config_simp,
      ⟨fun r hr => ?_, rfl, rfl, rfl, by_simp_all⟩⟩
    zucad
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hk1' := (hG.frame (fun r hr => hf1.1 r (by
    unfold GRReg at hr; unfold StCRG; omega))).rk'
  obtain ⟨c', k, e, hk', hw', hi', hn', hb', hr', hf'⟩ := forN (P := P) (W := W)
    (ri := 130834) (rn := 130015) (body := argBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130834 = j ∧ c'.nreg 130015 = g.k' ∧
      ((j = 0 ∧ c'.nreg 130835 = g.μ + 1 ∧ c'.nreg 130836 = 0) ∨
        (0 < j ∧ c'.nreg 130836 < j ∧ c'.nreg 130835 = cnt ztvgd)) ∧
      (∀ r, r < j → c'.nreg 130835 ≤ cnt r) ∧
      PFr StCRG ztbvx c c')
    g.k' 7 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, hst2, hmin2, hf2⟩ => by
      have hG2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      have r64 := hG2.rbase 34 by_omega
      zudqb
      have mj : c2.nmem (g.base 34 + j) = cnt j := by
        rw [hf2.2.2.2.2 _ by_simp]; simp_all
      have hcj := hcle j hj
      obtain ⟨c3, k3, e3, hk3, hw3, hf3, h37, h3⟩ : ∃ c3 k3, Exec P W
          ztjou c2 c3 k3 ∧ k3 = 2 ∧
          WordsBounded W c3 ∧ PFr ARG ztbvx c2 c3 ∧ c3.nreg 130837 = cnt j ∧
          (∀ r, r ≠ 130837 → c3.nreg r = c2.nreg r) := by
        exec_block
        · grind
        · refine ⟨rfl, by omega, ⟨fun r hr => ?_, rfl, rfl, rfl, by simp_all⟩, ?_, fun r hr => ?_⟩
          · zujpf
            repeat (rw [Machine.upd_other _ _ _ (by omega)])
          · simp_all
          simp_all
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, h4⟩ : ∃ c4 k4, Exec P W
          ztyzp
          c3 c4 k4 ∧ k4 ≤ 3 ∧ WordsBounded W c4 ∧ PFr ARG ztbvx c3 c4 ∧
          (c4.nreg 130834 = j ∧ ((0 < j + 1 ∧ c4.nreg 130836 < j + 1 ∧
            c4.nreg 130835 = cnt (c4.nreg 130836)) ∧
            ∀ r, r < j + 1 → c4.nreg 130835 ≤ cnt r)) := by
        by_cases hp : c3.nreg 130837 < c3.nreg 130835
        · obtain ⟨c5, k5, e5, hk5, hw5, hf5, h5a, h5b, h5c⟩ : ∃ c5 k5, Exec P W
              ztfbm c3 c5 k5 ∧ k5 = 2 ∧
              WordsBounded W c5 ∧ PFr ARG ztbvx c3 c5 ∧ c5.nreg 130835 = cnt j ∧
              c5.nreg 130836 = j ∧ c5.nreg 130834 = j := by
            exec_block
            refine ⟨rfl, by_omega, ztrg, ?_, ?_, ?_⟩
            · zujpf
              repeat (rw [Machine.upd_other _ _ _ (by omega)])
            · simp_all
            · simp_all
            simp_all
          refine ⟨c5, k5 + 1, .ifLtN_true hp e5, by_omega, hw5, hf5, h5c, by_simp_all, fun r hr => ?_⟩
          grind
        · refine ⟨c3, 0 + 2, .ifLtN_false hp ztdyd, by_omega, hw3, PFr.refl c3,
            by simp_all, ?_, fun r hr => ?_⟩
          · grind
          grind
      have e6 := Exec.addN (P := P) hw4 130834 130834 130001 (by
        zunik; omega)
      have hf6 : PFr ARG ztbvx c4
          { c4 with nreg := upd c4.nreg 130834 (c4.nreg 130834 + c4.nreg 130001) } :=
          ⟨fun r hr => by
            simp only [Machine.upd_other _ _ _ (show r ≠ 130834 by
              unfold ARG at hr; omega)], rfl, rfl, rfl, by_simp_all⟩
      refine ⟨_, k3 + ztfsx, .seq e3 ztgxa, by_omega, e6.wb_right, ?_, ?_, Or.inr ?_,
        ?_, hf2.trans ((hf3.trans ztjxt).mono
          (fun r h => by simp only [ARG, StCRG] at h ⊢; omega) by_simp_all)⟩
      · zuvz
        zunik
      · simp only [Machine.upd_other _ _ _ (show (130015 : ℕ) ≠ 130834 by omega)]
        rw [hf4.1 _ ztjqo, h3 _ by_omega]; omega
      · simp_all
      · simp only [Machine.upd_other _ _ _ (show (130835 : ℕ) ≠ 130834 by omega)]
        grind)
    (j₀ := 0) ⟨hw1, h34, hk1', Or.inl ⟨rfl, h35, h36⟩, fun r hr => by_omega, hf1⟩
    ztbg
  rcases hb' with h0 | ⟨-, hlt, heq⟩
  · simp_all
  · exact ⟨c', k1 + k, .seq e1 e, by_omega, hw', hf', hlt, by_simp_all⟩
end proofs
def lvStore : Stmt := block [.addN 130843 130067 130840, .subN 130844 130840 130841,
  .storeN 130843 130844, .addN 130843 130068 130840, .addN 130844 130840 130839,
  .subN 130844 130844 130841, .storeN 130843 130844, .addN 130843 130065 130840,
  .storeN 130843 130842, .addN 130843 130066 130840]

/-- One level. -/
def lvBody : Stmt := .seq lvStore
  (.seq ztfmc
  (.seq (.instr (.addN 130841 130841 130001))
  (.seq ztgbo
    (.instr (.addN 130840 130840 130001)))))

/-- **The level tables.** -/
def lvS : Stmt := .seq (block [.subN 130839 130015 130001, .subN 130838 130839 130836,
  .constN 130840 0, .copyN 130841 130838, .constN 130842 0]) (.whileLtN 130840 130011 lvBody)

/-- The registers of the level step. -/
def LVRG (r : ℕ) : Prop := 130840 ≤ r ∧ r ≤ 130844

/-- The memory of the level tables. -/
def LvMem (g : GV) (a : ℕ) : Prop := g.base 35 ≤ a ∧ a < g.base 39

/-- The table entries of the level `l` for the shift `c`. -/
def LvOK (g : GV) (m : ℕ → ℕ) (c l : ℕ) : Prop :=
  m (g.base 37 + l) = l - ztjzu % g.k' ∧
  m (g.base 38 + l) = l + zttlb - ztjzu % g.k' ∧
  m ztcdg = ztjzu / g.k' ∧
  m ztcnm = if ztjzu % g.k' < g.k' - 1 then 0 else 1
section proofs
variable {P : Polygon} {W : ℕ}
variable {g : GV}
set_option maxHeartbeats 4000000 in
theorem lvBody_exec {c2 : Config} (hw2 : WordsBounded W c2) (hG2 : GR g c2)
    (hk : 0 < g.k') (hkμ : g.k' ≤ g.μ) {j cs : ℕ} (hj : j < g.μ) (hc : cs < g.k')
    (h40 : c2.nreg 130840 = j) (h41 : c2.nreg 130841 = ztcag % g.k')
    (h42 : c2.nreg 130842 = ztcag / g.k') (h39 : c2.nreg 130839 = g.k' - 1)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W lvBody c2 c' k ∧ k ≤ 20 ∧ WordsBounded W c' ∧
      PFr LVRG zthrf c2 c' ∧ c'.nreg 130840 = j + 1 ∧
      c'.nreg 130841 = ztgkn % g.k' ∧ c'.nreg 130842 = ztgkn / g.k' ∧
      LvOK g c'.nmem cs j ∧
      (∀ a, a ≠ g.base 37 + j → a ≠ g.base 38 + j → a ≠ g.base 35 + j → a ≠ g.base 36 + j →
        c'.nmem a = c2.nmem a) := by
  zuuv
  zudgx
  have b38 := g.base_eq 38; have b39 := g.base_eq 39
  have r65 := hG2.rbase 35 by_omega; have r66 := hG2.rbase 36 by_omega
  have r67 := hG2.rbase 37 by_omega; have r68 := hG2.rbase 38 by_omega
  have r1 := hG2.one; have r0 := hG2.zero; have rk := hG2.rk'
  have ht : ztcag % g.k' < g.k' := Nat.mod_lt _ hk
  have hb : ztcag / g.k' ≤ j + cs := Nat.div_le_self _ _
  obtain ⟨hmod, hdiv⟩ := mod_succ_step hk ztcag
  rw [show j + cs + 1 = j + 1 + cs by omega] at hmod hdiv
  unfold lvBody
  -- the stores
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hm3, h43, h40', h41', h42', h39', h1', h0', hk'⟩ :
      ∃ c3 k3, Exec P W lvStore c2 c3 k3 ∧ k3 = 10 ∧ WordsBounded W c3 ∧
      PFr LVRG zthrf c2 c3 ∧
      c3.nmem = upd (upd (upd c2.nmem (g.base 37 + j) (j - ztcag % g.k'))
        (g.base 38 + j) (j + zttlb - ztcag % g.k')) (g.base 35 + j) ((j + cs) / g.k') ∧
      c3.nreg 130843 = g.base 36 + j ∧ c3.nreg 130840 = j ∧
      c3.nreg 130841 = ztcag % g.k' ∧ c3.nreg 130842 = ztcag / g.k' ∧
      c3.nreg 130839 = g.k' - 1 ∧ c3.nreg 130001 = 1 ∧ c3.nreg 130009 = 0 ∧
      c3.nreg 130015 = g.k' := by
    unfold lvStore
    exec_block
    all_goals try (config_simp; simp only [r65, r66, r67, r68, h40, h41, h39]; omega)
    refine ⟨rfl, by_omega, ztsu, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · simp only; unfold LVRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    · unfold LvMem at ha
      config_simp; simp only [r65, r67, r68, h40, h41, h39, h42]
      rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
    all_goals (config_simp; simp only [r65, r66, r67, r68, h40, h41, h39, h42, r1, r0, rk])
  -- the light flag
  set hl := if ztcag % g.k' < g.k' - 1 then 0 else 1 with hhl
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hm4, hr4⟩ : ∃ c4 k4, Exec P W
      ztfmc
      c3 c4 k4 ∧ k4 ≤ 3 ∧ WordsBounded W c4 ∧ PFr LVRG zthrf c3 c4 ∧
      c4.nmem = upd c3.nmem (g.base 36 + j) hl ∧ c4.nreg = c3.nreg := by
    by_cases hp : c3.nreg 130841 < c3.nreg 130839
    · have e := Exec.storeN (P := P) hw3 130843 130009
      refine ⟨_, 1 + 1, .ifLtN_true hp e, by_omega, e.wb_right,
        ⟨by_grind, rfl, rfl, rfl, fun a ha => ?_⟩, ?_⟩
      · zufcv
      grind
    · have e := Exec.storeN (P := P) hw3 130843 130001
      refine ⟨_, 1 + 2, .ifLtN_false hp e, by_omega, e.wb_right,
        ⟨by_grind, rfl, rfl, rfl, fun a ha => ?_⟩, ?_⟩
      · zufcv
      grind
  -- the step of the residue
  have e5 := Exec.addN (P := P) hw4 130841 130841 130001 by_grind
  set c5 := { c4 with nreg := upd c4.nreg 130841 _ } with hc5
  have h5t : c5.nreg 130841 = ztcag % g.k' + 1 := by simp [c5, hr4, h41', h1']
  have h5r : ∀ r, r ≠ 130841 → c5.nreg r = c3.nreg r := fun r hr => by
    simp only [c5, Machine.upd_other _ _ _ hr, hr4]
  obtain ⟨c6, k6, e6, hk6, hw6, hm6, h6t, h6b, h6r, h6rr, h6rm, h6o⟩ : ∃ c6 k6, Exec P W
      ztgbo c5 c6 k6
      ∧ k6 ≤ 4 ∧ WordsBounded W c6 ∧ c6.nmem = c5.nmem ∧ c6.nreg 130841 = ztgkn % g.k' ∧
      c6.nreg 130842 = ztgkn / g.k' ∧
      (∀ r, r ≠ 130841 → r ≠ 130842 → c6.nreg r = c5.nreg r) ∧ c6.rreg = c5.rreg ∧
      c6.rmem = c5.rmem ∧ c6.output = c5.output := by
    by_cases hp : c5.nreg 130841 < c5.nreg 130015
    · rw [h5t, h5r _ by_omega, hk'] at hp
      refine ⟨c5, 0 + 1, .ifLtN_true by_grind (.skip e5.wb_right),
        by omega, e5.wb_right, rfl, ?_, ?_, by_omega, rfl, rfl, rfl⟩
      · grind
      grind
    · zumel
      rw [h5t, h5r _ by_omega, hk'] at hp'
      have e7 := Exec.constN (P := P) e5.wb_right 130841 0 by_omega
      have e8 := Exec.addN (P := P) e7.wb_right 130842 130842 130001 (by
        simp only [Machine.upd_other _ _ _ ztkxg,
          Machine.upd_other _ _ _ ztkxc]
        grind)
      refine ⟨_, ztzsk + 2, .ifLtN_false hp (.seq e7 (.seq e8 (.skip e8.wb_right))),
        by omega, e8.wb_right, rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
      · simp only [Machine.upd_other _ _ _ (show (130841 : ℕ) ≠ 130842 by omega),
          Machine.upd_same]
        grind
      · simp only [Machine.upd_same,
          Machine.upd_other _ _ _ ztkxg,
          Machine.upd_other _ _ _ ztkxc]
        grind
      · zueep
  have h6l : c6.nreg 130840 = j := by rw [h6r _ by_omega by_omega, h5r _ by_omega, h40']
  have h61 : c6.nreg 130001 = 1 := by rw [h6r _ by_omega by_omega, h5r _ by_omega, h1']
  have e9 := Exec.addN (P := P) hw6 130840 130840 130001 by_grind
  have hmfin : ({ c6 with nreg := upd c6.nreg 130840 (c6.nreg 130840 + c6.nreg 130001) } :
      Config).nmem = upd c3.nmem (g.base 36 + j) hl := by
    grind
  refine ⟨_, k3 + (k4 + (1 + zttql)), .seq e3 (.seq e4 (.seq e5 (.seq e6 e9))), by_omega,
    e9.wb_right, hf3.trans (hf4.trans ⟨fun r hr => ?_, h6rr, h6rm, h6o, fun a ha => ?_⟩), ?_, ?_, ?_,
    ?_, fun a h1 h2 h3 h4 => ?_⟩
  · unfold LVRG at hr
    simp only [Machine.upd_other _ _ _ (show r ≠ 130840 by omega)]
    rw [h6r _ by_omega by_omega, h5r _ by_omega, hr4]
  · grind
  · simp only [Machine.upd_same, h6l, h61]
  · simp only [Machine.upd_other _ _ _ (show (130841 : ℕ) ≠ 130840 by omega)]
    omega
  · simp only [Machine.upd_other _ _ _ (show (130842 : ℕ) ≠ 130840 by omega)]
    omega
  · rw [hmfin]
    zudfi
    · rw [Machine.upd_other _ _ _ by_omega, hm3, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_same]
    · rw [Machine.upd_other _ _ _ by_omega, hm3, Machine.upd_other _ _ _ by_omega,
        Machine.upd_same]
    · rw [Machine.upd_other _ _ _ by_omega, hm3, Machine.upd_same]
    · zumls
  · rw [hmfin, Machine.upd_other _ _ _ h4, hm3, Machine.upd_other _ _ _ h3,
      Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h1]
theorem lvS_exec {c : Config} (hw : WordsBounded W c) (hG : GR g c) (hk : 0 < g.k')
    (hkμ : g.k' ≤ g.μ) {rho : ℕ} (hrho : c.nreg 130836 = rho) (hrk : rho < g.k')
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W lvS c c' k ∧ k ≤ 22 * g.μ + 7 ∧ WordsBounded W c' ∧
      PFr StCRG zthrf c c' ∧ c'.nreg 130838 = g.k' - 1 - rho ∧
      ∀ l, l < g.μ → LvOK g c'.nmem (g.k' - 1 - rho) l := by
  zuuv
  set cs := g.k' - 1 - rho with hcs
  have hc : cs < g.k' := by_omega
  unfold lvS
  obtain ⟨c1, k1, e1, hk1, hw1, h39, h38, h40, h41, h42, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.subN 130839 130015 130001, .subN 130838 130839 130836, .constN 130840 0,
        .copyN 130841 130838, .constN 130842 0]) c c1 k1 ∧ k1 = 5 ∧ WordsBounded W c1 ∧
      c1.nreg 130839 = g.k' - 1 ∧ c1.nreg 130838 = cs ∧ c1.nreg 130840 = 0 ∧
      c1.nreg 130841 = ztsql % g.k' ∧ c1.nreg 130842 = ztsql / g.k' ∧
      PFr StCRG zthrf c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, by_omega, ?_, ?_, ?_, ?_, ?_, ztrg⟩
    · config_simp; rw [hG.rk', hG.one]
    · config_simp; rw [hG.rk', hG.one, hrho]
    · config_simp
    · config_simp; rw [hG.rk', hG.one, hrho, Nat.mod_eq_of_lt hc]
    · config_simp; rw [Nat.div_eq_of_lt hc]
    · zucad
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hG1 := hG.frame (fun r hr => hf1.1 r ztdcm)
  obtain ⟨c', k, e, hk', hw', hi', hn', h41', h42', h39', h38', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130840) (rn := 130011) (body := lvBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130840 = j ∧ c'.nreg 130011 = g.μ ∧
      c'.nreg 130841 = ztcag % g.k' ∧ c'.nreg 130842 = ztcag / g.k' ∧
      c'.nreg 130839 = g.k' - 1 ∧ c'.nreg 130838 = cs ∧ PFr StCRG zthrf c c' ∧
      ∀ l, l < j → LvOK g c'.nmem cs l)
    g.μ 20 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, ht2, hb2, h392, h382, hf2, hm2⟩ => by
      have hG2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      obtain ⟨c3, k3, e3, hk3, hw3, hf3, h40', h41', h42', hok, hkeep⟩ :=
        lvBody_exec (P := P) hw2 hG2 hk hkμ hj hc hi2 ht2 hb2 h392 hW
      refine ⟨c3, k3, e3, hk3, hw3, h40', by zunnx; omega,
        h41', h42', by zunnx; omega,
        by zunnx; omega,
        hf2.trans (hf3.mono (fun r h => by simp only [LVRG, StCRG] at h ⊢; omega) ztjvm),
        fun l hl => ?_⟩
      rcases Nat.lt_or_ge l j with h | h
      · zudgx
        have b38 := g.base_eq 38
        obtain ⟨o1, o2, o3, o4⟩ := hm2 l h
        zudfi
        · zunbd; exact o1
        · zunbd; exact o2
        · zunbd; exact o3
        · zunbd; exact o4
      grind)
    (j₀ := 0) ⟨hw1, h40, hG1.rμ, h41, h42, h39, h38, hf1, fun l hl => by_omega⟩ ztbg
  exact ⟨c', k1 + k, .seq e1 e, by_omega, hw', hf', h38', hm'⟩
end proofs
def stageC : Stmt := .seq halfS (.seq powS (.seq resS (.seq rcS (.seq argS lvS))))

/-- The memory written by stage C. -/
def CMem (g : GV) (a : ℕ) : Prop := g.base 33 ≤ a ∧ a < g.base 41
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **Stage C.** -/
theorem stageC_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hk : 0 < g.k') (hkμ : g.k' ≤ g.μ) {lev : ℕ → ℕ}
    (hlev : ∀ v, v < g.μ → c.nmem ztjc = lev v) (hlt : ∀ v, v < g.μ → lev v < g.μ)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageC c c' k ∧ k ≤ 80 * g.μ + 6 * g.L + 60 ∧ WordsBounded W c' ∧
      PFr StCRG zteme c c' ∧
      (∀ w, w ≤ g.μ → c'.nmem zthxm = w / 2) ∧
      (∀ j, j < g.L → c'.nmem ztlpe = 2 ^ j) ∧
      ∃ ρ, ρ < g.k' ∧ (∀ l, l < g.μ → LvOK g c'.nmem ztdom l) ∧
        ∀ r, r < g.k' → cntBelow ztdhh g.μ ρ ≤
          cntBelow ztdhh g.μ r := by
  zuegq
  have b3 := g.base_eq 3; have b33 := g.base_eq 33; have b34 := g.base_eq 34
  have b35 := g.base_eq 35; have b39 := g.base_eq 39; have b40 := g.base_eq 40
  have b41 := g.base_eq 41
  have fr : ∀ {Am : ℕ → Prop} {c1 c2 : Config}, PFr StCRG Am c1 c2 → (∀ a, Am a → CMem g a) →
      PFr StCRG zteme c1 c2 := fun h hA => h.mono ztng hA
  have gr : ∀ {c1 : Config}, PFr StCRG zteme c c1 → GR g c1 := fun h =>
    hG.frame (fun r hr => h.1 r ztdcm)
  unfold stageC
  obtain ⟨c1, k1, e1, hk1, hw1, hf1, hh1⟩ := halfS_exec (P := P) hw hG hW
  have f1 : PFr StCRG zteme c c1 := fr hf1 ztdns
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hp2⟩ := powS_exec (P := P) hw1 (gr f1) hW
  have f2 : PFr StCRG zteme c c2 := f1.trans (fr hf2 ztdns)
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hr3⟩ := resS_exec (P := P) hw2 (gr f2) hk hkμ hW
  have f3 : PFr StCRG zteme c c3 := f2.trans (fr hf3 ztdns)
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hc4⟩ := rcS_exec (P := P) hw3 (gr f3) hk hkμ
    (lev := lev) (fun v hv => by rw [f3.2.2.2.2 _ ztggk]; grind) hlt
    hr3 hW
  have f4 : PFr StCRG zteme c c4 := f3.trans (fr hf4 ztdns)
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, hρ5, hmin5⟩ := argS_exec (P := P) hw4 (gr f4) hk hkμ hc4
    (fun r hr => cntBelow_le _ _ _) hW
  have f5 : PFr StCRG zteme c c5 := f4.trans (fr hf5 (fun a h => h.elim))
  obtain ⟨c6, k6, e6, hk6, hw6, hf6, -, hlv6⟩ := lvS_exec (P := P) hw5 (gr f5) hk hkμ rfl hρ5 hW
  have f6 : PFr StCRG zteme c c6 := f5.trans (fr hf6 (fun a h => by
    unfold LvMem at h; unfold CMem; omega))
  have k16 : ∀ a, ¬ LvMem g a → ¬ (g.base 33 ≤ a ∧ a < g.base 33 + g.μ) →
      ¬ (g.base 34 ≤ a ∧ a < g.base 34 + g.k') → c6.nmem a = c2.nmem a := fun a h6 h3 h4 => by
    rw [hf6.2.2.2.2 a h6, hf5.2.2.2.2 a id, hf4.2.2.2.2 a h4, hf3.2.2.2.2 a h3]
  refine ⟨c6, k1 + ztrd,
    .seq e1 ztvb, by_omega, hw6, f6,
    fun w hw' => ?_, fun j hj => ?_, c5.nreg 130836, hρ5, hlv6, hmin5⟩
  · rw [k16 _ ztqgb by_omega by_omega,
      hf2.2.2.2.2 _ by_omega]; grind
  · rw [k16 _ ztqgb by_omega by_omega]; grind
end proofs
def StDRG (r : ℕ) : Prop := ztbxr ∨ (130800 ≤ r ∧ r ≤ 130805) ∨
  (130850 ≤ r ∧ r ≤ 130899)

/-- The block of a vertex, `μ` for the light levels. -/
def blkOf (μ : ℕ) (lev hl blk : ℕ → ℕ) (v : ℕ) : ℕ := if hl ztkag = 1 then μ else blk ztkag

/-- One vertex of the block count. -/
def bcBody : Stmt := .seq (block [.addN 130851 130033 130850, .loadN 130852 130851,
  .addN 130851 130066 130852, .loadN 130853 130851])
  (.seq (.ifLtN 130853 130001 (block [.addN 130851 130065 130852, .loadN 130854 130851,
    .addN 130851 130072 130854, .loadN 130855 130851, .addN 130855 130855 130001,
    .storeN 130851 130855]) .skip)
  (.instr (.addN 130850 130850 130001)))

/-- **The block sizes.** -/
def bcS : Stmt := .seq (fillWith 130072 130011 130009)
  (.seq (.instr (.constN 130850 0)) (.whileLtN 130850 130011 bcBody))

/-- The registers of the count step. -/
def BCRG (r : ℕ) : Prop := 130850 ≤ r ∧ r ≤ 130855

/-- The number of elements below `n` with value below `j`. -/
noncomputable def cntLt (f : ℕ → ℕ) (n j : ℕ) : ℕ := ((Finset.range n).filter (fun v => f v < j)).card
variable (f : ℕ → ℕ) (n j : ℕ)
theorem sum_cntBelow :
    ∑ i ∈ Finset.range j, cntBelow f n i = cntLt f n j := by
  induction j with
  | zero => zuocu
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    unfold cntLt cntBelow
    rw [← Finset.card_union_of_disjoint]
    · zucr
      grind
    · zuzt
      grind
theorem cntLt_le : cntLt f n j ≤ n := by
  unfold cntLt; grind

/-- One block of the prefix sums. -/
def pfxBody : Stmt := block [.addN 130858 130072 130856, .loadN 130859 130858,
  .storeN 130858 130857, .addN 130857 130857 130859, .addN 130856 130856 130001]

/-- **The starts of the blocks** (exclusive prefix sums in place). -/
def pfxS : Stmt := .seq ztkqu
  (.whileLtN 130856 130011 pfxBody)
section proofs
variable {P : Polygon} {W : ℕ}
variable {g : GV} {c : Config}
set_option maxHeartbeats 4000000 in
theorem bcS_exec (hw : WordsBounded W c) (hG : GR g c)
    {lev hl blk : ℕ → ℕ} (hlev : ∀ v, v < g.μ → c.nmem ztjc = lev v)
    (hlt : ∀ v, v < g.μ → lev v < g.μ) (hhl : ∀ l, l < g.μ → c.nmem ztcnm = hl l)
    (hhl1 : ∀ l, l < g.μ → hl l ≤ 1) (hblk : ∀ l, l < g.μ → c.nmem ztcdg = blk l)
    (hblt : ∀ l, l < g.μ → hl l ≠ 1 → blk l < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W bcS c c' k ∧ k ≤ 20 * g.μ + 12 ∧ WordsBounded W c' ∧
      PFr StDRG ztcde c c' ∧
      ∀ b, b < g.μ → c'.nmem ztys = cntBelow ztbsf g.μ b := by
  have hU := g.U_ge; have hE := g.END_eq; have b3 := g.base_eq 3; have b35 := g.base_eq 35
  have b36 := g.base_eq 36; have b42 := g.base_eq 42
  unfold bcS
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hz1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 42 by_omega) hG.rμ hG.zero ztpc ztpc
    ztpc by_omega by_omega
  have e2 := Exec.constN (P := P) hw1 130850 0 by_omega
  set c2 := { c1 with nreg := upd c1.nreg 130850 0 } with hc2
  have f2 : PFr StDRG ztcde c c2 :=
    (hf1.mono zthxh by_omega).trans
      ⟨fun r hr => by simp only [c2, Machine.upd_other _ _ _ (show r ≠ 130850 by
        unfold StDRG at hr; omega)], rfl, rfl, rfl, by_simp_all⟩
  have hG2 := hG.frame ztyqr
  zucet
  obtain ⟨c', k, e, hk', hw', hi', hn', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130850) (rn := 130011) (body := bcBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130850 = j ∧ c'.nreg 130011 = g.μ ∧
      PFr StDRG Am c c' ∧
      ∀ b, b < g.μ → c'.nmem ztys = cntBelow ztbsf j b)
    g.μ 13 zthd
    (fun j c3 hj ⟨hw3, hi3, hn3, hf3, hm3⟩ => by
      have hG3 := hG.frame (fun r hr => hf3.1 r (by
        unfold GRReg at hr; unfold StDRG; omega))
      have r33 := hG3.rbase 3 by_omega; have r65 := hG3.rbase 35 by_omega
      have r66 := hG3.rbase 36 by_omega; have r72 := hG3.rbase 42 by_omega
      zumfp
      zufvi
      have ml : ztzpj := by rw [hf3.2.2.2.2 _ by_omega]; grind
      have mh : c3.nmem (g.base 36 + lev j) = hl zteak := by
        zubbh
      have mb : c3.nmem ztqoo = blk zteak := by
        zubbh
      have hcle : ∀ b, cntBelow ztbsf j b ≤ j := fun b => cntBelow_le _ _ _
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, h52, h53, h50, h4r⟩ : ∃ c4 k4, Exec P W
          (block [.addN 130851 130033 130850, .loadN 130852 130851,
            .addN 130851 130066 130852, .loadN 130853 130851]) c3 c4 k4 ∧ k4 = 4 ∧
          WordsBounded W c4 ∧ PFr BCRG ztbvx c3 c4 ∧ c4.nreg 130852 = lev j ∧
          c4.nreg 130853 = hl zteak ∧ c4.nreg 130850 = j ∧
          (∀ r, ¬ BCRG r → c4.nreg r = c3.nreg r) := by
        exec_block
        · grind
        · config_simp; rw [r66, r33, hi3, ml]; omega
        · refine ⟨rfl, by omega, ⟨fun r hr => ?_, rfl, rfl, rfl, by grind⟩, ?_, ?_, ?_,
            fun r hr => ?_⟩
          · simp only; unfold BCRG at hr
            repeat (rw [Machine.upd_other _ _ _ (by omega)])
          · config_simp; rw [r33, hi3, ml]
          · config_simp; zunlp
          · config_simp; omega
          · simp only; unfold BCRG at hr
            repeat (rw [Machine.upd_other _ _ _ (by omega)])
      have r1' : ztizd := by zunny; exact r1
      obtain ⟨c5, k5, e5, hk5, hw5, hf5, hm5, h50'⟩ : ∃ c5 k5, Exec P W
          (.ifLtN 130853 130001 (block [.addN 130851 130065 130852, .loadN 130854 130851,
            .addN 130851 130072 130854, .loadN 130855 130851, .addN 130855 130855 130001,
            .storeN 130851 130855]) .skip) c4 c5 k5 ∧ k5 ≤ 7 ∧ WordsBounded W c5 ∧
          PFr BCRG Am c4 c5 ∧
          (∀ b, b < g.μ → c5.nmem ztys = cntBelow ztbsf ztl b) ∧
          c5.nreg 130850 = j := by
        by_cases hp : c4.nreg 130853 < c4.nreg 130001
        · zuiij
          have hh : hl zteak ≠ 1 := by_omega
          have hbj : blk _ < g.μ := hblt _ hlj hh
          have hbo : blkOf g.μ lev hl blk j = blk zteak := by unfold blkOf; grind
          have r65' : c4.nreg 130065 = g.base 35 := by zunny; omega
          have r72' : c4.nreg 130072 = g.base 42 := by zunny; omega
          have mb' : c4.nmem ztqoo = blk zteak := by rw [hf4.2.2.2.2 _ id]; exact mb
          have mc : c4.nmem (g.base 42 + blk zteak) =
              cntBelow ztbsf j ztbafp := by
            zuijs
          have hcl := hcle ztbafp
          obtain ⟨c6, k6, e6, hk6, hw6, hf6, hm6, h50''⟩ : ∃ c6 k6, Exec P W
              (block [.addN 130851 130065 130852, .loadN 130854 130851,
                .addN 130851 130072 130854, .loadN 130855 130851, .addN 130855 130855 130001,
                .storeN 130851 130855]) c4 c6 k6 ∧ k6 = 6 ∧ WordsBounded W c6 ∧
              PFr BCRG Am c4 c6 ∧
              c6.nmem = upd c4.nmem _
                _ ∧
              c6.nreg 130850 = j := by
            exec_block
            · omega
            · config_simp; rw [r72', r65', h52, mb']; omega
            · config_simp; zunil; omega
            · refine ⟨rfl, by omega, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ?_, ?_⟩
              · simp only; unfold BCRG at hr
                repeat (rw [Machine.upd_other _ _ _ (by omega)])
              · config_simp; rw [r72', r65', h52, mb', Machine.upd_other _ _ _ (by
                  omega)]
              · config_simp; zunil
              · config_simp; omega
          refine ⟨c6, k6 + 1, .ifLtN_true by_omega e6, by_omega, hw6, hf6,
            fun b hb => ?_, h50''⟩
          rw [hm6, Machine.upd_apply, cntBelow_succ, hbo]
          zudlv
          · grind
          · omega
          · omega
          · zuijs
        · zuiij
          have hh : hl zteak = 1 := by_grind
          have hbo : blkOf g.μ lev hl blk j = g.μ := by unfold blkOf; grind
          refine ⟨c4, 0 + 2, .ifLtN_false by_omega ztpsa, by_omega,
            hw4, PFr.refl c4, fun b hb => ?_, h50⟩
          rw [cntBelow_succ, hbo, ite_eq_right by_omega, Nat.add_zero, hf4.2.2.2.2 _ id]
          grind
      have e7 := Exec.addN (P := P) hw5 130850 130850 130001 (by
        zunrn; omega)
      have hf7 : PFr BCRG Am c5
          { c5 with nreg := upd c5.nreg 130850 (c5.nreg 130850 + c5.nreg 130001) } :=
          ⟨fun r hr => by
            simp only [Machine.upd_other _ _ _ (show r ≠ 130850 by
              unfold BCRG at hr; omega)], rfl, rfl, rfl, by_grind⟩
      refine ⟨_, k4 + zttqk, .seq e4 ztspz, by_omega, e7.wb_right, ?_, ?_,
        hf3.trans (((hf4.mono by_grind by_grind).trans (hf5.trans hf7)).mono
          (fun r h => by simp only [BCRG, StDRG] at h ⊢; omega) by_omega), hm5⟩
      · zuvz
        zunrn
      · simp only [Machine.upd_other _ _ _ (show (130011 : ℕ) ≠ 130850 by omega)]
        rw [hf5.1 _ ztcuh, hf4.1 _ ztcuh]; omega)
    (j₀ := 0) ⟨e2.wb_right, by_rfl, hG2.rμ, f2, fun b hb => by
      rw [show c2.nmem = c1.nmem from rfl, hz1 b hb]; rfl⟩ (Nat.zero_le _)
  exact ztedp
theorem pfxS_exec (hw : WordsBounded W c) (hG : GR g c) {f : ℕ → ℕ}
    (hcnt : ∀ b, b < g.μ → c.nmem ztys = cntBelow f g.μ b) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W pfxS c c' k ∧ k ≤ 7 * g.μ + 4 ∧ WordsBounded W c' ∧
      PFr StDRG ztcde c c' ∧
      ∀ b, b < g.μ → c'.nmem ztys = cntLt f g.μ b := by
  have hU := g.U_ge; have hE := g.END_eq; have b42 := g.base_eq 42
  unfold pfxS
  zucet
  obtain ⟨c1, k1, e1, hk1, hw1, h56, h57, hf1, hm1⟩ : ∃ c1 k1, Exec P W
      ztkqu c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧
      c1.nreg 130856 = 0 ∧ c1.nreg 130857 = 0 ∧ PFr StDRG Am c c1 ∧ c1.nmem = c.nmem := by
    exec_block
    all_goals try omega
    refine ⟨rfl, by_omega, by config_simp, by config_simp, ⟨fun r hr => ?_, rfl, rfl, rfl,
      by simp_all⟩, rfl⟩
    zujph
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hG1 := hG.frame (fun r hr => hf1.1 r ztun)
  obtain ⟨c', k, e, hk', hw', hi', hn', h57', hf', hm', -⟩ := forN (P := P) (W := W)
    (ri := 130856) (rn := 130011) (body := pfxBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130856 = j ∧ c'.nreg 130011 = g.μ ∧
      c'.nreg 130857 = cntLt f g.μ j ∧ PFr StDRG Am c c' ∧
      (∀ b, b < j → c'.nmem ztys = cntLt f g.μ b) ∧
      (∀ b, j ≤ b → b < g.μ → c'.nmem ztys = cntBelow f g.μ b))
    g.μ 5 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, ha2, hf2, hlo2, hhi2⟩ => by
      have hG2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StDRG; omega))
      zukiq
      zudqb
      have mj := hhi2 j le_rfl hj
      have hsum : cntLt f g.μ ztl = cntLt f g.μ j + cntBelow f g.μ j := by
        zugxz
      have hle := cntLt_le f g.μ ztl
      unfold pfxBody
      exec_block
      · grind
      · config_simp; grind
      · config_simp; omega
      · refine ⟨le_refl _, by omega, by simp_all, by simp_all,
          by simp_all, hf2.trans ⟨fun r hr => ?_, rfl, rfl, rfl,
          fun a ha => ?_⟩, fun b hb => ?_, fun b hb1 hb2 => ?_⟩
        · simp only; simp only [StDRG] at hr
          repeat (rw [Machine.upd_other _ _ _ (by omega)])
        · config_simp; rw [r72, hi2, Machine.upd_other _ _ _ by_omega]
        · config_simp; rw [r72, hi2, ha2, Machine.upd_apply]
          grind
        · config_simp; rw [r72, hi2, Machine.upd_other _ _ _ by_omega]
          grind)
    (j₀ := 0) ⟨hw1, h56, hG1.rμ, by rw [h57]; zuocu, hf1, fun b hb => by_omega,
      fun b _ hb => by_simp_all⟩
    ztbg
  exact ztcxq
end proofs
noncomputable def cB (μ : ℕ) (bo key : ℕ → ℕ) (j b : ℕ) : ℕ :=
  ((Finset.range μ).filter (fun w => bo w = b ∧ key w < j)).card

/-- The rank of `v` in its block. -/
noncomputable def rk (μ : ℕ) (bo key : ℕ → ℕ) (v : ℕ) : ℕ :=
  ((Finset.range μ).filter (fun w => bo w = bo v ∧ key w < key v)).card

/-- The final position of an item. -/
noncomputable def plPos (μ : ℕ) (bo key : ℕ → ℕ) (v : ℕ) : ℕ := cntLt bo μ ztepn + rk μ bo key v
variable (f : ℕ → ℕ) {v : ℕ} {a1 a2 a3 : ℕ} {m0 m : ℕ → ℕ}
theorem cntLt_succ (n b : ℕ) : cntLt f n ztds = cntLt f n b + cntBelow f n b := by
  zugxz
theorem cntLt_mono (n : ℕ) {b b' : ℕ} (h : b ≤ b') : cntLt f n b ≤ cntLt f n b' := by
  unfold cntLt; apply Finset.card_le_card; grind
variable {μ : ℕ} {bo key : ℕ → ℕ}
theorem rk_lt (hv : v < μ) : rk μ bo key v < cntBelow bo μ ztepn := by
  unfold rk cntBelow
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (fun w hw => by
    simp_all)]
  exact ⟨v, by_simp_all, by_simp⟩
theorem rk_lt_rk {v w : ℕ} (hw : w < μ) (hb : bo w = bo v) (hk : key w < key v) :
    rk μ bo key w < rk μ bo key v := by
  zumui
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (fun x hx => by
    grind)]
  exact ⟨w, by_simp_all, by_simp⟩
theorem rk_eq_cB : rk μ bo key v = cB μ bo key ztjzk ztepn := rfl
theorem plPos_ge (v : ℕ) : cntLt bo μ ztepn ≤ plPos μ bo key v := Nat.le_add_right _ _
theorem plPos_lt (hv : v < μ) : plPos μ bo key v < cntLt bo μ ztlgh := by
  have := rk_lt (bo := bo) (key := key) hv; unfold plPos; rw [cntLt_succ]; omega

/-- **The positions are distinct.** -/
theorem plPos_inj (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w) {v w : ℕ} (hv : v < μ)
    (hw : w < μ) (h : plPos μ bo key v = plPos μ bo key w) : v = w := by
  rcases lt_trichotomy ztepn ztvfq with hb | hb | hb
  · have h1 := plPos_lt (bo := bo) (key := key) hv; have h2 := plPos_ge (μ := μ) (bo := bo) (key := key) w
    have h3 := cntLt_mono bo μ (show bo v + 1 ≤ bo w by omega); omega
  · rcases lt_trichotomy ztjzk (key w) with hk | hk | hk
    · have := rk_lt_rk (bo := bo) (key := key) hv hb hk; unfold plPos at h; simp_all
    · grind
    · have := rk_lt_rk (bo := bo) (key := key) hw hb.symm hk; unfold plPos at h; simp_all
  · have h1 := plPos_lt (bo := bo) (key := key) hw; have h2 := plPos_ge (μ := μ) (bo := bo) (key := key) v
    have h3 := cntLt_mono bo μ (show bo w + 1 ≤ bo v by omega); omega

/-- **The positions are in key order** inside a block. -/
theorem key_le_of_plPos {v w : ℕ} (hw : w < μ) (hb : bo w = bo v)
    (h : plPos μ bo key v ≤ plPos μ bo key w) : key v ≤ key w := by
  by_contra hk
  have := rk_lt_rk (bo := bo) (key := key) hw hb by_omega; unfold plPos at h; grind

/-- **The block `b` fills its segment.** -/
theorem exists_plPos (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w) {b i : ℕ}
    (h1 : cntLt bo μ b ≤ i) (h2 : i < cntLt bo μ ztds) :
    ∃ v, v < μ ∧ bo v = b ∧ plPos μ bo key v = i := by
  set T := (Finset.range μ).filter zthhe with hT
  have hsub : T.image ztruk ⊆ Finset.Ico ztrnr ztzle := by
    zuh
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    simp only [hT, Finset.mem_filter, Finset.mem_range] at hv
    have := plPos_lt (bo := bo) (key := key) hv.1; have := plPos_ge (μ := μ) (bo := bo) (key := key) v
    grind
  have hcard : (T.image ztruk).card = cntBelow bo μ b := by
    rw [Finset.card_image_of_injOn (fun v hv w hw h => by
      simp only [hT, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hv hw
      exact plPos_inj hinj hv.1 hw.1 h)]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Nat.card_Ico, cntLt_succ]; omega)
  have hi : i ∈ Finset.Ico ztrnr ztzle := by_simp_all
  grind

/-- One step of the scan: the item of key `j`. -/
theorem cB_succ_of (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w) {v j b : ℕ}
    (hv : v < μ) (hk : key v = j) :
    cB μ bo key ztl b = cB μ bo key j b + if bo v = b then 1 else 0 := by
  unfold cB
  split_ifs with hb
  · rw [← Finset.card_insert_of_notMem (s := (Finset.range μ).filter _) (a := v) by_simp_all]
    apply congrArg Finset.card; grind
  · refine (congrArg Finset.card ?_).trans (Nat.add_zero _).symm; grind

/-- One step of the scan without an item of block `b`. -/
theorem cB_succ_none {j b : ℕ} (h : ∀ w, w < μ → key w = j → bo w ≠ b) :
    cB μ bo key ztl b = cB μ bo key j b := by
  unfold cB; apply congrArg Finset.card; grind
theorem cB_full {n b : ℕ} (h : ∀ w, w < μ → key w < n) : cB μ bo key n b = cntBelow bo μ b := by
  unfold cB cntBelow; apply congrArg Finset.card; grind
theorem plPos_lt_μ (hv : v < μ) (_hb : bo v < μ) : plPos μ bo key v < μ := by
  have := plPos_lt (bo := bo) (key := key) hv; have := cntLt_le bo μ ztlgh; omega

/-- **The invariant of the placement scan** (counters at `a1`, items at `a2`, positions at
`a3`; `m0` the memory before the scan). -/
structure PlInv (μ : ℕ) (bo key : ℕ → ℕ) (a1 a2 a3 : ℕ) (m0 : ℕ → ℕ) (j : ℕ) (m : ℕ → ℕ) :
    Prop where
  cnt : ∀ b, b < μ → m ztnqy = cntLt bo μ b + cB μ bo key j b
  pos : ∀ v, v < μ → m ztnrb = if bo v < μ ∧ key v < j then plPos μ bo key v else m0 ztnrb
  act : ∀ v, v < μ → bo v < μ → key v < j → m ztnra = v
theorem PlInv.zero {m : ℕ → ℕ} (h : ∀ b, b < μ → m ztnqy = cntLt bo μ b) :
    PlInv μ bo key a1 a2 a3 m 0 m :=
  ⟨fun b hb => by rw [h b hb]; simp [cB], fun v _ => by_simp, fun v _ _ h => by_omega⟩

/-- **A placing step.** -/
theorem PlInv.step (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w) {a1 a2 a3 : ℕ}
    (h12 : a1 + μ ≤ a2) (h23 : a2 + μ ≤ a3) {m0 m : ℕ → ℕ} {j : ℕ}
    (hI : PlInv μ bo key a1 a2 a3 m0 j m) {v : ℕ} (hv : v < μ) (hk : key v = j) (hb : bo v < μ) :
    PlInv μ bo key a1 a2 a3 m0 ztl (upd (upd (upd m ztnra v) ztnrb
      ztglh) (a1 + bo v) (plPos μ bo key v + 1)) := by
  have hq := plPos_lt_μ (key := key) hv hb
  have hqe : plPos μ bo key v = cntLt bo μ ztepn + cB μ bo key j ztepn := by
    unfold plPos; rw [rk_eq_cB, hk]
  refine ⟨fun b hb' => ?_, fun w hw => ?_, fun w hw hbw hkw => ?_⟩
  · rw [cB_succ_of hinj hv hk]
    by_cases hbb : bo v = b
    · subst hbb; rw [Machine.upd_same, ite_eq_left rfl, hqe]; omega
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, hI.cnt b hb', ite_eq_right hbb, Nat.add_zero]
  · zubc
    zujub
    · subst hwv; rw [Machine.upd_same, ite_eq_left ztuha]
    · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega, hI.pos w hw]
      grind
  · have hqw := plPos_lt_μ (key := key) hw hbw
    zucw
    zujub
    · subst hwv; simp
    · have hne : plPos μ bo key w ≠ plPos μ bo key v := fun h => hwv (plPos_inj hinj hw hv h)
      zubc
      exact hI.act w hw hbw (by
        grind)

/-- **A step without placement.** -/
theorem PlInv.skip {j : ℕ}
    (hI : PlInv μ bo key a1 a2 a3 m0 j m) (hn : ∀ w, w < μ → key w = j → ¬ bo w < μ) :
    PlInv μ bo key a1 a2 a3 m0 ztl m := by
  refine ⟨fun b hb => ?_, fun w hw => ?_, fun w hw hbw hkw => ?_⟩
  · rw [cB_succ_none (fun w hw hk h => hn w hw hk by_omega)]; exact hI.cnt b hb
  · rw [hI.pos w hw]
    grind
  · exact hI.act w hw hbw (by
      grind)

/-- The end of the scan. -/
theorem PlInv.full {n : ℕ}
    (hI : PlInv μ bo key a1 a2 a3 m0 n m) (h : ∀ w, w < μ → key w < n) {b : ℕ} (hb : b < μ) :
    m ztnqy = cntLt bo μ ztds := by
  rw [hI.cnt b hb, cB_full h, cntLt_succ]
def placeB : Stmt := block [.addN 130861 130065 130865, .loadN 130867 130861,
  .addN 130861 130072 130867, .loadN 130868 130861, .addN 130869 130073 130868,
  .storeN 130869 130863, .addN 130869 130074 130863, .storeN 130869 130868,
  .addN 130868 130868 130001, .storeN 130861 130868]

/-- The light test. -/
def lightB : Stmt := .seq (block [.addN 130861 130033 130863, .loadN 130865 130861,
  .addN 130861 130066 130865, .loadN 130866 130861]) (.ifLtN 130866 130001 placeB .skip)

/-- One preorder position. -/
def placeBody : Stmt := .seq (block [.addN 130861 130062 130860, .loadN 130862 130861,
  .addN 130861 130023 130862, .loadN 130863 130861, .addN 130861 130030 130863,
  .loadN 130864 130861])
  (.seq ztjcx
    (.instr (.addN 130860 130860 130001)))

/-- **The placement** of the items in preorder. -/
def placeS : Stmt := .seq (.instr (.constN 130860 0)) (.whileLtN 130860 130014 placeBody)

/-- The registers of the placement. -/
def PLRG (r : ℕ) : Prop := 130860 ≤ r ∧ r ≤ 130869

/-- The memory written by the placement. -/
def PlMem (g : GV) (a : ℕ) : Prop := g.base 42 ≤ a ∧ a < g.base 45
section proofs
variable {P : Polygon} {W : ℕ}
variable {g : GV} {c : Config}
set_option maxHeartbeats 2000000 in
theorem placeB_exec (hw : WordsBounded W c) (hG : GR g c)
    {v l b q : ℕ} (h63 : c.nreg 130863 = v) (hv : v < g.μ) (h65 : c.nreg 130865 = l)
    (hl : l < g.μ) (hb : c.nmem ztcdg = b) (hbμ : b < g.μ)
    (hq : c.nmem ztys = q) (hqμ : q < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W placeB c c' k ∧ k = 10 ∧ WordsBounded W c' ∧ PFr PLRG ztens c c' ∧
      c'.nreg 130860 = c.nreg 130860 ∧
      c'.nmem = upd ztzoc
        ztys ztfo := by
  have hU := g.U_ge; have hE := g.END_eq; have b35 := g.base_eq 35; have b42 := g.base_eq 42
  have b43 := g.base_eq 43; have b44 := g.base_eq 44; have b45 := g.base_eq 45
  have r65 := hG.rbase 35 by_omega; have r72 := hG.rbase 42 by_omega
  have r73 := hG.rbase 43 by_omega; have r74 := hG.rbase 44 by_omega
  zumfo
  unfold placeB
  exec_block
  · grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · config_simp; grind
  · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, by config_simp, ?_⟩
    · zufcx
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    · config_simp; unfold PlMem at ha
      rw [r74, r73, r72, r65, h65, hb, hq, h63]
      rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
    simp_all
set_option maxHeartbeats 2000000 in
theorem lightB_exec (hw : WordsBounded W c) (hG : GR g c)
    {v l h b q : ℕ} (h63 : c.nreg 130863 = v) (hv : v < g.μ)
    (hlev : c.nmem ztjc = l) (hl : l < g.μ) (hh : c.nmem ztcnm = h)
    (hh1 : h ≤ 1) (hb : c.nmem ztcdg = b) (hbμ : h ≠ 1 → b < g.μ)
    (hq : c.nmem ztys = q) (hqμ : h ≠ 1 → q < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W lightB c c' k ∧ k ≤ 16 ∧ WordsBounded W c' ∧ PFr PLRG ztens c c' ∧
      c'.nreg 130860 = c.nreg 130860 ∧
      c'.nmem = if h ≠ 1 then upd ztzoc
        ztys ztfo else c.nmem := by
  zucma
  have r33 := hG.rbase 3 by_omega; have r66 := hG.rbase 36 by_omega
  zumfo
  obtain ⟨c1, k1, e1, hk1, hw1, hf1, h65, h66, h63', h60, hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130861 130033 130863, .loadN 130865 130861,
        .addN 130861 130066 130865, .loadN 130866 130861]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧
      PFr PLRG ztens c c1 ∧ c1.nreg 130865 = l ∧ c1.nreg 130866 = h ∧
      c1.nreg 130863 = v ∧ c1.nreg 130860 = c.nreg 130860 ∧ c1.nmem = c.nmem := by
    exec_block
    · grind
    · config_simp; grind
    · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, ?_, ?_, ?_,
        by config_simp, rfl⟩
      · simp only; unfold PLRG at hr
        repeat (rw [Machine.upd_other _ _ _ (by omega)])
      · simp_all
      · simp_all
      simp_all
  zuiwa
  have r1' := hG1.one
  unfold lightB
  by_cases hp : h < 1
  · have hne : h ≠ 1 := by_omega
    obtain ⟨c2, k2, e2, hk2, hw2, hf2, h60', hm2⟩ := placeB_exec (P := P) hw1 hG1 h63' hv h65 hl
      by_simp_all (hbμ hne) by_simp_all (hqμ hne) hW
    refine ⟨c2, k1 + ztcvw, .seq e1 (.ifLtN_true by_omega e2), by_omega,
      hw2, hf1.trans hf2, by_omega, ?_⟩
    simp_all
  · have he : h = 1 := by_omega
    refine ⟨c1, k1 + ztdeu, .seq e1 (.ifLtN_false by_omega ztdbq),
      by omega, hw1, hf1, h60, ?_⟩
    simp_all
set_option maxHeartbeats 2000000 in
/-- **One placement step.** -/
theorem placeBody_exec (hw : WordsBounded W c) (hG : GR g c)
    {p gg v f l h b q : ℕ} (h60 : c.nreg 130860 = p) (hpN : p < g.N)
    (hinv : c.nmem ztlpb = gg) (hgW : g.bV + gg ≤ W)
    (hvert : c.nmem (g.bV + gg) = v) (hv : v < g.μ) (hfst : c.nmem ztbrk = f)
    (hlev : f = gg → c.nmem ztjc = l) (hl : f = gg → l < g.μ)
    (hh : f = gg → c.nmem ztcnm = h) (hh1 : f = gg → h ≤ 1)
    (hb : f = gg → c.nmem ztcdg = b) (hbμ : f = gg → h ≠ 1 → b < g.μ)
    (hq : f = gg → c.nmem ztys = q) (hqμ : f = gg → h ≠ 1 → q < g.μ)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W placeBody c c' k ∧ k ≤ 30 ∧ WordsBounded W c' ∧
      PFr PLRG ztens c c' ∧ c'.nreg 130860 = p + 1 ∧
      c'.nmem = if f = gg ∧ h ≠ 1 then upd (upd ztdpt
        ztczp q) (g.base 42 + b) (q + 1) else c.nmem := by
  have hU := g.U_ge; have hE := g.END_eq; have b32 := g.base_eq 32; have b0 := g.base_eq 0
  have hN : g.N ≤ g.U := by_omega
  have r62 := hG.rbase 32 by_omega; have r30 := hG.rbase 0 by_omega
  have r23 := hG.rV; have r1 := hG.one
  obtain ⟨c1, k1, e1, hk1, hw1, hf1, h62, h63, h64, h60', hm1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 130861 130062 130860, .loadN 130862 130861,
        .addN 130861 130023 130862, .loadN 130863 130861, .addN 130861 130030 130863,
        .loadN 130864 130861]) c c1 k1 ∧ k1 = 6 ∧ WordsBounded W c1 ∧
      PFr PLRG ztens c c1 ∧ c1.nreg 130862 = gg ∧ c1.nreg 130863 = v ∧
      c1.nreg 130864 = f ∧ c1.nreg 130860 = p ∧ c1.nmem = c.nmem := by
    exec_block
    · grind
    · simp_all
    · config_simp; rw [r30, r23, r62, h60, hinv, hvert]; omega
    · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, ?_, ?_, ?_, ?_, rfl⟩
      · zufcx
        repeat (rw [Machine.upd_other _ _ _ (by omega)])
      · simp_all
      · simp_all
      · simp_all
      simp_all
  zuiwa
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, h60'', hm2⟩ : ∃ c2 k2, Exec P W
      ztjcx c1 c2 k2 ∧ k2 ≤ 20 ∧
      WordsBounded W c2 ∧ PFr PLRG ztens c1 c2 ∧ c2.nreg 130860 = p ∧
      c2.nmem = if f = gg ∧ h ≠ 1 then upd (upd ztdpt
        ztczp q) (g.base 42 + b) (q + 1) else c.nmem := by
    by_cases h1 : f < gg
    · refine ⟨c1, 0 + 1, .ifLtN_true by_omega ztdbq, by_omega, hw1,
        PFr.refl c1, h60', ?_⟩
      grind
    by_cases h2 : gg < f
    · refine ⟨c1, ztbgo + 2, .ifLtN_false by_omega
        ztzrv, by_omega, hw1,
        PFr.refl c1, h60', ?_⟩
      grind
    have hfg : f = gg := by_omega
    obtain ⟨c3, k3, e3, hk3, hw3, hf3, h603, hm3⟩ := lightB_exec (P := P) hw1 hG1 h63 hv
      by_simp_all (hl hfg) by_simp_all (hh1 hfg)
      by_simp_all (hbμ hfg) by_simp_all (hqμ hfg) hW
    refine ⟨c3, (k3 + 2) + 2, .ifLtN_false by_omega
      (.ifLtN_false by_omega e3), by_omega, hw3, hf3,
      by omega, ?_⟩
    simp_all
  have r1' : zthoo := by
    rw [hf2.1 _ ztjra, hf1.1 _ ztjra]; exact r1
  have e3 := Exec.addN (P := P) hw2 130860 130860 130001 by_omega
  refine ⟨_, k1 + ztcvw, .seq e1 ztbpc, by_omega, e3.wb_right,
    (hf1.trans hf2).trans ztbtf, ?_, hm2⟩
  · simp only [Machine.upd_other _ _ _ (show r ≠ 130860 by unfold PLRG at hr; omega)]
  simp_all
set_option maxHeartbeats 4000000 in
/-- **The placement scan.** -/
theorem placeS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {inv vert first lev hl blk key : ℕ → ℕ}
    (hinv : ∀ p, p < g.N → c.nmem ztlpb = inv p)
    (hvW : ∀ p, p < g.N → g.bV + inv p < g.A0)
    (hvert : ∀ p, p < g.N → c.nmem (g.bV + inv p) = vert ztmlv)
    (hvlt : ∀ p, p < g.N → vert ztmlv < g.μ)
    (hfst : ∀ v, v < g.μ → c.nmem ztbrk = first v)
    (hlev : ∀ v, v < g.μ → c.nmem ztjc = lev v)
    (hlt : ∀ v, v < g.μ → lev v < g.μ) (hhl : ∀ l, l < g.μ → c.nmem ztcnm = hl l)
    (hhl1 : ∀ l, l < g.μ → hl l ≤ 1) (hblk : ∀ l, l < g.μ → c.nmem ztcdg = blk l)
    (hblt : ∀ l, l < g.μ → hl l ≠ 1 → blk l < g.μ)
    (hk1 : ∀ v, v < g.μ → key v < g.N ∧ inv ztjzk = first v ∧ vert zthws = v)
    (hk2 : ∀ p, p < g.N → first ztbaiv = inv p → key ztbaiv = p)
    (hcnt : ∀ b, b < g.μ → c.nmem ztys = cntLt ztbsf g.μ b)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W placeS c c' k ∧ k ≤ 32 * g.N + 4 ∧ WordsBounded W c' ∧
      PFr StDRG ztens c c' ∧
      PlInv g.μ ztbsf key ztvra ztvrb ztvrc c.nmem g.N
        c'.nmem := by
  have hU := g.U_ge; have hE := g.END_eq; have b42 := g.base_eq 42; have b43 := g.base_eq 43
  have b44 := g.base_eq 44; have b45 := g.base_eq 45; have b0 := g.base_eq 0
  have b3 := g.base_eq 3; have b32 := g.base_eq 32; have b35 := g.base_eq 35
  have b36 := g.base_eq 36
  zugyo
  have hinj : ztflk := fun v w hv hw h => by
    grind
  have hbo_lt : ∀ v, v < g.μ → (bo v < g.μ ↔ hl ztkag ≠ 1) := fun v hv => by
    zuocl
    zus
    · zugyx
    grind
  unfold placeS
  have e1 := Exec.constN (P := P) hw 130860 0 by_omega
  set c1 := { c with nreg := upd c.nreg 130860 0 } with hc1
  have f1 : PFr StDRG ztens c c1 :=
    ⟨fun r hr => by simp only [c1, Machine.upd_other _ _ _ (show r ≠ 130860 by
        unfold StDRG at hr; omega)], rfl, rfl, rfl, fun a _ => rfl⟩
  zuiwb
  obtain ⟨c', k, e, hk', hw', hi', hn', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130860) (rn := 130014) (body := placeBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130860 = j ∧ c'.nreg 130014 = g.N ∧
      PFr StDRG ztens c c' ∧
      PlInv g.μ bo key ztvra ztvrb ztvrc c.nmem j c'.nmem)
    g.N 30 zthd
    (fun j c3 hj ⟨hw3, hi3, hn3, hf3, hI3⟩ => by
      have hG3 : ztkzy := hG.frame (fun r hr => hf3.1 r (by
        unfold GRReg at hr; unfold StDRG; omega))
      have keep : ∀ a, a < g.base 42 → c3.nmem a = c.nmem a := fun a ha =>
        hf3.2.2.2.2 a (by unfold PlMem; omega)
      set v := vert (inv j) with hv
      have hvμ : v < g.μ := hvlt j hj
      have hlv := hlt v hvμ
      set b := blk ztkag with hb
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, hi4, hm4⟩ := placeBody_exec (P := P) hw3 hG3
        (gg := inv j) (v := v) (f := first v) (l := lev v) (h := hl ztkag) (b := b)
        (q := c3.nmem ztys) hi3 hj
        by_grind by_grind
        by_grind hvμ
        by_grind
        ztfrh (fun _ => hlv)
        ztfrh (fun _ => hhl1 _ hlv)
        ztfrh (fun _ h => hblt _ hlv h)
        ztdnl (fun hf hh => by
          have hkv : ztuun := hk2 j hj hf
          have hbv : ztund := by simp only [hbo, blkOf, ite_eq_right hh, hb]
          have hbμ : b < g.μ := hblt _ hlv hh
          rw [hI3.cnt b hbμ, ← hbv, ← hkv, ← rk_eq_cB]
          have := rk_lt (bo := bo) (key := key) hvμ
          have := cntLt_succ bo g.μ ztepn; have := cntLt_le bo g.μ ztlgh
          omega) hW
      refine ⟨c4, k4, e4, hk4, hw4, hi4, by
        rw [hf4.1 _ ztjra]; omega,
        hf3.trans (hf4.mono (fun r h => by unfold PLRG at h; unfold StDRG; omega)
          ztjvm), ?_⟩
      zumnq
      zugif
      · have hkv : ztuun := hk2 j hj hc.1
        have hbv : ztund := by simp only [hbo, blkOf, ite_eq_right hc.2, hb]
        have hbμ : bo v < g.μ := (hbo_lt v hvμ).2 hc.2
        have hq : c3.nmem ztys = plPos g.μ bo key v := by
          rw [← hbv, hI3.cnt _ hbμ]; unfold plPos; rw [rk_eq_cB, hkv]
        have := hI3.step hinj by_omega by_omega hvμ hkv hbμ
        rw [hq, ← hbv]; omega
      · refine hI3.skip (fun w hw hkw hbw => hc ?_)
        grind)
    (j₀ := 0) ⟨e1.wb_right, by_rfl, hG1.rN, f1, PlInv.zero hcnt⟩ ztbg
  exact ⟨c', 1 + k, .seq e1 e, by_omega, hw', hf', hm'⟩
end proofs
noncomputable def segL (s μ : ℕ) (bo : ℕ → ℕ) : ℕ → List ztw
  | 0 => []
  | j + 1 => optSeg s (cntLt bo μ j) (cntLt bo μ ztl) ++ segL s μ bo j
theorem segL_length_le (s μ : ℕ) (bo : ℕ → ℕ) (j : ℕ) : (segL s μ bo j).length ≤ j := by
  induction j with
  | zero => zuocn
  | succ j ih =>
    simp only [segL, List.length_append, optSeg]
    split_ifs <;> simp <;> omega

/-- One block of the stack scan. -/
def stkBody : Stmt := .seq (block [.addN 130872 130072 130870, .loadN 130671 130872,
  .copyN 130670 130871]) (.seq (pushOne 0) (block [.copyN 130871 130671,
  .addN 130870 130870 130001]))

/-- **The initial work stack.** -/
def stkS : Stmt := .seq zthsg
  (.whileLtN 130870 130011 stkBody)

/-- The registers of the stack scan. -/
def StkRG (r : ℕ) : Prop :=
  (130870 ≤ r ∧ r ≤ 130872) ∨ (130670 ≤ r ∧ r ≤ 130671) ∨ (130701 ≤ r ∧ r ≤ 130703)
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
theorem stkS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c) {s : ℕ}
    {bo : ℕ → ℕ} (hs : c.nreg 130674 = s) (hS : c.nreg 130700 = g.base 46)
    (hcnt : ∀ b, b < g.μ → c.nmem ztys = cntLt bo g.μ ztds) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stkS c c' k ∧ k ≤ 20 * g.μ + 5 ∧ WordsBounded W c' ∧
      PFr StkRG (fun a => g.base 46 ≤ a ∧ a < g.base 46 + 2 * g.μ) c c' ∧
      c'.nreg 130701 = 2 * (segL s g.μ bo g.μ).length ∧
      segL s g.μ bo g.μ = stkList c'.nmem ztmkh (segL s g.μ bo g.μ).length := by
  have hU := g.U_ge; have hE := g.END_eq; have b42 := g.base_eq 42; have b46 := g.base_eq 46
  set Am : ℕ → Prop := fun a => g.base 46 ≤ a ∧ a < g.base 46 + 2 * g.μ with hAm
  unfold stkS
  obtain ⟨c1, k1, e1, hk1, hw1, h70, h71, htp1, hf1⟩ : ∃ c1 k1, Exec P W
      zthsg c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ c1.nreg 130870 = 0 ∧ c1.nreg 130871 = 0 ∧ c1.nreg 130701 = 0 ∧
      PFr StkRG Am c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp,
      ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    zujpi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have hG1 : ztido := hG.frame (fun r hr => hf1.1 r ztkve)
  obtain ⟨c', k, e, hk', hw', hi', hn', h71', htp', hL', hf'⟩ := forN (P := P) (W := W)
    (ri := 130870) (rn := 130011) (body := stkBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130870 = j ∧ c'.nreg 130011 = g.μ ∧
      c'.nreg 130871 = cntLt bo g.μ j ∧ c'.nreg 130701 = 2 * (segL s g.μ bo j).length ∧
      segL s g.μ bo j = stkList c'.nmem ztmkh (segL s g.μ bo j).length ∧
      PFr StkRG Am c c')
    g.μ 18 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, h712, htp2, hL2, hf2⟩ => by
      have hG2 : ztsbm := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StkRG; omega))
      zukiq
      zudqb
      have hlen := segL_length_le s g.μ bo j
      have mj : c2.nmem (g.base 42 + j) = cntLt bo g.μ ztl := by
        zuede
      have hle := cntLt_le bo g.μ ztl
      obtain ⟨c3, k3, e3, hk3, hw3, h670, h671, htp3, h703, hf3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130872 130072 130870, .loadN 130671 130872, .copyN 130670 130871])
          c2 c3 k3 ∧ k3 = 3 ∧ WordsBounded W c3 ∧ c3.nreg 130670 = cntLt bo g.μ j ∧
          c3.nreg 130671 = cntLt bo g.μ ztl ∧ c3.nreg 130701 = c2.nreg 130701 ∧
          c3.nreg 130870 = j ∧
          (∀ r, ¬ StkRG r → c3.nreg r = c2.nreg r) ∧ c3.nmem = c2.nmem ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
        exec_block
        · grind
        · refine ⟨rfl, ‹_›, by_tauto, by config_simp; grind,
            by config_simp, by_tauto, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
          zujpi
          repeat (rw [Machine.upd_other _ _ _ by_omega])
      obtain ⟨c4, k4, e4, hk4, hw4, hm4, htp4, hr4, hrr4, hrm4, ho4⟩ := pushOne_exec (P := P) hw3 0 (s := s) (bS := g.base 46)
        (tp := 2 * (segL s g.μ bo j).length)
        by_omega (by rw [hf3 _ ztbsl, r1]) h670 h671
        (by zunro; exact hs)
        (by zunro; exact hS)
        by_omega by_omega
      have hpush : (c4.nmem, c4.nreg 130701) = pushF ztmkh s ztrnq
          ztzld ztisf := by
        rw [hm4, htp4]; unfold pushF; grind
      obtain ⟨hL5, htp5, hout5⟩ := pushF_stk (bS := g.base 46) (s := s) (a := cntLt bo g.μ j)
        (b := cntLt bo g.μ ztl) (q := ztisf)
        (L := segL s g.μ bo j) by_grind rfl
      rw [← hpush] at hL5 htp5 hout5
      have hlen' := segL_length_le s g.μ bo ztl
      have r1' : ztizd := by
        rw [hr4 _ by_omega by_omega by_omega, hf3 _ ztbsl, r1]
      have h70' : c4.nreg 130870 = j := by
        grind
      have h671' : c4.nreg 130671 = cntLt bo g.μ ztl := by
        grind
      obtain ⟨c6, k6, e6, hk6, hw6, h70'', h71'', hr6, hm6, hrr6, hrm6, ho6⟩ : ∃ c6 k6, Exec P W
          (block [.copyN 130871 130671, .addN 130870 130870 130001]) c4 c6 k6 ∧ k6 = 2 ∧
          WordsBounded W c6 ∧ c6.nreg 130870 = j + 1 ∧ c6.nreg 130871 = cntLt bo g.μ ztl ∧
          (∀ r, r ≠ 130870 → r ≠ 130871 → c6.nreg r = c4.nreg r) ∧ c6.nmem = c4.nmem ∧
          c6.rreg = c4.rreg ∧ c6.rmem = c4.rmem ∧ c6.output = c4.output := by
        exec_block
        · config_simp; omega
        · refine ⟨rfl, ‹_›, by config_simp; omega, by config_simp; omega,
            fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
          zubi
          repeat (rw [Machine.upd_other _ _ _ by_omega])
      have hseg : segL s g.μ bo ztl = optSeg s ztrnq ztzld ++
          segL s g.μ bo j := rfl
      refine ⟨c6, k3 + (k4 + k6), .seq e3 ztgxa, by_omega, hw6, h70'', ?_, h71'', ?_,
        ?_, ?_⟩
      · rw [hr6 _ by_omega by_omega, hr4 _ by_omega by_omega by_omega,
          hf3 _ ztbsl]; omega
      · grind
      · grind
      · refine hf2.trans ztgox
        · unfold StkRG at hr
          rw [hr6 _ by_omega by_omega, hr4 _ by_omega by_omega by_omega,
            hf3 _ ztbsl]
        · grind
        · grind
        · grind
        · rw [hm6]
          grind)
    (j₀ := 0) ⟨hw1, h70, hG1.rμ, by rw [h71]; zuocu, by_tauto,
      by rfl, hf1⟩ (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, by_omega, hw', hf', htp', hL'⟩
end proofs
noncomputable def seg (μ : ℕ) (bo : ℕ → ℕ) (b : ℕ) : ℕ × ℕ := (cntLt bo μ b, cntLt bo μ ztds)

/-- The finished (small) blocks. -/
noncomputable def finL (s μ : ℕ) (bo : ℕ → ℕ) : Finset ztw :=
  ((Finset.range μ).filter (fun b => cntBelow bo μ b ≤ s)).image (seg μ bo)
variable {s μ : ℕ} {bo : ℕ → ℕ}
theorem len_seg (b : ℕ) : len ztrwt = cntBelow bo μ b := by
  unfold len seg; rw [cntLt_succ]; omega
theorem mem_segL {j : ℕ} {p : ℕ × ℕ} :
    p ∈ segL s μ bo j ↔ ∃ b, b < j ∧ s < cntBelow bo μ b ∧ p = seg μ bo b := by
  induction j with
  | zero => zuocn
  | succ j ih =>
    simp only [segL, List.mem_append, ih, optSeg]
    constructor
    · rintro (h | ⟨b, h1, h2, h3⟩)
      · split_ifs at h with hs
        · zvnns at h
          exact ⟨j, by_omega, by rw [cntLt_succ] at hs; omega, h⟩
        simp_all
      grind
    · rintro ⟨b, h1, h2, h3⟩
      rcases Nat.lt_or_ge b j with h | h
      · grind
      · have hb : b = j := by_omega
        zulsy
        left; rw [ite_eq_left (by rw [cntLt_succ]; omega)]; simp [h3, seg]
variable {p : ℕ × ℕ} (j : ℕ) {key act : ℕ → ℕ}
theorem mem_finL :
    p ∈ finL s μ bo ↔ ∃ b, b < μ ∧ cntBelow bo μ b ≤ s ∧ p = seg μ bo b := by
  unfold finL
  grind
theorem lv_iff :
    Lv ztkeu ztlnu p ↔ ∃ b, b < μ ∧ p = seg μ bo b := by
  unfold Lv; rw [mem_segL, mem_finL]
  grind
theorem seg_disj {b b' : ℕ} (h : b < b') : (seg μ bo b).2 ≤ (seg μ bo b').1 :=
  cntLt_mono bo μ by_omega
theorem segL_nodup : (segL s μ bo j).Nodup := by
  induction j with
  | zero => zuocn
  | succ j ih =>
    zugzp

    · refine List.nodup_cons.mpr ⟨fun hm => ?_, ih⟩
      obtain ⟨b, h1, h2, h3⟩ := mem_segL.mp hm
      have := seg_disj (μ := μ) (bo := bo) h1
      rw [← h3] at this; simp only [seg] at this; omega
    · simp_all

/-- The potential of the initial stack. -/
theorem sum_segL :
    ∑ p ∈ (segL s μ bo j).toFinset, ztcyr ≤ 2 * cntLt bo μ j := by
  induction j with
  | zero => simp [segL, cntLt]
  | succ j ih =>
    zumma
    zugzp

    · have hn := segL_nodup (s := s) (μ := μ) (bo := bo) ztl
      simp only [segL, optSeg, ite_eq_left hs] at hn
      rw [List.singleton_append, List.toFinset_cons, Finset.sum_insert (by
        simp_all)]
      have : ztxix := len_seg j
      omega
    · grind

/-- The items of a block segment. -/
theorem items_seg (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w)
    (hact : ∀ v, v < μ → bo v < μ → act ztglh = v) {b : ℕ} (hb : b < μ) :
    items act ztrwt = (Finset.range μ).filter zthhe := by
  zuepb
  rw [mem_items]; simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, h1, h2, rfl⟩
    obtain ⟨w, hw, hbw, rfl⟩ := exists_plPos (key := key) hinj h1 h2
    simp_all
  · rintro ⟨hv, hbv⟩
    refine ⟨plPos μ bo key v, ?_, ?_, hact v hv by_omega⟩
    · have := plPos_ge (μ := μ) (bo := bo) (key := key) v; rw [hbv] at this; tauto
    · have := plPos_lt (μ := μ) (bo := bo) (key := key) hv; rw [hbv] at this; tauto
theorem inj_seg (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w)
    (hact : ∀ v, v < μ → bo v < μ → act ztglh = v) {b : ℕ} (hb : b < μ) :
    Set.InjOn act (Finset.Ico (seg μ bo b).1 (seg μ bo b).2) := by
  zukjk
  simp only [Finset.coe_Ico, Set.mem_Ico] at hi hi'
  obtain ⟨w, hw, hbw, rfl⟩ := exists_plPos (key := key) hinj hi.1 hi.2
  obtain ⟨w', hw', hbw', rfl⟩ := exists_plPos (key := key) hinj hi'.1 hi'.2
  simp_all

/-- **The initial state of the work stack.** -/
theorem SInv.init {k : ℕ} {H : Finset ℕ} {slab : ℕ → ℕ} {Adj : ℕ → ℕ → Prop} {key act : ℕ → ℕ}
    (hinj : ∀ v w, v < μ → w < μ → key v = key w → v = w)
    (hact : ∀ v, v < μ → bo v < μ → act ztglh = v)
    (hH : ∀ v, v < μ → (v ∈ H ↔ ¬ bo v < μ)) (_hHμ : ∀ v ∈ H, v < μ)
    (hslab : ∀ v w, v < μ → w < μ → bo v < μ → bo v = bo w → slab v = slab w)
    (hedge : ∀ x y, Adj x y → x ∉ H → y ∉ H → x < μ ∧ y < μ ∧ bo x = bo y) :
    SInv μ k s H slab Adj act ztkeu ztlnu ∅ 0 := by
  have hit : ∀ p, Lv ztkeu ztlnu p → ∃ b, b < μ ∧ p = seg μ bo b ∧
      items act p = (Finset.range μ).filter zthhe := fun p hp => by
    zucno
    exact ⟨b, hb, rfl, items_seg hinj hact hb⟩
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp v hv => ?_, segL_nodup μ, fun p hp hf => ?_,
    fun p q hp hq hpq => ?_, fun p q hp hq hpq => ?_, fun p hp => ?_, fun p hp => ?_,
    fun v hv hvH _ => ?_, fun p hp v hv => ?_, fun p hp v hv w hw => ?_,
    fun x y hxy hx _ hy _ => ?_, by_simp, ?_, ?_⟩
  · obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp; exact cntLt_mono bo μ by_omega
  · obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp; exact inj_seg hinj hact hb
  · grind
  · obtain ⟨b, -, h2, rfl⟩ := mem_segL.mp hp
    obtain ⟨b', -, h2', h3'⟩ := mem_finL.mp hf
    have := congrArg len h3'; rw [len_seg, len_seg] at this; omega
  · obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp; obtain ⟨b', hb', rfl⟩ := lv_iff.mp hq
    unfold RDisj
    rcases lt_trichotomy b b' with h | h | h
    · exact Or.inl ztwdk
    · grind
    · exact Or.inr (Or.inl ztwdk)
  · obtain ⟨b, hb, rfl, hi⟩ := hit p hp; obtain ⟨b', hb', rfl, hi'⟩ := hit q hq
    rw [hi, hi', Finset.disjoint_left]
    grind
  · obtain ⟨b, -, h2, rfl⟩ := mem_segL.mp hp; zuouc; exact h2
  · obtain ⟨b, -, h2, rfl⟩ := mem_finL.mp hp; zuouc; exact h2
  · have hb : bo v < μ := by_grind
    refine ⟨seg μ bo ztepn, lv_iff.mpr ⟨bo v, hb, rfl⟩, ?_⟩
    rw [items_seg hinj hact hb]; grind
  · zudqv
  · zudqv
  · obtain ⟨hxμ, hyμ, hb⟩ := hedge x y hxy hx hy
    have hbx : bo x < μ := by_grind
    refine ⟨seg μ bo (bo x), lv_iff.mpr ⟨bo x, hbx, rfl⟩, ?_, ?_⟩ <;>
      rw [items_seg hinj hact hbx] <;> simp [hxμ, hyμ, hb]
  · zubqp

    rw [Finset.card_empty, Nat.mul_zero, Nat.zero_add, ← Finset.mul_sum]
    have : 3 * k * ∑ p ∈ (segL s μ bo μ).toFinset, ztcyr ≤ 3 * k * ztnfg :=
      Nat.mul_le_mul_left _ by_omega
    grind
  · zubqp

    omega
def stageD : Stmt := .seq (fillWith 130074 130011 130011)
  (.seq zthsw
  (.seq invStmt (.seq bcS (.seq pfxS (.seq placeS (fillWith 130078 130011 130009))))))

/-- The memory written by stage D. -/
def DMem (g : GV) (a : ℕ) : Prop :=
  (g.base 32 ≤ a ∧ a < g.base 33) ∨ (g.base 42 ≤ a ∧ a < g.base 45) ∨
    (g.base 48 ≤ a ∧ a < g.base 49)

/-- An injective self-map of `[0, N)` is onto. -/
theorem surj_range {N : ℕ} {f : ℕ → ℕ} (hlt : ∀ i, i < N → f i < N)
    (hinj : ∀ i j, i < N → j < N → f i = f j → i = j) : ∀ p, p < N → ∃ i, i < N ∧ f i = p := by
  zuda
  have := Finset.surjOn_of_injOn_of_card_le f (s := Finset.range N) (t := Finset.range N)
    ztgjg
    (fun i hi j hj h => by
      grind) le_rfl
  obtain ⟨i, hi, hfi⟩ := this (by simp_all : p ∈ (Finset.range N : Set ℕ))
  grind
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 8000000 in
/-- **Stage D.** -/
theorem stageD_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    {lev hl blk : ℕ → ℕ}
    (hpre_lt : ∀ i, i < g.N → c.nmem ztfsb < g.N)
    (hpre_inj : ∀ i j, i < g.N → j < g.N → c.nmem ztfsb = c.nmem ztrqs →
      i = j)
    (hfst_lt : ∀ v, v < g.μ → c.nmem ztbrk < g.N)
    (hvf : ∀ v, v < g.μ → c.nmem (g.bV + c.nmem ztbrk) = v)
    (hvlt : ∀ i, i < g.N → c.nmem zttkz < g.μ) (hVA : g.bV + g.N ≤ g.A0)
    (hlev : ∀ v, v < g.μ → c.nmem ztjc = lev v)
    (hlt : ∀ v, v < g.μ → lev v < g.μ) (hhl : ∀ l, l < g.μ → c.nmem ztcnm = hl l)
    (hhl1 : ∀ l, l < g.μ → hl l ≤ 1) (hblk : ∀ l, l < g.μ → c.nmem ztcdg = blk l)
    (hblt : ∀ l, l < g.μ → hl l ≠ 1 → blk l < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageD c c' k ∧ k ≤ 40 * zttld + 40 ∧ WordsBounded W c' ∧
      PFr StDRG ztemj c c' ∧
      (∀ b, b < g.μ → c'.nmem ztys = cntLt ztbsf g.μ ztds) ∧
      (∀ v, v < g.μ → c'.nmem ztczp = if blkOf g.μ lev hl blk v < g.μ then
        plPos g.μ ztbsf ztxxc v
        else g.μ) ∧
      (∀ v, v < g.μ → blkOf g.μ lev hl blk v < g.μ → c'.nmem (g.base 43 + plPos g.μ
        ztbsf ztxxc v) = v) ∧
      (∀ v, v < g.μ → c'.nmem ztvz = 0) := by
  zuuv
  have b0 := g.base_eq 0; have b3 := g.base_eq 3; have b29 := g.base_eq 29
  have b32 := g.base_eq 32; have b33 := g.base_eq 33; have b35 := g.base_eq 35
  have b36 := g.base_eq 36; have b42 := g.base_eq 42; have b43 := g.base_eq 43
  have b44 := g.base_eq 44; have b45 := g.base_eq 45; have b48 := g.base_eq 48
  have b49 := g.base_eq 49
  have hA0 : g.A0 = g.base 0 := by_omega
  zugyo
  set key : ℕ → ℕ := fun v => c.nmem (g.base 29 + c.nmem ztbrk) with hkey
  -- the memory reads survive every step
  have rd : ∀ c' : Config, PFr StDRG ztemj c c' →
      (∀ a, a < g.base 32 → c'.nmem a = c.nmem a) ∧
      (∀ a, g.base 33 ≤ a → a < g.base 42 → c'.nmem a = c.nmem a) := fun c' h =>
    ⟨fun a ha => h.2.2.2.2 a ztxg,
     fun a h1 h2 => h.2.2.2.2 a ztxg⟩
  unfold stageD
  -- POS := μ
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hz1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 44 by_omega) hG.rμ hG.rμ ztpc ztpc
    ztpc by_omega by_omega
  have f1 : PFr StDRG ztemj c c1 := hf1.mono zthxh
    ztfrl
  zuiwb
  -- the inversion
  obtain ⟨c2, k2, e2, hk2, hw2, h800, h801, h802, hf2, hm2⟩ : ∃ c2 k2, Exec P W
      zthsw c1 c2 k2 ∧
      k2 = 3 ∧ WordsBounded W c2 ∧ c2.nreg 130800 = g.base 29 ∧ c2.nreg 130801 = g.base 32 ∧
      c2.nreg 130802 = g.N ∧ PFr StDRG ztemj c1 c2 ∧ c2.nmem = c1.nmem := by
    have r59 := hG1.rbase 29 by_omega; have r62 := hG1.rbase 32 by_omega; have rN := hG1.rN
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; omega, by config_simp; omega, by config_simp; exact rN,
      ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, rfl⟩
    zujph
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have f2 := f1.trans hf2
  have hG2 : ztsbm := hG.frame ztyqr
  have rd2 := rd c2 f2
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hinv3⟩ := invStmt_exec (P := P) hw2 hG2.one h800 h801 h802
    (fun i hi => by rw [rd2.1 _ by_omega]; grind)
    (fun i j hi hj h => hpre_inj i j hi hj (by rwa [rd2.1 _ by_omega, rd2.1 _ by_omega] at h))
    by_omega by_omega by_omega by_omega
  have f3 : PFr StDRG ztemj c c3 := f2.trans (hf3.mono (fun r h => by
    unfold InvRG at h; unfold StDRG; omega) (fun a h => by unfold DMem; omega))
  have hG3 : ztkzy := hG.frame (fun r hr => f3.1 r ztun)
  have rd3 := rd c3 f3
  set inv : ℕ → ℕ := fun p => c3.nmem ztlpb with hinvd
  have hinvpre : ∀ i, i < g.N → inv (c.nmem ztfsb) = i := fun i hi => by
    have := hinv3 i hi; rw [rd2.1 _ by_omega] at this; omega
  have hsurj := surj_range hpre_lt hpre_inj
  have hinv_lt : ∀ p, p < g.N → inv p < g.N ∧ c.nmem (g.base 29 + inv p) = p := fun p hp => by
    obtain ⟨i, hi, rfl⟩ := hsurj p hp
    grind
  -- block sizes and starts
  have hlev3 : ∀ v, v < g.μ → c3.nmem ztjc = lev v := fun v hv => by
    grind
  have hhl3 : ∀ l, l < g.μ → c3.nmem ztcnm = hl l := fun l hl' => by
    zuhnj
  have hblk3 : ∀ l, l < g.μ → c3.nmem ztcdg = blk l := fun l hl' => by
    zuhnj
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hcnt4⟩ := bcS_exec (P := P) hw3 hG3 hlev3 hlt hhl3 hhl1 hblk3
    hblt hW
  have f4 : PFr StDRG ztemj c c4 := f3.trans (hf4.mono ztng
    ztfrl)
  have hG4 : ztsbn := hG.frame (fun r hr => f4.1 r ztun)
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, hcnt5⟩ := pfxS_exec (P := P) hw4 hG4 hcnt4 hW
  have f45 : PFr StDRG ztcde c3 c5 := hf4.trans hf5
  have f5 : PFr StDRG ztemj c c5 := f3.trans (f45.mono ztng
    ztfrl)
  have hG5 : GR g c5 := hG.frame (fun r hr => f5.1 r ztun)
  have rd5 := rd c5 f5
  have k35 : ∀ a, (a < g.base 42 ∨ g.base 42 + g.μ ≤ a) → c5.nmem a = c3.nmem a := fun a ha =>
    f45.2.2.2.2 a by_omega
  -- the placement
  obtain ⟨c6, k6, e6, hk6, hw6, hf6, hI6⟩ := placeS_exec (P := P) hw5 hG5 (inv := inv)
    (vert := fun i => c.nmem zttkz) (first := fun v => c.nmem ztbrk) (key := key)
    (fun p hp => by rw [k35 _ by_omega])
    (fun p hp => by have := (hinv_lt p hp).1; omega)
    (fun p hp => by have := (hinv_lt p hp).1; zunnz)
    (fun p hp => hvlt _ (hinv_lt p hp).1)
    (fun v hv => by zunnz)
    (fun v hv => by zunnz; exact hlev v hv) hlt
    (fun l hl' => by zuocv; exact hhl l hl') hhl1
    (fun l hl' => by zuocv; exact hblk l hl') hblt
    (fun v hv => ⟨hpre_lt _ zttno, hinvpre _ zttno, hvf v hv⟩)
    (fun p hp h => by
      zuoqr; zvmwc; exact (hinv_lt p hp).2)
    hcnt5 hW
  have f6 : PFr StDRG ztemj c c6 := f5.trans (hf6.mono ztng
    (fun a h => by unfold PlMem at h; unfold DMem; omega))
  have hG6 : GR g c6 := hG.frame (fun r hr => f6.1 r ztun)
  -- DF := 0
  obtain ⟨c7, k7, x7, hk7, hw7, hf7, hz7⟩ := fillWith_exec (P := P) hw6 hG6.one
    (hG6.rbase 48 by_omega) hG6.rμ hG6.zero ztpc ztpc
    ztpc by_omega by_omega
  have f7 : PFr StDRG ztemj c c7 := f6.trans (hf7.mono (fun r h => by
    unfold FillRG at h; unfold StDRG; omega) (fun a h => by unfold DMem; omega))
  have k67 : ∀ a, a < g.base 48 → c7.nmem a = c6.nmem a := fun a ha =>
    hf7.2.2.2.2 a by_omega
  have hnk : ∀ w, w < g.μ → key w < g.N := fun w hw => hpre_lt _ (hfst_lt w hw)
  refine ⟨c7, k1 + ztcnr,
    .seq x1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 x7))))), by_omega, hw7, f7,
    fun b hb => ?_, fun v hv => ?_, fun v hv hbv => ?_, fun v hv => hz7 v hv⟩
  · zuoii; exact hI6.full hnk hb
  · rw [k67 _ by_omega, hI6.pos v hv]
    by_cases h : bo v < g.μ
    · rw [ite_eq_left ⟨h, hnk v hv⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h h'.1), ite_eq_right h, k35 _ by_omega]
      rw [hf3.2.2.2.2 _ by_omega, hm2]
      exact hz1 v hv
  · have := plPos_lt_μ (key := key) hv hbv
    zuoii; exact hI6.act v hv hbv (hnk v hv)
end proofs
open Chazelle.Separator Chazelle.Separator.CombMap
def ssOf (g : GV) : SS where
  bACT := g.base 43
  bFIRST := g.base 0
  bFPRE := g.base 29
  bPOW := g.base 40
  bFSZ := g.base 28
  bUP := g.A0 + 54 * g.U + g.L * g.U
  L := g.L
  N := g.N
  bLEV := g.base 3
  bUPT := g.A0 + 54 * g.U
  bPV := g.base 6
  bPOS := g.base 44
  bDF := g.base 48
  μ := g.μ
  bSO := g.base 11
  bSF := g.base 17
  bFPAR := g.base 26
  bTMP := g.base 45
  bHALF := g.base 39
  bLBOT := g.base 37
  bLTOP := g.base 38
  bVERT := g.bV
  bOPP := g.bO
  bATT := g.base 9
  bFP := g.base 7
  s := g.s
  bSTK := g.base 46
variable {g : GV}
theorem ssOf_lay {W : ℕ} (hμN : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0)
    (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) : (ssOf g).Lay g.A0 g.U W := by
  have hU := g.U_ge; have hLU := g.L_le_U
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, by show g.μ + 3 ≤ g.U; omega, by show g.N + 1 ≤ g.U; omega, hLU,
    by tauto, hV, hO, hW⟩

/-- The first dart of each vertex, read from slot 0. -/
def firstOf (g : GV) (m : ℕ → ℕ) (h : ∀ u, u < g.μ → m ztrk < g.N) :
    Fin g.μ → Fin g.N := fun v => ⟨m ztbrk, h v v.2⟩

/-- The window of a slab from the level tables. -/
theorem lv_win {k cs l l' : ℕ} (hk : 0 < k) (h : ztocm / k = ztetu / k) :
    l - ztetu % k ≤ l' ∧ l' ≤ l + ztie - ztetu % k := by
  have h1 := Nat.div_add_mod ztetu k; have h2 := Nat.mod_lt ztetu hk
  have h3 := Nat.div_add_mod ztocm k; have h4 := Nat.mod_lt ztocm hk
  grind
variable {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The static facts.** -/
theorem sfacts_of {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face ztdbz = f} {C : CoTree ztqc} {R : BTree} {preE slot : ℕ → ℕ}
    {m : ℕ → ℕ} (hA : AF g M T m) (hB1 : B1F g M T a ha m) (hB2 : B2F g C R preE slot m)
    (hpl : M.Planar) (hμN : g.μ ≤ g.N) (hO : g.bO + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0)
    (hW : g.END ≤ W) (hL : 0 < g.L)
    (hhalf : ∀ w, w ≤ g.μ → m zthxm = w / 2)
    (hpow : ∀ j, j < g.L → m ztlpe = 2 ^ j)
    (hk : 0 < g.k') {cs : ℕ} (hlv : ∀ l, l < g.μ → LvOK g m cs l) :
    SFacts M T a ha C R (firstOf g m hA.first_lt) preE slot ztqxy g.k' cs ztmol g.A0 g.U W
      m := by
  zueqs
  have hP := g.two_pow_L; have hPU := g.P_le_U
  refine ⟨ssOf_lay hμN hO hV hW, rfl, rfl, hpl, fun v => ?_, fun d => (hA.map d).2.2,
    fun d => (hA.map d).1, fun v => rfl, hA.lev, hA.lev_lt, hB1.att, hB1.fp, fun x => ?_,
    fun x => ?_, hB2.fpar, hB2.fpar_lt, hB2.r0, hB2.pre, hB2.sz, hB2.R_ok, hB2.R_n, hB2.R_up,
    hB2.R_root, hB2.R_pre, hB2.up_tab, fun v => ?_, fun x hx => upTf_lt T hx, fun x hx => ?_,
    hA.upt, hpow, by_tauto, hPU, hL, hhalf, fun v x hvx => ?_,
    fun v => ?_⟩
  · zulvn
    have h1 := (hA.map (firstOf g m hA.first_lt v)).2.2
    have h2 := hA.first_v v v.2
    simp only [firstOf] at h1 ⊢
    omega
  · zuim
    · show m ztrqo = (M.opp d : ℕ)
      exact (hB1.so d).1
    · show m (g.base 11 + ztnzv) = 2 * g.N + d
      zunew; exact (hB1.so d).2.1
    · show m (g.base 11 + ztjfg) = g.N + d
      zunew; exact (hB1.so d).2.2
  · zuim
    · show m ztrqp = (d : ℕ)
      exact (hB1.sf d).1
    · show m (g.base 17 + ztnzv) = (d : ℕ)
      zunew; exact (hB1.sf d).2.1
    · show m (g.base 17 + ztjfg) = ((M.fperm⁻¹ d : Fin g.N) : ℕ)
      zunew; exact (hB1.sf d).2.2
  · unfold upTf; simp
  · have := hA.pv ztfxa; simp only at this
    show m ztlpg = upTf T x
    zumvj
  · zuddh

    simp only [slabN, dite_eq_left v.2, dite_eq_left x.2] at hvx
    show m ztqop ≤ T.level x ∧ T.level x ≤ m ztqoq
    rw [hb, ht]; exact lv_win hk hvx
  · zuddh

    show m ztqoq + 1 - m ztqop ≤ g.k'
    omega
def copies (l : List ztw) : Stmt := block (l.map (fun p => .copyN p.1 p.2))

/-- The copies of the driver registers (destination, source). -/
def regCopies : List ztw :=
  [(130320, 130073), (130321, 130030), (130322, 130059), (130323, 130070), (130324, 130017),
   (130325, 130058), (130326, 130085), (130327, 130085), (130328, 130014), (130345, 130017),
   (130601, 130033), (130602, 130084), (130603, 130070), (130604, 130017), (130605, 130036),
   (130606, 130074), (130607, 130078), (130608, 130011), (130620, 130084), (130632, 130041),
   (130633, 130047), (130634, 130056), (130635, 130059), (130636, 130058), (130650, 130075),
   (130651, 130073), (130652, 130074), (130653, 130078), (130654, 130030), (130655, 130059),
   (130674, 130016), (130675, 130011), (130680, 130037), (130682, 130014), (130692, 130069),
   (130694, 130067), (130695, 130068), (130696, 130023), (130697, 130021), (130698, 130039),
   (130700, 130076), (130704, 130009), (130880, 130009)]

/-- One step of the products `L N` and `L μ`. -/
def mulBody : Stmt := block [.addN 130327 130327 130014, .addN 130620 130620 130011,
  .addN 130880 130880 130001]

/-- **The driver registers.** -/
def regsS : Stmt := .seq (copies regCopies) (.seq (.instr (.addN 130681 130014 130014))
  (.whileLtN 130880 130017 mulBody))

/-- The registers written by `regsS`. -/
def RegRG (r : ℕ) : Prop := 130300 ≤ r ∧ r ≤ 130889
section proofs
variable {P : Polygon} {W : ℕ}

/-- **A block of copies** with sources below `b ≤` destinations, destinations distinct. -/
theorem copies_exec {c : Config} (hw : WordsBounded W c) (l : List ztw) {b : ℕ}
    (hsep : ∀ p ∈ l, p.2 < b ∧ b ≤ p.1) (hnd : (l.map Prod.fst).Nodup) :
    ∃ c', Exec P W (copies l) c c' l.length ∧ WordsBounded W c' ∧
      ztfcu ∧ (∀ r, (∀ p ∈ l, p.1 ≠ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction l generalizing c with
  | nil => exact ⟨c, .skip hw, hw, by_simp_all, by_omega, rfl, rfl, rfl, rfl⟩
  | cons p t ih =>
    have e1 := Exec.copyN (P := P) hw p.1 p.2
    set c1 := { c with nreg := upd c.nreg p.1 _ } with hc1
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨c', e', hw', h1, h2, hm, hr, hrm, ho⟩ := ih e1.wb_right
      by_grind hnd.2
    have hp := hsep p (List.mem_cons_self)
    refine ⟨c', ?_, hw', fun q hq => ?_, fun r hr' => ?_, hm, hr, hrm, ho⟩
    · show Exec P W (.seq (.instr (.copyN p.1 p.2)) (copies t)) c c' (t.length + 1)
      zuocq; tauto
    · zujcq
      · rw [h2 _ by_grind]
        simp [c1]
      · have := hsep q by_omega
        rw [h1 q hq]; zuoqu
        zubc
    · rw [h2 r by_grind]
      zuoqu
      zuigp
set_option maxHeartbeats 4000000 in
/-- **The driver registers.** -/
theorem regsS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W regsS c c' k ∧ k ≤ 5 * g.L + 50 ∧ WordsBounded W c' ∧
      (ssOf g).Regs c' ∧ c'.nreg 130704 = 0 ∧ (∀ r, ¬ RegRG r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuegq
  zudyj
  have hLμ : ztpow := Nat.mul_le_mul_left _ by_omega
  unfold regsS
  obtain ⟨c1, e1, hw1, h1, h2, hm1, hr1, hrm1, ho1⟩ := copies_exec (P := P) hw regCopies
    (b := 130300) by_decide by_decide
  have g1 : ∀ r, r < 130300 → c1.nreg r = c.nreg r := fun r hr =>
    h2 r (fun p hp h => by have := ((show ∀ p ∈ regCopies, 130300 ≤ p.1 by decide) p hp); omega)
  have hG1 := hG.frame ztyqs
  have cp : ∀ d s, ztfqw ∈ regCopies → c1.nreg d = c.nreg s := by_grind
  have e2 := Exec.addN (P := P) hw1 130681 130014 130014 (by zuoud; omega)
  set c2 := { c1 with nreg := upd c1.nreg 130681 _ } with hc2
  have k12 : ∀ r, r ≠ 130681 → c2.nreg r = c1.nreg r := fun r h => by
    simp only [c2]; rw [Machine.upd_other _ _ _ h]
  have hG2 := hG1.frame (fun r hr => k12 r ztdgy)
  have h681 : c2.nreg 130681 = 2 * g.N := by
    simp only [c2, Machine.upd_same]; zuoud; ring
  obtain ⟨c3, k3, e3, hk3, ⟨hw3, h880, hL3, h327, h620, hk23, hm3, hr3, hrm3, ho3⟩⟩ := forN (P := P) (W := W)
    (ri := 130880) (rn := 130017) (body := mulBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130880 = j ∧ c'.nreg 130017 = g.L ∧
      c'.nreg 130327 = g.A0 + 54 * g.U + g.L * g.U + j * g.N ∧
      c'.nreg 130620 = g.A0 + 54 * g.U + j * g.μ ∧
      (∀ r, r ≠ 130327 → r ≠ 130620 → r ≠ 130880 → c'.nreg r = c2.nreg r) ∧
      c'.nmem = c2.nmem ∧ c'.rreg = c2.rreg ∧ c'.rmem = c2.rmem ∧ c'.output = c2.output)
    g.L 3 zthd
    (fun j c4 hj ⟨hw4, h4i, h4n, h4a, h4b, h4r, h4m, h4rr, h4rm, h4o⟩ => by
      have hN4 : c4.nreg 130014 = g.N := by zunhe; exact hG2.rN
      have hμ4 : c4.nreg 130011 = g.μ := by zunhe; exact hG2.rμ
      have h14 : ztizd := by zunhe; exact hG2.one
      have hjN : ztl * g.N ≤ g.L * g.N := Nat.mul_le_mul_right _ by_omega
      have hjμ : ztl * g.μ ≤ g.L * g.μ := Nat.mul_le_mul_right _ by_omega
      rw [Nat.succ_mul] at hjN hjμ
      unfold mulBody
      exec_block
      · omega
      · config_simp; omega
      · config_simp; omega
      · refine ⟨le_refl _, by_omega, by config_simp; omega, by_tauto,
          by config_simp; grind,
          by config_simp; grind, fun r a1 a2 a3 => ?_, h4m, h4rr,
          h4rm, h4o⟩
        zubi
        rw [Machine.upd_other _ _ _ a3, Machine.upd_other _ _ _ a2, Machine.upd_other _ _ _ a1]
        grind)
    (j₀ := 0) ⟨e2.wb_right, by rw [k12 _ by_omega, cp 130880 130009 by_decide]; exact hG.zero,
      hG2.rL, by rw [k12 _ by_omega, cp 130327 130085 by_decide, hG.rUP]; ring,
      by rw [k12 _ by_omega, cp 130620 130084 by_decide, hG.rbase 54 by_omega, g.base_eq]; ring,
      fun r _ _ _ => rfl, rfl, rfl, rfl, rfl⟩ (Nat.zero_le _)
  have kk3 : ∀ r, r ≠ 130327 → r ≠ 130620 → r ≠ 130880 → r ≠ 130681 → c3.nreg r = c1.nreg r :=
    by grind
  have R : ∀ d s, ztfqw ∈ regCopies → d ≠ 130327 → d ≠ 130620 → d ≠ 130880 → d ≠ 130681 →
      c3.nreg d = c.nreg s := by_grind
  have hlen : regCopies.length = 43 := rfl
  refine ⟨c3, regCopies.length + (1 + k3), .seq e1 ztbpc, by_omega, hw3, ?_,
    by rw [R 130704 130009 by_decide by_omega by_omega by_omega by_omega]; exact hG.zero,
    fun r hr => ?_, by_grind, by_grind, by_grind,
    by grind⟩
  · refine ⟨by zunjm; exact hG.one,
      by zunjm; exact hG.zero,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [R 130320 130073 by_decide by_omega by_omega by_omega by_omega, hG.rbase 43 by_omega]; rfl
    · rw [R 130321 130030 by_decide by_omega by_omega by_omega by_omega, hG.rbase 0 by_omega]; rfl
    · rw [R 130322 130059 by_decide by_omega by_omega by_omega by_omega, hG.rbase 29 by_omega]; rfl
    · rw [R 130323 130070 by_decide by_omega by_omega by_omega by_omega, hG.rbase 40 by_omega]; rfl
    · rw [R 130324 130017 by_decide by_omega by_omega by_omega by_omega, hG.rL]; rfl
    · rw [R 130325 130058 by_decide by_omega by_omega by_omega by_omega, hG.rbase 28 by_omega]; rfl
    · rw [R 130326 130085 by_decide by_omega by_omega by_omega by_omega, hG.rUP]; rfl
    · tauto
    · rw [R 130328 130014 by_decide by_omega by_omega by_omega by_omega, hG.rN]; rfl
    · rw [R 130345 130017 by_decide by_omega by_omega by_omega by_omega, hG.rL]; rfl
    · rw [R 130601 130033 by_decide by_omega by_omega by_omega by_omega, hG.rbase 3 by_omega]; rfl
    · rw [R 130602 130084 by_decide by_omega by_omega by_omega by_omega, hG.rbase 54 by_omega]; rfl
    · rw [R 130603 130070 by_decide by_omega by_omega by_omega by_omega, hG.rbase 40 by_omega]; rfl
    · rw [R 130604 130017 by_decide by_omega by_omega by_omega by_omega, hG.rL]; rfl
    · rw [R 130605 130036 by_decide by_omega by_omega by_omega by_omega, hG.rbase 6 by_omega]; rfl
    · rw [R 130606 130074 by_decide by_omega by_omega by_omega by_omega, hG.rbase 44 by_omega]; rfl
    · rw [R 130607 130078 by_decide by_omega by_omega by_omega by_omega, hG.rbase 48 by_omega]; rfl
    · rw [R 130608 130011 by_decide by_omega by_omega by_omega by_omega, hG.rμ]; rfl
    · tauto
    · rw [R 130632 130041 by_decide by_omega by_omega by_omega by_omega, hG.rbase 11 by_omega]; rfl
    · rw [R 130633 130047 by_decide by_omega by_omega by_omega by_omega, hG.rbase 17 by_omega]; rfl
    · rw [R 130634 130056 by_decide by_omega by_omega by_omega by_omega, hG.rbase 26 by_omega]; rfl
    · rw [R 130635 130059 by_decide by_omega by_omega by_omega by_omega, hG.rbase 29 by_omega]; rfl
    · rw [R 130636 130058 by_decide by_omega by_omega by_omega by_omega, hG.rbase 28 by_omega]; rfl
    · rw [R 130650 130075 by_decide by_omega by_omega by_omega by_omega, hG.rbase 45 by_omega]; rfl
    · rw [R 130651 130073 by_decide by_omega by_omega by_omega by_omega, hG.rbase 43 by_omega]; rfl
    · rw [R 130652 130074 by_decide by_omega by_omega by_omega by_omega, hG.rbase 44 by_omega]; rfl
    · rw [R 130653 130078 by_decide by_omega by_omega by_omega by_omega, hG.rbase 48 by_omega]; rfl
    · rw [R 130654 130030 by_decide by_omega by_omega by_omega by_omega, hG.rbase 0 by_omega]; rfl
    · rw [R 130655 130059 by_decide by_omega by_omega by_omega by_omega, hG.rbase 29 by_omega]; rfl
    · rw [R 130674 130016 by_decide by_omega by_omega by_omega by_omega, hG.rs]; rfl
    · rw [R 130675 130011 by_decide by_omega by_omega by_omega by_omega, hG.rμ]; rfl
    · rw [R 130680 130037 by_decide by_omega by_omega by_omega by_omega, hG.rbase 7 by_omega]; rfl
    · rw [hk23 _ by_omega by_omega by_omega, h681]; rfl
    · rw [R 130682 130014 by_decide by_omega by_omega by_omega by_omega, hG.rN]; rfl
    · rw [R 130692 130069 by_decide by_omega by_omega by_omega by_omega, hG.rbase 39 by_omega]; rfl
    · rw [R 130694 130067 by_decide by_omega by_omega by_omega by_omega, hG.rbase 37 by_omega]; rfl
    · rw [R 130695 130068 by_decide by_omega by_omega by_omega by_omega, hG.rbase 38 by_omega]; rfl
    · rw [R 130696 130023 by_decide by_omega by_omega by_omega by_omega, hG.rV]; rfl
    · rw [R 130697 130021 by_decide by_omega by_omega by_omega by_omega, hG.rO]; rfl
    · rw [R 130698 130039 by_decide by_omega by_omega by_omega by_omega, hG.rbase 9 by_omega]; rfl
    · rw [R 130700 130076 by_decide by_omega by_omega by_omega by_omega, hG.rbase 46 by_omega]; rfl
  · unfold RegRG at hr
    rw [kk3 _ by_omega by_omega by_omega by_omega]
    exact h2 r (fun p hp h => by
      have := (show ∀ p ∈ regCopies, 130300 ≤ p.1 ∧ p.1 ≤ 130889 by decide) p hp; omega)
end proofs
theorem BTree.PreInv.pre_inj {R : BTree} {pre slot : ℕ → ℕ} (hR : R.OK)
    (hP : R.PreInv pre slot R.n) {g h : ℕ} (hg : g < R.n) (hh : h < R.n) (he : pre g = pre h) :
    g = h := by
  have s1 := BTree.one_le_card_sub (R := R) hg
  have s2 := BTree.one_le_card_sub (R := R) hh
  have a1 := (hP.anc_iff hR hg hh).mpr ⟨le_of_eq he, by_omega⟩
  have a2 := (hP.anc_iff hR hh hg).mpr ⟨le_of_eq he.symm, by_omega⟩
  exact hR.anc_antisymm hh hg a1 a2
theorem div_succ_eq {a k : ℕ} (hk : 0 < k) (h : a % k ≠ k - 1) : ztdf / k = a / k := by
  apply Nat.succ_div_of_not_dvd
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have := Nat.mod_lt a hk
  have hk1 : k ≠ 1 := by_omega
  rw [Nat.one_mod_eq_one.mpr hk1, Nat.mod_eq_of_lt by_omega]
  omega

/-- Adjacent levels off the boundary levels are in one slab. -/
theorem div_eq_of_adj {a b k : ℕ} (hk : 0 < k) (h1 : b ≤ a + 1) (h2 : a ≤ b + 1)
    (ha : a % k ≠ k - 1) (hb : b % k ≠ k - 1) : a / k = b / k := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [show b = a + 1 by omega, div_succ_eq hk ha]
  · zuzx
  · rw [show a = b + 1 by omega, div_succ_eq hk hb]
variable {W : ℕ}
set_option maxHeartbeats 8000000 in
/-- **The initial driver invariant.** -/
theorem dinv_init {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face ztdbz = f} {C : CoTree ztqc} {R : BTree} {first : Fin g.μ → Fin g.N}
    {preE slot : ℕ → ℕ} {upT : ℕ → ℕ} {cs : ℕ} {m : ℕ → ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT g.k' cs ztmol g.A0 g.U W m)
    (hhead : ∀ d : Fin g.N, T.level ztbyq ≤ T.level ztbmc + 1)
    (hk : 0 < g.k') (hcs : cs < g.k') (_hkμ : g.k' ≤ g.μ)
    (hlv : ∀ l, l < g.μ → LvOK g m cs l)
    (hpos : ∀ v, v < g.μ → m ztczp =
      if blkOf g.μ ztwnn ztuq
        ztup v < g.μ then
      plPos g.μ (blkOf g.μ ztwnn ztuq
        ztup) (fun v => m (g.base 29 + m (g.base 0 + v))) v else g.μ)
    (hact : ∀ v, v < g.μ → blkOf g.μ ztwnn ztuq
        ztup v < g.μ →
      m (g.base 43 + plPos g.μ (blkOf g.μ ztwnn ztuq
        ztup) (fun v => m (g.base 29 + m (g.base 0 + v))) v) = v)
    (hdf : ∀ v, v < g.μ → m ztvz = 0)
    (hstk : segL g.s g.μ (blkOf g.μ ztwnn ztuq
        ztup) g.μ = stkList m (g.base 46) (segL g.s g.μ
        (blkOf g.μ ztwnn ztuq
        ztup) g.μ).length) :
    DInv M T g.k' cs ztmol m (segL g.s g.μ (blkOf g.μ ztwnn
      ztuq ztup) g.μ)
      (finL g.s g.μ (blkOf g.μ ztwnn ztuq
        ztup)) ∅ 0 := by
  set bo := blkOf g.μ ztwnn ztuq
    ztup with hbo
  set key : ℕ → ℕ := fun v => m ztzfz with hkey
  have hN : (ssOf g).N = g.N := rfl
  -- the key is the preorder of the first dart
  have hkeyv : ∀ v : Fin g.μ, key v = preE zthws := fun v => by
    zuoqr
    have h1 : m ztbrk = first v := hSF.first v
    zvmwp; exact hSF.pre _ (first v).2
  have hinj : ztflk := fun v w hv hw h => by
    have e := (hkeyv ztbbl).symm.trans (h.trans (hkeyv ztdxo))
    have hn := hSF.R_n
    have := BTree.PreInv.pre_inj hSF.R_ok hSF.R_pre by_omega
      by_omega e
    have hf : first ztbbl = first ztdxo := Fin.ext this
    have := congrArg M.vert hf
    rw [hSF.vert_first, hSF.vert_first] at this
    grind
  -- the blocks
  have hlev : ∀ v (hv : v < g.μ), m ztjc = T.level ztbbl := fun v hv => hSF.lev ztbbl
  have hbo_eq : ∀ v (hv : v < g.μ), bo v = if ztwul % g.k' < g.k' - 1 then
      ztwul / g.k' else g.μ := fun v hv => by
    obtain ⟨-, -, h35, h36⟩ := hlv _ (hSF.lev_lt ztbbl)
    zuocl; rw [hlev v hv, h36, h35]
    split_ifs <;> simp_all
  have hdivlt : ∀ l, l < g.μ → ztetu / g.k' < g.μ := fun l hl => by
    zulph
    obtain ⟨t, ht⟩ : ∃ t, g.μ = t + 1 := ⟨g.μ - 1, by_omega⟩
    zukwh
    have : t ≤ t * g.k' := Nat.le_mul_of_pos_right _ hk
    omega
  have hbo_lt : ∀ v (hv : v < g.μ), bo v < g.μ ↔ ztwul % g.k' < g.k' - 1 :=
    fun v hv => by
      rw [hbo_eq v hv]
      zus
      · exact ⟨fun _ => h, fun _ => hdivlt _ (by have := hSF.lev_lt ztbbl; omega)⟩
      omega
  have hH : ∀ v, v < g.μ → (v ∈ Hset T cs g.k' ↔ ¬ bo v < g.μ) := fun v hv => by
    rw [hbo_lt v hv]
    simp only [Hset, Finset.mem_filter, Finset.mem_range]
    have := Nat.mod_lt ztwul hk
    constructor
    · omega
    grind
  have hHμ : ∀ v ∈ Hset T cs g.k', v < g.μ := fun v h => by
    simp only [Hset, Finset.mem_filter, Finset.mem_range] at h; omega
  have hslab : ∀ v w, v < g.μ → w < g.μ → bo v < g.μ → bo v = bo w →
      slabN T cs g.k' v = slabN T cs g.k' w := fun v w hv hw hb he => by
    have hb' := hb; zvmxm at hb'
    have e1 := hbo_eq v hv; have e2 := hbo_eq w hw
    rw [ite_eq_left ((hbo_lt v hv).mp hb)] at e1
    rw [ite_eq_left ((hbo_lt w hw).mp hb')] at e2
    simp only [slabN, dite_eq_left hv, dite_eq_left hw]
    omega
  have hedge : ∀ x y, AdjN M x y → x ∉ Hset T cs g.k' → y ∉ Hset T cs g.k' →
      x < g.μ ∧ y < g.μ ∧ bo x = bo y := fun x y hxy hx hy => by
    obtain ⟨d, rfl, rfl⟩ := hxy
    have hxμ := (M.vert d).2; have hyμ := (M.head d).2
    refine ⟨hxμ, hyμ, ?_⟩
    have hx' := (hH _ hxμ).not.mp hx; have hy' := (hH _ hyμ).not.mp hy
    simp only [not_not] at hx' hy'
    rw [hbo_lt _ hxμ] at hx'; rw [hbo_lt _ hyμ] at hy'
    rw [hbo_eq _ hxμ, hbo_eq _ hyμ, ite_eq_left hx', ite_eq_left hy']
    have h1 := hhead d
    have h2 := hhead ztxa
    have e1 : M.head ztxa = M.vert d := by simp [CombMap.head, M.opp_opp]
    have e2 : M.vert ztxa = M.head d := rfl
    zvmws at h2
    simp only [Fin.eta] at hx' hy' ⊢
    exact div_eq_of_adj hk by_omega by_omega by_omega by_omega
  have hsinv := SInv.init (k := g.k') (s := g.s) (μ := g.μ) (bo := bo) (key := key)
    (act := fun i => m (g.base 43 + i)) hinj hact hH hHμ hslab hedge
  refine ⟨hsinv, fun v hv => ?_, fun v hv => by_grind, fun p hp i h1 h2 => ?_,
    fun w hw => ?_, fun p hp => ?_, hstk, fun p hp => ?_⟩
  · show m ztvz = 1 ↔ v ∈ (∅ : Finset ℕ)
    grind
  · zucno
    obtain ⟨v, hv, hbv, rfl⟩ := exists_plPos (key := key) hinj h1 h2
    show m (g.base 44 + m ztmkg) = plPos g.μ bo key v
    grind
  · show m (g.base 44 + w) = g.μ ∨ _
    by_cases hb : bo w < g.μ
    · right
      have e := hpos w hw; rw [ite_eq_left hb] at e
      rw [show (ssOf g).bPOS = g.base 44 from rfl, show (ssOf g).bACT = g.base 43 from rfl, e]
      exact ⟨seg g.μ bo ztvfq, lv_iff.mpr ⟨bo w, hb, rfl⟩, plPos_ge w, plPos_lt hw,
        hact w hw hb⟩
    grind
  · obtain ⟨b, hb, -, rfl⟩ := mem_segL.mp hp
    zukjl
    simp only [seg] at h1 h3
    obtain ⟨v, hv, hbv, rfl⟩ := exists_plPos (key := key) hinj h1 by_omega
    obtain ⟨v', hv', hbv', rfl⟩ := exists_plPos (key := key) hinj by_omega h3
    show m (g.base 29 + m (g.base 0 + m ztmkg)) ≤
      m (g.base 29 + m (g.base 0 + m (g.base 43 + plPos g.μ bo key v')))
    rw [hact v hv by_omega, hact v' hv' by_omega]
    exact key_le_of_plPos (bo := bo) (key := key) hv' by_omega h2
  · zucno
    exact cntLt_le bo g.μ ztds
def flagBody : Stmt := .seq (block [.addN 130891 130033 130890, .loadN 130892 130891,
  .addN 130891 130066 130892, .loadN 130893 130891])
  (.seq ztyzq
  (.instr (.addN 130890 130890 130001)))

/-- **Flag the light levels.** -/
def flagS : Stmt := .seq (.instr (.constN 130890 0)) (.whileLtN 130890 130011 flagBody)

/-- The registers of the flagging. -/
def FlRG (r : ℕ) : Prop := 130890 ≤ r ∧ r ≤ 130899
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
theorem flagS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hlt : ∀ v, v < g.μ → c.nmem ztjc < g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W flagS c c' k ∧ k ≤ 14 * g.μ + 3 ∧ WordsBounded W c' ∧
      PFr FlRG (fun a => g.base 48 ≤ a ∧ a < g.base 48 + g.μ) c c' ∧
      ∀ v, v < g.μ → c'.nmem ztvz =
        if c.nmem ztxxe < 1 then c.nmem ztvz else 1 := by
  zucma
  have b48 := g.base_eq 48
  set Am : ℕ → Prop := fun a => g.base 48 ≤ a ∧ a < g.base 48 + g.μ with hAm
  unfold flagS
  have e1 := Exec.constN (P := P) hw 130890 0 by_omega
  set c1 := { c with nreg := upd c.nreg 130890 0 } with hc1
  have f1 : PFr FlRG Am c c1 :=
    ⟨fun r hr => by simp only [c1, Machine.upd_other _ _ _ (show r ≠ 130890 by
        unfold FlRG at hr; omega)], rfl, rfl, rfl, fun a _ => rfl⟩
  have hG1 : ztido := hG.frame (fun r hr => f1.1 r ztkvd)
  obtain ⟨c', k, e, hk', hw', hi', hn', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130890) (rn := 130011) (body := flagBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130890 = j ∧ c'.nreg 130011 = g.μ ∧
      PFr FlRG Am c c' ∧
      ∀ v, v < g.μ → c'.nmem ztvz = if j ≤ v then c.nmem ztvz else
        if c.nmem ztxxe < 1 then c.nmem ztvz else 1)
    g.μ 12 zthd
    (fun j c3 hj ⟨hw3, hi3, hn3, hf3, hm3⟩ => by
      have hG3 : ztkzy := hG.frame (fun r hr => hf3.1 r (by
        unfold GRReg at hr; unfold FlRG; omega))
      have r33 := hG3.rbase 3 by_omega; have r66 := hG3.rbase 36 by_omega
      have r78 := hG3.rbase 48 by_omega; have r1 := hG3.one
      zufvi
      have ml : c3.nmem zthxl = c.nmem zthxl := hf3.2.2.2.2 _ by_omega
      have mh : c3.nmem ztcey =
          c.nmem ztcey := hf3.2.2.2.2 _ by_omega
      obtain ⟨c4, k4, e4, hk4, hw4, h93, h90, h4r, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
          (block [.addN 130891 130033 130890, .loadN 130892 130891,
            .addN 130891 130066 130892, .loadN 130893 130891]) c3 c4 k4 ∧ k4 = 4 ∧
          WordsBounded W c4 ∧ c4.nreg 130893 = c.nmem ztcey ∧
          c4.nreg 130890 = j ∧ (∀ r, ¬ FlRG r → c4.nreg r = c3.nreg r) ∧ c4.nmem = c3.nmem ∧
          c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
        exec_block
        · grind
        · config_simp; rw [r66, r33, hi3, ml]; omega
        · refine ⟨rfl, ‹_›, by config_simp; zunlp, by_tauto,
            fun r hr => ?_, rfl, rfl, rfl, rfl⟩
          zujpg
          repeat (rw [Machine.upd_other _ _ _ by_omega])
      have r1' : ztizd := by zuoia; exact r1
      have r78' : c4.nreg 130078 = g.base 48 := by zuoia; omega
      obtain ⟨c5, k5, e5, hk5, hw5, h5r, h590, hm5, hrr5, hrm5, ho5⟩ : ∃ c5 k5, Exec P W
          ztyzq
          c4 c5 k5 ∧ k5 ≤ 4 ∧ WordsBounded W c5 ∧ (∀ r, ¬ FlRG r → c5.nreg r = c4.nreg r) ∧
          c5.nreg 130890 = j ∧
          c5.nmem = (if c.nmem ztcey < 1 then c4.nmem else
            upd c4.nmem ztlpf 1) ∧
          c5.rreg = c4.rreg ∧ c5.rmem = c4.rmem ∧ c5.output = c4.output := by
        by_cases hp : c4.nreg 130893 < c4.nreg 130001
        · refine ⟨c4, 0 + 1, .ifLtN_true hp ztpsa, by_omega, hw4, fun r _ => rfl, h90, ?_,
            rfl, rfl, rfl⟩
          grind
        · obtain ⟨c6, k6, e6, hk6, hw6, h6r, h690, hm6, hrr6, hrm6, ho6⟩ : ∃ c6 k6, Exec P W
              ztepj c4 c6 k6 ∧ k6 = 2 ∧
              WordsBounded W c6 ∧ (∀ r, ¬ FlRG r → c6.nreg r = c4.nreg r) ∧
              c6.nreg 130890 = j ∧ c6.nmem = upd c4.nmem ztlpf 1 ∧
              c6.rreg = c4.rreg ∧ c6.rmem = c4.rmem ∧ c6.output = c4.output := by
            exec_block
            · omega
            · refine ⟨rfl, ‹_›, fun r hr => ?_, by config_simp; omega,
                by grind, rfl, rfl, rfl⟩
              zujpg
              repeat (rw [Machine.upd_other _ _ _ by_omega])
          refine ⟨c6, k6 + 2, .ifLtN_false hp e6, by_omega, hw6, h6r, h690, ?_, hrr6, hrm6, ho6⟩
          grind
      have e7 := Exec.addN (P := P) hw5 130890 130890 130001 (by
        zunrj; omega)
      refine ⟨_, k4 + zttqk, .seq e4 ztspz, by_omega, e7.wb_right, ?_, ?_, ?_, ?_⟩
      · zuvz
        zunrj
      · simp only [Machine.upd_other _ _ _ (show (130011 : ℕ) ≠ 130890 by omega)]
        rw [h5r _ ztcul, h4r _ ztcul]; omega
      · refine hf3.trans ⟨fun r hr => ?_, by_grind,
          by grind, by_grind, fun a ha => ?_⟩
        · zubi
          rw [Machine.upd_other _ _ _ (by unfold FlRG at hr; omega), h5r r hr, h4r r hr]
        · zuhqf
          split_ifs
          · rfl
          · zuigp
      · zuml
        zuhqf
        by_cases hvj : v = j
        · subst hvj
          rw [ite_eq_right (show ¬ (v + 1 ≤ v) by omega)]
          by_cases hL : c.nmem ztxxe < 1
          · grind
          · rw [ite_eq_right hL, ite_eq_right hL, Machine.upd_same]
        · have e : (if c.nmem ztcey < 1 then c3.nmem else
              upd c3.nmem ztlpf 1) (g.base 48 + v) = c3.nmem (g.base 48 + v) := by
            split_ifs
            · rfl
            · zubc
          grind)
    (j₀ := 0) ⟨e1.wb_right, by_rfl, hG1.rμ, f1, fun v hv => by_rfl⟩ ztbg
  exact ⟨c', 1 + k, .seq e1 e, by_omega, hw', hf', fun v hv => by_simp_all⟩
end proofs
section reach
variable {μ k s : ℕ} {H : Finset ℕ} {slab : ℕ → ℕ} {Adj : ℕ → ℕ → Prop} {act : ℕ → ℕ}
  {fin : Finset ztw} {D : Finset ℕ} {nsp : ℕ}

/-- **Reachability stays in a finished segment.** -/
theorem reach_items {G : Env} (hI : SInv μ k s H slab Adj act [] fin D nsp)
    (hstep : ∀ u w, G.Step u w → Adj u w ∧ u ∉ H ∧ u ∉ D ∧ w ∉ H ∧ w ∉ D)
    {p : ℕ × ℕ} (hp : p ∈ fin) {x y : ℕ} (hx : x ∈ items act p) (hr : G.Reach x y) :
    y ∈ items act p := by
  induction hr with
  | refl => exact hx
  | tail _ hst ih =>
    rename_i b c'
    obtain ⟨hadj, h1, h2, h3, h4⟩ := hstep _ _ hst
    obtain ⟨q, hq, hbq, hcq⟩ := hI.edge _ _ hadj h1 h2 h3 h4
    zudme
    · simp_all
    · exact absurd (Finset.disjoint_left.mp (hI.disj q p hq ztvcj hqp) hbq) (not_not.mpr ih)

/-- **A label class has at most `s` vertices.** -/
theorem class_card {G : Env} (hI : SInv μ k s H slab Adj act [] fin D nsp)
    (hstep : ∀ u w, G.Step u w → Adj u w ∧ u ∉ H ∧ u ∉ D ∧ w ∉ H ∧ w ∉ D)
    {lab : ℕ → ℕ} {X : Finset ℕ} (hX : ∀ v ∈ X, v < μ ∧ v ∉ H ∧ v ∉ D)
    (hlab : ∀ x ∈ X, ∀ y ∈ X, lab x = lab y → G.Reach x y) (l : ℕ) :
    (X.filter zthhf).card ≤ s := by
  by_cases hne : (X.filter zthhf).Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    simp only [Finset.mem_filter] at hx0
    obtain ⟨hμ0, hH0, hD0⟩ := hX x0 hx0.1
    obtain ⟨p, hp, hxp⟩ := hI.cover x0 hμ0 hH0 hD0
    have hpf : p ∈ fin := hp.resolve_left by_simp
    have hsub : X.filter zthhf ⊆ items act p := fun v hv => by
      simp only [Finset.mem_filter] at hv
      exact reach_items hI hstep hpf hxp (hlab x0 hx0.1 v hv.1 (hx0.2.trans hv.2.symm))
    calc _ ≤ (items act p).card := Finset.card_le_card hsub
      _ = len p := items_card (hI.inj p hp)
      _ ≤ s := hI.small p hpf
  simp_all
end reach

/-- The light residue. -/
theorem mod_light {l k ρ : ℕ} (hk : 0 < k) (hρ : ρ < k) :
    (l + ztqsf) % k = k - 1 ↔ l % k = ρ := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show k - 1 - ρ < k by omega)]
  have h := Nat.mod_lt l hk
  generalize l % k = r at h ⊢
  by_cases hr : r + ztqsf < k
  · rw [Nat.mod_eq_of_lt hr]; omega
  · zuzu

/-- **The least frequent residue class is small.** -/
theorem minres_card {μ k ρ : ℕ} {f : ℕ → ℕ} (_hk : 0 < k) (hf : ∀ v, v < μ → f v < k)
    (hmin : ∀ r, r < k → cntBelow f μ ρ ≤ cntBelow f μ r) : k * cntBelow f μ ρ ≤ μ := by
  have hsum : ∑ r ∈ Finset.range k, cntBelow f μ r = μ := by
    rw [sum_cntBelow]; unfold cntLt
    rw [Finset.filter_true_of_mem (fun v hv => hf v ztuyp)]; simp
  calc k * cntBelow f μ ρ = ∑ _r ∈ Finset.range k, cntBelow f μ ρ := by_simp
    _ ≤ ∑ r ∈ Finset.range k, cntBelow f μ r :=
        Finset.sum_le_sum (fun r hr => hmin r (Finset.mem_range.mp hr))
    _ = μ := hsum

/-- **The size of `D*`.** -/
theorem dstar_bound {μ k k' s D H : ℕ} (hk : 1 ≤ k) (hμ : 0 < μ) (hμk : μ ≤ k ^ 3)
    (hk' : k' = min k μ) (hs : s = min ztjzf μ) (hD : s * D ≤ 6 * k' * μ)
    (hH : k' * H ≤ μ) : D + H ≤ 7 * k ^ 2 := by
  rcases Nat.le_total k μ with hkμ | hkμ
  · have e : ztskb := by_omega
    zugig
    have hH' : H ≤ k' ^ 2 := by
      have : k' * H ≤ k' * k' ^ 2 := by
        linarith
      exact Nat.le_of_mul_le_mul_left this by_omega
    have hD' : D ≤ 6 * k' ^ 2 := by
      rcases Nat.le_total ztjzf μ with h | h
      · rw [hs, min_eq_left h] at hD
        have : k' * k' * D ≤ k' * k' * ztput := by
          calc k' * k' * D ≤ 6 * k' * μ := hD
            _ ≤ 6 * k' * k' ^ 3 := Nat.mul_le_mul_left _ hμk
            _ = k' * k' * ztput := by_ring
        exact Nat.le_of_mul_le_mul_left this (Nat.mul_pos by_omega by_omega)
      · rw [hs, min_eq_right h] at hD
        have : μ * D ≤ μ * ztstz := by
          grind
        have := Nat.le_of_mul_le_mul_left this hμ
        linarith
    omega
  · have e : k' = μ := by_omega
    zugig
    have hs' : s = k' := by zvmyz; exact min_eq_right (Nat.le_mul_of_pos_left _ hμ)
    rw [hs'] at hD
    have hD' : D ≤ 6 * k' := by
      have : k' * D ≤ k' * ztstz := by
        grind
      zulxe
    have hH' : H ≤ 1 := by
      have : k' * H ≤ k' * 1 := by_omega
      zulxe
    have : k ≤ k ^ 2 := by_nlinarith
    omega

/-- The cluster size is at most `k²`. -/
theorem s_le_sq {μ k k' s : ℕ} (hk' : k' = min k μ) (hs : s = min ztjzf μ) : s ≤ k ^ 2 := by
  have h1 : k' ≤ k := by_omega
  have h2 : s ≤ k' * k' := by_omega
  have : k' * k' ≤ k * k := Nat.mul_le_mul h1 h1
  linarith
