module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ClusterStageB2S

/-!
# WP-I, part 49: stage C1 — the halving table, the powers of two and the residues

* `halfS`: `HALF[w] = w / 2` for `w ≤ μ` (slot `39`);
* `powS`: `POW[j] = 2 ^ j` for `j < L` (slot `40`);
* `resS`: `RES[ℓ] = ℓ % k'` for `ℓ < μ` (slot `33`).

Registers `130820 … 130831`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- The registers of stage C. -/
def StCRG (r : ℕ) : Prop := (130150 ≤ r ∧ r ≤ 130154) ∨ (130820 ≤ r ∧ r ≤ 130869)

/-- The registers of the halving step. -/
def HRG (r : ℕ) : Prop := 130820 ≤ r ∧ r ≤ 130823

/-- One entry of the halving table. -/
def halfBody : Stmt := .seq (block [.addN 130823 130069 130820, .storeN 130823 130821])
  (.seq (.ifLtN 130822 130001 (.instr (.constN 130822 1))
    (block [.constN 130822 0, .addN 130821 130821 130001]))
    (.instr (.addN 130820 130820 130001)))

/-- **The halving table.** -/
def halfS : Stmt := .seq (block [.constN 130820 0, .constN 130821 0, .constN 130822 0,
  .addN 130824 130011 130001]) (.whileLtN 130820 130824 halfBody)

/-- One power of two. -/
def powBody : Stmt := block [.addN 130827 130070 130825, .storeN 130827 130826,
  .addN 130826 130826 130826, .addN 130825 130825 130001]

/-- **The powers of two.** -/
def powS : Stmt := .seq (block [.constN 130825 0, .constN 130826 1])
  (.whileLtN 130825 130017 powBody)

/-- One residue. -/
def resBody : Stmt := .seq (block [.addN 130830 130063 130828, .storeN 130830 130829,
  .addN 130829 130829 130001])
  (.seq (.ifLtN 130829 130015 .skip (.instr (.constN 130829 0)))
    (.instr (.addN 130828 130828 130001)))

/-- **The residues.** -/
def resS : Stmt := .seq (block [.constN 130828 0, .constN 130829 0])
  (.whileLtN 130828 130011 resBody)

section proofs

variable {P : Polygon} {W : ℕ}

theorem halfS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W halfS c c' k ∧ k ≤ 11 * g.μ + 20 ∧ WordsBounded W c' ∧
      PFr StCRG (fun a => g.base 39 ≤ a ∧ a < g.base 39 + (g.μ + 1)) c c' ∧
      ∀ w, w ≤ g.μ → c'.nmem (g.base 39 + w) = w / 2 := by
  have hU := g.U_ge; have hE := g.END_eq; have b39 := g.base_eq 39
  unfold halfS
  obtain ⟨c1, k1, e1, hk1, hw1, h20, h21, h22, h24, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 130820 0, .constN 130821 0, .constN 130822 0, .addN 130824 130011 130001])
      c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 130820 = 0 ∧ c1.nreg 130821 = 0 ∧
      c1.nreg 130822 = 0 ∧ c1.nreg 130824 = g.μ + 1 ∧
      PFr StCRG (fun a => g.base 39 ≤ a ∧ a < g.base 39 + (g.μ + 1)) c c1 := by
    exec_block
    all_goals try (config_simp; rw [hG.rμ, hG.one]; omega)
    all_goals try omega
    refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp,
      by config_simp; rw [hG.rμ, hG.one], ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    simp only; unfold StCRG at hr
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  obtain ⟨c', k, e, hk, hw', hi', hn', h21', h22', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130820) (rn := 130824) (body := halfBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130820 = j ∧ c'.nreg 130824 = g.μ + 1 ∧
      c'.nreg 130821 = j / 2 ∧ c'.nreg 130822 = j % 2 ∧
      PFr StCRG (fun a => g.base 39 ≤ a ∧ a < g.base 39 + (g.μ + 1)) c c' ∧
      ∀ w, w < j → c'.nmem (g.base 39 + w) = w / 2)
    (g.μ + 1) 7 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, hh2, hp2, hf2, hm2⟩ => by
      have hG2 : GR g c2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      have r69 := hG2.rbase 39 (by omega)
      have r1 := hG2.one
      set Am : ℕ → Prop := fun a => g.base 39 ≤ a ∧ a < g.base 39 + (g.μ + 1) with hAm
      obtain ⟨c3, k3, e3, hk3, hw3, hf3, hm3, h20, h21, h22, h1⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130823 130069 130820, .storeN 130823 130821]) c2 c3 k3 ∧ k3 = 2 ∧
          WordsBounded W c3 ∧ PFr HRG Am c2 c3 ∧
          c3.nmem = upd c2.nmem (g.base 39 + j) (j / 2) ∧
          c3.nreg 130820 = j ∧ c3.nreg 130821 = j / 2 ∧ c3.nreg 130822 = j % 2 ∧
          c3.nreg 130001 = 1 := by
        exec_block
        · rw [r69, hi2]; omega
        · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [Machine.upd_other _ _ _ (show r ≠ 130823 by
              unfold HRG at hr; omega)]
          · config_simp; rw [r69, hi2, Machine.upd_other _ _ _ (by simp only [hAm] at ha; omega)]
          · config_simp; rw [r69, hi2, hh2]
          · config_simp; exact hi2
          · config_simp; exact hh2
          · config_simp; exact hp2
          · config_simp; exact r1
      -- the parity step
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, hm4, h20', h21', h22', h1'⟩ : ∃ c4 k4, Exec P W
          (.ifLtN 130822 130001 (.instr (.constN 130822 1))
            (block [.constN 130822 0, .addN 130821 130821 130001])) c3 c4 k4 ∧ k4 ≤ 4 ∧
          WordsBounded W c4 ∧ PFr HRG Am c3 c4 ∧ c4.nmem = c3.nmem ∧ c4.nreg 130820 = j ∧
          c4.nreg 130821 = (j + 1) / 2 ∧ c4.nreg 130822 = (j + 1) % 2 ∧
          c4.nreg 130001 = 1 := by
        by_cases hp : c3.nreg 130822 < c3.nreg 130001
        · have e := Exec.constN (P := P) hw3 130822 1 (by omega)
          rw [h22, h1] at hp
          refine ⟨_, 1 + 1, .ifLtN_true (by rw [h22, h1]; exact hp) e, by omega, e.wb_right,
            ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, rfl, ?_, ?_, ?_, ?_⟩
          · simp only [Machine.upd_other _ _ _ (show r ≠ 130822 by
              unfold HRG at hr; omega)]
          all_goals config_simp
          · exact h20
          · rw [h21]; omega
          · omega
          · exact h1
        · rw [h22, h1] at hp
          obtain ⟨c5, k5, e5, hk5, hw5, hf5, hm5, h5a, h5b, h5c, h5d⟩ : ∃ c5 k5, Exec P W
              (block [.constN 130822 0, .addN 130821 130821 130001]) c3 c5 k5 ∧ k5 = 2 ∧
              WordsBounded W c5 ∧ PFr HRG Am c3 c5 ∧ c5.nmem = c3.nmem ∧
              c5.nreg 130820 = j ∧ c5.nreg 130821 = (j + 1) / 2 ∧ c5.nreg 130822 = (j + 1) % 2 ∧
              c5.nreg 130001 = 1 := by
            exec_block
            · omega
            · config_simp; rw [h21, h1]; omega
            · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, rfl, ?_, ?_, ?_,
                ?_⟩
              · simp only [Machine.upd_other _ _ _ (show r ≠ 130822 by
                  unfold HRG at hr; omega), Machine.upd_other _ _ _ (show r ≠ 130821 by
                  unfold HRG at hr; omega)]
              all_goals config_simp
              · exact h20
              · rw [h21, h1]; omega
              · omega
              · exact h1
          exact ⟨c5, k5 + 2, .ifLtN_false (by rw [h22, h1]; exact hp) e5, by omega, hw5, hf5, hm5,
            h5a, h5b, h5c, h5d⟩
      have e6 := Exec.addN (P := P) hw4 130820 130820 130001 (by rw [h20', h1']; omega)
      have hf6 : PFr HRG Am c4 { c4 with nreg := upd c4.nreg 130820 (c4.nreg 130820 +
          c4.nreg 130001) } := ⟨fun r hr => by
            simp only [Machine.upd_other _ _ _ (show r ≠ 130820 by
              unfold HRG at hr; omega)], rfl, rfl, rfl, fun a _ => rfl⟩
      refine ⟨_, k3 + (k4 + 1), .seq e3 (.seq e4 e6), by omega, e6.wb_right, ?_, ?_, ?_, ?_,
        hf2.trans ((hf3.trans (hf4.trans hf6)).mono (fun r h => by
          simp only [HRG, StCRG] at h ⊢; omega) (fun a h => h)), fun w hw => ?_⟩
      · simp only [Machine.upd_same, h20', h1']
      · rw [(hf3.trans (hf4.trans hf6)).1 130824 (by unfold HRG; omega)]; exact hn2
      · simp only [Machine.upd_other _ _ _ (show (130821 : ℕ) ≠ 130820 by omega)]
        exact h21'
      · simp only [Machine.upd_other _ _ _ (show (130822 : ℕ) ≠ 130820 by omega)]
        exact h22'
      · show c4.nmem _ = _
        rw [hm4, hm3, Machine.upd_apply]
        split_ifs with h
        · rw [show w = j by omega]
        · exact hm2 w (by omega))
    (j₀ := 0) ⟨hw1, h20, h24, by rw [h21], by rw [h22], hf1, fun w hw => by omega⟩
    (Nat.zero_le _)
  refine ⟨c', k1 + k, .seq e1 e, by omega, hw', hf', fun w hw => hm' w (by omega)⟩

/-- The residue after a step. -/
theorem mod_succ_step {k : ℕ} (hk : 0 < k) (j : ℕ) :
    (j + 1) % k = (if j % k + 1 < k then j % k + 1 else 0) ∧
    (j + 1) / k = (if j % k + 1 < k then j / k else j / k + 1) := by
  have h := Nat.div_add_mod j k
  have hr := Nat.mod_lt j hk
  by_cases h1 : j % k + 1 < k
  · Ξ ite_eq_left h1, ite_eq_left h1
    have e : j + 1 = (j % k + 1) + k * (j / k) := ⋄
    constructor
    · Ξ e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1
    · rw [e, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt h1]; omega
  · Ξ ite_eq_right h1, ite_eq_right h1
    have e : j + 1 = k * (j / k + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    constructor
    · Ξ e, Nat.mul_mod_right
    · Ξ e, Nat.mul_div_cancel_left _ hk

theorem powS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W powS c c' k ∧ k ≤ 6 * g.L + 4 ∧ WordsBounded W c' ∧
      PFr StCRG (fun a => g.base 40 ≤ a ∧ a < g.base 40 + g.L) c c' ∧
      ∀ j, j < g.L → c'.nmem (g.base 40 + j) = 2 ^ j := by
  have hU := g.U_ge; have hE := g.END_eq; have b40 := g.base_eq 40
  have hPU := g.P_le_U; have hLU := g.L_le_U
  unfold powS
  obtain ⟨c1, k1, e1, hk1, hw1, h25, h26, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 130825 0, .constN 130826 1]) c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧
      c1.nreg 130825 = 0 ∧ c1.nreg 130826 = 1 ∧
      PFr StCRG (fun a => g.base 40 ≤ a ∧ a < g.base 40 + g.L) c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, by config_simp, by config_simp, ⟨fun r hr => ?_, rfl, rfl, rfl,
      fun a _ => rfl⟩⟩
    simp only; unfold StCRG at hr
    repeat (rw [Machine.upd_other _ _ _ (⋄)])
  have hL1 : c1.nreg 130017 = g.L := (hG.frame (fun r hr => hf1.1 r (by
    unfold GRReg at hr; unfold StCRG; omega))).rL
  obtain ⟨c', k, e, hk, hw', hi', hn', h26', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130825) (rn := 130017) (body := powBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130825 = j ∧ c'.nreg 130017 = g.L ∧
      c'.nreg 130826 = 2 ^ j ∧
      PFr StCRG (fun a => g.base 40 ≤ a ∧ a < g.base 40 + g.L) c c' ∧
      ∀ i, i < j → c'.nmem (g.base 40 + i) = 2 ^ i)
    g.L 4 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, hp2, hf2, hm2⟩ => by
      have hG2 : GR g c2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      have r70 := hG2.rbase 40 (⋄)
      have r1 := hG2.one
      have hpj : 2 ^ (j + 1) ≤ 2 ^ g.L := Nat.pow_le_pow_right (⋄) hj
      have hpj' : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := ⋆
      unfold powBody
      exec_block
      · rw [r70, hi2]; omega
      · config_simp; rw [hp2]; omega
      · config_simp; rw [hi2, r1]; omega
      · refine ⟨le_refl _, ‹_›, by config_simp; rw [hi2, r1], by config_simp; exact hn2,
          by config_simp; rw [hp2, hpj'], hf2.trans ⟨fun r hr => ?_, rfl, rfl, rfl,
          fun a ha => ?_⟩, fun i hi => ?_⟩
        · simp only; ϴ' StCRG at hr ⊢
          repeat (rw [Machine.upd_other _ _ _ (⋄)])
        · config_simp; Ξ r70, hi2, Machine.upd_other _ _ _ (⋄)
        · config_simp; Ξ r70, hi2, hp2, Machine.upd_apply
          split_ifs with h
          · Ξ show i = j by omega
          · exact hm2 i (⋄))
    (j₀ := 0) ⟨hw1, h25, hL1, by rw [h26]; rfl, hf1, fun i hi => ⋄⟩ (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, ⋄, hw', hf', hm'⟩

/-- The registers of the residue step. -/
def RRG (r : ℕ) : Prop := 130828 ≤ r ∧ r ≤ 130830

theorem resS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c) (hk : 0 < g.k')
    (hkμ : g.k' ≤ g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W resS c c' k ∧ k ≤ 9 * g.μ + 4 ∧ WordsBounded W c' ∧
      PFr StCRG (fun a => g.base 33 ≤ a ∧ a < g.base 33 + g.μ) c c' ∧
      ∀ l, l < g.μ → c'.nmem (g.base 33 + l) = l % g.k' := by
  have hU := g.U_ge; have hE := g.END_eq; have b33 := g.base_eq 33
  unfold resS
  obtain ⟨c1, k1, e1, hk1, hw1, h28, h29, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 130828 0, .constN 130829 0]) c c1 k1 ∧ k1 = 2 ∧ WordsBounded W c1 ∧
      c1.nreg 130828 = 0 ∧ c1.nreg 130829 = 0 ∧
      PFr StCRG (fun a => g.base 33 ≤ a ∧ a < g.base 33 + g.μ) c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, by config_simp, by config_simp, ⟨fun r hr => ?_, rfl, rfl, rfl,
      fun a _ => rfl⟩⟩
    simp only; unfold StCRG at hr
    repeat (rw [Machine.upd_other _ _ _ (⋄)])
  have hμ1 : c1.nreg 130011 = g.μ := (hG.frame (fun r hr => hf1.1 r (by
    unfold GRReg at hr; unfold StCRG; omega))).rμ
  obtain ⟨c', k, e, hk', hw', hi', hn', h29', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130828) (rn := 130011) (body := resBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130828 = j ∧ c'.nreg 130011 = g.μ ∧
      c'.nreg 130829 = j % g.k' ∧
      PFr StCRG (fun a => g.base 33 ≤ a ∧ a < g.base 33 + g.μ) c c' ∧
      ∀ l, l < j → c'.nmem (g.base 33 + l) = l % g.k')
    g.μ 7 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, hr2, hf2, hm2⟩ => by
      have hG2 : GR g c2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      have r63 := hG2.rbase 33 (⋄)
      have r1 := hG2.one
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
        · rw [r63, hi2]; omega
        · config_simp; rw [hr2, r1]; omega
        · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
          · simp only; unfold RRG at hr
            repeat (rw [Machine.upd_other _ _ _ (⋄)])
          · config_simp; Ξ r63, hi2, Machine.upd_other _ _ _ (by simp only [hAm] at ha; omega)
          · config_simp; Ξ r63, hi2, hr2
          · config_simp; exact hi2
          · config_simp; Ξ hr2, r1
          · config_simp; exact r1
          · config_simp; exact rk
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, hm4, h28', h29', h1'⟩ : ∃ c4 k4, Exec P W
          (.ifLtN 130829 130015 .skip (.instr (.constN 130829 0))) c3 c4 k4 ∧ k4 ≤ 3 ∧
          WordsBounded W c4 ∧ PFr RRG Am c3 c4 ∧ c4.nmem = c3.nmem ∧ c4.nreg 130828 = j ∧
          c4.nreg 130829 = (j + 1) % g.k' ∧ c4.nreg 130001 = 1 := by
        by_cases hp : c3.nreg 130829 < c3.nreg 130015
        · refine ⟨c3, 0 + 1, .ifLtN_true hp (.skip hw3), ⋄, hw3, PFr.refl c3, rfl, h28,
            ?_, h1⟩
          Ξ' h29, hk3' at hp; Ξ hmod, ite_eq_left hp, h29
        · have e := Exec.constN (P := P) hw3 130829 0 (⋄)
          refine ⟨_, 1 + 2, .ifLtN_false hp e, ⋄, e.wb_right,
            ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, rfl, ?_, ?_, ?_⟩
          · simp only [Machine.upd_other _ _ _ (show r ≠ 130829 by
              unfold RRG at hr; omega)]
          all_goals config_simp
          · exact h28
          · Ξ' h29, hk3' at hp; Ξ hmod, ite_eq_right hp
          · exact h1
      have e6 := Exec.addN (P := P) hw4 130828 130828 130001 (by rw [h28', h1']; omega)
      have hf6 : PFr RRG Am c4 { c4 with nreg := upd c4.nreg 130828 (c4.nreg 130828 +
          c4.nreg 130001) } := ⟨fun r hr => by
            simp only [Machine.upd_other _ _ _ (show r ≠ 130828 by
              unfold RRG at hr; omega)], rfl, rfl, rfl, fun a _ => rfl⟩
      refine ⟨_, k3 + (k4 + 1), .seq e3 (.seq e4 e6), ⋄, e6.wb_right, ?_, ?_, ?_,
        hf2.trans ((hf3.trans (hf4.trans hf6)).mono (fun r h => by
          ϴ' RRG, StCRG at h ⊢; omega) (fun a h => h)), fun l hl => ?_⟩
      · ϴ Machine.upd_same, h28', h1'
      · rw [(hf3.trans (hf4.trans hf6)).1 130011 (by unfold RRG; omega)]; exact hn2
      · ϴ Machine.upd_other _ _ _ (show (130829 : ℕ) ≠ 130828 by omega)
        exact h29'
      · show c4.nmem _ = _
        Ξ hm4, hm3, Machine.upd_apply
        split_ifs with h
        · Ξ show l = j by omega
        · exact hm2 l (⋄))
    (j₀ := 0) ⟨hw1, h28, hμ1, by rw [h29]; simp, hf1, fun l hl => ⋄⟩ (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, ⋄, hw', hf', hm'⟩

end proofs

end

end Chazelle.Core.Cluster
