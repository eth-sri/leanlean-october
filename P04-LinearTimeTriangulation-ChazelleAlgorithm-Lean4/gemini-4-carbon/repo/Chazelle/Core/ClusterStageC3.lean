module

public import Chazelle.Core.ClusterStageC2

/-!
# WP-I, part 51: stage C3 — the tables of the levels

With the shift `c = k' - 1 - ρ` (register `130838`), for every level `ℓ < μ`, writing
`t = (ℓ + c) % k'`: `LBOT[ℓ] = ℓ - t` (slot `37`), `LTOP[ℓ] = ℓ + (k' - 1) - t` (slot `38`),
`BLK[ℓ] = (ℓ + c) / k'` (slot `35`), `HL[ℓ] = 1` iff `t = k' - 1` (slot `36`).
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- The four table entries of the level `ℓ`. -/
def lvStore : Stmt := block [.addN 130843 130067 130840, .subN 130844 130840 130841,
  .storeN 130843 130844, .addN 130843 130068 130840, .addN 130844 130840 130839,
  .subN 130844 130844 130841, .storeN 130843 130844, .addN 130843 130065 130840,
  .storeN 130843 130842, .addN 130843 130066 130840]

/-- One level. -/
def lvBody : Stmt := .seq lvStore
  (.seq (.ifLtN 130841 130839 (.instr (.storeN 130843 130009)) (.instr (.storeN 130843 130001)))
  (.seq (.instr (.addN 130841 130841 130001))
  (.seq (.ifLtN 130841 130015 .skip (block [.constN 130841 0, .addN 130842 130842 130001]))
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
  m (g.base 37 + l) = l - (l + c) % g.k' ∧
  m (g.base 38 + l) = l + (g.k' - 1) - (l + c) % g.k' ∧
  m (g.base 35 + l) = (l + c) / g.k' ∧
  m (g.base 36 + l) = if (l + c) % g.k' < g.k' - 1 then 0 else 1

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
theorem lvBody_exec {g : GV} {c2 : Config} (hw2 : WordsBounded W c2) (hG2 : GR g c2)
    (hk : 0 < g.k') (hkμ : g.k' ≤ g.μ) {j cs : ℕ} (hj : j < g.μ) (hc : cs < g.k')
    (h40 : c2.nreg 130840 = j) (h41 : c2.nreg 130841 = (j + cs) % g.k')
    (h42 : c2.nreg 130842 = (j + cs) / g.k') (h39 : c2.nreg 130839 = g.k' - 1)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W lvBody c2 c' k ∧ k ≤ 20 ∧ WordsBounded W c' ∧
      PFr LVRG (LvMem g) c2 c' ∧ c'.nreg 130840 = j + 1 ∧
      c'.nreg 130841 = (j + 1 + cs) % g.k' ∧ c'.nreg 130842 = (j + 1 + cs) / g.k' ∧
      LvOK g c'.nmem cs j ∧
      (∀ a, a ≠ g.base 37 + j → a ≠ g.base 38 + j → a ≠ g.base 35 + j → a ≠ g.base 36 + j →
        c'.nmem a = c2.nmem a) := by
  have hU := g.U_ge; have hE := g.END_eq
  have b35 := g.base_eq 35; have b36 := g.base_eq 36; have b37 := g.base_eq 37
  have b38 := g.base_eq 38; have b39 := g.base_eq 39
  have r65 := hG2.rbase 35 (by omega); have r66 := hG2.rbase 36 (by omega)
  have r67 := hG2.rbase 37 (by omega); have r68 := hG2.rbase 38 (by omega)
  have r1 := hG2.one; have r0 := hG2.zero; have rk := hG2.rk'
  have ht : (j + cs) % g.k' < g.k' := Nat.mod_lt _ hk
  have hb : (j + cs) / g.k' ≤ j + cs := Nat.div_le_self _ _
  obtain ⟨hmod, hdiv⟩ := mod_succ_step hk (j + cs)
  rw [show j + cs + 1 = j + 1 + cs by omega] at hmod hdiv
  unfold lvBody
  -- the stores
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hm3, h43, h40', h41', h42', h39', h1', h0', hk'⟩ :
      ∃ c3 k3, Exec P W lvStore c2 c3 k3 ∧ k3 = 10 ∧ WordsBounded W c3 ∧
      PFr LVRG (LvMem g) c2 c3 ∧
      c3.nmem = upd (upd (upd c2.nmem (g.base 37 + j) (j - (j + cs) % g.k'))
        (g.base 38 + j) (j + (g.k' - 1) - (j + cs) % g.k')) (g.base 35 + j) ((j + cs) / g.k') ∧
      c3.nreg 130843 = g.base 36 + j ∧ c3.nreg 130840 = j ∧
      c3.nreg 130841 = (j + cs) % g.k' ∧ c3.nreg 130842 = (j + cs) / g.k' ∧
      c3.nreg 130839 = g.k' - 1 ∧ c3.nreg 130001 = 1 ∧ c3.nreg 130009 = 0 ∧
      c3.nreg 130015 = g.k' := by
    unfold lvStore
    exec_block
    all_goals try (config_simp; simp only [r65, r66, r67, r68, h40, h41, h39]; omega)
    refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · simp only; unfold LVRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    · unfold LvMem at ha
      config_simp; simp only [r65, r67, r68, h40, h41, h39, h42]
      rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
    all_goals (config_simp; simp only [r65, r66, r67, r68, h40, h41, h39, h42, r1, r0, rk])
  -- the light flag
  set hl := if (j + cs) % g.k' < g.k' - 1 then 0 else 1 with hhl
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hm4, hr4⟩ : ∃ c4 k4, Exec P W
      (.ifLtN 130841 130839 (.instr (.storeN 130843 130009)) (.instr (.storeN 130843 130001)))
      c3 c4 k4 ∧ k4 ≤ 3 ∧ WordsBounded W c4 ∧ PFr LVRG (LvMem g) c3 c4 ∧
      c4.nmem = upd c3.nmem (g.base 36 + j) hl ∧ c4.nreg = c3.nreg := by
    by_cases hp : c3.nreg 130841 < c3.nreg 130839
    · have e := Exec.storeN (P := P) hw3 130843 130009
      refine ⟨_, 1 + 1, .ifLtN_true hp e, by omega, e.wb_right,
        ⟨fun r _ => rfl, rfl, rfl, rfl, fun a ha => ?_⟩, ?_⟩
      · simp only; rw [h43, Machine.upd_other _ _ _ (by unfold LvMem at ha; omega)]
      · rw [h41', h39'] at hp
        refine ⟨?_, rfl⟩
        simp only; rw [h43, h0', hhl, ite_eq_left hp]
    · have e := Exec.storeN (P := P) hw3 130843 130001
      refine ⟨_, 1 + 2, .ifLtN_false hp e, by omega, e.wb_right,
        ⟨fun r _ => rfl, rfl, rfl, rfl, fun a ha => ?_⟩, ?_⟩
      · simp only; rw [h43, Machine.upd_other _ _ _ (by unfold LvMem at ha; omega)]
      · rw [h41', h39'] at hp
        refine ⟨?_, rfl⟩
        simp only; rw [h43, h1', hhl, ite_eq_right hp]
  -- the step of the residue
  have e5 := Exec.addN (P := P) hw4 130841 130841 130001 (by rw [hr4, h41', h1']; omega)
  set c5 := { c4 with nreg := upd c4.nreg 130841 (c4.nreg 130841 + c4.nreg 130001) } with hc5
  have h5t : c5.nreg 130841 = (j + cs) % g.k' + 1 := by simp [c5, hr4, h41', h1']
  have h5r : ∀ r, r ≠ 130841 → c5.nreg r = c3.nreg r := fun r hr => by
    simp only [c5, Machine.upd_other _ _ _ hr, hr4]
  obtain ⟨c6, k6, e6, hk6, hw6, hm6, h6t, h6b, h6r, h6rr, h6rm, h6o⟩ : ∃ c6 k6, Exec P W
      (.ifLtN 130841 130015 .skip (block [.constN 130841 0, .addN 130842 130842 130001])) c5 c6 k6
      ∧ k6 ≤ 4 ∧ WordsBounded W c6 ∧ c6.nmem = c5.nmem ∧ c6.nreg 130841 = (j + 1 + cs) % g.k' ∧
      c6.nreg 130842 = (j + 1 + cs) / g.k' ∧
      (∀ r, r ≠ 130841 → r ≠ 130842 → c6.nreg r = c5.nreg r) ∧ c6.rreg = c5.rreg ∧
      c6.rmem = c5.rmem ∧ c6.output = c5.output := by
    by_cases hp : c5.nreg 130841 < c5.nreg 130015
    · rw [h5t, h5r _ (by omega), hk'] at hp
      refine ⟨c5, 0 + 1, .ifLtN_true (by rw [h5t, h5r _ (by omega), hk']; exact hp) (.skip e5.wb_right),
        by omega, e5.wb_right, rfl, ?_, ?_, fun _ _ _ => rfl, rfl, rfl, rfl⟩
      · rw [h5t, hmod, ite_eq_left hp]
      · rw [h5r _ (by omega), h42', hdiv, ite_eq_left hp]
    · have hp' := hp
      rw [h5t, h5r _ (by omega), hk'] at hp'
      have e7 := Exec.constN (P := P) e5.wb_right 130841 0 (by omega)
      have e8 := Exec.addN (P := P) e7.wb_right 130842 130842 130001 (by
        simp only [Machine.upd_other _ _ _ (show (130842 : ℕ) ≠ 130841 by omega),
          Machine.upd_other _ _ _ (show (130001 : ℕ) ≠ 130841 by omega)]
        rw [h5r _ (by omega), h5r _ (by omega), h42', h1']; omega)
      refine ⟨_, (1 + (1 + 0)) + 2, .ifLtN_false hp (.seq e7 (.seq e8 (.skip e8.wb_right))),
        by omega, e8.wb_right, rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
      · simp only [Machine.upd_other _ _ _ (show (130841 : ℕ) ≠ 130842 by omega),
          Machine.upd_same]
        rw [hmod, ite_eq_right hp']
      · simp only [Machine.upd_same,
          Machine.upd_other _ _ _ (show (130842 : ℕ) ≠ 130841 by omega),
          Machine.upd_other _ _ _ (show (130001 : ℕ) ≠ 130841 by omega)]
        rw [h5r _ (by omega), h5r _ (by omega), h42', h1', hdiv, ite_eq_right hp']
      · simp only [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2]
  have h6l : c6.nreg 130840 = j := by rw [h6r _ (by omega) (by omega), h5r _ (by omega), h40']
  have h61 : c6.nreg 130001 = 1 := by rw [h6r _ (by omega) (by omega), h5r _ (by omega), h1']
  have e9 := Exec.addN (P := P) hw6 130840 130840 130001 (by rw [h6l, h61]; omega)
  have hmfin : ({ c6 with nreg := upd c6.nreg 130840 (c6.nreg 130840 + c6.nreg 130001) } :
      Config).nmem = upd c3.nmem (g.base 36 + j) hl := by
    show c6.nmem = _; rw [hm6, show c5.nmem = c4.nmem from rfl, hm4]
  refine ⟨_, k3 + (k4 + (1 + (k6 + 1))), .seq e3 (.seq e4 (.seq e5 (.seq e6 e9))), by omega,
    e9.wb_right, hf3.trans (hf4.trans ⟨fun r hr => ?_, h6rr, h6rm, h6o, fun a ha => ?_⟩), ?_, ?_, ?_,
    ?_, fun a h1 h2 h3 h4 => ?_⟩
  · unfold LVRG at hr
    simp only [Machine.upd_other _ _ _ (show r ≠ 130840 by omega)]
    rw [h6r _ (by omega) (by omega), h5r _ (by omega), hr4]
  · show c6.nmem a = c4.nmem a; rw [hm6]
  · simp only [Machine.upd_same, h6l, h61]
  · simp only [Machine.upd_other _ _ _ (show (130841 : ℕ) ≠ 130840 by omega)]
    exact h6t
  · simp only [Machine.upd_other _ _ _ (show (130842 : ℕ) ≠ 130840 by omega)]
    exact h6b
  · rw [hmfin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Machine.upd_other _ _ _ (by omega), hm3, Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega), Machine.upd_same]
    · rw [Machine.upd_other _ _ _ (by omega), hm3, Machine.upd_other _ _ _ (by omega),
        Machine.upd_same]
    · rw [Machine.upd_other _ _ _ (by omega), hm3, Machine.upd_same]
    · rw [Machine.upd_same]
  · rw [hmfin, Machine.upd_other _ _ _ h4, hm3, Machine.upd_other _ _ _ h3,
      Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h1]

theorem lvS_exec {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c) (hk : 0 < g.k')
    (hkμ : g.k' ≤ g.μ) {rho : ℕ} (hrho : c.nreg 130836 = rho) (hrk : rho < g.k')
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W lvS c c' k ∧ k ≤ 22 * g.μ + 7 ∧ WordsBounded W c' ∧
      PFr StCRG (LvMem g) c c' ∧ c'.nreg 130838 = g.k' - 1 - rho ∧
      ∀ l, l < g.μ → LvOK g c'.nmem (g.k' - 1 - rho) l := by
  have hU := g.U_ge; have hE := g.END_eq
  set cs := g.k' - 1 - rho with hcs
  have hc : cs < g.k' := by omega
  unfold lvS
  obtain ⟨c1, k1, e1, hk1, hw1, h39, h38, h40, h41, h42, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.subN 130839 130015 130001, .subN 130838 130839 130836, .constN 130840 0,
        .copyN 130841 130838, .constN 130842 0]) c c1 k1 ∧ k1 = 5 ∧ WordsBounded W c1 ∧
      c1.nreg 130839 = g.k' - 1 ∧ c1.nreg 130838 = cs ∧ c1.nreg 130840 = 0 ∧
      c1.nreg 130841 = (0 + cs) % g.k' ∧ c1.nreg 130842 = (0 + cs) / g.k' ∧
      PFr StCRG (LvMem g) c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    · config_simp; rw [hG.rk', hG.one]
    · config_simp; rw [hG.rk', hG.one, hrho]
    · config_simp
    · config_simp; rw [hG.rk', hG.one, hrho, Nat.mod_eq_of_lt hc]
    · config_simp; rw [Nat.div_eq_of_lt hc]
    · simp only; unfold StCRG at hr
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hG1 : GR g c1 := hG.frame (fun r hr => hf1.1 r (by unfold GRReg at hr; unfold StCRG; omega))
  obtain ⟨c', k, e, hk', hw', hi', hn', h41', h42', h39', h38', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130840) (rn := 130011) (body := lvBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130840 = j ∧ c'.nreg 130011 = g.μ ∧
      c'.nreg 130841 = (j + cs) % g.k' ∧ c'.nreg 130842 = (j + cs) / g.k' ∧
      c'.nreg 130839 = g.k' - 1 ∧ c'.nreg 130838 = cs ∧ PFr StCRG (LvMem g) c c' ∧
      ∀ l, l < j → LvOK g c'.nmem cs l)
    g.μ 20 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, ht2, hb2, h392, h382, hf2, hm2⟩ => by
      have hG2 : GR g c2 := hG.frame (fun r hr => hf2.1 r (by
        unfold GRReg at hr; unfold StCRG; omega))
      obtain ⟨c3, k3, e3, hk3, hw3, hf3, h40', h41', h42', hok, hkeep⟩ :=
        lvBody_exec (P := P) hw2 hG2 hk hkμ hj hc hi2 ht2 hb2 h392 hW
      refine ⟨c3, k3, e3, hk3, hw3, h40', by rw [hf3.1 _ (by unfold LVRG; omega)]; exact hn2,
        h41', h42', by rw [hf3.1 _ (by unfold LVRG; omega)]; exact h392,
        by rw [hf3.1 _ (by unfold LVRG; omega)]; exact h382,
        hf2.trans (hf3.mono (fun r h => by simp only [LVRG, StCRG] at h ⊢; omega) (fun a h => h)),
        fun l hl => ?_⟩
      rcases Nat.lt_or_ge l j with h | h
      · have b35 := g.base_eq 35; have b36 := g.base_eq 36; have b37 := g.base_eq 37
        have b38 := g.base_eq 38
        obtain ⟨o1, o2, o3, o4⟩ := hm2 l h
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hkeep _ (by omega) (by omega) (by omega) (by omega)]; exact o1
        · rw [hkeep _ (by omega) (by omega) (by omega) (by omega)]; exact o2
        · rw [hkeep _ (by omega) (by omega) (by omega) (by omega)]; exact o3
        · rw [hkeep _ (by omega) (by omega) (by omega) (by omega)]; exact o4
      · rw [show l = j by omega]; exact hok)
    (j₀ := 0) ⟨hw1, h40, hG1.rμ, h41, h42, h39, h38, hf1, fun l hl => by omega⟩ (Nat.zero_le _)
  exact ⟨c', k1 + k, .seq e1 e, by omega, hw', hf', h38', hm'⟩

end proofs

end

end Chazelle.Core.Cluster
