module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterStageC1

/-!
# WP-I, part 50: stage C2 — the residue counts and the lightest residue

* `cntS`: `RCNT[r] = #{v < μ : LEV[v] % k' = r}` (slot `34`, after a zero fill of `k'` cells);
* `argS`: `ρ` (register `130836`) with `RCNT[ρ]` least among `RCNT[0 … k')`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- One vertex of the count: `RCNT[RES[LEV[v]]] += 1`. -/
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

section
variable (f : ℕ → ℕ) (j r : ℕ)
theorem cntBelow_succ :
    cntBelow f (j + 1) r = cntBelow f j r + if f j = r then 1 else 0 := by
  aesop (add simp [cntBelow, Finset.range_add_one, Finset.filter_insert]) (add safe (by omega))

theorem cntBelow_le : cntBelow f j r ≤ j := by
  core_grind


end

/-- One residue of the minimum search. -/
def argBody : Stmt := .seq (block [.addN 130837 130064 130834, .loadN 130837 130837])
  (.seq (.ifLtN 130837 130835 (block [.copyN 130835 130837, .copyN 130836 130834]) .skip)
    (.instr (.addN 130834 130834 130001)))

/-- **The lightest residue** `ρ` (register `130836`). -/
def argS : Stmt := .seq (block [.constN 130834 0, .addN 130835 130011 130001, .constN 130836 0])
  (.whileLtN 130834 130015 argBody)

/-- The registers of the minimum search. -/
def ARG (r : ℕ) : Prop := 130834 ≤ r ∧ r ≤ 130837

section proofs

variable {P : Polygon} {W : ℕ}

section
variable {g : GV} {c : Config} (hw : WordsBounded W c) (hG : GR g c) (hk : 0 < g.k') (hkμ : g.k' ≤ g.μ)
include hw hG hk hkμ
theorem rcS_exec {lev : ℕ → ℕ} (hlev : ∀ v, v < g.μ → c.nmem (g.base 3 + v) = lev v)
    (hlt : ∀ v, v < g.μ → lev v < g.μ)
    (hres : ∀ l, l < g.μ → c.nmem (g.base 33 + l) = l % g.k') (hW : g.END ≤ W) :
    ∃ c' k, Exec P W rcS c c' k ∧ k ≤ 11 * g.μ + 5 * g.k' + 12 ∧ WordsBounded W c' ∧
      PFr StCRG (fun a => g.base 34 ≤ a ∧ a < g.base 34 + g.k') c c' ∧
      ∀ r, r < g.k' → c'.nmem (g.base 34 + r) = cntBelow (fun v => lev v % g.k') g.μ r := by
  have hU := g.U_ge; have hE := g.END_eq; have b33 := g.base_eq 33; have b34 := g.base_eq 34
  have b3 := g.base_eq 3
  unfold rcS
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hz1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 34 (by omega)) hG.rk' hG.zero (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega) (by omega)
  have f1 : PFr StCRG (fun a => g.base 34 ≤ a ∧ a < g.base 34 + g.k') c c1 :=
    hf1.mono (fun r h => by ram_grind) (fun a h => h)
  have e2 := Exec.constN (P := P) hw1 130831 0 (by omega)
  set c2 := { c1 with nreg := upd c1.nreg 130831 0 } with hc2
  have f2 : PFr StCRG (fun a => g.base 34 ≤ a ∧ a < g.base 34 + g.k') c c2 :=
    f1.trans ⟨fun r hr => by ram_simp, rfl, rfl, rfl, fun a _ => rfl⟩
  have hG2 : GR g c2 := hG.frame (fun r hr => f2.1 r (by grind [GRReg, StCRG]))
  obtain ⟨c', k, e, hk', hw', hi', hn', hf', hm'⟩ := forN (P := P) (W := W)
    (ri := 130831) (rn := 130011) (body := rcBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130831 = j ∧ c'.nreg 130011 = g.μ ∧
      PFr StCRG (fun a => g.base 34 ≤ a ∧ a < g.base 34 + g.k') c c' ∧
      ∀ r, r < g.k' → c'.nmem (g.base 34 + r) = cntBelow (fun v => lev v % g.k') j r)
    g.μ 9 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c3 hj ⟨hw3, hi3, hn3, hf3, hm3⟩ => by
      have hG3 : GR g c3 := hG.frame (fun r hr => hf3.1 r (by
        grind [GRReg, StCRG]))
      have r33 := hG3.rbase 3 (by omega)
      have r63 := hG3.rbase 33 (by omega)
      have r64 := hG3.rbase 34 (by omega)
      have r1 := hG3.one
      have hlj := hlt j hj
      have ml : c3.nmem (g.base 3 + j) = lev j := by
        rw [hf3.2.2.2.2 _ (by omega)]; omega_nf
      have mr : c3.nmem (g.base 33 + lev j) = lev j % g.k' := by
        rw [hf3.2.2.2.2 _ (by omega)]; ram_grind
      have hrk : lev j % g.k' < g.k' := Nat.mod_lt _ hk
      have hcnt := hm3 _ hrk
      have hcle := cntBelow_le (fun v => lev v % g.k') j (lev j % g.k')
      unfold rcBody
      exec_block
      · ram_grind
      · config_simp; grind
      · config_simp; grind
      · config_simp; grind
      · omega_nf
      · refine ⟨le_refl _, ‹_›, by ram_simp, by ram_simp,
          hf3.trans ⟨fun r hr => ?_, rfl, rfl, rfl, fun a ha => ?_⟩, fun r hr => ?_⟩
        · simp only; simp only [StCRG] at hr ⊢
          repeat ram_simp
        · config_simp; rw [r64, r63, r33, hi3, ml, mr, Machine.upd_other _ _ _ (by omega)]
        · config_simp
          rw [r64, r63, r33, hi3, ml, mr, hcnt, r1, Machine.upd_apply, cntBelow_succ]
          grind)
    (j₀ := 0) ⟨e2.wb_right, by simp [c2], by rw [hG2.rμ], f2, fun r hr => by
      grind [cntBelow]⟩ (Nat.zero_le _)
  exact ⟨c', k1 + (1 + k), .seq x1 (.seq e2 e), by omega, hw', hf', hm'⟩

theorem argS_exec {cnt : ℕ → ℕ} (hcnt : ∀ r, r < g.k' → c.nmem (g.base 34 + r) = cnt r)
    (hcle : ∀ r, r < g.k' → cnt r ≤ g.μ) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W argS c c' k ∧ k ≤ 9 * g.k' + 5 ∧ WordsBounded W c' ∧
      PFr StCRG (fun _ => False) c c' ∧ c'.nreg 130836 < g.k' ∧
      ∀ r, r < g.k' → cnt (c'.nreg 130836) ≤ cnt r := by
  have hU := g.U_ge; have hE := g.END_eq; have b34 := g.base_eq 34
  unfold argS
  obtain ⟨c1, k1, e1, hk1, hw1, h34, h35, h36, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 130834 0, .addN 130835 130011 130001, .constN 130836 0]) c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 130834 = 0 ∧ c1.nreg 130835 = g.μ + 1 ∧
      c1.nreg 130836 = 0 ∧ PFr StCRG (fun _ => False) c c1 := by
    exec_block
    all_goals try (config_simp; ram_grind)
    all_goals try omega
    refine ⟨rfl, ‹_›, by config_simp, by config_simp; ram_grind, by config_simp,
      ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩⟩
    simp only; unfold StCRG at hr
    repeat ram_simp
  have hk1' : c1.nreg 130015 = g.k' := (hG.frame (fun r hr => hf1.1 r (by
    grind [GRReg, StCRG]))).rk'
  obtain ⟨c', k, e, hk', hw', hi', hn', hb', hr', hf'⟩ := forN (P := P) (W := W)
    (ri := 130834) (rn := 130015) (body := argBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130834 = j ∧ c'.nreg 130015 = g.k' ∧
      ((j = 0 ∧ c'.nreg 130835 = g.μ + 1 ∧ c'.nreg 130836 = 0) ∨
        (0 < j ∧ c'.nreg 130836 < j ∧ c'.nreg 130835 = cnt (c'.nreg 130836))) ∧
      (∀ r, r < j → c'.nreg 130835 ≤ cnt r) ∧
      PFr StCRG (fun _ => False) c c')
    g.k' 7 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, hst2, hmin2, hf2⟩ => by
      have hG2 : GR g c2 := hG.frame (fun r hr => hf2.1 r (by
        grind [GRReg, StCRG]))
      have r64 := hG2.rbase 34 (by omega)
      have r1 := hG2.one
      have mj : c2.nmem (g.base 34 + j) = cnt j := by
        ram_grind
      have hcj := hcle j hj
      obtain ⟨c3, k3, e3, hk3, hw3, hf3, h37, h3⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130837 130064 130834, .loadN 130837 130837]) c2 c3 k3 ∧ k3 = 2 ∧
          WordsBounded W c3 ∧ PFr ARG (fun _ => False) c2 c3 ∧ c3.nreg 130837 = cnt j ∧
          (∀ r, r ≠ 130837 → c3.nreg r = c2.nreg r) := by
        exec_block
        · ram_grind
        · refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, ?_, fun r hr => ?_⟩
          · simp only; unfold ARG at hr
            repeat ram_simp
          all_goals (ram_simp <;> omega_nf)
      obtain ⟨c4, k4, e4, hk4, hw4, hf4, h4⟩ : ∃ c4 k4, Exec P W
          (.ifLtN 130837 130835 (block [.copyN 130835 130837, .copyN 130836 130834]) .skip)
          c3 c4 k4 ∧ k4 ≤ 3 ∧ WordsBounded W c4 ∧ PFr ARG (fun _ => False) c3 c4 ∧
          (c4.nreg 130834 = j ∧ ((0 < j + 1 ∧ c4.nreg 130836 < j + 1 ∧
            c4.nreg 130835 = cnt (c4.nreg 130836)) ∧
            ∀ r, r < j + 1 → c4.nreg 130835 ≤ cnt r)) := by
        by_cases hp : c3.nreg 130837 < c3.nreg 130835
        · obtain ⟨c5, k5, e5, hk5, hw5, hf5, h5a, h5b, h5c⟩ : ∃ c5 k5, Exec P W
              (block [.copyN 130835 130837, .copyN 130836 130834]) c3 c5 k5 ∧ k5 = 2 ∧
              WordsBounded W c5 ∧ PFr ARG (fun _ => False) c3 c5 ∧ c5.nreg 130835 = cnt j ∧
              c5.nreg 130836 = j ∧ c5.nreg 130834 = j := by
            exec_block
            refine ⟨rfl, ‹_›, ⟨fun r hr => ?_, rfl, rfl, rfl, fun a _ => rfl⟩, ?_, ?_, ?_⟩
            · simp only; unfold ARG at hr
              repeat ram_simp
            all_goals (ram_simp )
          refine ⟨c5, k5 + 1, .ifLtN_true hp e5, by omega, hw5, hf5, h5c, ⟨by omega, by omega,
            by ram_grind⟩, fun r hr => ?_⟩
          ram_grind
        · refine ⟨c3, 0 + 2, .ifLtN_false hp (.skip hw3), by omega, hw3, PFr.refl c3,
            by ram_grind, ?_, fun r hr => ?_⟩
          all_goals grind
      have e6 := Exec.addN (P := P) hw4 130834 130834 130001 (by
        rw [h4.1, hf4.1 _ (by omega_nf), h3 _ (by omega), r1]; omega)
      have hf6 : PFr ARG (fun _ => False) c4
          { c4 with nreg := upd c4.nreg 130834 (c4.nreg 130834 + c4.nreg 130001) } :=
          ⟨fun r hr => by
            simp only [Machine.upd_other _ _ _ (show r ≠ 130834 by
              ram_grind)], rfl, rfl, rfl, fun a _ => rfl⟩
      refine ⟨_, k3 + (k4 + 1), .seq e3 (.seq e4 e6), by omega, e6.wb_right, ?_, ?_, Or.inr ?_,
        ?_, hf2.trans ((hf3.trans (hf4.trans hf6)).mono
          (fun r h => by ram_grind) (fun a h => h))⟩
      · simp only [Machine.upd_same]
        rw [h4.1, hf4.1 _ (by omega_nf), h3 _ (by omega), r1]
      · simp only [Machine.upd_other _ _ _ (show (130015 : ℕ) ≠ 130834 by omega)]
        rw [hf4.1 _ (by omega_nf), h3 _ (by omega)]; exact hn2
      · ram_simp
      · simp only [Machine.upd_other _ _ _ (show (130835 : ℕ) ≠ 130834 by omega)]
        exact h4.2.2)
    (j₀ := 0) ⟨hw1, h34, hk1', Or.inl ⟨rfl, h35, h36⟩, fun r hr => by omega, hf1⟩
    (Nat.zero_le _)
  rcases hb' with h0 | ⟨-, hlt, heq⟩
  · omega
  · exact ⟨c', k1 + k, .seq e1 e, by omega, hw', hf', hlt, fun r hr => by
      omega_nf⟩


end

end proofs

end

end Chazelle.Core.Cluster
