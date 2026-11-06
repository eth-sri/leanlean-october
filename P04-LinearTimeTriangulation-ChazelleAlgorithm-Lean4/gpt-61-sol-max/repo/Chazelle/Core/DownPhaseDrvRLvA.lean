module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvRLvlSpec
public import Chazelle.Core.DownPhaseDrvRPad
public import Chazelle.Core.DownPhaseDrvRProg
public import Chazelle.Core.Setup

/-!
# Down-phase driver (RAM side): one level, the parameters

`lvPar`: from the setup record (`coreReg 0`, tables of `2^i` and `⌈i/5⌉`) and the level `λ`
(register `210000`), the parameters of the level: `211000` `S`, `211001` `p`, `211002`
`μ = nextLvl λ`, `211003` `⌈βμ⌉`, `211004` `C = 2^μ`, `211006` `γ₀ = 3 · 2^(⌈βμ⌉+10)`,
`211007` `γ_r = 2^(⌈βμ⌉+12)`, `211008` the `LeftInside` bit (normalized from the interior model
descriptor), constants `211014 … 211017` (`1, 3, 0, 2`); the region table `T` (`211009`, three
words per region, `K + 1` regions, `211011`), padded (`padS`); loop registers `211010` (region),
`211012` (total kept), `211013` (largest kept) set to `0` (`lvPar_exec`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The parameters of the level. -/
def lvParA : Stmt := block [
  .copyN 211000 230000, .constN 211014 1, .constN 211015 3, .constN 211016 0, .constN 211017 2,
  .addN 211021 211000 211014, .loadN 211001 211021,
  .constN 211022 4, .addN 211023 211000 211001, .addN 211023 211023 211022,
  .addN 211021 211023 210000, .loadN 211002 211021, .constN 211022 11,
  .addN 211002 211002 211022,
  .addN 211021 211023 211002, .loadN 211003 211021,
  .addN 211024 211000 211017,
  .addN 211021 211024 211002, .loadN 211004 211021,
  .constN 211022 10, .addN 211021 211024 211003, .addN 211021 211021 211022,
  .loadN 211005 211021,
  .addN 211006 211005 211005, .addN 211006 211006 211005,
  .addN 211021 211021 211017, .loadN 211007 211021,
  .addN 211021 210001 211014, .loadN 211025 211021, .constN 211008 0]

section exec

variable {P : Polygon} {W : ℕ}

/-- The registers `lvParA` writes. -/
def Bpar (r : ℕ) : Bool := decide (211000 ≤ r ∧ r < 211030)

theorem wr_lvParA : SignK.wr Bpar lvParA = true := by decide

set_option maxHeartbeats 4000000 in
theorem lvParA_exec (c : Config) (hw : WordsBounded W c) {S n lam MD : ℕ}
    (h0 : c.nreg 230000 = S) (hl : c.nreg 210000 = lam) (h1 : c.nreg 210001 = MD)
    (hS : SetupAt c.nmem S n (c.nreg ALLOC)) (h16 : 16 ≤ lam) (hlp : lam ≤ topGrade n)
    (hMD : MD + 6 ≤ c.nreg ALLOC) (hAW : c.nreg ALLOC ≤ W) (hW : 11 ≤ W) :
    ∃ c' k, Exec P W lvParA c c' k ∧ k = 30 ∧
      c'.nreg 211000 = S ∧ c'.nreg 211001 = topGrade n ∧ c'.nreg 211002 = nextLvl lam ∧
      c'.nreg 211003 = Cost.ceilBeta (nextLvl lam) ∧ c'.nreg 211004 = 2 ^ nextLvl lam ∧
      c'.nreg 211005 = 2 ^ (Cost.ceilBeta (nextLvl lam) + 10) ∧
      c'.nreg 211006 = 3 * 2 ^ (Cost.ceilBeta (nextLvl lam) + 10) ∧
      c'.nreg 211007 = 2 ^ (Cost.ceilBeta (nextLvl lam) + 12) ∧
      c'.nreg 211025 = c.nmem (MD + 1) ∧ c'.nreg 211008 = 0 ∧
      c'.nreg 211014 = 1 ∧ c'.nreg 211015 = 3 ∧ c'.nreg 211016 = 0 ∧ c'.nreg 211017 = 2 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hS0, hS1, hT, hSE⟩ := hS
  set p := topGrade n with hp
  have hμl : nextLvl lam < lam := nextLvl_lt h16
  have hcb : ∀ i, Cost.ceilBeta i = (i + 4) / 5 := Setup.ceilBeta_eq
  have hμ : nextLvl lam = (lam + 4) / 5 + 11 := by core_grind
  have hb12 : Cost.ceilBeta (nextLvl lam) + 12 ≤ nextLvl lam := by grind
  have t1 : c.nmem (S + p + 4 + lam) = Cost.ceilBeta lam := (hT lam (by omega)).2
  have t2 : c.nmem (S + p + 4 + nextLvl lam) = Cost.ceilBeta (nextLvl lam) :=
    (hT _ (by omega)).2
  have t3 : c.nmem (S + 2 + nextLvl lam) = 2 ^ nextLvl lam := (hT _ (by omega)).1
  have t4 : c.nmem (S + 2 + (Cost.ceilBeta (nextLvl lam) + 10)) =
      2 ^ (Cost.ceilBeta (nextLvl lam) + 10) := (hT _ (by omega)).1
  have t5 : c.nmem (S + 2 + (Cost.ceilBeta (nextLvl lam) + 12)) =
      2 ^ (Cost.ceilBeta (nextLvl lam) + 12) := (hT _ (by omega)).1
  have hpW : p + 1 ≤ W := by omega
  have w5 := hw.2 (S + 2 + (Cost.ceilBeta (nextLvl lam) + 12))
  rw [t5] at w5
  have hpow : 2 ^ (Cost.ceilBeta (nextLvl lam) + 12) = 4 * 2 ^ (Cost.ceilBeta (nextLvl lam) + 10) := by
    ring_nf 
  have hμ' : Cost.ceilBeta lam + 11 = nextLvl lam := rfl
  have w3 := hw.2 (S + 2 + nextLvl lam)
  rw [t3] at w3
  
  
  
  
  have t4' : c.nmem (S + 2 + Cost.ceilBeta (nextLvl lam) + 10) =
      2 ^ (Cost.ceilBeta (nextLvl lam) + 10) := by
    omega
  have t5' : c.nmem (S + 2 + Cost.ceilBeta (nextLvl lam) + 10 + 2) =
      2 ^ (Cost.ceilBeta (nextLvl lam) + 12) := by
    omega
  unfold lvParA
  exec_block
  all_goals try (config_simp; (try simp only [h0, hl, h1, hS1, t1, hμ', t2, t3, t4', t5']); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    config_simp <;> (try simp only [h0, hl, h1, hS1, t1, hμ', t2, t3, t4', t5']); (try omega)

/-- The `LeftInside` bit, normalized: `1` iff the word is `1`. -/
def lvParB : Stmt :=
  .ifLtN 211025 211017 (.ifLtN 211016 211025 (.instr (.constN 211008 1)) .skip) .skip

/-- The table of the regions (three words per region) and the loop registers. -/
def lvParC : Stmt :=
  block [.copyN 211009 9999, .addN 211011 210003 211014, .addN 211026 211011 211011,
    .addN 211026 211026 211011, .addN 9999 9999 211026, .constN 211010 0, .constN 211012 0,
    .constN 211013 0]

theorem lvParB_exec (c : Config) (hw : WordsBounded W c) (h16 : c.nreg 211016 = 0)
    (h17 : c.nreg 211017 = 2) (h08 : c.nreg 211008 = 0) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W lvParB c c' k ∧ k ≤ 4 ∧ c'.nreg 211008 ≤ 1 ∧
      (c'.nreg 211008 = 1 ↔ c.nreg 211025 = 1) ∧
      (∀ r, r ≠ 211008 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lvParB
  by_cases ha : c.nreg 211025 < c.nreg 211017
  · by_cases hb : c.nreg 211016 < c.nreg 211025
    · have e := Exec.constN (P := P) hw 211008 1 hW
      refine ⟨_, _, .ifLtN_true ha (.ifLtN_true hb e), by omega, by simp, ?_, fun r hr => by
        simp [hr], rfl, rfl, rfl, rfl⟩
      ram_simp <;> omega_nf
    · refine ⟨_, _, .ifLtN_true ha (.ifLtN_false hb (.skip hw)), by omega, by omega, ?_,
        fun r _ => rfl, rfl, rfl, rfl, rfl⟩
      omega
  · refine ⟨_, _, .ifLtN_false ha (.skip hw), by omega, by omega, ?_, fun r _ => rfl, rfl, rfl,
      rfl, rfl⟩
    omega

/-- The registers `lvParC` writes. -/
def BparC (r : ℕ) : Bool :=
  decide (211009 ≤ r ∧ r ≤ 211013) || decide (r = 211026) || decide (r = 9999)

theorem wr_lvParC : SignK.wr BparC lvParC = true := by decide

theorem lvParC_exec (c : Config) (hw : WordsBounded W c) {K : ℕ} (h03 : c.nreg 210003 = K)
    (h14 : c.nreg 211014 = 1) (hW : c.nreg ALLOC + 3 * (K + 1) ≤ W) :
    ∃ c' k, Exec P W lvParC c c' k ∧ k = 8 ∧ c'.nreg 211009 = c.nreg 9999 ∧
      c'.nreg 211011 = K + 1 ∧ c'.nreg 9999 = c.nreg 9999 + 3 * (K + 1) ∧
      c'.nreg 211010 = 0 ∧ c'.nreg 211012 = 0 ∧ c'.nreg 211013 = 0 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hA : c.nreg 9999 + 3 * (K + 1) ≤ W := hW
  unfold lvParC
  exec_block
  all_goals try (config_simp; (try simp only [h03, h14]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h03, h14]);
    (try omega)

/-- **The parameters of the level** and the region table. -/
def lvPar : Stmt := .seq lvParA (.seq lvParB (.seq lvParC (padS 211009)))

theorem lvPar_exec (c : Config) (hw : WordsBounded W c) {S n lam MD K : ℕ}
    (h0 : c.nreg 230000 = S) (hl : c.nreg 210000 = lam) (h1 : c.nreg 210001 = MD)
    (h03 : c.nreg 210003 = K)
    (hS : SetupAt c.nmem S n (c.nreg ALLOC)) (h16 : 16 ≤ lam) (hlp : lam ≤ topGrade n)
    (hMD : MD + 6 ≤ c.nreg ALLOC) (hAW : c.nreg ALLOC + 3 * (K + 1) ≤ W) (hW : 11 ≤ W) :
    ∃ c' k, Exec P W lvPar c c' k ∧ k ≤ 9 * (K + 1) + 46 ∧
      c'.nreg 211000 = S ∧ c'.nreg 211001 = topGrade n ∧ c'.nreg 211002 = nextLvl lam ∧
      c'.nreg 211003 = Cost.ceilBeta (nextLvl lam) ∧ c'.nreg 211004 = 2 ^ nextLvl lam ∧
      c'.nreg 211006 = 3 * 2 ^ (Cost.ceilBeta (nextLvl lam) + 10) ∧
      c'.nreg 211007 = 2 ^ (Cost.ceilBeta (nextLvl lam) + 12) ∧
      c'.nreg 211008 ≤ 1 ∧ (c'.nreg 211008 = 1 ↔ c.nmem (MD + 1) = 1) ∧
      c'.nreg 211014 = 1 ∧ c'.nreg 211015 = 3 ∧ c'.nreg 211016 = 0 ∧ c'.nreg 211017 = 2 ∧
      c'.nreg 211009 = c.nreg ALLOC ∧ c'.nreg 211011 = K + 1 ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (K + 1) ∧
      c'.nreg 211010 = 0 ∧ c'.nreg 211012 = 0 ∧ c'.nreg 211013 = 0 ∧ WordsBounded W c' ∧
      (∀ q, (q < 211000 ∨ 211030 ≤ q) → q ≠ 210068 → q ≠ 210069 → q ≠ ALLOC →
        c'.nreg q = c.nreg q) ∧
      c'.nmem = c.nmem ∧ Frame {bDownDrv} c c' k := by
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a05, a06, a07, a25, a08, a14, a15, a16, a17,
    m₁, rr₁, rm₁, o₁⟩ :=
    lvParA_exec (P := P) c hw h0 hl h1 hS h16 hlp hMD (by omega) hW
  have g₁ : FrameB Bpar c c₁ := exec_frameB e₁ wr_lvParA
  obtain ⟨c₂, k₂, e₂, hk₂, b08, b08', g₂, m₂, rr₂, rm₂, o₂⟩ :=
    lvParB_exec (P := P) c₁ e₁.wb_right a16 a17 a08 (by omega)
  have u₂ : ∀ r, r ≠ 211008 → Bpar r = false → c₂.nreg r = c.nreg r := fun r h h' =>
    (g₂ r h).trans (g₁.1 r h')
  have q03 : c₂.nreg 210003 = K := by ram_grind
  have q14 : c₂.nreg 211014 = 1 := by grind
  have qA : c₂.nreg 9999 = c.nreg 9999 := u₂ _ (by decide) (by decide)
  have hA9 : c.nreg 9999 + 3 * (K + 1) ≤ W := hAW
  obtain ⟨c₃, k₃, e₃, hk₃, d09, d11, d99, d10, d12, d13, m₃, rr₃, rm₃, o₃⟩ :=
    lvParC_exec (P := P) c₂ e₂.wb_right q03 q14 (by omega_nf)
  have g₃ : FrameB BparC c₂ c₃ := exec_frameB e₃ wr_lvParC
  obtain ⟨c₄, e₄, g₄, rr₄, m₄, rm₄, o₄, w₄⟩ :=
    padS_exec (P := P) (src := 211009) e₃.wb_right (by omega)
      (by omega)
  have v : ∀ r, Bpar r = false → BparC r = false → r ≠ 211008 → r ≠ 210068 → r ≠ 210069 →
      c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 =>
    (g₄ r h4 h5).trans ((g₃.1 r h2).trans (u₂ r h3 h1))
  have k4 : 3 * (c₃.nreg 9999 - c₃.nreg 211009) + 4 = 9 * (K + 1) + 4 := by
    omega
  rw [k4] at e₄
  have ex : Exec P W lvPar c c₄ (k₁ + (k₂ + (k₃ + (9 * (K + 1) + 4)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have w₃ : ∀ r, BparC r = false → c₃.nreg r = c₂.nreg r := g₃.1
  have v32 : ∀ r, BparC r = false → r ≠ 210068 → r ≠ 210069 → c₄.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 => (g₄ r h2 h3).trans (w₃ r h1)
  have hmm : c₄.nmem = c.nmem := by grind
  have hA4 : c₄.nreg 9999 = c.nreg 9999 + 3 * (K + 1) := by
    grind
  have hreg : ∀ q, (q < 211000 ∨ 211030 ≤ q) → q ≠ 210068 → q ≠ 210069 → q ≠ ALLOC →
      c₄.nreg q = c.nreg q := fun q hq h68 h69 hA => v q
    (by grind [Bpar, decide_eq_false_iff_not])
    (by simp only [BparC, Bool.or_eq_false_iff, decide_eq_false_iff_not]; unfold ALLOC at hA; omega)
    (by omega) h68 h69
  refine ⟨c₄, _, ex, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hA4, ?_, ?_, ?_, w₄, hreg, hmm, ?_⟩
  · ram_simp
  · ram_simp
  · ram_simp
  · ram_simp
  · ram_simp
  · ram_simp
  · ram_simp
  · rw [v32 _ (by decide) (by decide) (by decide)]; exact b08
  · rw [v32 _ (by decide) (by decide) (by decide), b08', a25]
  · ram_simp
  · ram_simp
  · ram_simp
  · ram_simp
  · ram_grind
  · grind
  · grind
  · grind
  · grind
  · refine ⟨fun r hr hrA => hreg r ?_ ?_ ?_ hrA, fun r _ => by grind,
      fun a _ => by rw [hmm], fun a _ => by grind, by grind,
      by omega_nf,
      by omega_nf⟩
    all_goals grind [Finset.mem_singleton, bandOf, bDownDrv]

end exec

end

end DrvR

end Chazelle.Core
