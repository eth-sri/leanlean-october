module

public import Chazelle.Core.ShootCutPath
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# WP-G, part 22: the main loop

* `Uof`: the unwrapped position of a walk vertex in the lap from `U₀`; `resid_gap`: the gap
  between two positions less than a lap apart, read from their residues;
* `uStep_exec`: the piece `uPc` through the uncounted block, from `2m + 6` to `6`;
* `setFlag_exec`; `CoreRegs.of_frame'`;
* `LoopI`: the invariant of the main loop; `loopBody_exec`: one iteration; `mainLoop_exec`:
  the whole loop, from the first walk vertex `U₀` to the final one `F` (`F - U₀ < 2m + 7`).
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-! ## Unwrapped positions -/

/-- The unwrapped position of the residue `c` in the lap from `U₀`. -/
def Uof (U₀ n c : ℕ) : ℕ := U₀ + (c + n - U₀ % n) % n

theorem add_mod_split {n U D : ℕ} (hn : 0 < n) (hD : D < n) :
    (U + D) % n = if U % n + D < n then U % n + D else U % n + D - n := by
  have hU := Nat.mod_lt U hn
  rw [Nat.add_mod, Nat.mod_eq_of_lt hD]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem Uof_eq {U₀ n U : ℕ} (hn : 0 < n) (h0 : U₀ ≤ U) (h1 : U < U₀ + n) :
    Uof U₀ n (U % n) = U := by
  unfold Uof
  have e := add_mod_split (U := U₀) hn (show U - U₀ < n by omega)
  rw [show U₀ + (U - U₀) = U by omega] at e
  rw [e]
  have ha := Nat.mod_lt U₀ hn
  split_ifs with h
  · rw [show U₀ % n + (U - U₀) + n - U₀ % n = (U - U₀) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show U₀ % n + (U - U₀) - n + n - U₀ % n = U - U₀ by omega, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The gap between two positions** less than a lap apart. -/
theorem resid_gap {n U F : ℕ} (hn : 0 < n) (hU : U < F) (hF : F < U + n) :
    U % n ≠ F % n ∧
      F = U + (if U % n < F % n then F % n - U % n else n - U % n + F % n) := by
  have e := add_mod_split (U := U) hn (show F - U < n by omega)
  rw [show U + (F - U) = F by omega] at e
  have ha := Nat.mod_lt U hn
  split_ifs at e with h
  · rw [e]; constructor
    · omega
    · rwo [ite_eq_left (by omega)]
  · rw [e]; constructor
    · omega
    · rwo [ite_eq_right (by omega)]

/-! ## The piece through the uncounted block -/

/-- The piece from the top `2m + 6` through the uncounted block to the walk vertex `6`. -/
def uPc (m : ℕ) : Pc := ⟨⟨2 * m + 6, 0⟩, ⟨6, 0⟩, 0, 0, 0, 0, 0⟩

theorem uPc_ok (P : Polygon) (C : Chain) (m₀ : ℕ → ℕ) (h γ : ℕ) : PcOK P C m₀ h γ (uPc C.m) := by
  refine ⟨proper_vtx' P C _, proper_vtx' P C _, by simp [uPc], by simp [uPc],
    Or.inl rfl, fun _ => ?_, fun h1 => by simp [uPc] at h1⟩
  have := wt_U_to_six C (Qof P) (n := P.n) (x := ⟨2 * C.m + 6, 0⟩) (proper_vtx' P C _)
    (Or.inr rfl)
  simp [uPc, key_hgt0] at this ⊢
  rwo [this]

/-- **The step through the uncounted block.** -/
theorem uStep_exec {P : Polygon} {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop}
    {I : List Pc → Config → Prop} (hE : EmitOK P W emit A₀ Pv I K) {ps : List Pc} {m : ℕ}
    (d : Config) (hw : WordsBounded W d) (h32 : d.nreg 150032 = 2 * m + 6)
    (h96 : d.nreg 150096 = 6) (hI : I ps d) (hpv : Pv (uPc m)) :
    ∃ d' k, Exec P W (uStep emit) d d' k ∧ k ≤ K + 7 ∧ I (ps ++ [uPc m]) d' ∧
      d'.nreg 150040 = 6 ∧ (∀ r, Keep r → r ≠ 150040 → d'.nreg r = d.nreg r) ∧
      (∀ a, a < A₀ → d'.nmem a = d.nmem a) := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.copyN 150050 150032, .constN 150051 0, .copyN 150052 150096, .constN 150053 0,
        .constN 150054 0]) d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = 2 * m + 6 ∧ d₁.nreg 150051 = 0 ∧ d₁.nreg 150052 = 6 ∧
      d₁.nreg 150053 = 0 ∧ d₁.nreg 150054 = 0 ∧
      (∀ r, (r < 150050 ∨ 150055 ≤ r) → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩
    all_goals first | (config_simp; rw [h32]; done) | (config_simp; rw [h96]; done) |
      (config_simp; done) | skip
    simp [upd]; split_ifs <;> first | rfl | omega
  have fr₁ : FrameB Scr d d₁ := exec_frameB e₁ (by decide)
  have hR : PcRegs d₁ (uPc m) := ⟨v50, v51, v52, v53, v54, fun h => by simp [uPc] at h⟩
  obtain ⟨d₂, k₂, e₂, hk₂, hI₂, kp, mem₂⟩ := hE.run _ (uPc m) d₁ e₁.wb_right (hE.stable _ _ _ hI fr₁) hR hpv
  have q96 : d₂.nreg 150096 = 6 := by
    rw [kp _ (by ufo Keep), r₁ _ (by omega), h96]
  have e₃ := Exec.copyN (P := P) e₂.wb_right 150040 150096
  refine ⟨_, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ e₃), by omega,
    hE.stable _ _ _ hI₂ (exec_frameB e₃ (by decide)), by config_simp; rw [q96],
    fun r hr h1 => ?_, fun a ha => ?_⟩
  · config_simp
    rw [upd_other _ _ _ h1, kp r hr, r₁ r (by ufo Keep at hr)]
  · config_simp; rw [mem₂ a ha, m₁]

/-- **The loop flag**: `150042 := [c ≠ f]`. -/
theorem setFlag_exec {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W setFlag d d' k ∧ k ≤ 5 ∧
      d'.nreg 150042 = (if d.nreg 150040 = d.nreg 150041 then 0 else 1) ∧
      (∀ x, x ≠ 150042 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  unfold setFlag
  by_cases h1 : d.nreg 150040 < d.nreg 150041
  · refine spec_ifLtN_true h1 (spec_instr (Exec.constN hw _ _ (by omega)) fun _ =>
      ⟨by omega, ?_, fun x hx => by simp [hx], rfl⟩)
    config_simp; rw [ite_eq_right (by omega)]
  · by_cases h2 : d.nreg 150041 < d.nreg 150040
    · refine spec_ifLtN_false h1 (spec_ifLtN_true h2 (spec_instr (Exec.constN hw _ _ (by omega))
        fun _ => ⟨by omega, ?_, fun x hx => by simp [hx], rfl⟩))
      config_simp; rw [ite_eq_right (by omega)]
    · refine spec_ifLtN_false h1 (spec_ifLtN_false h2 (spec_instr (Exec.constN hw _ _
        (by omega)) fun _ => ⟨by omega, ?_, fun x hx => by simp [hx], rfl⟩))
      config_simp; rw [ite_eq_left (by omega)]

theorem CoreRegs.of_frame' {P : Polygon} {C : Chain} {H : Host} {Hh MD h γ mode : ℕ}
    {s e : WPos} {m₀ : ℕ → ℕ} {c c' : Config} (R : CoreRegs P C H Hh MD h γ mode s e m₀ c)
    (hk : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → r ≠ 150042 → c'.nreg r = c.nreg r)
    (h90 : c'.nreg 150090 = 0) (h91 : c'.nreg 150091 = 1) (h92 : c'.nreg 150092 = 2)
    (h93 : c'.nreg 150093 = 3) (h96 : c'.nreg 150096 = 6) :
    CoreRegs P C H Hh MD h γ mode s e m₀ c' := by
  have k : ∀ r, 150000 ≤ r → r < 150040 ∨ (150042 < r ∧ r < 150044) ∨ r = 150041 →
      c'.nreg r = c.nreg r := fun r h1 h2 => hk r h1 (by omega) (by omega) (by omega)
  exact ⟨⟨(k _ (by norm_num) (by norm_num)).trans R.chain.h21,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h22,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h23,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h26,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h28,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h29, h91, h93, h96⟩,
    (k _ (by norm_num) (by norm_num)).trans R.h00, (k _ (by norm_num) (by norm_num)).trans R.h01,
    (k _ (by norm_num) (by norm_num)).trans R.h02, (k _ (by norm_num) (by norm_num)).trans R.h03,
    (k _ (by norm_num) (by norm_num)).trans R.h04, (k _ (by norm_num) (by norm_num)).trans R.h09,
    (k _ (by norm_num) (by norm_num)).trans R.h13, (k _ (by norm_num) (by norm_num)).trans R.h20,
    (k _ (by norm_num) (by norm_num)).trans R.h27, (k _ (by norm_num) (by norm_num)).trans R.h31,
    (k _ (by norm_num) (by norm_num)).trans R.h32, (k _ (by norm_num) (by norm_num)).trans R.h33,
    (k _ (by norm_num) (by norm_num)).trans R.h34, (k _ (by norm_num) (by norm_num)).trans R.h35,
    (k _ (by norm_num) (by norm_num)).trans R.h36, h90, h92⟩

end

end ShootCut

end Chazelle.Core
