module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvBExpA

/-!
# Down-phase base (D9), RAM: expansion of a host block, part 2 (runs)

A run item `.run a ℓ` of the host is expanded by `runS`: the counter `r212029 = t` runs up to
`ℓ + 1` (`r212028`), the vertex `r212030 = (a + t) mod n` is written (`wrV`) and advanced
cyclically (`runS_exec`).  Also the counted loop with a potential (`forLoopPot`).
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs
open BuildRam (FrameM FrameM.mono FrameM.trans exec_frameM wrM)

@[expose] public section

/-- One step of a run: write the vertex, advance it cyclically, count. -/
def runBody : Stmt := .seq wrV (.seq
  (block [.addN 212030 212030 212000, .addN 212029 212029 212000])
  (.ifLtN 212030 212010 .skip (.instr (.copyN 212030 212001))))

/-- **A run** `(a = r212027, ℓ = r212028)`. -/
def runS : Stmt := .seq
  (block [.addN 212028 212028 212000, .copyN 212029 212001, .copyN 212030 212027])
  (.whileLtN 212029 212028 runBody)

theorem wr_runBody :
    wrM (fun r => decide (r = 212025 ∨ r = 212029 ∨ r = 212030)) runBody = true := ⌖

theorem wr_runTail : wrM Bexp (.seq
    (block [.addN 212030 212030 212000, .addN 212029 212029 212000])
    (.ifLtN 212030 212010 .skip (.instr (.copyN 212030 212001)))) = true := ⌖

theorem wr_runS :
    wrM (fun r => decide (r = 212025 ∨ r = 212028 ∨ r = 212029 ∨ r = 212030)) runS = true := by
  decide

theorem wr_runInit : wrM Bexp
    (block [.addN 212028 212028 212000, .copyN 212029 212001, .copyN 212030 212027]) = true := by
  decide

theorem succ_mod_ite (x n : ℕ) (hn : 0 < n) :
    (x + 1) % n = if x % n + 1 < n then x % n + 1 else 0 := by
  have h := Nat.mod_lt x hn
  Ξ Nat.add_mod
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · Ξ Nat.mod_eq_of_lt h1
    split_ifs with h2
    · exact Nat.mod_eq_of_lt h2
    · have : x % n + 1 = n := ⋄
      Ξ this, Nat.mod_self
  · have : n = 1 := ⋄
    subst this; Θ Nat.mod_one

section loops

variable {P : Polygon} {W : ℕ}

/-- **A counted loop with a potential** `Φ`: the iteration at `j` costs at most
`Φ (j + 1) - Φ j`. -/
theorem forLoopPot {ir nr : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (Φ : ℕ → ℕ) (N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c →
      ∃ c' k, Exec P W body c c' k ∧ Inv (j + 1) c' ∧ k + Φ j ≤ Φ (j + 1))
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W (.whileLtN ir nr body) c c' k ∧ Inv N c' ∧
      k + Φ j ≤ Φ N + 2 * (N - j) + 2 := by
  induction hn : N - j generalizing j c with
  | zero =>
    have hjN : j = N := ⋄
    subst hjN
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    exact ⟨c, 2, .whileLtN_false (by rw [h1, h2]; omega) hw, hc, ⋄⟩
  | succ t ih =>
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    have hlt : j < N := ⋄
    obtain ⟨c₁, k₁, e₁, hI₁, hk₁⟩ := hbody j c hlt hc
    obtain ⟨c', k₂, e₂, hI', hk₂⟩ := ih hI₁ (⋄) (⋄)
    exact ⟨c', k₁ + 2 + k₂, .whileLtN_true (by rw [h1, h2]; exact hlt) e₁ e₂, hI', ⋄⟩

end loops

section exec

variable {P : Polygon} {W : ℕ}

/-- **One step of a run.** -/
theorem runBody_exec {n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ e : Config} {K₀ t a : ℕ}
    (hS : ESt W n PA li L c₀ e (K₀ + t)) (hK : K₀ + t < L.length) (hn : 0 < n)
    (h29 : e.nreg 212029 = t) (h30 : e.nreg 212030 = (a + t) % n)
    (hx : L.getD (K₀ + t) (.vtx 0) = .vtx ((a + t) % n)) :
    ∃ e' k, Exec P W runBody e e' k ∧ k ≤ 12 ∧ ESt W n PA li L c₀ e' (K₀ + t + 1) ∧
      e'.nreg 212029 = t + 1 ∧ e'.nreg 212030 = (a + (t + 1)) % n ∧
      FrameM (fun r => decide (r = 212025 ∨ r = 212029 ∨ r = 212030)) e e' := by
  obtain ⟨e₁, k₁, x₁, hk₁, hS₁, f₁⟩ := wrV_exec (P := P) hS hK (Ρ hx, h30)
  have r29 := (f₁.1 _ (⌖)).trans h29
  have r30 := (f₁.1 _ (⌖)).trans h30
  have hw₁ := hS₁.wb
  have h0 := hS₁.r0
  have h1 := hS₁.r1
  have hrn := hS₁.rn
  have hnW := hrn ▸ hw₁.1 212010
  have hmod := Nat.mod_lt (a + t) hn
  have hLW := hS₁.hW
  have hsucc := succ_mod_ite (a + t) n hn
  obtain ⟨e₂, k₂, x₂, hk₂, h29', h30', h25', hm'⟩ : ∃ e₂ k₂, Exec P W (.seq
      (block [.addN 212030 212030 212000, .addN 212029 212029 212000])
      (.ifLtN 212030 212010 .skip (.instr (.copyN 212030 212001)))) e₁ e₂ k₂ ∧ k₂ ≤ 5 ∧
      e₂.nreg 212029 = t + 1 ∧ e₂.nreg 212030 = (a + (t + 1)) % n ∧
      e₂.nreg 212025 = e₁.nreg 212025 ∧ e₂.nmem = e₁.nmem := by
    refine spec_seq ?_
    exec_block
    · rw [r30, h0]; omega
    · config_simp; rw [r29, h0]; omega
    · Ξ ← Nat.add_assoc, hsucc
      by_cases hlt : (a + t) % n + 1 < n
      · refine spec_ifLtN_true (by config_simp; rw [r30, h0, hrn]; exact hlt) ?_
        refine spec_skip ‹_› ?_
        refine ⟨⋄, ?_, ?_, by config_simp, rfl⟩
        · config_simp; Ξ r29, h0
        · config_simp; simp only [hlt, ↓reduceIte]; Ξ r30, h0
      · refine spec_ifLtN_false (by config_simp; rw [r30, h0, hrn]; exact hlt) ?_
        refine spec_instr (Machine.Exec.copyN ‹_› _ _) fun _ => ?_
        refine ⟨⋄, ?_, ?_, by config_simp, rfl⟩
        · config_simp; Ξ r29, h0
        · config_simp; simp only [hlt, ↓reduceIte]; Ξ h1
  have hS₂ := hS₁.frame x₂.wb_right (exec_frameM x₂ wr_runTail) h25' hm'
  have X := Exec.seq x₁ x₂
  exact ⟨e₂, _, X, ⋄, hS₂, h29', h30', exec_frameM X wr_runBody⟩

/-- **A run**: the points `(a + t) mod n`, `t ≤ ℓ`, are written. -/
theorem runS_exec {n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ e : Config} {K₀ a ℓ : ℕ}
    (hS : ESt W n PA li L c₀ e K₀) (h27 : e.nreg 212027 = a) (h28 : e.nreg 212028 = ℓ)
    (ha : a < n) (hℓ : ℓ < n) (hK : K₀ + (ℓ + 1) ≤ L.length)
    (hx : ∀ t, t ≤ ℓ → L.getD (K₀ + t) (.vtx 0) = .vtx ((a + t) % n)) :
    ∃ e' k, Exec P W runS e e' k ∧ k ≤ 14 * (ℓ + 1) + 5 ∧
      ESt W n PA li L c₀ e' (K₀ + (ℓ + 1)) ∧
      FrameM (fun r => decide (r = 212025 ∨ r = 212028 ∨ r = 212029 ∨ r = 212030)) e e' := by
  have hw := hS.wb
  have h0 := hS.r0
  have h1 := hS.r1
  have hnW : n ≤ W := hS.rn ▸ hw.1 212010
  have hn : 0 < n := ⋄
  obtain ⟨e₁, k₁, x₁, hk₁, h28', h29', h30', h25', hm'⟩ : ∃ e₁ k₁, Exec P W
      (block [.addN 212028 212028 212000, .copyN 212029 212001, .copyN 212030 212027]) e e₁ k₁ ∧
      k₁ ≤ 3 ∧ e₁.nreg 212028 = ℓ + 1 ∧ e₁.nreg 212029 = 0 ∧ e₁.nreg 212030 = a ∧
      e₁.nreg 212025 = e.nreg 212025 ∧ e₁.nmem = e.nmem := by
    exec_block
    · rw [h28, h0]; omega
    · config_simp
      Ξ h28, h0, h1, h27
      exact ⟨⋄, rfl, rfl, rfl⟩
  have hS₁ := hS.frame x₁.wb_right (exec_frameM x₁ wr_runInit) h25' hm'
  let Inv : ℕ → Config → Prop := fun t d => ESt W n PA li L c₀ d (K₀ + t) ∧
    d.nreg 212029 = t ∧ d.nreg 212028 = ℓ + 1 ∧ d.nreg 212030 = (a + t) % n
  have I0 : Inv 0 e₁ := ⟨by simpa using hS₁, h29', h28', by rw [h30', Nat.add_zero,
    Nat.mod_eq_of_lt ha]⟩
  obtain ⟨e', k₂, x₂, ⟨hS', -⟩, hk₂⟩ := DrvR.forLoop (P := P) (W := W) (ir := 212029)
    (nr := 212028) (body := runBody) Inv 12 (ℓ + 1)
    (fun j d ⟨hS, h1, h2, _⟩ => ⟨hS.wb, h1, h2⟩)
    (fun j d hj ⟨hS, h1, h2, h3⟩ => by
      obtain ⟨d', k', x, hk', hS', h29, h30, f⟩ :=
        runBody_exec (P := P) hS (⋄) hn h1 h3 (hx j (⋄))
      exact ⟨d', k', x, ⟨by simpa [Nat.add_assoc] using hS', h29,
        (f.1 _ (⌖)).trans h2, h30⟩, hk'⟩)
    I0 (Nat.zero_le _)
  have X := Exec.seq x₁ x₂
  exact ⟨e', _, X, by rw [Nat.sub_zero] at hk₂; omega, hS', exec_frameM X wr_runS⟩

end exec

end

end DrvB

end Chazelle.Core
