module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OraclePrepZipSp2

/-!
# Lemma 3.6 (WP-H), preprocessing part 14: the special pairs on the RAM

`spS`: the analyses of the walk vertices `6`, `6 + rT`, `2 m + 6` (`kiS`), then the five guarded
emissions of the special pairs; `spS_exec`: the pairs `zipSp` are appended to the raw arrays.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- The pairs appended so far and the memory outside them. -/
def PInv (m₀ m : ℕ → ℕ) (R1 R2 c₀ : ℕ) (l : List (ℕ × ℕ)) : Prop :=
  PairsAt m (R1 + c₀) (R2 + c₀) l ∧
    ∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + l.length ≤ a ∧ a < R2 + c₀) ∨ R2 + c₀ + l.length ≤ a) →
      m a = m₀ a

theorem PInv.nil (m₀ : ℕ → ℕ) (R1 R2 c₀ : ℕ) : PInv m₀ m₀ R1 R2 c₀ [] :=
  ⟨fun t ht => by simp at ht, fun _ _ => rfl⟩

theorem PInv.step {m₀ m m' : ℕ → ℕ} {R1 R2 c₀ : ℕ} {l L : List (ℕ × ℕ)}
    (h : PInv m₀ m R1 R2 c₀ l) (hR : R1 + c₀ + l.length + L.length ≤ R2)
    (hp : PairsAt m' (R1 + (c₀ + l.length)) (R2 + (c₀ + l.length)) L)
    (hm : ∀ a, (a < R1 + (c₀ + l.length) ∨ (R1 + (c₀ + l.length) + L.length ≤ a ∧
      a < R2 + (c₀ + l.length)) ∨ R2 + (c₀ + l.length) + L.length ≤ a) → m' a = m a) :
    PInv m₀ m' R1 R2 c₀ (l ++ L) := by
  obtain ⟨p, o⟩ := h
  refine ⟨PairsAt.append (PairsAt.congr p fun t ht => ⟨hm _ (Or.inl (by omega)),
    hm _ (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩) (by
      grind), fun a ha => ?_⟩
  grind

/-! ## The guards -/

/-- Guard of the first special pair: `0 < rT`. -/
def g1S : Stmt :=
  .seq (block [.copyN 110299 110231, .copyN 110214 110234, .constN 110245 0])
    (.ifLtN 120028 110050 (.instr (.constN 110245 1)) .skip)

/-- Guard of the second special pair: none. -/
def g2S : Stmt := block [.copyN 110299 110235, .copyN 110214 110238, .constN 110245 1]

/-- Guard of the top pair `6`, `κT`. -/
def g3S : Stmt :=
  .seq (block [.copyN 110299 110232, .copyN 110214 110236, .addN 110246 110233 110237,
      .constN 110245 0])
    (.ifLtN 120028 110050 (.ifLtN 120012 110246 .skip (.instr (.constN 110245 1))) .skip)

/-- Guard of the top pair `κT`, `2 m + 6`. -/
def g4S : Stmt :=
  .seq (block [.copyN 110299 110236, .copyN 110214 110240, .addN 110246 110237 110241,
      .constN 110245 0])
    (.ifLtN 120012 110246 .skip (.instr (.constN 110245 1)))

/-- Guard of the top pair `6`, `2 m + 6`. -/
def g5S : Stmt :=
  .seq (block [.copyN 110299 110232, .copyN 110214 110240, .addN 110246 110233 110241,
      .constN 110245 0])
    (.ifLtN 120012 110246 .skip (.instr (.constN 110245 1)))

/-- The registers written by the guards. -/
def BG (r : ℕ) : Bool :=
  decide (r = 110299) || decide (r = 110214) || decide (r = 110245) || decide (r = 110246)

/-- The result of a guard. -/
def GRes (c c' : Config) (a b g : ℕ) : Prop :=
  FrameB BG c c' ∧ c'.nreg 110299 = a ∧ c'.nreg 110214 = b ∧ c'.nreg 110245 = g

section
variable {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
include hw
theorem g1S_exec {R : ℕ}
    (h6 : c.nreg 120028 = 6) (hR : c.nreg 110050 = 6 + R) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g1S c c' k ∧ k ≤ 6 ∧
      GRes c c' (c.nreg 110231) (c.nreg 110234) (if 0 < R then 1 else 0) := by
  have hwr : wr BG g1S = true := by decide
  suffices H : ∃ c' k, Exec P W g1S c c' k ∧ k ≤ 6 ∧ c'.nreg 110299 = c.nreg 110231 ∧
      c'.nreg 110214 = c.nreg 110234 ∧ c'.nreg 110245 = (if 0 < R then 1 else 0) by
    obtain ⟨c', k, e, hk, a, b, g⟩ := H
    exact ⟨c', k, e, hk, exec_frameB e hwr, a, b, g⟩
  unfold g1S
  refine spec_seq ?_
  exec_block
  · omega
  · by_cases h : 0 < R
    · refine spec_ifLtN_true (by simp_all) ?_
      refine spec_instr (Exec.constN ‹_› _ _ hW) fun _ => ⟨by omega, ?_, ?_, ?_⟩ <;> config_simp
      simp_all
    · refine spec_ifLtN_false (by simp_all) ?_
      refine spec_skip ‹_› ⟨by omega, ?_, ?_, ?_⟩ <;> config_simp
      simp_all

theorem g2S_exec (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g2S c c' k ∧ k ≤ 6 ∧ GRes c c' (c.nreg 110235) (c.nreg 110238) 1 := by
  have hwr : wr BG g2S = true := by decide
  suffices H : ∃ c' k, Exec P W g2S c c' k ∧ k ≤ 6 ∧ c'.nreg 110299 = c.nreg 110235 ∧
      c'.nreg 110214 = c.nreg 110238 ∧ c'.nreg 110245 = 1 by
    obtain ⟨c', k, e, hk, a, b, g⟩ := H
    exact ⟨c', k, e, hk, exec_frameB e hwr, a, b, g⟩
  unfold g2S
  exec_block
  all_goals simp_all


end

/-- A guard from a sum of flags (and optionally `0 < rT`). -/
theorem gSum_exec {P : Polygon} {W : ℕ} {c₁ : Config} {s : Stmt} (hw₁ : WordsBounded W c₁)
    (h0 : c₁.nreg 120012 = 0)
    (hs : s = .ifLtN 120012 110246 .skip (.instr (.constN 110245 1))) (hg : c₁.nreg 110245 = 0)
    (hW : 1 ≤ W) :
    ∃ c₂ k, Exec P W s c₁ c₂ k ∧ k ≤ 3 ∧ (∀ r, r ≠ 110245 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output ∧
      c₂.nreg 110245 = if c₁.nreg 110246 = 0 then 1 else 0 := by
  subst hs
  by_cases h : c₁.nreg 110246 = 0
  · have ht : ¬ c₁.nreg 120012 < c₁.nreg 110246 := by omega
    exact ⟨_, _, .ifLtN_false ht (Exec.constN hw₁ 110245 1 hW), by omega,
      fun r hr => by simp_all, rfl, rfl, rfl, rfl,
      by simp_all⟩
  · have ht : c₁.nreg 120012 < c₁.nreg 110246 := by omega
    exact ⟨_, _, .ifLtN_true ht (.skip hw₁), by omega, fun _ _ => rfl, rfl, rfl, rfl, rfl,
      by simp_all⟩

section
variable {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
include hw
section
variable (h0 : c.nreg 120012 = 0)
include h0
theorem g4S_exec (hb : c.nreg 110237 + c.nreg 110241 ≤ W) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g4S c c' k ∧ k ≤ 8 ∧ GRes c c' (c.nreg 110236) (c.nreg 110240)
      (if c.nreg 110237 + c.nreg 110241 = 0 then 1 else 0) := by
  have hwr : wr BG g4S = true := by decide
  obtain ⟨c₁, k₁, e₁, hk₁, n₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110299 110236,
      .copyN 110214 110240, .addN 110246 110237 110241, .constN 110245 0]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 110299 (c.nreg 110236)) 110214 (c.nreg 110240)) 110246
        (c.nreg 110237 + c.nreg 110241)) 110245 0 := by
    exec_block
    all_goals simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, -, -, -, -, v₂⟩ := gSum_exec (P := P) e₁.wb_right
    (by simp_all) rfl (by simp_all) hW
  have ex : Exec P W g4S c c₂ _ := .seq e₁ e₂
  refine ⟨c₂, _, ex, by omega, exec_frameB ex hwr, ?_, ?_, ?_⟩
  · simp_all
  all_goals (simp_all +zetaDelta )

theorem g5S_exec (hb : c.nreg 110233 + c.nreg 110241 ≤ W) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g5S c c' k ∧ k ≤ 8 ∧ GRes c c' (c.nreg 110232) (c.nreg 110240)
      (if c.nreg 110233 + c.nreg 110241 = 0 then 1 else 0) := by
  have hwr : wr BG g5S = true := by decide
  obtain ⟨c₁, k₁, e₁, hk₁, n₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110299 110232,
      .copyN 110214 110240, .addN 110246 110233 110241, .constN 110245 0]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 110299 (c.nreg 110232)) 110214 (c.nreg 110240)) 110246
        (c.nreg 110233 + c.nreg 110241)) 110245 0 := by
    exec_block
    all_goals simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, -, -, -, -, v₂⟩ := gSum_exec (P := P) e₁.wb_right
    (by simp_all) rfl (by simp_all) hW
  have ex : Exec P W g5S c c₂ _ := .seq e₁ e₂
  refine ⟨c₂, _, ex, by omega, exec_frameB ex hwr, ?_, ?_, ?_⟩
  · simp_all
  all_goals simp_all


end

theorem g3S_exec {R : ℕ}
    (h0 : c.nreg 120012 = 0) (h6 : c.nreg 120028 = 6) (hR : c.nreg 110050 = 6 + R)
    (hb : c.nreg 110233 + c.nreg 110237 ≤ W) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g3S c c' k ∧ k ≤ 10 ∧ GRes c c' (c.nreg 110232) (c.nreg 110236)
      (if 0 < R ∧ c.nreg 110233 + c.nreg 110237 = 0 then 1 else 0) := by
  have hwr : wr BG g3S = true := by decide
  obtain ⟨c₁, k₁, e₁, hk₁, n₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110299 110232,
      .copyN 110214 110236, .addN 110246 110233 110237, .constN 110245 0]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 110299 (c.nreg 110232)) 110214 (c.nreg 110236)) 110246
        (c.nreg 110233 + c.nreg 110237)) 110245 0 := by
    exec_block
    all_goals simp_all
  have w₁ := e₁.wb_right
  have x28 : c₁.nreg 120028 = 6 := by simp_all
  have x50 : c₁.nreg 110050 = 6 + R := by simp_all
  have g299 : c₁.nreg 110299 = c.nreg 110232 := by simp_all
  have g214 : c₁.nreg 110214 = c.nreg 110236 := by simp_all
  have g246 : c₁.nreg 110246 = c.nreg 110233 + c.nreg 110237 := by simp_all
  by_cases hr : 0 < R
  · have ht : c₁.nreg 120028 < c₁.nreg 110050 := by omega
    obtain ⟨c₂, k₂, e₂, hk₂, r₂, -, -, -, -, v₂⟩ := gSum_exec (P := P) w₁
      (by simp_all) rfl (by simp_all) hW
    have ex : Exec P W g3S c c₂ _ := .seq e₁ (.ifLtN_true (e := .skip) ht e₂)
    refine ⟨c₂, _, ex, by omega, exec_frameB ex hwr, ?_, ?_, ?_⟩
    all_goals grind
  · have ht : ¬ c₁.nreg 120028 < c₁.nreg 110050 := by omega
    have ex : Exec P W g3S c c₁ _ := .seq e₁ (.ifLtN_false (t := .ifLtN 120012 110246 .skip
      (.instr (.constN 110245 1))) ht (.skip w₁))
    refine ⟨c₁, _, ex, by omega, exec_frameB ex hwr, g299, g214, ?_⟩
    simp_all

/-! ## The analyses of the three top keys -/


end

/-- Save the analysis of the first key. -/
def cp1 : Stmt := block [.copyN 110230 110223, .copyN 110231 110224, .copyN 110232 110227,
  .copyN 110233 110228]
/-- Save the analysis of the second key. -/
def cp2 : Stmt := block [.copyN 110234 110223, .copyN 110235 110224, .copyN 110236 110227,
  .copyN 110237 110228]
/-- Save the analysis of the third key. -/
def cp3 : Stmt := block [.copyN 110238 110223, .copyN 110239 110224, .copyN 110240 110227,
  .copyN 110241 110228]

/-- **The analyses of `6`, `6 + rT`, `2 m + 6`.** -/
def spA : Stmt :=
  .seq (.instr (.constN 110220 6)) (.seq (.seq kiS cp1) (.seq (.instr (.copyN 110220 110050))
    (.seq (.seq kiS cp2) (.seq (.instr (.copyN 110220 120029)) (.seq kiS cp3)))))

/-- The registers written by `spA`. -/
def BSA (r : ℕ) : Bool := BKI r || decide (r = 110220) || decide (110230 ≤ r ∧ r ≤ 110241)

theorem BSA_keep {r : ℕ} (h : ZKeep r = true ∨ (110242 ≤ r ∧ r ≤ 110299)) : BSA r = false := by
  simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at h
  core_grind

section
variable {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV}
/-- One analysis and its saving. -/
theorem kiCp_exec {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {X : ℕ} (hX : c.nreg 110220 = X)
    (h6 : 6 ≤ X) (h7 : X ≤ 2 * C.m + 6) (cp : Stmt) (b : ℕ)
    (hcp : cp = block [.copyN b 110223, .copyN (b + 1) 110224, .copyN (b + 2) 110227,
      .copyN (b + 3) 110228]) (hb : b = 110230 ∨ b = 110234 ∨ b = 110238) :
    ∃ c' k, Exec P W (.seq kiS cp) c c' k ∧ k ≤ 5500 * (V.L + 1) + 260 ∧ FrameB BSA c c' ∧
      (∀ r, r ≠ b → r ≠ b + 1 → r ≠ b + 2 → r ≠ b + 3 → (r < 110223 ∨ 110228 < r) →
        BKI r = false → c'.nreg r = c.nreg r) ∧
      c'.nreg (b + 3) ≤ 2 ∧
      KInfo C (Qof P) N X (c'.nreg b) (c'.nreg (b + 1)) (c'.nreg (b + 2)) (c'.nreg (b + 3)) := by
  obtain ⟨hL, -, -⟩ := h.mem
  have hA := hL.A
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, j₁, b₁, a₁, s₁, K₁⟩ := kiS_exec hw h hX h6 h7
  subst hcp
  have w₁ := e₁.wb_right
  have KI : KInfo C (Qof P) N X (c₁.nreg 110223) (c₁.nreg 110224) (c₁.nreg 110227)
      (c₁.nreg 110228) := ⟨by omega, by omega, by omega,
    fun hne => by
      grind⟩
  obtain ⟨c₂, k₂, e₂, hk₂, n₂⟩ : ∃ c₂ k₂, Exec P W (block [.copyN b 110223, .copyN (b + 1) 110224,
      .copyN (b + 2) 110227, .copyN (b + 3) 110228]) c₁ c₂ k₂ ∧ k₂ = 4 ∧
      c₂.nreg = upd (upd (upd (upd c₁.nreg b (c₁.nreg 110223)) (b + 1) (c₁.nreg 110224))
        (b + 2) (c₁.nreg 110227)) (b + 3) (c₁.nreg 110228) := by
    rcases hb with rfl | rfl | rfl <;> (exec_block; grind)
  have fr₂ : FrameB BSA c₁ c₂ := by
    rcases hb with rfl | rfl | rfl <;> exact exec_frameB e₂ (by decide)
  have ex := Exec.seq e₁ e₂
  have e0 : c₂.nreg b = c₁.nreg 110223 := by
    rw [n₂]; grind [upd]
  have e1 : c₂.nreg (b + 1) = c₁.nreg 110224 := by
    rw [n₂]; grind [upd]
  have e2' : c₂.nreg (b + 2) = c₁.nreg 110227 := by
    rw [n₂]; grind [upd]
  have e3 : c₂.nreg (b + 3) = c₁.nreg 110228 := by
    rw [n₂]; grind [upd]
  refine ⟨c₂, _, ex, by omega, (FrameB.mono f₁ fun r hr => by core_grind).trans fr₂,
    fun r a1 a2 a3 a4 a5 a6 => ?_, by omega, by grind⟩
  rw [n₂]; simp only [upd]
  ram_grind

theorem ZEnv.of_BSA {c c' : Config}
    (h : ZEnv P W lo C N V c) (f : FrameB BSA c c') : ZEnv P W lo C N V c' :=
  h.stable (fun r hr => f.1 r (BSA_keep (Or.inl hr))) (fun a _ => by rw [f.2.2.1])

theorem spA_exec {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) :
    ∃ c' k, Exec P W spA c c' k ∧ k ≤ 3 * (5500 * (V.L + 1) + 262) ∧ FrameB BSA c c' ∧
      c'.nreg 110233 ≤ 2 ∧ c'.nreg 110237 ≤ 2 ∧ c'.nreg 110241 ≤ 2 ∧
      KInfo C (Qof P) N (6 : ℕ) (c'.nreg 110230) (c'.nreg 110231) (c'.nreg 110232) (c'.nreg 110233) ∧
      KInfo C (Qof P) N (6 + rT C : ℕ) (c'.nreg 110234) (c'.nreg 110235) (c'.nreg 110236)
        (c'.nreg 110237) ∧
      KInfo C (Qof P) N (2 * C.m + 6 : ℕ) (c'.nreg 110238) (c'.nreg 110239) (c'.nreg 110240)
        (c'.nreg 110241) := by
  have hm1 := C.one_le
  have hR := rT_lt C
  -- the first key
  have e₀ := Exec.constN (P := P) hw 110220 6 (by have := h.hW; omega)
  set c₀ : Config := { c with nreg := upd c.nreg 110220 6 } with hc₀
  have f₀ : FrameB BSA c c₀ := exec_frameB e₀ (by decide)
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, r₁, s₁, K₁⟩ := kiCp_exec e₀.wb_right (h.of_BSA f₀) (X := 6)
    (by simp_all) le_rfl (by omega) cp1 110230 rfl (Or.inl rfl)
  have h₁ := (h.of_BSA f₀).of_BSA f₁
  -- the second key
  have e₂ := Exec.copyN (P := P) e₁.wb_right 110220 110050
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 110220 (c₁.nreg 110050) } with hc₂
  have f₂ : FrameB BSA c₁ c₂ := exec_frameB e₂ (by decide)
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, r₃, s₃, K₃⟩ := kiCp_exec e₂.wb_right (h₁.of_BSA f₂)
    (X := 6 + rT C) (by rw [hc₂]; config_simp; exact h₁.pk.k0) (by omega) (by omega) cp2 110234 rfl
    (Or.inr (Or.inl rfl))
  have h₃ := (h₁.of_BSA f₂).of_BSA f₃
  -- the third key
  have e₄ := Exec.copyN (P := P) e₃.wb_right 110220 120029
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 110220 (c₃.nreg 120029) } with hc₄
  have f₄ : FrameB BSA c₃ c₄ := exec_frameB e₄ (by decide)
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, r₅, s₅, K₅⟩ := kiCp_exec e₄.wb_right (h₃.of_BSA f₄)
    (X := 2 * C.m + 6) (by rw [hc₄]; config_simp; exact h₃.pk.tEnd) (by omega) le_rfl cp3 110238 rfl
    (Or.inr (Or.inr rfl))
  have ex : Exec P W spA c c₅ _ := .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))))
  -- the saved values survive
  have keep35 : ∀ r, 110230 ≤ r → r ≤ 110237 → c₅.nreg r = c₃.nreg r := fun r a b => by
    rw [r₅ r (by omega) (by omega) (by omega) (by omega) (by omega) (BKI_keep (Or.inr ⟨by omega,
      by omega⟩)), hc₄]; config_simp; rw [upd_other _ _ _ (by omega)]
  have keep13 : ∀ r, 110230 ≤ r → r ≤ 110233 → c₃.nreg r = c₁.nreg r := fun r a b => by
    rw [r₃ r (by omega) (by omega) (by omega) (by omega) (by omega) (BKI_keep (Or.inr ⟨by omega,
      by omega⟩)), hc₂]; config_simp; rw [upd_other _ _ _ (by omega)]
  grind [Chazelle.Core.SignK.FrameB, Chazelle.Core.OracleR.BSA, Chazelle.Core.OracleR.KInfo, Chazelle.WordsBounded, Chazelle.Core.OracleR.ZEnv, Chazelle.Core.OracleR.BKI]

/-! ## The five emissions -/


end

/-- The registers written by the emissions. -/
def BEm (r : ℕ) : Bool :=
  BG r || decide (r = 110295) || decide (r = 110296) || decide (r = 110215) ||
    decide (110290 ≤ r ∧ r ≤ 110292)

/-- The state of the emissions. -/
structure EmSt (m₀ : ℕ → ℕ) (R1 R2 c₀ : ℕ) (l : List (ℕ × ℕ)) (c : Config) : Prop where
  one : c.nreg 120011 = 1
  zero : c.nreg 120012 = 0
  r1 : c.nreg 110293 = R1
  r2 : c.nreg 110294 = R2
  cnt : c.nreg 110295 = c₀ + l.length
  inv : PInv m₀ c.nmem R1 R2 c₀ l

theorem emitStep_exec {P : Polygon} {W : ℕ} {c c₁ : Config} {m₀ : ℕ → ℕ} {R1 R2 c₀ : ℕ}
    {l : List (ℕ × ℕ)} (hs : EmSt m₀ R1 R2 c₀ l c) {a b g : ℕ} (hw₁ : WordsBounded W c₁)
    (hG : GRes c c₁ a b g) (hroom : R1 + c₀ + l.length + 1 ≤ R2)
    (hRW : R2 + c₀ + l.length + 1 ≤ W) (ha : a + 1 ≤ W) (hb : b + 1 ≤ W) :
    ∃ c₂ k, Exec P W emitG c₁ c₂ k ∧ k ≤ 25 ∧ (∀ r, BEm r = false → c₂.nreg r = c.nreg r) ∧
      (∀ r, BEm r = false → c₂.rreg r = c.rreg r) ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output ∧
      EmSt m₀ R1 R2 c₀ (l ++ (gOpt g a b).toList) c₂ := by
  obtain ⟨f, va, vb, vg⟩ := hG
  have gg : ∀ r, BG r = false → c₁.nreg r = c.nreg r := f.1
  obtain ⟨c₂, k, e, hk, r₂, rr₂, rm₂, o₂, cnt₂, pr₂, mm₂⟩ := emitG_exec (P := P) (R1 := R1)
    (R2 := R2) (c₀ := c₀ + l.length) hw₁
    (by ram_grind) (by ram_grind)
    (by ram_grind) (by ram_grind)
    (by ram_grind) (by omega) (by omega) (by omega)
    (by omega)
  rw [vg, va, vb] at cnt₂ pr₂ mm₂
  have hm₁ : c₁.nmem = c.nmem := f.2.2.1
  have hlen : (gOpt g a b).toList.length ≤ 1 := by grind
  refine ⟨c₂, k, e, hk, fun r hr => ?_, fun r hr => ?_, by ram_grind,
    by ram_grind, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · grind [BEm, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  · simp only [BEm, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    ram_grind
  · ram_grind
  · ram_grind
  · ram_grind
  · ram_grind
  · grind
  · exact PInv.step hs.inv (by omega) pr₂ (fun x hx => by grind)

theorem fm5 {α : Type} (o1 o2 o3 o4 o5 : Option α) :
    [o1, o2, o3, o4, o5].filterMap id =
      [] ++ o1.toList ++ o2.toList ++ o3.toList ++ o4.toList ++ o5.toList := by
  cases o1 <;> cases o2 <;> cases o3 <;> cases o4 <;> cases o5 <;> rfl

/-- **The five emissions.** -/
def spB : Stmt :=
  .seq g1S (.seq emitG (.seq g2S (.seq emitG (.seq g3S (.seq emitG (.seq g4S (.seq emitG
    (.seq g5S emitG))))))))

/-- The saved values and the constants read by the emissions. -/
structure SpVals (c : Config) (R : ℕ) (v : Fin 12 → ℕ) : Prop where
  val : ∀ i : Fin 12, c.nreg (110230 + i) = v i
  six : c.nreg 120028 = 6
  k0 : c.nreg 110050 = 6 + R

theorem SpVals.congr {c c' : Config} {R : ℕ} {v : Fin 12 → ℕ} (h : SpVals c R v)
    (hr : ∀ r, BEm r = false → c'.nreg r = c.nreg r) : SpVals c' R v :=
  by ram_grind

theorem spB_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {R R1 R2 c₀ : ℕ}
    {v : Fin 12 → ℕ} (hv : SpVals c R v) (hs : EmSt c.nmem R1 R2 c₀ [] c)
    (hroom : R1 + c₀ + 5 ≤ R2) (hRW : R2 + c₀ + 5 ≤ W) (hvW : ∀ i, v i + 1 ≤ W)
    (hs3 : v 3 ≤ 2) (hs7 : v 7 ≤ 2) (hs11 : v 11 ≤ 2) (hW4 : 4 ≤ W) :
    ∃ c' k, Exec P W spB c c' k ∧ k ≤ 200 ∧ (∀ r, BEm r = false → c'.nreg r = c.nreg r) ∧
      (∀ r, BEm r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      EmSt c.nmem R1 R2 c₀ ((spRam R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
        (v 10) (v 11)).filterMap id) c' := by
  have len1 : ∀ o : Option (ℕ × ℕ), o.toList.length ≤ 1 := fun o => by simp_all
  -- 1
  obtain ⟨c₁, k₁, e₁, hk₁, G₁⟩ := g1S_exec (P := P) hw hv.six hv.k0 (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, R₂, rr₂, rm₂, o₂, S₂⟩ := emitStep_exec (P := P) hs e₁.wb_right G₁
    (by grind) (by grind) (by rw [(show c.nreg 110231 = v 1 from hv.val 1)]; exact hvW 1) (by rw [(show c.nreg 110234 = v 4 from hv.val 4)]; exact hvW 4)
  have hv₂ := hv.congr R₂
  rw [(show c.nreg 110231 = v 1 from hv.val 1), (show c.nreg 110234 = v 4 from hv.val 4)] at S₂
  -- 2
  obtain ⟨c₃, k₃, e₃, hk₃, G₃⟩ := g2S_exec (P := P) e₂.wb_right (by omega)
  obtain ⟨c₄, k₄, e₄, hk₄, R₄, rr₄, rm₄, o₄, S₄⟩ := emitStep_exec (P := P) S₂ e₃.wb_right G₃
    (by grind)
    (by grind)
    (by rw [(show c₂.nreg 110235 = v 5 from hv₂.val 5)]; exact hvW 5) (by rw [(show c₂.nreg 110238 = v 8 from hv₂.val 8)]; exact hvW 8)
  have hv₄ := hv₂.congr R₄
  rw [(show c₂.nreg 110235 = v 5 from hv₂.val 5), (show c₂.nreg 110238 = v 8 from hv₂.val 8)] at S₄
  -- 3
  obtain ⟨c₅, k₅, e₅, hk₅, G₅⟩ := g3S_exec (P := P) e₄.wb_right S₄.zero hv₄.six hv₄.k0
    (by rw [(show c₄.nreg 110233 = v 3 from hv₄.val 3), (show c₄.nreg 110237 = v 7 from hv₄.val 7)]; omega) (by omega)
  rw [(show c₄.nreg 110232 = v 2 from hv₄.val 2), (show c₄.nreg 110236 = v 6 from hv₄.val 6), (show c₄.nreg 110233 = v 3 from hv₄.val 3), (show c₄.nreg 110237 = v 7 from hv₄.val 7)] at G₅
  obtain ⟨c₆, k₆, e₆, hk₆, R₆, rr₆, rm₆, o₆, S₆⟩ := emitStep_exec (P := P) S₄ e₅.wb_right G₅
    (by grind)
    (by grind)
    (hvW 2) (hvW 6)
  have hv₆ := hv₄.congr R₆
  -- 4
  obtain ⟨c₇, k₇, e₇, hk₇, G₇⟩ := g4S_exec (P := P) e₆.wb_right S₆.zero
    (by rw [(show c₆.nreg 110237 = v 7 from hv₆.val 7), (show c₆.nreg 110241 = v 11 from hv₆.val 11)]; omega) (by omega)
  rw [(show c₆.nreg 110236 = v 6 from hv₆.val 6), (show c₆.nreg 110240 = v 10 from hv₆.val 10), (show c₆.nreg 110237 = v 7 from hv₆.val 7), (show c₆.nreg 110241 = v 11 from hv₆.val 11)] at G₇
  obtain ⟨c₈, k₈, e₈, hk₈, R₈, rr₈, rm₈, o₈, S₈⟩ := emitStep_exec (P := P) S₆ e₇.wb_right G₇
    (by grind)
    (by grind)
    (hvW 6) (hvW 10)
  have hv₈ := hv₆.congr R₈
  -- 5
  obtain ⟨c₉, k₉, e₉, hk₉, G₉⟩ := g5S_exec (P := P) e₈.wb_right S₈.zero
    (by rw [(show c₈.nreg 110233 = v 3 from hv₈.val 3), (show c₈.nreg 110241 = v 11 from hv₈.val 11)]; omega) (by omega)
  rw [(show c₈.nreg 110232 = v 2 from hv₈.val 2), (show c₈.nreg 110240 = v 10 from hv₈.val 10), (show c₈.nreg 110233 = v 3 from hv₈.val 3), (show c₈.nreg 110241 = v 11 from hv₈.val 11)] at G₉
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, R₁₀, rr₁₀, rm₁₀, o₁₀, S₁₀⟩ := emitStep_exec (P := P) S₈ e₉.wb_right G₉
    (by grind)
    (by grind)
    (hvW 2) (hvW 10)
  have ex : Exec P W spB c c₁₀ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇
    (.seq e₈ (.seq e₉ e₁₀))))))))
  refine ⟨c₁₀, _, ex, by omega, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · grind
  · grind
  · convert S₁₀ using 2
    unfold spRam
    exact fm5 _ _ _ _ _

/-- **The special pairs.** -/
def spS : Stmt := .seq spA spB

/-- The registers written by `spS`. -/
def BSP (r : ℕ) : Bool := BSA r || BEm r

theorem spS_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {R1 R2 c₀ : ℕ} (hR1 : c.nreg 110293 = R1)
    (hR2 : c.nreg 110294 = R2) (hc : c.nreg 110295 = c₀) (hlo : lo ≤ R1)
    (hroom : R1 + c₀ + 5 ≤ R2) (hRW : R2 + c₀ + 5 ≤ W) :
    ∃ c' k, Exec P W spS c c' k ∧ k ≤ 3 * (5500 * (V.L + 1) + 262) + 200 ∧
      (∀ r, BSP r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BSP r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 110295 = c₀ + (zipSp C (Qof P) N).length ∧
      PInv c.nmem c'.nmem R1 R2 c₀ (zipSp C (Qof P) N) ∧ ZEnv P W lo C N V c' := by
  obtain ⟨hL, -, -⟩ := h.mem
  have hA := hL.A
  have hAW : V.A + 1 ≤ W := by
    have a := hL.SB_le; have b := hL.TB_le; have c' := hL.A_lt
    rcases Nat.eq_zero_or_pos V.L with h0 | h0
    all_goals grind
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, s3, s7, s11, K6, KT, K2⟩ := spA_exec hw h
  have h₁ := h.of_BSA f₁
  set v : Fin 12 → ℕ := fun i => c₁.nreg (110230 + i) with hv
  have SV : SpVals c₁ (rT C) v := ⟨fun i => rfl, h₁.pk.six, h₁.pk.k0⟩
  have keep : ∀ r, 110293 ≤ r → r ≤ 110295 → c₁.nreg r = c.nreg r := fun r a b =>
    f₁.1 r (BSA_keep (Or.inr ⟨by omega, by omega⟩))
  have ES : EmSt c₁.nmem R1 R2 c₀ [] c₁ := ⟨h₁.pk.one, h₁.pk.zero,
    by simp_all, by simp_all,
    by simp_all, PInv.nil _ _ _ _⟩
  have hvW : ∀ i, v i + 1 ≤ W := by
    obtain ⟨a0, a1, a2, -⟩ := K6
    obtain ⟨b0, b1, b2, -⟩ := KT
    obtain ⟨d0, d1, d2, -⟩ := K2
    rw [← hA] at a0 a1 a2 b0 b1 b2 d0 d1 d2
    have hW4 := h.hW
    intro i; fin_cases i <;> simp [hv] <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, rm₂, o₂, ES₂⟩ := spB_exec (P := P) e₁.wb_right SV ES
    (by omega) (by omega) hvW s3 s7 s11 (by omega)
  have K6' : KInfo C (Qof P) N 6 (c₁.nreg 110230) (c₁.nreg 110231) (c₁.nreg 110232)
      (c₁.nreg 110233) := by omega
  have KT' : KInfo C (Qof P) N (κT C) (c₁.nreg 110234) (c₁.nreg 110235) (c₁.nreg 110236)
      (c₁.nreg 110237) := by grind [rT_def]
  have K2' : KInfo C (Qof P) N (2 * C.m + 6) (c₁.nreg 110238) (c₁.nreg 110239) (c₁.nreg 110240)
      (c₁.nreg 110241) := by grind
  have heq := spRam_eq h.isNF h.simple K6' KT' K2'
  rw [show (spRam (rT C) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10)
    (v 11)).filterMap id = zipSp C (Qof P) N from heq] at ES₂
  have hm₁ : c₁.nmem = c.nmem := f₁.2.2.1
  rw [hm₁] at ES₂
  refine ⟨c₂, _, .seq e₁ e₂, by omega, fun r hr => ?_, fun r hr => ?_, by ram_grind,
    by ram_grind, ES₂.cnt, ES₂.inv, ?_⟩
  · simp only [BSP, Bool.or_eq_false_iff] at hr
    rw [r₂ r hr.2, f₁.1 r hr.1]
  · simp only [BSP, Bool.or_eq_false_iff] at hr
    rw [rr₂ r hr.2, f₁.2.1 r hr.1]
  · refine h₁.stable (fun r hr => r₂ r ?_) (fun a ha => ?_)
    · simp only [ZKeep, Bool.or_eq_true, decide_eq_true_eq] at hr
      simp [BEm, BG]; omega
    · rw [ES₂.inv.2 a (Or.inl (by omega)), hm₁]

end

end OracleR

end Chazelle.Core
