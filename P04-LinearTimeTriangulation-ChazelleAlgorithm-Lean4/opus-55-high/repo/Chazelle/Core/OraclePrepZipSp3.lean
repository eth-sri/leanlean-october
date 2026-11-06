module

public import Chazelle.MacT
public import Chazelle.Core.OraclePrepPosRam
public import Chazelle.Core.ClusterLabelStage

section
set_option hygiene false
local macro "zqbho" : tactic => `(tactic| refine ⟨c₂, _, ex, by_omega, exec_frameB ex hwr, ?_, ?_, ?_⟩)
local macro "zqbhp" : tactic => `(tactic| (obtain ⟨c', k, e, hk, a, b, g⟩ := H
                                           exact ⟨c', k, e, hk, exec_frameB e hwr, a, b, g⟩))
set_option hygiene true

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
def PInv (m₀ m : ℕ → ℕ) (R1 R2 c₀ : ℕ) (l : List ztw) : Prop :=
  PairsAt m ztfol ztenu l ∧
    ∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + l.length ≤ a ∧ a < R2 + c₀) ∨ R2 + c₀ + l.length ≤ a) →
      m a = m₀ a
theorem PInv.nil (m₀ : ℕ → ℕ) (R1 R2 c₀ : ℕ) : PInv m₀ m₀ R1 R2 c₀ [] :=
  ⟨fun t ht => by_simp_all, by_omega⟩
theorem PInv.step {m₀ m m' : ℕ → ℕ} {R1 R2 c₀ : ℕ} {l L : List ztw}
    (h : PInv m₀ m R1 R2 c₀ l) (hR : R1 + c₀ + l.length + L.length ≤ R2)
    (hp : PairsAt m' (R1 + zthgi) (R2 + zthgi) L)
    (hm : ∀ a, (a < R1 + zthgi ∨ (R1 + zthgi + L.length ≤ a ∧
      a < R2 + zthgi) ∨ R2 + (c₀ + l.length) + L.length ≤ a) → m' a = m a) :
    PInv m₀ m' R1 R2 c₀ (l ++ L) := by
  obtain ⟨p, o⟩ := h
  refine ⟨PairsAt.append (PairsAt.congr p by_grind) (by
      grind), fun a ha => ?_⟩
  grind

/-! ## The guards -/

/-- Guard of the first special pair: `0 < rT`. -/
def g1S : Stmt :=
  .seq (block [.copyN 110299 110231, .copyN 110214 110234, .constN 110245 0])
    (.ifLtN 120028 110050 ztdrz .skip)

/-- Guard of the second special pair: none. -/
def g2S : Stmt := block [.copyN 110299 110235, .copyN 110214 110238, .constN 110245 1]

/-- Guard of the top pair `6`, `κT`. -/
def g3S : Stmt :=
  .seq (block [.copyN 110299 110232, .copyN 110214 110236, .addN 110246 110233 110237,
      .constN 110245 0])
    (.ifLtN 120028 110050 ztxty .skip)

/-- Guard of the top pair `κT`, `2 m + 6`. -/
def g4S : Stmt :=
  .seq (block [.copyN 110299 110236, .copyN 110214 110240, .addN 110246 110237 110241,
      .constN 110245 0])
    ztxty

/-- Guard of the top pair `6`, `2 m + 6`. -/
def g5S : Stmt :=
  .seq (block [.copyN 110299 110232, .copyN 110214 110240, .addN 110246 110233 110241,
      .constN 110245 0])
    ztxty

/-- The registers written by the guards. -/
def BG (r : ℕ) : Bool :=
  decide (r = 110299) || decide (r = 110214) || decide (r = 110245) || decide (r = 110246)

/-- The result of a guard. -/
def GRes (c c' : Config) (a b g : ℕ) : Prop :=
  FrameB BG c c' ∧ c'.nreg 110299 = a ∧ c'.nreg 110214 = b ∧ c'.nreg 110245 = g
variable {P : Polygon} {W : ℕ} {c : Config}
theorem g1S_exec (hw : WordsBounded W c) {R : ℕ}
    (h6 : c.nreg 120028 = 6) (hR : c.nreg 110050 = 6 + R) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g1S c c' k ∧ k ≤ 6 ∧
      GRes c c' (c.nreg 110231) (c.nreg 110234) ztgkh := by
  have hwr : wr BG g1S = true := by_decide
  suffices H : ∃ c' k, Exec P W g1S c c' k ∧ k ≤ 6 ∧ c'.nreg 110299 = c.nreg 110231 ∧
      c'.nreg 110214 = c.nreg 110234 ∧ c'.nreg 110245 = ztgkh by
    zqbhp
  unfold g1S
  refine spec_seq ?_
  exec_block
  · omega
  · by_cases h : 0 < R
    · zuek
      refine spec_instr (Exec.constN ‹_› _ _ hW) fun _ => ztcbn <;> config_simp
      simp_all
    · zudx
      refine spec_skip ‹_› ztcbn <;> config_simp
      simp_all
theorem g2S_exec (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g2S c c' k ∧ k ≤ 6 ∧ GRes c c' (c.nreg 110235) (c.nreg 110238) 1 := by
  have hwr : wr BG g2S = true := by_decide
  suffices H : ∃ c' k, Exec P W g2S c c' k ∧ k ≤ 6 ∧ c'.nreg 110299 = c.nreg 110235 ∧
      c'.nreg 110214 = c.nreg 110238 ∧ c'.nreg 110245 = 1 by
    zqbhp
  unfold g2S
  exec_block
  · omega
  simp

/-- A guard from a sum of flags (and optionally `0 < rT`). -/
theorem gSum_exec {c₁ : Config} {s : Stmt} (hw₁ : WordsBounded W c₁)
    (h0 : c₁.nreg 120012 = 0)
    (hs : s = .ifLtN 120012 110246 .skip ztdrz) (hg : c₁.nreg 110245 = 0)
    (hW : 1 ≤ W) :
    ∃ c₂ k, Exec P W s c₁ c₂ k ∧ k ≤ 3 ∧ (∀ r, r ≠ 110245 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem ∧ c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output ∧
      c₂.nreg 110245 = if c₁.nreg 110246 = 0 then 1 else 0 := by
  subst hs
  by_cases h : c₁.nreg 110246 = 0
  · have ht : ¬ c₁.nreg 120012 < c₁.nreg 110246 := by_omega
    exact ⟨_, _, .ifLtN_false ht (Exec.constN hw₁ 110245 1 hW), by_omega,
      by simp_all, rfl, rfl, rfl, rfl,
      by simp_all⟩
  · have ht : c₁.nreg 120012 < c₁.nreg 110246 := by_omega
    exact ⟨_, _, .ifLtN_true ht ztekd, by_omega, by_omega, rfl, rfl, rfl, rfl,
      by simp_all⟩
theorem g4S_exec (hw : WordsBounded W c)
    (h0 : c.nreg 120012 = 0) (hb : c.nreg 110237 + c.nreg 110241 ≤ W) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g4S c c' k ∧ k ≤ 8 ∧ GRes c c' ztmfp ztmfq
      (if c.nreg 110237 + c.nreg 110241 = 0 then 1 else 0) := by
  have hwr : wr BG g4S = true := by_decide
  obtain ⟨c₁, k₁, e₁, hk₁, n₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110299 110236,
      .copyN 110214 110240, .addN 110246 110237 110241, .constN 110245 0]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 110299 ztmfp) 110214 ztmfq) 110246
        (c.nreg 110237 + c.nreg 110241)) 110245 0 := by
    exec_block
    · simp_all
    · omega
    simp
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, -, -, -, -, v₂⟩ := gSum_exec (P := P) e₁.wb_right
    by_simp_all rfl by_simp_all hW
  have ex : Exec P W g4S c c₂ _ := .seq e₁ e₂
  zqbho
  · simp_all
  · simp_all
  simp_all
theorem g5S_exec (hw : WordsBounded W c)
    (h0 : c.nreg 120012 = 0) (hb : c.nreg 110233 + c.nreg 110241 ≤ W) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g5S c c' k ∧ k ≤ 8 ∧ GRes c c' ztmfo ztmfq
      (if c.nreg 110233 + c.nreg 110241 = 0 then 1 else 0) := by
  have hwr : wr BG g5S = true := by_decide
  obtain ⟨c₁, k₁, e₁, hk₁, n₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110299 110232,
      .copyN 110214 110240, .addN 110246 110233 110241, .constN 110245 0]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd ztznz 110214 ztmfq) 110246
        (c.nreg 110233 + c.nreg 110241)) 110245 0 := by
    exec_block
    · simp_all
    · omega
    simp
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, -, -, -, -, v₂⟩ := gSum_exec (P := P) e₁.wb_right
    by_simp_all rfl by_simp_all hW
  have ex : Exec P W g5S c c₂ _ := .seq e₁ e₂
  zqbho
  · simp_all
  · simp_all
  simp_all
theorem g3S_exec (hw : WordsBounded W c) {R : ℕ}
    (h0 : c.nreg 120012 = 0) (h6 : c.nreg 120028 = 6) (hR : c.nreg 110050 = 6 + R)
    (hb : c.nreg 110233 + c.nreg 110237 ≤ W) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W g3S c c' k ∧ k ≤ 10 ∧ GRes c c' ztmfo ztmfp
      (if 0 < R ∧ c.nreg 110233 + c.nreg 110237 = 0 then 1 else 0) := by
  have hwr : wr BG g3S = true := by_decide
  obtain ⟨c₁, k₁, e₁, hk₁, n₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110299 110232,
      .copyN 110214 110236, .addN 110246 110233 110237, .constN 110245 0]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd ztznz 110214 ztmfp) 110246
        (c.nreg 110233 + c.nreg 110237)) 110245 0 := by
    exec_block
    · simp_all
    · omega
    simp
  zud
  have x28 : c₁.nreg 120028 = 6 := by_simp_all
  have x50 : c₁.nreg 110050 = 6 + R := by_simp_all
  have g299 : c₁.nreg 110299 = c.nreg 110232 := by_simp_all
  have g214 : c₁.nreg 110214 = c.nreg 110236 := by_simp_all
  have g246 : c₁.nreg 110246 = c.nreg 110233 + c.nreg 110237 := by_simp_all
  by_cases hr : 0 < R
  · have ht : c₁.nreg 120028 < c₁.nreg 110050 := by_omega
    obtain ⟨c₂, k₂, e₂, hk₂, r₂, -, -, -, -, v₂⟩ := gSum_exec w₁
      by_simp_all rfl by_simp_all hW
    have ex : Exec P W g3S c c₂ _ := .seq e₁ ztspm
    zqbho
    · simp_all
    · simp_all
    simp_all
  · have ht : ¬ c₁.nreg 120028 < c₁.nreg 110050 := by_omega
    have ex : Exec P W g3S c c₁ _ := .seq e₁ (.ifLtN_false ht ztwd)
    refine ⟨c₁, _, ex, by_omega, exec_frameB ex hwr, g299, g214, ?_⟩
    simp_all

/-! ## The analyses of the three top keys -/

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
  zubis
  simp [BSA, BKI, BLZ, BTS, BL, Bdir, Bloc, Bcmp, Bk]
  omega

/-- One analysis and its saving. -/
theorem kiCp_exec {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {X : ℕ} (hX : c.nreg 110220 = X)
    (h6 : 6 ≤ X) (h7 : X ≤ 2 * C.m + 6) (cp : Stmt) (b : ℕ)
    (hcp : cp = block [.copyN b 110223, .copyN ztds 110224, .copyN ztub 110227,
      .copyN zthdn 110228]) (hb : b = 110230 ∨ b = 110234 ∨ b = 110238) :
    ∃ c' k, Exec P W (.seq kiS cp) c c' k ∧ k ≤ 5500 * ztbts + 260 ∧ FrameB BSA c c' ∧
      (∀ r, r ≠ b → r ≠ b + 1 → r ≠ b + 2 → r ≠ b + 3 → (r < 110223 ∨ 110228 < r) →
        BKI r = false → c'.nreg r = c.nreg r) ∧
      c'.nreg zthdn ≤ 2 ∧
      KInfo C zta N X (c'.nreg b) (c'.nreg ztds) (c'.nreg ztub) (c'.nreg zthdn) := by
  zumn

  obtain ⟨c₁, k₁, e₁, hk₁, f₁, j₁, b₁, a₁, s₁, K₁⟩ := kiS_exec hw h hX h6 h7
  subst hcp
  zud
  have KI : KInfo C zta N X ztvmk ztvml ztvmm
      (c₁.nreg 110228) := ⟨by_omega, by_omega, by_omega,
    by grind⟩
  obtain ⟨c₂, k₂, e₂, hk₂, n₂⟩ : ∃ c₂ k₂, Exec P W (block [.copyN b 110223, .copyN (b + 1) 110224,
      .copyN ztub 110227, .copyN zthdn 110228]) c₁ c₂ k₂ ∧ k₂ = 4 ∧
      c₂.nreg = upd (upd (upd (upd c₁.nreg b ztvmk) ztds ztvml)
        ztub ztvmm) (b + 3) (c₁.nreg 110228) := by
    rcases hb with rfl | rfl | rfl <;> (exec_block; exact by_simp_all)
  have fr₂ : ztuks := by
    rcases hb with rfl | rfl | rfl <;> exact exec_frameB e₂ by_decide
  have ex := Exec.seq e₁ e₂
  have e0 : c₂.nreg b = c₁.nreg 110223 := by
    simp_all
  have e1 : c₂.nreg ztds = c₁.nreg 110224 := by
    simp_all
  have e2' : c₂.nreg ztub = c₁.nreg 110227 := by
    simp_all
  have e3 : c₂.nreg zthdn = c₁.nreg 110228 := by
    simp_all
  refine ⟨c₂, _, ex, by_omega, (FrameB.mono f₁ fun r hr => by simp [BSA, hr]).trans fr₂,
    fun r a1 a2 a3 a4 a5 a6 => ?_, by_omega, by_grind⟩
  rw [n₂]; zvmwf
  rw [ite_eq_right a4, ite_eq_right a3, ite_eq_right a2, ite_eq_right a1]
  exact f₁.1 r a6
theorem ZEnv.of_BSA {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c c' : Config}
    (h : ZEnv P W lo C N V c) (f : FrameB BSA c c') : ZEnv P W lo C N V c' :=
  h.stable (fun r hr => f.1 r (BSA_keep ztcgw)) (fun a _ => by zunkg)
theorem spA_exec {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) :
    ∃ c' k, Exec P W spA c c' k ∧ k ≤ 3 * ztxup ∧ FrameB BSA c c' ∧
      c'.nreg 110233 ≤ 2 ∧ c'.nreg 110237 ≤ 2 ∧ c'.nreg 110241 ≤ 2 ∧
      KInfo C zta N (6 : ℕ) (c'.nreg 110230) (c'.nreg 110231) (c'.nreg 110232) (c'.nreg 110233) ∧
      KInfo C zta N (6 + rT C : ℕ) (c'.nreg 110234) (c'.nreg 110235) (c'.nreg 110236)
        (c'.nreg 110237) ∧
      KInfo C zta N (2 * C.m + 6 : ℕ) (c'.nreg 110238) (c'.nreg 110239) (c'.nreg 110240)
        (c'.nreg 110241) := by
  zubb
  zubwh
  -- the first key
  have e₀ := Exec.constN (P := P) hw 110220 6 (by have := h.hW; omega)
  set c₀ : Config := { c with nreg := upd c.nreg 110220 6 } with hc₀
  have f₀ : FrameB BSA c c₀ := exec_frameB e₀ by_decide
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, r₁, s₁, K₁⟩ := kiCp_exec e₀.wb_right (h.of_BSA f₀) (X := 6)
    by_rfl le_rfl by_omega cp1 110230 rfl ztp
  have h₁ := (h.of_BSA f₀).of_BSA f₁
  -- the second key
  have e₂ := Exec.copyN (P := P) e₁.wb_right 110220 110050
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 110220 _ } with hc₂
  have f₂ : ztuks := exec_frameB e₂ by_decide
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, r₃, s₃, K₃⟩ := kiCp_exec e₂.wb_right (h₁.of_BSA f₂)
    (X := 6 + rT C) (by zumxp; config_simp; exact h₁.pk.k0) by_omega by_omega cp2 110234 rfl
    ztwiz
  have h₃ := (h₁.of_BSA f₂).of_BSA f₃
  -- the third key
  have e₄ := Exec.copyN (P := P) e₃.wb_right 110220 120029
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 110220 _ } with hc₄
  have f₄ : FrameB BSA c₃ c₄ := exec_frameB e₄ by_decide
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, r₅, s₅, K₅⟩ := kiCp_exec e₄.wb_right (h₃.of_BSA f₄)
    (X := 2 * C.m + 6) (by zunbf; config_simp; exact h₃.pk.tEnd) by_omega le_rfl cp3 110238 rfl
    ztwrm
  have ex : Exec P W spA c c₅ _ := .seq e₀ ztyoe
  -- the saved values survive
  have keep35 : ∀ r, 110230 ≤ r → r ≤ 110237 → c₅.nreg r = c₃.nreg r := fun r a b => by
    rw [r₅ r by_omega by_omega by_omega by_omega by_omega ztuwo, hc₄]; config_simp; zumya
  have keep13 : ∀ r, 110230 ≤ r → r ≤ 110233 → c₃.nreg r = c₁.nreg r := fun r a b => by
    rw [r₃ r by_omega by_omega by_omega by_omega by_omega ztuwo, hc₂]; config_simp; zumya
  refine ⟨c₅, _, ex, by_omega, f₀.trans (f₁.trans ztmkc), ?_, ?_,
    s₅, ?_, ?_, K₅⟩
  · grind
  · grind
  · grind
  grind

/-! ## The five emissions -/

/-- The registers written by the emissions. -/
def BEm (r : ℕ) : Bool :=
  BG r || decide (r = 110295) || decide (r = 110296) || decide ztogc ||
    decide ztekh

/-- The state of the emissions. -/
structure EmSt (m₀ : ℕ → ℕ) (R1 R2 c₀ : ℕ) (l : List ztw) (c : Config) : Prop where
  one : c.nreg 120011 = 1
  zero : c.nreg 120012 = 0
  r1 : c.nreg 110293 = R1
  r2 : c.nreg 110294 = R2
  cnt : c.nreg 110295 = c₀ + l.length
  inv : PInv m₀ c.nmem R1 R2 c₀ l
theorem emitStep_exec {c c₁ : Config} {m₀ : ℕ → ℕ} {R1 R2 c₀ : ℕ}
    {l : List ztw} (hs : EmSt m₀ R1 R2 c₀ l c) {a b g : ℕ} (hw₁ : WordsBounded W c₁)
    (hG : GRes c c₁ a b g) (hroom : R1 + c₀ + l.length + 1 ≤ R2)
    (hRW : R2 + c₀ + l.length + 1 ≤ W) (ha : a + 1 ≤ W) (hb : b + 1 ≤ W) :
    ∃ c₂ k, Exec P W emitG c₁ c₂ k ∧ k ≤ 25 ∧ (∀ r, BEm r = false → c₂.nreg r = c.nreg r) ∧
      (∀ r, BEm r = false → c₂.rreg r = c.rreg r) ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output ∧
      EmSt m₀ R1 R2 c₀ (l ++ (gOpt g a b).toList) c₂ := by
  obtain ⟨f, va, vb, vg⟩ := hG
  have gg := f.1
  obtain ⟨c₂, k, e, hk, r₂, rr₂, rm₂, o₂, cnt₂, pr₂, mm₂⟩ := emitG_exec (P := P) (R1 := R1)
    (R2 := R2) (c₀ := c₀ + l.length) hw₁
    (by rw [gg 120011 by_decide]; exact hs.one) (by rw [gg 120012 by_decide]; exact hs.zero)
    (by rw [gg 110293 by_decide]; exact hs.r1) (by rw [gg 110294 by_decide]; exact hs.r2)
    (by rw [gg 110295 by_decide]; exact hs.cnt) by_omega by_omega by_omega
    by_omega
  rw [vg, va, vb] at cnt₂ pr₂ mm₂
  have hm₁ := f.2.2.1
  have hlen : (gOpt g a b).toList.length ≤ 1 := by_simp
  refine ⟨c₂, k, e, hk, fun r hr => ?_, fun r hr => ?_, by rw [rm₂, f.2.2.2.1],
    by rw [o₂, f.2.2.2.2], ztcbl⟩
  · zuggf
    grind
  · zuggf
    zunsn; exact f.2.1 r hr.1.1.1.1
  · rw [r₂ 120011 by_decide by_decide by_decide by_decide, gg 120011 by_decide]
    exact hs.one
  · rw [r₂ 120012 by_decide by_decide by_decide by_decide, gg 120012 by_decide]
    exact hs.zero
  · rw [r₂ 110293 by_decide by_decide by_decide by_decide, gg 110293 by_decide]
    exact hs.r1
  · rw [r₂ 110294 by_decide by_decide by_decide by_decide, gg 110294 by_decide]
    exact hs.r2
  · grind
  · exact PInv.step hs.inv by_omega pr₂ ztjwq
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
  val : ∀ i : Fin 12, c.nreg ztsqy = v i
  six : c.nreg 120028 = 6
  k0 : c.nreg 110050 = 6 + R
theorem SpVals.congr {c c' : Config} {R : ℕ} {v : Fin 12 → ℕ} (h : SpVals c R v)
    (hr : ∀ r, BEm r = false → c'.nreg r = c.nreg r) : SpVals c' R v :=
  ⟨fun i => by rw [hr _ (by simp [BEm, BG]; omega)]; exact h.val i,
    by zumwn; exact h.six, by zumwn; exact h.k0⟩
theorem spB_exec (hw : WordsBounded W c) {R R1 R2 c₀ : ℕ}
    {v : Fin 12 → ℕ} (hv : SpVals c R v) (hs : EmSt c.nmem R1 R2 c₀ [] c)
    (hroom : R1 + c₀ + 5 ≤ R2) (hRW : R2 + c₀ + 5 ≤ W) (hvW : ∀ i, v i + 1 ≤ W)
    (hs3 : v 3 ≤ 2) (hs7 : v 7 ≤ 2) (hs11 : v 11 ≤ 2) (hW4 : 4 ≤ W) :
    ∃ c' k, Exec P W spB c c' k ∧ k ≤ 200 ∧ (∀ r, BEm r = false → c'.nreg r = c.nreg r) ∧
      (∀ r, BEm r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      EmSt c.nmem R1 R2 c₀ ((spRam R ztwhc ztwhd ztwhg ztwhh ztwhi ztwhj ztwhk ztwhl ztwhm ztwhn
        ztwhe ztwhf).filterMap id) c' := by
  have len1 : ∀ o : Option ztw, o.toList.length ≤ 1 := by_simp_all
  -- 1
  obtain ⟨c₁, k₁, e₁, hk₁, G₁⟩ := g1S_exec (P := P) hw hv.six hv.k0 by_omega
  obtain ⟨c₂, k₂, e₂, hk₂, R₂, rr₂, rm₂, o₂, S₂⟩ := emitStep_exec (P := P) hs e₁.wb_right G₁
    by_grind by_grind (by rw [ztltb]; simp_all) (by rw [ztltc]; simp_all)
  have hv₂ := hv.congr R₂
  rw [ztltb, ztltc] at S₂
  -- 2
  obtain ⟨c₃, k₃, e₃, hk₃, G₃⟩ := g2S_exec (P := P) e₂.wb_right by_omega
  obtain ⟨c₄, k₄, e₄, hk₄, R₄, rr₄, rm₄, o₄, S₄⟩ := emitStep_exec (P := P) S₂ e₃.wb_right G₃
    by_grind
    by_grind
    (by rw [ztltd]; simp_all) (by rw [ztlte]; simp_all)
  have hv₄ := hv₂.congr R₄
  rw [ztltd, ztlte] at S₄
  -- 3
  obtain ⟨c₅, k₅, e₅, hk₅, G₅⟩ := g3S_exec (P := P) e₄.wb_right S₄.zero hv₄.six hv₄.k0
    (by rw [ztltf, ztltg]; omega) by_omega
  rw [(show c₄.nreg 110232 = v 2 from hv₄.val 2), (show c₄.nreg 110236 = v 6 from hv₄.val 6), ztltf, ztltg] at G₅
  obtain ⟨c₆, k₆, e₆, hk₆, R₆, rr₆, rm₆, o₆, S₆⟩ := emitStep_exec (P := P) S₄ e₅.wb_right G₅
    by_grind
    by_grind
    ztvwn ztvwo
  have hv₆ := hv₄.congr R₆
  -- 4
  obtain ⟨c₇, k₇, e₇, hk₇, G₇⟩ := g4S_exec (P := P) e₆.wb_right S₆.zero
    (by rw [ztlth, ztlti]; omega) by_omega
  rw [(show c₆.nreg 110236 = v 6 from hv₆.val 6), (show c₆.nreg 110240 = v 10 from hv₆.val 10), ztlth, ztlti] at G₇
  obtain ⟨c₈, k₈, e₈, hk₈, R₈, rr₈, rm₈, o₈, S₈⟩ := emitStep_exec (P := P) S₆ e₇.wb_right G₇
    by_grind
    by_grind
    ztvwo ztvwm
  have hv₈ := hv₆.congr R₈
  -- 5
  obtain ⟨c₉, k₉, e₉, hk₉, G₉⟩ := g5S_exec (P := P) e₈.wb_right S₈.zero
    (by rw [ztltj, ztltk]; omega) by_omega
  rw [(show c₈.nreg 110232 = v 2 from hv₈.val 2), (show c₈.nreg 110240 = v 10 from hv₈.val 10), ztltj, ztltk] at G₉
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, R₁₀, rr₁₀, rm₁₀, o₁₀, S₁₀⟩ := emitStep_exec (P := P) S₈ e₉.wb_right G₉
    by_grind
    by_grind
    ztvwn ztvwm
  have ex : Exec P W spB c c₁₀ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇
    ztncr))))))
  refine ⟨c₁₀, _, ex, by_omega, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
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
theorem spS_exec {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {R1 R2 c₀ : ℕ} (hR1 : c.nreg 110293 = R1)
    (hR2 : c.nreg 110294 = R2) (hc : c.nreg 110295 = c₀) (hlo : lo ≤ R1)
    (hroom : R1 + c₀ + 5 ≤ R2) (hRW : R2 + c₀ + 5 ≤ W) :
    ∃ c' k, Exec P W spS c c' k ∧ k ≤ 3 * ztxup + 200 ∧
      (∀ r, BSP r = false → c'.nreg r = c.nreg r) ∧ (∀ r, BSP r = false → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 110295 = c₀ + (zipSp C zta N).length ∧
      PInv c.nmem c'.nmem R1 R2 c₀ (zipSp C zta N) ∧ ZEnv P W lo C N V c' := by
  zumn

  have hAW : ztmty := by
    zuuq

    · grind
    · omega
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, s3, s7, s11, K6, KT, K2⟩ := spA_exec hw h
  have h₁ := h.of_BSA f₁
  set v : Fin 12 → ℕ := fun i => c₁.nreg ztsqy with hv
  have SV : SpVals c₁ _ v := ⟨by_simp_all, h₁.pk.six, h₁.pk.k0⟩
  have keep : ∀ r, 110293 ≤ r → r ≤ 110295 → c₁.nreg r = c.nreg r := fun r a b =>
    f₁.1 r (BSA_keep by_omega)
  have ES : EmSt c₁.nmem R1 R2 c₀ [] c₁ := ⟨h₁.pk.one, h₁.pk.zero,
    by simp_all, by_simp_all,
    by simp_all, PInv.nil _ _ _ _⟩
  have hvW : ∀ i, v i + 1 ≤ W := by
    obtain ⟨a0, a1, a2, -⟩ := K6
    obtain ⟨b0, b1, b2, -⟩ := KT
    obtain ⟨d0, d1, d2, -⟩ := K2
    rw [← hA] at a0 a1 a2 b0 b1 b2 d0 d1 d2
    have hW4 := h.hW
    intro i; fin_cases i <;> simp [hv] <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, rm₂, o₂, ES₂⟩ := spB_exec (P := P) e₁.wb_right SV ES
    by_omega by_omega hvW s3 s7 s11 by_omega
  have K6' : KInfo C zta N 6 (c₁.nreg 110230) (c₁.nreg 110231) (c₁.nreg 110232)
      (c₁.nreg 110233) := by_omega
  have KT' : KInfo C zta N ztbgn (c₁.nreg 110234) (c₁.nreg 110235) (c₁.nreg 110236)
      (c₁.nreg 110237) := by convert KT using 1; try (rw [← rT_def]; push_cast; ring)
  have K2' : KInfo C zta N ztcc (c₁.nreg 110238) (c₁.nreg 110239) (c₁.nreg 110240)
      (c₁.nreg 110241) := by_grind
  have heq := spRam_eq h.isNF h.simple K6' KT' K2'
  rw [show (spRam ztkdv ztwhc ztwhd ztwhg ztwhh ztwhi ztwhj ztwhk ztwhl ztwhm ztwhn ztwhe
    ztwhf).filterMap id = zipSp C (Qof P) N from heq] at ES₂
  zugmw
  rw [hm₁] at ES₂
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, fun r hr => ?_, fun r hr => ?_, by rw [rm₂, f₁.2.2.2.1],
    by rw [o₂, f₁.2.2.2.2], ES₂.cnt, ES₂.inv, ?_⟩
  · zuhoq
    rw [r₂ r hr.2, f₁.1 r hr.1]
  · zuhoq
    rw [rr₂ r hr.2, f₁.2.1 r hr.1]
  · refine h₁.stable (fun r hr => r₂ r ?_) ztts
    · zucqx
      simp [BEm, BG]; omega
    · rw [ES₂.inv.2 a by_omega, hm₁]
end
end OracleR
end Chazelle.Core
end
namespace Chazelle.Core
namespace OracleR
@[expose] public section
def PLe (x y : ℕ × ℕ) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
theorem PLe.antisymm {x y : ℕ × ℕ} (h : PLe x y) (h' : PLe y x) : x = y := by
  unfold PLe at *; grind
open Classical in
/-- The kept pair at position `t`. -/
noncomputable def dedupF (n : ℕ) (pr : ℕ → ℕ × ℕ) (s : ℕ → ℕ) (t : ℕ) : Option ztw :=
  if t < n ∧ (t = 0 ∨ pr ztkc ≠ pr ztxag) then some ztbaim else none

/-- A sorted sequence: pairs increase along positions. -/
def SortedSeq (pr : ℕ → ℕ × ℕ) (s : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t t', t ≤ t' → t' < n → PLe ztbaim (pr ztfil)
variable {pr : ℕ → ℕ × ℕ} {s : ℕ → ℕ} {n : ℕ}
theorem dedup_key (hs : SortedSeq pr s n) {a a' : ℕ}
    {b : ℕ × ℕ} (hlt : a < a') (h1 : dedupF n pr s a = some b) (h2 : dedupF n pr s a' = some b) :
    False := by
  unfold dedupF at h1 h2
  split_ifs at h1 h2 with c1 c2
  have e : pr (s a) = pr (s a') := (Option.some.inj h1).trans (Option.some.inj h2).symm
  obtain ⟨ha', c2⟩ := c2
  rcases c2 with c2 | c2
  · omega
  · have e1 := hs a ztter by_omega by_omega
    have e2 := hs ztter a' by_omega ha'
    zvmwe at e1
    exact c2 (PLe.antisymm e2 e1).symm
theorem dedup_nodup (hs : SortedSeq pr s n) :
    (emitted ztroo n).Nodup := by
  zulbq

  rcases lt_trichotomy a a' with h | h | h
  · exact absurd (dedup_key hs h hb hb') id
  · zubh
  · exact absurd (dedup_key hs h hb' hb) id
theorem mem_dedup (hsurj : ∀ i, i < n → ∃ t, t < n ∧ s t = i)
    (hlt : ∀ t, t < n → s t < n) {x : ℕ × ℕ} :
    x ∈ emitted ztroo n ↔ ∃ i, i < n ∧ pr i = x := by
  zulqm

  · rintro ⟨t, ht, h⟩
    unfold dedupF at h
    grind
  · zuin
    classical
    have hex : ∃ t, t < n ∧ pr ztkc = pr i := by
      grind
    let t0 := Nat.find hex
    obtain ⟨h0, e0⟩ := Nat.find_spec hex
    refine ⟨t0, h0, ?_⟩
    have hcond : t0 = 0 ∨ pr (s t0) ≠ pr (s (t0 - 1)) := by
      by_cases hz : t0 = 0
      · omega
      · right
        zuchf
        have := Nat.find_min hex (show t0 - 1 < t0 by omega)
        grind
    unfold dedupF
    rw [ite_eq_left ⟨h0, hcond⟩, e0]
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
def dBody : Stmt :=
  .seq (block [.addN 60015 60007 60010, .loadN 60015 60015, .addN 60016 60004 60015,
      .loadN 60012 60016, .addN 60016 60005 60015, .loadN 60013 60016])
    (.ifLtN 120012 60010
      (.seq (block [.subN 60015 60010 120011, .addN 60015 60007 60015, .loadN 60015 60015,
          .addN 60016 60004 60015, .loadN 60018 60016, .addN 60016 60005 60015,
          .loadN 60019 60016])
        (ifEq 60012 60018 (ifEq 60013 60019 (.instr (.constN 60011 0)) ztifz)
          ztifz))
      ztifz)

/-- The registers written by `dBody`. -/
def BDB (r : ℕ) : Bool := decide (60011 ≤ r ∧ r ≤ 60019 ∧ r ≠ 60014 ∧ r ≠ 60017)

/-- The memory read by the dedup body. -/
structure DMem (m : ℕ → ℕ) (Sb Z1 Z2 n : ℕ) (s P1 P2 : ℕ → ℕ) : Prop where
  s_eq : ∀ t, t < n → m ztis = s t
  s_lt : ∀ t, t < n → s t < n
  p1 : ∀ i, i < n → m zthdf = P1 i
  p2 : ∀ i, i < n → m zthdg = P2 i
variable {P : Polygon} {W : ℕ} {c : Config}
theorem dBody_exec (hw : WordsBounded W c) {Sb Z1 Z2 n t : ℕ}
    {s P1 P2 : ℕ → ℕ} (hM : DMem c.nmem Sb Z1 Z2 n s P1 P2) (h7 : c.nreg 60007 = Sb)
    (h4 : c.nreg 60004 = Z1) (h5 : c.nreg 60005 = Z2) (h1 : c.nreg 120011 = 1)
    (h0 : c.nreg 120012 = 0) (ht : c.nreg 60010 = t) (htn : t < n) (hSW : Sb + n ≤ W)
    (hZW : Z1 + n ≤ W) (hZW' : Z2 + n ≤ W) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W dBody c c' k ∧ k ≤ 30 ∧ FrameB BDB c c' ∧
      (dedupF n ztbri s t = none → c'.nreg 60011 = 0) ∧
      ∀ x, dedupF n ztbri s t = some x →
        c'.nreg 60011 = 1 ∧ c'.nreg 60012 = x.1 ∧ c'.nreg 60013 = x.2 := by
  have hwr : wr BDB dBody = true := by_decide
  have hs := hM.s_lt t htn
  obtain ⟨c₁, k₁, e₁, hk₁, n₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 60015 60007 60010,
      .loadN 60015 60015, .addN 60016 60004 60015, .loadN 60012 60016, .addN 60016 60005 60015,
      .loadN 60013 60016]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 60015 ztkc) 60016 (Z2 + s t)) 60012 (P1 ztkc)) 60013
        (P2 ztkc) := by
    exec_block
    · omega
    · config_simp; rw [h7, ht, h4, hM.s_eq t htn]; omega
    · config_simp; rw [h7, ht, h5, hM.s_eq t htn]; omega
    · zubee
      config_simp; rw [h7, ht, h4, h5, hM.s_eq t htn, hM.p1 _ hs, hM.p2 _ hs]
      funext r; zvmwf; grind
  zud
  have R₁ : ∀ r, r ≠ 60015 → r ≠ 60016 → r ≠ 60012 → r ≠ 60013 → c₁.nreg r = c.nreg r :=
    by simp_all
  have x12 : c₁.nreg 60012 = P1 ztkc := by_simp_all
  have x13 : c₁.nreg 60013 = P2 ztkc := by_simp_all
  suffices H : ∃ c₂ k₂, Exec P W _ c₁ c₂ k₂ ∧ k₂ ≤ 24 ∧
      c₂.nreg 60012 = P1 ztkc ∧ c₂.nreg 60013 = P2 ztkc ∧
      c₂.nreg 60011 = (if t = 0 ∨ (P1 ztkc, P2 ztkc) ≠ (P1 ztxag, P2 ztxag)
        then 1 else 0) by
    obtain ⟨c₂, k₂, e₂, hk₂, a, b, f⟩ := H
    have ex : Exec P W dBody c c₂ _ := .seq e₁ e₂
    refine ⟨c₂, _, ex, by_omega, exec_frameB ex hwr, fun hn => ?_, fun x hx => ?_⟩
    · unfold dedupF at hn
      simp_all
    · unfold dedupF at hx
      grind
  by_cases hz : t = 0
  · have ht' : ¬ c₁.nreg 120012 < c₁.nreg 60010 := by
      simp_all
    exact ⟨_, _, .ifLtN_false ht' (Exec.constN w₁ 60011 1 hW), by_omega, by_simp_all,
      by simp_all, by_simp_all⟩
  · have ht' : c₁.nreg 120012 < c₁.nreg 60010 := by
      grind
    have hs' := hM.s_lt ztso by_omega
    obtain ⟨c₂, k₂, e₂, hk₂, n₂⟩ : ∃ c₂ k₂, Exec P W (block [.subN 60015 60010 120011,
        .addN 60015 60007 60015, .loadN 60015 60015, .addN 60016 60004 60015, .loadN 60018 60016,
        .addN 60016 60005 60015, .loadN 60019 60016]) c₁ c₂ k₂ ∧ k₂ = 7 ∧
        c₂.nreg = upd (upd (upd (upd c₁.nreg 60015 ztxag) 60016 (Z2 + s ztso)) 60018
          (P1 ztxag)) 60019 (P2 (s (t - 1))) := by
      have a7 : c₁.nreg 60007 = Sb := by_simp_all
      have a4 : c₁.nreg 60004 = Z1 := by_simp_all
      have a5 : c₁.nreg 60005 = Z2 := by_simp_all
      have a10 : c₁.nreg 60010 = t := by
        simp_all
      have a11 : ztdxr := by
        simp_all
      have hmem :=
        (exec_frameB e₁ (B := BDB) by_decide).2.2.1
      exec_block
      · config_simp; omega
      · config_simp; rw [a7, a10, a11, a4, hmem, hM.s_eq _ by_omega]; omega
      · config_simp; rw [a7, a10, a11, a5, hmem, hM.s_eq _ by_omega]; omega
      · zubee
        config_simp; rw [a7, a10, a11, a4, a5, hmem, hM.s_eq _ by_omega, hM.p1 _ hs', hM.p2 _ hs']
        funext r; zvmwf; grind
    zue
    have y12 : c₂.nreg 60012 = P1 ztkc := by_simp_all
    have y13 : c₂.nreg 60013 = P2 ztkc := by_simp_all
    have y18 : c₂.nreg 60018 = P1 ztxag := by_simp_all
    have y19 : c₂.nreg 60019 = P2 ztxag := by_simp_all
    by_cases e1 : P1 ztkc = P1 ztxag
    · have q1 : c₂.nreg 60012 = c₂.nreg 60018 := by_omega
      by_cases e2 : P2 ztkc = P2 ztxag
      · have q2 : c₂.nreg 60013 = c₂.nreg 60019 := by_omega
        exact ⟨_, _, .ifLtN_true ht' (.seq e₂ (ifEq_eq_exec q1 (ifEq_eq_exec q2
          (Exec.constN w₂ 60011 0 ztbg)))), by_omega, by_simp_all,
          by simp_all, by
            simp_all⟩
      · have q2 : c₂.nreg 60013 ≠ c₂.nreg 60019 := by_omega
        obtain ⟨k', e', hk'⟩ := ifEq_ne_exec q2
          ztpxy
        exact ⟨_, _, .ifLtN_true ht' (.seq e₂ (ifEq_eq_exec q1 e')), by_omega,
          by simp_all, by_simp_all, by
            simp_all⟩
    · have q1 : c₂.nreg 60012 ≠ c₂.nreg 60018 := by_omega
      obtain ⟨k', e', hk'⟩ := ifEq_ne_exec q1
        ztpxy
      exact ⟨_, _, .ifLtN_true ht' (.seq e₂ e'), by_omega, by_simp_all,
        by simp_all, by
          simp_all⟩

/-! ## Saving the handles, the items, the sort -/

/-- Save the handles into band `bDecomp`. -/
def dSave : Stmt :=
  block [.copyN 60001 110072, .copyN 60002 110073, .copyN 60003 110074, .copyN 60004 110293,
    .copyN 60005 110294, .copyN 60006 110295]

/-- The item array `0 … n - 1` at the allocator (`30003`). -/
def itemS : Stmt :=
  .seq ztctx
    (scatS 60020 60006 120011 60016 60017 (block [.addN 60016 30003 60020, .copyN 60017 60020]))

/-- The inputs of the sort and of the comparator. -/
def sortSet : Stmt :=
  block [.copyN 30004 60006, .copyN 115000 60004, .copyN 115001 60005, .copyN 115005 60006]

/-- **Save, build the items, sort them by their raw pairs.** -/
def dSort : Stmt :=
  .seq dSave (.seq itemS (.seq sortSet (.seq ztvdi
    ztovs)))

/-- The bands written by `dSort` (besides the allocator). -/
def dBands : Finset ℕ := {bSort, bDecomp, bOPrep}
theorem dSort_exec (hw : WordsBounded W c)
    {CH1 CH2 nI Z1 Z2 n A₀ : ℕ} (h72 : c.nreg 110072 = CH1) (h73 : c.nreg 110073 = CH2)
    (h74 : c.nreg 110074 = nI) (h93 : c.nreg 110293 = Z1) (h94 : c.nreg 110294 = Z2)
    (h95 : c.nreg 110295 = n) (h1 : c.nreg 120011 = 1) (hAl : c.nreg 9999 = A₀)
    (hZ1 : Z1 + n ≤ A₀) (hZ2 : Z2 + n ≤ A₀)
    (hroom : A₀ + n + SortR.sortCost 20 n ≤ W) :
    ∃ c' k, Exec P W dSort c c' k ∧ k ≤ 7 * n + SortR.sortCost 20 n + 20 ∧
      FrameN dBands c c' ∧ A₀ + n ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + n + SortR.sortCost 20 n ∧
      c'.nreg 60001 = CH1 ∧ c'.nreg 60002 = CH2 ∧ c'.nreg 60003 = nI ∧ c'.nreg 60004 = Z1 ∧
      c'.nreg 60005 = Z2 ∧ c'.nreg 60006 = n ∧
      A₀ + n ≤ c'.nreg 60007 ∧ c'.nreg 60007 + n ≤ c'.nreg 9999 ∧
      SortedSeq ztyev ztzfu n ∧
      ztxey ∧
      ztxzg := by
  -- 1. save
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W dSave c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 60001 CH1) 60002 CH2) 60003 nI) 60004 Z1)
        60005 Z2) 60006 n ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧
      c₁.output = c.output := by
    unfold dSave
    exec_block
    simp_all
  -- 2. the items
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      ztctx c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg = upd ztrxt 9999 ztsva ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    zud
    zujwq
    have a6 : c₁.nreg 60006 = n := by_simp_all
    exec_block
    · config_simp; omega
    simp_all
  zudct

  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, mm₃, rm₃, o₃, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60020) (rn := 60006) (r1 := 120011) (ra := 60016) (rv := 60017)
    (body := block [.addN 60016 30003 60020, .copyN 60017 60020])
    (B := fun r => decide zthka) by_decide by_decide by_decide by_decide
    by_decide ztdky A₀
    (fun d d' hJ hr hm => JK.stable (rs := [60020]) (fun r hr' => by
      simp_all) hJ
      ztdod hm)
    (n := n) (κ := 2) ztijn ztfrq ztbeo
    (fun i d hi hJ hwd hri => by
      zuegc
      obtain ⟨d', k, e, hk, v1, v2⟩ : ∃ d' k, Exec P W (block [.addN 60016 30003 60020,
          .copyN 60017 60020]) d d' k ∧ k = 2 ∧ d'.nreg 60016 = A₀ + i ∧ d'.nreg 60017 = i := by
        exec_block
        · omega
        simp_all
      exact ztdjb)
    e₂.wb_right ztdkz a6 a11 by_omega
  zujwf
  -- 3. the inputs of the sort
  obtain ⟨c₄, k₄, e₄, hk₄, n₄⟩ : ∃ c₄ k₄, Exec P W sortSet c₃ c₄ k₄ ∧ k₄ = 4 ∧
      c₄.nreg = upd ztibm 115005 n := by
    zubj
    zujwu
    have b4 : ztusg := by
      simp_all
    have b5 : ztush := by
      simp_all
    unfold sortSet
    exec_block
    grind
  have hm₄ :=
    (exec_frameB e₄ (B := fun r => decide ztsi) by_decide).2.2.1
  have R₄ : ztfdw := fun r a b => by
    zufob
  have g9 : ztrgn := by
    rw [R₄ _ by_decide by_decide, R₃ _ by_decide by_decide by_decide, n₂]; config_simp
  have g30 : ztpnr := by
    grind
  -- the items in memory
  have hitems : ztios := by
    zugy

    zulzs
  -- 4. the sort
  zukao
  have hmem₄ : ztced := fun a ha => by
    rw [hm₄, mm₃, scat_below by_grind ha, m₂, m₁]
  obtain ⟨c₅, k₅, e₅, hk₅, J₅, F₅, s₁, s₂, L', hseg, hperm, hpw⟩ := SortR.sortStmt_exec (P := P)
    (W := W) (lexCmp_ok (m₀ := c₄.nmem) (A₀ := A₀ + n) (B1 := Z1) (B2 := Z2) (K := n)
      by_omega by_omega (by have := SortR.sortCost_ge 20 n; omega) hW') by_decide
    ztgiu ztqsz
    e₄.wb_right ⟨by zungn; config_simp, by zungn; config_simp, by zungn; config_simp,
      fun _ _ => rfl⟩ (by zuncx; exact lexJ_stable _ _ _ _ _) (List.range n) hitems
    ztnuh ztgra ztgrb
  zubeg

  -- 5. the base of the sorted items

  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 60007 _ } with hc₆
  have ex : Exec P W dSort c c₆ _ := .seq e₁ ztbaqz
  have hF5 : zteik := fun r hr =>
    F₅.1 r ztnuv ztche
  have v : ∀ r, 60001 ≤ r → r ≤ 60006 → c₆.nreg r = c₁.nreg r := fun r a b => by
    zumys; config_simp; rw [upd_other _ _ _ by_omega, hF5 r ztdmk,
      R₄ r by_omega by_omega, R₃ r by_omega by_omega by_omega, n₂]
    rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega]
  zufhu

  -- the sorted sequence
  have hsd : ztgqe := fun t ht => by
    zueya
  zudyi
  have hmemL : ztkpb := fun t ht => by
    zujvu

  have hc5 := fun a ha => F₅.2.2.1 a (by zuncx; exact ha)
  zuffp

  refine ⟨c₆, _, ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · -- the frame
    have F14 : ztukz := by
      refine PF.frameN (B := fun r => decide ztyc || decide ztgzi ||
        decide ztgyw || decide ztneb)
        ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_⟩ ztez ?_
      · zupg
        rw [R₄ r by_omega by_omega, R₃ r by_omega by_omega by_omega, n₂, n₁]
        zvmwf; split_ifs <;> first | omega
      · have := (exec_frameB e₄ (B := fun r => decide ztsi)
          by_decide).2.1 r by_grind
        rw [this, rr₃ r by_grind,
          rr₂, rr₁]
      · grind
      · rw [(exec_frameB e₄ (B := fun r => decide ztsi)
          by_decide).2.2.2.1, rm₃, rm₂, rm₁]
      · rw [(exec_frameB e₄ (B := fun r => decide ztsi)
          by_decide).2.2.2.2, o₃, o₂, o₁]
      · zufw
        zuws
        · zuhcq
        · zufic
        · zufie
        · zufid
      · have := (exec_frameB e₄ (B := fun r => decide ztsi)
          by_decide).2.1 ALLOC by_decide
        rw [this, rr₃ _ by_decide, rr₂, rr₁]
    have F56 : ztula :=
      Frame.toN (NFLoc.frame_of_frameB (exec_frameB e₆ (B := fun r => decide zttxu)
        by_decide) (fun r hr => by
          simp at hr; subst hr; decide) 1)
    exact (F14.trans ztihd
      by_omega).trans F56
      by_omega
  · have := F₅.2.2.2.2.2.1; rw [g9'] at this
    zujis
  · have := F₅.2.2.2.2.2.2; rw [g9'] at this
    zufnl
  · rw [v _ by_norm_num by_norm_num, n₁]; config_simp
  · rw [v _ by_norm_num by_norm_num, n₁]; config_simp
  · rw [v _ by_norm_num by_norm_num, n₁]; config_simp
  · rw [v _ by_norm_num by_norm_num, n₁]; config_simp
  · rw [v _ by_norm_num by_norm_num, n₁]; config_simp
  · rw [v _ by_norm_num by_norm_num, n₁]; config_simp
  · omega
  · rw [v7, hc₆]; config_simp; exact s₂
  · -- sorted
    zubom

    have hc4 : ∀ i, i < n → c₄.nmem _ = c.nmem zthdf ∧ c₄.nmem _ = c.nmem zthdg :=
      fun i hi => ztook
    zujdp
    · zulaq
    · have := List.pairwise_iff_getElem.1 hpw t t' by_omega by_omega h
      zugz

  · zug
    zulgv
    zucoh
    exact ztgpq
  grind

/-- **The dedup emission** into the chord arrays. -/
def dEmit : Stmt := emitS 60010 60006 120011 60011 60012 60013 60001 60002 60003 60014 dBody

/-- The environment of the dedup emission. -/
def DEnv (Sb Z1 Z2 n : ℕ) (s P1 P2 : ℕ → ℕ) (d : Config) : Prop :=
  d.nreg 60004 = Z1 ∧ d.nreg 60005 = Z2 ∧ d.nreg 60007 = Sb ∧ d.nreg 120011 = 1 ∧
    d.nreg 120012 = 0 ∧ DMem d.nmem Sb Z1 Z2 n s P1 P2
theorem dEmit_exec (hw : WordsBounded W c)
    {CH1 CH2 nI Sb Z1 Z2 n : ℕ} {s P1 P2 : ℕ → ℕ} (hE : DEnv Sb Z1 Z2 n s P1 P2 c)
    (h1 : c.nreg 60001 = CH1) (h2 : c.nreg 60002 = CH2) (h3 : c.nreg 60003 = nI)
    (h6 : c.nreg 60006 = n) (hC : CH1 + nI + n ≤ CH2) (hZ : CH2 + nI + n ≤ Z1)
    (hZ12 : Z1 ≤ Z2) (hZS : Z2 ≤ Sb) (hSW : Sb + n ≤ W) :
    ∃ c' k, Exec P W dEmit c c' k ∧ k ≤ n * 40 + 3 ∧
      (∀ r, BDB r = false → r ≠ 60010 → r ≠ 60003 → r ≠ 60014 → c'.nreg r = c.nreg r) ∧
      (∀ r, BDB r = false → c'.rreg r = c.rreg r) ∧
      c'.nreg 60003 = nI + (emitted ztxny n).length ∧
      PairsAt c'.nmem ztswe ztswf (emitted ztxny n) ∧
      (∀ a, (a < CH1 + nI ∨ (CH1 + nI + (emitted ztxny n).length ≤ a ∧
        a < CH2 + nI) ∨ CH2 + nI + (emitted (dedupF n (fun i => (P1 i, P2 i)) s) n).length ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, r', rr', cnt, pr, mm, rm, o, -⟩ := emitS_exec (P := P) (W := W)
    (ri := 60010) (rn := 60006) (r1 := 120011) (rf := 60011) (rv1 := 60012) (rv2 := 60013)
    (rR1 := 60001) (rR2 := 60002) (rc := 60003) (rt := 60014) (body := dBody) (B := BDB)
    by_decide by_decide by_decide by_decide by_decide by_decide by_decide
    (R1 := CH1) (R2 := CH2) (c₀ := nI) (n := n) (κ := 30) (DEnv Sb Z1 Z2 n s P1 P2)
    (fun d d' hJ hr hm => by
      zudqu
      refine ⟨by rw [hr _ by_decide by_decide by_decide by_decide, a4],
        by rw [hr _ by_decide by_decide by_decide by_decide, a5],
        by rw [hr _ by_decide by_decide by_decide by_decide, a7],
        by rw [hr _ by_decide by_decide by_decide by_decide, a11],
        by rw [hr _ by_decide by_decide by_decide by_decide, a12], ⟨fun t ht => ?_,
        hM.s_lt, fun i hi => ?_, fun i hi => ?_⟩⟩
      · zvmzz; exact hM.s_eq t ht
      · zvmzz; exact hM.p1 i hi
      · zvmzz; exact hM.p2 i hi)
    ztxny
    (fun i d hi hJ hwd hri => by
      zudqu
      exact dBody_exec hwd hM a7 a4 a5 a11 a12 hri hi hSW by_omega by_omega by_omega)
    hw hE h6 hE.2.2.2.1 h1 h2 h3 hC by_omega
  exact ⟨c', k, ex, by_nlinarith, r', rr', cnt, pr, mm, rm, o⟩
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open OracleR OracleBook
namespace OracleQ
theorem graphOK_of {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF ztc Q N)
    (hP : C.P.Simple) {D : List ztw} (hD : D.Nodup) (hDm : ∀ x, x ∈ D ↔ x ∈ zipRaw C Q N) :
    GraphOK C Q N ⟨N.arcs.length + 3, starList ztfii N.arcs.length, D⟩ where
  three_le := by_simp
  arcs_le := by_simp
  I_nodup := starList_nodup _ _
  O_nodup := hD
  I_ok := fun c hc => by
    zufxz
    refine ⟨by_omega, by_grind, fun h => ?_⟩
    grind
  O_ok := fun c hc => by
    obtain ⟨h1, h2, -⟩ := zipRaw_sound hN hP ztost
    refine ⟨h1, by_grind, fun h => ?_⟩
    simp_all
  I_star := fun c hc => by
    zufxz
    obtain ⟨f1, f2, f3⟩ := fpos_spec ztfii c.2
    refine ⟨by_omega, h1, by_simp_all, fun q _ hq => ?_⟩
    simp_all
  O_zip := fun c hc => by
    obtain ⟨h1, h2, h3⟩ := zipRaw_sound hN hP ztost
    exact ⟨by_omega, h2, h3⟩
  I_complete := fun p hp => by
    obtain ⟨f1, f2, f3⟩ := fpos_spec ztfii p
    refine ⟨fpos ztfii p, by_omega, f1, fun q _ hq => f3 q hq, ?_⟩
    rcases starList_complete ztfii hp with h | h | h
    · omega
    · simp_all
    tauto
  O_complete := fun p q hpq hq hZ => by
    rcases zipRaw_complete hN hP hpq hq hZ with h | h
    · tauto
    simp_all
end OracleQ
end
namespace OracleR
@[expose] public section
def PLt (x y : ℕ × ℕ) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)
variable (M : ℕ) (G K s : ℕ → ℕ)

/-- The sequence is a sorted enumeration of the darts. -/
structure SortedDarts : Prop where
  lt : ∀ t, t < M → s t < M
  surj : ∀ d, d < M → ∃ t, t < M ∧ s t = d
  sorted : ∀ t t', t < t' → t' < M → PLt ztzby ztzbx
open Classical in
/-- The first position of vertex `v` in the sequence. -/
noncomputable def fpN (v : ℕ) : ℕ :=
  if h : ∃ t, t < M ∧ G ztkc = v then Nat.find h else 0
open Classical in
/-- **The rotation at position `t`.** -/
noncomputable def rotN (t : ℕ) : ℕ :=
  if t + 1 < M ∧ G (s ztbx) = G ztkc then s ztbx else s ztbama
variable {M G K s}
theorem fpN_spec (_h : SortedDarts M G K s) {t : ℕ} (ht : t < M) :
    fpN M G s ztwwy < M ∧ G (s ztbama) = G ztkc ∧
      ∀ t', t' < M → G ztfil = G ztkc → fpN M G s ztwwy ≤ t' := by
  classical
  have hex : ∃ t', t' < M ∧ G ztfil = G ztkc := ztbik
  zudwg

  exact ⟨a, b, fun t' ht' e => Nat.find_min' hex ⟨ht', e⟩⟩

/-- Positions are ordered like the pairs. -/
theorem pos_lt_of (h : SortedDarts M G K s) {t t' : ℕ} (ht : t < M) (_ht' : t' < M)
    (hp : PLt ztzby ztzbx) : t < t' := by
  zukr
  rcases eq_or_lt_of_le (not_lt.1 hc) with e | e
  · subst e; unfold PLt at hp; omega
  · have := h.sorted t' t e ht
    unfold PLt at hp this; omega

/-- **The rotation is the cyclic successor in key order.** -/
theorem rotN_spec (h : SortedDarts M G K s) {t : ℕ} (ht : t < M) :
    rotN M G s t < M ∧ G ztgls = G ztkc ∧
      ((K ztkc < K ztgls ∧ ∀ f, f < M → G f = G ztkc → K ztkc < K f →
          K ztgls ≤ K f) ∨
        ((∀ f, f < M → G f = G ztkc → K f ≤ K ztkc) ∧
          ∀ f, f < M → G f = G ztkc → K ztgls ≤ K f)) := by
  unfold rotN
  split_ifs with hn
  · obtain ⟨h1, h2⟩ := hn
    refine ⟨h.lt _ h1, h2, Or.inl ⟨?_, fun f hf hg hk => ?_⟩⟩
    · have := h.sorted t ztbx by_omega h1
      zugin
    · zucea
      have hlt : t < t' := pos_lt_of h ht ht' (Or.inr ⟨hg.symm, hk⟩)
      zujdq
      · simp_all
      · have := h.sorted ztbx t' e ht'
        zugin
  · obtain ⟨f1, f2, f3⟩ := fpN_spec h ht
    refine ⟨h.lt _ f1, f2, Or.inr ⟨fun f hf hg => ?_, fun f hf hg => ?_⟩⟩
    · zucea
      zukr
      have hlt : t < t' := pos_lt_of h ht ht' (Or.inr ⟨hg.symm, by_omega⟩)
      apply hn
      zubsc
      have a := h.sorted t ztbx by_omega by_omega
      zujdq
      · simp_all
      · have b := h.sorted ztbx t' e ht'
        unfold PLt at a b; omega
    · zucea
      have hle := f3 t' ht' hg
      rcases eq_or_lt_of_le hle with e | e
      · zui
      · have := h.sorted _ t' e ht'
        zugin
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open OracleBook OracleBook.BookData
@[expose] public section
variable {M : ℕ}
theorem inj_of_surj {s : ℕ → ℕ} (hlt : ∀ t, t < M → s t < M)
    (hs : ∀ d, d < M → ∃ t, t < M ∧ s t = d) {t t' : ℕ} (ht : t < M) (ht' : t' < M)
    (h : s t = s t') : t = t' := by
  let f : Fin M → Fin M := fun x => ⟨s x, hlt x x.2⟩
  have hsurj : Function.Surjective f := fun d => by
    obtain ⟨t, ht, e⟩ := hs d d.2
    exact ⟨ztujn, Fin.ext e⟩
  have hinj := Finite.injective_iff_surjective.2 hsurj
  have := hinj (a₁ := ztujn) (a₂ := ⟨t', ht'⟩) ztmay
  simp_all
theorem sortedDarts_of {G K s : ℕ → ℕ}
    (hsort : SortedSeq (fun d => (G d, K d)) s M) (hlt : ∀ t, t < M → s t < M)
    (hs : ∀ d, d < M → ∃ t, t < M ∧ s t = d)
    (hinj : ∀ d d', d < M → d' < M → G d = G d' → K d = K d' → d = d') :
    SortedDarts M G K s := by
  refine ⟨hlt, hs, fun t t' htt ht' => ?_⟩
  have h := hsort t t' htt.le ht'
  unfold PLe at h; unfold PLt; simp only at h ⊢
  zulv
  · omega
  · zujdn
    · have := hinj _ _ (hlt t by_omega) (hlt t' ht') h1 e
      exact absurd (inj_of_surj hlt hs by_omega ht' this) by_omega
    omega
variable {B : BookData}

/-- **The rotation of the sorted darts is the rotation of the book map.** -/
theorem rot_eq_csucc (hV : B.Valid) {s : ℕ → ℕ}
    (h : SortedDarts ztbck ztxcn ztywa s)
    {t : ℕ} (ht : t < 2 * B.E) :
    (csucc (gN (B := B)) (kN (B := B)) ztpfu).1 =
      rotN ztbck ztxcn s t := by
  obtain ⟨hl, hg, hc⟩ := rotN_spec h ht
  have := csucc_eq ztqsk (d := ztpfu) (e := ⟨_, hl⟩) hg (by
    rcases hc with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a, fun f hf hk => b f.1 f.2 hf hk⟩
    · exact Or.inr ⟨fun f hf => a f.1 f.2 hf, fun f hf => b f.1 f.2 hf⟩)
  simp_all

/-- **The book map in memory is a planar map.** -/
theorem planarMapAt_of_arrays (hV : B.Valid) {m : ℕ → ℕ} {Bh : ℕ}
    (hopp : ∀ d, d < 2 * B.E → m ztlrd = oppN d)
    (hrot : ∀ d (hd : d < 2 * B.E), m (m ztsvl + d) = (csucc (gN (B := B)) (kN (B := B)) ztpw).1)
    (hvt : ∀ d, d < 2 * B.E → m ztgky = View.tail B.N ztbgk) :
    PlanarMapAt m Bh B.N B.E :=
  ⟨FaceT hV, inferInstance, inferInstance, B.map hV, B.planar hV,
    fun d => ⟨hopp d d.2, hrot d d.2, hvt d d.2⟩⟩

/-- **The graph of the map in memory is the graph of the book.** -/
theorem memGraph_eq {m : ℕ → ℕ} {Bh : ℕ}
    (hopp : ∀ d, d < 2 * B.E → m ztlrd = oppN d)
    (hvt : ∀ d, d < 2 * B.E → m ztgky = View.tail B.N ztbgk) :
    memGraph m Bh B.N B.E = OracleQ.bookGraph B := by
  have hdart : ∀ u v : ℕ, MemDart m Bh B.E u v ↔ OracleQ.BookAdj B u v := by
    intro u v
    constructor
    · zufmf

      rw [hopp d hd, hvt _ ztwbc, view_oppN, View.tail_rev] at h2
      zucvi
    · zufmf

      rw [hopp d hd, hvt _ ztwbc, view_oppN, View.tail_rev, h2]
  ext u v
  simp only [memGraph, OracleQ.bookGraph, hdart]
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData
@[expose] public section
def eU (N : ℕ) (L : List ztw) (e : ℕ) : ℕ := if e < N then e else (L.getD zttjj ztdr).1

/-- The second end of edge `e`. -/
def eV (N : ℕ) (L : List ztw) (e : ℕ) : ℕ :=
  if e < N then (if e + 1 < N then e + 1 else 0) else (L.getD zttjj ztdr).2

/-- The kind of edge `e`. -/
def eKind (N nI e : ℕ) : ℕ := if e < N then 0 else if e - N < nI then 1 else 2

/-- The key of the dart `2 e`. -/
def dKey0 (N k u v : ℕ) : ℕ := if k = 0 then 0 else if k = 1 then v - u else 2 * N - 2 - ztbnr

/-- The key of the dart `2 e + 1`. -/
def dKey1 (N k u v : ℕ) : ℕ :=
  if k = 0 then N - 1 else if k = 1 then N - v + u else N - 2 + ztbnr
theorem getD_I {B : BookData} {j : ℕ} (hj : j < B.I.length) :
    B.I.getD j ztdr = (B.I ++ B.O).getD j ztdr := by_grind
theorem getD_O {B : BookData} {j : ℕ} (hj : B.I.length ≤ j) :
    B.O.getD (j - B.I.length) ztdr = (B.I ++ B.O).getD j ztdr :=
  by grind

/-- **The even dart of an edge.** -/
theorem view_even (B : BookData) (_hV : B.Valid) {e : ℕ} (_he : e < B.E) :
    View.tail B.N ztbadt = eU B.N ztclc e ∧
      View.key B.N ztbadt =
        dKey0 B.N ztrpb ztzll ztzlm := by
  have h2 : 2 * e / 2 = e := by_omega
  have h3 : 2 * e % 2 = 0 := by_omega
  zuefa
  zuczw
  zujry
  · rw [ite_eq_left a, ite_eq_left h3]; simp [View.tail, View.key, eU, eKind, dKey0, a]
  · zulqa
    have hL : B.I.length ≤ e - B.N ∨ e - B.N < B.I.length := by_omega
    zuhsa
    · rw [ite_eq_left b, ite_eq_left h3, getD_I by_omega]
      simp [View.tail, View.key, eU, eV, eKind, dKey0, a, show e - B.N < B.I.length by omega]
    · rw [ite_eq_right b, ite_eq_left h3, show e - B.N - B.I.length = ztnxo - B.I.length by omega,
        getD_O by_omega]
      simp [View.tail, View.key, eU, eV, eKind, dKey0, a, show ¬ e - B.N < B.I.length by omega]

/-- **The odd dart of an edge.** -/
theorem view_odd (B : BookData) (hV : B.Valid) {e : ℕ} (he : e < B.E) :
    View.tail B.N ztbads = eV B.N ztclc e ∧
      View.key B.N ztbads =
        dKey1 B.N ztrpb ztzll ztzlm := by
  have h2 : ztgcg / 2 = e := by_omega
  have h3 : ¬ ztgcg % 2 = 0 := by_omega
  zuefa
  zuczw
  zujry
  · rw [ite_eq_left a, ite_eq_right h3]
    zujx
    · simp only [View.tail, eV, ite_eq_left a]
      zus
      · zubql
      · rw [show e + 1 = B.N by omega, Nat.mod_self]
    · simp [View.key, eKind, dKey1, a]
  · zulqa
    zuhsa
    · rw [ite_eq_left b, ite_eq_right h3, getD_I by_omega]
      simp only [View.tail, View.key, eU, eV, eKind, dKey1, ite_eq_right a,
        ite_eq_left (show e - B.N < B.I.length by omega)]
      simp
    · rw [ite_eq_right b, ite_eq_right h3, show e - B.N - B.I.length = ztnxo - B.I.length by omega,
        getD_O by_omega]
      simp only [View.tail, View.key, eU, eV, eKind, dKey1, ite_eq_right a,
        ite_eq_right _]
      refine ⟨trivial, ?_⟩
      -- the outer chords have increasing ends
      have hmem : (B.I ++ B.O).getD ztnxo ztdr ∈ B.O := by
        rw [← getD_O by_omega]
        exact getD_mem (by unfold E at he; omega)
      obtain ⟨h1, -, -⟩ := hV.2.2.2.2.1 _ hmem
      grind

/-! ## The ends of an edge on the RAM -/

/-- The ends (`60031`, `60032`) and the kind (`60033`) of the edge in `60030`. -/
def edgeS : Stmt :=
  .ifLtN 60030 60034
    (.seq (block [.copyN 60031 60030, .addN 60032 60030 120011])
      (.seq (.ifLtN 60032 60034 .skip (.instr (.constN 60032 0))) (.instr (.constN 60033 0))))
    (.seq (block [.subN 60035 60030 60034, .addN 60036 60001 60035, .loadN 60031 60036,
        .addN 60036 60002 60035, .loadN 60032 60036])
      (.ifLtN 60035 60008 (.instr (.constN 60033 1)) (.instr (.constN 60033 2))))

/-- The registers written by `edgeS`. -/
def BEd (r : ℕ) : Bool := decide ((60031 ≤ r ∧ r ≤ 60033) ∨ r = 60035 ∨ r = 60036)
variable {P : Polygon} {W : ℕ} {c : Config}
theorem edgeS_exec (hw : WordsBounded W c) {N nI CH1 CH2 e : ℕ}
    {L : List ztw} (hN : c.nreg 60034 = N) (hI : c.nreg 60008 = nI) (h1 : c.nreg 60001 = CH1)
    (h2 : c.nreg 60002 = CH2) (hone : c.nreg 120011 = 1) (he : c.nreg 60030 = e)
    (heL : e < N + L.length) (hP : PairsAt c.nmem CH1 CH2 L) (hW1 : CH1 + L.length ≤ W)
    (hW2 : CH2 + L.length ≤ W) (hNW : N + 2 ≤ W) :
    ∃ c' k, Exec P W edgeS c c' k ∧ k ≤ 12 ∧ FrameB BEd c c' ∧ c'.nreg 60031 = eU N L e ∧
      c'.nreg 60032 = eV N L e ∧ c'.nreg 60033 = eKind N nI e := by
  have hwr : wr BEd edgeS = true := by_decide
  suffices H : ∃ c' k, Exec P W edgeS c c' k ∧ k ≤ 12 ∧ c'.nreg 60031 = eU N L e ∧
      c'.nreg 60032 = eV N L e ∧ c'.nreg 60033 = eKind N nI e by
    zucsn

  unfold edgeS eU eV eKind
  by_cases hs : e < N
  · zudd
    refine spec_seq ?_
    exec_block
    · config_simp; omega
    · zujl
      by_cases h' : e + 1 < N
      · refine spec_ifLtN_true by_simp_all (spec_skip ‹_› ?_)
        refine spec_instr ztemn fun _ => ztcbn <;>
          config_simp <;> simp [hs, h', he, hone]
      · refine spec_ifLtN_false by_simp_all
          (spec_instr (Exec.constN ‹_› _ 0 ztbg) fun _ => ?_)
        refine spec_instr ztemn fun _ => ztcbn <;>
          config_simp <;> simp [hs, h', he]
  · zubv
    have hj : e - N < L.length := by_omega
    obtain ⟨p1, p2⟩ := hP _ hj
    refine spec_seq ?_
    exec_block
    · config_simp; omega
    · config_simp; omega
    · by_cases h' : e - N < nI
      · refine spec_ifLtN_true by_simp_all
          ztywr <;>
          config_simp <;> simp only [he, hN, h1, h2, p1, p2, ite_eq_right hs, ite_eq_left h']
      · refine spec_ifLtN_false by_simp_all
          ztywr <;>
          config_simp <;> simp only [he, hN, h1, h2, p1, p2, ite_eq_right hs, ite_eq_right h']

/-! ## The values of the darts -/

/-- The address and the value of the dart array `k` (`0, 1`: vertices, `2, 3`: keys, `4, 5`:
opposite darts; even `k`: dart `2 e`, odd `k`: dart `2 e + 1`). -/
def dvS : ℕ → Stmt
  | 0 => block [.addN 60040 60030 60030, .addN 60040 60040 60050, .copyN 60041 60031]
  | 1 => block [.addN 60040 60030 60030, .addN 60040 60040 60050, .addN 60040 60040 120011,
      .copyN 60041 60032]
  | 2 => .seq (block [.addN 60040 60030 60030, .addN 60040 60040 60051, .subN 60042 60032 60031])
      (.ifLtN 60033 120011 (.instr (.constN 60041 0))
        (.ifLtN 60033 120048 (.instr (.copyN 60041 60042))
          (block [.addN 60041 60034 60034, .subN 60041 60041 120048, .subN 60041 60041 60042])))
  | 3 => .seq (block [.addN 60040 60030 60030, .addN 60040 60040 60051, .addN 60040 60040 120011,
        .subN 60042 60032 60031])
      (.ifLtN 60033 120011 (.instr (.subN 60041 60034 120011))
        (.ifLtN 60033 120048 (block [.subN 60041 60034 60032, .addN 60041 60041 60031])
          (block [.subN 60041 60034 120048, .addN 60041 60041 60042])))
  | 4 => block [.addN 60040 60030 60030, .addN 60040 60040 60052, .addN 60041 60030 60030,
      .addN 60041 60041 120011]
  | _ => block [.addN 60040 60030 60030, .addN 60040 60040 60052, .addN 60040 60040 120011,
      .addN 60041 60030 60030]

/-- The base register of the dart array `k`. -/
def dBase (k : ℕ) : ℕ := if k < 2 then 60050 else if k < 4 then 60051 else 60052

/-- The value of the dart array `k`. -/
def dVal (k N e u v kd : ℕ) : ℕ :=
  if k = 0 then u else if k = 1 then v else if k = 2 then dKey0 N kd u v
  else if k = 3 then dKey1 N kd u v else if k = 4 then 2 * e + 1 else 2 * e

/-- The registers written by `dvS`. -/
def BDV (r : ℕ) : Bool := decide (60040 ≤ r ∧ r ≤ 60042)
theorem dvS_exec (hw : WordsBounded W c) {k : ℕ} (hk : k < 6)
    {N e u v kd base : ℕ} (hb : c.nreg ztvow = base) (he : c.nreg 60030 = e)
    (hu : c.nreg 60031 = u) (hv : c.nreg 60032 = v) (hkd : c.nreg 60033 = kd) (hkd2 : kd ≤ 2)
    (hN : c.nreg 60034 = N) (h1 : c.nreg 120011 = 1) (h2 : c.nreg 120048 = 2) (huN : u ≤ N)
    (hvN : v ≤ N) (hNW : 2 * N + 2 ≤ W) (hbW : base + 2 * e + 2 ≤ W) :
    ∃ c' kk, Exec P W ztmit c c' kk ∧ kk ≤ 12 ∧ FrameB BDV c c' ∧
      c'.nreg 60040 = base + 2 * e + k % 2 ∧ c'.nreg 60041 = dVal k N e u v kd := by
  have hwr : wr BDV ztmit = true := by interval_cases k <;> decide
  suffices H : ∃ c' kk, Exec P W _ c c' kk ∧ kk ≤ 12 ∧
      c'.nreg 60040 = base + 2 * e + k % 2 ∧ c'.nreg 60041 = dVal k N e u v kd by
    obtain ⟨c', kk, ex, hkk, a, b⟩ := H
    exact ⟨c', kk, ex, hkk, exec_frameB ex hwr, a, b⟩
  interval_cases k <;> simp only [dBase] at hb <;> norm_num at hb <;> unfold dvS dVal
  · exec_block
    · omega
    · config_simp; omega
    · exact ⟨by_omega, by config_simp; omega, by_simp_all⟩
  · exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · exact ⟨by_omega, by config_simp; omega, by_simp_all⟩
  · refine spec_seq ?_
    exec_block
    · omega
    · config_simp; omega
    · simp only [dKey0]
      zujrz
      · refine spec_ifLtN_true by_simp_all
          (spec_instr (Exec.constN ‹_› _ _ ztbg) fun _ => ztss)
        · config_simp; omega
        simp_all
      · zudx
        zujsa
        · refine spec_ifLtN_true by_simp_all
            (spec_instr ztowy fun _ => ztss)
          · config_simp; omega
          simp_all
        · refine spec_ifLtN_false (by config_simp; omega) ?_
          exec_block
          · config_simp; omega
          · zujfy
            · config_simp; omega
            · config_simp; grind
  · refine spec_seq ?_
    exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · simp only [dKey1]
      zujrz
      · refine spec_ifLtN_true by_simp_all
          (spec_instr zthao fun _ => ztss)
        · config_simp; omega
        simp_all
      · zudx
        zujsa
        · zuek
          exec_block
          · config_simp; omega
          · zujfy
            · config_simp; omega
            simp_all
        · refine spec_ifLtN_false (by config_simp; omega) ?_
          exec_block
          · config_simp; omega
          · zujfy
            · config_simp; omega
            simp_all
  · exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · exact ⟨by_omega, by config_simp; omega, by config_simp; grind⟩
  · exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · exact ⟨by_omega, by config_simp; omega, by config_simp; grind⟩

/-! ## One pass over the edges -/

/-- The environment of the passes. -/
structure DartEnv (N nI CH1 CH2 VT E lo : ℕ) (L : List ztw) (c : Config) : Prop where
  rN : c.nreg 60034 = N
  rI : c.nreg 60008 = nI
  r1 : c.nreg 60001 = CH1
  r2 : c.nreg 60002 = CH2
  one : c.nreg 120011 = 1
  two : c.nreg 120048 = 2
  rV : c.nreg 60050 = VT
  rK : c.nreg 60051 = VT + 2 * E
  rO : c.nreg 60052 = VT + 4 * E
  rE : c.nreg 60037 = E
  pairs : PairsAt c.nmem CH1 CH2 L
  hE : E = N + L.length
  hC1 : CH1 + L.length ≤ lo
  hC2 : CH2 + L.length ≤ lo
  hlo : lo ≤ VT
  ends : ∀ t, t < L.length → (L.getD t ztdr).1 ≤ N ∧ (L.getD t ztdr).2 ≤ N
  hI : nI ≤ L.length

/-- The registers the passes keep. -/
def DKeep (r : ℕ) : Bool :=
  decide (r = 60034) || decide (r = 60008) || decide (r = 60001) || decide (r = 60002) ||
    decide ztoge || decide (r = 120048) || decide (60050 ≤ r ∧ r ≤ 60052) ||
    decide (r = 60037)
theorem DartEnv.stable {N nI CH1 CH2 VT E lo : ℕ} {L : List ztw} {c c' : Config}
    (h : DartEnv N nI CH1 CH2 VT E lo L c) (hr : ∀ r, DKeep r = true → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < lo → c'.nmem a = c.nmem a) : DartEnv N nI CH1 CH2 VT E lo L c' where
  rN := by zumwn; exact h.rN
  rI := by zumwn; exact h.rI
  r1 := by zumwn; exact h.r1
  r2 := by zumwn; exact h.r2
  one := by zumwn; exact h.one
  two := by zumwn; exact h.two
  rV := by zumwn; exact h.rV
  rK := by zumwn; exact h.rK
  rO := by zumwn; exact h.rO
  rE := by zumwn; exact h.rE
  pairs := PairsAt.congr h.pairs fun t ht => ⟨hm _ (by have := h.hC1; omega),
    hm _ (by have := h.hC2; omega)⟩
  hE := h.hE
  hC1 := h.hC1
  hC2 := h.hC2
  hlo := h.hlo
  ends := h.ends
  hI := h.hI
theorem DKeep_B {r : ℕ} (h : DKeep r = true) : (BEd r || BDV r) = false ∧ r ≠ 60030 := by
  unfold DKeep at h; unfold BEd BDV
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h ⊢
  omega

/-- One pass: the dart array `k` over the edges. -/
def passS (k : ℕ) : Stmt := scatS 60030 60037 120011 60040 60041 (.seq edgeS ztmit)

/-- The base of the dart array `k`. -/
def dBaseV (VT E k : ℕ) : ℕ := if k < 2 then VT else if k < 4 then VT + 2 * E else VT + 4 * E
theorem passS_exec (hw : WordsBounded W c) {k : ℕ} (hk : k < 6)
    {N nI CH1 CH2 VT E lo : ℕ} {L : List ztw} (h : DartEnv N nI CH1 CH2 VT E lo L c)
    (hNW : 2 * N + 2 ≤ W) (hVW : VT + 6 * E + 2 ≤ W) :
    ∃ c' kk, Exec P W (passS k) c c' kk ∧ kk ≤ E * 40 + 3 ∧
      ztfab ∧
      ztfyw ∧
      c'.nmem = scat c.nmem zthgx
        ztecg E ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ DartEnv N nI CH1 CH2 VT E lo L c' := by
  have hB : ∀ r, (BEd r || BDV r) = false → BEd r = false ∧ BDV r = false := by_simp_all
  obtain ⟨c', kk, ex, hkk, r', rr', mm, rm, o, J', -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60030) (rn := 60037) (r1 := 120011) (ra := 60040) (rv := 60041)
    (body := .seq edgeS ztmit) (B := fun r => BEd r || BDV r) by_decide by_decide
    by_decide by_decide by_decide (DartEnv N nI CH1 CH2 VT E lo L) lo
    (fun d d' hJ hr hm => hJ.stable (fun r hr' => hr r (DKeep_B hr').1 (DKeep_B hr').2) hm)
    (n := E) (κ := 36) zthgx
    ztecg
    (fun i _ => by
      show lo ≤ dBaseV VT E k + 2 * i + k % 2
      have := h.hlo; unfold dBaseV; grind)
    (fun i d hi hJ hwd hri => by
      obtain ⟨d₁, k₁, e₁, hk₁, f₁, v1, v2, v3⟩ := edgeS_exec (P := P) hwd hJ.rN hJ.rI hJ.r1 hJ.r2 hJ.one hri
        (by rw [← hJ.hE]; exact hi) hJ.pairs (by have := hJ.hC1; have := hJ.hlo; omega)
        (by have := hJ.hC2; have := hJ.hlo; omega) by_omega
      have K : ∀ r, DKeep r = true → d₁.nreg r = d.nreg r := fun r hr => f₁.1 r (by
        have := (DKeep_B hr).1; simp_all)
      have hJ₁ := hJ.stable K ztdnq
      have hkd : eKind N nI i ≤ 2 := by unfold eKind; grind
      have huN : eU N L i ≤ N := by
        unfold eU; split_ifs with a
        · omega
        · exact (hJ.ends _ ztlhm).1
      have hvN : eV N L i ≤ N := by
        unfold eV; split_ifs with a b
        · omega
        · omega
        · exact (hJ.ends _ ztlhm).2
      have hb : d₁.nreg ztvow = dBaseV VT E k := by
        unfold dBase dBaseV
        split_ifs
        · exact hJ₁.rV
        · exact hJ₁.rK
        · exact hJ₁.rO
      obtain ⟨d₂, k₂, e₂, hk₂, f₂, a2, b2⟩ := dvS_exec (P := P) (e := i) e₁.wb_right hk hb
        (by zuomh; omega) v1 v2 v3 hkd hJ₁.rN hJ₁.one hJ₁.two huN hvN hNW
        (by unfold dBaseV; grind)
      have ex : Exec P W _ d d₂ _ := .seq e₁ e₂
      refine ⟨d₂, _, ex, by_omega, (FrameB.mono f₁ by_simp_all).trans
        (FrameB.mono f₂ by_simp_all), a2, b2⟩)
    hw h h.rE h.one by_omega
  exact ⟨c', kk, ex, by_nlinarith, by_simp_all,
    by simp_all, mm, rm, o, J'⟩

/-! ## The six passes -/

/-- The first `j` passes. -/
def passesS : ℕ → Stmt
  | 0 => .skip
  | j + 1 => .seq ztwbp (passS j)

/-- The dart arrays `k < j` are written. -/
def DArr (N nI VT E : ℕ) (L : List ztw) (j : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ k, k < j → ∀ e, e < E →
    m (dBaseV VT E k + 2 * e + k % 2) = dVal k N e (eU N L e) (eV N L e) (eKind N nI e)
theorem dAddr_ne {VT E k k' e e' : ℕ} (hk : k < 6) (hk' : k' < 6) (he : e < E) (he' : e' < E)
    (hne : k ≠ k' ∨ e ≠ e') :
    dBaseV VT E k + 2 * e + k % 2 ≠ dBaseV VT E k' + 2 * e' + k' % 2 := by
  unfold dBaseV
  grind
theorem dAddr_range {VT E k e : ℕ} (_hk : k < 6) (he : e < E) :
    VT ≤ dBaseV VT E k + 2 * e + k % 2 ∧ dBaseV VT E k + 2 * e + k % 2 < VT + 6 * E := by
  unfold dBaseV; grind

/-- **The passes.** -/
theorem passesS_exec (hw : WordsBounded W c) {j : ℕ}
    (hj : j ≤ 6) {N nI CH1 CH2 VT E lo : ℕ} {L : List ztw}
    (h : DartEnv N nI CH1 CH2 VT E lo L c) (hNW : 2 * N + 2 ≤ W) (hVW : VT + 6 * E + 2 ≤ W) :
    ∃ c' kk, Exec P W ztwbp c c' kk ∧ kk ≤ j * (E * 40 + 3) ∧
      ztfab ∧
      ztfyw ∧
      DArr N nI VT E L j c'.nmem ∧ (∀ a, (a < VT ∨ VT + 6 * E ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ DartEnv N nI CH1 CH2 VT E lo L c' := by
  induction j with
  | zero =>
    exact ⟨c, 0, .skip hw, by_omega, by_omega, by_simp_all,
      fun k hk => by_omega, by_omega, rfl, rfl, h⟩
  | succ j ih =>
    obtain ⟨c₁, k₁, e₁, hk₁, r₁, rr₁, D₁, m₁, rm₁, o₁, J₁⟩ := ih by_omega
    obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, m₂, rm₂, o₂, J₂⟩ :=
      passS_exec e₁.wb_right (k := j) by_omega J₁ hNW hVW
    refine ⟨c₂, _, .seq e₁ e₂, by_grind,
      by grind,
      by grind, ?_, ?_, rm₂.trans rm₁, o₂.trans o₁, J₂⟩
    · intro k hk e he
      zunbg
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [scat_other fun i hi => dAddr_ne by_omega by_omega hi he by_omega]
        exact D₁ k hk e he
      · exact scat_at he
          by_omega
    · zuge
      rw [m₂, scat_other fun i hi e => by
        have := dAddr_range (VT := VT) (k := j) by_omega hi; omega]
      grind

/-- **The dart arrays**: the tails at `VT`, the keys at `VT + 2 E`, the opposite darts at
`VT + 4 E`. -/
theorem darts_of (B : BookData) (hV : B.Valid) {VT : ℕ} {m : ℕ → ℕ}
    (h : DArr B.N B.I.length VT B.E ztclc 6 m) {d : ℕ} (hd : d < 2 * B.E) :
    m ztbjm = View.tail B.N ztbgk ∧ m (VT + 2 * B.E + d) = View.key B.N ztbgk ∧
      m ztnqf = oppN d := by
  have he : d / 2 < B.E := by_omega
  rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
  · have hd' : d = 2 * ztcmw := by_omega
    obtain ⟨a, b⟩ := view_even B hV he
    have x0 := h 0 by_omega _ he
    have x2 := h 2 by_omega _ he
    have x4 := h 4 by_omega _ he
    simp only [dBaseV, dVal] at x0 x2 x4
    norm_num at x0 x2 x4
    zusk
    · grind
    · grind
    · rw [show VT + 4 * B.E + d = VT + 4 * B.E + 2 * ztcmw by omega, x4]
      zufdk
  · have hd' : d = 2 * ztcmw + 1 := by_omega
    obtain ⟨a, b⟩ := view_odd B hV he
    have x1 := h 1 by_omega _ he
    have x3 := h 3 by_omega _ he
    have x5 := h 5 by_omega _ he
    simp only [dBaseV, dVal] at x1 x3 x5
    norm_num at x1 x3 x5
    zusk
    · grind
    · grind
    · rw [show VT + 4 * B.E + d = VT + 4 * B.E + 2 * ztcmw + 1 by omega, x5]
      zufdk
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
@[expose] public section
def sortCore : Stmt :=
  .seq itemS (.seq sortSet (.seq ztvdi ztovs))
theorem sortCore_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {Z1 Z2 n A₀ : ℕ} (h4 : c.nreg 60004 = Z1) (h5 : c.nreg 60005 = Z2)
    (h6 : c.nreg 60006 = n) (h1 : c.nreg 120011 = 1) (hAl : c.nreg 9999 = A₀)
    (hZ1 : Z1 + n ≤ A₀) (hZ2 : Z2 + n ≤ A₀)
    (hroom : A₀ + n + SortR.sortCost 20 n ≤ W) :
    ∃ c' k, Exec P W sortCore c c' k ∧ k ≤ 7 * n + SortR.sortCost 20 n + 20 ∧
      FrameN dBands c c' ∧ A₀ + n ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + n + SortR.sortCost 20 n ∧
      (∀ r, bandOf r = 6 → r ≠ 60007 → r ≠ 60016 → r ≠ 60017 → r ≠ 60020 →
        c'.nreg r = c.nreg r) ∧
      A₀ + n ≤ c'.nreg 60007 ∧ c'.nreg 60007 + n ≤ c'.nreg 9999 ∧
      SortedSeq ztyev ztzfu n ∧
      ztxey ∧
      ztxzg := by
  -- 1. the items
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      ztctx c c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg = upd (upd c.nreg 30003 A₀) 9999 ztsva ∧ c₂.nmem = c.nmem ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    exec_block
    · config_simp; omega
    simp_all
  zudct

  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, mm₃, rm₃, o₃, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60020) (rn := 60006) (r1 := 120011) (ra := 60016) (rv := 60017)
    (body := block [.addN 60016 30003 60020, .copyN 60017 60020])
    (B := fun r => decide zthka) by_decide by_decide by_decide by_decide
    by_decide ztdky A₀
    (fun d d' hJ hr hm => JK.stable (rs := [60020]) (fun r hr' => by
      simp_all) hJ
      ztdod hm)
    (n := n) (κ := 2) ztijn ztfrq ztbeo
    (fun i d hi hJ hwd hri => by
      zuegc
      obtain ⟨d', k, e, hk, v1, v2⟩ : ∃ d' k, Exec P W (block [.addN 60016 30003 60020,
          .copyN 60017 60020]) d d' k ∧ k = 2 ∧ d'.nreg 60016 = A₀ + i ∧ d'.nreg 60017 = i := by
        exec_block
        · omega
        simp_all
      exact ztdjb)
    e₂.wb_right ztdkz a6 a11 by_omega
  have R₃ : ztcqm := fun r a b c' =>
    r₃ r by_simp_all c'
  -- 2. the inputs of the sort
  obtain ⟨c₄, k₄, e₄, hk₄, n₄⟩ : ∃ c₄ k₄, Exec P W sortSet c₃ c₄ k₄ ∧ k₄ = 4 ∧
      c₄.nreg = upd ztibm 115005 n := by
    zubj
    zujwu
    have b4 : ztusg := by
      simp_all
    have b5 : ztush := by
      simp_all
    unfold sortSet
    exec_block
    grind
  have hm₄ : ztmvj :=
    (exec_frameB e₄ (B := fun r => decide ztsi) by_decide).2.2.1
  have R₄ : ztfdw := fun r a b => by
    zufob
  have g9 : ztrgn := by
    simp_all
  have g30 : ztpnr := by
    simp_all
  have hitems : ztios := by
    zugy

    exact scat_at (g := fun i => A₀ + i) (f := fun i => i) h1 (fun j _ hj => by_omega)
  -- 3. the sort
  zukao
  have hmem₄ : ztced := fun a ha => by
    rw [hm₄, mm₃, scat_below ztbeo ha, m₂]
  obtain ⟨c₅, k₅, e₅, hk₅, J₅, F₅, s₁, s₂, L', hseg, hperm, hpw⟩ := SortR.sortStmt_exec (P := P)
    (W := W) (lexCmp_ok (m₀ := c₄.nmem) (A₀ := A₀ + n) (B1 := Z1) (B2 := Z2) (K := n)
      by_omega by_omega (by have := SortR.sortCost_ge 20 n; omega) hW') by_decide
    ztgiu ztqsz
    e₄.wb_right ⟨by zungn; config_simp, by zungn; config_simp, by zungn; config_simp,
      fun _ _ => rfl⟩ (by zuncx; exact lexJ_stable _ _ _ _ _) (List.range n) hitems
    ztnuh ztgra ztgrb
  zubeg

  -- 4. the base of the sorted items

  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 60007 (c₅.nreg 30005) } with hc₆
  have ex : Exec P W sortCore c c₆ _ := .seq ztcr ztxjw
  have hF5 : zteik := fun r hr =>
    F₅.1 r ztnuv ztche
  zufhu

  have hsd : ztgqe := fun t ht => by
    zueya
  zudyi
  have hmemL : ztkpb := fun t ht => by
    zujvu

  zuffp

  refine ⟨c₆, _, ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · -- the frame
    have F14 : ztukz := by
      refine PF.frameN (B := fun r => decide ztyc || decide ztgzi ||
        decide ztgyw || decide ztneb)
        ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_⟩ ztez ?_
      · zupg
        rw [R₄ r by_omega by_omega, R₃ r by_omega by_omega by_omega, n₂]
        zubd
      · have := (exec_frameB e₄ (B := fun r => decide ztsi)
          by_decide).2.1 r by_grind
        rw [this, rr₃ r by_grind,
          rr₂]
      · grind
      · rw [(exec_frameB e₄ (B := fun r => decide ztsi)
          by_decide).2.2.2.1, rm₃, rm₂]
      · rw [(exec_frameB e₄ (B := fun r => decide ztsi)
          by_decide).2.2.2.2, o₃, o₂]
      · zufw
        zuws
        · zuhcq
        · zufic
        · zufie
        · zufid
      · have := (exec_frameB e₄ (B := fun r => decide ztsi)
          by_decide).2.1 ALLOC by_decide
        rw [this, rr₃ _ by_decide, rr₂]
    have F56 : ztula :=
      Frame.toN (NFLoc.frame_of_frameB (exec_frameB e₆ (B := fun r => decide zttxu)
        by_decide) (fun r hr => by
          simp at hr; subst hr; decide) 1)
    exact (F14.trans ztihd
      by_omega).trans F56
      by_omega
  · have := F₅.2.2.2.2.2.1; rw [g9'] at this
    zujis
  · have := F₅.2.2.2.2.2.2; rw [g9'] at this
    zufnl
  · intro r hr a b c' d
    rw [hc₆]; config_simp
    rw [upd_other _ _ _ a, hF5 r hr, R₄ r ztbej
      ztbej, R₃ r b c' d, n₂]
    rw [upd_other _ _ _ ztbej,
      upd_other _ _ _ ztbej]
  · omega
  · rw [v7, hc₆]; config_simp; exact s₂
  · -- sorted
    zubom

    have hc4 : ∀ i, i < n → c₄.nmem zthdf = c.nmem zthdf ∧ c₄.nmem zthdg = c.nmem zthdg :=
      fun i hi => ztook
    zujdp
    · zulaq
    · have := List.pairwise_iff_getElem.1 hpw t t' by_omega by_omega h
      zugz

  · zug
    have : ztsjf := hperm.symm.subset ztuzq
    zucoh
    exact ztgpq
  grind
def BR (r : ℕ) : Bool := decide (60064 ≤ r ∧ r ≤ 60070)

/-! ## The first positions -/

/-- The body of `fpS`: address `FPb + G (s (M - 1 - i))`, value `M - 1 - i`. -/
def fpBody : Stmt :=
  block [.subN 60065 60060 60063, .subN 60065 60065 120011, .addN 60067 60007 60065,
    .loadN 60067 60067, .addN 60067 60050 60067, .loadN 60067 60067, .addN 60064 60061 60067]
variable {P : Polygon} {W : ℕ} {c : Config} {M : ℕ} {G s G' s' : ℕ → ℕ}
theorem fpBody_exec (hw : WordsBounded W c)
    {Sb VT M FPb i : ℕ} (h7 : c.nreg 60007 = Sb) (h50 : c.nreg 60050 = VT)
    (h60 : c.nreg 60060 = M) (h61 : c.nreg 60061 = FPb) (h1 : c.nreg 120011 = 1)
    (hi : c.nreg 60063 = i) (hiM : i < M) (hSW : Sb + M ≤ W) (hVW : VT + M ≤ W)
    (hs : c.nmem ztbfw < M)
    (hFW : FPb + c.nmem ztxds ≤ W) :
    ∃ c' k, Exec P W fpBody c c' k ∧ k ≤ 7 ∧ FrameB BR c c' ∧
      c'.nreg 60064 = FPb + c.nmem ztxds ∧
      c'.nreg 60065 = M - 1 - i := by
  have hwr : wr BR fpBody = true := by_decide
  suffices H : ∃ c' k, Exec P W fpBody c c' k ∧ k ≤ 7 ∧
      c'.nreg 60064 = FPb + c.nmem _ ∧
      c'.nreg 60065 = M - 1 - i by
    zumr

  unfold fpBody
  exec_block
  · config_simp; omega
  · config_simp; grind
  · config_simp; grind
  · exact ⟨by_omega, by config_simp; grind, by config_simp; omega⟩

/-- The environment of `fpS`. -/
def FPJ (Sb VT M FPb : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop :=
  c.nreg 60007 = Sb ∧ c.nreg 60050 = VT ∧ c.nreg 60060 = M ∧ c.nreg 60061 = FPb ∧
    c.nreg 120011 = 1 ∧ ∀ a, a < FPb → c.nmem a = m₀ a

/-- **The first positions**: a scatter over `i < M`. -/
def fpS : Stmt := scatS 60063 60060 120011 60064 60065 fpBody
theorem fpS_exec (hw : WordsBounded W c)
    {Sb VT M FPb N : ℕ} (hJ : FPJ Sb VT M FPb c.nmem c) (hSF : Sb + M ≤ FPb) (hVF : VT + M ≤ FPb)
    (hs : ∀ t, t < M → c.nmem ztis < M) (hG : ∀ d, d < M → c.nmem ztbjm < N)
    (hFW : FPb + N ≤ W) :
    ∃ c' k, Exec P W fpS c c' k ∧ k ≤ M * 11 + 3 ∧
      ztgng ∧
      ztrf ∧
      c'.nmem = scat c.nmem ztbanx
        ztgjf M ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ FPJ Sb VT M FPb c.nmem c' := by
  obtain ⟨c', k, ex, hk, r', rr', mm, rm, o, J', -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60063) (rn := 60060) (r1 := 120011) (ra := 60064) (rv := 60065) (body := fpBody)
    (B := BR) by_decide by_decide by_decide by_decide by_decide
    (FPJ Sb VT M FPb c.nmem) FPb
    (fun d d' hJ hr hm => ⟨by zumxs; exact hJ.1,
      by zumxs; exact hJ.2.1,
      by zumxs; exact hJ.2.2.1,
      by zumxs; exact hJ.2.2.2.1,
      by zumxs; exact hJ.2.2.2.2.1,
      fun a ha => by zunps; exact hJ.2.2.2.2.2 a ha⟩)
    (n := M) (κ := 7) ztbanx
    ztgjf ztbeo
    (fun i d hi hJd hwd hri => by
      obtain ⟨a7, a50, a60, a61, a1, am⟩ := hJd
      have e1 : d.nmem _ = c.nmem ztbfw := am _ by_omega
      have hs' := hs ztpzv by_omega
      have e2 : d.nmem (VT + d.nmem ztbfw) =
          c.nmem ztxds := by_grind
      have hg' := hG _ hs'
      obtain ⟨d', k, ex, hk, F, v1, v2⟩ := fpBody_exec hwd a7 a50 a60 a61 a1 hri hi
        by_omega by_omega by_omega by_omega
      exact ⟨d', k, ex, hk, F, by_omega, v2⟩)
    hw hJ hJ.2.2.1 hJ.2.2.2.2.1 by_omega
  exact ztfvz
theorem fpN_spec' {G s : ℕ → ℕ} {t : ℕ} (ht : t < M) :
    fpN M G s ztwwy < M ∧ G (s ztbama) = G ztkc ∧
      ∀ t', t' < M → G ztfil = G ztkc → fpN M G s ztwwy ≤ t' := by
  classical
  have hex : ∃ t', t' < M ∧ G _ = G ztkc := ztbik
  zudwg

  exact ⟨a, b, fun t' ht' e => Nat.find_min' hex by_omega⟩
theorem fpN_congr (h : ∀ t, t < M → G ztkc = G' ztqvv) (v : ℕ) :
    fpN M G s v = fpN M G' s' v := by
  classical
  by_cases hex : ∃ t, t < M ∧ G ztkc = v
  · obtain ⟨t, ht, rfl⟩ := hex
    have e := h t ht
    obtain ⟨a1, a2, a3⟩ := fpN_spec' (G := G) (s := s) ht
    obtain ⟨b1, b2, b3⟩ := fpN_spec' (G := G') (s := s') ht
    grind
  · have hex' : ¬ ∃ t, t < M ∧ G' ztqvv = v := by_simp_all
    unfold fpN; grind

/-- **The first-position array** holds `fpN`. -/
theorem fp_scat {M FPb : ℕ} {G s g : ℕ → ℕ} (hg : ∀ i, i < M → g i = FPb + G (s ztpzv))
    (m : ℕ → ℕ) {t : ℕ} (ht : t < M) :
    scat m g ztgjf M (FPb + G ztkc) = fpN M G s ztwwy := by
  obtain ⟨f1, f2, f3⟩ := fpN_spec' (G := G) (s := s) ht
  set t₀ := fpN M G s ztwwy
  have ha : FPb + G ztkc = g ztjjr := by
    rw [hg _ by_omega, show M - 1 - ztjjr = t₀ by omega, f2]
  rw [ha, scat_at by_omega fun j hj hij e => by
    rw [hg _ hj, hg _ by_omega, show M - 1 - ztjjr = t₀ by omega, f2] at e
    have := f3 (M - 1 - j) by_omega by_omega
    omega]
  omega
theorem rotN_congr (hs : ∀ t, t < M → s t = s' t)
    (h : ∀ t, t < M → G ztkc = G' ztqvv) {t : ℕ} (ht : t < M) :
    rotN M G s t = rotN M G' s' t := by
  unfold rotN
  have e1 := fpN_congr h ztwwy
  have hf := (fpN_spec' (G := G) (s := s) ht).1
  grind
theorem SortedSeq.congr {pr pr' s : ℕ → ℕ} {n : ℕ} (h : SortedSeq (fun i => (pr i, pr' i)) s n)
    {q q' : ℕ → ℕ} (hq : ∀ t, t < n → pr ztkc = q ztkc ∧ pr' ztkc = q' ztkc) :
    SortedSeq (fun i => (q i, q' i)) s n := fun t t' htt ht' => by
  have := h t t' htt ht'
  grind

/-! ## The rotation -/

/-- `s t`, `ROTb + s t`, `G (s t)`, `t + 1`. -/
def rPre : Stmt :=
  block [.addN 60066 60007 60063, .loadN 60068 60066, .addN 60064 60062 60068,
    .addN 60067 60050 60068, .loadN 60067 60067, .addN 60069 60063 120011]

/-- `s (t + 1)` in `60065`, `G (s (t + 1))` in `60070`. -/
def rNext : Stmt :=
  block [.addN 60066 60066 120011, .loadN 60065 60066, .addN 60070 60050 60065,
    .loadN 60070 60070]

/-- `s (FP (G (s t)))` in `60065`. -/
def rFb : Stmt :=
  block [.addN 60070 60061 60067, .loadN 60070 60070, .addN 60070 60007 60070,
    .loadN 60065 60070]

/-- The body of `rotS`. -/
def rotBody : Stmt :=
  .seq rPre (.ifLtN 60069 60060
    (.seq rNext (.ifLtN 60070 60067 rFb (.ifLtN 60067 60070 rFb .skip))) rFb)

/-- The environment of `rotS` (memory `m₁` below `ROTb`). -/
def RotJ (Sb VT M FPb ROTb : ℕ) (m₁ : ℕ → ℕ) (c : Config) : Prop :=
  c.nreg 60007 = Sb ∧ c.nreg 60050 = VT ∧ c.nreg 60060 = M ∧ c.nreg 60061 = FPb ∧
    c.nreg 60062 = ROTb ∧ c.nreg 120011 = 1 ∧ ∀ a, a < ROTb → c.nmem a = m₁ a
theorem rPre_exec (hw : WordsBounded W c)
    {Sb VT ROTb t : ℕ} (h7 : c.nreg 60007 = Sb) (h50 : c.nreg 60050 = VT)
    (h62 : c.nreg 60062 = ROTb) (h1 : c.nreg 120011 = 1) (hi : c.nreg 60063 = t)
    (hb1 : Sb + t + 1 ≤ W) (hb2 : ROTb + c.nmem ztis ≤ W) (hb3 : VT + c.nmem ztis ≤ W) :
    ∃ c' k, Exec P W rPre c c' k ∧ k = 6 ∧
      FrameB ztecj c c' ∧
      c'.nreg 60066 = Sb + t ∧ c'.nreg 60064 = ROTb + c.nmem ztis ∧
      c'.nreg 60067 = c.nmem ztxne ∧ c'.nreg 60069 = t + 1 := by
  have hwr : wr ztecj
    rPre = true := by_decide
  suffices H : ∃ c' k, Exec P W rPre c c' k ∧ k = 6 ∧
      c'.nreg 60066 = Sb + t ∧ c'.nreg 60064 = ROTb + c.nmem _ ∧
      c'.nreg 60067 = c.nmem _ ∧ c'.nreg 60069 = t + 1 by
    zuchq

  unfold rPre
  exec_block
  · omega
  · simp_all
  · simp_all
  · config_simp; omega
  simp_all
theorem rNext_exec (hw : WordsBounded W c)
    {VT a : ℕ} (h50 : c.nreg 60050 = VT) (h1 : c.nreg 120011 = 1) (h66 : c.nreg 60066 = a)
    (hb1 : a + 1 ≤ W) (hb2 : VT + c.nmem ztdf ≤ W) :
    ∃ c' k, Exec P W rNext c c' k ∧ k = 4 ∧
      FrameB ztgjn c c' ∧
      c'.nreg 60065 = c.nmem ztdf ∧ c'.nreg 60070 = c.nmem (VT + c.nmem ztdf) := by
  have hwr : wr ztgjn rNext = true := by_decide
  suffices H : ∃ c' k, Exec P W rNext c c' k ∧ k = 4 ∧
      c'.nreg 60065 = c.nmem _ ∧ c'.nreg 60070 = c.nmem _ by
    obtain ⟨c', k, ex, hk, x, y⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, x, y⟩
  unfold rNext
  exec_block
  · omega
  · simp_all
  simp_all
theorem rFb_exec (hw : WordsBounded W c)
    {Sb FPb g : ℕ} (h7 : c.nreg 60007 = Sb) (h61 : c.nreg 60061 = FPb) (h67 : c.nreg 60067 = g)
    (hb1 : FPb + g ≤ W) (hb2 : Sb + c.nmem ztsxl ≤ W) :
    ∃ c' k, Exec P W rFb c c' k ∧ k = 4 ∧
      FrameB ztikf c c' ∧
      c'.nreg 60065 = c.nmem (Sb + c.nmem ztsxl) := by
  have hwr : wr ztikf rFb = true := by_decide
  suffices H : ∃ c' k, Exec P W rFb c c' k ∧ k = 4 ∧
      c'.nreg 60065 = c.nmem _ by
    obtain ⟨c', k, ex, hk, x⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, x⟩
  unfold rFb
  exec_block
  · omega
  · simp_all
  simp_all
theorem rotBody_exec (hw : WordsBounded W c)
    {Sb VT M FPb ROTb N t : ℕ} {m₁ : ℕ → ℕ} (hJ : RotJ Sb VT M FPb ROTb m₁ c)
    (hi : c.nreg 60063 = t) (ht : t < M) (hSR : Sb + M ≤ ROTb) (hVR : VT + M ≤ ROTb)
    (hFR : FPb + N ≤ ROTb) (hRW : ROTb + M ≤ W)
    (hs : ∀ t, t < M → m₁ ztis < M) (hG : ∀ d, d < M → m₁ ztbjm < N)
    (hfp : ∀ t, t < M → m₁ ztbapv =
      fpN M ztwrz ztwsb ztball)
    (hfpl : ∀ t, t < M → fpN M ztwrz ztwsb
      ztball < M) :
    ∃ c' k, Exec P W rotBody c c' k ∧ k ≤ 24 ∧ FrameB BR c c' ∧
      c'.nreg 60064 = ROTb + m₁ ztis ∧
      c'.nreg 60065 = rotN M ztwrz ztwsb t := by
  obtain ⟨a7, a50, a60, a61, a62, a1, am⟩ := hJ
  have hwr : wr BR rotBody = true := by_decide
  suffices H : ∃ c' k, Exec P W rotBody c c' k ∧ k ≤ 24 ∧
      c'.nreg 60064 = ROTb + m₁ _ ∧
      c'.nreg 60065 = rotN M (fun d => m₁ _) (fun t => m₁ _) t by
    zumr

  have mS : ∀ u, u < M → c.nmem _ = m₁ (Sb + u) := fun u hu => am _ by_omega
  have mV : ∀ d, d < M → c.nmem _ = m₁ ztbjm := fun d hd => am _ by_omega
  have mF : ∀ v, v < N → c.nmem _ = m₁ (FPb + v) := fun v hv => am _ by_omega
  have hst := hs t ht
  have hGt := hG _ hst
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, p66, p64, p67, p69⟩ := rPre_exec (P := P) hw a7 a50 a62 a1 hi
    by_omega by_grind by_grind
  rw [mS t ht] at p64 p67
  rw [mV _ hst] at p67
  have K₁ := fun r hr => F₁.1 r ztmz
  have m₁e := F₁.2.2.1
  -- the fallback: `s (fpN (G (s t)))`
  have fb : ∀ d, WordsBounded W d → d.nmem = c.nmem → d.nreg 60007 = Sb → d.nreg 60061 = FPb →
      d.nreg 60067 = m₁ ztwob → d.nreg 60064 = ROTb + m₁ ztis →
      ∃ d' k, Exec P W rFb d d' k ∧ k = 4 ∧ d'.nreg 60064 = ROTb + m₁ ztis ∧
        d'.nreg 60065 = m₁ (Sb + fpN M ztwrz ztwsb
          ztball) := by
    intro d hwd hm h7 h61 h67 h64
    have q1 : d.nmem ztbapv =
        fpN M ztwrz ztwsb ztball := by
      grind
    obtain ⟨d', k, ex, hk, F, v⟩ := rFb_exec (P := P) hwd h7 h61 h67 by_omega
      by_grind
    refine ⟨d', k, ex, hk, by rw [F.1 _ by_decide, h64], ?_⟩
    simp_all
  unfold rotBody
  by_cases hn : t + 1 < M
  · have hs1 := hs _ hn
    have hG1 := hG _ hs1
    obtain ⟨c₂, k₂, e₂, hk₂, F₂, x65, x70⟩ := rNext_exec e₁.wb_right
      (by rw [K₁ _ by_omega, a50]) by_grind p66 by_omega
      (by rw [m₁e, show Sb + t + 1 = Sb + ztbx by omega, mS _ hn]; omega)
    rw [m₁e, show Sb + t + 1 = Sb + ztbx by omega, mS _ hn] at x65 x70
    rw [mV _ hs1] at x70
    have K₂ := fun r hr => F₂.1 r ztmz
    have hm₂ := F₂.2.2.1.trans m₁e
    have b7 : c₂.nreg 60007 = Sb := by_grind
    have b61 : c₂.nreg 60061 = FPb := by_grind
    have b67 : c₂.nreg 60067 = m₁ ztwob := by_grind
    have b64 : c₂.nreg 60064 = ROTb + m₁ ztis := by_grind
    have hrot : rotN M ztwrz ztwsb t =
        if m₁ ztyic = m₁ ztwob then m₁ (Sb + ztbx) else
          m₁ (Sb + fpN M ztwrz ztwsb
            ztball) := by
      unfold rotN; simp only [hn, true_and]
    have hc1 : c₁.nreg 60069 < c₁.nreg 60060 := by_grind
    rcases lt_trichotomy (m₁ ztyic) ztball with h | h | h
    · zucdu
      refine ⟨c₃, _, .seq e₁ (.ifLtN_true hc1 (.seq e₂ (.ifLtN_true by_omega
        e₃))), by_omega, v64, by zunwh⟩
    · refine ⟨c₂, _, .seq e₁ (.ifLtN_true hc1 (.seq e₂ (.ifLtN_false by_omega
        (.ifLtN_false by_omega ztdyc)))), by_omega, b64,
        by grind⟩
    · zucdu
      refine ⟨c₃, _, .seq e₁ (.ifLtN_true hc1 (.seq e₂ (.ifLtN_false by_omega
        (.ifLtN_true by_omega e₃)))), by_omega, v64,
        by zunwh⟩
  · have hc1 : ¬ c₁.nreg 60069 < c₁.nreg 60060 := by_grind
    obtain ⟨c₃, k₃, e₃, hk₃, v64, v65⟩ := fb c₁ e₁.wb_right m₁e
      by_grind by_grind p67 p64
    refine ⟨c₃, _, .seq e₁ (.ifLtN_false hc1 e₃), by_omega, v64, ?_⟩
    rw [v65]; unfold rotN; grind

/-- **The rotation**: a scatter over the positions. -/
def rotS : Stmt := scatS 60063 60060 120011 60064 60065 rotBody
theorem rotS_exec (hw : WordsBounded W c)
    {Sb VT M FPb ROTb N : ℕ} (hJ : RotJ Sb VT M FPb ROTb c.nmem c)
    (hSR : Sb + M ≤ ROTb) (hVR : VT + M ≤ ROTb)
    (hFR : FPb + N ≤ ROTb) (hRW : ROTb + M ≤ W)
    (hs : ∀ t, t < M → c.nmem ztis < M) (hG : ∀ d, d < M → c.nmem ztbjm < N)
    (hfp : ∀ t, t < M → c.nmem (FPb + c.nmem ztxne) =
      fpN M ztzeu ztzfv ztbasm)
    (hfpl : ∀ t, t < M → fpN M ztzeu ztzfv
      ztbasm < M) :
    ∃ c' k, Exec P W rotS c c' k ∧ k ≤ M * 28 + 3 ∧
      ztgng ∧
      ztrf ∧
      c'.nmem = scat c.nmem ztyqu
        ztxco M ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ RotJ Sb VT M FPb ROTb c.nmem c' := by
  obtain ⟨c', k, ex, hk, r', rr', mm, rm, o, J', -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60063) (rn := 60060) (r1 := 120011) (ra := 60064) (rv := 60065) (body := rotBody)
    (B := BR) by_decide by_decide by_decide by_decide by_decide
    (RotJ Sb VT M FPb ROTb c.nmem) ROTb
    (fun d d' hJ hr hm => ⟨by zumxs; exact hJ.1,
      by zumxs; exact hJ.2.1,
      by zumxs; exact hJ.2.2.1,
      by zumxs; exact hJ.2.2.2.1,
      by zumxs; exact hJ.2.2.2.2.1,
      by zumxs; exact hJ.2.2.2.2.2.1,
      fun a ha => by zunps; exact hJ.2.2.2.2.2.2 a ha⟩)
    (n := M) (κ := 24) ztyqu
    ztxco ztbeo
    (fun i d hi hJd hwd hri => by
      obtain ⟨d', k, ex, hk, F, v1, v2⟩ := rotBody_exec hwd hJd hri hi hSR hVR hFR hRW hs hG hfp hfpl
      exact ⟨d', k, ex, hk, F, v1, v2⟩)
    hw hJ hJ.2.2.1 hJ.2.2.2.2.2.1 by_omega
  exact ztfvz
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData
@[expose] public section
theorem planar_of_mem {B : BookData} (hV : B.Valid) {m : ℕ → ℕ} {Bh VT ROT : ℕ} {s : ℕ → ℕ}
    (hsd : SortedDarts ztbck ztxcn
      ztywa s)
    (hvt : ∀ d, d < 2 * B.E → m ztbjm = View.tail B.N ztbgk)
    (hop : ∀ d, d < 2 * B.E → m ztnqf = oppN d)
    (hrot : ∀ t, t < 2 * B.E → m (ROT + s t) = rotN ztbck ztxcn s t)
    (h0 : m Bh = VT + 4 * B.E) (h1 : m ztsvl = ROT) (h2 : m (Bh + 2) = VT) :
    PlanarMapAt m Bh B.N B.E ∧ memGraph m Bh B.N B.E = OracleQ.bookGraph B := by
  have hopp : ∀ d, d < 2 * B.E → m ztlrd = oppN d := by_simp_all
  have hvt' : ∀ d, d < 2 * B.E → m ztgky = View.tail B.N ztbgk := by_simp_all
  refine ⟨planarMapAt_of_arrays hV hopp ztbzy hvt', memGraph_eq hopp hvt'⟩
  obtain ⟨t, ht, rfl⟩ := hsd.surj d hd
  rw [h1, hrot t ht, ← rot_eq_csucc hV hsd ht]

/-! ## The set-up blocks -/

/-- The dart arrays at the allocator: `VT` (`60050`), `VT + 2 E` (`60051`), `VT + 4 E`
(`60052`); the allocator grows by `6 E`. -/
def vtS : Stmt :=
  block [.copyN 60050 9999, .addN 60051 60050 60037, .addN 60051 60051 60037,
    .addN 60052 60051 60037, .addN 60052 60052 60037, .addN 9999 60052 60037,
    .addN 9999 9999 60037]
variable {P : Polygon} {W : ℕ} {c : Config} {r : ℕ}
theorem vtS_exec (hw : WordsBounded W c) {E A₀ : ℕ}
    (hE : c.nreg 60037 = E) (hA : c.nreg 9999 = A₀) (hW : A₀ + 6 * E ≤ W) :
    ∃ c' k, Exec P W vtS c c' k ∧ k = 7 ∧
      FrameB ztfcb c c' ∧
      c'.rreg = c.rreg ∧ c'.nreg 60050 = A₀ ∧ c'.nreg 60051 = A₀ + 2 * E ∧ c'.nreg 60052 = A₀ + 4 * E ∧
      c'.nreg 9999 = A₀ + 6 * E := by
  have hwr : wr ztfcb vtS = true := by
    decide
  suffices H : ∃ c' k, Exec P W vtS c c' k ∧ k = 7 ∧ c'.rreg = c.rreg ∧
      c'.nreg 60050 = A₀ ∧ c'.nreg 60051 = A₀ + 2 * E ∧ c'.nreg 60052 = A₀ + 4 * E ∧
      c'.nreg 9999 = A₀ + 6 * E by
    obtain ⟨c', k, ex, hk, rr, a, b, d, e⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, rr, a, b, d, e⟩
  unfold vtS
  exec_block
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  · exact ⟨rfl, rfl, by_simp_all, by config_simp; omega,
      by config_simp; omega, by config_simp; omega⟩

/-- The inputs of the sort of the darts. -/
def sortPrep : Stmt :=
  block [.copyN 60004 60050, .copyN 60005 60051, .addN 60006 60037 60037, .copyN 60060 60006]
theorem sortPrep_exec (hw : WordsBounded W c) {E VT : ℕ}
    (hE : c.nreg 60037 = E) (h50 : c.nreg 60050 = VT) (h51 : c.nreg 60051 = VT + 2 * E)
    (hW : 2 * E ≤ W) :
    ∃ c' k, Exec P W sortPrep c c' k ∧ k = 4 ∧
      FrameB ztxwz c c' ∧
      c'.nreg 60004 = VT ∧ c'.nreg 60005 = VT + 2 * E ∧ c'.nreg 60006 = 2 * E ∧
      c'.nreg 60060 = 2 * E := by
  have hwr : wr ztxwz sortPrep = true := by
    decide
  suffices H : ∃ c' k, Exec P W sortPrep c c' k ∧ k = 4 ∧
      c'.nreg 60004 = VT ∧ c'.nreg 60005 = VT + 2 * E ∧ c'.nreg 60006 = 2 * E ∧
      c'.nreg 60060 = 2 * E by
    zuchq

  unfold sortPrep
  exec_block
  · config_simp; omega
  · exact ⟨rfl, by_simp_all, by_simp_all,
      by config_simp; omega, by config_simp; omega⟩

/-- Allocate `n` (register `rn`) words, base into `rb`. -/
def allocS (rb rn : ℕ) : Stmt := block [.copyN rb 9999, .addN 9999 9999 rn]
theorem allocS_exec (hw : WordsBounded W c) {rb rn A n : ℕ}
    (hrb : rb ≠ 9999) (hA : c.nreg 9999 = A) (hn : c.nreg rn = n) (hrn : rn ≠ rb) (hW : A + n ≤ W) :
    ∃ c' k, Exec P W zttfd c c' k ∧ k = 2 ∧
      FrameB ztikh c c' ∧ c'.rreg = c.rreg ∧ c'.nreg rb = A ∧
      c'.nreg 9999 = A + n := by
  have hwr : wr ztikh zttfd = true := by
    simp [allocS, block, wr, wrOK]
  suffices H : ∃ c' k, Exec P W _ c c' k ∧ k = 2 ∧ c'.rreg = c.rreg ∧
      c'.nreg rb = A ∧ c'.nreg 9999 = A + n by
    obtain ⟨c', k, ex, hk, rr, a, b⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, rr, a, b⟩
  unfold allocS
  exec_block
  · config_simp; zunep; omega
  · exact ⟨rfl, rfl, by_simp_all,
      by config_simp; zunep⟩

/-- The three handle words (`OPP`, `ROT`, `VT`) at the allocator; the handle into `60071`. -/
def hdS : Stmt :=
  block [.copyN 60071 9999, .addN 9999 9999 120048, .addN 9999 9999 120011, .storeN 60071 60052,
    .addN 60072 60071 120011, .storeN 60072 60062, .addN 60072 60072 120011, .storeN 60072 60050]
theorem hdS_exec (hw : WordsBounded W c) {A OPP ROT VT : ℕ}
    (hA : c.nreg 9999 = A) (h1 : c.nreg 120011 = 1) (h2 : c.nreg 120048 = 2)
    (h52 : c.nreg 60052 = OPP) (h62 : c.nreg 60062 = ROT) (h50 : c.nreg 60050 = VT)
    (hW : A + 3 ≤ W) :
    ∃ c' k, Exec P W hdS c c' k ∧ k = 8 ∧
      (∀ r, r ≠ 60071 → r ≠ 60072 → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nmem = upd (upd (upd c.nmem A OPP) ztbo ROT) ztbcl VT ∧
      c'.nreg 60071 = A ∧ c'.nreg 9999 = A + 3 := by
  unfold hdS
  exec_block
  · config_simp; omega
  · simp_all
  · config_simp; omega
  · config_simp; omega
  simp_all

/-! ## The map stage -/

/-- **The planar map of the book.** -/
def mapS : Stmt :=
  .seq vtS (.seq (passesS 6) (.seq sortPrep (.seq sortCore (.seq (allocS 60061 60034)
    (.seq fpS (.seq (allocS 60062 60060) (.seq rotS hdS)))))))

/-- The registers kept by `mapS`. -/
def MPres (r : ℕ) : Prop :=
  (60000 ≤ r ∧ r < 70000 ∧ (r < 60004 ∨ ztnhr ∨ r = 60034 ∨ r = 60037 ∨
    60080 ≤ r)) ∨ (bandOf r ≠ 3 ∧ bandOf r ≠ 6 ∧ bandOf r ≠ 11 ∧ r ≠ 9999)
theorem MPres_not (h : MPres r) : ¬ ((60004 ≤ r ∧ r ≤ 60007) ∨ (60016 ≤ r ∧ r ≤ 60033) ∨
    (60035 ≤ r ∧ r ≤ 60036) ∨ (60038 ≤ r ∧ r ≤ 60079) ∨ r = 9999) := by
  unfold MPres bandOf at h; omega
theorem b6_ne (hr : (decide ztlgf || decide ztyc) = false) :
    r ≠ 9999 ∧ (r < 60000 ∨ 70000 ≤ r) := by
  zvnam at hr; unfold bandOf at hr; omega
set_option maxHeartbeats 2000000 in
theorem mapS_exec (hw : WordsBounded W c) {B : BookData}
    (hV : B.Valid) {CH1 CH2 A₀ : ℕ} (hN : c.nreg 60034 = B.N) (hI : c.nreg 60008 = B.I.length)
    (h1r : c.nreg 60001 = CH1) (h2r : c.nreg 60002 = CH2) (hone : c.nreg 120011 = 1)
    (htwo : c.nreg 120048 = 2) (hE : c.nreg 60037 = B.E) (hAl : c.nreg 9999 = A₀)
    (hP : PairsAt c.nmem CH1 CH2 ztclc) (hC1 : CH1 + (B.I ++ B.O).length ≤ A₀)
    (hC2 : CH2 + (B.I ++ B.O).length ≤ A₀)
    (hroom : A₀ + 10 * B.E + SortR.sortCost 20 ztbck + B.N + 3 ≤ W) (hNW : 2 * B.N + 2 ≤ W) :
    ∃ c' k, Exec P W mapS c c' k ∧ k ≤ 400 * B.E + SortR.sortCost 20 ztbck + 100 ∧
      FrameN dBands c c' ∧ A₀ ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + 10 * B.E + SortR.sortCost 20 ztbck + B.N + 3 ∧
      c'.nreg 60071 + 3 = c'.nreg ALLOC ∧
      (∀ r, MPres r → c'.nreg r = c.nreg r) ∧
      Robust ztdo c'.nmem (fun m => PlanarMapAt m ztvgo B.N B.E ∧
        memGraph m ztvgo B.N B.E = OracleQ.bookGraph B) := by
  zuhp
  set E := B.E with hEdef
  set N := B.N with hNdef
  have hLE : E = N + (B.I ++ B.O).length := by
    rw [hEdef, hNdef]; unfold BookData.E; grind
  -- 1. the dart arrays
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, rr₁, v50, v51, v52, v99⟩ :=
    vtS_exec (P := P) hw hE hAl by_omega
  have K₁ : ∀ r, MPres r → c₁.nreg r = c.nreg r := fun r hr => F₁.1 r (by
    have := MPres_not hr; grind)
  have mp : ∀ r, (r = 60001 ∨ r = 60002 ∨ r = 60008 ∨ r = 60034 ∨ r = 60037) → MPres r :=
    fun r hr => Or.inl by_omega
  have mq : ∀ r, (r = 120011 ∨ r = 120048) → MPres r :=
    fun r hr => Or.inr ztdmk
  have DE : DartEnv N B.I.length CH1 CH2 A₀ E A₀ _ c₁ :=
    { rN := by_simp_all
      rI := by_simp_all
      r1 := by_simp_all
      r2 := by_simp_all
      one := by_simp_all
      two := by_simp_all
      rV := v50
      rK := v51
      rO := v52
      rE := by_simp_all
      pairs := by rw [F₁.2.2.1]; exact hP
      hE := hLE
      hC1 := hC1
      hC2 := hC2
      hlo := le_rfl
      ends := fun t ht => by
        have hm := getD_mem ht
        rcases List.mem_append.1 hm with h | h
        · have := hV.2.2.2.1 _ h; unfold ChordOK at this; omega
        · have := hV.2.2.2.2.1 _ h; unfold ChordOK at this; omega
      hI := by_simp }
  -- 2. the passes
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, D₂, m₂, rm₂, o₂, J₂⟩ :=
    passesS_exec (P := P) e₁.wb_right (j := 6) le_rfl DE hNW by_omega
  have arrs := fun d (hd : d < 2 * E) => darts_of B hV D₂ hd
  have K₂ : ∀ r, MPres r → c₂.nreg r = c₁.nreg r := fun r hr => r₂ r
    (by have := MPres_not hr; unfold BEd; grind)
    (by have := MPres_not hr; unfold BDV; grind)
    (by have := MPres_not hr; omega)
  -- 3. the inputs of the sort
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, w4, w5, w6, w60⟩ :=
    sortPrep_exec (P := P) e₂.wb_right J₂.rE J₂.rV J₂.rK by_omega
  have K₃ : ∀ r, MPres r → c₃.nreg r = c₂.nreg r := fun r hr => F₃.1 r (by
    have := MPres_not hr; grind)
  have a99₃ : c₃.nreg 9999 = A₀ + 6 * E := by
    rw [F₃.1 _ by_decide, r₂ _ by_decide by_decide by_decide, v99]
  have one₃ : zthos := by
    grind
  have hm₃ := F₃.2.2.1
  -- 4. the sort
  obtain ⟨c₄, k₄, e₄, hk₄, F₄, al₄a, al₄b, R₄, sb₁, sb₂, hsort, hsurj, hlt⟩ :=
    sortCore_exec (P := P) e₃.wb_right (Z1 := A₀) (Z2 := A₀ + 2 * E) (n := 2 * E)
      (A₀ := A₀ + 6 * E) w4 w5 w6 one₃ a99₃ by_omega by_omega by_omega
  zvnek at al₄a al₄b
  have K₄ : ∀ r, MPres r → c₄.nreg r = c₃.nreg r := fun r hr => by
    zubuj
    · exact R₄ r ztdmk by_omega by_omega by_omega by_omega
    · exact F₄.1 r (by simp [dBands, bSort, bDecomp, bOPrep]; omega) by_omega
  have mem₄ : ∀ a, a < A₀ + 6 * E → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [F₄.2.2.1 a by_grind, hm₃]
  have k50 : c₄.nreg 60050 = A₀ := by
    rw [R₄ _ by_rfl by_omega by_omega by_omega by_omega,
      F₃.1 _ by_decide, r₂ _ by_decide by_decide by_decide, v50]
  have k52 : c₄.nreg 60052 = A₀ + 4 * E := by
    rw [R₄ _ by_rfl by_omega by_omega by_omega by_omega,
      F₃.1 _ by_decide, r₂ _ by_decide by_decide by_decide, v52]
  have k60 : c₄.nreg 60060 = 2 * E := by
    rw [R₄ _ by_rfl by_omega by_omega by_omega by_omega, w60]
  have k34 : c₄.nreg 60034 = N := by
    rw [K₄ _ by_grind, K₃ _ by_grind, K₂ _ by_grind,
      K₁ _ by_grind, hN]
  -- the sorted darts
  set Sb := c₄.nreg 60007 with hSb
  set F := c₄.nreg 9999 with hF
  -- 5. the first positions
  obtain ⟨c₅, k₅, e₅, hk₅, F₅, rr₅, f61, f99⟩ := allocS_exec (P := P) e₄.wb_right (rb := 60061)
    (rn := 60034) (A := F) (n := N) by_decide rfl k34 by_decide by_omega
  have hm₅ := F₅.2.2.1
  have K₅ : ∀ r, MPres r → c₅.nreg r = c₄.nreg r := fun r hr => F₅.1 r (by
    have := MPres_not hr; grind)
  have hGt : ∀ d, d < 2 * E → c₄.nmem ztsuz = View.tail N ztbgk := fun d hd => by
    rw [mem₄ _ by_omega]; grind
  have hGl : ∀ d, d < 2 * E → View.tail N _ < N := fun d hd =>
    tail_lt hV (view_ok hd)
  have hJ5 : FPJ Sb A₀ _ F c₅.nmem c₅ :=
    ⟨by rw [F₅.1 _ by_decide], by rw [F₅.1 _ by_decide, k50],
      by rw [F₅.1 _ by_decide, k60], f61,
      by rw [K₅ _ by_grind, K₄ _ by_grind, one₃], by_omega⟩
  obtain ⟨c₆, k₆, e₆, hk₆, r₆, rr₆, mm₆, rm₆, o₆, J₆⟩ := fpS_exec (P := P) e₅.wb_right (N := N)
    hJ5 by_omega by_omega (fun t ht => by rw [hm₅]; exact hlt t ht)
    (fun d hd => by rw [hm₅, hGt d hd]; exact hGl d hd) by_omega
  have K₆ : ∀ r, MPres r → c₆.nreg r = c₅.nreg r := fun r hr => r₆ r
    (by have := MPres_not hr; unfold BR; grind)
    (by have := MPres_not hr; omega)
  -- 6. the rotation
  obtain ⟨c₇, k₇, e₇, hk₇, F₇, rr₇, g62, g99⟩ := allocS_exec (P := P) e₆.wb_right (rb := 60062)
    (rn := 60060) (A := F + N) (n := 2 * E) by_decide
    (by rw [r₆ _ by_decide by_decide, f99]) J₆.2.2.1 by_decide by_omega
  have hm₇ := F₇.2.2.1
  have K₇ : ∀ r, MPres r → c₇.nreg r = c₆.nreg r := fun r hr => F₇.1 r (by
    have := MPres_not hr; grind)
  have below7 : ∀ a, a < F → c₇.nmem a = c₄.nmem a := fun a ha => by
    rw [hm₇, mm₆, scat_below by_grind ha, hm₅]
  have mS7 : ∀ t, t < 2 * E → c₇.nmem _ = c₄.nmem ztis := fun t ht =>
    below7 _ by_omega
  have mV7 : ∀ d, d < 2 * E → c₇.nmem ztsuz = View.tail N _ := fun d hd => by
    rw [below7 _ by_omega]; exact hGt d hd
  have hcong : ∀ t, t < 2 * E → c₇.nmem (A₀ + c₇.nmem _) =
      View.tail N _ := fun t ht => by
    rw [mS7 t ht, mV7 _ ztoau]
  have hfpv : ∀ t, t < 2 * E → c₇.nmem (F + View.tail N ztzbl) =
      fpN ztdsj (fun d => View.tail N ztbgk) (fun t => c₄.nmem ztis)
        (View.tail N ztzbl) := fun t ht => by
    rw [hm₇, mm₆]
    refine fp_scat (G := fun d => View.tail N ztbgk) (s := fun t => c₄.nmem ztis)
      ztdp _ ht
    show F + c₅.nmem _ = _
    rw [hm₅, hGt _ (hlt _ by_omega)]
  have hJ7 : RotJ Sb A₀ ztdsj F _ c₇.nmem c₇ :=
    ⟨by zuncy; exact J₆.1, by zuncy; exact J₆.2.1,
      by zuncy; exact J₆.2.2.1, by zuncy; exact J₆.2.2.2.1,
      g62, by zuncy; exact J₆.2.2.2.2.1, by_omega⟩
  obtain ⟨c₈, k₈, e₈, hk₈, r₈, rr₈, mm₈, rm₈, o₈, J₈⟩ := rotS_exec (P := P) e₇.wb_right
    (N := N) hJ7 by_omega by_omega le_rfl by_omega
    (fun t ht => by zuomk; exact hlt t ht)
    (fun d hd => by rw [mV7 d hd]; exact hGl d hd)
    (fun t ht => by
      rw [hcong t ht, hfpv t ht, fpN_congr (s := fun t => c₇.nmem _)
        (G' := fun d => View.tail N _) by_omega])
    (fun t ht => by
      rw [hcong t ht, fpN_congr (s := fun t => c₇.nmem _)
        (G' := fun d => View.tail N _) by_omega]
      exact (fpN_spec' ht).1)
  have K₈ : ∀ r, MPres r → c₈.nreg r = c₇.nreg r := fun r hr => r₈ r
    (by have := MPres_not hr; unfold BR; grind)
    (by have := MPres_not hr; omega)
  -- 7. the handle
  obtain ⟨c₉, k₉, e₉, hk₉, K₉', rr₉, rm₉, o₉, mm₉, b71, b99⟩ := hdS_exec (P := P) e₈.wb_right
    (A := F + N + 2 * E) (OPP := A₀ + 4 * E) (ROT := F + N) (VT := A₀)
    (by rw [r₈ _ by_decide by_decide, g99])
    J₈.2.2.2.2.2.1
    (by rw [K₈ _ ztdvl, K₇ _ ztdvl, K₆ _ ztdvl,
      K₅ _ ztdvl, K₄ _ ztdvl, K₃ _ ztdvl,
      K₂ _ ztdvl, K₁ _ ztdvl, htwo])
    (by rw [r₈ _ by_decide by_decide, F₇.1 _ by_decide, r₆ _ by_decide by_decide,
      F₅.1 _ by_decide, k52])
    J₈.2.2.2.2.1 J₈.2.1 by_omega
  have K₉ : ∀ r, MPres r → c₉.nreg r = c₈.nreg r := fun r hr =>
    K₉' r (by have := MPres_not hr; omega) (by have := MPres_not hr; omega)
      (by have := MPres_not hr; omega)
  have ex : Exec P W mapS c c₉ _ :=
    .seq e₁ ztqr
  refine ⟨c₉, _, ex, by_omega, ?_, by zunpv; omega, by zunpv; omega,
    by rw [hAL, b99, b71], fun r hr => by
      rw [K₉ r hr, K₈ r hr, K₇ r hr, K₆ r hr, K₅ r hr, K₄ r hr, K₃ r hr, K₂ r hr, K₁ r hr], ?_⟩
  · have hB6 : ∀ r, (decide ztlgf || decide ztyc) = true →
        bandOf r ∈ dBands ∨ r = ALLOC := fun r hr => by
      zufw
      zubuj
      · zugoq
      omega
    have FA : FrameN dBands c c₃ := PF.frameN
      ⟨fun r hr => by
        have := b6_ne hr
        rw [F₃.1 r ztmz,
          r₂ r ztjqs
            ztjqr by_omega,
          F₁.1 r ztmz],
      fun r hr => by
        have := b6_ne hr
        rw [F₃.2.1 r ztmz,
          rr₂ r ztjqs
            ztjqr, rr₁],
      fun a ha => by
        rw [hAL, hAl] at ha
        rw [hm₃, m₂ a ztbbu, F₁.2.2.1],
      fun a ha => by rw [F₃.2.2.2.1, rm₂, F₁.2.2.2.1],
      by rw [F₃.2.2.2.2, o₂, F₁.2.2.2.2]⟩ hB6
      (by rw [hAL, F₃.2.1 _ by_decide, rr₂ _ by_decide by_decide, rr₁])
    have FC : FrameN dBands c₄ c₉ :=
      PF.frameN
      ⟨fun r hr => by
        have := b6_ne hr
        rw [K₉' r by_omega by_omega by_omega,
          r₈ r ztcui by_omega,
          F₇.1 r ztmz,
          r₆ r ztcui by_omega,
          F₅.1 r ztmz],
      fun r hr => by
        have := b6_ne hr
        rw [rr₉, rr₈ r ztcui, rr₇,
          rr₆ r ztcui, rr₅],
      fun a ha => by
        zuksd
        zumcv
        rw [mm₉, upd_other _ _ _ (show a ≠ F + N + 2 * E + 2 by omega),
          upd_other _ _ _ (show a ≠ F + N + 2 * E + 1 by omega),
          upd_other _ _ _ (show a ≠ F + N + 2 * E by omega), mm₈,
          scat_below ztbeo (show a < F + N by omega), hm₇, mm₆,
          scat_below ztbeo ha', hm₅],
      fun a ha => by rw [rm₉, rm₈, F₇.2.2.2.1, rm₆, F₅.2.2.2.1],
      by rw [o₉, o₈, F₇.2.2.2.2, o₆, F₅.2.2.2.2]⟩ hB6
      (by rw [hAL, rr₉, rr₈ _ by_decide, rr₇, rr₆ _ by_decide, rr₅])
    exact (FA.trans F₄ (by rw [hAL, hAl, a99₃]; omega)).trans FC
      (by rw [hAL, hAl]; show A₀ ≤ F; omega)
  · unfold Robust
    zubxa
    rw [b71]
    have hA9 : c₉.nreg ALLOC = F + N + 2 * E + 3 := by zunpv
    have below9' : ∀ a, a < F + N + 2 * E → m' a = c₈.nmem a := by
      zuge
      have e1 := hm' a ztepy
      rw [e1, mm₉]
      zudlr
      zugeu
    have below9 : ∀ a, a < F + N → m' a = c₇.nmem a := fun a ha => by
      rw [below9' a by_omega, mm₈, scat_below ztbeo ha]
    have hsort' : SortedSeq (fun d => (View.tail N _, View.key N _))
        ztqod _ :=
      SortedSeq.congr
        hsort (fun t ht => ⟨by
          show c₃.nmem _ = _; zuozy; exact (arrs _ ztoau).1, by
          show c₃.nmem _ = _; zuozy; exact (arrs _ ztoau).2.1⟩)
    have hsd : SortedDarts ztbck (fun d => View.tail B.N _)
        (fun d => View.key B.N _) ztqod :=
      sortedDarts_of hsort' hlt hsurj fun d d' hd hd' hg hk =>
        congrArg Fin.val (keyInj hV ztpw ⟨d', hd'⟩ hg hk)
    refine planar_of_mem hV (VT := A₀) (ROT := F + N) hsd ztbzy ztbzy
      ztjwn ?_ ?_ ?_
    · rw [below9 _ by_omega, mV7 d hd]
    · rw [below9 _ by_omega, below7 _ by_omega, mem₄ _ by_omega]; exact (arrs d hd).2.2
    · have hst := hlt t ht
      rw [below9' _ by_omega, mm₈]
      have hgt : F + N + c₄.nmem ztis = (fun t => F + N + c₇.nmem ztis) t := by
        simp only; zuomk
      rw [hgt, scat_at ht fun j hj htj e => by
        try simp only at e
        rw [mS7 j hj, mS7 t ht] at e
        have := inj_of_surj hlt hsurj hj ht by_omega
        omega]
      exact rotN_congr mS7 hcong ht
    · rw [hm' _ ztepy, mm₉, upd_other _ _ _ (show F + N + 2 * E ≠ F + N + 2 * E + 2 by omega),
        upd_other _ _ _ (show F + N + 2 * E ≠ F + N + 2 * E + 1 by omega)]
      simp [upd, hEdef]
    · rw [hm' _ ztepy, mm₉,
        upd_other _ _ _ (show F + N + 2 * E + 1 ≠ F + N + 2 * E + 2 by omega)]
      simp
    · rw [hm' _ ztepy, mm₉]
      simp
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData
@[expose] public section
def kBody : Stmt :=
  block [.addN 60092 60092 60091, .addN 60092 60092 60091, .addN 60092 60092 60091,
    .addN 60092 60092 60090, .addN 60092 60092 60090, .addN 60092 60092 60090,
    .addN 60092 60092 120011, .addN 60091 60091 60090, .addN 60091 60091 60090,
    .addN 60091 60091 120011, .addN 60090 60090 120011]

/-- **The least `k ≥ 1` with `μ ≤ k³`.** -/
def kS : Stmt :=
  .seq zthsn (.whileLtN 60092 60034 kBody)

/-- The registers written by `kS`. -/
def BK3 (r : ℕ) : Bool := decide (60090 ≤ r ∧ r ≤ 60092)
variable {P : Polygon} {W : ℕ} {c : Config}
theorem kBody_exec (hw : WordsBounded W c) {j μ : ℕ}
    (h0 : c.nreg 60090 = j) (h1 : c.nreg 60091 = j ^ 2) (h2 : c.nreg 60092 = j ^ 3)
    (hone : c.nreg 120011 = 1) (hj : 1 ≤ j) (hlt : j ^ 3 < μ) (hW : 8 * μ ≤ W) :
    ∃ c' k, Exec P W kBody c c' k ∧ k = 11 ∧ FrameB BK3 c c' ∧ c'.nreg 60090 = j + 1 ∧
      c'.nreg 60091 = ztl ^ 2 ∧ c'.nreg 60092 = ztl ^ 3 := by
  have hwr : wr BK3 kBody = true := by_decide
  suffices H : ∃ c' k, Exec P W kBody c c' k ∧ k = 11 ∧ c'.nreg 60090 = j + 1 ∧
      c'.nreg 60091 = ztl ^ 2 ∧ c'.nreg 60092 = ztl ^ 3 by
    zucsn

  have e3 : ztl ^ 3 = j ^ 3 + 3 * j ^ 2 + 3 * j + 1 := by_ring
  have hb : ztl ^ 3 ≤ 8 * j ^ 3 := by nlinarith [sq_nonneg j, pow_pos (by omega : 0 < j) 2]
  have hsq : 0 ≤ j ^ 2 := Nat.zero_le _
  unfold kBody
  exec_block
  all_goals (try config_simp)
  all_goals (try rw [h0, h1, h2, hone])
  all_goals (try nlinarith)
  grind
theorem kS_exec (hw : WordsBounded W c) {μ : ℕ}
    (hμ : c.nreg 60034 = μ) (hone : c.nreg 120011 = 1) (hW : 8 * μ + 8 ≤ W) :
    ∃ c' k, Exec P W kS c c' k ∧ k ≤ 16 * μ + 5 ∧ FrameB BK3 c c' ∧
      1 ≤ c'.nreg 60090 ∧ μ ≤ c'.nreg 60090 ^ 3 ∧
      (c'.nreg 60090 = 1 ∨ ztrlg ^ 3 < μ) := by
  have hwr : wr BK3 kS = true := by_decide
  obtain ⟨c₁, k₁, e₁, hk₁, a0, a1, a2, R₁⟩ : ∃ c₁ k₁, Exec P W
      zthsn c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 60090 = 1 ∧ c₁.nreg 60091 = 1 ∧ c₁.nreg 60092 = 1 ∧
      (∀ r, BK3 r = false → c₁.nreg r = c.nreg r) := by
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, fun r hr => ?_⟩
      unfold BK3 at hr; zvnan at hr
      config_simp; simp only [upd_apply]; grind
  let I : Config → Prop := fun d => WordsBounded W d ∧ d.nreg 60034 = μ ∧ d.nreg 120011 = 1 ∧
    ∃ j, 1 ≤ j ∧ d.nreg 60090 = j ∧ d.nreg 60091 = j ^ 2 ∧ d.nreg 60092 = j ^ 3 ∧
      (j = 1 ∨ zthv ^ 3 < μ)
  have hI₁ : ztkzz := ⟨e₁.wb_right, by rw [R₁ _ by_decide, hμ], by rw [R₁ _ by_decide, hone],
    1, le_rfl, a0, by_omega, by_omega, Or.inl rfl⟩
  obtain ⟨c₂, k₂, e₂, ⟨-, -, -, j, hj1, b0, -, b2, hjm⟩, hn, hk₂, -⟩ :=
    SortR.whileLtN_potential_lb (P := P) (W := W) (a := 60092) (b := 60034) (body := kBody) I
      (fun d => 16 * (μ - d.nreg 60090)) ztczh ztesk
      (fun d ⟨hwd, dμ, d1, j, hj1, d0, dsq, dcu, _⟩ ht => by
        rw [dcu, dμ] at ht
        obtain ⟨d', k, ex, hk, F, v0, v1, v2⟩ := kBody_exec (P := P) hwd d0 dsq dcu d1 hj1 ht by_omega
        have hjμ : j < μ := lt_of_le_of_lt (by nlinarith [pow_pos (by omega : 0 < j) 2]) ht
        refine ⟨d', k, ex, ⟨ex.wb_right, by rw [F.1 _ by_decide, dμ], by rw [F.1 _ by_decide, d1],
          j + 1, by_omega, v0, v1, v2, Or.inr by_simp_all⟩, ?_, Nat.zero_le _⟩
        omega) hI₁
  refine ⟨c₂, _, .seq e₁ e₂, ?_, exec_frameB ztyv hwr, by_omega, ?_, ?_⟩
  · omega
  · rw [b0]; rw [b2] at hn
    have : c₂.nreg 60034 = μ := by
      rw [(exec_frameB e₂ (B := BK3) by_decide).1 _ by_decide, R₁ _ by_decide, hμ]
    omega
  simp_all

/-! ## The call -/

/-- The inputs of the cluster decomposition. -/
def clSet : Stmt :=
  block [.copyN 130000 60071, .copyN 130001 60034, .copyN 130002 60037, .copyN 130003 60090]

/-- **The cluster stage.** -/
def clStage : Stmt := .seq kS (.seq clSet Cluster.clusterProg)

/-- The cost of the cluster decomposition for `μ` nodes and `E` edges. -/
def clCost (μ E : ℕ) : ℕ := Cluster.clusterK * (ztufg * (Nat.clog 2 ztufg + 1) + 1)
theorem card_fin_filter (n : ℕ) (p : ℕ → Prop) [DecidablePred p]
    [DecidablePred (fun v : Fin n => p v)] :
    (Finset.univ.filter (fun v : Fin n => p v)).card = ((Finset.range n).filter p).card := by
  zugfo
  zucr
  zumx
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · grind
  · rintro ⟨h, hp⟩; exact ⟨⟨x, h⟩, hp, rfl⟩
set_option maxHeartbeats 2000000 in
open Classical in
theorem clStage_exec (hw : WordsBounded W c) {B : BookData}
    {Bh A : ℕ} (hBh : c.nreg 60071 = Bh) (hμ : c.nreg 60034 = B.N) (hE : c.nreg 60037 = B.E)
    (hone : c.nreg 120011 = 1) (hA : c.nreg ALLOC = A)
    (hR : Robust A c.nmem (fun m => PlanarMapAt m Bh B.N B.E ∧
      memGraph m Bh B.N B.E = OracleQ.bookGraph B))
    (hPW : P.n + 3 ≤ W) (hW : 8 * B.N + 8 ≤ W) (hroom : A + clCost B.N B.E ≤ W) :
    ∃ c' k, Exec P W clStage c c' k ∧ k ≤ 16 * B.N + 9 + clCost B.N B.E ∧
      FrameN {bDecomp, bCluster} c c' ∧ A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + k ∧
      (∀ r, bandOf r = 6 → (r < 60090 ∨ 60092 < r) → c'.nreg r = c.nreg r) ∧
      1 ≤ c'.nreg 60090 ∧ B.N ≤ c'.nreg 60090 ^ 3 ∧
      (c'.nreg 60090 = 1 ∨ ztrlg ^ 3 < B.N) ∧
      A ≤ c'.nreg 130004 ∧ A ≤ c'.nreg 130005 ∧
      c'.nreg 130004 + B.N ≤ c'.nreg ALLOC ∧ c'.nreg 130005 + B.N ≤ c'.nreg ALLOC ∧
      ((Finset.range B.N).filter (fun v => c'.nmem ztrld = 1)).card ≤
        7 * c'.nreg 60090 ^ 2 ∧
      (∀ u v (w : (OracleQ.bookGraph B).Walk u v),
        (∀ x ∈ w.support, c'.nmem (c'.nreg 130004 + x) ≠ 1) →
          c'.nmem (c'.nreg 130005 + u) = c'.nmem ztrle) ∧
      (∀ l, ((Finset.range B.N).filter (fun v => c'.nmem ztrld ≠ 1 ∧
        c'.nmem ztrle = l)).card ≤ c'.nreg 60090 ^ 2) := by
  zuhp
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, kpos, kcube, kmin⟩ := kS_exec (P := P) hw hμ hone by_omega
  set kk := c₁.nreg 60090 with hkk
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, s0, s1, s2, s3⟩ : ∃ c₂ k₂, Exec P W clSet c₁ c₂ k₂ ∧ k₂ = 4 ∧
      FrameB ztzfo c₁ c₂ ∧ c₂.nreg 130000 = Bh ∧
      c₂.nreg 130001 = B.N ∧ c₂.nreg 130002 = B.E ∧ c₂.nreg 130003 = kk := by
    have hwr : wr ztzfo clSet = true := by_decide
    suffices H : ∃ c₂ k₂, Exec P W clSet c₁ c₂ k₂ ∧ k₂ = 4 ∧ c₂.nreg 130000 = Bh ∧
        c₂.nreg 130001 = B.N ∧ c₂.nreg 130002 = B.E ∧ c₂.nreg 130003 = kk by
      obtain ⟨c₂, k₂, ex, hk, a, b, d, e⟩ := H
      exact ⟨c₂, k₂, ex, hk, exec_frameB ex hwr, a, b, d, e⟩
    zud
    unfold clSet
    exec_block
    exact ⟨rfl, by config_simp; rw [F₁.1 _ by_decide, hBh],
      by config_simp; zunzr, by config_simp; rw [F₁.1 _ by_decide, hE],
      by rfl⟩
  have m₂ : ztckc := F₂.2.2.1.trans F₁.2.2.1
  have A₂ : ztlyb := by
    rw [hAL, F₂.1 _ by_decide, F₁.1 _ by_decide]; exact hA
  have r0 : rd c₂ bCluster 0 = Bh := s0
  have r1 : rd c₂ bCluster 1 = B.N := s1
  have r2 : rd c₂ bCluster 2 = B.E := s2
  have r3 : rd c₂ bCluster 3 = kk := s3
  have hcost : c₂.nreg ALLOC + Cluster.clusterK * (ztlst *
      (Nat.clog 2 ztlst + 1) + 1) ≤ W := by
    rw [A₂, r1, r2]; exact hroom
  obtain ⟨c₃, k₃, e₃, hk₃, post, F₃⟩ := clusterProg_meets P W c₂ e₂.wb_right
    ⟨hPW, by_omega, by_simp_all, fun m' hm' => by
      zuime
      exact (hR m' ztese).1⟩ hcost
  beta_reduce at hk₃
  rw [r1, r2] at hk₃
  obtain ⟨p4, p5, p4', p5', pcard, pwalk, pclus⟩ := post
  have hG : memGraph c₂.nmem Bh B.N B.E = OracleQ.bookGraph B :=
    (hR c₂.nmem (fun a _ => by zunbg)).2
  revert p4' p5' pcard pwalk pclus
  rw [r0, r1, r2, r3, hG]
  intro p4' p5' pcard pwalk pclus
  have K6 : ∀ r, bandOf r = 6 → c₃.nreg r = c₂.nreg r := fun r hr =>
    F₃.1 r (by simp [hr, bCluster]) (by zvnek; intro h; zvmwc at hr; simp [bandOf] at hr)
  have k3 : c₃.nreg 60090 = kk := by
    rw [K6 _ by_rfl, F₂.1 _ by_decide]
  have A₃a : A ≤ c₃.nreg ALLOC := by_omega
  have A₃b : c₃.nreg ALLOC ≤ A + k₃ := by have := F₃.2.2.2.2.2.2; omega
  refine ⟨c₃, _, .seq e₁ ztcr, by unfold clCost; omega, ?_, A₃a, by_omega, ?_,
    by omega, by_grind, by_grind,
    by zuoso; exact p4, by zuoso; exact p5, p4', p5', ?_, pwalk, ?_⟩
  · have FA : FrameN {bDecomp, bCluster} c c₂ :=
      PF.frameN (B := fun r => BK3 r || decide ztgxr)
        ⟨fun r hr => by
          zufar
          zunte,
        fun r hr => by
          zufar
          rw [F₂.2.1 r hr.2, F₁.2.1 r hr.1],
        fun a _ => by zunbg, fun a _ => by zuomf,
        by zuomg⟩
        (fun r hr => by
          simp only [BK3, Bool.or_eq_true, decide_eq_true_eq] at hr
          left
          zubuj
          · simp [bDecomp, bandOf]; omega
          · simp [bCluster, bandOf]; omega)
        (by rw [hAL, F₂.2.1 _ by_decide, F₁.2.1 _ by_decide])
    exact FA.trans (FrameN.mono (Frame.toN F₃) by_decide) by_omega
  · intro r hr hr'
    rw [K6 r hr, F₂.1 r ztdua,
      F₁.1 r (by unfold BK3; grind)]
  · zuozw; refine le_trans ztkad pcard
    refine Eq.trans ?_ (card_fin_filter B.N (fun v => c₃.nmem ztroe = 1)).symm
    zucr
  · intro l; zuozw; refine le_trans (le_of_eq ?_) (pclus l)
    refine Eq.trans ?_ (card_fin_filter B.N (fun v => c₃.nmem ztroe ≠ 1 ∧
      c₃.nmem (c₃.nreg 130005 + v) = l)).symm
    zucr
