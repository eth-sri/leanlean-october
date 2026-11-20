module

public import Chazelle.Core.GranPz

/-!
# WP-F, init part 2: the bit `pz` on the RAM

`pzStmt` decides, for the walk position `⟨e, h⟩` (`r110 = e`, `r111 = h`), whether its edge is
counted and its parameter is nonzero, into `r112` (`pz_exec`).  It reuses the host and index
routines of double identification (`NFLoc`): `chHead`, `chIdx`, `cntStmt`, `hostPt` (chain
model, via `chPts`, the two walk vertices of a tour edge) and `intIdx` (interior model), and
compares height-vertex indices (distinct heights, `GranPz`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideE)

@[expose] public section

/-! ## Height-vertex indices and bit tests -/

/-- `dst := hv` of the symbolic point at `r` (`r50032 = 1`). -/
def hvS (dst r : ℕ) : Stmt :=
  .ifLtN r 50032 (.instr (.copyN dst (r + 1))) (.instr (.copyN dst (r + 2)))

theorem hvS_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {dst r : ℕ}
    {sp : SymPt} (h32 : c.nreg 50032 = 1) (hsp : SymPtIn c r sp) :
    ∃ c' k, Exec P W (hvS dst r) c c' k ∧ k ≤ 3 ∧ c'.nreg dst = hv sp ∧
      (∀ q, q ≠ dst → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem := by
  unfold hvS
  cases sp with
  | vtx i =>
    obtain ⟨h0, h1⟩ := hsp
    exact ⟨_, _, .ifLtN_true (by rw [h0, h32]; omega) (Exec.copyN hw _ _), by omega,
      by simp [upd, h1, hv], fun q hq => by simp [upd, hq], rfl⟩
  | onEdge e k =>
    obtain ⟨h0, -, h2⟩ := hsp
    exact ⟨_, _, .ifLtN_false (by rw [h0, h32]; omega) (Exec.copyN hw _ _), by omega,
      by simp [upd, h2, hv], fun q hq => by simp [upd, hq], rfl⟩

/-- `s` if `r a ≠ r b`, else `t`. -/
def ifNe (a b : ℕ) (s t : Stmt) : Stmt := .ifLtN a b s (.ifLtN b a s t)

theorem ifNe_ne {P : Polygon} {W : ℕ} {a b : ℕ} {s t : Stmt} {c c' : Config} {k : ℕ}
    (h : c.nreg a ≠ c.nreg b) (e : Exec P W s c c' k) :
    ∃ k', Exec P W (ifNe a b s t) c c' k' ∧ k' ≤ k + 3 := by
  by_cases hlt : c.nreg a < c.nreg b
  · exact ⟨_, .ifLtN_true hlt e, by omega⟩
  · exact ⟨_, .ifLtN_false hlt (.ifLtN_true (by omega) e), by omega⟩

theorem ifNe_eq {P : Polygon} {W : ℕ} {a b : ℕ} {s t : Stmt} {c c' : Config} {k : ℕ}
    (h : c.nreg a = c.nreg b) (e : Exec P W t c c' k) :
    Exec P W (ifNe a b s t) c c' (k + 2 + 2) :=
  .ifLtN_false (by omega) (.ifLtN_false (by omega) e)

/-- `r112 := 1` if `r111 ≠ 0`, `r ra ≠ r rb` and `r rc ≠ r rd` (else unchanged). -/
def tail3 (ra rb rc rd : ℕ) : Stmt :=
  .ifLtN 90111 90019 .skip (ifNe ra rb (ifNe rc rd (.instr (.constN 90112 1)) .skip) .skip)

theorem tail3_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W)
    (ra rb rc rd : ℕ) (h19 : c.nreg 90019 = 1) (h112 : c.nreg 90112 = 0) :
    ∃ c' k, Exec P W (tail3 ra rb rc rd) c c' k ∧ k ≤ 10 ∧
      c'.nreg 90112 ≤ 1 ∧
      (c'.nreg 90112 = 1 ↔ (c.nreg 90111 ≠ 0 ∧ c.nreg ra ≠ c.nreg rb ∧ c.nreg rc ≠ c.nreg rd)) ∧
      (∀ q, q ≠ 90112 → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem := by
  unfold tail3
  by_cases h0 : c.nreg 90111 = 0
  · exact ⟨c, _, .ifLtN_true (by rw [h19]; omega) (.skip hw), by omega, by omega,
      by simp [h0, h112], fun _ _ => rfl, rfl⟩
  have e0 : ¬ c.nreg 90111 < c.nreg 90019 := by rw [h19]; omega
  by_cases h1 : c.nreg ra = c.nreg rb
  · exact ⟨c, _, .ifLtN_false e0 (ifNe_eq h1 (.skip hw)), by omega, by omega,
      by simp [h1, h112], fun _ _ => rfl, rfl⟩
  by_cases h2 : c.nreg rc = c.nreg rd
  · obtain ⟨k', e', hk'⟩ := ifNe_ne (s := ifNe rc rd (.instr (.constN 90112 1)) .skip)
      (t := .skip) h1 (ifNe_eq (P := P) (W := W) (s := .instr (.constN 90112 1)) h2 (.skip hw))
    exact ⟨c, _, .ifLtN_false e0 e', by omega, by omega, by simp [h2, h112],
      fun _ _ => rfl, rfl⟩
  · obtain ⟨k₁, e₁, hk₁⟩ := ifNe_ne (s := .instr (.constN 90112 1)) (t := .skip) h2
      (Exec.constN (P := P) hw 90112 1 hW)
    obtain ⟨k', e', hk'⟩ := ifNe_ne (s := ifNe rc rd (.instr (.constN 90112 1)) .skip)
      (t := .skip) h1 e₁
    exact ⟨_, _, .ifLtN_false e0 e', by omega, by simp [upd], by simp [upd, h0, h1, h2],
      fun q hq => by simp [upd, hq], rfl⟩

/-! ## The procedure -/

/-- The chain model (after `chHead`). -/
def pzChain : Stmt :=
  .ifLtN 50002 50081 (.instr (.constN 90112 0))
    (.seq (block [.subN 50056 50002 50081, .subN 50057 50056 50053])
      (.ifLtN 50057 50053
        (.seq chPts (.seq (hvS 90113 50040) (.seq (hvS 90114 50043)
          (.seq (block [.constN 90112 0, .subN 90115 90111 90019])
            (tail3 90113 90114 90115 90113)))))
        (.instr (.constN 90112 0))))

/-- The interior model. -/
def pzInt : Stmt :=
  .seq intIdx (.seq (block [.constN 90112 0, .subN 90115 90111 90019])
    (tail3 90115 50041 90115 50041))

/-- **The bit `pz`** of the position `⟨r110, r111⟩` into `r112`. -/
def pzStmt : Stmt :=
  .seq (.instr (.copyN 50002 90110)) (.ifLtN 90023 90019 (.seq chHead pzChain) pzInt)

/-- The registers `pzStmt` writes. -/
def Bpz (r : ℕ) : Bool := Bdir r || decide (r = 50002) || decide (90110 ≤ r ∧ r < 90120)

theorem wr_pzStmt : wr Bpz pzStmt = true := by decide

/-- The registers `chPts` writes. -/
def Bpts (r : ℕ) : Bool := decide (50040 ≤ r ∧ r < 50049) || decide (50056 ≤ r ∧ r < 50100)

theorem wr_chPts_fine : wr Bpts chPts = true := by decide

end

end Gran

end Chazelle.Core
