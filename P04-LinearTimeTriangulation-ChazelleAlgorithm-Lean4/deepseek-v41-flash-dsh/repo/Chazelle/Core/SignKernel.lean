module

public import Chazelle.Golf

public import Chazelle.Core.SignKernelRam

/-!
# The sign kernel (WP-A): `SignKernelSpec`

The kernel `SignK.signProg` (at most `230` steps, writing only band `bSign`):

1. `prelude`: constants;
2. `loadPt` three times: the homogeneous representation `symRep P sᵢ` of each symbolic point
   (`x = (x₀ + ε x₁) / (d₀ + ε d₁)` with eventually positive denominator, `y = y₀ + ε y₁`),
   read from the input `P` by `readX`/`readY`;
3. `polyStmt`: the coefficient lists `xPoly`, `yPoly`, `dPoly` (at most degree `4` in `ε`);
4. `selStmt`: the list of the requested test;
5. `lexStmt`: its lexicographic sign (lowest nonzero coefficient);
6. `finStmt`: the positivity bit for tests `0, 1, 2`, the zero bit for test `3`.

Correctness (`SignK.signTest_iff_lex`): by stability (`StableAt`, from `GoodShear` at
`epsOf P`) the truth value of a test in `Qof P` equals its value for all smaller `ε > 0`, which
for small `ε` is the lexicographic sign of the coefficient list.
-/

namespace Chazelle.Core

namespace SignK

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## Write sets of the stages -/

/-- Registers written by `prelude`. -/
def Bpre (r : ℕ) : Bool := decide (10020 ≤ r ∧ r < 10024)
/-- Registers written by `loadPt _ ob`. -/
def Bload (ob r : ℕ) : Bool := decide (10040 ≤ r ∧ r < 10051) || decide (ob ≤ r ∧ r < ob + 6)
/-- Registers written by `polyStmt`. -/
def Bpoly (r : ℕ) : Bool := decide (10200 ≤ r ∧ r < 10302)
/-- Registers written by `selStmt`. -/
def Bsel (r : ℕ) : Bool := decide (10400 ≤ r ∧ r < 10405)
/-- Registers written by `lexStmt`. -/
def Blex (r : ℕ) : Bool := decide (10410 ≤ r ∧ r < 10412)

/-- **The sign kernel.** -/
def signProg : Stmt :=
  .seq prelude (.seq (loadPt 10000 10100) (.seq (loadPt 10003 10110) (.seq (loadPt 10006 10120)
    (.seq polyStmt (.seq selStmt
      (.seq (lexStmt 10020 10410 10411 [10400, 10401, 10402, 10403, 10404]) finStmt))))))

/-- A symbolic point is determined by its registers. -/
theorem symPtIn_unique {c : Config} {r : ℕ} {s s' : SymPt} (h : SymPtIn c r s)
    (h' : SymPtIn c r s') : s = s' := by
  cases s with
  | vtx i =>
    cases s' with
    | vtx i' => simp only [SymPtIn] at h h'; rw [← h.2, ← h'.2]
    | onEdge e' h'' => simp only [SymPtIn] at h h'; omega
  | onEdge e hh =>
    cases s' with
    | vtx i' => simp only [SymPtIn] at h h'; omega
    | onEdge e' h'' => simp only [SymPtIn] at h h'; rw [← h.2.1, ← h'.2.1, ← h.2.2, ← h'.2.2]

/-- A symbolic point in registers survives when its three registers do. -/
theorem symPtIn_of_eq {c c' : Config} {r : ℕ} {s : SymPt} (h : SymPtIn c r s)
    (he : ∀ j, r ≤ j → j < r + 3 → c'.nreg j = c.nreg j) : SymPtIn c' r s := by
  cases s with
  | vtx i =>
    exact ⟨(he r le_rfl (⋄)).trans h.1, (he (r + 1) (⋄) (⋄)).trans h.2⟩
  | onEdge e hh =>
    exact ⟨(he r le_rfl (⋄)).trans h.1, (he (r + 1) (⋄) (⋄)).trans h.2.1,
      (he (r + 2) (⋄) (⋄)).trans h.2.2⟩

/-- A representation in registers survives when its six registers do. -/
theorem repAt_of_eq {c c' : Config} {ob : ℕ} {r : Rep} (h : RepAt c ob r)
    (he : ∀ j, ob ≤ j → j < ob + 6 → c'.rreg j = c.rreg j) : RepAt c' ob r :=
  ⟨(he ob le_rfl (⋄)).trans h.1, (he (ob + 1) (⋄) (⋄)).trans h.2.1,
    (he (ob + 2) (⋄) (⋄)).trans h.2.2.1,
    (he (ob + 3) (⋄) (⋄)).trans h.2.2.2.1,
    (he (ob + 4) (⋄) (⋄)).trans h.2.2.2.2.1,
    (he (ob + 5) (⋄) (⋄)).trans h.2.2.2.2.2⟩

end

end SignK

end Chazelle.Core
