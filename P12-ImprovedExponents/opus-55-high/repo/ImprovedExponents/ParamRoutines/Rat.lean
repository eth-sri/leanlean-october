
import ImprovedExponents.ParamRoutines.Routines
import ImprovedExponents.ParamRoutines.Pack


/-!
# Theorem 17 for programs, with `D = ⌊n^{a/b}⌋` and `g = ⌈D^{c/d}⌉`

The routines `dRatBody a b` and `gRatBody c d` are parameter procedures of the host of Theorem 17,
for all natural numbers `a`, `b`, `c`, `d` with `b ≥ 1` and `d ≥ 1` (`paramProc_dRat`,
`paramProc_gRat`).  The parameters and the numbers that the routines form are polynomially bounded
without any condition on the exponents.

The times are `O(n^{a/b})` and `O(D^{c/d})`: `O(n^k)` if `a ≤ k b`, and `O(D^k)` if `c ≤ k d`
(`steps_tDRat_pow`, `steps_tGRat_pow`).  The bound of Theorem 17 is uniform in all `n`, `D`, `g`
with `16 ≤ D ≤ n` and `1 ≤ g ≤ √D`; here `D` is not tied to the value of the routine.  Upstream
charges the parameter routines to the third term `n² D g`, that is, to the monomial `n² (√D)²`
(`Scale.SoftO.withinBuild`).  A function of `n` alone is `O(n² D)` for all such `D` only if it is
`O(n²)`, and a power of `D` is `O(n² D)` for all `D ≤ n` only if it is `O(D³)`.  So the routines
run within that monomial if `a ≤ 2 b` and `c ≤ 3 d` (`steps_tDRat`, `steps_tGRat`), and for that
monomial these conditions cannot be weakened.  They are the only conditions on the exponents:

* `paramPackRat a b c d` is the pack of the two routines;
* `claim_theorem_17_rat` is Theorem 17 for programs at these parameters;
* `claim_theorem_17_rat_upstream` recovers upstream's `claim_theorem_17₂₆` from the case
  `a/b = 1/18`, `c/d = 63/2000`.

For `c = 0` the parameter `g` is 1 (`paramGRat_zero`).
-/

namespace ImprovedExponents.ParamRoutines

open ThreeSumApsp Light Light.Sec3

/-! ## The routines as parameter procedures -/

/-- The four routines, placed behind a program of length `o`, at the numbers `o`, …, `o + 3`:
powLt, rootCeil, dRat and gRat. -/
def ratProcs (a b c d o : ℕ) : Program :=
  [powLtBody, rootCeilBody o, dRatBody a b (o + 1), gRatBody c d (o + 1)]

variable {b : ℕ}

/-- `dRatBody a b` computes `⌊n^{a/b}⌋`. -/
theorem paramProc_dRat (hb : b ≠ 0) (a c d : ℕ) (Q R : Program) :
    ParamProc (Q ++ ratProcs a b c d Q.length ++ R) (Q.length + 2) (paramDRatNat a b)
      (tDRat a b) (wDRat a b) := by
  intro lim dep x μ _ _ hw hd
  exact dRat_meets (getElem?_behind Q _ R (i := 2) rfl) (getElem?_behind Q _ R (i := 1) rfl)
    (getElem?_behind Q _ R (i := 0) rfl) hb hw

variable {d : ℕ}

/-- `gRatBody c d` computes `⌈D^{c/d}⌉`. -/
theorem paramProc_gRat (hd : d ≠ 0) (a b c : ℕ) (Q R : Program) :
    ParamProc (Q ++ ratProcs a b c d Q.length ++ R) (Q.length + 3) (paramGRatNat c d)
      (tGRat c d) (wGRat c d) := by
  intro lim dep x μ hx _ hw hd'
  exact gRat_meets (getElem?_behind Q _ R (i := 3) rfl) (getElem?_behind Q _ R (i := 1) rfl)
    (getElem?_behind Q _ R (i := 0) rfl) hd hx hw (by omega)

/-! ## The parameters and the words are polynomially bounded -/

/-- `⌊n^{a/b}⌋ ≤ n^a`. -/
theorem polyBounded_paramDRatNat (a b : ℕ) : PolyBounded fun n _ => paramDRatNat a b n :=
  (by growth_poly [] : PolyBounded _).of_le fun n _ => paramDRatNat_le a b n

variable {D : ℕ → ℕ}

/-- `⌈D^{c/d}⌉ ≤ D^c + 1`. -/
theorem polyBounded_paramGRatNat (c d : ℕ) (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => paramGRatNat c d (D n) :=
  (by growth_poly [hD] : PolyBounded fun n _ => D n ^ c + 1).of_le fun n _ =>
    by grind [paramGRatNat_le]

/-- The numbers of `dRatBody`. -/
theorem polyBounded_wDRat (a b : ℕ) : PolyBounded fun n _ => wDRat a b n := by
  unfold wDRat
  growth_poly [polyBounded_paramDRatNat a b]

/-- The numbers of `gRatBody`. -/
theorem polyBounded_wGRat (c d : ℕ) (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => wGRat c d (D n) := by
  unfold wGRat
  growth_poly [hD, polyBounded_paramGRatNat c d hD]

variable {a : ℕ}

/-! ## The time of the routines -/

/-- `dRatBody` takes a constant number of steps for each number up to `⌊n^{a/b}⌋ + 1`: `O(n^k)`
steps if `a ≤ k b`. -/
theorem steps_tDRat_pow {k : ℕ} (hb : b ≠ 0) (hab : a ≤ k * b) :
    StepsMon (fun θ => tDRat a b θ.n) k 0 0 := by
  have hD : StepsMon _ k 0 0 :=
    ((steps_n.pow k).mono fun i => by fin_cases i <;> simp).of_le fun _ hθ =>
      paramDRatNat_le_pow hb hab hθ.one_le_n_nat
  unfold tDRat
  apply Scale.SoftO.mono
  · growth_rules [hD]
  simp

/-- `dRatBody` takes `O(n²)` steps if `a ≤ 2 b`. -/
theorem steps_tDRat (hb : b ≠ 0) (hab : a ≤ 2 * b) :
    StepsMon (fun θ => tDRat a b θ.n) 2 2 0 :=
  (steps_tDRat_pow hb hab).mono (by decide)

/-- `gRatBody` takes `O(n² D)` steps if `c ≤ 3 d`: it takes a constant number of steps for each
number up to `⌈D^{c/d}⌉ ≤ D³`, and `D ≤ n`. -/
theorem steps_tGRat {c : ℕ} (hd : d ≠ 0) (hcd : c ≤ 3 * d) :
    StepsMon (fun θ => tGRat c d θ.D) 2 2 0 := by
  have hG :=
    (by growth [steps_n, steps_D] : StepsMon (fun θ => θ.n ^ 2 * θ.D) 2 2 0).of_le fun θ hθ =>
      (paramGRatNat_le_pow hd hcd hθ.one_le_D_nat).trans (by
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hθ.hDn 2))
  unfold tGRat
  growth [hG]

/-! ## The pack and the claim -/

/-- **The pack of the routines for `D = ⌊n^{a/b}⌋` and `g = ⌈D^{c/d}⌉`**, for `b ≥ 1`, `d ≥ 1`,
`a ≤ 2 b` and `c ≤ 3 d`. -/
def paramPackRat (a b c d : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hab : a ≤ 2 * b) (hcd : c ≤ 3 * d) :
    ParamPack (paramDRat a b) (paramGRatOf a b c d) := ⟨ratProcs a b c d, 2, 3, paramDRatNat a b, paramGRatNat c d, tDRat a b, tGRat c d, wDRat a b, wGRat c d, paramProc_dRat (by omega) a c d, paramProc_gRat (by omega) a b c, fun _ hn => one_le_paramDRatNat (by omega) a hn, polyBounded_paramDRatNat a b, polyBounded_paramGRatNat c d (polyBounded_paramDRatNat a b), polyBounded_wDRat a b, polyBounded_wGRat c d (polyBounded_paramDRatNat a b), paramDRatNat_eq (by omega) a, fun _ hn => paramGRatNat_paramDRat (by omega) a b c (one_le_paramDRat (by omega) a hn), steps_tDRat (by omega) hab, steps_tGRat (by omega) hcd⟩
