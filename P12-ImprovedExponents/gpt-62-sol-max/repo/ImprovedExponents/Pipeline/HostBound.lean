module

public import ThreeSumApsp.TimeClaims.Sec3.Theorem19
public import ImprovedExponents.Pipeline.ThinClaim
public import ThreeSumApsp.Util.Asymptotics.UpperBounds

@[expose] public section

/-!
# From the thin product to Exact Triangle: the statements

The deduction of Section 3 of the paper, for arbitrary parameters. The three statements are about a
time model `M : DetTimeModel`, as upstream's `Claim.Corollary_16`, `Claim.Theorem_17` and
`Claim.Theorem_19_explicit`, whose parameters they generalize.

* `LopClaim M ε γ q`: Lop-AE-SparseTri(n, D) with `w` query pairs is solved, for `D ≤ n^ε`, in time
  `O(n² (log D + 1)²/D^γ + w D^q (log D + 1))`. (Corollary 16 has `γ = 0.063`, `q = 0.437` and
  `ε = 1/18`.)
* `HostBound M MM D g Dc`: the bound of Theorem 17 for the parameters `D(n)` and `g(n)`, with every
  call of the solver charged at the dimension `Dc(n)` of the middle part. For `Dc = D` this is
  `Claim.Theorem_17` (`hostBound_iff_theorem_17`).
* `ExplicitFrom M δ e`: Exact Triangle in time `K κ n^{3-δ} (log n)^e` for weights up to `n^κ`, from
  some size `n₀` on. (`Claim.Theorem_19_explicit` has `n₀ = 16^18`.)
-/

namespace ImprovedExponents

open ThreeSumApsp Light.Sec4

/-- Lop-AE-SparseTri (detection) is solved by one procedure whose time on the instances with
`D ≤ n^ε` is at most a constant times `n² (log D + 1)²/D^γ + w D^q (log D + 1)`. -/
def LopClaim (M : DetTimeModel) (ε γ q : ℝ) : Prop :=
  ∃ (C : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), M.lopDetect Td ∧
    ∀ n D w : ℕ, 1 ≤ n → 1 ≤ D → (D : ℝ) ≤ (n : ℝ) ^ ε →
      Td n D w ≤ C * (preBound31 γ n D + (w : ℝ) * queryBound31 q D)

/-- The time charged for the calls to the lopsided solver and the host's overhead. -/
noncomputable def hostCharge (MM : ℕ → ℝ) (n D g Dc : ℕ) (C κ : ℝ)
    (T : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  4 * (n : ℝ) * g * (T n Dc (queryCap n D) + C * ((n : ℝ) ^ 2 / Real.sqrt D)) +
    C * (termScans n g κ + termPrime MM n D + termBuild n D g)

/-- The bound of Theorem 17 for the parameters `D(n)` and `g(n)`, with each of the at most `4ng`
calls of the solver charged at the dimension `Dc(n)`. -/
def HostBound (M : DetTimeModel) (MM : ℕ → ℝ) (D g Dc : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopDetect T →
    ∃ T' : ℕ → ℝ → ℝ, M.exactTriangle T' ∧
      ∀ (n : ℕ) (κ u : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
        u ≤ (n : ℝ) ^ κ →
        T' n u ≤ hostCharge MM n (D n) (g n) (Dc n) C κ T

/-- The polynomial-time bound after a threshold, uniformly over polynomial weight bounds. -/
abbrev ExplicitBound (δ : ℝ) (e n₀ : ℕ) (K : ℝ) (T : ℕ → ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (κ u : ℝ), n₀ ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
    T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))

/-- Exact Triangle is solved by one algorithm that, from some size `n₀` on and for every `κ ≥ 1`,
takes time at most `K κ n^{3-δ} (log n)^e` on weights of absolute value at most `n^κ`. -/
def ExplicitFrom (M : DetTimeModel) (δ : ℝ) (e : ℕ) : Prop :=
  ∃ n₀ K T, M.exactTriangle T ∧ ExplicitBound δ e n₀ K T

/-- Specialize the bound to any family of weights growing at most polynomially. -/
theorem ExplicitBound.along {δ K c κ : ℝ} {e n₀ : ℕ} {T : ℕ → ℝ → ℝ} {B : ℕ → ℝ}
    (h : ExplicitBound δ e n₀ K T) (hκ : 0 ≤ κ)
    (hB : ∀ n, 1 ≤ n → B n ≤ c * (n : ℝ) ^ κ) :
    UpperPowPolylog (fun n => T n (B n)) (3 - δ) := by
  refine ⟨K * (κ + 1), e, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop n₀, Filter.eventually_ge_atTop ⌈c⌉₊,
    Filter.eventually_ge_atTop 1] with n hn₀ hnc hn1
  rw [mul_assoc]
  refine h n _ _ hn₀ (by linarith) ((hB n hn1).trans ?_)
  rw [Real.rpow_add_one (by positivity), mul_comm ((n : ℝ) ^ κ)]
  gcongr
  simp_all

end ImprovedExponents
