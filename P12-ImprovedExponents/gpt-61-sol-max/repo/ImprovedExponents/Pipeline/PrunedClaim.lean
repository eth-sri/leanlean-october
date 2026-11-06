module

public import Mathlib.Tactic
public import ImprovedExponents.Pipeline.ExactTriangle
public import ImprovedExponents.Optimum.PerCBasic
public import ImprovedExponents.PrunedEncoding.Costs
public import ImprovedExponents.Cost8P.Offline
public import ImprovedExponents.PrunedProgram.Wrapper.Program

@[expose] public section

/-!
# The hypothesis on the pruned encoder, proved

`PrunedEncoderClaim` (`ImprovedExponents.Pipeline.General`) says that a thin-product solver with
pruned encodings meets the time bound of the mathematics of
`ImprovedExponents.PrunedEncoding`: for all rational ratios `c = a/b > 10` and `θ = p/q < 0.9`,
every `0 < γ < γX(c, θ)` and every `ε < R'_c(γ)`, the thin product is solved in the sense of
`ThinClaim lightModel ε γ q(θ)`.  The solver is `programP G r s`
(`ImprovedExponents.PrunedProgram.Wrapper.Program`): upstream's program with the regime test
`D^r ≤ N^s` and the pruned encoder.  Its running time is within the bounds by the cost analysis
`ImprovedExponents.Cost8P` (`offlineWithinP`), the tile fits in the regime by `exists_fitsRS`, and
the generic solver of `ImprovedExponents.Pipeline.ThinClaim` puts the two together
(`thinClaimRS_of_offlineWithinT`).  The exponent `r/s` is chosen strictly between
`A'(c)/ln 4` and `1/ε`, which is possible because `ε < R'_c(γ) < ln 4/A'(c)`; for `ε ≤ 0` the
claim follows from the one at a positive `ε` (`ThinClaim.mono`).

So `prunedEncoderClaim` discharges the one hypothesis of the paper, and the theorems of
`ImprovedExponents.Pipeline.General` that assumed it hold outright: `explicitFrom_pruned` and
`allSolved_pruned`, every saving below the optimum `R'_c(Γ(c)) Γ(c)/2` of the method with pruned
encodings at every ratio `c ≥ 21`.
-/

namespace ImprovedExponents

open ThreeSumApsp Light Light.Sec4 Real

/-- **The thin product with pruned encodings and the regime test `D^r ≤ N^s`**, at the ratios
`c = a/b` and `θ = p/q` with `A'(c) < (r/s) ln 4`: every exponent `γ < γX(c, θ)`, for
`ε < R'_c(γ)` and `ε ≤ s/r`. -/
-- adapted from ImprovedExponents/Pipeline/Claims.lean (thinClaimRS_gammaX)
theorem thinClaimP_gammaX {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a) (hp : 1 ≤ p)
    (hθ : 10 * p < 9 * q) {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hrs : basePruned (a / b) < (r : ℝ) / s * log 4) {γ ε}
    (hγ0 : 0 < γ) (hγ : γ < gammaX (a / b) (p / q))
    (hε : ε < RcP (a / b) γ) (hεrs : ε ≤ (s : ℝ) / r) :
    ThinClaim lightModel ε γ (qOf (p / q)) := by
  obtain ⟨m₁, h₁⟩ := offlineWithinP cShared30 hb hq hc hp hθ hγ0 hγ hε
  obtain ⟨m₂, h₂⟩ := exists_fitsRS hb hq hc hp hθ hr hs hrs
  have hm₀ : 1 ≤ max (max m₁ m₂) 1 := le_max_right _ _
  obtain ⟨hoff, hauxO, hall⟩ :=
    offline32PRoutine_programP ⟨a, b, p, q, max (max m₁ m₂) 1, hb, hq, hc, hθ⟩ r s
  exact thinClaimRS_of_offlineWithinT (O := offline32PRoutine _ r s) hr
    (h₂ _ hm₀ ((le_max_right _ _).trans (le_max_left _ _))) ⟨_, rfl⟩ hall hoff hauxO hεrs
    (h₁ _ hm₀ ((le_max_left _ _).trans (le_max_left _ _)))

end ImprovedExponents
