module
public import CoxeterGrowth.Instances
public import CoxeterGrowth.Family

@[expose] public section
/-
Solution: proofs of the challenge statements, transferred from the CoxeterGrowth development
(`CoxeterGrowth.Triangle` for the general identity, `CoxeterGrowth.Instances` for the instances,
`CoxeterGrowth.Plastic` for the plastic number, `CoxeterGrowth.Family` for the family statements
(12)–(20)).
-/

namespace TriangleGrowth

/-- **(1) The growth series of the triangle Coxeter group `(p, q, ∞)`.** -/
alias growth_series := CoxeterGrowth.Triangle.growth_series

/-- **(2) Non-vacuity**: the Coxeter matrix of type `(p, q, ∞)` exists for all `p, q ≥ 2`. -/
alias triangle_matrix_exists := CoxeterGrowth.Triangle.triM_exists

/-- **(3) `(2,3,∞)`.** -/
alias growth_series_23 := CoxeterGrowth.Triangle.growth_series_23

/-- **(4) `(2,4,∞)`.** -/
alias growth_series_24 := CoxeterGrowth.Triangle.growth_series_24

/-- **(5) `(3,3,∞)`.** -/
alias growth_series_33 := CoxeterGrowth.Triangle.growth_series_33

/-- **(6) `(2,3,∞)` sphere sizes**: `1, 3, 5, 7, 9`, then `a(n+5) = a(n+3) + a(n+2)`. -/
alias sphere23_values := CoxeterGrowth.Triangle.sphere23_facts

/-- **(7)** The recursion of (6) fails one step earlier: `a(4) ≠ a(2) + a(1)`. -/
alias sphere23_rec_fails_at_4 := CoxeterGrowth.Triangle.sphere23_rec_fails_at_4

/-- **(8) Padovan**: `a(n) = Pad(n + 5)` for `n ≥ 2`. -/
alias sphere23_padovan := CoxeterGrowth.Triangle.sphere23_padovan

/-- **(9)** The plastic number exists and is unique. -/
alias plastic_exists_unique := CoxeterGrowth.plastic_exists_unique

/-- **(10) Two-sided growth bound** for `(2,3,∞)`: `2ρⁿ ≤ a(n) ≤ 4ρⁿ`, `n ≥ 2`. -/
alias sphere23_growth_bounds := CoxeterGrowth.Triangle.sphere23_growth

/-- **(11) Growth rate** of `(2,3,∞)`: `a(n)^{1/n} → ρ`, the plastic number. -/
alias sphere23_root_tendsto := CoxeterGrowth.Triangle.sphere23_root_tendsto

/-- **(12) Monotonicity** in `(p, q)`: `a_{p,q}(n) ≤ a_{p',q'}(n)` for `p ≤ p'`, `q ≤ q'`. -/
alias sphere_mono := CoxeterGrowth.Triangle.sphere_mono

/-- **(13) Symmetry**: `a_{p,q}(n) = a_{q,p}(n)`. -/
alias sphere_symm := CoxeterGrowth.Triangle.sphere_symm

/-- **(14) The plastic number bounds the whole family from below**: for every hyperbolic
`(p, q, ∞)`, `2ρⁿ ≤ a(n)` for `n ≥ 2`. -/
alias sphere_ge_plastic := CoxeterGrowth.Triangle.sphere_ge_plastic

/-- **(15) The rate equation** has exactly one root `τ > 1` for every hyperbolic `(p, q)`. -/
alias rate_exists_unique := CoxeterGrowth.Triangle.rate_exists_unique

/-- **(16) Growth rate of every member**: `a(n)^{1/n} → τ`, the root of the rate equation. -/
alias sphere_root_tendsto_rate := CoxeterGrowth.Triangle.sphere_root_tendsto_rate

/-- **(17) The rate is strictly increasing** in `(p, q)`. -/
alias rate_lt_rate := CoxeterGrowth.Triangle.rate_lt_rate

/-- **(18) The plastic number is the minimal rate**: `ρ ≤ τ`, with equality exactly for
`(p, q) = (2, 3)` and `(3, 2)`. -/
alias plastic_le_rate := CoxeterGrowth.Triangle.plastic_le_rate

/-- **(19)** Every rate is below `2`. -/
alias rate_lt_two := CoxeterGrowth.Triangle.rate_lt_two

/-- **(20)** The rates tend to `2` as `p, q → ∞`. -/
alias rate_tendsto_two := CoxeterGrowth.Triangle.rate_tendsto_two

end TriangleGrowth
