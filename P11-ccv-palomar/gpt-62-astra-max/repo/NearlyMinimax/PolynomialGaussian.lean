module

public import NearlyMinimax.Allocation
public import NearlyMinimax.GaussianSum


@[expose] public section

/-!
# Polynomial absorption and the abstract finite bias allocation

These are deterministic analytic lemmas for the `U12` bias allocation. The
polynomial factor is absorbed using a proved term of the exponential series.
The final finite-sum bound assumes the scalar allocation identities and their
budget reserve, rather than assuming any estimator or minimax risk bound.
-/

noncomputable section
open scoped BigOperators

namespace NearlyMinimax

section
variable (r : ℕ) {a : ℝ} (q : ℕ) {β S t u : ℝ} (ha : 0 < a) (hS : 0 < S)

/-- An explicit constant that absorbs any fixed polynomial into half the exponential. -/
def polynomialGaussianConstant (a : ℝ) : ℝ :=
  r.factorial / (a / 2) ^ r * Real.exp (a / 2)

include ha in
/-- The exponential-series argument behind the polynomial Gaussian absorption. -/
theorem polynomial_exp_absorption (ht : 0 ≤ t) :
    (1 + t) ^ r * Real.exp (-a * t) ≤
      polynomialGaussianConstant r a * Real.exp (-(a / 2) * t) := by
  have hh := Real.pow_div_factorial_le_exp (a / 2 * (1 + t))
    (by positivity) r
  have hp : (1 + t) ^ r ≤
      r.factorial / (a / 2) ^ r * Real.exp (a / 2 * (1 + t)) := by
    have hb := (div_le_iff₀ (by positivity)).1 hh
    rw [mul_pow] at hb
    calc
      _ ≤ (Real.exp (a / 2 * (1 + t)) * r.factorial) / (a / 2) ^ r := by
        apply (le_div_iff₀ (pow_pos (by positivity) r)).2
        simpa [mul_comm] using hb
      _ = _ := by ring
  apply (mul_le_mul_of_nonneg_right hp (Real.exp_pos (-a * t)).le).trans_eq
  unfold polynomialGaussianConstant
  have he : Real.exp (a / 2 * (1 + t)) * Real.exp (-a * t) =
      Real.exp (a / 2) * Real.exp (-(a / 2) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring
  grind

include ha hS in
/-- The exact polynomial absorption step at the paper's rescaled Gaussian variable. -/
theorem polynomial_gaussian_absorption :
    (1 + u ^ 2 / S) ^ r * Real.exp (-a * u ^ 2 / S) ≤
      polynomialGaussianConstant r a * Real.exp (-(a / 2) * u ^ 2 / S) := by
  grind [polynomial_exp_absorption r ha (div_nonneg (sq_nonneg u) hS.le)]

/-- Floor and coordinate subtraction give both needed bounds on approximation degree. -/
theorem profile_approximation_degree_bounds {Q : ℝ} {q : ℕ}
    (hβQ : 0 ≤ β * Q) (hq : q ≤ Nat.floor (β * Q)) :
    β * Q - q - 1 ≤ (Nat.floor (β * Q) - q : ℕ) ∧
      (Nat.floor (β * Q) - q : ℕ) + 1 ≤ β * Q + 1 := by
  have hf := Nat.floor_le hβQ
  have hl := Nat.lt_floor_add_one (β * Q)
  rw [Nat.cast_sub hq]
  grind

/-- The profile upper bound controls the entire fixed polynomial prefactor. -/
theorem profile_polynomial_prefactor_bound {z m : ℝ}
    (hβ : 0 ≤ β) (hS : 1 ≤ S) (hm : 0 ≤ m + 1)
    (hmQ : m + 1 ≤ β * quadraticProfile S z + 1) :
    let ratio := (z - S / 2) ^ 2
    (m + 1) ^ r ≤ (1 + 3 * β / 2) ^ r * S ^ r *
      (1 + ratio / S) ^ r := by
  intro ratio
  have hS₀  := lt_of_lt_of_le zero_lt_one hS
  have hQ := quadraticProfile_gaussian_upper (z := z) hS₀
  have ht : 0 ≤ ratio / S := by positivity
  have hupper : m + 1 ≤ (1 + 3 * β / 2) * S *
      (1 + ratio / S) := by
    rw [show 3 * ratio / (2 * S) =
      3 / 2 * (ratio / S) by ring] at hQ
    have htriple := mul_nonneg hβ (mul_nonneg (sub_nonneg.mpr hS) ht)
    nlinarith [mul_nonneg hS₀.le ht, mul_nonneg hβ hS₀.le]
  simpa only [mul_pow] using pow_le_pow_left₀ hm hupper r

include hS in
/-- The logarithmic reserve cancels `S^r` leaving the Gaussian normalizer. -/
theorem pow_mul_log_factor_eq_inv_sqrt :
    S ^ r * Real.exp (-(r + 1 / 2) * Real.log S) = 1 / Real.sqrt S := by
  rw [← Real.exp_log (pow_pos hS r), Real.log_pow, ← Real.exp_add]
  simp
  rw [← Real.exp_log (Real.sqrt_pos.2 hS), ← Real.exp_neg]
  congr 1
  rw [Real.log_sqrt hS.le]
  ring

/-- Explicit constant for the normalized term bound in `eq:U12-term`. -/
def allocationBiasTermConstant (β θ τ : ℝ) : ℝ :=
  (1 + 3 * β / 2) ^ r * Real.exp (τ * (q + 1)) * polynomialGaussianConstant r θ

theorem allocationBiasTermConstant_pos {θ τ : ℝ}
    (hβ : 0 ≤ β) (hθ : 0 < θ) : 0 < allocationBiasTermConstant r q β θ τ := mul_pos (mul_pos (by positivity) (Real.exp_pos _))
    (by unfold polynomialGaussianConstant; positivity)

end

section
variable {A : Finset ℕ} {r q : ℕ} {u₀ b β θ τ S z ell T m : ℝ}

/-- The profile identity and degree lower bound produce the Gaussian decay. -/
theorem allocation_bias_mass_bound
    (_hθ : 0 < θ) (hτ : 0 < τ) (hS : 0 < S) (hθβ : τ * β = θ)
    (hm : β * quadraticProfile S z - q - 1 ≤ m)
    (hreserve : (r + 1 / 2) * Real.log S ≤ θ * (S - ell - T)) :
    Real.exp (-θ * (z - ell - T) - τ * m) ≤
      Real.exp (τ * (q + 1)) *
        Real.exp (-(r + 1 / 2) * Real.log S) *
          Real.exp (-θ * (z - S / 2) ^ 2 / S) := by
  have hml := mul_le_mul_of_nonneg_left hm hτ.le
  have hrewrite : τ * (β * quadraticProfile S z - q - 1) =
      θ * quadraticProfile S z - τ * (q + 1) := by
    rw [← hθβ]
    ring
  have hid : θ * (z + quadraticProfile S z - S) = θ * (z - S / 2) ^ 2 / S := by
    rw [quadraticProfile_bias_identity hS.ne']
    ring
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  ring_nf at hml hreserve hid ⊢
  linarith

/-- The actual deterministic bias summand is bounded by a normalized Gaussian. -/
theorem allocation_bias_term_bound
    (hβ : 0 ≤ β) (hθ : 0 < θ) (hτ : 0 < τ) (hS : 1 ≤ S)
    (hθβ : τ * β = θ) (hmpos : 0 ≤ m + 1)
    (hml : β * quadraticProfile S z - q - 1 ≤ m)
    (hmu : m + 1 ≤ β * quadraticProfile S z + 1)
    (hreserve : (r + 1 / 2) * Real.log S ≤ θ * (S - ell - T)) :
    let ratio := (z - S / 2) ^ 2
    Real.exp (-θ * (z - ell - T) - τ * m) * (m + 1) ^ r ≤
      allocationBiasTermConstant r q β θ τ / Real.sqrt S *
        Real.exp (-(θ / 2) * ratio / S) := by
  intro ratio
  have hS₀  := lt_of_lt_of_le zero_lt_one hS
  have hm := allocation_bias_mass_bound hθ hτ hS₀ hθβ hml hreserve
  have hp := profile_polynomial_prefactor_bound r hβ hS hmpos hmu
  have ha := polynomial_gaussian_absorption r hθ (u := z - S / 2) hS₀
  let expScale := Real.exp (-(r + 1 / 2) * Real.log S)
  calc
    _ ≤ (Real.exp (τ * (q + 1)) *
        expScale *
          Real.exp (-θ * ratio / S)) *
            ((1 + 3 * β / 2) ^ r * S ^ r * (1 + ratio / S) ^ r) :=
      by bound
    _ = ((1 + 3 * β / 2) ^ r * Real.exp (τ * (q + 1))) *
        (S ^ r * expScale) *
          ((1 + ratio / S) ^ r * Real.exp (-θ * ratio / S)) := by ring
    _ ≤ ((1 + 3 * β / 2) ^ r * Real.exp (τ * (q + 1))) *
        (S ^ r * expScale) *
          (polynomialGaussianConstant r θ * Real.exp (-(θ / 2) * ratio / S)) :=
      by bound
    _ = _ := by
      rw [pow_mul_log_factor_eq_inv_sqrt r hS₀]
      unfold allocationBiasTermConstant
      ring

/-- The full finite scalar bias sum, under the quadratic profile and budget conditions. -/
theorem finite_allocation_bias_sum_bound {m : ℕ → ℕ}
    (hb : 0 < b) (hβ : 0 ≤ β) (hθ : 0 < θ) (hτ : 0 < τ) (hS : 1 ≤ S)
    (hθβ : τ * β = θ)
    (hreserve : (r + 1 / 2) * Real.log S ≤ θ * (S - ell - T))
    (hml : ∀ j ∈ A, β * quadraticProfile S (u₀ + j * b + S / 2) - q - 1 ≤ (m j))
    (hmu : ∀ j ∈ A, (m j) + 1 ≤ β * quadraticProfile S (u₀ + j * b + S / 2) + 1) :
    (∑ j ∈ A, Real.exp (-θ * (u₀ + j * b + S / 2 - ell - T) - τ * (m j)) *
      ((m j) + 1) ^ r) ≤
        allocationBiasTermConstant r q β θ τ * (2 + Real.sqrt (Real.pi / (θ / 2)) / b) := by
  have hterm j hj := allocation_bias_term_bound hβ hθ hτ hS hθβ
    (by positivity) (hml j hj) (hmu j hj) hreserve
  have hsum : (∑ j ∈ A, Real.exp (-θ * (u₀ + j * b + S / 2 - ell - T) - τ * (m j)) *
      ((m j) + 1) ^ r) ≤
        ∑ j ∈ A, allocationBiasTermConstant r q β θ τ / Real.sqrt S *
          Real.exp (-(θ / 2) * (u₀ + j * b) ^ 2 / S) := by
    apply Finset.sum_le_sum
    grind
  apply hsum.trans
  rw [← Finset.mul_sum]
  have hgauss := GaussianSum.normalized_gaussian_lattice_sum_le A u₀ (θ / 2) b S
    (by positivity) hb hS
  grind [mul_le_mul_of_nonneg_left hgauss ((allocationBiasTermConstant_pos r q hβ hθ (τ := τ)).le)]

end

section
variable {A : Finset ℕ} (r q : ℕ)

/-- The resulting finite-sum constant, independent of center and number of levels. -/
def allocationBiasSumConstant (β θ τ b : ℝ) : ℝ :=
  allocationBiasTermConstant r q β θ τ * (2 + Real.sqrt (Real.pi / (θ / 2)) / b)

/-- A single scalar threshold supplies all coordinate-order guards in the finite sum. -/
theorem profile_coordinate_order_admissible {β S z : ℝ}
    (hβ : 0 ≤ β) (hS : 0 < S) (hthreshold : q ≤ β * S / 4) :
    q ≤ Nat.floor (β * quadraticProfile S z) := by
  apply Nat.le_floor
  bound [mul_le_mul_of_nonneg_left (quadraticProfile_lower (z := z) hS) hβ]

/-- The finite bias sum in the original cell-mass variables, assuming their log identities. -/
theorem raw_allocation_bias_sum_bound
    {u₀ b β θ τ S ell T Kstar : ℝ} {K : ℕ → ℝ} (m : ℕ → ℕ)
    (hb : 0 < b) (hβ : 0 ≤ β) (hθ : 0 < θ) (hτ : 0 < τ) (hS : 1 ≤ S)
    (hθβ : τ * β = θ) (hKstar : 0 < Kstar)
    (hK : ∀ j ∈ A, 0 < K j)
    (hlog : ∀ j ∈ A, Real.log (K j) - Real.log Kstar =
      u₀ + j * b + S / 2 - ell - T)
    (hreserve : (r + 1 / 2) * Real.log S ≤ θ * (S - ell - T))
    (hml : ∀ j ∈ A, β * quadraticProfile S (u₀ + j * b + S / 2) - q - 1 ≤ (m j))
    (hmu : ∀ j ∈ A, (m j) + 1 ≤ β * quadraticProfile S (u₀ + j * b + S / 2) + 1) :
    (∑ j ∈ A, (K j) ^ (-θ) * ((m j) + 1) ^ r * (Real.exp (-τ)) ^ (m j)) ≤
      allocationBiasSumConstant r q β θ τ b * Kstar ^ (-θ) := by
  have he j (hj : j ∈ A) : (K j) ^ (-θ) * (Real.exp (-τ)) ^ (m j) =
      Kstar ^ (-θ) * Real.exp (-θ * (u₀ + j * b + S / 2 - ell - T) - τ * (m j)) := by
    rw [Real.rpow_def_of_pos (hK j hj), Real.rpow_def_of_pos hKstar,
      ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    grind
  have hsum := finite_allocation_bias_sum_bound
    hb hβ hθ hτ hS hθβ hreserve hml hmu
  calc
    _ = ∑ j ∈ A, Kstar ^ (-θ) *
        (Real.exp (-θ * (u₀ + j * b + S / 2 - ell - T) - τ * (m j)) * ((m j) + 1) ^ r) := by
      apply Finset.sum_congr rfl
      grind
    _ = Kstar ^ (-θ) * ∑ j ∈ A,
        Real.exp (-θ * (u₀ + j * b + S / 2 - ell - T) - τ * (m j)) * ((m j) + 1) ^ r := by
      rw [Finset.mul_sum]
    _ ≤ Kstar ^ (-θ) *
        (allocationBiasTermConstant r q β θ τ * (2 + Real.sqrt (Real.pi / (θ / 2)) / b)) :=
      by bound
    _ = _ := by unfold allocationBiasSumConstant; ring

end

/-- The actual floored approximation degree in the scalar allocation. -/
def allocatedApproximationDegree (β S z : ℝ) (q : ℕ) : ℕ :=
  Nat.floor (β * quadraticProfile S z) - q

/-- `eq:U12-sum` for the floored scalar allocation, under its explicit reserve and log-cell identities.
No summand or sum bound is an assumption of this theorem. -/
theorem floored_raw_allocation_bias_sum_bound (A : Finset ℕ) (r q : ℕ)
    (u₀ : ℝ) {b β θ τ S ell T Kstar : ℝ} (K : ℕ → ℝ)
    (hb : 0 < b) (hβ : 0 ≤ β) (hθ : 0 < θ) (hτ : 0 < τ) (hS : 1 ≤ S)
    (hθβ : τ * β = θ) (hKstar : 0 < Kstar)
    (hK : ∀ j ∈ A, 0 < K j)
    (hlog : ∀ j ∈ A, Real.log (K j) - Real.log Kstar =
      u₀ + j * b + S / 2 - ell - T)
    (hreserve : (r + 1 / 2) * Real.log S ≤ θ * (S - ell - T))
    (hq : ∀ j ∈ A, q ≤ Nat.floor (β * quadraticProfile S (u₀ + j * b + S / 2))) :
    (∑ j ∈ A, (K j) ^ (-θ) *
      ((allocatedApproximationDegree β S (u₀ + j * b + S / 2) q : ℝ) + 1) ^ r *
        (Real.exp (-τ)) ^ (allocatedApproximationDegree β S (u₀ + j * b + S / 2) q)) ≤
      allocationBiasSumConstant r q β θ τ b * Kstar ^ (-θ) := by
  have hbounds j hj := profile_approximation_degree_bounds
    (mul_nonneg hβ ((by positivity : 0 ≤ S / 4).trans (quadraticProfile_lower (lt_of_lt_of_le zero_lt_one hS)))) (hq j hj)
  exact raw_allocation_bias_sum_bound r q _ hb hβ hθ hτ hS hθβ hKstar hK hlog hreserve (fun j hj => (hbounds j hj).1) (fun j hj => (hbounds j hj).2)

end NearlyMinimax
