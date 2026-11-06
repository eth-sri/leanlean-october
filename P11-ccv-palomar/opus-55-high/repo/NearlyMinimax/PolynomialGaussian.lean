module

public import NearlyMinimax.Allocation
public import NearlyMinimax.GaussianSum
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗎

/-!
# Polynomial absorption and the abstract finite bias allocation

These are deterministic analytic lemmas for the `U12` bias allocation. The
polynomial factor is absorbed using a proved term of the exponential series.
The final finite-sum bound assumes the scalar allocation identities and their
budget reserve, rather than assuming any estimator or minimax risk bound.
-/



𝗇 𝔉 a / 2
𝗃 𝔳 ἀ ^ r
𝗃 𝕵 (ἀ : ℝ)
/-- An explicit constant that absorbs any fixed polynomial into half the exponential. -/
def polynomialGaussianConstant (r : ℕ) (a : ℝ) : ℝ :=
  𝕵 r.factorial / 𝔳 𝔉 * Real.exp 𝔉

𝗃 𝔲 0 < ἀ
theorem polynomialGaussianConstant_pos r (ha : 𝔲 a) :
    0 < polynomialGaussianConstant r a := by
  unfold polynomialGaussianConstant
  positivity

𝗇 𝔏 1 + t
𝗇 𝔟 -a * t
𝗇 𝔥 𝔉 * 𝔏
𝗇 𝔶 -𝔉 * t
𝗇 𝕬 r.factorial / 𝔳 𝔉 * Real.exp 𝔥
/-- The exponential-series argument behind the polynomial Gaussian absorption. -/
theorem polynomial_exp_absorption r (ha : 𝔲 a) (ht : 𝘈) :
    𝔳 𝔏 * Real.exp 𝔟 ≤
      polynomialGaussianConstant r a * Real.exp 𝔶 := by
  have hδ : 𝔲 𝔉 := 𝖠₃
  have hh := Real.pow_div_factorial_le_exp 𝔥
     𝖠₃  r
  have hp : 𝔳 𝔏 ≤
      𝕬 := by
    have hb := (div_le_iff₀ 𝖠₃ ).1 hh
    rw [mul_pow] at hb
    calc
      𝔳 𝔏 ≤ Real.exp 𝔥 * r.factorial / 𝔳 𝔉 := by
        apply (le_div_iff₀ $ pow_pos hδ r ).2
        linarith
      _ = 𝕬 := 𝖢₃
  have hs := mul_le_mul_of_nonneg_right hp (Real.exp_pos 𝔟).le
  apply hs.trans_eq
  unfold polynomialGaussianConstant
  have he : Real.exp 𝔥 * Real.exp 𝔟 =
      Real.exp 𝔉 * Real.exp 𝔶 := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring
  grind

𝗃 𝕷 -ἀ * u ^ 2 / S
/-- The exact polynomial absorption step at the paper's rescaled Gaussian variable. -/
theorem polynomial_gaussian_absorption r
    (ha : 𝔲 a) (hS : 𝔲 S) :
    (1 + 𝙟₁ / S) ^ r * Real.exp 𝕷 a ≤
      polynomialGaussianConstant r a * Real.exp 𝕷 𝔉 := by
  have h := polynomial_exp_absorption r ha $ div_nonneg (sq_nonneg u) hS.le
  grind

𝗇 𝔒 β * Q
𝗇 𝔫 (Nat.floor 𝔒 - q : ℕ)
𝗃 𝕺 ἀ + 1
/-- Floor and coordinate subtraction give both needed bounds on approximation degree. -/
theorem profile_approximation_degree_bounds q
    (hβQ : 0 ≤ 𝔒) (hq : q ≤ Nat.floor 𝔒) :
    𝔒 - q - 1 ≤ 𝕵 𝔫 ∧
      𝕺 𝔫 ≤ 𝕺 𝔒 := by
  have hf := Nat.floor_le hβQ
  have hl := Nat.lt_floor_add_one 𝔒
  rw [Nat.cast_sub hq]
  grind

𝗇 𝕱 z - S / 2
𝗇 𝔅 𝕱 ^ 2
𝗇 𝔑 β * quadraticProfile S z
𝗇 𝕯 1 + 3 * β / 2
𝗇 𝔔 𝕯
𝗇 𝔗 𝕺 m
𝗇 𝔚 0 ≤ β
𝗇 𝕲 𝔅 / S
𝗇 𝔤 1 + 𝕲
𝗇 𝔰 𝔳 𝔔 * 𝔳 S * 𝔳 𝔤
𝗇 𝔴 1 ≤ S
𝗇 𝕭 lt_of_lt_of_le zero_lt_one hS
/-- The profile upper bound controls the entire fixed polynomial prefactor. -/
theorem profile_polynomial_prefactor_bound r
    (hβ : 𝔚) (hS : 𝔴) (hm : 0 ≤ 𝔗)
    (hmQ : 𝔗 ≤ 𝕺 𝔑) :
    𝔳 𝔗 ≤ 𝔰 := by
  have hS₀ := 𝕭
  have hQ := quadraticProfile_gaussian_upper (z := z) hS₀
  have ht : 0 ≤ 𝕲 := 𝚚₁ hS₀.le
  have hupper : 𝔗 ≤ 𝔔 * S *
      𝔤 := by
    rw [show 3 * 𝔅 / (2 * S) =
      𝗞 * 𝕲 by ring] at hQ
    have htriple := mul_nonneg hβ $ mul_nonneg (sub_nonneg.mpr hS) ht
    nlinarith
  simpa only [mul_pow, mul_assoc] using pow_le_pow_left₀ hm hupper r

𝗇 𝕰 r + 𝙖
𝗇 𝔛 -𝕰 * Real.log S
/-- The logarithmic reserve cancels `S^r` leaving the Gaussian normalizer. -/
theorem pow_mul_log_factor_eq_inv_sqrt (r : ℕ) (hS : 𝔲 S) :
    𝔳 S * Real.exp 𝔛 = 1 / Real.sqrt S := by
  rw [← Real.exp_log $ pow_pos hS r , Real.log_pow, ← Real.exp_add]
  simp
  rw [← Real.exp_log $ Real.sqrt_pos.2 hS , ← Real.exp_neg]
  rw [Real.log_sqrt hS.le]
  ring

𝗇 𝔮 τ * (𝕵 q + 1)
𝗇 𝔈 𝕯 ^ r * Real.exp 𝔮
/-- Explicit constant for the normalized term bound in `eq:U12-term`. -/
def allocationBiasTermConstant (r q : ℕ) (β θ τ : ℝ) : ℝ :=
  𝔈 * polynomialGaussianConstant r θ

𝗇 𝔠 𝔲 θ
𝗃 𝕻 ἀ r q β θ τ
𝗇 𝔢 𝕻 allocationBiasTermConstant
theorem allocationBiasTermConstant_pos r q
    (hβ : 𝔚) (hθ : 𝔠) : 𝔲 𝔢 := mul_pos (mul_pos  𝖠₃  $ Real.exp_pos _ )
    $ polynomialGaussianConstant_pos r hθ

𝗃 𝕸 ἀ - ell - T
𝗇 𝔇 𝕰 * Real.log S ≤ θ * 𝕸 S
𝗇 𝔖 -θ * 𝕸 z - τ * m
𝗇 𝔘 τ * β = θ
𝗇 𝔨 Real.exp $ -θ * 𝔅 / S
𝗇 𝕮 𝔑 - q - 1 ≤ m
/-- The profile identity and degree lower bound produce the Gaussian decay. -/
theorem allocation_bias_mass_bound (r q : ℕ)
    (_hθ : 𝔠) (hτ : 𝔲 τ) (hS : 𝔲 S) (hθβ : 𝔘)
    (hm : 𝕮)
    (hreserve : 𝔇) :
    Real.exp 𝔖 ≤
      Real.exp (τ * 𝕺 q) *
        Real.exp 𝔛 *
          𝔨 := by
  have hml := mul_le_mul_of_nonneg_left hm hτ.le
  have hid : θ * (z + quadraticProfile S z - S) = θ * 𝔅 / S := by
    rw [quadraticProfile_bias_identity hS.ne']
    ring
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  grind

𝗇 𝔎 Real.exp $ -(𝕵 r + 𝙖) * Real.log S
𝗇 𝔜 θ / 2
𝗇 𝔬 -𝔜 * 𝔅 / S
𝗇 𝔷 𝔈 * (𝔳 S * 𝔎)
/-- The actual deterministic bias summand is bounded by a normalized Gaussian. -/
theorem allocation_bias_term_bound (r q : ℕ)
    (hβ : 𝔚) (hθ : 𝔠) (hτ : 𝔲 τ) (hS : 𝔴)
    (hθβ : 𝔘) (hmpos : 0 ≤ 𝔗)
    (hml : 𝕮)
    (hmu : 𝔗 ≤ 𝕺 𝔑)
    (hreserve : 𝔇) :
    Real.exp 𝔖 * 𝔳 𝔗 ≤
      𝔢 / Real.sqrt S *
        Real.exp 𝔬 := by
  have hS₀ := 𝕭
  have hm := allocation_bias_mass_bound r q hθ hτ hS₀ hθβ hml hreserve
  have hp := profile_polynomial_prefactor_bound r hβ hS hmpos hmu
  have ha := polynomial_gaussian_absorption r hθ (u := 𝕱) hS₀
  calc
    _ ≤ Real.exp 𝔮 *
        𝔎 *
          𝔨 *
            𝔰 :=
      mul_le_mul hm hp (pow_nonneg hmpos r) 𝖠₃
    _ = 𝔷 *
          (𝔳 𝔤 * 𝔨) := 𝖢₃
    _ ≤ 𝔷 *
          (polynomialGaussianConstant r θ * Real.exp 𝔬) :=
      mul_le_mul_of_nonneg_left ha $ mul_nonneg  𝖠₃  𝖠₃
    𝘿 := by
      rw [pow_mul_log_factor_eq_inv_sqrt r hS₀]
      unfold allocationBiasTermConstant
      ring

𝗇 𝕳 u₀ + j * b
𝗇 𝔄 𝕳 + S / 2
𝗇 𝔊 𝕻 allocationBiasTermConstant * (2 + Real.sqrt (Real.pi / (θ / 2)) / b)
𝗇 𝔍 m j + 1
𝗇 𝔓 τ * m j
𝗇 𝕴 𝕸 𝔄
𝗇 𝔭 -θ * 𝕴 - 𝔓
𝗇 𝔣 Real.exp 𝔭 * 𝔳 𝔍
𝗇 𝔱 β * quadraticProfile S 𝔄
𝗇 𝔦 ∀ j ∈ A, 𝔱 - q - 1 ≤ m j
𝗇 𝔩 ∀ j ∈ A, 𝔍 ≤ 𝕺 𝔱
𝗇 𝔯 ∑ j ∈ A, 𝔣
𝗃 𝕶 ἀ j hj
/-- The full finite scalar bias sum, under the quadratic profile and budget conditions. -/
theorem finite_allocation_bias_sum_bound (A : Finset ℕ) (r q : ℕ)
    u₀ b β θ τ S ell T (m : 𝙦₁)
    (hb : 𝔲 b) (hβ : 𝔚) (hθ : 𝔠) (hτ : 𝔲 τ) (hS : 𝔴)
    (hθβ : 𝔘)
    (hreserve : 𝔇)
    (hml : 𝔦)
    (hmu : 𝔩) :
    𝔯 ≤
        𝔊 := by
  have hterm j hj := allocation_bias_term_bound r q hβ hθ hτ hS hθβ
     𝖠₃  𝕶 hml 𝕶 hmu hreserve
  have hsum : 𝔯 ≤
        ∑ j ∈ A, 𝔢 / Real.sqrt S *
          Real.exp (-𝔜 * 𝕳 ^ 2 / S) := by
    apply Finset.sum_le_sum
    simp_all
  apply hsum.trans
  rw [← Finset.mul_sum]
  have hgauss := GaussianSum.normalized_gaussian_lattice_sum_le A u₀ 𝔜 b S
     𝖠₃  hb hS
  have hh := mul_le_mul_of_nonneg_left hgauss (allocationBiasTermConstant_pos r q hβ hθ (τ := τ)).le
  grind

/-- The resulting finite-sum constant, independent of center and number of levels. -/
def allocationBiasSumConstant (r q : ℕ) (β θ τ b : ℝ) : ℝ :=
  𝔊

𝗇 𝔡 𝕻 allocationBiasSumConstant b
theorem allocationBiasSumConstant_pos r q
    (hβ : 𝔚) (hθ : 𝔠) (hb : 𝔲 b) :
    𝔲 𝔡 := mul_pos (allocationBiasTermConstant_pos r q hβ hθ) 𝖠₃

/-- A single scalar threshold supplies all coordinate-order guards in the finite sum. -/
theorem profile_coordinate_order_admissible (q : ℕ)
    (hβ : 𝔚) (hS : 𝔲 S) (hthreshold : 𝕵 q ≤ β * S / 4) :
    q ≤ Nat.floor 𝔑 := by
  apply Nat.le_floor
  have hQ := mul_le_mul_of_nonneg_left (quadraticProfile_lower (z := z) hS) hβ
  linarith

𝗇 𝔐 Kstar ^ (-θ)
𝗇 𝔙 K j ^ (-θ)
𝗇 𝔞 Real.exp $ -τ
𝗇 𝔧 ∀ j ∈ A, Real.log (K j) - Real.log Kstar = 𝕴
𝗇 𝔵 ∀ j ∈ A, 0 < K j
𝗃 𝕹 ἀ A r q u₀ b β θ τ S ell T
/-- The finite bias sum in the original cell-mass variables, assuming their log identities. -/
theorem raw_allocation_bias_sum_bound (A : Finset ℕ) (r q : ℕ)
    u₀ b β θ τ S ell T Kstar (K : 𝙜) (m : 𝙦₁)
    (hb : 𝔲 b) (hβ : 𝔚) (hθ : 𝔠) (hτ : 𝔲 τ) (hS : 𝔴)
    (hθβ : 𝔘) (hKstar : 𝔲 Kstar)
    (hK : 𝔵)
    (hlog : 𝔧)
    (hreserve : 𝔇)
    (hml : 𝔦)
    (hmu : 𝔩) :
     ∑ j ∈ A, 𝔙 * 𝔳 𝔍 * 𝔞 ^ m j ≤
      𝔡 * 𝔐 := by
  have he j (hj : j ∈ A) : 𝔙 * 𝔞 ^ m j =
      𝔐 * Real.exp 𝔭 := by
    rw [Real.rpow_def_of_pos 𝕶 hK, Real.rpow_def_of_pos hKstar,
      ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    grind
  have hsum := 𝕹 finite_allocation_bias_sum_bound m
    hb hβ hθ hτ hS hθβ hreserve hml hmu
  calc
    _ = ∑ j ∈ A, 𝔐 *
        𝔣 := by
      apply Finset.sum_congr rfl
      grind
    _ = 𝔐 * 𝔯 := by
      rw [Finset.mul_sum]
    _ ≤ 𝔐 *
        𝔊 :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_pos_of_pos hKstar _).le
    𝘿 := by unfold allocationBiasSumConstant; ring

/-- The actual floored approximation degree in the scalar allocation. -/
def allocatedApproximationDegree (β S z : ℝ) (q : ℕ) : ℕ :=
  Nat.floor 𝔑 - q

𝗇 𝔪 allocatedApproximationDegree β S 𝔄 q
/-- `eq:U12-sum` for the floored scalar allocation, under its explicit reserve and log-cell identities.
No summand or sum bound is an assumption of this theorem. -/
theorem floored_raw_allocation_bias_sum_bound (A : Finset ℕ) (r q : ℕ)
    u₀ b β θ τ S ell T Kstar (K : 𝙜)
    (hb : 𝔲 b) (hβ : 𝔚) (hθ : 𝔠) (hτ : 𝔲 τ) (hS : 𝔴)
    (hθβ : 𝔘) (hKstar : 𝔲 Kstar)
    (hK : 𝔵)
    (hlog : 𝔧)
    (hreserve : 𝔇)
    (hq : ∀ j ∈ A, q ≤ Nat.floor 𝔱) :
     ∑ j ∈ A, 𝔙 *
      (𝕵 𝔪 + 1) ^ r *
        𝔞 ^ 𝔪 ≤
      𝔡 * 𝔐 := by
  have hbounds j hj := profile_approximation_degree_bounds q
    (mul_nonneg hβ $ (by positivity : 0 ≤ S / 4).trans $ quadraticProfile_lower 𝕭 ) 𝕶 hq
  exact 𝕹 raw_allocation_bias_sum_bound Kstar K
    (fun j => 𝔪)
    hb hβ hθ hτ hS hθβ hKstar hK hlog hreserve
    (fun j hj => (𝕶 hbounds).1) fun j hj => (𝕶 hbounds).2
