module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
Algebraic and analytic ingredients of Section 4.
The declarations explicitly document which paper claims they cover.
-/

open Complex
namespace RoughRegime.Upper

𝗃 𝔩 q ^ k * (Real.cos $ ἀ * t : ℂ)
/-- The complete cosine generating series, with its constant term corrected to one. -/
def cosineKernel (q : ℂ) (t : ℝ) : ℂ :=
  2 * ∑' k : ℕ, 𝔩 𝙦 - 1

𝗇 𝔓 𝔩 k
𝗇 𝔉 Complex.exp $ -t * I
𝗇 𝔦 t * I
𝗇 𝔎 q * Complex.exp 𝔦
𝗇 𝔢 q * 𝔉
theorem cosine_geometric_term q t (k : ℕ) :
    𝔓 =
      (𝔎 ^ k +
       𝔢 ^ k) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, mul_pow, mul_pow,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  push_cast
  ring

𝗃 𝔚 ‖ἀ‖ < 1
theorem cosine_geometric_hasSum q t (hq : 𝔚 q) :
    HasSum (fun k : ℕ => 𝔓)
      $ ((1 - 𝔎)⁻¹ +
        (1 - 𝔢)⁻¹) / 2 := by
  have ha : 𝔚 𝔎 := by
    simpa
  have hb : 𝔚 𝔢 := by
    simpa only [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one] using hq
  convert ((hasSum_geometric_of_norm_lt_one ha).add
    $ hasSum_geometric_of_norm_lt_one hb ).div_const 2 using 1
  ext k
  exact cosine_geometric_term q t k

𝗃 𝔙 1 - ἀ ^ 2
/-- Poisson-kernel identity underlying Lemma 4, for complex `q` in the open unit disk. -/
theorem cosineKernel_eq q t (hq : 𝔚 q) :
    cosineKernel q t =
      𝔙 q / (1 - 2 * q * Real.cos t + q ^ 2) := by
  let E := Complex.exp 𝔦
  let F := 𝔉
  have hEF : E * F = 1 := by
    rw [← Complex.exp_add]
    simp
  have hsum : E + F = 2 * Real.cos t := by
    rw [Complex.ofReal_cos, Complex.cos]
    ring
  have hE : 1 - q * E ≠ 0 := by
    intro h
    have : q * E = 1 := by linear_combination -h
    have hnorm : ‖q * E‖ < 1 := by simpa [E, norm_mul] using hq
    simp_all
  have hF : 1 - q * F ≠ 0 := by
    intro h
    have : q * F = 1 := by linear_combination -h
    have hnorm : ‖q * F‖ < 1 := by
      dsimp [F]
      simpa only [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one] using hq
    simp_all
  rw [cosineKernel, (cosine_geometric_hasSum q t hq).tsum_eq]
  grind

/-- The midpoint, half-width, geometric mean, and convergence ratio of the paper. -/
def intervalCenter (lo hi : ℝ) : ℝ := (hi + lo) / 2
def intervalHalfWidth (lo hi : ℝ) : ℝ := (hi - lo) / 2
def intervalGeometricMean (lo hi : ℝ) : ℝ := Real.sqrt $ lo * hi
def intervalRho (lo hi : ℝ) : ℝ :=
  (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo)

𝗃 𝔊 ἀ lo hi
𝗇 𝔇 𝔊 intervalRho
𝗇 𝔑 𝙫₁
𝗇 𝔒 𝘰₂
𝗇 𝔠 Real.sqrt_pos.mpr $ lt_trans hlo hlt
theorem intervalRho_pos lo hi (hlo : 𝔑) (hlt : 𝔒) :
    0 < 𝔇 := div_pos (sub_pos.mpr $ Real.sqrt_lt_sqrt hlo.le hlt )
    $ add_pos 𝔠 $ Real.sqrt_pos.mpr hlo

theorem intervalRho_lt_one lo hi (hlo : 𝔑) (hlt : 𝔒) :
    𝔇 < 1 := by
  unfold intervalRho
  have hu := Real.sqrt_pos.mpr hlo
  have hv := 𝔠
  bound

𝗇 𝔏 𝔊 intervalGeometricMean
/-- The two normalization identities used at `z = 1` in Lemma 4. -/
theorem interval_normalizations lo hi (hlo : 𝔑) (hlt : 𝔒) :
    𝔙 𝔇 * 𝔊 intervalCenter =
      𝔏 * (1 + 𝔇 ^ 2) ∧
    𝔙 𝔇 * 𝔊 intervalHalfWidth =
      2 * 𝔇 * 𝔏 := by
  unfold intervalRho intervalCenter intervalHalfWidth intervalGeometricMean
  rw [Real.sqrt_mul hlo.le]
  grind

𝗇 𝔅 𝔊 intervalCenter + 𝔊 intervalHalfWidth * Real.cos t
theorem interval_angular_pos lo hi t (hlo : 𝔑) (hlt : 𝔒) :
    0 < 𝔅 := by
  have hc := Real.neg_one_le_cos t
  unfold intervalCenter intervalHalfWidth at *
  nlinarith

𝗇 𝔍 (-ρ) ^ 2
𝗇 𝔗 2 * -ρ
𝗇 𝔐 -(ρ : ℂ)
𝗇 𝔛 (𝔅 : ℝ)
𝗇 𝔣 1 - 𝔍
𝗃 𝔧 𝔊 ἀ hlo hlt
/-- The normalized reciprocal cosine series in Lemma 4, without any assumed series identity. -/
theorem interval_reciprocal_angular lo hi t (hlo : 𝔑) (hlt : 𝔒) :
    cosineKernel (-𝔇) t =
      𝔏 /
        𝔛 := by
  let ρ := 𝔇
  have hρ := 𝔧 intervalRho_pos
  have hρ1 := 𝔧 intervalRho_lt_one
  have hq : 𝔚 𝔐 := by simpa [ρ, norm_neg, Complex.norm_real, abs_of_pos hρ] using hρ1
  have hn := 𝔧 interval_normalizations
  have hnonzero := ne_of_gt $ 𝔊 interval_angular_pos t hlo hlt
  have hden :
      (1 - 𝔗 * Real.cos t + 𝔍) *
      (𝔏 : ℂ) =
      𝔣 *
      𝔛 := by
    have hr : (1 - 𝔗 * Real.cos t + 𝔍) *
        𝔏 = 𝔣 *
        𝔅 := by
      grind
    exact_mod_cast hr
  rw [cosineKernel_eq _ _ hq]
  have hdnonzero : 1 - 𝔗 * (Real.cos t : ℂ) + 𝔍 ≠ 0 := by
    have hB : 𝔙 𝔐 ≠ 0 := by
      simpa only [neg_sq] using by exact_mod_cast 𝖥₃
    intro hz
    rw [hz, zero_mul] at hden
    have : 𝔙 𝔐 *
      𝔛 ≠ 0 :=
      mul_ne_zero hB $ by exact_mod_cast hnonzero
    exact this hden.symm
  apply (div_eq_div_iff hdnonzero $ by exact_mod_cast hnonzero ).mpr
  grind

𝚵

𝗇 𝔜 Fin n → Ω → 𝗓
/-- Ordered, distinct-sample lift of one monomial. The denominator is exactly `n_q`. -/
def monomialLift (σ : Fin q → Fin p)
    (X : 𝔜) (ω : Ω) : ℝ :=
  (n.descFactorial q : ℝ)⁻¹ *
    ∑ e : Fin q ↪ Fin n, ∏ i : Fin q, X (e i) ω (σ i)

𝗇 𝔄 (x - 𝔊 intervalCenter) / 𝔊 intervalHalfWidth
𝗇 𝔘 -(𝔇 : ℂ) * z
𝗇 𝔞 𝘆
/-- The Chebyshev series of Lemma 4; index `k + 1` enumerates the positive integers. -/
def reciprocalSeries (lo hi : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  1 + 2 * ∑' k : ℕ,
    𝔘 ^ 𝔞 *
      (((Polynomial.Chebyshev.T ℝ (𝘆 : ℕ)).eval
        𝔄 : ℝ) : ℂ)

theorem reciprocalSeries_eq_cosineKernel lo hi x z t
    (hrep : 𝔄 = Real.cos t)
    (hq : 𝔚 𝔘) :
    𝔊 reciprocalSeries z x = cosineKernel (-𝔇 * z) t := by
  let q := -𝔇 * z
  have hs := (cosine_geometric_hasSum q t hq).summable
  have heval k :
      (Polynomial.Chebyshev.T ℝ (𝘆 : ℕ)).eval (Real.cos t) =
        Real.cos ( (𝔞 : ℕ) * t) := by
    simp
  unfold reciprocalSeries cosineKernel
  rw [hrep]
  simp_rw [heval]
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, Complex.ofReal_one]
  ring

𝗇 𝔤 x ∈ 𝔊 Set.Icc
theorem interval_argument_mem lo hi x (hlo : 𝔑) (hlt : 𝔒)
    (hx : 𝔤) :
    𝔄 ∈ Set.Icc (-1) 1 := by
  have hd : 0 < 𝔊 intervalHalfWidth := by unfold intervalHalfWidth; positivity
  constructor
  · apply (le_div_iff₀ hd).mpr
    unfold intervalCenter intervalHalfWidth
    grind
  · apply (div_le_iff₀ hd).mpr
    unfold intervalCenter intervalHalfWidth
    grind

/-- The `z = 1` reciprocal identity of Lemma 4, for every point in the interval. -/
theorem reciprocal_expansion_at_one lo hi x (hlo : 𝔑) (hlt : 𝔒)
    (hx : 𝔤) :
    𝔊 reciprocalSeries 1 x = 𝔏 / x := by
  let y := 𝔄
  let t := Real.arccos y
  have hy := 𝔊 interval_argument_mem x hlo hlt hx
  have hcos : Real.cos t = y := Real.cos_arccos hy.1 hy.2
  have hlt1 := 𝔧 intervalRho_lt_one
  have hq : ‖(-𝔇 * (1 : ℂ))‖ < 1 := by
    simpa [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos 𝔧 intervalRho_pos] using hlt1
  rw [𝔊 reciprocalSeries_eq_cosineKernel x 1 t hcos.symm hq]
  simp
  rw [𝔊 interval_reciprocal_angular t hlo hlt]
  rw [hcos]
  dsimp [y]
  have hd : 𝔊 intervalHalfWidth ≠ 0 := by unfold intervalHalfWidth; positivity
  field_simp
  ring

𝗇 𝔔 Fin p →₀ ℕ
/-- Slots of an exponent vector: variable `i` occurs `α i` times. -/
def ExponentSlots (α : 𝔔) := Σ i : Fin p, Fin $ α i

instance (α : 𝔔) : Fintype $ ExponentSlots α := by
  unfold ExponentSlots
  infer_instance

𝗇 𝔥 (Fintype.equivFin $ ExponentSlots α ).symm
𝗇 𝔈 (𝔥 j).1
𝗇 𝔖 Fintype.card $ ExponentSlots α
/-- A fixed ordering of the factors of a monomial. -/
def exponentCoordinates (α : 𝔔) :
    Fin 𝔖 → Fin p :=
  fun j => 𝔈

𝗇 𝔟 fun _ e => e
𝗇 𝔡 𝘦
theorem exponentSlots_card (α : 𝔔) :
    𝔖 = α.sum 𝔟 := by
  unfold ExponentSlots
  simp
  exact (Finsupp.sum_fintype α 𝔟 𝔡).symm

theorem exponentCoordinates_prod α (m : 𝗓) :
     ∏ j, m (exponentCoordinates α j) = ∏ i : Fin p, m i ^ α i := by
  change ∏ j : Fin 𝔖,
    m 𝔈 = _
  rw [Fintype.prod_equiv 𝔥
    (fun j => m 𝔈)
    (fun s => m s.1) 𝔡]
  unfold ExponentSlots
  rw [Fintype.prod_sigma]
  simp

/-- The polynomial lift, explicitly replacing each monomial by its distinct-sample statistic. -/
def polynomialLift (F : 𝙩₁)
    (X : 𝔜) (ω : Ω) : ℝ :=
  ∑ α ∈ F.support, F.coeff α * monomialLift (exponentCoordinates α) X ω

theorem chebyshev_abs_le_one y (hy : y ∈ Set.Icc (-1) 1) k :
    |(Polynomial.Chebyshev.T ℝ (k : ℕ)).eval y| ≤ 1 := by
  rw [← Real.cos_arccos hy.1 hy.2 , Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- Scalar real form of the reciprocal series. -/
theorem reciprocal_real_series lo hi x (hlo : 𝔑) (hlt : 𝔒)
    (hx : 𝔤) :
    1 + 2 * ∑' k : ℕ, (-𝔇) ^ 𝔞 *
      (Polynomial.Chebyshev.T ℝ (𝘆 : ℕ)).eval
        𝔄 =
      𝔏 / x := by
  have h := 𝔊 reciprocal_expansion_at_one x hlo hlt hx
  unfold reciprocalSeries at h
  simp only [mul_one, ← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_tsum] at h
  apply Complex.ofReal_injective
  simp_all
