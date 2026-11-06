module

public import NearlyMinimax.PaperIncrement
public import RoughRegime.ComplexDerivativeBridge
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/

open Polynomial

𝗃 𝔶 ἀ + 1
𝗇 𝔈 𝔶 n
𝗃 𝖉 ἀ - 1 - j
𝗇 𝔇 𝖉 n
𝗇 𝔏 n + 2
𝗇 𝔚 chebyshevForcing x y
𝗇 𝔤 𝙪₁
𝗇 𝔷 matrixChebyshevT y n
𝗇 𝕴 matrixChebyshevT x 𝔏
𝗇 𝕵 matrixChebyshevT x n
𝗇 𝕶 matrixChebyshevU x n
𝗇 𝕷 chebyshevResponse x 𝔚 n
𝗃 𝖑 2 * ἀ
section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]

𝗇 𝔐 (n : ℤ)
def matrixChebyshevT (x : R) (n : ℕ) : R := aeval x $ Chebyshev.T ℝ 𝔐
def matrixChebyshevU (x : R) (n : ℤ) : R := aeval x $ Chebyshev.U ℝ n

𝗇 𝔵 𝖑 x
section

variable (x : R)

theorem matrixChebyshevT_recurrence n :
    𝕴 = 𝔵 * matrixChebyshevT x 𝔈 - 𝕵 := by
  unfold matrixChebyshevT
  simp [map_ofNat]

theorem matrixChebyshevU_recurrence n :
    matrixChebyshevU x 𝔈 = 𝔵 * 𝕶 - matrixChebyshevU x 𝗈 := by
  unfold matrixChebyshevU
  rw [Chebyshev.U_add_one]
  simp [map_ofNat]

end

/-- The forcing term for Chebyshev polynomials at two possibly noncommuting matrices. -/
def chebyshevForcing (x y : R) (j : ℕ) : R :=
  if 𝘠 then 𝔤 else 𝖑 𝔤 * matrixChebyshevT y j

𝗃 𝔴 ∑ j ∈ Finset.range n, matrixChebyshevU x 𝖉 ἀ * f j
def chebyshevResponse (x : R) (f : ℕ → R) (n : ℕ) : R :=
  𝔴 𝔐

theorem chebyshevResponse_recurrence (x : R) f n :
    chebyshevResponse x f 𝔏 =
      𝔵 * chebyshevResponse x f 𝔈 - chebyshevResponse x f n + f 𝔈 := by
  unfold chebyshevResponse
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  simp only [show 𝔐 + 2 - 1 - n = 1 by ring,
    show 𝔐 + 2 - 1 - 𝔈 = 0 by ring,
    show 𝔶 𝔐 - 1 - n = 0 by ring]
  simp only [matrixChebyshevU, Chebyshev.U_zero, Chebyshev.U_one,
    map_one, map_mul, map_ofNat, aeval_X, one_mul]
  change 𝔴 𝔏 +
    𝔵 * f n + f 𝔈 =
    𝔵 * (𝔴 𝔈 + f n) -
      ∑ j ∈ Finset.range n, matrixChebyshevU x 𝔇 * f j + f 𝔈
  have hindex j : 𝖉 𝔏 = 𝔶 𝔐 - 1 - j + 1 := 𝖢₃
  simp_rw [hindex, matrixChebyshevU_recurrence]
  have hindex' j : 𝖉 𝔈 - 1 = 𝖉 𝔐 := 𝖢₃
  simp_rw [hindex']
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  noncomm_ring

/-- Exact discrete variation of constants; no commutativity of the two arguments is assumed. -/
theorem matrixChebyshevT_perturbation_identity (x y : R) n :
    𝔷 - 𝕵 =
      𝕷 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [matrixChebyshevT, chebyshevResponse]
  | one => simp [matrixChebyshevT, chebyshevResponse, chebyshevForcing, matrixChebyshevU]
  | more n hn hn1 =>
    rw [matrixChebyshevT_recurrence, matrixChebyshevT_recurrence,
      chebyshevResponse_recurrence, ← hn, ← hn1]
    simp only [chebyshevForcing, show 𝔈 ≠ 0 by omega, ↓reduceIte]
    noncomm_ring

end ChebyshevPerturbation

𝗇 𝔅 (𝔶 k : ℕ)
𝗃 𝖒 η ^ ἀ
/-- A finite positive weighted geometric constant; it is independent of polynomial degree. -/
def perturbationConstant (η : ℝ) : ℝ := ∑' k : ℕ, (𝔅 : ℝ) * 𝖒 k

𝗇 𝔬 fun k => 𝔅 * 𝖒 k
𝗇 𝕬 0 < η
𝗇 𝕭 η < 1
theorem perturbationConstant_pos η (hη : 𝕬) (hη1 : 𝕭) :
    0 < perturbationConstant η := by
  have hs : Summable 𝔬 := by
    simpa using RoughRegime.SeriesBounds.weighted_geometric_summable 1 η hη hη1
  apply hs.tsum_pos fun k => by positivity 0
  simp

𝗇 𝔄 (n - j : ℕ)
𝗇 𝔉 η ^ (n - j)
𝗇 𝔩 𝔶 j
𝗇 𝕸 j ∈ Finset.range n
𝗃 𝖏 (ἀ : ℕ)
theorem weighted_convolution_le_constant η (hη : 𝕬) (hη1 : 𝕭) n :
     ∑ j ∈ Finset.range n, (𝔄 : ℝ) * 𝔉 ≤ perturbationConstant η := by
  have hs : Summable 𝔬 := by
    simpa using RoughRegime.SeriesBounds.weighted_geometric_summable 1 η hη hη1
  rw [← Finset.sum_range_reflect]
  have he j (hj : 𝕸) : n - 𝔇 = 𝔩 := by
    grind
  calc
    _ = ∑ j ∈ Finset.range n, 𝔩 * 𝖒 𝔩 := by
      apply Finset.sum_congr rfl
      simp_all
    _ ≤ ∑ j ∈ Finset.range n, 𝖏 𝔩 * 𝖒 j := by
      bound
    𝖦 := hs.sum_le_tsum (Finset.range n) fun k hk => 𝖠₃

𝗇 𝔣 𝖒 n
𝗇 𝔥 𝘿
𝗇 𝔟 𝔄 * 𝔉
𝗇 𝔪 𝔄 * u j
𝗇 𝔓 𝖑 δ
𝗇 𝔢 4 * δ * perturbationConstant η
𝗃 𝖈 ∑ j ∈ Finset.range n, ἀ
𝗇 𝔲 1 + 𝔓 * 𝖈 𝔪
𝗇 𝕮 𝚈
/-- Discrete Gronwall majorant with a second-order convolution kernel. -/
theorem recurrence_exponential_majorant (u : 𝙜) η δ
    (hη : 𝕬) (hη1 : 𝕭) (hδ : 𝕮)
    (hsmall : 𝔢 ≤ 1)
    (hu : ∀ n, u n ≤ 𝔲) n :
    𝔣 * u n ≤ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hterm j (hj : 𝕸) :
        𝔣 * 𝔪 ≤
          𝖑 𝔟 := by
      have hjn := Finset.mem_range.mp hj
      have hp : 𝔣 = 𝔉 * 𝖒 j := by
        rw [← pow_add, Nat.sub_add_cancel $ Nat.le_of_lt hjn ]
      calc
        _ = 𝔟 * (𝖒 j * u j) := 𝖤₃
        _ ≤ 𝔟 * 2 :=
          mul_le_mul_of_nonneg_left (ih j hjn) 𝖠₃
        𝔥 := 𝖢₃
    have hsum := Finset.sum_le_sum hterm
    calc
      𝔣 * u n ≤ 𝔣 * 𝔲 :=
        mul_le_mul_of_nonneg_left (hu n) $ pow_nonneg hη.le n
      _ = 𝔣 + 𝔓 * ∑ j ∈ Finset.range n,
          𝔣 * 𝔪 := by rw [← Finset.mul_sum]; ring
      _ ≤ 1 + 𝔓 * ∑ j ∈ Finset.range n,
          𝖑 𝔟 :=
        add_le_add (pow_le_one₀ hη.le hη1.le) $ mul_le_mul_of_nonneg_left hsum 𝖠₃
      _ = 1 + 4 * δ * 𝖈 𝔟 := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ 1 + 𝔢 :=
        add_le_add (le_refl 1) $ mul_le_mul_of_nonneg_left
          (weighted_convolution_le_constant η hη hη1 n) 𝖠₃
      _ ≤ 2 := 𝖡₄

𝗃 𝖊 ‖ἀ‖
𝗃 𝖋 (2 : ἀ)
section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]

private theorem norm_two_ring : ‖𝖋 R‖ = 2 := by
  have h : 2 = 𝖋 ℝ • (1 : R) := by norm_num [Algebra.smul_def, map_ofNat]
  simp_all

𝗇 𝔙 ∀ n, ‖matrixChebyshevT x n‖ ≤ 1
𝗇 𝕹 𝖏 𝔏
theorem matrixChebyshevU_norm_le (x : R) (hx : 𝔙) (n : ℕ) :
    𝖊 𝕶 ≤ 𝔈 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [matrixChebyshevU]
  | one =>
    have hx1 : 𝖊 x ≤ 1 := by simpa [matrixChebyshevT] using hx 1
    simp only [matrixChebyshevU, Nat.cast_one, Chebyshev.U_one, map_mul, map_ofNat, aeval_X]
    calc
      _ ≤ ‖2‖ * 𝖊 x := norm_mul_le ..
      _ ≤ 2 := by rw [norm_two_ring]; linarith
      𝔥 := by norm_num
  | more n hn hn1 =>
    have he : matrixChebyshevU x 𝕹 =
        𝖑 𝕴 + 𝕶 := by
      unfold matrixChebyshevU matrixChebyshevT
      rw [show (𝕹 : ℤ) = 𝔏 by omega, Chebyshev.U_eq_two_mul_T_add_U]
      simp [map_ofNat]
    rw [he]
    calc
      _ ≤ ‖𝖑 𝕴‖ + 𝖊 𝕶 := norm_add_le ..
      _ ≤ 2 * 𝖊 𝕴 + 𝔈 := add_le_add (by simpa only [norm_two_ring] using norm_mul_le 𝖋 R _) hn
      𝖦 := 𝖤₃

section

variable (x y : R)

𝗇 𝔑 ‖matrixChebyshevT y j‖
𝗇 𝕯 𝖊 𝔤 ≤ δ
𝗇 𝕺 𝔓 * 𝔑
theorem chebyshevForcing_norm_le δ (hδ : 𝕮)
    (hd : 𝕯) j :
    ‖𝔚 j‖ ≤ 𝕺 := by
  unfold chebyshevForcing
  split_ifs with hj
  · subst j
    simpa [matrixChebyshevT] using hd.trans 𝖡₄
  · calc
      _ ≤ ‖𝖑 𝔤‖ * 𝔑 := norm_mul_le ..
      _ ≤ 𝕺 := by
        apply mul_le_mul_of_nonneg_right _ $ norm_nonneg _
        exact (norm_mul_le ..).trans $ by rw [norm_two_ring]; gcongr

𝗇 𝔰 𝖏 𝔇
𝗇 𝕰 𝔄 * 𝔑
𝗇 𝕱 ‖matrixChebyshevU x 𝔇 * 𝔚 j‖
theorem matrixChebyshevT_norm_volterra
    (hx : 𝔙) δ (hδ : 𝕮)
    (hd : 𝕯) n :
    𝖊 𝔷 ≤ 1 + 𝔓 *
      𝖈 𝕰 := by
  have hterm j (hj : 𝕸) :
      𝕱 ≤
        𝔓 * 𝕰 := by
    have hjn := Finset.mem_range.mp hj
    have hi : 𝔇 = (𝔰 : ℤ) := 𝖡₃
    have hn : 𝔶 𝔰 = (𝔄 : ℝ) := by
      exact_mod_cast 𝖡₃
    rw [hi]
    calc
      _ ≤ ‖matrixChebyshevU x 𝔰‖ *
          ‖𝔚 j‖ := norm_mul_le ..
      _ ≤ 𝔶 𝔰 *
          𝕺 :=
        mul_le_mul (matrixChebyshevU_norm_le x hx _) (chebyshevForcing_norm_le x y δ hδ hd j)
          (norm_nonneg _) 𝖠₃
      𝔥 := 𝖤₃
  have he : 𝔷 = 𝕵 +
      𝕷 := by
    exact sub_eq_iff_eq_add'.mp $ matrixChebyshevT_perturbation_identity x y n
  rw [he]
  calc
    _ ≤ 𝖊 𝕵 + 𝖊 𝕷 := norm_add_le ..
    _ ≤ 1 + 𝖈 𝕱 :=
      add_le_add (hx n) $ norm_sum_le ..
    _ ≤ 1 + ∑ j ∈ Finset.range n,
        𝔓 * 𝕰 :=
      add_le_add (le_refl 1) $ Finset.sum_le_sum hterm
    𝔥 := by rw [Finset.mul_sum]

/-- Uniform exponential control in a fixed noncommutative neighborhood of a bounded
Chebyshev center. The radius depends on `η`, never on the polynomial degree. -/
theorem matrixChebyshevT_neighborhood_bound
    (hx : 𝔙) η δ
    (hη : 𝕬) (hη1 : 𝕭) (hδ : 𝕮)
    (hsmall : 𝔢 ≤ 1) (hd : 𝕯) n :
    𝔣 * 𝖊 𝔷 ≤ 2 :=
  recurrence_exponential_majorant (fun n => 𝖊 𝔷) η δ hη hη1 hδ hsmall
    (matrixChebyshevT_norm_volterra x y hx δ hδ hd) n

end

end ChebyshevNorm

𝗇 𝔔 q ^ k
𝗃 𝖌 ‖PowerSeries.coeff k ἀ‖
section PowerSeriesBounds
variable {R I : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq I]

𝗇 𝔮 ∏ i ∈ s, f i
/-- Finite Cauchy products preserve a common geometric envelope in any normed
commutative ring, including the complexified matrix entries. -/
theorem powerSeries_prod_geometric_bound s (f : I → PowerSeries R)
    q B (hq : 0 < q) (hB : 𝙐)
    (hf : ∀ i ∈ s, ∀ k, ‖PowerSeries.coeff k (f i)‖ ≤ B * 𝔔) k :
    𝖌 𝔮 ≤
      B ^ s.card * 𝔅 ^ s.card * 𝔔 := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp
    split_ifs with hk
    · simp_all
    · simp ; positivity
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound
      (fun j => PowerSeries.coeff j 𝔮)
      (fun j => PowerSeries.coeff j $ f a ) s.card k q (B ^ s.card) B hq
       𝖠₃  hB
      ( ih fun i hi => hf i $ Finset.mem_insert_of_mem hi )
      $ hf a $ Finset.mem_insert_self ..
    rw [PowerSeries.coeff_mul]
    simpa only [RoughRegime.SeriesBounds.convolution, Finset.card_insert_of_notMem ha,
      pow_succ] using hh

end PowerSeriesBounds

𝗇 𝔒 Finset.range 𝔶 m
𝗃 𝖍 ἀ i j
𝗇 𝔡 𝖍 K
𝗇 𝖃 complexKernelSeries lo hi
section ComplexMatrices
𝚼
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
𝛞

𝗇 𝖆 𝘉₁
𝗇 𝔎 𝖆 ℂ
𝗇 𝕻 (intervalHalfWidth lo hi)⁻¹
def normalizeMatrix (lo hi : ℝ) (A : 𝔎) : 𝔎 :=
  𝕻 • (A - intervalCenter lo hi • 1)

𝗇 𝔛 normalizeMatrix lo hi A
theorem normalizedChebyshev_aeval_complex lo hi (A : 𝔎) k :
    aeval A (normalizedChebyshev lo hi k) = matrixChebyshevT 𝔛 k := by
  rw [normalizedChebyshev, aeval_comp]
  congr 1
  simp [normalizeMatrix, Algebra.smul_def]

𝗇 𝕼 spectrum ℝ A ⊆ Set.Icc lo hi
theorem normalizedChebyshev_complex_center_bound lo hi (hlo : 𝙫₁) (hlt : 𝘰₂)
    (A : 𝔎) (hA : A.IsHermitian) (hSpec : 𝕼) k :
    ‖matrixChebyshevT 𝔛 k‖ ≤ 1 := by
  rw [← normalizedChebyshev_aeval_complex]
  rw [← cfc_polynomial _ A $ Matrix.isHermitian_iff_isSelfAdjoint.mp hA ]
  apply norm_cfc_le 𝖠₄
  intro x hx
  rw [normalizedChebyshev_eval, Real.norm_eq_abs]
  exact RoughRegime.Upper.chebyshev_abs_le_one _
    (interval_argument_mem lo hi x hlo hlt $ hSpec hx ) k

𝗇 𝔫 normalizeMatrix lo hi B
theorem normalizeMatrix_sub lo hi (A B : 𝔎) :
    𝔫 - 𝔛 =
      𝕻 • (B - A) := by
  simp only [normalizeMatrix, ← smul_sub]
  abel

theorem matrix_entry_norm_le_l2 (A : 𝔎) i j : ‖𝖍 A‖ ≤ 𝖊 A := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have he : 𝖊 e = 1 := 𝖨₄
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) A
  have hi := PiLp.norm_apply_le (T e) i
  have hentry : (T e) i = 𝖍 A := by
    aesop
  rw [hentry] at hi
  exact hi.trans $ by simpa [he, T, Matrix.l2_opNorm_toEuclideanCLM] using
    (T.le_opNorm e)

𝗇 𝔦 𝖆 $ PowerSeries ℂ
𝗇 𝕲 kernelCoefficientPolynomial lo hi k
/-- The complex kernel is evaluated at arbitrary, possibly nonnormal matrices. -/
def complexKernelSeries (lo hi : ℝ) (A : 𝔎) : 𝔦 :=
  fun i j => PowerSeries.mk fun k => (aeval A 𝕲) i j

𝗇 𝕽 2 * intervalRho lo hi ^ k
theorem complex_kernel_coefficient_bound lo hi (hlo : 𝙫₁) (hlt : 𝘰₂)
    (A B : 𝔎) (hA : A.IsHermitian) (hSpec : 𝕼)
    η δ (hη : 𝕬) (hη1 : 𝕭) (hδ : 𝕮)
    (hsmall : 𝔢 ≤ 1)
    (hd : ‖𝔫 - 𝔛‖ ≤ δ) k :
    ‖aeval B 𝕲‖ ≤
      4 * (intervalRho lo hi / η) ^ k := by
  have hb := matrixChebyshevT_neighborhood_bound
    𝔛 𝔫
    (normalizedChebyshev_complex_center_bound lo hi hlo hlt A hA hSpec)
    η δ hη hη1 hδ hsmall hd k
  unfold kernelCoefficientPolynomial
  rw [map_mul, aeval_C, ← Algebra.smul_def, norm_smul, normalizedChebyshev_aeval_complex]
  have hr := 𝘱₂
  split_ifs with hk
  · subst k
    simp [matrixChebyshevT]
  · rw [Real.norm_eq_abs, abs_mul, show |𝖋 ℝ| = 2 by norm_num,
      abs_pow, abs_neg, abs_of_pos hr]
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ $ pow_pos hη k ).mpr
    calc
      _ = 𝕽 * (𝖒 k * ‖matrixChebyshevT 𝔫 k‖) := 𝖢₃
      _ ≤ 𝕽 * 2 := mul_le_mul_of_nonneg_left hb 𝖠₃
      𝔥 := 𝖢₃

𝗇 𝔖 Fintype.card $ Equiv.Perm n
𝗇 𝔯 ∏ i, K (σ i) i
𝗇 𝔱 ∀ i j k, 𝖌 𝔡 ≤ B * 𝔔
𝗇 𝕳 𝔖 * B ^ Fintype.card n
theorem determinant_series_coefficient_bound (K : 𝔦)
    q B (hq : 0 < q) (hB : 𝙐)
    (hK : 𝔱) k :
    𝖌 K.det ≤
      𝕳 *
        𝔅 ^ Fintype.card n * 𝔔 := by
  rw [Matrix.det_apply, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (Equiv.Perm.sign σ • 𝔯)‖ :=
      norm_sum_le ..
    _ = ∑ σ : Equiv.Perm n, 𝖌 𝔯 := by
      simp
    _ ≤ ∑ _σ : Equiv.Perm n,
        B ^ Fintype.card n * 𝔶 k ^ Fintype.card n * 𝔔 := by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa using powerSeries_prod_geometric_bound Finset.univ (fun i => K (σ i) i) q B hq hB
        (fun i hi => hK _ _ ) k
    𝔥 := by simp [mul_assoc]

𝗇 𝔍 Fintype.card n + 1
𝗇 𝔳 PowerSeries.coeff k $ 𝔡 * L.det
𝗇 𝕾 𝔖 * B ^ 𝔍
𝗇 𝕿 𝔅 ^ 𝔍 * 𝔔
𝗇 𝖀 A * 𝔅 ^ 𝔍 * 𝔔
𝗃 𝖐 fun k => PowerSeries.coeff k ἀ
/-- A finite combined-index inverse/determinant truncation admits a common
degree-independent bound whenever its entries share a geometric envelope. -/
theorem combined_truncation_uniform_bound (K L : 𝔦)
    q B (hq : 0 < q) (hq1 : q < 1) (hB : 𝙐)
    (hK : 𝔱)
    (hL : ∀ i j k, ‖PowerSeries.coeff k 𝖍 L‖ ≤ B * 𝔔)
    i j m :
    ‖∑ k ∈ 𝔒, 𝔳‖ ≤
      𝕾 *
        ∑' k : ℕ, 𝕿 := by
  let A := 𝕾
  have hcoeff k : 𝖊 𝔳 ≤
      𝖀 := by
    rw [mul_comm, PowerSeries.coeff_mul]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound
      𝖐 L.det 𝖐 𝔡
      (Fintype.card n) k q 𝕳 B
      hq  𝖠₃  hB (determinant_series_coefficient_bound L q B hq hB hL) 𝖍 hK
    simpa [RoughRegime.SeriesBounds.convolution, A, pow_succ, mul_assoc] using hh
  have hs := (RoughRegime.SeriesBounds.weighted_geometric_summable 𝔍 q hq hq1).mul_left A
  calc
    _ ≤ ∑ k ∈ 𝔒, 𝖊 𝔳 := norm_sum_le ..
    _ ≤ ∑ k ∈ 𝔒, 𝖀 :=
      Finset.sum_le_sum fun k hk => hcoeff k
    _ ≤ ∑' k : ℕ, A * 𝕿 := by
      simpa only [mul_assoc] using hs.sum_le_tsum 𝔒 fun k hk => 𝖠₃
    𝔥 := by rw [tsum_mul_left]

𝗇 𝔭 fun ij => A ij.1 ij.2
theorem variableMatrix_power_eval_complex (A : 𝔎) k i j :
    MvPolynomial.eval₂ Complex.ofRealHom 𝔭
      ((variableMatrix n ^ k) i j) = 𝚇₁ i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> simp
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, ih]
    simp [variableMatrix]

theorem matrixEntryPolynomial_eval_complex p (A : 𝔎) i j :
    MvPolynomial.eval₂ Complex.ofRealHom 𝔭
      (matrixEntryPolynomial p i j) = (aeval A p) i j := by
  rw [Polynomial.aeval_eq_sum_range]
  unfold matrixEntryPolynomial
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    variableMatrix_power_eval_complex, Matrix.sum_apply]
  rfl

theorem variableKernelSeries_eval_complex lo hi A :
    (PowerSeries.map $ MvPolynomial.eval₂Hom Complex.ofRealHom fun ij : n × n => A ij.1 ij.2 ).mapMatrix
      𝗝₂ = 𝖃 A := by
  ext i j k
  exact matrixEntryPolynomial_eval_complex _ A i j

/-- Complexification of real matrices preserves the real functional calculus. -/
def ofRealMatrixStarAlgHom : 𝖆 ℝ →⋆ₐ[ℝ] 𝔎 :=
  { Complex.ofRealHom.mapMatrix with
    commutes' := by
      intro a
      ext i j
      change ((if i = j then a else 0 : ℝ) : ℂ) = if i = j then (a : ℂ) else 0
      split_ifs <;> simp
    map_star' := by
      intro A
      ext i j
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] }

theorem ofRealMatrixStarAlgHom_injective : Function.Injective $ ofRealMatrixStarAlgHom (n := n) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective $ congrArg (fun M => 𝖍 M) h

theorem complexify_matrix_spectrum (A : 𝖆 ℝ) (hA : A.IsHermitian) :
    spectrum ℝ (A.map Complex.ofReal) = spectrum ℝ A := by
  have hs := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  exact hs.map_spectrum_real ofRealMatrixStarAlgHom
    ofRealMatrixStarAlgHom_injective
    (ofRealMatrixStarAlgHom ).toAlgHom.toLinearMap.continuous_of_finiteDimensional

end ComplexMatrices

𝗇 𝖄 𝗲
𝗇 𝔊 𝖄 ℂ
section ComplexFreeCoordinates
open RoughRegime.Upper RoughRegime.CombinedPolynomial RoughRegime.MatrixDeterminant
𝛐

def complexParentValuation (A C : 𝔊) : parentInverseVariables r → ℂ
  | Sum.inl ij => A ij.1 ij.2
  | Sum.inr ⟨_, ij⟩ => C ij.1 ij.2

theorem eval_renamed_series_complex (f : V → W) values
    (P : PowerSeries $ MvPolynomial V ℝ ) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom values)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
      PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom $ values ∘ f ) P := by
  ext k
  exact MvPolynomial.eval₂_rename ..

𝗇 𝖅 complexParentValuation r A C
𝗇 𝔗 MvPolynomial.eval₂Hom Complex.ofRealHom 𝖅
𝗇 𝔧 fun _ => r
𝗃 𝖎 PowerSeries.map 𝔗 $ ἀ r 𝔧 lo hi i j
theorem inverseVariableSeries_eval_complex lo hi
    A C i j :
    𝖎 inverseVariableSeries = 𝖃 A i j := by
  rw [inverseVariableSeries, eval_renamed_series_complex]
  exact congrArg (fun K => 𝔡) $ variableKernelSeries_eval_complex lo hi A

theorem determinantVariableSeries_eval_complex lo hi
    A C t :
    PowerSeries.map 𝔗
      (determinantVariableSeries r 𝔧 lo hi t) =
      (𝖃 C).det := by
  rw [determinantVariableSeries, eval_renamed_series_complex]
  change PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom fun ij => C ij.1 ij.2 )
    (𝗝₂).det = _
  rw [RingHom.map_det, variableKernelSeries_eval_complex]

𝗇 𝔠 𝖃 A i j * (𝖃 C).det
theorem parentInverseEntryPolynomial_eval_complex lo hi
    A C i j m :
    MvPolynomial.eval₂ Complex.ofRealHom 𝖅
      (parentInverseEntryPolynomial lo hi r m i j) =
       (intervalGeometricMean lo hi ^ 𝔶 r)⁻¹ *
        ∑ k ∈ 𝔒,
          PowerSeries.coeff k 𝔠 := by
  have he : 𝖎 combinedVariableSeries =
      𝔠 := by
    simp only [combinedVariableSeries, map_mul, inverseVariableSeries_eval_complex,
      determinantVariableSeries_eval_complex, Fin.prod_univ_one]
  simp only [parentInverseEntryPolynomial, truncationEntryPolynomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hc := congrArg ( PowerSeries.coeff k ) he
  assumption

end ComplexFreeCoordinates

section PolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A concrete finite coefficient envelope for a real polynomial on a complex coordinate ball. -/
def polynomialCoordinateBound (P : MvPolynomial V ℝ) (R : ℝ) : ℝ :=
  ∑ α ∈ P.support, ‖P.coeff α‖ * ∏ j : V, R ^ α j

theorem polynomial_complex_coordinate_bound P (z : V → ℂ)
    R (hR : 𝖡₂) (hz : ∀ j, ‖z j‖ ≤ R) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ polynomialCoordinateBound P R := by
  rw [MvPolynomial.eval₂_eq']
  calc
    _ ≤ ∑ α ∈ P.support, ‖Complex.ofRealHom (P.coeff α) * ∏ j : V, z j ^ α j‖ := norm_sum_le ..
    𝖦 := by
      apply Finset.sum_le_sum
      intro α hα
      rw [norm_mul, norm_prod]
      change ‖(P.coeff α : ℂ)‖ * ∏ j : V, ‖z j ^ α j‖ ≤ _
      rw [Complex.norm_real]
      apply mul_le_mul_of_nonneg_left _ $ norm_nonneg _
      apply Finset.prod_le_prod₀ fun j hj => norm_nonneg _
      intro j hj
      rw [norm_pow]
      bound

end PolynomialBounds

𝗇 𝔞 Sum.inl $ Sum.inr ⟨0, 𝘈₁⟩
𝗇 𝔨 Sum.inl $ Sum.inl 𝘈₁
section CoordinateOperators
𝛐

𝗇 𝔘 incrementVariables r → ℂ
𝗇 𝖁 𝔘 →ₗ[ℂ] 𝔊
def currentCoordinateMatrix : 𝖁 where
  toFun z i j := z 𝔨
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def parentCoordinateMatrix : 𝖁 where
  toFun z i j := z 𝔞
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

𝗇 𝖂 𝔘 →L[ℂ] 𝔊
def currentCoordinateCLM : 𝖂 :=
  (currentCoordinateMatrix r).toContinuousLinearMap

def parentCoordinateCLM : 𝖂 :=
  (parentCoordinateMatrix r).toContinuousLinearMap

theorem coordinate_parent_valuation (z : 𝔘) :
    z ∘ Sum.inl = complexParentValuation r (currentCoordinateCLM r z) (parentCoordinateCLM r z) := by
  funext v
  cases v with
  | inl ij => rfl
  | inr t =>
    rcases t with ⟨t, ij⟩
    have ht : t = 0 := Subsingleton.elim ..
    subst t
    rfl

end CoordinateOperators

section UniformNeighborhood
𝛐

end UniformNeighborhood

section ActualDerivatives
𝛐

𝗇 𝔜 𝖄 ℝ
/-- The paper's free moment polynomial after the canonical finite coordinate enumeration. -/
def incrementFinPolynomial (lo hi : ℝ) (T : 𝔜)
    (y : ℝ) (m : ℕ) (i : Fin r) :
    MvPolynomial 𝚕 ℝ :=
  MvPolynomial.rename (Fintype.equivFin $ incrementVariables r )
    $ incrementEntryPolynomial r lo hi T y m i

def currentRealCoordinateMatrix (u : incrementVariables r → ℝ) : 𝔜 :=
  fun i j => u 𝔨

def parentRealCoordinateMatrix (u : incrementVariables r → ℝ) : 𝔜 :=
  fun i j => u 𝔞
