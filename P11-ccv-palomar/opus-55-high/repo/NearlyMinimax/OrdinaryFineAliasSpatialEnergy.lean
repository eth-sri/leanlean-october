module

public import NearlyMinimax.HighCardinalSpatialEnergy
public import NearlyMinimax.LowerAliasScale
public import NearlyMinimax.HigherBandActivityConversion
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Full-product spatial energy for the actual all-count ordinary fine-band
alias expression. All bounds are uniform in the tuple-dependent nuisance
values; the spatial kernel is the constructed cardinal band. -/
𝛅
𝚶
𝚨
𝚩
𝚭
𝚬

𝗇 𝔑 ∏ i ∈ S, p i
𝗇 𝔖 𝖹₂
𝗇 𝔙 𝙬
𝗇 𝔚 𝙔
𝗇 𝔦 𝙇
𝗇 𝔧 globalCardinalBandMatrix lam L T 𝔖
𝗃 𝔲 ἀ ad bd
/-- The exact raw target-r ordinary fine-band expression produced by the
finite density selector and finite response matrix action. -/
def ordinaryFineAliasRawAction (ad bd lam L T : ℝ) (M r q : ℕ)
    (C a V η : ℝ) (U : 𝔦) (p g w : 𝔚)
    (c : 𝖲) (y : 𝙈) : ℝ :=
  𝔲 densityCountCoefficient M r n *
    ∑ S ∈ (Finset.univ : 𝙍).powersetCard r,
      𝔑 * 𝗔
        𝔧 c
         fun v => 𝖨 𝔙 v y

𝗇 𝔮 bd-ad
𝗇 𝔄 exteriorTau $ (ad+bd)/𝔮
𝗇 𝔊 (M+r : ℕ)
𝗇 𝔏 𝔮/4
𝗇 𝔗 𝔲 densityMargin 0
𝗇 𝔯 n-r
𝗇 𝔘 bd^𝔯
𝗇 𝔟 𝔊*𝔄
𝗇 𝔠 M * 𝔄
𝗇 𝔫 bd^r
𝗃 𝔵 0 ≤ ἀ
/-- Genuine uniform selector-product bound at every count. -/
theorem ordinary_count_product_abs_bound ad bd
    (ha : 𝖼) (hab : 𝖽) M r (hr : 𝘗)
    (p : 𝔚) (hp : ∀ i, p i ∈ 𝔲 Icc)
    S (hS : S.card = r) :
    |𝔲 densityCountCoefficient M r n * 𝔑| ≤
      𝖿₂ * 𝔲 ordinaryDensityActivityBase^r *
        Real.exp 𝔠 := by
  have hbd := ha.trans hab
  have hcard : r ≤ n := by simpa only [hS, Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S
  have hm := abs_pos.mpr $ 𝔲 densityMargin_zero_ne ha hab
  have hτ : 𝔵 𝔄 := by
    rw [𝔲 exteriorTau_sqrt_ratio ha hab]
    exact (densityIntervalExponent_pos ha hab).le
  have hprod : |𝔑| ≤ 𝔫 := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ i ∈ S, bd := Finset.prod_le_prod₀ 𝖢 fun i _ => by
        grind
      𝘿 := 𝖤₄
  have hcoeff := 𝔲 densityCountCoefficient_abs_bound ha hab M r n hr
  have hcosh : Real.cosh 𝔟 ≤
      Real.exp 𝔟 := by
    rw [Real.cosh_eq]
    have he := Real.exp_le_exp.mpr $ show -𝔟 ≤
      𝔟 by
        nlinarith
    linarith
  have he : Real.exp 𝔄 ≤
      Real.exp (1+𝔄) := Real.exp_le_exp.mpr 𝖡₄
  have hb : 𝔏/|𝔗| * Real.exp 𝔄 ≤
      𝔲 ordinaryDensityActivityBase := by
    unfold ordinaryDensityActivityBase
    rw [abs_div, abs_of_pos hbd]
    exact (mul_le_mul (div_le_div_of_nonneg_right  𝖡₄  hm.le) he
      𝙫 $ div_nonneg hbd.le hm.le ).trans_eq 𝖢₃
  have h1 := mul_le_mul hcoeff hprod (abs_nonneg _) $ by positivity
  have h2 := mul_le_mul_of_nonneg_left hcosh
    $ show 0 ≤ 𝔘*𝔏^r/|𝔗|^r *𝔫 by positivity
  have hid : 𝔘*𝔏^r/|𝔗|^r *𝔫 *
      Real.exp 𝔟 =
      𝖿₂ * ( 𝔏/|𝔗| *Real.exp 𝔄)^r *
        Real.exp 𝔠 := by
    have heq : Real.exp 𝔟 =
        Real.exp 𝔠 *
           Real.exp 𝔄 ^r := by
      rw [Nat.cast_add, add_mul, Real.exp_add]
      congr 1
      simpa only [mul_comm] using Real.exp_nat_mul 𝔄 r
    rw [heq]
    generalize 𝔏 = J
    generalize |𝔗| = H
    generalize Real.exp 𝔄 = X
    generalize Real.exp 𝔠 = Y
    rw [mul_pow, div_pow]
    have hpw : 𝔘*𝔫 = 𝖿₂ := by rw [← pow_add, Nat.sub_add_cancel hcard]
    grind
  have h3 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀  𝖠₃  hb r) $ pow_nonneg hbd.le n )
    (Real.exp_pos 𝔠).le
  grind

𝗃 𝔴 (ἀ : ℝ)
𝗇 𝔅 𝔴 M⁻¹
𝗇 𝔇 (1+𝔲 uniformOrdinaryDensityActivityBase c0)^R
𝗇 𝔰 1+bd
𝗇 𝔈 𝔰^n
𝗇 𝔐 𝔲 shrunkDensityExponent M
𝗇 𝔜 ad+𝔅
𝗇 𝔞 bd-𝔅
𝗇 𝔤 Real.exp $ M*𝔐
𝗃 𝔷 ἀ 𝔜 𝔞
𝗇 𝔨 ∀ i, p i ∈ 𝔷 Icc
𝗇 𝔬 𝔈 * 𝔇 * 𝔤
/-- Fixed constants bound every actual shrinking interval and every bounded
fine target, before the exterior degree or sample size is chosen. -/
theorem ordinary_count_product_shrunk_abs_bound {n M r R : ℕ}
    ad bd c0 (ha : 𝖼)
    (hshrink : 𝔜 < 𝔞)
    (htau : 𝔐 ≤ c0) (hr : 𝘗) (hrR : r ≤ R)
    (p : 𝔚) (hp : 𝔨)
    S (hS : S.card = r) :
    |𝔷 densityCountCoefficient M r n * 𝔑| ≤
      𝔬 := by
  have ht : 𝔵 𝔅 := inv_nonneg.mpr $ Nat.cast_nonneg _
  have hap : 0 < 𝔜 := 𝖡₄
  have hbp := hap.trans hshrink
  have he : exteriorTau ((𝔜+𝔞)/
      (𝔞-𝔜)) = 𝔐 := by
    rw [exteriorTau_sqrt_ratio _ _ hap hshrink]
    rfl
  have hb := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have hBr : 𝔷 ordinaryDensityActivityBase^r ≤
      𝔇 := by
    have hbase : 0 ≤ 𝔷 ordinaryDensityActivityBase := by
      unfold ordinaryDensityActivityBase
      positivity
    exact (pow_le_pow_left₀ hbase (hb.trans 𝖡₄ ) r).trans
      $ pow_le_pow_right₀  𝖡₄  hrR
  have h := 𝔷 ordinary_count_product_abs_bound
    hap hshrink M r hr p hp S hS
  rw [he] at h
  exact h.trans $ mul_le_mul_of_nonneg_right
    (mul_le_mul (pow_le_pow_left₀ hbp.le  𝖡₄  n) hBr
      (pow_nonneg (by unfold ordinaryDensityActivityBase; positivity) r)
      $ pow_nonneg  𝖡₄  n ) 𝙫

𝗃 𝔳 ἀ^2
def ordinaryAliasResponseConstant (q : ℕ) (C a ρ : ℝ) : ℝ :=
   2*𝔳 C * (∑ j : Fin 𝖵, |responseWeight q j|) * highSeparatedDerivativeBudget a ρ

𝗇 𝔓 ordinaryAliasResponseConstant q C a ρ
𝗃 𝔶 ἀ (D := F)
/-- Uniform pointwise all-count response and selector control. The primitive
nuisance guards hold at this tuple; no norm bound is supplied as a premise. -/
theorem ordinaryFineAliasRawAction_abs_bound_of_chart {d n F M r R : ℕ}
    ad bd c0 lam L T (haD : 𝖼)
    (hshrink : 𝔜 < 𝔞)
    (htau : 𝔐 ≤ c0) (hr : 𝘗) (hrR : r ≤ R)
    q (hn : 𝗚) C a V η ρ (hC : 1 ≤ C) (ha : 𝙆)
    (hη : 𝔵 η) (hρ : 𝔵 ρ) (hηρ : η ≤ 𝙸)
    U (hU : ∀ i l, |𝚅| ≤ 2)
    (p g w : 𝔚)
    (hpD : 𝔨)
    (hg : ∀ i, |g i| ≤ 𝙸) (hw : ∀ i, |w i| ≤ 1)
    (c : 𝖲) (hc : ∑ γ, |c γ| ≤ 𝗳)
    (hp : ∀ f , |f| ≤ ρ → 𝘃) y :
    |𝔷 ordinaryFineAliasRawAction lam L T M r q C a V η U p g w c y| ≤
      𝔬 *
      (𝔓 * 𝔳 n * 𝔳 η) *
        ∑ S ∈ Finset.univ.powersetCard r,
          spatialMatrixL1 (𝔶 globalCardinalBandMatrix lam L T 𝔖) := by
  unfold ordinaryFineAliasRawAction
  rw [Finset.mul_sum]
  apply 𝘡
  have hterm S (hmem : S ∈ Finset.univ.powersetCard r) :=
    𝔲 ordinary_count_product_shrunk_abs_bound c0 haD hshrink htau hr hrR p hpD S $ (fun S hS => (Finset.mem_powersetCard.mp hS).2) S hmem
  have hresponse S := high_response_matrix_all_count_bound q hn C a V η ρ
    (lt_of_lt_of_le zero_lt_one hC) ha hη hρ hηρ
    𝔧
    g w 𝔙 c y hc hg hw
    𝘢 hp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hmem
  have hh := mul_le_mul (hterm S hmem) (hresponse S) (abs_nonneg _)
    $ by
        grind
  simpa only [abs_mul, mul_assoc] using hh.trans_eq $ by
    unfold ordinaryAliasResponseConstant highSeparatedDerivativeBudget spatialMatrixL1
    ring

𝗇 𝔉 d*𝔯
𝗇 𝔥 𝔶 globalCardinalBandMatrix (spatialInterpolationLambda d) L T
𝗇 𝔎 (∑ S ∈ Finset.univ.powersetCard r, spatialMatrixL1 (𝔥 𝖹₂))^2
𝗇 𝔔 n.choose r ^2
𝗇 𝔩 𝖮₁
/-- Exact subset lifting of the constructed fine-band matrix envelope. -/
theorem ordinaryFineAliasKernel_sum_square_integrable_and_le
    (hd : 𝘚) (hr : 𝘠₁) (hL : 𝚛₂) (hT : 𝖹) (hLT : L ≤ T) :
    Integrable (fun U : 𝔦 =>
      𝔎) 𝔩 ∧
     ∫ U : 𝔦,
      𝔎 ∂𝔩 ≤
      𝔔 * 2 ^𝔉 *
        (𝔳 r*𝖥*cardinalBandSquareBudget d r L) := by
  let f := fun (S : 𝙍) (V : Fin S.card → Covariate d) =>
    spatialMatrixL1 $ 𝔥 V
  have hf S : Measurable $ f S := Finset.measurable_sum _ fun γ _ => Finset.measurable_sum _
       fun δ _ => (integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT γ δ).measurable.abs
  have hi S (hS : S ∈ Finset.univ.powersetCard r) :
      Integrable (fun V => f S V^2) $ fullSpatialPatchDesign d S.card :=
    globalCardinalBandMatrix_square_integrable hd  𝖤₄  hL hT hLT
  constructor
  · have h := finite_sum_abs_square_integrable 𝔩
      (Finset.univ.powersetCard r)
      (fun S U => f S 𝔖)
      (fun S _ => (hf S).comp $ spatialSubsetConfiguration_measurable S )
       fun S hS => spatial_subset_square_integrable_enumerated S (f S) $ hi S hS
    simpa only [f, abs_of_nonneg $ spatial_matrix_l1_nonnegative _ ] using h
  · exact spatial_subset_sum_square_integral_le f _ (fun S _ => hf S) hi
       fun S hS => by
        have h := 𝔶 globalCardinalBandMatrix_square_integral_le hd
          (show 2 ≤ S.card by simp_all) hL hT hLT
        grind

𝗇 𝔒 𝙉
𝗇 𝔱 𝔒^d
def ordinaryFineAliasSpatialBudget (d n M r R q : ℕ) (ad bd c0 C a ρ η L : ℝ) : ℝ :=
  ( 𝔈 * 𝔇 *
      Real.exp (𝔴 M*𝔐) *
    (𝔓 * 𝔴 n^2 * 𝔳 η))^2 *
      ((n.choose r : ℝ)^2 * 𝔒^𝔉 *
        (𝔴 r^2*𝔱*cardinalBandSquareBudget d r L))

𝗇 𝔡 64*𝔱*𝔳 𝔰
𝗇 𝔪 𝔳 𝔈 * n^4 * 𝔔
/-- The exact binomial, response-polynomial and unused-coordinate factors
are absorbed into one fixed exponential base. -/
theorem ordinary_alias_count_factors_le {d n r : ℕ} {bd } (hbd : 𝔵 bd) :
    𝔪 * 2 ^𝔉 ≤
      𝔡^n := by
  have hn : n ≤ 𝔒^n := by exact_mod_cast (Nat.lt_two_pow_self ).le
  have hc : n.choose r ≤ 𝔒^n := by exact_mod_cast Nat.choose_le_two_pow n r
  have hn4 : n^4 ≤ (16 : ℝ)^n := by
    convert pow_le_pow_left₀ (Nat.cast_nonneg n) hn 4 using 1 <;> rw [← pow_mul, Nat.mul_comm n 4, pow_mul] <;> norm_num
  have hc2 : 𝔔 ≤ 𝗦^n := by
    convert pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2 using 1 <;> rw [← pow_mul, Nat.mul_comm n 2, pow_mul] <;> norm_num
  have hv : 2^𝔉 ≤ 𝔱^n := by
    rw [← pow_mul]
    bound
  have h := mul_le_mul (mul_le_mul (mul_le_mul (le_refl 𝔳 𝔈) hn4
       𝖠₃  𝖠₃ ) hc2  𝖠₃  𝖠₃ ) hv  𝖠₃  𝖠₃
  apply h.trans_eq
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
  ring

𝗇 𝔭 𝔳 𝔇 * 𝔳 𝔓
def ordinaryAliasSpatialPrefactor (d q R : ℕ) (ad bd c0 C a ρ : ℝ) : ℝ :=
  𝔭 * lowerAliasSpatialA d R

def ordinaryAliasSpatialCountBase (d : ℕ) (bd : ℝ) : ℝ :=
  𝔡

def ordinaryAliasSpatialResponseBase (d : ℕ) (bd : ℝ) : ℝ :=
  3*ordinaryAliasSpatialCountBase d bd

𝗇 𝔛 ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ
theorem ordinaryAliasSpatialPrefactor_nonneg d q R ad bd c0 C a ρ :
    𝔵 𝔛 := mul_nonneg (𝖧₁ $ sq_nonneg _ ) $ lowerAliasSpatialA_nonneg d R

𝗇 𝔍 𝗐
𝗇 𝔢 ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η 𝔍
𝗇 𝔣 Real.exp $ 2*𝔐*M
/-- Genuine cardinal-band integration and elementary count factors give the
source alias scale, with constants fixed before M,n or nuisance values. -/
theorem ordinaryFineAliasSpatialBudget_source_scale_le {d n M r R : ℕ}
    (hd : 𝘚) (hrR : r ≤ R) {ad bd c0 C a ρ η D K N : ℝ}
    (hbd : 𝔵 bd) (hD : 𝔵 D) (hK : 𝔵 K) (hc0 : 𝔵 c0)
    (hDK : 𝚋₁) (hN : 𝘹) (hell : 1 ≤ 𝔍)
    (hH : Real.log 𝘵 ≤ M) q :
    𝔢 ≤
      𝔛 *
        𝗩 * 𝔣 * N^(4-𝔴 d) *
          Real.exp 𝘫₂ * ordinaryAliasSpatialCountBase d bd ^n := by
  have hkernel := cardinalBandSquareBudget_cutoff_le (by omega : 4 ≤ d) hrR
    (Nat.cast_nonneg M) hD hK hc0 hDK hN hell hH
  let P := 𝔭 * 𝗩 * 𝔣
  have hP : 𝔵 P := 𝖠₃
  have he : 𝔳 𝔤 =
      𝔣 := by
    rw [← Real.exp_nat_mul]
    ring
  have hid : 𝔢 =
      P * (𝔪 * 2^𝔉) *
        (𝔳 r*𝗝*cardinalBandSquareBudget d r 𝔍) := by
    unfold ordinaryFineAliasSpatialBudget P
    grind
  rw [hid]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (ordinary_alias_count_factors_le (d := d) (n := n) (r := r) hbd) hP) hkernel (by
      unfold cardinalBandSquareBudget
      have := cardinalBandDimensionConstant_nonneg d
      bound) 𝖠₃
  exact hh.trans_eq $ by unfold P ordinaryAliasSpatialPrefactor ordinaryAliasSpatialCountBase; ring
