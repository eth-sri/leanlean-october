module

public import NearlyMinimax.AtomicVariation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Complex.Exponential
public import RoughRegime.Macro

𝗌

/-! The genuine finite density-mark operator used by the high-smoothness
lower bound. Tensor derivative marks are proved to extract the square-free
coefficient, and exterior marks produce the count selector. -/
open MeasureTheory Set Polynomial
𝚨

𝗇 𝖊 derivativeOrder D + 1
𝗇 𝔦 Fin 𝖊
𝗇 𝔯 (D - 1) / 2
def densityDerivativeWeight (D : ℕ) (j : 𝔦) : ℝ :=
  lobattoDerivativeWeight 𝔯 j

𝗇 𝕷 fun _ => 1
/-- The exponent selected by one first-derivative mark in every coordinate. -/
def densityUnitExponent (r : ℕ) : Fin r →₀ ℕ :=
  Finsupp.onFinset Finset.univ 𝕷 $ by simp

@[simp] theorem densityUnitExponent_apply r i :
    densityUnitExponent r i = 1 := by rfl

@[simp] theorem densityUnitExponent_degree r :
    (densityUnitExponent r).degree = r := by
  simp [Finsupp.degree_eq_sum]

𝗇 𝔉 Fin r → Fin 𝖊
𝗇 𝔏 Fin r → ℝ
𝗃 𝖔 densityDerivativeWeight D $ ἀ l
𝗇 𝔑 ∏ l, 𝖔 h
𝗇 𝔷 lobattoNode $ derivativeOrder D
𝗃 𝖕 fun l => 𝔷 $ ἀ l
/-- Actual product of the finite Chebyshev derivative marks. -/
def densityDerivativeAction (r D : ℕ) (f : 𝔏 → ℝ) : ℝ :=
  ∑ h : 𝔉,
    𝔑 *
      f 𝖕 h

𝗇 𝔡 1 ≤ D
𝗇 𝕽 densityDerivativeWeight D j
𝗇 𝕾 ℝ[X]
theorem derivative_rule_monomial D (hD : 𝔡) k (hk : k ≤ D) :
     ∑ j : 𝔦,
      𝕽 *
        𝔷 j ^ k = if k = 1 then 1 else 0 := by
  have hp : (X ^ k : 𝕾).degree ≤ D := by
    simpa
  simpa [densityDerivativeWeight, ← coeff_zero_eq_eval_zero, coeff_derivative,
    coeff_X_pow, eq_comm] using derivative_rule_exact D hD (X ^ k) hp

𝗇 𝔛 if d = densityUnitExponent r then 1 else 0
𝗇 𝕿 ∀ l, d l ≤ D
𝗇 𝖀 densityDerivativeAction r D
theorem densityDerivativeAction_monomial r D (hD : 𝔡)
    d (hd : 𝕿) :
    𝖀 (fun ε => ∏ l, ε l ^ d l) =
      𝔛 := by
  unfold densityDerivativeAction
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum fun l j =>
    𝕽 * 𝔷 j ^ d l ]
  simp_rw [derivative_rule_monomial D hD _ $ hd _ ]
  by_cases he : d = densityUnitExponent r
  · subst d
    simp
  · rw [if_neg he]
    obtain ⟨l, hl⟩ : ∃ l, d l ≠ 1 := by
      by_contra hn
      apply he
      ext l
      simp_all
    apply Finset.prod_eq_zero $ Finset.mem_univ l
    simpa

𝗇 𝔒 ∏ l, lobattoNode (derivativeOrder D) (h l) ^ d l
𝗇 𝔜 _ = _
𝗇 𝕯 ∑ h : 𝔉, 𝔑 * 𝔒
𝗃 𝖖 fun ε => MvPolynomial.eval ε ἀ
/-- Tensor exactness follows from the proved one-variable moments, without
an assumed mixed-derivative or interpolation identity. -/
theorem densityDerivativeAction_polynomial r D (hD : 𝔡)
    P
    (hP : ∀ d ∈ P.support, 𝕿) :
    𝖀 𝖖 P =
      P.coeff (densityUnitExponent r) := by
  unfold densityDerivativeAction
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm d :
       ∑ h : 𝔉,
        𝔑 *
          (P.coeff d * 𝔒) =
        P.coeff d *
          𝕯 := by
    rw [Finset.mul_sum]
    grind
  simp_rw [hm]
  have he d hd :
      𝕯 =
        𝔛 :=
    densityDerivativeAction_monomial r D hD d $ hP d hd
  calc
    _ = ∑ d ∈ P.support, P.coeff d * 𝔛 := by
      apply Finset.sum_congr rfl
      simp_all
    𝔜 := by
      simp_all

𝗇 𝔧 B i l
𝗇 𝕳 ι → 𝔏
/-- Each mark acts on one affine density factor. -/
def densityModulationPolynomial (r : ℕ) (B : 𝕳)
    (i : ι) : MvPolynomial (Fin r) ℝ :=
  ∑ l, MvPolynomial.C 𝔧 * MvPolynomial.X l

𝗇 𝖌 densityModulationPolynomial r B
𝗇 𝔞 𝖌 i
theorem densityModulationPolynomial_homogeneous r
    B (i : ι) :
    (𝔞).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro l _
  exact MvPolynomial.isHomogeneous_C_mul_X ..

𝗇 𝔖 t * p i
/-- The product of the incoming densities after their affine mark reset. -/
def densityResetPolynomial [DecidableEq ι] (S : Finset ι)
    (r : ℕ) (z t : ℝ) (p : ι → ℝ) (B : 𝕳) : MvPolynomial (Fin r) ℝ :=
  ∏ i ∈ S, (MvPolynomial.C z + MvPolynomial.C 𝔖 *
    𝔞)

𝗇 𝔇 (∏ i ∈ U, 𝖌 i).coeff $ densityUnitExponent r
𝗇 𝔈 ∏ i ∈ U, p i
𝗇 𝔍 ∑ l, ε l * B i l
𝗃 𝖏 ἀ S r z t p B
𝗇 𝔓 𝖏 densityResetPolynomial
𝗇 𝖍 S.card - r
𝗃 𝖗 ἀ ^ r
𝗇 𝔘 z ^ 𝖍 * 𝖗 t
𝗇 𝔴 ∑ U ∈ S.powersetCard r, 𝔈 * 𝔇
𝗇 𝔵 ∏ i ∈ S, (z + 𝔖 * 𝔍)
𝗃 𝕱 (ἀ ..).trans
section

variable [DecidableEq ι]
    (S : Finset ι)

theorem densityResetPolynomial_eval r z t p B ε :
    MvPolynomial.eval ε 𝔓 =
      𝔵 := by
  simp only [densityResetPolynomial, map_prod, map_add, map_mul,
    MvPolynomial.eval_C, densityModulationPolynomial, map_sum, MvPolynomial.eval_X]
  grind

theorem densityResetPolynomial_totalDegree r z t p B :
    (𝔓).totalDegree ≤ S.card := by
  apply 𝕱 MvPolynomial.totalDegree_finsetProd
  calc
    _ ≤ ∑ _i ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply 𝕱 MvPolynomial.totalDegree_add
      apply max_le
      · simp
      · have h := (densityModulationPolynomial_homogeneous r B i).C_mul 𝔖
        exact h.totalDegree_le
    𝔜 := by simp

𝗇 𝔭 z ^ (S \ U).card * t ^ U.card
/-- Exactly one occurrence of every mark selects only observation subsets
of cardinality r. -/
theorem densityResetPolynomial_coefficient r z t p B :
    (𝔓).coeff (densityUnitExponent r) =
      𝔘 *
        𝔴 := by
  classical
  unfold densityResetPolynomial
  simp_rw [add_comm $ MvPolynomial.C z ]
  rw [Finset.prod_add]
  simp only [MvPolynomial.coeff_sum]
  have he U (hU : U ∈ S.powerset) :
      ((∏ i ∈ U, MvPolynomial.C 𝔖 * 𝔞) *
        ∏ i ∈ S \ U, MvPolynomial.C z).coeff (densityUnitExponent r) =
      𝔭 * 𝔈 *
        𝔇 := by
    rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod,
      mul_comm _ $ MvPolynomial.C _ , mul_assoc, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C_mul]
    simp only [Finset.prod_const, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl he]
  have hz U (hU : U ∈ S.powerset) :
      𝔭 * 𝔈 *
        𝔇 =
      if U.card = r then
        𝔘 * (𝔈 *
          𝔇)
      else 0 := by
    by_cases hc : U.card = r
    · grind
    · have hh := MvPolynomial.IsHomogeneous.prod U
         𝖌 𝕷
         fun i _ => densityModulationPolynomial_homogeneous r B i
      have hzero := hh.coeff_eq_zero (d := densityUnitExponent r) $ by aesop
      simp_all
  rw [Finset.sum_congr rfl hz]
  rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter, ← Finset.mul_sum]

end

𝗇 𝕸 fun ε => 𝔵
𝗇 𝖁 S.card ≤ D
theorem density_derivative_product_exact [DecidableEq ι]
    S r D (hD : 𝔡) (hSD : 𝖁)
    z t (p : ι → ℝ) B :
    𝖀 𝕸 =
      𝔘 *
        𝔴 := by
  have hf : 𝕸 =
      𝖖 𝔓 := by
    funext ε
    exact (𝖏 densityResetPolynomial_eval ε).symm
  rw [hf]
  rw [densityDerivativeAction_polynomial r D hD]
  · exact 𝖏 densityResetPolynomial_coefficient
  · intro d hd l
    exact (MvPolynomial.le_degreeOf_of_mem_support l hd).trans
      $ 𝕱 MvPolynomial.degreeOf_le_totalDegree
        $ (𝖏 densityResetPolynomial_totalDegree).trans hSD

𝗇 𝖈 b - a
𝗇 𝔟 𝖈
/-- The quadratic density-interval margin in the manuscript. -/
def densityMargin (a b z : ℝ) : ℝ := (z - a) * (b - z) / 𝔟

𝗃 𝕰 ἀ a b
𝗇 𝔐 𝕰 densityMargin z
𝗇 𝔔 a < b
𝗇 𝔰 𝕰 Icc
𝗇 𝕴 (div_le_iff₀ hba).mpr
𝗇 𝖎 a + b
theorem densityMargin_bounds a b (hab : 𝔔) z (hz : z ∈ 𝔰) :
    0 ≤ 𝔐 ∧ 𝔐 ≤ z - a ∧
      𝔐 ≤ b - z ∧ 𝔐 ≤ 𝔟 / 4 := by
  have hba := sub_pos.mpr hab
  have hn := sub_nonneg.mpr hz.1
  have hm := sub_nonneg.mpr hz.2
  refine ⟨div_nonneg (mul_nonneg hn hm) hba.le, ?_, ?_, ?_⟩
  · apply 𝕴
    nlinarith
  · apply 𝕴
    nlinarith
  · apply 𝕴
    nlinarith [sq_nonneg $ z - 𝖎 / 2 ]

𝗇 𝔗 𝕰 densityMargin 0
𝗇 𝔙 0 < a
theorem densityMargin_zero_ne a b (ha : 𝔙) (hab : 𝔔) :
    𝔗 ≠ 0 := div_ne_zero (mul_ne_zero (by simpa using ha.ne') $ by linarith )
    (sub_pos.mpr hab).ne'

def densityMarginPolynomial (a b : ℝ) : 𝕾 :=
  (X - C a) * (C b - X) * C 𝔟 ⁻¹

@[simp] theorem densityMarginPolynomial_eval a b z :
    (𝕰 densityMarginPolynomial).eval z = 𝔐 := by
  simp [densityMarginPolynomial, densityMargin, div_eq_mul_inv]

theorem densityMarginPolynomial_natDegree a b :
    (𝕰 densityMarginPolynomial).natDegree ≤ 2 := by
  apply natDegree_mul_le.trans
  have h₁ : (X - C a).natDegree ≤ 1 :=
    𝕱 natDegree_sub_le $ by simp
  have h₂ : (C b - X).natDegree ≤ 1 :=
    𝕱 natDegree_sub_le $ by simp
  simpa using (natDegree_mul_le ).trans $ add_le_add h₁ h₂

𝗇 𝔚 k - r
def densityCountPolynomial (a b : ℝ) (k r : ℕ) : 𝕾 :=
  X ^ 𝔚 * 𝕰 densityMarginPolynomial ^ r

𝗇 𝔣 𝕰 densityCountPolynomial k r
@[simp] theorem densityCountPolynomial_eval a b z k r :
    (𝔣).eval z = z ^ 𝔚 * 𝖗 𝔐 := by
  simp [densityCountPolynomial]

theorem densityCountPolynomial_natDegree a b k r (hrk : r ≤ k) :
    (𝔣).natDegree ≤ k + r := by
  apply natDegree_mul_le.trans
  have hp := (natDegree_pow_le ).trans
    $ Nat.mul_le_mul_left r 𝕰 densityMarginPolynomial_natDegree
  simp only [natDegree_X_pow]
  omega

𝗇 𝔅 m + r
𝗇 𝖉 𝕰 exteriorNode 𝔅 j
𝗇 𝔲 𝖉 ^ 𝔚 * 𝕰 densityMargin 𝖉 ^ r
𝗇 𝔳 Fin $ 𝔅 + 1
𝗇 𝔶 𝕰 exteriorWeight 𝔅 j
𝗇 𝕲 ∑ j : 𝔳, 𝔶 * 𝔲
/-- The actual exterior count factor, including counts above the cutoff. -/
def densityCountCoefficient (a b : ℝ) (m r k : ℕ) : ℝ :=
  𝕲 / 𝖗 𝔗

𝗇 𝔠 1 ≤ r
𝗇 𝖂 𝕰 densityCountCoefficient m r
𝗃 𝖐 𝕰 ἀ ha hab
/-- Exact target-count selection is derived from the concrete exterior
rule: every other count through m is annihilated. -/
theorem densityCountCoefficient_exact a b (ha : 𝔙) (hab : 𝔔)
    m r k (hr : 𝔠) (hrk : r ≤ k) (hkm : k ≤ m) :
    𝖂 k = if k = r then 1 else 0 := by
  have hdeg : (𝔣).degree ≤ 𝔅 :=
    degree_le_natDegree.trans $ by
      exact_mod_cast (𝕰 densityCountPolynomial_natDegree k r hrk).trans $ Nat.add_le_add_right hkm r
  have he := 𝕰 exterior_rule_exact hab 𝔅 (by omega)
    𝔣 hdeg
  simp at he
  unfold densityCountCoefficient
  rw [he]
  by_cases hkr : k = r
  · subst k
    simp [pow_ne_zero r 𝖐 densityMargin_zero_ne]
  · have hpos : 𝔚 ≠ 0 := by omega
    simp_all

𝗇 𝔄 exteriorTau $ 𝖎 / 𝖈
𝗇 𝔊 b ^ (k - r) * (𝖈 / 4) ^ r
𝗇 𝔱 (𝔅 : ℕ) * 𝔄
𝗇 𝖃 𝖐 exterior_rule_variation
/-- Uniform finite-variation control for the count factor beyond the cutoff. -/
theorem densityCountCoefficient_abs_bound a b (ha : 𝔙) (hab : 𝔔)
    m r k (hr : 𝔠) :
    |𝖂 k| ≤
       𝔊 / |𝔗| ^ r *
        Real.cosh 𝔱 := by
  have hb : ∀ j ,
      |𝔲| ≤
      𝔊 := by
    intro j
    have hz := 𝕰 exteriorNode_mem hab.le 𝔅 j
    have ht := 𝕰 densityMargin_bounds hab _ hz
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg $ ha.le.trans hz.1 , abs_of_nonneg ht.1]
    bound
  have hs : |𝕲| ≤
      Real.cosh 𝔱 *
        𝔊 := by
    calc
      _ ≤ ∑ j : 𝔳, |𝔶| *
          𝔊 := by
        apply 𝕱 Finset.abs_sum_le_sum_abs
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        bound
      𝔜 := by rw [← Finset.sum_mul, 𝖃 _ $ by omega ]
  unfold densityCountCoefficient
  rw [abs_div, abs_pow]
  exact (div_le_div_of_nonneg_right hs $ by positivity ).trans_eq $ by ring

𝗇 𝔨 (r : ℝ)
/-- The incoming density is reset exactly as in (LB-loc-update). -/
def localDensityReset (a b : ℝ) (r : ℕ) (z : ℝ)
    (ε : 𝔏) (p : ι → ℝ) (B : 𝕳) (i : ι) : ℝ :=
  z + 𝔐 / (𝔨 * b) * p i * 𝔍

𝗇 𝔤 r * b
𝗇 𝕵 _ ≤ ∑ _l : Fin r, 1
𝗇 𝕹 div_nonneg hθ.1 (mul_pos hrR hb).le
𝗇 𝖄 𝔐 / 𝔤
theorem localDensityReset_slope_bound a b (ha : 𝔙) (hab : 𝔔)
    r (hr : 𝔠) z (hz : z ∈ 𝔰)
    (ε : 𝔏) (hε : ∀ l, |ε l| ≤ 1) (B : 𝕳) i
    (hB : ∀ l, |𝔧| ≤ 1) :
    |𝖄 * 𝔍| ≤
      𝔟 / (4 * b) := by
  have hb := ha.trans hab
  have hrR : 0 < 𝔨 := by exact_mod_cast hr
  have hθ := 𝕰 densityMargin_bounds hab z hz
  have hsum : |𝔍| ≤ r := by
    calc
      _ ≤ ∑ l, |ε l * 𝔧| := Finset.abs_sum_le_sum_abs ..
      𝕵 := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        bound
      𝔜 := by simp
  have hcoef :=
    𝕹
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    _ ≤ 𝖄 * r :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = 𝔐 / b := by field_simp
    _ ≤ 𝔟 / 4 / b := div_le_div_of_nonneg_right hθ.2.2.2 hb.le
    𝔜 := by ring

𝗇 𝖋 𝕰 localDensityReset r z ε p B i
theorem localDensityReset_mem_interval a b (ha : 𝔙) (hab : 𝔔)
    r (hr : 𝔠) z (hz : z ∈ 𝔰)
    ε (hε : ∀ l, |ε l| ≤ 1) p
    B (i : ι) (hp : p i ∈ 𝔰) (hB : ∀ l, |𝔧| ≤ 1) :
    𝖋 ∈ 𝔰 := by
  have hb := ha.trans hab
  have hrR : 0 < 𝔨 := by exact_mod_cast hr
  have hθ := 𝕰 densityMargin_bounds hab z hz
  have hp0 := ha.le.trans hp.1
  have hsum : |𝔍| ≤ r := by
    calc
      _ ≤ ∑ l, |ε l * 𝔧| := Finset.abs_sum_le_sum_abs ..
      𝕵 := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        bound
      𝔜 := by simp
  have hcoef :=
    𝕹
  have hshift : |𝖄 * p i * 𝔍| ≤
      𝔐 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hcoef, abs_of_nonneg hp0]
    calc
      _ ≤ 𝖄 * p i * r :=
        mul_le_mul_of_nonneg_left hsum $ mul_nonneg hcoef hp0
      _ = 𝔐 / b * p i := by field_simp
      _ ≤ 𝔐 / b * b :=
        mul_le_mul_of_nonneg_left hp.2 $ div_nonneg hθ.1 hb.le
      𝔜 := div_mul_cancel₀ _ hb.ne'
  obtain ⟨hl, hu⟩ := abs_le.mp hshift
  constructor <;> dsimp [localDensityReset] <;> linarith

𝗇 𝕺 ∏ i ∈ S, 𝔞
/-- Symmetrization is the square-free coefficient divided by r!: it is
independent of any ordering chosen for the observation subset. -/
def densitySeparatedSym [DecidableEq ι] (r : ℕ)
    (B : 𝕳) (S : Finset ι) : ℝ :=
  (𝕺).coeff (densityUnitExponent r) /
    (r.factorial : ℝ)

𝗇 𝕶 b / 𝔗
def densityPacketPrefactor (a b : ℝ) (r : ℕ) : ℝ :=
  𝖗 𝔨 / (r.factorial : ℝ) * 𝖗 𝕶

𝗇 𝔩 𝕰 densityPacketPrefactor r
𝗇 𝕬 𝖉
/-- The exact finite action of Gamma_{r,m}. -/
def densityPacketAction (a b : ℝ) (m r D : ℕ) (f : ℝ → 𝔏 → ℝ) : ℝ :=
  𝔩 * ∑ j : 𝔳,
    𝔶 *
      𝖀 (f 𝕬)

𝗃 𝖑 𝕰 ἀ m r D
𝗇 𝔎 𝖑 densityPacketAction fun z ε => ∏ i ∈ S, 𝖋
𝗇 𝕮 ∑ U ∈ S.powersetCard r, 𝔈 * densitySeparatedSym r B U
theorem density_packet_product_exact [DecidableEq ι]
    (S : Finset ι) a b (ha : 𝔙) (hab : 𝔔)
    m r D (hr : 𝔠) (hD : 𝔡) (hSD : 𝖁)
    p B :
    𝔎 =
      𝖂 S.card *
        𝕮 := by
  have hb := (ha.trans hab).ne'
  unfold densityPacketAction localDensityReset
  simp_rw [density_derivative_product_exact S r D hD hSD]
  unfold densityCountCoefficient densitySeparatedSym
  have hsum : ∑ U ∈ S.powersetCard r, 𝔈 *
      (𝔇 /
        r.factorial) =
      𝔴 /
        r.factorial := by simp_rw [← mul_div_assoc]; rw [Finset.sum_div]
  rw [hsum]
  unfold densityPacketPrefactor
  simp only [div_pow, mul_pow]
  rw [Finset.mul_sum]
  calc
    _ = ∑ j : 𝔳,
       𝔶 *
        (𝕬 ^ 𝖍 *
          𝕰 densityMargin 𝕬 ^ r) / 𝖗 𝔗 *
        (𝔴 /
          r.factorial) := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp
    𝔜 := by simp only [← Finset.sum_mul, Finset.sum_div]

𝗇 𝔢 Fin r → Fin r
𝗇 𝕻 Finsupp.single (f i) 1
private def densityAssignmentExponent (r : ℕ) (f : 𝔢) : Fin r →₀ ℕ :=
  ∑ i, 𝕻

𝗃 𝖓 ἀ $ e i
private theorem densityAssignmentExponent_eq_unit_iff (r : ℕ) (f : 𝔢) :
    densityAssignmentExponent r f = densityUnitExponent r ↔ Function.Bijective f := by
  classical
  constructor
  · intro he
    have hs : Function.Surjective f := by
      intro l
      by_contra hn
      have hne i : f i ≠ l := fun h => hn ⟨i, h⟩
      have hv := congrArg (fun d => d l) he
      simp [densityAssignmentExponent, hne] at hv
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  · intro hf
    let e := Equiv.ofBijective f hf
    change ∑ i, 𝖓 Finsupp.single 1 = densityUnitExponent r
    rw [e.sum_comp fun l => Finsupp.single l 1 ]
    ext l
    simp

𝗇 𝔪 Equiv.Perm $ Fin r
𝗃 𝖘 B i $ ἀ i
𝗇 𝔫 𝖘 f
/-- The selected coefficient is the genuine permanent, hence the sum of
all r! assignments of distinct marks to distinct observations. -/
theorem density_linear_product_permanent r B :
    (∏ i, 𝔞).coeff (densityUnitExponent r) =
      ∑ σ : 𝔪, ∏ i, 𝖘 σ := by
  classical
  unfold densityModulationPolynomial
  rw [Fintype.prod_sum]
  simp_rw [MvPolynomial.C_mul_X_eq_monomial]
  have hm f :
       ∏ i, MvPolynomial.monomial 𝕻 𝔫 =
      MvPolynomial.monomial (densityAssignmentExponent r f) (∏ i, 𝔫) :=
    (MvPolynomial.monomial_sum_prod Finset.univ ..).symm
  simp_rw [hm]
  simp
  simp only [densityAssignmentExponent_eq_unit_iff]
  have hs : (∑ f : 𝔢, if Function.Bijective f then ∏ i, 𝔫 else 0) =
      ∑ f : {f : 𝔢 // Function.Bijective f}, ∏ i, 𝖘 f.1 := by
    apply Finset.sum_congr_set {f : 𝔢 | Function.Bijective f}
    all_goals simp_all
  rw [hs]
  apply Fintype.sum_equiv Equiv.bijectiveEquiv
  intro f
  rfl

𝗇 𝔮 ∏ i, 𝖓 B (σ i)
section

variable [DecidableEq ι]

/-- Coefficient-based symmetrization agrees with the paper's average over
permutations, for every enumeration of a cardinality-r subset. -/
theorem densitySeparatedSym_eq_permutation_average r B (S : Finset ι) (e : Fin r ≃ S) :
    densitySeparatedSym r B S =
      (∑ σ : 𝔪, 𝔮) / r.factorial := by
  unfold densitySeparatedSym
  have he : 𝕺 =
      ∏ i : Fin r, densityModulationPolynomial r (fun i l => 𝖓 B l) i := by
    rw [← Finset.prod_coe_sort]
    exact (e.prod_comp fun i => 𝔞 ).symm
  rw [he, density_linear_product_permanent]

𝗃 𝖒 ἀ S a b ha hab m r D hr hD hSD
𝗇 𝔥 𝖒 density_packet_product_exact p B
theorem density_packet_product_zero_of_small_count
    (S : Finset ι) a b (ha : 𝔙) (hab : 𝔔)
    m r D (hr : 𝔠) (hD : 𝔡) (hSD : 𝖁)
    (hSr : S.card < r) p B :
    𝔎 = 0 := by
  rw [𝔥,
    Finset.powersetCard_eq_empty.mpr hSr]
  simp

/-- The full count selector identity for all counts through m. -/
theorem density_packet_product_count_selector
    (S : Finset ι) a b (ha : 𝔙) (hab : 𝔔)
    m r D (hr : 𝔠) (hD : 𝔡) (hSD : 𝖁)
    (hSm : S.card ≤ m) p B :
    𝔎 =
      if S.card = r then 𝕮 else 0 := by
  by_cases hSr : r ≤ S.card
  · rw [𝔥,
      𝖐 densityCountCoefficient_exact m r S.card hr hSr hSm]
    simp
  · rw [𝖒 density_packet_product_zero_of_small_count (by omega) p B,
      if_neg $ by omega ]

end

def densityPacketAtom (a b : ℝ) (m r D : ℕ)
    (j : 𝔳 × 𝔉) : ℝ × 𝔏 :=
  (𝕰 exteriorNode 𝔅 j.1, 𝖕 j.2)

def densityPacketWeight (a b : ℝ) (m r D : ℕ)
    (j : 𝔳 × 𝔉) : ℝ :=
  𝔩 * 𝕰 exteriorWeight 𝔅 j.1 *
    ∏ l, 𝖔 j.2

𝗇 𝕭 𝖑 densityPacketAtom
𝗇 𝖅 𝖑 densityPacketWeight
/-- Gamma_{r,m} as an actual finite signed measure on density marks. -/
def densityPacketSignedRule (a b : ℝ) (m r D : ℕ) : SignedMeasure $ ℝ × 𝔏 :=
  atomicSignedRule 𝕭 𝖅

𝗇 𝔬 𝖑 densityPacketSignedRule
theorem densityPacketSignedRule_integral a b m r D
    (f : ℝ → 𝔏 → ℝ) :
     ∫ᵛ e, f e.1 e.2 ∂<• 𝔬 =
      𝖑 densityPacketAction f := by
  rw [densityPacketSignedRule, atomicSignedRule_integral]
  simp only [Fintype.sum_prod_type, densityPacketWeight, densityPacketAtom,
    densityPacketAction, densityDerivativeAction]
  simp only [Finset.mul_sum, mul_assoc]

theorem densityPacketAtom_mem a b (hab : a ≤ b) m r D
    j :
    (𝕭 j).1 ∈ 𝔰 ∧
      ∀ l, |(𝕭 j).2 l| ≤ 1 := by
  constructor
  · exact 𝕰 exteriorNode_mem hab 𝔅 j.1
  · intro l
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem densityDerivativeWeight_variation D :
     ∑ j : 𝔦, |𝕽| = derivativeOrder D :=
  lobatto_derivative_rule_variation 𝔯

theorem densityDerivativeWeight_tensor_variation r D :
     ∑ h : 𝔉, ∏ l, |𝖔 h| =
       derivativeOrder D ^ r := by
  rw [← Fintype.prod_sum fun _l j =>
    |𝕽| ]
  simp only [densityDerivativeWeight_variation, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem densityPacketWeight_variation a b (ha : 𝔙) (hab : 𝔔)
    m r D (hr : 𝔠) :
     ∑ j : 𝔳 × 𝔉,
      |𝖅 j| =
      |𝔩| *
        Real.cosh 𝔱 * derivativeOrder D ^ r := by
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, densityDerivativeWeight_tensor_variation]
  rw [← Finset.sum_mul, ← Finset.mul_sum, 𝖃 _ $ by omega ]

𝗇 𝕼 ((𝔬).variation univ).toReal
theorem densityPacketSignedRule_totalVariation_bound a b (ha : 𝔙) (hab : 𝔔)
    m r D (hr : 𝔠) (hD : 𝔡) :
    𝕼 ≤
      |𝔩| *
        Real.cosh 𝔱 * 𝖗 D := by
  apply 𝕱 atomicSignedRule_totalVariation_le
  rw [𝖐 densityPacketWeight_variation m r D hr]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (derivative_rule_variation D hD).2 r)
    $ mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le

/-- The factorial normalization has the required exponential cost. -/
theorem densityPacketPrefactor_abs_le a b r :
    |𝔩| ≤ Real.exp r * |𝕶| ^ r := by
  unfold densityPacketPrefactor
  rw [abs_mul, abs_pow, abs_of_nonneg $ by positivity ]
  exact mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp r (Nat.cast_nonneg r) r)
    $ by positivity

𝗇 𝖆 1 + 𝔄
𝗇 𝖇 m * 𝔄
/-- The actual packet has cost C^r D^r exp(m tau), with an explicit C
depending only on the fixed density interval. -/
theorem densityPacketSignedRule_exponential_cost a b (ha : 𝔙) (hab : 𝔔)
    m r D (hr : 𝔠) (hD : 𝔡) :
    𝕼 ≤
      (Real.exp 𝖆 * |𝕶|) ^ r *
        𝖗 D * Real.exp 𝖇 := by
  have he : Real.cosh 𝔱 ≤
      Real.exp 𝔱 := by
    rw [← 𝖃 𝔅 $ by omega ]
    exact 𝖐 exterior_rule_variation_le_exp 𝔅 $ by omega
  apply (𝖐 densityPacketSignedRule_totalVariation_bound m r D hr hD).trans
  calc
    _ ≤ Real.exp r * |𝕶| ^ r *
        Real.exp 𝔱 * 𝖗 D := by
      apply mul_le_mul_of_nonneg_right _ $ by positivity
      exact mul_le_mul (𝕰 densityPacketPrefactor_abs_le r) he (Real.cosh_pos _).le
        $ mul_nonneg (Real.exp_pos _).le $ by positivity
    𝔜 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have heq : Real.exp r *
          Real.exp (𝔅 * 𝔄) =
          Real.exp (r * 𝖆) *
            Real.exp 𝖇 := by
        rw [← Real.exp_add, ← Real.exp_add]
        grind
      grind

theorem densitySeparatedSym_abs_le_one [DecidableEq ι]
    r B (S : Finset ι) (hS : S.card = r)
    (hB : ∀ i ∈ S, ∀ l, |𝔧| ≤ 1) : |densitySeparatedSym r B S| ≤ 1 := by
  classical
  let e := (Fintype.equivFinOfCardEq $ show Fintype.card S = r by simpa ).symm
  rw [densitySeparatedSym_eq_permutation_average r B S e, abs_div,
    abs_of_pos (by exact_mod_cast r.factorial_pos : (0 : ℝ) < r.factorial)]
  apply (div_le_iff₀ $ by exact_mod_cast r.factorial_pos ).mpr
  calc
    _ ≤ ∑ σ : 𝔪, |𝔮| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _σ : 𝔪, 1 := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => 𝖓 hB (e i).2 $ σ i ).trans_eq
        $ by simp
    𝔜 := by simp [Fintype.card_perm]
