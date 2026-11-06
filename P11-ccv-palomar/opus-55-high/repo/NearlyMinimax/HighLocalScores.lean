module

public import NearlyMinimax.HighResponseRemainder
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual finite density-marked response updates and their local scores.
All likelihood and score bounds are proved from legal density/response
factors and the finite atomic rules. -/
open MeasureTheory Set Polynomial
𝚨
𝚩
𝛈

section Packet
𝛢

𝗇 𝔄 𝙛
/-- Density marks are kept separate from the response covariance marks. -/
def highDensityResponseAction (q : ℕ) (C : ℝ) (weights : 𝙏)
    (A : E → ι → 𝔄) (c : 𝔄) (b : 𝙏)
    (Φ : 𝔄 → ℝ) : ℝ :=
  ∑ e, weights e * b e * 𝗔 (A e) c Φ

𝗇 𝔇 𝙔
𝗇 𝔍 𝙈
𝗇 𝔎 𝖨 φ c y
𝗇 𝔏 Fin n → 𝔄
omit [DecidableEq ι] in
theorem high_response_product_normalized (a V η : ℝ) (ha : 𝙞)
    (g w : 𝔇) (φ : 𝔏) (c : 𝔄) :
    ∑ y : 𝔍, 𝔎 = 1 := by
  unfold highResponseProduct
  rw [← Fintype.prod_sum]
  simp [ternary_normalized a _ V ha]

𝗇 𝔅 𝗡 φ c
𝗇 𝔉 𝖷 φ c y i
omit [DecidableEq ι] in
theorem high_response_variance_term_sum_zero (a V η : ℝ)
    (g w : 𝔇) (φ : 𝔏) (c : 𝔄) (i : Fin n) :
    ∑ y : 𝔍, 𝔉 = 0 := by
  simpa only [highResponseVarianceTerm, patchVarianceTerm, zero_mul, add_zero] using
    patch_variance_term_sum_zero n a V 0 𝔅 𝖾 0 i

/-- The explicit finite covariance-mark variation entering the response
packet; it is determined by the actual matrices and density weights. -/
def highResponsePacketCost (C : ℝ) (weights : 𝙏) (A : E → ι → 𝔄) : ℝ :=
  ∑ e, |weights e| * (𝘖 * ∑ k, ∑ l, |A e k l|)

𝗇 𝔐 𝗅
def highLocalDerivativeConstant (q : ℕ) (a ρ : ℝ) : ℝ :=
  (∑ j : Fin 𝖵, |responseWeight q j|) *
    (4 * ((𝗠 / 𝔐) ^ 2 + 2 / 𝔐))

theorem finite_density_product_abs_bound (p : 𝔇) pPlus
    (_hpPlus : 𝗊₂) (hp : ∀ i, |p i| ≤ pPlus) :
    |𝗊| ≤ pPlus ^ n := by
  rw [Finset.abs_prod]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod₀ (fun i _ => abs_nonneg $ p i )
       fun i (_ : i ∈ Finset.univ) => hp i

𝗇 𝔊 ternaryMass a (𝔅 l) V $ y l
omit [DecidableEq ι] in
theorem high_response_variance_term_abs_bound (a V η : ℝ) (ha : 𝙆)
    (g w : 𝔇) (φ : 𝔏) (c : 𝔄)
    (hp : ∀ i u, 0 ≤ ternaryMass a (𝔅 i) V u)
    (y : 𝔍) (i : Fin n) :
    |𝔉| ≤ 1 / 𝔐 := by
  have hprod : |∏ l ∈ (Finset.univ : 𝙍).erase i,
      𝔊| ≤ 1 := by
    rw [Finset.abs_prod]
    apply (Finset.prod_le_prod₀ (fun l _ => abs_nonneg _)
       fun l _ => show |𝔊| ≤ 1 from by
        rw [abs_of_nonneg $ hp l $ y l ]
        exact ternary_mass_le_one a _ V ha.ne' (hp l) $ y l ).trans_eq
    exact Finset.prod_const_one
  unfold highResponseVarianceTerm
  rw [abs_mul]
  exact (mul_le_mul (ternary_variance_derivative_abs_bound a ha $ y i ) hprod
    (abs_nonneg _) (by positivity : 0 ≤ 1 / 𝔐)).trans_eq $ mul_one _

𝗇 𝔈 highLocalDerivativeConstant q a ρ * 𝚍 * 𝙎
theorem high_density_response_product_abs_bound q (hn : 𝗚)
    C a V η ρ pPlus (hC : 𝙴) (ha : 𝙆) (hη : 𝗼)
    (hρ : 𝗛₁) (hηρ : η ≤ 𝙸) (hpPlus : 𝗊₂)
    weights A (pReset : E → 𝔇)
    (g w : 𝔇) φ c
    (hc : ∑ k, |c k| ≤ 𝗳) (hg : ∀ i, |g i| ≤ 𝙸) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝔄, ∑ k, |v k| ≤ 𝗳 → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝘃)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) y :
    |highDensityResponseAction q C weights A c (fun e => ∏ i, pReset e i)
      (fun c => 𝔎)| ≤
      pPlus ^ n * highResponsePacketCost C weights A *
        𝔈 := by
  apply 𝘡
  calc
    _ ≤ ∑ e, |weights e| * pPlus ^ n *
        ((𝘖 * ∑ k, ∑ l, |A e k l|) *
          𝔈) := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul, abs_mul]
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left
          (finite_density_product_abs_bound (pReset e) pPlus hpPlus $ hReset e ) $ abs_nonneg _ )
        _ (abs_nonneg _) 𝖠₃
      exact (high_response_matrix_all_count_bound q hn C a V η ρ hC ha hη hρ hηρ
        (A e) g w φ c y hc hg hw hφ hp).trans_eq $ by
          unfold highLocalDerivativeConstant
          ring
    𝘿 := by
      unfold highResponsePacketCost
      rw [Finset.mul_sum, Finset.sum_mul]
      grind
