module

public import NearlyMinimax.HighDensityUpdates
public import NearlyMinimax.HighResponseUpdates
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The local row identity for arbitrary finite positive separated
representations, derived from the genuine density and response marks. -/
𝚫
𝚮
𝚨
𝚩
𝚭

𝗇 𝔚 𝗔
𝗇 𝔇 𝔚 (A ζ) c Φ
𝗇 𝔉 𝙛
𝗇 𝔎 A ζ i j
𝗇 𝔘 Z → ι → 𝔉
𝗃 𝔜 Integrable (fun ζ => ἀ) σ
𝗇 𝔣 hA i j
𝗃 𝔤 fun i j => ∫ ζ, ἀ ∂σ
section ResponseIntegral
𝛑

/-- Fixed coefficients of the response action as a linear map of A. -/
def responseMatrixEntryCoefficient (q : ℕ) (C : ℝ) (c : 𝔉)
    (Φ : 𝔉 → ℝ) (i j : ι) : ℝ :=
  ∑ s : Bool, ∑ t : Bool, C ^ 2 / 2 * fairSign s * fairSign t *
    ∑ h : Fin 𝖵, 𝘐₁ *
      Φ (coefficientReset c (covarianceAtom C i j s t) $ responseNode q h )

theorem responseMatrixAction_entry_sum q C A
    (c : 𝔉) Φ :
    𝔚 A c Φ =
      ∑ i, ∑ j, 𝘩 * responseMatrixEntryCoefficient q C c Φ i j := by
  simp only [responseMatrixAction, covarianceAction, covarianceWeight,
    responseMatrixEntryCoefficient, Finset.mul_sum]
  ring

theorem responseMatrixAction_scalar_matrix q C t
    A (c : 𝔉) Φ :
    𝔚 (fun i j => t * 𝘩) c Φ =
      t * 𝔚 A c Φ := by
  simp only [responseMatrixAction_entry_sum, Finset.mul_sum, mul_assoc]

variable {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)

section

variable (q)
    (C)
    (A : 𝔘)
    (hA : ∀ i j, 𝔜 𝔎)
    (c)
    (Φ)

include hA

theorem responseMatrixAction_integrable :
    𝔜 𝔇 := by
  simp only [responseMatrixAction_entry_sum]
  fun_prop

𝗇 𝔑 fun j _ => (𝔣).mul_const _
/-- The actual fixed-atom response rule commutes with the positive
representation integral by its proved matrix linearity. -/
theorem responseMatrixAction_integral :
    𝔚 𝔤 𝔎 c Φ =
      ∫ ζ, 𝔇 ∂σ := by
  simp only [responseMatrixAction_entry_sum]
  rw [integral_finset_sum Finset.univ fun i _ => integrable_finset_sum _
    𝔑 ]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum Finset.univ 𝔑]
  simp only [integral_mul_const]

end

end ResponseIntegral

section Separated
variable {Z α : Type*} [MeasurableSpace Z] [DecidableEq α]

𝗇 𝔄 ∀ i l, Measurable fun ζ => B ζ i l
𝗇 𝔐 Z → α → 𝗢
𝗃 𝔦 ἀ r $ B ζ
𝗇 𝔈 𝔦 densitySeparatedSym
𝗇 𝔟 S.card = r
𝗇 𝔠 fun ζ => 𝔈 S
theorem densitySeparatedSym_measurable r (B : 𝔐)
    (hB : 𝔄) S (hS : 𝔟) :
    Measurable 𝔠 := by
  classical
  let e := (Fintype.equivFinOfCardEq $ show Fintype.card S = r by simpa using hS ).symm
  have he : 𝔠 =
       fun ζ => (∑ τ : Equiv.Perm $ Fin r , ∏ i, B ζ (e i) (τ i)) / r.factorial := by
    funext ζ
    exact 𝔦 densitySeparatedSym_eq_permutation_average S e
  rw [he]
  exact (Finset.measurable_fun_sum _ fun τ _ => Finset.measurable_fun_prod _
     fun i _ => hB (e i) $ τ i ).div_const _

𝛑

def separatedMatrixCost (A : 𝔘) (ζ : Z) : ℝ := ∑ i, ∑ j, |𝔎|

theorem separatedMatrixCost_entry_le A (ζ : Z) (i j : ι) :
    |𝔎| ≤ separatedMatrixCost A ζ := by
  apply (Finset.single_le_sum (fun k _ => abs_nonneg $ A ζ i k ) $ Finset.mem_univ j ).trans
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg $ A ζ k l )
    $ Finset.mem_univ i

𝗇 𝔅 𝙚
𝗇 𝔏 𝙧
theorem separatedMatrix_entry_integrable (σ : Measure Z) A
    (hA : 𝔅)
    (hcost : 𝔏) (i j : ι) :
    𝔜 𝔎 := by
  apply hcost.mono' (𝔣).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ζ => by
    simpa only [Real.norm_eq_abs] using separatedMatrixCost_entry_le A ζ i j

𝗇 𝔛 𝔈 S * 𝔎
/-- Actual separated representation of the symmetric matrix kernel on a
cardinality-r observation subset. -/
def separatedSubsetMatrix (σ : Measure Z) (r : ℕ) (B : 𝔐)
    (A : 𝔘) (S : Finset α) : ι → 𝔉 :=
  𝔤 𝔛

𝗇 𝔒 separated_subset_entry_integrable σ r B hB hBbound A hA hcost S hS
𝗇 𝔓 B ζ i l
𝗃 𝔥 𝔚 (separatedSubsetMatrix σ r B A ἀ) c Φ
section

variable (σ : Measure Z)
    (r)

theorem separated_subset_entry_integrable (B : 𝔐) (hB : 𝔄)
    (hBbound : ∀ ζ i l, |𝔓| ≤ 1) A
    (hA : 𝔅)
    (hcost : 𝔏)
    S (hS : 𝔟) (i j : ι) :
    𝔜 𝔛 := by
  apply hcost.mono' ((densitySeparatedSym_measurable r B hB S hS).mul 𝔣).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ζ
  change ‖𝔛‖ ≤ separatedMatrixCost A ζ
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ 1 * |𝔎| := mul_le_mul_of_nonneg_right
      (𝔦 densitySeparatedSym_abs_le_one S hS fun i _ l => hBbound ζ i l ) $ abs_nonneg _
    _ ≤ separatedMatrixCost A ζ := by simpa using separatedMatrixCost_entry_le A ζ i j

theorem separatedSubsetMatrix_response B (hB : 𝔄)
    (hBbound : ∀ ζ i l, |𝔓| ≤ 1) A
    (hA : 𝔅)
    (hcost : 𝔏) (S : Finset α) (hS : 𝔟)
    q C (c : 𝔉) Φ :
    𝔥 S =
      ∫ ζ, 𝔈 S * 𝔇 ∂σ := by
  unfold separatedSubsetMatrix
  rw [responseMatrixAction_integral σ q C _
    𝔒]
  simp only [responseMatrixAction_scalar_matrix]

end

theorem densityDerivativeAction_mul_right r D f t :
    densityDerivativeAction r D (fun ε => f ε * t) = densityDerivativeAction r D f * t := by
  simp only [densityDerivativeAction, Finset.sum_mul, mul_assoc]

𝗇 𝔗 densityPacketAction a b m r D
theorem densityPacketAction_mul_right a b m r D
    f t :
    𝔗 (fun z ε => f z ε * t) = 𝔗 f * t := by
  simp only [densityPacketAction, densityDerivativeAction_mul_right, Finset.sum_mul, mul_assoc]

theorem densityPacketAction_zero a b m r D :
    𝔗 (fun _ _ => 0) = 0 := by
  simp [densityPacketAction, densityDerivativeAction]

/-- The genuine iterated action of the density packet, representation
measure, and finite response covariance rule. -/
def highSeparatedPacketAction (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : 𝔘) (c : 𝔉)
    (G : Z → ℝ → 𝗢 → ℝ) (Φ : 𝔉 → ℝ) : ℝ :=
  ∫ ζ, 𝔗
     fun z ε => G ζ z ε * 𝔇 ∂σ

section

variable (σ : Measure Z)

theorem separated_subset_response_integrable (r : ℕ)
    (B : 𝔐) (hB : 𝔄)
    (hBbound : ∀ ζ i l, |𝔓| ≤ 1) (A : 𝔘)
    (hA : 𝔅)
    (hcost : 𝔏) (S : Finset α) (hS : 𝔟)
    (q : ℕ) (C : ℝ) (c : 𝔉) (Φ : 𝔉 → ℝ) :
    Integrable (fun ζ => 𝔈 S * 𝔇) σ := by
  have h := responseMatrixAction_integrable σ q C
    (fun ζ i j => 𝔛)
    𝔒 c Φ
  simpa only [responseMatrixAction_scalar_matrix] using h

𝗇 𝔙 ∏ i ∈ S, localDensityReset a b r z ε p (B ζ) i
𝗇 𝔊 highSeparatedPacketAction σ a b m r D q C A c (fun ζ z ε => 𝔙) Φ
𝗇 𝔢 ∏ i ∈ U, p i
𝗇 𝔍 ∑ U ∈ S.powersetCard r, 𝔢 * 𝔥 U
𝗇 𝔔 densityCountCoefficient a b m r S.card
𝗇 𝔖 𝔢
𝗃 𝔞 ἀ σ r B hB hBbound A hA hcost U (Finset.mem_powersetCard.mp hU).2 q C c Φ
𝗇 𝔡 𝔖 * (𝔈 U * 𝔇)
/-- The paper's local row formula for arbitrary positive separated
representations. All integrability needed to commute sums and integrals
is derived from the finite representation cost. -/
theorem highSeparatedPacketAction_row a b
    (ha : 𝙆) (hab : 𝙭) m r D q (hr : 𝘗) (hD : 𝗮)
    (S : Finset α) (hSD : S.card ≤ D) p
    B (hB : 𝔄)
    (hBbound : ∀ ζ i l, |𝔓| ≤ 1) C A
    (hA : 𝔅)
    (hcost : 𝔏) (c : 𝔉) Φ :
    𝔊 =
      𝔔 *
        𝔍 := by
  have hInt U (hU : U ∈ S.powersetCard r) :
      Integrable (fun ζ => 𝔡) σ :=
    (𝔞 separated_subset_response_integrable).const_mul _
  have he ζ : 𝔗
      (fun z ε => 𝔙 *
        𝔇) =
      𝔔 *
        ∑ U ∈ S.powersetCard r, 𝔡 := by
    rw [densityPacketAction_mul_right,
      density_packet_product_exact S a b ha hab m r D hr hD hSD p $ B ζ ]
    simp only [Finset.sum_mul, mul_assoc]
  unfold highSeparatedPacketAction
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ hInt]
  apply congrArg fun t => 𝔔 * t
  apply Finset.sum_congr rfl
  intro U hU
  rw [integral_const_mul, ← 𝔞 separatedSubsetMatrix_response]

theorem highSeparatedPacketAction_count_selector a b
    (ha : 𝙆) (hab : 𝙭) m r D q (hr : 𝘗) (hD : 𝗮)
    (S : Finset α) (hSD : S.card ≤ D) (hSm : S.card ≤ m) (hrS : r ≤ S.card) p
    B (hB : 𝔄)
    (hBbound : ∀ ζ i l, |𝔓| ≤ 1) C A
    (hA : 𝔅)
    (hcost : 𝔏) (c : 𝔉) Φ :
    𝔊 =
      if 𝔟 then 𝔍 else 0 := by
  rw [highSeparatedPacketAction_row σ a b ha hab m r D q hr hD S hSD p B hB hBbound C A hA hcost c Φ,
    densityCountCoefficient_exact a b ha hab m r S.card hr hrS hSm]
  simp
