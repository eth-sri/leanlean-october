module

public import NearlyMinimax.HighSeparatedScoreBounds
public import NearlyMinimax.CardinalSeparatedKernel
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The singleton ordinary row, instantiated with the genuine positive
separated representation of the spatial cardinal covariance. -/
𝚫
𝚪
𝚨
𝚭
𝚩
𝚬

𝗇 𝔈 cardinalSeparatedFactor lam ζ l $ U i
def highCardinalDensityReset (ad bd lam : ℝ)
    (U : 𝙇) (p : 𝙔)
    (ζ : CardinalSeparatedMark d n) (z : ℝ) (ε : 𝙔) (i : Fin n) : ℝ :=
  localDensityReset ad bd n z ε p (fun i l => 𝔈) i

𝗇 𝔄 fun ζ i l => 𝔈
𝗇 𝔅 𝚠₂
theorem cardinalSeparatedSubsetMatrix_univ lam (hlam : 𝖺)
    (hT : 𝖹) (U : 𝙇) (hU : ∀ i l, |𝚅| ≤ 2) :
    separatedSubsetMatrix 𝔅 n
      𝔄
      (cardinalSeparatedAmplitude (D := F) lam) Finset.univ =
        𝖯₁ := by
  funext β β'
  unfold separatedSubsetMatrix
  simp_rw [cardinal_density_separated_sym_eq]
  exact (integrated_cardinal_symmetric_separated_exact lam hlam hT U hU β β').symm

𝗇 𝔇 (Finset.univ : 𝙍)
/-- Exact selector for the genuine cardinal ordinary packet at its selected
count. Both the density selector and the matrix representation are evaluated. -/
theorem high_cardinal_packet_action_exact
    ad bd lam (ha : 𝖼) (hab : 𝖽) (hlam : 𝖺)
    (hT : 𝖹) m D q (hn : 𝗚) (hnm : n ≤ m) (hnD : 𝖠₁)
    C U (hU : ∀ i l, |𝚅| ≤ 2)
    p (c : 𝖲) Φ :
    highSeparatedPacketAction 𝔅 ad bd m n D q C
      (cardinalSeparatedAmplitude lam) c
      (fun ζ z ε => ∏ i, highCardinalDensityReset ad bd lam U p ζ z ε i) Φ =
        𝗊 * 𝗔 𝖯₁ c Φ := by
  have h := highSeparatedPacketAction_count_selector 𝔅 ad bd ha hab
    m n D q hn (hn.trans hnD) Finset.univ (by simpa using hnD)
    (by simpa using hnm)  𝖢₄  p
    𝔄
    (fun i l => cardinal_separated_factor_measurable lam l $ U i )
    (fun ζ i l => cardinal_separated_factor_abs_le_one lam ζ l (U i) $ hU i ) C
    (cardinalSeparatedAmplitude lam) (cardinal_separated_amplitude_measurable lam)
    (cardinal_separated_cost_integrable lam hT) c Φ
  simp only [highCardinalDensityReset] at ⊢
  rw [h]
  have hpow : (𝔇).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self 𝔇
  simp only [Finset.card_univ, Fintype.card_fin, ite_true, hpow,
    Finset.sum_singleton, cardinalSeparatedSubsetMatrix_univ lam hlam hT U hU]
