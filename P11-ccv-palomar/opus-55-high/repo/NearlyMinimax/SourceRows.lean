module

public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.SingletonRow
public import NearlyMinimax.FinePairRowNondegenerate
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The complete finite source row family: singleton, three genuine pair
rows, and all selected ordinary higher-target coarse/fine bands. -/
𝚫
𝚪
𝚨
𝚩
𝚾

𝗇 𝔉 𝙭₁
𝗃 𝔎 fun _ => ἀ i
def highUnionRowRestrict {d k D : ℕ} {I : Type*} {E : 𝗀} [𝙪]
    (R : 𝔉 I E) (i : I) : 𝔉 Unit 𝔎 E where
  rowLaw := 𝔎 R.rowLaw
  rowMass := 𝔎 R.rowMass
  rowActivation := 𝔎 R.rowActivation
  rowIntercept := 𝔎 R.rowIntercept
  rowSlope := fun j _ => R.rowSlope j i
  rowVector := 𝔎 R.rowVector
  rowTime := 𝔎 R.rowTime

𝗃 𝔏 ἀ d D M q
𝗃 𝔍 𝔏 ἀ a b C lam ℓ N μ
abbrev SourceRowIndex (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :=
  FinePairRowTag ⊕ Unit ⊕ 𝔍 HigherBandFamilyIndex

𝗇 𝔅 𝔍 SourceRowIndex
def SourceRowMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    𝔅 → Type
  | .inl p => 𝔏 FinePairRowMark p
  | .inr $ .inl _ => SingletonRowMark d D q
  | 𝗱₁ => 𝔍 HigherBandFamilyMark i

𝗇 𝔇 𝔍 SourceRowMark
instance sourceRowMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : 𝔅) : MeasurableSpace $ 𝔇 i := by
  cases i with
  | inl p => exact 𝔏 finePairRowMark_measurable p
  | inr i => cases i <;> dsimp [SourceRowMark] <;> infer_instance

instance sourceRowMark_standardBorel (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : 𝔅) : StandardBorelSpace $ 𝔇 i := by
  cases i with
  | inl p => exact 𝔏 finePairRowMark_standardBorel p
  | inr i => cases i <;> dsimp [SourceRowMark] <;> infer_instance

𝗃 𝔊 ἀ d k D M q a b C lam ℓ N μ
def sourceRowComponent (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : 𝔅) →
      𝔉 Unit 𝔎 𝔇
  | .inl p => highUnionRowRestrict (finePairRowData d k D M q a b C ℓ N) p
  | .inr $ .inl _ => singletonRowData d k D q a b C
  | 𝗱₁ => 𝔊 higherBandFamilyComponent i

𝗇 𝔄 𝔊 sourceRowComponent i
def sourceRowData (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    𝔉 𝔅
      𝔇 where
  rowLaw := fun i => (𝔄).rowLaw ()
  rowMass := fun i => (𝔄).rowMass ()
  rowActivation := fun i => (𝔄).rowActivation ()
  rowIntercept := fun i => (𝔄).rowIntercept ()
  rowSlope := fun j i => (𝔄).rowSlope j ()
  rowVector := fun i => (𝔄).rowVector ()
  rowTime := fun i => (𝔄).rowTime ()

𝗇 𝔈 (𝔊 sourceRowData).rowMass
theorem sourceRowMass_nonneg d k D M q a b C lam ℓ N μ
    i :
    0 ≤ 𝔈 i := by
  cases i with
  | inl p => exact 𝔏 finePairRowMass_nonneg a b C ℓ N p
  | inr i =>
    cases i with
    | inl _ => exact signedMarkMass_nonneg ..
    | inr i => exact (𝔊 higherBandFamily_mass_positive i).le

theorem sourceRowTotalMass_positive d k D M q (hq : 𝗘)
    a b (ha : 𝙆) (hab : 𝙭) C (hC : 𝙴) lam ℓ N μ :
    0 < highRowTotalMass 𝔈 := by
  apply (𝘇₂ C hC).trans_le
  exact Finset.single_le_sum (fun i _ => 𝔊 sourceRowMass_nonneg i)
    $ Finset.mem_univ $ Sum.inr $ Sum.inl ()
