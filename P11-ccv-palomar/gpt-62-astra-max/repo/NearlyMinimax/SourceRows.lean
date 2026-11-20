module

public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.SingletonRow
public import NearlyMinimax.FinePairRowNondegenerate

@[expose] public section

/-! The complete finite source row family: singleton, three genuine pair
rows, and all selected ordinary higher-target coarse/fine bands. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

def highUnionRowRestrict {d k D : ℕ} {I : Type*} {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    (R : HighUnionRowData d k D I E) (i : I) : HighUnionRowData d k D Unit (fun _ => E i) where
  rowLaw := fun _ => R.rowLaw i
  rowMass := fun _ => R.rowMass i
  rowActivation := fun _ => R.rowActivation i
  rowIntercept := fun _ => R.rowIntercept i
  rowSlope := fun j _ => R.rowSlope j i
  rowVector := fun _ => R.rowVector i
  rowTime := fun _ => R.rowTime i

variable (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)

abbrev SourceRowIndex :=
  FinePairRowTag ⊕ (Unit ⊕ HigherBandFamilyIndex d D M q a b C lam ℓ N μ)

def SourceRowMark :
    SourceRowIndex d D M q a b C lam ℓ N μ → Type
  | .inl p => FinePairRowMark d D M q p
  | .inr (.inl _) => SingletonRowMark d D q
  | .inr (.inr i) => HigherBandFamilyMark d D M q a b C lam ℓ N μ i

instance sourceRowMark_measurable
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) : MeasurableSpace (SourceRowMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => exact finePairRowMark_measurable d D M q p
  | inr i => cases i <;> dsimp [SourceRowMark] <;> infer_instance

instance sourceRowMark_standardBorel
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) : StandardBorelSpace (SourceRowMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => exact finePairRowMark_standardBorel d D M q p
  | inr i => cases i <;> dsimp [SourceRowMark, sourceRowMark_measurable] <;> infer_instance

def sourceRowComponent {d : ℕ} (k : ℕ) {D M q : ℕ} {a b C lam ℓ N μ : ℝ} :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      HighUnionRowData d k D Unit (fun _ => SourceRowMark d D M q a b C lam ℓ N μ i)
  | .inl p => highUnionRowRestrict (finePairRowData d k D M q a b C ℓ N) p
  | .inr (.inl _) => singletonRowData d k D q a b C
  | .inr (.inr i) => higherBandFamilyComponent k i

def sourceRowData :
    HighUnionRowData d k D (SourceRowIndex d D M q a b C lam ℓ N μ)
      (SourceRowMark d D M q a b C lam ℓ N μ) :=
  .ofRows (sourceRowComponent k)

theorem sourceRowMass_nonneg {a b C lam ℓ N μ : ℝ}
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    0 ≤ (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i := by
  cases i with
  | inl p => apply finePairRowMass_nonneg
  | inr i =>
    cases i with
    | inl _ => exact signedMarkMass_nonneg _ _
    | inr i => exact (higherBandFamily_mass_positive d k D M q i).le

theorem sourceRowTotalMass_positive (hq : 1 ≤ q)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {C : ℝ} (hC : 0 < C) (lam ℓ N μ : ℝ) :
    0 < highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass := by
  apply (singletonRowMass_positive d D q hq ha hab hC).trans_le
  exact Finset.single_le_sum (fun i _ => sourceRowMass_nonneg d k D M q i)
    (Finset.mem_univ (Sum.inr (Sum.inl ())))

end NearlyMinimax
