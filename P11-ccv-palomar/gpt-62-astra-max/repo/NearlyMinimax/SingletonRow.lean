module

public import NearlyMinimax.FinePairRowMass
public import NearlyMinimax.FinePairMatrixPositivity
public import NearlyMinimax.FinePairMatrixCost


@[expose] public section

/-! The source singleton ordinary row with its genuine one-point spatial
representation and finite density/response atoms. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section
variable (d k D q : ℕ) (a b C : ℝ)

abbrev SingletonRowMark := Unit × HighPacketMarkIndex (HighFrameIndex d D) D 1 D q

def singletonRowMass : ℝ :=
  highPacketMarkMass (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)

def singletonRowData :
    HighUnionRowData d k D Unit (fun _ => SingletonRowMark d D q) where
  rowLaw := fun _ => highPacketAbsoluteLaw (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
  rowMass := fun _ => singletonRowMass d D q a b C
  rowActivation := fun _ => highPacketActivation (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
  rowIntercept := fun _ => highPacketIntercept a b D 1 D q
  rowSlope := fun _ _ e _ => highPacketSlope a b (fun _ _ => 1) e
  rowVector := fun _ e => (highResponseMarkAtom C e.2.2).2
  rowTime := fun _ e => (highResponseMarkAtom 0 e.2.2).1

end

variable (d k D q : ℕ) (hq : 1 ≤ q) (hD : 1 ≤ D) {a b : ℝ} (ha : 0 < a) (hab : a < b) {C : ℝ}
    (hC : 0 < C)
include ha hab

include hq hC in
theorem singletonRowMass_positive :
    0 < singletonRowMass d D q a b C := by
  rw [singletonRowMass, highPacketMarkMass_eq_variation a b D 1 D q C
      (A := (fun _ => finePairUnitMatrix d D)) (fun _ _ => measurable_const) (integrable_const _),
    highPacketSignedMeasure_totalVariation a b D 1 D q C
      (A := (fun _ => finePairUnitMatrix d D)) (fun _ _ => measurable_const) (integrable_const _)]
  simp
  rw [densityPacketWeight_variation a b ha hab D 1 D (by norm_num)]
  have hp : densityPacketPrefactor a b 1 ≠ 0 := by
    simp only [densityPacketPrefactor, Nat.factorial_one, Nat.cast_one, one_pow, one_div, inv_one, pow_one, one_mul]
    exact div_ne_zero (ha.trans hab).ne' (densityMargin_zero_ne a b ha hab)
  have hn : 0 < (derivativeOrder D : ℝ) := by
    bound
  have hr  :=
    lt_of_lt_of_le zero_lt_one (response_absolute_cost_ge_one hq)
  have hA := finePairUnitMatrix_l1_pos d D
  exact mul_pos (mul_pos (mul_pos
    (by positivity) hr)
      (by positivity)) hA

include hD in
theorem singletonRowMass_exponential_bound (C : ℝ) :
    singletonRowMass d D q a b C ≤
      (Real.exp (1+intervalExteriorTau a b) * |b/densityMargin a b 0|) * D *
      Real.exp ((D : ℝ)*intervalExteriorTau a b) *
      responseVariation q * (2*C^2) := by
  rw [singletonRowMass, highPacketMarkMass_eq_variation a b D 1 D q C
    (A := (fun _ => finePairUnitMatrix d D)) (fun _ _ => measurable_const) (integrable_const _)]
  have h := highPacketSignedMeasure_exponential_cost (σ := (Measure.dirac ())) (a := a) (b := b) ha hab D 1 D q
    (by norm_num) hD C (A := (fun _ => finePairUnitMatrix d D)) (fun _ _ => measurable_const) (integrable_const _)
  simp at h
  apply h.trans
  have hA  := finePairUnitMatrix_l1_le d D
  exact (mul_le_mul_of_nonneg_left hA (by positivity)).trans_eq (mul_one _)

end NearlyMinimax
