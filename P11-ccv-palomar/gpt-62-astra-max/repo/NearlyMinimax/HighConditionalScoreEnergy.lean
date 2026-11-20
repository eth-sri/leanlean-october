module

public import NearlyMinimax.HighRawScoreEnergy
public import NearlyMinimax.HighMarkedMeasurable

@[expose] public section

/-! Genuine conditional finite-response energies determine square
integrability and Fisher energy in the actual normalized sample kernel.
No joint-score integrability assumption is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def finiteResponseSquareEnergy {α : Type*} [MeasurableSpace α] {n : ℕ}
    (a V : ℝ) (F : α → ℝ) (S : ((Fin n → α) × (TernaryVector n)) → ℝ)
    (x : Fin n → α) : ℝ :=
  ∑ y, (∏ i, ternaryMass a (F (x i)) V (y i)) * (S (x, y)) ^ 2

theorem response_sample_square_integrable_integral {α : Type*} [MeasurableSpace α]
    {n : ℕ} {μ : Measure (Fin n → α)} [SFinite μ] {a V : ℝ} (ha : a ≠ 0)
    {F : α → ℝ} (hF : Measurable F) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    {S : ((Fin n → α) × (TernaryVector n)) → ℝ} (hS : Measurable S)
    (hE : Integrable (finiteResponseSquareEnergy a V F S) μ) :
    let prod := μ.compProd (responseSampleIndexKernel n a V hF)
    Integrable (fun z => S z ^ 2) (prod) ∧
    (∫ z, S z ^ 2 ∂prod) =
      ∫ x, finiteResponseSquareEnergy a V F S x ∂μ := by
  intro prod
  let _ := responseSampleIndexKernel_markov n hF ha hq
  have he x : (∫ y, ‖S (x, y) ^ 2‖ ∂responseSampleIndexKernel n a V hF x) =
      finiteResponseSquareEnergy a V F S x := by
    simp_rw [Real.norm_eq_abs, abs_sq]
    solve_by_elim [responseSampleIndexKernel_integral]
  have hi : Integrable (fun z => S z ^ 2) (prod) := by
    apply (Measure.integrable_compProd_iff (hS.pow_const 2).aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall (fun _ => Integrable.of_finite)
    · simpa only [he] using hE
  refine ⟨hi, ?_⟩
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    responseSampleIndexKernel_integral a V hF x (fun i y => hq (x i) y) _)

end NearlyMinimax
