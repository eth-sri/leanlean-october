module
public import OAI.NumberTheory.DirichletL.Descent.SecondModeCanonical
public import OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRows

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic
open MeasureTheory SchwartzMap

open scoped EisensteinEis
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem second_geometric_energy_of_bound (K : ℕ) (labels : Finset (Ideal Eis))
    (rows : Finset Eis) (Γ : Finset OuterTriple) (F G : SecondChild → ℂ)
    (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ γ ∈ Γ,secondLabelEnergy K labels rows F γ ≤ E)
    (hG : ∀ γ ∈ Γ,secondLabelEnergy K labels rows G γ ≤ E) :
    Real.sqrt (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows G γ) ≤
      E * ∑ γ ∈ Γ,tripleDivisorWeight K γ := by
  have hb (P : SecondChild → ℂ) (hP : ∀ γ ∈ Γ,secondLabelEnergy K labels rows P γ ≤ E) :
      (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows P γ) ≤
      E * ∑ γ ∈ Γ,tripleDivisorWeight K γ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP γ hγ) (tripleDivisorWeight_nonneg K γ)
  calc
    _ ≤ Real.sqrt (E*∑ γ ∈ Γ,tripleDivisorWeight K γ) *
        Real.sqrt (E*∑ γ ∈ Γ,tripleDivisorWeight K γ) :=
      mul_le_mul (Real.sqrt_le_sqrt (hb F hF)) (Real.sqrt_le_sqrt (hb G hG))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (mul_nonneg hE (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))





