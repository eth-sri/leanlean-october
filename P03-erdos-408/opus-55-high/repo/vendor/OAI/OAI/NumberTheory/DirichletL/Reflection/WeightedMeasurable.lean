module

public import OAI.NumberTheory.DirichletL.Reflection.WeightedSourceSum
public import OAI.NumberTheory.DirichletL.Descent.CommonMeasure

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open MeasureTheory ActualEisensteinCubic CubicEisenstein InverseMoment
noncomputable section
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : ActualEisensteinCubic.O} {mode : Bool}

lemma weightedReflectedBranchHybridRow_aestronglyMeasurable
    (μ : Measure Ω) (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal ActualEisensteinCubic.O → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ)
    (r aw : Ω → Ideal ActualEisensteinCubic.O → ℂ) (w : Ω → Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (Pset nset bset : Finset (Ideal ActualEisensteinCubic.O)) (K : Ideal ActualEisensteinCubic.O)
    (hr : AEStronglyMeasurable (fun t => r t K) μ)
    (ha : ∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ)
    (hw : ∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) :
    AEStronglyMeasurable (fun t => weightedReflectedBranchHybridRow F jF e S s κ A
      (r t) (aw t) (w t) u m Pset nset bset K) μ := by
  unfold weightedReflectedBranchHybridRow
  apply (hr.const_mul _).mul
  unfold hybridRow
  apply Finset.aestronglyMeasurable_fun_sum
  intro P hP
  simp only [div_eq_mul_inv]
  apply (((ha P hP).const_mul _).mul_const _ |>.mul_const _).mul
  unfold hybridInner
  apply Finset.aestronglyMeasurable_fun_sum
  intro n hn
  apply Finset.aestronglyMeasurable_fun_sum
  intro b hb
  unfold frozenBranchColumn
  exact (((((hw n hn b hb).const_mul _).mul_const _).mul_const _).mul_const _).mul_const _

end
end SevenEighths.InverseReflectedPhase

end OAI
