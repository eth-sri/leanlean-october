module

public import OAI.NumberTheory.DirichletL.Descent.Decomposition
public import OAI.NumberTheory.DirichletL.Descent.Hybrid

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section


def supportedHybridRow (S : Finset (Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O)) (Pset : Finset (Ideal ActualEisensteinCubic.O))
    (a : Ideal ActualEisensteinCubic.O → ℂ) (beta : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ) (k : Ideal ActualEisensteinCubic.O)  :=
  ∑ p ∈ S, ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta p.1 p.2 *
    (quadraticRow k (primaryGenerator (p.1 * p.2)) * inverseCubicKernel P p.1 *
      (if IsCoprime P p.2 then 1 else 0) * (if IsCoprime k P then 1 else 0))

theorem supportedHybridRow_product  nset bset Pset 
     a   beta   k  :
    supportedHybridRow (nset ×ˢ bset) Pset a beta k = hybridRow Pset nset bset a beta k := by
  simp only [supportedHybridRow, hybridRow, hybridInner, Finset.sum_product,
    Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext n
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

def reconstructedHybridTerm (a : Ideal ActualEisensteinCubic.O → ℂ)
    (beta : Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ) (k : Ideal ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O)
    (d : HybridColumnData)  :=
  a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) *
    ((if IsCoprime k d.square then 1 else 0) *
      (if IsCoprime k (P * d.common) then 1 else 0) *
      quadraticRow k (primaryGenerator (d.residualN * d.residualB)) *
      inverseCubicKernel P (d.common * d.residualN) *
      (if IsCoprime P (d.residualB * d.square) then 1 else 0))

theorem supportedHybridRow_reconstruct
     S   Pset 
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ 0 ∧
      primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0)
     a   beta 
     k  (hk : Admissible k) :
    supportedHybridRow S Pset a beta k =
      ∑ d ∈ hybridColumnSupport S, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d := by
  unfold supportedHybridRow
  rw [hybrid_finite_column_reindex S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdS := (mem_hybridColumnSupport S d).mp hd
  have hdprim := hS d.reconstruct hdS
  have hct := (d.primary_factors hdprim.2.2.1 hdprim.2.2.2).2.2.2.2
  apply Finset.sum_congr rfl
  intro P hPP
  unfold reconstructedHybridTerm
  exact congrArg
    (fun z : ℂ => a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
      beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) * z)
    (hybrid_original_kernel_decomposition k P
    (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2)
    d.common d.residualN d.residualB d.square hk (hP P hPP) hdprim.2.2.1 rfl rfl hct)

end
end SevenEighths.InverseMoment

end OAI
