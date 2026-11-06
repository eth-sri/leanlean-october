module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.ShellSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section

variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : ActualEisensteinCubic.O} {mode : Bool}

def reflectedNDyad (k : ℕ)  :=
  (dualIdealDyad k).filter CubicSieve.Admissible

def reflectedBDyad (j : ℕ)  :=
  (dualIdealDyad j).filter (fun b => primaryGenerator b≠0)

section
variable (j k : ℕ) (A B : Finset (Ideal ActualEisensteinCubic.O)) (f : Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ)


lemma reflectedNDyad_bounds   : ∀ n∈reflectedNDyad k,
    CubicSieve.Admissible n ∧ (2:ℝ)^k/2≤(Ideal.absNorm n:ℝ) ∧ (Ideal.absNorm n:ℝ)≤(2:ℝ)^k := by
  intro n hn
  exact ⟨(Finset.mem_filter.mp hn).2,(dualIdealDyad_bounds k n (Finset.mem_filter.mp hn).1).2⟩

lemma reflectedBDyad_bounds   : ∀ b∈reflectedBDyad j,
    primaryGenerator b≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm b:ℝ) ∧ (Ideal.absNorm b:ℝ)≤(2:ℝ)^j := by
  intro b hb
  exact ⟨(Finset.mem_filter.mp hb).2,(dualIdealDyad_bounds j b (Finset.mem_filter.mp hb).1).2⟩

lemma double_sum_coe     :
    (∑ n : A, ∑ b : B, f n.val b.val)=∑ n∈A, ∑ b∈B, f n b := by
  rw [Finset.sum_coe_sort A (fun n : Ideal ActualEisensteinCubic.O => ∑ b : B, f n b.val)]
  apply Finset.sum_congr rfl
  intro n hn
  exact Finset.sum_coe_sort B (f n)

lemma sum_dual_mask     :
    (∑ n : dualIdealDyad k, ∑ b : dualIdealDyad j,
      if CubicSieve.Admissible n.val ∧ primaryGenerator b.val≠0 then f n.val b.val else 0)=
      ∑ n : reflectedNDyad k, ∑ b : reflectedBDyad j, f n.val b.val := by
  rw [double_sum_coe (dualIdealDyad k) (dualIdealDyad j)
    (fun n b => if CubicSieve.Admissible n ∧ primaryGenerator b≠0 then f n b else 0),
    double_sum_coe (reflectedNDyad k) (reflectedBDyad j) f]
  simp only [reflectedNDyad,reflectedBDyad,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn' : CubicSieve.Admissible n
  · simp only [hn',true_and,ite_eq_left]
  simp_all

end

theorem literalDyadicBlock_eq_filtered_source  F   K   hK 
     S   jF 
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
     u   i   QK QP  (hQK : 0<QK) (hQP : 0<QP)
    (hKr : QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK)
    (hPr : QP/2≤(Ideal.absNorm (∏ i,S.ideal i):ℝ) ∧ (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP)
     W   θ X  :
    literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i=
      ∑ n : reflectedNDyad i.2.2, ∑ b : reflectedBDyad i.2.1,
        actualKernelSourceTerm F K hK S jF D s hc u i.1 n.val b.val
          (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X := by
  rw [literalDyadicBlock_eq_shell_source F K hK S jF D s hc u i QK QP hQK hQP hKr hPr W θ X]
  exact sum_dual_mask i.2.1 i.2.2 (fun n b => actualKernelSourceTerm F K hK S jF D s hc u i.1 n b
    (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ X)
end
end SevenEighths.InverseReflectedPhase

end OAI
