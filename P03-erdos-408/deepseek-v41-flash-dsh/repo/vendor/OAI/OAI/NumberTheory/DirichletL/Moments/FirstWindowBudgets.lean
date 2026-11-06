module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalAnnularCommonBound

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstWindowBudgets
open CenteredMomentSecondWindowBudget

lemma sqrt_sum_le {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤E i):
    Real.sqrt (∑i∈s,E i)≤∑i∈s,Real.sqrt (E i):=by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have he:0≤E a:=hE a (Finset.mem_insert_self _ _)
    have hs:0≤∑i∈s,E i:=Finset.sum_nonneg (fun i hi=>hE i (Finset.mem_insert_of_mem hi))
    have hadd:Real.sqrt (E a+∑i∈s,E i)≤Real.sqrt (E a)+Real.sqrt (∑i∈s,E i):=by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt he,Real.sq_sqrt hs,
          mul_nonneg (Real.sqrt_nonneg (E a)) (Real.sqrt_nonneg (∑i∈s,E i))]
    exact hadd.trans (add_le_add le_rfl (ih (fun i hi=>hE i (Finset.mem_insert_of_mem hi))))

lemma windowBudget_sum {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤E i)
    (J:ℕ)(t:ℝ):
    windowBudget J t (∑i∈s,E i)≤∑i∈s,windowBudget J t (E i):=by
  unfold windowBudget
  rw [←Finset.sum_mul,←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sqrt_sum_le s E hE) (pow_nonneg (heightEnvelope_pos t).le _))
    (profileMoment_nonneg J)

theorem windowBudget_pair_sum {α β:Type*}(s:Finset α)(u:Finset β)
    (E:α→ℝ)(F:β→ℝ)(hE:∀i∈s,0≤E i)(hF:∀j∈u,0≤F j)
    (J₁ J₂:ℕ)(t:ℝ):
    windowBudget J₁ t (∑i∈s,E i)*windowBudget J₂ t (∑j∈u,F j)≤
      ∑i∈s,∑j∈u,windowBudget J₁ t (E i)*windowBudget J₂ t (F j):=by
  have hh:=mul_le_mul (windowBudget_sum s E hE J₁ t) (windowBudget_sum u F hF J₂ t)
    (windowBudget_nonneg J₂ t _) (Finset.sum_nonneg (fun i _=>windowBudget_nonneg J₁ t (E i)))
  apply hh.trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u

end SevenEighths.CenteredMomentFirstWindowBudgets

end

end OAI
