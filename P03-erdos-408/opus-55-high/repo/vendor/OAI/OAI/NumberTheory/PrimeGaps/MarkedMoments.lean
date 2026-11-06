module

public import OAI.NumberTheory.PrimeGaps.ProfileSymmetry

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set MeasureTheory








open scoped Convolution Pointwise

noncomputable def fixLastPerm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin 1))).trans finSumFinEquiv)

@[simp] theorem fixLastPerm_castSucc {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    fixLastPerm e i.castSucc=(e i).castSucc := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.castAdd 1 i)))=Fin.castAdd 1 (e i)
  simp

@[simp] theorem fixLastPerm_last {n : ℕ} (e : Equiv.Perm (Fin n)) :
    fixLastPerm e (Fin.last n)=Fin.last n := by
  change finSumFinEquiv ((Equiv.sumCongr e (Equiv.refl (Fin 1)))
    (finSumFinEquiv.symm (Fin.natAdd n (0 : Fin 1))))=Fin.natAdd n (0 : Fin 1)
  simp

@[simp] theorem cumulativeProfile_zero (tau : ℝ) (n : ℕ) :
    cumulativeProfile tau (0 : (Fin n → ℝ) → ℝ)=0 := by
  ext v
  simp [cumulativeProfile,cumulativeExtension,convolution_def]

@[simp] theorem divisorSum_zero (X M : ℕ) {n : ℕ} (b : Fin n → ℕ) :
    divisorSum X (0 : (Fin n → ℝ) → ℝ) M b=0 := by
  simp [divisorSum,divisorCoefficient]

@[simp] theorem unorderedBlock_zero (X h a M n : ℕ) :
    unorderedBlock X h a (0 : (Fin n → ℝ) → ℝ) M=0 := by
  simp [unorderedBlock]

noncomputable def restrictedUnorderedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (B : Finset (Fin h)) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    if S.val⊆B then divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) else 0

@[simp] theorem restrictedUnorderedBlock_zero (X h a M n : ℕ) (B : Finset (Fin h)) :
    restrictedUnorderedBlock X h a (0 : (Fin n → ℝ) → ℝ) B M=0 := by
  simp [restrictedUnorderedBlock]

end LargePrimeGaps

end OAI
