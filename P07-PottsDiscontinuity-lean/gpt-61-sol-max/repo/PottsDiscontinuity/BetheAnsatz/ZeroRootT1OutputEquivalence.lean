module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1OutputInverse

/-!
# The T₁ output-index equivalence

The zipper sends a canonical pair to an output permutation whose zero slot is
the unique LM endpoint. Conversely, the output interval determines the input
word and the inverse accumulated permutation.
-/

@[expose] public section

namespace PottsDiscontinuity.BetheAnsatz

section

variable {n : ℕ} {l : Fin (n + 1)}
include l

@[ext]
theorem T1PairIndex.ext 
    {i j : T1PairIndex n l} (hσ : i.σ = j.σ) (hw : i.w = j.w)
    (hedge : i.edge = j.edge) : i = j := by
  cases i with
  | mk σ w edge hσ₀ hleft₀ hright₀ hunique₀ =>
    simp_all

@[ext]
theorem T1OutputIndex.ext 
    {i j : T1OutputIndex n l} (hσ : i.σ = j.σ) (hedge : i.edge = j.edge) : i = j := by
  cases i with
  | mk σ edge hleft₀ =>
    simp_all

section

variable (i : T1PairIndex n l)


theorem t1PairOutputIndex_end 
     :
    (t1PairOutputIndex i).σ.symm l = t1PairRunEnd i := Equiv.injective (t1PairOutputIndex i).σ
                                                         (Trans.trans (Equiv.apply_symm_apply (t1PairOutputIndex i).σ l) (Eq.symm (t1PairZipperRun_root i)))

theorem t1PairOutputPath_eq_inputPath 
     :
    t1OutputPath (t1PairOutputIndex i) = t1PairZipperPath i := by
  unfold t1OutputPath t1PairZipperPath t1ShiftedRunEnd t1RunShift
    t1OutputCoordinate t1OutputShift
  rw [t1PairOutputIndex_end]
  rfl

theorem t1OutputWord_pairOutput_eq 
     (k : Fin (n + 1)) :
    t1OutputWord (t1PairOutputIndex i) k = i.w k := by
  let o := t1PairOutputIndex i
  let s := t1RunShift i
  let q := s.symm k
  
  have hiff : t1OutputWord o k = true ↔ i.w k = true := by
    unfold t1OutputWord
    simp only [decide_eq_true_eq]
    rw [ t1PairOutputIndex_end i ]
    change q ≤ s.symm (t1PairRunEnd i) ↔ i.w k = true
    
    simpa [t1ShiftedWord, q, s] using  (t1ShiftedWord_true_iff_le_end i q).symm 
  cases hout : t1OutputWord o k <;> cases hword : i.w k <;> simp_all

theorem t1OutputInput_pairOutput_sigma 
     :
    (t1OutputInput (t1PairOutputIndex i)).σ = i.σ := by
  let path := t1PairZipperPath i
  have hpath : t1OutputPath (t1PairOutputIndex i) = path :=
    t1PairOutputPath_eq_inputPath i
  change (zeroRootZipperRun path (i.σ, i.w)).1 *
      (zeroRootZipperPerm (t1OutputPath (t1PairOutputIndex i)))⁻¹ = i.σ
  rw [hpath, zeroRootZipperRun_perm]
  group

theorem t1OutputInput_pairOutput_eq 
     : t1OutputInput (t1PairOutputIndex i) = i := by
  apply T1PairIndex.ext
  · exact t1OutputInput_pairOutput_sigma i
  · funext k
    exact t1OutputWord_pairOutput_eq i k
  · rfl

end

theorem t1PairOutputIndex_outputInput_eq 
    (o : T1OutputIndex n l) : t1PairOutputIndex (t1OutputInput o) = o := by
  apply T1OutputIndex.ext
  · exact t1OutputInput_outputPerm o
  · rfl

end

noncomputable def t1PairOutputEquiv {n : ℕ} {l : Fin (n + 1)} :
    T1PairIndex n l ≃ T1OutputIndex n l := by
  classical
  exact Equiv.ofBijective t1PairOutputIndex ⟨
     fun i j hij => by
      grind [t1OutputInput_pairOutput_eq] ,
     fun o => ⟨t1OutputInput o, t1PairOutputIndex_outputInput_eq o⟩ ⟩

end PottsDiscontinuity.BetheAnsatz
