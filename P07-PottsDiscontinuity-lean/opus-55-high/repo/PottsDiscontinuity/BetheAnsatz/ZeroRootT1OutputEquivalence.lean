module

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
@[ext]
theorem T1PairIndex.ext {i j : T1PairIndex n l} (hσ : i.σ = j.σ) (hw : i.w = j.w)
    (hedge : i.edge = j.edge) : i = j := by
  cases i with
  | mk σ w edge hσ₀ hleft₀ hright₀ hunique₀ =>
    cases j with
    | mk σ' w' edge' hσ₁ hleft₁ hright₁ hunique₁ =>
      simp
      exact ⟨hσ, hw, hedge⟩

@[ext]
theorem T1OutputIndex.ext {i j : T1OutputIndex n l} (hσ : i.σ = j.σ) (hedge : i.edge = j.edge) : i = j := by
  cases i with
  | mk σ edge hleft₀ =>
    cases j with
    | mk σ' edge' hleft₁ =>
      simp
      exact ⟨hσ, hedge⟩

theorem t1PairOutputIndex_end (i : T1PairIndex n l) :
    (t1PairOutputIndex i).σ.symm l = t1PairRunEnd i := by
  have hroot : (t1PairOutputIndex i).σ (t1PairRunEnd i) = l := by
    simpa [t1PairOutputIndex] using t1PairZipperRun_root i
  grind

theorem t1PairOutputPath_eq_inputPath (i : T1PairIndex n l) :
    t1OutputPath (t1PairOutputIndex i) = t1PairZipperPath i := by
  unfold t1OutputPath t1PairZipperPath t1ShiftedRunEnd t1RunShift
    t1OutputCoordinate t1OutputShift
  rw [t1PairOutputIndex_end]
  rfl

theorem t1OutputWord_pairOutput_eq (i : T1PairIndex n l) (k : Fin (n + 1)) :
    t1OutputWord (t1PairOutputIndex i) k = i.w k := by
  let o := t1PairOutputIndex i
  let s := t1RunShift i
  let q := s.symm k
  have hiff : t1OutputWord o k = true ↔ i.w k = true := by
    unfold t1OutputWord
    simp
    rw [(t1PairOutputIndex_end i)]
    change q ≤ s.symm (t1PairRunEnd i) ↔ i.w k = true
    have h := (t1ShiftedWord_true_iff_le_end i q).symm
    grind [t1ShiftedWord, t1RunShift]
  grind

theorem t1OutputInput_pairOutput_sigma (i : T1PairIndex n l) :
    (t1OutputInput (t1PairOutputIndex i)).σ = i.σ := by
  let path := t1PairZipperPath i
  have hpath : t1OutputPath (t1PairOutputIndex i) = path :=
    t1PairOutputPath_eq_inputPath i
  change (zeroRootZipperRun path (i.σ, i.w)).1 *
      (zeroRootZipperPerm (t1OutputPath (t1PairOutputIndex i)))⁻¹ = i.σ
  rw [hpath, zeroRootZipperRun_perm]
  group

theorem t1OutputInput_pairOutput_eq (i : T1PairIndex n l) : t1OutputInput (t1PairOutputIndex i) = i := by
  apply T1PairIndex.ext
  · exact t1OutputInput_pairOutput_sigma i
  · funext k
    exact t1OutputWord_pairOutput_eq i k
  rfl

theorem t1PairOutputIndex_outputInput_eq (o : T1OutputIndex n l) : t1PairOutputIndex (t1OutputInput o) = o := by
  apply T1OutputIndex.ext
  · exact t1OutputInput_outputPerm o
  rfl

noncomputable def t1PairOutputEquiv  :
    T1PairIndex n l ≃ T1OutputIndex n l := by
  classical
  exact Equiv.ofBijective t1PairOutputIndex ⟨
    (fun i j hij => by
      grind [t1OutputInput, t1OutputInput_pairOutput_eq]),
    (fun o => ⟨t1OutputInput o, t1PairOutputIndex_outputInput_eq o⟩)⟩
end

end PottsDiscontinuity.BetheAnsatz
