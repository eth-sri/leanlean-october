module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RunPermutation

/-!
# Output indices for the global T₁ reindexing

After zipping, the zero label is at the unique LM endpoint. The original ML
left endpoint is fixed by the accumulated permutation, so it remains a valid
free index distinct from the output zero slot.
-/

@[expose] public section

namespace PottsDiscontinuity.BetheAnsatz

/-- An output permutation and the original ML edge's left endpoint. The output
permutation sends its implicit LM endpoint `σ.symm l` to the zero label. -/
structure T1OutputIndex (n : ℕ) (l : Fin (n + 1)) where
  σ : Equiv.Perm (Fin (n + 1))
  edge : Option (Fin n)
  hleft : t1EdgeLeft edge ≠ σ.symm l

noncomputable instance t1OutputIndexFintype {n : ℕ} {l : Fin (n + 1)} :
    Fintype (T1OutputIndex n l) := by
  classical
  apply Fintype.ofInjective  fun i => (i.σ, i.edge) 
  intro i j hij
  cases i with
  | mk σ edge hleft =>
    simp_all

/-- Reindex a canonical T₁ pair by its post-zipper permutation and original
ML edge. -/
noncomputable def t1PairOutputIndex {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) : T1OutputIndex n l := by
  let σout := (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1
  have hroot : σout (t1PairRunEnd i) = l := t1PairZipperRun_root i
  
  have hpre : σout.symm l = t1PairRunEnd i := by
    apply σout.injective
    simp [hroot]
  exact ⟨σout, i.edge, by simpa  using  by
                                                intro he
                                                have hfalse := i.hleft
                                                have htrue := (t1PairRunEnd_spec i).1
                                                all_goals simp_all ⟩

theorem t1PairOutputIndex_left {n : ℕ} {l : Fin (n + 1)}
    (i : T1PairIndex n l) :
    (t1PairOutputIndex i).σ (t1EdgeLeft i.edge) = i.σ (t1EdgeLeft i.edge) := t1PairZipperRun_left i

end PottsDiscontinuity.BetheAnsatz
