module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RunPermutation

/-!
# Output indices for the global T₁ reindexing

After zipping, the zero label is at the unique LM endpoint. The original ML
left endpoint is fixed by the accumulated permutation, so it remains a valid
free index distinct from the output zero slot.
-/

@[expose] public noncomputable section

namespace PottsDiscontinuity.BetheAnsatz

/-- An output permutation and the original ML edge's left endpoint. The output
permutation sends its implicit LM endpoint `σ.symm l` to the zero label. -/
structure T1OutputIndex (n : ℕ) (l : Fin (n + 1)) where
  σ : Equiv.Perm (Fin (n + 1))
  edge : Option (Fin n)
  hleft : t1EdgeLeft edge ≠ σ.symm l

instance t1OutputIndexFintype {n : ℕ} {l : Fin (n + 1)} :
    Fintype (T1OutputIndex n l) := by
  classical
  apply Fintype.ofInjective (fun i => (i.σ, i.edge))
  intro i j hij
  cases i with
  | mk σ edge hleft =>
    simp_all

section
variable {n : ℕ} {l : Fin (n + 1)} (i : T1PairIndex n l)
/-- Reindex a canonical T₁ pair by its post-zipper permutation and original
ML edge. -/
def t1PairOutputIndex  : T1OutputIndex n l := by
  let σout := (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1
  have hroot : σout (t1PairRunEnd i) = l := by
    simpa [σout] using t1PairZipperRun_root i
  have hleftEnd : t1EdgeLeft i.edge ≠ t1PairRunEnd i := by
    intro he
    have hfalse := i.hleft
    have htrue := (t1PairRunEnd_spec i).1
    simp_all
  have hpre : σout.symm l = t1PairRunEnd i := by
    grind
  exact ⟨σout, i.edge, by omega⟩

theorem t1PairOutputIndex_left  :
    (t1PairOutputIndex i).σ (t1EdgeLeft i.edge) = i.σ (t1EdgeLeft i.edge) :=
  t1PairZipperRun_left i
end

end PottsDiscontinuity.BetheAnsatz
