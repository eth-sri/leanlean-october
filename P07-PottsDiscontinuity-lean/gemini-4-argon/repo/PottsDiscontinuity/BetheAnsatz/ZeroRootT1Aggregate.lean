module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1OutputEquivalence
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RegularizedResidue

/-!
# The aggregate T₁ contribution after zipper reindexing

The output index is equivalent to an output permutation together with an
allowed ML-left slot. This exposes the derivative sum over all nonzero root
labels and the single seam indicator.
-/

@[expose] public section

open Finset Complex

namespace PottsDiscontinuity.BetheAnsatz

/-- A cyclic edge's left endpoint, including the seam edge at `Fin.last`. -/
def t1EdgeLeftEquiv {n : ℕ} : Option (Fin n) ≃ Fin (n + 1) where
  toFun := t1EdgeLeft
  invFun m := Fin.lastCases none (fun j => some j) m
  left_inv e := by cases e <;> simp [t1EdgeLeft, Fin.lastCases_last, Fin.lastCases_castSucc]
  right_inv m := Fin.lastCases (by simp [t1EdgeLeft, Fin.lastCases_last])
    (fun _ => by simp [t1EdgeLeft, Fin.lastCases_castSucc]) m

/-- Forget the seam/ordinary presentation and retain the left endpoint slot. -/
noncomputable def t1OutputIndexSigmaEquiv {n : ℕ} {l : Fin (n + 1)} :
    T1OutputIndex n l ≃ Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l} where
  toFun o := ⟨o.σ, ⟨t1EdgeLeftEquiv o.edge, o.hleft⟩⟩
  invFun q := ⟨q.1, t1EdgeLeftEquiv.symm q.2.1, by
    simpa only [show t1EdgeLeft (t1EdgeLeftEquiv.symm q.2.1) = q.2.1 from
      t1EdgeLeftEquiv.apply_symm_apply q.2.1] using q.2.2⟩
  left_inv o := T1OutputIndex.ext rfl (t1EdgeLeftEquiv.symm_apply_apply o.edge)
  right_inv := fun ⟨_, ⟨m, _⟩⟩ => by
    cases m using Fin.lastCases <;> simp [t1EdgeLeftEquiv, t1EdgeLeft]

/-- The corrected phase slope attached to an output permutation and a slot. -/
noncomputable def t1OutputSlope {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (m : Fin (n + 1)) : ℂ :=
  (zeroRootPhaseDerivative (N := N) Δ (p (σ m)) False : ℂ) +
    if m = Fin.last n then (N : ℂ) else 0

/-- The all-M regularized coefficient times the corrected slope. -/
noncomputable def t1OutputLimitTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (o : T1OutputIndex n l) : ℂ :=
  zeroRootRegularizedWordTerm (N := N) c x p l o.σ (fun _ => false) *
    t1OutputSlope (N := N) (anisotropy c) p o.σ (t1EdgeLeft o.edge)

/-- The same limit summand in permutation/left-slot coordinates. -/
noncomputable def t1SigmaLimitTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (q : Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l}) : ℂ :=
  zeroRootRegularizedWordTerm (N := N) c x p l q.1 (fun _ => false) *
    t1OutputSlope (N := N) (anisotropy c) p q.1 q.2.1

theorem t1OutputLimitTerm_sigma {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (q : Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l}) :
    t1OutputLimitTerm (N := N) c x p l (t1OutputIndexSigmaEquiv.symm q) =
      t1SigmaLimitTerm (N := N) c x p l q := by
  unfold t1OutputLimitTerm t1SigmaLimitTerm
  change zeroRootRegularizedWordTerm (N := N) c x p l q.1 (fun _ => false) *
      t1OutputSlope (N := N) (anisotropy c) p q.1
        (t1EdgeLeftEquiv (t1EdgeLeftEquiv.symm q.2.1)) = _
  rw [t1EdgeLeftEquiv.apply_symm_apply]

/-- Output slots other than the zero slot correspond exactly to the nonzero
root labels under an output permutation. -/
noncomputable def t1OutputSlotLabelEquiv {n : ℕ} (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    {m : Fin (n + 1) // m ≠ σ.symm l} ≃ {j : Fin (n + 1) // j ≠ l} where
  toFun m := ⟨σ m.1, fun h => m.2 (σ.injective (h.trans (σ.apply_symm_apply l).symm))⟩
  invFun j := ⟨σ.symm j.1, fun h => j.2 (by simpa using congrArg σ h)⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)

theorem sum_t1OutputDerivative_slots {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      (zeroRootPhaseDerivative (N := N) Δ (p (σ m.1)) False : ℂ)) =
      ∑ j : {j : Fin (n + 1) // j ≠ l},
        (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ) :=
  Equiv.sum_comp (t1OutputSlotLabelEquiv l σ)
    (fun j : {j : Fin (n + 1) // j ≠ l} =>
      (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ))

theorem sum_t1OutputSeam_slots {N n : ℕ} (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      if m.1 = Fin.last n then (N : ℂ) else 0) =
      if σ (Fin.last n) = l then 0 else (N : ℂ) := by
  classical
  by_cases hroot : σ.symm l = Fin.last n
  · rw [ite_eq_left (by rw [← hroot, σ.apply_symm_apply])]
    exact Finset.sum_eq_zero fun m _ => ite_eq_right fun heq => m.2 (heq.trans hroot.symm)
  · let m₀ : {m : Fin (n + 1) // m ≠ σ.symm l} := ⟨Fin.last n, Ne.symm hroot⟩
    have hσne : σ (Fin.last n) ≠ l := fun h => hroot (σ.injective ((σ.apply_symm_apply l).trans h.symm))
    have hsum := Finset.sum_eq_single_of_mem m₀ (Finset.mem_univ _)
      (f := fun m : {m : Fin (n + 1) // m ≠ σ.symm l} => if m.1 = Fin.last n then (N : ℂ) else 0)
      fun m _ hne => ite_eq_right fun heq => hne (Subtype.ext heq)
    simpa [m₀, hσne] using hsum

theorem sum_t1OutputSlope_slots {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      t1OutputSlope (N := N) Δ p σ m.1) =
      (∑ j : {j : Fin (n + 1) // j ≠ l},
        (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ)) +
        if σ (Fin.last n) = l then 0 else (N : ℂ) := by
  simp only [t1OutputSlope, Finset.sum_add_distrib,
    sum_t1OutputDerivative_slots, sum_t1OutputSeam_slots]

theorem t1PairLimit_eq_t1OutputLimitTerm {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) (i : T1PairIndex n l) :
    t1PairLimit (N := N) c x p l i =
      t1OutputLimitTerm (N := N) c x p l (t1PairOutputIndex i) := by
  let o := t1PairOutputIndex i
  have hoedge : o.edge = i.edge := rfl
  have hword : (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).2 = (fun _ => false) :=
    funext (t1PairZipperRun_word_eq_false i)
  have hreg' : zeroRootRegularizedWordTerm (N := N) c x p l o.σ (fun _ => false) =
      zeroRootRegularizedWordTerm (N := N) c x p l i.σ i.w := by
    simpa [o, t1PairOutputIndex, hword] using t1PairZipperRun_preserves hc x p hp hinj l hpl hBE i
  have hlabel : p (o.σ (t1EdgeLeft i.edge)) = p (i.σ (t1EdgeLeft i.edge)) :=
    congrArg p (t1PairOutputIndex_left i)
  rw [t1PairLimit_eq_regularizedWordTerm (N := N) (c := c) x p l i, ← hreg']
  change _ = zeroRootRegularizedWordTerm (N := N) c x p l o.σ (fun _ => false) *
    t1OutputSlope (N := N) (anisotropy c) p o.σ (t1EdgeLeft o.edge)
  cases hEdge : i.edge <;> simp [hEdge, t1EdgeLeft] at hlabel <;>
    simp [t1OutputSlope, t1EdgeLeft, hoedge, hEdge, zeroRootPhaseDerivative, hlabel]

theorem tendsto_sum_t1PairLimit_eq_sum_t1SigmaLimitTerm {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0)
    (hBE : BetheEquations N (anisotropy c) p) :
    (∑ i : T1PairIndex n l, t1PairLimit (N := N) c x p l i) =
      ∑ q : Σ σ : Equiv.Perm (Fin (n + 1)),
        {m : Fin (n + 1) // m ≠ σ.symm l}, t1SigmaLimitTerm (N := N) c x p l q := by
  rw [Finset.sum_congr rfl fun i _ => t1PairLimit_eq_t1OutputLimitTerm hc x p hp hinj l hpl hBE i]
  change (∑ i : T1PairIndex n l, t1OutputLimitTerm (N := N) c x p l (t1PairOutputEquiv i)) = _
  rw [Equiv.sum_comp t1PairOutputEquiv (t1OutputLimitTerm (N := N) c x p l),
    ← Equiv.sum_comp t1OutputIndexSigmaEquiv.symm (t1OutputLimitTerm (N := N) c x p l)]
  exact Finset.sum_congr rfl fun q _ => t1OutputLimitTerm_sigma c x p l q

end PottsDiscontinuity.BetheAnsatz
