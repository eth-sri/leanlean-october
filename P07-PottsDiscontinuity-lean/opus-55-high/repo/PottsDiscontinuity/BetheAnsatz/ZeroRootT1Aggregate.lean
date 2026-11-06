module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1OutputEquivalence
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1RegularizedResidue

/-!
# The aggregate T₁ contribution after zipper reindexing

The output index is equivalent to an output permutation together with an
allowed ML-left slot. This exposes the derivative sum over all nonzero root
labels and the single seam indicator.
-/

@[expose] public noncomputable section

open Finset Complex

namespace PottsDiscontinuity.BetheAnsatz

section
variable {n : ℕ}
/-- A cyclic edge's left endpoint, including the seam edge at `Fin.last`. -/
def t1EdgeLeftEquiv  : Option (Fin n) ≃ Fin (n + 1) where
  toFun := t1EdgeLeft
  invFun := fun m => Fin.lastCases none (fun j => some j) m
  left_inv := by
    intro e
    cases e <;> simp [t1EdgeLeft, Fin.lastCases_last, Fin.lastCases_castSucc]
  right_inv := by
    intro m
    refine Fin.lastCases ?_ (fun j => ?_) m <;> aesop

/-- Forget the seam/ordinary presentation and retain the left endpoint slot. -/
def t1OutputIndexSigmaEquiv {l : Fin (n + 1)} :
    T1OutputIndex n l ≃ Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l} where
  toFun o := ⟨o.σ, ⟨t1EdgeLeftEquiv o.edge, o.hleft⟩⟩
  invFun q := ⟨q.1, t1EdgeLeftEquiv.symm q.2.1, by
    have hm := q.2.2
    change t1EdgeLeftEquiv (t1EdgeLeftEquiv.symm q.2.1) ≠ q.1.symm l
    simp_all⟩
  left_inv := by
    intro o
    simp
  right_inv := by
    grind
end

/-- The corrected phase slope attached to an output permutation and a slot. -/
def t1OutputSlope {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (m : Fin (n + 1)) : ℂ :=
  (zeroRootPhaseDerivative (N := N) Δ (p (σ m)) False : ℂ) +
    if m = Fin.last n then (N : ℂ) else 0

section
variable {N n : ℕ} (c : ℝ) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
include c x p
/-- The all-M regularized coefficient times the corrected slope. -/
def t1OutputLimitTerm (o : T1OutputIndex n l) : ℂ :=
  zeroRootRegularizedWordTerm (N := N) c x p l o.σ (fun _ => false) *
    t1OutputSlope (N := N) (anisotropy c) p o.σ (t1EdgeLeft o.edge)

/-- The same limit summand in permutation/left-slot coordinates. -/
def t1SigmaLimitTerm (q : Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l}) : ℂ :=
  zeroRootRegularizedWordTerm (N := N) c x p l q.1 (fun _ => false) *
    t1OutputSlope (N := N) (anisotropy c) p q.1 q.2.1

theorem t1OutputLimitTerm_sigma (q : Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l}) :
    t1OutputLimitTerm (N := N) c x p l (t1OutputIndexSigmaEquiv.symm q) =
      t1SigmaLimitTerm (N := N) c x p l q := by
  unfold t1OutputLimitTerm t1SigmaLimitTerm
  change zeroRootRegularizedWordTerm c x p l q.1 (fun _ => false) *
      t1OutputSlope (anisotropy c) p q.1
        (t1EdgeLeftEquiv (t1EdgeLeftEquiv.symm q.2.1)) = _
  simp
end

/-- Output slots other than the zero slot correspond exactly to the nonzero
root labels under an output permutation. -/
def t1OutputSlotLabelEquiv {n : ℕ} (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    {m : Fin (n + 1) // m ≠ σ.symm l} ≃ {j : Fin (n + 1) // j ≠ l} where
  toFun m := ⟨σ m.1, by
    grind⟩
  invFun j := ⟨σ.symm j.1, by
    aesop⟩
  left_inv := by
    grind
  right_inv := by
    grind

section
variable {N n : ℕ}
theorem sum_t1OutputDerivative_slots (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      (zeroRootPhaseDerivative (N := N) Δ (p (σ m.1)) False : ℂ)) =
      ∑ j : {j : Fin (n + 1) // j ≠ l},
        (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ) :=
  Equiv.sum_comp (t1OutputSlotLabelEquiv l σ)
    (fun j : {j : Fin (n + 1) // j ≠ l} =>
      (zeroRootPhaseDerivative Δ (p j.1) False : ℂ))

theorem sum_t1OutputSeam_slots (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      if m.1 = Fin.last n then (N : ℂ) else 0) =
      if σ (Fin.last n) = l then 0 else (N : ℂ) := by
  by_cases hroot : σ.symm l = Fin.last n
  · have hsum : (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
        (if m.1 = Fin.last n then (N : ℂ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      simp_all
    grind
  · let m₀ : {m : Fin (n + 1) // m ≠ σ.symm l} :=
      ⟨Fin.last n, fun h => hroot h.symm⟩
    have hzero : ∀ m ∈ (Finset.univ : Finset {m : Fin (n + 1) // m ≠ σ.symm l}),
        m ≠ m₀ → (if m.1 = Fin.last n then (N : ℂ) else 0) = 0 := by
      grind
    have hsum := Finset.sum_eq_single_of_mem m₀ (Finset.mem_univ _) hzero
    grind

theorem sum_t1OutputSlope_slots (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      t1OutputSlope (N := N) Δ p σ m.1) =
      (∑ j : {j : Fin (n + 1) // j ≠ l},
        (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ)) +
        if σ (Fin.last n) = l then 0 else (N : ℂ) := by
  simp only [t1OutputSlope, Finset.sum_add_distrib]
  rw [sum_t1OutputDerivative_slots, sum_t1OutputSeam_slots]
end

section
variable {N n : ℕ} {c : ℝ} (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p)
include c hc x p hp hinj hpl hBE
theorem t1PairLimit_eq_t1OutputLimitTerm (i : T1PairIndex n l) :
    t1PairLimit (N := N) c x p l i =
      t1OutputLimitTerm (N := N) c x p l (t1PairOutputIndex i) := by
  rw [t1PairLimit_eq_regularizedWordTerm, ← t1PairZipperRun_preserves hc x p hp hinj l hpl hBE i,
    show (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).2 = fun _ => false from
      funext (t1PairZipperRun_word_eq_false i), ← t1PairOutputIndex_left i]
  change _ * _ = _ * t1OutputSlope (anisotropy c) p (t1PairOutputIndex i).σ (t1EdgeLeft i.edge)
  cases i.edge <;> simp [t1EdgeLeft, zeroRootPhaseDerivative, t1OutputSlope] <;> exact .inl rfl

theorem tendsto_sum_t1PairLimit_eq_sum_t1SigmaLimitTerm  :
    (∑ i : T1PairIndex n l, t1PairLimit (N := N) c x p l i) =
      ∑ q : Σ σ : Equiv.Perm (Fin (n + 1)),
        {m : Fin (n + 1) // m ≠ σ.symm l}, t1SigmaLimitTerm (N := N) c x p l q := by
  calc
    _ = ∑ i : T1PairIndex n l,
          t1OutputLimitTerm c x p l (t1PairOutputIndex i) := by
      simp_all [t1PairLimit_eq_t1OutputLimitTerm]
    _ = ∑ o : T1OutputIndex n l, t1OutputLimitTerm c x p l o :=
      Equiv.sum_comp t1PairOutputEquiv
        (t1OutputLimitTerm c x p l)
    _ = ∑ q : Σ σ : Equiv.Perm (Fin (n + 1)),
          {m : Fin (n + 1) // m ≠ σ.symm l},
          t1OutputLimitTerm c x p l (t1OutputIndexSigmaEquiv.symm q) :=
      (Equiv.sum_comp t1OutputIndexSigmaEquiv.symm
        (t1OutputLimitTerm (N := N) c x p l)).symm
    _ = _ := by
      grind [t1OutputLimitTerm_sigma]
end
end PottsDiscontinuity.BetheAnsatz
