module
public import Mathlib

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
  invFun := fun m => Fin.lastCases none  some  m
  left_inv := by
    intro e
    cases e <;> simp [t1EdgeLeft, Fin.lastCases_last, Fin.lastCases_castSucc]
  right_inv := by
    intro m
    refine Fin.lastCases ?_ (fun j => ?_) m
    all_goals aesop

/-- Forget the seam/ordinary presentation and retain the left endpoint slot. -/
noncomputable def t1OutputIndexSigmaEquiv {n : ℕ} {l : Fin (n + 1)} :
    T1OutputIndex n l ≃ Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l} where
  toFun o := ⟨o.σ, ⟨t1EdgeLeftEquiv o.edge, o.hleft⟩⟩
  invFun q := ⟨q.1, t1EdgeLeftEquiv.symm q.2.1, by
    have hm := q.2.2
    change t1EdgeLeftEquiv (t1EdgeLeftEquiv.symm q.2.1) ≠ q.1.symm l
    rw [t1EdgeLeftEquiv.apply_symm_apply]
    exact hm⟩
  left_inv := by
    intro o
    all_goals simp_all
  right_inv := by
    grind

/-- The corrected phase slope attached to an output permutation and a slot. -/
noncomputable def t1OutputSlope {N n : ℕ} (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (m : Fin (n + 1))  :=
  (zeroRootPhaseDerivative (N := N) Δ (p (σ m)) False : ℂ) +
    if m = Fin.last n then (N : ℂ) else 0

/-- The all-M regularized coefficient times the corrected slope. -/
noncomputable def t1OutputLimitTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (o : T1OutputIndex n l)  :=
  zeroRootRegularizedWordTerm (N := N) c x p l o.σ (fun _ => false) *
    t1OutputSlope (N := N) (anisotropy c) p o.σ (t1EdgeLeft o.edge)

/-- The same limit summand in permutation/left-slot coordinates. -/
noncomputable def t1SigmaLimitTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (q : Σ σ : Equiv.Perm (Fin (n + 1)),
      {m : Fin (n + 1) // m ≠ σ.symm l})  :=
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
  toFun m := ⟨σ m.1, by
    grind⟩
  invFun j := ⟨σ.symm j.1, by
    aesop⟩
  left_inv := by
    intro m
    apply Subtype.ext
    simp
  right_inv := by
    intro j
    apply Subtype.ext
    simp

section

variable {N n : ℕ}
include N n

theorem sum_t1OutputDerivative_slots  (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
     ∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      (zeroRootPhaseDerivative (N := N) Δ (p (σ m.1)) False : ℂ)  =
      ∑ j : {j : Fin (n + 1) // j ≠ l},
        (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ) := Equiv.sum_comp (t1OutputSlotLabelEquiv l σ)
                                                               fun j  =>
                                                                (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ) 

theorem sum_t1OutputSeam_slots  (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      if m.1 = Fin.last n then (N : ℂ) else 0) =
      if σ (Fin.last n) = l then 0 else (N : ℂ) := by
  
  by_cases hroot : σ.symm l = Fin.last n
  · have hσ : σ (Fin.last n) = l := by
      rw [← hroot]
      exact σ.apply_symm_apply l
    
    have hsum :  ∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
        (if m.1 = Fin.last n then (N : ℂ) else 0)  = 0 := by
      apply Finset.sum_eq_zero
      all_goals simp_all
    rw [hsum]
    simp [hσ]
  · let m₀ : {m : Fin (n + 1) // m ≠ σ.symm l} :=
      ⟨Fin.last n, fun h => hroot h.symm⟩
    have hzero : ∀ m ∈ (Finset.univ : Finset {m : Fin (n + 1) // m ≠ σ.symm l}),
        m ≠ m₀ → (if m.1 = Fin.last n then (N : ℂ) else 0) = 0 := by
      grind
    
    have hsum := Finset.sum_eq_single_of_mem m₀ (Finset.mem_univ _) hzero
    all_goals grind

theorem sum_t1OutputSlope_slots  (Δ : ℝ)
    (p : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
     ∑ m : {m : Fin (n + 1) // m ≠ σ.symm l},
      t1OutputSlope (N := N) Δ p σ m.1  =
       ∑ j : {j : Fin (n + 1) // j ≠ l},
        (zeroRootPhaseDerivative (N := N) Δ (p j.1) False : ℂ)  +
        if σ (Fin.last n) = l then 0 else (N : ℂ) := by
  simp only [t1OutputSlope, Finset.sum_add_distrib]
  rw [sum_t1OutputDerivative_slots, sum_t1OutputSeam_slots]

section

variable {c : ℝ} (hc : 2 < c) (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p) (l : Fin (n + 1)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p)
include hc hp hinj hpl hBE

theorem t1PairLimit_eq_t1OutputLimitTerm   (i : T1PairIndex n l) :
    t1PairLimit (N := N) c x p l i =
      t1OutputLimitTerm (N := N) c x p l (t1PairOutputIndex i) := by
  let o := t1PairOutputIndex i
  have hoedge : o.edge = i.edge := rfl
  have hword : (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).2 =
       fun _ => false  := by
    funext k
    exact t1PairZipperRun_word_eq_false i k
  have hreg := t1PairZipperRun_preserves hc x p hp hinj l hpl hBE i
  have hσout : o.σ = (zeroRootZipperRun (t1PairZipperPath i) (i.σ, i.w)).1 := rfl
  
  have hlabel : p (o.σ (t1EdgeLeft i.edge)) =
      p (i.σ (t1EdgeLeft i.edge)) := congrArg p (t1PairOutputIndex_left i)
  have hlim := t1PairLimit_eq_regularizedWordTerm (N := N) (c := c) x p l i
  change t1PairLimit (N := N) c x p l i =
    zeroRootRegularizedWordTerm (N := N) c x p l o.σ (fun _ => false) *
      t1OutputSlope (N := N) (anisotropy c) p o.σ (t1EdgeLeft o.edge)
  cases hEdge : i.edge with
  | none =>
      simp_all [t1EdgeLeft, zeroRootPhaseDerivative, t1OutputSlope]
  | some a =>
      simp_all [t1EdgeLeft, zeroRootPhaseDerivative, t1OutputSlope]

theorem tendsto_sum_t1PairLimit_eq_sum_t1SigmaLimitTerm   :
     ∑ i : T1PairIndex n l, t1PairLimit (N := N) c x p l i  =
      ∑ q : Σ σ : Equiv.Perm (Fin (n + 1)),
        {m : Fin (n + 1) // m ≠ σ.symm l}, t1SigmaLimitTerm (N := N) c x p l q := by
  calc
    _ = ∑ i : T1PairIndex n l,
          t1OutputLimitTerm (N := N) c x p l (t1PairOutputIndex i) := by
      simp_all [t1PairLimit_eq_t1OutputLimitTerm]
    _ = ∑ o : T1OutputIndex n l, t1OutputLimitTerm (N := N) c x p l o :=
      Equiv.sum_comp t1PairOutputEquiv
        (t1OutputLimitTerm (N := N) c x p l)
    _ = ∑ q : Σ σ : Equiv.Perm (Fin (n + 1)),
          {m : Fin (n + 1) // m ≠ σ.symm l},
          t1OutputLimitTerm (N := N) c x p l (t1OutputIndexSigmaEquiv.symm q) :=
      (Equiv.sum_comp t1OutputIndexSigmaEquiv.symm
        (t1OutputLimitTerm (N := N) c x p l)).symm
    _ = _ := by
      grind [t1OutputLimitTerm_sigma]

end

end
end PottsDiscontinuity.BetheAnsatz
