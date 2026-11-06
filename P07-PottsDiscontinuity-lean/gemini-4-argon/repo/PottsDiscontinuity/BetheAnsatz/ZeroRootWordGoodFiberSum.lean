module

public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordFiniteSum
public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordGoodFiber

/-!
# Finite indices for the surviving zero-root word terms

The complete word expansion is indexed by a root slot, a word, and a constrained
permutation. This file relates that index to the good root-incident subtype and
to the paired T₁ representatives.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- All words and permutations, grouped by the slot occupied by the root label. -/
abbrev RootSlotWordFiberIndex (n : ℕ) (l : Fin (n + 1)) :=
  RootSlotFiberIndex n l × (Fin (n + 1) → Bool)

/-- Reindex a root-slot/word fiber as a permutation and word. -/
noncomputable def rootSlotWordFiberEquiv {n : ℕ} (l : Fin (n + 1)) :
    RootSlotWordFiberIndex n l ≃
      (Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → Bool)) :=
  Equiv.prodCongr (rootSlotFiberEquiv l) (Equiv.refl _)

/-- The word value associated with the root-slot good-fiber condition. -/
def rootSlotWordGood {n : ℕ} (l : Fin (n + 1))
    (i : RootSlotWordFiberIndex n l) : Prop :=
  RootIncidentFiberPredicate l (i.1.val.1, (i.1.val.2, i.2))

/-- The two constant words, retained for the T₀ contribution. -/
def rootSlotWordConstant {n : ℕ} {l : Fin (n + 1)}
    (i : RootSlotWordFiberIndex n l) : Prop :=
  i.2 = (fun _ => true) ∨ i.2 = (fun _ => false)

/-- The surviving root-slot/word indices: the two constant words or a good T₁ fiber. -/
def rootSlotWordSurvivor {n : ℕ} (l : Fin (n + 1))
    (i : RootSlotWordFiberIndex n l) : Prop :=
  rootSlotWordConstant i ∨ rootSlotWordGood l i

abbrev RootSlotWordConstantIndex (n : ℕ) (l : Fin (n + 1)) :=
  {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i}

abbrev RootSlotWordGoodIndex (n : ℕ) (l : Fin (n + 1)) :=
  {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i}

abbrev RootSlotWordBadIndex (n : ℕ) (l : Fin (n + 1)) :=
  {i : RootSlotWordFiberIndex n l //
    ¬ rootSlotWordConstant i ∧ ¬ rootSlotWordGood l i}

abbrev RootSlotWordSurvivorIndex (n : ℕ) (l : Fin (n + 1)) :=
  {i : RootSlotWordFiberIndex n l // rootSlotWordSurvivor l i}

theorem rootSlotWordGood_notConstant {n : ℕ} {l : Fin (n + 1)}
    {i : RootSlotWordFiberIndex n l} (hi : rootSlotWordGood l i) :
    ¬ rootSlotWordConstant i :=
  fun hc => hc.elim hi.2.1 hi.2.2.1

/-- Within the survivor subtype, the constant part is the original constant subtype. -/
noncomputable def rootSlotWordSurvivorConstantEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordSurvivorIndex n l // rootSlotWordConstant i.1} ≃
      RootSlotWordConstantIndex n l where
  toFun i := ⟨i.1.1, i.2⟩
  invFun i := ⟨⟨i.1, Or.inl i.2⟩, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Within the survivor subtype, the nonconstant part is exactly the good subtype. -/
noncomputable def rootSlotWordSurvivorGoodEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordSurvivorIndex n l // ¬ rootSlotWordConstant i.1} ≃
      RootSlotWordGoodIndex n l where
  toFun i := ⟨i.1.1, Or.resolve_left i.1.2 i.2⟩
  invFun i := ⟨⟨i.1, Or.inr i.2⟩, rootSlotWordGood_notConstant i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A Boolean selecting one of the two constant words. -/
abbrev ConstantWordIndex (n : ℕ) :=
  {w : Fin (n + 1) → Bool //
    w = (fun _ => true) ∨ w = (fun _ => false)}

noncomputable def constantWordEquiv {n : ℕ} : Bool ≃ ConstantWordIndex n where
  toFun b := ⟨fun _ => b, by cases b <;> simp⟩
  invFun w := w.1 0
  left_inv b := by cases b <;> rfl
  right_inv w := Subtype.ext <| by rcases w.2 with h | h <;> simp [h]

/-- Separate the word and permutation coordinates on constant root fibers. -/
noncomputable def rootSlotWordConstantSubtypeEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i} ≃
      RootSlotFiberIndex n l × ConstantWordIndex n where
  toFun i := (i.1.1, ⟨i.1.2, i.2⟩)
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex constant root-slot terms by the permutation and constant-word bit. -/
noncomputable def rootSlotWordConstantEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i} ≃
      Equiv.Perm (Fin (n + 1)) × Bool :=
  rootSlotWordConstantSubtypeEquiv.trans
    (Equiv.prodCongr (rootSlotFiberEquiv l) constantWordEquiv.symm)

/-- The good root-slot/word indices are exactly the root-incident T₁ indices. -/
noncomputable def rootSlotWordGoodEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i} ≃
      RootIncidentFiberTermIndex n l where
  toFun i := ⟨(i.1.1.val.1, (i.1.1.val.2, i.1.2)), i.2⟩
  invFun j := ⟨(⟨(j.1.1, j.1.2.1), j.2.1⟩, j.1.2.2), j.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A nonconstant word with a selected ML edge disjoint from the root slot. -/
abbrev RootSlotBadWord {n : ℕ} (r : Fin (n + 1)) :=
  {w : Fin (n + 1) → Bool //
    w ≠ (fun _ => true) ∧ w ≠ (fun _ => false) ∧
      ¬ ∀ a, w a = false → w (finRotate (n + 1) a) = true →
        r = a ∨ r = finRotate (n + 1) a}

/-- The bad root-slot word/permutation fibers, grouped so permutations are summed
last and can be canceled by the selected ML edge. -/
abbrev RootSlotBadFiberIndex {n : ℕ} (l : Fin (n + 1)) :=
  Σ r : Fin (n + 1), RootSlotBadWord r × RootSlotPerm l r

/-- The complement of the constant and good root-slot/word terms is exactly
the set of nonconstant words with an ML edge away from the root slot. -/
noncomputable def rootSlotWordBadEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l //
      ¬ rootSlotWordConstant i ∧ ¬ rootSlotWordGood l i} ≃
      RootSlotBadFiberIndex l where
  toFun i := ⟨i.1.1.val.1, ⟨i.1.2, fun h => i.2.1 (Or.inl h), fun h => i.2.1 (Or.inr h),
    fun hAll => i.2.2 ⟨i.1.1.property, fun h => i.2.1 (Or.inl h), fun h => i.2.1 (Or.inr h), hAll⟩⟩,
    ⟨i.1.1.val.2, i.1.1.property⟩⟩
  invFun := fun ⟨r, ⟨w, hw⟩, σ⟩ => ⟨(⟨(r, σ.1), σ.2⟩, w),
    fun h => h.elim hw.1 hw.2.1, fun hg => hw.2.2 hg.2.2.2⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

/-- The complement of the survivor indices is exactly the bad subtype. -/
noncomputable def rootSlotWordSurvivorComplementEquiv {n : ℕ} {l : Fin (n + 1)} :
    {i : RootSlotWordFiberIndex n l // ¬ rootSlotWordSurvivor l i} ≃
      RootSlotWordBadIndex n l where
  toFun i := ⟨i.1, ⟨fun h => i.2 (Or.inl h), fun h => i.2 (Or.inr h)⟩⟩
  invFun i := ⟨i.1, fun h => h.elim i.2.1 i.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fixed-amplitude summand at a root-slot/word index. -/
noncomputable def rootSlotWordFiberTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ) {l : Fin (n + 1)}
    (i : RootSlotWordFiberIndex n l) : ℂ :=
  fixedAmplitudeWordTerm (N := N) c x p q i.1.val.2 i.2

/-- The same fixed-amplitude summand on the bad-word fiber index. -/
noncomputable def rootSlotBadFiberTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ) {l : Fin (n + 1)}
    (i : RootSlotBadFiberIndex l) : ℂ :=
  fixedAmplitudeWordTerm (N := N) c x p q i.2.2.1 i.2.1.1

/-- All nonconstant root-slot fibers outside the good set cancel after grouping
permutations by the selected root slot and word. -/
theorem sum_rootSlotWordBadFiberTerm_eq_zero {N n : ℕ} {c : ℝ}
    (hc : 2 < c) (hn : 0 < n) (p q : Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℤ) (l : Fin (n + 1))
    (hBE : BetheEquations N (anisotropy c) p)
    (hAgree : ∀ k, k ≠ l → q k = p k)
    (hNotOne : ∀ k, k ≠ l → z (p k) ≠ 1) :
    (∑ i : {i : RootSlotWordFiberIndex n l //
      ¬ rootSlotWordConstant i ∧ ¬ rootSlotWordGood l i},
      rootSlotWordFiberTerm (N := N) c x p q i.1) = 0 := by
  rw [← (rootSlotWordBadEquiv (l := l)).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun w _ => ?_
  have ⟨a, ha, hb, hra, hrb⟩ : ∃ a, w.1 a = false ∧ w.1 (finRotate (n + 1) a) = true ∧
      r ≠ a ∧ r ≠ finRotate (n + 1) a := by
    by_contra! h
    exact w.2.2.2 fun a ha hb => Classical.or_iff_not_imp_left.mpr (h a ha hb)
  exact sum_rootSlotFiber_fixedAmplitudeWordTerm_eq_zero_of_ML_away
    hc hn p q x l r a w.1 hBE hAgree hNotOne ha hb hra hrb

/-- The fixed-amplitude summand on a canonical root-incident term index. -/
noncomputable def rootIncidentTermTerm {N n : ℕ} (c : ℝ)
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ) {l : Fin (n + 1)}
    (i : RootIncidentTermIndex n l) : ℂ :=
  fixedAmplitudeWordTerm (N := N) c x p q i.σ.1 i.w

/-- The sum of the two constant root-slot/word fibers is exactly T₀. -/
theorem sum_rootSlotWordConstantFiberTerm_eq_constantWordSumPerturbed
     {N n : ℕ} {c : ℝ} (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) (t : ℝ) :
    (∑ i : {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i},
      rootSlotWordFiberTerm (N := N) c x p (perturbedMomenta p l t) i.1) =
      constantWordSumPerturbed (N := N) c x p l t := by
  let e := rootSlotWordConstantEquiv (n := n) (l := l)
  let f : Equiv.Perm (Fin (n + 1)) × Bool → ℂ := fun q =>
    fixedAmplitudeWordTerm (N := N) c x p (perturbedMomenta p l t) q.1 (fun _ => q.2)
  rw [show (∑ i : {i : RootSlotWordFiberIndex n l // rootSlotWordConstant i},
        rootSlotWordFiberTerm (N := N) c x p (perturbedMomenta p l t) i.1) =
      ∑ i, f (e i) from Finset.sum_congr rfl fun i _ => by
        rcases i.2 with h | h <;>
          simp [f, e, rootSlotWordFiberTerm, rootSlotWordConstantEquiv,
            rootSlotWordConstantSubtypeEquiv, rootSlotFiberEquiv, constantWordEquiv, h],
    Equiv.sum_comp e f, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, constantWordSumPerturbed]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [f, fixedAmplitudeWordTerm, wordCoefficient_false, wordCoefficient_true,
    wordPhase_false, wordPhase_true]; ring

/-- Convert a good root-slot/word index to its unique canonical T₁ index. -/
noncomputable def rootSlotWordGoodToIncidentEquiv {n : ℕ} {l : Fin (n + 1)}
    (hn : 0 < n) :
    {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i} ≃
      RootIncidentTermIndex n l :=
  rootSlotWordGoodEquiv.trans (rootIncidentFiberEquiv hn).symm

/-- The good-fiber summand is the fixed-amplitude term indexed by its canonical
root-incident T₁ index. -/
theorem rootSlotWordGoodFiberTerm_eq_incidentTerm {N n : ℕ} {c : ℝ}
    {l : Fin (n + 1)} (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ)
    (hn : 0 < n) (i : {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i}) :
    rootSlotWordFiberTerm (N := N) c x p q i.1 =
      rootIncidentTermTerm (N := N) c x p q (rootSlotWordGoodToIncidentEquiv hn i) := by
  let j := rootSlotWordGoodToIncidentEquiv hn i
  have hraw := congrArg Subtype.val ((rootIncidentFiberEquiv hn).apply_symm_apply (rootSlotWordGoodEquiv i))
  have hσ' : j.σ.1 = i.1.1.val.2 := congrArg (fun d : RootFiberRawData n => d.2.1) hraw
  have hw' : j.w = i.1.2 := congrArg (fun d : RootFiberRawData n => d.2.2) hraw
  change fixedAmplitudeWordTerm (N := N) c x p q i.1.1.val.2 i.1.2 =
    fixedAmplitudeWordTerm (N := N) c x p q j.σ.1 j.w
  rw [hσ', hw']

/-- Reindex the sum of all good root-slot/word fibers as paired T₁ terms. -/
theorem sum_rootSlotWordGoodFiberTerm_eq_sum_t1PairTerm {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (l : Fin (n + 1)) (t : ℝ) (hn : 0 < n) :
    (∑ i : {i : RootSlotWordFiberIndex n l // rootSlotWordGood l i},
      rootSlotWordFiberTerm (N := N) c x p (perturbedMomenta p l t) i.1) =
      ∑ i : T1PairIndex n l, t1PairTerm (N := N) c x p l t i := by
  let e := rootSlotWordGoodToIncidentEquiv (n := n) (l := l) hn
  let f : RootIncidentTermIndex n l → ℂ :=
    rootIncidentTermTerm (N := N) c x p (perturbedMomenta p l t)
  rw [Finset.sum_congr rfl fun i _ =>
      rootSlotWordGoodFiberTerm_eq_incidentTerm x p (perturbedMomenta p l t) hn i,
    Equiv.sum_comp e f, ← Equiv.sum_comp t1PairSideEquiv f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [f, t1PairTerm, rootIncidentTermTerm, t1PairSideEquiv,
    t1PairSideForward, fixedAmplitudeWordTerm, perturbedWordTerm]; ring

/-- The full root-slot/word sum partitions into its two constant words, good
root-incident fibers, and the nonconstant fibers canceled by an away ML edge. -/
theorem sum_rootSlotWordFiberTerm_eq_constant_good_bad {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p q : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    (∑ i : RootSlotWordFiberIndex n l,
      rootSlotWordFiberTerm (N := N) c x p q i) =
      (∑ i : RootSlotWordConstantIndex n l,
        rootSlotWordFiberTerm (N := N) c x p q i.1) +
      (∑ i : RootSlotWordGoodIndex n l,
        rootSlotWordFiberTerm (N := N) c x p q i.1) +
      ∑ i : RootSlotWordBadIndex n l,
        rootSlotWordFiberTerm (N := N) c x p q i.1 := by
  let f : RootSlotWordFiberIndex n l → ℂ := rootSlotWordFiberTerm (N := N) c x p q
  rw [← Fintype.sum_subtype_add_sum_subtype (rootSlotWordSurvivor l) f,
    ← Fintype.sum_subtype_add_sum_subtype
      (fun i : RootSlotWordSurvivorIndex n l => rootSlotWordConstant i.1) (fun i => f i.1),
    ← Equiv.sum_comp (rootSlotWordSurvivorConstantEquiv (n := n) (l := l)) (fun i => f i.1),
    ← Equiv.sum_comp (rootSlotWordSurvivorGoodEquiv (n := n) (l := l)) (fun i => f i.1),
    ← Equiv.sum_comp (rootSlotWordSurvivorComplementEquiv (n := n) (l := l)) (fun i => f i.1)]
  rfl

end PottsDiscontinuity.BetheAnsatz
