module

public import HypoellipticAleksandrov.Parabolic.CrossVelocityWeakDerivativeCommutation
public import HypoellipticAleksandrov.Parabolic.GenericParabolicIndexArithmetic
public import HypoellipticAleksandrov.Parabolic.MixedTimeVelocityWeakDerivativeCommutation
public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndexBoundCoherence
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique

/-!
# Generic add-two assembly for parabolic weak-derivative families

This module develops the index classification used to assemble supplied
Hessian and time-successor representatives into a coherent family whose
ambient parabolic bound `M + 2` is one larger than the supplied family's bound
`M + 1`.  The supplied Hessian and time entries lie two parabolic weights above
their source index `beta`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

namespace ParabolicDerivativeIndex

private lemma coe_timeSucc_add {d L : ℕ} (a : ParabolicDerivativeIndex d L) (h) :
    (timeSucc a h).1 = a.1 + Pi.single (timeCoord d) 1 := by
  classical
  ext c
  cases c <;> simp [timeSucc, TimeVelocityMultiIndex.ofTimeVelocity,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, timeCoord, velocityCoord]

private lemma coe_velocitySucc_add {d L : ℕ} (a : ParabolicDerivativeIndex d L) (i : Fin d) (h) :
    (velocitySucc a i h).1 = a.1 + Pi.single (velocityCoord i) 1 := by
  classical
  ext c
  rcases c with _ | j
  · rfl
  · by_cases hji : j = i <;> simp [velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.velocity, velocityCoord, hji]

/-- Removing a supported unit and reattaching it recovers the original index. -/
private lemma sub_single_add {d : ℕ} {a : TimeVelocityMultiIndex d} {i : TimeVelocityCoord d}
    (hi : 0 < a i) : a - Pi.single i 1 + Pi.single i 1 = a := by
  classical
  ext j
  by_cases h : j = i
  · subst j; simpa only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] using Nat.sub_add_cancel hi
  · simp [Pi.single_eq_of_ne h]

/-- Distinct last coordinates on the same index have a common predecessor. -/
private lemma exists_common_predecessor {d : ℕ} {a b : TimeVelocityMultiIndex d}
    {i j : TimeVelocityCoord d} (hij : i ≠ j)
    (h : a + Pi.single i 1 = b + Pi.single j 1) :
    ∃ r : TimeVelocityMultiIndex d, r + Pi.single j 1 = a ∧ r + Pi.single i 1 = b := by
  classical
  have hj : 0 < a j := by
    have he := congrFun h j
    simp [Pi.single_eq_of_ne hij.symm] at he
    omega
  let r := a - Pi.single j 1
  have hr : r + Pi.single j 1 = a := sub_single_add hj
  refine ⟨r, hr, add_right_cancel (b := Pi.single j 1) ?_⟩
  calc
    _ = (r + Pi.single j 1) + Pi.single i 1 := by ac_rfl
    _ = _ := hr ▸ h

private lemma exists_pos_velocity {d : ℕ} {a : TimeVelocityMultiIndex d}
    (ha : 0 < a.velocity.order) : ∃ i : Fin d, 0 < a (velocityCoord i) := by
  rw [VelocityMultiIndex.order, Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)] at ha
  obtain ⟨i, _, hi⟩ := ha
  exact ⟨i, hi⟩

/-- An inherited entry, a top time entry, or a purely spatial top entry. Only
    the identities needed for commuting the last derivatives are stored. -/
private inductive ExtensionPath {d M : ℕ} (a : ParabolicDerivativeIndex d (M + 2))
  | inherited (h : a.1.parabolicWeight ≤ M + 1)
  | time (b : ParabolicDerivativeIndex d M) (h : b.1 + Pi.single (timeCoord d) 1 = a.1)
  | spatial (b : ParabolicDerivativeIndex d M) (j i : Fin d)
      (h : b.1 + Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1 = a.1)
      (ht : a.1.timeOrder = 0)

private lemma spatial_path_nonempty {d M : ℕ} (a : ParabolicDerivativeIndex d (M + 2))
    (ha : ¬ a.1.parabolicWeight ≤ M + 1) (ht : a.1.timeOrder = 0) : Nonempty (ExtensionPath a) := by
  have ha' : a.1.parabolicWeight = M + 2 := by omega
  obtain ⟨i, hi⟩ := exists_pos_velocity (a := a.1) (by
    change 2 * a.1.timeOrder + a.1.velocity.order = M + 2 at ha'
    omega)
  let b := a.1 - Pi.single (velocityCoord i) 1
  have hb : b + Pi.single (velocityCoord i) 1 = a.1 := sub_single_add hi
  have hw := congrArg TimeVelocityMultiIndex.parabolicWeight hb
  simp only [TimeVelocityMultiIndex.parabolicWeight_add,
    TimeVelocityMultiIndex.parabolicWeight_single_velocity, ha'] at hw
  have hbt : b.timeOrder = 0 := by
    classical
    simpa [b, TimeVelocityMultiIndex.timeOrder, Pi.single_eq_of_ne, timeCoord, velocityCoord] using ht
  obtain ⟨j, hj⟩ := exists_pos_velocity (a := b) (by
    change 2 * b.timeOrder + b.velocity.order + 1 = M + 2 at hw
    omega)
  let c := b - Pi.single (velocityCoord j) 1
  have hc : c + Pi.single (velocityCoord j) 1 = b := sub_single_add hj
  have hw' := congrArg TimeVelocityMultiIndex.parabolicWeight hc
  simp only [TimeVelocityMultiIndex.parabolicWeight_add,
    TimeVelocityMultiIndex.parabolicWeight_single_velocity] at hw'
  exact ⟨.spatial ⟨c, by omega⟩ j i ((congrArg (· + Pi.single (velocityCoord i) 1) hc).trans hb) ht⟩

private noncomputable def extensionPath {d M : ℕ} (a : ParabolicDerivativeIndex d (M + 2)) :
    ExtensionPath a :=
  if h : a.1.parabolicWeight ≤ M + 1 then .inherited h
  else if ht : 0 < a.1.timeOrder then
    let b := a.1 - Pi.single (timeCoord d) 1
    have hb : b + Pi.single (timeCoord d) 1 = a.1 := sub_single_add ht
    .time ⟨b, by
      have hw := congrArg TimeVelocityMultiIndex.parabolicWeight hb
      simp only [TimeVelocityMultiIndex.parabolicWeight_add,
        TimeVelocityMultiIndex.parabolicWeight_single_time] at hw
      omega⟩ hb
  else Classical.choice (spatial_path_nonempty a h (Nat.eq_zero_of_not_pos ht))

private def velocityMiddle {d M : ℕ} (b : ParabolicDerivativeIndex d M) (i : Fin d) :
    ParabolicDerivativeIndex d (M + 1) := velocitySucc (castLE (Nat.le_succ M) b) i (by
  rw [coe_castLE]
  omega)

private lemma coe_velocityMiddle {d M : ℕ} (b : ParabolicDerivativeIndex d M) (i : Fin d) :
    (velocityMiddle b i).1 = b.1 + Pi.single (velocityCoord i) 1 :=
  coe_velocitySucc_add _ _ _

/-- The new entries and their weak-derivative certificates, relative to the
    inherited family. -/
private structure ExtensionData {d M : ℕ} {V : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u) where
  H : TimeVelocity d → ParabolicDerivativeIndex d M → Fin d → Fin d → ℝ
  W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ
  hessMem : ∀ b j i, ParabolicMemLpOn V 2 (fun z => H z b j i)
  hessWeak : ∀ b j i, HasWeakVelocityPartialDerivOn V i (D.representative (velocityMiddle b j))
    (fun z => H z b j i)
  timeMem : ∀ b, ParabolicMemLpOn V 2 (W b)
  timeWeak : ∀ b, HasWeakTimeDerivOn V (D.representative (castLE (Nat.le_succ M) b)) (W b)

namespace ExtensionData

open HypoellipticAleksandrov.Analysis

variable {d M : ℕ} {V : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
  {D : ParabolicWeakDerivativeFamily d (M + 1) V u}

private noncomputable def rep (A : ExtensionData D) (a : ParabolicDerivativeIndex d (M + 2)) : TimeVelocity d → ℝ :=
  match extensionPath a with
  | .inherited h => D.representative (restrictLE a h)
  | .time b _ => A.W b
  | .spatial b j i _ _ => fun z => A.H z b j i

private lemma rep_inherited (A : ExtensionData D) (a : ParabolicDerivativeIndex d (M + 2))
    (h : a.1.parabolicWeight ≤ M + 1) : A.rep a = D.representative (restrictLE a h) := by
  simp [rep, extensionPath, h]

private lemma rep_cast (A : ExtensionData D) (a : ParabolicDerivativeIndex d (M + 1)) :
    A.rep (castLE (by omega) a) = D.representative a := A.rep_inherited _ a.2

private lemma weakTime (A : ExtensionData D) (a : ParabolicDerivativeIndex d (M + 2))
    (h : a.1.parabolicWeight + 2 ≤ M + 2) :
    HasWeakTimeDerivOn V (A.rep a) (A.rep (timeSucc a h)) := by
  rw [A.rep_inherited a (by omega)]
  unfold rep
  cases extensionPath (timeSucc a h) with
  | inherited ht =>
    rw [parabolicWeight_timeSucc] at ht
    exact D.hasWeakTimeSucc (restrictLE a (by omega)) ht
  | time b he =>
    rw [coe_timeSucc_add] at he
    have he' : castLE (Nat.le_succ M) b = restrictLE a (by omega) := Subtype.ext (add_right_cancel he)
    rw [← he']
    exact A.timeWeak b
  | spatial b j i he ht => rw [timeOrder_timeSucc] at ht; omega

private lemma weakVelocity (A : ExtensionData D) (hV : IsOpen V) (a : ParabolicDerivativeIndex d (M + 2)) (k : Fin d)
    (h : a.1.parabolicWeight + 1 ≤ M + 2) :
    HasWeakVelocityPartialDerivOn V k (A.rep a) (A.rep (velocitySucc a k h)) := by
  let a' := restrictLE a (show a.1.parabolicWeight ≤ M + 1 by omega)
  rw [A.rep_inherited a a'.2]
  change HasWeakVelocityPartialDerivOn V k (D.representative a') (A.rep (velocitySucc a k h))
  unfold rep
  cases extensionPath (velocitySucc a k h) with
  | inherited ht =>
    rw [parabolicWeight_velocitySucc] at ht
    exact D.hasWeakVelocitySucc a' k ht
  | time b he =>
    rw [coe_velocitySucc_add] at he
    obtain ⟨r, hr, hrb⟩ := exists_common_predecessor (i := velocityCoord k) (j := timeCoord d)
      (by simp [timeCoord, velocityCoord]) he.symm
    have hw := congrArg TimeVelocityMultiIndex.parabolicWeight hr
    simp only [TimeVelocityMultiIndex.parabolicWeight_add,
      TimeVelocityMultiIndex.parabolicWeight_single_time] at hw
    let c : ParabolicDerivativeIndex d (M + 1) := ⟨r, by omega⟩
    have ht := D.hasWeakTimeSucc c (by change r.parabolicWeight + 2 ≤ M + 1; omega)
    have hv := D.hasWeakVelocitySucc c k (by change r.parabolicWeight + 1 ≤ M + 1; omega)
    rw [show timeSucc c _ = a' from Subtype.ext ((coe_timeSucc_add c _).trans hr)] at ht
    rw [show velocitySucc c k _ = castLE (Nat.le_succ M) b from
      Subtype.ext ((coe_velocitySucc_add c k _).trans hrb)] at hv
    exact hasWeakVelocityPartialDerivOn_of_hasWeakTimeDerivOn_velocityDeriv k ht hv (A.timeWeak b)
  | spatial b j i he ht =>
    rw [coe_velocitySucc_add, ← coe_velocityMiddle] at he
    by_cases hki : k = i
    · subst k
      have e : velocityMiddle b j = a' := Subtype.ext (add_right_cancel he)
      rw [← e]
      exact A.hessWeak b j i
    · obtain ⟨r, hr, hrb⟩ := exists_common_predecessor
        (i := velocityCoord k) (j := velocityCoord i) (fun e => hki (Sum.inr.inj e)) he.symm
      have hw := congrArg TimeVelocityMultiIndex.parabolicWeight hr
      simp only [TimeVelocityMultiIndex.parabolicWeight_add,
        TimeVelocityMultiIndex.parabolicWeight_single_velocity] at hw
      let c : ParabolicDerivativeIndex d M := ⟨r, by omega⟩
      have h₁ : velocityMiddle c i = a' := Subtype.ext ((coe_velocityMiddle _ _).trans hr)
      have h₂ : velocityMiddle c k = velocityMiddle b j := Subtype.ext ((coe_velocityMiddle _ _).trans hrb)
      have hc := HasWeakVelocityPartialDerivOn.cross_ae_eq_of_memLp hV i k _ _ _ _ _
        (A.hessMem c i k) (A.hessMem b j i)
        (D.hasWeakVelocitySucc (castLE (Nat.le_succ M) c) i _)
        (D.hasWeakVelocitySucc (castLE (Nat.le_succ M) c) k _)
        (A.hessWeak c i k) (by
          have hw := A.hessWeak b j i
          rw [← h₂] at hw
          exact hw)
      rw [← h₁]
      exact (A.hessWeak c i k).congr_ae Filter.EventuallyEq.rfl hc

private noncomputable def family (A : ExtensionData D) (hV : IsOpen V) : ParabolicWeakDerivativeFamily d (M + 2) V u where
  representative := A.rep
  memLp a := by
    unfold rep
    cases extensionPath a with
    | inherited h => exact D.memLp _
    | time b _ => exact A.timeMem b
    | spatial b j i _ _ => exact A.hessMem b j i
  zero_ae := by
    change A.rep (castLE (by omega) (zero d (M + 1))) =ᵐ[timeVelocityVolumeOn V] u
    rw [A.rep_cast]
    exact D.zero_ae
  hasWeakTimeSucc := A.weakTime
  hasWeakVelocitySucc := A.weakVelocity hV

private lemma sourceTime_ae (A : ExtensionData D) (hV : IsOpen V) (b : ParabolicDerivativeIndex d M) :
    (A.family hV).representative (sourceTime (L := M + 2) (by omega) b) =ᵐ[timeVelocityVolumeOn V]
      A.W b := by
  let a := castLE (Nat.le_succ M) b
  have hw := (A.family hV).hasWeakTimeSucc (castLE (by omega) a) (by simpa [a] using b.2)
  change HasWeakTimeDerivOn V (A.rep (castLE (by omega) a)) (A.rep (sourceTime (by omega) b)) at hw
  rw [A.rep_cast] at hw
  exact HasWeakTimeDerivOn.ae_eq_of_memLp hV (by norm_num) ((A.family hV).memLp _)
    (A.timeMem b) hw (A.timeWeak b)

private lemma sourceVelocityTwo_ae (A : ExtensionData D) (hV : IsOpen V) (b : ParabolicDerivativeIndex d M) (j i : Fin d) :
    (A.family hV).representative (sourceVelocityTwo (L := M + 2) (by omega) b j i) =ᵐ[timeVelocityVolumeOn V]
      fun z => A.H z b j i := by
  let a := castLE (by omega : M + 1 ≤ M + 2) (velocityMiddle b j)
  have h : a.1.parabolicWeight + 1 ≤ M + 2 := by
    dsimp only [a]
    rw [coe_castLE, coe_velocityMiddle, TimeVelocityMultiIndex.parabolicWeight_add,
      TimeVelocityMultiIndex.parabolicWeight_single_velocity]
    omega
  have he : velocitySucc a i h = sourceVelocityTwo (L := M + 2) (by omega) b j i := by
    apply Subtype.ext
    simp only [coe_velocitySucc_add, a, coe_castLE, coe_velocityMiddle, coe_sourceVelocityTwo]
  have hw := A.weakVelocity hV a i h
  rw [he] at hw
  dsimp only [a] at hw
  rw [A.rep_cast] at hw
  exact HasWeakVelocityPartialDerivOn.ae_eq_of_memLp hV (by norm_num) ((A.family hV).memLp _)
    (A.hessMem b j i) hw (A.hessWeak b j i)

private def energy (A : ExtensionData D) : ℝ := D.squaredL2Norm +
  (∑ b, ∑ j, ∑ i, squaredL2Seminorm (timeVelocityVolumeOn V) (fun z => A.H z b j i)) +
  ∑ b, squaredL2Seminorm (timeVelocityVolumeOn V) (A.W b)

private lemma rep_norm_le (A : ExtensionData D) (a : ParabolicDerivativeIndex d (M + 2)) :
    squaredL2Seminorm (timeVelocityVolumeOn V) (A.rep a) ≤ A.energy := by
  let H (b : ParabolicDerivativeIndex d M) (j i : Fin d) :=
    squaredL2Seminorm (timeVelocityVolumeOn V) (fun z => A.H z b j i)
  let W (b : ParabolicDerivativeIndex d M) := squaredL2Seminorm (timeVelocityVolumeOn V) (A.W b)
  have hH b j i : 0 ≤ H b j i := sq_nonneg _
  have hW b : 0 ≤ W b := sq_nonneg _
  have hD := ParabolicWeakDerivativeFamily.squaredL2Norm_nonneg D
  have hHs : 0 ≤ ∑ b, ∑ j, ∑ i, H b j i := by positivity
  have hWs : 0 ≤ ∑ b, W b := by positivity
  change squaredL2Seminorm (timeVelocityVolumeOn V) (A.rep a) ≤ D.squaredL2Norm + (∑ b, ∑ j, ∑ i, H b j i) + ∑ b, W b
  unfold rep
  cases extensionPath a with
  | inherited h =>
    exact (D.component_sq_le_squaredL2Norm _).trans (by linarith)
  | time b he =>
    exact (Finset.single_le_sum (f := W) (fun k _ => hW k) (Finset.mem_univ b)).trans
      (by linarith)
  | spatial b j i he ht =>
    have hi := Finset.single_le_sum (f := H b j) (fun k _ => hH b j k) (Finset.mem_univ i)
    have hj := Finset.single_le_sum (f := fun j => ∑ i, H b j i)
      (fun j _ => Finset.sum_nonneg fun i _ => hH b j i) (Finset.mem_univ j)
    have hb := Finset.single_le_sum (f := fun b => ∑ j, ∑ i, H b j i)
      (fun b _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hH b j i)
      (Finset.mem_univ b)
    exact (hi.trans (hj.trans hb)).trans (by linarith)

private lemma family_norm_le (A : ExtensionData D) (hV : IsOpen V) :
    (A.family hV).squaredL2Norm ≤ (Fintype.card (ParabolicDerivativeIndex d (M + 2)) : ℝ) * A.energy :=
  (Finset.sum_le_sum (fun a _ => A.rep_norm_le a)).trans_eq (by simp)

end ExtensionData

/-- A coherent weak family extends its ambient parabolic bound from `M + 1`
to `M + 2` using supplied representatives two weights above each `beta`. -/
theorem exists_parabolicWeakDerivativeFamily_add_two_of_hessian_timeSuccessors
    (d M : ℕ) (hM : 1 ≤ M)
    {V : Set (TimeVelocity d)} (hV : IsOpen V)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (H : TimeVelocity d → ParabolicDerivativeIndex d M →
      Fin d → Fin d → ℝ)
    (W : ParabolicDerivativeIndex d M → TimeVelocity d → ℝ)
    (hHmem : ∀ beta j i, ParabolicMemLpOn V 2
      (fun z => H z beta j i))
    (hHweak : ∀ beta j i, HasWeakVelocityPartialDerivOn V i
      (fun z =>
        D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE
              (Nat.le_succ M) beta) j
            (by
              change beta.1.parabolicWeight + 1 ≤ M + 1
              omega)) z)
      (fun z => H z beta j i))
    (hWmem : ∀ beta, ParabolicMemLpOn V 2 (W beta))
    (hWweak : ∀ beta, HasWeakTimeDerivOn V
      (fun z => D.representative
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z)
      (W beta)) :
    ∃ Dnext : ParabolicWeakDerivativeFamily d (M + 2) V u,
      (∀ alpha : ParabolicDerivativeIndex d (M + 1),
        Dnext.representative
          (ParabolicDerivativeIndex.castLE (by omega) alpha) =
            D.representative alpha) ∧
      (∀ beta : ParabolicDerivativeIndex d M,
        Dnext.representative
          (ParabolicDerivativeIndex.sourceTime
            (L := M + 2) (by omega) beta) =ᵐ[timeVelocityVolumeOn V]
              W beta) ∧
      (∀ beta : ParabolicDerivativeIndex d M, ∀ j i : Fin d,
        Dnext.representative
          (ParabolicDerivativeIndex.sourceVelocityTwo
            (L := M + 2) (by omega) beta j i) =ᵐ[timeVelocityVolumeOn V]
              fun z => H z beta j i) ∧
      ParabolicWeakDerivativeFamily.squaredL2Norm Dnext ≤
        (Fintype.card (ParabolicDerivativeIndex d (M + 2)) : ℝ) *
          (ParabolicWeakDerivativeFamily.squaredL2Norm D +
            (∑ beta : ParabolicDerivativeIndex d M,
              ∑ j : Fin d, ∑ i : Fin d,
                (ENNReal.toReal (eLpNorm (fun z => H z beta j i) 2
                  (timeVelocityVolumeOn V))) ^ 2) +
            ∑ beta : ParabolicDerivativeIndex d M,
              (ENNReal.toReal (eLpNorm (W beta) 2
                (timeVelocityVolumeOn V))) ^ 2) := by
  let A : ExtensionData D := ⟨H, W, hHmem, hHweak, hWmem, hWweak⟩
  exact ⟨A.family hV, A.rep_cast, A.sourceTime_ae hV, A.sourceVelocityTwo_ae hV,
    A.family_norm_le hV⟩

end ParabolicDerivativeIndex

end HypoellipticAleksandrov.Parabolic
