module

public import Erdos821.S2.HighRankTask
public import Erdos821.P3LowRank.LowRank
public import Erdos821.P3High.PathSum

/-! Absolute truncated history sums with real local multipliers are finite real path sums. -/

@[expose] public section

set_option autoImplicit false

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3High

open Erdos821.Blueprint.Graph hiding permuteActive
open Erdos821.S2Core Erdos821.P3Lowrank

attribute [local instance] bmsFintype ghostChoiceFintype edgeChoiceFintype

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Absolute ghost kernel with a real multiplier on each local choice. -/
def ghostK (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (φ : (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ)
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  if s.1 = t.1 ∧ s.2.1 = t.2.1 then
    ∑ c : GhostChoice s t, if ghostChoiceValid c then |ghostChoiceWeight F n rho i c| * φ s t c
      else 0
  else 0

/-- Absolute edge kernel with a real multiplier on each local choice. -/
def edgeK (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (φ : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ)
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s,
    if edgeChoiceValid A .all i s t c then
      ‖edgeChoiceCoefficient A n rho theta i s t c‖ * φ s t c else 0

theorem norm_weight_eq {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n) (rho theta : ℝ) :
    ‖H.Weight rho theta‖ = |P.memoryMass F J n (H.before 0)| *
      (∏ i, |ghostChoiceWeight F n rho i (H.ghost i)|) *
      ∏ i, (edgeSymmetryFactor P (J + F.ell) *
        ‖edgeChoiceCoefficient A n rho theta i (H.after i.castSucc) (H.before i.succ)
          (H.edge i)‖) := by
  simp only [S2Core.MemoryHistory.Weight, norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (edgeSymmetryFactor_nonneg P (J + F.ell))]

/-- Exact absolute choice expansion for one fixed state path. -/
theorem abs_choice_sum (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (Φ0 : P.MemoryState (J + F.ell) → ℝ)
    (φG : Fin (n + 1) → (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ)
    (φE : Fin n → (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ)
    (bf af : Fin (n + 1) → P.MemoryState (J + F.ell)) :
    ∑ c1 : (i : Fin (n + 1)) → GhostChoice (bf i) (af i),
      ∑ c2 : (i : Fin n) → EdgeChoice A (af i.castSucc),
        (if (⟨bf, af, c1, c2⟩ : MemoryHistory A n).Valid then
          ‖(⟨bf, af, c1, c2⟩ : MemoryHistory A n).Weight rho theta‖ *
            localFactor A n Φ0 φG φE ⟨bf, af, c1, c2⟩ else 0) =
      (if ∀ g, (bf 0).2.2 g = 0 then |P.memoryMass F J n (bf 0)| * Φ0 (bf 0) else 0) *
        (∏ i, ghostK F J n rho i (φG i) (bf i) (af i)) *
        (∏ i : Fin n, edgeK A n rho theta i (φE i) (af i.castSucc) (bf i.succ)) *
        (if ∀ g, (af (Fin.last n)).2.2 g = 0 then (1 : ℝ) else 0) := by
  convert choice_sum_factorized A n bf af (|P.memoryMass F J n (bf 0)| * Φ0 (bf 0)) (edgeSymmetryFactor P (J + F.ell))
    (fun i c => |ghostChoiceWeight F n rho i c| * φG i (bf i) (af i) c)
    (fun i c => ‖edgeChoiceCoefficient A n rho theta i (af i.castSucc) (bf i.succ) c‖ * φE i (af i.castSucc) (bf i.succ) c) using 1
  · refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
    split_ifs
    · simp only [norm_weight_eq, localFactor, Finset.prod_mul_distrib]
      ring
    · rfl
  · have hg (i : Fin (n + 1)) :
        (∑ c : GhostChoice (bf i) (af i),
          if ((bf i).1 = (af i).1 ∧ (bf i).2.1 = (af i).2.1) ∧ ghostChoiceValid c then
            |ghostChoiceWeight F n rho i c| * φG i (bf i) (af i) c else 0) =
        ghostK F J n rho i (φG i) (bf i) (af i) := by
      unfold ghostK
      exact sum_guard ((bf i).1 = (af i).1 ∧ (bf i).2.1 = (af i).2.1)
        (fun c : GhostChoice (bf i) (af i) => ghostChoiceValid c)
        (fun c => |ghostChoiceWeight F n rho i c| * φG i (bf i) (af i) c)
    simp only [hg, edgeK, Finset.mul_sum, mul_ite, mul_zero]

/-- The bounded history sum is the real path sum of the multiplied absolute kernels. -/
theorem history_sum_eq (A : Model F P J m) (n B : ℕ) (rho theta : ℝ)
    (Φ0 : P.MemoryState (J + F.ell) → ℝ)
    (φG : Fin (n + 1) → (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ)
    (φE : Fin n → (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ) :
    (∑ d : BoundedHistoryData A n B,
      (if (mkH d).Valid then ‖(mkH d).Weight rho theta‖ * localFactor A n Φ0 φG φE (mkH d)
        else 0)) =
      pathSum n (fun i (s t : BoundedMemoryState P (J + F.ell) B) =>
          ghostK F J n rho i (φG i) s.val t.val)
        (fun i (s t : BoundedMemoryState P (J + F.ell) B) =>
          edgeK A n rho theta i (φE i) s.val t.val)
        (fun s => if ∀ g, s.val.2.2 g = 0 then |P.memoryMass F J n s.val| * Φ0 s.val else 0)
        (fun s => if ∀ g, s.val.2.2 g = 0 then 1 else 0) := by
  unfold pathSum
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  exact abs_choice_sum A n rho theta Φ0 φG φE (fun i => (b i).val) (fun i => (a i).val)

theorem ghostK_nonneg (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    (φ : (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℝ)
    (hφ : ∀ s t c, 0 ≤ φ s t c) (s t : P.MemoryState (J + F.ell)) :
    0 ≤ ghostK F J n rho i φ s t := by
  unfold ghostK
  split_ifs
  · exact Finset.sum_nonneg fun c _ => by
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (hφ s t c)
      · exact le_rfl
  · exact le_rfl

theorem edgeK_nonneg (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (φ : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ)
    (hφ : ∀ s t c, 0 ≤ φ s t c) (s t : P.MemoryState (J + F.ell)) :
    0 ≤ edgeK A n rho theta i φ s t := by
  unfold edgeK
  apply mul_nonneg (edgeSymmetryFactor_nonneg P (J + F.ell))
  exact Finset.sum_nonneg fun c _ => by
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (hφ s t c)
    · exact le_rfl

end Erdos821.P3High
