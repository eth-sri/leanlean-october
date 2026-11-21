module

public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates.Raw

open MeasureTheory
open KPContLocalNorm

def zeroIndex (n k : ℕ) : MultiIndex n k := ⟨fun _ => 0, by simp⟩

def firstIndex {n : ℕ} (i : Fin n) : MultiIndex n 1 :=
  ⟨fun j => if j = i then 1 else 0, by
    simp only [apply_ite Fin.val, Fin.val_one, Fin.val_zero]
    simp⟩

theorem zero_dirs (n k : ℕ) : (zeroIndex n k).directions = [] := by
  simp [MultiIndex.directions, zeroIndex]
theorem first_dirs {n : ℕ} (i : Fin n) : (firstIndex i).directions = [i] := by
  classical
  simp only [MultiIndex.directions, firstIndex, apply_ite Fin.val, Fin.val_one,
    Fin.val_zero, List.replicate_one, List.replicate_zero]
  have h : ∀ l : List (Fin n), l.flatMap (fun j => if j = i then [j] else []) = l.filter (· = i) := by
    intro l; induction l with
    | nil => rfl
    | cons j l ih => by_cases hj : j = i <;> simp [hj, ih]
  have hrep : ∀ j : Fin n, List.replicate (if j = i then 1 else 0) j =
      if j = i then [j] else [] := by intro j; split_ifs <;> simp
  simp_rw [hrep]
  rw [h, List.filter_eq]
  simp
theorem cases_idx {n : ℕ} (α : MultiIndex n 1) :
    α = zeroIndex n 1 ∨ ∃ i : Fin n, α = firstIndex i := by
  classical
  by_cases hz : ∀ i, (α.val i).val = 0
  · left; apply Subtype.ext; funext i; apply Fin.ext; exact hz i
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    right; refine ⟨i, ?_⟩
    have hs := Finset.sum_le_one_iff.mp α.property
    have hone := (hs i i (Finset.mem_univ _) (Finset.mem_univ _) hi hi).2
    apply Subtype.ext; funext j; apply Fin.ext
    by_cases hji : j = i
    · subst j; simpa [firstIndex] using hone
    · have hj : (α.val j).val = 0 := by
        by_contra hj
        exact hji (hs j i (Finset.mem_univ _) (Finset.mem_univ _) hj hi).1
      simpa [firstIndex, hji] using hj
theorem first_degree {n : ℕ} (i : Fin n) : (firstIndex i).degree = 1 := by
  simp only [firstIndex, MultiIndex.degree, apply_ite Fin.val, Fin.val_one, Fin.val_zero]
  simp
theorem first_ne_zero {n : ℕ} (i : Fin n) : firstIndex i ≠ zeroIndex n 1 := by
  intro h
  have he := congrArg (fun α : MultiIndex n 1 => (α.val i).val) h
  simpa [firstIndex, zeroIndex] using he
theorem first_inj {n : ℕ} : Function.Injective (@firstIndex n) := by
  intro i j h
  have he := congrArg (fun α : MultiIndex n 1 => (α.val i).val) h
  by_contra hij
  simpa [firstIndex, hij] using he

def value {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k) : BallL2 B :=
  u.derivatives (zeroIndex n k)

def gradient {n : ℕ} {B : LocalBall n} (u : IntegerSobolev B 1)
    (i : Fin n) : BallL2 B :=
  u.derivatives (firstIndex i)

structure Coefficients {n : ℕ} (B : LocalBall n) (cρ Cρ κ Λ : ℝ) where
  density : Space n → ℝ
  matrix : Space n → Matrix (Fin n) (Fin n) ℝ
  density_smooth : ContDiffOn ℝ (⊤ : ℕ∞) density B.carrier
  matrix_smooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => matrix x i j) B.carrier
  density_bounds : ∀ x ∈ B.carrier, cρ ≤ density x ∧ density x ≤ Cρ
  symmetric : ∀ x ∈ B.carrier, ∀ i j, matrix x i j = matrix x j i
  ellipticity : ∀ x ∈ B.carrier, ∀ ξ : Space n,
    κ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, matrix x i j * ξ i * ξ j
  upper_bound : ∀ x ∈ B.carrier, ∀ ξ : Space n,
    (∑ i, ∑ j, matrix x i j * ξ i * ξ j) ≤ Λ * ‖ξ‖ ^ 2

def divergenceOperator {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (u : Space n → ℂ) : Space n → ℂ :=
  fun x => -(D.density x : ℂ)⁻¹ * ∑ i,
    fderiv ℝ (fun y => (D.density y : ℂ) *
      ∑ j, (D.matrix y i j : ℂ) * coordinateDerivativeList [j] u y) x
        (EuclideanSpace.single i 1)

def WeakEquation {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev B 1) (h : BallL2 B) : Prop :=
  ∀ φ : TestFunction B.toOpens ℂ ⊤,
    (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in B.carrier, (D.density x : ℂ) * value u x * star (φ x)) =
        ∫ x in B.carrier, (D.density x : ℂ) * h x * star (φ x)

def Represents {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k)
    (f : Space n → ℂ) : Prop :=
  ∀ᵐ x ∂volume.restrict B.carrier, value u x = f x

def RepresentsClassicalDerivatives {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (f : Space n → ℂ) : Prop :=
  ∀ α : MultiIndex n k,
    ∀ᵐ x ∂volume.restrict B.carrier, u.derivatives α x = coordinateDerivative α f x

def functionL2Norm {n : ℕ} (B : LocalBall n) (f : Space n → ℂ) : ℝ :=
  Real.sqrt (∫ x in B.carrier, ‖f x‖ ^ 2)

end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates.Raw

end
