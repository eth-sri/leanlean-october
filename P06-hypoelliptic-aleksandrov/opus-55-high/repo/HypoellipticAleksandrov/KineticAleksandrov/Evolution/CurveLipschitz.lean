module

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.Convex.Segment
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# Finite-slab Lipschitz bounds for continuous piecewise `C¹` curves

Used in the proof of the companion paper, Proposition 2.1.  A continuous piecewise `C¹`
curve `γ : ℝ → Vec n` need not be globally Lipschitz, but it is Lipschitz (for the Euclidean
norm) on every compact interval `[a, τ]`.  We prove this by bounding the derivative on each
closed piece of the partition and gluing the pieces, and then extend the finite-slab curve
constantly past the endpoints, which gives a globally Lipschitz curve with the same constant.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set

/-- The Euclidean triangle inequality in the form `‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖`. -/
theorem vecEuclideanNorm_sub_le_add {n : ℕ} (x y z : PDE.Vec n) :
    PDE.vecEuclideanNorm (x - z) ≤
      PDE.vecEuclideanNorm (x - y) + PDE.vecEuclideanNorm (y - z) := by
  have h : x - z = (x - y) + (y - z) := by abel
  rw [h]
  exact PDE.vecEuclideanNorm_add_le _ _

/-- The Euclidean-norm Lipschitz property of a curve on an interval. -/
def CurveLipschitzOn {n : ℕ} (γ : ℝ → PDE.Vec n) (L : ℝ) (S : Set ℝ) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, PDE.vecEuclideanNorm (γ s - γ t) ≤ L * |s - t|

variable {n : ℕ} {γ : ℝ → PDE.Vec n}

/-- Lipschitz bounds on two adjacent intervals glue to the union interval. -/
theorem CurveLipschitzOn.glue  {L a c b : ℝ} (hac : a ≤ c)
    (hcb : c ≤ b) (h₁ : CurveLipschitzOn γ L (Icc a c)) (h₂ : CurveLipschitzOn γ L (Icc c b)) :
    CurveLipschitzOn γ L (Icc a b) := by
  have key : ∀ s t, s ∈ Icc a c → t ∈ Icc c b →
      PDE.vecEuclideanNorm (γ s - γ t) ≤ L * |s - t| := by
    intro s t hs ht
    have h1 := h₁ s hs c ⟨hac, le_rfl⟩
    have h2 := h₂ c ⟨le_rfl, hcb⟩ t ht
    have e1 : |s - c| = c - s := by grind
    have e2 : |c - t| = t - c := by grind
    have e3 : |s - t| = t - s := by
      grind
    rw [e1] at h1
    rw [e2] at h2
    rw [e3]
    have := vecEuclideanNorm_sub_le_add (γ s) (γ c) (γ t)
    nlinarith
  intro s hs t ht
  by_cases hsc : s ≤ c
  · by_cases htc : t ≤ c
    · aesop
    grind
  · by_cases htc : t ≤ c
    · rw [PDE.vecEuclideanNorm_sub_comm, abs_sub_comm]
      grind
    · exact h₂ s ⟨(not_le.mp hsc).le, hs.2⟩ t ⟨(not_le.mp htc).le, ht.2⟩

/-- Weakening the constant. -/
theorem CurveLipschitzOn.mono_const  {L L' : ℝ} {S : Set ℝ}
    (h : CurveLipschitzOn γ L S) (hL : L ≤ L') : CurveLipschitzOn γ L' S := fun s hs t ht =>
  (h s hs t ht).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))

/-- A `C¹` curve on a compact interval is Lipschitz for the Euclidean norm there. -/
theorem exists_curveLipschitzOn_of_contDiffOn  {u v : ℝ}
    (h : ContDiffOn ℝ 1 γ (Icc u v)) :
    ∃ L : ℝ, 0 ≤ L ∧ CurveLipschitzOn γ L (Icc u v) := by
  obtain ⟨K, hK⟩ := h.exists_lipschitzOnWith one_ne_zero (convex_Icc u v) isCompact_Icc
  refine ⟨Real.sqrt n * K, by positivity, fun s hs t ht => ?_⟩
  have h1 := hK.dist_le_mul s hs t ht
  calc PDE.vecEuclideanNorm _ ≤ Real.sqrt n * ‖γ s - γ t‖ :=
        PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _
    _ ≤ Real.sqrt n * (K * |s - t|) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = Real.sqrt n * K * |s - t| := by ring

/-- (companion paper, 2.1).  A continuous piecewise `C¹` curve is Lipschitz, for the Euclidean
norm, on every finite interval `[a, τ]`. -/
theorem exists_evolution_curve_lipschitzOn
     (hγ : IsContinuousPiecewiseC1 γ)
    (a τ : ℝ) (haτ : a < τ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc a τ, ∀ t ∈ Icc a τ,
      PDE.vecEuclideanNorm (γ s - γ t) ≤ L * |s - t| := by
  obtain ⟨N, t, ht, h0, hl, hpiece⟩ := hγ.2 a τ haτ
  choose Lp hLp0 hLp using fun i : Fin _ => exists_curveLipschitzOn_of_contDiffOn (hpiece i)
  set L : ℝ := ∑ i, Lp i with hL
  have hLge : ∀ i, Lp i ≤ L := fun i =>
    Finset.single_le_sum (f := Lp) (fun j _ => hLp0 j) (Finset.mem_univ i)
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ => hLp0 j
  have hind : ∀ j : Fin _, CurveLipschitzOn γ L (Icc a (t j)) := by
    refine Fin.induction ?_ ?_
    · intro s hs u hu
      have hs' : s = a := le_antisymm (by simp_all) hs.1
      have hu' : u = a := le_antisymm (by simp_all) hu.1
      have h00 : PDE.vecEuclideanNorm (0 : PDE.Vec n) = 0 :=
        PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
      simp_all
    · intro i hi
      have hle : t i.castSucc ≤ t i.succ := (ht (Fin.castSucc_lt_succ)).le
      have hat : a ≤ t i.castSucc := by
        rw [← h0]; exact ht.monotone (Fin.zero_le _)
      exact CurveLipschitzOn.glue hat hle hi ((hLp i).mono_const (hLge i))
  aesop

/-- The constant extension of the finite-slab curve past the endpoints of `[a, τ]`. -/
def slabExtension {n : ℕ} (γ : ℝ → PDE.Vec n) (a τ : ℝ) (s : ℝ) : PDE.Vec n :=
  γ (max a (min τ s))

/-- The clamp `s ↦ max a (min τ s)` lands in `[a, τ]` when `a ≤ τ`. -/
theorem clamp_mem_Icc {a τ : ℝ} (h : a ≤ τ) (s : ℝ) : max a (min τ s) ∈ Icc a τ :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

/-- The clamp is `1`-Lipschitz. -/
theorem abs_clamp_sub_clamp_le (a τ s t : ℝ) :
    |max a (min τ s) - max a (min τ t)| ≤ |s - t| :=
  calc |max a _ - max a _| ≤ |min τ s - min τ t| := by
        grind
    _ ≤ max _ _ := abs_min_sub_min_le_max _ _ _ _
    _ = |s - t| := by simp

variable {n : ℕ} {γ : ℝ → PDE.Vec n}

/-- The slab extension agrees with the curve on `[a, τ]`. -/
theorem slabExtension_eq  (γ : ℝ → PDE.Vec n) {a τ s : ℝ} (hs : s ∈ Icc a τ) :
    slabExtension γ a τ s = γ s := by
  unfold slabExtension
  simp_all

/-- The slab extension of a continuous curve is continuous. -/
theorem continuous_slabExtension  (hγ : Continuous γ) (a τ : ℝ) :
    Continuous (slabExtension γ a τ) :=
  hγ.comp (continuous_const.max (continuous_const.min continuous_id))

/-- The slab extension of a curve that is `L`-Lipschitz on `[a, τ]` is globally `L`-Lipschitz. -/
theorem slabExtension_lipschitz  {a τ L : ℝ} (haτ : a ≤ τ)
    (hL : 0 ≤ L) (h : CurveLipschitzOn γ L (Icc a τ)) (s t : ℝ) :
    PDE.vecEuclideanNorm (slabExtension γ a τ s - slabExtension γ a τ t) ≤ L * |s - t| :=
  (h _ (clamp_mem_Icc haτ s) _ (clamp_mem_Icc haτ t)).trans
    (mul_le_mul_of_nonneg_left (abs_clamp_sub_clamp_le a τ s t) hL)

end HypoellipticAleksandrov.KineticAleksandrov
