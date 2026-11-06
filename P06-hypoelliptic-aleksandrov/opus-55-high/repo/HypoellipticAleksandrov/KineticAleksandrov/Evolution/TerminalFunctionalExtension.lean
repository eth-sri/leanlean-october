module

import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Positive extension of a sup-norm bounded functional from a dense probe space

Abstract extension principle used for Let `T : P → C_c(X, ℝ)` be a linear map with
uniformly dense range closed under squaring, and `s : P → ℝ` a linear functional which is
bounded by the sup norm of `T F` and nonnegative on nonnegative `T F`.  Then `s` factors
through a positive linear functional on `C_c(X, ℝ)` bounded by the sup norm; two sup-norm
bounded functionals agreeing on the range of `T` coincide.

There is no norm instance on `C_c(X, ℝ)` in Mathlib, so the sup norm enters through the
seminorm `ccSupSeminorm`, pulled back from `X →ᵇ ℝ`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open scoped CompactlySupported BoundedContinuousFunction
open CompactlySupportedContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- The inclusion of `C_c(X, ℝ)` into bounded continuous functions, as a linear map. -/
def ccToBcfLinear : C_c(X, ℝ) →ₗ[ℝ] (X →ᵇ ℝ) where
  toFun f := f.toBoundedContinuousFunction
  map_add' f g := by rfl
  map_smul' c f := by rfl

/-- The sup norm of a compactly supported continuous function, as a seminorm. -/
def ccSupSeminorm : Seminorm ℝ C_c(X, ℝ) :=
  (normSeminorm ℝ (X →ᵇ ℝ)).comp ccToBcfLinear

variable (f : C_c(X, ℝ))

/-- A compactly supported function is pointwise bounded by its sup seminorm. -/
theorem abs_apply_le_ccSupSeminorm  (x : X) : |f x| ≤ ccSupSeminorm f :=
  BoundedContinuousFunction.norm_coe_le_norm (f.toBoundedContinuousFunction) x

/-- The sup seminorm is nonnegative. -/
theorem ccSupSeminorm_nonneg  : 0 ≤ ccSupSeminorm f :=
  norm_nonneg (f.toBoundedContinuousFunction)

/-- A uniform bound dominates the sup seminorm. -/
theorem ccSupSeminorm_le {f : C_c(X, ℝ)} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, |f x| ≤ c) :
    ccSupSeminorm f ≤ c :=
  (BoundedContinuousFunction.norm_le hc).2 h

/-- Two functionals bounded by the sup norm and agreeing on a uniformly dense family agree. -/
theorem eq_of_bounded_of_dense {P : Type*} (T : P → C_c(X, ℝ))
    (ℓ₁ ℓ₂ : C_c(X, ℝ) →ₗ[ℝ] ℝ)
    (h₁ : ∀ f c, 0 ≤ c → (∀ x, |f x| ≤ c) → |ℓ₁ f| ≤ c)
    (h₂ : ∀ f c, 0 ≤ c → (∀ x, |f x| ≤ c) → |ℓ₂ f| ≤ c)
    (hagree : ∀ F, ℓ₁ (T F) = ℓ₂ (T F))
    (hdense : ∀ f : C_c(X, ℝ), ∀ ε : ℝ, 0 < ε → ∃ F, ∀ x, |T F x - f x| ≤ ε) :
    ℓ₁ = ℓ₂ := by
  refine LinearMap.ext fun f => ?_
  have key : ∀ ε : ℝ, 0 < ε → |ℓ₁ f - ℓ₂ f| ≤ 2 * ε := by
    intro ε hε
    obtain ⟨F, hF⟩ := hdense f ε hε
    have e₁ := h₁ (f - T F) ε hε.le (fun x => by
      rw [CompactlySupportedContinuousMap.sub_apply, abs_sub_comm]; grind)
    have e₂ := h₂ (f - T F) ε hε.le (fun x => by
      rw [CompactlySupportedContinuousMap.sub_apply, abs_sub_comm]; grind)
    grind
  have : |ℓ₁ f - ℓ₂ f| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (ε / 2) (half_pos hε)
    linarith
  grind

/-- Positive extension from a dense probe family closed under squaring. -/
theorem exists_positive_extension_of_dense {P : Type*} [AddCommGroup P] [Module ℝ P]
    (T : P →ₗ[ℝ] C_c(X, ℝ)) (s : P →ₗ[ℝ] ℝ)
    (hbd : ∀ F c, 0 ≤ c → (∀ x, |T F x| ≤ c) → |s F| ≤ c)
    (hpos : ∀ F, (∀ x, 0 ≤ T F x) → 0 ≤ s F)
    (hsq : ∀ F, ∃ G, T G = T F * T F)
    (hdense : ∀ f : C_c(X, ℝ), ∀ ε : ℝ, 0 < ε → ∃ F, ∀ x, |T F x - f x| ≤ ε) :
    ∃ ℓ : C_c(X, ℝ) →ₚ[ℝ] ℝ,
      (∀ f c, 0 ≤ c → (∀ x, |f x| ≤ c) → |ℓ f| ≤ c) ∧ ∀ F, ℓ (T F) = s F := by
  have hker : LinearMap.ker T ≤ LinearMap.ker s := by
    intro F hF
    have hT : T F = 0 := hF
    have := hbd F 0 le_rfl (fun x => by simp [hT])
    exact abs_nonpos_iff.mp this
  let ℓ₀ : LinearMap.range T →ₗ[ℝ] ℝ :=
    ((LinearMap.ker T).liftQ s hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hℓ₀ : ∀ F, ℓ₀ ⟨T F, LinearMap.mem_range_self T F⟩ = s F := by
    aesop
  have hp : ∀ d : LinearMap.range T, ℓ₀ d ≤ ccSupSeminorm (d : C_c(X, ℝ)) := by
    rintro ⟨_, F, rfl⟩
    rw [hℓ₀]
    exact (le_abs_self _).trans
      (hbd F _ (ccSupSeminorm_nonneg _) (fun x => abs_apply_le_ccSupSeminorm _ x))
  obtain ⟨g, hg, hgp⟩ := Module.Dual.exists_extension_of_le_seminorm_real
    (LinearMap.range T) ℓ₀ hp
  have hgT : ∀ F, g (T F) = s F := fun F => by
    grind
  have hgbd : ∀ f c, 0 ≤ c → (∀ x, |f x| ≤ c) → |g f| ≤ c := fun f c hc h =>
    (hgp f).trans (ccSupSeminorm_le hc h)
  have hgpos : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ g f := by
    intro f hf
    let k  := f.compLeft ⟨Real.sqrt, Real.continuous_sqrt⟩
    have hk : ∀ x, k x = Real.sqrt (f x) := fun x =>
      compLeft_apply (g := ⟨Real.sqrt, Real.continuous_sqrt⟩) (by simp) f x
    have hkk : ∀ x, k x * k x = f x := fun x => by
      simp_all
    set M : ℝ := ccSupSeminorm k with hM
    have hM0 : 0 ≤ M := ccSupSeminorm_nonneg _
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set δ : ℝ := min 1 (ε / (2 * M + 1)) with hδ
    have hδ0 : 0 < δ := lt_min one_pos (div_pos hε (by linarith))
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδε : δ * (2 * M + 1) ≤ ε := by
      have : δ ≤ ε / (2 * M + 1) := min_le_right _ _
      calc δ * (2 * M + 1) ≤ ε / (2 * M + 1) * (2 * M + 1) :=
            mul_le_mul_of_nonneg_right this (by linarith)
        _ = ε := by field_simp
    obtain ⟨F, hF⟩ := hdense k δ hδ0
    obtain ⟨G, hG⟩ := hsq F
    have hGx : ∀ x, T G x = T F x * T F x := fun x => by simp_all
    have hbound : ∀ x, |f x - T G x| ≤ δ * (2 * M + 1) := by
      intro x
      have h1  := hF x
      have h2 : |k x| ≤ M := abs_apply_le_ccSupSeminorm k x
      have h3 : |T F x + k x| ≤ 2 * M + 1 := by
        grind
      have h4 : f x - T G x = (k x - T F x) * (k x + T F x) := by
        grind
      rw [h4, abs_mul, abs_sub_comm, add_comm]
      exact mul_le_mul h1 h3 (abs_nonneg _) hδ0.le
    have hgGp : 0 ≤ g (T G) := by
      rw [hgT]; exact hpos G (fun x => by rw [hGx]; exact mul_self_nonneg _)
    have hrest' : |g _| ≤ ε :=
      (hgbd (f - T G) _ (by positivity) (fun x => by
        simp_all)).trans hδε
    have hsplit : g f = g (T G) + g (f - T G) := by simp
    have hneg : -ε ≤ g _ := (neg_le_neg hrest').trans (neg_abs_le _)
    linarith
  have hnn : ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ g f := fun f hf =>
    hgpos f (fun x => by aesop)
  exact ⟨PositiveLinearMap.mk₀ g hnn, hgbd, hgT⟩

end HypoellipticAleksandrov.KineticAleksandrov
