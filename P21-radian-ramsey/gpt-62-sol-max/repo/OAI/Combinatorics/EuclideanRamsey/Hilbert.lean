/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/FiniteEuclidean.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public section

open scoped RealInnerProductSpace
open Function
noncomputable section
namespace OAI.EuclideanRamsey

abbrev Hilbert := lp (fun _ : ℕ => ℝ) 2

namespace Hilbert
private lemma extend_norm {α β : Type*} (f : α → β) (x : α → ℝ) :
    (fun i => ‖extend f x 0 i‖ ^ (2:ℝ)) = extend f (fun i => ‖x i‖ ^ (2:ℝ)) 0 := by
  funext i
  simpa [Function.comp_def, Pi.zero_def] using apply_extend (g:=x) (fun t : ℝ => ‖t‖ ^ (2:ℝ)) f 0 i

private lemma two_pos : 0 < (2 : ENNReal).toReal := by simp

def extendIsometry {α β : Type*} (f : α → β) (hf : Injective f) :
    lp (fun _ : α => ℝ) 2 →ₗᵢ[ℝ] lp (fun _ : β => ℝ) 2 where
  toFun x := ⟨extend f x 0, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, extend_norm, summable_extend_zero hf] using (lp.memℓp x).summable two_pos⟩
  map_add' x y := Subtype.ext ((ExtendByZero.linearMap ℝ f).map_add (⇑x) (⇑y))
  map_smul' c x := Subtype.ext ((ExtendByZero.linearMap ℝ f).map_smul c (⇑x))
  norm_map' x := by
    simp only [lp.norm_eq_tsum_rpow two_pos, ENNReal.toReal_ofNat]
    change (∑' j, ‖extend f x 0 j‖ ^ (2:ℝ)) ^ (1/2:ℝ) = _
    rw [extend_norm,tsum_extend_zero hf]

def embed (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι →ₗᵢ[ℝ] Hilbert :=
  (extendIsometry (fun i : ι => (Fintype.equivFin ι i : ℕ))
    (Fin.val_injective.comp (Fintype.equivFin ι).injective)).comp
    (lpPiLpₗᵢ (p:=2) (fun _ : ι => ℝ) ℝ).symm.toLinearIsometry

def block (j : ℕ) : Hilbert →ₗᵢ[ℝ] Hilbert :=
  extendIsometry (Nat.pair j) fun _ _ h => (Nat.pair_eq_pair.mp h).2

private lemma blocks_orthogonal (x y : Hilbert) : ⟪block 0 x,block 1 y⟫ = 0 := by
  rw [lp.inner_eq_tsum]
  refine (tsum_congr (g := fun _ => 0) fun t => ?_).trans tsum_zero
  change ⟪extend (Nat.pair 0) x 0 t,extend (Nat.pair 1) y 0 t⟫ = 0
  by_cases h : t ∈ Set.range (Nat.pair 0)
  · obtain ⟨u,rfl⟩ := h
    simp
  · simp [extend_apply' _ _ _ h]

def flatten : List Hilbert → Hilbert
  | [] => 0
  | x :: l => block 0 x + block 1 (flatten l)

lemma flatten_cons_dist (x y : Hilbert) (l k : List Hilbert) :
    ‖flatten (x :: l)-flatten (y :: k)‖^2 = ‖x-y‖^2 + ‖flatten l-flatten k‖^2 := by
  simp [flatten,add_sub_add_comm,← map_sub,norm_add_sq_real,blocks_orthogonal]

lemma flatten_append_dist (l k l' k' : List Hilbert) (h : l.length=k.length) :
    ‖flatten (l++l')-flatten (k++k')‖^2 = ‖flatten l-flatten k‖^2 + ‖flatten l'-flatten k'‖^2 := by
  induction l generalizing k with
  | nil => cases k <;> simp_all
  | cons x l ih =>
    cases k with
    | nil => simp at h
    | cons y k =>
      simp only [List.cons_append,flatten_cons_dist,ih _ (by simpa using h),add_assoc]

end Hilbert

end OAI.EuclideanRamsey
end
