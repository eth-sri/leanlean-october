module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz

open private HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex.coordinateList_add_single_perm from HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz


/-!
# Germ-local time--velocity multi-index calculus

This module proves the pointwise product and successor-coordinate rules from
finite `ContDiffAt` hypotheses. Its auxiliary directional and block evaluators
are private proof devices; the public derivative remains `coordinateIteratedFDeriv`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {d : ℕ}

private def LocalBlockSplit {C : Type*} (beta : C → ℕ) : List C → Type
  | [] => PUnit
  | c :: cs => Fin (beta c + 1) × LocalBlockSplit beta cs

private instance {C : Type*} (beta : C → ℕ) (cs : List C) :
    Fintype (LocalBlockSplit beta cs) := by
  induction cs with
  | nil => simp [LocalBlockSplit]; infer_instance
  | cons c cs ih => simp [LocalBlockSplit]; infer_instance

private def localDirs : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | v :: vs, f => fun z => fderiv ℝ (localDirs vs f) z v

private theorem localDirs_append (xs ys : List E) (f : E → ℝ) :
    localDirs (xs ++ ys) f = localDirs xs (localDirs ys f) := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, localDirs]; rw [ih]

private theorem localDirs_ofFn_eq_iteratedFDeriv (n : ℕ) (v : Fin n → E)
    (f : E → ℝ) (z : E) (hf : ContDiffAt ℝ n f z) :
    localDirs (List.ofFn v) f z = iteratedFDeriv ℝ n f z v := by
  induction n generalizing f z with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ, localDirs, iteratedFDeriv_succ_apply_left]
      have hfun : localDirs (List.ofFn fun i => v i.succ) f =ᶠ[nhds z] fun y =>
          iteratedFDeriv ℝ n f y fun i => v i.succ := by
        filter_upwards [hf.eventually (by simp)] with y hy
        exact ih (fun i => v i.succ) f y (hy.of_le
          (show (n : WithTop ℕ∞) ≤ n + 1 by simp))
      change (fderiv ℝ (localDirs (List.ofFn fun i => v i.succ) f) z) (v 0) = _
      rw [hfun.fderiv_eq]

      rw [fderiv_continuousMultilinear_apply_const_apply (hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n))]
      rfl

private theorem localDirs_contDiffAt (l : List E) (m : ℕ) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ (m + l.length) f z) : ContDiffAt ℝ m (localDirs l f) z := by
  induction l generalizing m f with
  | nil => exact hf
  | cons v l ih =>
      rw [localDirs]
      have h : ContDiffAt ℝ (m + 1) (localDirs l f) z := by
        apply ih
        convert hf using 1
        norm_num
        exact_mod_cast (show (m + 1) + l.length = m + (l.length + 1) by omega)
      exact (h.fderiv_right (by norm_num)).clm_apply contDiffAt_const

private theorem localDirectional_comm (a b : E) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ 2 f z) :
    fderiv ℝ (fun y => fderiv ℝ f y a) z b =
      fderiv ℝ (fun y => fderiv ℝ f y b) z a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const a),
    fderiv_clm_apply hd (differentiableAt_const b)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.isSymmSndFDerivAt (by simp)).eq b a

private theorem localDirs_perm {l₁ l₂ : List E} (hperm : l₁.Perm l₂)
    (f : E → ℝ) (z : E) (hf : ContDiffAt ℝ l₁.length f z) :
    localDirs l₁ f z = localDirs l₂ f z := by
  induction hperm generalizing f z with
  | nil => rfl
  | @cons a l₁ l₂ hperm ih =>
      simp only [localDirs]

      exact congrArg (fun L : E →L[ℝ] ℝ => L a) (show localDirs l₁ f =ᶠ[nhds z] localDirs l₂ f by
          filter_upwards [hf.eventually (by simp)] with y hy
          exact ih f y (hy.of_le (by simp))).fderiv_eq
  | @swap a b l =>
      simp only [localDirs]
      apply localDirectional_comm
      apply localDirs_contDiffAt l 2 f z
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hf
  | @trans l₁ l₂ l₃ h₁₂ h₂₃ ih₁₂ ih₂₃ =>
      exact (ih₁₂ f z hf).trans (ih₂₃ f z (h₁₂.length_eq ▸ hf))

variable (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d)




variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) (hf : ContDiffAt ℝ (beta.order + 1) f z)

include hf
/-- Adding one coordinate differentiates the associated coordinate derivative
at a point under the exact finite germ-local regularity. -/
theorem coordinateIteratedFDeriv_add_single_at

     :
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
      fderiv ℝ (coordinateIteratedFDeriv beta f) z
        (timeVelocityBasis c) := by
  let vecList (alpha : TimeVelocityMultiIndex d)  :=
    alpha.coordinateList.map timeVelocityBasis
  have eval_dirs (alpha : TimeVelocityMultiIndex d) (y : TimeVelocity d)
      (ha : ContDiffAt ℝ alpha.order f y) :
      coordinateIteratedFDeriv alpha f y = localDirs (vecList alpha) f y := by
    unfold coordinateIteratedFDeriv
    have hlist : vecList alpha = List.ofFn (fun i =>
        timeVelocityBasis (alpha.coordinateList.get i)) := by
      symm
      simpa [vecList, Function.comp_def] using congrArg (List.map timeVelocityBasis)
        (List.ofFn_get alpha.coordinateList)
    rw [hlist, localDirs_ofFn_eq_iteratedFDeriv]
    simpa

  calc
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
        localDirs (vecList (beta + Pi.single c 1)) f z :=
      eval_dirs _ _ (by simpa using hf)
    _ = localDirs (timeVelocityBasis c :: vecList beta) f z := by
      apply localDirs_perm ((_root_.HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex.coordinateList_add_single_perm beta c).map timeVelocityBasis) f z
      simpa [vecList] using hf
    _ = fderiv ℝ (coordinateIteratedFDeriv beta f) z (timeVelocityBasis c) := by
      simp only [localDirs]

      exact congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L (timeVelocityBasis c))
        (show localDirs (vecList beta) f =ᶠ[nhds z]
          coordinateIteratedFDeriv beta f by
            filter_upwards [hf.eventually (by simp)] with y hy
            exact (eval_dirs beta y (hy.of_le (by simp))).symm).fderiv_eq

/-- A coordinate derivative composed before a coordinate multi-index agrees
with addition of that coordinate, under exact finite germ-local regularity. -/
theorem coordinateIteratedFDeriv_comp_single_at

     :
    coordinateIteratedFDeriv beta
        (coordinateIteratedFDeriv (Pi.single c 1) f) z =
      coordinateIteratedFDeriv (beta + Pi.single c 1) f z := by
  let vecList (alpha : TimeVelocityMultiIndex d)  :=
    alpha.coordinateList.map timeVelocityBasis
  have eval_dirs (alpha : TimeVelocityMultiIndex d) (g : HypoellipticAleksandrov.Parabolic.ScalarField d)
      (y : TimeVelocity d) (hg : ContDiffAt ℝ alpha.order g y) :
      coordinateIteratedFDeriv alpha g y = localDirs (vecList alpha) g y := by
    unfold coordinateIteratedFDeriv
    have hlist : vecList alpha = List.ofFn (fun i =>
        timeVelocityBasis (alpha.coordinateList.get i)) := by
      symm
      simpa [vecList, Function.comp_def] using congrArg (List.map timeVelocityBasis)
        (List.ofFn_get alpha.coordinateList)
    rw [hlist, localDirs_ofFn_eq_iteratedFDeriv]
    simpa


  have hsinglePerm : (vecList (Pi.single c 1)).Perm [timeVelocityBasis c] := by
    have h := (_root_.HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex.coordinateList_add_single_perm
      (0 : TimeVelocityMultiIndex d) c).map timeVelocityBasis
    simpa [vecList] using h

  calc
    coordinateIteratedFDeriv beta
        (coordinateIteratedFDeriv (Pi.single c 1) f) z =
        coordinateIteratedFDeriv beta
          (localDirs (vecList (Pi.single c 1)) f) z := coordinateIteratedFDeriv_congr_of_eventuallyEq beta (by
              filter_upwards [hf.eventually (by simp)] with y hy
              exact eval_dirs (Pi.single c 1) f y (by
                apply hy.of_le
                simp only [order_single, Nat.cast_one]
                exact le_add_self))
    _ = localDirs (vecList beta)
        (localDirs (vecList (Pi.single c 1)) f) z :=
      eval_dirs beta _ z (by
          apply localDirs_contDiffAt
          simpa [vecList, add_comm] using hf)
    _ = localDirs (vecList beta ++ vecList (Pi.single c 1)) f z := by
      rw [localDirs_append]
    _ = localDirs (vecList (beta + Pi.single c 1)) f z := by
      apply localDirs_perm (by

          exact (hsinglePerm.append_left (vecList beta)).trans
            (List.perm_append_comm.trans (((_root_.HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex.coordinateList_add_single_perm beta c).map timeVelocityBasis).symm))) f z
      simpa [vecList] using hf
    _ = coordinateIteratedFDeriv (beta + Pi.single c 1) f z := by
      symm
      apply eval_dirs
      simpa using hf

end HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
