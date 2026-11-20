module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz

/-!
# Germ-local time--velocity multi-index calculus

This module proves the pointwise product and successor-coordinate rules from
finite `ContDiffAt` hypotheses. Its auxiliary directional and block evaluators
are private proof devices; the public derivative remains `coordinateIteratedFDeriv`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {d : ℕ}

private def localDirs : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | v :: vs, f => fun z => fderiv ℝ (localDirs vs f) z v

section
variable (n : ℕ) (xs ys : List E) (a b : E) (l : List E) {l₁ l₂ : List E} (v : Fin n → E) (m : ℕ)
    (hperm : l₁.Perm l₂) (f : E → ℝ) (z : E)

private theorem localDirs_ofFn_eq_iteratedFDeriv (hf : ContDiffAt ℝ n f z) :
    localDirs (List.ofFn v) f z = iteratedFDeriv ℝ n f z v := by
  induction n generalizing f z with
  | zero => simp [localDirs]
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

private theorem localDirs_contDiffAt
    (hf : ContDiffAt ℝ (m + l.length) f z) : ContDiffAt ℝ m (localDirs l f) z := by
  induction l generalizing m f with
  | nil => exact hf
  | cons v l ih =>
      rw [localDirs]
      have h : ContDiffAt ℝ (m + 1) (localDirs l f) z := by
        apply ih
        convert hf using 1
        exact_mod_cast (show (m + 1) + l.length = m + (l.length + 1) by omega)
      fun_prop

private theorem localDirectional_comm
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

include hperm in
private theorem localDirs_perm (hf : ContDiffAt ℝ l₁.length f z) :
    localDirs l₁ f z = localDirs l₂ f z := by
  induction hperm generalizing f z with
  | nil => rfl
  | @cons a l₁ l₂ hperm ih =>
      simp only [localDirs]
      have heq : localDirs l₁ f =ᶠ[nhds z] localDirs l₂ f := by
        filter_upwards [hf.eventually (by simp)] with y hy
        exact ih f y (hy.of_le (by simp))
      exact congrArg (fun L : E →L[ℝ] ℝ => L a) heq.fderiv_eq
  | @swap a b l =>
      simp only [localDirs]
      apply localDirectional_comm
      apply localDirs_contDiffAt l 2 f z
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hf
  | @trans l₁ l₂ l₃ h₁₂ h₂₃ ih₁₂ ih₂₃ =>
      exact (ih₁₂ f z hf).trans (ih₂₃ f z (h₁₂.length_eq ▸ hf))

end

variable (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d) (f : TimeVelocity d → ℝ)
    (z : TimeVelocity d) (hf : ContDiffAt ℝ (beta.order + 1) f z)

private theorem coordinateList_add_single_perm_local :
    (beta + Pi.single c 1).coordinateList.Perm (c :: beta.coordinateList) := by
  classical
  letI : BEq (TimeVelocityCoord d) := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq (TimeVelocityCoord d) := ⟨by simp⟩
  rw [List.perm_iff_count]
  intro a
  have count_flat (q : TimeVelocityMultiIndex d) : ∀ l : List (TimeVelocityCoord d),
      l.Nodup → List.count a (l.flatMap fun b => List.replicate (q b) b) =
        if a ∈ l then q a else 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons b l ih =>
        grind
  unfold coordinateList
  rw [count_flat _ _ (Finset.nodup_toList Finset.univ)]
  simp only [List.count_cons]
  rw [count_flat _ _ (Finset.nodup_toList Finset.univ)]
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.add_apply]
  congr 1
  by_cases h : c = a
  · subst a
    simp
  simp_all

include hf in
/-- Adding one coordinate differentiates the associated coordinate derivative
at a point under the exact finite germ-local regularity. -/
theorem coordinateIteratedFDeriv_add_single_at :
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
      fderiv ℝ (coordinateIteratedFDeriv beta f) z
        (timeVelocityBasis c) := by
  let vecList (alpha : TimeVelocityMultiIndex d) : List (TimeVelocity d) :=
    alpha.coordinateList.map timeVelocityBasis
  have eval_dirs (alpha : TimeVelocityMultiIndex d) (y : TimeVelocity d)
      (ha : ContDiffAt ℝ alpha.order f y) :
      coordinateIteratedFDeriv alpha f y = localDirs (vecList alpha) f y := by
    unfold coordinateIteratedFDeriv
    have hlist : vecList alpha = List.ofFn (fun i =>
        timeVelocityBasis (alpha.coordinateList.get i)) := by
      symm
      simpa [Function.comp_def] using congrArg (List.map timeVelocityBasis)
        (List.ofFn_get alpha.coordinateList)
    rw [hlist, localDirs_ofFn_eq_iteratedFDeriv]
    simpa using ha
  have hperm : (vecList (beta + Pi.single c 1)).Perm
      (timeVelocityBasis c :: vecList beta) := by
    exact (coordinateList_add_single_perm_local beta c).map timeVelocityBasis
  calc
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
        localDirs (vecList (beta + Pi.single c 1)) f z :=
      eval_dirs _ _ (by simpa using hf)
    _ = localDirs (timeVelocityBasis c :: vecList beta) f z := by
      apply localDirs_perm hperm f z
      simpa [vecList] using hf
    _ = fderiv ℝ (coordinateIteratedFDeriv beta f) z (timeVelocityBasis c) := by
      simp only [localDirs]
      have hfun : localDirs (vecList beta) f =ᶠ[nhds z]
          coordinateIteratedFDeriv beta f := by
        filter_upwards [hf.eventually (by simp)] with y hy
        exact (eval_dirs beta y (hy.of_le (by simp))).symm
      exact congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L (timeVelocityBasis c))
        hfun.fderiv_eq

end HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
