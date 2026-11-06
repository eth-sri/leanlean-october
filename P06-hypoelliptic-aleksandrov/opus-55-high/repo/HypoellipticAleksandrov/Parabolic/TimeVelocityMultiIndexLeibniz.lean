module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Data.Nat.Choose.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Time--velocity multi-index derivatives

This file evaluates finite iterated Fréchet derivatives in the time--velocity
coordinate directions and proves their exact coordinatewise Leibniz formula.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex

open scoped BigOperators

variable {d : ℕ}

private def directionalFDeriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : E) (f : E → F) : E → F :=
  fun x => fderiv ℝ f x v

private def directionalFDerivs {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : List E → (E → F) → E → F
  | [], f => f
  | v :: l, f => directionalFDerivs l (directionalFDeriv v f)

private theorem contDiff_directionalFDeriv {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (v : E) (f : E → F) (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (directionalFDeriv v f) := (hf.fderiv_right (le_refl _)).clm_apply contDiff_const

private theorem directionalFDeriv_comm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : E) (f : E → F) (hf : ContDiff ℝ 2 f) :
    directionalFDeriv b (directionalFDeriv a f) =
      directionalFDeriv a (directionalFDeriv b f) := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  change fderiv ℝ (fun y => fderiv ℝ f y a) x b =
    fderiv ℝ (fun y => fderiv ℝ f y b) x a
  rw [fderiv_clm_apply hd (differentiableAt_const a),
    fderiv_clm_apply hd (differentiableAt_const b)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq b a

private theorem directionalFDerivs_congr {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : List E) {f g : E → F} (h : f = g) :
    directionalFDerivs l f = directionalFDerivs l g := by
  subst g
  rfl

private theorem directionalFDerivs_append {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l₁ l₂ : List E) (f : E → F) :
    directionalFDerivs (l₁ ++ l₂) f =
      directionalFDerivs l₂ (directionalFDerivs l₁ f) := by
  induction l₁ generalizing f with
  | nil => rfl
  | cons v l ih =>
      exact ih _

private theorem directionalFDerivs_eq_of_perm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l₁ l₂ : List E} (hperm : l₁.Perm l₂) (f : E → F)
    (hf : ContDiff ℝ l₁.length f) :
    directionalFDerivs l₁ f = directionalFDerivs l₂ f := by
  induction hperm generalizing f with
  | nil => rfl
  | @cons a l₁ l₂ hperm ih =>
      apply ih
      simpa using contDiff_directionalFDeriv a f hf
  | @swap a b l =>
      simp only [directionalFDerivs]
      apply directionalFDerivs_congr
      apply directionalFDeriv_comm
      apply hf.of_le
      simp only [List.length_cons]
      norm_cast
      omega
  | @trans l₁ l₂ l₃ h₁₂ h₂₃ ih₁₂ ih₂₃ =>
      exact (ih₁₂ f hf).trans (ih₂₃ f (h₁₂.length_eq ▸ hf))

private theorem directionalFDerivs_reverse_ofFn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (v : Fin n → E) (f : E → F) (z : E) (hf : ContDiff ℝ n f) :
    directionalFDerivs (List.ofFn v).reverse f z = iteratedFDeriv ℝ n f z v := by
  induction n generalizing f with
  | zero => simp [directionalFDerivs]
  | succ n ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat]
      simp only [directionalFDerivs]
      rw [ih]
      · calc
          _ = iteratedFDeriv ℝ n (fderiv ℝ f) z _
                _ :=
            iteratedFDeriv_clm_apply_const_apply
              (hc := hf.fderiv_right (by simp)) (hi := le_rfl)
          _ = _ := (iteratedFDeriv_succ_apply_right v).symm
      · exact contDiff_directionalFDeriv _ f hf

/-- The coordinate multiset of a multi-index, represented by the fixed `Finset.univ.toList`
coordinate order and repeated according to multiplicity. -/
def coordinateList (beta : TimeVelocityMultiIndex d) : List (TimeVelocityCoord d) :=
  (Finset.univ.toList).flatMap fun c => List.replicate (beta c) c

/-- The coordinatewise multinomial coefficient. -/
def choose (beta gamma : TimeVelocityMultiIndex d) : ℕ :=
  ∏ c, Nat.choose (beta c) (gamma c)

/-- A coordinatewise split of `beta`, recording the multiplicity sent to the left factor. -/
abbrev Split (beta : TimeVelocityMultiIndex d) :=
  (c : TimeVelocityCoord d) → Fin (beta c + 1)

/-- The left multi-index of a split. -/
def Split.left {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    TimeVelocityMultiIndex d := fun c => gamma c

/-- The complementary right multi-index of a split. -/
def Split.right {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    TimeVelocityMultiIndex d := beta - gamma.left

/-- The classical coordinate derivative associated to `beta`, implemented by evaluating the
actual iterated Fréchet derivative on its fixed coordinate list. -/
def coordinateIteratedFDeriv (beta : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  iteratedFDeriv ℝ beta.coordinateList.length f z fun i =>
    timeVelocityBasis (beta.coordinateList.get i)

/-- The zero multi-index has no coordinate directions. -/
@[simp] theorem coordinateList_zero (d : ℕ) :
    coordinateList (0 : TimeVelocityMultiIndex d) = [] := by
  simp [coordinateList]

variable (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d) (f : TimeVelocity d → ℝ) (z : TimeVelocity d)

/-- The coordinate list has length equal to the total differential order. -/
@[simp] theorem length_coordinateList  :
    beta.coordinateList.length = beta.order := by
  simp [coordinateList, TimeVelocityMultiIndex.order,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, timeCoord, velocityCoord]

/-- Choosing zero derivatives in every coordinate has coefficient one. -/
@[simp] theorem choose_zero_right  :
    beta.choose 0 = 1 := by
  simp [choose]

/-- Choosing every derivative in every coordinate has coefficient one. -/
@[simp] theorem choose_self  :
    beta.choose beta = 1 := by
  simp [choose]

/-- The left side of a split is bounded coordinatewise by the original index. -/
theorem Split.left_le {beta : TimeVelocityMultiIndex d}
    (gamma : Split beta) :
    gamma.left ≤ beta := by
  intro c
  exact Nat.le_of_lt_succ (gamma c).isLt

/-- The two sides of a split add back to the original multi-index. -/
@[simp] theorem Split.left_add_right
    {beta : TimeVelocityMultiIndex d} (gamma : Split beta) :
    gamma.left + gamma.right = beta := by
  funext c
  exact Nat.add_sub_of_le (gamma.left_le c)

/-- Total differential order is additive. -/
@[simp] theorem order_add (beta gamma : TimeVelocityMultiIndex d) :
    (beta + gamma).order = beta.order + gamma.order := by
  simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
    Finset.sum_add_distrib]
  omega

/-- Parabolic weight is additive. -/
@[simp] theorem parabolicWeight_add (beta gamma : TimeVelocityMultiIndex d) :
    (beta + gamma).parabolicWeight = beta.parabolicWeight + gamma.parabolicWeight := by
  simp [TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, Finset.sum_add_distrib]
  omega

/-- A single coordinate derivative has total order one. -/
@[simp] theorem order_single  :
    TimeVelocityMultiIndex.order (Pi.single c 1 : TimeVelocityMultiIndex d) = 1 := by
  cases c with
  | inl u => cases u; simp [TimeVelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.order, timeCoord, velocityCoord]
  | inr i =>
      change 0 + ∑ x,
        (Pi.single (Sum.inr i) 1 : TimeVelocityMultiIndex d) (Sum.inr x) = 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim

/-- A single time derivative has parabolic weight two. -/
@[simp] theorem parabolicWeight_single_time :
    TimeVelocityMultiIndex.parabolicWeight
      (Pi.single (timeCoord d) 1 : TimeVelocityMultiIndex d) = 2 := by
  simp [TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, timeCoord, velocityCoord]

/-- A single velocity derivative has parabolic weight one. -/
@[simp] theorem parabolicWeight_single_velocity (i : Fin d) :
    TimeVelocityMultiIndex.parabolicWeight
      (Pi.single (velocityCoord i) 1 : TimeVelocityMultiIndex d) = 1 := by
  change 2 * 0 + ∑ x,
    (Pi.single (Sum.inr i) 1 : TimeVelocityMultiIndex d) (Sum.inr x) = 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The coordinate derivative of order zero is evaluation of the function. -/
@[simp] theorem coordinateIteratedFDeriv_zero
     :
    coordinateIteratedFDeriv 0 f z = f z := by
  unfold coordinateIteratedFDeriv
  rw [coordinateList_zero]
  exact iteratedFDeriv_zero_apply _

private theorem coordinateList_add_single_perm
     :
    (beta + Pi.single c 1).coordinateList.Perm (c :: beta.coordinateList) := by
  classical
  letI : BEq (TimeVelocityCoord d) := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq (TimeVelocityCoord d) := ⟨by simp⟩
  rw [List.perm_iff_count]
  intro a
  have count_flat (q : TimeVelocityMultiIndex d) : ∀ l : List _,
      l.Nodup → List.count a (l.flatMap fun b => List.replicate (q b) b) =
        if a ∈ l then q a else 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons b l ih =>
        have hbl := (List.nodup_cons.mp hl).1
        have hln := (List.nodup_cons.mp hl).2
        by_cases hab : a = b
        · subst b
          simp [hbl, ih hln]
        · simp [ih hln]
          rw [List.count_replicate]
          split <;> simp_all
  unfold coordinateList
  rw [count_flat _ _ (Finset.nodup_toList _)]
  simp only [List.count_cons]
  rw [count_flat _ _ (Finset.nodup_toList _)]
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.add_apply]
  by_cases h : c = a
  · subst a
    simp
  · rw [Pi.single_apply, if_neg (fun hac => h hac.symm)]
    have hb : (c == a) = false := Bool.eq_false_iff.mpr fun heq => h (beq_iff_eq.mp heq)
    rw [hb]
    rfl

/-- Adding one coordinate to a multi-index differentiates the associated
classical coordinate derivative in that direction. -/
theorem coordinateIteratedFDeriv_add_single
    
    (hf : ContDiff ℝ (beta.order + 1) f) :
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
      fderiv ℝ (coordinateIteratedFDeriv beta f) z (timeVelocityBasis c) := by
  let vecList (alpha : TimeVelocityMultiIndex d)  :=
    alpha.coordinateList.map timeVelocityBasis
  have eval_dirs (alpha : TimeVelocityMultiIndex d) (y : TimeVelocity d)
      (ha : ContDiff ℝ alpha.order f) :
      coordinateIteratedFDeriv alpha f y =
        directionalFDerivs (vecList alpha).reverse f y := by
    unfold coordinateIteratedFDeriv
    rw [← directionalFDerivs_reverse_ofFn alpha.coordinateList.length
      _ f y
      (by simpa using ha)]
    congr 2
    have hget : List.ofFn (fun i => alpha.coordinateList.get i) =
        alpha.coordinateList := List.ofFn_get _
    simpa using! congrArg (List.map
      timeVelocityBasis) hget
  have hperm : ((vecList (beta + Pi.single c 1)).reverse).Perm
      ((vecList beta).reverse ++ [timeVelocityBasis c]) := by
    have hm := (coordinateList_add_single_perm beta c).map timeVelocityBasis
    exact (List.reverse_perm (l := vecList _)).trans
      (hm.trans (by
        simpa [vecList, List.map_ofFn, Function.comp_def] using!
          (List.reverse_perm (l := timeVelocityBasis c :: vecList beta)).symm))
  calc
    coordinateIteratedFDeriv _ f z =
        directionalFDerivs _ f z :=
      eval_dirs _ _ (by simpa using hf)
    _ = directionalFDerivs _ f z := congrFun (directionalFDerivs_eq_of_perm hperm f
        (by simpa [vecList, List.map_ofFn, Function.comp_def] using! hf)) z
    _ = directionalFDeriv _
          _ z := by
      rw [directionalFDerivs_append]
      rfl
    _ = fderiv ℝ _ z
          _ := congrArg (fun q => fderiv ℝ q z _)
        (funext fun y => (eval_dirs beta y (hf.of_le (by simp))).symm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Dependent choices of derivative counts, one for each coordinate block. -/
private def BlockSplit {C : Type*} (beta : C → ℕ) : List C → Type
  | [] => PUnit
  | c :: cs => Fin (beta c + 1) × BlockSplit beta cs

private instance {C : Type*} (beta : C → ℕ) (cs : List C) : Fintype (BlockSplit beta cs) := by
  induction cs with
  | nil => simp [BlockSplit]; infer_instance
  | cons c cs ih => simp [BlockSplit]; infer_instance

variable {d : ℕ}

variable {d : ℕ}

variable (beta : TimeVelocityMultiIndex d)

/-- Coordinate iterated derivatives depend only on the germ of a function at
the evaluation point. -/
theorem coordinateIteratedFDeriv_congr_of_eventuallyEq
    
    {f g : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hfg : f =ᶠ[nhds z] g) :
    coordinateIteratedFDeriv beta f z =
      coordinateIteratedFDeriv beta g z := congrArg
    (fun L => L (fun i => timeVelocityBasis (beta.coordinateList.get i)))
    (hfg.iteratedFDeriv ℝ beta.coordinateList.length).self_of_nhds

/-- On an open set, pointwise equality gives equality of every actual
coordinate iterated derivative at each point of that set. -/
theorem coordinateIteratedFDeriv_congr_of_eqOn
    (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (beta : TimeVelocityMultiIndex d)
    {f g : TimeVelocity d → ℝ}
    (hfg : Set.EqOn f g U)
    (z : TimeVelocity d) (hz : z ∈ U) :
    coordinateIteratedFDeriv beta f z =
      coordinateIteratedFDeriv beta g z := by
  apply coordinateIteratedFDeriv_congr_of_eventuallyEq beta
  filter_upwards [hU.mem_nhds hz] with x hx
  exact hfg hx

/-- Pointwise finite-order addition rule for actual coordinate derivatives. -/
theorem coordinateIteratedFDeriv_add_at
    
    (f g : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiffAt ℝ beta.order f z)
    (hg : ContDiffAt ℝ beta.order g z) :
    coordinateIteratedFDeriv beta (fun x ↦ f x + g x) z =
      coordinateIteratedFDeriv beta f z +
        coordinateIteratedFDeriv beta g z := by
  have hf' : ContDiffAt ℝ beta.coordinateList.length f z := by simpa using hf
  have hg' : ContDiffAt ℝ beta.coordinateList.length g z := by simpa using hg
  simpa using! congrArg
    (fun L => L (fun i => timeVelocityBasis (beta.coordinateList.get i)))
    (iteratedFDeriv_add_apply hf' hg')

end HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
