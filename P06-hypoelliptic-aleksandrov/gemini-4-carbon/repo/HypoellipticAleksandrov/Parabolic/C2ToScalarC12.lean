module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import PDEFoundation.Ambient.Basis
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Data.Nat.Choose.Basic
public import Lean.Elab.Tactic.Omega
public import HypoellipticAleksandrov.Parabolic.ScalarClassical

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators

variable {d : ℕ}

/-- The distinguished time coordinate followed by the velocity coordinates. -/
abbrev TimeVelocityCoord (d : ℕ) := Unit ⊕ Fin d

/-- The distinguished time coordinate. -/
def timeCoord (d : ℕ) : TimeVelocityCoord d :=
  Sum.inl ()

/-- The velocity coordinate associated to `i`. -/
def velocityCoord {d : ℕ} (i : Fin d) : TimeVelocityCoord d :=
  Sum.inr i

/-- The literal coordinate basis vector in `TimeVelocity d`. -/
def timeVelocityBasis {d : ℕ} : TimeVelocityCoord d → TimeVelocity d
  | Sum.inl _ => (1, 0)
  | Sum.inr i => (0, PDE.basisVec i)

/-- A velocity multi-index. -/
abbrev VelocityMultiIndex (d : ℕ) := Fin d → ℕ

/-- Total order of a velocity multi-index. -/
def VelocityMultiIndex.order (alpha : VelocityMultiIndex d) : ℕ :=
  ∑ i, alpha i

/-- An ordinary multi-index in all time--velocity coordinates. -/
abbrev TimeVelocityMultiIndex (d : ℕ) := TimeVelocityCoord d → ℕ

/-- Time order of an ordinary time--velocity multi-index. -/
def TimeVelocityMultiIndex.timeOrder
    (beta : TimeVelocityMultiIndex d) : ℕ :=
  beta (timeCoord d)

/-- Velocity restriction of an ordinary time--velocity multi-index. -/
def TimeVelocityMultiIndex.velocity
    (beta : TimeVelocityMultiIndex d) : VelocityMultiIndex d :=
  fun i => beta (velocityCoord i)

/-- Assemble an ordinary multi-index from its time and velocity orders. -/
def TimeVelocityMultiIndex.ofTimeVelocity
    (q : ℕ) (alpha : VelocityMultiIndex d) : TimeVelocityMultiIndex d
  | Sum.inl _ => q
  | Sum.inr i => alpha i

/-- Total ordinary order of a time--velocity multi-index. -/
def TimeVelocityMultiIndex.order
    (beta : TimeVelocityMultiIndex d) : ℕ :=
  beta.timeOrder + beta.velocity.order

/-- The numerical parabolic weight `2q + |alpha|`. -/
def VelocityMultiIndex.parabolicWeight
    (q : ℕ) (alpha : VelocityMultiIndex d) : ℕ :=
  2 * q + alpha.order

/-- Parabolic weight of an ordinary time--velocity multi-index. -/
def TimeVelocityMultiIndex.parabolicWeight
    (beta : TimeVelocityMultiIndex d) : ℕ :=
  beta.velocity.parabolicWeight beta.timeOrder

@[simp] theorem timeVelocityBasis_time (d : ℕ) :
    timeVelocityBasis (timeCoord d) = ((1, 0) : TimeVelocity d) :=
  rfl

@[simp] theorem timeVelocityBasis_velocity {d : ℕ} (i : Fin d) :
    timeVelocityBasis (velocityCoord i) =
      ((0, PDE.basisVec i) : TimeVelocity d) :=
  rfl

@[simp] theorem TimeVelocityMultiIndex.timeOrder_ofTimeVelocity
    (q : ℕ) (alpha : VelocityMultiIndex d) :
    (ofTimeVelocity q alpha).timeOrder = q :=
  rfl

@[simp] theorem TimeVelocityMultiIndex.velocity_ofTimeVelocity
    (q : ℕ) (alpha : VelocityMultiIndex d) :
    (ofTimeVelocity q alpha).velocity = alpha :=
  rfl


@[simp] theorem TimeVelocityMultiIndex.order_ofTimeVelocity
    (q : ℕ) (alpha : VelocityMultiIndex d) :
    (ofTimeVelocity q alpha).order = q + alpha.order :=
  rfl

@[simp] theorem TimeVelocityMultiIndex.parabolicWeight_ofTimeVelocity
    (q : ℕ) (alpha : VelocityMultiIndex d) :
    (ofTimeVelocity q alpha).parabolicWeight = alpha.parabolicWeight q :=
  rfl




/-- Ordinary time--velocity multi-indices of total order at most `m`. -/
abbrev TimeVelocityDerivativeIndex (d m : ℕ) :=
  {beta : TimeVelocityMultiIndex d // beta.order ≤ m}

/-- The zero multi-index at any finite order bound. -/
def TimeVelocityDerivativeIndex.zero (d m : ℕ) :
    TimeVelocityDerivativeIndex d m :=
  ⟨0, by
    simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
      TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order]⟩


end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
section

open scoped BigOperators

variable {d : ℕ}









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

/-- The coordinate list has length equal to the total differential order. -/
@[simp] theorem length_coordinateList (beta : TimeVelocityMultiIndex d) :
    beta.coordinateList.length = beta.order := by
  simp [coordinateList, TimeVelocityMultiIndex.order,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
    VelocityMultiIndex.order, timeCoord, velocityCoord]





/-- Total differential order is additive. -/
@[simp] theorem order_add (beta gamma : TimeVelocityMultiIndex d) :
    (beta + gamma).order = beta.order + gamma.order := by
  simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
    Finset.sum_add_distrib]
  omega


/-- A single coordinate derivative has total order one. -/
@[simp] theorem order_single (c : TimeVelocityCoord d) :
    TimeVelocityMultiIndex.order (Pi.single c 1 : TimeVelocityMultiIndex d) = 1 := by
  cases c with
  | inl u => cases u; simp [TimeVelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.order, timeCoord, velocityCoord]
  | inr i =>
      change 0 + ∑ x,
        (Pi.single (Sum.inr i) 1 : TimeVelocityMultiIndex d) (Sum.inr x) = 1
      rw [zero_add, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim



/-- The coordinate derivative of order zero is evaluation of the function. -/
@[simp] theorem coordinateIteratedFDeriv_zero
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    coordinateIteratedFDeriv 0 f z = f z := by
  unfold coordinateIteratedFDeriv
  rw [coordinateList_zero]
  exact iteratedFDeriv_zero_apply _



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




end

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {d : ℕ}


private instance {C : Type*} (beta : C → ℕ) (cs : List C) :
    Fintype (BlockSplit beta cs) := by
  induction cs with
  | nil => simp [BlockSplit]; infer_instance
  | cons c cs ih => simp [BlockSplit]; infer_instance

private def localDirs : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | v :: vs, f => fun z => fderiv ℝ (localDirs vs f) z v


private theorem localDirs_ofFn_eq_iteratedFDeriv (n : ℕ) (v : Fin n → E)
    (f : E → ℝ) (z : E) (hf : ContDiffAt ℝ n f z) :
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


private theorem localDirectional_comm (a b : E) (f : E → ℝ) (z : E)
    (hf : ContDiffAt ℝ 2 f z) :
    fderiv ℝ (fun y => fderiv ℝ f y a) z b =
      fderiv ℝ (fun y => fderiv ℝ f y b) z a := by
  have hd :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const a),
    fderiv_clm_apply hd (differentiableAt_const b)]
  simp
  exact (hf.isSymmSndFDerivAt (by simp)).eq b a

private theorem localDirs_perm {l₁ l₂ : List E} (hperm : l₁.Perm l₂)
    (f : E → ℝ) (z : E) (hf : ContDiffAt ℝ l₁.length f z) :
    localDirs l₁ f z = localDirs l₂ f z  := by
  have localDirs_contDiffAt (l : List E) (m : ℕ) (f : E → ℝ) (z : E) (hf : ContDiffAt ℝ (m + l.length) f z) :
      ContDiffAt ℝ m (localDirs l f) z := by
    induction l generalizing m f with
    | nil => simpa [localDirs] using hf
    | cons v l ih =>
        rw [localDirs]
        have h : ContDiffAt ℝ (m + 1) (localDirs l f) z := by
          apply ih
          convert hf using 1
          norm_num
          exact_mod_cast (show (m + 1) + l.length = m + (l.length + 1) by omega)
        exact (h.fderiv_right (by norm_num)).clm_apply contDiffAt_const
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


/-- Adding one coordinate differentiates the associated coordinate derivative
at a point under the exact finite germ-local regularity. -/
theorem coordinateIteratedFDeriv_add_single_at
    (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d)
    (f : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiffAt ℝ (beta.order + 1) f z) :
    coordinateIteratedFDeriv (beta + Pi.single c 1) f z =
      fderiv ℝ (coordinateIteratedFDeriv beta f) z
        (timeVelocityBasis c)  := by
  have coordinateList_add_single_perm_local :
      (beta + Pi.single c 1).coordinateList.Perm (c :: beta.coordinateList) := by
    classical
    letI : BEq (TimeVelocityCoord d) := ⟨fun a b => decide (a = b)⟩
    letI : LawfulBEq (TimeVelocityCoord d) := ⟨by intro a b; simp⟩
    rw [List.perm_iff_count]
    intro a
    have count_flat (q : TimeVelocityMultiIndex d) : ∀ l : List (TimeVelocityCoord d),
        l.Nodup → List.count a (l.flatMap fun b => List.replicate (q b) b) =
          if a ∈ l then q a else 0 := by
      intro l hl
      induction l with
      | nil => simp
      | cons b l ih =>
          have hln := (List.nodup_cons.mp hl).2
          by_cases hab : a = b
          · subst b
            simp [((List.nodup_cons.mp hl).1), ih hln]
          · simp [ih hln]
            rw [List.count_replicate]
            split <;> simp_all
    unfold coordinateList
    rw [count_flat _ _ (Finset.nodup_toList (Finset.univ : Finset (TimeVelocityCoord d)))]
    simp only [List.count_cons]
    rw [count_flat _ _ (Finset.nodup_toList (Finset.univ : Finset (TimeVelocityCoord d)))]
    simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.add_apply]
    congr 1
    by_cases h : c = a
    · subst a
      simp
    · rw [Pi.single_apply, if_neg (fun hac => h hac.symm)]
      rw [(Bool.eq_false_iff.mpr fun heq => h (beq_iff_eq.mp heq))]
      rfl
  let vecList (alpha : TimeVelocityMultiIndex d) : List (TimeVelocity d) :=
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
    simpa using ha
  have hperm : (vecList (beta + Pi.single c 1)).Perm
      (timeVelocityBasis c :: vecList beta) := by
    simpa [vecList] using (coordinateList_add_single_perm_local).map timeVelocityBasis
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

namespace HypoellipticAleksandrov.Parabolic
open TimeVelocityMultiIndex
open scoped Topology




private theorem scalarTimeDerivative_eq_coordinate_local
    {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hu : ContDiffAt ℝ 1 u z) :
    scalarTimeDerivative u z =
      coordinateIteratedFDeriv (Pi.single (timeCoord d) 1) u z := by
  have h := coordinateIteratedFDeriv_add_single_at
    0 (timeCoord d) u z
      (by simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity] using hu)
  simp at h
  rw [show coordinateIteratedFDeriv 0 u = u by
    funext x; exact coordinateIteratedFDeriv_zero u x] at h
  rw [h]
  unfold scalarTimeDerivative
  have hsF := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have hs : HasDerivAt (fun r : ℝ ↦ u (r, z.2))
      ((fderiv ℝ u z) (1, 0)) z.1 := by
    convert hsF.hasDerivAt using 1
    all_goals simp [Function.comp_def]
  exact hs.deriv

private theorem scalarSpatialGradient_eq_coordinate_local
    {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d) (j : Fin d)
    (hu : ContDiffAt ℝ 1 u z) :
    scalarSpatialGradient u z j =
      coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u z := by
  have h := coordinateIteratedFDeriv_add_single_at
    0 (velocityCoord j) u z
      (by simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity] using hu)
  simp at h
  rw [show coordinateIteratedFDeriv 0 u = u by
    funext x; exact coordinateIteratedFDeriv_zero u x] at h
  rw [h, scalarSpatialGradient, PDE.classicalGradient_apply]
  have hs : HasFDerivAt (fun y : PDE.Vec d ↦ u (z.1, y))
      ((fderiv ℝ u z).comp (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) z.2 :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.2
      ((hasFDerivAt_const (x := z.2) z.1).prodMk (hasFDerivAt_id z.2))
  rw [hs.fderiv]
  simp

private theorem scalarSpatialHessian_eq_coordinate_local
    {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d) (i j : Fin d)
    (hu : ContDiffAt ℝ 2 u z) :
    scalarSpatialHessian u z i j =
      coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) u z := by
  classical
  let q :=
    coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u
  have hq : ContDiffAt ℝ 1 q z := by
    have hr : ContDiffAt ℝ 1
        (fun x ↦ (fderiv ℝ u x) (timeVelocityBasis (velocityCoord j))) z :=
      (hu.fderiv_right (by norm_num)).clm_apply contDiffAt_const
    apply hr.congr_of_eventuallyEq
    filter_upwards [hu.eventually (by simp)] with x hx
    have hadd := coordinateIteratedFDeriv_add_single_at
      0 (velocityCoord j) u x
      (by simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity] using
        hx.of_le (by norm_num))
    rw [show coordinateIteratedFDeriv 0 u = u by
      funext y; exact coordinateIteratedFDeriv_zero u y] at hadd
    simpa [q] using hadd
  have hgradient : (fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) =ᶠ[nhds z] q := by
    filter_upwards [hu.eventually (by simp)] with x hx
    exact scalarSpatialGradient_eq_coordinate_local u x j (hx.of_le (by norm_num))
  have hgradientApply :
      (fderiv ℝ (fun y : PDE.Vec d ↦
          PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y j) z.2)
          (PDE.basisVec i) =
        (fderiv ℝ (fun y : PDE.Vec d ↦
          PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2
          (PDE.basisVec i)) j := by
    have hgrad : DifferentiableAt ℝ
        (fun y ↦ PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2 := by
      apply differentiableAt_pi.2
      intro k
      have hd :=
        ((hu.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      exact hd.clm_apply (differentiableAt_const (c := PDE.basisVec k))
    rw [fderiv_pi (fun k ↦ (differentiableAt_pi.mp hgrad) k)]
    simp
  have hcomp :
      fderiv ℝ (fun y : PDE.Vec d ↦ scalarSpatialGradient u (z.1, y) j) z.2 =
        (fderiv ℝ (fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) z).comp
          (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d)) := by
    change fderiv ℝ ((fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) ∘
      fun y : PDE.Vec d ↦ (z.1, y)) z.2 = _
    rw [fderiv_comp z.2 (hgradient.differentiableAt_iff.mpr (hq.differentiableAt (by norm_num)))
      ((differentiableAt_const (c := z.1)).prodMk differentiableAt_id)]
    congr 1
    exact ((hasFDerivAt_const (x := z.2) z.1).prodMk (hasFDerivAt_id z.2)).fderiv
  change (fderiv ℝ (fun y : PDE.Vec d ↦
      PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2
      (PDE.basisVec i)) j = _
  rw [← hgradientApply]
  change (fderiv ℝ (fun y : PDE.Vec d ↦
    scalarSpatialGradient u (z.1, y) j) z.2) (PDE.basisVec i) = _
  rw [hcomp, hgradient.fderiv_eq]
  simpa [q] using (coordinateIteratedFDeriv_add_single_at (Pi.single (velocityCoord j) 1) (velocityCoord i) u z (by simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order, TimeVelocityMultiIndex.velocity, TimeVelocityMultiIndex.timeOrder, timeCoord, velocityCoord, Pi.single_apply, show (1 : WithTop ℕ∞) + 1 = 2 by rfl] using hu)).symm

private theorem coordinateIteratedFDeriv_contDiff_local
    {d m : ℕ} (alpha : TimeVelocityMultiIndex d)
    (f : TimeVelocity d → ℝ) (hf : ContDiff ℝ (m + alpha.order) f) :
    ContDiff ℝ m (coordinateIteratedFDeriv alpha f) := by
  unfold coordinateIteratedFDeriv
  exact (contDiff_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun i ↦ timeVelocityBasis (alpha.coordinateList.get i)))).clm_apply (hf.iteratedFDeriv_right (m := m) (i := alpha.coordinateList.length) (by simp))

/-- An ambient `C²` function has the scalar anisotropic `C¹˒²` regularity
required on every carrier. -/
theorem isScalarC12On_of_contDiff_two
    {d : ℕ} {v : TimeVelocity d → ℝ}
    (hv : ContDiff ℝ 2 v) (D : Set (TimeVelocity d)) :
    IsScalarC12On v D := by
  refine ⟨hv.continuous.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact ((hv.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).differentiableAt
  · intro z hz
    exact hv.contDiffAt.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
  · apply Continuous.continuousOn
    apply Continuous.congr (coordinateIteratedFDeriv_contDiff_local
      (Pi.single (timeCoord d) 1) v (by norm_num at *; exact hv)).continuous
    intro z
    exact (scalarTimeDerivative_eq_coordinate_local v z
      ((hv.of_le (by norm_num)).contDiffAt)).symm
  · apply Continuous.continuousOn
    apply continuous_pi
    intro j
    apply Continuous.congr (coordinateIteratedFDeriv_contDiff_local
      (Pi.single (velocityCoord j) 1) v (by norm_num at *; exact hv)).continuous
    intro z
    exact (scalarSpatialGradient_eq_coordinate_local v z j
      ((hv.of_le (by norm_num)).contDiffAt)).symm
  · apply Continuous.continuousOn
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply Continuous.congr (coordinateIteratedFDeriv_contDiff_local
      (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) v
      (by norm_num at *; exact hv)).continuous
    intro z
    exact (scalarSpatialHessian_eq_coordinate_local v z i j hv.contDiffAt).symm

/-- The scalar time derivative is the canonical time-coordinate derivative. -/
theorem scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two
    {d : ℕ} {v : TimeVelocity d → ℝ} (hv : ContDiff ℝ 2 v)
    (z : TimeVelocity d) :
    scalarTimeDerivative v z =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (timeCoord d) 1) v z :=
  scalarTimeDerivative_eq_coordinate_local v z ((hv.of_le (by norm_num)).contDiffAt)

/-- Each scalar spatial-gradient entry is its canonical velocity-coordinate
derivative. -/
theorem scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two
    {d : ℕ} {v : TimeVelocity d → ℝ} (hv : ContDiff ℝ 2 v)
    (z : TimeVelocity d) (j : Fin d) :
    scalarSpatialGradient v z j =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1) v z :=
  scalarSpatialGradient_eq_coordinate_local v z j ((hv.of_le (by norm_num)).contDiffAt)

/-- The ordered Hessian entry `(i,j)` is `D_i(D_j v)`. -/
theorem scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two
    {d : ℕ} {v : TimeVelocity d → ℝ} (hv : ContDiff ℝ 2 v)
    (z : TimeVelocity d) (i j : Fin d) :
    scalarSpatialHessian v z i j =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1 +
          Pi.single (velocityCoord i) 1) v z :=
  scalarSpatialHessian_eq_coordinate_local v z i j hv.contDiffAt


end HypoellipticAleksandrov.Parabolic

