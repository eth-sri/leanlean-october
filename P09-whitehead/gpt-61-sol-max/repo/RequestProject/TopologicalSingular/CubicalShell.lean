import Mathlib.Tactic

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
Adapted to Lean 4.28.0 from Vilin97/homotopy-groups-lean, commit
c66523531ff172d7f41913d94e56921e790a1b47.
The simplex-specific dependency has been removed; cube-face definitions
are copied from the same revision of Hurewicz/StickSimplex.lean.
-/
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic

/-!
# Cubical shells in a pointed space

A map on a `(d+1)`-cube which is constant on the codimension-two cubical skeleton restricts on
each of its `2(d+1)` facets to a based `d`-loop.  This file packages that construction independently
of the stick-breaking simplex used later in the Hurewicz argument.

The first two supported homotopy-addition cases are also proved here.  If only one opposite pair
of facets can be nonconstant, varying its coordinate gives the required relative homotopy.  If
only two adjacent pairs can be nonconstant, convex interpolation between the bottom-right and
left-top routes across their square gives the four-face relation.  Consequently the full oriented
cubical boundary class vanishes in both cases.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

variable {d : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Insert a fixed coordinate into a cube. -/
def cubeFace {d : ℕ} (i : Fin (d + 1)) (a : I) : C(I^Fin d, I^Fin (d + 1)) where
  toFun t := i.insertNth a t
  continuous_toFun := by
    fun_prop

@[simp]
theorem cubeFace_apply {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin d) :
    cubeFace i a t = i.insertNth a t :=
  rfl

@[simp]
theorem cubeFace_apply_same {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin d) :
    cubeFace i a t i = a := by
  simp 

@[simp]
theorem cubeFace_apply_succAbove {d : ℕ} (i : Fin (d + 1)) (a : I)
    (t : I^Fin d) (j : Fin d) :
    cubeFace i a t (i.succAbove j) = t j := by
  simp 

/-- The codimension-two cubical skeleton: at least two distinct coordinates are endpoints. -/
def cubeCodimTwo (d : ℕ) : Set (I^Fin d) :=
  {t | ∃ i j : Fin d, i ≠ j ∧ (t i = 0 ∨ t i = 1) ∧ (t j = 0 ∨ t j = 1)}

theorem cubeFace_mem_cubeCodimTwo {d : ℕ} (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    cubeFace i a t ∈ cubeCodimTwo (d + 1) := by
  obtain ⟨j, hj⟩ := ht
  refine ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, ?_, ?_⟩
  · simpa using ha
  · simpa using hj

/-- Insert a varying coordinate into a cube. -/
def cubeFaceVary {d : ℕ} (i : Fin (d + 1)) : C(I × (I^Fin d), I^Fin (d + 1)) where
  toFun p := i.insertNth p.1 p.2
  continuous_toFun := by
    fun_prop

@[simp]
theorem cubeFaceVary_apply {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin d) :
    cubeFaceVary i (a, t) = cubeFace i a t :=
  rfl

/-! ### The two routes around a square -/

/-- The bottom edge of the unit square, directed from left to right. -/
def squareBottom : Path ((0, 0) : I × I) (1, 0) where
  toFun t := (t, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The right edge of the unit square, directed from bottom to top. -/
def squareRight : Path ((1, 0) : I × I) (1, 1) where
  toFun t := (1, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The left edge of the unit square, directed from bottom to top. -/
def squareLeft : Path ((0, 0) : I × I) (0, 1) where
  toFun t := (0, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The top edge of the unit square, directed from left to right. -/
def squareTop : Path ((0, 1) : I × I) (1, 1) where
  toFun t := (t, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The bottom-then-right route around the unit square. -/
def squareBottomRight  :=
  squareBottom.trans squareRight

/-- The left-then-top route around the unit square. -/
def squareLeftTop  :=
  squareLeft.trans squareTop

/-- Convex interpolation across the square gives a path homotopy between its two monotone
edge routes. -/
noncomputable def squareBoundaryHomotopy :
    Path.Homotopy squareBottomRight squareLeftTop where
  toFun p :=
    (Set.Icc.convexComb (squareBottomRight p.2).1 (squareLeftTop p.2).1 p.1,
      Set.Icc.convexComb (squareBottomRight p.2).2 (squareLeftTop p.2).2 p.1)
  continuous_toFun := by
    fun_prop
  map_zero_left t := by
    simp_all
  map_one_left t := by
    simp_all
  prop' s t ht := by
    aesop

variable {m : ℕ}
@[simp]
theorem cubeFace_last_eq_snoc  (a : I) (t : I^Fin m) :
    cubeFace (Fin.last m) a t = Fin.snoc t a := by
  simp 

@[simp]
theorem cubeFace_penultimate_snoc  (a b : I) (t : I^Fin m) :
    cubeFace (Fin.last m).castSucc a (Fin.snoc t b) = Fin.snoc (Fin.snoc t a) b := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      have hlast : (Fin.last m).castSucc.succAbove (Fin.last m) = Fin.last (m + 1) := by
        apply Fin.ext
        simp
      rw [← hlast, cubeFace_apply_succAbove]
      simp
  | cast j =>
      induction j using Fin.lastCases <;> simp_all [Fin.insertNth_apply_below]

@[simp]
theorem update_last_eq_snoc_init  (t : I^Fin (m + 1)) (a : I) :
    Function.update t (Fin.last m) a = Fin.snoc (Fin.init t) a := by
  classical grind [Fin.snoc_init_self, Fin.update_snoc_last]

/-- The convex sweep from the bottom-right route to the left-top route, with `m` passive
coordinates prepended. -/
noncomputable def squareSweepCube (m : ℕ) :
    C(I × (I^Fin (m + 1)), I^Fin (m + 2)) where
  toFun st :=
    Fin.snoc (Fin.snoc (Fin.init st.2) (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).1)
      (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).2
  continuous_toFun := by
    fun_prop

/-- Pointwise concatenation formula with the unclamped half-interval coordinates exposed. -/
theorem genLoop_transAt_apply_path {N : Type*} [DecidableEq N] (i : N)
    (f g : Ω^ N X x) (t : I^N) :
    (GenLoop.transAt i f g).val t =
      if h : (t i : ℝ) ≤ 1 / 2 then
        f (Function.update t i
          ⟨2 * t i, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(t i).2.1, h⟩⟩)
      else
        g (Function.update t i
          ⟨2 * t i - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 h).le, (t i).2.2⟩⟩) := by
  change (if (t i : ℝ) ≤ 1 / 2 then
      f (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i)))
    else g (Function.update t i (Set.projIcc 0 1 zero_le_one (2 * t i - 1)))) = _
  split_ifs with h
  · classical grind [Set.projIcc_of_mem, unitInterval.mul_pos_mem_iff, zero_lt_two]
  · classical grind [Set.projIcc_of_mem, unitInterval.two_mul_sub_one_mem_iff, not_le]

/-- A cubical shell is a map on a cube which collapses the codimension-two skeleton to the
chosen basepoint. -/
structure CubicalShell (d : ℕ) (X : Type*) [TopologicalSpace X] (x : X) where
  /-- The map on the ambient `(d+1)`-cube. -/
  map : C(I^Fin (d + 1), X)
  /-- The map is constant on the codimension-two cubical skeleton. -/
  codimTwo (t : I^Fin (d + 1)) (ht : t ∈ cubeCodimTwo (d + 1)) : map t = x

namespace CubicalShell

variable (S : CubicalShell d X x)
  (i : Fin (d + 1))
  (a : I)
variable (ha : a = 0 ∨ a = 1)
/-- The facet of a cubical shell at coordinate `i` and endpoint `a`, as a based generalized
loop. -/
noncomputable def faceLoop   
     : Ω^ (Fin d) X x :=
  ⟨S.map.comp (cubeFace i a), fun t ht ↦ S.codimTwo _
    (cubeFace_mem_cubeCodimTwo i a ha t ht)⟩

@[simp]
theorem faceLoop_apply   
     (t : I^Fin d) :
    (S.faceLoop i a ha).val t = S.map (cubeFace i a t) :=
  rfl

/-- The lower facet loop. -/
noncomputable def lowerFaceLoop    :=
  S.faceLoop i 0 (Or.inl rfl)

/-- The upper facet loop. -/
noncomputable def upperFaceLoop    :=
  S.faceLoop i 1 (Or.inr rfl)

variable (t : I^Fin d)
@[simp]
theorem lowerFaceLoop_apply  
     :
    (S.lowerFaceLoop i).val t = S.map (cubeFace i 0 t) :=
  rfl

@[simp]
theorem upperFaceLoop_apply  
     :
    (S.upperFaceLoop i).val t = S.map (cubeFace i 1 t) :=
  rfl

variable {m : ℕ}
/-- The sweep starts at the concatenation of the last lower face with the penultimate upper
face. -/
theorem squareSweepCube_zero  (S : CubicalShell (m + 1) X x)
    (t : I^Fin (m + 1)) :
    S.map (squareSweepCube m (0, t)) =
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
        (S.upperFaceLoop (Fin.last m).castSucc)).val t := by
  change S.map (Fin.snoc (Fin.snoc (Fin.init t)
    (squareBoundaryHomotopy (0, t (Fin.last m))).1)
    (squareBoundaryHomotopy (0, t (Fin.last m))).2) = _
  rw [ContinuousMap.HomotopyWith.apply_zero, squareBottomRight]
  simp only [Path.coe_toContinuousMap]
  rw [Path.trans_apply, genLoop_transAt_apply_path]
  split_ifs with h
  · classical aesop (add unsafe apply [congrArg, FiniteChains.TopologicalSingular.cubeFace_last_eq_snoc, FiniteChains.TopologicalSingular.update_last_eq_snoc_init])
  · change S.map _ = S.map (cubeFace (Fin.last m).castSucc 1 _)
    apply congrArg S.map
    rw [update_last_eq_snoc_init, cubeFace_penultimate_snoc]
    rfl

/-- The sweep ends at the concatenation of the penultimate lower face with the last upper
face. -/
theorem squareSweepCube_one  (S : CubicalShell (m + 1) X x)
    (t : I^Fin (m + 1)) :
    S.map (squareSweepCube m (1, t)) =
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last m).castSucc)
        (S.upperFaceLoop (Fin.last (m + 1)))).val t := by
  change S.map (Fin.snoc (Fin.snoc (Fin.init t)
    (squareBoundaryHomotopy (1, t (Fin.last m))).1)
    (squareBoundaryHomotopy (1, t (Fin.last m))).2) = _
  rw [ContinuousMap.HomotopyWith.apply_one, squareLeftTop]
  simp only [Path.coe_toContinuousMap]
  rw [Path.trans_apply, genLoop_transAt_apply_path]
  split_ifs with h
  · change S.map _ = S.map (cubeFace (Fin.last m).castSucc 0 _)
    apply congrArg S.map
    rw [update_last_eq_snoc_init, cubeFace_penultimate_snoc]
    rfl
  · classical aesop (add unsafe apply [congrArg, FiniteChains.TopologicalSingular.cubeFace_last_eq_snoc, FiniteChains.TopologicalSingular.update_last_eq_snoc_init])

/-- A facet of the ambient cube is constant at the shell basepoint. -/
def IsConstantFace     :=
  ∀ t : I^Fin (d + 1), t i = a → S.map t = x

theorem faceLoop_eq_const   
     (h : S.IsConstantFace i a) :
    S.faceLoop i a ha = GenLoop.const := by
  apply GenLoop.ext
  intro t
  exact h _ (by simp)

theorem lowerFaceLoop_eq_const  
    (h : S.IsConstantFace i 0) :
    S.lowerFaceLoop i = GenLoop.const :=
  S.faceLoop_eq_const i 0 (Or.inl rfl) h

/-- All facets in the first `m` directions are constant, leaving only the last two coordinate
pairs potentially nonconstant. -/
def LeadingFacesConstant  (S : CubicalShell (m + 1) X x)  :=
  ∀ i : Fin m,
    S.IsConstantFace i.castSucc.castSucc 0 ∧ S.IsConstantFace i.castSucc.castSucc 1

/-- The square filling relates the two concatenations formed by the last four facets. -/
theorem lastTwoFaceLoops_homotopic  (S : CubicalShell (m + 1) X x)
    (h : S.LeadingFacesConstant) :
    GenLoop.Homotopic
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
        (S.upperFaceLoop (Fin.last m).castSucc))
      (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last m).castSucc)
        (S.upperFaceLoop (Fin.last (m + 1)))) := by
  refine ⟨{
    toFun := fun st ↦ S.map (squareSweepCube m st)
    continuous_toFun := S.map.continuous.comp (squareSweepCube m).continuous
    map_zero_left := S.squareSweepCube_zero
    map_one_left := S.squareSweepCube_one
    prop' := fun s t ht ↦ ?_ }⟩
  have hstart := (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last (m + 1)))
    (S.upperFaceLoop (Fin.last m).castSucc)).property t ht
  apply Eq.trans ?_ hstart.symm
  obtain ⟨j, hj⟩ := ht
  obtain ⟨i, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
  · rcases h i with ⟨hi0, hi1⟩
    rcases hj with hj | hj
    · aesop (add simp [squareSweepCube])
    · aesop (add simp [squareSweepCube])
  · rcases hj with hj | hj
    · apply S.codimTwo
      refine ⟨(Fin.last m).castSucc, Fin.last (m + 1),
        Fin.castSucc_ne_last (Fin.last m), Or.inl ?_, Or.inl ?_⟩
      · simp [squareSweepCube, hj]
      · simp [squareSweepCube, hj]
    · apply S.codimTwo
      refine ⟨(Fin.last m).castSucc, Fin.last (m + 1),
        Fin.castSucc_ne_last (Fin.last m), Or.inr ?_, Or.inr ?_⟩
      · simp [squareSweepCube, hj]
      · simp [squareSweepCube, hj]

/-- The additive homotopy class of a lower facet. -/
noncomputable def lowerFaceClass   :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.lowerFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

/-- The additive homotopy class of an upper facet. -/
noncomputable def upperFaceClass   :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.upperFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

theorem lowerFaceClass_eq_zero [Nonempty (Fin d)] (S : CubicalShell d X x)
    (i : Fin (d + 1)) (h : S.IsConstantFace i 0) :
    S.lowerFaceClass i = 0 := by
  aesop (add simp [FiniteChains.TopologicalSingular.CubicalShell.lowerFaceLoop_eq_const, lowerFaceClass])

/-- The four face classes around the last-coordinate square satisfy the square boundary
relation. -/
theorem lastTwoFaceClass_relation  [Nontrivial (Fin (m + 1))]
    (S : CubicalShell (m + 1) X x) (h : S.LeadingFacesConstant) :
    S.upperFaceClass (Fin.last m).castSucc + S.lowerFaceClass (Fin.last (m + 1)) =
      S.upperFaceClass (Fin.last (m + 1)) + S.lowerFaceClass (Fin.last m).castSucc := by
  have hq :
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last m).castSucc⟧ ⟦S.lowerFaceLoop (Fin.last (m + 1))⟧ =
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last (m + 1))⟧ ⟦S.lowerFaceLoop (Fin.last m).castSucc⟧ := by
    rw [HomotopyGroup.mul_spec (i := Fin.last m),
      HomotopyGroup.mul_spec (i := Fin.last m)]
    exact Quotient.sound (S.lastTwoFaceLoops_homotopic h)
  exact congrArg Additive.ofMul hq

end FiniteChains.TopologicalSingular.CubicalShell


