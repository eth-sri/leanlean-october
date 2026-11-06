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
import RequestProject.Tac


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

bwd

namespace FiniteChains.TopologicalSingular

variable {d : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Insert a fixed coordinate into a cube. -/
def cubeFace (i : Fin (d + 1)) (a : I) : C(I^Fin d, I^Fin (d + 1)) where
  toFun t := i.insertNth a t
  continuous_toFun := by
    fun_prop


@[simp]
theorem cubeFace_apply_same i a (t : I^Fin d) :
    cubeFace i a t i = a := by
  simp [cubeFace]

@[simp]
theorem cubeFace_apply_succAbove i a
    t (j : Fin d) :
    cubeFace i a t (i.succAbove j) = t j := by
  simp [cubeFace]

/-- The codimension-two cubical skeleton: at least two distinct coordinates are endpoints. -/
def cubeCodimTwo d : Set (I^Fin d) :=
  {t | ∃ i j : Fin d, i ≠ j ∧ (t i = 0 ∨ t i = 1) ∧ (t j = 0 ∨ t j = 1)}

theorem cubeFace_mem_cubeCodimTwo i a
    (ha : a = 0 ∨ a = 1) t (ht : t ∈ Cube.boundary (Fin d)) :
    cubeFace i a t ∈ cubeCodimTwo (d + 1) := by
  cases' ht with j hj
  refine ⟨i, i.succAbove j, (i.succAbove_ne j).symm, ?_, ?_⟩
  · simpa using ha
  simp_all



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
def squareBottomRight :=
  squareBottom.trans squareRight

/-- The left-then-top route around the unit square. -/
def squareLeftTop :=
  squareLeft.trans squareTop

/-- Convex interpolation across the square gives a path homotopy between its two monotone
edge routes. -/
def squareBoundaryHomotopy :
    Path.Homotopy squareBottomRight squareLeftTop where
  toFun p :=
    (Set.Icc.convexComb (squareBottomRight p.2).1 (squareLeftTop p.2).1 p.1,
      Set.Icc.convexComb (squareBottomRight p.2).2 (squareLeftTop p.2).2 p.1)
  continuous_toFun := by
    fun_prop
  map_zero_left t := by
    simp
  map_one_left t := by
    simp
  prop' s t ht := by
    aesop

@[simp]
theorem cubeFace_last_eq_snoc a t :
    cubeFace (Fin.last m) a t = Fin.snoc t a := by
  simp [cubeFace]

@[simp]
theorem cubeFace_penultimate_snoc a b (t : I^Fin m) :
    cubeFace (Fin.last m).castSucc a (Fin.snoc t b) = Fin.snoc (Fin.snoc t a) b := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      have hlast : (Fin.last m).castSucc.succAbove (Fin.last m) = Fin.last _ := by
        apply Fin.ext
        simp
      rw [← hlast, cubeFace_apply_succAbove]
      simp
  | cast j =>
      induction j using Fin.lastCases with
      | last => simp
      | cast j => simp [cubeFace, Fin.insertNth_apply_below, Fin.snoc]

@[simp]
theorem update_last_eq_snoc_init (t : I^Fin (m + 1)) a :
    Function.update t (Fin.last m) a = Fin.snoc (Fin.init t) a := by
  conv_lhs => rw [← Fin.snoc_init_self t]
  exact Fin.update_snoc_last _ _ _

/-- The convex sweep from the bottom-right route to the left-top route, with `m` passive
coordinates prepended. -/
def squareSweepCube m :
    C(I × (I^Fin (m + 1)), I^Fin (m + 2)) where
  toFun st :=
    Fin.snoc (Fin.snoc (Fin.init st.2) (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).1)
      (squareBoundaryHomotopy (st.1, st.2 (Fin.last m))).2
  continuous_toFun := by
    fun_prop

/-- Pointwise concatenation formula with the unclamped half-interval coordinates exposed. -/
theorem genLoop_transAt_apply_path {N} [DecidableEq N] i
    (f g : Ω^ N X x) t :
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
  · rw [Set.projIcc_of_mem _ _]
  · rw [Set.projIcc_of_mem _ _]

/-- A cubical shell is a map on a cube which collapses the codimension-two skeleton to the
chosen basepoint. -/
structure CubicalShell (d : ℕ) (X : Type*) [TopologicalSpace X] (x : X) where
  /-- The map on the ambient `(d+1)`-cube. -/
  map : C(I^Fin (d + 1), X)
  /-- The map is constant on the codimension-two cubical skeleton. -/
  codimTwo (t : I^Fin (d + 1)) (ht : t ∈ cubeCodimTwo (d + 1)) : map t = x

namespace CubicalShell

/-- The facet of a cubical shell at coordinate `i` and endpoint `a`, as a based generalized
loop. -/
def faceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) : Ω^ (Fin d) X x :=
  ⟨S.map.comp (cubeFace i a), fun t ht ↦ S.codimTwo _
    (cubeFace_mem_cubeCodimTwo i a ha t ht)⟩


/-- The lower facet loop. -/
def lowerFaceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) :=
  S.faceLoop i 0 (Or.inl rfl)

/-- The upper facet loop. -/
def upperFaceLoop (S : CubicalShell d X x) (i : Fin (d + 1)) :=
  S.faceLoop i 1 (Or.inr rfl)



/-- The sweep starts at the concatenation of the last lower face with the penultimate upper
face. -/
theorem squareSweepCube_zero (S : CubicalShell (m + 1) X x)
    t :
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
  · change S.map _ = S.map (cubeFace (Fin.last _) 0 _)
    aesop
  · change S.map _ = S.map (cubeFace (Fin.last m).castSucc 1 _)
    aesop

/-- The sweep ends at the concatenation of the penultimate lower face with the last upper
face. -/
theorem squareSweepCube_one (S : CubicalShell (m + 1) X x)
    t :
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
    aesop
  · change S.map _ = S.map (cubeFace (Fin.last _) 1 _)
    aesop

/-- A facet of the ambient cube is constant at the shell basepoint. -/
def IsConstantFace (S : CubicalShell d X x) (i : Fin (d + 1)) (a : I) :=
  ∀ t, t i = a → S.map t = x


theorem lowerFaceLoop_eq_const (S : CubicalShell d X x) i
    (h : S.IsConstantFace i 0) :
    S.lowerFaceLoop i = GenLoop.const :=
  by aesop

/-- All facets in the first `m` directions are constant, leaving only the last two coordinate
pairs potentially nonconstant. -/
def LeadingFacesConstant (S : CubicalShell (m + 1) X x) :=
  ∀ i : Fin m,
    S.IsConstantFace i.castSucc.castSucc 0 ∧ S.IsConstantFace i.castSucc.castSucc 1

/-- The square filling relates the two concatenations formed by the last four facets. -/
theorem lastTwoFaceLoops_homotopic (S : CubicalShell (m + 1) X x)
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
  have hstart := (GenLoop.transAt (Fin.last m) (S.lowerFaceLoop (Fin.last _))
    (S.upperFaceLoop (Fin.last m).castSucc)).property t ht
  apply Eq.trans ?_ hstart.symm
  cases' ht with j hj
  obtain ⟨i, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
  · cases' h i with hi0 hi1
    rcases hj with hj | hj
    · exact hi0 _ (by simpa [squareSweepCube, Fin.init_def] using hj)
    · exact hi1 _ (by simpa [squareSweepCube, Fin.init_def] using hj)
  · rcases hj with hj | hj
    · apply S.codimTwo
      refine ⟨(Fin.last m).castSucc, Fin.last _,
        Fin.castSucc_ne_last _, Or.inl ?_, Or.inl ?_⟩
      · simp [squareSweepCube, hj]
      · simp [squareSweepCube, hj]
    · apply S.codimTwo
      refine ⟨(Fin.last m).castSucc, Fin.last _,
        Fin.castSucc_ne_last _, Or.inr ?_, Or.inr ?_⟩
      · simp [squareSweepCube, hj]
      · simp [squareSweepCube, hj]

/-- The additive homotopy class of a lower facet. -/
def lowerFaceClass (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.lowerFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

/-- The additive homotopy class of an upper facet. -/
def upperFaceClass (S : CubicalShell d X x) (i : Fin (d + 1)) :
    Additive (HomotopyGroup (Fin d) X x) :=
  Additive.ofMul (⟦S.upperFaceLoop i⟧ : HomotopyGroup (Fin d) X x)

theorem lowerFaceClass_eq_zero [Nonempty (Fin d)] (S : CubicalShell d X x)
    i (h : S.IsConstantFace i 0) :
    S.lowerFaceClass i = 0 := by
  rw [lowerFaceClass, S.lowerFaceLoop_eq_const i h]
  rfl

/-- The four face classes around the last-coordinate square satisfy the square boundary
relation. -/
theorem lastTwoFaceClass_relation {m : ℕ} [Nontrivial (Fin (m + 1))]
    (S : CubicalShell (m + 1) X x) (h : S.LeadingFacesConstant) :
    S.upperFaceClass (Fin.last m).castSucc + S.lowerFaceClass (Fin.last (m + 1)) =
      S.upperFaceClass (Fin.last (m + 1)) + S.lowerFaceClass (Fin.last m).castSucc := by
  have hq :
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last m).castSucc⟧ ⟦S.lowerFaceLoop (Fin.last _)⟧ =
      ((· * ·) : HomotopyGroup (Fin (m + 1)) X x →
          HomotopyGroup (Fin (m + 1)) X x → HomotopyGroup (Fin (m + 1)) X x)
        ⟦S.upperFaceLoop (Fin.last _)⟧ ⟦S.lowerFaceLoop (Fin.last m).castSucc⟧ := by
    rw [HomotopyGroup.mul_spec (i := Fin.last m),
      HomotopyGroup.mul_spec (i := Fin.last m)]
    exact Quotient.sound (S.lastTwoFaceLoops_homotopic h)
  tauto
