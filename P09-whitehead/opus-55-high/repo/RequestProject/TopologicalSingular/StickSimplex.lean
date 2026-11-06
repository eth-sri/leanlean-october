/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
Adapted from Vilin97/homotopy-groups-lean, commit
c66523531ff172d7f41913d94e56921e790a1b47, Hurewicz/StickSimplex.lean
and elementary face definitions from Hurewicz/SimplexGlue.lean.
The heavy singular-homology imports are replaced by local cubical geometry.
-/
import RequestProject.TopologicalSingular.CubicalShell
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Homotopy.HomotopyGroup


/-!
# The stick-breaking cube-to-simplex map

The usual stick-breaking coordinates give a particularly useful map from the `d`-cube to the
standard `d`-simplex.  Recursively, its zeroth barycentric coordinate is `1 - t₀`, while the
remaining coordinates are `t₀` times the stick-breaking coordinates of the tail of `t`.

Unlike an arbitrary cube--simplex homeomorphism, this map is adapted to oriented boundaries:

* setting cube coordinate `i` to `1` gives simplex face `i`;
* setting the last cube coordinate to `0` gives the last simplex face;
* every other lower cube face lands in the codimension-two skeleton.

Thus the nondegenerate pieces of the cubical boundary occur with precisely the alternating signs
of the simplicial boundary.  This is the geometric parameterization used by the higher homotopy
addition argument.
-/

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace FiniteChains.TopologicalSingular

variable {j : ℕ}

/-- The boundary of the standard `j`-simplex: the points with a vanishing coordinate. -/
def bdry j : Set (stdSimplex ℝ (Fin (j + 1))) := {x | ∃ i, x.1 i = 0}

/-- The `i`-th face inclusion `|Δ^j| → |Δ^{j+1}|`, inserting a zero in slot `i`. -/
def faceMap (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) : stdSimplex ℝ (Fin (j + 2)) :=
  ⟨i.insertNth 0 x.1, by
    refine ⟨i.forall_iff_succAbove.2 ⟨?_, fun k => ?_⟩, ?_⟩
    · simp
    · rw [Fin.insertNth_apply_succAbove]; exact x.2.1 k
    · simp [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, zero_add, x.2.2]⟩

@[simp]
theorem faceMap_coe_same i (x : stdSimplex ℝ (Fin (j + 1))) :
    (faceMap i x).1 i = 0 := by
  simp [faceMap]

@[simp]
theorem faceMap_coe_succAbove i x (k : Fin (j + 1)) :
    (faceMap i x).1 (i.succAbove k) = x.1 k := by
  simp [faceMap]

theorem faceMap_mem_bdry i x :
    faceMap i x ∈ bdry (j + 1) := ⟨i, faceMap_coe_same i x⟩

/-- The stick-breaking map from the `d`-cube to the standard `d`-simplex. -/
def stickSimplex : (d : ℕ) → C(I^Fin d, stdSimplex ℝ (Fin (d + 1)))
  | 0 => ContinuousMap.const _ (stdSimplex.vertex (0 : Fin 1))
  | d + 1 =>
      { toFun := fun t =>
          ⟨Fin.cons (1 - (t 0 : ℝ))
              ((t 0 : ℝ) * stickSimplex d (fun j => t j.succ) ·), by
            constructor
            · intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · exact sub_nonneg.mpr (t 0).2.2
              · exact mul_nonneg (t 0).2.1
                  ((stickSimplex d (t ·.succ)).property.1 j)
            · simp [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum, stdSimplex.sum_eq_one]⟩
        continuous_toFun := by
          apply Continuous.subtype_mk
          apply continuous_pi
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [Fin.cons_zero]
            fun_prop
          · have htail : Continuous (fun t : I^Fin (d + 1) => fun k : Fin d => t k.succ) := by
              fun_prop
            have hrec : Continuous
                (fun t : I^Fin (d + 1) => stickSimplex d (fun k : Fin d => t k.succ)) :=
              by fun_prop
            exact (by fun_prop : Continuous fun t : I^Fin (d + 1) => (t 0 : ℝ)).mul
              (((continuous_apply j).comp continuous_subtype_val).comp hrec) }

@[simp]
theorem stickSimplex_zero t :
    stickSimplex 0 t = stdSimplex.vertex (0 : Fin 1) :=
  rfl

@[simp]
theorem stickSimplex_succ_zero d t :
    stickSimplex (d + 1) t 0 = 1 - (t 0) :=
  rfl

@[simp]
theorem stickSimplex_succ_succ d t i :
    stickSimplex (d + 1) t i.succ =
      (t 0) * stickSimplex d (t ·.succ) i :=
  rfl


theorem stickSimplex_cons_val d a (t : I^Fin d) :
    (⇑(stickSimplex (d + 1) (Fin.cons a t))) =
      (Fin.cons (1 - a)
        (a * stickSimplex d t ·) : Fin (d + 2) → ℝ) := by
  rfl

/-! ### Cubical faces -/


theorem cubeFace_succ_eq_cons i a
    t :
    cubeFace i.succ a t =
      (Fin.cons (t 0) (cubeFace i a (Fin.tail t)) : I^Fin (d + 2)) := by
  rw [← Fin.cons_self_tail t]
  exact i.insertNth_succ_cons a _ _

/-! ### Compatibility with simplex faces -/

theorem faceMap_zero_val s :
    (⇑(faceMap 0 s)) =
      (Fin.cons 0 (⇑s) : Fin (d + 2) → ℝ) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  rfl

theorem faceMap_succ_val (i : Fin (d + 1))
    s :
    (⇑(faceMap i.succ s)) =
      (Fin.cons (s 0)
        (i.insertNth 0 (s ·.succ)) :
          Fin (d + 2) → ℝ) := by
  change (@Fin.insertNth _ (fun _ : Fin (d + 2) => ℝ) i.succ
      (0) (⇑s)) = _
  rw [← Fin.cons_self_tail (⇑s : Fin (d + 1) → ℝ), Fin.insertNth_succ_cons]
  rfl

theorem mul_insertNth_zero {d : ℕ} (i : Fin (d + 1)) (a : ℝ) (f : Fin d → ℝ) :
    (fun j : Fin (d + 1) => a *
        (@Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) i (0 : ℝ) f) j) =
      @Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) i 0
        (a * f ·) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp
  · simp

/-- The stick-breaking map sends every upper cube face to the simplex face with the same
index. -/
theorem stickSimplex_cubeFace_one : ∀ d i t,
    stickSimplex (d + 1) (cubeFace i 1 t) = faceMap i.castSucc (stickSimplex d t) := by
  intro d
  induction d with
  | zero =>
      intro i t
      have hi := i.eq_zero
      subst i
      have hinput : cubeFace (0) 1 t =
          (Fin.cons 1 t) := Fin.insertNth_zero' 1 t
      rw [hinput]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val,
        show (0 : Fin 1).castSucc = (0) by rfl, faceMap_zero_val]
      norm_num
  | succ d ih =>
      intro i t
      refine Fin.cases ?_ (fun i => ?_) i
      · have hinput : cubeFace (0) 1 t =
            (Fin.cons 1 t) := Fin.insertNth_zero' 1 t
        rw [hinput]
        apply stdSimplex.ext
        rw [stickSimplex_cons_val,
          show (0 : Fin (d + 2)).castSucc = (0) by rfl,
          faceMap_zero_val]
        norm_num
      · have hinput : cubeFace i.succ 1 t =
            (Fin.cons (t 0) (cubeFace i 1 (Fin.tail t))) := by
          rw [← Fin.cons_self_tail t]
          exact i.insertNth_succ_cons 1 _ _
        rw [hinput]
        apply stdSimplex.ext
        rw [stickSimplex_cons_val,
          show i.succ.castSucc = i.castSucc.succ by rfl,
          faceMap_succ_val i.castSucc]
        apply congrArg _
        rw [ih]
        exact mul_insertNth_zero i.castSucc _
          _

/-- The final lower cube face is the final simplex face. -/
theorem stickSimplex_cubeFace_last_zero : ∀ d t,
    stickSimplex (d + 1) (cubeFace (Fin.last d) 0 t) =
      faceMap (Fin.last (d + 1)) (stickSimplex d t) := by
  intro d
  induction d with
  | zero =>
      intro t
      have hinput : cubeFace (Fin.last 0) 0 t = (Fin.cons 0 t) := Fin.insertNth_zero' 0 t
      rw [hinput]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val,
        show Fin.last 1 = (0 : Fin 1).succ by rfl,
        faceMap_succ_val]
      funext j
      fin_cases j <;> norm_num [stickSimplex]
  | succ d ih =>
      intro t
      have hinput : cubeFace (Fin.last _) 0 t =
          (Fin.cons (t 0) (cubeFace (Fin.last d) 0 (Fin.tail t))) := by
        rw [← Fin.cons_self_tail t]
        exact Fin.insertNth_succ_cons (Fin.last d) 0 _ _
      rw [hinput]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val,
        show Fin.last _ = (Fin.last _).succ by rfl,
        faceMap_succ_val]
      apply congrArg _
      rw [ih]
      exact mul_insertNth_zero _ _
        _

/-- On the lower face in cube coordinate `i`, stick-breaking barycentric coordinate `i+1`
vanishes. -/
theorem stickSimplex_cubeFace_zero_succ : ∀ d i t,
    stickSimplex (d + 1) (cubeFace i 0 t) i.succ = 0 := by
  intro d
  induction d with
  | zero =>
      simp
  | succ d ih =>
      intro i t
      refine Fin.cases ?_ (fun i => ?_) i
      · change (0) * stickSimplex _ t 0 = 0
        ring
      · simp [cubeFace_succ_eq_cons, ih]

/-- Every lower cube face is sent into the final simplex face. -/
theorem stickSimplex_cubeFace_zero_last : ∀ d i t,
    stickSimplex (d + 1) (cubeFace i 0 t) (Fin.last (d + 1)) = 0 := by
  intro d
  induction d with
  | zero =>
      intro i t
      simpa only [show i = 0 by exact i.eq_zero,
        show Fin.last 1 = (0 : Fin 1).succ by rfl] using
          stickSimplex_cubeFace_zero_succ 0 _ t
  | succ d ih =>
      intro i t
      refine Fin.cases ?_ (fun i => ?_) i
      · change (0) * stickSimplex _ t (Fin.last _) = 0
        ring
      · rw [cubeFace_succ_eq_cons]
        change (t 0) *
            stickSimplex _ (cubeFace i 0 (Fin.tail t)) (Fin.last _) = 0
        simp_all

/-- The codimension-two skeleton of a standard simplex, expressed by two distinct vanishing
barycentric coordinates. -/
def simplexCodimTwo d : Set (stdSimplex ℝ (Fin (d + 1))) :=
  {z | ∃ i j, i ≠ j ∧ z i = 0 ∧ z j = 0}

/-- A simplex face applied to a boundary point lands in the codimension-two skeleton. -/
theorem faceMap_mem_simplexCodimTwo i
    z (hz : z ∈ bdry d) :
    faceMap i z ∈ simplexCodimTwo (d + 1) := by
  cases' hz with j hj
  refine ⟨i, i.succAbove j, (i.succAbove_ne j).symm,
    faceMap_coe_same i z, ?_⟩
  change (faceMap i z).1 (i.succAbove j) = 0
  simp_all

/-- Every nonfinal lower cube face lands in the codimension-two skeleton. -/
theorem stickSimplex_cubeFace_zero_mem_codimTwo i
    (hi : i ≠ Fin.last d) t :
    stickSimplex (d + 1) (cubeFace i 0 t) ∈ simplexCodimTwo (d + 1) := by
  have hlt := Fin.lt_last_iff_ne_last.mpr hi
  have hsucc : i.succ ≠ Fin.last _ := by
    simp_all
  exact ⟨i.succ, Fin.last _, hsucc,
    stickSimplex_cubeFace_zero_succ d i t,
    stickSimplex_cubeFace_zero_last d i t⟩

/-- Stick-breaking carries the boundary of the cube into the boundary of the simplex. -/
theorem stickSimplex_mem_bdry d t
    (ht : t ∈ Cube.boundary (Fin d)) : stickSimplex d t ∈ bdry d := by
  cases d with
  | zero =>
      cases' ht with i _
      exact i.elim0
  | succ d =>
      obtain ⟨i, hi | hi⟩ := ht
      · have hrep : t = cubeFace i 0 (i.removeNth t) := by
          calc
            t = i.insertNth (t i) (i.removeNth t) :=
              (i.insertNth_self_removeNth t).symm
            _ = i.insertNth 0 (i.removeNth t) := by simp_all
            _ = cubeFace i 0 (i.removeNth t) := rfl
        rw [hrep]
        exact ⟨i.succ, stickSimplex_cubeFace_zero_succ d i _⟩
      · have hrep : t = cubeFace i 1 (i.removeNth t) := by
          calc
            t = i.insertNth (t i) (i.removeNth t) :=
              (i.insertNth_self_removeNth t).symm
            _ = i.insertNth 1 (i.removeNth t) := by simp_all
            _ = cubeFace i 1 (i.removeNth t) := rfl
        rw [hrep, stickSimplex_cubeFace_one]
        exact faceMap_mem_bdry i.castSucc _

/-- Stick-breaking reflects the boundary: an interior cube point has no vanishing
barycentric coordinate. -/
theorem mem_cube_boundary_of_stickSimplex_mem_bdry : ∀ d t,
    stickSimplex d t ∈ bdry d → t ∈ Cube.boundary (Fin d) := by
  intro d
  induction d with
  | zero =>
      intro t ht
      cases' ht with i hi
      have hi0 := i.eq_zero
      simp_all
  | succ d ih =>
      intro t ht
      cases' ht with i hi
      cases i using Fin.cases with
      | zero =>
        change 1 - (t 0 : ℝ) = 0 at hi
        have ht0 : (t 0 : ℝ) = 1 := by linarith
        exact ⟨0, Or.inr (Subtype.ext ht0)⟩
      | succ j =>
        rcases mul_eq_zero.mp hi with ht0 | htail
        · exact ⟨0, Or.inl (Subtype.ext ht0)⟩
        · cases' ih _ ⟨j, htail⟩ with k hk
          exact ⟨k.succ, hk⟩

/-- Stick-breaking identifies precisely the cubical and simplicial boundaries. -/
theorem stickSimplex_mem_bdry_iff d t :
    stickSimplex d t ∈ bdry d ↔ t ∈ Cube.boundary (Fin d) :=
  ⟨mem_cube_boundary_of_stickSimplex_mem_bdry d t, stickSimplex_mem_bdry d t⟩

/-- Stick-breaking is injective away from the cubical boundary. -/
theorem stickSimplex_injective_of_not_mem_boundary : ∀ d t u,
    t ∉ Cube.boundary (Fin d) → u ∉ Cube.boundary (Fin d) →
      stickSimplex d t = stickSimplex d u → t = u := by
  intro d
  induction d with
  | zero =>
      simp
  | succ d ih =>
      intro t u ht hu hstick
      have hheadReal : (t 0 : ℝ) = (u 0) := by
        grind [stickSimplex_succ_zero]
      have hhead := Subtype.ext hheadReal
      have ht0 : (t 0 : ℝ) ≠ 0 := by
        intro ht0
        exact ht ⟨0, Or.inl (Subtype.ext ht0)⟩
      have httail : (fun j : Fin d => t j.succ) ∉ Cube.boundary _ := by
        rintro ⟨j, hj⟩
        exact ht ⟨j.succ, hj⟩
      have hutail : (fun j : Fin d => u j.succ) ∉ Cube.boundary _ := by
        rintro ⟨j, hj⟩
        exact hu ⟨j.succ, hj⟩
      have htailStick : stickSimplex d (t ·.succ) =
          stickSimplex d (u ·.succ) := by
        apply stdSimplex.ext
        funext j
        have hsucc := congrArg (· j.succ) hstick
        grind [stickSimplex_succ_succ]
      have htail := ih _ _
        httail hutail htailStick
      change Fin.tail t = Fin.tail u at htail
      rw [← Fin.cons_self_tail t, ← Fin.cons_self_tail u, hhead, htail]

/-- Every point of the standard simplex has stick-breaking coordinates. -/
theorem stickSimplex_surjective : ∀ d, Function.Surjective (stickSimplex d) := by
  intro d
  induction d with
  | zero =>
      intro z
      refine ⟨default, ?_⟩
      apply stdSimplex.ext
      funext i
      simp
  | succ d ih =>
      intro z
      let a := 1 - z.1 0
      have ha0 := sub_nonneg.mpr (stdSimplex.le_one z 0)
      have ha1 := sub_le_self 1 (z.property.1 0)
      by_cases ha : a = 0
      · let t : I^Fin (d + 1) := Fin.cons 0 (fun _ => 0)
        have hz0one : z.1 0 = 1 := by
          linarith
        refine ⟨t, ?_⟩
        apply stdSimplex.ext
        funext i
        cases i using Fin.cases with
        | zero =>
            change 1 - (t 0) = z.1 0
            aesop
        | succ j =>
            change (t 0) * stickSimplex d (t ·.succ) j = z.1 j.succ
            have hzsum := z.property.2
            rw [Fin.sum_univ_succ] at hzsum
            have hzj_le :=
              Finset.single_le_sum (fun k _ => z.property.1 k.succ) (Finset.mem_univ j)
            have htailsum : ∑ k : Fin (d + 1), z.1 k.succ = 0 := by
              simp_all
            rw [htailsum] at hzj_le
            have hzjzero :=
              le_antisymm hzj_le (z.property.1 j.succ)
            aesop
      · let ai : I := by tauto
        let y : stdSimplex ℝ (Fin (d + 1)) :=
          ⟨fun i => z.1 i.succ / a,
            fun i => div_nonneg (z.property.1 i.succ) ha0,
            by
              have hzsum := z.property.2
              rw [Fin.sum_univ_succ] at hzsum
              rw [← Finset.sum_div]
              grind⟩
        cases' ih y with u hu
        refine ⟨Fin.cons ai u, ?_⟩
        apply stdSimplex.ext
        funext i
        cases i using Fin.cases with
        | zero =>
            aesop
        | succ j =>
            change ai * stickSimplex d u j = z.1 j.succ
            rw [hu]
            exact mul_div_cancel₀ _ ha

/-- Every parameterized simplex face takes the cubical boundary into the codimension-two
skeleton of the ambient simplex. -/
theorem faceMap_stickSimplex_mem_codimTwo i
    t (ht : t ∈ Cube.boundary (Fin d)) :
    faceMap i (stickSimplex d t) ∈ simplexCodimTwo (d + 1) :=
  faceMap_mem_simplexCodimTwo i _ (stickSimplex_mem_bdry d t ht)

/-- A parameterized cubical face, restricted to its own boundary, lands in the codimension-two
skeleton of the simplex. -/
theorem stickSimplex_cubeFace_mem_codimTwo i a
    (ha : a = 0 ∨ a = 1) t (ht : t ∈ Cube.boundary (Fin d)) :
    stickSimplex (d + 1) (cubeFace i a t) ∈ simplexCodimTwo (d + 1) := by
  rcases ha with rfl | rfl
  · by_cases hi : i = Fin.last d
    · subst i
      rw [stickSimplex_cubeFace_last_zero]
      exact faceMap_stickSimplex_mem_codimTwo _ t ht
    · exact stickSimplex_cubeFace_zero_mem_codimTwo i hi t
  · rw [stickSimplex_cubeFace_one]
    exact faceMap_stickSimplex_mem_codimTwo _ t ht
