module

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license.
Adapted from Vilin97/homotopy-groups-lean, commit
c66523531ff172d7f41913d94e56921e790a1b47, Hurewicz/StickSimplex.lean
and elementary face definitions from Hurewicz/SimplexGlue.lean.
The heavy singular-homology imports are replaced by local cubical geometry.
-/
public import RequestProject.TopologicalSingular.CubicalShell
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

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
def bdry (j : ℕ) : Set (stdSimplex ℝ (Fin (j + 1))) := {x | ∃ i, x.1 i = 0}

/-- The `i`-th face inclusion `|Δ^j| → |Δ^{j+1}|`, inserting a zero in slot `i`. -/
def faceMap (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) : stdSimplex ℝ (Fin (j + 2)) :=
  ⟨i.insertNth 0 x.1, by
    refine ⟨(Fin.forall_iff_succAbove i).2 ⟨?_, fun k => ?_⟩, ?_⟩
    · aesop
    · simpa using x.2.1 k
    · rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
      simp only [Fin.insertNth_apply_succAbove]
      rw [zero_add, x.2.2]⟩

@[simp]
theorem faceMap_coe_same (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    (faceMap i x).1 i = 0 := by
  simp [faceMap]

@[simp]
theorem faceMap_coe_succAbove (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) (k : Fin (j + 1)) :
    (faceMap i x).1 (i.succAbove k) = x.1 k := by
  simp [faceMap]

theorem faceMap_mem_bdry (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    faceMap i x ∈ bdry (j + 1) := ⟨i, faceMap_coe_same i x⟩

/-- The stick-breaking map from the `d`-cube to the standard `d`-simplex. -/
def stickSimplex : (d : ℕ) → C(I^Fin d, stdSimplex ℝ (Fin (d + 1)))
  | 0 => ContinuousMap.const _ (stdSimplex.vertex (0 : Fin 1))
  | d + 1 =>
      { toFun := fun t =>
          ⟨Fin.cons (1 - (t 0 : ℝ))
              (fun i => (t 0 : ℝ) * stickSimplex d (fun j => t j.succ) i), by
            constructor
            · intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · exact sub_nonneg.mpr (t 0).2.2
              · exact mul_nonneg (t 0).2.1
                  ((stickSimplex d (fun j => t j.succ)).property.1 j)
            · rw [Fin.sum_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
              ring⟩
        continuous_toFun := by
          apply Continuous.subtype_mk
          apply continuous_pi
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp only [Fin.cons_zero]
            fun_prop
          · simp only [Fin.cons_succ]
            have htail : Continuous (fun t : I^Fin (d + 1) => fun k : Fin d => t k.succ) := by
              fun_prop
            have hrec  :=
              (stickSimplex d).continuous.comp htail
            exact (by fun_prop : Continuous fun t : I^Fin (d + 1) => (t 0 : ℝ)).mul
              (((continuous_apply j).comp continuous_subtype_val).comp hrec) }


@[simp]
theorem stickSimplex_succ_zero (d : ℕ) (t : I^Fin (d + 1)) :
    stickSimplex (d + 1) t 0 = 1 - (t 0 : ℝ) :=
  rfl

@[simp]
theorem stickSimplex_succ_succ (d : ℕ) (t : I^Fin (d + 1)) (i : Fin (d + 1)) :
    stickSimplex (d + 1) t i.succ =
      (t 0 : ℝ) * stickSimplex d (fun j => t j.succ) i :=
  rfl

theorem stickSimplex_cons_val (d : ℕ) (a : I) (t : I^Fin d) :
    (⇑(stickSimplex (d + 1) (Fin.cons a t)) : Fin (d + 2) → ℝ) =
      (Fin.cons (1 - (a : ℝ))
        (fun i => (a : ℝ) * stickSimplex d t i) : Fin (d + 2) → ℝ) := rfl

/-! ### Cubical faces -/

theorem cubeFace_zero_eq_cons {d : ℕ} (a : I) (t : I^Fin d) :
    cubeFace (0 : Fin (d + 1)) a t = (Fin.cons a t : I^Fin (d + 1)) := by
  change Fin.insertNth 0 a t = (Fin.cons a t : I^Fin (d + 1))
  aesop

theorem cubeFace_succ_eq_cons {d : ℕ} (i : Fin (d + 1)) (a : I)
    (t : I^Fin (d + 1)) :
    cubeFace i.succ a t =
      (Fin.cons (t 0) (cubeFace i a (Fin.tail t)) : I^Fin (d + 2)) := by
  change i.succ.insertNth a t =
    (Fin.cons (t 0) (i.insertNth a (Fin.tail t)) : I^Fin (d + 2))
  rw [← Fin.cons_self_tail t]
  exact Fin.insertNth_succ_cons i a (t 0) (Fin.tail t)

/-! ### Compatibility with simplex faces -/

theorem faceMap_zero_val {d : ℕ} (s : stdSimplex ℝ (Fin (d + 1))) :
    (⇑(faceMap (0 : Fin (d + 2)) s) : Fin (d + 2) → ℝ) =
      (Fin.cons (0 : ℝ) (⇑s : Fin (d + 1) → ℝ) : Fin (d + 2) → ℝ) := by
  exact Fin.insertNth_zero' _ _

theorem faceMap_succ_val {d : ℕ} (i : Fin (d + 1))
    (s : stdSimplex ℝ (Fin (d + 1))) :
    (⇑(faceMap i.succ s) : Fin (d + 2) → ℝ) =
      (Fin.cons (s 0)
        (i.insertNth (0 : ℝ) (fun j : Fin d => s j.succ)) :
          Fin (d + 2) → ℝ) := by
  change (@Fin.insertNth (d + 1) (fun _  => ℝ) i.succ
      0 (⇑s)) = _
  rw [← Fin.cons_self_tail (⇑s), Fin.insertNth_succ_cons]
  rfl

theorem mul_insertNth_zero {d : ℕ} (i : Fin (d + 1)) (a : ℝ) (f : Fin d → ℝ) :
    (fun j : Fin (d + 1) => a *
        (@Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) i (0 : ℝ) f) j) =
      @Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) i (0 : ℝ)
        (fun j : Fin d => a * f j) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp
  · simp

private theorem stickSimplex_cubeFace_succ {d : ℕ} (i : Fin (d + 1)) (j : Fin (d + 2))
    (a : I) (t : I^Fin (d + 1))
    (h : stickSimplex (d + 1) (cubeFace i a (Fin.tail t)) =
      faceMap j (stickSimplex d (Fin.tail t))) :
    stickSimplex (d + 2) (cubeFace i.succ a t) = faceMap j.succ (stickSimplex (d + 1) t) := by
  apply stdSimplex.ext
  rw [cubeFace_succ_eq_cons, stickSimplex_cons_val, faceMap_succ_val]
  simp only [stickSimplex_succ_zero, stickSimplex_succ_succ, h]
  congr 1
  exact mul_insertNth_zero j (t 0) _

private theorem stickSimplex_cubeFace_zero_one {d : ℕ} (t : I^Fin d) :
    stickSimplex (d + 1) (cubeFace 0 1 t) = faceMap 0 (stickSimplex d t) := by
  rw [cubeFace_zero_eq_cons]
  apply stdSimplex.ext
  rw [stickSimplex_cons_val, faceMap_zero_val]
  norm_num

/-- The stick-breaking map sends every upper cube face to the simplex face with the same
index. -/
theorem stickSimplex_cubeFace_one : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 1 t) = faceMap i.castSucc (stickSimplex d t)
  | 0, i, t => Fin.eq_zero i ▸ stickSimplex_cubeFace_zero_one t
  | d + 1, i, t => Fin.cases (stickSimplex_cubeFace_zero_one t)
      (fun j => stickSimplex_cubeFace_succ j j.castSucc 1 t
        (stickSimplex_cubeFace_one d j (Fin.tail t))) i

/-- The final lower cube face is the final simplex face. -/
theorem stickSimplex_cubeFace_last_zero : ∀ (d : ℕ) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace (Fin.last d) 0 t) =
      faceMap (Fin.last (d + 1)) (stickSimplex d t)
  | 0, t => by
    change stickSimplex 1 (cubeFace 0 0 t) = faceMap (0 : Fin 1).succ (stickSimplex 0 t)
    rw [cubeFace_zero_eq_cons]
    apply stdSimplex.ext
    rw [stickSimplex_cons_val, faceMap_succ_val]
    funext j
    fin_cases j <;> simp
  | d + 1, t => stickSimplex_cubeFace_succ (Fin.last d) (Fin.last (d + 1)) 0 t
      (stickSimplex_cubeFace_last_zero d (Fin.tail t))

/-- A zero cube coordinate kills all later stick-breaking coordinates. -/
private theorem stickSimplex_zero_suffix : ∀ {d : ℕ} (t : I^Fin d) (i : Fin d)
    (j : Fin (d + 1)), (i : ℕ) < (j : ℕ) → t i = 0 → stickSimplex d t j = 0 := by
  intro d
  induction d with
  | zero => intro t i; exact Fin.elim0 i
  | succ d ih =>
    intro t i j hij ht
    cases j using Fin.cases with
    | zero => simp at hij
    | succ j =>
      cases i using Fin.cases with
      | zero => simp [ht]
      | succ i => simp [ih (fun k => t k.succ) i j (by simpa using hij) ht]

theorem stickSimplex_cubeFace_zero_succ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d) :
    stickSimplex (d + 1) (cubeFace i 0 t) i.succ = 0 :=
  stickSimplex_zero_suffix _ i _ (by simp) (by simp [cubeFace])

theorem stickSimplex_cubeFace_zero_last (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d) :
    stickSimplex (d + 1) (cubeFace i 0 t) (Fin.last (d + 1)) = 0 :=
  stickSimplex_zero_suffix _ i _ i.isLt (by simp [cubeFace])

/-- The codimension-two skeleton of a standard simplex, expressed by two distinct vanishing
barycentric coordinates. -/
def simplexCodimTwo (d : ℕ) : Set (stdSimplex ℝ (Fin (d + 1))) :=
  {z | ∃ i j, i ≠ j ∧ z i = 0 ∧ z j = 0}

/-- A simplex face applied to a boundary point lands in the codimension-two skeleton. -/
theorem faceMap_mem_simplexCodimTwo {d : ℕ} (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) (hz : z ∈ bdry d) :
    faceMap i z ∈ simplexCodimTwo (d + 1) := by
  obtain ⟨j, hj⟩ := hz
  refine ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm,
    faceMap_coe_same i z, ?_⟩
  change (faceMap i z).1 (i.succAbove j) = 0
  simp_all

/-- Every nonfinal lower cube face lands in the codimension-two skeleton. -/
theorem stickSimplex_cubeFace_zero_mem_codimTwo {d : ℕ} (i : Fin (d + 1))
    (hi : i ≠ Fin.last d) (t : I^Fin d) :
    stickSimplex (d + 1) (cubeFace i 0 t) ∈ simplexCodimTwo (d + 1) := by
  have hlt  := Fin.lt_last_iff_ne_last.mpr hi
  have hsucc : i.succ ≠ Fin.last (d + 1) := by
    simp_all
  exact ⟨i.succ, Fin.last (d + 1), hsucc,
    stickSimplex_cubeFace_zero_succ d i t,
    stickSimplex_cubeFace_zero_last d i t⟩

/-- Stick-breaking carries the boundary of the cube into the boundary of the simplex. -/
theorem stickSimplex_mem_bdry (d : ℕ) (t : I^Fin d)
    (ht : t ∈ Cube.boundary (Fin d)) : stickSimplex d t ∈ bdry d := by
  obtain ⟨i, hi | hi⟩ := ht
  · exact ⟨i.succ, stickSimplex_zero_suffix t i _ (by simp) hi⟩
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    have he : cubeFace i 1 (Fin.removeNth i t) = t := by
      simpa [cubeFace, hi] using Fin.insertNth_self_removeNth i t
    rw [← he, stickSimplex_cubeFace_one]
    exact faceMap_mem_bdry _ _

/-- Stick-breaking reflects the boundary: an interior cube point has no vanishing
barycentric coordinate. -/
theorem mem_cube_boundary_of_stickSimplex_mem_bdry : ∀ (d : ℕ) (t : I^Fin d),
    stickSimplex d t ∈ bdry d → t ∈ Cube.boundary (Fin d) := by
  intro d
  induction d with
  | zero =>
      intro t ht
      obtain ⟨i, hi⟩ := ht
      have hi0  := Fin.eq_zero i
      subst i
      norm_num [stickSimplex, stdSimplex.vertex] at hi
  | succ d ih =>
      intro t ht
      obtain ⟨i, hi⟩ := ht
      cases i using Fin.cases with
      | zero =>
        change 1 - (t 0 : ℝ) = 0 at hi
        have ht0 : (t 0 : ℝ) = 1 := by linarith
        exact ⟨0, Or.inr (Subtype.ext ht0)⟩
      | succ j =>
        change (t 0) * stickSimplex d (fun k => t k.succ) j = 0 at hi
        rcases mul_eq_zero.mp hi with ht0 | htail
        · exact ⟨0, Or.inl (Subtype.ext ht0)⟩
        · obtain ⟨k, hk⟩ := ih (fun j => t j.succ) ⟨j, htail⟩
          exact ⟨k.succ, hk⟩

/-- Stick-breaking identifies precisely the cubical and simplicial boundaries. -/
theorem stickSimplex_mem_bdry_iff (d : ℕ) (t : I^Fin d) :
    stickSimplex d t ∈ bdry d ↔ t ∈ Cube.boundary (Fin d) :=
  ⟨mem_cube_boundary_of_stickSimplex_mem_bdry d t, stickSimplex_mem_bdry d t⟩

/-- Stick-breaking is injective away from the cubical boundary. -/
theorem stickSimplex_injective_of_not_mem_boundary : ∀ (d : ℕ) (t u : I^Fin d),
    t ∉ Cube.boundary (Fin d) → u ∉ Cube.boundary (Fin d) →
      stickSimplex d t = stickSimplex d u → t = u := by
  intro d
  induction d with
  | zero => intro t u _ _ _; exact Subsingleton.elim t u
  | succ d ih =>
    intro t u ht hu h
    have h₀ : t 0 = u 0 := Subtype.ext (by simpa using congrArg (fun z => z 0) h)
    have hne : (t 0 : ℝ) ≠ 0 := fun hz => ht ⟨0, Or.inl (Subtype.ext hz)⟩
    have hl : (fun k : Fin d => t k.succ) = (fun k : Fin d => u k.succ) := ih _ _
      (fun ⟨j, hj⟩ => ht ⟨j.succ, hj⟩) (fun ⟨j, hj⟩ => hu ⟨j.succ, hj⟩) (by
        apply stdSimplex.ext
        funext j
        apply mul_left_cancel₀ hne
        simpa only [stickSimplex_succ_succ, ← h₀] using congrArg (fun z => z j.succ) h)
    change Fin.tail t = Fin.tail u at hl
    rw [← Fin.cons_self_tail t, ← Fin.cons_self_tail u, h₀, hl]

/-- Every point of the standard simplex has stick-breaking coordinates. -/
theorem stickSimplex_surjective : ∀ d : ℕ, Function.Surjective (stickSimplex d) := by
  intro d
  induction d with
  | zero => exact fun z => ⟨default, stdSimplex.ext (funext fun i => by simp)⟩
  | succ d ih =>
    intro z
    let a := 1 - z 0
    have ha₀ : 0 ≤ a := sub_nonneg.mpr (stdSimplex.le_one z 0)
    have ha₁ : a ≤ 1 := sub_le_self _ (z.2.1 0)
    have hsum : ∑ i : Fin (d + 1), z i.succ = a := by
      rw [eq_sub_iff_add_eq', ← Fin.sum_univ_succ]
      exact z.2.2
    by_cases ha : a = 0
    · have hz : ∀ j : Fin (d + 1), z j.succ = 0 := fun j =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => z.2.1 k.succ)).1
          (hsum.trans ha) j (Finset.mem_univ j)
      have h₀ : z 0 = 1 := (sub_eq_zero.mp ha).symm
      refine ⟨Fin.cons 0 0, stdSimplex.ext (funext fun j => ?_)⟩
      exact Fin.cases (by simp [h₀]) (fun k => by simp [hz k]) j
    · let y : stdSimplex ℝ (Fin (d + 1)) :=
        ⟨fun i => z i.succ / a, fun i => div_nonneg (z.2.1 i.succ) ha₀,
          by rw [← Finset.sum_div, hsum, div_self ha]⟩
      obtain ⟨u, hu⟩ := ih y
      refine ⟨Fin.cons ⟨a, ha₀, ha₁⟩ u, stdSimplex.ext (funext fun j => ?_)⟩
      refine Fin.cases ?_ (fun k => ?_) j
      · change 1 - a = z 0
        simp [a]
      · change a * stickSimplex d u _ = z _
        rw [hu]
        exact mul_div_cancel₀ _ ha

/-- Every parameterized simplex face takes the cubical boundary into the codimension-two
skeleton of the ambient simplex. -/
theorem faceMap_stickSimplex_mem_codimTwo {d : ℕ} (i : Fin (d + 2))
    (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    faceMap i (stickSimplex d t) ∈ simplexCodimTwo (d + 1) :=
  faceMap_mem_simplexCodimTwo i _ (stickSimplex_mem_bdry d t ht)

/-- A parameterized cubical face, restricted to its own boundary, lands in the codimension-two
skeleton of the simplex. -/
theorem stickSimplex_cubeFace_mem_codimTwo {d : ℕ} (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    stickSimplex (d + 1) (cubeFace i a t) ∈ simplexCodimTwo (d + 1) := by
  rcases ha with rfl | rfl
  · by_cases hi : i = Fin.last d
    · subst i
      rw [stickSimplex_cubeFace_last_zero]
      exact faceMap_stickSimplex_mem_codimTwo _ t ht
    · exact stickSimplex_cubeFace_zero_mem_codimTwo i hi t
  · rw [stickSimplex_cubeFace_one]
    exact faceMap_stickSimplex_mem_codimTwo _ t ht

end FiniteChains.TopologicalSingular
