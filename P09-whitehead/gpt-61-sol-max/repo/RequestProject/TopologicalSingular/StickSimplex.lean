import Mathlib.Tactic

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
def bdry (j : ℕ) : Set (stdSimplex ℝ (Fin (j + 1))) := {x | ∃ i, x.1 i = 0}

variable (i : Fin (j + 2))
  (x : stdSimplex ℝ (Fin (j + 1)))
/-- The `i`-th face inclusion `|Δ^j| → |Δ^{j+1}|`, inserting a zero in slot `i`. -/
def faceMap   : stdSimplex ℝ (Fin (j + 2)) :=
  ⟨i.insertNth 0 x.1, by
    refine ⟨(Fin.forall_iff_succAbove i).2 ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [Fin.insertNth_apply_same]
    · rw [Fin.insertNth_apply_succAbove]; exact x.2.1 k
    · rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
      simp only [Fin.insertNth_apply_succAbove]
      rw [zero_add, x.2.2]⟩

@[simp]
theorem faceMap_coe_same   :
    (faceMap i x).1 i = 0 := by
  simp [faceMap]

@[simp]
theorem faceMap_coe_succAbove   (k : Fin (j + 1)) :
    (faceMap i x).1 (i.succAbove k) = x.1 k := by
  simp [faceMap]

theorem faceMap_mem_bdry   :
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
              simp 
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



variable {d : ℕ}
  (i : Fin (d + 1))
theorem cubeFace_succ_eq_cons   (a : I)
    (t : I^Fin (d + 1)) :
    cubeFace i.succ a t =
      (Fin.cons (t 0) (cubeFace i a (Fin.tail t)) : I^Fin (d + 2)) := by
  
  rw [← Fin.cons_self_tail t]
  exact Fin.insertNth_succ_cons i a (t 0) (Fin.tail t)

/-! ### Compatibility with simplex faces -/

theorem faceMap_zero_val  (s : stdSimplex ℝ (Fin (d + 1))) :
    (⇑(faceMap (0 : Fin (d + 2)) s) : Fin (d + 2) → ℝ) =
      (Fin.cons (0 : ℝ) (⇑s : Fin (d + 1) → ℝ) : Fin (d + 2) → ℝ) := by
  aesop (add simp [faceMap])

theorem faceMap_succ_val  
    (s : stdSimplex ℝ (Fin (d + 1))) :
    (⇑(faceMap i.succ s) : Fin (d + 2) → ℝ) =
      (Fin.cons (s 0)
        (i.insertNth (0 : ℝ) (fun j : Fin d => s j.succ)) :
          Fin (d + 2) → ℝ) := by
  change (@Fin.insertNth (d + 1) (fun _ : Fin (d + 2) => ℝ) i.succ
      (0 : ℝ) (⇑s : Fin (d + 1) → ℝ)) = _
  rw [← Fin.cons_self_tail (⇑s : Fin (d + 1) → ℝ), Fin.insertNth_succ_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem mul_insertNth_zero   (a : ℝ) (f : Fin d → ℝ) :
    (fun j : Fin (d + 1) => a *
        (@Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) i (0 : ℝ) f) j) =
      @Fin.insertNth d (fun _ : Fin (d + 1) => ℝ) i (0 : ℝ)
        (fun j : Fin d => a * f j) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp
  · simp

/-- The stick-breaking map sends every upper cube face to the simplex face with the same
index. -/
theorem stickSimplex_cubeFace_one : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 1 t) = faceMap i.castSucc (stickSimplex d t) := by
  intro d
  induction d with
  | zero =>
      intro i t
      have hi  := Fin.eq_zero i
      subst i
      have hinput : cubeFace (0 : Fin 1) 1 t =
          (Fin.cons 1 t : I^Fin 1) := by
        simp_all
      rw [hinput]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val,
        show (0 : Fin 1).castSucc = (0 : Fin 2) by rfl, faceMap_zero_val]
      norm_num
  | succ d ih =>
      intro i t
      refine Fin.cases ?_ (fun i => ?_) i
      · aesop (add simp [stickSimplex_cons_val, faceMap_zero_val])
      · have hinput : cubeFace i.succ 1 t =
            (Fin.cons (t 0) (cubeFace i 1 (Fin.tail t)) : I^Fin (d + 2)) := by
          
          rw [← Fin.cons_self_tail t]
          exact Fin.insertNth_succ_cons i 1 (t 0) (Fin.tail t)
        rw [hinput]
        apply stdSimplex.ext
        rw [stickSimplex_cons_val,
          show i.succ.castSucc = i.castSucc.succ by rfl,
          faceMap_succ_val i.castSucc]
        aesop (add unsafe apply [mul_insertNth_zero])

/-- The final lower cube face is the final simplex face. -/
theorem stickSimplex_cubeFace_last_zero : ∀ (d : ℕ) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace (Fin.last d) 0 t) =
      faceMap (Fin.last (d + 1)) (stickSimplex d t) := by
  intro d
  induction d with
  | zero =>
      intro t
      have hinput : cubeFace (Fin.last 0) 0 t = (Fin.cons 0 t : I^Fin 1) := by
        simp_all
      rw [hinput]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val,
        show Fin.last 1 = (0 : Fin 1).succ by rfl,
        faceMap_succ_val]
      funext j
      fin_cases j <;> norm_num [stickSimplex]
  | succ d ih =>
      intro t
      have hinput : cubeFace (Fin.last (d + 1)) 0 t =
          (Fin.cons (t 0) (cubeFace (Fin.last d) 0 (Fin.tail t)) : I^Fin (d + 2)) := by
        
        rw [← Fin.cons_self_tail t]
        exact Fin.insertNth_succ_cons (Fin.last d) 0 (t 0) (Fin.tail t)
      rw [hinput]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val,
        show Fin.last (d + 2) = (Fin.last (d + 1)).succ by rfl,
        faceMap_succ_val]
      simp only [stickSimplex_succ_zero, stickSimplex_succ_succ]
      apply congrArg (fun f : Fin (d + 2) → ℝ =>
        (Fin.cons (1 - (t 0 : ℝ)) f : Fin (d + 3) → ℝ))
      rw [ih]
      
      exact mul_insertNth_zero (Fin.last (d + 1)) (t 0 : ℝ)
        (⇑(stickSimplex d (Fin.tail t)) : Fin (d + 1) → ℝ)

/-- On the lower face in cube coordinate `i`, stick-breaking barycentric coordinate `i+1`
vanishes. -/
theorem stickSimplex_cubeFace_zero_succ : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 0 t) i.succ = 0 := by
  intro d
  induction d with
  | zero =>
      simp_all
  | succ d ih =>
      intro i t
      refine Fin.cases ?_ (fun i => ?_) i
      · aesop (add simp [stickSimplex])
      · rw [cubeFace_succ_eq_cons]
        change (t 0 : ℝ) *
            stickSimplex (d + 1) (cubeFace i 0 (Fin.tail t)) i.succ = 0
        rw [ih]
        ring

/-- Every lower cube face is sent into the final simplex face. -/
theorem stickSimplex_cubeFace_zero_last : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 0 t) (Fin.last (d + 1)) = 0 := by
  intro d
  induction d with
  | zero =>
      grind [stickSimplex_cubeFace_zero_succ]
  | succ d ih =>
      intro i t
      refine Fin.cases ?_ (fun i => ?_) i
      · aesop (add simp [stickSimplex])
      · rw [cubeFace_succ_eq_cons]
        change (t 0 : ℝ) *
            stickSimplex (d + 1) (cubeFace i 0 (Fin.tail t)) (Fin.last (d + 1)) = 0
        rw [ih]
        ring

/-- The codimension-two skeleton of a standard simplex, expressed by two distinct vanishing
barycentric coordinates. -/
def simplexCodimTwo (d : ℕ) : Set (stdSimplex ℝ (Fin (d + 1))) :=
  {z | ∃ i j, i ≠ j ∧ z i = 0 ∧ z j = 0}

/-- A simplex face applied to a boundary point lands in the codimension-two skeleton. -/
theorem faceMap_mem_simplexCodimTwo  (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) (hz : z ∈ bdry d) :
    faceMap i z ∈ simplexCodimTwo (d + 1) := by
  obtain ⟨j, hj⟩ := hz
  refine ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm,
    faceMap_coe_same i z, ?_⟩
  change (faceMap i z).1 (i.succAbove j) = 0
  rw [faceMap_coe_succAbove, hj]

/-- Every nonfinal lower cube face lands in the codimension-two skeleton. -/
theorem stickSimplex_cubeFace_zero_mem_codimTwo  
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
  cases d with
  | zero =>
      obtain ⟨i, _⟩ := ht
      exact Fin.elim0 i
  | succ d =>
      obtain ⟨i, hi | hi⟩ := ht
      · have hrep : t = cubeFace i 0 (Fin.removeNth i t) := by
          simp_all
        rw [hrep]
        exact ⟨i.succ, stickSimplex_cubeFace_zero_succ d i (Fin.removeNth i t)⟩
      · have hrep : t = cubeFace i 1 (Fin.removeNth i t) := by
          simp_all
        grind [stickSimplex_cubeFace_one, faceMap_mem_bdry]

/-- Stick-breaking reflects the boundary: an interior cube point has no vanishing
barycentric coordinate. -/
theorem mem_cube_boundary_of_stickSimplex_mem_bdry : ∀ (d : ℕ) (t : I^Fin d),
    stickSimplex d t ∈ bdry d → t ∈ Cube.boundary (Fin d) := by
  intro d
  induction d with
  | zero =>
      intro t ht
      obtain ⟨i, hi⟩ := ht
      have hi0 : i = 0 := Fin.eq_zero i
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
  | zero =>
      intro t u _ _ _
      funext i
      exact Fin.elim0 i
  | succ d ih =>
      intro t u ht hu hstick
      have hheadReal : (t 0 : ℝ) = (u 0 : ℝ) := by
        grind [stickSimplex_succ_zero]
      have hhead  := Subtype.ext hheadReal
      have ht0 : (t 0 : ℝ) ≠ 0 := by
        intro ht0
        exact ht ⟨0, Or.inl (Subtype.ext ht0)⟩
      have httail : (fun j : Fin d => t j.succ) ∉ Cube.boundary (Fin d) := by
        rintro ⟨j, hj⟩
        exact ht ⟨j.succ, hj⟩
      have hutail : (fun j : Fin d => u j.succ) ∉ Cube.boundary (Fin d) := by
        rintro ⟨j, hj⟩
        exact hu ⟨j.succ, hj⟩
      have htailStick : stickSimplex d (fun j => t j.succ) =
          stickSimplex d (fun j => u j.succ) := by
        apply stdSimplex.ext
        funext j
        have hsucc := congrArg (fun z : stdSimplex ℝ (Fin (d + 2)) => z j.succ) hstick
        simp only [stickSimplex_succ_succ] at hsucc
        rw [← hheadReal] at hsucc
        exact mul_left_cancel₀ ht0 hsucc
      have htail := ih (fun j => t j.succ) (fun j => u j.succ)
        httail hutail htailStick
      change Fin.tail t = Fin.tail u at htail
      rw [← Fin.cons_self_tail t, ← Fin.cons_self_tail u, hhead, htail]

/-- Every point of the standard simplex has stick-breaking coordinates. -/
theorem stickSimplex_surjective : ∀ d : ℕ, Function.Surjective (stickSimplex d) := by
  intro d
  induction d with
  | zero =>
      intro z
      refine ⟨default, ?_⟩
      ext <;> simp_all []
  | succ d ih =>
      intro z
      let a  := 1 - z.1 0
      have ha0  := sub_nonneg.mpr (stdSimplex.le_one z 0)
      have ha1 : a ≤ 1 := by
        dsimp [a]
        exact sub_le_self 1 (z.property.1 0)
      by_cases ha : a = 0
      · let t : I^Fin (d + 1) := Fin.cons 0 (fun _ => 0)
        have hz0one : z.1 0 = 1 := by
          dsimp [a] at ha
          linarith
        refine ⟨t, ?_⟩
        apply stdSimplex.ext
        funext i
        cases i using Fin.cases with
        | zero =>
            change 1 - (t 0 : ℝ) = z.1 0
            simp [t, hz0one]
        | succ j =>
            change (t 0 : ℝ) * stickSimplex d (fun k => t k.succ) j = z.1 j.succ
            have hzsum := z.property.2
            rw [Fin.sum_univ_succ] at hzsum
            change z.1 0 + ∑ k : Fin (d + 1), z.1 k.succ = 1 at hzsum
            have hzj_le  :=
              Finset.single_le_sum (fun k _ => z.property.1 k.succ) (Finset.mem_univ j)
            have htailsum : ∑ k : Fin (d + 1), z.1 k.succ = 0 := by
              simp_all
            rw [htailsum] at hzj_le
            have hzjzero  :=
              le_antisymm hzj_le (z.property.1 j.succ)
            simp [t, hzjzero]
      · let ai : I := ⟨a, ha0, ha1⟩
        let y : stdSimplex ℝ (Fin (d + 1)) :=
          ⟨fun i => z.1 i.succ / a,
            fun i => div_nonneg (z.property.1 i.succ) ha0,
            by
              have hzsum := z.property.2
              rw [Fin.sum_univ_succ] at hzsum
              change z.1 0 + ∑ i : Fin (d + 1), z.1 i.succ = 1 at hzsum
              rw [← Finset.sum_div]
              grind⟩
        obtain ⟨u, hu⟩ := ih y
        refine ⟨Fin.cons ai u, ?_⟩
        apply stdSimplex.ext
        funext i
        cases i using Fin.cases with
        | zero =>
            change 1 - (ai : ℝ) = z.1 0
            dsimp [ai, a]
            ring
        | succ j =>
            change (ai : ℝ) * stickSimplex d u j = z.1 j.succ
            rw [hu]
            change a * (z.1 j.succ / a) = z.1 j.succ
            exact mul_div_cancel₀ _ ha

/-- Every parameterized simplex face takes the cubical boundary into the codimension-two
skeleton of the ambient simplex. -/
theorem faceMap_stickSimplex_mem_codimTwo  (i : Fin (d + 2))
    (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    faceMap i (stickSimplex d t) ∈ simplexCodimTwo (d + 1) :=
  faceMap_mem_simplexCodimTwo i _ (stickSimplex_mem_bdry d t ht)

/-- A parameterized cubical face, restricted to its own boundary, lands in the codimension-two
skeleton of the simplex. -/
theorem stickSimplex_cubeFace_mem_codimTwo   (a : I)
    (ha : a = 0 ∨ a = 1) (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    stickSimplex (d + 1) (cubeFace i a t) ∈ simplexCodimTwo (d + 1) := by
  grind [stickSimplex_cubeFace_last_zero, faceMap_stickSimplex_mem_codimTwo, stickSimplex_cubeFace_zero_mem_codimTwo, stickSimplex_cubeFace_one]

end FiniteChains.TopologicalSingular
