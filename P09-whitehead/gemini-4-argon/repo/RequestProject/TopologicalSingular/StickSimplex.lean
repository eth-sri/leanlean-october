module

public import RequestProject.TopologicalSingular.CubicalShell
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

open scoped Topology Topology.Homotopy unitInterval

noncomputable section

namespace FiniteChains.TopologicalSingular

variable {j : ℕ}

def bdry (j : ℕ) : Set (stdSimplex ℝ (Fin (j + 1))) := {x | ∃ i, x.1 i = 0}

def faceMap (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) : stdSimplex ℝ (Fin (j + 2)) :=
  ⟨i.insertNth 0 x.1, (Fin.forall_iff_succAbove i).2 ⟨by simp, by simp [x.2.1]⟩,
    by simp [Fin.sum_univ_succAbove _ i, x.2.2]⟩

@[simp]
theorem faceMap_coe_same (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    (faceMap i x).1 i = 0 := by simp [faceMap]

@[simp]
theorem faceMap_coe_succAbove (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) (k : Fin (j + 1)) :
    (faceMap i x).1 (i.succAbove k) = x.1 k := by simp [faceMap]

theorem faceMap_mem_bdry (i : Fin (j + 2)) (x : stdSimplex ℝ (Fin (j + 1))) :
    faceMap i x ∈ bdry (j + 1) := ⟨i, faceMap_coe_same i x⟩

def stickSimplex : (d : ℕ) → C(I^Fin d, stdSimplex ℝ (Fin (d + 1)))
  | 0 => ContinuousMap.const _ (stdSimplex.vertex (0 : Fin 1))
  | d + 1 =>
      { toFun := fun t =>
          ⟨Fin.cons (1 - (t 0 : ℝ))
              (fun i => (t 0 : ℝ) * stickSimplex d (fun j => t j.succ) i),
            fun i => Fin.cases (sub_nonneg.mpr (t 0).2.2)
              (fun j => mul_nonneg (t 0).2.1 ((stickSimplex d _).2.1 j)) i,
            by simp [Fin.sum_univ_succ, ← Finset.mul_sum]⟩
        continuous_toFun := by
          refine Continuous.subtype_mk (continuous_pi fun i =>
            Fin.cases (by simp only [Fin.cons_zero]; fun_prop) (fun j => ?_) i) _
          simp only [Fin.cons_succ]
          exact (by fun_prop : Continuous fun t : I^Fin (d + 1) => (t 0 : ℝ)).mul
            (((continuous_apply j).comp continuous_subtype_val).comp
              ((stickSimplex d).continuous.comp (by fun_prop))) }

@[simp]
theorem stickSimplex_succ_zero (d : ℕ) (t : I^Fin (d + 1)) :
    stickSimplex (d + 1) t 0 = 1 - (t 0 : ℝ) := rfl

@[simp]
theorem stickSimplex_succ_succ (d : ℕ) (t : I^Fin (d + 1)) (i : Fin (d + 1)) :
    stickSimplex (d + 1) t i.succ = (t 0 : ℝ) * stickSimplex d (fun j => t j.succ) i := rfl

theorem stickSimplex_succ_val (d : ℕ) (t : I^Fin (d + 1)) :
    (⇑(stickSimplex (d + 1) t) : Fin (d + 2) → ℝ) =
      (Fin.cons (1 - (t 0 : ℝ))
        (fun i => (t 0 : ℝ) * stickSimplex d (fun j => t j.succ) i) : Fin (d + 2) → ℝ) := rfl

theorem stickSimplex_cons_val (d : ℕ) (a : I) (t : I^Fin d) :
    (⇑(stickSimplex (d + 1) (Fin.cons a t)) : Fin (d + 2) → ℝ) =
      (Fin.cons (1 - (a : ℝ)) (fun i => (a : ℝ) * stickSimplex d t i) : Fin (d + 2) → ℝ) := by
  rw [stickSimplex_succ_val]; simp only [Fin.cons_zero, Fin.cons_succ]

theorem cubeFace_zero_eq_cons {d : ℕ} (a : I) (t : I^Fin d) :
    cubeFace (0 : Fin (d + 1)) a t = (Fin.cons a t : I^Fin (d + 1)) :=
  Fin.insertNth_zero' a t

theorem cubeFace_succ_eq_cons {d : ℕ} (i : Fin (d + 1)) (a : I) (t : I^Fin (d + 1)) :
    cubeFace i.succ a t = (Fin.cons (t 0) (cubeFace i a (Fin.tail t)) : I^Fin (d + 2)) := by
  change i.succ.insertNth a t = (Fin.cons (t 0) (i.insertNth a (Fin.tail t)) : I^Fin (d + 2))
  rw [← Fin.cons_self_tail t]; exact Fin.insertNth_succ_cons i a (t 0) (Fin.tail t)

theorem faceMap_zero_val {d : ℕ} (s : stdSimplex ℝ (Fin (d + 1))) :
    (⇑(faceMap (0 : Fin (d + 2)) s) : Fin (d + 2) → ℝ) =
      (Fin.cons (0 : ℝ) (⇑s : Fin (d + 1) → ℝ) : Fin (d + 2) → ℝ) :=
  Fin.insertNth_zero' 0 s.1

theorem faceMap_succ_val {d : ℕ} (i : Fin (d + 1)) (s : stdSimplex ℝ (Fin (d + 1))) :
    (⇑(faceMap i.succ s) : Fin (d + 2) → ℝ) =
      (Fin.cons (s 0) (i.insertNth (0 : ℝ) (fun j : Fin d => s j.succ)) : Fin (d + 2) → ℝ) := by
  change (@Fin.insertNth (d + 1) (fun _ : Fin (d + 2) => ℝ) i.succ 0 (⇑s : Fin (d + 1) → ℝ)) = _
  rw [← Fin.cons_self_tail (⇑s : Fin (d + 1) → ℝ), Fin.insertNth_succ_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem mul_insertNth_zero {d : ℕ} (i : Fin (d + 1)) (a : ℝ) (f : Fin d → ℝ) :
    (fun j : Fin (d + 1) => a * (@Fin.insertNth d (fun _ => ℝ) i 0 f) j) =
      @Fin.insertNth d (fun _ => ℝ) i 0 (fun j : Fin d => a * f j) := by
  funext j; refine Fin.succAboveCases i (by simp) (by simp) j

theorem stickSimplex_cubeFace_one : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 1 t) = faceMap i.castSucc (stickSimplex d t)
  | 0, i, t => by
      rw [Fin.eq_zero i, cubeFace_zero_eq_cons]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val, show (0 : Fin 1).castSucc = 0 from rfl, faceMap_zero_val]
      norm_num
  | d + 1, i, t => Fin.cases (by
      rw [cubeFace_zero_eq_cons]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val, show (0 : Fin (d + 2)).castSucc = 0 from rfl, faceMap_zero_val]
      norm_num)
    (fun i => by
      rw [cubeFace_succ_eq_cons]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val, show i.succ.castSucc = i.castSucc.succ from rfl,
        faceMap_succ_val i.castSucc]
      simp only [stickSimplex_succ_zero, stickSimplex_succ_succ]
      apply congrArg (fun f : Fin (d + 2) → ℝ => (Fin.cons (1 - (t 0 : ℝ)) f : Fin (d + 3) → ℝ))
      rw [stickSimplex_cubeFace_one d]
      exact mul_insertNth_zero i.castSucc (t 0 : ℝ)
        (⇑(stickSimplex d (Fin.tail t)) : Fin (d + 1) → ℝ)) i

theorem stickSimplex_cubeFace_last_zero : ∀ (d : ℕ) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace (Fin.last d) 0 t) =
      faceMap (Fin.last (d + 1)) (stickSimplex d t)
  | 0, t => by
      rw [show Fin.last 0 = 0 from rfl, cubeFace_zero_eq_cons]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val, show Fin.last 1 = (0 : Fin 1).succ from rfl, faceMap_succ_val]
      funext j; fin_cases j <;> norm_num [stickSimplex]
  | d + 1, t => by
      rw [show Fin.last (d + 1) = (Fin.last d).succ from rfl, cubeFace_succ_eq_cons]
      apply stdSimplex.ext
      rw [stickSimplex_cons_val, show Fin.last (d + 2) = (Fin.last (d + 1)).succ from rfl,
        faceMap_succ_val]
      simp only [stickSimplex_succ_zero, stickSimplex_succ_succ]
      apply congrArg (fun f : Fin (d + 2) → ℝ => (Fin.cons (1 - (t 0 : ℝ)) f : Fin (d + 3) → ℝ))
      rw [stickSimplex_cubeFace_last_zero d]
      exact mul_insertNth_zero (Fin.last (d + 1)) (t 0 : ℝ)
        (⇑(stickSimplex d (Fin.tail t)) : Fin (d + 1) → ℝ)

theorem stickSimplex_cubeFace_zero_succ : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 0 t) i.succ = 0
  | 0, i, t => by
      rw [Fin.eq_zero i, cubeFace_zero_eq_cons]
      exact zero_mul (stickSimplex 0 t 0)
  | d + 1, i, t => Fin.cases
      (by rw [cubeFace_zero_eq_cons]; exact zero_mul (stickSimplex (d + 1) t 0))
      (fun i => by
        rw [cubeFace_succ_eq_cons]
        change (t 0 : ℝ) * stickSimplex (d + 1) (cubeFace i 0 (Fin.tail t)) i.succ = 0
        rw [stickSimplex_cubeFace_zero_succ d]; ring) i

theorem stickSimplex_cubeFace_zero_last : ∀ (d : ℕ) (i : Fin (d + 1)) (t : I^Fin d),
    stickSimplex (d + 1) (cubeFace i 0 t) (Fin.last (d + 1)) = 0
  | 0, i, t => by simpa [Fin.eq_zero i] using stickSimplex_cubeFace_zero_succ 0 0 t
  | d + 1, i, t => Fin.cases
      (by rw [cubeFace_zero_eq_cons]; exact zero_mul (stickSimplex (d + 1) t (Fin.last (d + 1))))
      (fun i => by
        rw [cubeFace_succ_eq_cons]
        change (t 0 : ℝ) * stickSimplex (d + 1) (cubeFace i 0 (Fin.tail t)) (Fin.last (d + 1)) = 0
        rw [stickSimplex_cubeFace_zero_last d]; ring) i

def simplexCodimTwo (d : ℕ) : Set (stdSimplex ℝ (Fin (d + 1))) :=
  {z | ∃ i j, i ≠ j ∧ z i = 0 ∧ z j = 0}

theorem faceMap_mem_simplexCodimTwo {d : ℕ} (i : Fin (d + 2))
    (z : stdSimplex ℝ (Fin (d + 1))) (hz : z ∈ bdry d) :
    faceMap i z ∈ simplexCodimTwo (d + 1) := by
  obtain ⟨j, hj⟩ := hz
  exact ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, faceMap_coe_same i z,
    (faceMap_coe_succAbove i z j).trans hj⟩

theorem stickSimplex_cubeFace_zero_mem_codimTwo {d : ℕ} (i : Fin (d + 1))
    (hi : i ≠ Fin.last d) (t : I^Fin d) :
    stickSimplex (d + 1) (cubeFace i 0 t) ∈ simplexCodimTwo (d + 1) :=
  ⟨i.succ, Fin.last (d + 1),
    ne_of_lt (Fin.succ_lt_succ_iff.mpr (Fin.lt_last_iff_ne_last.mpr hi)),
    stickSimplex_cubeFace_zero_succ d i t, stickSimplex_cubeFace_zero_last d i t⟩

theorem stickSimplex_mem_bdry (d : ℕ) (t : I^Fin d)
    (ht : t ∈ Cube.boundary (Fin d)) : stickSimplex d t ∈ bdry d := by
  cases d with
  | zero => obtain ⟨i, _⟩ := ht; exact Fin.elim0 i
  | succ d =>
      obtain ⟨i, hi | hi⟩ := ht <;>
        have hrep : t = cubeFace i (t i) (Fin.removeNth i t) :=
          (Fin.insertNth_self_removeNth i t).symm <;>
        rw [hrep, hi]
      · exact ⟨i.succ, stickSimplex_cubeFace_zero_succ d i _⟩
      · rw [stickSimplex_cubeFace_one]; exact faceMap_mem_bdry _ _

theorem mem_cube_boundary_of_stickSimplex_mem_bdry : ∀ (d : ℕ) (t : I^Fin d),
    stickSimplex d t ∈ bdry d → t ∈ Cube.boundary (Fin d) := by
  intro d; induction d with
  | zero =>
      rintro t ⟨i, hi⟩
      rw [Fin.eq_zero i] at hi
      norm_num [stickSimplex, stdSimplex.vertex] at hi
  | succ d ih =>
      rintro t ⟨i, hi⟩
      cases i using Fin.cases with
      | zero =>
        change 1 - (t 0 : ℝ) = 0 at hi
        exact ⟨0, .inr (Subtype.ext (sub_eq_zero.mp hi).symm)⟩
      | succ j =>
        change (t 0 : ℝ) * stickSimplex d (fun k => t k.succ) j = 0 at hi
        rcases mul_eq_zero.mp hi with ht0 | htail
        · exact ⟨0, .inl (Subtype.ext ht0)⟩
        · obtain ⟨k, hk⟩ := ih (fun j => t j.succ) ⟨j, htail⟩
          exact ⟨k.succ, hk⟩

theorem stickSimplex_mem_bdry_iff (d : ℕ) (t : I^Fin d) :
    stickSimplex d t ∈ bdry d ↔ t ∈ Cube.boundary (Fin d) :=
  ⟨mem_cube_boundary_of_stickSimplex_mem_bdry d t, stickSimplex_mem_bdry d t⟩

theorem stickSimplex_injective_of_not_mem_boundary : ∀ (d : ℕ) (t u : I^Fin d),
    t ∉ Cube.boundary (Fin d) → u ∉ Cube.boundary (Fin d) →
      stickSimplex d t = stickSimplex d u → t = u := by
  intro d; induction d with
  | zero => intro _ _ _ _ _; funext i; exact Fin.elim0 i
  | succ d ih =>
      intro t u ht hu hstick
      have hheadReal : (t 0 : ℝ) = (u 0 : ℝ) := by
        have := congrArg (fun z : stdSimplex ℝ (Fin (d + 2)) => z 0) hstick
        simp only [stickSimplex_succ_zero] at this; linarith
      have ht0 : (t 0 : ℝ) ≠ 0 := fun h => ht ⟨0, .inl (Subtype.ext h)⟩
      have htail : Fin.tail t = Fin.tail u :=
        ih (fun j => t j.succ) (fun j => u j.succ)
          (fun ⟨j, hj⟩ => ht ⟨j.succ, hj⟩) (fun ⟨j, hj⟩ => hu ⟨j.succ, hj⟩)
          (stdSimplex.ext (funext fun j => mul_left_cancel₀ ht0 (by
            have := congrArg (fun z : stdSimplex ℝ (Fin (d + 2)) => z j.succ) hstick
            simpa only [stickSimplex_succ_succ, ← hheadReal] using this)))
      rw [← Fin.cons_self_tail t, ← Fin.cons_self_tail u, Subtype.ext hheadReal, htail]

theorem stickSimplex_surjective : ∀ d : ℕ, Function.Surjective (stickSimplex d) := by
  intro d; induction d with
  | zero =>
      intro z; refine ⟨default, stdSimplex.ext (funext fun i => ?_)⟩
      rw [Fin.eq_zero i]; simp [stickSimplex, stdSimplex.vertex]
  | succ d ih =>
      intro z
      let a : ℝ := 1 - z.1 0
      have ha0 : 0 ≤ a := sub_nonneg.mpr (stdSimplex.le_one z 0)
      have hsum : ∑ i : Fin (d + 1), z.1 i.succ = a := by
        have hzsum := z.2.2; rw [Fin.sum_univ_succ] at hzsum
        change z.1 0 + ∑ i : Fin (d + 1), z.1 i.succ = 1 at hzsum
        linarith
      by_cases ha : a = 0
      · let t : I^Fin (d + 1) := Fin.cons 0 0
        refine ⟨t, stdSimplex.ext (funext fun i => ?_)⟩
        cases i using Fin.cases with
        | zero => change 1 - (t 0 : ℝ) = z.1 0; simp [t]; linarith
        | succ j =>
            have hle := Finset.single_le_sum (fun k _ => z.2.1 k.succ) (Finset.mem_univ j)
            have h0 : z.1 j.succ = 0 := le_antisymm (by linarith) (z.2.1 j.succ)
            change (t 0 : ℝ) * _ = z.1 j.succ; simp [t, h0]
      · let ai : I := ⟨a, ha0, sub_le_self 1 (z.2.1 0)⟩
        obtain ⟨u, hu⟩ := ih ⟨fun i => z.1 i.succ / a, fun i => div_nonneg (z.2.1 i.succ) ha0,
          by rw [← Finset.sum_div, hsum, div_self ha]⟩
        refine ⟨Fin.cons ai u, stdSimplex.ext (funext fun i => ?_)⟩
        cases i using Fin.cases with
        | zero => change 1 - (ai : ℝ) = z.1 0; dsimp [ai, a]; ring
        | succ j =>
            change (ai : ℝ) * stickSimplex d u j = z.1 j.succ
            rw [hu]; exact mul_div_cancel₀ _ ha

theorem faceMap_stickSimplex_mem_codimTwo {d : ℕ} (i : Fin (d + 2))
    (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    faceMap i (stickSimplex d t) ∈ simplexCodimTwo (d + 1) :=
  faceMap_mem_simplexCodimTwo i _ (stickSimplex_mem_bdry d t ht)

theorem stickSimplex_cubeFace_mem_codimTwo {d : ℕ} (i : Fin (d + 1)) (a : I)
    (ha : a = 0 ∨ a = 1) (t : I^Fin d) (ht : t ∈ Cube.boundary (Fin d)) :
    stickSimplex (d + 1) (cubeFace i a t) ∈ simplexCodimTwo (d + 1) := by
  rcases ha with rfl | rfl
  · by_cases hi : i = Fin.last d
    · rw [hi, stickSimplex_cubeFace_last_zero]; exact faceMap_stickSimplex_mem_codimTwo _ t ht
    · exact stickSimplex_cubeFace_zero_mem_codimTwo i hi t
  · rw [stickSimplex_cubeFace_one]; exact faceMap_stickSimplex_mem_codimTwo _ t ht
