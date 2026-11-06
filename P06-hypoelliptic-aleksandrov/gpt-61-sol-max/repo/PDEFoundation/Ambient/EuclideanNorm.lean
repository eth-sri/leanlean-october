module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Explicit Euclidean norm on native vectors

`PDE.Vec d = Fin d → ℝ` inherits the finite-product supremum norm. This
module supplies the distinct Euclidean dot product, squared norm, and norm
needed by energy estimates.
-/

@[expose] public section

open scoped BigOperators

namespace PDE

/-- The Euclidean dot product on native project vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i

variable {d : ℕ}

variable (x : Vec d)

/-- The square of the Euclidean norm on native project vectors. -/
def vecNormSq   : ℝ :=
  vecDot x x

/-- The Euclidean norm on native project vectors. -/
noncomputable def vecEuclideanNorm   : ℝ :=
  Real.sqrt (vecNormSq x)

theorem vecDot_comm  (x y : Vec d) :
    vecDot x y = vecDot y x := by
  simp_all [vecDot, mul_comm]

variable (x : Vec d)

theorem vecNormSq_eq_sum_sq   :
    vecNormSq x = ∑ i, x i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

theorem vecNormSq_nonneg   :
    0 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.sum_nonneg fun i _hi => sq_nonneg (x i)

theorem sq_apply_le_vecNormSq   (i : Fin d) :
    x i ^ 2 ≤ vecNormSq x := by
  rw [vecNormSq_eq_sum_sq]
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j))
    (Finset.mem_univ i)

theorem sq_vecDot_le_vecNormSq_mul_vecNormSq  (x y : Vec d) :
    vecDot x y ^ 2 ≤ vecNormSq x * vecNormSq y := by
  simpa [vecDot, vecNormSq, pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq
      (s := Finset.univ) (f := x) (g := y))

variable {x : Vec d}

theorem vecNormSq_eq_zero
    (h : vecNormSq x = 0) :
    x = 0 := by
  funext i

  exact sq_eq_zero_iff.mp (le_antisymm (by
      simpa [h] using sq_apply_le_vecNormSq x i) (sq_nonneg (x i)))

theorem vecNormSq_eq_zero_iff   :
    vecNormSq x = 0 ↔ x = 0 := by
  constructor
  · exact vecNormSq_eq_zero
  · intro hx
    rw [hx]
    simp [vecNormSq, vecDot]

theorem vecNormSq_smul  (c : ℝ) (x : Vec d) :
    vecNormSq (c • x) = c ^ 2 * vecNormSq x := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq]
  calc
    (∑ i, (c • x) i ^ 2) = ∑ i, c ^ 2 * x i ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]

variable (x y : Vec d)

theorem vecNormSq_add_expand   :
    vecNormSq (x + y) =
      vecNormSq x + 2 * vecDot x y + vecNormSq y := by
  simp only [vecNormSq, vecDot, Pi.add_apply]
  rw [Finset.sum_congr rfl (fun i (_hi : i ∈ Finset.univ) =>
    show (x i + y i) * (x i + y i) =
      x i * x i + 2 * (x i * y i) + y i * y i by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem vecNormSq_add_le   :
    vecNormSq (x + y) ≤
      2 * (vecNormSq x + vecNormSq y) := by
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq,
    vecNormSq_eq_sum_sq]
  calc
    (∑ i, (x + y) i ^ 2) ≤
        ∑ i, 2 * (x i ^ 2 + y i ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (x i - y i)]
    _ = 2 * ∑ i, (x i ^ 2 + y i ^ 2) := by
      rw [Finset.mul_sum]
    _ = 2 * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
      rw [Finset.sum_add_distrib]

theorem vecNormSq_weighted_add_le
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (v w : Vec d) :
    vecNormSq (a • v + b • w) ≤
      a * vecNormSq v + b * vecNormSq w := by
  unfold vecNormSq vecDot
  calc
    ∑ i : Fin d, (a • v + b • w) i * (a • v + b • w) i
        ≤ ∑ i : Fin d,
            (a * (v i * v i) + b * (w i * w i)) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hnonneg :
          0 ≤ a * b * (v i - w i) ^ 2 :=
        mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    _ = a * (∑ i : Fin d, v i * v i) +
        b * (∑ i : Fin d, w i * w i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem vecNormSq_neg  (x : Vec d) :
    vecNormSq (-x) = vecNormSq x := by
  rw [← neg_one_smul ℝ x, vecNormSq_smul]
  norm_num

theorem vecNormSq_sub_comm  (x y : Vec d) :
    vecNormSq (x - y) = vecNormSq (y - x) := by
  have hxy : x - y = -(y - x) := by
    ext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hxy, vecNormSq_neg]

variable (x : Vec d)

theorem vecEuclideanNorm_nonneg   :
    0 ≤ vecEuclideanNorm x :=
  Real.sqrt_nonneg _

theorem vecEuclideanNorm_sq   :
    vecEuclideanNorm x ^ 2 = vecNormSq x := Real.sq_sqrt (vecNormSq_nonneg x)

variable {x : Vec d}

theorem vecEuclideanNorm_eq_zero_iff   :
    vecEuclideanNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply vecNormSq_eq_zero
    rw [← vecEuclideanNorm_sq, h]
    norm_num
  · simp_all [vecEuclideanNorm, vecNormSq, vecDot]

theorem vecEuclideanNorm_pos_iff   :
    0 < vecEuclideanNorm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_eq, eq_comm,
    vecEuclideanNorm_eq_zero_iff]
  exact and_iff_right (vecEuclideanNorm_nonneg x)

variable (x : Vec d)

theorem abs_apply_le_vecEuclideanNorm
     (i : Fin d) :
    |x i| ≤ vecEuclideanNorm x := by
  unfold vecEuclideanNorm
  exact Real.abs_le_sqrt (sq_apply_le_vecNormSq x i)

/-- The Euclidean norm is bounded by the coordinate `ℓ¹` norm. -/
theorem vecEuclideanNorm_le_sum_abs   :
    vecEuclideanNorm x ≤ ∑ i : Fin d, |x i| := (Trans.trans
  (Trans.trans rfl
    (Real.sqrt_le_sqrt
      (Eq.mpr (id (congrArg (fun _a => _a ≤ (∑ i, |x i|) ^ 2) (vecNormSq_eq_sum_sq x)))
        (Eq.mp
          (congrFun' (congrArg LE.le (Finset.sum_congr (Eq.refl Finset.univ) fun x_1 a => sq_abs (x x_1)))
            ((∑ i, |x i|) ^ 2))
          (Finset.sum_sq_le_sq_sum_of_nonneg fun i _hi => abs_nonneg (x i))))))
  (Real.sqrt_sq (Finset.sum_nonneg fun i _hi => abs_nonneg (x i))))

theorem abs_vecDot_le_vecEuclideanNorm_mul
    (x y : Vec d) :
    |vecDot x y| ≤ vecEuclideanNorm x * vecEuclideanNorm y := (Trans.trans
  (Trans.trans
    (Trans.trans (Eq.symm (Real.sqrt_sq_eq_abs (vecDot x y)))
      (Real.sqrt_le_sqrt (sq_vecDot_le_vecNormSq_mul_vecNormSq x y)))
    (Real.sqrt_mul (vecNormSq_nonneg x) (vecNormSq y)))
  rfl)

theorem vecEuclideanNorm_smul  (c : ℝ) (x : Vec d) :
    vecEuclideanNorm (c • x) = |c| * vecEuclideanNorm x := by
  rw [vecEuclideanNorm, vecEuclideanNorm, vecNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem vecEuclideanNorm_neg  (x : Vec d) :
    vecEuclideanNorm (-x) = vecEuclideanNorm x := by
  rw [← neg_one_smul ℝ x, vecEuclideanNorm_smul]
  norm_num

variable (x y : Vec d)

theorem vecEuclideanNorm_sub_comm   :
    vecEuclideanNorm (x - y) = vecEuclideanNorm (y - x) := by
  unfold vecEuclideanNorm
  rw [vecNormSq_sub_comm]

theorem vecEuclideanNorm_add_le   :
    vecEuclideanNorm (x + y) ≤
      vecEuclideanNorm x + vecEuclideanNorm y := by


  calc
    vecEuclideanNorm (x + y)
        = Real.sqrt (vecNormSq (x + y)) := rfl
    _ ≤ Real.sqrt
          ((vecEuclideanNorm x + vecEuclideanNorm y) ^ 2) :=
      Real.sqrt_le_sqrt (by


          rw [vecNormSq_add_expand]
          nlinarith [((le_abs_self _).trans (abs_vecDot_le_vecEuclideanNorm_mul x y)), (vecEuclideanNorm_sq x), (vecEuclideanNorm_sq y)])
    _ = vecEuclideanNorm x + vecEuclideanNorm y :=
      Real.sqrt_sq
        (add_nonneg
          (vecEuclideanNorm_nonneg x)
          (vecEuclideanNorm_nonneg y))

variable (x : Vec d)

theorem norm_le_vecEuclideanNorm   :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (vecEuclideanNorm_nonneg x)]
  intro i
  exact abs_apply_le_vecEuclideanNorm x i

theorem vecNormSq_le_natCast_mul_norm_sq   :
    vecNormSq x ≤ (d : ℝ) * ‖x‖ ^ 2 := by
  rw [vecNormSq_eq_sum_sq]
  calc
    (∑ i : Fin d, x i ^ 2) ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hi : |x i| ≤ ‖x‖ := by
        exact norm_le_pi_norm x i
      nlinarith [abs_nonneg (x i), norm_nonneg x, sq_abs (x i)]
    _ = (d : ℝ) * ‖x‖ ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem vecEuclideanNorm_le_sqrt_natCast_mul_norm
     :
    vecEuclideanNorm x ≤ Real.sqrt d * ‖x‖ := by
  calc
    vecEuclideanNorm x = Real.sqrt (vecNormSq x) := rfl
    _ ≤ Real.sqrt ((d : ℝ) * ‖x‖ ^ 2) :=
      Real.sqrt_le_sqrt (vecNormSq_le_natCast_mul_norm_sq x)
    _ = Real.sqrt d * ‖x‖ := by
      simp_all

end PDE
