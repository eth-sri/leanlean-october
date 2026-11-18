module
public import OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex
open scoped BigOperators Topology FourierTransform SchwartzMap Classical

namespace ShortDraftLatticeCount

def q (x : ℤ × ℤ) : ℤ := x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem coordinate_squares (a b D : ℤ) (hD : 0 ≤ D)
    (h : a ^ 2 - a * b + b ^ 2 ≤ D) :
    a ^ 2 ≤ 2 * D ∧ b ^ 2 ≤ 2 * D := by
  constructor <;> nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b)]

theorem finite_lattice_count (S : Finset (ℤ × ℤ)) (D R : ℕ)
    (hR : 2 * D < R ^ 2)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ (2 * R + 1) ^ 2 := by
  let I := Finset.Icc (-(R : ℤ)) (R : ℤ)
  have hbox : S ⊆ I.product I := by
    intro x hx
    rcases x with ⟨a, b⟩
    have hD : (0 : ℤ) ≤ D := by positivity
    obtain ⟨ha, hb⟩ := coordinate_squares a b D hD (hS (a, b) hx)
    have hR' : 2 * (D : ℤ) < (R : ℤ) ^ 2 := by exact_mod_cast hR
    have hRnonneg : (0 : ℤ) ≤ R := by positivity
    apply Finset.mem_product.mpr
    constructor <;> simp only [I, Finset.mem_Icc] <;> constructor <;>
      nlinarith [sq_nonneg (a - R),
      sq_nonneg (a + R), sq_nonneg (b - R), sq_nonneg (b + R)]
  have hI : I.card = 2 * R + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    have hcast : (R : ℤ) + 1 + (R : ℤ) = ((R + 1 + R : ℕ) : ℤ) := by
      push_cast
      ring
    rw [sub_neg_eq_add, hcast, Int.toNat_natCast]
    ring
  calc
    S.card ≤ (I.product I).card := Finset.card_le_card hbox
    _ = I.card * I.card := Finset.card_product _ _
    _ = (2 * R + 1) ^ 2 := by rw [hI]; ring

theorem finite_lattice_count_linear (S : Finset (ℤ × ℤ)) (D : ℕ)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hR : 2 * D < (Nat.sqrt (2 * D) + 1) ^ 2 := by
    exact Nat.lt_succ_sqrt' _
  have hcount := finite_lattice_count S D (Nat.sqrt (2 * D) + 1) hR hS
  have hsquare : (Nat.sqrt (2 * D)) ^ 2 ≤ 2 * D := Nat.sqrt_le' _
  have hroot : Nat.sqrt (2 * D) ≤ 2 * D := Nat.sqrt_le_self _
  nlinarith

theorem actual_eisenstein_count
    (S : Finset ActualEisensteinCoordinates.O) (D : ℕ)
    (hS : ∀ x ∈ S, q (ActualEisensteinCoordinates.coords x) ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hinj : Function.Injective ActualEisensteinCoordinates.coords := by
    intro x y hxy
    calc
      x = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords x).1
          (ActualEisensteinCoordinates.coords x).2 :=
        (ActualEisensteinCoordinates.eval_coords x).symm
      _ = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords y).1
          (ActualEisensteinCoordinates.coords y).2 := by rw [hxy]
      _ = y := ActualEisensteinCoordinates.eval_coords y
  have hbound : ∀ v ∈ S.image ActualEisensteinCoordinates.coords,
      q v ≤ D := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hS x hx
  exact ((Finset.card_image_of_injective S hinj).symm).trans_le (finite_lattice_count_linear _ D hbound)

end ShortDraftLatticeCount

namespace ActualEisensteinCubic

open ShortDraftCusp

theorem A3_cubicChar_neg_one
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) :
    cubicChar P hgood (-1 : O ⧸ P) = 1 := by
  let χ := cubicChar P hgood
  have hcube : χ (-1 : O ⧸ P) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply isUnit_neg_one
  have hminus : (-1 : O ⧸ P) ^ 3 = -1 := by ring
  calc
    χ (-1 : O ⧸ P) = χ ((-1 : O ⧸ P) ^ 3) := by rw [hminus]
    _ = χ (-1 : O ⧸ P) ^ 3 := by rw [map_pow]
    _ = 1 := hcube

end ActualEisensteinCubic

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

end ShortDraftCusp

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

theorem coords_eval (a b : ℤ) :
    coords (eval a b) = (a, b) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext h.1 h.2

theorem qO_mul (x y : O) :
    q (coords (x * y)) = q (coords x) * q (coords y) := by
  have hxy : x * y = eval
      ((coords x).1 * (coords y).1 - (coords x).2 * (coords y).2)
      ((coords x).1 * (coords y).2 + (coords x).2 * (coords y).1 -
        (coords x).2 * (coords y).2) := by
    calc
      x * y = eval (coords x).1 (coords x).2 *
          eval (coords y).1 (coords y).2 := by rw [eval_coords, eval_coords]
      _ = _ := eval_mul _ _ _ _
  rw [hxy, coords_eval]
  exact ShortDraft.eisenstein_norm_mul (coords x) (coords y)

theorem qO_nonneg (x : O) : 0 ≤ q (coords x) := ShortDraft.eisenstein_norm_nonneg (coords x)

theorem qO_pos {x : O} (hx : x ≠ 0) : 0 < q (coords x) := by
  have hne : q (coords x) ≠ 0 := by
    intro hzero
    apply hx
    exact ((eval_coords x).symm).trans (by simp [((ShortDraft.eisenstein_norm_eq_zero_iff (coords x)).mp hzero), eval])
  exact lt_of_le_of_ne (qO_nonneg x) (Ne.symm hne)

def qNat (x : O) : ℕ := (q (coords x)).toNat

theorem qNat_mul (x y : O) : qNat (x * y) = qNat x * qNat y := by
  unfold qNat
  rw [qO_mul]
  exact Int.toNat_mul (qO_nonneg x) (qO_nonneg y)

theorem qNat_pos {x : O} (hx : x ≠ 0) : 0 < qNat x := by
  unfold qNat
  have hcast := Int.toNat_of_nonneg (qO_nonneg x)
  have hpos := qO_pos hx
  omega

theorem finite_multiples_count
    (p : O) (hp : p ≠ 0) (T : Finset O) (D : ℕ)
    (hT : ∀ x ∈ T, qNat (p * x) ≤ D) :
    T.card ≤ 64 * (D / qNat p + 1) := by
  have hbound : ∀ x ∈ T, q (coords x) ≤ (D / qNat p : ℕ) := by
    intro x hx
    have hmul := hT x hx
    rw [qNat_mul] at hmul
    have hdiv : qNat x ≤ D / qNat p :=
      (Nat.le_div_iff_mul_le (qNat_pos hp)).mpr (by
        simpa [mul_comm] using hmul)
    have hnat : qNat x = (q (coords x)) :=
      Int.toNat_of_nonneg (qO_nonneg x)
    have hdiv' : (qNat x : ℤ) ≤ (D / qNat p : ℕ) := by
      exact_mod_cast hdiv
    simpa only [hnat] using hdiv'
  exact actual_eisenstein_count T (D / qNat p) hbound

end ShortDraftLatticeCount

namespace AnalyticBridge

end AnalyticBridge

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

theorem finite_divisible_count
    (p : O) (hp : p ≠ 0) (S : Finset O) (D : ℕ)
    (hdiv : ∀ n ∈ S, p ∣ n)
    (hnorm : ∀ n ∈ S, qNat n ≤ D) :
    S.card ≤ 64 * (D / qNat p + 1) := by
  classical
  let quotient : (x : {n : O // n ∈ S}) → O :=
    fun x => Classical.choose (hdiv x.1 x.2)
  have hrep : ∀ x : {n : O // n ∈ S}, x.1 = p * quotient x := by
    intro x
    exact Classical.choose_spec (hdiv x.1 x.2)
  have hinj : Function.Injective quotient := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.1 = p * quotient x := hrep x
      _ = p * quotient y := by rw [hxy]
      _ = y.1 := (hrep y).symm
  let T := S.attach.image quotient
  have hcard : T.card = S.card := by
    simpa [T] using Finset.card_image_of_injective S.attach hinj
  have hT : ∀ m ∈ T, qNat (p * m) ≤ D := by
    intro m hm
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hm
    rw [← hrep x]
    exact hnorm x.1 x.2
  exact (hcard.symm).trans_le (finite_multiples_count p hp T D hT)

end ShortDraftLatticeCount

namespace IdealGaussCRT

end IdealGaussCRT

namespace ActualEisensteinCubic

section

open ShortDraftLatticeCount

theorem prime_sixth_row_approx
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0) (D : ℕ)
    (hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, p ∈ P i) → p ∣ n)
    (hcolnorm : ∀ n ∈ columns, qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / qNat p + 1) : ℕ) := by
  classical
  let S := columns.filter (fun n => ∃ i ∈ support n, p ∈ P i)
  have hdiv : ∀ n ∈ S, p ∣ n := by
    intro n hn
    obtain ⟨hcol, hsupp⟩ := Finset.mem_filter.mp hn
    exact hfactor n hcol hsupp
  have hnorm : ∀ n ∈ S, qNat n ≤ D := by
    intro n hn
    exact hcolnorm n (Finset.mem_filter.mp hn).1
  calc
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
        ∑ n ∈ S, ‖weight n‖ :=
      finiteSquarefreeRow_difference_norm P hgood columns support weight p
    _ ≤ ∑ n ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro n hn
      exact hweight n (Finset.mem_filter.mp hn).1
    _ = (S.card : ℝ) := by simp
    _ ≤ (64 * (D / qNat p + 1) : ℕ) := by exact_mod_cast (finite_divisible_count p hp S D hdiv hnorm)

end



end ActualEisensteinCubic

end

end OAI
