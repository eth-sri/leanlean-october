module

public import OAI.LinearAlgebra.MatrixMultiplication.Model
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic

public section

@[expose] section

namespace OAI.MatrixMultiplication

noncomputable section

open Set Filter Polynomial
open scoped BigOperators Classical Topology

universe u

/-! ### Core Tensors & Polynomial Degeneration -/

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

section Poly
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K) (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T x y z

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def prodTensor {n : ℕ} (F : Fin n → Tensor K X Y Z) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, F i (x i) (y i) (z i)

abbrev power (T : Tensor K X Y Z) (n : ℕ) := prodTensor fun _ : Fin n => T

abbrev pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0) (fun z' z => if z = fz z' then 1 else 0) T := by
  funext x y z; simp [pullback, restrict, ite_mul, mul_ite]

end Poly

def RankAtMost {X Y Z : Type*} (T : Tensor ℤ X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → ℤ) (b : Fin r → Y → ℤ) (c : Fin r → Z → ℤ),
    ∀ x y z, T x y z = ∑ i, a i x * b i y * c i z

def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor ℤ (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

def dotPairing (U : Type*) [DecidableEq U] : Tensor ℤ U U Unit :=
  fun i j _ => if i = j then 1 else 0

abbrev cyclic {X Y Z : Type*} (T : Tensor ℤ X Y Z) : Tensor ℤ Y Z X := fun y z x => T x y z

theorem RankAtMost.card_le_of_identity {X Y Z ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor ℤ X Y Z} {r : ℕ} (hT : RankAtMost T r) (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hid : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) : Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) ℤ := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι ℤ := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι ℤ) := funext fun i => funext fun j =>
    (heq (x i) (y i) (z j)).symm.trans (hid i j)
  refine (card_le_of_injective ℤ R.mulVecLin fun v w hvw => ?_).trans_eq (Fintype.card_fin r)
  simpa only [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hmul, Matrix.mulVecLin_one,
    LinearMap.id_apply] using congrArg L.mulVecLin hvw

structure PolynomialRestrictionDegeneration {F X Y Z X' Y' Z' : Type*} [CommRing F]
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor F X Y Z) (U : Tensor F X' Y' Z') (k Lx Ly : ℕ) where
  leftMap : X' → X → F[X]
  middleMap : Y' → Y → F[X]
  rightMap : Z' → Z → F[X]
  left_degree : ∀ x' x, (leftMap x' x).degree ≤ Lx
  middle_degree : ∀ y' y, (middleMap y' y).degree ≤ Ly
  vanishes : ∀ x' y' z' j, j < k →
    (restrict leftMap middleMap rightMap (fun x y z => C (T x y z)) x' y' z').coeff j = 0
  leading : ∀ x' y' z',
    (restrict leftMap middleMap rightMap (fun x y z => C (T x y z)) x' y' z').coeff k = U x' y' z'

end Tensor

abbrev matrixMultiplicationTensor (a b c : ℕ) : Tensor ℤ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  Tensor.matrixCoefficients (Fin a) (Fin b) (Fin c)

def convolution (a b : ℕ) : Tensor ℤ (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

def unitTensor {K : Type*} [One K] : Tensor K Unit Unit Unit := fun _ _ _ => 1

def sharedFirstTensor {K X Y Z : Type*} [Zero K] {M : ℕ} (B : Fin M → Tensor K X Y Z) :
    Tensor K X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

theorem restrict_directSum {R X Y Z U V W ι : Type*} [CommSemiring R]
    [Fintype U] [Fintype V] [Fintype W] [Fintype ι] [DecidableEq ι]
    (T : ι → Tensor R U V W) (A : ι → X → U → R) (B : ι → Y → V → R) (C : ι → Z → W → R) :
    Tensor.restrict (fun x q => A q.1 x q.2) (fun y q => B q.1 y q.2) (fun z q => C q.1 z q.2)
      (Tensor.directSum T) = fun x y z => ∑ i, Tensor.restrict (A i) (B i) (C i) (T i) x y z := by
  funext x y z; simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, ite_and]

def shiftedCoeff {R : Type*} [CommSemiring R] (p : R[X]) (h shift : ℕ) : R :=
  if shift ≤ h then p.coeff (h - shift) else 0

theorem sum_comm_three {R U V W ι : Type*} [CommSemiring R] [Fintype U] [Fintype V] [Fintype W] [Fintype ι]
    (f : ι → U → V → W → R) :
    (∑ u, ∑ v, ∑ w, ∑ i, f i u v w) = ∑ i, ∑ u, ∑ v, ∑ w, f i u v w := by
  calc (∑ u, ∑ v, ∑ w, ∑ i, f i u v w)
      = ∑ p : U × V × W, ∑ i, f i p.1 p.2.1 p.2.2 := by simp [Fintype.sum_prod_type]
    _ = ∑ i, ∑ p : U × V × W, f i p.1 p.2.1 p.2.2 := Finset.sum_comm
    _ = _ := by simp [Fintype.sum_prod_type]

namespace Tensor.PolynomialRestrictionDegeneration

variable {R X Y Z X' Y' Z' : Type*} [CommRing R] [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor R X Y Z} {U : Tensor R X' Y' Z'} {k Lx Ly : ℕ}

theorem prod_degree_le {R A B : Type*} [CommRing R] {d n : ℕ}
    (M : A → B → R[X]) (hM : ∀ a b, (M a b).degree ≤ d)
    (a : Fin n → A) (b : Fin n → B) : (∏ i : Fin n, M (a i) (b i)).degree ≤ ((d * n : ℕ) : WithBot ℕ) :=
  degree_le_of_natDegree_le <| (natDegree_prod_le _ _).trans <|
    (Finset.sum_le_sum fun i _ => natDegree_le_of_degree_le (hM (a i) (b i))).trans_eq (by simp [Nat.mul_comm n d])

def power (L : PolynomialRestrictionDegeneration T U k Lx Ly) (n : ℕ) :
    PolynomialRestrictionDegeneration (Tensor.power T n) (Tensor.power U n) (k * n) (Lx * n) (Ly * n) := by
  let base : Tensor R[X] X' Y' Z' := Tensor.restrict L.leftMap L.middleMap L.rightMap fun x y z => C (T x y z)
  let N : Tensor R[X] X' Y' Z' := fun x y z => (X_pow_dvd_iff.2 (L.vanishes x y z)).choose
  have hN (x y z) : base x y z = Polynomial.X ^ k * N x y z :=
    (X_pow_dvd_iff.2 (L.vanishes x y z)).choose_spec
  have hN0 (x y z) : (N x y z).coeff 0 = U x y z := by
    have h := L.leading x y z; change (base x y z).coeff k = U x y z at h
    rw [hN] at h; simpa [coeff_X_pow_mul'] using h
  have hbase : Tensor.restrict (fun x u => ∏ i : Fin n, L.leftMap (x i) (u i))
      (fun y v => ∏ i : Fin n, L.middleMap (y i) (v i)) (fun z w => ∏ i : Fin n, L.rightMap (z i) (w i))
      (fun u v w => C (Tensor.power T n u v w)) = Tensor.power base n := by
    funext x y z
    simp only [Tensor.restrict, Tensor.power, Tensor.prodTensor, base, map_prod,
      Fintype.prod_sum, Finset.prod_mul_distrib]
  have hprod (x y z) : Tensor.power base n x y z = Polynomial.X ^ (k * n) * Tensor.power N n x y z := by
    simp [Tensor.power, Tensor.prodTensor, hN, Finset.prod_mul_distrib, ← pow_mul]
  exact {
    leftMap := fun x u => ∏ i : Fin n, L.leftMap (x i) (u i)
    middleMap := fun y v => ∏ i : Fin n, L.middleMap (y i) (v i)
    rightMap := fun z w => ∏ i : Fin n, L.rightMap (z i) (w i)
    left_degree := prod_degree_le L.leftMap L.left_degree
    middle_degree := prod_degree_le L.middleMap L.middle_degree
    vanishes := fun x y z j hj => by rw [hbase, hprod, coeff_X_pow_mul']; simp [Nat.not_le_of_lt hj]
    leading := fun x y z => by rw [hbase, hprod, coeff_X_pow_mul']; simp [Tensor.power, Tensor.prodTensor, coeff_zero_prod, hN0] }

theorem extract (L : PolynomialRestrictionDegeneration T U k Lx Ly) :
    U = Tensor.restrict
      (fun x (q : (Fin (Lx + 1) × Fin (Ly + 1)) × X) => (L.leftMap x q.2).coeff q.1.1)
      (fun y (q : (Fin (Lx + 1) × Fin (Ly + 1)) × Y) => (L.middleMap y q.2).coeff q.1.2)
      (fun z (q : (Fin (Lx + 1) × Fin (Ly + 1)) × Z) => shiftedCoeff (L.rightMap z q.2) k (q.1.1.val + q.1.2.val))
      (Tensor.directSum fun _ : Fin (Lx + 1) × Fin (Ly + 1) => T) := by
  have hmul (p q t : R[X]) (hp : p.natDegree ≤ Lx) (hq : q.natDegree ≤ Ly) :
      (p * q * t).coeff k = ∑ i : Fin (Lx + 1), ∑ j : Fin (Ly + 1),
        p.coeff i * q.coeff j * shiftedCoeff t k (i.val + j.val) := by
    have ep : p = ∑ i : Fin (Lx + 1), monomial i.val (p.coeff i) :=
      (p.as_sum_range' (Lx + 1) (Nat.lt_succ_of_le hp)).trans
        (Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i)) (Lx + 1)).symm
    have eq : q = ∑ j : Fin (Ly + 1), monomial j.val (q.coeff j) :=
      (q.as_sum_range' (Ly + 1) (Nat.lt_succ_of_le hq)).trans
        (Fin.sum_univ_eq_sum_range (fun j => monomial j (q.coeff j)) (Ly + 1)).symm
    have hmon (r : R) (s : ℕ) : (monomial s r * t).coeff k = r * shiftedCoeff t k s := by
      rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']; rfl
    conv_lhs => rw [ep, eq]
    simp only [Finset.sum_mul, Finset.mul_sum, finsetSum_coeff, monomial_mul_monomial, hmon]
    exact Finset.sum_comm
  rw [restrict_directSum (fun _ : Fin (Lx + 1) × Fin (Ly + 1) => T)
    (fun q x u => (L.leftMap x u).coeff q.1) (fun q y v => (L.middleMap y v).coeff q.2)
    (fun q z w => shiftedCoeff (L.rightMap z w) k (q.1.val + q.2.val))]
  funext x y z; rw [← L.leading]
  simp only [Tensor.restrict, finsetSum_coeff, coeff_mul_C]
  simp_rw [hmul _ _ _ (natDegree_le_of_degree_le (L.left_degree x _)) (natDegree_le_of_degree_le (L.middle_degree y _))]
  simp only [Finset.sum_mul]
  simpa only [Fintype.sum_prod_type] using sum_comm_three fun (q : Fin (Lx + 1) × Fin (Ly + 1)) u v w =>
    (L.leftMap x u).coeff q.1 * (L.middleMap y v).coeff q.2 * shiftedCoeff (L.rightMap z w) k (q.1.val + q.2.val) * T u v w

end Tensor.PolynomialRestrictionDegeneration

/-! ### Growth Helpers -/

theorem le_of_eventually_pow_le_poly_mul_pow {a b C : ℝ} (s : ℕ) (ha : 0 ≤ a)
    (h : ∀ᶠ n : ℕ in atTop, b ^ n ≤ ((n : ℝ) + 1) ^ s * C * a ^ n) : b ≤ a := by
  by_contra! hab
  have hb : 0 < b := ha.trans_lt hab
  let C' := max C 1
  have hr0 : 0 ≤ a / b := div_nonneg ha hb.le
  have hr1 : a / b < 1 := (div_lt_one hb).2 hab
  have hlim : Tendsto (fun n : ℕ => ((2 : ℝ) ^ s * C') * ((n : ℝ) ^ s * (a / b) ^ n)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one s hr0 hr1).const_mul ((2 : ℝ) ^ s * C')
  have hbnd : ∀ᶠ n : ℕ in atTop, 1 ≤ ((2 : ℝ) ^ s * C') * ((n : ℝ) ^ s * (a / b) ^ n) := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    have h1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ 2 * n)
    have hC' : C ≤ C' := le_max_left _ _
    have hC'0 : 0 ≤ C' := zero_le_one.trans (le_max_right _ _)
    have hdiv := (div_le_div_iff_of_pos_right (pow_pos hb n)).2 hn
    rw [div_self (pow_ne_zero n hb.ne'), mul_div_assoc, ← div_pow] at hdiv
    refine hdiv.trans ?_
    calc ((n : ℝ) + 1) ^ s * C * (a / b) ^ n
        ≤ ((n : ℝ) + 1) ^ s * C' * (a / b) ^ n := by gcongr
      _ ≤ (2 * (n : ℝ)) ^ s * C' * (a / b) ^ n := by gcongr
      _ = ((2 : ℝ) ^ s * C') * ((n : ℝ) ^ s * (a / b) ^ n) := by rw [mul_pow]; ring
  linarith [ge_of_tendsto hlim hbnd]

theorem le_of_eventually_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ C * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_poly_mul_pow 0 ha (by simpa using h)

theorem rpow_exponent_le_of_nat_bound {a b C : ℝ} (hC : 0 < C)
    (hbound : ∀ k : ℕ, 1 ≤ k → ((2 ^ k : ℕ) : ℝ) ^ a ≤ C * ((2 ^ k : ℕ) : ℝ) ^ b) : a ≤ b := by
  by_contra! hab
  have hp : 0 < (a - b) * Real.log 2 := mul_pos (sub_pos.2 hab) (Real.log_pos (by norm_num))
  obtain ⟨k, hk⟩ := exists_nat_gt (max (Real.log C / ((a - b) * Real.log 2)) 1)
  have hk1 : 1 ≤ k := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hk).le
  have hk' : Real.log C < (k : ℝ) * ((a - b) * Real.log 2) := (div_lt_iff₀ hp).1 (lt_of_le_of_lt (le_max_left _ _) hk)
  have hn : (0 : ℝ) < (2 ^ k : ℕ) := by positivity
  have h := Real.log_le_log (Real.rpow_pos_of_pos hn a) (hbound k hk1)
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hn b).ne', Real.log_rpow hn a, Real.log_rpow hn b] at h
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  nlinarith

/-! ### Tensor Semiring & Exact Matrix Rank -/

def sumTensor {X Y Z U V W : Type*} (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W) : Tensor ℤ (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0

def sumRestriction {X U X' U' : Type*} (f : X' → X → ℤ) (g : U' → U → ℤ) : (X' ⊕ U') → (X ⊕ U) → ℤ
  | .inl x', .inl x => f x' x
  | .inr u', .inr u => g u' u
  | _, _ => 0

def IsRestriction {X Y Z U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W) : Prop :=
  ∃ A B C, T = Tensor.restrict A B C S

theorem IsRestriction.refl {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) : IsRestriction T T :=
  ⟨_, _, _, Tensor.pullback_eq_restrict id id id T⟩

theorem IsRestriction.trans {X Y Z U V W P Q R : Type*}
    [Fintype U] [Fintype V] [Fintype W] [Fintype P] [Fintype Q] [Fintype R]
    {T : Tensor ℤ X Y Z} {S : Tensor ℤ U V W} {L : Tensor ℤ P Q R}
    (hTS : IsRestriction T S) (hSL : IsRestriction S L) : IsRestriction T L := by
  rcases hTS with ⟨A, B, C, rfl⟩; rcases hSL with ⟨D, E, F, rfl⟩
  refine ⟨fun x p => ∑ u, A x u * D u p, fun y q => ∑ v, B y v * E v q,
    fun z r => ∑ w, C z w * F w r, funext fun x => funext fun y => funext fun z => ?_⟩
  simp only [Tensor.restrict]
  calc (∑ u, ∑ v, ∑ w, A x u * B y v * C z w * ∑ p, ∑ q, ∑ r, D u p * E v q * F w r * L p q r)
      = ∑ a : U × V × W, ∑ b : P × Q × R,
          A x a.1 * B y a.2.1 * C z a.2.2 * (D a.1 b.1 * E a.2.1 b.2.1 * F a.2.2 b.2.2 * L b.1 b.2.1 b.2.2) := by
          simp [Fintype.sum_prod_type, Finset.mul_sum]
    _ = ∑ b : P × Q × R, ∑ a : U × V × W,
          (A x a.1 * D a.1 b.1) * (B y a.2.1 * E a.2.1 b.2.1) * (C z a.2.2 * F a.2.2 b.2.2) * L b.1 b.2.1 b.2.2 :=
          Finset.sum_comm.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by
          conv_lhs => rw [Fintype.sum_prod_type]; simp only [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
          conv_rhs => rw [mul_assoc (∑ u, _) (∑ v, _) (∑ w, _), Finset.sum_mul_sum, Finset.sum_mul_sum]; simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
          simp only [mul_assoc]

theorem IsRestriction.pullback {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (fx : U → X) (fy : V → Y) (fz : W → Z) :
    IsRestriction (Tensor.pullback fx fy fz T) T := ⟨_, _, _, Tensor.pullback_eq_restrict fx fy fz T⟩

theorem IsRestriction.of_reindex {X Y Z U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    IsRestriction T (Tensor.pullback ex ey ez T) := by
  have h := IsRestriction.pullback (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z; simp [Tensor.pullback]
  rwa [heq] at h

theorem IsRestriction.product {X Y Z U V W P Q R U' V' W' : Type*}
    [Fintype P] [Fintype Q] [Fintype R] [Fintype U'] [Fintype V'] [Fintype W']
    {T : Tensor ℤ X Y Z} {S : Tensor ℤ U V W} {T' : Tensor ℤ P Q R} {S' : Tensor ℤ U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩; rcases hS with ⟨D, E, F, rfl⟩
  refine ⟨fun x u => A x.1 u.1 * D x.2 u.2, fun y v => B y.1 v.1 * E y.2 v.2,
    fun z w => C z.1 w.1 * F z.2 w.2, (funext fun x => funext fun y => funext fun z => ?_).symm⟩
  simp only [Tensor.product, Tensor.restrict, Fintype.sum_prod_type]
  calc (∑ p, ∑ u, ∑ q, ∑ v, ∑ r, ∑ w, (A x.1 p * D x.2 u) * (B y.1 q * E y.2 v) *
          (C z.1 r * F z.2 w) * (T' p q r * S' u v w))
      = ∑ p, ∑ q, ∑ r, ∑ u, ∑ v, ∑ w, (A x.1 p * D x.2 u) * (B y.1 q * E y.2 v) *
          (C z.1 r * F z.2 w) * (T' p q r * S' u v w) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <| Finset.sum_congr rfl fun _ _ =>
            (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ r, ∑ u, ∑ v, ∑ w, (A x.1 p * B y.1 q * C z.1 r * T' p q r) *
          (D x.2 u * E y.2 v * F z.2 w * S' u v w) := Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by simp_rw [Finset.sum_mul, Finset.mul_sum]

theorem IsRestriction.sum {X Y Z U V W P Q R U' V' W' : Type*}
    [Fintype P] [Fintype Q] [Fintype R] [Fintype U'] [Fintype V'] [Fintype W']
    {T : Tensor ℤ X Y Z} {S : Tensor ℤ U V W} {T' : Tensor ℤ P Q R} {S' : Tensor ℤ U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (sumTensor T S) (sumTensor T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩; rcases hS with ⟨D, E, F, rfl⟩
  refine ⟨sumRestriction A D, sumRestriction B E, sumRestriction C F, funext fun x => funext fun y => funext fun z => ?_⟩
  cases x <;> cases y <;> cases z <;> simp [Tensor.restrict, sumRestriction, sumTensor, Fintype.sum_sum_type]

theorem IsRestriction.zero {X Y Z U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (S : Tensor ℤ U V W) : IsRestriction (0 : Tensor ℤ X Y Z) S :=
  ⟨0, 0, 0, by funext _ _ _; simp [Tensor.restrict]⟩

structure FiniteTensor where
  nx : ℕ
  ny : ℕ
  nz : ℕ
  coeff : Tensor ℤ (Fin nx) (Fin ny) (Fin nz)

def FiniteTensor.ofTensor {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor ℤ X Y Z) : FiniteTensor :=
  ⟨Fintype.card X, Fintype.card Y, Fintype.card Z,
    Tensor.pullback (Fintype.equivFin X).symm (Fintype.equivFin Y).symm (Fintype.equivFin Z).symm T⟩

instance : Preorder FiniteTensor where
  le T S := IsRestriction T.coeff S.coeff
  le_refl T := IsRestriction.refl T.coeff
  le_trans _ _ _ := IsRestriction.trans

theorem FiniteTensor.ofTensor_le_iff {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W] (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W) :
    ofTensor T ≤ ofTensor S ↔ IsRestriction T S :=
  ⟨fun h => (IsRestriction.of_reindex T _ _ _).trans (IsRestriction.trans h (IsRestriction.pullback S _ _ _)),
   fun h => (IsRestriction.pullback T _ _ _).trans (h.trans (IsRestriction.of_reindex S _ _ _))⟩

abbrev TensorClass := Antisymmetrization FiniteTensor (· ≤ ·)

def classOf {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor ℤ X Y Z) : TensorClass :=
  toAntisymmetrization (· ≤ ·) (FiniteTensor.ofTensor T)

theorem classOf_le_iff {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W] (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W) :
    classOf T ≤ classOf S ↔ IsRestriction T S := FiniteTensor.ofTensor_le_iff T S

theorem classOf_reindex {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W] (T : Tensor ℤ X Y Z) (ex : U ≃ X) (ey : V ≃ Y) (ez : W ≃ Z) :
    classOf (Tensor.pullback ex ey ez T) = classOf T :=
  le_antisymm ((classOf_le_iff _ _).2 (IsRestriction.pullback T ex ey ez))
    ((classOf_le_iff _ _).2 (IsRestriction.of_reindex T ex ey ez))

theorem classOf_eq_of_reindex {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W] {T : Tensor ℤ X Y Z} {S : Tensor ℤ U V W}
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W) (h : Tensor.pullback ex ey ez S = T) :
    classOf T = classOf S :=
  (congrArg classOf h).symm.trans (classOf_reindex S ex ey ez)

@[simp] theorem mk_eq_classOf (T : FiniteTensor) : (Quot.mk _ T : TensorClass) = classOf T.coeff :=
  (toAntisymmetrization_eq (· ≤ ·) T (FiniteTensor.ofTensor T.coeff)).2
    ⟨IsRestriction.of_reindex T.coeff _ _ _, IsRestriction.pullback T.coeff _ _ _⟩

instance : Mul TensorClass where
  mul := Quotient.map₂ (fun T S => FiniteTensor.ofTensor (Tensor.product T.coeff S.coeff))
    fun _ _ hT _ _ hS => ⟨(FiniteTensor.ofTensor_le_iff _ _).2 (IsRestriction.product hT.1 hS.1),
      (FiniteTensor.ofTensor_le_iff _ _).2 (IsRestriction.product hT.2 hS.2)⟩

instance : Add TensorClass where
  add := Quotient.map₂ (fun T S => FiniteTensor.ofTensor (sumTensor T.coeff S.coeff))
    fun _ _ hT _ _ hS => ⟨(FiniteTensor.ofTensor_le_iff _ _).2 (IsRestriction.sum hT.1 hS.1),
      (FiniteTensor.ofTensor_le_iff _ _).2 (IsRestriction.sum hT.2 hS.2)⟩

instance : Zero TensorClass := ⟨classOf (0 : Tensor ℤ Empty Empty Empty)⟩
instance : One TensorClass := ⟨classOf (unitTensor (K := ℤ))⟩

theorem zero_eq : (0 : TensorClass) = classOf (0 : Tensor ℤ Empty Empty Empty) := rfl

theorem classOf_product {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W] (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W) :
    classOf (Tensor.product T S) = classOf T * classOf S :=
  (classOf_reindex (Tensor.product T S)
    (Equiv.prodCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.prodCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.prodCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)).symm

theorem classOf_sum {X Y Z U V W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W] (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W) :
    classOf (sumTensor T S) = classOf T + classOf S :=
  (classOf_eq_of_reindex
    (Equiv.sumCongr (Fintype.equivFin X).symm (Fintype.equivFin U).symm)
    (Equiv.sumCongr (Fintype.equivFin Y).symm (Fintype.equivFin V).symm)
    (Equiv.sumCongr (Fintype.equivFin Z).symm (Fintype.equivFin W).symm)
    (by funext x y z; cases x <;> cases y <;> cases z <;> rfl)).symm

theorem classOf_zero {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] :
    classOf (0 : Tensor ℤ X Y Z) = 0 :=
  le_antisymm ((classOf_le_iff _ _).2 (IsRestriction.zero _)) ((classOf_le_iff _ _).2 (IsRestriction.zero _))

theorem class_add_comm : ∀ a b : TensorClass, a + b = b + a :=
  Quot.ind fun a => Quot.ind fun b => by
    simp only [mk_eq_classOf, ← classOf_sum]
    exact classOf_eq_of_reindex (.sumComm _ _) (.sumComm _ _) (.sumComm _ _)
      (by funext x y z; cases x <;> cases y <;> cases z <;> rfl)

theorem class_add_zero : ∀ a : TensorClass, a + 0 = a :=
  Quot.ind fun a => by
    simp only [mk_eq_classOf, zero_eq, ← classOf_sum]
    exact (classOf_eq_of_reindex (Equiv.sumEmpty _ Empty).symm (Equiv.sumEmpty _ Empty).symm
      (Equiv.sumEmpty _ Empty).symm rfl).symm

theorem class_mul_comm : ∀ a b : TensorClass, a * b = b * a :=
  Quot.ind fun a => Quot.ind fun b => by
    simp only [mk_eq_classOf, ← classOf_product]
    exact classOf_eq_of_reindex (.prodComm _ _) (.prodComm _ _) (.prodComm _ _)
      (by funext x y z; simp [Tensor.pullback, Tensor.product, mul_comm])

theorem class_mul_one : ∀ a : TensorClass, a * 1 = a :=
  Quot.ind fun a => by
    simp only [mk_eq_classOf, show (1 : TensorClass) = classOf (unitTensor (K := ℤ)) from rfl, ← classOf_product]
    exact (classOf_eq_of_reindex (Equiv.prodPUnit _).symm (Equiv.prodPUnit _).symm
      (Equiv.prodPUnit _).symm (by funext x y z; simp [Tensor.pullback, Tensor.product, unitTensor])).symm

theorem class_mul_zero : ∀ a : TensorClass, a * 0 = 0 :=
  Quot.ind fun a => by
    rw [mk_eq_classOf, zero_eq, ← classOf_product,
      show Tensor.product a.coeff (0 : Tensor ℤ Empty Empty Empty) = 0 by funext _ _ _; simp [Tensor.product],
      classOf_zero, ← zero_eq]

theorem class_left_distrib : ∀ a b c : TensorClass, a * (b + c) = a * b + a * c :=
  Quot.ind fun a => Quot.ind fun b => Quot.ind fun c => by
    simp only [mk_eq_classOf, ← classOf_product, ← classOf_sum]
    exact (classOf_eq_of_reindex (Equiv.prodSumDistrib _ _ _).symm (Equiv.prodSumDistrib _ _ _).symm
      (Equiv.prodSumDistrib _ _ _).symm (by funext x y z; cases x <;> cases y <;> cases z <;>
        simp [Tensor.pullback, Tensor.product, sumTensor])).symm

instance : CommSemiring TensorClass where
  add_assoc := Quot.ind fun a => Quot.ind fun b => Quot.ind fun c => by
    simp only [mk_eq_classOf, ← classOf_sum]
    exact classOf_eq_of_reindex (.sumAssoc _ _ _) (.sumAssoc _ _ _) (.sumAssoc _ _ _)
      (by funext x y z; rcases x with (x | x) | x <;> rcases y with (y | y) | y <;> rcases z with (z | z) | z <;> rfl)
  add_comm := class_add_comm
  add_zero := class_add_zero
  zero_add a := (class_add_comm 0 a).trans (class_add_zero a)
  nsmul := nsmulRec
  mul_assoc := Quot.ind fun a => Quot.ind fun b => Quot.ind fun c => by
    simp only [mk_eq_classOf, ← classOf_product]
    exact classOf_eq_of_reindex (.prodAssoc _ _ _) (.prodAssoc _ _ _) (.prodAssoc _ _ _)
      (by funext x y z; simp [Tensor.pullback, Tensor.product, mul_assoc])
  mul_comm := class_mul_comm
  mul_one := class_mul_one
  one_mul a := (class_mul_comm 1 a).trans (class_mul_one a)
  mul_zero := class_mul_zero
  zero_mul a := (class_mul_comm 0 a).trans (class_mul_zero a)
  left_distrib := class_left_distrib
  right_distrib a b c := by rw [class_mul_comm, class_left_distrib, class_mul_comm c a, class_mul_comm c b]

theorem mul_mono {T T' S S' : TensorClass} (hT : T ≤ T') (hS : S ≤ S') : T * S ≤ T' * S' := by
  induction T using Quotient.inductionOn; induction T' using Quotient.inductionOn
  induction S using Quotient.inductionOn; induction S' using Quotient.inductionOn
  exact (FiniteTensor.ofTensor_le_iff _ _).2 (IsRestriction.product hT hS)

theorem add_mono {T T' S S' : TensorClass} (hT : T ≤ T') (hS : S ≤ S') : T + S ≤ T' + S' := by
  induction T using Quotient.inductionOn; induction T' using Quotient.inductionOn
  induction S using Quotient.inductionOn; induction S' using Quotient.inductionOn
  exact (FiniteTensor.ofTensor_le_iff _ _).2 (IsRestriction.sum hT hS)

theorem tc_zero_le : ∀ T : TensorClass, 0 ≤ T :=
  Quot.ind fun T => by rw [mk_eq_classOf, zero_eq]; exact (classOf_le_iff _ _).2 (IsRestriction.zero T.coeff)

theorem classOf_directSum {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {ι : Type} [Fintype ι] [DecidableEq ι] (T : ι → Tensor ℤ X Y Z) :
    classOf (Tensor.directSum T) = ∑ i, classOf (T i) := by
  have hfin (n : ℕ) : ∀ S : Fin n → Tensor ℤ X Y Z, classOf (Tensor.directSum S) = ∑ i, classOf (S i) := by
    induction n with
    | zero => intro S; rw [Fin.sum_univ_zero, show Tensor.directSum S = 0 from funext fun x => Fin.elim0 x.1, classOf_zero]
    | succ n ih =>
      intro S
      let e (U : Type) : (Fin n × U) ⊕ U ≃ Fin (n + 1) × U :=
        ⟨fun | .inl (i, u) => (i.castSucc, u) | .inr u => (Fin.last n, u),
         fun (i, u) => Fin.lastCases (.inr u) (fun j => .inl (j, u)) i,
         fun | .inl (i, u) => by simp | .inr u => by simp,
         fun (i, u) => Fin.lastCases (by simp) (fun j => by simp) i⟩
      have hsplit : classOf (Tensor.directSum S) =
          classOf (Tensor.directSum fun i : Fin n => S i.castSucc) + classOf (S (Fin.last n)) := by
        rw [← classOf_sum]; symm
        refine classOf_eq_of_reindex (e X) (e Y) (e Z) (funext fun x => funext fun y => funext fun z => ?_)
        rcases x with ⟨i, x⟩ | x <;> rcases y with ⟨j, y⟩ | y <;> rcases z with ⟨k, z⟩ | z <;>
          simp [e, Tensor.pullback, Tensor.directSum, sumTensor, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
      rw [hsplit, ih, Fin.sum_univ_castSucc]
  let e := Fintype.equivFin ι
  have hre : classOf (Tensor.directSum fun i => T (e.symm i)) = classOf (Tensor.directSum T) :=
    classOf_eq_of_reindex (Equiv.prodCongr e.symm (.refl X)) (Equiv.prodCongr e.symm (.refl Y))
      (Equiv.prodCongr e.symm (.refl Z)) (by funext x y z; simp [Tensor.pullback, Tensor.directSum, e.symm.injective.eq_iff])
  rw [← hre, hfin]; exact e.symm.sum_comp fun i => classOf (T i)

abbrev scalarTensor (r : ℕ) := Tensor.directSum fun _ : Fin r => unitTensor (K := ℤ)

theorem classOf_scalarTensor (r : ℕ) : classOf (scalarTensor r) = (r : TensorClass) := by
  simp [scalarTensor, classOf_directSum, show classOf (unitTensor (K := ℤ)) = 1 from rfl]

theorem classOf_le_natCast_iff_rankAtMost {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℤ X Y Z) (r : ℕ) : classOf T ≤ (r : TensorClass) ↔ Tensor.RankAtMost T r := by
  rw [← classOf_scalarTensor r, classOf_le_iff]
  refine ⟨fun ⟨A, B, C, h⟩ => ⟨fun i x => A x (i, ()), fun i y => B y (i, ()), fun i z => C z (i, ()), fun x y z => ?_⟩,
    fun ⟨a, b, c, h⟩ => ⟨fun x i => a i.1 x, fun y i => b i.1 y, fun z i => c i.1 z, funext fun x => funext fun y => funext fun z => ?_⟩⟩
  · simpa [Tensor.restrict, scalarTensor, Tensor.directSum, unitTensor, Fintype.sum_prod_type, mul_ite, ite_and]
      using congrFun (congrFun (congrFun h x) y) z
  · simpa [Tensor.restrict, scalarTensor, Tensor.directSum, unitTensor, Fintype.sum_prod_type, mul_ite, ite_and]
      using h x y z

theorem exists_le_natCast : ∀ x : TensorClass, ∃ r : ℕ, x ≤ (r : TensorClass) :=
  Quot.ind fun T => by
    rw [mk_eq_classOf]
    let e := Fintype.equivFin (Fin T.nx × Fin T.ny × Fin T.nz)
    refine ⟨Fintype.card (Fin T.nx × Fin T.ny × Fin T.nz), (classOf_le_natCast_iff_rankAtMost _ _).2 ?_⟩
    refine ⟨fun i x => if x = (e.symm i).1 then T.coeff (e.symm i).1 (e.symm i).2.1 (e.symm i).2.2 else 0,
      fun i y => if y = (e.symm i).2.1 then 1 else 0, fun i z => if z = (e.symm i).2.2 then 1 else 0, fun x y z => ?_⟩
    refine ((e.symm.sum_comp fun p =>
      (if x = p.1 then T.coeff p.1 p.2.1 p.2.2 else 0) * (if y = p.2.1 then 1 else 0) * (if z = p.2.2 then 1 else 0)).trans ?_).symm
    simp [Fintype.sum_prod_type, mul_ite]

def tcRank (x : TensorClass) : ℕ := Nat.find (exists_le_natCast x)

theorem le_tcRank (x : TensorClass) : x ≤ (tcRank x : TensorClass) := Nat.find_spec (exists_le_natCast x)

theorem tcRank_le {x : TensorClass} {r : ℕ} (h : x ≤ (r : TensorClass)) : tcRank x ≤ r :=
  Nat.find_min' (exists_le_natCast x) h

theorem tcRank_mono {x y : TensorClass} (h : x ≤ y) : tcRank x ≤ tcRank y :=
  tcRank_le (h.trans (le_tcRank y))

theorem tcRank_mul_le (x y : TensorClass) : tcRank (x * y) ≤ tcRank x * tcRank y :=
  tcRank_le (by push_cast; exact mul_mono (le_tcRank x) (le_tcRank y))

theorem tcRank_natCast (r : ℕ) : tcRank (r : TensorClass) = r :=
  le_antisymm (tcRank_le le_rfl) <| by
    have h := (classOf_le_natCast_iff_rankAtMost (scalarTensor r) (tcRank (r : TensorClass))).1
      ((classOf_scalarTensor r).trans_le (le_tcRank _))
    simpa using h.card_le_of_identity (fun i : Fin r => (i, ())) (fun i => (i, ())) (fun i => (i, ()))
      fun i j => by simp [scalarTensor, Tensor.directSum, unitTensor]

def matrixClass (n : ℕ) : TensorClass := classOf (matrixMultiplicationTensor n n n)

theorem matrixClass_mul (m n : ℕ) : matrixClass (m * n) = matrixClass m * matrixClass n := by
  let e : Fin (m * n) ≃ Fin m × Fin n := Fintype.equivOfCardEq (by simp)
  have h1 : matrixClass (m * n) = classOf (Tensor.matrixCoefficients (Fin m × Fin n) (Fin m × Fin n) (Fin m × Fin n)) :=
    classOf_eq_of_reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e) (Equiv.prodCongr e e)
      (by funext x y z; simp [Tensor.pullback, Tensor.matrixCoefficients, e.injective.eq_iff])
  rw [h1]; change _ = classOf _ * classOf _; rw [← classOf_product]
  refine classOf_eq_of_reindex (.prodProdProdComm _ _ _ _) (.prodProdProdComm _ _ _ _) (.prodProdProdComm _ _ _ _) ?_
  funext x y z; simp only [Tensor.pullback, Equiv.prodProdProdComm_apply, Tensor.product, Tensor.matrixCoefficients, Prod.ext_iff]
  split_ifs <;> simp_all

theorem matrixClass_pow (m j : ℕ) : matrixClass (m ^ j) = matrixClass m ^ j := by
  induction j with
  | zero =>
    change matrixClass 1 = 1
    let e : Fin 1 × Fin 1 ≃ PUnit.{1} := Fintype.equivOfCardEq (by simp)
    exact classOf_eq_of_reindex e e e (funext fun x => funext fun y => funext fun z => by
      simp [Tensor.pullback, matrixMultiplicationTensor, Tensor.matrixCoefficients, unitTensor,
        Subsingleton.elim x.2 y.1, Subsingleton.elim y.2 z.1, Subsingleton.elim z.2 x.1])
  | succ j ih => rw [pow_succ, matrixClass_mul, ih, pow_succ]

abbrev exactMatrixRank (n : ℕ) : ℕ := tcRank (matrixClass n)

theorem exactMatrixRank_spec (n : ℕ) :
    Tensor.RankAtMost (matrixMultiplicationTensor n n n) (exactMatrixRank n) :=
  (classOf_le_natCast_iff_rankAtMost _ _).1 (le_tcRank (matrixClass n))

theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ exactMatrixRank n := by
  have h := (exactMatrixRank_spec n).card_le_of_identity
    (fun i : Fin n × Fin n => (i.2, ⟨0, hn⟩)) (fun i => (⟨0, hn⟩, i.1)) id
    fun i k => by simp [matrixMultiplicationTensor, Tensor.matrixCoefficients, Prod.ext_iff, eq_comm]
  simpa [Fintype.card_prod, pow_two] using h

theorem exactMatrixRank_pos {n : ℕ} (hn : 0 < n) : 0 < exactMatrixRank n :=
  (pow_pos hn 2).trans_le (exactMatrixRank_lower hn)

abbrev exactRankSet : Set ℝ := {τ | ∃ n : ℕ, 2 ≤ n ∧ τ = Real.logb n (exactMatrixRank n)}
def exactRankExponent : ℝ := sInf exactRankSet

theorem exactMatrixRank_logb_lower {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ Real.logb n (exactMatrixRank n) := by
  refine (Real.le_logb_iff_rpow_le (by exact_mod_cast (by omega : 1 < n))
    (by exact_mod_cast exactMatrixRank_pos (by omega))).2 ?_
  rw [Real.rpow_two]; exact_mod_cast exactMatrixRank_lower (by omega)

theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : exactRankExponent < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ (exactMatrixRank n : ℝ) < (n : ℝ) ^ τ := by
  obtain ⟨_, ⟨n, hn, rfl⟩, hσ⟩ := exists_lt_of_csInf_lt (s := exactRankSet) ⟨_, 2, le_rfl, rfl⟩ hτ
  exact ⟨n, hn, (Real.logb_lt_iff_lt_rpow (by exact_mod_cast (by omega : 1 < n))
    (by exact_mod_cast exactMatrixRank_pos (by omega))).1 hσ⟩

/-! ### Characters & Symmetrization -/

structure Character where
  value : {X Y Z : Type} → [Fintype X] → [Fintype Y] → [Fintype Z] → Tensor ℤ X Y Z → ℝ
  nonneg : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor ℤ X Y Z), 0 ≤ value T
  map_one : value (unitTensor (K := ℤ)) = 1
  map_directSum : ∀ {ι X Y Z : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Y] [Fintype Z] (T : ι → Tensor ℤ X Y Z),
    value (Tensor.directSum T) = ∑ i, value (T i)
  map_product : ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W] (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W),
    value (Tensor.product T S) = value T * value S
  monotone : ∀ {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z'] (T : Tensor ℤ X Y Z)
    (A : X' → X → ℤ) (B : Y' → Y → ℤ) (C : Z' → Z → ℤ),
    value (Tensor.restrict A B C T) ≤ value T

namespace Character

variable (χ : Character)
variable {X Y Z X' Y' Z' : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y'] [Fintype Z']

theorem value_pullback_le (T : Tensor ℤ X Y Z) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    χ.value (Tensor.pullback fx fy fz T) ≤ χ.value T := by
  rw [Tensor.pullback_eq_restrict]; exact χ.monotone T _ _ _

theorem value_reindex (T : Tensor ℤ X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.value (Tensor.pullback ex ey ez T) = χ.value T := by
  refine le_antisymm (χ.value_pullback_le T ex ey ez) ?_
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext _ _ _; simp [Tensor.pullback]
  simpa only [heq] using χ.value_pullback_le (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm

theorem one_le_value_of_coefficient_one {T : Tensor ℤ X Y Z} (hT : ∃ x y z, T x y z = 1) :
    1 ≤ χ.value T := by
  obtain ⟨x, y, z, hxyz⟩ := hT
  have heq : Tensor.pullback (fun _ : Unit => x) (fun _ : Unit => y) (fun _ : Unit => z) T = unitTensor (K := ℤ) :=
    funext fun _ => funext fun _ => funext fun _ => hxyz
  simpa only [heq, χ.map_one] using χ.value_pullback_le T (fun _ : Unit => x) (fun _ : Unit => y) (fun _ : Unit => z)

def cyclicCharacter : Character where
  value T := χ.value (Tensor.cyclic T)
  nonneg T := χ.nonneg (Tensor.cyclic T)
  map_one := χ.map_one
  map_directSum T := by
    have heq : Tensor.cyclic (Tensor.directSum T) = Tensor.directSum fun i => Tensor.cyclic (T i) := by
      funext ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
      rcases eq_or_ne i j with rfl | _ <;> rcases eq_or_ne i k with rfl | _ <;>
        simp_all [Tensor.directSum, @eq_comm _ i]
    rw [heq, χ.map_directSum]
  map_product T S := χ.map_product (Tensor.cyclic T) (Tensor.cyclic S)
  monotone T A B C := by
    have heq : Tensor.cyclic (Tensor.restrict A B C T) = Tensor.restrict B C A (Tensor.cyclic T) := by
      funext y z x; simp only [Tensor.cyclic, Tensor.restrict]
      exact Finset.sum_comm.trans <| Finset.sum_congr rfl fun _ _ =>
        Finset.sum_comm.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    exact heq ▸ χ.monotone (Tensor.cyclic T) B C A

def swap23Character : Character where
  value T := χ.value (fun x z y => T x y z)
  nonneg T := χ.nonneg (fun x z y => T x y z)
  map_one := χ.map_one
  map_directSum T := by
    have heq : (fun x z y => Tensor.directSum T x y z) = Tensor.directSum fun i x z y => T i x y z := by
      funext x z y; simp only [Tensor.directSum, and_comm]
    change χ.value (fun x z y => Tensor.directSum T x y z) = _; rw [heq, χ.map_directSum]
  map_product T S := χ.map_product (fun x z y => T x y z) (fun x z y => S x y z)
  monotone T A B C := by
    have heq : (fun x z y => Tensor.restrict A B C T x y z) = Tensor.restrict A C B fun x z y => T x y z := by
      funext x z y; simp only [Tensor.restrict]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <|
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    change χ.value (fun x z y => Tensor.restrict A B C T x y z) ≤ _
    rw [heq]; exact χ.monotone (fun x z y => T x y z) A C B

def pZ : ℝ := Real.log (χ.value (Tensor.dotPairing (Fin 2))) / Real.log 2
def pY : ℝ := χ.cyclicCharacter.pZ
def pX : ℝ := χ.cyclicCharacter.cyclicCharacter.pZ

theorem value_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.dotPairing (Fin m)) = (m : ℝ) ^ χ.pZ := by
  let f (n : ℕ) : ℝ := χ.value (Tensor.dotPairing (Fin n))
  have hpos {n : ℕ} (hn : 0 < n) : 0 < f n :=
    zero_lt_one.trans_le (χ.one_le_value_of_coefficient_one ⟨⟨0, hn⟩, ⟨0, hn⟩, (), by simp [Tensor.dotPairing]⟩)
  have hmul (a b : ℕ) : f (a * b) = f a * f b := by
    have heq : Tensor.pullback finProdFinEquiv.symm finProdFinEquiv.symm (Equiv.prodUnique Unit Unit).symm
        (Tensor.product (Tensor.dotPairing (Fin a)) (Tensor.dotPairing (Fin b))) = Tensor.dotPairing (Fin (a * b)) := by
      funext x y z
      simp only [Tensor.pullback, Tensor.product, Tensor.dotPairing, ite_zero_mul_ite_zero,
        one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
    dsimp [f]; rw [← heq, χ.value_reindex, χ.map_product]
  have hmono {a b : ℕ} (hab : a ≤ b) : f a ≤ f b := by
    have heq : Tensor.pullback (Fin.castLE hab) (Fin.castLE hab) id (Tensor.dotPairing (Fin b)) = Tensor.dotPairing (Fin a) := by
      funext x y z; simp [Tensor.pullback, Tensor.dotPairing]
    dsimp [f]; rw [← heq]; exact χ.value_pullback_le _ _ _ _
  have hf1 : f 1 = 1 := by have hm1 := hmul 1 1; norm_num at hm1; nlinarith [hpos zero_lt_one]
  have hfpow (a k : ℕ) : f (a ^ k) = f a ^ k := by
    induction k with | zero => simpa using hf1 | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hp0 : 0 ≤ χ.pZ := div_nonneg (Real.log_nonneg (hf1 ▸ hmono (by omega : 1 ≤ 2))) (Real.log_nonneg one_le_two)
  have h2p : (2 : ℝ) ^ χ.pZ = f 2 := by
    rw [Real.rpow_def_of_pos zero_lt_two, pZ, mul_div_cancel₀ _ (Real.log_pos one_lt_two).ne', Real.exp_log (hpos zero_lt_two)]
  have hpow2 (j : ℕ) : ((2 ^ j : ℕ) : ℝ) ^ χ.pZ = f (2 ^ j) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_pow_comm zero_le_two, h2p, hfpow]
  have hf20 : 0 ≤ f 2 := (hpos zero_lt_two).le
  refine le_antisymm
    (le_of_eventually_pow_le_const_mul_pow (C := f 2) (by positivity) (Eventually.of_forall fun k => ?_))
    (le_of_eventually_pow_le_const_mul_pow (C := f 2) (hpos hm).le (Eventually.of_forall fun k => ?_))
  · obtain ⟨j, hlo, hhi⟩ := exists_nat_pow_near (Nat.one_le_pow k m hm) one_lt_two
    calc f m ^ k = f (m ^ k) := (hfpow m k).symm
      _ ≤ f (2 ^ (j + 1)) := hmono hhi.le
      _ = f 2 * ((2 ^ j : ℕ) : ℝ) ^ χ.pZ := by rw [hfpow, pow_succ, mul_comm, hpow2, ← hfpow]
      _ ≤ f 2 * ((m ^ k : ℕ) : ℝ) ^ χ.pZ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlo) hp0) hf20
      _ = f 2 * ((m : ℝ) ^ χ.pZ) ^ k := by rw [Nat.cast_pow, Real.rpow_pow_comm (Nat.cast_nonneg m)]
  · obtain ⟨j, hlo, hhi⟩ := exists_nat_pow_near (Nat.one_le_pow k m hm) one_lt_two
    calc ((m : ℝ) ^ χ.pZ) ^ k = ((m ^ k : ℕ) : ℝ) ^ χ.pZ := by rw [Nat.cast_pow, Real.rpow_pow_comm (Nat.cast_nonneg m)]
      _ ≤ ((2 ^ (j + 1) : ℕ) : ℝ) ^ χ.pZ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhi.le) hp0
      _ = f 2 * f (2 ^ j) := by rw [hpow2, hfpow, pow_succ, mul_comm, ← hfpow]
      _ ≤ f 2 * f (m ^ k) := mul_le_mul_of_nonneg_left (hmono hlo) hf20
      _ = f 2 * f m ^ k := by rw [hfpow]

theorem value_cyclic_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin m)))) = (m : ℝ) ^ χ.pX :=
  χ.cyclicCharacter.cyclicCharacter.value_dotPairing hm

theorem value_matrixMultiplication {m : ℕ} (hm : 0 < m) :
    χ.value (matrixMultiplicationTensor m m m) = (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.2 hm
  have htr : Tensor.pullback
      (⟨fun x => ((x.2, x.1), ()), fun x => (x.1.2, x.1.1), fun _ => rfl, fun ⟨⟨_, _⟩, ⟨⟩⟩ => rfl⟩ : (Fin m × Fin m) ≃ _)
      (⟨fun y => ((y.1, ()), y.2), fun y => (y.1.1, y.2), fun _ => rfl, fun ⟨⟨_, ⟨⟩⟩, _⟩ => rfl⟩ : (Fin m × Fin m) ≃ _)
      (⟨fun z => (((), z.2), z.1), fun z => (z.2, z.1.2), fun _ => rfl, fun ⟨⟨⟨⟩, _⟩, _⟩ => rfl⟩ : (Fin m × Fin m) ≃ _)
      (Tensor.product (Tensor.product (Tensor.dotPairing (Fin m)) (Tensor.cyclic (Tensor.dotPairing (Fin m))))
        (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin m))))) = matrixMultiplicationTensor m m m := by
    funext x y z
    change ((if x.2 = y.1 then (1 : ℤ) else 0) * (if z.2 = x.1 then 1 else 0)) * (if y.2 = z.1 then 1 else 0) = _
    simp only [ite_zero_mul_ite_zero, one_mul, matrixMultiplicationTensor, Tensor.matrixCoefficients]
    congr 1; exact propext ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  rw [← htr, χ.value_reindex, χ.map_product, χ.map_product, χ.value_dotPairing hm,
    show χ.value (Tensor.cyclic (Tensor.dotPairing (Fin m))) = (m : ℝ) ^ χ.pY from χ.cyclicCharacter.value_dotPairing hm,
    χ.value_cyclic_cyclic_dotPairing hm, Real.rpow_add hm', Real.rpow_add hm']
  ring

def permutedCharacter (i : Fin 6) : Character :=
  ![χ, χ.cyclicCharacter, χ.cyclicCharacter.cyclicCharacter,
    χ.swap23Character, χ.swap23Character.cyclicCharacter, χ.swap23Character.cyclicCharacter.cyclicCharacter] i

def sixfoldProduct (T : Tensor ℤ X Y Z) : ℝ :=
  ∏ i : Fin 6, (χ.permutedCharacter i).value T

theorem sixfoldProduct_nonneg (T : Tensor ℤ X Y Z) : 0 ≤ χ.sixfoldProduct T :=
  Finset.prod_nonneg fun i _ => (χ.permutedCharacter i).nonneg _

theorem value_prodTensor :
    ∀ {n : ℕ} (F : Fin n → Tensor ℤ X Y Z), χ.value (Tensor.prodTensor F) = ∏ i, χ.value (F i)
  | 0, F => by
    have h0 : Tensor.prodTensor F = Tensor.pullback (Equiv.equivPUnit _)
        (Equiv.equivPUnit _) (Equiv.equivPUnit _) (unitTensor (K := ℤ)) := by
      funext x y z; simp [Tensor.prodTensor, Tensor.pullback, unitTensor]
    rw [h0, χ.value_reindex, χ.map_one]; simp
  | n + 1, F => by
    have hs : Tensor.prodTensor F = Tensor.pullback
        (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
        (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
        (Tensor.product (F 0) (Tensor.prodTensor (Fin.tail F))) := by
      funext x y z; simp [Tensor.prodTensor, Tensor.pullback, Tensor.product, Fin.consEquiv, Fin.prod_univ_succ, Fin.tail]
    rw [hs, χ.value_reindex, χ.map_product, value_prodTensor (Fin.tail F), Fin.prod_univ_succ]; rfl

@[simp] theorem value_power (T : Tensor ℤ X Y Z) (n : ℕ) :
    χ.value (Tensor.power T n) = χ.value T ^ n := by
  simp [Tensor.power, χ.value_prodTensor]

theorem val_pullback_eq (T : Tensor ℤ X' Y' Z') (S : Tensor ℤ X Y Z)
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy) (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 → x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz)
    (ht : ∀ x y z, T (fx x) (fy y) (fz z) = S x y z) :
    χ.value T = χ.value S := by
  have hp : Tensor.pullback fx fy fz T = S := funext fun x => funext fun y => funext fun z => ht x y z
  rw [← hp]
  refine le_antisymm ?_ (χ.value_pullback_le T fx fy fz)
  have hext : T = Tensor.restrict (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0) (fun z' z => if fz z = z' then 1 else 0) (Tensor.pullback fx fy fz T) := by
    funext x' y' z'
    by_cases h0 : T x' y' z' = 0
    · simp only [Tensor.restrict, Tensor.pullback, h0]
      exact (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => by split_ifs <;> simp_all).symm
    · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩, ⟨z, rfl⟩⟩ := hs _ _ _ h0
      simp [Tensor.restrict, Tensor.pullback, hx.eq_iff, hy.eq_iff, hz.eq_iff, ite_mul, mul_ite]
  conv_lhs => rw [hext]
  exact χ.monotone _ _ _ _

theorem value_sharedFirstTensor_eq_sum {M : ℕ} (B : Fin M → Tensor ℤ X Y Z)
    (ly : Y → Fin M) (lz : Z → Fin M)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    χ.value (sharedFirstTensor B) = χ.value (∑ i, B i) := by
  refine χ.val_pullback_eq _ _ id (fun y => (ly y, y)) (fun z => (lz z, z)) Function.injective_id
    (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h) (fun x y z h => ?_) (fun x y z => ?_)
  · have hyz : y.1 = z.1 := by by_contra hne; exact h (by simp [sharedFirstTensor, hne])
    obtain ⟨hy, hz⟩ := hsupport y.1 x y.2 z.2 (by simpa [sharedFirstTensor, hyz] using h)
    exact ⟨⟨x, rfl⟩, ⟨y.2, Prod.ext hy rfl⟩, ⟨z.2, Prod.ext (hz.trans hyz) rfl⟩⟩
  · simp only [sharedFirstTensor, Finset.sum_apply]
    rw [Finset.sum_eq_single (ly y) (fun i _ hi => by by_contra h; exact hi (hsupport i x y z h).1.symm)
      (fun h => (h (Finset.mem_univ _)).elim)]
    split_ifs with h
    · rfl
    · symm; by_contra hb; exact h (hsupport (ly y) x y z hb).2.symm

theorem value_le_mul_of_power_comparisons
    (T : Tensor ℤ X Y Z) (U : Tensor ℤ X' Y' Z') (A B : ℕ) (C L : ℝ) (hL : 0 ≤ L)
    (h : ∀ n : ℕ, χ.value (Tensor.power U n) ≤ C * ((n : ℝ) * A + 1) * (n * B + 1) * L ^ n * χ.value (Tensor.power T n)) :
    χ.value U ≤ L * χ.value T := by
  have ha : 0 ≤ L * χ.value T := mul_nonneg hL (χ.nonneg T)
  refine le_of_eventually_pow_le_poly_mul_pow (C := max C 0 * ((A : ℝ) + 1) * ((B : ℝ) + 1)) 2 ha (Eventually.of_forall fun n => ?_)
  have hn : χ.value U ^ n ≤ C * ((n : ℝ) * A + 1) * (n * B + 1) * (L * χ.value T) ^ n := by
    simpa only [χ.value_power, mul_pow, mul_assoc] using h n
  refine hn.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg ha n))
  have h1 : (n : ℝ) * A + 1 ≤ ((n : ℝ) + 1) * ((A : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) A]
  have h2 : (n : ℝ) * B + 1 ≤ ((n : ℝ) + 1) * ((B : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) B]
  calc C * ((n : ℝ) * A + 1) * ((n : ℝ) * B + 1)
      ≤ max C 0 * (((n : ℝ) + 1) * ((A : ℝ) + 1)) * (((n : ℝ) + 1) * ((B : ℝ) + 1)) := by
        gcongr; exact le_max_left C 0
    _ = ((n : ℝ) + 1) ^ 2 * (max C 0 * ((A : ℝ) + 1) * ((B : ℝ) + 1)) := by ring

theorem value_polynomialRestrictionDegeneration_le_ring
    {T : Tensor ℤ X Y Z} {U : Tensor ℤ X' Y' Z'} {k Lx Ly : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly) : χ.value U ≤ χ.value T := by
  simpa using χ.value_le_mul_of_power_comparisons T U Lx Ly 1 1 zero_le_one fun n => by
    have h := χ.monotone
      (Tensor.directSum fun _ : Fin (Lx * n + 1) × Fin (Ly * n + 1) => Tensor.power T n)
      (fun x q => ((L.power n).leftMap x q.2).coeff q.1.1)
      (fun y q => ((L.power n).middleMap y q.2).coeff q.1.2)
      (fun z q => shiftedCoeff ((L.power n).rightMap z q.2) (k * n) (q.1.1.val + q.1.2.val))
    rw [← (L.power n).extract, χ.map_directSum] at h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    convert h using 1; ring

end Character

/-! ### Detecting Character Existence -/

theorem tensor_catalytic_obstruction {D s : TensorClass} {d k : ℕ}
    (hd : 0 < d) (hs1 : 1 ≤ s) (hcat : D + matrixClass d * s ≤ D + (k : TensorClass) * s) :
    (d : ℝ) ^ exactRankExponent ≤ k := by
  let ν := exactRankExponent
  have hνpos : 0 < ν := lt_of_lt_of_le zero_lt_two
    (le_csInf ⟨_, 2, le_rfl, rfl⟩ (by rintro _ ⟨_, hn, rfl⟩; exact exactMatrixRank_logb_lower hn))
  let C := tcRank D + 1
  have hD : D ≤ (C : TensorClass) * s := calc
    D ≤ (tcRank D : TensorClass) := le_tcRank D
    _ ≤ (C : TensorClass) * 1 := by dsimp [C]; push_cast; simpa using add_mono (le_refl (tcRank D : TensorClass)) (tc_zero_le 1)
    _ ≤ (C : TensorClass) * s := mul_mono le_rfl hs1
  have hiter (m : ℕ) : D + (m : TensorClass) * (matrixClass d * s) ≤ D + (m : TensorClass) * ((k : TensorClass) * s) := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc D + ((m + 1 : ℕ) : TensorClass) * (matrixClass d * s)
          = (D + matrixClass d * s) + (m : TensorClass) * (matrixClass d * s) := by push_cast; ring
        _ ≤ (D + (m : TensorClass) * (matrixClass d * s)) + (k : TensorClass) * s := (add_mono hcat le_rfl).trans_eq (by ring)
        _ ≤ D + ((m + 1 : ℕ) : TensorClass) * ((k : TensorClass) * s) := (add_mono ih le_rfl).trans_eq (by push_cast; ring)
  have hpow (n j : ℕ) : (n : TensorClass) ^ j * matrixClass d ^ j * s ≤ ((n * k + C : ℕ) : TensorClass) ^ j * s := by
    have habs : (n : TensorClass) * matrixClass d * s ≤ ((n * k + C : ℕ) : TensorClass) * s := calc
      (n : TensorClass) * matrixClass d * s ≤ D + (n : TensorClass) * (matrixClass d * s) := by
          simpa [mul_assoc] using add_mono (tc_zero_le D) le_rfl
      _ ≤ (C : TensorClass) * s + (n : TensorClass) * ((k : TensorClass) * s) := (hiter n).trans (add_mono hD le_rfl)
      _ = ((n * k + C : ℕ) : TensorClass) * s := by push_cast; ring
    induction j with
    | zero => simp
    | succ j ih =>
      calc (n : TensorClass) ^ (j + 1) * matrixClass d ^ (j + 1) * s
          = ((n : TensorClass) ^ j * matrixClass d ^ j) * ((n : TensorClass) * matrixClass d * s) := by ring
        _ ≤ ((n * k + C : ℕ) : TensorClass) * ((n : TensorClass) ^ j * matrixClass d ^ j * s) := (mul_mono le_rfl habs).trans_eq (by ring)
        _ ≤ ((n * k + C : ℕ) : TensorClass) ^ (j + 1) * s := (mul_mono le_rfl ih).trans_eq (by ring)
  have hrank_bound (n j g : ℕ) (hg : exactMatrixRank g ≤ n ^ j) :
      exactMatrixRank (d ^ j * g) ≤ tcRank s * (n * k + C) ^ j := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hg
    have hMg : matrixClass g ≤ (n : TensorClass) ^ j := by
      refine (le_tcRank (matrixClass g)).trans ?_
      change (exactMatrixRank g : TensorClass) ≤ _
      rw [← Nat.cast_pow, hq, Nat.cast_add]; simpa using add_mono le_rfl (tc_zero_le (q : TensorClass))
    have hcmp : matrixClass (d ^ j * g) ≤ (((n * k + C) ^ j : ℕ) : TensorClass) * s := by
      rw [Nat.cast_pow, matrixClass_mul, matrixClass_pow]
      have h1 : (n : TensorClass) ^ j * matrixClass d ^ j ≤ ((n : TensorClass) ^ j * matrixClass d ^ j) * s := by
        simpa using mul_mono (le_refl ((n : TensorClass) ^ j * matrixClass d ^ j)) hs1
      exact (mul_mono le_rfl hMg).trans ((mul_comm _ _).trans_le (h1.trans (hpow n j)))
    simpa only [tcRank_natCast, Nat.mul_comm] using (tcRank_mono hcmp).trans (tcRank_mul_le _ s)
  by_contra! hlt
  obtain ⟨n, hn⟩ := exists_nat_gt (max ((C : ℝ) / ((d : ℝ) ^ ν - k)) 1)
  have hn1 : 1 ≤ n := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hn).le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let N : ℝ := (n * k + C : ℕ)
  have hNpos : 0 < N := by dsimp [N, C]; exact_mod_cast (by omega : 0 < n * k + (tcRank D + 1))
  have hr1 : 1 < ((d : ℝ) ^ ν * n) / N := (one_lt_div hNpos).2 <| by
    have := (div_lt_iff₀ (sub_pos.2 hlt)).1 (lt_of_le_of_lt (le_max_left _ _) hn); dsimp [N]; push_cast; nlinarith
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt (n : ℝ) hr1
  let m := m₀ + 1
  let θ : ℝ := (m : ℝ) / (m + 1 : ℕ)
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hNlt : N < (d : ℝ) ^ ν * (n : ℝ) ^ θ := by
    refine lt_of_pow_lt_pow_left₀ (m + 1) (by positivity) ?_
    have hm_gt : (n : ℝ) < (((d : ℝ) ^ ν * n) / N) ^ (m + 1) := hm₀.trans_le (pow_le_pow_right₀ hr1.le (by omega))
    rw [div_pow, lt_div_iff₀ (pow_pos hNpos _), mul_pow, pow_succ (n : ℝ) m] at hm_gt
    rw [mul_pow, ← Real.rpow_mul_natCast hnpos.le, show θ * (m + 1 : ℕ) = m from div_mul_cancel₀ _ hm1, Real.rpow_natCast]
    exact lt_of_mul_lt_mul_right (a := (n : ℝ)) (by linarith) hnpos.le
  have hντ : ν < ν / θ := by
    rw [lt_div_iff₀ hθ0]; dsimp [θ]; rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; push_cast; nlinarith
  obtain ⟨u, hu, huR⟩ := exists_exactMatrixRank_lt_rpow hντ
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hRu : (exactMatrixRank u : ℝ) ^ θ ≤ (u : ℝ) ^ ν :=
    (Real.rpow_le_rpow (Nat.cast_nonneg _) huR.le hθ0.le).trans_eq
      (by rw [← Real.rpow_mul hu0.le, div_mul_cancel₀ _ hθ0.ne'])
  have hRu1 : 1 < exactMatrixRank u := by have := exactMatrixRank_lower (by omega : 0 < u); nlinarith
  have hrk_pow (r : ℕ) : exactMatrixRank (u ^ r) ≤ exactMatrixRank u ^ r := by
    change tcRank (matrixClass (u ^ r)) ≤ tcRank (matrixClass u) ^ r; rw [matrixClass_pow]
    induction r with
    | zero => simpa using (tcRank_natCast 1).le
    | succ r ih => rw [pow_succ, pow_succ]; exact (tcRank_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)
  refine not_le_of_gt hNlt (le_of_eventually_pow_le_const_mul_pow (C := (u : ℝ) ^ ν * tcRank s) (by positivity) ?_)
  filter_upwards with j
  obtain ⟨l, hlo, hhi⟩ := exists_nat_pow_near (one_le_pow₀ hn1 (n := j)) hRu1
  have hl2 : ((n : ℝ) ^ θ) ^ j ≤ (u : ℝ) ^ ν * ((u ^ l : ℕ) : ℝ) ^ ν := calc
    ((n : ℝ) ^ θ) ^ j = ((n ^ j : ℕ) : ℝ) ^ θ := by rw [Real.rpow_pow_comm hnpos.le, Nat.cast_pow]
    _ ≤ ((exactMatrixRank u ^ (l + 1) : ℕ) : ℝ) ^ θ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhi.le) hθ0.le
    _ = ((exactMatrixRank u : ℝ) ^ θ) ^ (l + 1) := by rw [Nat.cast_pow, Real.rpow_pow_comm (Nat.cast_nonneg _)]
    _ ≤ ((u : ℝ) ^ ν) ^ (l + 1) := pow_le_pow_left₀ (by positivity) hRu _
    _ = (u : ℝ) ^ ν * ((u ^ l : ℕ) : ℝ) ^ ν := by rw [pow_succ', Nat.cast_pow, Real.rpow_pow_comm hu0.le]
  have hlow : ((d ^ j * u ^ l : ℕ) : ℝ) ^ ν ≤ exactMatrixRank (d ^ j * u ^ l) := by
    let g := d ^ j * u ^ l
    have hg0 : 0 < g := mul_pos (pow_pos hd j) (pow_pos (by omega : 0 < u) l)
    by_cases hg2 : 2 ≤ g
    · exact (Real.le_logb_iff_rpow_le (by exact_mod_cast (by omega : 1 < g)) (by exact_mod_cast exactMatrixRank_pos hg0)).1
        (csInf_le ⟨2, by rintro _ ⟨_, hm, rfl⟩; exact exactMatrixRank_logb_lower hm⟩ ⟨g, hg2, rfl⟩)
    · have hg1 : d ^ j * u ^ l = 1 := by omega
      rw [hg1]; simpa using (by exact_mod_cast exactMatrixRank_lower zero_lt_one : (1 : ℝ) ≤ exactMatrixRank 1)
  calc ((d : ℝ) ^ ν * (n : ℝ) ^ θ) ^ j
      = ((d ^ j : ℕ) : ℝ) ^ ν * ((n : ℝ) ^ θ) ^ j := by rw [mul_pow, Real.rpow_pow_comm (Nat.cast_nonneg d), Nat.cast_pow]
    _ ≤ (u : ℝ) ^ ν * ((d ^ j * u ^ l : ℕ) : ℝ) ^ ν :=
          (mul_le_mul_of_nonneg_left hl2 (by positivity)).trans_eq
            (by rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]; ring)
    _ ≤ (u : ℝ) ^ ν * (exactMatrixRank (d ^ j * u ^ l) : ℝ) := mul_le_mul_of_nonneg_left hlow (by positivity)
    _ ≤ ((u : ℝ) ^ ν * tcRank s) * N ^ j := by
          rw [mul_assoc, ← Nat.cast_pow]; gcongr; exact_mod_cast hrank_bound n j (u ^ l) ((hrk_pow l).trans hlo)

def normStates (d : TensorClass) (k : ℕ) : Set (TensorClass → ℝ) :=
  {f | (∀ x, 0 ≤ f x ∧ f x ≤ tcRank x) ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, x ≤ y → f x ≤ f y) ∧ (∀ x, 1 ≤ x → (k : ℝ) * f x ≤ f (d * x))}

theorem normStates_nonempty {d k : ℕ} (hd : 2 ≤ d) (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent) :
    (normStates (matrixClass d) k).Nonempty := by
  let dS := matrixClass d
  let e1 (x : TensorClass) : TensorClass →₀ ℚ := Finsupp.single x 1
  let evalN : (TensorClass →₀ ℕ) →ₗ[ℕ] TensorClass := Finsupp.linearCombination ℕ id
  let toQ : (TensorClass →₀ ℕ) →+ (TensorClass →₀ ℚ) := Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℚ)
  have htoQ_single (x : TensorClass) (n : ℕ) : toQ (.single x n) = (n : ℚ) • e1 x := by
    simp [toQ]; exact (Finsupp.smul_single_one x (n : ℚ)).symm
  have pos_mul_det {a : ℕ} (ha : 0 < a) {t : TensorClass} (ht : 1 ≤ t) : 1 ≤ (a : TensorClass) * t := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    push_cast; rw [add_mul, one_mul]; simpa using add_mono (tc_zero_le _) ht
  let catLE (a b : TensorClass) : Prop :=
    ∃ D det : TensorClass, (det = 0 ∨ 1 ≤ det) ∧ D + a + dS * det ≤ D + b + (k : TensorClass) * det
  have catLE_of_le {a b : TensorClass} (h : a ≤ b) : catLE a b := ⟨0, 0, .inl rfl, by simpa using h⟩
  have catLE_mul {a : ℕ} (ha : 0 < a) {u v : TensorClass} : catLE u v → catLE ((a : TensorClass) * u) ((a : TensorClass) * v) := by
    rintro ⟨D, det, hdet, hle⟩
    refine ⟨(a : TensorClass) * D, (a : TensorClass) * det, hdet.imp (fun h => by simp [h]) (pos_mul_det ha), ?_⟩
    exact (by ring : _ = (a : TensorClass) * (D + u + dS * det)).trans_le ((mul_mono le_rfl hle).trans_eq (by ring))
  have catLE_add {u₁ v₁ u₂ v₂ : TensorClass} : catLE u₁ v₁ → catLE u₂ v₂ → catLE (u₁ + u₂) (v₁ + v₂) := by
    rintro ⟨D₁, det₁, h₁, hle₁⟩ ⟨D₂, det₂, h₂, hle₂⟩
    refine ⟨D₁ + D₂, det₁ + det₂, ?_, (by ring : _ = (D₁ + u₁ + dS * det₁) + (D₂ + u₂ + dS * det₂)).trans_le
      ((add_mono hle₁ hle₂).trans_eq (by ring))⟩
    rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
    · exact .inl (add_zero 0)
    · exact .inr (by simpa using h₂)
    · exact .inr (by simpa using h₁)
    · exact .inr (h₁.trans (by simpa using add_mono le_rfl (tc_zero_le _)))
  let s : Set (TensorClass →₀ ℚ) := {v | ∃ (m : ℕ) (_ : 0 < m) (p q : TensorClass →₀ ℕ),
    (m : ℚ) • v = toQ q - toQ p ∧ catLE (evalN p) (evalN q)}
  have s_zero : (0 : TensorClass →₀ ℚ) ∈ s := ⟨1, zero_lt_one, 0, 0, by simp, catLE_of_le (by simp)⟩
  have s_add {u v : TensorClass →₀ ℚ} (hu : u ∈ s) (hv : v ∈ s) : u + v ∈ s := by
    rcases hu with ⟨m₁, hm₁, p₁, q₁, hu₁, hc₁⟩; rcases hv with ⟨m₂, hm₂, p₂, q₂, hv₁, hc₂⟩
    refine ⟨m₁ * m₂, mul_pos hm₁ hm₂, m₂ • p₁ + m₁ • p₂, m₂ • q₁ + m₁ • q₂, ?_, ?_⟩
    · simp only [map_add, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_mul]
      calc ((m₁ : ℚ) * m₂) • (u + v) = (m₂ : ℚ) • ((m₁ : ℚ) • u) + (m₁ : ℚ) • ((m₂ : ℚ) • v) := by module
        _ = _ := by rw [hu₁, hv₁]; module
    · simpa only [map_add, map_smul, nsmul_eq_mul] using catLE_add (catLE_mul hm₂ hc₁) (catLE_mul hm₁ hc₂)
  have s_smul {c : ℚ} {v : TensorClass →₀ ℚ} (hc : 0 ≤ c) (hv : v ∈ s) : c • v ∈ s := by
    rcases eq_or_lt_of_le hc with rfl | hcpos
    · simpa using s_zero
    rcases hv with ⟨m, hm, p, q, hv₁, hcv⟩
    let a := c.num.toNat; let b := c.den
    have ha : 0 < a := Int.lt_toNat.2 (Rat.num_pos.2 hcpos)
    refine ⟨b * m, mul_pos c.den_pos hm, a • p, a • q, ?_, ?_⟩
    · have hca : (b : ℚ) • c = (a : ℚ) := by
        rw [smul_eq_mul, ← c.num_div_den, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 c.den_pos.ne')]
        exact_mod_cast (Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)).symm
      simp only [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_mul]
      calc ((b : ℚ) * m) • (c • v) = ((b : ℚ) • c) • ((m : ℚ) • v) := by module
        _ = (a : ℚ) • (toQ q - toQ p) := by rw [hca, hv₁]
        _ = _ := by module
    · simpa only [map_smul, nsmul_eq_mul] using catLE_mul ha hcv
  have s_low (x : TensorClass) : e1 x ∈ s :=
    ⟨1, zero_lt_one, 0, .single x 1, by simp [htoQ_single], catLE_of_le (by simp [evalN, tc_zero_le x])⟩
  have s_up (x : TensorClass) : (tcRank x : ℚ) • e1 1 - e1 x ∈ s :=
    ⟨1, zero_lt_one, .single x 1, .single 1 (tcRank x), by simp [htoQ_single], catLE_of_le (by simp [evalN, nsmul_eq_mul, le_tcRank x])⟩
  have he1_ne : e1 1 ∉ (⊥ : Submodule ℚ (TensorClass →₀ ℚ)) := fun h => by
    have := Finsupp.ext_iff.1 ((Submodule.mem_bot ℚ).1 h) 1; simp [e1] at this
  let p₀ : (TensorClass →₀ ℚ) →ₗ.[ℚ] ℝ := (⊥ : (TensorClass →₀ ℚ) →ₗ.[ℚ] ℝ).supSpanSingleton (e1 1) 1 he1_ne
  have hp_nonneg (u : p₀.domain) (hu : (u : TensorClass →₀ ℚ) ∈ s) : 0 ≤ p₀ u := by
    have hmem : (u : TensorClass →₀ ℚ) ∈ ℚ ∙ e1 1 := by
      simpa [p₀, LinearPMap.domain_supSpanSingleton, show (⊥ : (TensorClass →₀ ℚ) →ₗ.[ℚ] ℝ).domain = ⊥ from rfl] using u.2
    rcases Submodule.mem_span_singleton.1 hmem with ⟨c, hc⟩
    have hval : p₀ u = (c : ℝ) := by
      rw [show u = ⟨c • e1 1, Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨c, rfl⟩)⟩ from Subtype.ext hc.symm,
        LinearPMap.supSpanSingleton_apply_smul_self, RingHom.id_apply, Rat.smul_def, mul_one]
    rw [hval]; by_contra! hcneg
    have hcneg_q : c < 0 := by exact_mod_cast hcneg
    have hneg1 : -e1 1 ∈ s := by
      have := s_smul (inv_nonneg.2 (neg_nonneg.2 hcneg_q.le)) (hc ▸ hu)
      rwa [inv_neg, neg_smul, smul_smul, inv_mul_cancel₀ hcneg_q.ne, one_smul] at this
    rcases hneg1 with ⟨m, hm, p, q, hv, D, det, hdet, hle⟩
    have hp_eq : p = q + .single 1 m := by
      ext z; have hz := Finsupp.ext_iff.1 hv z
      by_cases h1 : (1 : TensorClass) = z
      · subst h1; simp [toQ, e1] at hz ⊢; exact_mod_cast (by linarith : (p 1 : ℚ) = (q 1 : ℚ) + m)
      · simp [toQ, e1, Finsupp.single_eq_of_ne (Ne.symm h1)] at hz ⊢; exact_mod_cast (by linarith : (p z : ℚ) = q z)
    rw [hp_eq, map_add, show evalN (.single 1 m) = (m : TensorClass) by simp [evalN, nsmul_eq_mul]] at hle
    let D' := D + evalN q
    have hcat : D' + (m : TensorClass) + dS * det ≤ D' + (k : TensorClass) * det := by dsimp [D']; simpa [add_assoc] using hle
    rcases hdet with rfl | hd1
    · rw [mul_zero, mul_zero, add_zero, add_zero] at hcat
      obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      have hD1 : D' + 1 ≤ D' :=
        (by simpa using add_mono (le_refl (D' + 1)) (tc_zero_le (l : TensorClass)) : D' + 1 ≤ D' + 1 + l).trans
          (by push_cast at hcat; simpa [add_comm (1 : TensorClass), add_assoc] using hcat)
      have hiter (j : ℕ) : D' + (j : TensorClass) ≤ D' := by
        induction j with
        | zero => simp
        | succ j ih => exact (by push_cast; ring : D' + ((j + 1 : ℕ) : TensorClass) = D' + j + 1).trans_le ((add_mono ih le_rfl).trans hD1)
      have hrk := tcRank_mono ((by simpa using add_mono (tc_zero_le D') le_rfl :
        ((tcRank D' + 1 : ℕ) : TensorClass) ≤ D' + ((tcRank D' + 1 : ℕ) : TensorClass)).trans (hiter (tcRank D' + 1)))
      rw [tcRank_natCast] at hrk; omega
    · exact not_lt_of_ge (tensor_catalytic_obstruction (by omega) hd1 <|
        (add_mono (by simpa using add_mono (le_refl D') (tc_zero_le (m : TensorClass))) le_rfl).trans hcat) hk
  have hp_dense (y : TensorClass →₀ ℚ) : ∃ x : p₀.domain, (x : TensorClass →₀ ℚ) + y ∈ s := by
    let b (z : TensorClass) : ℚ := max (-y z) 0
    let c : ℚ := ∑ z ∈ y.support, b z * tcRank z
    refine ⟨⟨c • e1 1, Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨c, rfl⟩)⟩, ?_⟩
    have hy_eq : y = ∑ z ∈ y.support, y z • e1 z := by
      simp_rw [e1, Finsupp.smul_single_one]; exact (Finsupp.sum_single y).symm
    have hsum_eq : c • e1 1 + y = ∑ z ∈ y.support, (b z • ((tcRank z : ℚ) • e1 1 - e1 z) + (b z + y z) • e1 z) := by
      conv_lhs => rw [hy_eq]
      dsimp only [c]; rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by simp [smul_sub, add_smul, mul_smul]; abel
    rw [hsum_eq]
    have s_sum : ∀ (t : Finset TensorClass) (g : TensorClass → TensorClass →₀ ℚ), (∀ z ∈ t, g z ∈ s) → (∑ z ∈ t, g z) ∈ s :=
      Finset.induction (fun _ _ => s_zero) fun z t hzt ih g hg => by
        rw [Finset.sum_insert hzt]; exact s_add (hg z (Finset.mem_insert_self _ _)) (ih g fun w hw => hg w (Finset.mem_insert_of_mem hw))
    exact s_sum y.support _ fun z _ => s_add (s_smul (le_max_right _ _) (s_up z))
      (s_smul (by dsimp [b]; linarith [le_max_left (-y z) 0]) (s_low z))
  let S : Set ((TensorClass →₀ ℚ) →ₗ.[ℚ] ℝ) := {q | ∀ x : q.domain, (x : TensorClass →₀ ℚ) ∈ s → 0 ≤ q x}
  have hSc : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := fun c hcs hch y hy => by
    have cne : c.Nonempty := ⟨y, hy⟩
    have hcd : DirectedOn (· ≤ ·) c := hch.directedOn
    refine ⟨LinearPMap.sSup c hcd, fun ⟨x, hx⟩ hxs => ?_, fun _ => LinearPMap.le_sSup hcd⟩
    obtain ⟨_, ⟨f, hfc, rfl⟩, hfx⟩ := (Submodule.mem_sSup_of_directed (cne.image _)
      (directedOn_image.2 (hcd.mono LinearPMap.domain_mono.monotone))).1 hx
    exact (LinearPMap.le_sSup hcd hfc).2 (x := ⟨x, hfx⟩) (y := ⟨x, hx⟩) rfl ▸ hcs hfc ⟨x, hfx⟩ hxs
  obtain ⟨q, hpq, hqs, hq⟩ := zorn_le_nonempty₀ S hSc p₀ hp_nonneg
  have htop : q.domain = ⊤ := by
    contrapose! hq
    have ⟨y, hy⟩ : ∃ y, y ∉ q.domain := by by_contra! h; exact hq (top_unique fun y _ => h y)
    have hqd (z) : ∃ x : q.domain, (x : TensorClass →₀ ℚ) + z ∈ s :=
      let ⟨x, hx⟩ := hp_dense z; ⟨Submodule.inclusion hpq.1 x, hx⟩
    have hne_n : (q '' {x : q.domain | -(x : TensorClass →₀ ℚ) - y ∈ s}).Nonempty :=
      let ⟨x, hx⟩ := hqd (-y); ⟨q (-x), -x, by simpa [sub_eq_add_neg] using hx, rfl⟩
    have hne_p : (q '' {x : q.domain | (x : TensorClass →₀ ℚ) + y ∈ s}).Nonempty := let ⟨x, hx⟩ := hqd y; ⟨q x, x, hx, rfl⟩
    obtain ⟨c, hbc⟩ := exists_between_of_forall_le hne_n hne_p (by
      rintro _ ⟨xn, hxn, rfl⟩ _ ⟨xp, hxp, rfl⟩
      have := hqs (xp - xn) (by simpa [sub_eq_add_neg, add_assoc] using s_add hxp hxn)
      rwa [q.map_sub, sub_nonneg] at this)
    refine ⟨q.supSpanSingleton y (-c) hy, ?_, q.left_le_sup _ _, fun hrq =>
      hy ((sup_le_iff.1 (LinearPMap.domain_mono.monotone hrq)).2 (Submodule.mem_span_singleton_self y))⟩
    rintro ⟨z, hz⟩ hzs
    rcases Submodule.mem_sup.1 hz with ⟨x, hx, _, hy', rfl⟩
    rcases Submodule.mem_span_singleton.1 hy' with ⟨t, rfl⟩
    rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ hx, RingHom.id_apply, Rat.smul_def,
      mul_neg, ← sub_eq_add_neg, sub_nonneg]
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have h1 := s_smul (inv_nonneg.2 (neg_nonneg.2 ht.le)) hzs
      rw [inv_neg, neg_smul, smul_add, smul_smul, mul_comm, mul_inv_cancel₀ ht.ne, one_smul,
        neg_add_rev, add_comm, ← sub_eq_add_neg] at h1
      have hle := hbc.1 ⟨t⁻¹ • ⟨x, hx⟩, h1, rfl⟩
      rw [q.map_smul, Rat.smul_def, Rat.cast_inv] at hle
      have ht' : (t : ℝ) < 0 := by exact_mod_cast ht
      simpa [← mul_assoc, mul_inv_cancel₀ ht'.ne] using mul_le_mul_of_nonpos_left hle ht'.le
    · simpa using hqs ⟨x, hx⟩ (by simpa using hzs)
    · have h1 := s_smul (inv_nonneg.2 ht.le) hzs
      rw [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h1
      have hle := hbc.2 ⟨t⁻¹ • ⟨x, hx⟩, h1, rfl⟩
      rw [q.map_smul, Rat.smul_def, Rat.cast_inv] at hle
      have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
      simpa [← mul_assoc, mul_inv_cancel₀ ht'.ne'] using mul_le_mul_of_nonneg_left hle ht'.le
  rcases q with ⟨qdom, qfun⟩; subst htop
  let g : (TensorClass →₀ ℚ) →ₗ[ℚ] ℝ := qfun.comp (LinearMap.id.codRestrict ⊤ fun _ => trivial)
  have hgs (x : TensorClass →₀ ℚ) (hx : x ∈ s) : 0 ≤ g x := hqs ⟨x, trivial⟩ hx
  let f (x : TensorClass) : ℝ := g (e1 x)
  have hf1 : f 1 = 1 :=
    (hpq.2 (x := ⟨e1 1, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩) rfl).symm.trans
      (LinearPMap.supSpanSingleton_apply_self _ _ _)
  have hg_nat (n : ℕ) (x : TensorClass) : g ((n : ℚ) • e1 x) = (n : ℝ) * f x := by
    rw [g.map_smul, Rat.smul_def, Rat.cast_natCast]
  refine ⟨f, fun x => ⟨hgs _ (s_low x), ?_⟩, hf1, fun x y => ?_, fun x y hxy => ?_, fun x hx => ?_⟩
  · simpa [map_sub, hg_nat, hf1, sub_nonneg] using hgs _ (s_up x)
  · have h1 := hgs (e1 (x + y) - e1 x - e1 y) ⟨1, zero_lt_one, .single x 1 + .single y 1, .single (x + y) 1,
      by simp [htoQ_single]; abel, catLE_of_le (by simp [evalN])⟩
    have h2 := hgs (e1 x + e1 y - e1 (x + y)) ⟨1, zero_lt_one, .single (x + y) 1, .single x 1 + .single y 1,
      by simp [htoQ_single], catLE_of_le (by simp [evalN])⟩
    simp only [map_sub, map_add] at h1 h2; linarith
  · simpa [map_sub, sub_nonneg] using hgs (e1 y - e1 x) ⟨1, zero_lt_one, .single x 1, .single y 1,
      by simp [htoQ_single], catLE_of_le (by simp [evalN, hxy])⟩
  · simpa [map_sub, hg_nat, sub_nonneg] using hgs (e1 (dS * x) - (k : ℚ) • e1 x)
      ⟨1, zero_lt_one, .single x k, .single (dS * x) 1,
        by simp [htoQ_single], 0, x, .inr hx, by simp [evalN, nsmul_eq_mul, add_comm]⟩

theorem exists_detecting_character {d k : ℕ} (hd : 2 ≤ d) (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent) :
    ∃ χ : Character, (k : ℝ) ≤ χ.value (matrixMultiplicationTensor d d d) := by
  let K := normStates (matrixClass d) k
  let nTr (z : TensorClass) (f : TensorClass → ℝ) (x : TensorClass) : ℝ := f (z * x) / f z
  have hKcompact : IsCompact K :=
    (isCompact_pi_infinite fun x => isCompact_Icc (a := (0 : ℝ)) (b := tcRank x)).inter_right <| by
      change IsClosed {f : TensorClass → ℝ | _}; simp only [ofPred_and, ofPred_forall]
      refine (isClosed_eq ?_ ?_).inter ((isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq ?_ ?_).inter
        ((isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_le ?_ ?_).inter
          (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_le ?_ ?_))) <;> fun_prop
  have hKcvx : Convex ℝ K := fun f hf g hg a b ha hb hab =>
    ⟨fun x => ⟨add_nonneg (mul_nonneg ha (hf.1 x).1) (mul_nonneg hb (hg.1 x).1),
      (add_le_add (mul_le_mul_of_nonneg_left (hf.1 x).2 ha) (mul_le_mul_of_nonneg_left (hg.1 x).2 hb)).trans_eq
        (by rw [← add_mul, hab, one_mul])⟩,
     by change a * f 1 + b * g 1 = 1; rw [hf.2.1, hg.2.1]; linarith,
     fun x y => by change a * f (x + y) + b * g (x + y) = (a * f x + b * g x) + (a * f y + b * g y); rw [hf.2.2.1, hg.2.2.1]; ring,
     fun x y hxy => add_le_add (mul_le_mul_of_nonneg_left (hf.2.2.2.1 x y hxy) ha) (mul_le_mul_of_nonneg_left (hg.2.2.2.1 x y hxy) hb),
     fun x hx => by change (k : ℝ) * (a * f x + b * g x) ≤ a * f (matrixClass d * x) + b * g (matrixClass d * x); nlinarith [hf.2.2.2.2 x hx, hg.2.2.2.2 x hx]⟩
  have hKzero {f : TensorClass → ℝ} (hf : f ∈ K) : f 0 = 0 := by have h := hf.2.2.1 0 0; rw [zero_add] at h; linarith
  have hKnat {f : TensorClass → ℝ} (hf : f ∈ K) (n : ℕ) (x : TensorClass) : f ((n : TensorClass) * x) = (n : ℝ) * f x := by
    induction n with
    | zero => simp [hKzero hf]
    | succ n ih => rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hf.2.2.1, ih]; push_cast; ring
  have h1le (w : TensorClass) : 1 ≤ w + 1 := by simpa using add_mono (tc_zero_le w) (le_refl (1 : TensorClass))
  have hK1 {f : TensorClass → ℝ} (hf : f ∈ K) {z : TensorClass} (hz : 1 ≤ z) : 1 ≤ f z := by
    simpa [hf.2.1] using hf.2.2.2.1 1 z hz
  have hKmap {z : TensorClass} (hz : 1 ≤ z) : MapsTo (nTr z) K K := fun f hf => by
    have hfz : 0 < f z := zero_lt_one.trans_le (hK1 hf hz)
    refine ⟨fun x => ⟨div_nonneg (hf.1 _).1 hfz.le, (div_le_iff₀ hfz).2
        (by simpa [hKnat hf] using hf.2.2.2.1 _ _ ((mul_mono le_rfl (le_tcRank x)).trans_eq (mul_comm _ _)))⟩,
      by simp [nTr, hfz.ne'], fun x y => by simp [nTr, mul_add, hf.2.2.1, add_div],
      fun x y hxy => div_le_div_of_nonneg_right (hf.2.2.2.1 _ _ (mul_mono le_rfl hxy)) hfz.le, fun x hx => ?_⟩
    have hzx : 1 ≤ z * x := hz.trans (by simpa using mul_mono (le_refl z) hx)
    have h := hf.2.2.2.2 (z * x) hzx; rw [show matrixClass d * (z * x) = z * (matrixClass d * x) by ring] at h
    simpa [nTr, mul_div_assoc] using div_le_div_of_nonneg_right h hfz.le
  have hR1 : (tcRank (1 : TensorClass) : ℝ) = 1 := by exact_mod_cast tcRank_natCast 1
  let F (w : TensorClass) : Set (TensorClass → ℝ) := {f | ∀ x, f ((w + 1) * x) = f (w + 1) * f x}
  have hFc (w : TensorClass) : IsClosed (F w) := by
    simp only [F, ofPred_forall]; exact isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
  have hslice : ∀ t : Finset TensorClass, ∃ C : Set (TensorClass → ℝ), C ⊆ K ∧ C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
      (∀ z : TensorClass, 1 ≤ z → MapsTo (nTr z) C C) ∧
      ∀ f ∈ C, ∀ w ∈ t, ∀ x, f ((w + 1) * x) = f (w + 1) * f x :=
    Finset.induction ⟨K, Subset.rfl, normStates_nonempty hd hk, hKcompact, hKcvx, fun _ hz => hKmap hz, by simp⟩
      fun w t _ ih => by
        obtain ⟨C, hCK, ⟨f₀, hf₀⟩, hCc, hCcvx, hCm, hCt⟩ := ih
        let z := w + 1
        have hz : 1 ≤ z := h1le w
        let u : ℕ → TensorClass → ℝ := Nat.rec f₀ fun _ g => nTr z g
        let M : ℝ := max (tcRank z : ℝ) 1
        have hu (n : ℕ) : u n ∈ C ∧ 1 ≤ f₀ (z ^ n) ∧ f₀ (z ^ n) ≤ M ^ n ∧
            ∀ x, f₀ (z ^ n * x) = f₀ (z ^ n) * u n x := by
          induction n with
          | zero => exact ⟨hf₀, by simp [(hCK hf₀).2.1], by simp [(hCK hf₀).2.1], fun x => by simp [u, (hCK hf₀).2.1]⟩
          | succ n ih =>
            rcases ih with ⟨hunC, ha1, haM, hmul⟩
            have hun1 : 1 ≤ u n z := hK1 (hCK hunC) hz
            have hunpos : 0 < u n z := zero_lt_one.trans_le hun1
            have han1 : f₀ (z ^ (n + 1)) = f₀ (z ^ n) * u n z := by rw [pow_succ, hmul z]
            refine ⟨hCm z hz hunC, han1 ▸ one_le_mul_of_one_le_of_one_le ha1 hun1, ?_, fun x => ?_⟩
            · rw [han1, pow_succ]; exact mul_le_mul haM (((hCK hunC).1 z).2.trans (le_max_left _ _)) (by positivity) (by positivity)
            · change f₀ (z ^ (n + 1) * x) = f₀ (z ^ (n + 1)) * (u n (z * x) / u n z)
              rw [han1, pow_succ, mul_assoc, hmul (z * x), mul_assoc, mul_div_cancel₀ _ hunpos.ne']
        have happrox (η : ℝ) (hη : 0 < η) : ∃ g ∈ C, ∀ x, |g (z * x) - g z * g x| ≤ 2 * M * tcRank x * η := by
          have ⟨t', ht0, htM, N, hN1, hrat⟩ : ∃ t' : ℝ, 0 < t' ∧ t' ≤ M ∧ ∃ N : ℕ, 1 ≤ N ∧
              f₀ (z ^ N) / t' ^ N + 1 ≤ η * ∑ n ∈ Finset.range N, f₀ (z ^ n) / t' ^ n := by
            let δ := η / 4
            have hδ : 0 < δ := by dsimp [δ]; linarith
            let S : Set ℝ := {r | 0 < r ∧ ∃ B, ∀ n, f₀ (z ^ n) ≤ B * r ^ n}
            have hMS : M ∈ S := ⟨zero_lt_one.trans_le (le_max_right _ _), 1, fun n => by simpa using (hu n).2.2.1⟩
            have h1S : ∀ r ∈ S, 1 ≤ r := fun r ⟨hr0, B, hB⟩ =>
              le_of_eventually_pow_le_const_mul_pow hr0.le (Eventually.of_forall fun n => by simpa using (hu n).2.1.trans (hB n))
            let r₀ := sInf S
            have hr₀1 : 1 ≤ r₀ := le_csInf ⟨M, hMS⟩ h1S
            obtain ⟨r₁, ⟨hr₁0, B, hB⟩, hr₁lt⟩ := exists_lt_of_csInf_lt ⟨M, hMS⟩ (by nlinarith : r₀ < r₀ * (1 + δ))
            let t' := r₁ / (1 + δ)
            have ht0 : 0 < t' := div_pos hr₁0 (by linarith)
            have htr₀ : t' < r₀ := (div_lt_iff₀ (by linarith)).2 hr₁lt
            have htM : t' ≤ M := htr₀.le.trans (csInf_le ⟨1, h1S⟩ hMS)
            have ⟨N₀, hN₀⟩ : ∃ n, 2 / η < f₀ (z ^ n) / t' ^ n := by
              by_contra! hall
              exact not_lt_of_ge (csInf_le ⟨1, h1S⟩ ⟨ht0, 2 / η, fun n => (div_le_iff₀ (pow_pos ht0 n)).1 (hall n)⟩) htr₀
            by_contra! hbad
            let B' := max B 1
            have hbn_le (n) : f₀ (z ^ n) / t' ^ n ≤ B' * (1 + δ) ^ n := by
              have h := (hB n).trans (mul_le_mul_of_nonneg_right (le_max_left B 1) (pow_nonneg hr₁0.le n))
              have hr₁t : r₁ = t' * (1 + δ) := by dsimp [t']; field_simp
              exact (div_le_iff₀ (pow_pos ht0 n)).2 (by rw [hr₁t, mul_pow] at h; dsimp [B']; linarith)
            let W (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, f₀ (z ^ n) / t' ^ n
            have hbn0 (n) : 0 ≤ f₀ (z ^ n) / t' ^ n := div_nonneg (by linarith [(hu n).2.1]) (pow_pos ht0 n).le
            have hWN0 : 2 / η < W (N₀ + 1) := hN₀.trans_le
              (Finset.single_le_sum (fun i _ => hbn0 i) (Finset.mem_range.2 (by omega)))
            have hWpos : 0 < W (N₀ + 1) := (div_pos zero_lt_two hη).trans hWN0
            have hW_ge (m : ℕ) : W (N₀ + 1) * (1 + η / 2) ^ m ≤ W (N₀ + 1 + m) := by
              induction m with
              | zero => simp
              | succ m ih =>
                have hWN : 2 / η < W (N₀ + 1 + m) := hWN0.trans_le
                  ((le_mul_of_one_le_right hWpos.le (one_le_pow₀ (by linarith))).trans ih)
                have hb := hbad t' ht0 htM (N₀ + 1 + m) (by omega)
                have hWs : W (N₀ + 1 + (m + 1)) = W (N₀ + 1 + m) + f₀ (z ^ (N₀ + 1 + m)) / t' ^ (N₀ + 1 + m) := by
                  dsimp [W]; rw [show N₀ + 1 + (m + 1) = (N₀ + 1 + m) + 1 by omega, Finset.sum_range_succ]
                nlinarith [(div_lt_iff₀ hη).1 hWN, pow_succ (1 + η / 2) m]
            have hW_up (N : ℕ) : W N ≤ (B' / δ) * (1 + δ) ^ N := by
              induction N with
              | zero => dsimp [W, B']; simp; positivity
              | succ N ih =>
                dsimp [W] at ih ⊢; rw [Finset.sum_range_succ]
                exact (add_le_add ih (hbn_le N)).trans_eq (by field_simp; ring)
            have hle : 1 + η / 2 ≤ 1 + δ := le_of_eventually_pow_le_const_mul_pow
              (C := (B' / δ) * (1 + δ) ^ (N₀ + 1) / W (N₀ + 1)) (by linarith) <| Eventually.of_forall fun m => by
                have h := (hW_ge m).trans (hW_up (N₀ + 1 + m)); rw [pow_add] at h
                exact ((le_div_iff₀' hWpos).2 h).trans_eq (by ring)
            dsimp [δ] at hle; linarith
          let wt (n : ℕ) : ℝ := f₀ (z ^ n) / t' ^ n
          let W : ℝ := ∑ n ∈ Finset.range N, wt n
          have hwpos (n) : 0 < wt n := div_pos (zero_lt_one.trans_le (hu n).2.1) (pow_pos ht0 n)
          have hWpos : 0 < W := (hwpos 0).trans_le (Finset.single_le_sum (fun n _ => (hwpos n).le) (Finset.mem_range.2 hN1))
          let g : TensorClass → ℝ := ∑ n ∈ Finset.range N, (wt n / W) • u n
          have hgC : g ∈ C := hCcvx.sum_mem (fun n _ => div_nonneg (hwpos n).le hWpos.le)
            (by simp only [div_eq_mul_inv, ← Finset.sum_mul]; exact mul_inv_cancel₀ hWpos.ne') fun n _ => (hu n).1
          have hWg (x) : W * g x = ∑ n ∈ Finset.range N, f₀ (z ^ n * x) / t' ^ n := by
            simp only [g, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => by have := (hu n).2.2.2 x; dsimp [wt]; field_simp; linarith
          have hdiff (x) : |g (z * x) - t' * g x| ≤ M * tcRank x * η := by
            have htel : W * (g (z * x) - t' * g x) = t' * (f₀ (z ^ N * x) / t' ^ N - f₀ x) := by
              rw [mul_sub, hWg (z * x), ← mul_assoc, mul_comm W t', mul_assoc, hWg x]
              conv_rhs => rw [show f₀ x = f₀ (z ^ 0 * x) / t' ^ 0 by simp, ← Finset.sum_range_sub (fun n => f₀ (z ^ n * x) / t' ^ n)]
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun n _ => by rw [pow_succ, mul_assoc, pow_succ]; field_simp
            have hfx0 := (hCK hf₀).1 x; have hwN0 := (hwpos N).le
            have hfN : 0 ≤ f₀ (z ^ N * x) / t' ^ N ∧ f₀ (z ^ N * x) / t' ^ N ≤ wt N * tcRank x := by
              rw [(hu N).2.2.2 x, mul_div_right_comm]
              exact ⟨mul_nonneg hwN0 ((hCK (hu N).1).1 x).1, mul_le_mul_of_nonneg_left ((hCK (hu N).1).1 x).2 hwN0⟩
            have habs : |f₀ (z ^ N * x) / t' ^ N - f₀ x| ≤ (wt N + 1) * tcRank x := abs_le.2 ⟨by nlinarith, by nlinarith⟩
            refine le_of_mul_le_mul_right (a := W) ?_ hWpos
            have h := congrArg abs htel; rw [abs_mul, abs_of_pos hWpos, abs_mul, abs_of_pos ht0] at h
            calc |g (z * x) - t' * g x| * W = t' * |f₀ (z ^ N * x) / t' ^ N - f₀ x| := (mul_comm _ _).trans h
              _ ≤ t' * ((wt N + 1) * tcRank x) := mul_le_mul_of_nonneg_left habs ht0.le
              _ ≤ M * tcRank x * η * W := (mul_le_mul htM (mul_le_mul_of_nonneg_right hrat (Nat.cast_nonneg _))
                  (by positivity) (by positivity)).trans_eq (by ring)
          refine ⟨g, hgC, fun x => ?_⟩
          have hd1 : |g z - t'| ≤ M * η := by simpa [(hCK hgC).2.1, hR1] using hdiff 1
          have hgx := (hCK hgC).1 x
          calc |g (z * x) - g z * g x| = |(g (z * x) - t' * g x) + (t' - g z) * g x| := by ring_nf
            _ ≤ |g (z * x) - t' * g x| + |g z - t'| * g x :=
                (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_sub_comm t' (g z), abs_of_nonneg hgx.1])
            _ ≤ 2 * M * tcRank x * η := (add_le_add (hdiff x) (mul_le_mul hd1 hgx.2 hgx.1 (by positivity))).trans_eq (by ring)
        let G (η : {r : ℝ // 0 < r}) : Set (TensorClass → ℝ) := {g | ∀ x, |g (z * x) - g z * g x| ≤ 2 * M * tcRank x * η.1}
        have hGc (η) : IsClosed (G η) := by
          simp only [G, ofPred_forall]; exact isClosed_iInter fun _ => isClosed_le (by fun_prop) (by fun_prop)
        obtain ⟨g, hgC, hg⟩ := hCc.inter_iInter_nonempty G hGc fun s => by
          by_cases hs : s.Nonempty
          · obtain ⟨g, hgC, hg⟩ := happrox (s.inf' hs Subtype.val) ((Finset.lt_inf'_iff hs).2 fun r _ => r.2)
            exact ⟨g, hgC, Set.mem_iInter₂.2 fun r hr x => (hg x).trans
              (mul_le_mul_of_nonneg_left (Finset.inf'_le Subtype.val hr) (by positivity))⟩
          · obtain ⟨g, hgC, _⟩ := happrox 1 zero_lt_one
            exact ⟨g, hgC, by simp [Finset.not_nonempty_iff_eq_empty.1 hs]⟩
        have hgz (x) : g (z * x) = g z * g x := by
          by_contra hne
          have hpos : 0 < |g (z * x) - g z * g x| := abs_pos.2 (sub_ne_zero.2 hne)
          have hle := Set.mem_iInter.1 hg ⟨|g (z * x) - g z * g x| / (2 * M * tcRank x + 1), by positivity⟩ x
          have : 0 ≤ 2 * M * tcRank x := by positivity
          nlinarith [(le_div_iff₀ (by positivity : 0 < 2 * M * tcRank x + 1)).1
            (by simpa only [mul_div_assoc'] using hle)]
        let c := g z
        have hcl : IsClosed {f : TensorClass → ℝ | ∀ x, f (z * x) = c * f x} := by
          simp only [ofPred_forall]; exact isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
        have hcvx : Convex ℝ {f : TensorClass → ℝ | ∀ x, f (z * x) = c * f x} := fun f hf h hh a b _ _ _ x => by
          change a * f (z * x) + b * h (z * x) = c * (a * f x + b * h x); rw [hf x, hh x]; ring
        refine ⟨C ∩ {f | ∀ x, f (z * x) = c * f x}, fun _ hf => hCK hf.1, ⟨g, hgC, hgz⟩,
          hCc.inter_right hcl, hCcvx.inter hcvx,
          fun u hu f hf => ⟨hCm u hu hf.1, fun x => by
            change f (u * (z * x)) / f u = c * (f (u * x) / f u)
            rw [show u * (z * x) = z * (u * x) by ac_rfl, hf.2 (u * x)]; ring⟩,
          fun f hf v hv x => ?_⟩
        rcases Finset.mem_insert.mp hv with rfl | hvt
        · rw [show f z = c by simpa [(hCK hf.1).2.1] using hf.2 1]; exact hf.2 x
        · exact hCt f hf.1 v hvt x
  obtain ⟨f, hf, hfmul⟩ := hKcompact.inter_iInter_nonempty F hFc fun t => by
    obtain ⟨C, hCK, ⟨f, hf⟩, _, _, _, hCt⟩ := hslice t
    exact ⟨f, hCK hf, mem_iInter₂.2 fun w hw => hCt f hf w hw⟩
  let φ : TensorClass →+* ℝ :=
    { toFun := f, map_zero' := hKzero hf, map_one' := hf.2.1, map_add' := hf.2.2.1
      map_mul' := fun x y => by
        have hm := mem_iInter.1 hfmul x y
        rw [add_mul, one_mul, hf.2.2.1, hf.2.2.1, hf.2.1] at hm; linarith }
  have hφ : Monotone φ := fun x y hxy => hf.2.2.2.1 x y hxy
  exact ⟨{
    value := fun T => φ (classOf T)
    nonneg := fun T => by simpa using hφ (tc_zero_le _)
    map_one := φ.map_one
    map_directSum := fun T => by rw [classOf_directSum, map_sum]
    map_product := fun T S => by rw [classOf_product, map_mul]
    monotone := fun T A B C => hφ ((classOf_le_iff _ _).2 ⟨A, B, C, rfl⟩) },
    by simpa [φ, matrixClass, hf.2.1] using hf.2.2.2.2 1 le_rfl⟩

/-! ### Cyclotomic Finite Separation & Convolution -/

abbrev CycAlg (L : ℕ) := AdjoinRoot (Polynomial.cyclotomic L ℤ)
abbrev CycIdx (L : ℕ) := Fin (Polynomial.cyclotomic L ℤ).natDegree

instance cyc_isDomain (L : ℕ) [NeZero L] : IsDomain (CycAlg L) :=
  AdjoinRoot.isDomain_of_prime (Polynomial.cyclotomic.irreducible (NeZero.pos L)).prime

theorem cyc_deg_pos (L : ℕ) [NeZero L] : 0 < (Polynomial.cyclotomic L ℤ).natDegree := by
  rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos L)

instance cyc_charZero (L : ℕ) [NeZero L] : CharZero (CycAlg L) :=
  charZero_of_injective_algebraMap <| AdjoinRoot.of.injective_of_monic_of_degree_pos
    (Polynomial.cyclotomic.monic L ℤ) (Polynomial.natDegree_pos_iff_degree_pos.1 (cyc_deg_pos L))

theorem cycRoot_prim (L : ℕ) [NeZero L] :
    IsPrimitiveRoot (AdjoinRoot.root (Polynomial.cyclotomic L ℤ)) L :=
  (Polynomial.isRoot_cyclotomic_iff_charZero (NeZero.pos L)).1 <| by
    rw [← Polynomial.map_cyclotomic_int L (CycAlg L)]; exact AdjoinRoot.isRoot_root _

theorem sum_root_pow {E : Type*} [CommRing E] [IsDomain E] {ζ : E} {L e : ℕ}
    (hζ : IsPrimitiveRoot ζ L) (h0 : 0 < e) (h2 : e < 2 * L) :
    (∑ r : Fin L, ζ ^ (r.val * e)) = if e = L then (L : E) else 0 := by
  have hdvd : ζ ^ e = 1 ↔ e = L := (hζ.pow_eq_one_iff_dvd e).trans
    ⟨fun ⟨k, hk⟩ => by rcases k with _ | _ | k <;> nlinarith, fun h => h ▸ dvd_refl L⟩
  rw [Fin.sum_univ_eq_sum_range (fun r => ζ ^ (r * e))]
  simp_rw [mul_comm _ e, pow_mul]
  split_ifs with hL
  · simp [hdvd.2 hL]
  · refine (mul_eq_zero.1 ?_).resolve_left (sub_ne_zero.2 (Ne.symm (mt hdvd.1 hL)))
    rw [mul_neg_geom_sum, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self]

theorem cyc_coprime_bound {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y'] [Fintype Z']
    (χ : Character) (T : Tensor ℤ X Y Z) (S : Tensor ℤ X' Y' Z') (L : ℕ) (hL0 : 0 < L)
    (hdeg : ∀ M : ℕ, L ≤ M → ∃ k Lx Ly : ℕ,
      Nonempty (Tensor.PolynomialRestrictionDegeneration
        (fun x y z => algebraMap ℤ (CycAlg M) (Tensor.directSum (fun _ : Fin M => T) x y z))
        (fun x y z => algebraMap ℤ (CycAlg M) ((M : ℤ) * S x y z)) k Lx Ly)) :
    χ.value S ≤ (L + 1 : ℝ) * χ.value T := by
  let descSrc (M Ux Uy n : ℕ) :=
    Tensor.directSum fun _ : CycIdx M × CycIdx M =>
      Tensor.directSum fun _ : Fin (Ux * n + 1) × Fin (Uy * n + 1) =>
        Tensor.power (Tensor.directSum fun _ : Fin M => T) n
  have hdesc (M : ℕ) (hM : L ≤ M) : ∃ Ux Uy : ℕ, ∀ n : ℕ, ∃ A C D,
      Tensor.restrict A C D (descSrc M Ux Uy n) = fun x y z => (M : ℤ) ^ n * Tensor.power S n x y z := by
    let : NeZero M := ⟨by omega⟩
    obtain ⟨k, Lx, Ly, ⟨D⟩⟩ := hdeg M hM
    refine ⟨Lx, Ly, fun n => ?_⟩
    let Tn := Tensor.directSum fun _ : Fin (Lx * n + 1) × Fin (Ly * n + 1) =>
      Tensor.power (Tensor.directSum fun _ : Fin M => T) n
    let Sn := fun x y z => (M : ℤ) ^ n * Tensor.power S n x y z
    have hsrc : (fun x y z => algebraMap ℤ (CycAlg M) (Tn x y z)) =
        Tensor.directSum fun _ : Fin (Lx * n + 1) × Fin (Ly * n + 1) =>
          Tensor.power (fun x y z => algebraMap ℤ (CycAlg M) (Tensor.directSum (fun _ : Fin M => T) x y z)) n := by
      funext x y z; simp only [Tn, Tensor.directSum, Tensor.power, Tensor.prodTensor]; split_ifs <;> simp [map_prod]
    have htrg : Tensor.power (fun x y z => algebraMap ℤ (CycAlg M) ((M : ℤ) * S x y z)) n =
        fun x y z => algebraMap ℤ (CycAlg M) (Sn x y z) := by
      funext x y z; simp [Tensor.power, Tensor.prodTensor, Sn, map_mul, map_pow, map_prod, Finset.prod_mul_distrib]
    let A0 (x : Fin n → X') (q : (Fin (Lx * n + 1) × Fin (Ly * n + 1)) × _) := ((D.power n).leftMap x q.2).coeff q.1.1
    let B0 (y : Fin n → Y') (q : (Fin (Lx * n + 1) × Fin (Ly * n + 1)) × _) := ((D.power n).middleMap y q.2).coeff q.1.2
    let C0 (z : Fin n → Z') (q : (Fin (Lx * n + 1) × Fin (Ly * n + 1)) × _) :=
      shiftedCoeff ((D.power n).rightMap z q.2) (k * n) (q.1.1.val + q.1.2.val)
    have heq : Tensor.restrict A0 B0 C0 (fun x y z => algebraMap ℤ (CycAlg M) (Tn x y z)) =
        fun x y z => algebraMap ℤ (CycAlg M) (Sn x y z) := by
      rw [hsrc, ← htrg]; exact (D.power n).extract.symm
    let pb := AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic M ℤ)
    let b : Module.Basis (CycIdx M) ℤ (CycAlg M) := pb.basis
    let π := b.coord ⟨0, cyc_deg_pos M⟩
    have hπ1 : π 1 = 1 := by
      have h1 : b ⟨0, cyc_deg_pos M⟩ = 1 := (pb.basis_eq_pow ⟨0, cyc_deg_pos M⟩).trans (pow_zero _)
      rw [Module.Basis.coord_apply, ← h1, Module.Basis.repr_self]; simp
    have hm (v : CycAlg M) (r : ℤ) : π (v * algebraMap ℤ (CycAlg M) r) = π v * r := by
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    have hexp (v w t : CycAlg M) : π (v * w * t) = ∑ q : CycIdx M × CycIdx M,
        b.repr v q.1 * b.repr w q.2 * π (b q.1 * b q.2 * t) := by
      conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul, Fintype.sum_prod_type]
      exact Finset.sum_comm.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    refine ⟨fun x q => b.repr (A0 x q.2) q.1.1, fun y q => b.repr (B0 y q.2) q.1.2,
      fun z q => π (b q.1.1 * b q.1.2 * C0 z q.2), ?_⟩
    dsimp only [descSrc]
    rw [restrict_directSum (fun _ : CycIdx M × CycIdx M => Tn)
      (fun q x u => b.repr (A0 x u) q.1) (fun q y v => b.repr (B0 y v) q.2) (fun q z w => π (b q.1 * b q.2 * C0 z w))]
    funext x y z; change _ = Sn x y z
    have hπS : Sn x y z = π (Tensor.restrict A0 B0 C0 (fun u v w => algebraMap ℤ (CycAlg M) (Tn u v w)) x y z) := by
      rw [congrFun (congrFun (congrFun heq x) y) z, Algebra.algebraMap_eq_smul_one, map_smul, hπ1, smul_eq_mul, mul_one]
    rw [hπS]; simp only [Tensor.restrict, map_sum, hm]
    refine ((Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ =>
      congrArg (· * Tn u v w) (hexp (A0 x u) (B0 y v) (C0 z w))).trans ?_).symm
    simp only [Finset.sum_mul]
    exact sum_comm_three fun (q : CycIdx M × CycIdx M) u v w =>
      b.repr (A0 x u) q.1 * b.repr (B0 y v) q.2 * π (b q.1 * b q.2 * C0 z w) * Tn u v w
  obtain ⟨Ax, Ay, hA⟩ := hdesc L le_rfl
  obtain ⟨Bx, By, hB⟩ := hdesc (L + 1) (Nat.le_succ L)
  let cA : ℝ := (Fintype.card (CycIdx L) : ℝ) ^ 2
  let cB : ℝ := (Fintype.card (CycIdx (L + 1)) : ℝ) ^ 2
  have hval (M Ux Uy n : ℕ) :
      χ.value (descSrc M Ux Uy n) =
        (Fintype.card (CycIdx M) : ℝ) ^ 2 * ((n : ℝ) * Ux + 1) * (n * Uy + 1) * (M : ℝ) ^ n * χ.value T ^ n := by
    simp only [descSrc, χ.map_directSum, χ.value_power, mul_pow, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  refine χ.value_le_mul_of_power_comparisons T S (Ax + Bx) (Ay + By) (cA + cB) (L + 1) (by positivity) fun n => ?_
  obtain ⟨u, v, huv⟩ := IsCoprime.pow (m := n) (n := n) (⟨-1, 1, by ring⟩ : IsCoprime (L : ℤ) ((L : ℤ) + 1))
  obtain ⟨A, B, C, h₁⟩ := hA n
  obtain ⟨A', B', C', h₂⟩ := hB n
  have hsc {U V W : Type} [Fintype U] [Fintype V] [Fintype W] (Q : Tensor ℤ U V W) (c m : ℤ)
      {P₁ P₂ P₃} (h : Tensor.restrict P₁ P₂ P₃ Q = fun x y z => m * Tensor.power S n x y z) (x y z) :
      Tensor.restrict P₁ P₂ (fun z w => c * P₃ z w) Q x y z = c * (m * Tensor.power S n x y z) := by
    rw [← congrFun (congrFun (congrFun h x) y) z]
    simp only [Tensor.restrict, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  let fam (b : Bool) :=
    if b then Tensor.restrict A' B' (fun z w => v * C' z w) (descSrc (L + 1) Bx By n)
    else Tensor.restrict A B (fun z w => u * C z w) (descSrc L Ax Ay n)
  have hfam : Tensor.restrict (fun x (bx : Bool × _) => if bx.2 = x then 1 else 0)
      (fun y (by_ : Bool × _) => if by_.2 = y then 1 else 0)
      (fun z (bz : Bool × _) => if bz.2 = z then 1 else 0) (Tensor.directSum fam) = Tensor.power S n := by
    funext x y z
    simp only [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, Fintype.sum_bool,
      ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Bool.true_eq_false, Bool.false_eq_true,
      and_false, and_true, ↓reduceIte, Finset.sum_const_zero, add_zero, zero_add,
      Finset.sum_ite_eq', Finset.mem_univ]
    dsimp [fam]; rw [hsc _ v _ h₂, hsc _ u _ h₁]; push_cast
    calc v * (((L : ℤ) + 1) ^ n * Tensor.power S n x y z) + u * ((L : ℤ) ^ n * Tensor.power S n x y z)
        = (u * (L : ℤ) ^ n + v * ((L : ℤ) + 1) ^ n) * Tensor.power S n x y z := by ring
      _ = _ := by rw [huv, one_mul]
  have hle := χ.monotone (Tensor.directSum fam) (fun x bx => if bx.2 = x then 1 else 0)
    (fun y by_ => if by_.2 = y then 1 else 0) (fun z bz => if bz.2 = z then 1 else 0)
  rw [hfam, χ.map_directSum, Fintype.sum_bool, add_comm] at hle
  have hc := hle.trans (add_le_add (χ.monotone _ A B _) (χ.monotone _ A' B' _))
  have hv : 0 ≤ χ.value T := χ.nonneg T
  rw [χ.value_power, hval L Ax Ay n, hval (L + 1) Bx By n] at hc
  simp only [Nat.cast_add, Nat.cast_one] at hc ⊢
  have ha : cA * ((n : ℝ) * Ax + 1) * (n * Ay + 1) * (L : ℝ) ^ n * χ.value T ^ n ≤
      cA * ((n : ℝ) * (Ax + Bx) + 1) * (n * (Ay + By) + 1) * (L + 1 : ℝ) ^ n * χ.value T ^ n := by
    dsimp [cA]; gcongr <;> first | positivity | linarith
  have hb : cB * ((n : ℝ) * Bx + 1) * (n * By + 1) * (L + 1 : ℝ) ^ n * χ.value T ^ n ≤
      cB * ((n : ℝ) * (Ax + Bx) + 1) * (n * (Ay + By) + 1) * (L + 1 : ℝ) ^ n * χ.value T ^ n := by
    dsimp [cB]; gcongr <;> first | positivity | linarith
  simpa only [χ.value_power] using (hc.trans (add_le_add ha hb)).trans_eq (by ring)

def sepTarget {X Y Z : Type*} {M : ℕ} (B : Fin M → Tensor ℤ X Y Z) :
    Tensor ℤ (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2 then B y.1.1 x.1 y.1.2 z.1.2 else 0

theorem finiteSeparation_bound_int {M : ℕ} {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (χ : Character) (hM : 0 < M) (B : Fin M → Tensor ℤ X Y Z) :
    (∑ i, χ.value (B i)) * (M : ℝ) ^ χ.pX ≤ 6 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  have hbound : χ.value (sepTarget B) ≤ ((5 * M : ℕ) + 1 : ℝ) * χ.value (sharedFirstTensor B) := by
    refine cyc_coprime_bound χ (sharedFirstTensor B) (sepTarget B) (5 * M) (by omega) fun L hL => ?_
    let : NeZero L := ⟨by omega⟩
    let E := CycAlg L; let ζ := AdjoinRoot.root (Polynomial.cyclotomic L ℤ)
    let BE : Fin M → Tensor E X Y Z := fun i x y z => algebraMap ℤ E (B i x y z)
    let mDeg (h u : ℕ) : ℕ := M ^ 2 + h * u - h ^ 2
    let rDeg (h v : ℕ) : ℕ := M ^ 2 - h * v
    let lMap : (X × Fin M) → (Fin L × X) → Polynomial E := fun x r =>
      if r.2 = x.1 then Polynomial.monomial (x.2.val ^ 2) (ζ ^ (r.1.val * (2 * x.2.val))) else 0
    let mMap : ((Fin M × Y) × Fin M) → (Fin L × (Fin M × Y)) → Polynomial E := fun y r =>
      if r.2 = y.1 then Polynomial.monomial (mDeg y.1.1.val y.2.val) (ζ ^ (r.1.val * (y.2.val + M - y.1.1.val))) else 0
    let rMap : ((Fin M × Z) × Fin M) → (Fin L × (Fin M × Z)) → Polynomial E := fun z r =>
      if r.2 = z.1 then Polynomial.monomial (rDeg z.1.1.val z.2.val) (ζ ^ (r.1.val * (L - M - z.2.val - z.1.1.val))) else 0
    let degBnd {A' B' : Type} [Fintype A'] [Fintype B'] (P : A' → B' → Polynomial E) : ℕ :=
      Finset.univ.sup fun q : A' × B' => (P q.1 q.2).natDegree
    have hdeg_le {A' B' : Type} [Fintype A'] [Fintype B'] (P : A' → B' → Polynomial E) (a : A') (b : B') :
        (P a b).degree ≤ degBnd P :=
      Polynomial.degree_le_of_natDegree_le <| Finset.le_sup (f := fun q : A' × B' => (P q.1 q.2).natDegree) (Finset.mem_univ (a, b))
    have hpoly (x : X × Fin M) (y : (Fin M × Y) × Fin M) (z : (Fin M × Z) × Fin M) :
        Tensor.restrict lMap mMap rMap
          (fun u v w => Polynomial.C (algebraMap ℤ E (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B) u v w))) x y z =
        if y.1.1 = z.1.1 ∧ 2 * x.2.val + y.2.val = z.2.val + 2 * y.1.1.val then
          Polynomial.monomial (x.2.val ^ 2 + mDeg y.1.1.val y.2.val + rDeg y.1.1.val z.2.val)
            ((L : E) * BE y.1.1 x.1 y.1.2 z.1.2) else 0 := by
      have hC : (fun u v w => Polynomial.C (algebraMap ℤ E (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B) u v w))) =
          Tensor.directSum fun _ : Fin L => fun u v w => Polynomial.C (sharedFirstTensor BE u v w) := by
        funext u v w; simp only [Tensor.directSum, sharedFirstTensor, BE]; split_ifs <;> simp
      rw [hC, restrict_directSum (fun _ : Fin L => fun u v w => Polynomial.C (sharedFirstTensor BE u v w))
        (fun r x u => lMap x (r, u)) (fun r y v => mMap y (r, v)) (fun r z w => rMap z (r, w))]
      simp only [Tensor.restrict, lMap, mMap, rMap, ite_mul, mul_ite, zero_mul, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ← Finset.sum_mul]
      by_cases hyz : y.1.1 = z.1.1
      · simp only [sharedFirstTensor, hyz, ↓reduceIte, true_and]
        rw [← hyz]
        simp_rw [Polynomial.monomial_mul_monomial, ← pow_add, ← mul_add, add_assoc]
        have := x.2.isLt; have := y.1.1.isLt; have := y.2.isLt; have := z.2.isLt
        rw [← map_sum, Polynomial.monomial_mul_C, sum_root_pow (cycRoot_prim L) (by omega) (by omega)]
        have hiff : (2 * x.2.val + ((y.2.val + M - y.1.1.val) + (L - M - z.2.val - y.1.1.val)) = L) ↔
            (2 * x.2.val + y.2.val = z.2.val + 2 * y.1.1.val) := by omega
        split_ifs <;> simp_all
      · simp [sharedFirstTensor, hyz]
    have hdeg_phase {g h u v : ℕ} (hh : h < M) (hv : v < M) (hp : 2 * g + u = v + 2 * h) :
        ((g ^ 2 + mDeg h u + rDeg h v : ℕ) : ℤ) = 2 * (M : ℤ) ^ 2 + ((g : ℤ) - h) ^ 2 := by
      have h1 : h ^ 2 ≤ M ^ 2 + h * u := by nlinarith
      have h2 : h * v ≤ M ^ 2 := by nlinarith
      have hp' : 2 * (g : ℤ) + u = v + 2 * h := by exact_mod_cast hp
      dsimp [mDeg, rDeg]; rw [Nat.cast_sub h1, Nat.cast_sub h2]; push_cast
      calc (g : ℤ) ^ 2 + ((M : ℤ) ^ 2 + h * u - h ^ 2) + ((M : ℤ) ^ 2 - h * v)
          = 2 * (M : ℤ) ^ 2 + ((g : ℤ) - h) ^ 2 + h * ((2 * (g : ℤ) + u) - (v + 2 * h)) := by ring
        _ = 2 * (M : ℤ) ^ 2 + ((g : ℤ) - h) ^ 2 := by rw [hp', sub_self, mul_zero, add_zero]
    refine ⟨2 * M ^ 2, degBnd lMap, degBnd mMap, ⟨{
      leftMap := lMap, middleMap := mMap, rightMap := rMap
      left_degree := hdeg_le lMap, middle_degree := hdeg_le mMap
      vanishes := fun x y z j hj => ?_, leading := fun x y z => ?_ }⟩⟩
    · rw [hpoly]; split_ifs with hcond
      · apply Polynomial.coeff_monomial_of_ne
        have hd := hdeg_phase y.1.1.isLt z.2.isLt hcond.2
        have hzle : ((2 * M ^ 2 : ℕ) : ℤ) ≤ ((x.2.val ^ 2 + mDeg y.1.1.val y.2.val + rDeg y.1.1.val z.2.val : ℕ) : ℤ) := by
          rw [hd]; push_cast; linarith [sq_nonneg ((x.2.val : ℤ) - y.1.1.val)]
        have := Nat.cast_le.1 hzle; omega
      · simp
    · rw [hpoly]
      by_cases hxy : x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2
      · obtain ⟨hx2, hyz, hy2⟩ := hxy
        have hp : 2 * x.2.val + y.2.val = z.2.val + 2 * y.1.1.val := by rw [hx2, hy2, Nat.add_comm]
        have hd : x.2.val ^ 2 + mDeg y.1.1.val y.2.val + rDeg y.1.1.val z.2.val = 2 * M ^ 2 :=
          Nat.cast_inj.1 (by rw [hdeg_phase y.1.1.isLt z.2.isLt hp, hx2]; push_cast; ring)
        rw [ite_eq_left ⟨hyz, hp⟩, hd, Polynomial.coeff_monomial_same]
        simp [sepTarget, hx2, hyz, hy2, BE]
      · simp only [sepTarget, hxy, ↓reduceIte, mul_zero, map_zero]
        split_ifs with hcond
        · apply Polynomial.coeff_monomial_of_ne
          intro heq
          have hd := hdeg_phase y.1.1.isLt z.2.isLt hcond.2
          have hcast : ((2 * M ^ 2 : ℕ) : ℤ) = 2 * (M : ℤ) ^ 2 := by push_cast; ring
          have hgh : (x.2.val : ℤ) = y.1.1.val := sub_eq_zero.1 (sq_eq_zero_iff.1 (by omega))
          exact hxy ⟨Fin.ext (by omega), hcond.1, Fin.ext (by omega)⟩
        · simp
  have hL : ((5 * M : ℕ) + 1 : ℝ) ≤ 6 * (M : ℝ) := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    push_cast; linarith
  have htarget := hbound.trans (mul_le_mul_of_nonneg_right hL (χ.nonneg _))
  let e1 : (X × Fin M) ≃ (Fin M × (X × Unit)) :=
    ⟨fun x => (x.2, (x.1, ())), fun x => (x.2.1, x.1), fun _ => rfl, fun ⟨_, _, ()⟩ => rfl⟩
  have hdir : sepTarget B = Tensor.pullback e1 (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
      (Tensor.directSum fun h => Tensor.product (B h) (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin M))))) := by
    funext x y z
    simp only [sepTarget, Tensor.pullback, Tensor.directSum, Tensor.product, Tensor.cyclic,
      Tensor.dotPairing, e1, Equiv.coe_fn_mk, Equiv.prodAssoc_apply]
    rcases eq_or_ne x.2 y.1.1 with h1 | h1 <;> rcases eq_or_ne y.1.1 z.1.1 with h2 | h2 <;> simp_all
  rw [hdir, χ.value_reindex, χ.map_directSum] at htarget
  simpa only [χ.map_product, χ.value_cyclic_cyclic_dotPairing hM, Finset.sum_mul] using htarget

/-! ### Subadditivity, Determinant & Sector Inequalities, and 9/4 Bound -/

theorem symmetrized_sharedFirst_subadditive (χ : Character)
    {σ : ℝ} (hσ : 0 < σ) (hsum : (∑ i, (χ.permutedCharacter i).pX) = σ)
    {s : ℕ} {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (B : Fin s → Tensor ℤ X Y Z) :
    ∑ a, χ.sixfoldProduct (B a) ^ (1 / σ) ≤ χ.sixfoldProduct (sharedFirstTensor B) ^ (1 / σ) := by
  let ψ := χ.permutedCharacter
  have hP0 (a : Fin s) : 0 ≤ χ.sixfoldProduct (B a) := χ.sixfoldProduct_nonneg _
  have hQ0 : 0 ≤ χ.sixfoldProduct (sharedFirstTensor B) := χ.sixfoldProduct_nonneg _
  let V (a : Fin s) : ℝ := χ.sixfoldProduct (B a) ^ (1 / σ)
  let S : ℝ := χ.sixfoldProduct (sharedFirstTensor B) ^ (1 / σ)
  let C : ℝ := (6 : ℝ) ^ (6 / σ)
  refine le_of_eventually_pow_le_poly_mul_pow (C := C) s (Real.rpow_nonneg hQ0 _) (Eventually.of_forall fun N => ?_)
  let cnt (w : Fin N → Fin s) (a : Fin s) : Fin (N + 1) :=
    ⟨(Finset.univ.filter fun j => w j = a).card, Nat.lt_succ_of_le <|
      (Finset.card_filter_le (Finset.univ : Finset (Fin N)) _).trans_eq (by simp)⟩
  have hpf (g : Fin s → ℝ) (w : Fin N → Fin s) : (∏ j, g (w j)) = ∏ a, g a ^ (cnt w a).val := by
    rw [← Finset.prod_fiberwise_of_maps_to (fun j _ => Finset.mem_univ (w j)) fun j => g (w j)]
    exact Finset.prod_congr rfl fun a _ =>
      (Finset.prod_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2]).trans (Finset.prod_const _)
  have hfiber (τ : Fin s → Fin (N + 1)) :
      ∑ w ∈ Finset.univ.filter (fun w => cnt w = τ), (∏ j, V (w j)) ≤ C * S ^ N := by
    let W := Finset.univ.filter (fun w : Fin N → Fin s => cnt w = τ)
    change ∑ w ∈ W, (∏ j, V (w j)) ≤ C * S ^ N
    by_cases hW : W.Nonempty
    · let M := W.card
      have hM : 0 < M := Finset.card_pos.2 hW
      have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
      let e : Fin M ≃ W := W.equivFin.symm
      let Wfam (m : Fin M) := Tensor.prodTensor (fun j => B ((e m).1 j))
      have hpull : Tensor.pullback id
          (fun y : Fin M × (Fin N → Y) => fun j => ((e y.1).1 j, y.2 j))
          (fun z : Fin M × (Fin N → Z) => fun j => ((e z.1).1 j, z.2 j))
          (Tensor.power (sharedFirstTensor B) N) = sharedFirstTensor Wfam := by
        funext x y z
        by_cases hyz : y.1 = z.1
        · simp [Tensor.pullback, Tensor.power, Tensor.prodTensor, sharedFirstTensor, Wfam, hyz]
        · obtain ⟨j, hj⟩ := Function.ne_iff.1 (fun h => hyz (e.injective (Subtype.ext h)))
          simp only [Tensor.pullback, Tensor.power, Tensor.prodTensor, sharedFirstTensor, hyz, ↓reduceIte, id_eq]
          exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
      have hi (i : Fin 6) : (M : ℝ) ^ (ψ i).pX * ∏ a, (ψ i).value (B a) ^ (τ a).val ≤
          6 * (ψ i).value (sharedFirstTensor B) ^ N := by
        have hval (m : Fin M) : (ψ i).value (Wfam m) = ∏ a, (ψ i).value (B a) ^ (τ a).val := by
          rw [(ψ i).value_prodTensor, hpf (fun a => (ψ i).value (B a)) (e m).1, (Finset.mem_filter.1 (e m).2).2]
        have hs1 := finiteSeparation_bound_int (ψ i) hM Wfam
        simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs1
        have hs2 : (ψ i).value (sharedFirstTensor Wfam) ≤ (ψ i).value (sharedFirstTensor B) ^ N := by
          rw [← hpull, ← (ψ i).value_power]; exact (ψ i).value_pullback_le _ _ _ _
        exact (mul_le_mul_iff_right₀ hMr).1 <|
          (by ring : _ = ((M : ℝ) * ∏ a, (ψ i).value (B a) ^ (τ a).val) * (M : ℝ) ^ (ψ i).pX).trans_le
            ((hs1.trans (mul_le_mul_of_nonneg_left hs2 (by positivity))).trans_eq (by ring))
      have hprod := Finset.prod_le_prod₀ (s := Finset.univ)
        (fun i _ => mul_nonneg (by positivity) (Finset.prod_nonneg fun a _ => pow_nonneg ((ψ i).nonneg _) _))
        fun i _ => hi i
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hMr _ Finset.univ, hsum,
        Finset.prod_comm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
      simp_rw [Finset.prod_pow] at hprod
      have hrpow := Real.rpow_le_rpow
        (mul_nonneg (by positivity) (Finset.prod_nonneg fun a _ => pow_nonneg (hP0 a) _)) hprod (by positivity : (0 : ℝ) ≤ 1 / σ)
      have hLHS : (((M : ℝ) ^ σ * ∏ a, χ.sixfoldProduct (B a) ^ (τ a).val) ^ (1 / σ)) = (M : ℝ) * ∏ a, V a ^ (τ a).val := by
        rw [Real.mul_rpow (by positivity) (Finset.prod_nonneg fun a _ => pow_nonneg (hP0 a) _),
          ← Real.rpow_mul hMr.le, mul_one_div_cancel hσ.ne', Real.rpow_one,
          ← Real.finsetProd_rpow Finset.univ _ (fun a _ => pow_nonneg (hP0 a) _)]
        congr 1; refine Finset.prod_congr rfl fun a _ => ?_
        rw [← Real.rpow_natCast_mul (hP0 a), ← Real.rpow_mul_natCast (hP0 a), mul_comm]
      have hRHS : (((6 : ℝ) ^ 6 * χ.sixfoldProduct (sharedFirstTensor B) ^ N) ^ (1 / σ)) = C * S ^ N := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg hQ0 N),
          ← Real.rpow_natCast_mul (by norm_num), Nat.cast_ofNat, mul_one_div,
          ← Real.rpow_natCast_mul hQ0, mul_comm (N : ℝ) (1 / σ), Real.rpow_mul_natCast hQ0]
      have hWsum : ∑ w ∈ W, (∏ j, V (w j)) = (M : ℝ) * ∏ a, V a ^ (τ a).val := by
        rw [Finset.sum_congr rfl fun w hw => by rw [hpf, (Finset.mem_filter.1 hw).2], Finset.sum_const, nsmul_eq_mul]
      dsimp only [ψ, Character.sixfoldProduct] at hrpow hLHS hRHS; rwa [hLHS, hRHS, ← hWsum] at hrpow
    · rw [Finset.not_nonempty_iff_eq_empty.1 hW, Finset.sum_empty]
      exact mul_nonneg (by positivity) (pow_nonneg (Real.rpow_nonneg hQ0 _) N)
  calc (∑ a, V a) ^ N = ∏ _j : Fin N, ∑ a, V a := by simp
    _ = ∑ w : Fin N → Fin s, ∏ j, V (w j) := Fintype.prod_sum fun _ a => V a
    _ = ∑ τ : Fin s → Fin (N + 1), ∑ w ∈ Finset.univ.filter (fun w => cnt w = τ), ∏ j, V (w j) :=
        (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
    _ ≤ ∑ _τ : Fin s → Fin (N + 1), C * S ^ N := Finset.sum_le_sum fun τ _ => hfiber τ
    _ = ((N : ℝ) + 1) ^ s * C * S ^ N := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, mul_assoc]

def diagDegeneration {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (T G : Tensor ℤ U V W) (bY : V → Bool) (bZ : W → Bool)
    (h0 : ∀ u v w, bY v = false → bZ w = false → T u v w = 0)
    (h1 : ∀ u v w, G u v w = if bY v ≠ bZ w then T u v w else 0) :
    Tensor.PolynomialRestrictionDegeneration T G 1 0 1 := by
  let dMap {I : Type} (s : I → ℤ[X]) (o i : I) : ℤ[X] := if i = o then s o else 0
  let sY (v : V) : ℤ[X] := if bY v then X else 1
  let sZ (w : W) : ℤ[X] := if bZ w then X else 1
  have happ (u : U) (v : V) (w : W) :
      Tensor.restrict (dMap fun _ => 1) (dMap sY) (dMap sZ) (fun u' v' w' => C (T u' v' w')) u v w =
        sY v * sZ w * C (T u v w) := by simp [Tensor.restrict, dMap, ite_mul, mul_ite]
  exact {
    leftMap := dMap fun _ => 1, middleMap := dMap sY, rightMap := dMap sZ
    left_degree := fun o i => by by_cases h : i = o <;> simp [dMap, h]
    middle_degree := fun o i => by by_cases h : i = o <;> [cases hb : bY o <;> simp [dMap, sY, h, hb]; simp [dMap, h]]
    vanishes := fun u v w n hn => by
      obtain rfl : n = 0 := by omega
      rw [happ]; (cases hy : bY v <;> cases hz : bZ w <;> simp [sY, sZ, hy, hz, ← pow_two]); exact h0 u v w hy hz
    leading := fun u v w => by
      rw [happ, h1]; (cases hy : bY v <;> cases hz : bZ w <;> simp [sY, sZ, hy, hz, ← pow_two])
      rw [← C_eq_intCast]; exact coeff_C_succ }

abbrev DetIdx (e : ℕ) := Fin (e + 2) ⊕ Fin e

def detAdapted (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (DetIdx e) (DetIdx (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | i, .inl j, .inr k => if j.val = e + 1 ∧ i.val < d ∧ e + i.val = k.val then 1 else 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

def detBranch (d e : ℕ) (n : Fin 2) : Tensor ℤ (Fin (d + 1)) (DetIdx e) (DetIdx (d + e))
  | i, .inl j, .inl k => if n = 0 ∧ i.val + j.val = k.val then 1 else 0
  | i, .inr j, .inr k => if n = 1 ∧ i.val + j.val = k.val then 1 else 0
  | _, _, _ => 0

def twoCopyConv (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (Fin (e + 1) × Fin 2) (Fin (d + e + 1) × Fin 2) :=
  fun i y z => if y.2 = z.2 ∧ i.val + y.1.val = z.1.val then 1 else 0

theorem detAdapted_is_restriction (d e : ℕ) :
    ∃ A B C, Tensor.restrict A B C (twoCopyConv d e) = detAdapted d e := by
  let A (i i' : Fin (d + 1)) : ℤ := if i' = i then 1 else 0
  let B : DetIdx e → (Fin (e + 1) × Fin 2) → ℤ
    | .inl j, (y, b) => if b = 0 then (if y.val = j.val then 1 else 0) else if j.val = e + 1 ∧ y.val = e then 1 else 0
    | .inr j, (y, b) => if b = 0 then (if y.val = j.val + 1 then -1 else 0) else if y.val = j.val then 1 else 0
  let C : DetIdx (d + e) → (Fin (d + e + 1) × Fin 2) → ℤ
    | .inl k, (z, b) => if b = 0 then (if z.val = k.val then 1 else 0) else if z.val + 1 = k.val then 1 else 0
    | .inr k, (z, b) => if b = 0 then 0 else if z.val = k.val then 1 else 0
  have hsum_val {n : ℕ} (m : ℕ) (hm : m < n) (g : Fin n → ℤ) :
      (∑ y : Fin n, if y.val = m then g y else 0) = g ⟨m, hm⟩ := by
    simp_rw [show ∀ y : Fin n, (y.val = m) ↔ (y = ⟨m, hm⟩) from fun y => ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩]; simp
  refine ⟨A, B, C, funext fun i => funext fun j => funext fun k => ?_⟩
  have hstep : Tensor.restrict A B C (twoCopyConv d e) i j k =
      ∑ y : Fin (e + 1), (B j (y, 0) * C k (⟨i.val + y.val, by omega⟩, 0) +
        B j (y, 1) * C k (⟨i.val + y.val, by omega⟩, 1)) := by
    simp only [Tensor.restrict, A, twoCopyConv, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Fin.isValue, Fin.reduceEq, false_and, true_and, ↓reduceIte, mul_ite, mul_one, mul_zero, add_zero, zero_add]
    simp_rw [@eq_comm ℕ (i.val + y.val)]
    rw [hsum_val (i.val + y.val) (by omega), hsum_val (i.val + y.val) (by omega)]
  rw [hstep]
  rcases j with j | j
  · by_cases hj : j.val < e + 1
    · have hne : j.val ≠ e + 1 := by omega
      simp only [B, hne, false_and, ↓reduceIte, Fin.isValue, Fin.reduceEq, add_zero, zero_mul, ite_mul, one_mul]
      rw [hsum_val j.val hj]; rcases k with k | k <;> simp [C, detAdapted, hne]
    · have hje : j.val = e + 1 := by omega
      simp only [B, hje, true_and, show ∀ y : Fin (e + 1), y.val ≠ e + 1 from fun y => by have := y.isLt; omega,
        ↓reduceIte, Fin.isValue, Fin.reduceEq, zero_add, zero_mul, ite_mul, one_mul]
      rw [hsum_val e (Nat.lt_succ_self e)]
      rcases k with k | k
      · simp [C, detAdapted, hje, Nat.add_assoc]
      · simp [C, detAdapted, hje]; have := k.isLt; split_ifs <;> omega
  · simp only [B, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_mul, neg_one_mul, one_mul, zero_mul, Finset.sum_add_distrib]
    rw [hsum_val (j.val + 1) (by omega), hsum_val j.val (by omega)]
    rcases k with k | k
    · simp only [C, Fin.isValue, Fin.reduceEq, ↓reduceIte, detAdapted, show i.val + (j.val + 1) = i.val + j.val + 1 by omega]; ring
    · simp [C, detAdapted]

theorem det_branch_bounds (ψ : Character) (d e : ℕ) :
    ψ.value (detBranch d e 0) = ψ.value (convolution (d + 1) (e + 2)) ∧
    ψ.value (detBranch d e 1) = ψ.value (convolution (d + 1) e) ∧
    ψ.value (sharedFirstTensor (detBranch d e)) ≤ (2 : ℝ) ^ ψ.pX * ψ.value (convolution (d + 1) (e + 1)) := by
  let lbl {m : ℕ} : DetIdx m → Fin 2 | .inl _ => 0 | .inr _ => 1
  refine ⟨ψ.val_pullback_eq _ _ id Sum.inl (fun k => .inl (Fin.cast (by omega) k))
      Function.injective_id Sum.inl_injective (Sum.inl_injective.comp (Fin.castOrderIso (by omega)).injective)
      (fun i j k h => by rcases j with j | j <;> rcases k with k | k <;> simp [detBranch] at h; exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp⟩⟩)
      (fun _ _ _ => by simp [detBranch, convolution]),
    ψ.val_pullback_eq _ _ id Sum.inr (fun k => .inr (Fin.cast (by omega) k))
      Function.injective_id Sum.inr_injective (Sum.inr_injective.comp (Fin.castOrderIso (by omega)).injective)
      (fun i j k h => by rcases j with j | j <;> rcases k with k | k <;> simp [detBranch] at h; exact ⟨⟨i, rfl⟩, ⟨j, rfl⟩, ⟨Fin.cast (by omega) k, by simp⟩⟩)
      (fun _ _ _ => by simp [detBranch, convolution]), ?_⟩
  have hsupp (n : Fin 2) (i) (j : DetIdx e) (k : DetIdx (d + e)) (h : detBranch d e n i j k ≠ 0) :
      lbl j = n ∧ lbl k = n := by
    fin_cases n <;> rcases j with j | j <;> rcases k with k | k <;> simp_all [detBranch, lbl]
  have hdeg := diagDegeneration (detAdapted d e) (∑ n, detBranch d e n)
    (fun | .inl _ => true | .inr _ => false) (fun | .inl _ => false | .inr _ => true)
    (fun _ j k hy hz => by rcases j with j | j <;> rcases k with k | k <;> simp_all [detAdapted])
    (fun i j k => by simp only [Fin.sum_univ_two, Finset.sum_apply]; rcases j with j | j <;> rcases k with k | k <;> simp [detBranch, detAdapted])
  rw [ψ.value_sharedFirstTensor_eq_sum _ lbl lbl hsupp]
  refine (ψ.value_polynomialRestrictionDegeneration_le_ring hdeg).trans ?_
  obtain ⟨A, B, C, hrest⟩ := detAdapted_is_restriction d e
  have hmon : ψ.value (detAdapted d e) ≤ ψ.value (twoCopyConv d e) := hrest ▸ ψ.monotone _ A B C
  have hprod : twoCopyConv d e = Tensor.pullback (fun i => (i, ())) id (fun z => (Fin.cast (by omega) z.1, z.2))
      (Tensor.product (convolution (d + 1) (e + 1)) (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin 2))))) := by
    funext i y z; by_cases hb : y.2 = z.2 <;> simp [twoCopyConv, Tensor.pullback, Tensor.product,
      Tensor.cyclic, Tensor.dotPairing, convolution, hb]
  exact hmon.trans (hprod ▸ (ψ.value_pullback_le _ _ _ _).trans_eq
    (by rw [ψ.map_product, ψ.value_cyclic_cyclic_dotPairing (by decide), Nat.cast_ofNat, mul_comm]))

abbrev YIdx (a : ℕ) := Fin (4 * a - 1)
abbrev ZIdx (a : ℕ) := Fin (a + (4 * a - 1) - 1)

def midY (a j : ℕ) : Prop := a ≤ j ∧ j < 3 * a - 1
def midZ (a k : ℕ) : Prop := 2 * a - 1 ≤ k ∧ k < 3 * a - 1

def secBranch (a : ℕ) (b : Fin 3) : Tensor ℤ (Fin a) (YIdx a) (ZIdx a) :=
  fun i j k =>
    if i.val + j.val = k.val ∧
      ((b = 0 ∧ j.val < a) ∨ (b = 1 ∧ midY a j.val ∧ midZ a k.val) ∨ (b = 2 ∧ 3 * a - 1 ≤ j.val))
    then 1 else 0

theorem sec_branch_bounds (ψ : Character) (a : ℕ) (ha : 1 ≤ a) :
    ψ.value (secBranch a 0) = ψ.value (convolution a a) ∧
    ψ.value (secBranch a 1) = ψ.value (fun i s r => convolution a a i r s) ∧
    ψ.value (secBranch a 2) = ψ.value (convolution a a) ∧
    ψ.value (sharedFirstTensor (secBranch a)) ≤ ψ.value (convolution a (4 * a - 1)) := by
  let sh {m n : ℕ} (off : ℕ) (ho : off + m ≤ n) (r : Fin m) : Fin n := ⟨off + r.val, by have := r.isLt; omega⟩
  have hsh {m n off : ℕ} (ho : off + m ≤ n) : Function.Injective (sh off ho) :=
    fun _ _ heq => Fin.ext (by have := congrArg Fin.val heq; dsimp [sh] at this; omega)
  refine ⟨ψ.val_pullback_eq _ _ id (sh 0 (by omega)) (sh 0 (by omega)) Function.injective_id (hsh (by omega)) (hsh (by omega))
      (fun i j k hn => by
        simp only [secBranch, Fin.isValue, true_and, Fin.reduceEq, false_and, or_false, ne_eq, ite_eq_right_iff,
          one_ne_zero, imp_false, not_not] at hn
        exact ⟨⟨i, rfl⟩, ⟨⟨j.val, hn.2⟩, Fin.ext (by simp [sh])⟩, ⟨⟨k.val, by have := i.isLt; omega⟩, Fin.ext (by simp [sh])⟩⟩)
      (fun i r s => by simp [secBranch, sh, convolution, r.isLt]),
    ψ.val_pullback_eq _ _ Fin.rev (sh a (by omega)) (sh (2 * a - 1) (by omega)) Fin.rev_injective (hsh (by omega)) (hsh (by omega))
      (fun i j k hn => by
        simp only [secBranch, Fin.isValue, Fin.reduceEq, false_and, true_and, false_or, or_false,
          midY, midZ, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hn
        exact ⟨⟨i.rev, Fin.rev_rev i⟩, ⟨⟨j.val - a, by omega⟩, Fin.ext (by dsimp [sh]; omega)⟩,
          ⟨⟨k.val - (2 * a - 1), by omega⟩, Fin.ext (by dsimp [sh]; omega)⟩⟩)
      (fun i s r => by
        have := i.isLt; have := r.isLt; have := s.isLt
        simp only [Fin.val_rev, secBranch, sh, Fin.isValue, Fin.reduceEq, false_and, true_and, false_or, or_false, midY, midZ, convolution]
        congr 1; exact propext ⟨fun _ => by omega, fun _ => ⟨by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩),
    ψ.val_pullback_eq _ _ id (sh (3 * a - 1) (by omega)) (sh (3 * a - 1) (by omega)) Function.injective_id (hsh (by omega)) (hsh (by omega))
      (fun i j k hn => by
        simp only [secBranch, Fin.isValue, Fin.reduceEq, false_and, true_and, false_or, ne_eq, ite_eq_right_iff,
          one_ne_zero, imp_false, not_not] at hn
        have := j.isLt; have := i.isLt
        exact ⟨⟨i, rfl⟩, ⟨⟨j.val - (3 * a - 1), by omega⟩, Fin.ext (by dsimp [sh]; omega)⟩,
          ⟨⟨k.val - (3 * a - 1), by omega⟩, Fin.ext (by dsimp [sh]; omega)⟩⟩)
      (fun i r s => by
        simp only [id_eq, secBranch, sh, Fin.isValue, Fin.reduceEq, false_and, true_and, false_or, convolution]
        congr 1; exact propext ⟨fun _ => by omega, fun _ => ⟨by omega, by omega⟩⟩), ?_⟩
  let yL (j : YIdx a) : Fin 3 := if j.val < a then 0 else if j.val < 3 * a - 1 then 1 else 2
  let zL (k : ZIdx a) : Fin 3 := if k.val < 2 * a - 1 then 0 else if k.val < 3 * a - 1 then 1 else 2
  have hsupp (b : Fin 3) (i : Fin a) (j : YIdx a) (k : ZIdx a) (hn : secBranch a b i j k ≠ 0) :
      yL j = b ∧ zL k = b := by
    have := i.isLt; dsimp only [secBranch, midY, midZ] at hn
    fin_cases b <;> (simp only [yL, zL]; split_ifs at hn ⊢ <;> simp_all <;> omega)
  have hdeg := diagDegeneration (convolution a (4 * a - 1)) (∑ b, secBranch a b)
    (fun j => decide (midY a j.val)) (fun k => !decide (midZ a k.val))
      (fun i j k hy hz => by
        have hy' : ¬midY a j.val := of_decide_eq_false hy
        have hz' : midZ a k.val := of_decide_eq_true (by simpa using hz)
        dsimp [midY, midZ] at hy' hz'; have := i.isLt; simp [convolution]; omega)
      (fun i j k => by
        have := i.isLt
        simp only [Fin.sum_univ_three, Finset.sum_apply, secBranch, Fin.isValue, true_and, Fin.reduceEq,
          false_and, or_false, false_or, convolution, midY, midZ]
        by_cases hij : i.val + j.val = k.val <;>
          by_cases h0 : j.val < a <;>
          by_cases h1 : a ≤ j.val ∧ j.val < 3 * a - 1 <;>
          by_cases hz : 2 * a - 1 ≤ k.val ∧ k.val < 3 * a - 1 <;>
          simp [hij, h0, h1, hz] <;> omega)
  rw [ψ.value_sharedFirstTensor_eq_sum _ yL zL hsupp]
  exact ψ.value_polynomialRestrictionDegeneration_le_ring hdeg

theorem exponent_sum_le_nine_quarters (χ : Character) : χ.pX + χ.pY + χ.pZ ≤ 9 / 4 := by
  let t : ℝ := (χ.pX + χ.pY + χ.pZ) / 3
  suffices hmean : t ≤ 3 / 4 by dsimp [t] at hmean; linarith
  by_cases ht : 0 < t
  · have hσ : 0 < 6 * t := by positivity
    have hsum_pX : (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 6 * t := by
      have hx : χ.swap23Character.pX = χ.pX := by
        unfold Character.pX Character.pZ; congr 2; apply congrArg χ.value; funext x y z; simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]
      have hy : χ.swap23Character.pY = χ.pZ := by
        unfold Character.pY Character.pZ; congr 2; apply congrArg χ.value; funext x y z; simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]
      have hz : χ.swap23Character.pZ = χ.pY := by
        unfold Character.pY Character.pZ; congr 2; apply congrArg χ.value; funext x y z; simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]
      simp only [Character.permutedCharacter, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      rw [show χ.cyclicCharacter.pX = χ.pZ from rfl, show χ.cyclicCharacter.cyclicCharacter.pX = χ.pY from rfl,
        hx, show χ.swap23Character.cyclicCharacter.pX = χ.swap23Character.pZ from rfl,
        hz, show χ.swap23Character.cyclicCharacter.cyclicCharacter.pX = χ.swap23Character.pY from rfl, hy]
      dsimp [t]; ring
    let P (a b : ℕ) : ℝ := χ.sixfoldProduct (convolution a b) ^ (1 / (6 * t))
    have h1 (a : ℕ) (ha : 1 ≤ a) : 1 ≤ P a a :=
      Real.one_le_rpow (by simpa [Character.sixfoldProduct] using Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ =>
        (χ.permutedCharacter i).one_le_value_of_coefficient_one ⟨⟨0, ha⟩, ⟨0, ha⟩, ⟨0, by omega⟩, rfl⟩) (by positivity)
    have hsym (a b : ℕ) : P a b = P b a := congrArg (· ^ (1 / (6 * t))) <| by
      let e : Fin (a + b - 1) ≃ Fin (b + a - 1) := finCongr (by omega)
      have heq : Tensor.pullback (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e (convolution b a) =
          fun j i k => convolution a b i j k := by funext j i k; simp [Tensor.pullback, e, convolution, Nat.add_comm]
      have h : χ.sixfoldProduct (Tensor.pullback (Equiv.refl _) (Equiv.refl _) e (convolution b a)) = χ.sixfoldProduct (convolution b a) :=
        Finset.prod_congr rfl fun i _ => (χ.permutedCharacter i).value_reindex _ _ _ _
      rw [heq] at h; rw [← h]; generalize convolution a b = T
      simp only [Character.sixfoldProduct, Fin.prod_univ_succ, Fin.prod_univ_zero]
      dsimp [Character.permutedCharacter, Character.cyclicCharacter, Character.swap23Character]; ac_rfl
    have hconc (d e : ℕ) : P (d + 1) e + P (d + 1) (e + 2) ≤ 2 * P (d + 1) (e + 1) := by
      have hsub := symmetrized_sharedFirst_subadditive χ hσ hsum_pX (detBranch d e)
      have hb0 (i) := (det_branch_bounds (χ.permutedCharacter i) d e).1
      have hb1 (i) := (det_branch_bounds (χ.permutedCharacter i) d e).2.1
      have hbs (i) := (det_branch_bounds (χ.permutedCharacter i) d e).2.2
      simp only [Character.sixfoldProduct, Fin.sum_univ_two, hb0, hb1] at hsub
      have hpr := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => (χ.permutedCharacter i).nonneg _) fun i _ => hbs i
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos zero_lt_two _ Finset.univ, hsum_pX] at hpr
      have hup : χ.sixfoldProduct (sharedFirstTensor (detBranch d e)) ^ (1 / (6 * t)) ≤ 2 * P (d + 1) (e + 1) :=
        (Real.rpow_le_rpow (χ.sixfoldProduct_nonneg _) hpr (by positivity)).trans_eq <| by
          change ((2 : ℝ) ^ (6 * t) * χ.sixfoldProduct (convolution (d + 1) (e + 1))) ^ (1 / (6 * t)) = _
          rw [Real.mul_rpow (by positivity) (χ.sixfoldProduct_nonneg _), ← Real.rpow_mul zero_le_two,
            mul_one_div_cancel hσ.ne', Real.rpow_one]
      dsimp only [P, Character.sixfoldProduct] at hup ⊢
      linarith [hsub.trans hup]
    have htrip {a : ℕ} (ha : 1 ≤ a) : 3 * P a a ≤ P a (4 * a - 1) := by
      have hsub := symmetrized_sharedFirst_subadditive χ hσ hsum_pX (secBranch a)
      have hs0 (i) := (sec_branch_bounds (χ.permutedCharacter i) a ha).1
      have hs1 (i) := (sec_branch_bounds (χ.permutedCharacter i) a ha).2.1
      have hs2 (i) := (sec_branch_bounds (χ.permutedCharacter i) a ha).2.2.1
      have hss (i) := (sec_branch_bounds (χ.permutedCharacter i) a ha).2.2.2
      simp only [Character.sixfoldProduct, Fin.sum_univ_three, hs0, hs1, hs2] at hsub
      have hsw : χ.sixfoldProduct (fun u s r => convolution a a u r s) = χ.sixfoldProduct (convolution a a) := by
        simp only [Character.sixfoldProduct, Fin.prod_univ_succ, Fin.prod_univ_zero]
        dsimp [Character.permutedCharacter, Character.cyclicCharacter, Character.swap23Character]
        unfold Tensor.cyclic; dsimp only
        rw [show (fun x z y => convolution a a x z y) = convolution a a from rfl]; ac_rfl
      change P a a + χ.sixfoldProduct (fun u s r => convolution a a u r s) ^ (1 / (6 * t)) + P a a ≤ _ at hsub
      rw [hsw] at hsub
      have hup : χ.sixfoldProduct (sharedFirstTensor (secBranch a)) ^ (1 / (6 * t)) ≤ P a (4 * a - 1) :=
        Real.rpow_le_rpow (χ.sixfoldProduct_nonneg _)
          (Finset.prod_le_prod₀ (fun i _ => (χ.permutedCharacter i).nonneg _) fun i _ => hss i) (by positivity)
      linarith [hsub.trans hup]
    let g (a : ℕ) : ℝ := P a (a + 1) - P a a
    have hdiag_inc {a : ℕ} (ha : 1 ≤ a) : P a a + g a + g (a + 1) ≤ P (a + 1) (a + 1) := by
      dsimp [g]; linarith [hconc a a, hsym a (a + 1)]
    have hdiag_up {a : ℕ} (ha : 1 ≤ a) : P a a ≤ ((3 * (a : ℝ) - 1) / 2) * g a := by
      obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
      have hd_anti : Antitone fun k => P (d + 1) (d + 1 + k + 1) - P (d + 1) (d + 1 + k) :=
        antitone_nat_of_succ_le fun k => by have := hconc d (d + 1 + k); rw [← Nat.add_assoc]; linarith
      have htan (k : ℕ) : P (d + 1) (d + 1 + k) ≤ P (d + 1) (d + 1) + (k : ℝ) * g (d + 1) := by
        induction k with
        | zero => simp
        | succ k ih =>
          have hstep : P (d + 1) (d + 1 + k + 1) - P (d + 1) (d + 1 + k) ≤ g (d + 1) := by simpa [g] using hd_anti (Nat.zero_le k)
          rw [← Nat.add_assoc]; push_cast; linarith
      have htr := (htrip ha).trans (by simpa [show d + 1 + (3 * (d + 1) - 1) = 4 * (d + 1) - 1 by omega,
        (Nat.cast_sub (by omega : 1 ≤ 3 * (d + 1)))] using htan (3 * (d + 1) - 1))
      push_cast; linarith
    let r (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (1 / 3 : ℝ)
    have hr3 (n : ℕ) : r n ^ 3 = (n : ℝ) + 1 := by dsimp [r]; rw [← Real.rpow_mul_natCast (by positivity)]; norm_num
    have hr_ind (n : ℕ) : r n ≤ g (n + 1) ∧ ((3 * ((n : ℝ) + 1) - 1) / 2) * r n ≤ P (n + 1) (n + 1) := by
      induction n with
      | zero =>
        have hP1 := h1 1 le_rfl; have hup := hdiag_up (a := 1) le_rfl
        dsimp [r]; norm_num at hup ⊢; exact ⟨by linarith, hP1⟩
      | succ n ih =>
        rcases ih with ⟨hg_n, hP_n⟩
        let x : ℝ := (n : ℝ) + 1
        have hx : 0 < x := by positivity
        have hup := hdiag_up (a := n + 2) (by omega)
        have hinc := hdiag_inc (a := n + 1) (by omega)
        rw [show ((n + 2 : ℕ) : ℝ) = x + 1 by dsimp [x]; push_cast; ring] at hup
        have hnext : r n * (1 + 1 / (3 * x)) ≤ g (n + 2) := by
          rw [show r n * (1 + 1 / (3 * x)) = (3 * x + 1) * r n / (3 * x) by field_simp]
          exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
        have hr_step : r (n + 1) ≤ r n * (1 + 1 / (3 * x)) := by
          refine le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity) ?_
          rw [hr3 (n + 1), mul_pow, hr3 n]
          have hfac : 1 + 1 / x ≤ (1 + 1 / (3 * x)) ^ 3 := by
            rw [show 1 / x = 3 * (1 / (3 * x)) by field_simp]
            nlinarith [sq_nonneg (1 / (3 * x)), mul_nonneg (sq_nonneg (1 / (3 * x))) (by positivity : 0 ≤ 1 / (3 * x))]
          have hx1 : x * (1 + 1 / x) = ((n + 1 : ℕ) : ℝ) + 1 := by dsimp [x]; push_cast; field_simp
          linarith [mul_le_mul_of_nonneg_left hfac hx.le]
        refine ⟨hr_step.trans hnext, ?_⟩
        have h1' : (3 * x / 2) * r (n + 1) ≤ ((3 * x + 1) / 2) * r n :=
          (mul_le_mul_of_nonneg_left hr_step (by positivity)).trans_eq (by field_simp)
        have h3 : ((3 * (((n + 1 : ℕ) : ℝ) + 1) - 1) / 2) * r (n + 1) = (3 * x / 2) * r (n + 1) + r (n + 1) := by
          dsimp [x]; push_cast; ring
        linarith [hr_step.trans hnext]
    have hpow4 (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ (4 : ℝ) ≤ (2 : ℝ) ^ ((1 / t) * 3) * (n : ℝ) ^ ((1 / t) * 3) := by
      cases n with
      | zero => omega
      | succ m =>
        have hconv (ψ : Character) : ψ.value (convolution (m + 1) (m + 1)) ≤ ((2 * (m + 1) : ℕ) : ℝ) := by
          let L := 2 * m + 1
          have hbnd := cyc_coprime_bound ψ (unitTensor (K := ℤ)) (convolution (m + 1) (m + 1)) L (by omega) fun M hM => by
            let : NeZero M := ⟨by omega⟩
            let ζ := AdjoinRoot.root (Polynomial.cyclotomic M ℤ)
            refine ⟨0, 0, 0, ⟨{
              leftMap := fun i q => Polynomial.C (ζ ^ (q.1.val * i.val))
              middleMap := fun j q => Polynomial.C (ζ ^ (q.1.val * j.val))
              rightMap := fun k q => Polynomial.C (ζ ^ (q.1.val * (M - k.val)))
              left_degree := fun _ _ => Polynomial.degree_C_le
              middle_degree := fun _ _ => Polynomial.degree_C_le
              vanishes := fun _ _ _ _ hj => (Nat.not_lt_zero _ hj).elim
              leading := fun i j k => ?_ }⟩⟩
            simp only [Tensor.restrict, Polynomial.finsetSum_coeff, ← Polynomial.C_mul, Polynomial.coeff_C_zero,
              Tensor.directSum, unitTensor, Fintype.sum_prod_type, Fintype.sum_unique, ite_and,
              apply_ite (algebraMap ℤ (CycAlg M)), map_one, map_zero, mul_ite, mul_one, mul_zero,
              Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
            rw [show (∑ r : Fin M, ζ ^ (r.val * i.val) * ζ ^ (r.val * j.val) * ζ ^ (r.val * (M - k.val))) =
                ∑ r : Fin M, ζ ^ (r.val * (i.val + j.val + (M - k.val))) from
              Finset.sum_congr rfl fun r _ => by rw [← pow_add, ← pow_add]; congr 1; ring,
              sum_root_pow (cycRoot_prim M) (by have := k.isLt; omega) (by have := i.isLt; have := j.isLt; omega)]
            have hiff : (i.val + j.val + (M - k.val) = M) ↔ (i.val + j.val = k.val) := by have := k.isLt; omega
            split_ifs <;> simp_all [convolution]
          rwa [ψ.map_one, mul_one, show (L + 1 : ℝ) = ((2 * (m + 1) : ℕ) : ℝ) by exact_mod_cast (by omega : L + 1 = 2 * (m + 1))] at hbnd
        have hpr : χ.sixfoldProduct (convolution (m + 1) (m + 1)) ≤ ((2 * (m + 1) : ℕ) : ℝ) ^ 6 :=
          (Finset.prod_le_prod₀ (fun i _ => (χ.permutedCharacter i).nonneg _) fun i _ => hconv _).trans_eq (by simp)
        have hup_m : P (m + 1) (m + 1) ≤ (2 * ((m + 1 : ℕ) : ℝ)) ^ (1 / t) :=
          (Real.rpow_le_rpow (χ.sixfoldProduct_nonneg _) hpr (by positivity)).trans_eq <| by
            rw [← Real.rpow_natCast_mul (by positivity), Nat.cast_mul, Nat.cast_ofNat]; congr 1; field_simp; norm_num
        have hlin : ((m : ℝ) + 1) * r m ≤ P (m + 1) (m + 1) :=
          (mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by dsimp [r]; positivity)).trans (hr_ind m).2
        calc ((m + 1 : ℕ) : ℝ) ^ (4 : ℝ) = (((m : ℝ) + 1) * r m) ^ 3 := by
                rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast, mul_pow, hr3 m]; push_cast; ring
          _ ≤ P (m + 1) (m + 1) ^ 3 := pow_le_pow_left₀ (by dsimp [r]; positivity) hlin 3
          _ ≤ ((2 * ((m + 1 : ℕ) : ℝ)) ^ (1 / t)) ^ 3 := pow_le_pow_left₀ (by linarith [h1 _ hn]) hup_m 3
          _ = (2 : ℝ) ^ ((1 / t) * 3) * ((m + 1 : ℕ) : ℝ) ^ ((1 / t) * 3) := by
              rw [← Real.rpow_mul_natCast (by positivity), Nat.cast_ofNat, Real.mul_rpow zero_le_two (by positivity)]
    have hcmp := mul_le_mul_of_nonneg_right (rpow_exponent_le_of_nat_bound (by positivity) fun k _ => hpow4 (2 ^ k) Nat.one_le_two_pow) ht.le
    rw [show (1 / t) * 3 * t = 3 by field_simp] at hcmp
    linarith
  · linarith

/-! ### Arithmetic Circuits over All Rings & Main Theorems -/

theorem exists_int_scheme_nine_quarters {ε : ℝ} (hε : 0 < ε) :
    ∃ n r : ℕ, 2 ≤ n ∧ (r : ℝ) ≤ (n : ℝ) ^ ((9 : ℝ) / 4 + ε) ∧
      Tensor.RankAtMost (Tensor.matrixCoefficients (Fin n) (Fin n) (Fin n)) r := by
  have hν : exactRankExponent ≤ (9 : ℝ) / 4 := by
    refine rpow_exponent_le_of_nat_bound zero_lt_two fun q hq => ?_
    let d := 2 ^ q
    have hd2 : 2 ≤ d := Nat.le_self_pow (by omega) 2
    have hx : 0 < (d : ℝ) ^ exactRankExponent := by dsimp [d]; positivity
    have hc : 1 ≤ ⌈(d : ℝ) ^ exactRankExponent⌉₊ := Nat.one_le_ceil_iff.2 hx
    let k := ⌈(d : ℝ) ^ exactRankExponent⌉₊ - 1
    obtain ⟨χ, hχ⟩ := exists_detecting_character hd2 (((Nat.ceil_eq_iff (by omega)).1 rfl).1)
    have hk_le : (d : ℝ) ^ exactRankExponent - 1 ≤ (k : ℝ) := by
      dsimp [k]; rw [Nat.cast_sub hc, Nat.cast_one]; linarith [Nat.le_ceil ((d : ℝ) ^ exactRankExponent)]
    have hbnd : χ.value (matrixMultiplicationTensor d d d) ≤ (d : ℝ) ^ ((9 : ℝ) / 4) := by
      rw [χ.value_matrixMultiplication (by omega)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ d)) (exponent_sum_le_nine_quarters χ)
    linarith [hk_le.trans (hχ.trans hbnd), Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ d) : (1 : ℝ) ≤ d) (by norm_num : (0 : ℝ) ≤ 9 / 4)]
  obtain ⟨n, hn, hR⟩ := exists_exactMatrixRank_lt_rpow (lt_add_of_pos_right exactRankExponent hε)
  exact ⟨n, exactMatrixRank n, hn,
    hR.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)), exactMatrixRank_spec n⟩

namespace Arithmetic

def regCost {F Input : Type*} : {r : ℕ} → Program F Input r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases g.cost (regCost p)

theorem admissibleExponent_two_le {F : Type u} [Ring F] [Nontrivial F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ := by
  classical
  have hsum {I : Type} {r : ℕ} (p : Program F I r) : ∑ i, regCost p i = p.cost := by
    induction p with
    | nil => rfl
    | step p g ih => simp [regCost, Program.cost, Fin.sum_univ_succ, ih, Nat.add_comm]
  have hz0 {I : Type} {r : ℕ} (p : Program F I r) : ∀ (i : Fin r), regCost p i = 0 →
      (∃ z : F, ∀ inp, p.eval inp i = z) ∨ (∃ a : I, ∀ inp, p.eval inp i = inp a) := by
    induction p with
    | nil => intro i; exact Fin.elim0 i
    | step p g ih =>
      refine Fin.cases (fun hi => ?_) ih
      cases g <;> simp [regCost, Gate.cost] at hi
      · exact .inl ⟨_, fun _ => rfl⟩
      · exact .inr ⟨_, fun _ => rfl⟩
  have hout_le {n : ℕ} (hn : 1 ≤ n) (P : MatrixAlgorithm F n n n) (hP : P.Correct) :
      n * n ≤ P.cost := by
    let j0 : Fin n := ⟨0, by omega⟩
    let eL (i : Fin n) : Matrix (Fin n) (Fin n) F := fun x y => if x = i then if y = j0 then 1 else 0 else 0
    let eR (k : Fin n) : Matrix (Fin n) (Fin n) F := fun y z => if z = k then if y = j0 then 1 else 0 else 0
    have heProd (i x k z : Fin n) : (eL i * eR k) x z = if (x, z) = (i, k) then 1 else 0 := by
      change (∑ y, eL i x y * eR k y z) = _
      by_cases hi : x = i <;> by_cases hk : z = k <;> simp [eL, eR, hi, hk]
    let outF : Fin n × Fin n → Fin P.registers := fun o => P.output o.1 o.2
    have hinj : Function.Injective outF := fun x y hxy => by
      have hx := congrFun (congrFun (hP (eL x.1) (eR x.2)) x.1) x.2
      have hy := congrFun (congrFun (hP (eL x.1) (eR x.2)) y.1) y.2
      have heq := hx.symm.trans ((congrArg (P.program.eval _) hxy).trans hy)
      by_contra hne; simp [heProd, Ne.symm hne] at heq
    have h1 (o : Fin n × Fin n) : 1 ≤ regCost P.program (outF o) := by
      by_contra h0
      have hent (A B : Matrix (Fin n) (Fin n) F) :
          P.program.eval (matrixInputs A B) (outF o) = (A * B) o.1 o.2 :=
        congrFun (congrFun (hP A B) o.1) o.2
      rcases hz0 P.program (outF o) (by omega) with ⟨z, hz⟩ | ⟨u, hu⟩
      · have hz0' : z = 0 := by simpa [hz] using hent 0 0
        have hz1 : z = 1 := by simpa [hz, heProd] using hent (eL o.1) (eR o.2)
        exact zero_ne_one (hz0'.symm.trans hz1)
      · rcases u with ⟨x, y⟩ | ⟨y, z⟩
        · have h := hent (Matrix.of fun _ _ => 1) 0; simp [hu, matrixInputs, Matrix.mul_apply] at h
        · have h := hent 0 (Matrix.of fun _ _ => 1); simp [hu, matrixInputs, Matrix.mul_apply] at h
    calc n * n = ∑ _ : Fin n × Fin n, 1 := by simp
      _ ≤ ∑ o : Fin n × Fin n, regCost P.program (outF o) := Finset.sum_le_sum fun o _ => h1 o
      _ = ∑ r ∈ Finset.univ.image outF, regCost P.program r :=
          (Finset.sum_image fun _ _ _ _ h => hinj h).symm
      _ ≤ ∑ r, regCost P.program r := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = P.cost := hsum P.program
  by_contra! hlt
  let ε := (2 - τ) / 2
  obtain ⟨C, hC, hbound⟩ := hτ ε (by dsimp [ε]; linarith)
  have hle : (2 : ℝ) ≤ τ + ε := rpow_exponent_le_of_nat_bound hC fun k _ => by
    obtain ⟨P, hP, hcost⟩ := hbound (2 ^ k) Nat.one_le_two_pow
    have hlow : ((2 ^ k : ℕ) : ℝ) ^ (2 : ℝ) ≤ P.cost := by
      rw [Real.rpow_two]; exact_mod_cast (by simpa [sq] using hout_le Nat.one_le_two_pow P hP : (2 ^ k) ^ 2 ≤ P.cost)
    exact hlow.trans hcost
  dsimp [ε] at hle; linarith

section BlockAndGrowth
variable {F : Type u} [Ring F]

structure Fam (F I O : Type*) where
  reg : ℕ
  prog : Program F I reg
  out : O → Fin reg

def Fam.eval {I O : Type*} (p : Fam F I O) (inp : I → F) (o : O) : F :=
  p.prog.eval inp (p.out o)

def wVal {I : Type*} {r : ℕ} (p : Program F I r) (inp : I → F) : Fin r ⊕ I ⊕ F → F
  | .inl i => p.eval inp i
  | .inr (.inl j) => inp j
  | .inr (.inr z) => z

def Fam.stepGate {I : Type*} {r s : ℕ} (a : Fam F I (Fin r ⊕ Fin s)) (h : Gate F I (Fin a.reg)) :
    Fam F I (Fin r ⊕ Fin (s + 1)) :=
  ⟨a.reg + 1, a.prog.step h, Sum.elim (fun i => (a.out (.inl i)).succ) (Fin.cases 0 fun j => (a.out (.inr j)).succ)⟩

def substProg {I M : Type*} {r : ℕ} (p : Program F I r) (w : M → Fin r ⊕ I ⊕ F) :
    {s : ℕ} → Program F M s → Fam F I (Fin r ⊕ Fin s)
  | 0, .nil => ⟨r, p, Sum.elim id Fin.elim0⟩
  | _ + 1, .step q g =>
    let a := substProg p w q
    match g with
    | .input m => match w m with
      | .inl i => ⟨a.reg, a.prog, Sum.elim (a.out ∘ .inl) (Fin.cases (a.out (.inl i)) (a.out ∘ .inr))⟩
      | .inr (.inl j) => a.stepGate (.input j)
      | .inr (.inr z) => a.stepGate (.constant z)
    | .constant z => a.stepGate (.constant z)
    | .add i j => a.stepGate (.add (a.out (.inr i)) (a.out (.inr j)))
    | .sub i j => a.stepGate (.sub (a.out (.inr i)) (a.out (.inr j)))
    | .mul i j => a.stepGate (.mul (a.out (.inr i)) (a.out (.inr j)))

theorem substProg_spec {I M : Type*} {r s : ℕ} (p : Program F I r) (w : M → Fin r ⊕ I ⊕ F) (q : Program F M s) :
    (∀ inp i, (substProg p w q).eval inp (.inl i) = p.eval inp i) ∧
    (∀ inp j, (substProg p w q).eval inp (.inr j) = q.eval (fun m => wVal p inp (w m)) j) ∧
    (substProg p w q).prog.cost = p.cost + q.cost := by
  induction q with
  | nil => exact ⟨fun _ _ => rfl, fun _ j => Fin.elim0 j, by simp [substProg, Program.cost]⟩
  | step q g ih =>
    rcases ih with ⟨ho, hn, hc⟩
    have hstep (h : Gate F I (Fin (substProg p w q).reg))
        (hev : ∀ inp, h.eval inp ((substProg p w q).prog.eval inp) =
          g.eval (fun m => wVal p inp (w m)) (q.eval (fun m => wVal p inp (w m))))
        (hcs : h.cost = g.cost) :
        (∀ inp i, ((substProg p w q).stepGate h).eval inp (.inl i) = p.eval inp i) ∧
        (∀ inp j, ((substProg p w q).stepGate h).eval inp (.inr j) = (q.step g).eval (fun m => wVal p inp (w m)) j) ∧
        ((substProg p w q).stepGate h).prog.cost = p.cost + (q.step g).cost :=
      ⟨fun inp k => ho inp k, fun inp => Fin.cases (hev inp) (hn inp), by simp [Fam.stepGate, Program.cost, hc, hcs, Nat.add_assoc]⟩
    rcases g with z | m | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
    · exact hstep _ (fun _ => rfl) rfl
    · cases hw : w m with
      | inl i =>
        have heq : substProg p w (q.step (.input m)) =
            ⟨(substProg p w q).reg, (substProg p w q).prog,
              Sum.elim ((substProg p w q).out ∘ .inl) (Fin.cases ((substProg p w q).out (.inl i)) ((substProg p w q).out ∘ .inr))⟩ := by
          simp [substProg, hw]
        rw [heq]
        exact ⟨ho, fun inp => Fin.cases (by simp [Fam.eval, Program.eval, Gate.eval, wVal, hw, ← ho inp i]) (hn inp),
          by simpa [Program.cost, Gate.cost] using hc⟩
      | inr x =>
        rcases x with j | z
        · rw [show substProg p w (q.step (.input m)) = (substProg p w q).stepGate (.input j) by simp [substProg, hw]]
          exact hstep (.input j) (fun _ => by simp [Gate.eval, wVal, hw]) rfl
        · rw [show substProg p w (q.step (.input m)) = (substProg p w q).stepGate (.constant z) by simp [substProg, hw]]
          exact hstep (.constant z) (fun _ => by simp [Gate.eval, wVal, hw]) rfl
    · exact hstep _ (fun inp => by change (substProg p w q).eval _ _ + (substProg p w q).eval _ _ = _; rw [hn, hn]; rfl) rfl
    · exact hstep _ (fun inp => by change (substProg p w q).eval _ _ - (substProg p w q).eval _ _ = _; rw [hn, hn]; rfl) rfl
    · exact hstep _ (fun inp => by change (substProg p w q).eval _ _ * (substProg p w q).eval _ _ = _; rw [hn, hn]; rfl) rfl

theorem exists_pad {n m : ℕ} (h : n ≤ m) (P : MatrixAlgorithm F m m m) (hP : P.Correct) :
    ∃ Q : MatrixAlgorithm F n n n, Q.Correct ∧ Q.cost ≤ P.cost := by
  let zPad (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin m) (Fin m) F :=
    fun i j => if hi : i.val < n then if hj : j.val < n then M ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0
  let chk (u v : Fin m) (mk : Fin n × Fin n → MatrixInput n n n) : Fin 0 ⊕ MatrixInput n n n ⊕ F :=
    if hu : u.val < n then if hv : v.val < n then .inr (.inl (mk (⟨u.val, hu⟩, ⟨v.val, hv⟩))) else .inr (.inr 0) else .inr (.inr 0)
  let src : MatrixInput m m m → Fin 0 ⊕ MatrixInput n n n ⊕ F
    | .inl (i, j) => chk i j .inl
    | .inr (j, k) => chk j k .inr
  let a := substProg .nil src P.program
  have ⟨_, hn, hc⟩ := substProg_spec .nil src P.program
  refine ⟨⟨a.reg, a.prog, fun i k => a.out (.inr (P.output (Fin.castLE h i) (Fin.castLE h k)))⟩,
    fun M N => funext fun i => funext fun k => ?_, by simpa [MatrixAlgorithm.cost, Program.cost] using hc.le⟩
  change a.eval (matrixInputs M N) (.inr _) = (M * N) i k
  rw [hn]
  have hsrc : (fun j => wVal .nil (matrixInputs M N) (src j)) = matrixInputs (zPad M) (zPad N) := by
    funext x; rcases x with ⟨u, v⟩ | ⟨u, v⟩ <;>
      (by_cases h1 : u.val < n <;> by_cases h2 : v.val < n <;> simp [wVal, src, chk, matrixInputs, zPad, h1, h2])
  rw [hsrc, show P.program.eval (matrixInputs (zPad M) (zPad N)) _ = (zPad M * zPad N) (Fin.castLE h i) (Fin.castLE h k) from
    congrFun (congrFun (hP (zPad M) (zPad N)) _) _, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _
    (fun j hj => ?_) (fun j => by simp [zPad, i.is_lt, j.is_lt, k.is_lt])
  simp [zPad, not_lt_of_ge (le_of_not_gt fun hlt => hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩)]

def Fam.comp {I M O : Type*} (p : Fam F I M) (q : Fam F M O) : Fam F I O :=
  let a := substProg p.prog (fun m => .inl (p.out m)) q.prog
  ⟨a.reg, a.prog, fun o => a.out (.inr (q.out o))⟩

theorem Fam.eval_comp {I M O : Type*} (p : Fam F I M) (q : Fam F M O) (inp : I → F) (o : O) :
    (p.comp q).eval inp o = q.eval (p.eval inp) o :=
  (substProg_spec p.prog (fun m => .inl (p.out m)) q.prog).2.1 inp (q.out o)

def Fam.all {I O : Type*} : (r : ℕ) → (Fin r → Fam F I O) → Fam F I (Fin r × O)
  | 0, _ => ⟨0, .nil, fun o => Fin.elim0 o.1⟩
  | r + 1, f =>
    let tl := Fam.all r fun i => f i.succ
    let a := substProg tl.prog (.inr ∘ .inl) (f 0).prog
    ⟨a.reg, a.prog, fun o => Fin.cases (a.out (.inr ((f 0).out o.2))) (fun i => a.out (.inl (tl.out (i, o.2)))) o.1⟩

theorem Fam.eval_all {I O : Type*} (r : ℕ) (f : Fin r → Fam F I O) (inp : I → F) (o : Fin r × O) :
    (Fam.all r f).eval inp o = (f o.1).eval inp o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    have sp := substProg_spec (Fam.all r fun j => f j.succ).prog (.inr ∘ .inl) (f 0).prog
    exact Fin.cases (sp.2.1 inp ((f 0).out o)) (fun j => (sp.1 inp _).trans (ih _ (j, o))) i

theorem Fam.cost_all {I O : Type*} (r : ℕ) (f : Fin r → Fam F I O) :
    (Fam.all r f).prog.cost = ∑ i, (f i).prog.cost := by
  induction r with
  | zero => simp [Fam.all, Program.cost]
  | succ r ih => dsimp [Fam.all]; rw [(substProg_spec _ _ _).2.2, ih, Fin.sum_univ_succ, Nat.add_comm]

def linFin {I : Type*} : (k : ℕ) → (Fin k → F) → (Fin k → I) → Fam F I Unit
  | 0, _, _ => ⟨1, Program.nil.step (.constant 0), fun _ => 0⟩
  | k + 1, a, w =>
    let tl := linFin k (fun i => a i.succ) (fun i => w i.succ)
    ⟨tl.reg + 4,
      (((tl.prog.step (.constant (a 0))).step (.input (w 0))).step (.mul 1 0)).step
        (.add 0 (tl.out ()).succ.succ.succ),
      fun _ => 0⟩

def Fam.linMap {I O T : Type*} [Fintype O] [Fintype T]
    (a : O → T → F) (w : O → T → I) : Fam F I O :=
  let eO := Fintype.equivFin O; let eT := Fintype.equivFin T
  let p := Fam.all (Fintype.card O) fun i =>
    linFin (Fintype.card T) (fun j => a (eO.symm i) (eT.symm j)) (fun j => w (eO.symm i) (eT.symm j))
  ⟨p.reg, p.prog, fun o => p.out (eO o, ())⟩

theorem Fam.eval_linMap {I O T : Type*} [Fintype O] [Fintype T]
    (a : O → T → F) (w : O → T → I) (inp : I → F) (o : O) :
    (Fam.linMap a w).eval inp o = ∑ t, a o t * inp (w o t) := by
  have hev : ∀ (k : ℕ) (c : Fin k → F) (v : Fin k → I), (linFin k c v).eval inp () = ∑ i, c i * inp (v i) := by
    intro k; induction k with
    | zero => simp [linFin, Fam.eval, Program.eval, Gate.eval]
    | succ k ih => intro c v; simp only [Fin.sum_univ_succ, ← ih]; rfl
  change (Fam.all _ _).eval inp ((Fintype.equivFin O) o, ()) = _
  rw [Fam.eval_all, hev, Equiv.symm_apply_apply]
  exact (Fintype.equivFin T).symm.sum_comp fun t => a o t * inp (w o t)

theorem Fam.cost_linMap {I O T : Type*} [Fintype O] [Fintype T]
    (a : O → T → F) (w : O → T → I) :
    (Fam.linMap a w).prog.cost = 2 * Fintype.card O * Fintype.card T := by
  have hc : ∀ (k : ℕ) (c : Fin k → F) (v : Fin k → I), (linFin k c v).prog.cost = 2 * k := by
    intro k; induction k with
    | zero => intro _ _; rfl
    | succ k ih => intro c v; simp [linFin, Program.cost, Gate.cost, ih]; omega
  simp [Fam.linMap, Fam.cost_all, hc]; ring

theorem int_rank_block_step {n r m : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (Fin n) (Fin n) (Fin n)) r)
    (p : MatrixAlgorithm F m m m) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm F (n * m) (n * m) (n * m), q.Correct ∧
      q.cost ≤ r * p.cost + 6 * r * n ^ 2 * m ^ 2 := by
  rcases h with ⟨a, b, c, h⟩
  let join (i : Fin n) (j : Fin m) : Fin (n * m) := finProdFinEquiv (i, j)
  let inA (q : Fin r) (u : MatrixInput m m m) (x : Fin n × Fin n) : F :=
    match u with | .inl _ => a q x | .inr _ => b q x
  let inW (u : MatrixInput m m m) (x : Fin n × Fin n) : MatrixInput (n * m) (n * m) (n * m) :=
    match u with
    | .inl (s, t) => .inl (join x.1 s, join x.2 t)
    | .inr (t, u) => .inr (join x.1 t, join x.2 u)
  let pFam : Fam F (MatrixInput m m m) (Fin m × Fin m) := ⟨p.registers, p.program, fun o => p.output o.1 o.2⟩
  let midF := Fam.all r fun q => (Fam.linMap (inA q) inW).comp pFam
  let outF := Fam.linMap
    (fun (o : Fin (n * m) × Fin (n * m)) (q : Fin r) =>
      (c q ((finProdFinEquiv.symm o.2).1, (finProdFinEquiv.symm o.1).1) : F))
    (fun o q => (q, ((finProdFinEquiv.symm o.1).2, (finProdFinEquiv.symm o.2).2)))
  let tot := midF.comp outF
  refine ⟨⟨tot.reg, tot.prog, fun i k => tot.out (i, k)⟩, fun A B => ?_, ?_⟩
  · funext i₀ k₀
    obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i₀
    obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k₀
    change tot.eval (matrixInputs A B) (join i s, join k u) = (A * B) (join i s) (join k u)
    rw [Fam.eval_comp, Fam.eval_linMap]
    simp only [join, Equiv.symm_apply_apply]
    have hmid (q : Fin r) : midF.eval (matrixInputs A B) (q, (s, u)) =
        ∑ t : Fin m, (∑ x : Fin n × Fin n, (a q x : F) * A (join x.1 s) (join x.2 t)) *
          (∑ y : Fin n × Fin n, (b q y : F) * B (join y.1 t) (join y.2 u)) := by
      rw [Fam.eval_all, Fam.eval_comp]
      let inFq := Fam.linMap (inA q) inW
      let L : Matrix (Fin m) (Fin m) F := fun s' t' => inFq.eval (matrixInputs A B) (.inl (s', t'))
      let R : Matrix (Fin m) (Fin m) F := fun t' u' => inFq.eval (matrixInputs A B) (.inr (t', u'))
      have hm : inFq.eval (matrixInputs A B) = matrixInputs L R := by funext x; cases x <;> rfl
      change p.program.eval (inFq.eval (matrixInputs A B)) (p.output s u) = _
      rw [hm, show p.program.eval (matrixInputs L R) (p.output s u) = (L * R) s u from congrFun (congrFun (hp L R) s) u,
        Matrix.mul_apply]
      exact Finset.sum_congr rfl fun t _ => by simp only [L, R, inFq, Fam.eval_linMap, inA, inW, matrixInputs]
    have hbil (lA rB : Fin n × Fin n → F) :
        (∑ q : Fin r, (c q (k, i) : F) * (∑ x, (a q x : F) * lA x) * (∑ y, (b q y : F) * rB y)) =
        ∑ j : Fin n, lA (i, j) * rB (j, k) := by
      have hcent (u' v' w' : ℤ) (x' y' : F) : (w' : F) * ((u' : F) * x') * ((v' : F) * y') = ((u' * v' * w' : ℤ) : F) * x' * y' := by
        simp only [Int.cast_mul, mul_assoc]
        rw [← mul_assoc x', ← Int.cast_comm v' x', mul_assoc, ← mul_assoc (w' : F), Int.cast_comm w',
          mul_assoc, ← mul_assoc (w' : F), Int.cast_comm w', mul_assoc]
      have hcf (x y : Fin n × Fin n) :
          (∑ q, ((a q x * b q y * c q (k, i) : ℤ) : F)) =
            ((Tensor.matrixCoefficients (Fin n) (Fin n) (Fin n) x y (k, i) : ℤ) : F) := by
        simpa using (congrArg (Int.cast (R := F)) (h x y (k, i))).symm
      simp only [Finset.sum_mul, Finset.mul_sum]
      calc (∑ q, ∑ y, ∑ x, (c q (k, i) : F) * ((a q x : F) * lA x) * ((b q y : F) * rB y))
          = ∑ x, ∑ y, (∑ q, ((a q x * b q y * c q (k, i) : ℤ) : F)) * lA x * rB y := by
              simp only [Finset.sum_mul]
              exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans <| Finset.sum_comm.trans <|
                Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <|
                  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => hcent _ _ _ _ _
        _ = ∑ j, lA (i, j) * rB (j, k) := by
              simp_rw [hcf]; simp [Tensor.matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_mul]
    have h1 : (∑ q, (c q (k, i) : F) * midF.eval (matrixInputs A B) (q, (s, u))) =
        ∑ t : Fin m, ∑ j : Fin n, A (join i s) (join j t) * B (join j t) (join k u) := by
      rw [show (∑ q, (c q (k, i) : F) * midF.eval (matrixInputs A B) (q, (s, u))) =
        ∑ q, ∑ t, (c q (k, i) : F) * ((∑ x, (a q x : F) * A (join x.1 s) (join x.2 t)) *
          ∑ y, (b q y : F) * B (join y.1 t) (join y.2 u)) from
        Finset.sum_congr rfl fun q _ => by rw [hmid, Finset.mul_sum], Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp_rw [← mul_assoc]
      exact hbil (fun x => A (join x.1 s) (join x.2 t)) (fun y => B (join y.1 t) (join y.2 u))
    rw [h1, Finset.sum_comm, Matrix.mul_apply]
    exact (Fintype.sum_prod_type _).symm.trans (finProdFinEquiv.sum_comp fun j => A (finProdFinEquiv (i, s)) j * B j (finProdFinEquiv (k, u)))
  · change tot.prog.cost ≤ r * p.program.cost + _
    have hcc {I M O : Type} (u : Fam F I M) (v : Fam F M O) : (u.comp v).prog.cost = u.prog.cost + v.prog.cost :=
      (substProg_spec _ _ _).2.2
    simp only [tot, midF, outF, pFam, hcc, Fam.cost_all, Fam.cost_linMap, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, smul_eq_mul]
    exact le_of_eq (by ring)

theorem admissibleExponent_nine_quarters (F : Type u) [Ring F] : AdmissibleExponent F ((9 : ℝ) / 4) := by
  intro ε hε
  obtain ⟨b, r, hb, hr, hR_scheme⟩ := exists_int_scheme_nine_quarters (half_pos hε)
  let s := (9 : ℝ) / 4 + ε
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hbpos : (0 : ℝ) < b := zero_lt_one.trans hb1
  let q := (b : ℝ) ^ s
  have hrate : (r : ℝ) < q := hr.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hb1 (by dsimp [s]; linarith))
  have hquad : ((b ^ 2 : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hb1.le (by dsimp [s]; linarith)
  let K := 6 * r * b ^ 2
  let recCost : ℕ → ℕ := Nat.rec 1 fun j c => r * c + K * (b ^ j) ^ 2
  have hpow_prog (k : ℕ) : ∃ P : MatrixAlgorithm F (b ^ k) (b ^ k) (b ^ k), P.Correct ∧ P.cost ≤ recCost k := by
    induction k with
    | zero =>
      change ∃ P : MatrixAlgorithm F 1 1 1, P.Correct ∧ P.cost ≤ 1
      exact ⟨⟨3, ((Program.nil.step (.input (.inl (0, 0)))).step (.input (.inr (0, 0)))).step (.mul 1 0), fun _ _ => 0⟩,
        fun A B => by
          funext i k; rw [Subsingleton.elim i 0, Subsingleton.elim k 0]
          change A 0 0 * B 0 0 = (A * B) 0 0; simp [Matrix.mul_apply], le_rfl⟩
    | succ k ih =>
      obtain ⟨P, hP, hPc⟩ := ih
      obtain ⟨Q, hQ, hQc⟩ := int_rank_block_step hR_scheme P hP
      have hbnd : Q.cost ≤ recCost (k + 1) := hQc.trans (by
        change _ ≤ r * recCost k + K * (b ^ k) ^ 2
        exact Nat.add_le_add_right (Nat.mul_le_mul_left r hPc) _)
      exact (pow_succ' b k).symm ▸ ⟨Q, hQ, hbnd⟩
  have hgap : 0 < q - r := sub_pos.2 hrate
  let C : ℝ := 1 + (K : ℝ) / (q - r)
  have hK0 : 0 ≤ (K : ℝ) / (q - r) := div_nonneg (Nat.cast_nonneg K) hgap.le
  have hCpos : 0 < C := by dsimp [C]; linarith
  have hrec_le (k : ℕ) : (Nat.cast (recCost k) : ℝ) ≤ C * q ^ k := by
    induction k with
    | zero => simp [recCost, C, hK0]
    | succ k ih =>
      change (Nat.cast (r * recCost k + K * (b ^ k) ^ 2) : ℝ) ≤ C * q ^ (k + 1)
      push_cast
      have hbk : ((b : ℝ) ^ k) ^ 2 ≤ q ^ k := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        exact pow_le_pow_left₀ (by positivity) (by simpa using hquad) k
      have hKq : (q - r) * ((K : ℝ) / (q - r)) = K := mul_div_cancel₀ _ hgap.ne'
      have hCq : (r : ℝ) * C + K ≤ C * q := by
        have : (K : ℝ) / (q - r) ≤ C := by dsimp [C]; linarith
        nlinarith [mul_le_mul_of_nonneg_left this hgap.le]
      calc (r : ℝ) * Nat.cast (recCost k) + K * ((b : ℝ) ^ k) ^ 2
          ≤ (r : ℝ) * (C * q ^ k) + K * q ^ k := add_le_add (mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg r))
              (mul_le_mul_of_nonneg_left hbk (Nat.cast_nonneg K))
        _ = ((r : ℝ) * C + K) * q ^ k := by ring
        _ ≤ (C * q) * q ^ k := mul_le_mul_of_nonneg_right hCq (by positivity)
        _ = C * q ^ (k + 1) := by rw [pow_succ]; ring
  refine ⟨C * q, mul_pos hCpos (Real.rpow_pos_of_pos hbpos s), fun n hn => ?_⟩
  let k := Nat.log b n + 1
  have hnk : n ≤ b ^ k := (Nat.lt_pow_succ_log_self (by omega) n).le
  have hkn : b ^ k ≤ b * n := by rw [pow_succ']; exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b (by omega))
  obtain ⟨P, hP, hPc⟩ := hpow_prog k
  obtain ⟨Q, hQ, hQP⟩ := exists_pad hnk P hP
  refine ⟨Q, hQ, ?_⟩
  calc (Q.cost : ℝ) ≤ Nat.cast (recCost k) := by exact_mod_cast hQP.trans hPc
    _ ≤ C * q ^ k := hrec_le k
    _ = C * ((b ^ k : ℕ) : ℝ) ^ s := by dsimp [q]; rw [Real.rpow_pow_comm hbpos.le, Nat.cast_pow]
    _ ≤ C * ((b : ℝ) * n) ^ s := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkn) hs) hCpos.le
    _ = (C * q) * (n : ℝ) ^ s := by dsimp [q]; rw [Real.mul_rpow hbpos.le (Nat.cast_nonneg n)]; ring

end BlockAndGrowth
end Arithmetic

end

end OAI.MatrixMultiplication
