module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

public section

@[expose] section

namespace OAI.MatrixMultiplication

noncomputable section

open Filter
open scoped BigOperators Topology Polynomial

namespace Foundation

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

variable {K X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [CommSemiring K]

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

theorem RankAtMost.scale {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (u : K) :
    RankAtMost (fun x y z => u * T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => u * a i x, b, c, by funext x y z; simp [rankOne, Finset.mul_sum, mul_assoc]⟩

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) :=
  ⟨fun i => a ((Fintype.equivFin ι).symm i),
    fun i => b ((Fintype.equivFin ι).symm i),
    fun i => c ((Fintype.equivFin ι).symm i),
    funext fun x => funext fun y => funext fun z =>
      ((Fintype.equivFin ι).symm.sum_comp (fun i => rankOne (a i) (b i) (c i) x y z)).symm⟩

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  let aa : (Fin r × Fin s) → (X × U) → K := fun i x => a i.1 x.1 * d i.2 x.2
  let bb : (Fin r × Fin s) → (Y × V) → K := fun i y => b i.1 y.1 * e i.2 y.2
  let cc : (Fin r × Fin s) → (Z × W) → K := fun i z => c i.1 z.1 * f i.2 z.2
  have heq : Tensor.product
      (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (fun u v w => ∑ j, rankOne (d j) (e j) (f j) u v w) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    simp only [Tensor.product, Fintype.sum_prod_type, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by dsimp [rankOne, aa, bb, cc]; ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  let aa : (Fin n → Fin r) → (Fin n → X) → K := fun f x => ∏ i, a (f i) (x i)
  let bb : (Fin n → Fin r) → (Fin n → Y) → K := fun f y => ∏ i, b (f i) (y i)
  let cc : (Fin n → Fin r) → (Fin n → Z) → K := fun f z => ∏ i, c (f i) (z i)
  have heq : Tensor.power (fun x y z => ∑ j, rankOne (a j) (b j) (c j) x y z) n =
      fun x y z => ∑ f, rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [Tensor.power, Fintype.prod_sum, rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

theorem sum_comm_three {ι : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype ι]
    (f : ι → X → Y → Z → K) :
    (∑ x, ∑ y, ∑ z, ∑ i, f i x y z) = ∑ i, ∑ x, ∑ y, ∑ z, f i x y z :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans <|
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

section Restrict
variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_rankOne (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (a : X → K) (b : Y → K) (c : Z → K) :
    restrict A B C (rankOne a b c) =
      rankOne (fun x' => ∑ x, A x' x * a x)
        (fun y' => ∑ y, B y' y * b y)
        (fun z' => ∑ z, C z' z * c z) := by
  funext x' y' z'
  simp only [restrict, rankOne]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => by ring

theorem restrict_sum {ι : Type*} [Fintype ι]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : ι → Tensor K X Y Z) :
    restrict A B C (fun x y z => ∑ i, T i x y z) =
      fun x' y' z' => ∑ i, restrict A B C (T i) x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  exact sum_comm_three _

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  rw [restrict_sum]
  funext x' y' z'
  exact Finset.sum_congr rfl fun i _ =>
    congrFun (congrFun (congrFun (restrict_rankOne A B C (a i) (b i) (c i)) x') y') z'

end Restrict

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by
  funext x y z; simp [pullback, restrict, ite_mul, mul_ite]

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y), fun i z => c i (fz z), rfl⟩

def dotPairing (U : Type*) [DecidableEq U] : Tensor K U U Unit :=
  fun i j _ => if i = j then 1 else 0

def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

theorem matrixCoefficients_product {A B C D E F : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (x : (A × D) × (B × E)) (y : (B × E) × (C × F)) (z : (C × F) × (A × D)) :
    product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)
      ((x.1.1, x.2.1), (x.1.2, x.2.2))
      ((y.1.1, y.2.1), (y.1.2, y.2.2))
      ((z.1.1, z.2.1), (z.1.2, z.2.2)) =
      matrixCoefficients (A × D) (B × E) (C × F) x y z := by
  simp only [product, matrixCoefficients, Prod.ext_iff]
  split_ifs <;> simp_all

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X :=
  fun y z x => T x y z

theorem cyclic_directSum {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    cyclic (directSum T) = directSum (fun i => cyclic (T i)) := by
  funext ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
  by_cases hij : i = j <;> by_cases hik : i = k <;> subst_vars <;>
    simp_all [cyclic, directSum, eq_comm]

def composeRestrictionMatrix [Fintype X']
    (D : X'' → X' → K) (A : X' → X → K) : X'' → X → K :=
  fun x'' x => ∑ x', D x'' x' * A x' x

theorem restrict_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : X'' → X' → K) (E : Y'' → Y' → K) (F : Z'' → Z' → K)
    (T : Tensor K X Y Z) :
    restrict D E F (restrict A B C T) =
      restrict (composeRestrictionMatrix D A) (composeRestrictionMatrix E B)
        (composeRestrictionMatrix F C) T := by
  funext x'' y'' z''
  unfold restrict composeRestrictionMatrix
  calc
    _ = ∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z,
        D x'' x' * E y'' y' * F z'' z' * (A x' x * B y' y * C z' z * T x y z) := by
      simp only [Finset.mul_sum]
    _ = ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z',
        D x'' x' * E y'' y' * F z'' z' * (A x' x * B y' y * C z' z * T x y z) := by
      simpa only [Fintype.sum_prod_type] using Finset.sum_comm
        (s := (Finset.univ : Finset (X' × Y' × Z'))) (t := (Finset.univ : Finset (X × Y × Z)))
        (f := fun p q => D x'' p.1 * E y'' p.2.1 * F z'' p.2.2 *
          (A p.1 q.1 * B p.2.1 q.2.1 * C p.2.2 q.2.2 * T q.1 q.2.1 q.2.2))
    _ = _ := Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun z _ => by
        rw [Finset.sum_mul_sum]
        simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ =>
          Finset.sum_congr rfl fun z' _ => by ring

theorem restrict_product {U V W U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : U' → U → K) (E : V' → V → K) (F : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    restrict (fun (x : X' × U') (u : X × U) => A x.1 u.1 * D x.2 u.2)
      (fun (y : Y' × V') (v : Y × V) => B y.1 v.1 * E y.2 v.2)
      (fun (z : Z' × W') (w : Z × W) => C z.1 w.1 * F z.2 w.2) (product T S) =
      product (restrict A B C T) (restrict D E F S) := by
  funext x' y' z'
  simp only [restrict, product, Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * D x'.2 u) * (B y'.1 y * E y'.2 v) *
          (C z'.1 z * F z'.2 w) * (T x y z * S u v w) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans <|
        Finset.sum_congr rfl fun _ _ =>
          (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * B y'.1 y * C z'.1 z * T x y z) *
          (D x'.2 u * E y'.2 v * F z'.2 w * S u v w) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by simp_rw [Finset.sum_mul, Finset.mul_sum]

theorem restrict_identity [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) :
    restrict (fun x' x => if x = x' then 1 else 0)
      (fun y' y => if y = y' then 1 else 0)
      (fun z' z => if z = z' then 1 else 0) T = T :=
  (pullback_eq_restrict id id id T).symm

theorem RankAtMost.card_le_of_identity [Nontrivial K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    exact (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm.trans (hidentity i j)
  have hinj : Function.Injective R.mulVecLin := fun v w hvw => by
    simpa only [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul,
      hmul, Matrix.mulVecLin_one, LinearMap.id_apply] using congrArg L.mulVecLin hvw
  simpa only [Fintype.card_fin] using card_le_of_injective K R.mulVecLin hinj

structure PolynomialRestrictionDegeneration
    {F : Type*} [CommRing F] [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor F X Y Z) (U : Tensor F X' Y' Z') (k Lx Ly Lz : ℕ) where
  leftMap : X' → X → Polynomial F
  middleMap : Y' → Y → Polynomial F
  rightMap : Z' → Z → Polynomial F
  left_degree : ∀ x' x, (leftMap x' x).degree ≤ Lx
  middle_degree : ∀ y' y, (middleMap y' y).degree ≤ Ly
  right_degree : ∀ z' z, (rightMap z' z).degree ≤ Lz
  vanishes : ∀ x' y' z' j, j < k →
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff j = 0
  leading : ∀ x' y' z',
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff k = U x' y' z'

def PolynomialRestrictionDegeneration.basePolynomial
    {F : Type*} [CommRing F] [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor F X Y Z} {U : Tensor F X' Y' Z'} {k Lx Ly Lz : ℕ}
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap (fun x y z => Polynomial.C (T x y z))

end Tensor
end Foundation

namespace AuxiliarySeparation

open Foundation

variable {K : Type*} [CommSemiring K]

def matrixMultiplicationTensor (a b c : ℕ) :
    Tensor K (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

def convolution (a b : ℕ) : Tensor K (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

def convolutionOutput {a b : ℕ} (i : Fin a) (j : Fin b) : Fin (a + b - 1) :=
  ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩

@[simp] theorem convolution_at_output {a b : ℕ} (i : Fin a) (j : Fin b) :
    convolution (K := K) a b i j (convolutionOutput i j) = 1 := by
  simp [convolution, convolutionOutput]

theorem convolution_comm (a b : ℕ) (i : Fin a) (j : Fin b)
    (k : Fin (a + b - 1)) :
    convolution (K := K) a b i j k =
      convolution (K := K) b a j i (Fin.cast (by omega) k) := by
  simp only [convolution, Fin.val_cast, Nat.add_comm]

theorem convolution_one_left_dotPairing (b : ℕ) :
    Tensor.pullback (Equiv.equivPUnit (Fin 1)).symm (Equiv.refl (Fin b))
      (finCongr (by omega) : Fin b ≃ Fin (1 + b - 1)) (convolution (K := K) 1 b) =
      Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin b))) := by
  funext i j k
  simp [Tensor.pullback, Tensor.cyclic, Tensor.dotPairing, convolution, Fin.ext_iff]

variable {M : ℕ} {X Y Z : Type*}

def sectorNumber (i : Fin M) : ℤ := (i.val : ℤ) + 1

theorem sectorNumber_bounds (i : Fin M) :
    1 ≤ sectorNumber i ∧ sectorNumber i ≤ M := by
  have := i.isLt; unfold sectorNumber; omega

theorem sectorNumber_injective : Function.Injective (@sectorNumber M) := fun _ _ hij => by
  apply Fin.ext; unfold sectorNumber at hij; omega

def sharedFirstTensor (B : Fin M → Tensor K X Y Z) :
    Tensor K X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

theorem restrict_constantCopies_delta
    {A B C A' B' C' R : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [DecidableEq R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : Tensor K A B C) (fa : A' → A) (fb : B' → B) (fc : C' → C)
    (a : A' → R → K) (b : B' → R → K) (c : C' → R → K)
    (x : A') (y : B') (z : C') :
    Tensor.restrict
        (fun x r => if r.2 = fa x then a x r.1 else 0)
        (fun y r => if r.2 = fb y then b y r.1 else 0)
        (fun z r => if r.2 = fc z then c z r.1 else 0)
        (Tensor.directSum (fun _ : R => T)) x y z =
      (∑ r : R, a x r * b y r * c z r) * T (fa x) (fb y) (fc z) := by
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, Finset.sum_mul]

def separationTarget (B : Fin M → Tensor K X Y Z) :
    Tensor K (X × Fin M) ((Fin M × Y) × Fin M) ((Fin M × Z) × Fin M) :=
  fun x y z => if x.2 = y.1.1 ∧ y.1.1 = z.1.1 ∧ y.2 = z.2 then
    B y.1.1 x.1 y.1.2 z.1.2 else 0

def separationFirstEquiv : (X × Fin M) ≃ (Fin M × (X × Unit)) :=
  (Equiv.prodComm X (Fin M)).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodPUnit X).symm)

def separationSideEquiv (A : Type*) : ((Fin M × A) × Fin M) ≃
    (Fin M × (A × Fin M)) := Equiv.prodAssoc _ _ _

theorem separationTarget_eq_directSum
    (B : Fin M → Tensor K X Y Z) :
    separationTarget B =
      Tensor.pullback
        separationFirstEquiv (separationSideEquiv Y) (separationSideEquiv Z)
        (Tensor.directSum (fun h => Tensor.product (B h)
          (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin M)))))) := by
  funext x y z
  simp only [separationTarget, Tensor.pullback, Tensor.directSum, Tensor.product,
    Tensor.cyclic, Tensor.dotPairing, separationFirstEquiv, separationSideEquiv,
    Equiv.trans_apply, Equiv.prodComm_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply]
  by_cases hxy : x.2 = y.1.1
  · by_cases hyz : y.1.1 = z.1.1 <;> simp [hxy, hyz]
  · simp [hxy]

theorem le_of_eventually_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ C * a ^ j) : b ≤ a := by
  by_contra hba
  have hab : a < b := lt_of_not_ge hba
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hlim : Tendsto (fun j : ℕ => C * (a / b) ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha hb.le)
      ((div_lt_one hb).2 hab)).const_mul C
  have hbound : ∀ᶠ j : ℕ in atTop, 1 ≤ C * (a / b) ^ j := by
    filter_upwards [h] with j hj
    simpa only [div_self (pow_ne_zero j hb.ne'), mul_div_assoc, div_pow] using
      (div_le_div_iff_of_pos_right (pow_pos hb j)).2 hj
  linarith [ge_of_tendsto hlim hbound]

theorem le_of_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ j : ℕ, b ^ j ≤ C * a ^ j) : b ≤ a :=
  le_of_eventually_pow_le_const_mul_pow ha (Eventually.of_forall h)

theorem rpow_exponent_le_of_nat_bound {a b C : ℝ}
    (hbound : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ^ a ≤ C * (n : ℝ) ^ b) :
    a ≤ b := by
  refine (Real.rpow_le_rpow_left_iff one_lt_two).mp
    (le_of_eventually_pow_le_const_mul_pow (C := C) (by positivity) ?_)
  filter_upwards [eventually_ge_atTop 1] with k hk
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_pow_comm zero_le_two] using
    hbound (2 ^ k) (by simpa using Nat.pow_le_pow_right zero_lt_two hk)

theorem diagonal_exponent_le_three_quarters {D : ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ D n)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ 4 ≤ D n ^ 3)
    (hupper : ∀ n : ℕ, 1 ≤ n → D n ≤ (2 * (n : ℝ) - 1) ^ (1 / t)) :
    t ≤ 3 / 4 := by
  have hexp : 0 ≤ 1 / t := le_of_lt (one_div_pos.mpr ht)
  have hpower : ∀ n : ℕ, 2 ≤ n →
      (n : ℝ) ^ (4 : ℝ) ≤ (2 : ℝ) ^ ((1 / t) * 3) * (n : ℝ) ^ ((1 / t) * 3) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hu : D n ≤ (2 * (n : ℝ)) ^ (1 / t) :=
      (hupper n hn1).trans (Real.rpow_le_rpow (by linarith) (by linarith) hexp)
    calc
      (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by norm_num
      _ ≤ D n ^ 3 := hlower n hn1
      _ ≤ ((2 * (n : ℝ)) ^ (1 / t)) ^ 3 := pow_le_pow_left₀ (hnonneg n hn1) hu 3
      _ = (2 * (n : ℝ)) ^ ((1 / t) * 3) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_mul_natCast (show 0 ≤ 2 * (n : ℝ) by positivity) (1 / t) 3).symm
      _ = (2 : ℝ) ^ ((1 / t) * 3) * (n : ℝ) ^ ((1 / t) * 3) :=
        Real.mul_rpow (by norm_num) (by positivity)
  have hmul := mul_le_mul_of_nonneg_right (rpow_exponent_le_of_nat_bound hpower) ht.le
  rw [show ((1 / t) * 3) * t = (3 : ℝ) by field_simp] at hmul
  linarith

theorem exists_rankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let a : X × Y × Z → X → K := fun p x => if x = p.1 then T p.1 p.2.1 p.2.2 else 0
  let b : X × Y × Z → Y → K := fun p y => if y = p.2.1 then 1 else 0
  let c : X × Y × Z → Z → K := fun p z => if z = p.2.2 then 1 else 0
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z; simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, mul_ite]
  exact ⟨Fintype.card (X × Y × Z), heq ▸ Tensor.rankAtMost_sum_rankOne a b c⟩

section NontrivialRank

def exactRank [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

theorem exactRank_spec [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : Tensor.RankAtMost T (exactRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

theorem exactRank_le [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) : exactRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

theorem exactRank_restrict_le {X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : exactRank (Tensor.restrict A B C T) ≤ exactRank T :=
  exactRank_le ((exactRank_spec T).restrict A B C)

theorem exactRank_reindex {X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    exactRank (Tensor.pullback ex ey ez T) = exactRank T := by
  apply le_antisymm (exactRank_le ((exactRank_spec T).pullback ex ey ez))
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z; simp [Tensor.pullback]
  simpa only [heq] using exactRank_le
    ((exactRank_spec (Tensor.pullback ex ey ez T)).pullback ex.symm ey.symm ez.symm)

theorem exactRank_product_le {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    exactRank (Tensor.product T S) ≤ exactRank T * exactRank S :=
  exactRank_le ((exactRank_spec T).product (exactRank_spec S))

variable [Nontrivial K]

def exactMatrixRank (K : Type*) [CommSemiring K] [Nontrivial K] (n : ℕ) : ℕ :=
  exactRank ((matrixMultiplicationTensor (K := K)) n n n)

theorem exactMatrixRank_spec (n : ℕ) :
    Tensor.RankAtMost ((matrixMultiplicationTensor (K := K)) n n n) ((exactMatrixRank K) n) :=
  exactRank_spec _

theorem matrixMultiplication_rank_lower {n R : ℕ} (hn : 0 < n)
    (hRank : Tensor.RankAtMost ((matrixMultiplicationTensor (K := K)) n n n) R) : n ^ 2 ≤ R := by
  let j : Fin n := ⟨0, hn⟩
  have h := hRank.card_le_of_identity
    (fun i : Fin n × Fin n => (i.2, j)) (fun i : Fin n × Fin n => (j, i.1)) id
    (fun i k => by simp [matrixMultiplicationTensor, Prod.ext_iff, eq_comm])
  simpa [Fintype.card_prod, pow_two] using h

theorem exactMatrixRank_lower {n : ℕ} (hn : 0 < n) : n ^ 2 ≤ (exactMatrixRank K) n :=
  matrixMultiplication_rank_lower hn (exactMatrixRank_spec n)

theorem exactMatrixRank_pos {n : ℕ} (hn : 0 < n) : 0 < (exactMatrixRank K) n :=
  lt_of_lt_of_le (pow_pos hn 2) (exactMatrixRank_lower hn)

def exactRankExponentSet (K : Type*) [CommSemiring K] [Nontrivial K] : Set ℝ :=
  {τ | ∃ n : ℕ, 2 ≤ n ∧ τ = Real.logb n ((exactMatrixRank K) n)}

def exactRankExponent (K : Type*) [CommSemiring K] [Nontrivial K] : ℝ := sInf (exactRankExponentSet K)

theorem exactRankExponentSet_nonempty : (exactRankExponentSet K).Nonempty :=
  ⟨Real.logb 2 ((exactMatrixRank K) 2), 2, le_rfl, rfl⟩

theorem exactMatrixRank_logb_lower {n : ℕ} (hn : 2 ≤ n) :
    2 ≤ Real.logb n ((exactMatrixRank K) n) := by
  rw [Real.le_logb_iff_rpow_le (by exact_mod_cast (show 1 < n by omega))
    (by exact_mod_cast exactMatrixRank_pos (show 0 < n by omega)), Real.rpow_two]
  exact_mod_cast exactMatrixRank_lower (show 0 < n by omega)

theorem exactRankExponent_lower : 2 ≤ (exactRankExponent K) :=
  le_csInf exactRankExponentSet_nonempty (by rintro τ ⟨n, hn, rfl⟩; exact exactMatrixRank_logb_lower hn)

theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (exactRankExponent K) ≤ (exactMatrixRank K) n := by
  by_cases hn2 : 2 ≤ n
  · exact (Real.le_logb_iff_rpow_le (by exact_mod_cast (show 1 < n by omega))
      (by exact_mod_cast exactMatrixRank_pos hn)).mp
      (csInf_le ⟨2, by rintro τ ⟨m, hm, rfl⟩; exact exactMatrixRank_logb_lower hm⟩ ⟨n, hn2, rfl⟩)
  · obtain rfl : n = 1 := by omega
    simpa using (by exact_mod_cast exactMatrixRank_lower (K := K) zero_lt_one :
      (1 : ℝ) ≤ exactMatrixRank K 1)

theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : (exactRankExponent K) < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ ((exactMatrixRank K) n : ℝ) < (n : ℝ) ^ τ := by
  obtain ⟨σ, ⟨n, hn, rfl⟩, hσ⟩ :=
    exists_lt_of_csInf_lt exactRankExponentSet_nonempty hτ
  exact ⟨n, hn, (Real.logb_lt_iff_lt_rpow (by exact_mod_cast (show 1 < n by omega))
    (by exact_mod_cast exactMatrixRank_pos (show 0 < n by omega))).mp hσ⟩

theorem exists_rankAtMost_of_exponent_slack {ε : ℝ} (hε : 0 < ε) :
    ∃ n R : ℕ, 2 ≤ n ∧ Tensor.RankAtMost ((matrixMultiplicationTensor (K := K)) n n n) R ∧
      (R : ℝ) ≤ (n : ℝ) ^ ((exactRankExponent K) + ε) := by
  obtain ⟨n, hn, hR⟩ := exists_exactMatrixRank_lt_rpow (K := K) (lt_add_of_pos_right _ hε)
  exact ⟨n, (exactMatrixRank K) n, hn, exactMatrixRank_spec n, hR.le⟩

end NontrivialRank

theorem exp_le_of_tendsto_log_div {u : ℕ → ℝ} {n : ℕ → ℕ} {b C L : ℝ}
    (hb : 0 < b) (hC : 0 < C) (hn : Tendsto n atTop atTop)
    (hu : ∀ᶠ k in atTop, 0 < u k)
    (hlim : Tendsto (fun k => Real.log (u k) / (n k : ℝ)) atTop (𝓝 L))
    (hbound : ∀ᶠ k in atTop, u k ≤ C * b ^ n k) :
    Real.exp L ≤ b := by
  have hconstant : Tendsto (fun k => Real.log C / (n k : ℝ) + Real.log b)
      atTop (𝓝 (Real.log b)) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (Real.log C)).comp hn).add_const (Real.log b)
  have hnormalized : ∀ᶠ k in atTop,
      Real.log (u k) / (n k : ℝ) ≤ Real.log C / (n k : ℝ) + Real.log b := by
    filter_upwards [hu, hbound, hn.eventually (eventually_gt_atTop 0)] with k huk hk hnk
    have hnpos : (0 : ℝ) < n k := by exact_mod_cast hnk
    have hlog := Real.log_le_log huk hk
    rw [Real.log_mul hC.ne' (pow_ne_zero _ hb.ne'), Real.log_pow] at hlog
    calc Real.log (u k) / (n k : ℝ) ≤ (Real.log C + (n k : ℝ) * Real.log b) / (n k : ℝ) :=
          (div_le_div_iff_of_pos_right hnpos).2 hlog
      _ = Real.log C / (n k : ℝ) + Real.log b := by field_simp
  simpa only [Real.exp_log hb] using
    Real.exp_le_exp.mpr (le_of_tendsto_of_tendsto hlim hconstant hnormalized)

def unitTensor : Tensor K PUnit PUnit PUnit := fun _ _ _ => 1

def scalarTensor (r : ℕ) : Tensor K (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ i = k then 1 else 0

def sumTensor {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0

structure Character (K : Type*) [CommSemiring K] where
  value : {X Y Z : Type} → [Fintype X] → [Fintype Y] → [Fintype Z] →
    Tensor K X Y Z → ℝ
  nonneg : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z), 0 ≤ value T
  map_zero : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z],
    value (0 : Tensor K X Y Z) = 0
  map_one : value (unitTensor (K := K)) = 1
  map_directSum : ∀ {ι X Y Z : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Y] [Fintype Z] (T : ι → Tensor K X Y Z),
    value (Tensor.directSum T) = ∑ i, value (T i)
  map_product : ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W),
    value (Tensor.product T S) = value T * value S
  monotone : ∀ {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K)
    (B : Y' → Y → K) (C : Z' → Z → K),
    value (Tensor.restrict A B C T) ≤ value T

namespace Integral

variable {R E ι U V W : Type*}

section Semiring
variable [CommSemiring R]

theorem restrict_directSum [Fintype U] [Fintype V] [Fintype W]
    [Fintype ι] [DecidableEq ι]
    (T : ι → Tensor R U V W)
    (A : ι → X → U → R) (B : ι → Y → V → R) (C : ι → Z → W → R) :
    Tensor.restrict (fun x q => A q.1 x q.2)
      (fun y q => B q.1 y q.2) (fun z q => C q.1 z q.2)
      (Tensor.directSum T) = fun x y z => ∑ i, Tensor.restrict (A i) (B i) (C i) (T i) x y z := by
  funext x y z
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type, ite_and]

theorem restrict_power [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor R U V W) (A : X → U → R) (B : Y → V → R)
    (C : Z → W → R) (k : ℕ) :
    Tensor.restrict (fun x u => ∏ i : Fin k, A (x i) (u i))
      (fun y v => ∏ i : Fin k, B (y i) (v i))
      (fun z w => ∏ i : Fin k, C (z i) (w i)) (Tensor.power T k) =
      Tensor.power (Tensor.restrict A B C T) k := by
  funext x y z
  simp only [Tensor.restrict, Tensor.power, Fintype.prod_sum, Finset.prod_mul_distrib]

def shiftedCoeff (p : R[X]) (h shift : ℕ) : R :=
  if shift ≤ h then p.coeff (h - shift) else 0

theorem coeff_monomial_mul_full (p : R[X]) (r : R) (shift h : ℕ) :
    ((Polynomial.monomial shift r) * p).coeff h = r * shiftedCoeff p h shift := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  rfl

theorem coeff_mul_mul_bounded (p q t : R[X]) (a b h : ℕ)
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p * q * t).coeff h =
      ∑ i : Fin (a + 1), ∑ j : Fin (b + 1),
        p.coeff i * q.coeff j * shiftedCoeff t h (i.val + j.val) := by
  have ep : p = ∑ i : Fin (a + 1), Polynomial.monomial i.val (p.coeff i) :=
    (p.as_sum_range' (a + 1) (Nat.lt_succ_of_le hp)).trans
      (Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (p.coeff i)) (a + 1)).symm
  have eq : q = ∑ j : Fin (b + 1), Polynomial.monomial j.val (q.coeff j) :=
    (q.as_sum_range' (b + 1) (Nat.lt_succ_of_le hq)).trans
      (Fin.sum_univ_eq_sum_range (fun j => Polynomial.monomial j (q.coeff j)) (b + 1)).symm
  conv_lhs => rw [ep, eq]
  simp only [Finset.sum_mul, Finset.mul_sum, Polynomial.finsetSum_coeff,
    Polynomial.monomial_mul_monomial, coeff_monomial_mul_full]
  exact Finset.sum_comm

theorem restrict_coefficient [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor R U V W)
    (A : X → U → R[X]) (B : Y → V → R[X]) (C : Z → W → R[X])
    (a b h : ℕ) (hA : ∀ x u, (A x u).natDegree ≤ a)
    (hB : ∀ y v, (B y v).natDegree ≤ b) :
    (fun x y z => (Tensor.restrict A B C
      (fun u v w => Polynomial.C (T u v w)) x y z).coeff h) =
    Tensor.restrict
      (fun x (q : (Fin (a + 1) × Fin (b + 1)) × U) => (A x q.2).coeff q.1.1)
      (fun y (q : (Fin (a + 1) × Fin (b + 1)) × V) => (B y q.2).coeff q.1.2)
      (fun z (q : (Fin (a + 1) × Fin (b + 1)) × W) =>
        shiftedCoeff (C z q.2) h (q.1.1.val + q.1.2.val))
      (Tensor.directSum (fun _ : Fin (a + 1) × Fin (b + 1) => T)) := by
  rw [restrict_directSum (fun _ : Fin (a + 1) × Fin (b + 1) => T)
    (fun q x u => (A x u).coeff q.1)
    (fun q y v => (B y v).coeff q.2)
    (fun q z w => shiftedCoeff (C z w) h (q.1.val + q.2.val))]
  funext x y z
  simp only [Tensor.restrict, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C]
  simp_rw [coeff_mul_mul_bounded _ _ _ a b h (hA x _) (hB y _)]
  simp only [Finset.sum_mul]
  simpa only [Fintype.sum_prod_type] using Tensor.sum_comm_three
    (fun (q : Fin (a + 1) × Fin (b + 1)) (u : U) (v : V) (w : W) =>
      (A x u).coeff q.1 * (B y v).coeff q.2 *
        shiftedCoeff (C z w) h (q.1.val + q.2.val) * T u v w)

end Semiring

variable [CommRing R] [CommRing E] [Algebra R E] [Fintype ι]

theorem project_mul_mul (basis : Module.Basis ι R E) (π : E →ₗ[R] R)
    (v w t : E) :
    π (v * w * t) = ∑ i, ∑ j,
      basis.repr v i * basis.repr w j * π (basis i * basis j * t) := by
  classical
  calc
    π (v * w * t) =
        π ((∑ i, basis.repr v i • basis i) *
          (∑ j, basis.repr w j • basis j) * t) := by
      rw [basis.sum_repr, basis.sum_repr]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_assoc,
        mul_smul_comm, map_smul, smul_eq_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem _root_.OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost.descend_finite_basis_powers
    (basis : Module.Basis ι R E) (π : E →ₗ[R] R) (hπ : π 1 = 1)
    {T : Tensor R X Y Z} {r : ℕ}
    (h : Tensor.RankAtMost (fun x y z => algebraMap R E (T x y z)) r) (k : ℕ) :
    Tensor.RankAtMost (Tensor.power T k) (r ^ k * Fintype.card ι * Fintype.card ι) := by
  classical
  have hp : Tensor.RankAtMost
      (fun x y z => algebraMap R E (Tensor.power T k x y z)) (r ^ k) := by
    convert h.power k using 1
    funext x y z; simp only [Tensor.power, map_prod]
  rcases hp with ⟨a, b, c, heq⟩
  let aa : Fin (r ^ k) × (ι × ι) → (Fin k → X) → R := fun q x => basis.repr (a q.1 x) q.2.1
  let bb : Fin (r ^ k) × (ι × ι) → (Fin k → Y) → R := fun q y => basis.repr (b q.1 y) q.2.2
  let cc : Fin (r ^ k) × (ι × ι) → (Fin k → Z) → R := fun q z => π (basis q.2.1 * basis q.2.2 * c q.1 z)
  have hT : Tensor.power T k = fun x y z => ∑ q, Tensor.rankOne (aa q) (bb q) (cc q) x y z := by
    funext x y z
    have hv : Tensor.power T k x y z = π (algebraMap R E (Tensor.power T k x y z)) := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]
    rw [hv, congrFun (congrFun (congrFun heq x) y) z]
    simp only [map_sum, Fintype.sum_prod_type, Tensor.rankOne]
    exact Finset.sum_congr rfl fun q _ => project_mul_mul basis π (a q x) (b q y) (c q z)
  rw [hT]
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc] using
    Tensor.rankAtMost_sum_rankOne aa bb cc

set_option maxHeartbeats 800000 in
theorem descend_restriction_basis [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq ι] (basis : Module.Basis ι R E) (π : E →ₗ[R] R) (hπ : π 1 = 1)
    (S : Tensor R X Y Z) (T : Tensor R U V W)
    (A : X → U → E) (B : Y → V → E) (C : Z → W → E)
    (h : Tensor.restrict A B C (fun u v w => algebraMap R E (T u v w)) =
      fun x y z => algebraMap R E (S x y z)) :
    S = Tensor.restrict
      (fun x (q : (ι × ι) × U) => basis.repr (A x q.2) q.1.1)
      (fun y (q : (ι × ι) × V) => basis.repr (B y q.2) q.1.2)
      (fun z (q : (ι × ι) × W) => π (basis q.1.1 * basis q.1.2 * C z q.2))
      (Tensor.directSum (fun _ : ι × ι => T)) := by
  have hm (v : E) (r : R) : π (v * algebraMap R E r) = π v * r := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have heq : (fun x y z => π (Tensor.restrict A B C
      (fun u v w => algebraMap R E (T u v w)) x y z)) =
    Tensor.restrict
      (fun x (q : (ι × ι) × U) => basis.repr (A x q.2) q.1.1)
      (fun y (q : (ι × ι) × V) => basis.repr (B y q.2) q.1.2)
      (fun z (q : (ι × ι) × W) => π (basis q.1.1 * basis q.1.2 * C z q.2))
      (Tensor.directSum (fun _ : ι × ι => T)) := by
    rw [restrict_directSum (fun _ : ι × ι => T)
      (fun q x u => basis.repr (A x u) q.1)
      (fun q y v => basis.repr (B y v) q.2)
      (fun q z w => π (basis q.1 * basis q.2 * C z w))]
    funext x y z
    simp only [Tensor.restrict, map_sum, hm]
    calc
      _ = ∑ u, ∑ v, ∑ w, (∑ q : ι × ι,
          basis.repr (A x u) q.1 * basis.repr (B y v) q.2 *
            π (basis q.1 * basis q.2 * C z w)) * T u v w :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
          Finset.sum_congr rfl fun w _ => by
            rw [project_mul_mul basis π (A x u) (B y v) (C z w), Fintype.sum_prod_type]
      _ = _ := by
        simp only [Finset.sum_mul]
        simpa only [Fintype.sum_prod_type] using Tensor.sum_comm_three
          (fun (q : ι × ι) (u : U) (v : V) (w : W) =>
            basis.repr (A x u) q.1 * basis.repr (B y v) q.2 *
              π (basis q.1 * basis q.2 * C z w) * T u v w)
  rw [h] at heq
  simpa only [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one] using heq

def monicQuotientProjection {f : Polynomial R} (hf : f.Monic) : AdjoinRoot f →ₗ[R] R :=
  (Polynomial.lcoeff R 0).comp (AdjoinRoot.modByMonicHom hf)

theorem monicQuotientProjection_one [Nontrivial R] {f : Polynomial R} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) : monicQuotientProjection hf 1 = 1 := by
  have hmod : (1 : Polynomial R) %ₘ f = 1 :=
    (Polynomial.modByMonic_eq_self_iff hf).mpr (by
      simpa only [Polynomial.degree_one] using
        Polynomial.natDegree_pos_iff_degree_pos.mp hdeg)
  change (AdjoinRoot.modByMonicHom hf (1 : AdjoinRoot f)).coeff 0 = 1
  rw [← map_one (AdjoinRoot.mk f), AdjoinRoot.modByMonicHom_mk, hmod]
  exact Polynomial.coeff_one_zero

end Integral
end AuxiliarySeparation

namespace Foundation.Tensor.PolynomialRestrictionDegeneration

open AuxiliarySeparation.Integral

variable {R X Y Z X' Y' Z' : Type*} [CommRing R]
variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor R X Y Z} {U : Tensor R X' Y' Z'}
variable {k Lx Ly Lz : ℕ}

theorem prod_degree_le {A B : Type*} {n L : ℕ} {P : A → B → Polynomial R}
    (hP : ∀ a b, (P a b).degree ≤ L) (x : Fin n → A) (u : Fin n → B) :
    (∏ i : Fin n, P (x i) (u i)).degree ≤ (L * n : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  calc
    _ ≤ ∑ i : Fin n, (P (x i) (u i)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin n, L := Finset.sum_le_sum fun i _ => Polynomial.natDegree_le_of_degree_le (hP (x i) (u i))
    _ = L * n := by simp [Nat.mul_comm]

def power (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) (n : ℕ) :
    PolynomialRestrictionDegeneration (Tensor.power T n) (Tensor.power U n)
      (k * n) (Lx * n) (Ly * n) (Lz * n) := by
  let N : Tensor (Polynomial R) X' Y' Z' := fun x y z =>
    Classical.choose (Polynomial.X_pow_dvd_iff.mpr (L.vanishes x y z))
  have hN (x : X') (y : Y') (z : Z') :
      L.basePolynomial x y z = Polynomial.X ^ k * N x y z :=
    Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (L.vanishes x y z))
  have hN0 (x : X') (y : Y') (z : Z') : (N x y z).coeff 0 = U x y z := by
    have h := L.leading x y z
    change (L.basePolynomial x y z).coeff k = U x y z at h
    rw [hN] at h
    simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using h
  have hbase : Tensor.restrict
      (fun x u => ∏ i : Fin n, L.leftMap (x i) (u i))
      (fun y v => ∏ i : Fin n, L.middleMap (y i) (v i))
      (fun z w => ∏ i : Fin n, L.rightMap (z i) (w i))
      (fun u v w => Polynomial.C (Tensor.power T n u v w)) =
      Tensor.power L.basePolynomial n := by
    have hC : (fun u v w => Polynomial.C (Tensor.power T n u v w)) =
        Tensor.power (fun u v w => Polynomial.C (T u v w)) n := by
      funext u v w; simp only [Tensor.power, map_prod]
    rw [hC, restrict_power]; rfl
  have hprod (x : Fin n → X') (y : Fin n → Y') (z : Fin n → Z') :
      Tensor.power L.basePolynomial n x y z =
        Polynomial.X ^ (k * n) * Tensor.power N n x y z := by
    simp [Tensor.power, hN, Finset.prod_mul_distrib, ← pow_mul]
  refine {
    leftMap := fun x u => ∏ i : Fin n, L.leftMap (x i) (u i)
    middleMap := fun y v => ∏ i : Fin n, L.middleMap (y i) (v i)
    rightMap := fun z w => ∏ i : Fin n, L.rightMap (z i) (w i)
    left_degree := prod_degree_le L.left_degree
    middle_degree := prod_degree_le L.middle_degree
    right_degree := prod_degree_le L.right_degree
    vanishes := fun x y z j hj => by
      rw [hbase, hprod, Polynomial.coeff_X_pow_mul']
      simp only [Nat.not_le_of_lt hj, ite_false]
    leading := fun x y z => by
      rw [hbase, hprod, Polynomial.coeff_X_pow_mul']
      simp only [le_refl, ite_true, Nat.sub_self, Tensor.power, Polynomial.coeff_zero_prod, hN0] }

theorem extract (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    U = Tensor.restrict
      (fun x (q : (Fin (Lx + 1) × Fin (Ly + 1)) × X) => (L.leftMap x q.2).coeff q.1.1)
      (fun y (q : (Fin (Lx + 1) × Fin (Ly + 1)) × Y) => (L.middleMap y q.2).coeff q.1.2)
      (fun z (q : (Fin (Lx + 1) × Fin (Ly + 1)) × Z) =>
        shiftedCoeff (L.rightMap z q.2) k (q.1.1.val + q.1.2.val))
      (Tensor.directSum (fun _ : Fin (Lx + 1) × Fin (Ly + 1) => T)) := by
  have h := restrict_coefficient T L.leftMap L.middleMap L.rightMap Lx Ly k
    (fun x u => Polynomial.natDegree_le_of_degree_le (L.left_degree x u))
    (fun y v => Polynomial.natDegree_le_of_degree_le (L.middle_degree y v))
  simpa only [L.leading] using h

end Foundation.Tensor.PolynomialRestrictionDegeneration

namespace AuxiliarySeparation

open Foundation

theorem le_of_pow_le_const_product_linear_mul_pow {a b A B C : ℝ}
    (ha : 0 ≤ a)
    (h : ∀ n : ℕ, b ^ n ≤ C * ((n : ℝ) * A + 1) * (n * B + 1) * a ^ n) :
    b ≤ a := by
  by_contra hba
  have hab : a < b := lt_of_not_ge hba
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hr₀ : 0 ≤ a / b := div_nonneg ha hb.le
  have hr₁ : a / b < 1 := (div_lt_one hb).2 hab
  have hquadratic := (tendsto_pow_const_mul_const_pow_of_lt_one 2 hr₀ hr₁).mul_const (C * A * B)
  have hlinear := (tendsto_self_mul_const_pow_of_lt_one hr₀ hr₁).mul_const (C * (A + B))
  have hconstant := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).const_mul C
  have hlim : Tendsto (fun n : ℕ =>
      C * ((n : ℝ) * A + 1) * (n * B + 1) * (a / b) ^ n) atTop (𝓝 0) := by
    convert (hquadratic.add hlinear).add hconstant using 1 <;> try simp
    funext n; ring
  have hbound : ∀ᶠ n : ℕ in atTop,
      1 ≤ C * ((n : ℝ) * A + 1) * (n * B + 1) * (a / b) ^ n := by
    filter_upwards with n
    have hdiv := (div_le_div_iff_of_pos_right (pow_pos hb n)).2 (h n)
    simpa only [div_self (pow_ne_zero n hb.ne'), mul_div_assoc, div_pow] using hdiv
  linarith [ge_of_tendsto hlim hbound]

namespace Character

variable {K : Type*} [CommSemiring K] (χ : Character K)
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

theorem value_pullback_le (T : Tensor K X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    χ.value (Tensor.pullback fx fy fz T) ≤ χ.value T := by
  classical
  simpa only [Tensor.pullback_eq_restrict] using χ.monotone T _ _ _

theorem value_reindex (T : Tensor K X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.value (Tensor.pullback ex ey ez T) = χ.value T := by
  apply le_antisymm (χ.value_pullback_le T ex ey ez)
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z; simp [Tensor.pullback]
  simpa only [heq] using χ.value_pullback_le (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm

@[simp] theorem value_scalarTensor (r : ℕ) : χ.value ((scalarTensor (K := K)) r) = r := by
  have heq : Tensor.pullback (Equiv.prodPUnit (Fin r)).symm
      (Equiv.prodPUnit (Fin r)).symm (Equiv.prodPUnit (Fin r)).symm
      (Tensor.directSum fun _ : Fin r => (unitTensor (K := K))) = (scalarTensor (K := K)) r := rfl
  rw [← heq, χ.value_reindex, χ.map_directSum]
  simp [χ.map_one]

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem restrict_scalarTensor (r : ℕ) (a : Fin r → X → K)
    (b : Fin r → Y → K) (c : Fin r → Z → K) :
    Tensor.restrict (fun x i => a i x) (fun y i => b i y) (fun z i => c i z)
      ((scalarTensor (K := K)) r) =
      fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z := by
  funext x y z; simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]

theorem value_le_rank {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.value T ≤ r := by
  rcases h with ⟨a, b, c, rfl⟩
  rw [← restrict_scalarTensor r a b c]
  exact (χ.monotone ((scalarTensor (K := K)) r) _ _ _).trans_eq (χ.value_scalarTensor r)

theorem one_le_value_of_coefficient_one {T : Tensor K X Y Z}
    (hT : ∃ x y z, T x y z = 1) : 1 ≤ χ.value T := by
  obtain ⟨x, y, z, hxyz⟩ := hT
  have heq : Tensor.pullback (fun _ : PUnit.{1} => x) (fun _ : PUnit.{1} => y) (fun _ : PUnit.{1} => z) T =
      (unitTensor (K := K)) := funext fun _ => funext fun _ => funext fun _ => hxyz
  simpa only [heq, χ.map_one] using
    χ.value_pullback_le T (fun _ : PUnit.{1} => x) (fun _ : PUnit.{1} => y) (fun _ : PUnit.{1} => z)

@[simp] theorem value_power (T : Tensor K X Y Z) (n : ℕ) :
    χ.value (Tensor.power T n) = χ.value T ^ n := by
  induction n with
  | zero =>
      have heq : Tensor.power T 0 = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) (unitTensor (K := K)) := by
        funext x y z; simp [Tensor.power, Tensor.pullback, unitTensor]
      rw [heq, χ.value_reindex, χ.map_one, pow_zero]
  | succ n ih =>
      have heq : Tensor.power T (n + 1) = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product T (Tensor.power T n)) := by
        funext x y z
        simp [Tensor.power, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, χ.value_reindex, χ.map_product, ih, pow_succ, mul_comm]

omit [Fintype X'] [Fintype Y'] [Fintype Z'] in
theorem _root_.OAI.MatrixMultiplication.AuxiliarySeparation.tensor_eq_extendByZero_pullback
    (T : Tensor K X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    letI := Classical.decEq X'; letI := Classical.decEq Y'; letI := Classical.decEq Z'
    T = Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0)
      (Tensor.pullback fx fy fz T) := by
  classical
  funext x' y' z'
  by_cases h : x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz
  · rcases h with ⟨⟨x, rfl⟩, ⟨y, rfl⟩, ⟨z, rfl⟩⟩
    simp [Tensor.restrict, Tensor.pullback, hx.eq_iff, hy.eq_iff, hz.eq_iff, ite_mul, mul_ite]
  · have hzero : T x' y' z' = 0 := by by_contra hn; exact h (hs _ _ _ hn)
    rw [hzero]
    rcases not_and_or.mp h with hx' | hyz
    · simp [Tensor.restrict, show ∀ x, fx x ≠ x' from fun x hx => hx' ⟨x, hx⟩]
    · rcases not_and_or.mp hyz with hy' | hz'
      · simp [Tensor.restrict, show ∀ y, fy y ≠ y' from fun y hy => hy' ⟨y, hy⟩]
      · simp [Tensor.restrict, show ∀ z, fz z ≠ z' from fun z hz => hz' ⟨z, hz⟩]

theorem value_eq_pullback_of_support (T : Tensor K X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    χ.value T = χ.value (Tensor.pullback fx fy fz T) := by
  classical
  refine le_antisymm ?_ (χ.value_pullback_le T fx fy fz)
  conv_lhs => rw [tensor_eq_extendByZero_pullback T fx fy fz hx hy hz hs]
  exact χ.monotone _ _ _ _

def cyclicCharacter : Character K where
  value T := χ.value (Tensor.cyclic T)
  nonneg T := χ.nonneg (Tensor.cyclic T)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by rw [Tensor.cyclic_directSum, χ.map_directSum]
  map_product T S := χ.map_product (Tensor.cyclic T) (Tensor.cyclic S)
  monotone T A B C := by
    have heq : Tensor.cyclic (Tensor.restrict A B C T) =
        Tensor.restrict B C A (Tensor.cyclic T) := by
      funext y z x
      simp only [Tensor.cyclic, Tensor.restrict]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    rw [heq]
    exact χ.monotone (Tensor.cyclic T) B C A

theorem value_dotPairing_mono {m n : ℕ} (hmn : m ≤ n) :
    χ.value (Tensor.dotPairing (K := K) (Fin m)) ≤
      χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback (Fin.castLE hmn) (Fin.castLE hmn) id
      (Tensor.dotPairing (K := K) (Fin n)) = Tensor.dotPairing (K := K) (Fin m) := by
    funext x y z; simp [Tensor.pullback, Tensor.dotPairing]
  rw [← heq]
  exact χ.value_pullback_le _ _ _ _

theorem value_dotPairing_mul (m n : ℕ) :
    χ.value (Tensor.dotPairing (K := K) (Fin (m * n))) =
      χ.value (Tensor.dotPairing (K := K) (Fin m)) *
        χ.value (Tensor.dotPairing (K := K) (Fin n)) := by
  have heq : Tensor.pullback finProdFinEquiv.symm finProdFinEquiv.symm
      (Equiv.prodUnique Unit Unit).symm
      (Tensor.product (Tensor.dotPairing (K := K) (Fin m))
        (Tensor.dotPairing (K := K) (Fin n))) =
      Tensor.dotPairing (K := K) (Fin (m * n)) := by
    funext x y z
    simp only [Tensor.pullback, Tensor.product, Tensor.dotPairing,
      ite_zero_mul_ite_zero, one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
  rw [← heq, χ.value_reindex, χ.map_product]

def pZ : ℝ :=
  Real.log (χ.value (Tensor.dotPairing (K := K) (Fin 2))) / Real.log 2

def pY : ℝ := χ.cyclicCharacter.pZ

def pX : ℝ := χ.cyclicCharacter.cyclicCharacter.pZ

theorem value_dotPairing {n : ℕ} (hn : 0 < n) :
    χ.value (Tensor.dotPairing (K := K) (Fin n)) = (n : ℝ) ^ χ.pZ := by
  let f (m : ℕ) := χ.value (Tensor.dotPairing (K := K) (Fin m))
  have hpos {m : ℕ} (hm : 0 < m) : 0 < f m :=
    lt_of_lt_of_le zero_lt_one (χ.one_le_value_of_coefficient_one
      ⟨⟨0, hm⟩, ⟨0, hm⟩, (), by simp [Tensor.dotPairing]⟩)
  have hf1 : f 1 = 1 := by
    have hm := χ.value_dotPairing_mul 1 1
    have hp := hpos zero_lt_one
    dsimp [f] at hp ⊢; rw [mul_one] at hm; nlinarith
  have hpow (m k : ℕ) : f (m ^ k) = f m ^ k := by
    induction k with
    | zero => simpa using hf1
    | succ k ih => rw [pow_succ, pow_succ, ← ih]; exact χ.value_dotPairing_mul _ _
  have hlog_le {a b j k : ℕ} (ha : 0 < a) (h : a ^ j ≤ b ^ k) :
      (j : ℝ) * Real.log (f a) ≤ (k : ℝ) * Real.log (f b) := by
    simpa only [← Real.log_pow, ← hpow] using
      Real.log_le_log (hpos (pow_pos ha j)) (χ.value_dotPairing_mono h)
  have hf2 : 0 ≤ Real.log (f 2) :=
    Real.log_nonneg (hf1 ▸ χ.value_dotPairing_mono (by omega : 1 ≤ 2))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have herr (k : ℕ) :
      |(k : ℝ) * (Real.log (f n) * Real.log 2 - Real.log (n : ℝ) * Real.log (f 2))| ≤
        Real.log (f 2) * Real.log 2 := by
    obtain ⟨m, hlow, hupp⟩ :=
      exists_nat_pow_near (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k hn.ne')) (by omega : 1 < 2)
    have hflow := hlog_le zero_lt_two hlow
    have hfupp := hlog_le hn hupp.le
    have hnlow := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) m)
      (by exact_mod_cast hlow : (2 : ℝ) ^ m ≤ (n : ℝ) ^ k)
    have hnupp := Real.log_le_log (pow_pos hnp k)
      (by exact_mod_cast hupp.le : (n : ℝ) ^ k ≤ (2 : ℝ) ^ (m + 1))
    simp only [Real.log_pow, Nat.cast_add, Nat.cast_one] at hflow hfupp hnlow hnupp
    rw [abs_le]; constructor <;> nlinarith
  have heq : Real.log (f n) * Real.log 2 = Real.log (n : ℝ) * Real.log (f 2) := by
    by_contra hne
    have hd : 0 < |Real.log (f n) * Real.log 2 - Real.log (n : ℝ) * Real.log (f 2)| :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨k, hk⟩ := exists_nat_gt
      (Real.log (f 2) * Real.log 2 / |Real.log (f n) * Real.log 2 - Real.log (n : ℝ) * Real.log (f 2)|)
    have hk' := (div_lt_iff₀ hd).mp hk
    have h := herr k
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)] at h
    linarith
  have hlog : Real.log (f n) = Real.log (n : ℝ) * χ.pZ := by
    dsimp [pZ, f] at heq ⊢; rw [← mul_div_assoc, ← heq, mul_div_cancel_right₀ _ hlog2.ne']
  rw [Real.rpow_def_of_pos hnp, ← hlog, Real.exp_log (hpos hn)]

theorem value_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m))) =
      (m : ℝ) ^ χ.pY :=
  χ.cyclicCharacter.value_dotPairing hm

theorem value_cyclic_cyclic_dotPairing {m : ℕ} (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := K) (Fin m)))) =
      (m : ℝ) ^ χ.pX :=
  χ.cyclicCharacter.cyclicCharacter.value_dotPairing hm

theorem value_matrixMultiplication {m : ℕ} (hm : 0 < m) :
    χ.value ((matrixMultiplicationTensor (K := K)) m m m) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  let D := Tensor.dotPairing (K := K) (Fin m)
  let ex : Fin m × Fin m ≃ (Fin m × Fin m) × Unit :=
    ⟨fun x => ((x.2, x.1), ()), fun x => (x.1.2, x.1.1), fun _ => rfl, fun ⟨⟨_, _⟩, ⟨⟩⟩ => rfl⟩
  let ey : Fin m × Fin m ≃ (Fin m × Unit) × Fin m :=
    ⟨fun y => ((y.1, ()), y.2), fun y => (y.1.1, y.2), fun _ => rfl, fun ⟨⟨_, ⟨⟩⟩, _⟩ => rfl⟩
  let ez : Fin m × Fin m ≃ (Unit × Fin m) × Fin m :=
    ⟨fun z => (((), z.2), z.1), fun z => (z.2, z.1.2), fun _ => rfl, fun ⟨⟨⟨⟩, _⟩, _⟩ => rfl⟩
  have heq : Tensor.pullback ex ey ez
      (Tensor.product (Tensor.product D (Tensor.cyclic D)) (Tensor.cyclic (Tensor.cyclic D))) =
      (matrixMultiplicationTensor (K := K)) m m m := by
    funext x y z
    change ((if x.2 = y.1 then (1 : K) else 0) *
      (if z.2 = x.1 then 1 else 0)) * (if y.2 = z.1 then 1 else 0) =
      if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
    have hguard : ((x.2 = y.1 ∧ z.2 = x.1) ∧ y.2 = z.1) ↔
        (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
      ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
    simp only [ite_zero_mul_ite_zero, one_mul, hguard]
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [← heq, χ.value_reindex, χ.map_product, χ.map_product,
    χ.value_dotPairing hm, χ.value_cyclic_dotPairing hm, χ.value_cyclic_cyclic_dotPairing hm,
    Real.rpow_add hm', Real.rpow_add hm']
  ring

section RingCharacter
variable {R : Type*} [CommRing R] (ψ : Character R)

theorem value_le_mul_of_power_comparisons
    (T : Tensor R X Y Z) (U : Tensor R X' Y' Z') (A B C L : ℝ) (hL : 0 ≤ L)
    (h : ∀ n : ℕ, ψ.value (Tensor.power U n) ≤
      C * ((n : ℝ) * A + 1) * (n * B + 1) * L ^ n * ψ.value (Tensor.power T n)) :
    ψ.value U ≤ L * ψ.value T := by
  apply le_of_pow_le_const_product_linear_mul_pow
    (A := A) (B := B) (C := C) (mul_nonneg hL (ψ.nonneg T))
  intro n
  simpa only [ψ.value_power, mul_pow, mul_assoc] using h n

theorem value_polynomialRestrictionDegeneration_le_ring
    {T : Tensor R X Y Z} {U : Tensor R X' Y' Z'} {k Lx Ly Lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    ψ.value U ≤ ψ.value T := by
  simpa only [one_mul] using
    ψ.value_le_mul_of_power_comparisons T U Lx Ly 1 1 zero_le_one fun n => by
      have h := ψ.monotone
        (Tensor.directSum (fun _ : Fin (Lx * n + 1) × Fin (Ly * n + 1) => Tensor.power T n))
        (fun x (q : (Fin (Lx * n + 1) × Fin (Ly * n + 1)) × (Fin n → X)) =>
          ((L.power n).leftMap x q.2).coeff q.1.1)
        (fun y (q : (Fin (Lx * n + 1) × Fin (Ly * n + 1)) × (Fin n → Y)) =>
          ((L.power n).middleMap y q.2).coeff q.1.2)
        (fun z (q : (Fin (Lx * n + 1) × Fin (Ly * n + 1)) × (Fin n → Z)) =>
          Integral.shiftedCoeff ((L.power n).rightMap z q.2) (k * n)
            (q.1.1.val + q.1.2.val))
      rw [← (L.power n).extract, ψ.map_directSum] at h
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
      convert h using 1; ring

omit [Fintype X'] [Fintype Y'] [Fintype Z'] in
theorem value_le_add_of_coprime_scaled_restrictions
    {U₁ V₁ W₁ U₂ V₂ W₂ : Type}
    [Fintype U₁] [Fintype V₁] [Fintype W₁]
    [Fintype U₂] [Fintype V₂] [Fintype W₂]
    (T : Tensor R X Y Z) (S₁ : Tensor R U₁ V₁ W₁) (S₂ : Tensor R U₂ V₂ W₂)
    {d e : R} (hde : IsCoprime d e) (n : ℕ)
    (h₁ : ∃ (A : X → U₁ → R) (B : Y → V₁ → R) (C : Z → W₁ → R),
      Tensor.restrict A B C S₁ = fun x y z => d ^ n * T x y z)
    (h₂ : ∃ (A : X → U₂ → R) (B : Y → V₂ → R) (C : Z → W₂ → R),
      Tensor.restrict A B C S₂ = fun x y z => e ^ n * T x y z) :
    ψ.value T ≤ ψ.value S₁ + ψ.value S₂ := by
  classical
  obtain ⟨u, v, huv⟩ := hde.pow (m := n) (n := n)
  obtain ⟨A₁, B₁, C₁, h₁⟩ := h₁
  obtain ⟨A₂, B₂, C₂, h₂⟩ := h₂
  let P : Bool → Tensor R X Y Z := fun b x y z => (if b then d ^ n else e ^ n) * T x y z
  have heq : Tensor.restrict (fun x (q : Bool × X) => if q.2 = x then 1 else 0)
      (fun y (q : Bool × Y) => if q.2 = y then 1 else 0)
      (fun z (q : Bool × Z) => if q.2 = z then (if q.1 then u else v) else 0)
      (Tensor.directSum P) = T := by
    rw [Integral.restrict_directSum P
      (fun _ x x' => if x' = x then 1 else 0)
      (fun _ y y' => if y' = y then 1 else 0)
      (fun b z z' => if z' = z then (if b then u else v) else 0)]
    funext x y z
    simp [Tensor.restrict, P, ite_mul, mul_ite]
    calc u * (d ^ n * T x y z) + v * (e ^ n * T x y z)
        = (u * d ^ n + v * e ^ n) * T x y z := by ring
      _ = T x y z := by rw [huv, one_mul]
  have h := ψ.monotone (Tensor.directSum P)
    (fun x (q : Bool × X) => if q.2 = x then 1 else 0)
    (fun y (q : Bool × Y) => if q.2 = y then 1 else 0)
    (fun z (q : Bool × Z) => if q.2 = z then (if q.1 then u else v) else 0)
  rw [heq, ψ.map_directSum, Fintype.sum_bool] at h
  have hP1 : P true = Tensor.restrict A₁ B₁ C₁ S₁ := by funext x y z; simp [P, h₁]
  have hP2 : P false = Tensor.restrict A₂ B₂ C₂ S₂ := by funext x y z; simp [P, h₂]
  rw [hP1, hP2] at h
  exact h.trans (add_le_add (ψ.monotone S₁ A₁ B₁ C₁) (ψ.monotone S₂ A₂ B₂ C₂))

end RingCharacter

end Character

theorem exactRankExponent_le_nine_quarters_of_characters {K : Type*} [CommSemiring K] [Nontrivial K]
    (detect : ∀ d : ℕ, 2 ≤ d → ∀ k : ℕ,
      (k : ℝ) < (d : ℝ) ^ (exactRankExponent K) →
      ∃ χ : Character K, (k : ℝ) ≤ χ.value ((matrixMultiplicationTensor (K := K)) d d d))
    (bound : ∀ χ : Character K, ∀ d : ℕ, 2 ≤ d →
      χ.value ((matrixMultiplicationTensor (K := K)) d d d) ≤ (d : ℝ) ^ (9 / 4 : ℝ)) :
    exactRankExponent K ≤ 9 / 4 := by
  apply rpow_exponent_le_of_nat_bound (C := 2)
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let x := (d : ℝ) ^ (exactRankExponent K)
  have hc : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hdpos _)
  let k := ⌈x⌉₊ - 1
  have hk : x - 1 ≤ (k : ℝ) := by
    dsimp [k]; rw [Nat.cast_sub hc, Nat.cast_one]; linarith [Nat.le_ceil x]
  have hk' : (k : ℝ) < x := ((Nat.ceil_eq_iff (by omega : ⌈x⌉₊ ≠ 0)).1 rfl).1
  obtain ⟨χ, hχ⟩ := detect d hd k hk'
  have h := hk.trans (hχ.trans (bound χ d hd))
  have hpow : 1 ≤ (d : ℝ) ^ (9 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ d by omega)) (by norm_num)
  dsimp [x] at h; linarith

end AuxiliarySeparation

end

end OAI.MatrixMultiplication
