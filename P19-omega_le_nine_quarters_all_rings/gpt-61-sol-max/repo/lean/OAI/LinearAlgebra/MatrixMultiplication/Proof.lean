module
public import Mathlib
public import OAI.LinearAlgebra.MatrixMultiplication.Model

/-!
The coefficient constructions remain generic where extension algebras are needed.
The restriction semiring, its spectrum, and the matrix-rank exponent are specialized
here to integer coefficients; these exact schemes are then interpreted by the
unchanged arithmetic model over every associative unital ring.
-/

@[expose] public section
noncomputable section
set_option maxHeartbeats 2000000
variable {K F S Input Input' Mid Output Term : Type*}
variable {X Y Z X' Y' Z' U V W P Q R U' V' W' : Type}
variable [CommSemiring K] [Ring F] [CommSemiring S] [Preorder S]
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype X'] [Fintype Y'] [Fintype Z'] [Fintype U] [Fintype V] [Fintype W] [Fintype P] [Fintype Q] [Fintype R] [Fintype U'] [Fintype V'] [Fintype W']
open scoped BigOperators Classical Topology Polynomial
namespace OAI.MatrixMultiplication
namespace Foundation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Entropy/ComplexFiniteEntropy -/
/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

def finiteEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

structure FiniteLaw (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

/-- The uniform finite probability law. -/
def FiniteLaw.uniformThree : FiniteLaw (Fin 3) where
  mass _ := 1 / 3
  nonneg _ := by norm_num
  total := by norm_num

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Tensor/ComplexTensor -/
section
/-! Finite coefficient tensors and their algebraic transformations. -/

abbrev Tensor (K : Type*) (X Y Z : Type) := X → Y → Z → K

namespace Tensor

def matrixCoefficients (A B C : Type) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

def dotPairing (U : Type) [DecidableEq U] : Tensor K U U Unit :=
  fun i j _ => if i = j then 1 else 0

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X :=
  fun y z x => T x y z

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

variable (T : Tensor K X Y Z)

def RankAtMost  (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def product  (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power  (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

theorem rankAtMost_sum_rankOne {ι : Type} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  let e := (Fintype.equivFin ι).symm
  refine ⟨a ∘ e, b ∘ e, c ∘ e, ?_⟩
  funext x y z
  exact (e.sum_comp
    fun i => rankOne (a i) (b i) (c i) x y z).symm

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  convert rankAtMost_sum_rankOne
    (fun (f : Fin n → Fin r) (x : Fin n → X) => ∏ i, a (f i) (x i))
    (fun f (y : Fin n → Y) => ∏ i, b (f i) (y i))
    (fun f (z : Fin n → Z) => ∏ i, c (f i) (z i)) using 1
  · ext <;> simp_all [Tensor.power, rankOne, Fintype.prod_sum, Finset.prod_mul_distrib]
  · simp

/-- Move a finite sum past the three tensor coordinates. -/
theorem sum_comm_three {ι : Type*}    [Fintype ι]
    (f : ι → U → V → W → K) :
    ∑ u, ∑ v, ∑ w, ∑ i, f i u v w = ∑ i, ∑ u, ∑ v, ∑ w, f i u v w := by
  simp only [← Fintype.sum_prod_type' (α₁ := V) (α₂ := W)]
  exact Finset.sum_comm_cycle

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict

    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by ext <;> simp_all [pullback, restrict]

end Tensor
end

attribute [simp] Tensor.pullback Tensor.product Tensor.directSum Tensor.rankOne Tensor.cyclic Tensor.dotPairing Tensor.matrixCoefficients

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Tensor/ComplexTensorFlattening -/
/-! Finite coefficient tensors and their algebraic transformations. -/

namespace Tensor

variable [Nontrivial K]

theorem RankAtMost.card_le_of_identity {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = 1 := by aesop
  have hinj : Function.Injective R.mulVecLin :=
    LinearMap.injective_of_comp_eq_id _ L.mulVecLin (by
      rw [← Matrix.mulVecLin_mul, hmul, Matrix.mulVecLin_one])
  simpa only [Fintype.card_fin] using card_le_of_injective K R.mulVecLin hinj

end Tensor

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Tensor/ComplexFactorialLogBounds -/
section
/-! Finite coefficient tensors and their algebraic transformations. -/

open Filter

def factorialLogRemainder (n : ℕ) :=
  Real.log (Nat.factorial n  ) - (n * Real.log n - n)

theorem tendsto_factorialLogRemainder_div :
    Tendsto (fun n : ℕ => factorialLogRemainder n / (n : ℝ)) atTop (𝓝 0) := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hstirling  :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log n / n)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hconstant := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  refine Tendsto.congr' ?_ (by
    simpa using (hstirling.add ((hconstant.add hlog).const_mul (1 / 2 : ℝ))))
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div (Nat.cast_ne_zero.mpr hn) (Real.exp_ne_zero _), Real.log_exp] at h
  rw [Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn)] at h
  unfold factorialLogRemainder
  linear_combination h / n

theorem tendsto_factorialLogRemainder_mul_div (c : ℕ) :
    Tendsto (fun t : ℕ => factorialLogRemainder (t * c) / (t : ℝ))
      atTop (𝓝 0) := by
  by_cases hc : c = 0
  · simp_all [factorialLogRemainder]
  simpa only [Function.comp_def, Nat.cast_mul, ← div_div,
    div_mul_cancel₀ _ ((show (c : ℝ) ≠ 0 by exact_mod_cast hc)), zero_mul, id_eq] using
    (tendsto_factorialLogRemainder_div.comp
      (tendsto_id.atTop_mul_const' (Nat.pos_of_ne_zero hc))).mul_const (c : ℝ)
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Polynomial/ComplexPolynomialDegenerationComposition -/
/-! Polynomial tensor restrictions and exact coefficient extraction. -/

namespace Tensor

variable {F : Type*} [CommRing F]

structure PolynomialRestrictionDegeneration
    (T : Tensor F X Y Z) (U : Tensor F X' Y' Z') (k : ℕ) where
  leftMap : X' → X → Polynomial F
  middleMap : Y' → Y → Polynomial F
  rightMap : Z' → Z → Polynomial F
  coeff : ∀ x' y' z' j, j ≤ k →
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff j =
        if j = k then U x' y' z' else 0

/-- A binary triangular support filtration is a degree-one polynomial degeneration. -/
def PolynomialRestrictionDegeneration.triangular (T : Tensor F X Y Z) (p : Y → Prop) (q : Z → Prop)
    [DecidablePred p] [DecidablePred q]
    (h : ∀ x y z, q z → ¬p y → T x y z = 0) :
    PolynomialRestrictionDegeneration T (fun x y z => if p y ↔ q z then T x y z else 0) 1 := by

  refine ⟨(fun x i => if i = x then 1 else 0),
    (fun y i => if i = y then if p y then Polynomial.X else 1 else 0),
    (fun z i => if i = z then if q z then 1 else Polynomial.X else 0), ?_⟩
  intro x y z n hn
  interval_cases n <;> by_cases hp : p y <;> by_cases hq : q z <;>
    simp_all [restrict]

end Tensor

end Foundation
open Foundation

namespace Arithmetic

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Arithmetic/Complexity -/
/-! Division-free arithmetic programs over a ring and their operation counts. -/

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Arithmetic/Programs -/
section
/-! Division-free arithmetic programs over a ring and their operation counts. -/

namespace Gate

variable {R S : Type*}

def map (f : Input → Input' ⊕ F) (ρ : R → S) : Gate F Input R → Gate F Input' S
  | .constant z => .constant z
  | .input i => match f i with
    | .inl j => .input j
    | .inr z => .constant z
  | .add i j => .add (ρ i) (ρ j)
  | .sub i j => .sub (ρ i) (ρ j)
  | .mul i j => .mul (ρ i) (ρ j)

variable (g : Gate F Input R) (f : Input → Input' ⊕ F) (ρ : R → S)

@[simp] theorem eval_map (inputs : Input' → F) (registers : S → F) :
    (g.map f ρ).eval inputs registers =
      g.eval (fun i => Sum.elim inputs id (f i)) (fun j => registers (ρ j)) := by
  aesop (add simp [map, eval])

@[simp] theorem cost_map : (g.map f ρ).cost = g.cost := by
  aesop (add simp [map])

end Gate

namespace Program

def append {r : ℕ} (p : Program F Input r) : {s : ℕ} → Program F Input s → Program F Input (r + s)
  | 0, .nil => p
  | s + 1, .step q g => (p.append q).step (g.map Sum.inl (Fin.castLE (Nat.le_add_left s r)))

variable {r s : ℕ} (p : Program F Input r) (q : Program F Input s)

theorem eval_append_new
    (inputs : Input → F) :
    ∀ i : Fin s, (p.append q).eval inputs (i.castLE (Nat.le_add_left s r)) = q.eval inputs i := by
  induction q with
  | nil => simp_all
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp_all [append,  eval]
    aesop

theorem eval_append_old
    (inputs : Input → F) :
    ∀ i : Fin r, (p.append q).eval inputs (i.addNat s) = p.eval inputs i := by
  induction q with
  | nil => aesop
  | @step s q g ih => assumption

@[simp] theorem cost_append    :
    (p.append q).cost = p.cost + q.cost := by
  induction q with
  | nil => ac_rfl
  | @step s q g ih => simp [append, cost, ih, Nat.add_assoc]

end Program
end

end Arithmetic

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Growth/PolynomialOverhead -/
section
/-!
# Removing polynomial overhead from exponential inequalities

The interpolation argument in Section 4 bounds tensor powers with an extra
linear factor. Such a factor does not change their exponential growth rate.
The statements below include eventual inequalities and constant factors, so
the same argument also removes fixed counting losses in entropy limits.
-/

open Filter

/-- An eventual quadratic prefactor does not change an exponential growth rate. -/
theorem le_of_eventually_pow_le_quadratic_mul_pow {a b A B C : ℝ}
    (ha : 0 ≤ a)
    (h : ∀ᶠ n : ℕ in atTop, b ^ n ≤ ((n : ℝ) ^ 2 * A + n * B + C) * a ^ n) :
    b ≤ a := by
  by_contra hba
  have hab  := lt_of_not_ge hba
  have hb  := lt_of_le_of_lt ha hab
  have hr₀  := div_nonneg ha hb.le
  have hr₁  := (div_lt_one hb).2 hab
  have hquadratic := (tendsto_pow_const_mul_const_pow_of_lt_one 2 hr₀ hr₁).mul_const A
  have hlinear := (tendsto_self_mul_const_pow_of_lt_one hr₀ hr₁).mul_const B
  have hconstant := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).const_mul C
  have hlim : Tendsto (fun n : ℕ =>
      (n ^ 2 * A + n * B + C) * (a / b) ^ n) atTop (𝓝 0) := by
    convert (hquadratic.add hlinear).add hconstant using 1 <;> try simp
    funext
    ring
  have hbound : ∀ᶠ n : ℕ in atTop,
      1 ≤ (n ^ 2 * A + n * B + C) * (a / b) ^ n := by
    filter_upwards [h] with n hn
    have hdiv := (div_le_div_iff_of_pos_right (pow_pos hb n)).2 hn
    simpa only [div_self (pow_ne_zero n hb.ne'), mul_div_assoc, div_pow] using hdiv
  have hfalse  := ge_of_tendsto hlim hbound
  linarith

/-- The product of the two local degree bounds is a harmless overhead. -/
theorem le_of_pow_le_const_sq_mul_pow {a b A C : ℝ}
    (ha : 0 ≤ a)
    (h : ∀ n : ℕ, b ^ n ≤ C * ((n : ℝ) * A + 1) ^ 2 * a ^ n) :
    b ≤ a := by
  apply le_of_eventually_pow_le_quadratic_mul_pow
    (A := C * A * A) (B := C * (A + A))  ha
  apply Eventually.of_forall
  intro n
  convert h n using 1 <;> ring

/-- Fixed multiplicative losses disappear on taking exponential growth rates. -/
theorem le_of_eventually_pow_le_const_mul_pow {a b C : ℝ} (ha : 0 ≤ a)
    (h : ∀ᶠ j : ℕ in atTop, b ^ j ≤ C * a ^ j) : b ≤ a := by
  apply le_of_eventually_pow_le_quadratic_mul_pow (A := 0) (B := 0)  ha
  aesop
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Arithmetic/ExponentComparison -/
section
/-!
# Comparing power growth

The last scalar step of the auxiliary-separation argument compares a
fourth-power lower bound for the cube of the diagonal profile with its
dimension upper bound.  Powers of two suffice to compare the exponents, so
the argument needs no asymptotic estimates or approximation of constants.
-/

open Filter

/-- A uniform bound on all positive natural inputs forces the exponent on
the left to be no larger than the exponent on the right. -/
theorem rpow_exponent_le_of_nat_bound {a b C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ a ≤ C * (n : ℝ) ^ b) :
    a ≤ b := by
  apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp
  apply le_of_eventually_pow_le_const_mul_pow (C := C) (by positivity)
  apply Filter.Eventually.of_forall
  intro n
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] using
    hbound (2 ^ n) (Nat.one_le_pow' n 1)
end

end AuxiliarySeparation

namespace Arithmetic

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Arithmetic/LowerBound -/
section
/-! Division-free arithmetic programs over a ring and their operation counts. -/

namespace Program

variable {F : Type*}

def registerCost : {r : ℕ} → Program F Input r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _, .step p g => Fin.cases g.cost p.registerCost

theorem sum_registerCost {r : ℕ} (p : Program F Input r) :
    ∑ i, p.registerCost i = p.cost := by
  induction p with
  | nil => ac_rfl
  | step p g ih => simp [registerCost, cost, Fin.sum_univ_succ, ih, Nat.add_comm]

theorem eval_eq_constant_or_input_of_registerCost_eq_zero [Ring F]
    {r : ℕ} (p : Program F Input r) (i : Fin r) (hi : p.registerCost i = 0) :
    (∃ z : F, ∀ inputs, p.eval inputs i = z) ∨
      ∃ a : Input, ∀ inputs, p.eval inputs i = inputs a := by
  induction p with
  | nil => exact Fin.elim0 i
  | step p g ih =>
    cases i using Fin.cases with
    | zero => aesop (add simp [registerCost, Gate.cost])
    | succ i => exact ih i hi

end Program

namespace MatrixAlgorithm

variable [Nontrivial F] {a b c : ℕ}

variable (P : MatrixAlgorithm F a b c)

variable (hb : 1 ≤ b) (hP : P.Correct)

include hb hP in
theorem output_size_le_cost : a * c ≤ P.cost := by

  let j : Fin b := ⟨0, by omega⟩
  have hinj : Function.Injective fun o : Fin a × Fin c => P.output o.1 o.2 := by
    intro x y hxy
    let A := Matrix.single x.1 j (1 : F)
    let B := Matrix.single j x.2 (1 : F)
    have h := congrArg (P.program.eval (matrixInputs A B)) hxy
    change P.eval A B x.1 x.2 = P.eval A B y.1 y.2 at h
    rw [hP] at h
    simpa [A, B, Matrix.single_apply, Prod.ext_iff] using h
  have hone (i : Fin a) (k : Fin c) :
      1 ≤ P.program.registerCost (P.output i k) := by
    by_contra hn
    have hzero : P.program.registerCost (P.output i k) = 0 := by omega
    have hentry A B :
        P.program.eval (matrixInputs A B) (P.output i k) = (A * B) i k :=
      congrFun (congrFun (hP A B) i) k
    rcases P.program.eval_eq_constant_or_input_of_registerCost_eq_zero
        (P.output i k) hzero with ⟨z, hz⟩ | ⟨u, hu⟩
    · have h0 := hentry 0 0
      have h1 := hentry (Matrix.single i j (1 : F)) (Matrix.single j k (1 : F))
      simp_all
    · rcases u with ⟨x, y⟩ | ⟨y, z⟩
      · have h := hentry (Matrix.of fun _ _ => 1) 0
        simp_all [matrixInputs]
      · have h := hentry 0 (Matrix.of fun _ _ => 1)
        simp_all [matrixInputs]
  rw [MatrixAlgorithm.cost, ← P.program.sum_registerCost]
  simpa using Finset.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ)
    (g := P.program.registerCost) (fun o : Fin a × Fin c => P.output o.1 o.2)
    hinj.injOn (Finset.subset_univ _)
    (fun o _ => hone o.1 o.2) (by simp)

end MatrixAlgorithm

theorem admissibleExponent_two_le {F : Type*} [Ring F] [Nontrivial F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨C, _, hC⟩ := hτ ε hε
  apply AuxiliarySeparation.rpow_exponent_le_of_nat_bound
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hC n hn
  refine le_trans ?_ hcost
  rw [Real.rpow_two, pow_two]
  exact_mod_cast P.output_size_le_cost hn hP

universe u

theorem admissibleExponent_bddBelow (R : Type u) [Ring R] [Nontrivial R] :
    BddBelow {τ : ℝ | AdmissibleExponent R τ} :=
  ⟨2, fun _ h => admissibleExponent_two_le h⟩
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Arithmetic/ProgramComposition -/
section
/-! Division-free arithmetic programs over a ring and their operation counts. -/

namespace Program

def mapSource (f : Input → Input' ⊕ F) : {r : ℕ} → Program F Input r → Program F Input' r
  | 0, .nil => .nil
  | _, .step p g => (p.mapSource f).step (g.map f id)

variable (f : Input → Input' ⊕ F) {r : ℕ} (p : Program F Input r)

@[simp] theorem eval_mapSource
     (inputs : Input' → F) :
    ∀ i : Fin r, (p.mapSource f).eval inputs i =
      p.eval (fun j => Sum.elim inputs id (f j)) i := by
  induction p with
  | nil => simp_all
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp_all [mapSource, eval, ]
    · exact ih j

@[simp] theorem cost_mapSource
     : (p.mapSource f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp  [mapSource, cost,  ih]

structure Substituted {r s : ℕ} (p : Program F Input r) (q : Program F Mid s)
    (wires : Mid → Fin r) where
  program : Program F Input (r + s)
  output : Fin s → Fin (r + s)
  correctOld : ∀ inputs i, program.eval inputs (i.addNat s) = p.eval inputs i
  correct : ∀ inputs i, program.eval inputs (output i) =
    q.eval (fun j => p.eval inputs (wires j)) i
  cost_eq : program.cost = p.cost + q.cost

def substitute {r : ℕ} (p : Program F Input r) :
    {s : ℕ} → (q : Program F Mid s) → (wires : Mid → Fin r) → Substituted p q wires
  | 0, .nil, wires =>
    { program := p
      output := Fin.elim0
      correctOld := fun _ _ => rfl
      correct := fun _ i => Fin.elim0 i
      cost_eq := rfl }
  | s + 1, .step q g, wires =>
    let a := substitute p q wires
    { program := a.program.step (g.map (fun _ => .inr 0) a.output)
      output := Fin.cases (match g with
        | .input j => ((wires j).addNat s).succ
        | _ => 0) (fun i => (a.output i).succ)
      correctOld := a.correctOld
      correct := by
        intro inputs i
        refine Fin.cases ?_ (fun j => ?_) i
        · cases g <;> simp [Gate.map, Gate.eval, eval, a.correct, a.correctOld]
        · exact a.correct inputs j
      cost_eq := by simp [cost, a.cost_eq, Nat.add_assoc] }

end Program
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Arithmetic/Padding -/
section

namespace MatrixAlgorithm

/-- Zero padding restricts square multiplication without adding arithmetic gates. -/
theorem exists_restrict {m n : ℕ} (hmn : m ≤ n)
    (P : MatrixAlgorithm F n n n) (hP : P.Correct) :
    ∃ Q : MatrixAlgorithm F m m m, Q.Correct ∧ Q.cost ≤ P.cost := by
  let padSource (x : MatrixInput n n n) : MatrixInput m m m ⊕ F :=
    let p := x.elim id id
    if h : p.1.val < m ∧ p.2.val < m then
      .inl ((if x.isLeft then Sum.inl else Sum.inr) (⟨p.1.val, h.1⟩, ⟨p.2.val, h.2⟩))
    else .inr 0
  refine ⟨⟨P.registers, P.program.mapSource padSource,
    fun i k => P.output (Fin.castLE hmn i) (Fin.castLE hmn k)⟩, ?_,
    (Program.cost_mapSource padSource P.program).le⟩
  intro M N
  let f  := fun x => Sum.elim (matrixInputs M N) id (padSource x)
  let M'  := fun i j => f (.inl (i, j))
  let N'  := fun j k => f (.inr (j, k))
  have hf : matrixInputs M' N' = f := by aesop
  funext i k
  change (P.program.mapSource padSource).eval
    (matrixInputs M N) (P.output (Fin.castLE hmn i) (Fin.castLE hmn k)) = _
  rw [Program.eval_mapSource]
  have h := congrFun (congrFun (hP M' N') (Fin.castLE hmn i)) (Fin.castLE hmn k)
  simp  [MatrixAlgorithm.eval, hf] at h
  apply h.trans
  symm
  apply Fintype.sum_of_injective (Fin.castLE hmn) (Fin.castLE_injective hmn)
  · intro j hj
    by_cases hjm : j.val < m
    · simp_all +zetaDelta
    · simp [M',  f, padSource, hjm]
  aesop

end MatrixAlgorithm
end

end Arithmetic

namespace Arithmetic.RecursiveBlock

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Arithmetic/RecursiveBlockPrograms -/
/-! Division-free arithmetic programs over a ring and their operation counts. -/

structure Family (F Input Output : Type*) where
  registers : ℕ
  program : Program F Input registers
  output : Output → Fin registers

namespace Family

variable (p : Family F Input Output)

def eval  (inputs : Input → F) (o : Output) : F :=
  p.program.eval inputs (p.output o)

def cost := p.program.cost

variable (p : Family F Input Mid) (q : Family F Mid Output)

def compose   : Family F Input Output :=
  let s := p.program.substitute q.program p.output
  ⟨_, s.program, fun o => s.output (q.output o)⟩

theorem eval_compose
    (inputs : Input → F) (o : Output) :
    (compose p q).eval inputs o = q.eval (p.eval inputs) o :=
  (p.program.substitute q.program p.output).correct inputs (q.output o)

variable {NewInput : Type*} (f : Input → NewInput) (p : Family F Input Output)

def mapInputs    :
    Family F NewInput Output :=
  ⟨p.registers, p.program.mapSource (Sum.inl ∘ f), p.output⟩

def parallel : (r : ℕ) → (Fin r → Family F Input Output) → Family F Input (Fin r × Output)
  | 0, _ => ⟨0, Program.nil, fun o => Fin.elim0 o.1⟩
  | r + 1, p =>
    let head := p 0
    let tail := parallel r fun i => p i.succ
    { registers := head.registers + tail.registers
      program := head.program.append tail.program
      output := fun o => Fin.cases
        ((head.output o.2).addNat tail.registers)
        (fun i => (tail.output (i, o.2)).castLE (Nat.le_add_left _ _)) o.1 }

variable (r : ℕ) (p : Fin r → Family F Input Output)

theorem eval_parallel
    (inputs : Input → F) (o : Fin r × Output) :
    (parallel r p).eval inputs o = (p o.1).eval inputs o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Program.eval_append_old _ _ inputs _
    · exact (Program.eval_append_new _ _ inputs _).trans
        (ih (fun j => p j.succ) (j, o))

theorem cost_parallel : (parallel r p).cost = ∑ i, (p i).cost := by
  induction r <;> simp_all [parallel, cost, Program.cost, Program.cost_append, Fin.sum_univ_succ]

def linearFin : (n : ℕ) → (Fin n → F) → (Fin n → Input) → Family F Input Unit
  | 0, _, _ => ⟨1, .step .nil (.constant 0), fun _ => 0⟩
  | n + 1, a, wire =>
    let p := linearFin n (fun i => a i.succ) (fun i => wire i.succ)
    ⟨p.registers + 4,
      (((p.program.step (.constant (a 0))).step (.input (wire 0))).step (.mul (Fin.succ 0) 0)).step
        (.add 0 (p.output ()).succ.succ.succ), fun _ => 0⟩

variable (n : ℕ) (a : Fin n → F) (wire : Fin n → Input)

theorem eval_linearFin    (inputs : Input → F) :
    (linearFin n a wire).eval inputs () = ∑ i, a i * inputs (wire i) := by
  induction n with
  | zero => ac_rfl
  | succ n ih =>
    change a 0 * inputs (wire 0) +
      (linearFin n (fun i => a i.succ) (fun i => wire i.succ)).eval inputs () = _
    rw [ih, Fin.sum_univ_succ]

theorem cost_linearFin : (linearFin n a wire).cost = 2 * n := by
  induction n <;> simp_all [linearFin, cost, Program.cost, Gate.cost, Nat.mul_add, Nat.add_assoc]

def linear [Fintype Term] (a : Term → F) (wire : Term → Input) : Family F Input Unit :=
  linearFin (Fintype.card Term) (a ∘ (Fintype.equivFin Term).symm)
    (wire ∘ (Fintype.equivFin Term).symm)

theorem eval_linear [Fintype Term] (a : Term → F) (wire : Term → Input) (inputs : Input → F) :
    (linear a wire).eval inputs () = ∑ i, a i * inputs (wire i) := by
  rw [linear, eval_linearFin]
  exact (Fintype.equivFin Term).symm.sum_comp fun i => a i * inputs (wire i)

def collect [Fintype Output] (p : Output → Family F Input Unit) : Family F Input Output :=
  let e := Fintype.equivFin Output
  let q := parallel (Fintype.card Output) fun i => p (e.symm i)
  ⟨q.registers, q.program, fun o => q.output (e o, ())⟩

theorem eval_collect [Fintype Output] (p : Output → Family F Input Unit)
    (inputs : Input → F) (o : Output) :
    (collect p).eval inputs o = (p o).eval inputs () := by
  change (parallel (Fintype.card Output) _).eval inputs ((Fintype.equivFin Output) o, ()) = _
  simp_all [eval_parallel]

theorem cost_collect [Fintype Output] (p : Output → Family F Input Unit) :
    (collect p).cost = ∑ o, (p o).cost := by
  change (parallel (Fintype.card Output) _).cost = _
  rw [cost_parallel]
  exact (Fintype.equivFin Output).symm.sum_comp fun o => (p o).cost

variable (r : ℕ) (p : Family F Input Output)

def copies :=
  parallel r fun i => p.mapInputs fun x => (i, x)

theorem eval_copies
    (inputs : Fin r × Input → F) (o : Fin r × Output) :
    (copies r p).eval inputs o = p.eval (fun x => inputs (o.1, x)) o.2 := by
  rw [copies, eval_parallel]
  exact Program.eval_mapSource _ _ _ _

variable {m : ℕ}

variable (p : MatrixAlgorithm F m m m)

def ofMatrix   :
    Family F (MatrixInput m m m) (Fin m × Fin m) :=
  ⟨p.registers, p.program, fun o => p.output o.1 o.2⟩

theorem eval_ofMatrix (hp : p.Correct)
    (inputs : MatrixInput m m m → F) (o : Fin m × Fin m) :
    (ofMatrix p).eval inputs o =
      ∑ j, inputs (.inl (o.1, j)) * inputs (.inr (j, o.2)) := by
  convert congr($(hp (fun i j => inputs (.inl (i, j)))
    (fun j k => inputs (.inr (j, k)))) o.1 o.2) using 1
  dsimp only [eval, ofMatrix, MatrixAlgorithm.eval]
  congr 1
  funext x
  rcases x with ⟨i, j⟩ | ⟨j, k⟩ <;> rfl
  all_goals rfl

end Family

variable {n m r : ℕ}

def join {n m : ℕ} (i : Fin n) (j : Fin m) := finProdFinEquiv (i, j)

/-- An integer rank scheme supplies a recursive block step over every
associative unital ring. No commutativity of input values is assumed. -/
theorem int_rank_block_step
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n)) r)
    (p : MatrixAlgorithm F m m m) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm F (n * m) (n * m) (n * m), q.Correct ∧
      q.cost = r * p.cost +
        6 * r * n ^ 2 * m ^ 2 := by
  rcases h with ⟨a, b, c, h⟩
  let inputFamily := Family.collect fun v : Fin r × MatrixInput m m m =>
    let p := v.2.elim id id
    Family.linear (fun x => ((bif v.2.isLeft then a else b) v.1 x : F))
      fun x => (bif v.2.isLeft then Sum.inl else Sum.inr) (join x.1 p.1, join x.2 p.2)
  let outputFamily := Family.collect fun o : Fin (n * m) × Fin (n * m) =>
    Family.linear (fun q => (c q ((finProdFinEquiv.symm o.2).1, (finProdFinEquiv.symm o.1).1) : F))
      fun q => (q, ((finProdFinEquiv.symm o.1).2, (finProdFinEquiv.symm o.2).2))
  let f := (inputFamily.compose (Family.copies r (Family.ofMatrix p))).compose outputFamily
  refine ⟨⟨f.registers, f.program, fun i k => f.output (i, k)⟩, ?_, ?_⟩
  · intro A B
    funext i k
    obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
    change f.eval (matrixInputs A B) (join i s, join k u) = _
    dsimp only [f]
    rw [Family.eval_compose]
    simp only [outputFamily, Family.eval_collect, Family.eval_linear, join]
    simp_rw [Family.eval_compose, Family.eval_copies, Family.eval_ofMatrix _ hp,
      inputFamily, Family.eval_collect, Family.eval_linear, matrixInputs]
    dsimp only [Sum.isLeft, cond]
    conv_lhs =>
      arg 2
      ext q
      rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc]
    trans ∑ t : Fin m, ∑ j : Fin n, A (join i s) (join j t) * B (join j t) (join k u)
    · apply Finset.sum_congr rfl
      intro t _
      have hcentral (u v w  ) (x y  ) :
          w * (u * x) * (v * y) =
            ((u * v * w : ℤ) : F) * x * y := by
        simp  [← zsmul_eq_mul,   smul_smul]
        ring
      have hcoeff x y
          z :
          ∑ q, ((a q x * b q y * c q z : ℤ) : F) =
            ((Tensor.matrixCoefficients (K := ℤ) (Fin n) (Fin n) (Fin n) x y z  )  ) := by
        simpa [Tensor.rankOne] using
          congrArg (Int.castRingHom F) (congr($h x y z)).symm
      simp only [Finset.sum_mul, Finset.mul_sum, hcentral]
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2
        ext y
        rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcoeff]
      simp [Fintype.sum_prod_type, ite_and]
    · rw [Finset.sum_comm]
      exact (Fintype.sum_prod_type _).symm.trans
        (finProdFinEquiv.sum_comp fun j => A (join i s) j * B j (join k u))

  · simp  [f, MatrixAlgorithm.cost, Family.compose, Program.Substituted.cost_eq]
    change Family.cost _ + Family.cost _ + Family.cost _ = _
    simp  [inputFamily, outputFamily, Family.cost_collect, Family.copies, Family.linear, Family.cost_parallel,
      Family.cost_linearFin, Fintype.card_prod, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ]
    all_goals simp [Family.cost, Family.mapInputs, Family.ofMatrix]
    all_goals ring

end Arithmetic.RecursiveBlock

namespace Foundation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/Separation/ComplexTypeCounting -/
/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

variable {A : Type*} [Fintype A] [DecidableEq A]

variable (counts : A → ℕ)

abbrev ExactWords  :=
  {w : Fin (∑ a, counts a) → A // ∀ a, Fintype.card {i // w i = a} = counts a}

instance exactWords_nonempty  : Nonempty (ExactWords counts) := by
  let e : Fin (∑ a, counts a) ≃ Σ a, Fin (counts a) :=
    Fintype.equivOfCardEq (by simp)
  refine ⟨⟨(fun i : Σ a, Fin (counts a) => i.1) ∘ e, ?_⟩⟩
  intro a
  simpa using Fintype.card_congr
    ((Equiv.subtypeEquiv e fun _ => Iff.rfl).trans (Equiv.sigmaSubtype a))

theorem exactWords_card :
    Fintype.card (ExactWords counts) = Nat.multinomial Finset.univ counts := by

  obtain ⟨w⟩ := exactWords_nonempty counts
  let I := Fin (∑ a, counts a)
  let G := DomMulAct (Equiv.Perm I)
  let := Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  let eOrbit : ExactWords counts ≃ MulAction.orbit G w.val :=
    Equiv.subtypeEquivRight fun v => by
      constructor
      · intro h
        let es := fun a => Fintype.equivOfCardEq ((h a).trans (w.property a).symm)
        exact ⟨DomMulAct.mk (Equiv.ofFiberEquiv es), funext (Equiv.ofFiberEquiv_map es)⟩
      · rintro ⟨g, rfl⟩ a
        exact (Fintype.card_congr (Equiv.subtypeEquiv (DomMulAct.mk.symm g) fun _ => Iff.rfl)).trans (w.property a)
  let eStab : MulAction.stabilizer G w.val ≃
      {e : Equiv.Perm I // w.val ∘ e = w.val} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm fun _ => DomMulAct.mem_stabilizer_iff
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w.val
  rw [← Fintype.card_congr eOrbit, Fintype.card_congr eStab,
    DomMulAct.stabilizer_card, Fintype.card_congr DomMulAct.mk.symm, Fintype.card_perm] at h
  have hp := w.property
  simp  [I, hp] at h
  exact Nat.eq_div_of_mul_eq_left
    (ne_of_gt (Nat.prod_factorial_pos Finset.univ counts)) h

end Foundation

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Convolution/Basic -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# The polynomial multiplication tensor

The coefficient tensor `convolution a b` represents multiplication of binary forms
of degrees `a - 1` and `b - 1`, or equivalently ordinary coefficient convolution.
The output leg has `a + b - 1` coordinates.  The definitions also make sense when
an input dimension is zero, while the nonzero and full-output-support statements
use the positive dimensions assumed in Section 5 of the paper.
-/

/-- The tensor `C(a,b)` of Section 5, in monomial coefficient coordinates. -/
def convolution (a b : ℕ) : Tensor K (Fin a) (Fin b) (Fin (a + b - 1)) :=
  fun i j k => if i.val + j.val = k.val then 1 else 0

end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Convex/ConeSupport -/
section
variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A minimal nonnegative representation has independent support. -/
theorem exists_linearIndependent_subcone [Fintype I] (A : I → E) {x : E}
    (hx : x ∈ PointedCone.hull ℝ (Set.range A)) :
    ∃ s : Finset I, LinearIndependent ℝ (fun i : s ↦ A i) ∧
      x ∈ PointedCone.hull ℝ (Set.range fun i : s ↦ A i) := by

  let P s := ∃ w : I → ℝ, (∀ i ∈ s, 0 ≤ w i) ∧ ∑ i ∈ s, w i • A i = x
  have hP : P Finset.univ := by
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (Nonneg ℝ)).mp hx
    exact ⟨fun i => w i, fun i _ => (w i).2, hw⟩
  obtain ⟨s, hmin⟩ := exists_minimalFor_of_wellFoundedLT P Finset.card ⟨_, hP⟩
  obtain ⟨w, hw, heq⟩ := hmin.prop
  refine ⟨s, ?_, ?_⟩
  · by_contra h
    obtain ⟨g, hg, i, hi, hgi⟩ :=
      not_linearIndepOn_finset_iff (R := ℝ) (v := A).mp h
    have hrel : ∃ g : I → ℝ, ∑ i ∈ s, g i • A i = 0 ∧ ∃ i ∈ s, 0 < g i := by
      rcases lt_or_gt_of_ne hgi with hn | hp
      · exact ⟨fun j => -g j, by simp_all +zetaDelta, i, hi, neg_pos.mpr hn⟩
      aesop
    obtain ⟨g, hg, i, hi, hgi⟩ := hrel
    let p := s.filter fun i => 0 < g i
    obtain ⟨i₀, hi₀, hratio⟩ : ∃ i₀ ∈ p, ∀ j ∈ p, w i₀ / g i₀ ≤ w j / g j :=
      p.exists_min_image _ ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
    have his := (Finset.mem_filter.mp hi₀).1
    have hgi₀ := (Finset.mem_filter.mp hi₀).2
    let v := fun j => w j - w i₀ / g i₀ * g j
    have hv₀ : v i₀ = 0 := by grind [ne_of_gt]
    apply hmin.not_prop_of_lt (Finset.card_erase_lt_of_mem his)
    refine ⟨v, ?_, ?_⟩
    · intro j hj
      have hjs := Finset.mem_of_mem_erase hj
      apply sub_nonneg.mpr
      by_cases hjp : j ∈ p
      · exact (le_div_iff₀ (Finset.mem_filter.mp hjp).2).mp (hratio j hjp)
      · have hgj : g j ≤ 0 := by simp_all +zetaDelta
        exact (mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg (hw i₀ his) hgi₀.le) hgj).trans (hw j hjs)
    · calc
        _ = ∑ j ∈ s, v j • A j := Finset.sum_erase _ (by exact?)
        _ = x := by
          simp  [v, sub_smul, mul_smul,
            ← Finset.smul_sum, hg,   heq]
  · rw [← heq]
    apply Submodule.sum_mem
    intro i hi
    exact PointedCone.smul_mem _ (hw i hi) (PointedCone.subset_hull ⟨⟨i, hi⟩, rfl⟩)
end

end AuxiliarySeparation

namespace AuxiliarySeparation.Sector

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Sector/Weights -/
/-!
# Interval weights for the three-sector convolution degeneration

Section 5.2 assigns weights to the second and third coordinates of
`C(a, 3 * h + a - 1)`. The total weight is nonnegative on convolution support,
and its zero set consists exactly of the three matching sector blocks.
The middle block is a convolution with the last two legs exchanged and the
first coordinate reversed.
-/

/-- Number of second-leg coordinates in the original convolution. -/
def sourceWidth (a h : ℕ) := 3 * h + a - 1

/-- Beginning of the right sector on both the second and third legs. -/
def rightStart (a h : ℕ) := 2 * h + a - 1

/-- The middle interval on the second tensor leg. -/
def MiddleY (a h j : ℕ) := h ≤ j ∧ j < rightStart a h

/-- The middle interval on the third tensor leg. -/
def MiddleZ (a h k : ℕ) := h + a - 1 ≤ k ∧ k < rightStart a h

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Sector/Degeneration -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# The actual three-sector polynomial degeneration

The interval weights of `SectorWeights` act by diagonal local maps on the
coefficient tensor `C(a, 3h+a-1)`. Shifting every third-leg weight by one makes
the local maps polynomial. Their leading coefficient is the retained tensor, so the existing
polynomial-restriction degeneration interface applies with leading order one and local degree bounds `(0,1,1)`.
-/

open Polynomial

abbrev YIndex (a h : ℕ) := Fin (sourceWidth a h)
abbrev ZIndex (a h : ℕ) := Fin (a + sourceWidth a h - 1)

/-- The source coefficient tensor, with its actual shared first-input space. -/
def source (a h : ℕ) : Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  convolution  a (sourceWidth a h)

/-- Label a second-leg coordinate by its interval. -/
def yLabel (a h : ℕ) (j : YIndex a h) : Fin 3 :=
  if j.val < h then 0 else if j.val < rightStart a h then 1 else 2

/-- Label a third-leg coordinate by its corresponding interval. -/
def zLabel (a h : ℕ) (k : ZIndex a h) : Fin 3 :=
  if k.val < h + a - 1 then 0 else if k.val < rightStart a h then 1 else 2

/-- The weight-zero part in the original coordinate spaces. -/
def retained (a h : ℕ) : Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if MiddleY a h j.val ↔ MiddleZ a h k.val then source  a h i j k else 0

/-- Retain the coefficient in precisely its matching labelled branch. -/
def branchFamily (a h : ℕ) (b : Fin 3) :
    Tensor ℤ (Fin a) (YIndex a h) (ZIndex a h) :=
  fun i j k => if yLabel a h j = b ∧ zLabel a h k = b then source  a h i j k else 0

theorem branchFamily_labels {a h : ℕ} {b : Fin 3} {i : Fin a}
    {j : YIndex a h} {k : ZIndex a h} (hn : branchFamily  a h b i j k ≠ 0) :
    yLabel a h j = b ∧ zLabel a h k = b := by
  simp_all [branchFamily]

theorem sum_branchFamily (a h : ℕ) :
    ∑ b : Fin 3, branchFamily  a h b = retained  a h := by
  funext i j k
  by_cases hs : source  a h i j k = 0
  · simp [branchFamily, retained, hs]
  · simp [source, convolution] at hs
    simp [ branchFamily, retained, ite_and]
    grind [yLabel, zLabel, MiddleY, MiddleZ, rightStart]

/-- The interval filtration is triangular on convolution support. -/
def restriction (a h : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (source a h) (retained  a h) 1 :=
  Tensor.PolynomialRestrictionDegeneration.triangular (source a h) (fun j => MiddleY a h j.val)
    (fun k => MiddleZ a h k.val) (by
      intro i j k hz hy
      by_contra hn
      simp [source, convolution] at hn
      grind [MiddleY, MiddleZ, rightStart])
end

end AuxiliarySeparation.Sector

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/MatrixMultiplication -/
section

/-- The matrix multiplication coefficient tensor over an arbitrary scalar field.
At `K = ℂ` this is definitionally the repository's original
`Foundation.Tensor.matrixMultiplication`. -/
def matrixMultiplicationTensor (a b c : ℕ) :=
  Tensor.matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c)
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/DirectSum -/
section
/-!
# Binary sums of finite coefficient tensors

The coordinate types of the summands may differ.  The identities below give
the explicit changes of coordinates needed for the tensor semiring, together
with the block-diagonal restriction maps.
-/

/-- The scalar multiplication tensor, the multiplicative unit. -/
def unitTensor : Tensor K PUnit PUnit PUnit := fun _ _ _ => 1

/-- The direct sum of `r` scalar multiplication tensors, in diagonal coordinates. -/
def scalarTensor (r : ℕ) : Tensor K (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ i = k then 1 else 0

/-- The binary direct sum, with each of its three block labels retained. -/
def sumTensor (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X ⊕ U) (Y ⊕ V) (Z ⊕ W)
  | .inl x, .inl y, .inl z => T x y z
  | .inr u, .inr v, .inr w => S u v w
  | _, _, _ => 0
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Arithmetic/RankExponent -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Exact tensor rank and its matrix multiplication exponent

The rank is the least size of an exact decomposition into simple tensors. The
exponent is the infimum of the finite matrix multiplication rank ratios from
Section 3; no attainment of this real infimum is assumed.
-/

/-- Every finite coefficient tensor has a finite exact rank decomposition. -/
theorem exists_rankAtMost
    (T : Tensor K X Y Z) : ∃ r : ℕ, Tensor.RankAtMost T r := by

  refine ⟨Fintype.card (X × Y), ?_⟩
  convert Tensor.rankAtMost_sum_rankOne
    (fun (p : X × Y) x => if x = p.1 then 1 else 0)
    (fun p y => if y = p.2 then 1 else 0)
    (fun p z => T p.1 p.2 z) using 1
  simp_all [Fintype.sum_prod_type]

/-- Exact rank of a finite tensor over the coefficient semiring. -/
def exactRank
    (T : Tensor K X Y Z) : ℕ :=
  Nat.find (exists_rankAtMost T)

/-- The least exact rank comes with an actual rank decomposition. -/
theorem exactRank_spec
    (T : Tensor K X Y Z) : Tensor.RankAtMost T (exactRank T) :=
  Nat.find_spec (exists_rankAtMost T)

/-- Every exact decomposition bounds the least rank. -/
theorem exactRank_le
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) : exactRank T ≤ r :=
  Nat.find_min' (exists_rankAtMost T) h

/-- Exact rank of the square matrix multiplication tensor. -/
def exactMatrixRank (n : ℕ) : ℕ := exactRank (matrixMultiplicationTensor (K := ℤ) n n n)

variable {n : ℕ}

theorem exactMatrixRank_lower  (hn : 0 < n) : n ^ 2 ≤ exactMatrixRank n := by
  let j : Fin n := ⟨0, hn⟩
  simpa [exactMatrixRank, pow_two] using
    (exactRank_spec (matrixMultiplicationTensor (K := ℤ) n n n)).card_le_of_identity
      (fun i : Fin n × Fin n => (i.2, j))
      (fun i : Fin n × Fin n => (j, i.1)) id
      (by simp_all [matrixMultiplicationTensor, eq_comm])

theorem exactMatrixRank_pos (hn : 0 < n) : (0 : ℝ) < exactMatrixRank n := by
  exact_mod_cast (pow_pos hn 2).trans_le (exactMatrixRank_lower hn)

/-- The set of finite exact-rank exponents in the definition of `ν`. -/
def exactRankExponentSet : Set ℝ :=
  {τ | ∃ n : ℕ, 2 ≤ n ∧ τ = Real.logb n (exactMatrixRank n)}

/-- The exact-rank exponent `ν = inf_{n ≥ 2} logRTₙ/logn`. -/
def exactRankExponent : ℝ := sInf exactRankExponentSet

theorem exactRankExponentSet_nonempty : exactRankExponentSet.Nonempty :=
  ⟨Real.logb 2 (exactMatrixRank 2), 2, le_rfl, rfl⟩

theorem exactMatrixRank_logb_lower  (hn : 2 ≤ n) :
    2 ≤ Real.logb n (exactMatrixRank n) := by
  apply (Real.le_logb_iff_rpow_le (by aesop) (exactMatrixRank_pos (by omega))).mpr
  exact_mod_cast exactMatrixRank_lower (show 0 < n by omega)

theorem exactRankExponent_lower : 2 ≤ exactRankExponent :=
  le_csInf exactRankExponentSet_nonempty (by
    rintro τ ⟨n, hn, rfl⟩
    exact exactMatrixRank_logb_lower hn)

/-- A strict upper bound for the infimum is witnessed by an actual finite block. -/
theorem exists_exactMatrixRank_lt_rpow {τ : ℝ} (hτ : exactRankExponent < τ) :
    ∃ n : ℕ, 2 ≤ n ∧ (exactMatrixRank n : ℝ) < (n : ℝ) ^ τ ∧
      Tensor.RankAtMost (matrixMultiplicationTensor (K := ℤ) n n n) (exactMatrixRank n) := by
  obtain ⟨σ, ⟨n, hn, rfl⟩, hσ⟩ :=
    exists_lt_of_csInf_lt exactRankExponentSet_nonempty hτ
  refine ⟨n, hn, ?_, exactRank_spec _⟩
  exact (Real.logb_lt_iff_lt_rpow (by aesop) (exactMatrixRank_pos (by omega))).mp hσ

end

end AuxiliarySeparation

namespace AuxiliarySeparation.TensorSemiring

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/Semiring -/
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Finite tensors modulo mutual restriction

Representatives have three natural-number dimensions and coefficients in `K`.
The order is actual linear restriction, and equality in the quotient is mutual
restriction. In particular, changing coordinates does not change the class.
-/

/-- `T` is obtained from `S` by three linear maps on its coordinate spaces. -/
def IsRestriction (T : Tensor K X Y Z) (S : Tensor K U V W) : Prop :=
  ∃ (A : X → U → K) (B : Y → V → K) (C : Z → W → K),
    T = Tensor.restrict A B C S

/-- Exact rank decompositions are precisely restrictions of diagonal scalar tensors. -/
theorem rankAtMost_iff_restriction_scalar {X Y Z : Type}
    {T : Tensor K X Y Z} {r : ℕ} :
    Tensor.RankAtMost T r ↔ IsRestriction T (scalarTensor r) := by
  constructor <;> rintro ⟨A, B, C, rfl⟩ <;>
    refine ⟨Function.swap A, Function.swap B, Function.swap C, ?_⟩ <;>
    ext <;> simp_all [Tensor.restrict, scalarTensor, Function.swap, ite_and]

theorem IsRestriction.refl (T : Tensor K X Y Z) : IsRestriction T T :=
  ⟨_, _, _, Tensor.pullback_eq_restrict id id id T⟩

variable {T : Tensor K X Y Z} {S : Tensor K U V W}

theorem IsRestriction.trans
    {L : Tensor K P Q R} (hTS : IsRestriction T S) (hSL : IsRestriction S L) :
    IsRestriction T L := by
  rcases hTS with ⟨A, B, C, rfl⟩
  rcases hSL with ⟨D, E, F, rfl⟩
  refine ⟨Matrix.of A * Matrix.of D, Matrix.of B * Matrix.of E, Matrix.of C * Matrix.of F, ?_⟩
  funext
  simp  [Tensor.restrict, Matrix.mul_apply, Matrix.of_apply, mul_assoc, Finset.sum_mul]
  simp  [Finset.mul_sum]
  simp only [mul_left_comm, mul_comm]
  iterate 2 (rw [Tensor.sum_comm_three]; congr 1 with _)
  exact Tensor.sum_comm_three _

theorem IsRestriction.pullback (T : Tensor K X Y Z)
    (fx : U → X) (fy : V → Y) (fz : W → Z) :
    IsRestriction (Tensor.pullback fx fy fz T) T :=
  ⟨_, _, _, Tensor.pullback_eq_restrict fx fy fz T⟩

variable {T' : Tensor K P Q R}

theorem IsRestriction.product

       {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  refine ⟨Matrix.kronecker A D, Matrix.kronecker B E, Matrix.kronecker C F, ?_⟩
  symm
  funext
  simp  [Tensor.restrict, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul_sum, mul_comm, mul_left_comm]

theorem IsRestriction.sum

       {S' : Tensor K U' V' W'}
    (hT : IsRestriction T T') (hS : IsRestriction S S') :
    IsRestriction (sumTensor T S) (sumTensor T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  refine ⟨Matrix.fromBlocks A 0 0 D, Matrix.fromBlocks B 0 0 E, Matrix.fromBlocks C 0 0 F, ?_⟩
  aesop (add simp [Tensor.restrict, Matrix.fromBlocks, sumTensor])

theorem IsRestriction.zero (S : Tensor K U V W) :
    IsRestriction (0 : Tensor K X Y Z) S := by
  refine ⟨0, 0, 0, ?_⟩
  ext <;> simp_all [Tensor.restrict]

theorem IsRestriction.rank_le
    (h : IsRestriction T S) : exactRank T ≤ exactRank S :=
  exactRank_le (rankAtMost_iff_restriction_scalar.mpr
    (h.trans (rankAtMost_iff_restriction_scalar.mp (exactRank_spec S))))

/-- A finite tensor presentation. Arbitrary finite coordinate types avoid
unnecessary changes of basis to `Fin`. -/
structure FiniteTensor where
  X : Type
  Y : Type
  Z : Type
  [fX : Fintype X]
  [fY : Fintype Y]
  [fZ : Fintype Z]
  coeff : Tensor ℤ X Y Z

attribute [instance] FiniteTensor.fX FiniteTensor.fY FiniteTensor.fZ

namespace FiniteTensor

def ofTensor (T : Tensor ℤ X Y Z) : FiniteTensor where
  X := X
  Y := Y
  Z := Z
  coeff := T

instance : Preorder FiniteTensor where
  le T S := IsRestriction T.coeff S.coeff
  le_refl T := IsRestriction.refl T.coeff
  le_trans _ _ _ := IsRestriction.trans

end FiniteTensor

/-- Finite tensors over `ℤ`, with two presentations identified exactly when
each is a linear restriction of the other. -/
abbrev TensorClass := Antisymmetrization FiniteTensor (· ≤ ·)

/-- The quotient class of a tensor on any three finite coordinate sets. -/
def classOf
    (T : Tensor ℤ X Y Z) : TensorClass := toAntisymmetrization (· ≤ ·) (FiniteTensor.ofTensor T)

variable (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W)

theorem classOf_eq_iff
      :
    classOf T = classOf S ↔ IsRestriction T S ∧ IsRestriction S T := le_antisymm_iff

theorem classOf_eq_of_reindex
    {T : Tensor ℤ X Y Z} {S : Tensor ℤ U V W}
    (ex : X ≃ U) (ey : Y ≃ V) (ez : Z ≃ W)
    (h : Tensor.pullback ex ey ez S = T) : classOf T = classOf S :=
  by
  subst T
  apply (classOf_eq_iff _ _).mpr
  refine ⟨IsRestriction.pullback S ex ey ez, ?_⟩
  convert IsRestriction.pullback (Tensor.pullback ex ey ez S) ex.symm ey.symm ez.symm using 1
  grind [Tensor.pullback]

instance : Mul TensorClass where
  mul := Quotient.map₂ (fun T S => FiniteTensor.ofTensor (Tensor.product T.coeff S.coeff)) (by
    intro T T' hT S S' hS
    exact ⟨IsRestriction.product hT.1 hS.1,
      IsRestriction.product hT.2 hS.2⟩)

instance : Add TensorClass where
  add := Quotient.map₂ (fun T S => FiniteTensor.ofTensor (sumTensor T.coeff S.coeff)) (by
    intro T T' hT S S' hS
    exact ⟨IsRestriction.sum hT.1 hS.1, IsRestriction.sum hT.2 hS.2⟩)

instance : Zero TensorClass := ⟨classOf (0 : Tensor ℤ Empty Empty Empty)⟩
instance : One TensorClass := ⟨classOf fun (_ _ _ : PUnit.{1}) => (1 : ℤ)⟩

theorem classOf_zero :
    classOf (0 : Tensor ℤ X Y Z) = 0 :=
  (classOf_eq_iff _ _).mpr ⟨IsRestriction.zero _, IsRestriction.zero _⟩

theorem class_add_comm (a b : TensorClass) : a + b = b + a := by
  induction a, b using Quotient.inductionOn₂
  apply classOf_eq_of_reindex (Equiv.sumComm _ _) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  aesop

variable (a : TensorClass)

theorem class_add_zero  : a + 0 = a := by
  induction a using Quotient.inductionOn
  symm
  apply classOf_eq_of_reindex (Equiv.sumEmpty _ Empty).symm (Equiv.sumEmpty _ Empty).symm
    (Equiv.sumEmpty _ Empty).symm
  rfl

theorem class_mul_comm (a b : TensorClass) : a * b = b * a := by
  induction a, b using Quotient.inductionOn₂
  apply classOf_eq_of_reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  grind [FiniteTensor.ofTensor, Tensor.pullback, Tensor.product, mul_comm]

theorem class_mul_one  : a * 1 = a := by
  induction a using Quotient.inductionOn
  symm
  apply classOf_eq_of_reindex (Equiv.prodPUnit _).symm (Equiv.prodPUnit _).symm
    (Equiv.prodPUnit _).symm
  grind [FiniteTensor.ofTensor, Tensor.pullback, Tensor.product]

theorem class_mul_zero : a * 0 = 0 := by
  induction a using Quotient.inductionOn with
  | h a =>
    change classOf (Tensor.product a.coeff (0 : Tensor ℤ Empty Empty Empty)) = 0
    rw [Subsingleton.elim (Tensor.product a.coeff _) 0, classOf_zero]

theorem class_left_distrib (a b c : TensorClass) : a * (b + c) = a * b + a * c := by
  induction a, b, c using Quotient.inductionOn₃
  symm
  apply classOf_eq_of_reindex (Equiv.prodSumDistrib _ _ _).symm
    (Equiv.prodSumDistrib _ _ _).symm (Equiv.prodSumDistrib _ _ _).symm
  aesop (add simp [FiniteTensor.ofTensor, sumTensor])

instance : CommSemiring TensorClass where
  add_assoc a b c := by
    induction a, b, c using Quotient.inductionOn₃
    apply classOf_eq_of_reindex (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _)
      (Equiv.sumAssoc _ _ _)
    aesop
  add_comm := class_add_comm
  zero_add a := (class_add_comm 0 a).trans (class_add_zero a)
  add_zero := class_add_zero
  nsmul := nsmulRec
  mul_assoc a b c := by
    induction a, b, c using Quotient.inductionOn₃
    apply classOf_eq_of_reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
      (Equiv.prodAssoc _ _ _)
    ext <;> simp [FiniteTensor.ofTensor, mul_assoc]
  mul_comm := class_mul_comm
  one_mul a := (class_mul_comm 1 a).trans (class_mul_one a)
  mul_one := class_mul_one
  zero_mul a := (class_mul_comm 0 a).trans (class_mul_zero a)
  mul_zero := class_mul_zero
  left_distrib := class_left_distrib
  right_distrib a b c := by simp_all [class_mul_comm, class_left_distrib]

theorem zero_le (T : TensorClass) : 0 ≤ T := by
  induction T using Quotient.inductionOn
  exact IsRestriction.zero _

instance : IsOrderedAddMonoid TensorClass where
  add_le_add_left a b h c := by
    induction a, b using Quotient.inductionOn₂
    induction c using Quotient.inductionOn
    exact IsRestriction.sum h (.refl _)

instance : IsOrderedMonoid TensorClass where
  mul_le_mul_left a b h c := by
    induction a, b using Quotient.inductionOn₂
    induction c using Quotient.inductionOn
    exact IsRestriction.product h (.refl _)

instance : ZeroLEOneClass TensorClass := ⟨zero_le 1⟩

/-- Exact rank descends to mutual-restriction classes. -/
def rank : TensorClass → ℕ := Quotient.lift (fun T : FiniteTensor => exactRank T.coeff)
  (by
    intro T S h
    exact le_antisymm (IsRestriction.rank_le h.1) (IsRestriction.rank_le h.2))

theorem rank_mono {T S : TensorClass} (h : T ≤ S) : rank T ≤ rank S := by
    induction T, S using Quotient.inductionOn₂
    exact IsRestriction.rank_le h

/-- Square matrix multiplication as an element of the tensor semiring. -/
def matrixClass (n : ℕ) : TensorClass := classOf (matrixMultiplicationTensor n n n)

@[simp] theorem rank_matrixClass (n : ℕ) : rank (matrixClass n) = exactMatrixRank n :=
  rfl

theorem matrixClass_mul (m n : ℕ) : matrixClass (m * n) = matrixClass m * matrixClass n := by
  let d : Fin (m * n) ≃ Fin m × Fin n := finProdFinEquiv.symm
  let e  :=
    (Equiv.prodCongr d d).trans
      (Equiv.prodProdProdComm _ _ _ _)
  apply classOf_eq_of_reindex e e e
  funext
  simp  [matrixMultiplicationTensor, FiniteTensor.ofTensor, e, Equiv.trans_apply, Equiv.prodCongr_apply]
  grind [d.injective.eq_iff, Prod.ext_iff, Prod.map]

@[simp] theorem matrixClass_one : matrixClass 1 = 1 := by
  let e : Fin 1 × Fin 1 ≃ PUnit.{1} := Fintype.equivOfCardEq (by simp)
  apply classOf_eq_of_reindex e e e
  aesop (add simp [Fin.eq_zero])

theorem matrixClass_pow (m j : ℕ) : matrixClass (m ^ j) = matrixClass m ^ j := by
  induction j with
  | zero => simp
  | succ j ih => grind [matrixClass_mul]

end AuxiliarySeparation.TensorSemiring

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Basic -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Characters of finite tensors over a commutative coefficient semiring

The tensor operations in this file are the coefficient operations from
`MatrixMultiplication.Foundation.Tensor`. A character is an assumption on those
operations, not an assertion that a character exists. Restriction monotonicity
forces invariance under independent invertible changes of coordinates, so this
interface descends to the mutual-restriction classes of Section 3 of the paper.
-/

/-- A normalized, additive, multiplicative, restriction-monotone tensor valuation.

Index types vary over all finite types in `Type`. No character-existence result is
included among the fields or claimed by this definition.
-/
structure Character where
  value : {X Y Z : Type} → [Fintype X] → [Fintype Y] → [Fintype Z] →
    Tensor ℤ X Y Z → ℝ
  map_zero : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z],
    value (0 : Tensor ℤ X Y Z) = 0
  map_one : value unitTensor = 1
  value_sumTensor : ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W),
    value (sumTensor T S) = value T + value S
  map_product : ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor ℤ X Y Z) (S : Tensor ℤ U V W),
    value (Tensor.product T S) = value T * value S
  monotone : ∀ {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℤ X Y Z) (A : X' → X → ℤ)
    (B : Y' → Y → ℤ) (C : Z' → Z → ℤ),
    value (Tensor.restrict A B C T) ≤ value T

namespace Character

variable (χ : Character)

/-- Coordinate pullbacks are restrictions. -/
theorem value_pullback_le (T : Tensor ℤ X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    χ.value (Tensor.pullback fx fy fz T) ≤ χ.value T := by

  rw [Tensor.pullback_eq_restrict]
  exact χ.monotone T _ _ _

/-- Independent coordinate bijections preserve a character. -/
theorem value_reindex (T : Tensor ℤ X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.value (Tensor.pullback ex ey ez T) = χ.value T := by
  apply le_antisymm (χ.value_pullback_le T ex ey ez)
  convert χ.value_pullback_le (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm using 1
  congr 1
  grind [Tensor.pullback]

/-- Binary additivity implies additivity of arbitrary finite direct sums. -/
theorem map_directSum {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : ι → Tensor ℤ X Y Z) :
    χ.value (Tensor.directSum T) = ∑ i, χ.value (T i) := by

  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ [DecidableEq ι] (T : ι → Tensor ℤ X Y Z),
      χ.value (Tensor.directSum T) = ∑ i, χ.value (T i)) ?_ ?_ ?_ ι T
  · intro α β _ e ih _ T
    letI := Fintype.ofEquiv β e.symm
    rw [← e.sum_comp (fun i => χ.value (T i)), ← ih]
    convert (χ.value_reindex (Tensor.directSum T)
      (Equiv.prodCongr e (Equiv.refl X)) (Equiv.prodCongr e (Equiv.refl Y))
      (Equiv.prodCongr e (Equiv.refl Z))).symm using 1
    congr 1
    ext <;> simp_all
  · intro _ T
    rw [Subsingleton.elim (Tensor.directSum T) 0, χ.map_zero]
    simp
  · intro α _ ih _ T
    rw [← χ.value_reindex (Tensor.directSum T)
      optionProdEquiv.symm optionProdEquiv.symm optionProdEquiv.symm,
      Fintype.sum_option, ← ih]
    convert χ.value_sumTensor (T none) (Tensor.directSum fun i => T (some i)) using 1
    congr 1
    aesop (add simp [sumTensor, optionProdEquiv])

/-- Character values are bounded by every exact rank decomposition size. -/
theorem value_le_rank {T : Tensor ℤ X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.value T ≤ r := by
  obtain ⟨A, B, C, rfl⟩ := TensorSemiring.rankAtMost_iff_restriction_scalar.mp h
  apply (χ.monotone _ A B C).trans_eq
  let T : Fin r → Tensor ℤ PUnit PUnit PUnit := fun _ => unitTensor
  have h := χ.value_reindex (Tensor.directSum T)
    (Equiv.prodPUnit (Fin r)).symm (Equiv.prodPUnit (Fin r)).symm
    (Equiv.prodPUnit (Fin r)).symm
  change χ.value (scalarTensor r) = χ.value (Tensor.directSum T) at h
  simpa [T, χ.map_directSum, χ.map_one] using h

/-- A unit coefficient gives a scalar restriction over every commutative semiring. -/
theorem one_le_value_of_coefficient_one {T : Tensor ℤ X Y Z}
    (hT : ∃ x y z, T x y z = 1) : 1 ≤ χ.value T := by
  obtain ⟨x, y, z, hxyz⟩ := hT
  convert χ.value_pullback_le T (fun _ : PUnit => x)
    (fun _ : PUnit => y) (fun _ : PUnit => z) using 1
  rw [← χ.map_one]
  congr 1
  ext
  exact hxyz.symm

theorem nonneg (T : Tensor ℤ X Y Z) : 0 ≤ χ.value T := by
  have h := χ.one_le_value_of_coefficient_one
    (T := sumTensor unitTensor T) ⟨.inl PUnit.unit, .inl PUnit.unit, .inl PUnit.unit, rfl⟩
  simpa [χ.value_sumTensor, χ.map_one] using h

end Character
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/CharacterBounds -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Character values on powers and varying-dimension direct sums

These are consequences of the normalized restriction-monotone character
interface. Coordinate changes preserve values; permuting the three tensor
legs need not preserve an individual character.
-/

/-- A word prescribes one branch tensor at each tensor-product position. -/
def branchWordTensor {s : ℕ} (B : Fin s → Tensor ℤ X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    Tensor ℤ (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, B (w i) (x i) (y i) (z i)

namespace Character

variable (χ : Character)

/-- The canonical branch word tensor evaluates multiplicatively. -/
theorem value_branchWordTensor {s : ℕ}
    (B : Fin s → Tensor ℤ X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    χ.value (branchWordTensor B w) = ∏ i, χ.value (B (w i)) := by
  induction n with
  | zero =>
      convert (χ.value_reindex unitTensor
        (Equiv.equivPUnit (Fin 0 → X)) (Equiv.equivPUnit (Fin 0 → Y))
        (Equiv.equivPUnit (Fin 0 → Z))).trans χ.map_one using 1 <;> rfl
  | succ n ih =>
      rw [Fin.prod_univ_succ, ← ih, ← χ.map_product]
      convert χ.value_reindex _
        (Fin.consEquiv fun _ : Fin (n + 1) => X).symm
        (Fin.consEquiv fun _ : Fin (n + 1) => Y).symm
        (Fin.consEquiv fun _ : Fin (n + 1) => Z).symm using 1
      congr 1
      ext <;> simp_all [branchWordTensor, Fin.prod_univ_succ, Fin.tail]

/-- Tensor powers turn a character value into an ordinary natural power. -/
@[simp] theorem value_power (T : Tensor ℤ X Y Z) (n : ℕ) :
    χ.value (Tensor.power T n) = χ.value T ^ n := by
  convert
    χ.value_branchWordTensor (fun _ : Fin 1 => T) (fun _ : Fin n => 0) using 1 <;> first | rfl | simp

end Character
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/SupportExtension -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Recovering tensors from their supported coordinate subspaces

If a tensor has support inside three injectively embedded coordinate sets, it
is exactly the extension by zero of its pullback to those sets. Characters
therefore have the same value on the ambient tensor and this smaller tensor.
-/

namespace Character

/-- A character ignores ambient coordinates outside a tensor's support. -/
theorem value_eq_pullback_of_support (χ : Character) (T : Tensor ℤ X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    χ.value T = χ.value (Tensor.pullback fx fy fz T) := by

  apply le_antisymm ?_ (χ.value_pullback_le T fx fy fz)
  convert χ.monotone (Tensor.pullback fx fy fz T)
    (fun x' x => if fx x = x' then 1 else 0)
    (fun y' y => if fy y = y' then 1 else 0)
    (fun z' z => if fz z = z' then 1 else 0) using 1
  congr 1
  funext x' y' z'
  by_cases ht : T x' y' z' = 0
  · simp [ht, Tensor.restrict]
    symm
    repeat' (apply Finset.sum_eq_zero; intro _ _)
    split_ifs <;> simp_all
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩, ⟨z, rfl⟩⟩ := hs _ _ _ ht
    simp [Tensor.restrict, hx.eq_iff, hy.eq_iff, hz.eq_iff]
end Character
end

end AuxiliarySeparation

namespace AuxiliarySeparation.Sector

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Sector/Branches -/
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Coordinate identifications of the three retained sectors

Each outer branch is a zero extension of `C(a,h)`, using the same first-leg
coordinates. The middle branch is a zero extension after reversing the first
coordinate and exchanging the second and third tensor legs.
-/

variable (χ : Character)

variable (a h : ℕ)

/-- Both translated outer branches have the original convolution value. -/
theorem value_outerTensor (b : Bool) :
    χ.value (branchFamily a h (if b then 2 else 0)) = χ.value (convolution a h) := by
  let start := if b then rightStart a h else 0
  let outerY (r : Fin h) : YIndex a h :=
    ⟨start + r.val, by grind [sourceWidth, rightStart]⟩
  let outerZ (s : Fin (a + h - 1)) : ZIndex a h :=
    ⟨start + s.val, by grind [sourceWidth, rightStart]⟩
  refine (χ.value_eq_pullback_of_support _ id (outerY) (outerZ)
    Function.injective_id (by simp [outerY, Function.Injective, Fin.ext_iff])
    (by simp [outerZ, Function.Injective, Fin.ext_iff]) ?_).trans ?_
  · intro i j k hn
    have hb := branchFamily_labels hn
    refine ⟨⟨i, rfl⟩,
      ⟨⟨j.val - start, ?_⟩, Fin.ext ?_⟩,
      ⟨⟨k.val - start, ?_⟩, Fin.ext ?_⟩⟩
    all_goals
      cases b <;> simp only [Bool.false_eq_true] at hb ⊢
      all_goals
        simp [yLabel, zLabel, ite_eq_iff] at hb
        dsimp [outerY, outerZ, start, sourceWidth, rightStart] at *
        omega
  · congr 1
    funext
    cases b <;>
      simp (disch := omega) [Tensor.pullback, branchFamily, outerY, outerZ, start, yLabel,
        zLabel, source, convolution, rightStart] <;> grind

/-- The middle-branch value is the value of the exchanged convolution tensor. -/
theorem value_middleTensor   :
    χ.value (branchFamily  a h 1) = χ.value (fun i s r => convolution a h i r s) := by
    let middleY (s : Fin (a + h - 1)) : YIndex a h :=
      (Fin.natAdd h s).castLE (by unfold sourceWidth; omega)
    let middleZ (r : Fin h) : ZIndex a h :=
      (Fin.natAdd (h + a - 1) r).castLE (by unfold sourceWidth; omega)
    refine (χ.value_eq_pullback_of_support _ Fin.rev (middleY) (middleZ)
      Fin.rev_injective (by simp [middleY, Function.Injective])
      (by simp [middleZ, Function.Injective]) ?_).trans ?_
    · intro i j k hn
      have hb := branchFamily_labels hn
      simp  [yLabel, zLabel, ite_eq_iff] at hb
      refine ⟨⟨i.rev, by simp⟩,
        ⟨⟨j.val - h, ?_⟩, Fin.ext ?_⟩,
        ⟨⟨k.val - (h + a - 1), ?_⟩, Fin.ext ?_⟩⟩ <;>
        dsimp [middleY, middleZ, rightStart] at * <;>
        omega
    · congr 1
      funext
      simp (disch := omega) [Tensor.pullback, branchFamily, middleY, middleZ, yLabel,
        zLabel, rightStart,  source, convolution] <;> grind

end AuxiliarySeparation.Sector

namespace Foundation.Tensor

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Integral/FiniteFreeDescent -/
/-! Fixed finite free algebra descent. No field hypothesis and no division.
The unit-splitting functional is supplied explicitly: it need not exist for an
arbitrary finite algebra over a ring. -/

variable {E : Type*} [CommRing E]

/-- Expand only the first two extension coefficients in a fixed basis. -/
theorem project_mul_mul {ι : Type*} [Fintype ι] (basis : Module.Basis ι ℤ E) (π : E →ₗ[ℤ] ℤ)
    (v w t : E) :
    π (v * w * t) = ∑ i, ∑ j,
      basis.repr v i * basis.repr w j * π (basis i * basis j * t) := by
  conv_lhs => rw [← basis.sum_repr v, ← basis.sum_repr w]
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum, smul_mul_assoc,
    mul_smul_comm, map_smul, smul_eq_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

end Foundation.Tensor

namespace AuxiliarySeparation.Integral

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Integral/Cyclotomic -/
section
/-! Integral cyclotomic coefficients: a fixed finite free algebra containing
a primitive root as a unit, without inverting its order. -/

variable (L : ℕ)

abbrev CyclotomicAlgebra  := AdjoinRoot (Polynomial.cyclotomic L ℤ)

instance cyclotomicAlgebra_isDomain (L : ℕ) [NeZero L] :
    IsDomain (CyclotomicAlgebra L) :=
  AdjoinRoot.isDomain_of_prime (Polynomial.cyclotomic.irreducible (NeZero.pos L)).prime

theorem cyclotomic_natDegree_pos  [NeZero L] :
    0 < (Polynomial.cyclotomic L ℤ).natDegree := by
  rw [Polynomial.natDegree_cyclotomic]
  exact Nat.totient_pos.mpr (NeZero.pos L)

instance cyclotomicAlgebra_charZero (L : ℕ) [NeZero L] :
    CharZero (CyclotomicAlgebra L) := by
  apply charZero_of_injective_algebraMap (R := ℤ)
  exact AdjoinRoot.of.injective_of_monic_of_degree_pos
    (Polynomial.cyclotomic.monic L ℤ)
    (Polynomial.natDegree_pos_iff_degree_pos.mp (cyclotomic_natDegree_pos L))

theorem cyclotomic_root_primitive  [NeZero L] :
    IsPrimitiveRoot (AdjoinRoot.root (Polynomial.cyclotomic L ℤ)) L := by
  apply (Polynomial.isRoot_cyclotomic_iff_charZero (NeZero.pos L)).mp
  rw [← Polynomial.map_cyclotomic_int L (CyclotomicAlgebra L)]
  exact AdjoinRoot.isRoot_root _

def cyclotomicUnit  [NeZero L] : (CyclotomicAlgebra L)ˣ :=
  ((cyclotomic_root_primitive L).isUnit (NeZero.ne L)).unit

theorem cyclotomicUnit_primitive  [NeZero L] :
    IsPrimitiveRoot (cyclotomicUnit L) L :=
  (cyclotomic_root_primitive L).isUnit_unit (NeZero.ne L)

def cyclotomicBasis  :
    Module.Basis (Fin (Polynomial.cyclotomic L ℤ).natDegree) ℤ (CyclotomicAlgebra L) :=
  AdjoinRoot.powerBasisAux' (Polynomial.cyclotomic.monic L ℤ)

def cyclotomicProjection [NeZero L] : CyclotomicAlgebra L →ₗ[ℤ] ℤ :=
  (cyclotomicBasis L).coord ⟨0, cyclotomic_natDegree_pos L⟩

theorem cyclotomicProjection_one [NeZero L] :
    cyclotomicProjection L 1 = 1 := by
  have h : cyclotomicBasis L ⟨0, cyclotomic_natDegree_pos L⟩ = 1 := by
    change (AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic L ℤ)).basis
      ⟨0, cyclotomic_natDegree_pos L⟩ = 1
    rw [PowerBasis.basis_eq_pow]
    rfl
  simp_all [cyclotomicProjection, ← h]
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Integral/UnnormalizedFourier -/
section
variable {E : Type*} [CommRing E] [IsDomain E] {ζ : Eˣ} {L : ℕ}

/-- Fourier orthogonality without division, including negative unit powers. -/
theorem sum_unit_zpow_primitive_root_of_abs_lt {e : ℤ}
    (hζ : IsPrimitiveRoot ζ L) (he : |e| < (L : ℤ)) :
    ∑ r : Fin L, (↑(ζ ^ ((r.val : ℤ) * e)) : E) =
      if e = 0 then (L : E) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun r => (↑(ζ ^ ((r : ℤ) * e)) : E))]
  simp_rw [mul_comm (b := e), zpow_mul, zpow_natCast, Units.val_pow_eq_pow_val]
  split_ifs with h
  · subst e
    simp
  · have hne : (↑(ζ ^ e) : E) ≠ 1 := by
      simpa [hζ.zpow_eq_one_iff_dvd] using
        (fun (hd : (L : ℤ) ∣ e) => h (Int.eq_zero_of_abs_lt_dvd hd he))
    apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hne))
    rw [mul_neg_geom_sum, mul_zero, sub_eq_zero]
    norm_cast
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow, Units.val_one]
end

end AuxiliarySeparation.Integral

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Separation/Basic -/
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# The tensor map with an arbitrary Fourier period

The branches have a common first coordinate space and common sizes on the other
two legs. Their second and third coordinates carry a matching sector label.
The three maps below are independent linear substitutions on the three legs of
`L` complete copies of the source tensor.
-/

variable {M : ℕ}

/-- The paper numbers sectors from one, while `Fin M` numbers them from zero. -/
def sectorNumber (i : Fin M) : ℤ := i.val + 1

theorem sectorNumber_bounds (i : Fin M) :
    1 ≤ sectorNumber i ∧ sectorNumber i ≤ M := by
    unfold sectorNumber
    omega

theorem sectorNumber_injective : Function.Injective (@sectorNumber M) := by
  intro i j hij
  unfold sectorNumber at hij
  omega

/-- Branches sharing X, with matching and disjoint Y and Z sectors. -/
def sharedFirstTensor (B : Fin M → Tensor K X Y Z) :
    Tensor K X (Fin M × Y) (Fin M × Z) :=
  fun x y z => if y.1 = z.1 then B y.1 x y.2 z.2 else 0

/-- The separated target is a direct sum of branch/dot-product tensors. -/
def separationTarget (B : Fin M → Tensor K X Y Z) :=
  Tensor.directSum fun h => Tensor.product (B h)
    (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin M))))

end AuxiliarySeparation

namespace AuxiliarySeparation.Integral

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Integral/RestrictionDescent -/
section
/-! Restriction-level finite-free descent. Kept separate from rank descent so
its larger coefficient-map identities do not delay monic quotient setup. -/

variable {E : Type*} {ι : Type}
variable [CommRing E] [Fintype ι]

/-- When the functional splits the unit, a restriction defined over the finite
free algebra descends to D² source copies over the base ring. -/
theorem descend_restriction_basis
    [DecidableEq ι] (basis : Module.Basis ι ℤ E) (π : E →ₗ[ℤ] ℤ) (hπ : π 1 = 1)
    (S : Tensor ℤ X Y Z) (T : Tensor ℤ U V W)
    (h : TensorSemiring.IsRestriction (fun x y z => algebraMap ℤ E (S x y z))
      (fun u v w => algebraMap ℤ E (T u v w))) :
    TensorSemiring.IsRestriction S (Tensor.directSum fun _ : ι × ι => T) := by
  rcases h with ⟨A, B, C, h⟩
  refine ⟨(fun x q => basis.repr (A x q.2) q.1.1),
    (fun y q => basis.repr (B y q.2) q.1.2),
    (fun z q => π (basis q.1.1 * basis q.1.2 * C z q.2)), ?_⟩
  have ha v : π (algebraMap ℤ E v) = v := by
    simpa [hπ] using map_zsmul π v (1 : E)
  funext x y z
  rw [← ha (S x y z), congrFun (congrFun (congrFun h x) y) z]
  simp only [Tensor.restrict, map_sum, LinearMap.map_mul_algebraMap]
  simp [Fintype.sum_prod_type, ite_and]
  conv_lhs =>
    enter [2, u, 2, v, 2, w]
    rw [Tensor.project_mul_mul basis π]
  simp  [Finset.sum_mul]
  simp only [← Fintype.sum_prod_type' (α₁ := ι) (α₂ := ι)]
  exact Tensor.sum_comm_three _
end

end AuxiliarySeparation.Integral

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Integral/CoefficientExtraction -/
section
/-!
# Coefficient extraction without interpolation

Only the target coefficient degree controls the number of copies. The guard
in `shiftedCoeff` is essential: natural subtraction alone would incorrectly
reuse the constant coefficient when the shift exceeds the requested degree.
-/

namespace AuxiliarySeparation.Integral

variable {R : Type*} [CommSemiring R]

/-- The coefficient left after a monomial shift, including the negative-index case. -/
def shiftedCoeff (p : R[X]) (h shift : ℕ) : R :=
  if shift ≤ h then p.coeff (h - shift) else 0

end AuxiliarySeparation.Integral

namespace Foundation.Tensor.PolynomialRestrictionDegeneration

open OAI.MatrixMultiplication.AuxiliarySeparation.Integral

variable {R : Type*} [CommRing R]
variable {T : Tensor R X Y Z} {U : Tensor R X' Y' Z'}
variable {k : ℕ}

/-- Extracting a coefficient of each tensor power gives an exact restriction
with only quadratic overhead in the power. -/
theorem extract (L : PolynomialRestrictionDegeneration T U k) (n : ℕ) :
    AuxiliarySeparation.TensorSemiring.IsRestriction (Tensor.power U n)
      (Tensor.directSum fun _ : Fin (k * n + 1) × Fin (k * n + 1) => Tensor.power T n) := by
  let h := k * n
  let A := fun (x : Fin n → X') (u : Fin n → X) => ∏ i, L.leftMap (x i) (u i)
  let B := fun (y : Fin n → Y') (v : Fin n → Y) => ∏ i, L.middleMap (y i) (v i)
  let C := fun (z : Fin n → Z') (w : Fin n → Z) => ∏ i, L.rightMap (z i) (w i)
  let P := Tensor.restrict A B C (fun u v w => Polynomial.C (Tensor.power T n u v w))
  choose N hN using fun x y z =>
    Polynomial.X_pow_dvd_iff.mpr (fun j hj =>
      (L.coeff x y z j hj.le).trans (ite_eq_right (ne_of_lt hj)))
  have hN0 x y z : (N x y z).coeff 0 = U x y z := by
    have h := L.coeff x y z k le_rfl
    rw [hN] at h
    simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] using h
  have hbase : P =
      Tensor.power (Tensor.restrict L.leftMap L.middleMap L.rightMap
        fun x y z => Polynomial.C (T x y z)) n := by
    funext
    simp  [P, A, B, C, Tensor.restrict, Tensor.power,
      Fintype.prod_sum, Finset.prod_mul_distrib]
  have hlead x y z :
      (P x y z).coeff h =
        Tensor.power U n x y z := by
    rw [hbase]
    simp [h, Tensor.power, hN, Finset.prod_mul_distrib, ← pow_mul,
      Polynomial.coeff_X_pow_mul', Polynomial.coeff_zero_prod, hN0]
  refine ⟨(fun x q => (A x q.2).coeff q.1.1),
    (fun y q => (B y q.2).coeff q.1.2),
    (fun z q =>
        shiftedCoeff (C z q.2) h (q.1.1.val + q.1.2.val)), ?_⟩
  funext x y z
  rw [← hlead x y z]
  simp [P, h, Tensor.restrict, Fintype.sum_prod_type, ite_and]
  simp only [← Fintype.sum_prod_type' (α₁ := Fin (k * n + 1)) (α₂ := Fin (k * n + 1))]
  rw [← Tensor.sum_comm_three]
  congr 1 with u
  congr 1 with v
  congr 1 with w
  simp only [Fintype.sum_prod_type, ← Finset.sum_mul]
  congr 1
  simp only [Finset.sum_fin_eq_sum_range]
  rw [mul_assoc, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [dite_eq_left (Finset.mem_range.mp hi)]
  rw [← Finset.sum_subset (Finset.range_mono (show h - i + 1 ≤ h + 1 by omega))
    (by
      simp_all [shiftedCoeff] <;> omega)]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  grind [shiftedCoeff, Nat.sub_sub, mul_assoc, mul_zero]

end Foundation.Tensor.PolynomialRestrictionDegeneration
end

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Integral/CharacterTransport -/
/-
Copyright c 2026. Released under Apache-2.0 as described in LICENSE.
Developed for the integral extension of OpenAI's matrix-multiplication proof.
-/

namespace Character

variable (χ : Character)

/-- Division-free polynomial coefficient extraction proves character
monotonicity over every commutative ring. No infinitude or field assumption
and no continuity of the character are needed. -/
theorem value_polynomialRestrictionDegeneration_le_ring
    {T : Tensor ℤ X Y Z} {U : Tensor ℤ X' Y' Z'} {k : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k) :
    χ.value U ≤ χ.value T := by
  apply le_of_pow_le_const_sq_mul_pow
    (A := k) (C := 1) (χ.nonneg T)
  intro n
  obtain ⟨A, B, C, h⟩ := L.extract n
  have hm := h.symm ▸ χ.monotone _ A B C
  clear h
  simp_all [ χ.map_directSum,       ] <;> nlinarith

end Character

end AuxiliarySeparation

namespace AuxiliarySeparation.Character

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Dot -/
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Dot-product exponents of tensor characters

The power laws here follow from restriction monotonicity and tensor products.
They are not additional assumptions on a character. The three exponents refer
to the leg on which the corresponding dot product has dimension one.
-/

variable (χ : Character)

/-- Precomposing a character with a cyclic permutation gives a character. -/
def cyclicCharacter : Character where
  value T := χ.value (Tensor.cyclic T)
  map_zero := χ.map_zero
  map_one := χ.map_one
  value_sumTensor T S := by
    convert χ.value_sumTensor (Tensor.cyclic T) (Tensor.cyclic S) using 1
    congr 1
    aesop
  map_product T S := χ.map_product (Tensor.cyclic T) (Tensor.cyclic S)
  monotone T A B C := by
    convert χ.monotone (Tensor.cyclic T) B C A using 1
    congr 1
    funext
    simp only [Tensor.cyclic, Tensor.restrict, mul_left_comm, mul_comm]
    exact Finset.sum_comm_cycle.symm

variable {m : ℕ}

/-- The exponent on dot products whose third leg has dimension one. -/
def pZ : ℝ :=
  Real.log (χ.value (Tensor.dotPairing  (Fin 2))) / Real.log 2

/-- The exponent on dot products whose second leg has dimension one. -/
def pY : ℝ := χ.cyclicCharacter.pZ

/-- The exponent on dot products whose first leg has dimension one. -/
def pX : ℝ := χ.cyclicCharacter.cyclicCharacter.pZ

theorem value_dotPairing {n : ℕ} (hn : 0 < n) :
    χ.value (Tensor.dotPairing  (Fin n)) = (n : ℝ) ^ χ.pZ := by
  let f : ℕ →*o ℝ :=
    { toFun := fun m => χ.value (Tensor.dotPairing (Fin m))
      monotone' m n hmn := by
        change χ.value (Tensor.dotPairing (Fin m)) ≤ χ.value (Tensor.dotPairing (Fin n))
        convert χ.value_pullback_le (Tensor.dotPairing (Fin n)) (Fin.castLE hmn) (Fin.castLE hmn) id using 1
        congr 1
        grind [Tensor.pullback, Tensor.dotPairing]
      map_mul' m n := by
        rw [← χ.map_product]
        convert χ.value_reindex _ finProdFinEquiv.symm finProdFinEquiv.symm
          (Equiv.prodUnique Unit Unit).symm using 1
        congr 1
        ext
        simp only [Tensor.pullback, Tensor.product, Tensor.dotPairing,
          ite_zero_mul_ite_zero, one_mul, ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
      map_one' := by
        apply le_antisymm
        · simpa using χ.value_le_rank (T := Tensor.dotPairing (Fin 1)) (r := 1)
            ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, by
              ext
              simp [Fin.eq_zero]⟩
        · exact χ.one_le_value_of_coefficient_one ⟨0, 0, (), rfl⟩ }
  have hpos n (hn : 0 < n) : 0 < f n :=
    zero_lt_one.trans_le (by simpa using f.monotone' hn)
  let p := Real.log (f 2) / Real.log 2
  have hf2 : 1 ≤ f 2 := by simpa using f.monotone' (by norm_num : 1 ≤ 2)
  have hp : 0 ≤ p := div_nonneg (Real.log_nonneg hf2) (Real.log_nonneg (by norm_num))
  have he : (2 : ℝ) ^ p = f 2 :=
    Real.rpow_logb (by norm_num) (by norm_num) (hpos 2 (by omega))
  have hb (k : ℕ) : f n ^ k ≤ f 2 * ((n : ℝ) ^ p) ^ k ∧
      ((n : ℝ) ^ p) ^ k ≤ f 2 * f n ^ k := by
    obtain ⟨m, hl, hu⟩ := exists_nat_pow_near
      (show 1 ≤ n ^ k from Nat.one_le_iff_ne_zero.mpr (by positivity))
      (show 1 < 2 by omega)
    have hlo := OrderHomClass.monotone f hl
    have hup := OrderHomClass.monotone f hu.le
    simp only [map_pow] at hlo hup
    have hl' := Real.rpow_le_rpow (by positivity)
      (show (2 : ℝ) ^ m ≤ (n : ℝ) ^ k by exact_mod_cast hl) hp
    have hu' := Real.rpow_le_rpow (by positivity)
      (show (n : ℝ) ^ k ≤ (2 : ℝ) ^ (m + 1) by exact_mod_cast hu.le) hp
    simp  [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_pow_comm (Nat.cast_nonneg n), he] at hl' hu'
    rw [pow_succ'] at hu' hup
    constructor
    · exact hup.trans (by gcongr)
    nlinarith
  apply le_antisymm
  · exact le_of_eventually_pow_le_const_mul_pow (by positivity)
      (Filter.Eventually.of_forall fun k => (hb k).1)
  · exact le_of_eventually_pow_le_const_mul_pow (hpos n hn).le
      (Filter.Eventually.of_forall fun k => (hb k).2)

theorem value_cyclic_cyclic_dotPairing (hm : 0 < m) :
    χ.value (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (Fin m)) )) =
      (m : ℝ) ^ χ.pX :=
  χ.cyclicCharacter.cyclicCharacter.value_dotPairing hm

/-- The square matrix character is the product of its three oriented dot characters. -/
theorem value_matrixMultiplication (hm : 0 < m) :
    χ.value (matrixMultiplicationTensor m m m) =
      (m : ℝ) ^ (χ.pX + χ.pY + χ.pZ) := by
  rw [Real.rpow_add (Nat.cast_pos.mpr hm), Real.rpow_add (Nat.cast_pos.mpr hm)]
  rw [pX, pY, ← χ.cyclicCharacter.cyclicCharacter.value_dotPairing hm,
    ← χ.cyclicCharacter.value_dotPairing hm, ← χ.value_dotPairing hm]
  dsimp only [cyclicCharacter]
  rw [← χ.map_product, ← χ.map_product]
  convert χ.value_reindex _
    (Equiv.prodCongr (Equiv.uniqueProd (Fin m) Unit).symm (Equiv.refl (Fin m)))
    ((Equiv.prodComm (Fin m) (Fin m)).trans
      (Equiv.prodCongr (Equiv.prodUnique (Fin m) Unit).symm (Equiv.refl (Fin m))))
    (Equiv.prodUnique (Fin m × Fin m) Unit).symm using 1
  congr 1
  ext x y z
  dsimp [matrixMultiplicationTensor, Tensor.pullback, Tensor.product, Tensor.cyclic, Tensor.dotPairing, Tensor.matrixCoefficients]
  split_ifs <;> simp_all

end AuxiliarySeparation.Character

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Integral/Arithmetic -/
section
/-!
# Integer rank schemes give arithmetic algorithms over every ring

This bridge uses exact integer coefficient identities, rather than transferring
functional correctness from a finite coefficient field. Integer constants are
central in every associative unital ring, so the original recursive arithmetic
programs apply without commuting the two input values.

No numerical upper bound on the integer rank exponent is assumed here.
-/

namespace AuxiliarySeparation.Integral

universe u
open Arithmetic

/-- The exact integer rank exponent is an admissible arithmetic exponent over
every associative unital ring. This operation-count statement includes the
zero ring; nontriviality is needed only for the infimum lower bound below. -/
theorem exactRankExponent_int_admissible (R : Type u) [Ring R] :
    Arithmetic.AdmissibleExponent R exactRankExponent := by
  intro ε hε
  obtain ⟨n, hn, hr, hrank⟩ := exists_exactMatrixRank_lt_rpow (lt_add_of_pos_right _ (half_pos hε))
  let r := exactMatrixRank n
  have hν := exactRankExponent_lower
  let K := 6 * r * n ^ 2
  let q := (n : ℝ) ^ (exactRankExponent + ε)
  have hbone : 1 < (n : ℝ) := by aesop
  have hrate : r < q :=
    hr.trans (Real.rpow_lt_rpow_of_exponent_lt hbone (by linarith))
  have hquad : n ^ 2 ≤ q := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbone.le (by norm_cast; linarith)
  have hfrac : 0 ≤ K / (q - r) := by positivity
  let C := 1 + K / (q - r)
  have hC : 0 < C := by positivity
  have hcoeff : r * C + K ≤ C * q := by
    linarith [div_mul_cancel₀ (K : ℝ) (sub_ne_zero.mpr hrate.ne')]
  have hpower : ∀ k : ℕ, ∃ P : MatrixAlgorithm R (n ^ k) (n ^ k) (n ^ k),
      P.Correct ∧ P.cost ≤ C * q ^ k := by
    intro k
    induction k with
    | zero =>
      refine ⟨⟨3, ((Program.nil.step (.input (.inl (0, 0)))).step
        (.input (.inr (0, 0)))).step (.mul 1 0), fun _ _ => 0⟩, ?_, ?_⟩
      · change @MatrixAlgorithm.Correct R _ 1 1 1 _
        intro A B
        funext
        aesop (add simp [Matrix.mul_apply, Fin.eq_zero])
      · change ((1 : ℕ) : ℝ) ≤ C * q ^ 0
        aesop
    | succ k ih =>
      obtain ⟨P, hP, hcost⟩ := ih
      obtain ⟨Q, hQ, hQcost⟩ := RecursiveBlock.int_rank_block_step hrank P hP
      rw [pow_succ']
      refine ⟨Q, hQ, ?_⟩
      have hk : (n ^ k) ^ 2 ≤ q ^ k := by
        rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
        exact pow_le_pow_left₀ (sq_nonneg _) hquad k
      calc
        Q.cost = r * P.cost + K * ((n : ℝ) ^ k) ^ 2 := by exact_mod_cast hQcost
        _ ≤ C * q ^ (k + 1) := by
          linear_combination (norm := (simp only [pow_succ]; ring_nf))
            (r : ℝ) * hcost + (K : ℝ) * hk + q ^ k * hcoeff
          norm_num
  refine ⟨C * n ^ (exactRankExponent + ε), mul_pos hC (by positivity), ?_⟩
  intro m hm
  obtain ⟨k, hk, hmk⟩ := exists_nat_pow_near hm (show 1 < n by omega)
  have hkm : n ^ (k + 1) ≤ n * m := by
    simpa [pow_succ'] using Nat.mul_le_mul_left n hk
  obtain ⟨P, hP, hcost⟩ := hpower (k + 1)
  obtain ⟨Q, hQ, hQP⟩ := MatrixAlgorithm.exists_restrict hmk.le P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ P.cost := by exact_mod_cast hQP
    _ ≤ _ := hcost
    _ = C * (n ^ (k + 1) : ℝ) ^ (exactRankExponent + ε) := by
      simp  [q, Real.rpow_pow_comm (Nat.cast_nonneg n)]
    _ ≤ C * (n * m) ^ (exactRankExponent + ε) := by
      gcongr
      exact_mod_cast hkm
    _ = (C * n ^ (exactRankExponent + ε)) * m ^ (exactRankExponent + ε) := by
      rw [Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg m)]
      ring

end AuxiliarySeparation.Integral

namespace Arithmetic

universe u

theorem admissibleExponent_nonempty (R : Type u) [Ring R] :
    Set.Nonempty {τ : ℝ | AdmissibleExponent R τ} :=
  ⟨_, AuxiliarySeparation.Integral.exactRankExponent_int_admissible R⟩

theorem omega_two_le (R : Type u) [Ring R] [Nontrivial R] : 2 ≤ omega R :=
  le_csInf (admissibleExponent_nonempty R) fun _ h => admissibleExponent_two_le h

end Arithmetic
end

namespace AuxiliarySeparation.Integral

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Integral/ConvolutionRank -/
variable {E : Type*} [CommRing E] [IsDomain E] {a b : ℕ} {ζ : Eˣ}

/-- Both consecutive Fourier periods use h rows; the second removes
its evaluation at one by subtracting the unused top coefficient. -/
theorem convolution_fourier_rank {L : ℕ}
    (hζ : IsPrimitiveRoot ζ L) (hL : L = a + b - 1 ∨ L = a + b - 1 + 1) :
    Tensor.RankAtMost (fun i j k => (L : E) * convolution (K := E) a b i j k)
      (a + b - 1) := by
  let fourierValue (r : ℕ) (e : ℤ) := (ζ ^ (r * e)).val
  have fourierValue_mul (r : ℕ) (s t : ℤ) :
      fourierValue r s * fourierValue r t = fourierValue r (s + t) := by
    simp [fourierValue, mul_add, zpow_add]
  let h := a + b - 1
  let δ := L - h
  refine ⟨fun r i => fourierValue (r.val + δ) i.val,
    fun r j => fourierValue (r.val + δ) j.val,
    fun r k => fourierValue (r.val + δ) (-k.val) - (δ : E) * fourierValue (r.val + δ) 1, ?_⟩
  funext i j k
  have he0 : (i.val : ℤ) + j.val - k.val = 0 ↔ i.val + j.val = k.val := by omega
  rcases hL with rfl | rfl
  · have he : |(i.val : ℤ) + j.val - k.val| < h := by grind
    simp  [δ, h, Nat.cast_zero, zero_mul, sub_zero, fourierValue_mul, ← sub_eq_add_neg]
    simpa [convolution, he0, fourierValue] using
      (sum_unit_zpow_primitive_root_of_abs_lt hζ he).symm
  · have he : |(i.val : ℤ) + j.val - k.val| < (h + 1 : ℤ) := by grind
    have he' : |(i.val : ℤ) + j.val + 1| < (h + 1 : ℤ) := by grind
    have he1 : (i.val : ℤ) + j.val + 1 ≠ 0 := by omega
    have h0 := sum_unit_zpow_primitive_root_of_abs_lt hζ he
    have h1 := sum_unit_zpow_primitive_root_of_abs_lt hζ he'
    simp [Fin.sum_univ_succ, Fin.val_succ, he1] at h0 h1
    simp  [δ, h, Nat.cast_one, one_mul, mul_sub, fourierValue_mul, ← sub_eq_add_neg, Finset.sum_sub_distrib]
    simpa only [add_sub_add_left_eq_sub, sub_zero, he0, convolution,
      mul_ite, mul_one, mul_zero, fourierValue, Nat.cast_add, Nat.cast_one] using (congrArg₂ (· - ·) h0 h1).symm

/-- Each of the two periods gives all tensor powers over one fixed algebra. -/
theorem convolution_fourier_power_rank (L : ℕ) [NeZero L]
    (hL : L = a + b - 1 ∨ L = a + b - 1 + 1) (k : ℕ) :
    Tensor.RankAtMost
      (fun x y z => (L : ℤ) ^ k * Tensor.power (convolution a b) k x y z)
      ((a + b - 1) ^ k * (Polynomial.cyclotomic L ℤ).natDegree ^ 2) := by
  let basis := cyclotomicBasis L
  let π := cyclotomicProjection L
  let ι := Fin (Polynomial.cyclotomic L ℤ).natDegree
  obtain ⟨A, B, C, h⟩ := (convolution_fourier_rank (cyclotomicUnit_primitive L) hL).power k
  convert Tensor.rankAtMost_sum_rankOne
    (fun (q : Fin ((a + b - 1) ^ k) × ι × ι) x => basis.repr (A q.1 x) q.2.1)
    (fun q y => basis.repr (B q.1 y) q.2.2)
    (fun q z => π (basis q.2.1 * basis q.2.2 * C q.1 z)) using 1
  · funext x y z
    trans π (Tensor.power (fun i j k => (L : CyclotomicAlgebra L) * convolution a b i j k) k x y z)
    · dsimp only [π]
      simp only [Tensor.power, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, ← Nat.cast_pow]
      simp only [← nsmul_eq_mul, map_nsmul]
      simp [convolution, Finset.prod_boole, apply_ite, cyclotomicProjection_one]
      split_ifs <;> aesop
    · rw [h]
      simp only [map_sum, Fintype.sum_prod_type, Tensor.rankOne]
      congr 1 with q
      exact Tensor.project_mul_mul basis π (A q x) (B q y) (C q z)
  · simp [ι, Nat.mul_assoc, pow_two]

end AuxiliarySeparation.Integral

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Spectrum/NormalizedStates -/
section
/-!
# Compact convex spaces of normalized additive states

These are the closed linear constraints in Appendix A. The nonemptiness of
this state space, and its instantiation by the tensor restriction semiring,
are separate statements.
-/

open Set

/-- Additive restriction-monotone states with a fixed detector inequality. -/
def normalizedStates (R : S → ℕ) (d : S) (k : ℝ) : Set (S → ℝ) :=
  {f | (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, x ≤ y → f x ≤ f y) ∧
    ∀ x, k * f x ≤ f (d * x)}

variable {R : S → ℕ} {d : S} {k : ℝ} {f : S → ℝ}
    (hf : f ∈ normalizedStates R d k)
include hf

theorem state_zero : f 0 = 0 := by
  have h := hf.2.2.1 0 0
  simp_all
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/Scalar -/
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Natural numbers and rank in the tensor semiring

The natural number `r` is the class of the diagonal scalar tensor with `r`
terms.  Consequently, comparison with `r` in the restriction order is exactly
the existence of a rank decomposition with `r` terms.
-/

namespace TensorSemiring

/-- Natural-number casts are diagonal scalar tensors. -/
@[simp] theorem classOf_scalarTensor (r : ℕ) :
    classOf (scalarTensor r) = (r : TensorClass) := by
  induction r with
  | zero => rw [Subsingleton.elim (scalarTensor 0) 0, classOf_zero, Nat.cast_zero]
  | succ r ih =>
    let e : Fin r ⊕ PUnit ≃ Fin (r + 1) := Fintype.equivOfCardEq (by simp)
    have he : Tensor.pullback e e e (scalarTensor (r + 1)) =
        sumTensor (scalarTensor r) (unitTensor (K := ℤ)) := by
      aesop (add simp [scalarTensor, e.injective.eq_iff, sumTensor, unitTensor])
    convert (classOf_eq_of_reindex e e e he).symm using 1
    change (r : TensorClass) + 1 = classOf (scalarTensor r) + 1
    rw [ih]

/-- Rank takes its usual value on natural numbers in the tensor semiring. -/
@[simp] theorem rank_natCast (r : ℕ) : rank (r : TensorClass) = r := by
  rw [← classOf_scalarTensor r]
  dsimp only [rank, classOf, FiniteTensor.ofTensor]
  apply le_antisymm (exactRank_le (TensorSemiring.rankAtMost_iff_restriction_scalar.mpr (TensorSemiring.IsRestriction.refl _)))
  have h := (exactRank_spec (scalarTensor (K := ℤ) r)).card_le_of_identity id id id
    (by simp_all [scalarTensor])
  simp_all

/-- The rank is a natural-number upper bound in the restriction order. -/
theorem le_rank (T : TensorClass) : T ≤ (rank T : TensorClass) := by
  induction T using Quotient.inductionOn
  rw [← classOf_scalarTensor]
  exact rankAtMost_iff_restriction_scalar.mp (exactRank_spec _)

end TensorSemiring

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Spectrum/Obstruction -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# The rank obstruction behind the preliminary spectral state

The finite catalyst is kept fixed while first tensor powers, then exponent
slack, then the number of copies are varied.  The hypotheses below isolate the
rank inequalities supplied by the catalytic comparison; they do not assert
the existence of a tensor spectrum or the separation argument producing that
comparison.
-/

open Filter Topology

/-- The rank lower bound includes the one-dimensional boundary case. -/
theorem exactMatrixRank_rpow_lower_of_pos {n : ℕ}  (hn : 0 < n) :
    (n : ℝ) ^ exactRankExponent ≤ exactMatrixRank n := by
  by_cases hn2 : 2 ≤ n
  · exact (Real.le_logb_iff_rpow_le (by aesop) (exactMatrixRank_pos hn)).mp (csInf_le (s := exactRankExponentSet) ⟨2, by rintro τ ⟨m, hm, rfl⟩; exact exactMatrixRank_logb_lower hm⟩ ⟨n, hn2, rfl⟩)
  · obtain rfl : n = 1 := by omega
    simp only [Nat.cast_one, Real.one_rpow]
    exact_mod_cast exactMatrixRank_lower hn

/-- Tensor powers of a fixed exact matrix algorithm retain their exact rank
bound after identifying the product coordinates with one matrix dimension. -/
theorem exactMatrixRank_pow_le (u j : ℕ) :
    exactMatrixRank (u ^ j) ≤ exactMatrixRank u ^ j := by
  open TensorSemiring in
  simpa only [← matrixClass_pow, ← Nat.cast_pow, rank_natCast, rank_matrixClass] using
    rank_mono (pow_le_pow_left' (le_rank (matrixClass u)) j)

open TensorSemiring

/-- Iterate a comparison without duplicating its fixed additive catalyst. -/
lemma catalytic_mul {D x y : TensorClass} (h : D + x ≤ D + y) (n : ℕ) :
    D + (n : TensorClass) * x ≤ D + (n : TensorClass) * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h₁ := add_le_add_right h ((n : TensorClass) * x)
    have h₂ := add_le_add_right ih y
    push_cast
    ring_nf at h₁ h₂ ⊢
    exact h₁.trans h₂

/-- A fixed finite catalyst cannot make `k` copies dominate multiplication by
`T_d` unless `k ≥ d^ν`. -/
theorem tensor_catalytic_obstruction_of_one_le
    {D s : TensorClass} {d k m : ℕ} (hd : 0 < d) (hs1 : 1 ≤ s)
    (hcat : D + (m : TensorClass) + matrixClass d * s ≤ D + (k : TensorClass) * s) :
    (d : ℝ) ^ exactRankExponent ≤ k := by
  have hcat  :=
    (add_le_add_left (le_add_of_nonneg_right (zero_le (m : TensorClass))) _).trans hcat
  let C := rank D
  let R := rank s
  have hD  :=
    (le_rank D).trans (by simpa using mul_le_mul_right hs1 C)
  let ν := exactRankExponent
  have hν : 0 < ν := (by norm_num : (0 : ℝ) < 2).trans_le exactRankExponent_lower
  have hsmall (n : ℕ) (hn : 1 ≤ n) : (d : ℝ) ^ ν * n ≤ n * k + C := by
    have hc : ContinuousAt (fun δ : ℝ =>
        (d : ℝ) ^ ν * (n : ℝ) ^ (ν / (ν + δ))) 0 := by fun_prop (disch := positivity)
    have hlim := hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ _)
    apply le_of_tendsto (by simpa [hν.ne'] using hlim)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    let budget := n * k + C
    suffices d ^ exactRankExponent *
        (n : ℝ) ^ (exactRankExponent / (exactRankExponent + δ)) ≤ budget by
      simpa [budget, Nat.cast_add, Nat.cast_mul] using this

    let τ := ν + δ
    have hτ  := add_pos hν hδ
    obtain ⟨u, hu, huR, _⟩ := exists_exactMatrixRank_lt_rpow
      (show exactRankExponent < τ from lt_add_of_pos_right _ hδ)
    apply le_of_eventually_pow_le_const_mul_pow (C := u ^ ν * R)
      (Nat.cast_nonneg budget)
    filter_upwards [Filter.eventually_ge_atTop 1] with j hj
    let l := Nat.log (exactMatrixRank u) (n ^ j)
    let g := u ^ l
    have hg : 0 < g := pow_pos (by omega) l
    have hbudget  :=
      (exactMatrixRank_pow_le u l).trans (Nat.pow_log_le_self _ (by positivity))
    have hsize : (n : ℝ) ^ ((j : ℝ) / τ) ≤ (u : ℝ) * g := by
      have hr : 1 < exactMatrixRank u := by
        have := exactMatrixRank_lower (show 0 < u by omega)
        nlinarith
      have hp  :=
        (show (n : ℝ) ^ j ≤ (exactMatrixRank u : ℝ) ^ (l + 1) by
          exact_mod_cast (Nat.lt_pow_succ_log_self hr (n ^ j)).le).trans
            (pow_le_pow_left₀ (by positivity) huR.le _)
      have h := Real.rpow_le_rpow (by positivity) hp (by positivity : 0 ≤ 1 / τ)
      rw [← Real.rpow_pow_comm (Real.rpow_nonneg (Nat.cast_nonneg u) _),
        ← Real.rpow_mul (Nat.cast_nonneg u), mul_one_div_cancel hτ.ne',
        Real.rpow_one] at h
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)] at h
      simpa only [g, Nat.cast_pow, pow_succ, mul_comm, div_eq_mul_inv, one_mul, mul_one] using h
    have hrank : exactMatrixRank (d ^ j * g) ≤ R * budget ^ j := by
      have hb : matrixClass g ≤ (n : TensorClass) ^ j := by
        exact (le_rank _).trans (by simpa using (Nat.mono_cast hbudget :
          (exactMatrixRank g : TensorClass) ≤ (n ^ j : ℕ)))
      have hc : matrixClass (d ^ j * g) ≤ (budget : TensorClass) ^ j * s := by
        calc
          _ = matrixClass d ^ j * matrixClass g := by rw [matrixClass_mul, matrixClass_pow]
          _ ≤ matrixClass d ^ j * n ^ j := mul_le_mul_right hb _
          _ = (n : TensorClass) ^ j * matrixClass d ^ j * 1 := by ring
          _ ≤ (n : TensorClass) ^ j * matrixClass d ^ j * s := mul_le_mul_right hs1 _
          _ ≤ _ := by
            have habsorb : (n : TensorClass) * (matrixClass d) * s ≤ ((n * k + C : ℕ) : TensorClass) * s := by
              calc
                _ = _ := by ring
                _ ≤ _ := add_le_add (zero_le D) le_rfl
                _ ≤ _ := catalytic_mul hcat n
                _ ≤ _ := add_le_add hD le_rfl
                _ = _ := by push_cast; ring
            clear * -habsorb
            induction j with
            | zero => simp
            | succ j ih =>
              have h₁ := mul_le_mul_right habsorb ((n : TensorClass) ^ j * matrixClass d ^ j)
              have h₂ := mul_le_mul_right ih ((n * k + C : ℕ) : TensorClass)
              simp only [pow_succ]
              ring_nf at h₁ h₂ ⊢
              exact h₁.trans h₂
      simpa only [rank_matrixClass, ← Nat.cast_pow, ← Nat.cast_mul, rank_natCast, Nat.mul_comm] using
        rank_mono (hc.trans (mul_le_mul_right (le_rank s) _))
    have hlow := exactMatrixRank_rpow_lower_of_pos (mul_pos (pow_pos hd j) hg)
    have hpow_n : (n ^ (ν / τ)) ^ j =
        ((n : ℝ) ^ (j / τ)) ^ ν := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
        ← Real.rpow_mul (Nat.cast_nonneg n)]
      ring
    calc
      _ =
          (d ^ j : ℕ) ^ ν * ((n : ℝ) ^ (j / τ)) ^ ν := by
        rw [mul_pow, Real.rpow_pow_comm (Nat.cast_nonneg d), hpow_n, Nat.cast_pow]
      _ ≤ (d ^ j : ℕ) ^ ν * (u * g) ^ ν := by
        gcongr
      _ = u ^ ν * (d ^ j * g : ℕ) ^ ν := by
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg u) (Nat.cast_nonneg g),
          Real.mul_rpow (Nat.cast_nonneg (d ^ j)) (Nat.cast_nonneg g)]
        ring
      _ ≤ u ^ ν * (R * budget ^ j) :=
        mul_le_mul_of_nonneg_left (hlow.trans (by exact_mod_cast hrank)) (by positivity)
      _ = (u : ℝ) ^ ν * R * (budget : ℝ) ^ j := by ring
  apply ge_of_tendsto (by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)).const_add (k : ℝ))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  nlinarith [hsmall n hn, div_mul_cancel₀ (C : ℝ) hn'.ne']

end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Spectrum/StateObstruction -/
section
/-!+# Finite obstructions to normalized additive states

The state equations are homogeneous integer inequalities, except for the
normalization at the unit. Their finite certificates are interpreted in the
additive group completion, preserving catalysts in the original semiring.
-/

open Set

/-- The homogeneous inequalities defining a normalized additive state. Both
signs of the additive relation are included. -/
inductive StateConstraint (S : Type*) [Preorder S] where
  | lower (x : S)
  | upper (x : S)
  | addPos (x y : S)
  | addNeg (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detector (x : S)

variable (R : S → ℕ)
    (d : S)
    (k : ℕ)

/-- Integer coefficient vector of a homogeneous state constraint. -/
def stateConstraintVector
    (c : StateConstraint S) : S →₀ ℤ := match c with
  | .lower x => Finsupp.single x 1
  | .upper x => Finsupp.single 1 (R x : ℤ) - Finsupp.single x 1
  | .addPos x y => Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1
  | .addNeg x y => -(Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1)
  | .order x y _ => Finsupp.single y 1 - Finsupp.single x 1
  | .detector x => Finsupp.single (d * x) 1 - Finsupp.single x (k : ℤ)

/-- The ordinary monotonicity difference in a state constraint. -/
def stateConstraintLower (c : StateConstraint S) : S :=
  match c with
  | .lower _ => 0
  | .upper x => x
  | .order x _ _ => x
  | _ => 0

def stateConstraintUpper  (c : StateConstraint S) : S :=
  match c with
  | .lower x => x
  | .upper x => R x
  | .order _ y _ => y
  | _ => 0

/-- The multiplier of the distinguished detector difference. -/
def stateConstraintDetector (c : StateConstraint S) : S :=
  match c with
  | .detector x => x
  | _ => 0

/-- Interpreting a constraint in the group completion separates its ordinary
order difference from its detector difference. -/
theorem stateConstraintVector_completion
    (c : StateConstraint S) :
    Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))
        (stateConstraintVector R d k c) =
      Algebra.GrothendieckAddGroup.of (stateConstraintUpper R c) -
        Algebra.GrothendieckAddGroup.of (stateConstraintLower c) +
      Algebra.GrothendieckAddGroup.of (d * stateConstraintDetector c) -
        k • Algebra.GrothendieckAddGroup.of (stateConstraintDetector c) := by

  cases c <;> simp [stateConstraintVector, stateConstraintLower, stateConstraintUpper, stateConstraintDetector, Nat.cast_smul_eq_nsmul] <;> first | rfl | (rw [← nsmul_one, map_nsmul]; rfl)

variable [IsOrderedAddMonoid S]
variable (hzero : ∀ x : S, 0 ≤ x)
    (hbound : ∀ x : S, x ≤ (R x : S))
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
include hzero hbound hno

/-- Absence of positive scalar-gain catalysts guarantees the existence of a
normalized additive monotone state satisfying the detector inequality. -/
theorem normalizedStates_nonempty_of_no_catalyst

     :
    (normalizedStates R d k).Nonempty := by
  let B : Set (S → ℝ) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ R x}
  let K  := B ∩ {f | f 1 = 1}
  let t  :=
    fun c ↦ {f : S → ℝ | 0 ≤ Finsupp.linearCombination ℤ f (stateConstraintVector R d k c)}
  have hBcompact  :=
    isCompact_pi_infinite fun x ↦ isCompact_Icc (a := 0) (b := (R x : ℝ))
  have hKcompact : IsCompact K :=
    hBcompact.inter_right (isClosed_eq (continuous_apply 1) continuous_const)
  have htclosed : ∀ c, IsClosed (t c) := fun c ↦
    isClosed_le continuous_const (by
      simp [Finsupp.linearCombination_apply, Finsupp.sum]
      fun_prop)
  have hfinite : ∀ F : Finset (StateConstraint S), (K ∩ ⋂ c ∈ F, t c).Nonempty := by
    intro F

    let H  := insert 1 (F.biUnion fun c ↦ (stateConstraintVector R d k c).support)
    have hOne : 1 ∈ H := Finset.mem_insert_self _ _
    let I := F ⊕ Bool × H
    let cs : I → StateConstraint S
      | .inl c => c
      | .inr (false, x) => .lower x
      | .inr (true, x) => .upper x
    have hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H := by
      intro i a ha
      cases i with
      | inl c =>
        aesop
      | inr i =>
        rcases i with ⟨tag, x⟩
        cases tag <;> aesop (add simp [cs, stateConstraintVector, Finsupp.mem_support_iff,
          Finsupp.single_apply])
    let A : I → H → ℤ := fun i j ↦ stateConstraintVector R d k (cs i) j
    let u : H → ℤ := fun j ↦ (Finsupp.single (1 : S) 1) j
    have hcert : ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
        ∀ j, ∑ i, (n i  ) * A i j = -m * u j := by
      rintro ⟨m, hm, n, hn⟩
      have hn' : ∑ i, n i • stateConstraintVector R d k (cs i) =
          -(m : ℤ) • Finsupp.single (1 : S) (1 : ℤ) := by
        ext x
        by_cases hx : x ∈ H
        · simpa [u,
               Finsupp.single_apply, neg_ite] using hn ⟨x, hx⟩
        · have hz i  :=
            Finsupp.notMem_support_iff.mp fun h ↦ hx (hH i h)
          simp [ hz,
            show x ≠ 1 from fun h => hx (h.symm ▸ hOne)]
      have heq := congrArg
        (Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))) hn'
      simp only [map_sum, map_nsmul, map_smul, Finsupp.linearCombination_single,
        one_smul, stateConstraintVector_completion] at heq
      let X := ∑ i, n i • stateConstraintLower (cs i)
      let Y := ∑ i, n i • stateConstraintUpper R (cs i)
      let s := ∑ i, n i • stateConstraintDetector (cs i)
      have hXY : X ≤ Y := Finset.sum_le_sum fun i _ =>
        nsmul_le_nsmul_right (by cases cs i <;> simp_all [stateConstraintLower, stateConstraintUpper]) (n i)
      let η : S →+ Algebra.GrothendieckAddGroup S := Algebra.GrothendieckAddGroup.of
      have heq' : η (m + Y + d * s) = η (X + k * s) := by
        simp only [map_add, ← nsmul_one m, ← nsmul_eq_mul, map_nsmul]
        simp only [X, Y, s, smul_sub, smul_add,
          Finset.sum_sub_distrib, Finset.sum_add_distrib, map_sum, map_nsmul,
          Finset.mul_sum, mul_smul_comm, ← smul_comm k, Finset.smul_sum] at heq ⊢
        simp only [neg_zsmul, natCast_zsmul] at heq
        linear_combination (norm := abel) heq
      obtain ⟨C, hC⟩ := (AddLocalization.addMonoidOf ⊤).exists_of_eq heq'
      apply hno (C + Y) s m hm
      calc
        _ = _ := by ac_rfl
        _ = _ := hC
        _ ≤ _ := add_le_add le_rfl (add_le_add hXY le_rfl)
        _ = _ := by ac_rfl
    let C : ProperCone ℝ (H → ℝ) :=
      { toSubmodule := PointedCone.hull ℝ (Set.range fun i j => (A i j : ℝ))
        isClosed' := by
          let A := fun i j => (A i j : ℝ)

          let S := {s : Finset I // LinearIndependent ℝ fun i : s ↦ A i}
          have heq : (PointedCone.hull ℝ (Set.range A)).carrier =
              ⋃ s : S, (PointedCone.hull ℝ (Set.range fun i : s.1 ↦ A i) : Set (H → ℝ)) := by
            ext x
            constructor
            · intro hx
              obtain ⟨s, hs, hx⟩ := exists_linearIndependent_subcone A hx
              exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩
            · intro hx
              obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
              apply Submodule.span_mono _ hs
              rintro _ ⟨i, rfl⟩
              exact ⟨i.1, rfl⟩
          rw [heq]
          exact isClosed_iUnion_of_finite fun s : S ↦ by
            have hf  :=
              LinearMap.isClosedEmbedding_of_injective
                (LinearMap.ker_eq_bot.mpr s.2.fintypeLinearCombination_injective)
            convert hf.isClosedMap (Set.Ici (0 : s.1 → ℝ)) isClosed_Ici using 1
            ext x
            simp only [PointedCone.hull, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
            constructor
            · rintro ⟨c, hc⟩
              exact ⟨fun i => (c i : ℝ), fun i => (c i).2, hc⟩
            · rintro ⟨c, hc, hcx⟩
              exact ⟨fun i => ⟨c i, hc i⟩, hcx⟩
      }
    have houtside : -(fun j => (u j : ℝ)) ∉ C := by
      intro hmem
      obtain ⟨s, hs, hb⟩ := exists_linearIndependent_subcone (fun i j => (A i j : ℝ)) hmem
      obtain ⟨w, heq⟩ := (Submodule.mem_span_range_iff_exists_fun (Nonneg ℝ)).mp hb
      have hreal j := congrFun heq j
      simp only [← Nonneg.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at hreal
      obtain ⟨p, hp1⟩ := Module.Projective.exists_dual_eq_one ℚ (one_ne_zero : (1 : ℝ) ≠ 0)
      have hm (v : ℝ) (z : ℤ) : p (v * z) = p v * z := by
        simpa only [zsmul_eq_mul, mul_comm] using map_zsmul p z v
      have hp (z : ℤ) : p (z : ℝ) = z := by
        simpa [hp1] using hm 1 z
      let q : s → ℚ := fun i => p (w i)
      have hq j := congrArg p (hreal j)
      simp only [map_sum, hm, map_neg, hp] at hq
      have hqReal j : ∑ i : s, (q i  ) * (A i j : ℝ) = -(u j  ) := by
        exact_mod_cast hq j
      have hwq : (fun i => (q i : ℝ)) = fun i => (w i : ℝ) := by
        apply hs.fintypeLinearCombination_injective
        ext j
        simpa only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] using (hqReal j).trans (hreal j).symm
      have hqpos i : 0 ≤ q i := by
        exact_mod_cast (congrFun hwq i ▸ (w i).2  )
      let Q : Matrix s Unit ℚ := fun i _ => q i
      let D := Q.den
      have hD : 0 < D := Nat.pos_of_ne_zero Q.den_ne_zero
      let c i := (Q.num i ()).toNat
      have hc i : (D : ℚ) * q i = (c i : ℚ) := by
        have he := (div_eq_iff (Nat.cast_ne_zero.mpr Q.den_ne_zero)).mp (Q.num_div_den i ())
        have hp : 0 ≤ Q.num i () :=
          Rat.num_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (hqpos i))
        convert (mul_comm _ _).trans he.symm using 1
        exact_mod_cast Int.toNat_of_nonneg hp
      apply hcert
      refine ⟨D, hD, fun i => if hi : i ∈ s then c ⟨i, hi⟩ else 0, fun j => ?_⟩
      have hscaled : ∑ i : s, (c i  ) * (A i j : ℚ) = -(D : ℚ) * (u j : ℚ) := by
        simp_rw [← hc, mul_assoc]
        rw [← Finset.mul_sum, hq, mul_neg, neg_mul]
      calc
        _ = ∑ i : s, (c i  ) * A i j := by
          rw [← Finset.sum_subset (Finset.subset_univ s)
            (by simp_all)]
          rw [Finset.sum_subtype s (fun _ => Iff.rfl)]
          apply Finset.sum_congr rfl
          simp
        _ = _ := by exact_mod_cast hscaled

    obtain ⟨g, hg, hgu⟩ := C.hyperplane_separation_point houtside
    have hpos : 0 < g fun j => (u j : ℝ) := by
      simpa only [map_neg, neg_lt_zero] using hgu
    let L := (g fun j => (u j : ℝ))⁻¹ • g.toLinearMap
    have hLu := inv_mul_cancel₀ hpos.ne'
    let f (x : S) := L fun j : H ↦ if j = x then 1 else 0
    have heval (v : S →₀ ℤ) : Finsupp.linearCombination ℤ f v = L fun j : H ↦ (v j : ℝ) := by
      simp only [f, Finsupp.linearCombination_apply, Finsupp.sum,
        ← L.map_smul_of_tower (R := ℤ), ← map_sum]
      congr 1
      ext
      simp_all [Finset.sum_apply]
    have hf1 : f 1 = 1 := by
      have heq := heval (Finsupp.single 1 1)
      simpa [f] using heq.trans hLu
    have hfc (i : I) : 0 ≤ Finsupp.linearCombination ℤ f (stateConstraintVector R d k (cs i)) := by
      rw [heval]
      exact mul_nonneg (inv_nonneg.mpr hpos.le)
        (hg _ (PointedCone.subset_hull (Set.mem_range_self i)))
    refine ⟨f, ⟨?_, hf1⟩, ?_⟩
    · intro x
      by_cases hx : x ∈ H
      · have hlo := hfc (.inr (false, ⟨x, hx⟩))
        have hhi := hfc (.inr (true, ⟨x, hx⟩))
        constructor
        · simpa [cs, stateConstraintVector] using hlo
        · simpa [cs, stateConstraintVector, hf1] using hhi
      · have h0 : f x = 0 := by
          simp [f,
            show ∀ j : H, j ≠ x from fun j h => hx (h ▸ j.property)]
          exact L.map_zero
        simp [h0]
    · simp  [Set.mem_iInter]
      intro c hc
      exact hfc (.inl ⟨c, hc⟩)
  obtain ⟨f, hfK, hft⟩ := hKcompact.inter_iInter_nonempty t htclosed hfinite
  have hc (c : StateConstraint S) : 0 ≤ Finsupp.linearCombination ℤ f (stateConstraintVector R d k c) :=
    mem_iInter.mp hft c
  refine ⟨f, hfK.1, hfK.2, ?_, ?_, ?_⟩
  · intro x y
    have hp := hc (.addPos x y)
    have hm := hc (.addNeg x y)
    simp [stateConstraintVector] at hp hm
    linarith
  · intro x y hxy
    simpa [stateConstraintVector] using hc (.order x y hxy)
  · intro x
    simpa [stateConstraintVector] using hc (.detector x)
end

end AuxiliarySeparation

namespace AuxiliarySeparation.UnitDominating

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/Primitive -/
/-
Copyright c 2026. Released under Apache-2.0 as described in LICENSE.
Developed for the integral extension of OpenAI's matrix-multiplication proof.
-/

/-!
# The zero-or-unit-dominating subsemiring

The restriction semiring over integers need not have `1 ≤ x` for every
nonzero `x`. Its zero-or-unit-dominating part does. A real-valued character
on that part extends to the full semiring by `χ(x + 1) - 1`; no faithfulness
of the extended character on arbitrary nonzero elements is asserted.
-/

/-- Elements that are zero or admit the unit below them in the order. -/
def subsemiring : Subsemiring TensorSemiring.TensorClass where
  carrier := {x | x = 0 ∨ 1 ≤ x}
  zero_mem' := Or.inl rfl
  one_mem' := Or.inr le_rfl
  add_mem' := by
    rintro a b (rfl | ha) hb
    · simpa using hb
    · exact Or.inr (ha.trans (le_add_of_nonneg_right (TensorSemiring.zero_le b)))
  mul_mem' := by
    rintro a b (rfl | ha) (rfl | hb) <;> simp_all [one_le_mul]

/-- Adding one always places an element in the unit-dominating part. -/
def stabilize (x : TensorSemiring.TensorClass) : subsemiring :=
  ⟨x + 1, Or.inr (le_add_of_nonneg_left (TensorSemiring.zero_le x))⟩

/-- Extend a character by additive stabilization. -/
def extend (φ : subsemiring →+*o ℝ) : TensorSemiring.TensorClass →+*o ℝ where
  toFun x := φ (stabilize x) - 1
  monotone' := by
    intro x y h
    apply sub_le_sub_right (φ.monotone' ?_) 1
    exact add_le_add h le_rfl
  map_zero' := by
    simp_all [show stabilize 0 = 1 from Subtype.ext (zero_add _)]
  map_one' := by change φ (1 + 1) - 1 = 1; simp
  map_add' x y := by
    have h : stabilize (x + y) + 1 =
        stabilize x + stabilize y := by
      apply Subtype.ext
      dsimp [stabilize]
      ring
    have h := congrArg φ h
    grind
  map_mul' x y := by
    have h : stabilize (x * y) + stabilize x + stabilize y =
        stabilize x * stabilize y + 1 + 1 := by
      apply Subtype.ext
      dsimp [stabilize]
      ring
    have h := congrArg φ h
    grind

end AuxiliarySeparation.UnitDominating

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Existence -/
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Detecting characters of the integer tensor semiring

This proves Lemma 3.1, including Appendix A. Finite inconsistency would
produce a positive scalar-gain catalyst, ruled out by the exact-rank exponent.
A compact normalized state space on primitive tensor classes yields a
multiplicative state. Additive stabilization extends it to the full tensor
semiring and hence to the concrete coefficient-level character interface.
-/

open Set

/-- Lemma 3.1: normalized, additive, multiplicative, restriction-monotone
characters detect every integer strictly below the exact-rank growth value. -/
theorem exists_detecting_character {d k : ℕ} (hd : 2 ≤ d)
    (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent) :
    ∃ χ : Character, (k : ℝ) ≤ χ.value (matrixMultiplicationTensor d d d) := by
  let P := UnitDominating.subsemiring
  let normalizedTranslate (z : P) (f : P → ℝ) := fun x => f (z * x) / f z
  have hunit (x : P) (hx : x ≠ 0) : 1 ≤ x :=
    x.property.resolve_left fun h => hx (Subtype.ext h)
  let R (x : P) := TensorSemiring.rank x.val
  let i : Fin d := ⟨0, by omega⟩
  let t : P := ⟨TensorSemiring.matrixClass d, Or.inr (by
    change TensorSemiring.IsRestriction (fun (_ _ _ : PUnit) => (1 : ℤ))
      (matrixMultiplicationTensor d d d)
    convert TensorSemiring.IsRestriction.pullback (matrixMultiplicationTensor d d d)
      (fun _ : PUnit => (i, i)) (fun _ : PUnit => (i, i))
      (fun _ : PUnit => (i, i)) using 1
    ext
    simp [matrixMultiplicationTensor])⟩
  have hb (x : P)  := TensorSemiring.le_rank x.val
  have hno (D s : P) (m : ℕ) (hm : 0 < m)
      (hcat : D + (m : P) +
          t * s ≤
        D + (k : P) * s) : False := by
    change D.val + (m : TensorSemiring.TensorClass) +
        TensorSemiring.matrixClass d * s.val ≤
      D.val + (k : TensorSemiring.TensorClass) *
        s.val at hcat
    by_cases hs : s = 0
    · subst s
      have hbad : D + m ≤ D.val := by simp_all
      have hiter := catalytic_mul (hbad.trans_eq (add_zero D.val).symm) (TensorSemiring.rank D.val + 1)
      simp only [mul_zero, add_zero, ← Nat.cast_mul] at hiter
      have hr := TensorSemiring.rank_mono
        ((le_add_of_nonneg_left (TensorSemiring.zero_le D.val)).trans hiter)
      simp only [TensorSemiring.rank_natCast] at hr
      nlinarith only [hm, hr]
    · exact hk.not_ge (tensor_catalytic_obstruction_of_one_le (by omega)
        (hunit s hs) hcat)
  have hnonempty := normalizedStates_nonempty_of_no_catalyst
    R t k
    (fun x => TensorSemiring.zero_le x.val) hb
    hno
  have hdom (z x  ) :
      z * x ≤ (R x : P) * z := by
    calc
      _ ≤ _ :=
        mul_le_mul_right (hb x) z
      _ = _ := mul_comm _ _
  have hφ : ∃ φ : P →+*o ℝ, (k : ℝ) ≤ φ t := by
    let states := normalizedStates R t k
    have hKcompact : IsCompact states := by
      apply (isCompact_univ_pi fun x => isCompact_Icc (a := 0) (b := (R x : ℝ))).of_isClosed_subset
      · simp  [states, normalizedStates, ofPred_and, ofPred_forall]
        repeat' first | apply IsClosed.inter | apply isClosed_iInter | intro
        all_goals first | apply isClosed_le | apply isClosed_eq
        all_goals fun_prop
      · intro f hf x _
        exact hf.1 x
    have hKconvex : Convex ℝ states := by
      intro f hf g hg a b ha hb hab
      simp only [states, normalizedStates, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine ⟨fun x => convex_Icc 0 (R x : ℝ) (hf.1 x) (hg.1 x) ha hb hab, ?_, ?_, ?_, ?_⟩
      · simpa [hf.2.1, hg.2.1] using hab
      · intro x y
        simp [hf.2.2.1, hg.2.2.1]
        ring
      · intro x y hxy
        linear_combination a * hf.2.2.2.1 x y hxy + b * hg.2.2.2.1 x y hxy
      · intro x
        linear_combination a * hf.2.2.2.2 x + b * hg.2.2.2.2 x
    have hKpos f (hf : f ∈ states) z (hz : z ≠ 0) : 0 < f z := by
      linarith [hf.2.2.2.1 1 z (hunit z hz), hf.2.1]
    let Pred C := C ⊆ states ∧ C.Nonempty ∧ IsCompact C ∧ Convex ℝ C ∧
      ∀ z : P, z ≠ 0 → MapsTo (normalizedTranslate z) C C
    obtain ⟨C, hC⟩ : ∃ C, Minimal Pred C := by
      apply zorn_superset
      intro F hF hchain
      obtain rfl | hnonempty := F.eq_empty_or_nonempty
      · refine ⟨states, ⟨Subset.rfl, hnonempty, hKcompact, hKconvex, ?_⟩, by simp⟩
        intro z hz f hf
        change (fun x => f (z * x) / f z) ∈ normalizedStates R t k
        have hfz := hKpos f hf z hz
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro x
          refine ⟨div_nonneg (hf.1 (z * x)).1 hfz.le, ?_⟩
          apply (div_le_iff₀ hfz).mpr
          have hn := (AddMonoidHom.mk' f hf.2.2.1).map_nsmul (R x) z
          simp only [nsmul_eq_mul, AddMonoidHom.mk'_apply] at hn
          exact (hf.2.2.2.1 _ _ (hdom z x)).trans_eq hn
        · grind [ne_of_gt]
        · simp [mul_add, hf.2.2.1, add_div]
        · intro x y hxy
          exact div_le_div_of_nonneg_right (hf.2.2.2.1 _ _ (mul_le_mul_right hxy z)) hfz.le
        · intro x
          simpa only [mul_div_assoc, mul_left_comm t z] using
            div_le_div_of_nonneg_right (hf.2.2.2.2 (z * x)) hfz.le
      have hsub  := (sInter_subset_of_mem hnonempty.choose_spec).trans (hF hnonempty.choose_spec).1
      have hclosed  := isClosed_sInter fun t ht => (hF ht).2.2.1.isClosed
      have hnonempty : (⋂₀ F).Nonempty := by
        have  := hnonempty.to_subtype
        exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
          (show IsChain (· ⊇ ·) F from hchain.symm).directedOn (fun _ ht => (hF ht).2.1)
          (fun _ ht => (hF ht).2.2.1) (fun _ ht => (hF ht).2.2.1.isClosed)
      refine ⟨⋂₀ F, ⟨hsub, hnonempty, hKcompact.of_isClosed_subset hclosed hsub,
        convex_sInter fun t ht => (hF ht).2.2.2.1, ?_⟩,
        fun t ht => sInter_subset_of_mem ht⟩
      intro z hz f hf
      exact mem_sInter.mpr fun t ht => (hF ht).2.2.2.2 z hz (mem_sInter.mp hf t ht)
    obtain ⟨hCK, hCne, hCcompact, hCconvex, hCmap⟩ := hC.prop
    have hsurj z (hz : z ≠ 0) : normalizedTranslate z '' C = C := by
      have hsub := mapsTo_iff_image_subset.mp (hCmap z hz)
      symm
      apply hC.eq_of_ge (y := normalizedTranslate z '' C) _ hsub
      refine ⟨hsub.trans hCK, hCne.image _, ?_, ?_, ?_⟩
      · apply hCcompact.image_of_continuousOn
        apply continuousOn_pi.mpr
        intro x
        exact (continuous_apply (z * x)).continuousOn.div
          (continuous_apply z).continuousOn fun f hf => (hKpos f (hCK hf) z hz).ne'
      · rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩ a b ha hb hab
        have hfz := hKpos f (hCK hf) z hz
        have hgz := hKpos g (hCK hg) z hz
        let D := a * g z + b * f z
        have hD : 0 < D := hKpos _ (hCK (hCconvex hg hf ha hb hab)) z hz
        refine ⟨(a * g z / D) • f + (b * f z / D) • g,
          hCconvex hf hg (by positivity) (by positivity) (by grind), ?_⟩
        ext x
        dsimp [normalizedTranslate]
        field_simp
        grind
      · rintro w hw _ ⟨f, hf, rfl⟩
        refine ⟨normalizedTranslate w f, hCmap w hw hf, ?_⟩
        ext x
        simp [normalizedTranslate,
          div_div_div_cancel_right₀ (hKpos f (hCK hf) z hz).ne',
          div_div_div_cancel_right₀ (hKpos f (hCK hf) w hw).ne']
        congr 1 <;> ac_rfl
    obtain ⟨f, hf⟩ := hCcompact.extremePoints_nonempty hCne
    have hfK := hCK hf.1
    have hfmul (z x : P) : f (z * x) = f z * f x := by
      by_cases hz : z = 0
      · simp [hz, state_zero hfK]
      have hz1 : z + 1 ≠ 0 := by
        intro h
        have := hfK.2.2.1 z 1
        rw [h, state_zero hfK, hfK.2.1] at this
        linarith [hKpos f hfK z hz]
      obtain ⟨g, hg, hgf⟩ := hsurj (z + 1) hz1 ▸ hf.1
      have hgz := hKpos g (hCK hg) z hz
      have hsum : g z / (g z + 1) + 1 / (g z + 1) = 1 := by
        rw [← add_div, div_self (by positivity)]
      have hseg : f ∈ openSegment ℝ (normalizedTranslate z g) g := by
        refine ⟨g z / (g z + 1), 1 / (g z + 1), by positivity, by positivity, hsum, ?_⟩
        rw [← hgf]
        ext y
        dsimp [normalizedTranslate]
        rw [add_mul, one_mul, (hCK hg).2.2.1 _ _, (hCK hg).2.2.1 _ _, (hCK hg).2.1]
        field_simp
      obtain ⟨hfg, hgg⟩ := (mem_extremePoints.mp hf).2 _ (hCmap z hz hg) _ hg hseg
      rw [hgg] at hfg
      exact ((div_eq_iff (hKpos f hfK z hz).ne').mp (congrFun hfg x)).trans (mul_comm _ _)

    let χ : P →+*o ℝ :=
      { toFun := f
        monotone' := hfK.2.2.2.1
        map_zero' := state_zero hfK
        map_one' := hfK.2.1
        map_add' := hfK.2.2.1
        map_mul' := hfmul }
    refine ⟨χ, ?_⟩
    change (k : ℝ) ≤ f t
    simpa only [mul_one, hfK.2.1] using hfK.2.2.2.2 1
  obtain ⟨φ, hdetect⟩ := hφ
  let ψ := UnitDominating.extend φ
  refine ⟨{
    value := fun T => ψ (TensorSemiring.classOf T)
    map_zero := by intros; simpa only [TensorSemiring.classOf_zero] using map_zero ψ
    map_one := map_one ψ
    value_sumTensor T S := map_add ψ (TensorSemiring.classOf T) (TensorSemiring.classOf S)
    map_product T S := map_mul ψ (TensorSemiring.classOf T) (TensorSemiring.classOf S)
    monotone T A B C := ψ.monotone' ⟨A, B, C, rfl⟩
  }, ?_⟩
  change k ≤ φ (t + 1) - 1
  simpa using hdetect

end AuxiliarySeparation

namespace AuxiliarySeparation.Character

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Permutation -/
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# The six permuted tensor characters

Precomposing a character with a leg permutation gives another character. The
six resulting values multiply to the symmetrized product, and each singleton
leg exponent occurs twice among their first-leg exponents.
-/

variable (χ : Character)

/-- The reflected character exchanges the second and third tensor legs. -/
def swap23Character : Character where
  value T := χ.value fun x z y => T x y z
  map_zero := χ.map_zero
  map_one := χ.map_one
  value_sumTensor T S := by
    convert χ.value_sumTensor (fun x z y => T x y z) (fun x z y => S x y z) using 1
    congr 1
    aesop
  map_product T S := χ.map_product (fun x z y => T x y z) fun x z y => S x y z
  monotone T A B C := by
    convert χ.monotone (fun x z y => T x y z) A C B using 1
    congr 1
    funext
    simp  [Tensor.restrict]
    congr 1 with i
    rw [Finset.sum_comm]
    ring

/-- The three cyclic orders followed by their reflected orders. -/
def permutedCharacter (i : Fin 6) : Character :=
  ![χ, χ.cyclicCharacter, χ.cyclicCharacter.cyclicCharacter,
    χ.swap23Character, χ.swap23Character.cyclicCharacter,
    χ.swap23Character.cyclicCharacter.cyclicCharacter] i

/-- The product of character values in the six orders of possibly different legs. -/
def sixfoldProduct (T : Tensor ℤ X Y Z) : ℝ :=
  ∏ i : Fin 6, (χ.permutedCharacter i).value T

/-- Both adjacent leg exchanges preserve the sixfold character product. -/
theorem sixfoldProduct_swaps (T : Tensor ℤ X Y Z) :
    χ.sixfoldProduct (fun y x z => T x y z) = χ.sixfoldProduct T ∧
      χ.sixfoldProduct (fun x z y => T x y z) = χ.sixfoldProduct T := by
  constructor <;>
    simp [sixfoldProduct, permutedCharacter, Fin.prod_univ_succ,
      cyclicCharacter, swap23Character] <;>
    unfold Tensor.cyclic <;> ring

/-- Commuting convolution inputs preserves the sixfold character product. -/
theorem sixfoldProduct_convolution_comm (a b : ℕ) :
    χ.sixfoldProduct (convolution a b) = χ.sixfoldProduct (convolution b a) := by
  rw [← (χ.sixfoldProduct_swaps (convolution a b)).1]
  apply Finset.prod_congr rfl
  intro i _
  convert (χ.permutedCharacter i).value_reindex (convolution b a)
    (Equiv.refl (Fin b)) (Equiv.refl (Fin a))
    (finCongr (by omega) : Fin (a + b - 1) ≃ Fin (b + a - 1)) using 1
  congr 1
  ext <;> simp [convolution, Nat.add_comm]

end AuxiliarySeparation.Character

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/TagInequality -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# The shared-input tensor tag inequality

Exact type words in a power of a matched-sector tensor are obtained by explicit
coordinate pullbacks. Their character values depend only on the type counts.
The finite auxiliary separation inequality therefore supplies the integral
bounds required by the entropy limit.
-/

open Filter

/-- The finite shared-input separation bound used by the entropy argument. -/
def Character.SeparationBound (χ : Character) : Prop :=
  ∀ {M : ℕ} {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z'],
      0 < M → ∀ B' : Fin M → Tensor ℤ X' Y' Z',
        (∑ i, χ.value (B' i)) * M ^ χ.pX ≤
          6 * M * χ.value (sharedFirstTensor B')

variable {s : ℕ}

/-- Positive branch values imply the shared-input tag inequality from a
finite separation bound. No field structure is used. -/
theorem Character.sharedFirst_tag_of_separation (χ : Character)
    (hsep : χ.SeparationBound)
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor ℤ X Y Z)
    (hB : ∀ a, 0 < χ.value (B a)) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstTensor B) := by
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (q.total.trans_ne one_ne_zero)
  have hT := by
    apply (hB a).trans_le
    convert χ.value_pullback_le (sharedFirstTensor B) id
      (fun y => (a, y)) (fun z => (a, z)) using 1
    congr 1
    grind [Tensor.pullback, sharedFirstTensor]
  let values a := χ.value (B a)
  let source := χ.value (sharedFirstTensor B)
  have hfinite (counts : Fin s → ℕ) :
      (Fintype.card (ExactWords counts) : ℝ) ^ χ.pX * ∏ a, values a ^ counts a ≤
        6 * source ^ ∑ a, counts a := by
    let M := Fintype.card (ExactWords counts)
    let e : Fin M ≃ ExactWords counts := (Fintype.equivFin _).symm
    let W  :=
      fun h => branchWordTensor B (e h).val
    have hM : 0 < M := Fintype.card_pos
    have hv (h : Fin M) : χ.value (W h) = ∏ a, χ.value (B a) ^ counts a := by
      rw [χ.value_branchWordTensor,
        ← Fintype.prod_fiberwise' (e h).val fun a => χ.value (B a)]
      simp  [Finset.prod_const, Finset.card_univ]
      congr 1 with a
      rw [show Fintype.card {i // (e h).val i = a} = counts a from (e h).property a]
    have hfinite := hsep hM W
    simp only [hv, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hfinite
    let coord {U : Type} (y : Fin M × (Fin (∑ a, counts a) → U)) :=
      fun i => ((e y.1).val i, y.2 i)
    have hsource : χ.value (sharedFirstTensor W) ≤
        χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
      convert χ.value_pullback_le (Tensor.power (sharedFirstTensor B) (∑ a, counts a))
        id coord coord using 1
      · congr 1
        symm
        funext x y z
        by_cases h : y.1 = z.1
        · simp [W, Tensor.power, coord, sharedFirstTensor, branchWordTensor, h]
        · have hword : (e y.1).val ≠ (e z.1).val := by
            intro heq
            exact h (e.injective (Subtype.ext heq))
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hword
          simp only [Tensor.pullback, Tensor.power, sharedFirstTensor, h,
            coord]
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [hi]
      · exact (χ.value_power _ _).symm

    apply (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hM : (0 : ℝ) < M)).mp
    convert hfinite.trans (mul_le_mul_of_nonneg_left hsource (by positivity)) using 1 <;> simp only [M, Fintype.card_eq_nat_card] <;> ring
  have htype (counts : Fin s → ℕ) (hD : 0 < ∑ a, counts a) :
      χ.pX * finiteEntropy (fun a => (counts a  ) / (∑ a, counts a  )) +
        ∑ a, (counts a  ) / (∑ a, counts a  ) * Real.log (values a) ≤
          Real.log source := by
    have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := by exact_mod_cast hD
    have hc := ((tendsto_const_div_atTop_nhds_zero_nat (Real.log 6)).comp
      (tendsto_id.atTop_mul_const' hD)).add_const (Real.log source)
    have herror := ((tendsto_factorialLogRemainder_mul_div (∑ a, counts a)).sub
      (tendsto_finsetSum Finset.univ fun a _ =>
        tendsto_factorialLogRemainder_mul_div (counts a))).div_const (∑ a, counts a : ℝ)
    apply le_of_tendsto_of_tendsto
      (by simpa using
        (((herror.const_add (finiteEntropy fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))).const_mul χ.pX).add_const _))
      (by simpa only [zero_add] using hc)
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply, id_eq, Nat.cast_mul]
    have hp : 0 < (Fintype.card (ExactWords fun a => t * counts a) : ℝ) := by positivity
    have hP := Finset.prod_pos (s := Finset.univ) fun a _ =>
      pow_pos (hB a) (t * counts a)
    have h := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hp χ.pX) hP)
      (hfinite (fun a => t * counts a))
    rw [Real.log_mul (Real.rpow_pos_of_pos hp χ.pX).ne' hP.ne',
      Real.log_rpow hp, Real.log_prod (fun a _ => (pow_pos (hB a) _).ne'),
      Real.log_mul (by norm_num : (0 : ℝ) < 6).ne' (pow_ne_zero _ hT.ne'), Real.log_pow] at h
    have hcard := exactWords_card (fun a : Fin s => t * counts a)
    simp only [Fintype.card_eq_nat_card] at hcard
    simp only [ ← Finset.mul_sum, Nat.cast_mul, mul_assoc,
      Fintype.card_eq_nat_card, hcard] at h
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have hh := (div_le_div_iff_of_pos_right (mul_pos ht' hD')).2 h
    convert hh using 1
    · have hf n : factorialLogRemainder n =
          Real.log (Nat.factorial n : ℝ) + Real.negMulLog n + n := by
        grind [factorialLogRemainder, Real.negMulLog]
      rw [Nat.multinomial, Nat.cast_div_charZero (Nat.prod_factorial_dvd_factorial_sum _ _),
        Real.log_div (by positivity) (by positivity), Nat.cast_prod,
        Real.log_prod (fun _ _ => by positivity)]
      simp_rw [hf]
      simp [finiteEntropy, div_eq_mul_inv,  Real.negMulLog_mul,
        Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      unfold Real.negMulLog
      simp [Real.log_inv]
      field_simp [ht'.ne']
      dsimp [values]
      ring_nf
      congr 1
      simp only [Finset.mul_sum]
      congr 1 with x
      ring
    · field_simp
      rfl
  have hlog : χ.pX * finiteEntropy q.mass +
      ∑ a, q.mass a * Real.log (values a) ≤ Real.log source := by
    let counts (n : ℕ) a := ⌈q.mass a * (n + 1)⌉₊
    have ht := tendsto_atTop_add_const_right _ (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have hraw a := (tendsto_nat_ceil_mul_div_atTop (q.nonneg a)).comp ht
    have hsum : Tendsto (fun n => (∑ a, counts n a : ℕ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa [ Finset.sum_div, q.total] using
        tendsto_finsetSum Finset.univ fun a _ => hraw a
    have hpos n : 0 < ∑ a, counts n a := by
      have ha  := (q.nonneg a).lt_of_ne' ha
      exact Finset.sum_pos' (by simp) ⟨a, Finset.mem_univ a, Nat.ceil_pos.mpr (by positivity)⟩
    have hr a : Tendsto (fun n => (counts n a : ℝ) / (∑ b, counts n b : ℕ))
        atTop (𝓝 (q.mass a)) := by
      simpa (disch := positivity) only [Function.comp_def, Pi.div_def, counts, div_div_div_cancel_right₀, div_one] using
        (hraw a).div hsum one_ne_zero
    have hent := tendsto_finsetSum Finset.univ fun a _ =>
      (Real.continuous_negMulLog.tendsto _).comp (hr a)
    have hlinear := tendsto_finsetSum Finset.univ fun a _ => (hr a).mul_const (Real.log (values a))
    apply le_of_tendsto ((hent.const_mul χ.pX).add hlinear)
    aesop
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hT, Real.exp_add, Real.exp_sum] at h
  convert h using 1
  congr 1
  congr 1 with a
  rw [Real.rpow_def_of_pos (hB a), mul_comm]
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Polynomial/Laws -/
/-!
# Probability laws for the polynomial tensor inequalities

The determinant filtration uses an arbitrary binary law, while the three-sector
filtration uses the uniform law on three branches.
-/

/-- The three-sector entropy factor is `3 ^ p`. -/
theorem uniformThree_entropy_factor (p : ℝ) :
    Real.exp (p * finiteEntropy (FiniteLaw.uniformThree).mass) = (3 : ℝ) ^ p := by
  rw [Real.rpow_def_of_pos (by norm_num  )]
  simp_all [FiniteLaw.uniformThree, finiteEntropy, Real.negMulLog] <;> ring

end AuxiliarySeparation

namespace AuxiliarySeparation.DeterminantFiltration

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Determinant/Filtration -/
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# The finite determinant filtration of polynomial multiplication

The first leg is kept fixed throughout. The second and third legs use explicit coefficient maps for the quotient and
kernel vectors. Their restriction identity verifies simultaneous triangularity
without constructing polynomial modules or bases.
-/

open Polynomial

variable (e : ℕ)

abbrev Index  := Sum (Fin (e + 2)) (Fin e)

/-- All multiplication coefficients in the explicit adapted bases.
Here `a=d+1`, `b=e+1`, and no first-leg change of coordinates occurs. -/
def adaptedTensor (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | i, .inl j, .inr k =>
      if j.val = e + 1 ∧ i.val < d ∧ e + i.val = k.val then 1 else 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

/-- The associated graded tensor, whose two branches still share the first leg. -/
def gradedTensor (d e : ℕ) : Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if i.val + j.val = k.val then 1 else 0
  | _, .inl _, .inr _ => 0
  | _, .inr _, .inl _ => 0
  | i, .inr j, .inr k => if i.val + j.val = k.val then 1 else 0

/-- The adapted bases make the determinant filtration triangular. -/
def degeneration (d e : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (adaptedTensor d e)
      (gradedTensor  d e) 1 := by
  convert Tensor.PolynomialRestrictionDegeneration.triangular (adaptedTensor  d e)
    (fun j => j.isLeft) (fun k => k.isLeft) (by
      aesop) using 1
  funext i j k
  cases j <;> cases k <;> simp [gradedTensor, adaptedTensor]

/-! The actual coordinate change from the original two-copy convolution. -/

abbrev OriginalIndex  := Sum (Fin (e + 1)) (Fin (e + 1))

/-- The two original components are shifted by the same monomial. -/
def shift (d e : ℕ) (i : Fin (d + 1)) : OriginalIndex e → OriginalIndex (d + e)
  | .inl j => .inl ⟨i.val + j.val, by omega⟩
  | .inr j => .inr ⟨i.val + j.val, by omega⟩

def sourceTensor (d e : ℕ) :
    Tensor ℤ (Fin (d + 1)) (OriginalIndex e) (OriginalIndex (d + e)) :=
  fun i j k => if shift d e i j = k then 1 else 0

/-- Record the polynomial coordinate and the choice of `s` or `w` separately. -/
def originalCoordinate  : OriginalIndex e → Fin (e + 1) × Fin 2
  | .inl j => (j, 0)
  | .inr j => (j, 1)

/-- Quotient vectors `(X^j,0)`, the top vector `(0,X^e)`, and
kernel vectors `(-X^(j+1),X^j)`, in original coordinates. -/
def inputChange : Index e → OriginalIndex e → ℤ
  | .inl j, old => if h : j.val ≤ e then
      if old = .inl ⟨j.val, by omega⟩ then 1 else 0
    else if old = .inr (Fin.last e) then 1 else 0
  | .inr j, old => (if old = .inr ⟨j.val, by omega⟩ then 1 else 0) -
      (if old = .inl ⟨j.val + 1, by omega⟩ then 1 else 0)

/-- Inverse output coordinates: `(X^l,0)=q_l` and
`(0,X^l)=q_(l+1)+k_l`, with the nonexistent top kernel coordinate omitted. -/
def outputDualChange : Index e → OriginalIndex e → ℤ
  | .inl k, .inl l => if l.val = k.val then 1 else 0
  | .inl k, .inr l => if l.val + 1 = k.val then 1 else 0
  | .inr _, .inl _ => 0
  | .inr k, .inr l => if l.val = k.val then 1 else 0

end AuxiliarySeparation.DeterminantFiltration

namespace AuxiliarySeparation

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Separation/BranchTagging -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# Recovering branch tags from coordinate support

When both non-shared coordinates determine a branch label, adding explicit
matching branch tags does not change a character's value. The tags can be
recovered by independent coordinate maps, and forgetting them recovers the
original coefficientwise sum of branches.
-/

variable {M : ℕ}

namespace Character

/-- Branch labels determined by both non-shared coordinates can be inserted
or forgotten without changing a character. -/
theorem value_sharedFirstTensor_eq_sum (χ : Character)
    (B : Fin M → Tensor ℤ X Y Z) (ly : Y → Fin M) (lz : Z → Fin M)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    χ.value (sharedFirstTensor B) = χ.value (∑ i, B i) := by
  apply (χ.value_eq_pullback_of_support (sharedFirstTensor B) id
    (fun y => (ly y, y)) (fun z => (lz z, z)) Function.injective_id
    (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h)
    (by simp_all [sharedFirstTensor]; grind)).trans
  apply congrArg χ.value
  funext x y z
  simp
  change (if ly y = lz z then B (ly y) x y z else 0) = ∑ i, B i x y z
  have hsum : ∑ i, B i x y z = B (ly y) x y z := by
    apply Finset.sum_eq_single (ly y)
    · grind
    · simp
  grind

end Character
end

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Determinant/Character -/
section
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# The determinant inequality for an actual tensor character

The shared-input tag inequality is applied to the two concrete branches of the
checked determinant degeneration. All basis changes and the output-dual change
are supplied by `DeterminantFiltration`.
-/

namespace DeterminantFiltration

/-- The two graded blocks, padded with zeros in common coordinate spaces. -/
def branch (d e : ℕ) (n : Fin 2) :
    Tensor ℤ (Fin (d + 1)) (Index e) (Index (d + e))
  | i, .inl j, .inl k => if n = 0 then if i.val + j.val = k.val then 1 else 0 else 0
  | i, .inr j, .inr k => if n = 1 then if i.val + j.val = k.val then 1 else 0 else 0
  | _, _, _ => 0

def branchLabel (e : ℕ) : Index e → Fin 2
  | .inl _ => 0
  | .inr _ => 1

theorem sum_branch (d e : ℕ) : ∑ n, branch  d e n = gradedTensor d e := by
  aesop (add simp [branch])

end DeterminantFiltration

namespace Character

open DeterminantFiltration

variable (χ : Character)

theorem value_determinant_branch (d e : ℕ) (n : Fin 2) :
    χ.value (branch d e n) = χ.value (convolution (d + 1) (if n = 0 then e + 2 else e)) := by
  fin_cases n <;> first
  | apply χ.value_eq_pullback_of_support (branch d e 0) id Sum.inl
      (fun k : Fin (d + 1 + (e + 2) - 1) => Sum.inl (Fin.cast (by omega) k))
      Function.injective_id Sum.inl_injective
      (Sum.inl_injective.comp (finCongr (by omega)).injective)
  | apply χ.value_eq_pullback_of_support (branch d e 1) id Sum.inr
      (fun k : Fin (d + 1 + e - 1) => Sum.inr (Fin.cast (by omega) k))
      Function.injective_id Sum.inr_injective
      (Sum.inr_injective.comp (finCongr (by omega)).injective)
  all_goals
    intro i j k h
    rcases j with j | j <;> rcases k with k | k
    all_goals
      simp_all [branch] <;>
      exact ⟨Fin.cast (by omega) k, rfl⟩

end Character
end

end AuxiliarySeparation

namespace AuxiliarySeparation.Character

/-! ## OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Polynomial/Inequalities -/
/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-!
# The inequalities for the polynomial profile

The six character values are combined before the common probability law is
optimized. Each first-leg exponent occurs twice, so the total entropy exponent
is exactly six times the mean exponent used to normalize the profile.
-/

open DeterminantFiltration Sector

def ConvolutionBound (ψ : Character) : Prop :=
  ∀ a b : ℕ,
      ψ.value (convolution  a b) ≤ (a + b - 1 : ℕ)

variable (χ : Character)

def meanExponent : ℝ := (χ.pX + χ.pY + χ.pZ) / 3

def convolutionProfile (a b : ℕ) : ℝ :=
  χ.sixfoldProduct (convolution a b) ^ (1 / (6 * χ.meanExponent))

/-- The exponents of the six permuted characters have the normalization total. -/
theorem sum_permutedCharacter_pX_mean :
    ∑ i : Fin 6, (χ.permutedCharacter i).pX = 6 * χ.meanExponent := by
  unfold meanExponent
  simp [permutedCharacter, pX, pY, pZ, cyclicCharacter, swap23Character,
    Fin.sum_univ_succ]
  unfold Tensor.cyclic Tensor.dotPairing
  conv_lhs => simp only [eq_comm]
  conv_rhs => simp only [eq_comm]
  ring

theorem convolution_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < χ.value (convolution a b) :=
  zero_lt_one.trans_le (χ.one_le_value_of_coefficient_one
    ⟨⟨0, ha⟩, ⟨0, hb⟩, ⟨0, by omega⟩, rfl⟩)

/-- The actual polynomial profile is concave in its second positive index. -/
theorem convolutionProfile_concave_of_separation
    (hsep : ∀ ψ : Character, ψ.SeparationBound)
    {a b : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hb : 2 ≤ b) :
    χ.convolutionProfile a (b - 1) + χ.convolutionProfile a (b + 1) ≤
      2 * χ.convolutionProfile a b := by
  let A  := fun i => (χ.permutedCharacter i).value (convolution a b)
  let B  := fun i => (χ.permutedCharacter i).value (convolution a (b + 1))
  let C  := fun i => (χ.permutedCharacter i).value (convolution a (b - 1))
  let p  := fun i => (χ.permutedCharacter i).pX
  let s := 6 * χ.meanExponent
  have hs : 0 < s := by linarith
  have hsum : ∑ i, p i = s := χ.sum_permutedCharacter_pX_mean
  have hA i : 0 < A i := (χ.permutedCharacter i).convolution_pos ha (by omega)
  have hB i : 0 < B i := (χ.permutedCharacter i).convolution_pos ha (by omega)
  have hC i : 0 < C i := (χ.permutedCharacter i).convolution_pos ha (by omega)
  have hprodA : 0 < ∏ i, A i := Finset.prod_pos fun i _ => hA i
  have hprodB : 0 < ∏ i, B i := Finset.prod_pos fun i _ => hB i
  have hprodC : 0 < ∏ i, C i := Finset.prod_pos fun i _ => hC i
  let u  := (∏ i, A i) ^ (1 / s)
  let v  := (∏ i, B i) ^ (1 / s)
  let w  := (∏ i, C i) ^ (1 / s)
  have hu : 0 < u := Real.rpow_pos_of_pos hprodA _
  have hv : 0 < v := Real.rpow_pos_of_pos hprodB _
  have hw : 0 < w := Real.rpow_pos_of_pos hprodC _
  let q  := v / (v + w)
  have hq0  := (div_pos hv (add_pos hv hw)).le
  have hq1  := (div_le_one (add_pos hv hw)).mpr (le_add_of_nonneg_right hw.le)
  let law : FiniteLaw (Fin 2) := {
    mass i := if i = 0 then q else 1 - q
    nonneg i := by positivity
    total := by simp_all }
  have hlog : ∀ i, p i * Real.binEntropy q + q * Real.log (B i) +
      (1 - q) * Real.log (C i) ≤ p i * Real.log 2 + Real.log (A i) := by
    intro i
    have := hA i
    have := hB i
    have := hC i
    let ψ := χ.permutedCharacter i
    have hdet : Real.exp (ψ.pX * Real.binEntropy q) *
        ψ.value (convolution a (b + 1)) ^ q * ψ.value (convolution a (b - 1)) ^ (1 - q) ≤
          2 ^ ψ.pX * ψ.value (convolution a b) := by
      obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
      obtain ⟨e, rfl, he⟩ : ∃ e, b = e + 1 ∧ 0 < e := ⟨b - 1, by omega, by omega⟩
      have ht := ψ.sharedFirst_tag_of_separation (hsep ψ) law (branch d e) (by
        intro n
        rw [ψ.value_determinant_branch]
        exact ψ.convolution_pos (by omega) (by split_ifs <;> omega))
      rw [ψ.value_sharedFirstTensor_eq_sum (branch  d e)
        (branchLabel e) (branchLabel (d + e)) (by intros; grind [branch, branchLabel]), sum_branch] at ht
      simp [Fin.prod_univ_two, law, finiteEntropy, Fin.sum_univ_two,
        ← Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub] at ht
      simp  [ψ.value_determinant_branch, Fin.isValue] at ht
      apply le_trans (b := ψ.value (gradedTensor  d e))
      · simpa [mul_assoc] using ht
      ·
        calc
          _ ≤ _ :=
            ψ.value_polynomialRestrictionDegeneration_le_ring (degeneration  d e)
          _ ≤ _ := by
            convert ψ.monotone (sourceTensor d e) (fun i j => if i = j then 1 else 0) (inputChange e)
              (outputDualChange (d + e)) using 1
            congr 1
            symm
            funext i j k
            simp  [Tensor.restrict, sourceTensor]
            rcases j with j | j
            · by_cases hj : j.val ≤ e
              · aesop (add simp [inputChange, ite_mul, outputDualChange, shift, adaptedTensor])
              · have hj' : j.val = e + 1 := by omega
                simp_all [inputChange, outputDualChange, shift, adaptedTensor, ] <;> grind
            · aesop (add simp [inputChange, sub_mul, Finset.sum_sub_distrib, ite_mul, outputDualChange, shift, adaptedTensor, Nat.add_assoc])
          _ ≤ _ := by
            let T := Tensor.product (convolution (d + 1) (e + 1))
              (Tensor.cyclic (Tensor.cyclic (Tensor.dotPairing (K := ℤ) (Fin 2))))
            refine le_trans (b := ψ.value T) ?_ ?_
            · convert ψ.value_pullback_le T (fun i => (i, ())) (originalCoordinate e)
                (fun k => (Fin.cast (by omega) (originalCoordinate (d + e) k).1,
                  (originalCoordinate (d + e) k).2)) using 1
              congr 1
              grind [Tensor.pullback, Tensor.product, Tensor.cyclic, Tensor.dotPairing,
                originalCoordinate, sourceTensor, shift, convolution, Fin.ext_iff]
            · dsimp only [T]
              rw [ψ.map_product, mul_comm, ψ.value_cyclic_cyclic_dotPairing (by decide)]
              norm_num
    have h := Real.log_le_log (by positivity) hdet
    simpa (disch := positivity) only [Real.log_mul, Real.log_exp, Real.log_rpow] using h
  have hlogs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hlog i
  simp  [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hsum, ← Real.log_prod fun i _ => (hA i).ne',
    ← Real.log_prod fun i _ => (hB i).ne',
    ← Real.log_prod fun i _ => (hC i).ne'] at hlogs
  have h : v + w ≤ 2 * u := by
    apply (Real.log_le_log_iff (add_pos hv hw) (mul_pos (by norm_num) hu)).mp
    rw [Real.log_mul (by norm_num) hu.ne']
    convert div_le_div_of_nonneg_right hlogs hs.le using 1
    · have hsum := ne_of_gt (add_pos hv hw)
      have hcomplement : 1 - q = w / (v + w) := by grind
      simp [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
      rw [hcomplement]
      dsimp [q]
      rw [Real.log_div hv.ne' hsum, Real.log_div hw.ne' hsum,
        Real.log_rpow hprodB, Real.log_rpow hprodC]
      field_simp
      ring
    · rw [Real.log_rpow hprodA]
      field_simp
  simpa only [convolutionProfile, sixfoldProduct, add_comm] using h

/-- The actual three-sector degeneration triples the normalized profile. -/
theorem convolutionProfile_tripling_of_separation
    (hsep : ∀ ψ : Character, ψ.SeparationBound)
    {a h : ℕ} (ht : 0 < χ.meanExponent)
    (ha : 0 < a) (hh : 0 < h) :
    3 * χ.convolutionProfile a h ≤ χ.convolutionProfile a (3 * h + a - 1) := by
  let A  := fun i => (χ.permutedCharacter i).value (convolution a (3 * h + a - 1))
  let B  := fun i => (χ.permutedCharacter i).value (convolution a h)
  let C  := fun i => (χ.permutedCharacter i).value fun x z y => convolution a h x y z
  let p  := fun i => (χ.permutedCharacter i).pX
  let s := 6 * χ.meanExponent
  have hs : 0 < s := by linarith
  have hsum  := χ.sum_permutedCharacter_pX_mean
  have hB i  := (χ.permutedCharacter i).convolution_pos ha hh
  have hC i : 0 ≤ C i := (χ.permutedCharacter i).nonneg _
  have hprod_eq : ∏ i, C i = ∏ i, B i := (χ.sixfoldProduct_swaps _).2
  have hBprod : 0 < ∏ i, B i := Finset.prod_pos fun i _ => hB i
  have hprod : 3 ^ s * ∏ i, B i ≤ ∏ i, A i := by
    have hmul := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun i => 3 ^ p i * B i ^ (2 / 3 : ℝ) * C i ^ (1 / 3 : ℝ))
      (g := A)
      (fun i _ => by
        have := hB i
        have := hC i
        positivity)
      fun i _ => by
        let ψ := χ.permutedCharacter i
        have hv := hB i
        have hw : 0 < C i :=
          ψ.swap23Character.convolution_pos ha hh
        have h0 := value_outerTensor ψ a h false
        have h2 := value_outerTensor ψ a h true
        simp only [Bool.false_eq_true, ↓reduceIte] at h0 h2
        have htag := ψ.sharedFirst_tag_of_separation (hsep ψ) (FiniteLaw.uniformThree)
          (branchFamily  a h) (fun b => by
            fin_cases b
            · exact hv.trans_eq h0.symm
            · exact hw.trans_eq (value_middleTensor ψ a h).symm
            · exact hv.trans_eq h2.symm)
        rw [uniformThree_entropy_factor,
          ψ.value_sharedFirstTensor_eq_sum _ (yLabel a h) (zLabel a h)
            (fun _ _ _ _ => branchFamily_labels), sum_branchFamily] at htag
        simp only [Fin.prod_univ_three,
          h0, value_middleTensor, h2] at htag
        have hresult := htag.trans (ψ.value_polynomialRestrictionDegeneration_le_ring (restriction a h))
        rw [show (2 / 3 : ℝ) = 1 / 3 * 2 by norm_num,
          Real.rpow_mul (ψ.nonneg (convolution a h)), Real.rpow_two]
        simp only [FiniteLaw.uniformThree, A, C, p, ψ, source, sourceWidth, pow_two,
          mul_assoc,  mul_comm, one_div] at hresult ⊢
        exact hresult
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Real.rpow_sum_of_pos (by norm_num  ) p Finset.univ, hsum,
      Real.finsetProd_rpow Finset.univ B fun i _ => (hB i).le,
      Real.finsetProd_rpow Finset.univ C fun i _ => hC i, hprod_eq,
      mul_assoc, ← Real.rpow_add hBprod] at hmul
    norm_num at hmul
    exact hmul
  have hmean := Real.rpow_le_rpow (by positivity) hprod (by positivity : 0 ≤ 1 / s)
  rwa [Real.mul_rpow (by positivity) hBprod.le,
    ← Real.rpow_mul (by norm_num  ), mul_one_div_cancel hs.ne',
    Real.rpow_one] at hmean

/-- The three dot-product exponents of an actual character sum to at most `9/4`. -/
theorem exponent_sum_le_nine_quarters_of_separation_and_convolution
    (hsep : ∀ ψ : Character, ψ.SeparationBound)
    (hconv : ∀ ψ : Character, ψ.ConvolutionBound)
    : χ.pX + χ.pY + χ.pZ ≤ 9 / 4 := by
  by_contra! hbad
  have ht : 0 < χ.meanExponent := by unfold meanExponent; linarith
  let f := χ.convolutionProfile
  have hboundary : f 1 1 = 1 := by
    have h1 (ψ : Character) : ψ.value (convolution 1 1) = 1 :=
      le_antisymm (by simpa using hconv ψ 1 1)
        (ψ.one_le_value_of_coefficient_one ⟨0, 0, 0, rfl⟩)
    simp [f, convolutionProfile, sixfoldProduct, h1]
  have hrank (a : ℕ) (ha : 1 ≤ a) : f a a ≤ (2 * (a : ℝ) - 1) ^ (1 / χ.meanExponent) := by
    let T := convolution (K := ℤ) a a
    let r := a + a - 1
    have hp : χ.sixfoldProduct T ≤ r ^ 6 := by
      calc
        _ ≤ ∏ i : Fin 6, (r : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => (χ.permutedCharacter i).nonneg T)
            fun i _ => hconv (χ.permutedCharacter i) a a
        _ = _ := by simp
    have haa : 1 ≤ a + a := by omega
    convert Real.rpow_le_rpow
      (Finset.prod_nonneg fun i _ => (χ.permutedCharacter i).nonneg T)
      hp (by positivity : 0 ≤ 1 / (6 * χ.meanExponent)) using 1
    all_goals try rfl
    rw [← Real.rpow_natCast r 6, ← Real.rpow_mul (by positivity)]
    simp_all [r] <;> ring
  have hincrement (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
      2 * f a a / (3 * (a : ℝ) - 1) ≤ f a (h + 1) - f a h := by
    let u n := f a (n + 1)
    have hd : Antitone fun n : ℕ => u (n + 1) - u n := by
      apply antitone_nat_of_succ_le
      intro n
      have hc := χ.convolutionProfile_concave_of_separation hsep ht (a := a) (b := n + 2) (by omega) (by omega)
      grind
    have ht n : 3 * u n ≤ u (3 * n + (a + 1)) := by
      convert χ.convolutionProfile_tripling_of_separation hsep ht (a := a) (h := n + 1) (by omega) (by omega) using 2 <;> omega
    have bounds (n k : ℕ) :
        u n + k * (u (n + k + 1) - u (n + k)) ≤ u (n + k) ∧
        u (n + k) ≤ u n + k * (u (n + 1) - u n) := by
      induction k with
      | zero => simp
      | succ k ih =>
        have h₁ := hd (show n ≤ n + k by omega)
        have h₂ := hd (show n + k ≤ n + (k + 1) by omega)
        have h₃ := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg (α := ℝ) k)
        grind
    let j := a - 1
    let k := h - 1
    have hb := (bounds j k).1
    have hu := (bounds (j + k) (2 * (j + k) + (a + 1))).2
    have htt := ht (j + k)
    push_cast at hb hu
    have he : u j ≤ ((j : ℝ) + (a + 1) / 2) * (u (j + k + 1) - u (j + k)) := by
      ring_nf at hb hu htt ⊢
      nlinarith
    have he := he.trans (mul_le_mul_of_nonneg_left (hd (show k ≤ j + k by omega)) (by positivity))
    simp only [u, j, k, Nat.sub_add_cancel ha, Nat.sub_add_cancel hh] at he
    rw [Nat.cast_sub ha] at he
    apply (div_le_iff₀ (by
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha
      linarith)).mpr
    nlinarith
  let D n := f n n
  have hlower : ∀ n : ℕ, 1 ≤ n → n ^ 4 ≤ D n ^ 3 := by
    have hinc a (ha : 1 ≤ a) : D a + 2 * D a / (3 * a - 1) +
        2 * D (a + 1) / (3 * (a + 1) - 1) ≤ D (a + 1) := by
      have h₂ := hincrement (a + 1) a (by omega) ha
      have hs : f a (a + 1) = f (a + 1) a := by
        simp only [f, convolutionProfile, χ.sixfoldProduct_convolution_comm]
      grind
    suffices ∀ k : ℕ, (k + 1) ^ 4 ≤ D (k + 1) ^ 3 by
      rintro (_ | k) hk
      · omega
      · simpa using this k
    intro k
    induction k with
    | zero => simp_all [D]
    | succ k ih =>
      let n : ℝ := k + 1
      let q := (3 * n + 1) * (3 * n + 2) / (3 * n * (3 * n - 1))
      have hn : 0 < n := by positivity
      have hm : 0 < 3 * n - 1 := by grind
      have hq : 0 ≤ q := by positivity
      have hstep : q * D (k + 1) ≤ D (k + 2) := by
        have h := hinc (k + 1) (by omega)
        push_cast at h
        change D (k + 1) + 2 * D (k + 1) / (3 * n - 1) +
          2 * D (k + 2) / (3 * (n + 1) - 1) ≤ D (k + 2) at h
        have hm' : 0 < 3 * (n + 1) - 1 := by linarith
        dsimp [q]
        linear_combination (norm := (field_simp [ hm.ne'] <;> ring_nf))
          ((3 * (n + 1) - 1) / (3 * n)) * h
        exact le_rfl
      have hf : ((n + 1) / n) ^ 4 ≤ q ^ 3 := by
        rw [div_pow, div_pow]
        apply (div_le_div_iff₀ (pow_pos hn _) (pow_pos (mul_pos (by positivity) hm) _)).mpr
        dsimp [n]
        apply sub_nonneg.mp
        ring_nf
        positivity

      have h := (show Odd 3 by decide).pow_le_pow.mpr hstep
      push_cast
      change (n + 1) ^ 4 ≤ D (k + 2) ^ 3
      rw [div_pow, div_le_iff₀ (pow_pos hn 4)] at hf
      nlinarith [mul_le_mul_of_nonneg_left ih (pow_nonneg hq 3)]
  have hexp  := le_of_lt (one_div_pos.mpr ht)
  have hpower : ∀ n : ℕ, 1 ≤ n →
      n ^ (4 : ℝ) ≤
        2 ^ (1 / χ.meanExponent * 3) * (n : ℝ) ^ (1 / χ.meanExponent * 3) := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hbase : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
    have hu : D n ≤ (2 * n) ^ (1 / χ.meanExponent) :=
      (hrank n hn).trans (Real.rpow_le_rpow hbase (by linarith) hexp)
    calc
      _ = _ := by norm_num
      _ ≤ _ := hlower n hn
      _ ≤ _ :=
        (show Odd 3 by decide).pow_le_pow.mpr hu
      _ = _ := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_mul_natCast (show 0 ≤ 2 * (n : ℝ) by positivity) (1 / χ.meanExponent) 3).symm
      _ = _ :=
        Real.mul_rpow (by norm_num) (by positivity)
  have h := rpow_exponent_le_of_nat_bound hpower
  rw [one_div_mul_eq_div, le_div_iff₀ ht] at h
  unfold meanExponent at h
  linarith

end AuxiliarySeparation.Character
end OAI.MatrixMultiplication
