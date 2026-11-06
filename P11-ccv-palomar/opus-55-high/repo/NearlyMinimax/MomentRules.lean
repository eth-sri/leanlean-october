module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import RoughRegime.Macro

𝗎

/-!
# Finite moment rules

The finite signed rules below are represented by their finite weighted-sum action.
This retains coincident atoms (so the sum of absolute weights is an upper bound on
measure total variation). Polynomial degree bounds count the number of distinct
nodes, and no interpolation property is assumed as a hypothesis.
-/



open Polynomial Finset

section Cardinal

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

𝗇 𝔑 F[X]
𝗇 𝔒 Lagrange.basis s v i
𝗇 𝔓 P.eval $ v i
𝗇 𝔗 Lagrange.eq_interpolate hv hP
𝗇 𝔟 Set.InjOn v s
𝗇 𝔣 P.degree < s.card
𝗃 𝔨 congrArg (fun p => ἀ x) 𝔗
/-- Applying cardinal evaluation weights is evaluation at the chosen point. -/
theorem cardinal_evaluation_exact (s : Finset ι) v
    (hv : 𝔟) (P : 𝔑) (hP : 𝔣) x :
     ∑ i ∈ s, (𝔒).eval x * 𝔓 = P.eval x := by
  have h := 𝔨 p.eval
  simpa only [Lagrange.interpolate_apply, eval_finset_sum, eval_mul, eval_C,
    mul_comm] using h.symm

/-- Coefficients of cardinal polynomials extract that coefficient exactly. -/
theorem cardinal_coefficient_exact (s : Finset ι) v
    (hv : 𝔟) (P : 𝔑) (hP : 𝔣) a :
     ∑ i ∈ s, (𝔒).coeff a * 𝔓 = P.coeff a := by
  have h := congrArg (fun p => p.coeff a) 𝔗
  simp at h
  grind

/-- Differentiating cardinal interpolation gives the finite derivative rule. -/
theorem cardinal_derivative_exact (s : Finset ι) v
    (hv : 𝔟) (P : 𝔑) (hP : 𝔣) x :
     ∑ i ∈ s, (𝔒).derivative.eval x * 𝔓 =
      P.derivative.eval x := by
  have h := 𝔨 p.derivative.eval
  simp only [Lagrange.interpolate_apply, derivative_sum, derivative_C_mul,
    eval_finset_sum, eval_mul, eval_C] at h
  grind

𝗇 𝔎 ∏ j ∈ s.erase i, v j / (v j - v i)
/-- The exterior cardinal weight has the product formula in Lemma 3(a). -/
theorem cardinal_weight_at_zero s (v : ι → F) i :
    (𝔒).eval 0 = 𝔎 := by
  simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_mul,
    eval_C, eval_sub, eval_X]
  grind

section

variable (s : Finset ι)

/-- The explicit exterior product rule reproduces every polynomial in its degree range. -/
theorem exterior_product_rule_exact v
    (hv : 𝔟) (P : 𝔑) (hP : 𝔣) :
     ∑ i ∈ s, 𝔎 * 𝔓 = P.eval 0 := by
  simpa only [cardinal_weight_at_zero] using cardinal_evaluation_exact s v hv P hP 0

/-- The coefficient rule has Kronecker monomial moments. -/
theorem cardinal_coefficient_monomial (v : ι → F)
    (hv : 𝔟) a b (hb : b < s.card) :
     ∑ i ∈ s, (𝔒).coeff a * v i ^ b =
      if b = a then 1 else 0 := by
  have hd : (X ^ b : 𝔑).degree < s.card := by
    simpa
  simpa [coeff_X_pow, eq_comm] using cardinal_coefficient_exact s v hv (X ^ b) hd a

end

end Cardinal

𝗇 𝔥 2 * q + 2
𝗇 𝔄 Fin 𝔥
𝗇 𝔠 2 * q + 1
/-- The fixed scalar-response nodes from Lemma 3(c). -/
def responseNode (q : ℕ) (j : 𝔄) : ℝ :=
  (j.val : ℝ) / (𝔠 : ℕ)

theorem responseNode_injective q : Function.Injective $ responseNode q := by
  intro i j hij
  have hn : (𝔠 : ℝ) ≠ 0 := by positivity
  have h : (i.val : ℝ) = j.val := by
    apply (div_left_inj' hn).mp
    simpa [responseNode] using hij
  aesop

/-- The scalar-response extraction weights. -/
def responseWeight (q : ℕ) (j : 𝔄) : ℝ :=
  (Lagrange.basis Finset.univ (responseNode q) j).coeff 2

𝗇 𝔘 responseNode q j
𝗇 𝔡 responseWeight q j
𝗃 𝔧 ἀ Finset.univ (responseNode q) (responseNode_injective q).injOn
/-- The paper's fixed rule extracts the quadratic coefficient, including zero mass and mean. -/
theorem response_rule_moments q a (ha : a ≤ 𝔠) :
     ∑ j : 𝔄, 𝔡 * 𝔘 ^ a =
      if a = 2 then 1 else 0 := 𝔧 cardinal_coefficient_monomial 2 a $ by simpa using by omega

/-- Exactness of the fixed quadratic-extraction rule on every polynomial of the stated degree. -/
theorem response_rule_exact (q : ℕ) (P : ℝ[X]) (hP : P.degree < 𝔥) :
     ∑ j : 𝔄, 𝔡 * P.eval 𝔘 =
      P.coeff 2 := 𝔧 cardinal_coefficient_exact P (by simpa using hP) 2

/-- The fixed response rule has zero total mass. -/
theorem response_zero_mass q :
     ∑ j : 𝔄, 𝔡 = 0 := by
  simpa using response_rule_moments q 0 $ by omega

/-- The fixed response rule has zero first moment. -/
theorem response_zero_mean q :
     ∑ j : 𝔄, 𝔡 * 𝔘 = 0 := by
  simpa using response_rule_moments q 1 $ by omega

/-- When at least three nodes are present, the second moment is one. -/
theorem response_second_moment q (hq : 1 ≤ q) :
     ∑ j : 𝔄, 𝔡 * 𝔘 ^ 2 = 1 := by
  simpa using response_rule_moments q 2 $ by omega

/-- A fair sign, represented on the two-point Boolean space. -/
def fairSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem fairSign_abs b : |fairSign b| = 1 := by cases b <;> norm_num [fairSign]

private theorem finite_sum_abs_bound [Fintype κ] (g b : κ → ℝ)
    (h : ∀ k, |g k| ≤ b k) : |∑ k, g k| ≤ ∑ k, b k := (Finset.abs_sum_le_sum_abs ..).trans
    $ Finset.sum_le_sum fun k hk => h k

section Covariance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

𝗇 𝔊 2 * C
𝗃 𝔦 if ἀ = k then 1 else 0
𝗇 𝔏 fairSign s * 𝔦 i
𝗇 𝔐 fairSign t * 𝔦 j
𝗇 𝔞 ι → ℝ
/-- Fixed atoms of the covariance rule. They do not depend on the matrix. -/
def covarianceAtom (C : ℝ) (i j : ι) (s t : Bool) : 𝔞 :=
  fun k => (𝔏 +
    𝔐) / 𝔊

𝗇 𝔇 C ^ 2 / 2
𝗇 𝔈 ι → 𝔞
𝗇 𝔍 A i j
𝗃 𝔩 𝔇 * ἀ * fairSign s * fairSign t
/-- The factor `1/4` from fair sign averaging is included in the weight. -/
def covarianceWeight (C : ℝ) (A : 𝔈) (i j : ι) (s t : Bool) : ℝ :=
  𝔩 𝔍

𝗇 𝔅 covarianceWeight C A i j s t
𝗇 𝔜 covarianceAtom C i j s t
𝗇 𝔉 f 𝔜
𝗇 𝔛 ∑ s : Bool, ∑ t : Bool, 𝔅 * 𝔉
/-- The finite signed covariance kernel evaluated against a function. -/
def covarianceAction (C : ℝ) (A : 𝔈) (f : 𝔞 → ℝ) : ℝ :=
  ∑ i, ∑ j, 𝔛

𝗇 𝔙 𝔩 a
private theorem sign_mass (C a : ℝ) :
     ∑ s : Bool, ∑ t : Bool, 𝔙 = 0 := by
  simp [fairSign]

𝗇 𝔔 fairSign s * x + fairSign t * y
𝗇 𝔤 𝔔 / 𝔊
private theorem sign_mean (C a x y : ℝ) :
     ∑ s : Bool, ∑ t : Bool,
      𝔙 *
        𝔤 = 0 := by
  simp [fairSign]
  ring

private theorem sign_second (C a x y u v : ℝ) (hC : C ≠ 0) :
     ∑ s : Bool, ∑ t : Bool,
      𝔙 *
        (𝔤 *
          ((fairSign s * u + fairSign t * v) / 𝔊)) =
      a / 2 * (x * v + y * u) := by
  simp only [Fintype.sum_bool, fairSign, Bool.false_eq_true, ↓reduceIte]
  field_simp
  ring

𝗇 𝔚 covarianceAction C A
/-- The action is additive in the test function. -/
theorem covarianceAction_add C (A : 𝔈)
    f g :
    𝔚 (fun x => f x + g x) =
      𝔚 f + 𝔚 g := by
  simp only [covarianceAction, mul_add, Finset.sum_add_distrib]

/-- The action is homogeneous in the test function. -/
theorem covarianceAction_mul C a (A : 𝔈)
    f :
    𝔚 (fun x => a * f x) = a * 𝔚 f := by
  simp only [covarianceAction, mul_left_comm, Finset.mul_sum]

/-- The action commutes with a finite sum of test functions. -/
theorem covarianceAction_sum S C
    A (f : κ → 𝔞 → ℝ) :
    𝔚 (fun x => ∑ i ∈ S, f i x) =
      ∑ i ∈ S, 𝔚 (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [covarianceAction]
  | @insert k S hk ih =>
      simp only [Finset.sum_insert hk]
      rw [covarianceAction_add, ih]

/-- The covariance rule annihilates constants. -/
theorem covariance_zero_mass C (A : 𝔈) :
    𝔚 (fun _ => 1) = 0 := by
  simp only [covarianceAction, covarianceWeight, mul_one]
  simp_rw [sign_mass]
  simp

/-- The covariance rule annihilates each coordinate. -/
theorem covariance_zero_mean C A (k : ι) :
    𝔚 (fun x => x k) = 0 := by
  simp only [covarianceAction, covarianceWeight, covarianceAtom]
  simp_rw [sign_mean]
  simp

𝗇 𝔖 covarianceAction C A fun x => x k * x l
/-- Without a symmetry assumption the second moment is the matrix's symmetric part. -/
theorem covariance_second_moment C A (hC : C ≠ 0) (k l : ι) :
    𝔖 = (A k l + A l k) / 2 := by
  simp only [covarianceAction, covarianceWeight, covarianceAtom]
  simp_rw [sign_second C _ _ _ _ _ hC]
  simp [mul_add, Finset.sum_add_distrib]
  ring

/-- For symmetric matrices the covariance rule has precisely the prescribed second moment. -/
theorem covariance_second_moment_symmetric C A
    (hC : C ≠ 0) (hA : ∀ i j, 𝔍 = A j i) (k l : ι) :
    𝔖 = A k l := by
  rw [covariance_second_moment C A hC, hA l k]
  ring

/-- Each atom lies in the coefficient ball of radius `1/C`. -/
theorem covarianceAtom_mem_ball C (hC : 0 < C) (i j : ι) s t :
     ∑ k, |𝔜 k| ≤ C⁻¹ := by
  have hden : 0 < 𝔊 := by positivity
  calc
     ∑ k, |𝔜 k| ≤
        ∑ k, (|𝔏| +
          |𝔐|) / 𝔊 := by
      apply Finset.sum_le_sum
      intro k hk
      dsimp [covarianceAtom]
      rw [abs_div, abs_of_pos hden]
      exact div_le_div_of_nonneg_right (abs_add_le ..) $ le_of_lt hden
    _ = C⁻¹ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp [apply_ite abs]
      ring

𝗇 𝔢 2 * C ^ 2
/-- The sum of absolute atom weights is the variation bound in the paper. -/
theorem covariance_weight_variation C (A : 𝔈) :
     ∑ i, ∑ j, ∑ s : Bool, ∑ t : Bool, |𝔅| =
      𝔢 * ∑ i, ∑ j, |𝔍| := by
  have hw i j s t : |𝔅| = 𝔇 * |𝔍| := by
    dsimp [covarianceWeight]
    rw [abs_mul, abs_mul, abs_mul, abs_div]
    simp
  simp_rw [hw]
  simp only [Fintype.sum_bool]
  calc
     ∑ i, ∑ j, (𝔇 * |𝔍| + 𝔇 * |𝔍| +
      (𝔇 * |𝔍| + 𝔇 * |𝔍|)) =
      ∑ i, ∑ j, 𝔢 * |𝔍| := by
        ring
    _ = _ := by simp only [Finset.mul_sum]

/-- The signed-rule action is bounded by the atom variation times a uniform bound. -/
theorem covarianceAction_abs_le C B (A : 𝔈)
    f
    (hf : ∀ i j s t, |𝔉| ≤ B) :
    |𝔚 f| ≤ (𝔢 * ∑ i, ∑ j, |𝔍|) * B := by
  have ht i j s t :
      |𝔅 * 𝔉| ≤
        |𝔅| * B := by
    rw [abs_mul]
    bound
  have h := finite_sum_abs_bound
    (fun i => ∑ (j : ι), 𝔛)
    (fun i => ∑ (j : ι), ∑ s : Bool, ∑ t : Bool, |𝔅| * B)
     fun i => finite_sum_abs_bound _ _ fun j =>
      finite_sum_abs_bound _ _ fun s => finite_sum_abs_bound _ _ $ ht i j s
  simpa only [covarianceAction, ← Finset.sum_mul, covariance_weight_variation] using h
