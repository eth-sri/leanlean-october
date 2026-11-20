module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources and the all-fields extension
to support the integral/ring proof. Field-only claims remain explicitly scoped.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

public section

@[expose] section

namespace OAI.MatrixMultiplication.AuxiliarySeparation

open Foundation TensorSemiring
open scoped NNReal

/-- Characters are ordered semiring homomorphisms out of the restriction classes. -/
abbrev Character := TensorClass →+*o ℝ≥0

namespace Character

noncomputable section

variable (χ : Character)
variable {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

def value (T : IntTensor X Y Z) : ℝ≥0 := χ (classOf T)

theorem value_le_of_restriction {T : IntTensor X Y Z} {S : IntTensor U V W}
    (h : IsRestriction S T) : χ.value S ≤ χ.value T :=
  χ.monotone' h

theorem map_product (T : IntTensor X Y Z) (S : IntTensor U V W) :
    χ.value (Tensor.product T S) = χ.value T * χ.value S := by simp [value, classOf_product, _root_.map_mul]

@[simp] theorem value_scalarTensor (r : ℕ) : χ.value (scalarTensor r) = r := by simp [value]

@[simp] theorem value_power (T : IntTensor X Y Z) (n : ℕ) :
    χ.value (Tensor.power T n) = χ.value T ^ n := by
  simp [value, Tensor.power]

def cyclicCharacter : Character := χ.comp (permuteClass true)
def swap23Character : Character := χ.comp (permuteClass false)

/-- The character's growth exponent on matrix multiplication. -/
def exponent : ℝ := Real.logb 2 (χ (matrixClass 2))

theorem value_matrixMultiplication {n : ℕ} (hn : 0 < n) :
    χ (matrixClass n) = (n : ℝ≥0) ^ χ.exponent :=
  monotoneMonoidHom_eq_rpow (χ.toMonoidHom.comp matrixClass) (χ.monotone'.comp matrixClass_mono) hn

/-- The three cyclic orders followed by their reflected orders. -/
def permutedCharacter (i : Fin 6) : Character :=
  ![χ, χ.cyclicCharacter, χ.cyclicCharacter.cyclicCharacter,
    χ.swap23Character, χ.cyclicCharacter.swap23Character,
    χ.cyclicCharacter.cyclicCharacter.swap23Character] i

@[simp] private theorem swap23_dot (m : ℕ) : χ.swap23Character (dotClass m) = χ (dotClass m) := by
  apply congrArg χ
  apply congrArg (fun t => classOf t)
  ext; simp [dot, eq_comm]

/-- Record the six nonnegative values as a multiplicative vector. -/
def classValues : TensorClass →* (Fin 6 → ℝ≥0) :=
  MonoidHom.pi fun i => (χ.permutedCharacter i).toMonoidHom

abbrev values (T : IntTensor X Y Z) := χ.classValues (classOf T)

/-- Geometric normalization is multiplicative on value vectors. -/
def normalize : (Fin 6 → ℝ≥0) →* ℝ≥0 where
  toFun v := (∏ i, v i) ^ (1 / (2 * χ.exponent))
  map_one' := by simp
  map_mul' v w := by simp [Finset.prod_mul_distrib, NNReal.mul_rpow]

theorem normalize_mono (ht : 0 < χ.exponent) : Monotone χ.normalize :=
  fun _ _ h => NNReal.rpow_le_rpow (Finset.prod_le_prod fun i _ => h i) (by positivity)

theorem normalize_const (c : ℝ≥0) :
    χ.normalize (fun _ => c) = c ^ (3 / χ.exponent) := by
  simp [normalize, ← NNReal.rpow_natCast_mul]
  congr 1
  ring

/-- A singleton-leg dot product has normalized value equal to its dimension. -/
theorem normalize_dot (ht : 0 < χ.exponent) {m : ℕ} (hm : 0 < m) :
    χ.normalize (χ.values (dot m)) = m := by
  change (∏ i, χ.permutedCharacter i (dotClass m)) ^ (1 / (2 * χ.exponent)) = _
  have H : (∏ i, χ.permutedCharacter i (dotClass m)) = χ (matrixClass m)^2 := by
    simp [Fin.prod_univ_succ, permutedCharacter, matrixClass, cyclicCharacter, pow_two]
    ring
  rw [H, χ.value_matrixMultiplication hm, ← NNReal.rpow_natCast_mul, ← NNReal.rpow_mul]
  grind [NNReal.rpow_one]

/-- Geometric normalization by the sum of the singleton-leg exponents. -/
def classProfile : TensorClass →* ℝ≥0 := χ.normalize.comp χ.classValues

abbrev symmetrizedProfile (T : IntTensor X Y Z) := χ.classProfile (classOf T)

local macro "symmetrize_swap " e:term : tactic => `(tactic|
  (unfold symmetrizedProfile classProfile normalize
   simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk]
   congr 1
   rw [← Equiv.prod_comp ($e : Equiv.Perm (Fin 6))]
   apply Finset.prod_congr rfl
   intro i _
   fin_cases i <;> rfl))

theorem symmetrizedProfile_swap12 (T : IntTensor X Y Z) :
    χ.symmetrizedProfile (fun y x z => T x y z) = χ.symmetrizedProfile T := by
  symmetrize_swap (Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4)

theorem symmetrizedProfile_swap23 (T : IntTensor X Y Z) :
    χ.symmetrizedProfile (fun x z y => T x y z) = χ.symmetrizedProfile T := by
  symmetrize_swap (Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5)


end
end Character
end OAI.MatrixMultiplication.AuxiliarySeparation
