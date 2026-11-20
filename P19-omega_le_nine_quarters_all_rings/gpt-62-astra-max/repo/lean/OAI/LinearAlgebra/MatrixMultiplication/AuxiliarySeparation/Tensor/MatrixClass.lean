module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Resource

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation.TensorResource
open Foundation
variable {K : Type*} [CommSemiring K]

/-- Cycle the legs or reflect in the first leg. Both operations preserve
restriction and binary tensor operations, so act on the spectrum. -/
def permute (reflect : Bool) : FiniteTensor K →o FiniteTensor K where
  toFun a := if reflect then .mk fun x z y => a.coeff x y z else .mk a.coeff.cyclic
  monotone' := by
    rintro a b ⟨f,g,h,e⟩
    cases reflect
    · refine ⟨g,h,f,?_⟩
      funext; simp [Tensor.cyclic, e, Tensor.restrict]; tensor_sums
    · refine ⟨f,h,g,?_⟩
      funext; simp [e, Tensor.restrict]; tensor_sums

def permuteHom (b : Bool) : TensorClass K →*o TensorClass K where
  __ := (permute b).antisymmetrization
  map_one' := by cases b <;> rfl
  map_mul' x y := Quotient.inductionOn₂ x y fun _ _ => by cases b <;> rfl

/-- Diagonal scalars form an ordered multiplicative family. No addition
operation or distributivity laws on tensor classes are needed. -/
def scalars : ℕ →*o TensorClass K where
  toFun n := classOf (scalarTensor (Fin n))
  map_one' := by
    tensor_relabel Equiv.equivPUnit _
    grind [scalarTensor, Tensor.pullback, unitTensor]
  map_mul' m n := by
    tensor_relabel finProdFinEquiv.symm
    funext x y z
    let e : Fin (m*n) ≃ Fin m × Fin n := finProdFinEquiv.symm
    have he (x y : Fin (m*n)) : x = y ↔ (e x).1 = (e y).1 ∧ (e x).2 = (e y).2 := e.injective.eq_iff.symm.trans Prod.ext_iff
    simp only [Tensor.pullback, Tensor.product, scalarTensor, ite_zero_mul_ite_zero, one_mul, he x y, he x z]
    dsimp only [e]; grind
  monotone' := by
    intro i j hij
    apply (classOf_le_iff ..).mpr
    convert IsRestriction.pullback (scalarTensor (Fin j)) (Fin.castLE hij) (Fin.castLE hij) (Fin.castLE hij) using 1
    grind [Tensor.pullback, scalarTensor]

theorem permute_scalar (b : Bool) (n : ℕ) : permuteHom b (scalars n) = scalars (K := K) n := by
  cases b <;> apply congrArg classOf <;> funext <;> simp [Tensor.cyclic, scalarTensor] <;> grind

/-- Dot pairings turn products of dimensions into tensor products. -/
def dotClass : ℕ →*o TensorClass K where
  toFun n := classOf (Tensor.dotPairing n)
  map_one' := by
    tensor_relabel Equiv.equivPUnit _
    grind [Tensor.dotPairing, Tensor.pullback, unitTensor]
  map_mul' i j := by
    refine classOf_eq_of_reindex (Equiv.prodUnique Unit Unit).symm finProdFinEquiv.symm finProdFinEquiv.symm ?_
    funext; simp only [Tensor.pullback, Tensor.product, Tensor.dotPairing, ite_zero_mul_ite_zero, one_mul,
      ← Prod.ext_iff, Equiv.apply_eq_iff_eq]
  monotone' := by
    intro i j hij
    apply (classOf_le_iff ..).mpr
    convert IsRestriction.pullback (Tensor.dotPairing j) id (Fin.castLE hij) (Fin.castLE hij) using 1
    grind [Tensor.pullback, Tensor.dotPairing]

abbrev rotate : TensorClass K →*o TensorClass K := permuteHom false

def triple : TensorClass K →*o TensorClass K := .id _ * rotate * rotate.comp rotate

def matrixClass (m : ℕ) := classOf (squareTensor K m)

theorem matrix_factors (m : ℕ) : matrixClass (K := K) m =
    triple (dotClass m) := by
  let u := (Equiv.prodUnique (Fin m) Unit).symm
  let v := (Equiv.uniqueProd (Fin m) Unit).symm
  let s := Equiv.prodComm (Fin m) (Fin m)
  refine classOf_eq_of_reindex (s.trans (v.prodCongr (.refl _)))
    (s.trans (Equiv.prodUnique _ Unit).symm) (u.prodCongr (.refl _)) ?_
  funext x y z
  change ((if y.2 = z.1 then 1 else 0) * (if x.2 = y.1 then 1 else 0)) * (if z.2 = x.1 then 1 else 0) = (if _ then (1:K) else 0)
  grind

theorem matrixClass_pow (m j : ℕ) : matrixClass (K := K) (m ^ j) = matrixClass m ^ j := by simp [matrix_factors]

theorem matrixClass_mul (a b : ℕ) : matrixClass (K := K) (a*b) = matrixClass a * matrixClass b := by simp [matrix_factors]

theorem diag_le (d : ℕ) : scalars d ≤ matrixClass (K := K) d := by
  apply (classOf_le_iff ..).mpr
  let f (i : Fin d) := (i,i)
  convert IsRestriction.pullback (squareTensor K d) f f f using 1
  funext; simp [Tensor.pullback, squareTensor, scalarTensor, f]; grind

end OAI.MatrixMultiplication.AuxiliarySeparation.TensorResource
