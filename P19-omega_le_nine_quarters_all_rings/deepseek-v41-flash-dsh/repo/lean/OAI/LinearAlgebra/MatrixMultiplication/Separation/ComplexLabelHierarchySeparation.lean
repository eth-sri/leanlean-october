module

public import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteSeparation
public import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexAuxiliarySeparation
public import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteControl
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexLocalMaps
public import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexSharedAuxiliaryBank

public section

@[expose] section

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace LabelHierarchySeparation

section Bank

variable {K I : Type*} [CommSemiring K] [Fintype I]
variable {X Y Z : I → Type*}

variable {Node : Type*} [Fintype Node]

end Bank

section PrefixSeparation

variable {X Y Z Prefix Label Pairing G : Type*}
variable [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [DecidableEq Label] [DecidableEq Pairing]

@[simp] theorem separated_coefficient
    (T : Tensor ℂ X Y Z) (lx : X → Label)
    (x : X) (y : Y) (z : Z) (u : Pairing) :
    separatedTensor lx T (x, u) (y, u) (z, lx x) = T x y z := by
  simp [separatedTensor]

end PrefixSeparation

section ExactPools

variable {X Y Z Prefix Label : Type*} [DecidableEq Label]

def poolCode (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (prior : X → Prefix) (label : X → Label)
    (allowed : ∀ x, label x ∈ pool (prior x)) : X → Fin k :=
  fun x => enumerate (prior x) ⟨label x, allowed x⟩

omit [DecidableEq Label] in
@[simp] theorem poolCode_decode (pool : Prefix → Finset Label) {k : ℕ}
    (enumerate : ∀ p, ↥(pool p) ≃ Fin k)
    (prior : X → Prefix) (label : X → Label)
    (allowed : ∀ x, label x ∈ pool (prior x)) (x : X) :
    ((enumerate (prior x)).symm (poolCode pool enumerate prior label allowed x)).val =
      label x := by
  simp [poolCode]

end ExactPools

section SharedBranches

variable {K X Y Z A B C A' B' C' Label : Type*}
variable [CommSemiring K] [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype A] [Fintype B] [Fintype C] [Fintype Label]

end SharedBranches

section FiniteAssembly

universe u

variable {K : Type*} [CommSemiring K]
variable {X Y Z A B C : ℕ → Type*}

def AuxiliaryCoordinates (A : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => AuxiliaryCoordinates A n × A n

instance auxiliaryCoordinatesFintype [∀ n, Fintype (A n)] (n : ℕ) :
    Fintype (AuxiliaryCoordinates A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
      letI : Fintype (AuxiliaryCoordinates A n) := ih
      exact inferInstanceAs (Fintype (AuxiliaryCoordinates A n × A n))

end FiniteAssembly

end LabelHierarchySeparation
end MatrixMultiplication.Foundation

end OAI
