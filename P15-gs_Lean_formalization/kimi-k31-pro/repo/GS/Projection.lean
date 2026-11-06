module

public import GS.Frobenius

@[expose] public section

noncomputable section
open Matrix
namespace GS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsSkew (A : Matrix ι ι ℝ) : Prop := Aᵀ = -A

theorem isSkew_diagonal_zero {A : Matrix ι ι ℝ} (hA : IsSkew A) (i : ι) :
    A i i = 0 := by
  have he : A i i = -A i i := congrFun (congrFun hA i) i
  linarith

end GS
