module

public import GS.Unitary.Factorization
public import GS.NonmanifoldCompletion.BlockRealization

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Row-block Gram invariants for the unitary three-factor family

The Gram matrices of all two-by-two blocks in a fixed block row commute.
The assertion permits zero entries and does not require generic factors.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.UnitaryNonmanifold
open GS.UnitaryGeometry

def cBlock {q : ℕ} (M : CMat (q*2)) (i j : Fin q) : CMat 2 :=
  fun a b => M (finProdFinEquiv (i,a)) (finProdFinEquiv (j,b))

def diagTwo (a b : ℂ) : CMat 2 := Matrix.diagonal ![a,b]

end GS.UnitaryNonmanifold
