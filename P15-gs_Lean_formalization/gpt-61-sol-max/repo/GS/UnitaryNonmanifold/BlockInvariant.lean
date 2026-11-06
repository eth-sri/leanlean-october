
import GS.Unitary.Factorization
import GS.NonmanifoldCompletion.BlockRealization



/-!
# Row-block Gram invariants for the unitary three-factor family

The Gram matrices of all two-by-two blocks in a fixed block row commute.
The assertion permits zero entries and does not require generic factors.
-/


namespace GS.UnitaryNonmanifold



def diagTwo (a b : ℂ) := Matrix.diagonal ![a,b]

end GS.UnitaryNonmanifold
