module
public import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.InverseInitialExcludedGeometry
open HeckeFamily InverseInitialExcludedPolynomial IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

end SevenEighths.InverseInitialExcludedGeometry

end

end OAI
