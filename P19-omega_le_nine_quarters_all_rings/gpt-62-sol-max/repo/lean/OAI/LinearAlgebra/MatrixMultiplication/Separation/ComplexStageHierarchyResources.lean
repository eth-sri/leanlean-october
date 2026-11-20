module

public import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchySeparationRates

public section

@[expose] section

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.StageHierarchyResources

open Filter
open scoped BigOperators Topology

universe u v

local instance (priority := low) {B : Type*} : DecidableEq B := Classical.decEq B

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

end MatrixMultiplication.Foundation.StageHierarchyResources

end

end OAI
