module

public import Erdos821.Blueprint.Analytic
public import Erdos821.S34.Hoeffding
public import Erdos821.S34.BilinearEstimate
public import Erdos821.S34.Probability

@[expose] public section


namespace Erdos821.S34Core

/-- The earlier standalone finite data has the same fields as the shared
analytic interface. This conversion reduces definitionally on every field. -/
def coreGroups (G : Blueprint.Analytic.PrimeGroups) : S34.Core.PrimeGroups where
  size := G.size
  primes := G.primes
  small := G.small
  prime := G.prime
  disjoint := G.disjoint

end Erdos821.S34Core

namespace Erdos821.Blueprint.Analytic

theorem integer_bilinear_proof : Erdos821.Blueprint.Analytic.integer_bilinear_statement :=
  @Erdos821.S34.Proofs.integer_bilinear

end Erdos821.Blueprint.Analytic
