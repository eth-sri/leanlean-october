module

public import Erdos821.Blueprint.Ideal

/-! Both models use the same group indices and prime sets. P5 needs this bridge. -/

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint.Analytic

abbrev PrimeGroups.graph (P : PrimeGroups) : Graph.PrimeGroups where
  count := P.size
  primes := P.primes
  big := fun g => decide (g ∉ P.small)
  prime := P.prime
  disjoint := P.disjoint

@[simp] theorem graph_small (P : PrimeGroups) : P.graph.smallGroups = P.small := by
  ext g
  simp [Graph.PrimeGroups.smallGroups]

@[simp] theorem graph_big (P : PrimeGroups) : P.graph.bigGroups = P.big := by
  ext g
  simp [Graph.PrimeGroups.bigGroups, PrimeGroups.big]

@[simp] theorem graph_mass (P : PrimeGroups) (g : Fin P.size) : P.graph.V g = mass P g := by
  simp [Graph.PrimeGroups.V, mass]

end Erdos821.Blueprint.Analytic
