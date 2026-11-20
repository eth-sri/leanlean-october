module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34.Core

noncomputable section

def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * t * Complex.I)

structure PrimeGroups where
  size : ℕ
  primes : Fin size → Finset ℕ
  small : Finset (Fin size)
  prime : ∀ g p, p ∈ primes g → p.Prime
  disjoint : ∀ g h, g ≠ h → Disjoint (primes g) (primes h)

def mass (G : PrimeGroups) (g : Fin G.size) : ℝ := ∑ p ∈ G.primes g, 1 / (p : ℝ)
def mu (G : PrimeGroups) (g : Fin G.size) (p : ℕ) : ℝ := 1 / (mass G g * p)
def Label (G : PrimeGroups) (g : Fin G.size) := {p : ℕ // p ∈ G.primes g}
def Tuple (G : PrimeGroups) (k : Fin G.size → ℕ) := ∀ g, Fin (k g) → Label G g

instance (G : PrimeGroups) (g : Fin G.size) : Fintype (Label G g) :=
  inferInstanceAs (Fintype ↥(G.primes g))
instance (G : PrimeGroups) (k : Fin G.size → ℕ) : Fintype (Tuple G k) :=
  inferInstanceAs (Fintype (∀ g, Fin (k g) → Label G g))

def product (G : PrimeGroups) (k : Fin G.size → ℕ) (z : Tuple G k) : ℕ :=
  ∏ g, ∏ j, (z g j).val
def tupleWeight (G : PrimeGroups) (k : Fin G.size → ℕ) (z : Tuple G k) : ℝ :=
  ∏ g, ∏ j, mu G g (z g j).val
def rho (G : PrimeGroups) (k : Fin G.size → ℕ) (n : ℕ) : ℝ :=
  ∑ z, if product G k z = n then tupleWeight G k z else 0

end
end Erdos821.S34.Core
