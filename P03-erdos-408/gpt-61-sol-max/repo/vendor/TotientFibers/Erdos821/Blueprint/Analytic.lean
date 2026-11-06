module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-! Planning interfaces for §§3–4. These declarations are deliberately not an
acceptance artifact: lemma proofs are placeholders, definitions are complete.
All divisions in analytic quantities take place in ℝ or ℂ. -/

@[expose] public section

open scoped BigOperators ContDiff
open Filter MeasureTheory

namespace Erdos821.Blueprint.Analytic

noncomputable section
attribute [local instance] Classical.propDecidable

def L (x : ℝ)  := Real.log x
def T (x : ℝ)  := Real.log (L x)

def e (t : ℝ)  := Complex.exp (2 * Real.pi * t * Complex.I)
def mellin (n t : ℝ)  := Complex.exp (Complex.I * t * Real.log n)


def dp (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ)  :=
  ∑ n ∈ s, c n * mellin n t

def sqNorm (s : Finset ℕ) (c : ℕ → ℂ)  := ∑ n ∈ s, ‖c n‖ ^ 2

structure Geometry where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  c₀ : ℝ
  C₀ : ℝ
  vmin : ℝ
  vmax : ℝ
  q : ℝ
  ell : ℕ
  ordered : 0 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < 0.47
  positive : 0 < c₀ ∧ 0 < C₀ ∧ 0 < vmin ∧ vmin ≤ vmax
  damping : 0 < q ∧ q < 1
  marks : 1 ≤ ell

structure PrimeGroups where
  size : ℕ
  primes : Fin size → Finset ℕ
  small : Finset (Fin size)
  prime : ∀ g p, p ∈ primes g → p.Prime
  disjoint : ∀ g h, g ≠ h → Disjoint (primes g) (primes h)

def PrimeGroups.big (G : PrimeGroups)  := Finset.univ \ G.small
def mass (G : PrimeGroups) (g : Fin G.size)  := ∑ p ∈ G.primes g, 1 / (p : ℝ)
def mu (G : PrimeGroups) (g : Fin G.size) (p : ℕ)  := 1 / (mass G g * p)

def Admissible (P : Geometry) (x : ℝ) (G : PrimeGroups)  :=
  (P.c₀ * T x ≤ G.small.card ∧ (G.small.card : ℝ) ≤ P.C₀ * T x) ∧
  (P.c₀ * T x ≤ G.big.card ∧ (G.big.card : ℝ) ≤ P.C₀ * T x) ∧
  (∀ g, P.vmin ≤ mass G g ∧ mass G g ≤ P.vmax) ∧
  (∀ g p, p ∈ G.primes g →
    if g ∈ G.small then Real.exp (L x ^ P.a) ≤ p ∧ (p : ℝ) ≤ Real.exp (L x ^ P.b)
    else Real.exp (L x ^ P.c) ≤ p ∧ (p : ℝ) ≤ Real.exp (L x ^ P.d)) ∧
  (∀ g, g ∈ G.big → ∃ lo hi : ℝ, ∀ p : ℕ,
    p ∈ G.primes g ↔ p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ hi)

abbrev Label (G : PrimeGroups) (g ) := {p : ℕ // p ∈ G.primes g}
abbrev Tuple (G : PrimeGroups) (k : Fin G.size → ℕ) := ∀ g, Fin (k g) → Label G g

def product (G ) (k ) (z : Tuple G k)  :=
  ∏ g, ∏ j, (z g j).val

def tupleWeight (G ) (k ) (z : Tuple G k)  :=
  ∏ g, ∏ j, mu G g (z g j).val

def expect (G ) (k ) (f : Tuple G k → ℂ)  :=
  ∑ z, (tupleWeight G k z : ℂ) * f z

def tupleNorm (G ) (k ) (f : Tuple G k → ℂ)  :=
  Real.sqrt (∑ z, tupleWeight G k z * ‖f z‖ ^ 2)

def rho (G : PrimeGroups) (k : Fin G.size → ℕ) (n : ℕ)  :=
  ∑ z, if product G k z = n then tupleWeight G k z else 0

def bigSlots (G : PrimeGroups) (k : Fin G.size → ℕ) (m : ℕ)  :=
  (∑ g, k g) > 0 ∧ ∀ g, k g ≤ m ∧ (g ∈ G.small → k g = 0)

abbrev CharacterIndex (Q ) := (r : Fin Q) × DirichletCharacter ℂ (r.val + 1)

def primitiveCharacters (Q ) : Finset (CharacterIndex Q) :=
  Finset.univ.filter fun χ => χ.2.IsPrimitive

def charValue {Q } (χ : CharacterIndex Q) (n : ℕ)  := χ.2 (n : ZMod (χ.1.val + 1))

def cell (h : ℝ) (n : ℕ)  := ⌊Real.log n / h⌋
def cellMass (G : PrimeGroups) (k : Fin G.size → ℕ) (h : ℝ) (j : ℤ)  :=
  ∑ z, if cell h (product G k z) = j then tupleWeight G k z else 0

def cellKernel (G : PrimeGroups) (k : Fin G.size → ℕ) (Q : ℕ) (h ξ : ℝ)
    (D X : ℕ)  :=
  if cell h D = cell h X ∧ ξ ≤ cellMass G k h (cell h X) then
    (cellMass G k h (cell h X) : ℂ)⁻¹ *
      ∑ χ ∈ primitiveCharacters Q, star (charValue χ D) * charValue χ X
  else 0

/-- §3, eq. ideal-product-atom, including all zero-probability fibers. -/
abbrev product_atom_bound_statement  :=
  ∀ (P : Geometry) (m : ℕ),
    ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G →
      ∀ k, bigSlots G k m → ∀ n : ℕ, 0 < n →
      rho G k n ≤ L x ^
        (P.C₀ * (Real.log (Nat.factorial m) + m * Real.log (max 1 P.vmin⁻¹))) / n
/-- §3, Lemma integer bilinear estimate. Origins N and M are unrestricted. -/
abbrev integer_bilinear_statement  :=
  ∀ (C : ℝ) (_ : 0 < C),
    ∃ K : ℝ, 0 < K ∧ ∀ (U V N M α β : ℝ) (u : ℤ) (r : ℕ)
      (s t : Finset ℤ) (a b : ℤ → ℂ),
      1 ≤ U → 1 ≤ V → 1 ≤ r → Nat.Coprime u.natAbs r →
      α = (u : ℝ) / r + β → |β| ≤ (r : ℝ) ^ (-2 : ℤ) →
      (∀ n ∈ s, N ≤ (n : ℝ) ∧ (n : ℝ) ≤ N + C * U) →
      (∀ n ∈ t, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ M + C * V) →
      ‖∑ n ∈ s, ∑ v ∈ t, a n * b v * e (α * n * v)‖ ≤
        K * Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) * Real.sqrt (∑ v ∈ t, ‖b v‖ ^ 2) *
          Real.sqrt (U + (1 + V / r) * (U + r * Real.log (2 * r)))
abbrev cell_kernel_sup_statement  :=
  ∀ (G : PrimeGroups) (k : Fin G.size → ℕ)
    (Q : ℕ) (h ξ : ℝ) (_ : 0 < ξ) (D X : ℕ),
    ‖cellKernel G k Q h ξ D X‖ ≤ (Q : ℝ) ^ 2 / ξ
def comparisonError (G ) (a b )
    (Q : ℕ) (h ξ α ζ : ℝ) (f : Tuple G b → ℂ) (g : Tuple G a → ℂ)  :=
  expect G b fun XB => expect G a fun XA =>
    star (f XB) * g XA *
      (mellin (product G a XA * product G b XB) ζ * e (α * product G a XA * product G b XB) -
      expect G a fun DA => expect G b fun DB =>
        cellKernel G a Q h ξ (product G a DA) (product G a XA) *
        cellKernel G b Q h ξ (product G b DB) (product G b XB) *
        mellin (product G a DA * product G b DB) ζ * e (α * product G a DA * product G b DB))

/-- §3 comparison kernel; Q is rounded down, h and ξ are exact real powers. -/
abbrev comparison_kernel_statement  :=
  ∀ (P : Geometry) (m : ℕ) (A C₄ : ℝ)
    (_ : 0 < A) (_ : 0 ≤ C₄),
    ∃ qexp hexp ξexp : ℝ, 0 < qexp ∧ 0 < hexp ∧ 0 < ξexp ∧
      ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G →
        ∀ a b, bigSlots G a m → bigSlots G b m →
        ∀ (α ζ : ℝ) (f : Tuple G b → ℂ) (g : Tuple G a → ℂ),
        |ζ| ≤ L x ^ C₄ →
        ‖comparisonError G a b ⌊L x ^ qexp⌋₊ (L x ^ (-hexp))
            (L x ^ (-ξexp)) α ζ f g‖ ≤ L x ^ (-A) * tupleNorm G b f * tupleNorm G a g
-- `inclusion_exclusion` is proved in `Erdos821/Leaves/`.




-- `mark_sup` is proved in `Erdos821/Leaves/`.



def CutoffBound (x C lo hi : ℝ) (Ψ : ℝ → ℂ) (bounds : ℕ → ℝ)  :=
  ContDiff ℝ ∞ Ψ ∧ Function.support Ψ ⊆ Set.Icc lo hi ∧
  ∀ j y, ‖iteratedDeriv j Ψ y‖ ≤ bounds j * L x ^ (C * (j + 1))

def primePolynomial (s : Finset ℕ) (b : ℕ → ℂ) (t : ℝ)  :=
  dp s (fun p => b p / (p : ℂ)) t
def occupied (s : Finset ℕ) (b : ℕ → ℂ) (threshold Tmax : ℝ) : Set ℤ :=
  {j | ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
    |t| ≤ Tmax ∧ threshold < ‖primePolynomial s b t‖}

-- `exceptional_times` is proved in `Erdos821/P5/ExceptionalTheorem.lean`.

end
end Erdos821.Blueprint.Analytic
