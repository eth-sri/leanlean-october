module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Perm

/-! Finite data for §2 of Weighted dilation graphs. No placeholder proofs. -/

@[expose] public section

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

/-- §1 logarithmic scales. -/
def L (x : ℝ) : ℝ := Real.log x
def T (x : ℝ) : ℝ := Real.log (L x)

structure FixedData where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  c₀ : ℝ
  C₀ : ℝ
  vMin : ℝ
  vMax : ℝ
  q : ℝ
  ell : ℕ
  a_pos : 0 < a
  ab : a < b
  bc : b < c
  cd : c < d
  d_lt : d < (47 : ℝ) / 100
  c₀_pos : 0 < c₀
  C₀_pos : 0 < C₀
  vMin_pos : 0 < vMin
  vMax_pos : 0 < vMax
  q_pos : 0 < q
  q_lt : q < 1

/-- def:prime-groups. Small and big groups are separated by a Boolean flag. -/
structure PrimeGroups where
  count : ℕ
  primes : Fin count → Finset ℕ
  big : Fin count → Bool
  prime : ∀ g p, p ∈ primes g → Nat.Prime p
  disjoint : ∀ g h, g ≠ h → Disjoint (primes g) (primes h)

namespace PrimeGroups
variable (P : PrimeGroups)
abbrev Group := Fin P.count
abbrev Prime (g : P.Group) := {p : ℕ // p ∈ P.primes g}
def omegaGroup (g : P.Group) (n : ℤ) : ℕ := (P.primes g |>.filter (fun p : ℕ => (p : ℤ) ∣ n)).card
def omega (n : ℤ) : ℕ := ∑ g, P.omegaGroup g n

abbrev BigGroup := {g : P.Group // P.big g = true}
abbrev BigLabels (M : ℕ) := (g : P.BigGroup) → Fin M → P.Prime g.val
abbrev BigAux (J : ℕ) := (g : P.BigGroup) → Fin J → P.Prime g.val

end PrimeGroups

/-- Patterns and coefficients; K has only big-label arguments. -/
structure Pattern (P : PrimeGroups) (J ell m : ℕ) where
  changed : P.Group → Finset (Fin J)
  small : ∀ g, P.big g = false → changed g = ∅
  bound : ∀ g, (changed g).card ≤ m
  coefficient : P.BigLabels (J + ell) → P.BigLabels (J + ell) → P.BigAux J → ℂ
  coefficient_aux_ext : ∀ a b u v,
    (∀ g i, i ∈ changed g.val → u g i = v g i) → coefficient a b u = coefficient a b v

namespace Pattern
variable {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)

end Pattern

/-- Finite family; supremum is a finite maximum including zero. -/
structure Model (F : FixedData) (P : PrimeGroups) (J m : ℕ) where
  patternCount : ℕ
  pattern : Fin patternCount → Pattern P J F.ell m
  k : ℤ
  zeta : ℝ

namespace Model
variable {F : FixedData} {P : PrimeGroups} {J m : ℕ} (A : Model F P J m)

-- The maximum does not require a nonempty label space when evaluated via `sSup`.
end Model

namespace Model
variable {F : FixedData} {P : PrimeGroups} {J m : ℕ} (A : Model F P J m)

end Model

namespace PrimeGroups
variable (P : PrimeGroups)

end PrimeGroups

namespace PrimeGroups
variable (P : PrimeGroups)
instance primeNeZero (g : P.Group) (p : P.Prime g) : NeZero p.val :=
  ⟨(P.prime g p.val p.property).ne_zero⟩

end PrimeGroups

/-- Birth collections are disjoint nonsingleton blocks of potential addresses. -/
def BirthCollection {a : ℕ} (π : Finset (Finset (Fin a))) : Prop :=
  (∀ B ∈ π, 2 ≤ B.card) ∧ (π : Set (Finset (Fin a))).Pairwise Disjoint

/-- Equality rank adds |B|-1 separately for each block. -/
def birthRank {a : ℕ} (π : Finset (Finset (Fin a))) : ℕ := ∑ B ∈ π, (B.card - 1)

def birthMobius {a : ℕ} (π : Finset (Finset (Fin a))) : ℤ :=
  ∏ B ∈ π, (-1 : ℤ) ^ (B.card - 1) * (Nat.factorial (B.card - 1) : ℤ)

def birthEvent {a : ℕ} (performed : Finset (Fin a)) (value : Fin a → ℕ)
    (π : Finset (Finset (Fin a))) : Prop :=
  ∀ B ∈ π, B ⊆ performed ∧ ∀ i ∈ B, ∀ j ∈ B, value i = value j

end Erdos821.S2
