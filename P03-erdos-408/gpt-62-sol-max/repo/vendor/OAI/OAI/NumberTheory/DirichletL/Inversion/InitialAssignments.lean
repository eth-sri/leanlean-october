module

public import OAI.NumberTheory.DirichletL.Inversion.InitialQuotientGeometry

@[expose] public section

namespace OAI.SevenEighths.InverseInitialQuotientGeometry
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

/-- All admissible assignments of slots to elements and of the remaining slots
    to disjoint, norm-bounded lists of primes. -/
abbrev ForInitialAssignments {ι : Type*} (N : ι → ℝ) (K : ℕ) (Z : ℝ)
    (P : ∀ (σ : Type) [DecidableEq σ], Finset σ → Finset σ → (σ → Finset ι) →
      (σ → ℝ) → (σ → ι → ℂ) → (σ → O) → (σ → ℝ) → (σ → ℝ) → (σ → ℝ) →
      (σ → ℝ → ℂ) → Prop) : Prop :=
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset ι)(Hslot:σ→ℝ)(coeff:σ→ι→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,N P≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    P σ all assigned lists Hslot coeff qelem z al bl primeW

/-- The scale identities and margins used to initialize the source estimate. -/
abbrev ForInitialSourceScales {σ : Type*} [DecidableEq σ] (all assigned : Finset σ)
    (Hslot z bl : σ → ℝ) (Z cap η gap : ℝ) (P : ℝ → ℝ → ℝ → Prop) : Prop :=
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    P D m r

end OAI.SevenEighths.InverseInitialQuotientGeometry
