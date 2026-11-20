module

public import GradedNear.Defs

/-!
# Common domains of the response and threshold bounds

The uniform estimates concern the same class of entry families, and use the same tests
on the local zeros. These are binder and formula notations: the hypotheses can still
be introduced separately when applying an estimate.
-/

@[expose] public section
namespace GradedNear

/-- For all sufficiently large levels, at a safe anchor, for admissible entry families.
The non-principal characters must be distinct only if the sieve weight is nonzero. -/
scoped macro "ForLargeEntries " q:ident ι:ident E:ident " of " D:term ", " p:term : term =>
  `(∃ q₀ : ℕ, ∀ $q : ℕ, [NeZero $q] → q₀ ≤ $q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log $q / 3 →
    SafeAnchor $q (NearData.s₁ $D) (2*T+1) → ∀ ($ι : Type) [Fintype $ι] ($E : Entries $q $ι),
    (∀ j, Entries.χ $E j ≠ 1) → (∀ j, |Entries.γ $E j| ≤ T) → (∀ j, Entries.δ $E j ∈ NearData.Δ $D) →
    ((∃ k < NearData.m $D, NearData.h $D k ≠ 0) → Function.Injective (Entries.χ $E)) → $p)

/-- Diagonal including the pair excess, before normalization. -/
scoped notation "rowDiag " D:arg E:arg j:arg =>
  NearData.Dδ D (Entries.δ E j) - NearData.d₁ D + pairExcess D E j

/-- Feature numerator at a real upper bound for an entry's zero. -/
scoped notation "upperTerm " D:arg E:arg j:arg hi:arg =>
  Complex.re (laplace (NearData.f D) ((hi - (anchorOf D E j) : ℝ) : ℂ))

/-- Every kept zero belongs to the requested character and disc. -/
scoped macro "keptInDisc " χ:term:arg γ:term:arg δ:term:arg S:term:arg : term =>
  `(∀ ρ ∈ $S, DirichletCharacter.LFunction $χ ρ = 0 ∧ inDisc[$γ, $δ] ρ)
/-- Omitted zeros on the adverse side of the anchor are far in normalized height.
The binder lets a row describe omission via a set or (for a singleton) inequality. -/
scoped macro "adverseFar " q:term:arg χ:term:arg γ:term:arg σ:term:arg δ:term:arg M:term:arg
    " where " ρ:ident " ↦ " p:term:arg : term =>
  `(∀ $ρ : ℂ, DirichletCharacter.LFunction $χ $ρ = 0 → inDisc[$γ, $δ] $ρ → $p →
    λρ[$q] $ρ < $σ → $M ≤ |$γ - Complex.im $ρ| * Real.log $q)
/-- Total omitted adverse multiplicity in the local disc. -/
scoped macro "adverseCount " q:term:arg χ:term:arg γ:term:arg σ:term:arg δ:term:arg
    " where " ρ:ident " ↦ " p:term:arg : term =>
  `(∑ᶠ $ρ:ident ∈ {$ρ:ident : ℂ | DirichletCharacter.LFunction $χ $ρ = 0 ∧ inDisc[$γ, $δ] $ρ ∧ $p ∧
    λρ[$q] $ρ < $σ}, zmult $χ $ρ)

/-- Existential separation and local radius of the zero estimates. -/
scoped macro "ExistsDiscControls " M:ident δ:ident ", " p:term : term =>
  `(∃ $M:ident : ℝ, 0 < $M ∧ ∃ $δ:ident : ℝ, 0 < $δ ∧ $δ < 1 ∧ $p)

/-- Give every entry a set of kept zeros satisfying the three local tests. -/
scoped macro "ForKept " S:ident " of " D:term:arg E:term:arg q:term:arg ι:term:arg
    " with " δ:term:arg M:term:arg K:term:arg ", " p:term : term =>
  `(∀ $S : $ι → Finset ℂ,
      (∀ j, keptInDisc (Entries.χ $E j) (Entries.γ $E j) $δ ($S j)) →
      (∀ j, adverseFar $q (Entries.χ $E j) (Entries.γ $E j) (anchorOf $D $E j) $δ $M where ρ ↦ (ρ ∉ $S j)) →
      (∀ j, adverseCount $q (Entries.χ $E j) (Entries.γ $E j) (anchorOf $D $E j) $δ where ρ ↦ (ρ ∉ $S j) ≤ $K) → $p)

end GradedNear
