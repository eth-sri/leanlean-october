module

public import RequestProject.Pigeonhole
public import RequestProject.SubgroupCompactness

@[expose] public section

/-!
# Theorem A: the formal skeleton

Theorem A of the paper reads: for a connected two-complex `K` the following are
equivalent.

1. For every `n ≥ 1` there is a chain `K = K₀ ⊊ K₁ ⊊ ⋯ ⊊ Kₙ` of two-complexes
   in which every inclusion induces zero on `π₂`.
2. `K` has a connected acyclic regular cover.

Homotopy theory of two-complexes (`π₁`, `π₂`, Hurewicz, covering spaces, the
CAT(0) cube complexes behind the blocks `B_q`) is far outside what can be built
here, so the notions occurring in Theorem A are packaged in the interface
`TwoComplexData`, and the geometric statements proved in the paper are recorded
as explicit hypotheses:

* `RelativeInputs` records Lemma 3.1 (the initial Cockcroft pair `D ⊂ Y_D`)
  together with the properties of the replacement operation `T` and its
  terminal extension `Q` established in Lemmas 3.9 and 3.10;
* `SufficiencyInputs` adds the descent step, Proposition 3.11;
* `NecessityInputs` records the Fox-boundary input of Section 2, namely
  formula (2.3) relating a chain to normal subgroups of `G = π₁(K)`, the finite
  determinacy of the requirements, their stability under intersections of
  chains, Lemma 2.1 in the form "the commutator subgroup inherits the
  requirements", and the identification of an acyclic regular cover with a
  perfect normal subgroup satisfying them.

What *is* proved here is the entire bookkeeping of the paper's two inductions:
the construction of relative chains of arbitrary length from the operations `T`
and `Q` (Proposition 3.7), the descent to `K` (so `(2) ⇒ (1)`), and the
pigeonhole/compactness/minimality derivation of a perfect normal subgroup from
chains of every finite length (so `(1) ⇒ (2)`).
-/

namespace FiniteChains

universe u

/-- The notions of Theorem A, as an abstract interface. -/
structure TwoComplexData where
  /-- The two-complexes under consideration. -/
  Cx : Type u
  /-- `Sub K L` : `K` is a subcomplex of `L` (all cells of `K` are retained). -/
  Sub : Cx → Cx → Prop
  sub_refl : ∀ K, Sub K K
  sub_trans : ∀ {K L M}, Sub K L → Sub L M → Sub K M
  /-- The Hurewicz map of the complex vanishes. -/
  Cockcroft : Cx → Prop
  /-- `ZeroPi2 K L` : the inclusion `K ⊆ L` induces the zero map on `π₂`. -/
  ZeroPi2 : Cx → Cx → Prop
  /-- `Pi1Trivial K L` : the map `π₁(K) → π₁(L)` is trivial. -/
  Pi1Trivial : Cx → Cx → Prop
  /-- The complex is acyclic. -/
  Acyclic : Cx → Prop
  /-- `IsAcyclicCover D K` : `D` is a connected acyclic regular cover of `K`. -/
  IsAcyclicCover : Cx → Cx → Prop

variable (W : TwoComplexData)

/-- A chain `c 0 ⊊ c 1 ⊊ ⋯ ⊊ c n` all of whose inclusions are zero on `π₂`: condition (1)
of Theorem A. -/
structure IsZeroChain (c : ℕ → W.Cx) (n : ℕ) : Prop where
  sub : ∀ i < n, W.Sub (c i) (c (i + 1))
  strict : ∀ i < n, c i ≠ c (i + 1)
  zero : ∀ i < n, W.ZeroPi2 (c i) (c (i + 1))

/-- The chains produced by Proposition 3.7: a chain over the fixed acyclic core `D`, with
all terms Cockcroft and with `π₁(D)` killed from the first step on. -/
structure IsRelativeChain (D : W.Cx) (c : ℕ → W.Cx) (n : ℕ) : Prop extends IsZeroChain W c n where
  base : c 0 = D
  cockcroft : ∀ i ≤ n, W.Cockcroft (c i)
  pi1 : ∀ i, 1 ≤ i → i ≤ n → W.Pi1Trivial D (c i)

/-- Condition (2) of Theorem A. -/
def HasAcyclicRegularCover (K : W.Cx) : Prop := ∃ D, W.IsAcyclicCover D K

/-!
## Input from Section 3: the replacement operation and its terminal extension
-/

/-- The geometric input of Section 3 over a fixed acyclic core `D`: the initial Cockcroft
pair of Lemma 3.1, and the operations `T` (replacement) and `Q` (terminal extension) with
the properties established in Lemmas 3.9 and 3.10. -/
structure RelativeInputs (D : W.Cx) where
  /-- `D` is acyclic, hence Cockcroft. -/
  cockcroft_core : W.Cockcroft D
  /-- The complex `Y_D` of Lemma 3.1. -/
  Y : W.Cx
  sub_Y : W.Sub D Y
  ne_Y : D ≠ Y
  cockcroft_Y : W.Cockcroft Y
  zero_Y : W.ZeroPi2 D Y
  pi1_Y : W.Pi1Trivial D Y
  /-- The replacement operation `T` of Section 3.4. -/
  repl : W.Cx → W.Cx
  /-- The terminal extension `Q` of Section 3.4. -/
  term : W.Cx → W.Cx
  /-- `T(D) = D`: the core is retained literally. -/
  repl_core : repl D = D
  /-- `T` respects labelled inclusions. -/
  repl_mono : ∀ P P', W.Sub P P' → W.Sub (repl P) (repl P')
  /-- Strictness is preserved (fresh generators and fresh block lists). -/
  repl_strict : ∀ P P', W.Sub P P' → P ≠ P' → repl P ≠ repl P'
  /-- `T` preserves Cockcroftness (Lemma 3.9). -/
  repl_cockcroft : ∀ P, W.Cockcroft P → W.Cockcroft (repl P)
  /-- `T` preserves zero maps on `π₂` (Lemma 3.9). -/
  repl_zero : ∀ P P', W.Sub P P' → W.ZeroPi2 P P' → W.ZeroPi2 (repl P) (repl P')
  /-- `T` preserves the triviality of the core group. -/
  repl_pi1 : ∀ P, W.Pi1Trivial D P → W.Pi1Trivial D (repl P)
  /-- `Q(P)` literally extends `T(P)` (Lemma 3.10). -/
  sub_term : ∀ P, W.Cockcroft P → W.Pi1Trivial D P → W.Sub (repl P) (term P)
  ne_term : ∀ P, W.Cockcroft P → W.Pi1Trivial D P → repl P ≠ term P
  /-- `Q(P)` is Cockcroft (Lemma 3.10). -/
  cockcroft_term : ∀ P, W.Cockcroft P → W.Pi1Trivial D P → W.Cockcroft (term P)
  /-- `T(P) ⊂ Q(P)` is zero on `π₂` (Lemma 3.10). -/
  zero_term : ∀ P, W.Cockcroft P → W.Pi1Trivial D P → W.ZeroPi2 (repl P) (term P)
  /-- The core group stays trivial in `Q(P)`. -/
  pi1_term : ∀ P, W.Pi1Trivial D P → W.Pi1Trivial D (term P)

variable {W}

variable (W)

/-- The remaining input for `(2) ⇒ (1)`: relative chains exist over any acyclic complex,
acyclic covers are acyclic, and the descent of Proposition 3.11. -/
structure SufficiencyInputs where
  rel : ∀ D : W.Cx, W.Acyclic D → RelativeInputs W D
  acyclic_of_cover : ∀ D K : W.Cx, W.IsAcyclicCover D K → W.Acyclic D
  /-- **Proposition 3.11**: a relative chain over an acyclic regular cover `D` of `K`
  descends to a chain of Cockcroft complexes over `K` with all maps zero on `π₂`. -/
  descent : ∀ (K D : W.Cx) (c : ℕ → W.Cx) (n : ℕ), W.IsAcyclicCover D K →
      IsRelativeChain W D c n →
      ∃ e : ℕ → W.Cx, e 0 = K ∧ IsZeroChain W e n ∧ ∀ i ≤ n, W.Cockcroft (e i)

variable {W}

/-!
## Input from Section 2: Fox boundaries and the requirements (2.2)
-/

/-- The input of Section 2 for a fixed complex `K`.  `Req` indexes the requirements (2.2),
one for each finitely supported coefficient vector, integrally and modulo every prime;
`Sat N v` says that the requirement `v` holds for the normal subgroup `N`, i.e. that the
Fox boundary `∂_{2,N}` does not kill `v`. -/
structure NecessityInputs (W : TwoComplexData) (K : W.Cx) where
  /-- The fundamental group `G = π₁(K)`. -/
  G : Type u
  grp : Group G
  /-- The requirements (2.2). -/
  Req : Type u
  /-- `Sat N v` : the requirement `v` is satisfied by the normal subgroup `N`. -/
  Sat : @Subgroup G grp → Req → Prop
  /-- **Formula (2.3)**: a chain of `n` inclusions starting at `K` supplies `n+1` normal
  subgroups of `G` such that a requirement failing at one stage holds at all later
  stages. -/
  chain_subgroups : ∀ (c : ℕ → W.Cx) (n : ℕ), c 0 = K → IsZeroChain W c n →
      ∃ M : ℕ → @Subgroup G grp, (∀ r, @Subgroup.Normal G grp (M r)) ∧
        ∀ r v, ¬ Sat (M r) v → ∀ s, r < s → s ≤ n → Sat (M s) v
  /-- Each requirement depends on finitely many decisions `g ∈ M`.  For the Fox
  requirements this is proved in `FoxRequirement.lean`
  (`FiniteChains.foxSat_finitelyDetermined`). -/
  det : @FinitelyDetermined G grp Req Sat
  /-- Requirements pass to intersections of decreasing chains of normal subgroups. -/
  sat_sInf_chain : ∀ C : Set (@Subgroup G grp), IsChain (· ≤ ·) C → C.Nonempty →
      (∀ N ∈ C, @Subgroup.Normal G grp N ∧ ∀ v, Sat N v) → ∀ v, Sat (sInf C) v
  /-- **Lemma 2.1**: if `N` satisfies all requirements then so does `[N, N]`.  For the Fox
  requirements this is proved in `FoxCommutator.lean`
  (`FiniteChains.foxSat_commutator_forall`), assuming only that `N/[N, N]` is torsion
  free. -/
  sat_commutator : ∀ N : @Subgroup G grp, @Subgroup.Normal G grp N → (∀ v, Sat N v) →
      ∀ v, Sat ⁅N, N⁆ v
  /-- A perfect normal subgroup satisfying all requirements yields the acyclic regular
  cover `K_N`: `H₁(K_N) = N/[N,N] = 0` and `H₂(K_N) = ker ∂_{2,N} = 0`. -/
  cover_of_perfect : ∀ N : @Subgroup G grp, @Subgroup.Normal G grp N → (∀ v, Sat N v) →
      ⁅N, N⁆ = N → HasAcyclicRegularCover W K

end FiniteChains
