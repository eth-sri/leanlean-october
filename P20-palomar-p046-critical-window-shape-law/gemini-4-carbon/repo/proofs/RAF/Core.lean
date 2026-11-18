module

public import Mathlib

@[expose] public section

namespace RAF.Polymer

/-- A binary word of fixed positive length, represented by its bit pattern. -/
abbrev Word (length : Nat) := Fin (2 ^ length)

/-- Nonempty binary words of length at most `n`. The `Fin n` index `k`
represents length `k+1`. -/
abbrev Molecule (n : Nat) := Σ k : Fin n, Word (k.val + 1)

theorem card_molecule_sigma (n : Nat) :
    Fintype.card (Molecule n) = ∑ k : Fin n, 2 ^ (k.val + 1) := by
  simp [Molecule, Word]

/-- A split-position bidirectional reaction. The index `k` represents a
product of length `k+1`; `split : Fin k` records one of its `k` splits. -/
abbrev Reaction (n : Nat) := Σ k : Fin n, Word (k.val + 1) × Fin k.val

theorem card_reaction_sigma (n : Nat) :
    Fintype.card (Reaction n) = ∑ k : Fin n, 2 ^ (k.val + 1) * k.val := by
  simp [Reaction, Word]

end RAF.Polymer

namespace RAF

def Catalysis (M R : Type*) := M → R → Prop

end RAF

namespace RAF.Concrete
open MeasureTheory ProbabilityTheory unitInterval RAF RAF.Polymer

/-- Length of an ambient binary polymer. -/
def molLength {n : Nat} (x : Molecule n) : Nat := x.1.val + 1

theorem moleculeOfCode_index_lt {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n) :
    L - 1 < n :=
  Nat.lt_of_lt_of_le (Nat.sub_lt hL (Nat.zero_lt_succ 0)) hLn

theorem moleculeOfCode_pow_eq {L : Nat} (hL : 1 ≤ L) :
    2 ^ L = 2 ^ (L - 1 + 1) :=
  congrArg (fun k : Nat => 2 ^ k) (Nat.sub_add_cancel hL).symm

/-- A length-indexed word viewed as an ambient molecule. -/
def moleculeOfCode {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n)
    (x : Word L) : Molecule n :=
  ⟨⟨L - 1, moleculeOfCode_index_lt hL hLn⟩,
    Fin.cast (moleculeOfCode_pow_eq hL) x⟩

/-- Concatenate the bit patterns of two molecules.  `finProdFinEquiv` is the
standard mixed-radix bijection, here with radices `2^|u|` and `2^|v|`. -/
def concatCode {n : Nat} (u v : Molecule n) : Word (molLength u + molLength v) :=
  Fin.cast ((pow_add 2 (molLength u) (molLength v)).symm)
    (finProdFinEquiv (u.2, v.2))

def concatMolecule {n : Nat} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) : Molecule n :=
  moleculeOfCode (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le u.1.val))
    (Nat.le_add_right (molLength u) (molLength v))) h (concatCode u v)

@[simp] theorem molLength_moleculeOfCode {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n)
    (x : Word L) : molLength (moleculeOfCode hL hLn x) = L :=
  Nat.sub_add_cancel hL

def reactionProductLength {n : Nat} (r : Reaction n) : Nat := r.1.val + 1
def reactionLeftLength {n : Nat} (r : Reaction n) : Nat := r.2.2.val + 1
def reactionRightLength {n : Nat} (r : Reaction n) : Nat :=
  r.1.val - r.2.2.val

theorem reaction_length_add {n : Nat} (r : Reaction n) :
    reactionLeftLength r + reactionRightLength r = reactionProductLength r := by
  unfold reactionLeftLength reactionRightLength reactionProductLength; have := r.2.2.isLt; omega

theorem reaction_left_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionLeftLength r := Nat.succ_pos _

theorem reaction_right_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionRightLength r := Nat.sub_pos_of_lt r.2.2.isLt

theorem reaction_product_le {n : Nat} (r : Reaction n) :
    reactionProductLength r ≤ n := r.1.isLt

theorem reaction_pow_split {n : Nat} (r : Reaction n) :
    2 ^ (r.1.val + 1) =
      2 ^ reactionLeftLength r * 2 ^ reactionRightLength r := by
  rw [← pow_add, reaction_length_add]; rfl

/-- Split the encoded product at its recorded split position. -/
def splitCodes {n : Nat} (r : Reaction n) :
    Word (reactionLeftLength r) × Word (reactionRightLength r) :=
  (finProdFinEquiv).symm
    (Fin.cast (reaction_pow_split r) r.2.1)

def reactionLeft {n : Nat} (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_left_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).1

def reactionRight {n : Nat} (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_right_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).2

def reactionProduct {n : Nat} (r : Reaction n) : Molecule n :=
  ⟨r.1, r.2.1⟩

@[simp] theorem molLength_reactionLeft {n : Nat} (r : Reaction n) :
    molLength (reactionLeft r) = reactionLeftLength r := by
  simp [reactionLeft]

@[simp] theorem molLength_reactionRight {n : Nat} (r : Reaction n) :
    molLength (reactionRight r) = reactionRightLength r := by
  simp [reactionRight]

@[simp] theorem molLength_reactionProduct {n : Nat} (r : Reaction n) :
    molLength (reactionProduct r) = reactionProductLength r := rfl

/-- A reversible CRS records the two sides of each base reaction. Catalysis is
indexed by the base reaction, so one sampled coordinate catalyzes both
directions, exactly as in the paper's reaction convention. -/
structure ReversibleCRS (M R : Type*) [DecidableEq M] where
  lhs : R → Finset M
  rhs : R → Finset M
  food : Finset M

def RevEnabledLhs {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) : Prop :=
  Q.lhs r ⊆ available

def RevEnabledRhs {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) : Prop :=
  Q.rhs r ⊆ available

instance revEnabledLhsDecidable {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) :
    Decidable (RevEnabledLhs Q available r) := by
  unfold RevEnabledLhs
  infer_instance

instance revEnabledRhsDecidable {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) :
    Decidable (RevEnabledRhs Q available r) := by
  unfold RevEnabledRhs
  infer_instance

def revClosureStep {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (available : Finset M) : Finset M :=
  available ∪ S.biUnion (fun r =>
    (if RevEnabledLhs Q available r then Q.rhs r else ∅) ∪
    (if RevEnabledRhs Q available r then Q.lhs r else ∅))

def revClosureAt {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Nat → Finset M
  | 0 => Q.food
  | k + 1 => revClosureStep Q S (revClosureAt Q S k)

def binaryFood (n t : Nat) : Finset (Molecule n) :=
  Finset.univ.filter (fun x => molLength x ≤ t)

/-- The concrete split-position, bidirectional binary-polymer CRS. -/
def binaryPolymerCRS (n t : Nat) : ReversibleCRS (Molecule n) (Reaction n) where
  lhs := fun r => {reactionLeft r, reactionRight r}
  rhs := fun r => {reactionProduct r}
  food := binaryFood n t

section
variable {M R : Type*} [DecidableEq M]

def RevSeedReaction (Q : ReversibleCRS M R) (r : R) : Prop :=
  Q.lhs r ⊆ Q.food ∨ Q.rhs r ⊆ Q.food

instance revSeedReactionDecidable (Q : ReversibleCRS M R) (r : R) :
    Decidable (RevSeedReaction Q r) := by
  unfold RevSeedReaction
  infer_instance

def RevFoodGenerated (Q : ReversibleCRS M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ k, Q.lhs r ∪ Q.rhs r ⊆ revClosureAt Q S k

def RevReflexivelyAutocatalytic (Q : ReversibleCRS M R)
    (C : Catalysis M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ x k, x ∈ revClosureAt Q S k ∧ C x r

def IsRevRAF (Q : ReversibleCRS M R) (C : Catalysis M R)
    (S : Finset R) : Prop :=
  S.Nonempty ∧ RevFoodGenerated Q S ∧ RevReflexivelyAutocatalytic Q C S

theorem exists_rev_seed_of_foodGenerated (Q : ReversibleCRS M R) (S : Finset R)
    (hne : S.Nonempty) (hfg : RevFoodGenerated Q S) :
    ∃ r ∈ S, RevSeedReaction Q r := by
  by_contra! hn
  have h0 (k : ℕ) : revClosureAt Q S k = Q.food := by
    induction k with
    | zero => rfl
    | succ _ ih =>
      rw [revClosureAt, ih, revClosureStep, Finset.union_eq_left]
      exact Finset.biUnion_subset.mpr fun r hr => by
        rw [ite_eq_right fun (h : RevEnabledLhs Q Q.food r) => hn r hr (.inl h),
          ite_eq_right fun (h : RevEnabledRhs Q Q.food r) => hn r hr (.inr h)]; simp
  obtain ⟨r, hr⟩ := hne
  obtain ⟨k, hk⟩ := hfg r hr
  exact hn r hr (.inl ((Finset.subset_union_left).trans (h0 k ▸ hk)))

abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}
end

abbrev SeedCoord (n : Nat) := Molecule n × PolymerSeedReaction n 2
abbrev NonseedReaction (n : Nat) :=
  {r : Reaction n // ¬ RevSeedReaction (binaryPolymerCRS n 2) r}
abbrev NonseedCoord (n : Nat) := Molecule n × NonseedReaction n

/-- Partitioned representation of every molecule--reaction coordinate. -/
abbrev CatalysisSample (n : Nat) := Set (SeedCoord n) × Set (NonseedCoord n)

noncomputable def rawCatalysisP (n : Nat) (lambda : ℝ) : ℝ :=
  lambda * n / Fintype.card (Reaction n)

/-- Clamp only to obtain a total unit-interval parameter.  The asymptotic proof
later shows the clamp is inactive in the positive fixed-lambda tail. -/
noncomputable def catalysisP (n : Nat) (lambda : ℝ) : I :=
  ⟨min 1 (max 0 (rawCatalysisP n lambda)), by
    constructor
    · exact le_min (by norm_num) (le_max_left _ _)
    · exact min_le_left _ _⟩

/-- Genuine product Bernoulli probability measure.  Seed and nonseed
coordinates are independently sampled with the same parameter. -/
noncomputable def uniformCatalysisMeasure (n : Nat) (lambda : ℝ) :
    Measure (CatalysisSample n) :=
  (setBernoulli (Set.univ : Set (SeedCoord n)) (catalysisP n lambda)).prod
    (setBernoulli (Set.univ : Set (NonseedCoord n)) (catalysisP n lambda))

noncomputable instance uniformCatalysisMeasure_isProbability (n : Nat) (lambda : ℝ) :
    IsProbabilityMeasure (uniformCatalysisMeasure n lambda) := by
  unfold uniformCatalysisMeasure
  infer_instance

/-- Convert a sampled partition back to the catalysis relation on the concrete
base reactions. -/
def catalysisOf {n : Nat} (ω : CatalysisSample n) :
    Catalysis (Molecule n) (Reaction n) := fun x r =>
  if h : RevSeedReaction (binaryPolymerCRS n 2) r then
    (x, ⟨r, h⟩) ∈ ω.1
  else
    (x, ⟨r, h⟩) ∈ ω.2

def HasRAFEvent (n : Nat) : Set (CatalysisSample n) :=
  {ω | ∃ S : Finset (Reaction n),
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf ω) S}

end RAF.Concrete

namespace OverlapCorrectedRAF.Source
open RAF RAF.Polymer RAF.Concrete

/-- The exact order used when `create_XFR` builds its molecule list: shorter
words precede longer words, and equal-length words use binary-code order. -/
abbrev moleculePrecedes {n : Nat} (u v : Molecule n) : Prop :=
  molLength u < molLength v ∨
    (molLength u = molLength v ∧ u.2.val ≤ v.2.val)

/-- Numeric code of the displayed concatenation `u ++ v`. -/
def displayedConcat {n : Nat} (u v : Molecule n) : Nat :=
  u.2.val * 2 ^ molLength v + v.2.val

/-- Canonical representative of the repository's displayed-reaction quotient.
Both orientations are retained when `u ++ v` and `v ++ u` differ.  When they
coincide, the repository emits only the orientation whose first factor occurs
first in its molecule list. -/
abbrev RepositoryChannel (n : Nat) :=
  {uv : Molecule n × Molecule n //
    molLength uv.1 + molLength uv.2 ≤ n ∧
      (displayedConcat uv.1 uv.2 ≠ displayedConcat uv.2 uv.1 ∨
        moleculePrecedes uv.1 uv.2)}

/-- The literal reversible reaction system generated by the public repository:
one base reaction per displayed-reaction channel, with catalysis attached to the
base channel and therefore shared by its ligation and cleavage orientations. -/
def repositoryCRS (n t : Nat) :
    ReversibleCRS (Molecule n) (RepositoryChannel n) where
  lhs := fun r => {r.1.1, r.1.2}
  rhs := fun r => {concatMolecule r.1.1 r.1.2 r.2.1}
  food := binaryFood n t

theorem repositorySeedChannels_card_le_34 (n : Nat) :
    (Finset.univ.filter fun r : RepositoryChannel n => RevSeedReaction (repositoryCRS n 2) r).card ≤ 34 := by
  rw [← Fintype.card_subtype]
  have hlen {r : RepositoryChannel n} (hs : RevSeedReaction (repositoryCRS n 2) r) :
      molLength r.1.1 ≤ 2 ∧ molLength r.1.2 ≤ 2 := by
    rcases hs with h | h
    · exact ⟨(Finset.mem_filter.mp (h (by simp [repositoryCRS]))).2,
        (Finset.mem_filter.mp (h (by simp [repositoryCRS]))).2⟩
    · have hp := (Finset.mem_filter.mp (h (Finset.mem_singleton_self _))).2
      rw [concatMolecule, molLength_moleculeOfCode] at hp; omega
  let tr (x : Molecule n) (hx : molLength x ≤ 2) : Molecule 2 :=
    ⟨⟨x.1.1, by dsimp [molLength] at hx; omega⟩, x.2⟩
  let f : {r : RepositoryChannel n // RevSeedReaction (repositoryCRS n 2) r} →
      {uv : Molecule 2 × Molecule 2 // displayedConcat uv.1 uv.2 ≠ displayedConcat uv.2 uv.1 ∨ moleculePrecedes uv.1 uv.2} :=
    fun r => ⟨(tr r.1.1.1 (hlen r.2).1, tr r.1.1.2 (hlen r.2).2), r.1.2.2⟩
  have hinj {x y : Molecule n} {p q} (h : (⟨⟨x.1.1, p⟩, x.2⟩ : Molecule 2) = ⟨⟨y.1.1, q⟩, y.2⟩) : x = y := by
    rcases x with ⟨xi, xw⟩; rcases y with ⟨yi, yw⟩
    obtain rfl : xi = yi := Fin.ext (congrArg (·.1.1) h)
    exact congrArg (Sigma.mk _) (eq_of_heq (Sigma.mk.inj h).2)
  exact (Fintype.card_le_of_injective f fun a b h => Subtype.ext (Subtype.ext
    (Prod.ext (hinj (Prod.mk.inj (Subtype.mk.inj h)).1)
      (hinj (Prod.mk.inj (Subtype.mk.inj h)).2)))).trans_eq (by decide)

end OverlapCorrectedRAF.Source
