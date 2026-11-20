module

public import Mathlib
public import Mathlib.Probability.Distributions.SetBernoulli

@[expose] public section

def RAF.Catalysis (M R : Type*) := M → R → Prop

namespace RAF.Polymer


/-- A binary word of fixed positive length, represented by its bit pattern. -/
abbrev Word (length : Nat) := Fin (2 ^ length)

/-- Nonempty binary words of length at most `n`. The `Fin n` index `k`
represents length `k+1`. -/
abbrev Molecule (n : Nat) := Σ k : Fin n, Word (k.val + 1)

/-- A split-position bidirectional reaction. The index `k` represents a
product of length `k+1`; `split : Fin k` records one of its `k` splits. -/
abbrev Reaction (n : Nat) := Σ k : Fin n, Word (k.val + 1) × Fin k.val

end RAF.Polymer

namespace RAF.Concrete

open RAF.Polymer

variable {n : Nat}

/-- Length of an ambient binary polymer. -/
def molLength (x : Molecule n) : Nat := x.1.val + 1

section
variable {L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n)

include hL hLn in
theorem moleculeOfCode_index_lt :
    L - 1 < n :=
  Nat.lt_of_lt_of_le (Nat.sub_lt hL (Nat.zero_lt_succ 0)) hLn

include hL in
theorem moleculeOfCode_pow_eq :
    2 ^ L = 2 ^ (L - 1 + 1) :=
  congrArg (fun k : Nat => 2 ^ k) (Nat.sub_add_cancel hL).symm

/-- A length-indexed word viewed as an ambient molecule. -/
def moleculeOfCode (x : Word L) : Molecule n :=
  ⟨⟨L - 1, moleculeOfCode_index_lt hL hLn⟩,
    Fin.cast (moleculeOfCode_pow_eq hL) x⟩

@[simp] theorem molLength_moleculeOfCode (x : Word L) : molLength (moleculeOfCode hL hLn x) = L := by simp_all [molLength, moleculeOfCode]

end

/-- Concatenate the bit patterns of two molecules.  `finProdFinEquiv` is the
standard mixed-radix bijection, here with radices `2^|u|` and `2^|v|`. -/
def concatCode (u v : Molecule n) : Word (molLength u + molLength v) :=
  Fin.cast ((pow_add 2 (molLength u) (molLength v)).symm)
    (finProdFinEquiv (u.2, v.2))

def concatMolecule (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) : Molecule n :=
  moleculeOfCode (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le u.1.val))
    (Nat.le_add_right (molLength u) (molLength v))) h (concatCode u v)

def reactionProductLength (r : Reaction n) : Nat := r.1.val + 1
def reactionLeftLength (r : Reaction n) : Nat := r.2.2.val + 1
def reactionRightLength (r : Reaction n) : Nat :=
  r.1.val - r.2.2.val

theorem reaction_length_add (r : Reaction n) :
    reactionLeftLength r + reactionRightLength r = reactionProductLength r := by
  unfold reactionLeftLength reactionRightLength reactionProductLength
  omega

theorem reaction_left_pos (r : Reaction n) :
    1 ≤ reactionLeftLength r := by simp [reactionLeftLength]

theorem reaction_right_pos (r : Reaction n) :
    1 ≤ reactionRightLength r := by grind [reactionRightLength]

theorem reaction_product_le (r : Reaction n) :
    reactionProductLength r ≤ n := by simp [reactionProductLength]

theorem reaction_pow_split (r : Reaction n) :
    2 ^ (r.1.val + 1) =
      2 ^ reactionLeftLength r * 2 ^ reactionRightLength r := by
  rw [← pow_add, reaction_length_add]
  rfl

/-- Split the encoded product at its recorded split position. -/
def splitCodes (r : Reaction n) :
    Word (reactionLeftLength r) × Word (reactionRightLength r) :=
  (finProdFinEquiv).symm
    (Fin.cast (reaction_pow_split r) r.2.1)

def reactionLeft (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_left_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).1

def reactionRight (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_right_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).2

def reactionProduct (r : Reaction n) : Molecule n :=
  ⟨r.1, r.2.1⟩

@[simp] theorem molLength_reactionLeft (r : Reaction n) :
    molLength (reactionLeft r) = reactionLeftLength r := by
  rfl

@[simp] theorem molLength_reactionRight (r : Reaction n) :
    molLength (reactionRight r) = reactionRightLength r := by
  simp [reactionRight]

@[simp] theorem molLength_reactionProduct (r : Reaction n) :
    molLength (reactionProduct r) = reactionProductLength r := rfl

theorem molecule_ext {x y : Molecule n}
    (hl : molLength x = molLength y) (hc : x.2.val = y.2.val) : x = y :=
  Sigma.ext (Fin.ext (Nat.add_right_cancel hl)) ((Fin.heq_ext_iff (congrArg (2 ^ ·) hl)).2 hc)

/-- A reversible CRS records the two sides of each base reaction. Catalysis is
indexed by the base reaction, so one sampled coordinate catalyzes both
directions, exactly as in the paper's reaction convention. -/
structure ReversibleCRS (M R : Type*) [DecidableEq M] where
  lhs : R → Finset M
  rhs : R → Finset M
  food : Finset M

section
variable {M R : Type*} [DecidableEq M]

section
variable (Q : ReversibleCRS M R) (available : Finset M) (r : R)

def RevEnabledLhs : Prop := Q.lhs r ⊆ available

def RevEnabledRhs : Prop := Q.rhs r ⊆ available

instance revEnabledLhsDecidable : Decidable (RevEnabledLhs Q available r) := by
  unfold RevEnabledLhs
  infer_instance

instance revEnabledRhsDecidable : Decidable (RevEnabledRhs Q available r) := by
  unfold RevEnabledRhs
  infer_instance

end

def revClosureStep
    (Q : ReversibleCRS M R) (S : Finset R) (available : Finset M) : Finset M :=
  available ∪ S.biUnion (fun r =>
    (if RevEnabledLhs Q available r then Q.rhs r else ∅) ∪
    (if RevEnabledRhs Q available r then Q.lhs r else ∅))

def revClosureAt
    (Q : ReversibleCRS M R) (S : Finset R) : Nat → Finset M
  | 0 => Q.food
  | k + 1 => revClosureStep Q S (revClosureAt Q S k)

end

def binaryFood (n t : Nat) : Finset (Molecule n) :=
  Finset.univ.filter (fun x => molLength x ≤ t)

/-- The concrete split-position, bidirectional binary-polymer CRS. -/
def binaryPolymerCRS (n t : Nat) : ReversibleCRS (Molecule n) (Reaction n) where
  lhs := fun r => {reactionLeft r, reactionRight r}
  rhs := fun r => {reactionProduct r}
  food := binaryFood n t

open MeasureTheory ProbabilityTheory unitInterval

section
variable {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)

def RevSeedReaction (r : R) : Prop :=
  Q.lhs r ⊆ Q.food ∨ Q.rhs r ⊆ Q.food

instance revSeedReactionDecidable (r : R) :
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

end

abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}

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
