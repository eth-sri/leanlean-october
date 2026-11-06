module

public import Mathlib.Probability.Distributions.SetBernoulli
public import proofs.RAF.Core.RAFAll
public import proofs.RAF.Polymer.RAFPolymerAll

@[expose] public section


namespace RAF.Concrete

section
open RAF.Polymer

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
    (x : Word L) : molLength (moleculeOfCode hL hLn x) = L := by
  simp [molLength, moleculeOfCode]
  omega

def reactionProductLength {n : Nat} (r : Reaction n) : Nat := r.1.val + 1
def reactionLeftLength {n : Nat} (r : Reaction n) : Nat := r.2.2.val + 1
def reactionRightLength {n : Nat} (r : Reaction n) : Nat :=
  r.1.val - r.2.2.val

theorem reaction_length_add {n : Nat} (r : Reaction n) :
    reactionLeftLength r + reactionRightLength r = reactionProductLength r := by
  exact Eq.trans
    (Nat.add_right_comm r.2.2.val 1 (r.1.val - r.2.2.val))
    (congrArg (fun k : Nat => k + 1)
      (Eq.trans (Nat.add_comm r.2.2.val (r.1.val - r.2.2.val))
        (Nat.sub_add_cancel (Nat.le_of_lt r.2.2.isLt))))

theorem reaction_left_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionLeftLength r := by
  exact Nat.succ_pos r.2.2.val

theorem reaction_right_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionRightLength r := by
  exact Nat.sub_pos_of_lt r.2.2.isLt

theorem reaction_product_le {n : Nat} (r : Reaction n) :
    reactionProductLength r ≤ n := by
  exact r.1.isLt

theorem reaction_pow_split {n : Nat} (r : Reaction n) :
    2 ^ (r.1.val + 1) =
      2 ^ reactionLeftLength r * 2 ^ reactionRightLength r := by
  rw [← pow_add, reaction_length_add]
  rfl

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


end

section
open RAF RAF.Polymer

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

lemma revClosureStep_eq_food_of_no_seed (Q : ReversibleCRS M R) (S : Finset R)
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) :
    revClosureStep Q S Q.food = Q.food := by
    have hempty : S.biUnion (fun r =>
        (if RevEnabledLhs Q Q.food r then Q.rhs r else ∅) ∪
        (if RevEnabledRhs Q Q.food r then Q.lhs r else ∅)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      simp  at hx
      obtain ⟨r, hr, hx⟩ := hx
      have hn := h r hr
      have hnl : ¬ RevEnabledLhs Q Q.food r := fun hl => hn (Or.inl hl)
      have hnr : ¬ RevEnabledRhs Q Q.food r := fun hr' => hn (Or.inr hr')
      simp [hnl, hnr] at hx
    simp [revClosureStep, hempty]
lemma revClosureAt_eq_food_of_no_seed (Q : ReversibleCRS M R) (S : Finset R)
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) :
    ∀ k, revClosureAt Q S k = Q.food := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [revClosureAt, ih, revClosureStep_eq_food_of_no_seed Q S h]

theorem exists_rev_seed_of_foodGenerated (Q : ReversibleCRS M R) (S : Finset R)
    (hne : S.Nonempty) (hfg : RevFoodGenerated Q S) :
    ∃ r ∈ S, RevSeedReaction Q r := by
  by_contra hexists
  have hnoseed : ∀ r ∈ S, ¬ RevSeedReaction Q r := by
    intro r hr hs
    exact hexists ⟨r, hr, hs⟩
  obtain ⟨r, hr⟩ := hne
  obtain ⟨k, hk⟩ := hfg r hr
  have hc := revClosureAt_eq_food_of_no_seed Q S hnoseed k
  have hl : Q.lhs r ⊆ Q.food := by
    intro x hx
    exact hc ▸ hk (Finset.mem_union_left _ hx)
  exact hnoseed r hr (Or.inl hl)

abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}


end

section
open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer

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


end

section
open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer

def HasRAFEvent (n : Nat) : Set (CatalysisSample n) :=
  {ω | ∃ S : Finset (Reaction n),
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf ω) S}

theorem measurableSet_hasRAFEvent (n : Nat) : MeasurableSet (HasRAFEvent n) := by
  exact Set.toFinite (HasRAFEvent n) |>.measurableSet


end

end RAF.Concrete
