module
public import Mathlib

/-! The finite binary polymer universe and literal split-position reaction system. -/

@[expose] public section

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
variable {n L : ℕ}

/-- Length of an ambient binary polymer. -/
def molLength (x : Molecule n) : Nat := x.1.val + 1

theorem moleculeOfCode_index_lt (hL : 1 ≤ L) (hLn : L ≤ n) :
    L - 1 < n :=
  Nat.lt_of_lt_of_le (Nat.sub_lt hL (Nat.zero_lt_succ 0)) hLn

theorem moleculeOfCode_pow_eq (hL : 1 ≤ L) :
    2 ^ L = 2 ^ (L - 1 + 1) :=
  congrArg (fun k : Nat => 2 ^ k) (Nat.sub_add_cancel hL).symm

/-- A length-indexed word viewed as an ambient molecule. -/
def moleculeOfCode (hL : 1 ≤ L) (hLn : L ≤ n)
    (x : Word L) : Molecule n :=
  ⟨⟨L - 1, moleculeOfCode_index_lt hL hLn⟩,
    Fin.cast (moleculeOfCode_pow_eq hL) x⟩

/-- Concatenate the bit patterns of two molecules.  `finProdFinEquiv` is the
standard mixed-radix bijection, here with radices `2^|u|` and `2^|v|`. -/
def concatCode (u v : Molecule n) : Word (molLength u + molLength v) :=
  Fin.cast ((pow_add 2 (molLength u) (molLength v)).symm)
    (finProdFinEquiv (u.2, v.2))

def concatMolecule (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) : Molecule n :=
  moleculeOfCode (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le u.1.val))
    (Nat.le_add_right (molLength u) (molLength v))) h (concatCode u v)

@[simp] theorem molLength_moleculeOfCode (hL : 1 ≤ L) (hLn : L ≤ n)
    (x : Word L) : molLength (moleculeOfCode hL hLn x) = L := by
  simp [molLength, moleculeOfCode]
  omega

variable (r : Reaction n)
def reactionProductLength : Nat := r.1.val + 1
def reactionLeftLength : Nat := r.2.2.val + 1
def reactionRightLength : Nat :=
  r.1.val - r.2.2.val

theorem reaction_length_add :
    reactionLeftLength r + reactionRightLength r = reactionProductLength r := by
  grind [reactionProductLength, reactionRightLength, reactionLeftLength]

theorem reaction_left_pos :
    1 ≤ reactionLeftLength r := Nat.succ_pos r.2.2.val

theorem reaction_right_pos :
    1 ≤ reactionRightLength r := Nat.sub_pos_of_lt r.2.2.isLt

theorem reaction_product_le :
    reactionProductLength r ≤ n := r.1.isLt

theorem reaction_pow_split :
    2 ^ (r.1.val + 1) =
      2 ^ reactionLeftLength r * 2 ^ reactionRightLength r := by
  rw [← pow_add, reaction_length_add]
  rfl

/-- Split the encoded product at its recorded split position. -/
def splitCodes :
    Word (reactionLeftLength r) × Word (reactionRightLength r) :=
  (finProdFinEquiv).symm
    (Fin.cast (reaction_pow_split r) r.2.1)

def reactionLeft : Molecule n :=
  moleculeOfCode (reaction_left_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).1

def reactionRight : Molecule n :=
  moleculeOfCode (reaction_right_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).2

def reactionProduct : Molecule n :=
  ⟨r.1, r.2.1⟩

@[simp] theorem molLength_reactionLeft :
    molLength (reactionLeft r) = reactionLeftLength r := by
  simp [reactionLeft]

@[simp] theorem molLength_reactionRight :
    molLength (reactionRight r) = reactionRightLength r := by
  simp [reactionRight]

@[simp] theorem molLength_reactionProduct :
    molLength (reactionProduct r) = reactionProductLength r := rfl

/-- A reversible CRS records the two sides of each base reaction. Catalysis is
indexed by the base reaction, so one sampled coordinate catalyzes both
directions, exactly as in the paper's reaction convention. -/
structure ReversibleCRS (M R : Type*) [DecidableEq M] where
  lhs : R → Finset M
  rhs : R → Finset M
  food : Finset M

variable {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
section
variable (available : Finset M) (r : R)
def RevEnabledLhs : Prop :=
  Q.lhs r ⊆ available

def RevEnabledRhs : Prop :=
  Q.rhs r ⊆ available

instance revEnabledLhsDecidable :
    Decidable (RevEnabledLhs Q available r) := by
  unfold RevEnabledLhs
  infer_instance

instance revEnabledRhsDecidable :
    Decidable (RevEnabledRhs Q available r) := by
  unfold RevEnabledRhs
  infer_instance

end

variable (S : Finset R)

def revClosureStep (available : Finset M) : Finset M :=
  available ∪ S.biUnion (fun r =>
    (if RevEnabledLhs Q available r then Q.rhs r else ∅) ∪
    (if RevEnabledRhs Q available r then Q.lhs r else ∅))

def revClosureAt : Nat → Finset M
  | 0 => Q.food
  | k + 1 => revClosureStep Q S (revClosureAt k)

def binaryFood (n t : Nat) : Finset (Molecule n) :=
  Finset.univ.filter (fun x => molLength x ≤ t)

/-- The concrete split-position, bidirectional binary-polymer CRS. -/
def binaryPolymerCRS (n t : Nat) : ReversibleCRS (Molecule n) (Reaction n) where
  lhs := fun r => {reactionLeft r, reactionRight r}
  rhs := fun r => {reactionProduct r}
  food := binaryFood n t

theorem molecule_ext {x y : Molecule n}
    (hl : molLength x = molLength y) (hc : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  have hij : i = j := by grind [molLength]
  aesop

variable {t : ℕ}

def lowerMolecule (x : Molecule n) (h : molLength x ≤ t) :
    Molecule t :=
  moleculeOfCode (by simp [molLength]) h x.2

lemma lower_inj {x y : Molecule n} {hx hy}
    (e : lowerMolecule x (t := t) hx = lowerMolecule y hy) : x = y :=
  molecule_ext (congrArg (@molLength t) e) (congrArg (fun z : Molecule t => z.2.val) e)

end RAF.Concrete

namespace HordijkSteelThreshold

open RAF.Polymer

/-- Upper bound for the finite seed census. -/
theorem card_molecules_le (n : ℕ) : Fintype.card (Molecule n) ≤ 2^(n+1) := by
  simp only [Molecule,Word,Fintype.card_sigma,Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 2^(i+1))]
  induction n with
  | zero => decide
  | succ n ih => rw [Finset.sum_range_succ,pow_succ]; omega

end HordijkSteelThreshold
