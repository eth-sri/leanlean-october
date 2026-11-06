module

public import proofs.RAF.Core.RAF

@[expose] public section

namespace RAF.Frankl

open RAF

variable {M R : Type*} [DecidableEq M]

/-- A reaction is retained by one RAF-pruning step when its reactants and at
least one catalyst occur at some finite stage of the molecular closure. -/
def Supported (Q : CRS M R) (C : Catalysis M R) (S : Finset R) (r : R) : Prop :=
  (∃ k, Q.inputs r ⊆ closureAt Q S k) ∧ CatalyzedFromClosure Q C S r

/-- The source-faithful one-step RAF pruning operator. -/
noncomputable def prune (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) : Finset R := by
  classical
  exact S.filter (Supported Q C S)

@[simp] theorem mem_prune (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) (r : R) :
    r ∈ prune Q C S ↔ r ∈ S ∧ Supported Q C S r := by
  classical
  simp [prune]

/-- Exact finite family of all nonempty RAFs. Classical decidability is used
only to enumerate a finite powerset; the mathematical predicate is `IsRAF`. -/
noncomputable def rafFamily (Q : CRS M R) (C : Catalysis M R) [Fintype R] :
    Finset (Finset R) := by
  classical
  exact Finset.univ.powerset.filter (IsRAF Q C)

@[simp] theorem mem_rafFamily (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    (S : Finset R) : S ∈ rafFamily Q C ↔ IsRAF Q C S := by
  classical
  simp [rafFamily]

/-- The full pruning fixed family: the empty fixed point together with all
nonempty RAFs. -/
noncomputable def fixedFamily (Q : CRS M R) (C : Catalysis M R) [Fintype R] :
    Finset (Finset R) := by
  classical
  exact insert ∅ (rafFamily Q C)

@[simp] theorem mem_fixedFamily (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    (S : Finset R) : S ∈ fixedFamily Q C ↔ S = ∅ ∨ IsRAF Q C S := by
  classical
  simp [fixedFamily]

end RAF.Frankl
