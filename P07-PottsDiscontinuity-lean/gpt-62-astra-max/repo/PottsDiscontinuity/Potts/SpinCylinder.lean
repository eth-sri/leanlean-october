module
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section


namespace PottsDiscontinuity.Potts

noncomputable section

abbrev SpinSpace (q : ℕ) := ℤ × ℤ → Set.Icc 1 q

/-- The spin configurations agreeing with `ξ` on the finite set `A`. -/
def spinCylinder {q : ℕ} (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) : Set (SpinSpace q) :=
  {σ | ∀ x ∈ A, σ x = ξ x}

theorem spinCylinder_isClopen (q : ℕ) (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) :
    IsClopen (spinCylinder A ξ) := by
  simpa only [spinCylinder, Set.ofPred_forall, Set.preimage, Set.mem_singleton_iff] using
    isClopen_biInter_finset (s := A) fun x _ =>
      (isClopen_discrete ({ξ x} : Set (Set.Icc 1 q))).preimage (continuous_apply (A := fun _ : ℤ × ℤ => Set.Icc 1 q) x)

end
end PottsDiscontinuity.Potts
