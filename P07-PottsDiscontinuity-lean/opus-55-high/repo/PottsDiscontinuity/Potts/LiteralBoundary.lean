module

public import PottsDiscontinuity.Potts.FiniteExpansion
public import PottsDiscontinuity.Frozen.Defs.PottsProb

/-!
# Joint spin-bond law for the literal Potts boundary term

The bond index consists of the induced lattice edges and exactly one additional
bond for each boundary vertex. For a positive boundary colour these additional
bonds join the vertex to a ghost of that colour. For boundary colour zero they
are forced closed and can be discarded. No multiplicity of exterior neighbours
appears in this definition, including at corners or in the singleton box.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

/-- The frozen finite spin configuration carrier. -/
abbrev SpinConfiguration (q : ℕ) (V : Finset (ℤ × ℤ)) :=
  ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q

section
variable (V : Finset (ℤ × ℤ))
/-- One ghost bond is indexed by one boundary vertex. -/
abbrev BoundaryVertex  :=
  {x : ↥(V : Set (ℤ × ℤ)) // x.val ∈ vertexBoundary V}

/-- Interior bonds and one ghost bond per boundary vertex. -/
abbrev LiteralBond  :=
  (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet ⊕ BoundaryVertex V
end

local instance literalBondDecidableEq (V : Finset (ℤ × ℤ)) : DecidableEq (LiteralBond V) :=
  fun _ _ => Classical.propDecidable _

local instance boundaryVertexFintype (V : Finset (ℤ × ℤ)) : Fintype (BoundaryVertex V) :=
  Fintype.ofFinite _

section
variable (q : ℕ) (V : Finset (ℤ × ℤ)) (i : Fin (q + 1)) (σ : SpinConfiguration q V)
/-- The agreement enforced by an open interior or ghost bond. -/
abbrev literalAgreement  : LiteralBond V → Prop
  | Sum.inl e => ∀ x ∈ e.val, ∀ y ∈ e.val, σ x = σ y
  | Sum.inr x => (σ x.val : ℕ) = (i : ℕ)

theorem sum_literalAgreement  :
    (∑ e : LiteralBond V, if literalAgreement q V i σ e then (1 : ℝ) else 0) =
      -pottsHamiltonian q V i σ := by
  rw [Fintype.sum_sum_type]
  have hb :
      (∑ x : BoundaryVertex V, if (σ x.val : ℕ) = (i : ℕ) then (1 : ℝ) else 0) =
      ∑ x : ↥(V : Set (ℤ × ℤ)),
        if x.val ∈ vertexBoundary V ∧ (σ x : ℕ) = (i : ℕ) then (1 : ℝ) else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun x : ↥(V : Set (ℤ × ℤ)) =>
      x.val ∈ vertexBoundary V)) (by simp) (fun x => if (σ x : ℕ) = (i : ℕ) then (1 : ℝ) else 0)]
    rw [Finset.sum_filter]
    grind
  unfold pottsHamiltonian
  conv_rhs => rw [neg_sub, sub_neg_eq_add, add_comm]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · ring
  · grind
end

section
variable (q : ℕ) (V : Finset (ℤ × ℤ)) (β : ℝ) (i : Fin (q + 1)) (σ : SpinConfiguration q V)
theorem constraintGibbsWeight_literalAgreement  :
    constraintGibbsWeight β (literalAgreement q V i) σ =
      Real.exp (-β * pottsHamiltonian q V i σ) := by
  grind [constraintGibbsWeight, sum_literalAgreement]

/-- The actual joint spin-bond probability mass for the frozen Hamiltonian. -/
abbrev literalJointProbability (ω : LiteralBond V → Bool) : ℝ :=
  constraintJointProbability β (literalAgreement q V i) σ ω
end

section
variable (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ)
include hq
/-- Summing the bonds recovers the exact frozen Potts probability, including
its literal soft boundary term. -/
theorem literalJointProbability_spin_marginal (i : Fin (q + 1)) (σ : SpinConfiguration q V) :
    ∑ ω : LiteralBond V → Bool, literalJointProbability q V β i σ ω =
      pottsProb q V β i σ := by
  let : Nonempty (Set.Icc 1 q) := by aesop
  have h := constraintJointProbability_spin_marginal β (literalAgreement q V i) σ
  grind [constraintGibbsWeight_literalAgreement, pottsProb]

theorem sum_literalJointProbability (i : Fin (q + 1)) :
    ∑ σ : SpinConfiguration q V, ∑ ω : LiteralBond V → Bool,
      literalJointProbability q V β i σ ω = 1 := by
  let : Nonempty (Set.Icc 1 q) := by aesop
  exact sum_constraintJointProbability β (literalAgreement q V i)

end

end

end PottsDiscontinuity.Potts
