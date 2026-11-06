module

public import Mathlib

/-!
# Counting cluster colourings

Colourings are functions constant on the classes of an explicit equivalence
relation. Isolated vertices are included. Pinning the class of a distinguished
vertex removes exactly one independent colour choice.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

variable {V C : Type*}

section
variable (R : Setoid V)
/-- Vertex colourings constant on every class of `R`. -/
abbrev ClusterColoring (C : Type*) :=
  {σ : V → C // R ≤ Setoid.ker σ}

/-- Assigning one colour to each class is equivalent to a compatible colouring. -/
def clusterColoringEquiv  : ClusterColoring R C ≃ (Quotient R → C) :=
  Setoid.liftEquiv R
end

theorem card_clusterColoring [Finite V] (R : Setoid V) :
    Nat.card (ClusterColoring R C) = Nat.card C ^ Nat.card (Quotient R) := by
  rw [Nat.card_congr (clusterColoringEquiv R), Nat.card_fun]

section
variable (R : Setoid V) (g : V) (i : C)
/-- Colourings with the entire class of `g` fixed to `i`. -/
abbrev PinnedClusterColoring  :=
  {σ : ClusterColoring R C // σ.val g = i}

/-- Pinning a vertex is exactly pinning its quotient class. -/
def pinnedClusterColoringEquiv  :
    PinnedClusterColoring R g i ≃ {f : Quotient R → C // f (Quotient.mk R g) = i} :=
  (clusterColoringEquiv R).subtypeEquiv (fun _ => Iff.rfl)
end

section
variable [Finite V] [Finite C]
theorem card_pinned_functions (g : V) (i : C) :
    Nat.card {f : V → C // f g = i} = Nat.card C ^ (Nat.card V - 1) := by
  let := Fintype.ofFinite V
  let := Fintype.ofFinite C
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Fintype.piFinset_univ, Finset.card_univ] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset C) g
      (Finset.mem_univ i)

theorem card_pinnedClusterColoring (R : Setoid V) (g : V) (i : C) :
    Nat.card (PinnedClusterColoring R g i) =
      Nat.card C ^ (Nat.card (Quotient R) - 1) := by
  rw [Nat.card_congr (pinnedClusterColoringEquiv R g i), card_pinned_functions]
end

/-- The exact probability of a vertex colouring under independent uniform class colours. -/
def clusterColoringProbability [Finite V] [Finite C] (R : Setoid V) (σ : V → C) : ℝ :=
  if R ≤ Setoid.ker σ then ((Nat.card C : ℝ) ^ Nat.card (Quotient R))⁻¹ else 0



end

end PottsDiscontinuity.Potts
