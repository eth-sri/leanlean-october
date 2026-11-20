module

public import RequestProject.CombPi1
public import RequestProject.CoverComplex
public import RequestProject.PresentationDictionary

@[expose] public section

/-!
# The fundamental group of a presentation complex

`RequestProject/CombPi1.lean` defines the edge-path fundamental group `Comb.Pi1` of a
combinatorial two-complex, and `RequestProject/CoverComplex.lean` defines the presentation
complex `Comb.presComplex ρ` of a presentation `⟨x_i | r_j⟩` (one vertex, one edge per
generator, one two-cell per relator).  Everywhere in the project the group of the
presentation is taken to be `FiniteChains.PresGroup ρ = FreeGroup α ⧸ relSub ρ`; this file
proves that this really is the fundamental group of the complex:

`FiniteChains.Comb.pi1PresEquiv : Pi1 (presComplex ρ) PUnit.unit ≃* PresGroup ρ`.

The proof is the usual one, made combinatorial: an edge loop is literally a word in the
generators, homotopies are backtrack cancellations (trivial in the free group) and removals
of attaching words (trivial modulo the normal closure of the relators), and conversely the
free group maps to `π₁` by sending a generator to the corresponding edge loop.
-/

namespace FiniteChains
namespace Comb

universe u

variable {α : Type u} [DecidableEq α] {J : Type u}

/-! ### From edge loops to the presented group -/

section

variable (ρ : J → FreeGroup α)

/-- The class in `G = F/R` of the word spelled by an edge path of the presentation
complex. -/
def presWord (l : List (α × Bool)) : PresGroup ρ := QuotientGroup.mk (FreeGroup.mk l)

omit [DecidableEq α] in
@[simp] theorem presWord_nil : presWord ρ [] = 1 := rfl

omit [DecidableEq α] in
theorem presWord_append (l l' : List _) :
    presWord ρ (l ++ l') = presWord ρ l * presWord ρ l' := rfl

theorem presWord_att (j : J) : presWord ρ ((presComplex ρ).att j) = 1 := by
  have h : presWord ρ ((presComplex ρ).att j) = QuotientGroup.mk (ρ j) := by
    unfold presWord
    rw [show (presComplex ρ).att j = (ρ j).toWord from rfl, FreeGroup.mk_toWord]
  rw [h, QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure ⟨j, rfl⟩

/-- Elementary cancellations of edge paths do not change the class of the spelled word. -/
theorem presWord_cancels {l l' : List _} (h : Cancels (presComplex ρ) l l') :
    presWord ρ l = presWord ρ l' := by
  rcases h with ⟨p, q, eb, hl, hl'⟩ | ⟨p, q, j, hl, hl'⟩
  · subst hl; subst hl'; exact congrArg QuotientGroup.mk (Quot.sound FreeGroup.Red.Step.not)
  · subst hl; subst hl'
    rw [presWord_append, presWord_append, presWord_append, presWord_att, mul_one]

/-- Homotopic edge paths spell the same element of `G`. -/
theorem presWord_htpy {a b : (presComplex ρ).V} {l l' : List _}
    (h : Htpy _ a b l l') : presWord ρ l = presWord ρ l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact ih.trans (presWord_cancels ρ hs.2.2)
      · exact ih.trans (presWord_cancels ρ hs.2.2).symm

/-- The homomorphism `π₁(K) → G` reading off the word spelled by an edge loop. -/
def pi1ToPres : Pi1 (presComplex ρ) PUnit.unit →* PresGroup ρ where
  toFun := Quotient.lift _ (fun _ _ h => presWord_htpy ρ h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩ <;> rfl

/-! ### From the presented group to edge loops -/

/-- The class of an arbitrary word, read as an edge loop of the presentation complex. -/
def loopClass (l : List (α × Bool)) : Pi1 (presComplex ρ) PUnit.unit :=
  Pi1.mk ⟨l, isPath_of_subsingleton _ _ _ _ _⟩

theorem loopClass_append (l l' : List _) :
    loopClass ρ (l ++ l') = loopClass ρ l * loopClass ρ l' := rfl

@[simp] theorem loopClass_nil : loopClass ρ [] = 1 := rfl

variable (i : α)

/-- The edge loop of a generator. -/
def genLoop := loopClass ρ [(i, true)]

/-- Attaching words are null-homotopic, so they give the trivial loop class. -/
theorem loopClass_att (j : J) : loopClass ρ ((presComplex ρ).att j) = 1 := by
  refine Quotient.sound ?_
  refine Htpy.of_step ⟨isPath_of_subsingleton _ _ _ _ _, isPath_of_subsingleton _ _ _ _ _, ?_⟩
  exact Or.inr ⟨[], [], j, by simp, rfl⟩

/-- The homomorphism `F → π₁(K)` sending a generator to its edge loop. -/
def freeToPi1 := FreeGroup.lift (genLoop ρ)

theorem freeToPi1_mk (l : List _) :
    freeToPi1 ρ (FreeGroup.mk l) = loopClass ρ l := by
  induction l with
  | nil =>
      rfl
  | cons eb l ih =>
      obtain ⟨i, b⟩ := eb
      have hsplit : ((i, b) :: l) = [(i, b)] ++ l := rfl
      rw [hsplit, ← FreeGroup.mul_mk, map_mul, ih, loopClass_append]
      congr 1
      cases b <;> rfl

theorem freeToPi1_relator (j : J) : freeToPi1 ρ (ρ j) = 1 := by
  have h : freeToPi1 ρ (ρ j) = loopClass ρ ((presComplex ρ).att j) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := ρ j)]
    simp [freeToPi1_mk]
  rw [h, loopClass_att]

theorem relSub_le_ker_freeToPi1 : relSub ρ ≤ (freeToPi1 ρ).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨j, rfl⟩
  exact freeToPi1_relator ρ j

/-- The homomorphism `G → π₁(K)` induced by `F → π₁(K)`. -/
def presToPi1 :=
  QuotientGroup.lift _ _ (fun _ hx => relSub_le_ker_freeToPi1 ρ hx)

@[simp] theorem presToPi1_mk (w : FreeGroup α) :
    presToPi1 ρ (QuotientGroup.mk w) = freeToPi1 ρ w := rfl

/-! ### The isomorphism -/

theorem presToPi1_pi1ToPres (x : Pi1 (presComplex ρ) PUnit.unit) :
    presToPi1 ρ (pi1ToPres ρ x) = x := by
  induction x using Quotient.inductionOn with
  | h p =>
      solve_by_elim [presToPi1_mk, freeToPi1_mk]

theorem pi1ToPres_presToPi1 (g : PresGroup ρ) : pi1ToPres ρ (presToPi1 ρ g) = g := by
  induction g using QuotientGroup.induction_on with
  | H w =>
      rw [presToPi1_mk, ← FreeGroup.mk_toWord (x := w), freeToPi1_mk] <;> rfl

/-- **The fundamental group of a presentation complex is the presented group**: the edge-path
group of `presComplex ρ` at its unique vertex is `F/⟪r_j⟫`. -/
def pi1PresEquiv : Pi1 (presComplex ρ) PUnit.unit ≃* PresGroup ρ where
  toFun := pi1ToPres ρ
  invFun := presToPi1 ρ
  left_inv := presToPi1_pi1ToPres ρ
  right_inv := pi1ToPres_presToPi1 ρ
  map_mul' := (pi1ToPres ρ).map_mul

end

end Comb
end FiniteChains
