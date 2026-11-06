import Mathlib.Tactic

import RequestProject.CombPi1
import RequestProject.CoverComplex
import RequestProject.PresentationDictionary

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

namespace FiniteChains.Comb



variable {α : Type u} [DecidableEq α] {J : Type u}

/-! ### From edge loops to the presented group -/

section

variable (ρ : J → FreeGroup α)

  (l : List (α × Bool))
/-- The class in `G = F/R` of the word spelled by an edge path of the presentation
complex. -/
def presWord  : PresGroup ρ := QuotientGroup.mk (FreeGroup.mk l)

section
omit [DecidableEq α]
@[simp] theorem presWord_nil : presWord ρ [] = 1 := rfl

theorem presWord_append (l l' : List (α × Bool)) :
    presWord ρ (l ++ l') = presWord ρ l * presWord ρ l' := rfl
end

variable (j : J)
theorem presWord_att  : presWord ρ ((presComplex ρ).att j) = 1 := by
  have h : presWord ρ ((presComplex ρ).att j) = QuotientGroup.mk (ρ j) := by
    unfold presWord
    rw [show (presComplex ρ).att j = (ρ j).toWord from rfl, FreeGroup.mk_toWord]
  rw [h, QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure ⟨j, rfl⟩

/-- Elementary cancellations of edge paths do not change the class of the spelled word. -/
theorem presWord_cancels {l l' : List (α × Bool)} (h : Cancels (presComplex ρ) l l') :
    presWord ρ l = presWord ρ l' := by
  rcases h with ⟨p, q, eb, hl, hl'⟩ | ⟨p, q, j, hl, hl'⟩
  · obtain ⟨x, b⟩ := eb
    subst hl; subst hl'
    unfold presWord
    exact congrArg QuotientGroup.mk (Quot.sound FreeGroup.Red.Step.not)
  · subst hl; subst hl'
    rw [presWord_append, presWord_append, presWord_append, presWord_att, mul_one]

/-- Homotopic edge paths spell the same element of `G`. -/
theorem presWord_htpy {a b : (presComplex ρ).V} {l l' : List (α × Bool)}
    (h : Htpy (presComplex ρ) a b l l') : presWord ρ l = presWord ρ l' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact ih.trans (presWord_cancels ρ hs.2.2)
      · exact ih.trans (presWord_cancels ρ hs.2.2).symm

/-- The homomorphism `π₁(K) → G` reading off the word spelled by an edge loop. -/
def pi1ToPres : Pi1 (presComplex ρ) PUnit.unit →* PresGroup ρ where
  toFun := Quotient.lift (fun p => presWord ρ p.1) (fun _ _ h => presWord_htpy ρ h)
  map_one' := rfl
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    exact presWord_append ρ p.1 q.1

/-! ### From the presented group to edge loops -/

/-- The class of an arbitrary word, read as an edge loop of the presentation complex. -/
def loopClass  : Pi1 (presComplex ρ) PUnit.unit :=
  Pi1.mk ⟨l, isPath_of_subsingleton _ _ _ _ _⟩





/-- The edge loop of a generator. -/
def genLoop (i : α)  := loopClass ρ [(i, true)]



/-- Attaching words are null-homotopic, so they give the trivial loop class. -/
theorem loopClass_att  : loopClass ρ ((presComplex ρ).att j) = 1 := by
  refine Quotient.sound ?_
  refine Htpy.of_step ⟨isPath_of_subsingleton _ _ _ _ _, isPath_of_subsingleton _ _ _ _ _, ?_⟩
  exact Or.inr ⟨[], [], j, by simp, rfl⟩

/-- The homomorphism `F → π₁(K)` sending a generator to its edge loop. -/
def freeToPi1  := FreeGroup.lift (genLoop ρ)

theorem freeToPi1_mk  :
    freeToPi1 ρ (FreeGroup.mk l) = loopClass ρ l := by
  induction l <;> aesop (add simp [freeToPi1])

theorem freeToPi1_relator  : freeToPi1 ρ (ρ j) = 1 := by
  have h : freeToPi1 ρ (ρ j) = loopClass ρ ((presComplex ρ).att j) := by
    grind [FreeGroup.mk_toWord, FiniteChains.Comb.freeToPi1_mk]
  rw [h, loopClass_att]

theorem relSub_le_ker_freeToPi1 : relSub ρ ≤ (freeToPi1 ρ).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨j, rfl⟩
  exact freeToPi1_relator ρ j

/-- The homomorphism `G → π₁(K)` induced by `F → π₁(K)`. -/
def presToPi1  :=
  QuotientGroup.lift (relSub ρ) (freeToPi1 ρ) (fun _ hx => relSub_le_ker_freeToPi1 ρ hx)

@[simp] theorem presToPi1_mk (w : FreeGroup α) :
    presToPi1 ρ (QuotientGroup.mk w) = freeToPi1 ρ w := rfl

/-! ### The isomorphism -/

theorem presToPi1_pi1ToPres (x : Pi1 (presComplex ρ) PUnit.unit) :
    presToPi1 ρ (pi1ToPres ρ x) = x := by
  induction x using Quotient.inductionOn with
  | h p =>
      solve_by_elim [FiniteChains.Comb.freeToPi1_mk]

theorem pi1ToPres_presToPi1 (g : PresGroup ρ) : pi1ToPres ρ (presToPi1 ρ g) = g := by
  induction g using QuotientGroup.induction_on with
  | H w =>
      rw [presToPi1_mk, ← FreeGroup.mk_toWord (x := w), freeToPi1_mk]
      show presWord ρ w.toWord = _
      rw [show presWord ρ w.toWord = QuotientGroup.mk (FreeGroup.mk w.toWord) from rfl,
        FreeGroup.mk_toWord]

/-- **The fundamental group of a presentation complex is the presented group**: the edge-path
group of `presComplex ρ` at its unique vertex is `F/⟪r_j⟫`. -/
def pi1PresEquiv : Pi1 (presComplex ρ) PUnit.unit ≃* PresGroup ρ where
  toFun := pi1ToPres ρ
  invFun := presToPi1 ρ
  left_inv := presToPi1_pi1ToPres ρ
  right_inv := pi1ToPres_presToPi1 ρ
  map_mul' := (pi1ToPres ρ).map_mul

end

end FiniteChains.Comb

