module
public import proofs.RAFReactionQuotient.QuotientMap
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw

/-! Canonical physical coordinates and the infinite quotient law. -/

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
variable {n : ℕ}

/-- Canonicalize a valid split only when the factors commute and the right
factor is shorter. Equal-length commuting factors are identical, so there is
no separate tie to collapse. Invalid coordinates are harmless unused marks. -/
def canonicalIndex (z : List Bool × ℕ) : List Bool × ℕ :=
  if 0 < z.2 ∧ z.2 < z.1.length ∧ z.1.length-z.2 < z.2 ∧
      z.1.take z.2 ++ z.1.drop z.2 = z.1.drop z.2 ++ z.1.take z.2 then
    (z.1,z.1.length-z.2)
  else z

@[simp] theorem canonicalIndex_product (z : List Bool × ℕ) :
    (canonicalIndex z).1 = z.1 := by unfold canonicalIndex; split <;> rfl

def quotientField (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (canonicalIndex (w,k))

/-- Infinite reversible quotient survival, realized by iid marks on canonical
coordinates. Noncanonical and invalid latent coordinates do not affect it. -/
noncomputable def quotientSurvival (a : I) : ENNReal :=
  infiniteSplitPi a {ω | ReversibleUnbounded 2 (quotientField ω)}


def orderedCoordinate (r : OrderedChannel n) : List Bool × ℕ :=
  (moleculeWord r.val.1 ++ moleculeWord r.val.2, molLength r.val.1)

theorem orderedCoordinate_split (r : Reaction n) :
    orderedCoordinate (splitToOrdered r) = literalSplitCoordinate r := Prod.ext (reaction_words_append r) rfl

theorem orderedCoordinate_injective (n : ℕ) : Function.Injective (@orderedCoordinate n) := by
  intro q j he
  have h := List.append_inj (congrArg Prod.fst he) (show (moleculeWord q.val.1).length = (moleculeWord j.val.1).length by
    simp only [moleculeWord_length]; exact congrArg Prod.snd he)
  exact Subtype.ext (Prod.ext (moleculeWord_injective h.1) (moleculeWord_injective h.2))

noncomputable def quotientCoordinate (j : RepositoryChannel n) : List Bool × ℕ :=
  orderedCoordinate ⟨j.val,j.property.1⟩

theorem word_comm_iff (u v : Molecule n) :
    moleculeWord u ++ moleculeWord v = moleculeWord v ++ moleculeWord u ↔
      displayedConcat u v = displayedConcat v u := by
  constructor
  · intro h; simpa [displayedConcat] using congrArg binaryWordCode h
  · intro h; exact binaryWordCode_injective_length (by simp [Nat.add_comm]) (by simpa [displayedConcat] using h)

private theorem canonicalIndex_ordered (r : OrderedChannel n) :
    canonicalIndex (orderedCoordinate r) = quotientCoordinate (canonical r) := by
  rcases r with ⟨⟨u,v⟩,h⟩
  have hv : 1 < 2 ^ molLength v := by simp [molLength]
  unfold canonical
  split <;> simp [canonicalIndex,orderedCoordinate,quotientCoordinate,moleculeWord_length,molLength] <;>
    grind [word_comm_iff,displayedConcat,molLength]

theorem canonicalIndex_split (r : Reaction n) :
    canonicalIndex (literalSplitCoordinate r) = quotientCoordinate (splitToQuotient r) := by
  rw [← orderedCoordinate_split]
  exact canonicalIndex_ordered _

end RAFReactionQuotient
