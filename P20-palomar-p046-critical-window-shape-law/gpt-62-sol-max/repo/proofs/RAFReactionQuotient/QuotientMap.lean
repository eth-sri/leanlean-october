module

public import proofs.RAF.Concrete.PolymerCRS
public import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryCRS
public import proofs.HordijkSteelThreshold.BinaryReactionSplit
public import proofs.RAFEmergenceApprox.RAFBounds
public import proofs.HordijkSteelThreshold.ReversibleClosure
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF.Concrete RAF.Polymer OverlapCorrectedRAF.Source HordijkSteelThreshold MeasureTheory unitInterval RAFCriticalWindowQuantitative
open scoped ENNReal

abbrev OrderedChannel (n : ℕ) :=
  {uv : Molecule n × Molecule n // molLength uv.1 + molLength uv.2 ≤ n}

theorem precedes_total {n : ℕ} (u v : Molecule n) :
    moleculePrecedes u v ∨ moleculePrecedes v u := by
  unfold moleculePrecedes
  omega

def canonical {n : ℕ} (r : OrderedChannel n) : RepositoryChannel n :=
  if h : displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2 then
    ⟨r.val, r.property, h⟩
  else
    ⟨(r.val.2, r.val.1), (Nat.add_comm (molLength r.val.2) (molLength r.val.1)).le.trans r.property,
      Or.inr ((precedes_total r.val.1 r.val.2).resolve_left (fun hp => h (Or.inr hp)))⟩

def splitToOrdered {n : ℕ} (r : Reaction n) : OrderedChannel n :=
  ⟨(reactionLeft r, reactionRight r), by
    simp only [molLength_reactionLeft, molLength_reactionRight, reaction_length_add]
    exact Nat.succ_le_of_lt r.1.isLt⟩

def splitToQuotient {n : ℕ} (r : Reaction n) : RepositoryChannel n :=
  canonical (splitToOrdered r)

theorem splitToQuotient_surjective (n : ℕ) : Function.Surjective (@splitToQuotient n) := by
  intro j
  obtain ⟨r,hl,hr,_⟩ := source_append_split
    (moleculeWord j.val.1) (moleculeWord j.val.2)
    (by simp [molLength]) (by simp [molLength])
    (by simpa using j.property.1)
  have he : splitToOrdered r = ⟨j.val,j.property.1⟩ :=
    Subtype.ext (Prod.ext (moleculeWord_injective hl) (moleculeWord_injective hr))
  exact ⟨r, by simp [splitToQuotient, he, canonical, j.property.2]⟩

noncomputable def quotientClosure (n L : ℕ) (S : Finset (RepositoryChannel n)) :
    Finset (Molecule n) := Finset.univ.filter
      (fun x => ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k)

noncomputable def quotientCatalyticLaw (n : ℕ) (p : I) :=
  RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : RepositoryChannel n => p)

/-- Canonicalize a valid split only when the factors commute and the right
factor is shorter. Equal-length commuting factors are identical, so there is
no separate tie to collapse. Invalid coordinates are harmless unused marks. -/
def canonicalIndex (z : List Bool × ℕ) : List Bool × ℕ :=
  if 0 < z.2 ∧ z.2 < z.1.length ∧ z.1.length-z.2 < z.2 ∧
      z.1.take z.2 ++ z.1.drop z.2 = z.1.drop z.2 ++ z.1.take z.2 then
    (z.1,z.1.length-z.2)
  else z

def quotientCut (z : SplitIndex) : ℕ := (canonicalIndex z).2

theorem quotientCut_relabel (z : SplitIndex) : CutMap.relabel quotientCut z = canonicalIndex z := by
  grind [quotientCut, CutMap.relabel, canonicalIndex]

def quotientField (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (canonicalIndex (w,k))

/-- Infinite reversible quotient survival, realized by iid marks on canonical
coordinates. Noncanonical and invalid latent coordinates do not affect it. -/
noncomputable def quotientSurvival (a : I) : ENNReal :=
  infiniteSplitPi a {ω | ReversibleUnbounded 2 (quotientField ω)}

variable {n : ℕ}

noncomputable def quotientCoordinate (j : RepositoryChannel n) : List Bool × ℕ :=
  (moleculeWord j.val.1 ++ moleculeWord j.val.2, molLength j.val.1)

theorem canonicalIndex_split (r : Reaction n) :
    canonicalIndex (literalSplitCoordinate r) = quotientCoordinate (splitToQuotient r) := by
  let u := reactionLeft r
  let v := reactionRight r
  have commutes : moleculeWord u ++ moleculeWord v = moleculeWord v ++ moleculeWord u ↔
      displayedConcat u v = displayedConcat v u := by
    calc
      _ ↔ binaryWordCode (moleculeWord u ++ moleculeWord v) = binaryWordCode (moleculeWord v ++ moleculeWord u) :=
        ⟨congrArg binaryWordCode, binaryWordCode_injective_length (by grind)⟩
      _ ↔ _ := by simp [displayedConcat]
  rw [literalSplitCoordinate, ← reaction_words_append, ← molLength_reactionLeft]
  change canonicalIndex (moleculeWord u ++ moleculeWord v, molLength u) =
    quotientCoordinate (canonical ⟨(u,v), (splitToOrdered r).property⟩)
  nth_rw 1 [← moleculeWord_length u]
  unfold canonicalIndex canonical quotientCoordinate
  simp only [List.length_append, List.take_left, List.drop_left, Nat.add_sub_cancel_left]
  simp only [moleculeWord_length, commutes]
  split <;> split <;> grind [molLength]

theorem quotient_sides {t : ℕ} (r : Reaction n) :
    (repositoryCRS n t).lhs (splitToQuotient r) = (binaryPolymerCRS n t).lhs r ∧
    (repositoryCRS n t).rhs (splitToQuotient r) = (binaryPolymerCRS n t).rhs r := by
  constructor
  · unfold splitToQuotient canonical
    split <;> first | rfl | exact Finset.pair_comm ..
  · have h := congrArg Prod.fst ((canonicalIndex_split r).symm.trans (quotientCut_relabel _).symm)
    apply congrArg ({·})
    apply molecule_ext
    · simpa [quotientCoordinate, CutMap.relabel, literalSplitCoordinate, concatMolecule] using congrArg List.length h
    · simpa [quotientCoordinate, CutMap.relabel, literalSplitCoordinate, concatMolecule, moleculeOfCode, concatCode,
        finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using congrArg binaryWordCode h

noncomputable def criticalOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-lambda)]⟩

theorem fullClosure_quotient_pullback {L : ℕ} (q : RepositoryChannel n → Prop) :
    fullClosure (repositoryCRS n L) (openChannels q) =
      fullClosure (binaryPolymerCRS n L) (openChannels (fun r => q (splitToQuotient r))) := by
  suffices ∀ k, revClosureAt (repositoryCRS n L) (openChannels q) k =
      revClosureAt (binaryPolymerCRS n L) (openChannels (fun r => q (splitToQuotient r))) k from this _
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    ext x
    simp only [revClosureAt, ih, mem_revClosureStep_ends, mem_openChannels,
      (splitToQuotient_surjective n).exists, fun r => (quotient_sides (t := L) r).1,
      fun r => (quotient_sides (t := L) r).2]

noncomputable def quotientCatalogue (N : ℕ) : FiniteCatalogue (RepositoryChannel N) N quotientCut where
  coordinate := quotientCoordinate
  injective := by
    intro j k h
    obtain ⟨h₁,h₂⟩ := List.append_inj (congrArg Prod.fst h)
      (by simpa only [moleculeWord_length, quotientCoordinate] using congrArg Prod.snd h)
    exact Subtype.ext (Prod.ext (moleculeWord_injective h₁) (moleculeWord_injective h₂))
  fix_short z h := by grind [quotientCut, canonicalIndex]
  chemistry := repositoryCRS N 0
  restrict L ω := by
    change fullClosure (repositoryCRS N L) _ = _
    rw [fullClosure_quotient_pullback]
    congr 1
    ext r
    simp only [restrictedSplitReactions, mem_openChannels, pullbackField, quotientCut_relabel,
      ← canonicalIndex_split, literalSplitCoordinate]

end RAFReactionQuotient
