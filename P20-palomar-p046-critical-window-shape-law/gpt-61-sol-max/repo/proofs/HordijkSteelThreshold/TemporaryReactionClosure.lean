import proofs.RAFReactionQuotient.QuotientMap

import proofs.HordijkSteelThreshold.InfiniteLigation
import proofs.HordijkSteelThreshold.GatewayCavity
import proofs.HordijkSteelThreshold.WordDetourSource
import proofs.HordijkSteelThreshold.WordDetourIncidence
import proofs.HordijkSteelThreshold.BasicSourceEdges




namespace HordijkSteelThreshold
abbrev NearFull {X : Type*} [Fintype X] (m : ℕ) (S : Finset X) :=
  (m-1)*Fintype.card X ≤ m*S.card

abbrev MassDeficit {X : Type*} [Fintype X] (m : ℕ) (S : Finset X) :=
  m*S.card < (m-1)*Fintype.card X


variable {L N : ℕ}
open RAF.Concrete





variable {M R : Type*}

variable [DecidableEq M] (Q : ReversibleCRS M R) (S : Finset R)

theorem revClosureAt_subset_succ   (k : Nat) :
    revClosureAt Q S k ⊆ revClosureAt Q S (k + 1) := by
  intro x hx
  
  exact Finset.mem_union_left _ hx

theorem revClosureAt_mono_stage   {i j : Nat} (hij : i ≤ j) :
    revClosureAt Q S i ⊆ revClosureAt Q S j := by
  exact monotone_nat_of_le_succ (revClosureAt_subset_succ Q S) hij

variable (s : List Bool) (side : Bool)

def wordDropShort  (k : ℕ)  :=
  if side then s.take (s.length-k) else s.drop k

theorem wordDropShort_length  (k : ℕ) :
    (wordDropShort s side k).length = s.length-k := by grind [wordDropShort]

theorem wordDropShort_one  :
    wordDropShort s side 1 = if side then s.dropLast else s.tail := by
  cases side <;> simp [wordDropShort, List.dropLast_eq_take]

theorem wordDropShort_comp  (j : ℕ) :
    wordDropShort (wordDropShort s side 1) side j =
      wordDropShort s side (j+1) := by
  simp_all [HordijkSteelThreshold.wordDropShort] ; grind

variable  (e : WordBasicEdge L N)

theorem contract_wordDropShort_one  :
    contractFoodWord L (wordDropShort e.1.val e.2 1) = (wordEdgeParent e).val := by
  rw [wordDropShort_one]
  aesop (add simp [HordijkSteelThreshold.WordBasicEdge, contractFoodWord, wordDropShort, HordijkSteelThreshold.BoundedFoodWord, wordEdgeParent])

theorem wordEdgeParent_nonroot_word 
    (h : wordEdgeParent e ≠ boundedFoodRoot L N) :
    (wordEdgeParent e).val = wordDropShort e.1.val e.2 1 := by
  have he := contract_wordDropShort_one e
  aesop (add simp [HordijkSteelThreshold.WordBasicEdge, HordijkSteelThreshold.BoundedFoodWord, wordEdgeParent, boundedFoodRoot, wordDropShort, contractFoodWord])

theorem wordEdgeParent_root_length 
    (h : wordEdgeParent e = boundedFoodRoot L N) : e.1.val.length ≤ L+1 := by
  have he := contract_wordDropShort_one e
  grind [boundedFoodRoot, contractFoodWord, wordDropShort]

variable {w : ℕ}

def wordShortStart  (r : WordShortKey L N w)  :=
  contractFoodWord L r.1.1.val

def wordShortEnd  (r : WordShortKey L N w)  :=
  contractFoodWord L (wordDropShort r.1.1.val r.1.2 (r.2.val+1))

open RAF.Polymer

theorem wordDetour_reach_parent
    (d : WordShortKey L N w) :
    indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
      (wordShortStart d) (wordEdgeParent d.1).val := by
  have upper : indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
      _ _ :=
    Relation.EqvGen.rel _ _ ⟨d, by simp [wordDetourKeys], rfl, rfl⟩
  by_cases hj : d.2.val = 0
  · have he : wordShortEnd d = (wordEdgeParent d.1).val := by
      simpa [wordShortEnd, hj] using contract_wordDropShort_one d.1
    exact he ▸ upper
  · by_cases hp : wordEdgeParent d.1 = boundedFoodRoot L N
    · have hm := wordEdgeParent_root_length d.1 hp
      have he : wordShortEnd d = (wordEdgeParent d.1).val := by
        rw [hp]

        apply ite_eq_left
        rw [wordDropShort_length]
        omega
      exact he ▸ upper
    · let r : WordShortKey L N w :=
        ((wordEdgeParent d.1, d.1.2), ⟨d.2.val-1, lt_of_le_of_lt (Nat.sub_le _ _) d.2.isLt⟩)
      have hlower : wordDetourLower d = some r := by
        simp [wordDetourLower, hj, hp]
        rfl
      have hr : r ∈ wordDetourKeys d := by simp [wordDetourKeys, hlower]
      have hrs : contractFoodWord L (wordEdgeParent d.1).val = (wordEdgeParent d.1).val :=
        ite_eq_right (not_le.mpr (boundedFoodWord_nonroot_length _ hp))
      have hre  := by
        have hjr : d.2.val-1+1 = d.2.val := by omega
        change contractFoodWord L (wordDropShort (wordEdgeParent d.1).val d.1.2
          (d.2.val-1+1)) = wordShortEnd d
        rw [hjr, wordEdgeParent_nonroot_word d.1 hp, wordDropShort_comp]
        rfl

      exact _root_.trans upper (_root_.symm (Relation.EqvGen.rel _ _ ⟨r, hr, hrs, hre⟩))


open Classical


/-- The ordinary literal reversible closure, with arbitrary temporary food cutoff. -/
noncomputable def temporaryReactionClosure  (L : ℕ) (S : Finset (Reaction N))  := Finset.univ.filter (fun x => ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS N L) S k)

variable  (S : Finset (Reaction N))

variable (x : Molecule N)

@[simp] theorem mem_temporaryReactionClosure 
     : x ∈ temporaryReactionClosure L S ↔
      ∃ k, x ∈ revClosureAt (binaryPolymerCRS N L) S k := by
  simp [temporaryReactionClosure]

theorem temporaryReactionClosure_mono {N L : ℕ} {S T : Finset (Reaction N)}
    (hST : S ⊆ T) : temporaryReactionClosure L S ⊆ temporaryReactionClosure L T := by
  intro x hx
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
  exact (mem_temporaryReactionClosure T x).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

theorem temporaryReactionClosure_food 
     (hx : molLength x ≤ L) : x ∈ temporaryReactionClosure L S := by
  apply (mem_temporaryReactionClosure S x).mpr
  exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

theorem moleculeWord_injective  : Function.Injective (@moleculeWord N) := by
  intro x y h
  
  
  have hh := congrArg (fun s => (s.length, binaryWordCode s)) h
  simp only [moleculeWord_length, binaryWordCode_moleculeWord, Prod.mk.injEq] at hh
  exact RAFReactionQuotient.molecule_ext hh.1 hh.2

/-- Generability is well defined on contracted words: every representative of
food is generated, while a nonfood word has a unique source molecule. -/
def contractedWordGenerated  (L : ℕ) (S : _) (s : List Bool)  :=
  ∀ x : Molecule N, contractFoodWord L (moleculeWord x) = s → x ∈ temporaryReactionClosure L S

theorem contractedWordGenerated_root  :
    contractedWordGenerated L S [] := by
  grind [contractedWordGenerated, contractFoodWord, moleculeWord, temporaryReactionClosure_food]

theorem contractedWordGenerated_iff   :
    contractedWordGenerated L S (contractFoodWord L (moleculeWord x)) ↔
      x ∈ temporaryReactionClosure L S := by
  grind [contractedWordGenerated, contractFoodWord, moleculeWord, temporaryReactionClosure_food, moleculeWord_injective]

end HordijkSteelThreshold
