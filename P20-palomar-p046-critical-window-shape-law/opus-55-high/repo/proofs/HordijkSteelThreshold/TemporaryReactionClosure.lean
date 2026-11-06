module

public import proofs.HordijkSteelThreshold.MarkedCoreAdapter
public import proofs.HordijkSteelThreshold.WordDetourLiteralPaths

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

variable {N : ℕ}

    (L : ℕ) (S : Finset $ Reaction N)

/-- The ordinary literal reversible closure, with arbitrary temporary food cutoff. -/
noncomputable def temporaryReactionClosure   :
    Finset (Molecule N) := Finset.univ.filter (fun x => ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS N L) S k)

@[simp] theorem mem_temporaryReactionClosure {N L : ℕ} (S : Finset $ Reaction N)
    (x : Molecule N) : x ∈ temporaryReactionClosure L S ↔
      ∃ k, x ∈ revClosureAt (binaryPolymerCRS N L) S k := by
  simp [temporaryReactionClosure]

theorem temporaryReactionClosure_mono {N L : ℕ} {S T : Finset $ Reaction N}
    (hST : S ⊆ T) : temporaryReactionClosure L S ⊆ temporaryReactionClosure L T := by
  simp only [Finset.subset_iff, mem_temporaryReactionClosure]
  exact fun x ⟨k, hk⟩ => ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

theorem temporaryReactionClosure_food {N L : ℕ} (S : Finset $ Reaction N)
    (x : Molecule N) (hx : molLength x ≤ L) : x ∈ temporaryReactionClosure L S :=
  (mem_temporaryReactionClosure S x).2 ⟨0, by simpa [revClosureAt, binaryPolymerCRS, binaryFood]⟩

theorem temporaryReactionClosure_ligation {N L : ℕ} (S : Finset $ Reaction N)
    (r : Reaction N) (hr : r ∈ S)
    (hl : reactionLeft r ∈ temporaryReactionClosure L S)
    (hh : reactionRight r ∈ temporaryReactionClosure L S) :
    reactionProduct r ∈ temporaryReactionClosure L S := by
  simp at *
  obtain ⟨⟨kl, hkl⟩, kr, hkr⟩ := And.intro hl hh
  have := revClosureAt_mono_stage _ S (le_max_left kl kr) hkl
  have := revClosureAt_mono_stage _ S (le_max_right kl kr) hkr
  refine ⟨max kl kr + 1, Finset.mem_union_right _ $ Finset.mem_biUnion.2 ⟨r, hr, ?_⟩⟩
  simp_all [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff]

theorem temporaryReactionClosure_cleavage {N L : ℕ} (S : Finset $ Reaction N)
    (r : Reaction N) (hr : r ∈ S)
    (hp : reactionProduct r ∈ temporaryReactionClosure L S) :
    reactionLeft r ∈ temporaryReactionClosure L S ∧
      reactionRight r ∈ temporaryReactionClosure L S := by
  simp at *
  obtain ⟨k, hk⟩ := hp
  have h : {reactionLeft r, reactionRight r} ⊆ revClosureAt (binaryPolymerCRS N L) S (k+1) :=
    fun x hx => Finset.mem_union_right _ $ Finset.mem_biUnion.2 ⟨r, hr, by
      simp_all [RevEnabledRhs, binaryPolymerCRS]; tauto⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at h
  grind

theorem moleculeWord_injective  : Function.Injective (@moleculeWord N) := by
  rintro ⟨kx, vx⟩ ⟨ky, vy⟩ h
  have h1 := congrArg List.length h
  have h2 := congrArg binaryWordCode h
  simp only [moleculeWord_length, binaryWordCode_moleculeWord, molLength] at h1 h2
  obtain rfl : kx = ky := Fin.ext $ by omega
  grind

/-- Generability is well defined on contracted words: every representative of
food is generated, while a nonfood word has a unique source molecule. -/
def contractedWordGenerated   (s : List Bool) : Prop :=
  ∀ x : Molecule N, contractFoodWord L (moleculeWord x) = s → x ∈ temporaryReactionClosure L S


theorem contractedWordGenerated_root {N L : ℕ} (S : Finset $ Reaction N) :
    contractedWordGenerated L S [] := fun x hx => temporaryReactionClosure_food S x (by
  have := moleculeWord_length x; grind [contractFoodWord])

theorem contractedWordGenerated_iff {N L : ℕ} (S : Finset $ Reaction N) (x : Molecule N) :
    contractedWordGenerated L S (contractFoodWord L $ moleculeWord x) ↔
      x ∈ temporaryReactionClosure L S := by
  refine ⟨fun h => h x rfl, fun hx y hy => ?_⟩
  by_cases hyl : (moleculeWord y).length ≤ L
  · exact temporaryReactionClosure_food S y $ by rwa [moleculeWord_length] at hyl
  · unfold contractFoodWord at hy
    split_ifs at hy
    · simp_all
    · exact moleculeWord_injective hy ▸ hx

end HordijkSteelThreshold
