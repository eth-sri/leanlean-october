module

public import proofs.HordijkSteelThreshold.MarkedCoreAdapter
public import proofs.HordijkSteelThreshold.WordDetourLiteralPaths

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

/-- The ordinary literal reversible closure, with arbitrary temporary food cutoff. -/
noncomputable def temporaryReactionClosure {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) :
    Finset (Molecule N) := Finset.univ.filter (fun x => ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS N L) S k)

@[simp] theorem mem_temporaryReactionClosure {N L : ℕ} (S : Finset (Reaction N))
    (x : Molecule N) : x ∈ temporaryReactionClosure L S ↔
      ∃ k, x ∈ revClosureAt (binaryPolymerCRS N L) S k := by
  simp [temporaryReactionClosure]

theorem temporaryReactionClosure_mono {N L : ℕ} {S T : Finset (Reaction N)}
    (hST : S ⊆ T) : temporaryReactionClosure L S ⊆ temporaryReactionClosure L T :=
  fun _ hx => let ⟨k, hk⟩ := (mem_temporaryReactionClosure S _).mp hx
    (mem_temporaryReactionClosure T _).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

theorem temporaryReactionClosure_food {N L : ℕ} (S : Finset (Reaction N))
    (x : Molecule N) (hx : molLength x ≤ L) : x ∈ temporaryReactionClosure L S :=
  (mem_temporaryReactionClosure S x).mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

theorem temporaryReactionClosure_ligation {N L : ℕ} (S : Finset (Reaction N))
    (r : Reaction N) (hr : r ∈ S)
    (hl : reactionLeft r ∈ temporaryReactionClosure L S)
    (hh : reactionRight r ∈ temporaryReactionClosure L S) :
    reactionProduct r ∈ temporaryReactionClosure L S := by
  obtain ⟨kl, hkl⟩ := (mem_temporaryReactionClosure S _).mp hl
  obtain ⟨kr, hkr⟩ := (mem_temporaryReactionClosure S _).mp hh
  have hl' := revClosureAt_mono_stage (binaryPolymerCRS N L) S (Nat.le_max_left kl kr) hkl
  have hr' := revClosureAt_mono_stage (binaryPolymerCRS N L) S (Nat.le_max_right kl kr) hkr
  refine (mem_temporaryReactionClosure S _).mpr ⟨max kl kr + 1, Finset.mem_union_right _ <|
    Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_union_left _ ?_⟩⟩
  rw [ite_eq_left (by simpa [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff] using And.intro hl' hr')]
  exact Finset.mem_singleton_self _

theorem temporaryReactionClosure_cleavage {N L : ℕ} (S : Finset (Reaction N))
    (r : Reaction N) (hr : r ∈ S)
    (hp : reactionProduct r ∈ temporaryReactionClosure L S) :
    reactionLeft r ∈ temporaryReactionClosure L S ∧
      reactionRight r ∈ temporaryReactionClosure L S := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S _).mp hp
  have hadd {x} (hx : x ∈ ({reactionLeft r, reactionRight r} : Finset (Molecule N))) :
      x ∈ temporaryReactionClosure L S :=
    (mem_temporaryReactionClosure S _).mpr ⟨k + 1, Finset.mem_union_right _ <|
      Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_union_right _ <| by
        rwa [ite_eq_left (by simpa [RevEnabledRhs, binaryPolymerCRS] using hk)]⟩⟩
  exact ⟨hadd (by simp), hadd (by simp)⟩

theorem moleculeWord_injective {N : ℕ} : Function.Injective (@moleculeWord N) := by
  rintro ⟨kx, vx⟩ ⟨ky, vy⟩ h
  have hh := congrArg List.length h
  rw [moleculeWord_length, moleculeWord_length, molLength, molLength] at hh
  cases Fin.ext (Nat.succ.inj hh)
  have hc := congrArg binaryWordCode h
  rw [binaryWordCode_moleculeWord, binaryWordCode_moleculeWord] at hc
  exact congrArg (Sigma.mk kx) (Fin.ext hc)

def contractedWordGenerated {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) (s : List Bool) : Prop :=
  ∀ x : Molecule N, contractFoodWord L (moleculeWord x) = s → x ∈ temporaryReactionClosure L S

theorem contractedWordGenerated_root {N L : ℕ} (S : Finset (Reaction N)) :
    contractedWordGenerated L S [] := fun x hx => by
  by_cases hlen : (moleculeWord x).length ≤ L
  · exact temporaryReactionClosure_food S x (by rwa [moleculeWord_length] at hlen)
  · rw [contractFoodWord, ite_eq_right hlen] at hx
    exact False.elim (by simpa [moleculeWord_length, molLength] using congrArg List.length hx)

theorem contractedWordGenerated_iff {N L : ℕ} (S : Finset (Reaction N)) (x : Molecule N) :
    contractedWordGenerated L S (contractFoodWord L (moleculeWord x)) ↔
      x ∈ temporaryReactionClosure L S :=
  ⟨fun h => h x rfl, fun hx y hy => by
    by_cases hxl : (moleculeWord x).length ≤ L
    · exact contractedWordGenerated_root S y (hy.trans (by simp [contractFoodWord, hxl]))
    · by_cases hyl : (moleculeWord y).length ≤ L
      · exact temporaryReactionClosure_food S y (by rwa [moleculeWord_length] at hyl)
      · rw [contractFoodWord, ite_eq_right hyl, contractFoodWord, ite_eq_right hxl] at hy
        exact moleculeWord_injective hy ▸ hx⟩

end HordijkSteelThreshold
