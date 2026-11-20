module
public import proofs.HordijkSteelThreshold.BinaryReactionSplit
public import proofs.RAF.Concrete.Closure

/-! Word generation, localization at the first long word, and docking with finite reaction closure. -/

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete RAFCriticalWindowQuantitative
variable {M N K L B : ℕ}

/-- The ordinary literal reversible closure, with arbitrary temporary food cutoff. -/
noncomputable def temporaryReactionClosure (L : ℕ) (S : Finset (Reaction N)) :
    Finset (Molecule N) := Finset.univ.filter (fun x => ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS N L) S k)

variable (S : Finset (Reaction N))

lemma full_eq_temporary : fullClosure (binaryPolymerCRS N L) S = temporaryReactionClosure L S := by
  ext; simp [temporaryReactionClosure,full_mem]

/-- Reindex actual food molecules into the finite cutoff universe. This is the
same bounded-word injection used in the repository's reversible trace counts. -/
theorem binaryFood_card_le_cutoff (n L : ℕ) :
    (binaryFood n L).card ≤ Fintype.card (Molecule L) := by
  let f (x : binaryFood n L) := lowerMolecule x.val (Finset.mem_filter.mp x.property).2
  simpa using Fintype.card_le_of_injective f (fun _ _ e => Subtype.ext (lower_inj e))

/-- An infinite split-position environment. `openAt w k` records openness of
the ligation producing `w` at split position `k`. -/
abbrev InfiniteSplitEnvironment := List Bool → Nat → Prop

/-- Ordinary reversible generation in the countable word universe. Unlike
the older ligation-only exploration, this includes recovery of both factors. -/
inductive InfiniteReversibleGenerated (L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} (hne : w ≠ []) (hL : w.length ≤ L) :
      InfiniteReversibleGenerated L field w
  | ligate {u v} (hu : InfiniteReversibleGenerated L field u)
      (hv : InfiniteReversibleGenerated L field v) (ho : field (u ++ v) u.length) :
      InfiniteReversibleGenerated L field (u ++ v)
  | left {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field u
  | right {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field v

/-- Capping the universe just clips the food and closes overlong products. -/
abbrev FiniteReversibleGenerated (N L : ℕ) (field : InfiniteSplitEnvironment) :=
  InfiniteReversibleGenerated (min L N) (fun w i => field w i ∧ w.length ≤ N)

variable {φ ψ : InfiniteSplitEnvironment} {u v w : List Bool}

lemma InfiniteReversibleGenerated.bind (hl : ∀ u : List Bool, u ≠ [] → u.length ≤ L → InfiniteReversibleGenerated K ψ u) (hf : ∀ w i, φ w i → ψ w i)
    (h : InfiniteReversibleGenerated L φ w) : InfiniteReversibleGenerated K ψ w := by
  induction h <;> solve_by_elim (maxDepth := 8) [InfiniteReversibleGenerated.ligate,
    InfiniteReversibleGenerated.left,InfiniteReversibleGenerated.right]

lemma InfiniteReversibleGenerated.mono (hl : L ≤ K) (hf : ∀ w i, φ w i → ψ w i)
    (h : InfiniteReversibleGenerated L φ w) : InfiniteReversibleGenerated K ψ w :=
  h.bind (fun _ ne le => .food ne (le.trans hl)) hf

lemma InfiniteReversibleGenerated.bond (hu : u ≠ []) (hv : v ≠ []) (h : φ (u++v) u.length) :
    InfiniteReversibleGenerated L φ u ∧ InfiniteReversibleGenerated L φ v ↔ InfiniteReversibleGenerated L φ (u++v) :=
  ⟨fun ⟨l,r⟩ => .ligate l r h, fun p => ⟨.left hu hv p h,.right hu hv p h⟩⟩

lemma finiteReversibleGenerated_length_le (h : FiniteReversibleGenerated N L φ w) : w.length ≤ N := by
  induction h <;> grind

lemma finiteReversibleGenerated_mono_cap (hm : N ≤ M) (h : FiniteReversibleGenerated N L φ w) :
    FiniteReversibleGenerated M L φ w := by grind [h.mono]

lemma finiteReversibleGenerated_to_infinite (h : FiniteReversibleGenerated N L φ w) : InfiniteReversibleGenerated L φ w := by grind [h.mono]

abbrev Escapes (L B : ℕ) (φ : InfiniteSplitEnvironment) :=
  ∃ w, B < w.length ∧ InfiniteReversibleGenerated L φ w

abbrev RecordWord (B : ℕ) := {x : Molecule (2*B) // B < molLength x}

/-- Until the first record, every generated word has a derivation entirely
below the cutoff. The record itself can only be a ligation. -/
lemma escape_iff_record (hLB : L ≤ B) : Escapes L B φ ↔ ∃ x : RecordWord B,
    FiniteReversibleGenerated (moleculeWord x.val).length L φ (moleculeWord x.val) := by
  refine ⟨fun ⟨w,hw,hg⟩ => ?_, fun ⟨x,h⟩ => ⟨_,by simpa using x.property,finiteReversibleGenerated_to_infinite h⟩⟩
  by_contra! no
  apply hw.not_ge
  apply finiteReversibleGenerated_length_le (L := L) (φ := φ)
  clear hw
  induction hg with
  | food hn hl => exact .food hn (le_min hl (hl.trans hLB))
  | @ligate u v _ _ ho l r =>
    by_cases hb : (u++v).length ≤ B
    · exact .ligate l r ⟨ho,hb⟩
    have hc : (u++v).length ≤ 2*B := by have := finiteReversibleGenerated_length_le l; have := finiteReversibleGenerated_length_le r; grind
    let x := sourceWordMolecule (u++v) (by grind) hc
    exfalso; apply no ⟨x,by simpa [x] using lt_of_not_ge hb⟩
    simp only [x,sourceWordMolecule_word]
    exact .ligate (finiteReversibleGenerated_mono_cap (by omega) l) (finiteReversibleGenerated_mono_cap (by omega) r) ⟨ho,le_rfl⟩
  | left hu hv _ ho ih => exact .left hu hv ih ⟨ho,finiteReversibleGenerated_length_le ih⟩
  | right hu hv _ ho ih => exact .right hu hv ih ⟨ho,finiteReversibleGenerated_length_le ih⟩

noncomputable def restrictedSplitReactions (N : ℕ) (field : InfiniteSplitEnvironment) :
    Finset (Reaction N) := Finset.univ.filter
      (fun r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r))

theorem finiteReversible_iff_literalClosure (φ : InfiniteSplitEnvironment) (w : List Bool) :
    FiniteReversibleGenerated N L φ w ↔ ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N φ), moleculeWord x = w := by
  rw [←full_eq_temporary]
  let S := restrictedSplitReactions N φ
  let Q := binaryPolymerCRS N L
  let C := fullClosure Q S
  let good w := ∃ x ∈ C, moleculeWord x = w
  let G := FiniteReversibleGenerated N L φ
  change G w ↔ good w
  constructor
  · intro hw
    have mem x : good (moleculeWord x) ↔ x ∈ C := by simp only [good,moleculeWord_injective.eq_iff,exists_eq_right]
    have split {u v : List Bool} (hu : u ≠ []) (hv : v ≠ []) (ho : φ (u++v) u.length ∧ (u++v).length ≤ N) :
        good (u++v) ↔ good u ∧ good v := by
      obtain ⟨r,hl,hr,hp⟩ := source_append_split u v hu hv ho.2
      have hs : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by grind [moleculeWord_length,molLength_reactionLeft]⟩
      rw [←hp,←hl,←hr,mem,mem,mem]; simpa [C,Q,binaryPolymerCRS,Finset.insert_subset_iff] using (full_closed Q S r hs).symm
    have ne {u} : good u → u ≠ [] := fun ⟨x,_,he⟩ => he ▸ moleculeWord_nonempty x
    induction hw with
    | @food w hn hL =>
      let x := sourceWordMolecule w hn (le_min_iff.mp hL).2
      exact ⟨x,full_food Q S (by simpa [Q,x,binaryPolymerCRS,binaryFood] using (le_min_iff.mp hL).1),by simp [x]⟩
    | ligate | left | right => grind
  · rintro ⟨x,hx,rfl⟩
    let A := Finset.univ.filter fun y : Molecule N => G (moleculeWord y)
    suffices C ⊆ A from (Finset.mem_filter.mp (this hx)).2
    apply full_le
    · intro y hy; simp [A]; exact .food (by simp) (by simpa [Q,binaryPolymerCRS,binaryFood] using And.intro hy (moleculeWord_cap y))
    · intro r hr
      have ho := (Finset.mem_filter.mp hr).2
      simp only [Q,binaryPolymerCRS,Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_filter,Finset.mem_univ,true_and,A]
      rw [←reaction_words_append]
      apply InfiniteReversibleGenerated.bond <;> grind [reaction_words_append,moleculeWord_nonempty,moleculeWord_cap,moleculeWord_length,molLength_reactionLeft]

@[simp] lemma finite_word_iff {x : Molecule N} :
    FiniteReversibleGenerated N L φ (moleculeWord x) ↔ x ∈ temporaryReactionClosure L (restrictedSplitReactions N φ) := by
  simp [finiteReversible_iff_literalClosure,moleculeWord_injective.eq_iff]

abbrev hasLonger (K : ℕ) (C : Finset (Molecule N)) := ∃ x ∈ C, K < molLength x

lemma escape_of_large (h : hasLonger K (temporaryReactionClosure L (restrictedSplitReactions N φ))) : Escapes L K φ := by
  obtain ⟨x,hx,hl⟩ := h
  exact ⟨_,by simpa,finiteReversibleGenerated_to_infinite (finite_word_iff.mpr hx)⟩

lemma escape_iff_large (h : L ≤ K) (φ : InfiniteSplitEnvironment) : Escapes L K φ ↔
    hasLonger K (temporaryReactionClosure L (restrictedSplitReactions (2*K) φ)) := by
  refine ⟨fun he => ?_, escape_of_large⟩
  obtain ⟨x,hg⟩ := (escape_iff_record h).mp he
  exact ⟨x.val,finite_word_iff.mp (finiteReversibleGenerated_mono_cap (moleculeWord_cap _) hg),x.property⟩

def ReversibleUnbounded (L : ℕ) (φ : InfiniteSplitEnvironment) : Prop :=
  ∀ K : ℕ, ∃ w, K < w.length ∧ InfiniteReversibleGenerated L φ w

end HordijkSteelThreshold

namespace RAFCriticalWindowQuantitative
open RAF.Concrete RAF.Polymer HordijkSteelThreshold
def computedClosure (N L : ℕ) (S : Finset (Reaction N)) : Finset (Molecule N) :=
  revClosureAt (binaryPolymerCRS N L) S (Fintype.card (Molecule N))

end RAFCriticalWindowQuantitative
