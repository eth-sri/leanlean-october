
import proofs.HordijkSteelThreshold.InfiniteLigation
import proofs.HordijkSteelThreshold.TargetTrials




namespace HordijkSteelThreshold

variable {L N : ℕ}
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

inductive FiniteReversibleGenerated (N L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} (hne : w ≠ []) (hL : w.length ≤ L) (hN : w.length ≤ N) :
      FiniteReversibleGenerated N L field w
  | ligate {u v} (hu : FiniteReversibleGenerated N L field u)
      (hv : FiniteReversibleGenerated N L field v) (ho : field (u ++ v) u.length)
      (hN : (u ++ v).length ≤ N) : FiniteReversibleGenerated N L field (u ++ v)
  | left {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : FiniteReversibleGenerated N L field (u ++ v))
      (ho : field (u ++ v) u.length) : FiniteReversibleGenerated N L field u
  | right {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : FiniteReversibleGenerated N L field (u ++ v))
      (ho : field (u ++ v) u.length) : FiniteReversibleGenerated N L field v

theorem finiteReversibleGenerated_mono_cap {N M L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool} (hNM : N ≤ M)
    (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated M L field w := by
  induction h <;> grind [FiniteReversibleGenerated]

theorem finiteReversibleGenerated_to_infinite {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : InfiniteReversibleGenerated L field w := by
  induction h <;> grind [InfiniteReversibleGenerated]

variable  {field : InfiniteSplitEnvironment} {w : List Bool}

theorem infiniteReversibleGenerated_iff_finite_certificate :
    InfiniteReversibleGenerated L field w ↔ ∃ N, FiniteReversibleGenerated N L field w := by
  constructor
  · intro h
    induction h with
    | @ligate u v _ _ ho ihu ihv =>
      obtain ⟨N, hN⟩ := ihu
      obtain ⟨M, hM⟩ := ihv
      refine ⟨max (max N M) (u ++ v).length, .ligate
        (finiteReversibleGenerated_mono_cap (by omega) hN)
        (finiteReversibleGenerated_mono_cap (by omega) hM) ho (by omega)⟩
    | _ => first | tauto | grind [FiniteReversibleGenerated]
  · rintro ⟨_,h⟩
    exact finiteReversibleGenerated_to_infinite h

open Classical RAF.Polymer RAF.Concrete

noncomputable def restrictedSplitReactions (N : ℕ) (field : InfiniteSplitEnvironment) :
    Finset (Reaction N) := Finset.univ.filter
      fun r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)

variable  (x : Molecule N)

theorem moleculeWord_nonempty  : moleculeWord x ≠ [] := by grind [moleculeWord, molLength]

theorem moleculeWord_cap  : (moleculeWord x).length ≤ N := by grind [moleculeWord, molLength]

theorem reaction_words_append {N : ℕ} (r : Reaction N) :
    moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r) =
      moleculeWord (reactionProduct r) := by
  rw [moleculeWord_reactionLeft, moleculeWord_reactionRight, List.take_append_drop]


variable (field : InfiniteSplitEnvironment)

theorem literalClosure_to_finiteReversible  
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L (restrictedSplitReactions N field)) :
    FiniteReversibleGenerated N L field (moleculeWord x) := by
  apply temporaryReactionClosure_induction (restrictedSplitReactions N field)
    (fun y => FiniteReversibleGenerated N L field (moleculeWord y)) ?_ ?_ ?_ x hx <;>
  grind [FiniteReversibleGenerated,
    moleculeWord_nonempty, moleculeWord_cap, reaction_words_append, moleculeWord_length,
    molLength_reactionLeft, restrictedSplitReactions]

theorem finiteReversible_to_literalClosure  {field : InfiniteSplitEnvironment}
    {w : List Bool} (hw : FiniteReversibleGenerated N L field w) :
    ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w := by
  let S := restrictedSplitReactions N field
  have split_mem (u v : List Bool) (r : Reaction N)
      (hl : moleculeWord (reactionLeft r) = u)
      (hp : moleculeWord (reactionProduct r) = u ++ v) (ho : field (u ++ v) u.length) : r ∈ S := by
    grind [restrictedSplitReactions, moleculeWord_length, molLength_reactionLeft]
  induction hw with
  | @food w hn hL hN =>
    let x := sourceWordMolecule w (List.length_pos_iff.mpr hn) hN
    exact ⟨x, temporaryReactionClosure_food S x (by simpa [x] using hL),
      sourceWordMolecule_word _ _ _⟩
  | @ligate u v _ _ ho hN ihu ihv =>
    obtain ⟨x, hx, hxu⟩ := ihu
    obtain ⟨y, hy, hyv⟩ := ihv
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr (hxu ▸ moleculeWord_nonempty x))
      (List.length_pos_iff.mpr (hyv ▸ moleculeWord_nonempty y)) (by simpa using hN)
    
    grind [moleculeWord_injective, temporaryReactionClosure_rules]
  | @left u v hu hv _ ho ih | @right u v hu hv _ ho ih =>
    obtain ⟨x, hx, hxp⟩ := ih
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr hu) (List.length_pos_iff.mpr hv)
      (by rw [← List.length_append, ← hxp]; exact moleculeWord_cap x)
    
    grind [moleculeWord_injective, temporaryReactionClosure_rules]

abbrev finiteReversible_iff_literalClosure (w : List Bool) :=
  Iff.intro (@finiteReversible_to_literalClosure N L field w)
    (fun ⟨x, hx, he⟩ => he ▸ literalClosure_to_finiteReversible field x hx)

open MeasureTheory

variable (N L : ℕ)

@[fun_prop] theorem measurable_finiteReversibleGenerated  (w : List Bool) :
    Measurable (fun field : InfiniteSplitEnvironment => FiniteReversibleGenerated N L field w) := by
  simp_rw [finiteReversible_iff_literalClosure]
  
  exact (measurable_of_finite fun ω : Reaction N → Prop => ∃ x ∈ temporaryReactionClosure L
    (Finset.univ.filter ω), moleculeWord x = w).comp (by fun_prop)

variable (L : ℕ)

@[fun_prop] theorem measurable_infiniteReversibleGenerated  (w : List Bool) :
    Measurable (fun field : InfiniteSplitEnvironment => InfiniteReversibleGenerated L field w) := by
  simp_rw [infiniteReversibleGenerated_iff_finite_certificate]
  fun_prop

variable (seed : Finset (List Bool))

theorem measurableSet_infinite_seed   :
    MeasurableSet {field : InfiniteSplitEnvironment |
      ∀ w ∈ seed, InfiniteReversibleGenerated L field w} := by
  apply Measurable.setOf
  fun_prop

/-- Any finite collection of infinite generation certificates fits in one cap. -/
theorem finite_seed_common_cap {L : ℕ} {field : InfiniteSplitEnvironment}
    (seed : Finset _) :
    (∀ w ∈ seed, InfiniteReversibleGenerated L field w) ↔
      ∃ N, ∀ w ∈ seed, FiniteReversibleGenerated N L field w := by
  simp only [infiniteReversibleGenerated_iff_finite_certificate]
  simpa only [iSup_Prop_eq, iInf_Prop_eq, Finset.mem_coe] using
    (iff_of_eq (seed.finite_toSet.iSup_biInf_of_monotone
      (f := fun w N => FiniteReversibleGenerated N L field w)
      (fun _ _ _ _ h => finiteReversibleGenerated_mono_cap h))).symm




end HordijkSteelThreshold
