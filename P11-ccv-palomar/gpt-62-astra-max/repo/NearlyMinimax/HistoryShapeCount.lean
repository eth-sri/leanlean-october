module

public import NearlyMinimax.HistoryProjection


@[expose] public section

/-!
# Actual shape multiplicities and finite pair-chain coding

For fixed label multiplicities, a shape injects into one fixed-length binary
chain for each unordered distinct dependent pair. Its cardinality is therefore
at most the product of the pair-interleaving bounds used in the paper.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} [DecidableEq J]

section
variable {independent dependent : J → J → Prop} (j : J)

theorem historyWord_count_shape_invariant {u v : List J}
    (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) : u.count j = v.count j := by
  induction h with
  | rel _ _ h =>
    cases h with
    | swap before after x y hxy => simp [List.count_append, List.count_cons, Nat.add_comm, Nat.add_left_comm]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def historyShapeMultiplicity :
    DependenceHeap dependent → ℕ :=
  Quotient.lift (List.count j) (fun _ _ h => historyWord_count_shape_invariant j h)

end

section
variable (dependent : J → J → Prop)

theorem historyShapeMultiplicity_out (j : J)
    (g : DependenceHeap dependent) :
    (Quotient.out g).count j = historyShapeMultiplicity j g := congrArg (historyShapeMultiplicity j) (Quotient.out_eq g)

abbrev HistoryMultiplicityShape (n : J → ℕ) :=
  {g : DependenceHeap dependent // ∀ j, historyShapeMultiplicity j g = n j}

end

section
variable (i j : J) (word : List J)

theorem historyPairProjection_symm :
    historyPairProjection i j word = historyPairProjection j i word := by
  unfold historyPairProjection
  simp [or_comm]

theorem historyPairProjection_self :
    historyPairProjection j j word = List.replicate (word.count j) j := by
  induction word with
  | nil => tauto
  | cons a word ih =>
    by_cases haj : a = j
    · subst a
      simpa [historyPairProjection, List.replicate_succ] using congrArg (List.cons j) ih
    · simpa [historyPairProjection, haj] using ih

theorem historyPairProjection_length {i j : J} (hij : i ≠ j) (word : List J) :
    (historyPairProjection i j word).length = word.count i + word.count j := by
  induction word with
  | nil => tauto
  | cons a word ih =>
    by_cases hai : a = i
    · subst a
      simp [historyPairProjection] at ih
      simp [historyPairProjection, hij]
      omega
    · by_cases haj : a = j
      · subst a
        simp [historyPairProjection] at ih
        simp [historyPairProjection, Ne.symm hij]
        omega
      · simpa [historyPairProjection,  hai, haj] using ih

def historyPairBits : List Bool :=
  (historyPairProjection i j word).map (fun x => decide (x = j))

end

section
variable {i j : J} (hij : i ≠ j) (word : List J)
include hij

theorem historyPairBits_length :
    (historyPairBits i j word).length = word.count i + word.count j := by
  rw [historyPairBits, List.length_map, historyPairProjection_length hij]

theorem historyPairBits_reconstruct :
    (historyPairBits i j word).map (fun b => if b then j else i) = historyPairProjection i j word := by
  unfold historyPairBits
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (historyPairProjection i j word)]
  apply List.map_congr_left
  intro x hx
  grind [of_decide_eq_true (List.mem_filter.1 hx).2]

theorem historyPairProjection_eq_of_bits_eq {u v : List J}
    (h : historyPairBits i j u = historyPairBits i j v) : historyPairProjection i j u = historyPairProjection i j v := by
  rw [← historyPairBits_reconstruct hij u, ← historyPairBits_reconstruct hij v, h]

end

section
variable (dependent : J → J → Prop) [LinearOrder J]

abbrev HistoryOrderedDependentPair :=
  {p : J × J // p.1 < p.2 ∧ dependent p.1 p.2}

instance historyOrderedDependentPair_fintype [Fintype J] [LinearOrder J] (dependent : J → J → Prop) :
    Fintype (HistoryOrderedDependentPair dependent) := by
  unfold HistoryOrderedDependentPair
  exact Fintype.ofFinite _

def historyMultiplicityPairCode (n : J → ℕ)
    (g : HistoryMultiplicityShape dependent n) :
    ∀ p : HistoryOrderedDependentPair dependent, List.Vector Bool (n p.val.1 + n p.val.2) := fun p =>
  ⟨historyPairBits p.val.1 p.val.2 (Quotient.out g.val), by
    rw [historyPairBits_length p.prop.1.ne, historyShapeMultiplicity_out, historyShapeMultiplicity_out,
      g.prop p.val.1, g.prop p.val.2]⟩

end

theorem historyMultiplicityPairCode_injective {dependent : J → J → Prop} [LinearOrder J]
    [Std.Refl dependent] [Std.Symm dependent] (n : J → ℕ) :
    Function.Injective (historyMultiplicityPairCode dependent n) := by
  intro g h hcode
  have hproj : ∀ i j, dependent i j → historyPairProjection i j (Quotient.out g.val) = historyPairProjection i j (Quotient.out h.val) := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have he := congrArg Subtype.val (congrFun hcode ⟨⟨i, j⟩, hlt, hij⟩)
      exact historyPairProjection_eq_of_bits_eq hlt.ne he
    · subst j
      rw [historyPairProjection_self, historyPairProjection_self, historyShapeMultiplicity_out,
        historyShapeMultiplicity_out, g.prop i, h.prop i]
    · have he := congrArg Subtype.val (congrFun hcode ⟨⟨j, i⟩, hgt, symm hij⟩)
      rw [historyPairProjection_symm i j, historyPairProjection_symm i j]
      exact historyPairProjection_eq_of_bits_eq hgt.ne he
  apply Subtype.ext
  exact (Quotient.out_eq g.val).symm.trans ((Quotient.sound (historyShapeRelation_of_pair_projections hproj)).trans (Quotient.out_eq h.val))

variable [Fintype J] [LinearOrder J] {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent]
    (n : J → ℕ)

theorem historyMultiplicityShape_finite :
    Finite (HistoryMultiplicityShape dependent n) :=
  Finite.of_injective _ (historyMultiplicityPairCode_injective n)

theorem historyMultiplicityShape_card_le :
    Nat.card (HistoryMultiplicityShape dependent n) ≤
      ∏ p : HistoryOrderedDependentPair dependent, 2 ^ (n p.val.1 + n p.val.2) := by
  have hh := Nat.card_le_card_of_injective (historyMultiplicityPairCode dependent n)
    (historyMultiplicityPairCode_injective n)
  have hc : Nat.card (∀ p : HistoryOrderedDependentPair dependent, List.Vector Bool (n p.val.1 + n p.val.2)) =
      ∏ p : HistoryOrderedDependentPair dependent, 2 ^ (n p.val.1 + n p.val.2) := by
    norm_num
  rwa [hc] at hh

end NearlyMinimax
