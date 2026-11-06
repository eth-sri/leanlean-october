module

public import NearlyMinimax.HistoryProjection
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗎

/-!
# Actual shape multiplicities and finite pair-chain coding

For fixed label multiplicities, a shape injects into one fixed-length binary
chain for each unordered distinct dependent pair. Its cardinality is therefore
at most the product of the pair-interleaving bounds used in the paper.
-/


variable {J : Type*} [DecidableEq J]

theorem historyWord_count_shape_invariant independent (j : J)
    (h : 𝚞₁ u v) : u.count j = v.count j := by
  induction h with
  | rel _ _ h =>
    cases h with
    | swap before after x y hxy => simp [List.count_cons, Nat.add_comm, Nat.add_left_comm]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

𝗇 𝔄 𝖴
𝗇 𝔇 𝙁
def historyShapeMultiplicity (dependent : 𝔇) (j : J) :
    HistoryShape 𝔄 → ℕ :=
  Quotient.lift (List.count j) fun _ _ h => historyWord_count_shape_invariant _ j h

𝗇 𝔏 historyShapeMultiplicity dependent j
theorem historyShapeMultiplicity_out dependent (j : J)
    g :
    (Quotient.out g).count j = 𝔏 g := congrArg 𝔏 $ Quotient.out_eq g

𝗇 𝔐 J → ℕ
abbrev HistoryMultiplicityShape (dependent : 𝔇) (n : 𝔐) :=
  {g : HistoryShape 𝔄 // ∀ j, 𝔏 g = n j}

𝗇 𝔈 historyPairProjection i j word
theorem historyPairProjection_symm (i j : J) word :
    𝔈 = historyPairProjection j i word := by
  unfold historyPairProjection
  grind

theorem historyPairProjection_self (j : J) word :
    historyPairProjection j j word = List.replicate (word.count j) j := by
  induction word with
  | nil => simp [historyPairProjection]
  | cons a word ih =>
    by_cases haj : a = j
    · subst a
      simpa [historyPairProjection, List.replicate_succ] using congrArg (List.cons j) ih
    · simpa [historyPairProjection, haj] using ih

𝗇 𝔑 𝘚₁
theorem historyPairProjection_length (hij : 𝔑) (word : List J) :
    (𝔈).length = word.count i + word.count j := by
  induction word with
  | nil => simp [historyPairProjection]
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
      · simpa [historyPairProjection, List.count_cons, hai, haj] using ih

def historyPairBits (i j : J) (word : List J) : List Bool :=
  (𝔈).map fun x => decide $ x = j

𝗇 𝔒 historyPairBits i j
theorem historyPairBits_length (hij : 𝔑) (word : List J) :
    (𝔒 word).length = word.count i + word.count j := by
  rw [historyPairBits, List.length_map, historyPairProjection_length hij]

theorem historyPairBits_reconstruct (hij : 𝔑) (word : List J) :
    (𝔒 word).map (fun b => if b then j else i) = 𝔈 := by
  unfold historyPairBits
  rw [List.map_map]
  conv_rhs => rw [← List.map_id 𝔈]
  apply List.map_congr_left
  intro x hx
  have hm := of_decide_eq_true (List.mem_filter.1 hx).2
  grind

𝗇 𝔓 historyPairProjection i j
theorem historyPairProjection_eq_of_bits_eq {i j : J} (hij : 𝔑) {u v }
    (h : 𝔒 u = 𝔒 v) : 𝔓 u = 𝔓 v := by
  rw [← historyPairBits_reconstruct hij u, ← historyPairBits_reconstruct hij v, h]

abbrev HistoryOrderedDependentPair (dependent : 𝔇) [LinearOrder J] :=
  {p : J × J // p.1 < p.2 ∧ dependent p.1 p.2}

instance historyOrderedDependentPair_fintype [Fintype J] [LinearOrder J] (dependent : 𝔇) :
    Fintype $ HistoryOrderedDependentPair dependent := Fintype.ofFinite _

𝗇 𝔊 HistoryMultiplicityShape dependent n
𝗇 𝔍 n p.val.1 + n p.val.2
def historyMultiplicityPairCode (dependent : 𝔇) [LinearOrder J] (n : 𝔐)
    (g : 𝔊) :
    ∀ p : HistoryOrderedDependentPair dependent, List.Vector Bool 𝔍 := fun p =>
  ⟨historyPairBits p.val.1 p.val.2 $ Quotient.out g.val , by
    rw [historyPairBits_length p.prop.1.ne, historyShapeMultiplicity_out, historyShapeMultiplicity_out,
      g.prop p.val.1, g.prop p.val.2]⟩

𝗇 𝔅 𝘼
𝗇 𝔉 ∀ i, dependent i i
𝗇 𝔔 historyMultiplicityPairCode dependent n
theorem historyMultiplicityPairCode_injective (dependent : 𝔇) [LinearOrder J]
    (hrefl : 𝔉) (hsymm : 𝔅) n :
    Function.Injective 𝔔 := by
  intro g h hcode
  have hproj : ∀ i j, dependent i j → 𝔓 (Quotient.out g.val) = 𝔓 (Quotient.out h.val) := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact historyPairProjection_eq_of_bits_eq hlt.ne $ congrArg Subtype.val $ congrFun hcode ⟨⟨i, j⟩, hlt, hij⟩
    · subst j
      rw [historyPairProjection_self, historyPairProjection_self, historyShapeMultiplicity_out,
        historyShapeMultiplicity_out, g.prop i, h.prop i]
    · rw [historyPairProjection_symm i j, historyPairProjection_symm i j]
      exact historyPairProjection_eq_of_bits_eq hgt.ne $ congrArg Subtype.val $ congrFun hcode ⟨⟨j, i⟩, hgt, hsymm hij⟩
  apply Subtype.ext
  have hh : Quotient.mk (historyShapeSetoid 𝔄) (Quotient.out g.val) =
      Quotient.mk (historyShapeSetoid 𝔄) (Quotient.out h.val) :=
    Quotient.sound $ historyShapeRelation_of_pair_projections hrefl hsymm hproj
  exact (Quotient.out_eq g.val).symm.trans $ hh.trans $ Quotient.out_eq h.val

𝗇 𝔎 historyMultiplicityPairCode_injective dependent hrefl hsymm n
theorem historyMultiplicityShape_finite [Fintype J] [LinearOrder J] dependent
    (hrefl : 𝔉) (hsymm : 𝔅) (n : 𝔐) :
    Finite 𝔊 :=
  Finite.of_injective _ 𝔎

theorem historyMultiplicityShape_card_le [Fintype J] [LinearOrder J] dependent
    (hrefl : 𝔉) (hsymm : 𝔅) (n : 𝔐) :
    Nat.card 𝔊 ≤
      ∏ p : HistoryOrderedDependentPair dependent, 2 ^ 𝔍 := by
  let := historyMultiplicityShape_finite dependent hrefl hsymm n
  have hh := Nat.card_le_card_of_injective 𝔔
    𝔎
  simp_all
