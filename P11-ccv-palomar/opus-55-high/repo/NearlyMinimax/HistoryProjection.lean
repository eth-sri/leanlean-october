module

public import NearlyMinimax.HistoryShapes
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# Dependent-pair projections determine a history shape

The projections of a word onto each dependent pair of labels are invariant
under consecutive independent exchanges. Conversely, equality of these
projections produces such exchanges, by moving the first letter through its
independent predecessors. This is the concrete injective encoding used for
the finite reference-law normalizer in `lower_heaps`.
-/


variable {J : Type*} [DecidableEq J]

𝗇 𝔍 x = i ∨ x = j
def historyPairProjection (i j : J) (word : List J) : List J :=
  word.filter fun x => decide 𝔍

𝗇 𝔄 𝘼
𝗇 𝔇 ∀ i, dependent i i
𝗇 𝔉 𝙁
𝗇 𝔎 y = i ∨ y = j
𝗇 𝔑 dependent i j
omit [DecidableEq J] in
theorem history_dependent_pair_members {dependent : 𝔉}
    (hrefl : 𝔇) (hsymm : 𝔄)
    {i j x y : J} (hij : 𝔑) (hx : 𝔍) (hy : 𝔎) :
    dependent x y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact hrefl _
  · exact hij
  · exact hsymm hij
  · exact hrefl _

𝗇 𝔅 𝖴
𝗇 𝔊 historyPairProjection i j u = historyPairProjection i j v
theorem historyPairProjection_exchange {dependent : 𝔉}
    (hrefl : 𝔇) (hsymm : 𝔄)
    {i j } (hij : 𝔑) {u v }
    (h : IndependentHistoryExchange 𝔅 u v) :
    𝔊 := by
  cases h with
  | swap before after x y hxy =>
    by_cases hx : 𝔍
    · have hy : ¬ 𝔎 := fun hy => hxy $ history_dependent_pair_members hrefl hsymm hij hx hy
      simp [historyPairProjection, hx, hy]
    · by_cases hy : 𝔎 <;> simp [historyPairProjection, hx, hy]

𝗇 𝔓 Relation.EqvGen (IndependentHistoryExchange 𝔅) u v
theorem historyPairProjection_shape_invariant {dependent : 𝔉}
    (hrefl : 𝔇) (hsymm : 𝔄)
    {i j } (hij : 𝔑) {u v }
    (h : 𝔓) :
    𝔊 := by
  induction h with
  | rel _ _ h => exact historyPairProjection_exchange hrefl hsymm hij h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

𝗃 𝔐 a :: ἀ
𝗇 𝔏 before ++ 𝔐 after
theorem history_first_decomposition (ha : a ∈ word) :
    ∃ before after, word = 𝔏 ∧ a ∉ before := by
  induction word with
  | nil => simp at ha
  | cons b word ih =>
    by_cases hba : b = a
    · subst b; exact ⟨[], word, rfl, 𝖢₄⟩
    · obtain ⟨before, after, hword, hbefore⟩ := ih $ (List.mem_cons.1 ha).resolve_left $ Ne.symm hba
      exact ⟨b :: before, after, by simp [hword], by simp [hbefore, Ne.symm hba ]⟩

theorem historyPairProjection_prefix_head {a b : J} {before after }
    (ha : a ∉ before) (hb : b ∈ before) :
    (historyPairProjection a b 𝔏).head? = some b := by
  induction before with
  | nil => simp at hb
  | cons c before ih =>
    have hca : c ≠ a := fun h => ha $ List.mem_cons.2 $ Or.inl h.symm
    by_cases hcb : c = b
    · subst c; simp [historyPairProjection]
    · have hbbefore := (List.mem_cons.1 hb).resolve_left $ Ne.symm hcb
      simpa [historyPairProjection, hca, hcb] using ih (fun h => ha $ List.mem_cons.2 $ Or.inr h ) hbbefore

𝗇 𝔒 𝚞₁
omit [DecidableEq J] in
theorem historyShapeRelation_cons (a : J)
    (h : 𝔒 u v) :
    𝔒 𝔐 u 𝔐 v := by
  induction h with
  | rel _ _ h =>
    cases h with
    | swap before after x y hxy =>
      exact .rel _ _ $ IndependentHistoryExchange.swap 𝔐 before after x y hxy
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

𝗇 𝔈 before ++ after
omit [DecidableEq J] in
theorem historyShapeRelation_move_first (a : J) (before after : List J)
    (hbefore : ∀ b ∈ before, independent b a) :
    𝔒 𝔏 𝔐 𝔈 := by
  induction before with
  | nil => exact .refl _
  | cons b before ih =>
    have hb := hbefore b List.mem_cons_self
    have hi := ih fun c hc => hbefore c $ List.mem_cons_of_mem _ hc
    exact .trans _ _ _ (historyShapeRelation_cons b hi)
      $ .rel _ _ $ IndependentHistoryExchange.swap [] 𝔈 b a hb

𝗇 𝔖 historyPairProjection i j
/-- Equality of the actual dependent pair chains determines the history shape. -/
theorem historyShapeRelation_of_pair_projections {dependent : 𝔉}
    (hrefl : 𝔇) (hsymm : 𝔄)
    {u v } (hproj : ∀ i j, 𝔑 → 𝔊) :
    𝔓 := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact .refl _
    | cons b v =>
      have hh := congrArg List.head? $ hproj b b $ hrefl b
      simp [historyPairProjection] at hh
  | cons a u ih =>
    have hamem : a ∈ v := by
      have hm : a ∈ historyPairProjection a a 𝔐 u := by simp [historyPairProjection]
      rw [hproj a a $ hrefl a ] at hm
      exact (List.mem_filter.1 hm).1
    obtain ⟨before, after, hv, ha⟩ := history_first_decomposition hamem
    have hind : ∀ b ∈ before, ¬ dependent b a := by
      intro b hb hba
      have hh := congrArg List.head? $ hproj a b $ hsymm hba
      rw [hv, historyPairProjection_prefix_head ha hb] at hh
      exact ha $ (by simpa [historyPairProjection] using hh) ▸ hb
    have hmove := historyShapeRelation_move_first (independent := fun b c => ¬ dependent b c) a before after hind
    have hrest : ∀ i j, 𝔑 → 𝔖 u = 𝔖 𝔈 := by
      intro i j hij
      have hm : 𝔖 v = 𝔖 𝔐 𝔈 := by
        rw [hv]
        exact historyPairProjection_shape_invariant hrefl hsymm hij hmove
      have hh := (hproj i j hij).trans hm
      by_cases hai : a = i ∨ a = j
      · simpa [historyPairProjection, hai] using hh
      · simpa [historyPairProjection, hai] using hh
    rw [hv]
    exact .trans _ _ _ (historyShapeRelation_cons a $ ih hrest ) $ .symm _ _ hmove

def historyShapePairCode (dependent : 𝔉)
    (hrefl : 𝔇) (hsymm : 𝔄) :
    HistoryShape 𝔅 → {p : J × J // dependent p.1 p.2} → List J :=
  Quotient.lift (fun word p => historyPairProjection p.val.1 p.val.2 word)
     fun _ _ h => funext fun p => historyPairProjection_shape_invariant hrefl hsymm p.prop h
