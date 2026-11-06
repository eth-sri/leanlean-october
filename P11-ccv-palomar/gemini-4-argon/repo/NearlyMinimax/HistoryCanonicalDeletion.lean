module
public import NearlyMinimax.HistoryPriorDensity
@[expose] public section
noncomputable section
section
namespace NearlyMinimax
section
section
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyShapeRelation_append {independent : J → J → Prop} 
    (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) (suffix ) :
    Relation.EqvGen (IndependentHistoryExchange independent) (u ++ suffix) (v ++ suffix) := by
  induction h with
  | rel u v h =>
    cases h with
    | swap before after x y hxy =>
      simpa only [List.append_assoc, List.cons_append] using
        Relation.EqvGen.rel _ _ (IndependentHistoryExchange.swap before (after ++ suffix) x y hxy)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
def historyShapeAppend (dependent : J → J → Prop) (j : J) :
    HistoryShape (fun a b => ¬ dependent a b) → HistoryShape (fun a b => ¬ dependent a b) :=
  Quotient.lift (fun word => Quotient.mk _ (word ++ [j]))
    (fun _ _ h => Quotient.sound (historyShapeRelation_append h [j]))
@[simp] theorem historyShapeAppend_mk (dependent : J → J → Prop) (j : J) (word : List J) :
    historyShapeAppend dependent j (Quotient.mk _ word) = Quotient.mk _ (word ++ [j]) := rfl
end
variable {J : Type*} {n : ℕ}
def historyPositionStep (dependent : J → J → Prop) (labels : Fin n → J)
    (x y : Fin n) : Prop := x < y ∧ dependent (labels x) (labels y)
theorem historyAdjacent_swap_lt (labels : Fin n → J) (dependent : J → J → Prop)
    (i j x y : Fin n) (hij : i.val + 1 = j.val)
    (hind : ¬ dependent (labels i) (labels j))
    (hxy : historyPositionStep dependent labels x y) :
    Equiv.swap i j x < Equiv.swap i j y := by
  have hlt  := hxy.1
  by_cases hxi : x = i
  · subst x
    by_cases hyj : y = j
    · subst y; exact (hind hxy.2).elim
    · have hyi : y ≠ i := by intro he; subst y; simp at hlt
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyi hyj]
      have := Fin.val_ne_iff.2 hyj
      omega
  · by_cases hxj : x = j
    · subst x
      have hyi : y ≠ i := by intro he; subst y; omega
      have hyj : y ≠ j := by intro he; subst y; simp at hlt
      simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hyi hyj]
      omega
    · by_cases hyi : y = i
      · subst y
        simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxi hxj]
        omega
      · by_cases hyj : y = j
        · subst y
          simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hxi hxj]
          have := Fin.val_ne_iff.2 hxi
          omega
        · simpa only [Equiv.swap_apply_of_ne_of_ne hxi hxj,
            Equiv.swap_apply_of_ne_of_ne hyi hyj] using hxy.1
theorem wordHeap_le_iff_position_reachable (word : List J) (dependent )
    (x y : WordHeapPiece word dependent) :
    x ≤ y ↔ Relation.ReflTransGen (historyPositionStep dependent word.get) x.position y.position := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail hreach hstep ih => exact ih.tail hstep
  · intro h
    have hlift : ∀ {p q : Fin word.length},
        Relation.ReflTransGen (historyPositionStep dependent word.get) p q →
          Relation.ReflTransGen wordHeapStep (⟨p⟩ : WordHeapPiece word dependent) ⟨q⟩ := by
      intro p q hpq
      induction hpq with
      | refl => exact .refl
      | tail hreach hstep ih => exact ih.tail hstep
    cases x
    cases y
    exact hlift h
theorem historyEquiv_reachable_iff  (e : A ≃ B)
    (r s)
    (hstep : ∀ x y, r x y ↔ s (e x) (e y)) (x y ) :
    Relation.ReflTransGen r x y ↔ Relation.ReflTransGen s (e x) (e y) := by
  constructor
  · exact Relation.ReflTransGen.lift e (fun a b h => (hstep a b).1 h) x y
  · intro h
    have hlift := Relation.ReflTransGen.lift e.symm
      (r := s) (p := r) (fun a b h => by
        apply (hstep (e.symm a) (e.symm b)).2
        simpa only [e.apply_symm_apply] using h) (e x) (e y) h
    change Relation.ReflTransGen r (e.symm (e x)) (e.symm (e y)) at hlift
    simpa only [e.symm_apply_apply] using hlift
def wordHeapOrderIsoPosition (word word' : List J) (dependent )
    (e : Fin word.length ≃ Fin word'.length)
    (hstep : ∀ x y, historyPositionStep dependent word.get x y ↔
      historyPositionStep dependent word'.get (e x) (e y)) :
    WordHeapPiece word dependent ≃o WordHeapPiece word' dependent where
  toFun x := ⟨e x.position⟩
  invFun x := ⟨e.symm x.position⟩
  left_inv x := WordHeapPiece.ext (e.symm_apply_apply x.position)
  right_inv x := WordHeapPiece.ext (e.apply_symm_apply x.position)
  map_rel_iff' := by
    intro x y
    rw [wordHeap_le_iff_position_reachable, wordHeap_le_iff_position_reachable]
    exact (historyEquiv_reachable_iff e _ _ hstep x.position y.position).symm
def historyTuplePositionEquiv (labels : Fin n → J) : Fin (List.ofFn labels).length ≃ Fin n :=
  finCongr List.length_ofFn
theorem historyTuplePositionEquiv_get (labels : Fin n → J) (i : Fin (List.ofFn labels).length) :
    (List.ofFn labels).get i = labels (historyTuplePositionEquiv labels i) := List.get_ofFn labels i
def historyTupleSwapPositions (labels : Fin n → J) (i j : Fin n) :
    Fin (List.ofFn labels).length ≃ Fin (List.ofFn (labels ∘ Equiv.swap i j)).length :=
  (historyTuplePositionEquiv labels).trans
    ((Equiv.swap i j).trans (historyTuplePositionEquiv (labels ∘ Equiv.swap i j)).symm)
def historyTupleSwapHeapIso (labels : Fin n → J) (dependent : J → J → Prop)
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    (i j : Fin n) (hij : i.val + 1 = j.val) (hind : ¬ dependent (labels i) (labels j)) :
    WordHeapPiece (List.ofFn labels) dependent ≃o
      WordHeapPiece (List.ofFn (labels ∘ Equiv.swap i j)) dependent :=
  wordHeapOrderIsoPosition _ _ dependent (historyTupleSwapPositions labels i j) (by
    intro x y
    unfold historyPositionStep
    simp only [historyTuplePositionEquiv_get]
    have hx : (historyTuplePositionEquiv (labels ∘ Equiv.swap i j))
        (historyTupleSwapPositions labels i j x) = Equiv.swap i j (historyTuplePositionEquiv labels x) := by
      simp [historyTupleSwapPositions]
    have hy : (historyTuplePositionEquiv (labels ∘ Equiv.swap i j))
        (historyTupleSwapPositions labels i j y) = Equiv.swap i j (historyTuplePositionEquiv labels y) := by
      simp [historyTupleSwapPositions]
    rw [hx, hy]
    simp only [Function.comp_def, Equiv.swap_apply_self]
    constructor
    · intro h
      have hpos : historyPositionStep dependent labels (historyTuplePositionEquiv labels x)
          (historyTuplePositionEquiv labels y) := by
        refine ⟨?_, h.2⟩
        simpa [historyTuplePositionEquiv, finCongr] using h.1
      have he := historyAdjacent_swap_lt labels dependent i j _ _ hij hind hpos
      exact ⟨by simpa [historyTupleSwapPositions, historyTuplePositionEquiv, finCongr] using he, h.2⟩
    · intro h
      have hnew : historyPositionStep dependent (labels ∘ Equiv.swap i j)
          (Equiv.swap i j (historyTuplePositionEquiv labels x))
          (Equiv.swap i j (historyTuplePositionEquiv labels y)) := by
        refine ⟨?_, ?_⟩
        · simpa [historyTupleSwapPositions, historyTuplePositionEquiv, finCongr] using h.1
        · simpa only [Function.comp_def, Equiv.swap_apply_self] using h.2
      have hind' : ¬ dependent ((labels ∘ Equiv.swap i j) i) ((labels ∘ Equiv.swap i j) j) := by
        simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right]
        exact fun hd => hind (hsymm hd)
      have he := historyAdjacent_swap_lt (labels ∘ Equiv.swap i j) dependent i j _ _ hij hind' hnew
      exact ⟨by simpa [historyTuplePositionEquiv, finCongr] using he, h.2⟩)
end
section
variable {A B : Type*} [PartialOrder A] [PartialOrder B] [DecidableEq A] [DecidableEq B]
theorem historyMaximalPieces_orderIso_map (e : A ≃o B) (S : Finset A) :
    historyMaximalPieces (S.map e.toEquiv.toEmbedding) =
      (historyMaximalPieces S).map e.toEquiv.toEmbedding := by
  have hmem : ∀ (T : Finset A) (b : B), b ∈ T.map e.toEquiv.toEmbedding ↔ e.symm b ∈ T := by
    intro T b
    constructor
    · intro hb
      obtain ⟨a, ha, hab⟩ := Finset.mem_map.1 hb
      have hea : a = e.symm b := by apply e.injective; simpa using hab
      simpa only [← hea] using ha
    · intro hb
      exact Finset.mem_map.2 ⟨e.symm b, hb, e.apply_symm_apply b⟩
  ext b
  rw [mem_historyMaximalPieces, hmem, hmem, mem_historyMaximalPieces]
  constructor
  · rintro ⟨hb, hm⟩
    refine ⟨hb, ?_⟩
    intro a ha hba
    apply e.injective
    simpa only [e.apply_symm_apply] using
      hm (e a) (Finset.mem_map.2 ⟨a, ha, rfl⟩) (by simpa only [e.apply_symm_apply] using e.monotone hba)
  · rintro ⟨hb, hm⟩
    refine ⟨hb, ?_⟩
    intro c hc hbc
    simpa only [e.apply_symm_apply] using congrArg e (hm (e.symm c) ((hmem S c).1 hc) (e.symm.monotone hbc))
theorem historyUpperDensity_orderIso_map (e : A ≃o B) (weight )
    (S : Finset A) (t ) :
    historyUpperDensity weight (S.map e.toEquiv.toEmbedding) t =
      historyUpperDensity (weight ∘ e) S t := by
  rw [historyUpperDensity_eq_deletionPolynomial, historyUpperDensity_eq_deletionPolynomial]
  unfold historyDeletionPolynomial
  rw [Finset.card_map]
  apply Finset.sum_congr rfl
  intro k hk
  have h_historyDeletionCoefficient_orderIso_map k (S : Finset A) : historyDeletionCoefficient weight k (S.map e.toEquiv.toEmbedding) =
      historyDeletionCoefficient (weight ∘ e) k S := by
    induction k generalizing S with
    | zero => rfl
    | succ k ih =>
      rw [historyDeletionCoefficient_succ, historyDeletionCoefficient_succ,
        historyMaximalPieces_orderIso_map, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.map_erase, ih]
      rfl
  rw [h_historyDeletionCoefficient_orderIso_map]
end
section
variable {A : Type*} {n : ℕ}
theorem historyTuple_swap_take (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    (List.ofFn (f ∘ Equiv.swap i j)).take i.val = (List.ofFn f).take i.val := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.getElem_take, List.getElem_ofFn, Function.comp_def]
  have : k < i.val := by
    simp only [List.length_take, List.length_ofFn] at hk
    exact hk.trans_le (Nat.min_le_left _ _)
  rw [Equiv.swap_apply_of_ne_of_ne (by intro he; have : k = i.val := congrArg Fin.val he; omega) (by intro he; have : k = j.val := congrArg Fin.val he; omega)]
theorem historyTuple_swap_drop (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    (List.ofFn (f ∘ Equiv.swap i j)).drop (j.val + 1) = (List.ofFn f).drop (j.val + 1) := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  simp only [List.getElem_drop, List.getElem_ofFn, Function.comp_def]
  have : j.val + 1 + k < n := by simp only [List.length_drop, List.length_ofFn] at hk; omega
  rw [Equiv.swap_apply_of_ne_of_ne (by intro he; have : j.val + 1 + k = i.val := congrArg Fin.val he; omega) (by intro he; have : j.val + 1 + k = j.val := congrArg Fin.val he; omega)]
theorem historyTuple_adjacent_decomposition (f : Fin n → A) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    List.ofFn f = (List.ofFn f).take i.val ++ f i :: f j :: (List.ofFn f).drop (j.val + 1) := by
  calc
    _ = (List.ofFn f).take i.val ++ (List.ofFn f).drop i.val := (List.take_append_drop _ _).symm
    _ = _ := by
      rw [List.drop_eq_getElem_cons (by simp), hij, List.drop_eq_getElem_cons (by simp)]
      simp only [List.getElem_ofFn, Fin.eta]
end
variable {J : Type*}
theorem historyWord_swap_tuple (before after : List J) (a b : J) :
    let word := before ++ a :: b :: after
    let i : Fin word.length := ⟨before.length, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    let j : Fin word.length := ⟨before.length + 1, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    List.ofFn (word.get ∘ Equiv.swap i j) = before ++ b :: a :: after := by
  let word := before ++ a :: b :: after
  let i : Fin word.length := ⟨before.length, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
  let j : Fin word.length := ⟨before.length + 1, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
  have hi : word.get i = a := by
    rw [List.get_eq_getElem, List.getElem_append_right (by dsimp [i]; omega)]
    simp [i]
  have hj : word.get j = b := by
    rw [List.get_eq_getElem, List.getElem_append_right (by dsimp [j]; omega)]
    simp [j]
  have hc := historyTuple_adjacent_decomposition (word.get ∘ Equiv.swap i j) i j (by rfl)
  rw [historyTuple_swap_take word.get i j (by rfl),
    historyTuple_swap_drop word.get i j (by rfl)] at hc
  simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right, hi, hj,
    List.ofFn_get] at hc
  have ht : word.take i.val = before := by
    exact List.take_left
  have hd : word.drop (j.val + 1) = after := by
    rw [List.drop_append]
    have hb : before.drop (before.length + 1 + 1) = [] := by
      rw [List.drop_eq_nil_iff]
      omega
    rw [hb, List.nil_append, show before.length + 1 + 1 - before.length = 2 by omega]
    rfl
  rw [ht, hd] at hc
  exact hc
theorem historyTupleSwapHeapIso_label (dependent : J → J → Prop)
    (hsymm labels) (i j : Fin n) (hij hind)
    (x : WordHeapPiece (List.ofFn labels) dependent) :
    wordHeapLabel (historyTupleSwapHeapIso labels dependent hsymm i j hij hind x) = wordHeapLabel x := by
  simp [wordHeapLabel, historyTupleSwapHeapIso, wordHeapOrderIsoPosition,
    historyTupleSwapPositions, historyTuplePositionEquiv, finCongr,
    Function.comp_def]
  congr 1
theorem historyWord_exchange_heapIso (dependent : J → J → Prop)
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    {u v : List J} (h : IndependentHistoryExchange (fun a b => ¬ dependent a b) u v) :
    ∃ e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  cases h with
  | swap before after a b hind =>
    let word := before ++ a :: b :: after
    let i : Fin word.length := ⟨before.length, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    let j : Fin word.length := ⟨before.length + 1, by dsimp [word]; simp only [List.length_append, List.length_cons]; omega⟩
    have hi : word.get i = a := by
      rw [List.get_eq_getElem, List.getElem_append_right (by dsimp [i]; omega)]
      simp [i]
    have hj : word.get j = b := by
      rw [List.get_eq_getElem, List.getElem_append_right (by dsimp [j]; omega)]
      simp [j]
    have hind' : ¬ dependent (word.get i) (word.get j) := by simpa only [hi, hj] using hind
    have he : ∃ e : WordHeapPiece (List.ofFn word.get) dependent ≃o
        WordHeapPiece (List.ofFn (word.get ∘ Equiv.swap i j)) dependent,
        ∀ x, wordHeapLabel (e x) = wordHeapLabel x :=
      ⟨historyTupleSwapHeapIso word.get dependent hsymm i j (by rfl) hind',
        historyTupleSwapHeapIso_label dependent hsymm word.get i j (by rfl) hind'⟩
    rw [List.ofFn_get word, historyWord_swap_tuple before after a b] at he
    exact he
theorem historyShapeRelation_heapIso (dependent : J → J → Prop)
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    {u v : List J} (h : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v) :
    ∃ e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  induction h with
  | rel u v h => exact historyWord_exchange_heapIso dependent hsymm h
  | refl u => exact ⟨OrderIso.refl _, fun _ => rfl⟩
  | symm u v h ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e.symm, ?_⟩
    intro x
    simpa only [e.apply_symm_apply] using (he (e.symm x)).symm
  | trans u v w h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e₁, he₁⟩ := ih₁
    obtain ⟨e₂, he₂⟩ := ih₂
    exact ⟨e₁.trans e₂, fun x => (he₂ (e₁ x)).trans (he₁ x)⟩
end NearlyMinimax
end
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
section
section
section
theorem historyMap_withDensity {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (f : A → B) (hf : Measurable f) (p : B → ℝ≥0∞) (hp : Measurable p) :
    Measure.map f (μ.withDensity (p ∘ f)) = (Measure.map f μ).withDensity p := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hs.preimage hf), withDensity_apply _ hs,
    Measure.restrict_map hf hs, lintegral_map hp hf]
  rfl
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyMarkedPrior_eq_withDensity (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ) (ha : Measurable a) :
    historyMarkedPrior dependent Δ t π a =
      (historyMarkedReference dependent Δ π).withDensity
        (fun h => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a h)) := by
  unfold historyMarkedPrior historyMarkedReference
  have h_historyMarkedPriorRaw_eq_withDensity : historyMarkedPriorRaw dependent Δ t π a =
      (historyMarkedReferenceRaw dependent Δ π).withDensity
        (fun h => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a h)) := by
    let p : HistoryMarked dependent E → ℝ≥0∞ := fun h =>
      ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a h)
    have hp : Measurable p := (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal
    have hm : ∀ g, Measure.map (fun marks => (⟨g, marks⟩ : HistoryMarked dependent E))
        (historyMarkedFiberPrior dependent Δ t π a g) =
          (Measure.map (fun marks => (⟨g, marks⟩ : HistoryMarked dependent E))
            (Measure.pi (fun _ => π))).withDensity p := by
      intro g
      change Measure.map _ ((Measure.pi _).withDensity (p ∘ _)) = _
      exact historyMap_withDensity _ _ (historyMarked_measurable_mk dependent g) p hp
    change historyMarkedPriorRaw dependent Δ t π a = (historyMarkedReferenceRaw dependent Δ π).withDensity p
    unfold historyMarkedPriorRaw historyMarkedReferenceRaw
    rw [withDensity_sum]
    apply congrArg Measure.sum
    funext g
    rw [withDensity_smul_measure]
    exact congrArg (fun μ => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) • μ) (hm g)
  rw [withDensity_smul_measure, h_historyMarkedPriorRaw_eq_withDensity]
end
variable {J : Type*}
def wordHeapPiecePositionEquiv (word : List J) (dependent ) :
    WordHeapPiece word dependent ≃ Fin word.length where
  toFun := WordHeapPiece.position
  invFun i := ⟨i⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl
def historyHeapCoordinateEquiv {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) : Fin u.length ≃ Fin v.length :=
  (wordHeapPiecePositionEquiv u dependent).symm.trans
    (e.toEquiv.trans (wordHeapPiecePositionEquiv v dependent))
@[simp] theorem historyHeapCoordinateEquiv_position {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) (x : WordHeapPiece u dependent) :
    historyHeapCoordinateEquiv e x.position = (e x).position := by
  cases x
  rfl
def historyHeapMarkEquiv {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent)  [MeasurableSpace E] :
    (Fin u.length → E) ≃ᵐ (Fin v.length → E) :=
  MeasurableEquiv.piCongrLeft (fun _ => E) (historyHeapCoordinateEquiv e)
@[simp] theorem historyHeapMarkEquiv_position {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E]
    (marks : Fin u.length → E) (x : WordHeapPiece u dependent) :
    historyHeapMarkEquiv e marks (e x).position = marks x.position := by
  have hh := MeasurableEquiv.piCongrLeft_apply_apply (historyHeapCoordinateEquiv e)
    (β := fun _ => E) marks x.position
  simpa only [historyHeapMarkEquiv, historyHeapCoordinateEquiv_position] using hh
end
section
variable {J : Type*}
theorem historyShapeRelation_prefix {independent : J → J → Prop} (preword )
     (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) :
    Relation.EqvGen (IndependentHistoryExchange independent) (preword ++ u) (preword ++ v) := by
  induction preword with
  | nil => exact h
  | cons a preword ih => exact historyShapeRelation_cons a ih
theorem historyShapeRelation_move_last {independent : J → J → Prop} (a after)
    (hafter : ∀ b ∈ after, independent a b) :
    Relation.EqvGen (IndependentHistoryExchange independent) (a :: after) (after ++ [a]) := by
  induction after with
  | nil => exact .refl _
  | cons b after ih =>
    exact .trans _ _ _ (.rel _ _ (IndependentHistoryExchange.swap [] after a b (hafter b List.mem_cons_self)))
      (historyShapeRelation_cons b (ih (fun c hc => hafter c (List.mem_cons_of_mem _ hc))))
def historyWordDeletePiece (word : List J) (dependent )
    (x : WordHeapPiece word dependent) : List J :=
  word.take x.position.val ++ word.drop (x.position.val + 1)
theorem wordHeap_maximal_suffix_independent (word : List J) (dependent )
    (x : WordHeapPiece word dependent) (hx : x ∈ historyMaximalPieces Finset.univ) :
    ∀ b ∈ word.drop (x.position.val + 1), ¬ dependent (wordHeapLabel x) b := by
  intro b hb hdep
  obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.1 hb
  have hybound : x.position.val + 1 + k < word.length := by
    simp only [List.length_drop] at hk
    omega
  let y : WordHeapPiece word dependent := ⟨⟨x.position.val + 1 + k, hybound⟩⟩
  have hylabel : wordHeapLabel y = b := by
    change word.get ⟨x.position.val + 1 + k, hybound⟩ = b
    rw [List.get_eq_getElem]
    simpa only [List.getElem_drop] using hkb
  have hxy : x ≤ y := wordHeapStep_le ⟨by dsimp [y]; change x.position.val < x.position.val + 1 + k; omega,
    by simpa only [hylabel] using hdep⟩
  have : x.position.val + 1 + k = x.position.val := congrArg (fun z => z.position.val) ((mem_historyMaximalPieces.1 hx).2 y (Finset.mem_univ y) hxy)
  omega
theorem wordHeap_maximal_delete_shape (word : List J) (dependent )
    (x : WordHeapPiece word dependent) (hx : x ∈ historyMaximalPieces Finset.univ) :
    Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b))
      word (historyWordDeletePiece word dependent x ++ [wordHeapLabel x]) := by
  have hmove := historyShapeRelation_move_last (independent := fun a b => ¬ dependent a b) (wordHeapLabel x)
    (word.drop (x.position.val + 1)) (wordHeap_maximal_suffix_independent word dependent x hx)
  have hword : word = word.take x.position.val ++ wordHeapLabel x :: word.drop (x.position.val + 1) := by
    change word = word.take x.position.val ++ word.get x.position :: word.drop (x.position.val + 1)
    rw [List.cons_get_drop_succ]
    exact (List.take_append_drop _ _).symm
  conv_lhs => rw [hword]
  simpa only [historyWordDeletePiece, List.append_assoc] using (historyShapeRelation_prefix (word.take x.position.val) hmove)
variable [Fintype J] [LinearOrder J]
def wordHeapAppendedPiece (word : List J) (dependent j) :
    WordHeapPiece (word ++ [j]) dependent := ⟨⟨word.length, by simp⟩⟩
@[simp] theorem wordHeapAppendedPiece_label (word : List J) (dependent : J → J → Prop) (j : J) :
    wordHeapLabel (wordHeapAppendedPiece word dependent j) = j := by
  unfold wordHeapLabel wordHeapAppendedPiece
  rw [List.get_eq_getElem, List.getElem_append_right (by rfl)]
  simp
theorem wordHeapAppendedPiece_maximal (word : List J) (dependent j) :
    wordHeapAppendedPiece word dependent j ∈ historyMaximalPieces Finset.univ := by
  apply mem_historyMaximalPieces.2
  refine ⟨Finset.mem_univ _, ?_⟩
  intro y hy hxy
  have hlo := wordHeap_reachable_position_le hxy
  have hhi := y.position.isLt
  simp only [List.length_append, List.length_singleton] at hhi
  apply WordHeapPiece.ext
  apply Fin.ext
  change word.length ≤ y.position.val at hlo
  change y.position.val = word.length
  omega
theorem historyShape_terminal_iff_maximal (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    g ∈ Set.range (historyShapeAppend dependent j) ↔
      ∃ x : WordHeapPiece g.out dependent,
        x ∈ historyMaximalPieces Finset.univ ∧ wordHeapLabel x = j := by
  constructor
  · rintro ⟨u, hu⟩
    have hmk : (Quotient.mk _ (u.out ++ [j]) : HistoryShape (fun a b => ¬ dependent a b)) = g := by
      calc
        _ = historyShapeAppend dependent j (Quotient.mk _ u.out) := rfl
        _ = historyShapeAppend dependent j u := congrArg _ (Quotient.out_eq u)
        _ = g := hu
    have hr  := Quotient.exact (hmk.trans (Quotient.out_eq g).symm)
    obtain ⟨e, he⟩ := historyShapeRelation_heapIso dependent hsymm hr
    let x := wordHeapAppendedPiece u.out dependent j
    have hx := wordHeapAppendedPiece_maximal u.out dependent j
    have hxmap : e x ∈ historyMaximalPieces ((Finset.univ : Finset (WordHeapPiece (u.out ++ [j]) dependent)).map e.toEquiv.toEmbedding) := by
      rw [historyMaximalPieces_orderIso_map]
      exact Finset.mem_map.2 ⟨x, hx, rfl⟩
    rw [Finset.map_univ_equiv e.toEquiv] at hxmap
    exact ⟨e x, hxmap, (he x).trans (wordHeapAppendedPiece_label u.out dependent j)⟩
  · rintro ⟨x, hx, hlabel⟩
    have h_wordHeap_maximal_delete_append : historyShapeAppend dependent (wordHeapLabel x) (Quotient.mk _ (historyWordDeletePiece g.out dependent x)) =
      (Quotient.mk _ g.out : HistoryShape (fun a b => ¬ dependent a b)) := by
      rw [historyShapeAppend_mk]
      exact (Quotient.sound (wordHeap_maximal_delete_shape g.out dependent x hx)).symm
    have hd := h_wordHeap_maximal_delete_append
    rw [hlabel] at hd
    exact ⟨Quotient.mk _ (historyWordDeletePiece g.out dependent x), hd.trans (Quotient.out_eq g)⟩
end
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem historyCanonicalAppendHeapIso_exists (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    ∃ e : WordHeapPiece (g.out ++ [j]) dependent ≃o
        WordHeapPiece (historyShapeAppend dependent j g).out dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  exact historyShapeRelation_heapIso dependent hsymm (Quotient.exact ((congrArg (historyShapeAppend dependent j) (Quotient.out_eq g)).trans (Quotient.out_eq _).symm))
def historyCanonicalAppendHeapIso (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    WordHeapPiece (g.out ++ [j]) dependent ≃o
      WordHeapPiece (historyShapeAppend dependent j g).out dependent :=
  (historyCanonicalAppendHeapIso_exists dependent hsymm j g).choose
theorem historyCanonicalAppendHeapIso_label (dependent )
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) (x : WordHeapPiece (g.out ++ [j]) dependent) :
    wordHeapLabel (historyCanonicalAppendHeapIso dependent hsymm j g x) = wordHeapLabel x :=
  (historyCanonicalAppendHeapIso_exists dependent hsymm j g).choose_spec x
def historyFiniteMarkAppendEquiv (n )  [MeasurableSpace E] :
    E × (Fin n → E) ≃ᵐ (Fin (n + 1) → E) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => E) (Fin.last n)).symm
theorem historyFiniteMarkAppendEquiv_preserving (n )  [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] :
    MeasurePreserving (historyFiniteMarkAppendEquiv n (E := E))
      (π.prod (Measure.pi (fun _ => π))) (Measure.pi (fun _ => π)) :=
  (measurePreserving_piFinSuccAbove (fun _ => π) (Fin.last n)).symm _
def historyCanonicalAppendCoordinates (dependent )
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Fin (historyShapeLength dependent g + 1) ≃ Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) :=
  (finCongr (by rw [historyShapeLength_out]; simp)).trans
    ((historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)).trans
      (finCongr (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm))
def historyCanonicalMarkAppendEquiv (dependent )
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E] :
    E × (Fin (historyShapeLength dependent g) → E) ≃ᵐ
      (Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) → E) :=
  (historyFiniteMarkAppendEquiv (historyShapeLength dependent g)).trans
    (MeasurableEquiv.piCongrLeft (fun _ => E) (historyCanonicalAppendCoordinates dependent hsymm j g))
def historyCanonicalAppendedPiece (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    WordHeapPiece (historyShapeAppend dependent j g).out dependent :=
  historyCanonicalAppendHeapIso dependent hsymm j g (wordHeapAppendedPiece g.out dependent j)
theorem historyCanonicalAppendedPiece_maximal (dependent )
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyCanonicalAppendedPiece dependent hsymm j g ∈ historyMaximalPieces Finset.univ := by
  let e := historyCanonicalAppendHeapIso dependent hsymm j g
  have hx : e (wordHeapAppendedPiece g.out dependent j) ∈ historyMaximalPieces
      ((Finset.univ : Finset (WordHeapPiece (g.out ++ [j]) dependent)).map e.toEquiv.toEmbedding) := by
    rw [historyMaximalPieces_orderIso_map]
    exact Finset.mem_map.2 ⟨_, wordHeapAppendedPiece_maximal g.out dependent j, rfl⟩
  rw [Finset.map_univ_equiv e.toEquiv] at hx
  exact hx
@[simp] theorem historyCanonicalAppendedPiece_label (dependent )
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    wordHeapLabel (historyCanonicalAppendedPiece dependent hsymm j g) = j :=
  (historyCanonicalAppendHeapIso_label dependent hsymm j g _).trans
    (wordHeapAppendedPiece_label g.out dependent j)
def historyCanonicalFreshCoordinate (dependent )
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Fin (historyShapeLength dependent (historyShapeAppend dependent j g)) :=
  Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
    (historyCanonicalAppendedPiece dependent hsymm j g).position
@[simp] theorem historyFiniteMarkAppendEquiv_last (n )  [MeasurableSpace E]
    (fresh : E) (marks : Fin n → E) :
    historyFiniteMarkAppendEquiv n (fresh, marks) (Fin.last n) = fresh := by
  have hh := congrArg Prod.fst
    ((MeasurableEquiv.piFinSuccAbove (fun _ => E) (Fin.last n)).apply_symm_apply (fresh, marks))
  exact hh
end
section
section
variable {A B : Type*} [PartialOrder A] [PartialOrder B] [DecidableEq A] [DecidableEq B]
theorem historyScaledUpperDensity_orderEmbedding_map (f : A ↪o B) (weight ρ) (S : Finset A) (t ) :
    historyScaledUpperDensity weight ρ (S.map f.toEmbedding) t =
      historyScaledUpperDensity (weight ∘ f) ρ S t := by
  have h_historyUpperDensity_orderEmbedding_map (weight) : historyUpperDensity weight (S.map f.toEmbedding) t = historyUpperDensity (weight ∘ f) S t := by
    rw [historyUpperDensity_eq_deletionPolynomial, historyUpperDensity_eq_deletionPolynomial]
    unfold historyDeletionPolynomial
    rw [Finset.card_map]
    apply Finset.sum_congr rfl
    intro k hk
    have h_historyDeletionCoefficient_orderEmbedding_map k (S : Finset A) : historyDeletionCoefficient weight k (S.map f.toEmbedding) =
        historyDeletionCoefficient (weight ∘ f) k S := by
      induction k generalizing S with
      | zero => rfl
      | succ k ih =>
        have h_historyMaximalPieces_orderEmbedding_map : historyMaximalPieces (S.map f.toEmbedding) = (historyMaximalPieces S).map f.toEmbedding := by
          ext b
          constructor
          · intro hb
            obtain ⟨hb, hm⟩ := mem_historyMaximalPieces.1 hb
            obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hb
            refine Finset.mem_map.2 ⟨x, mem_historyMaximalPieces.2 ⟨hx, ?_⟩, rfl⟩
            intro y hy hxy
            exact f.injective (hm (f y) (Finset.mem_map.2 ⟨y, hy, rfl⟩) (f.monotone hxy))
          · intro hb
            obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hb
            obtain ⟨hx, hm⟩ := mem_historyMaximalPieces.1 hx
            refine mem_historyMaximalPieces.2 ⟨Finset.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
            intro c hc hxc
            obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hc
            exact congrArg f (hm y hy (f.le_iff_le.1 hxc))
        rw [historyDeletionCoefficient_succ, historyDeletionCoefficient_succ,
          h_historyMaximalPieces_orderEmbedding_map, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.map_erase, ih]
        rfl
    rw [h_historyDeletionCoefficient_orderEmbedding_map]
  exact h_historyUpperDensity_orderEmbedding_map _
end
variable {J : Type*}
def historyPrefixPosition (word : List J) (j ) : Fin word.length ↪ Fin (word ++ [j]).length where
  toFun x := ⟨x.val, by have := x.isLt; simp only [List.length_append, List.length_singleton]; omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    exact congrArg (fun z => z.val) h
theorem historyPrefixPosition_get (word : List J) (j ) (x : Fin word.length) :
    (word ++ [j]).get (historyPrefixPosition word j x) = word.get x := by
  change (word ++ [j]).get ⟨x.val, _⟩ = word.get x
  rw [List.get_eq_getElem, List.getElem_append_left x.isLt, List.get_eq_getElem]
theorem historyPrefixPosition_step (word : List J) (dependent j)
    {x y : Fin word.length} (hxy : historyPositionStep dependent word.get x y) :
    historyPositionStep dependent (word ++ [j]).get
      (historyPrefixPosition word j x) (historyPrefixPosition word j y) := by
  refine ⟨hxy.1, ?_⟩
  simpa only [historyPrefixPosition_get] using hxy.2
theorem historyPrefixPosition_reachable_reflect (word : List J) (dependent j)
    {p q : Fin (word ++ [j]).length} (hp hq)
    (h : Relation.ReflTransGen (historyPositionStep dependent (word ++ [j]).get) p q) :
    Relation.ReflTransGen (historyPositionStep dependent word.get) ⟨p.val, hp⟩ ⟨q.val, hq⟩ := by
  have h_historyPrefixPosition_get_of_lt (x : Fin (word ++ [j]).length) (hx) : (word ++ [j]).get x = word.get ⟨x.val, hx⟩ := by
    rw [List.get_eq_getElem, List.getElem_append_left hx, List.get_eq_getElem]
  induction h with
  | refl => exact .refl
  | @tail r q hreach hstep ih =>
    have hlt : r.val < q.val := hstep.1
    have hr : r.val < word.length := hlt.trans hq
    apply (ih hr).tail
    refine ⟨hstep.1, ?_⟩
    simpa only [h_historyPrefixPosition_get_of_lt r hr, h_historyPrefixPosition_get_of_lt q hq] using hstep.2
theorem historyPrefixPosition_reachable_iff (word : List J) (dependent ) (j : J)
    (x y : Fin word.length) :
    Relation.ReflTransGen (historyPositionStep dependent word.get) x y ↔
      Relation.ReflTransGen (historyPositionStep dependent (word ++ [j]).get)
        (historyPrefixPosition word j x) (historyPrefixPosition word j y) := by
  constructor
  · exact Relation.ReflTransGen.lift (historyPrefixPosition word j)
      (fun a b h => historyPrefixPosition_step word dependent j h) x y
  · intro h
    have hh := historyPrefixPosition_reachable_reflect word dependent j x.isLt y.isLt h
    cases x
    cases y
    exact hh
def historyPrefixHeapEmbedding (word : List J) (dependent : J → J → Prop) (j : J) :
    WordHeapPiece word dependent ↪o WordHeapPiece (word ++ [j]) dependent where
  toFun x := ⟨historyPrefixPosition word j x.position⟩
  inj' := by intro x y h; apply WordHeapPiece.ext; exact (historyPrefixPosition word j).injective (congrArg WordHeapPiece.position h)
  map_rel_iff' := by
    intro x y
    rw [wordHeap_le_iff_position_reachable, wordHeap_le_iff_position_reachable]
    exact (historyPrefixPosition_reachable_iff word dependent j x.position y.position).symm
theorem historyPrefixHeap_density_delete (word : List J) (dependent j weight) (ρ t : ℝ) :
    historyScaledUpperDensity weight ρ (Finset.univ.erase (wordHeapAppendedPiece word dependent j)) t =
      historyScaledUpperDensity (weight ∘ historyPrefixHeapEmbedding word dependent j) ρ Finset.univ t := by
  have h_historyPrefixHeapEmbedding_univ : (Finset.univ : Finset (WordHeapPiece word dependent)).map (historyPrefixHeapEmbedding word dependent j).toEmbedding =
      (Finset.univ : Finset (WordHeapPiece (word ++ [j]) dependent)).erase (wordHeapAppendedPiece word dependent j) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
      apply Finset.mem_erase.2
      refine ⟨?_, Finset.mem_univ _⟩
      intro he
      have hv := congrArg (fun z => z.position.val) he
      have hlt := x.position.isLt
      change x.position.val = word.length at hv
      omega
    · intro hy
      have hne := (Finset.mem_erase.1 hy).1
      have hbound : y.position.val < word.length := by
        have hlt := y.position.isLt
        simp only [List.length_append, List.length_singleton] at hlt
        have : y.position.val ≠ word.length := by
          intro hv
          apply hne
          apply WordHeapPiece.ext
          apply Fin.ext
          exact hv
        omega
      let x : WordHeapPiece word dependent := ⟨⟨y.position.val, hbound⟩⟩
      refine Finset.mem_map.2 ⟨x, Finset.mem_univ _, ?_⟩
      apply WordHeapPiece.ext
      apply Fin.ext
      rfl
  rw [← h_historyPrefixHeapEmbedding_univ]
  exact historyScaledUpperDensity_orderEmbedding_map _ _ ρ _ t
end
section
theorem historySigma_measurable_iff {I : Type*} {X : I → Type*} {Y : Type*}
    [∀ i, MeasurableSpace (X i)] [MeasurableSpace Y] (f : Sigma X → Y) :
    Measurable f ↔ ∀ i, Measurable (fun x => f ⟨i, x⟩) := by
  constructor
  · intro hf i
    exact hf.comp (Measurable.of_le_map (iInf_le _ i))
  · intro hf s hs
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun i => hf i hs
def historySigmaProdMeasurableEquiv {I : Type*} [Countable I] (X : I → Type*) (Y : Type*)
    [∀ i, MeasurableSpace (X i)] [∀ i, StandardBorelSpace (X i)]
    [MeasurableSpace Y] [StandardBorelSpace Y] : (Sigma X) × Y ≃ᵐ Sigma (fun i => X i × Y) := by
  let := fun i => upgradeStandardBorel (X i)
  let := upgradeStandardBorel Y
  let : BorelSpace (Sigma X) := historySigma_borelSpace
  let : BorelSpace (Sigma (fun i => X i × Y)) := historySigma_borelSpace
  exact (Homeomorph.sigmaProdDistrib (X := X) (Y := Y)).toMeasurableEquiv
variable {J : Type*} [Fintype J] [LinearOrder J]
def historyMarkedAppend (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) {E : Type*} [MeasurableSpace E] (h : HistoryMarked dependent E × E) :
    HistoryMarked dependent E :=
  ⟨historyShapeAppend dependent j h.1.1,
    historyCanonicalMarkAppendEquiv dependent hsymm j h.1.1 (h.2, h.1.2)⟩
theorem historyMarkedAppend_measurable (dependent )
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] :
    Measurable (historyMarkedAppend dependent hsymm j (E := E)) := by
  let X := fun g : HistoryShape (fun a b => ¬ dependent a b) => Fin (historyShapeLength dependent g) → E
  let e := historySigmaProdMeasurableEquiv X E
  let f : Sigma (fun g => X g × E) → HistoryMarked dependent E := fun h =>
    ⟨historyShapeAppend dependent j h.1,
      historyCanonicalMarkAppendEquiv dependent hsymm j h.1 (h.2.2, h.2.1)⟩
  have hf : Measurable f := by
    rw [historySigma_measurable_iff]
    intro g
    exact (historyMarked_measurable_mk dependent (historyShapeAppend dependent j g)).comp
      ((historyCanonicalMarkAppendEquiv dependent hsymm j g).measurable.comp
        MeasurableEquiv.prodComm.measurable)
  exact hf.comp e.measurable
end
variable {J : Type*} [Fintype J] [LinearOrder J]
@[simp] theorem historyFiniteMarkAppendEquiv_old (n )  [MeasurableSpace E]
    (fresh : E) (marks : Fin n → E) (x : Fin n) :
    historyFiniteMarkAppendEquiv n (fresh, marks) x.castSucc = marks x := by
  have hh := congrArg (fun p : E × (Fin n → E) => p.2 x)
    ((MeasurableEquiv.piFinSuccAbove (fun _ => E) (Fin.last n)).apply_symm_apply (fresh, marks))
  change historyFiniteMarkAppendEquiv n (fresh, marks) ((Fin.last n).succAbove x) = marks x at hh
  simpa only [Fin.succAbove_last_apply] using hh
theorem historyCanonicalAppend_density_delete (dependent hsymm)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*} [MeasurableSpace E]
    (fresh : E) (marks : Fin (historyShapeLength dependent g) → E)
    (a : E → ℝ) (ρ t : ℝ) :
    historyScaledUpperDensity
      (historyMarkedPieceWeight dependent a
        ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩)
      ρ (Finset.univ.erase (historyCanonicalAppendedPiece dependent hsymm j g)) t =
      historyMarkedDensity dependent ρ t a ⟨g, marks⟩ := by
  classical
  let e := historyCanonicalAppendHeapIso dependent hsymm j g
  let w := historyMarkedPieceWeight dependent a
    ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩
  have h_historyScaledUpperDensity_orderIso_map : historyScaledUpperDensity w ρ ((Finset.univ.erase (wordHeapAppendedPiece g.out dependent j)).map e.toEquiv.toEmbedding) t =
      historyScaledUpperDensity (w ∘ e) ρ (Finset.univ.erase (wordHeapAppendedPiece g.out dependent j)) t := by
    exact historyUpperDensity_orderIso_map e _ (Finset.univ.erase (wordHeapAppendedPiece g.out dependent j)) t
  have ht := h_historyScaledUpperDensity_orderIso_map
  rw [Finset.map_erase, Finset.map_univ_equiv] at ht
  have hw : (w ∘ e) ∘ historyPrefixHeapEmbedding g.out dependent j =
      historyMarkedPieceWeight dependent a ⟨g, marks⟩ := by
    funext x
    have h_historyCanonicalMarkAppendEquiv_old : historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)
      (Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyCanonicalAppendHeapIso dependent hsymm j g
          (historyPrefixHeapEmbedding g.out dependent j x)).position) =
      marks (Fin.cast (historyShapeLength_out dependent g).symm x.position) := by
      have h_historyCanonicalAppendCoordinates_old : historyCanonicalAppendCoordinates dependent hsymm j g
          (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc =
          Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
            (historyCanonicalAppendHeapIso dependent hsymm j g
              (historyPrefixHeapEmbedding g.out dependent j x)).position := by
        let hlen : historyShapeLength dependent g + 1 = (g.out ++ [j]).length := by
          rw [historyShapeLength_out]; simp
        have hp : (finCongr hlen)
            (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc =
              (historyPrefixHeapEmbedding g.out dependent j x).position := by
          apply Fin.ext
          rfl
        unfold historyCanonicalAppendCoordinates
        change Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
          (historyHeapCoordinateEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)
            ((finCongr hlen) (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc)) = _
        rw [hp, historyHeapCoordinateEquiv_position]
      rw [← h_historyCanonicalAppendCoordinates_old]
      have hh := MeasurableEquiv.piCongrLeft_apply_apply
        (historyCanonicalAppendCoordinates dependent hsymm j g)
        (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks))
        (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc
      change MeasurableEquiv.piCongrLeft
        (fun _ => E)
        (historyCanonicalAppendCoordinates dependent hsymm j g)
        (historyFiniteMarkAppendEquiv _ (fresh, marks))
        (historyCanonicalAppendCoordinates dependent hsymm j g
          (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc) = _
      rw [hh, historyFiniteMarkAppendEquiv_old]
    exact congrArg a h_historyCanonicalMarkAppendEquiv_old
  rw [historyPrefixHeap_density_delete, hw] at ht
  exact ht
end NearlyMinimax
