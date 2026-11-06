module

public import NearlyMinimax.HistoryReferenceMeasure
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-!
# Actual shape append and its reference-weight change

Appending a fixed label descends through independent exchanges, is injective
by the proved dependent-pair characterization, increases length by exactly one,
and multiplies the exact source reference weight by `rho`.
-/


𝚲

𝗃 𝔊 ἀ ++ suffix
omit [Fintype J] [LinearOrder J] in
/-- Independent-exchange equivalence is preserved by an arbitrary suffix. -/
theorem historyShapeRelation_append
    (h : 𝚞₁ u v) (suffix : List J) :
    𝚞₁ 𝔊 u 𝔊 v := by
  induction h with
  | rel u v h =>
    cases h with
    | swap before after x y hxy =>
      simpa only [List.append_assoc, List.cons_append] using
        Relation.EqvGen.rel _ _ $ IndependentHistoryExchange.swap before 𝔊 after x y hxy
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

𝗇 𝔄 𝖴
𝗇 𝔉 [j]
𝗃 𝔍 ἀ ++ 𝔉
𝗇 𝔅 Quotient.mk _ 𝔍 word
𝗇 𝔇 𝙁
/-- Appending an actual local-update label is well-defined on the history shape. -/
def historyShapeAppend (dependent : 𝔇) (j : J) :
    HistoryShape 𝔄 → HistoryShape 𝔄 :=
  Quotient.lift (fun word => 𝔅)
     fun _ _ h => Quotient.sound $ historyShapeRelation_append h 𝔉

𝗇 𝔈 𝗡₁
omit [Fintype J] [LinearOrder J] in
@[simp] theorem historyShapeAppend_mk (dependent : 𝔇) (j : J) (word : List J) :
    𝔈 (Quotient.mk _ word) = 𝔅 := rfl

omit [Fintype J] in
/-- The append map cannot merge histories: dependent pair words right-cancel. -/
theorem historyShapeAppend_injective (dependent : 𝔇)
    (hrefl : 𝙂) (hsymm : 𝘼) (j : J) :
    Function.Injective 𝔈 := by
  intro g h heq
  induction g using Quotient.inductionOn
  rename_i u
  induction h using Quotient.inductionOn
  rename_i v
  apply Quotient.sound
  apply historyShapeRelation_of_pair_projections hrefl hsymm
  intro i k hik
  have hc := congrArg (fun shape => historyShapePairCode dependent hrefl hsymm shape ⟨(i, k), hik⟩) heq
  change historyPairProjection i k 𝔍 u = historyPairProjection i k 𝔍 v at hc
  unfold historyPairProjection at hc ⊢
  rw [List.filter_append, List.filter_append] at hc
  exact List.append_cancel_right hc

@[simp] theorem historyShapeLength_append dependent (j : J)
    g :
    historyShapeLength dependent (𝔈 g) = 𝗠₁ + 1 := by
  induction g using Quotient.inductionOn
  rename_i word
  rw [historyShapeAppend_mk, historyShapeLength_mk, historyShapeLength_mk]
  simp

/-- The exact source reference factor needed for append/delete change of variables. -/
theorem historyShapeReferenceWeight_append dependent Δ (j : J)
    g :
    historyShapeReferenceWeight dependent Δ (𝔈 g) =
      historyReferenceRho Δ * 𝘎₁ := by
  unfold historyShapeReferenceWeight
  rw [historyShapeLength_append, pow_succ, mul_comm]
