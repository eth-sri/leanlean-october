module

public import RequestProject.PosetCoverLowerInterval
public import RequestProject.PosetCoverTargetIso

@[expose] public section

/-! A punctured lower link stays in the sheet of its specified lifted top cell. -/

namespace FiniteChains.Comb.IsPosetCover
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] {f : P → Q}
  (hf : IsPosetCover f)

variable (v : P) (a : Q)

noncomputable def puncturedLowerOrderIso :
    {p : P // p < v ∧ f p ≠ a} ≃o {q : Q // q < f v ∧ q ≠ a} where
  toFun p := ⟨f p.1, hf.strictMono p.2.1, p.2.2⟩
  invFun q := ⟨(hf.lowerIntervalLift v _).1,
    (hf.lowerIntervalLift v ⟨q.1, q.2.1⟩).2, by
      grind [hf.lowerIntervalLift_projection]⟩
  left_inv p := Subtype.ext (hf.down_inj
    (hf.lowerIntervalLift v ⟨f p.1, hf.strictMono p.2.1⟩).2.le p.2.1.le
    (hf.lowerIntervalLift_projection v _))
  right_inv q := Subtype.ext (hf.lowerIntervalLift_projection v _)
  map_rel_iff' {a b} :=
    ⟨fun h => hf.le_of_le_below a.2.1.le b.2.1.le h, fun h => hf.mono h⟩

/-- Unlike the full inverse image, this interval cover is one fixed sheet. -/
theorem puncturedLower_isPosetCover :
    IsPosetCover (fun p : {p : P // p < v ∧ f p ≠ a} =>
      (⟨f p.1, hf.strictMono p.2.1, p.2.2⟩ : {q : Q // q < f v ∧ q ≠ a})) := by
  let hi : IsPosetCover (id : {p : P // p < v ∧ f p ≠ a} → _) :=
    ⟨monotone_id, Function.surjective_id,
      fun x y h => ⟨y, ⟨h, rfl⟩, fun z hz => hz.2⟩,
      fun x y h => ⟨y, ⟨h, rfl⟩, fun z hz => hz.2⟩⟩
  exact hi.postcompose_orderIso (hf.puncturedLowerOrderIso v a)

end FiniteChains.Comb.IsPosetCover
