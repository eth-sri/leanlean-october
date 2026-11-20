module

public import RequestProject.OrderComplexFreeFace
public import RequestProject.OrderCxNatHtpy

@[expose] public section

/-! Constructed loop representatives under the first elementary collapse deletion. -/
namespace FiniteChains.Comb
variable {P : Type} [PartialOrder P]

/-- Every loop based in `B` has a representative in `B` under an increasing order map
from `C` to `B`. The connecting germs at its base are included explicitly. -/
theorem loop_representative_of_monotone_map {C B : P → Prop}
    (hBC : ∀ x, B x → C x) (r : {x : P // C x} → P) (hr : Monotone r)
    (hrB : ∀ x, B (r x)) (hle : ∀ x, x.1 ≤ r x)
    {a : P} {p : List _} (ha : B a)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) (hC : PathIn C p) :
    ∃ l, IsPath (orderCx P).src (orderCx P).tgt l a a ∧ PathIn B l ∧
      Htpy _ a a p l := by
  let aC : {x : P // C x} := ⟨a, hBC a ha⟩
  let l := mapPath (orderCxMap r hr) (liftPathIn p hC)
  have hlB : PathIn B l := by
    intro e he
    obtain ⟨eb, _, rfl⟩ := List.mem_map.mp he
    solve_by_elim
  let e := [ordPos (hle aC)]
  let en := [ordNeg (hle aC)]
  have hen : IsPath _ _ en _ a := isPath_ordNeg _
  have hnat := htpy_mapPath_le monotone_subtypeVal hr hle
    _ (isPath_liftPathIn p hC aC.2 aC.2 hp)
  change Htpy _ a _
    (mapPath (subposetHom C) (liftPathIn p hC) ++ e) (e ++ l) at hnat
  rw [mapPath_liftPathIn] at hnat
  have hpush := hnat.congr_append (show IsPath (orderCx P).src (orderCx P).tgt [] a a from rfl) hen
  have hkill := (htpy_ordPos_ordNeg (hle aC)).congr_append hp
    (show IsPath (orderCx P).src (orderCx P).tgt [] a a from rfl)
  refine ⟨e ++ l ++ en, ((isPath_ordPos _).append (isPath_mapPath _ (isPath_liftPathIn p hC aC.2 aC.2 hp))).append hen,
    pathIn_append (pathIn_append (pathIn_cons ⟨ha, hrB aC⟩ (pathIn_nil B)) hlB) (pathIn_cons ⟨ha, hrB aC⟩ (pathIn_nil B)), ?_⟩
  have hstrip : Htpy _ a a p ((p ++ e) ++ en) := by
    simpa [e, en, List.append_assoc] using hkill.symm
  apply hstrip.trans <;> assumption

/-- The inclusion reflects relative null homotopies, and represents every ambient loop
based in the smaller poset. These two assertions travel through the same collapses. -/
def LoopComparison (C B : P → Prop) : Prop := InjIn C B ∧
  ∀ a p, B a → (orderCx P).IsEdgePath p a a → PathIn C p →
    ∃ l, (orderCx P).IsEdgePath l a a ∧ PathIn B l ∧ Htpy _ a a p l

theorem LoopComparison.refl (C : P → Prop) : LoopComparison C C :=
  ⟨injIn_self C, fun _ p _ hp hc => ⟨p, hp, hc, Htpy.refl _⟩⟩

theorem LoopComparison.trans {C A B : P → Prop} (h : LoopComparison C A)
    (k : LoopComparison A B) (hBA : ∀ x, B x → A x) : LoopComparison C B := by
  refine ⟨injIn_trans hBA h.1 k.1, ?_⟩
  intro a p ha hp hC
  obtain ⟨r, hr, hA, hpr⟩ := h.2 a p (hBA a ha) hp hC
  obtain ⟨l, hl, hB, hrl⟩ := k.2 a r ha hr hA
  exact ⟨l, hl, hB, hpr.trans hrl⟩

/-- Both parts of the comparison use the same order retraction. -/
theorem loopComparison_delete_free_face {C : P → Prop} {f t : P}
    (ht : C t) (hft : f ≤ t) (hne : t ≠ f)
    (hunique : ∀ x, C x → f ≤ x → x ≠ f → x = t) :
    LoopComparison C (fun x => C x ∧ x ≠ f) := by
  obtain ⟨r, hr, hle, hav, hfix⟩ := exists_freeFace_upper_retraction ht hft hne hunique
  let f' := Subtype.val ∘ r
  have hm := monotone_subtypeVal.comp hr
  have hB : ∀ x, C _ ∧ f' x ≠ f := fun x => ⟨(r x).2, hav x⟩
  refine ⟨injIn_of_monotone_retraction (fun _ h => h.1) f' hm hB
    (fun x hx => congrArg Subtype.val (hfix x hx.2)), ?_⟩
  exact fun _ _ => loop_representative_of_monotone_map (B := fun x => C x ∧ x ≠ f)
    (fun _ h => h.1) f' hm hB hle

end FiniteChains.Comb
