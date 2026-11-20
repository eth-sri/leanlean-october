module

public import RequestProject.OrderUniversalPosetCover

@[expose] public section

/-! Actual edge and triangle coordinates of the universal-cover order complex. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

def uOrderEdge (e : OrdEdge (UOrder P a)) : UE (orderCx P) a :=
  ⟨(e.1.1, ⟨(uOrderEnd _, uOrderEnd _), uOrderEnd_monotone e.2⟩), rfl⟩

def uOrderFace (t : OrdTri (UOrder P a)) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(uOrderEnd _, uOrderEnd _, uOrderEnd _),
    uOrderEnd_monotone t.2.1, uOrderEnd_monotone t.2.2⟩), rfl⟩

theorem uOrder_up_injective {v w z : UOrder P a} (hw : v ≤ w) (hz : v ≤ z)
    (he : uOrderEnd w = uOrderEnd z) : w = z := by
  obtain ⟨hvw, ew⟩ := hw
  obtain ⟨hvz, ez⟩ := hz <;> simp_all

theorem uOrderEdge_injective : Function.Injective (uOrderEdge (P := P) (a := a)) := by
  intro e f h
  have hroot := congrArg (fun g : UE (orderCx P) a => g.1.1) h
  have ht := uOrder_up_injective e.2 (hroot ▸ f.2) (congrArg (fun g : UE (orderCx P) a => g.1.2.1.2) h)
  exact Subtype.ext (Prod.ext hroot ht)

theorem uOrderFace_injective : Function.Injective (uOrderFace (P := P) (a := a)) := by
  intro t s h
  have hroot := congrArg (fun g : UF (orderCx P) a => g.1.1) h
  have hm := uOrder_up_injective t.2.1 (hroot ▸ s.2.1) (congrArg (fun g : UF (orderCx P) a => g.1.2.1.2.1) h)
  have ht :=
    uOrder_up_injective (t.2.1.trans t.2.2) (hroot ▸ s.2.1.trans s.2.2) (congrArg (fun g : UF (orderCx P) a => g.1.2.1.2.2) h)
  exact Subtype.ext (Prod.ext hroot (Prod.ext hm ht))

theorem uOrderEdge_surjective : Function.Surjective (uOrderEdge (P := P) (a := a)) := by
  rintro ⟨⟨v, e⟩, hv⟩
  have hv' : uOrderEnd v = e.1.1 := hv
  let h := hv'.le.trans e.2
  refine ⟨⟨(v, (uOrderStep v _ h)), uOrderStep_le v _ h⟩, ?_⟩
  exact Subtype.ext (Prod.ext rfl
    (Subtype.ext (Prod.ext hv (uOrderStep_end v _ h))))

theorem uOrderFace_surjective : Function.Surjective (uOrderFace (P := P) (a := a)) := by
  rintro ⟨⟨v, t⟩, hv⟩
  have hv' : uOrderEnd v = t.1.1 := hv
  let h := hv'.le.trans t.2.1
  let w := uOrderStep v _ h
  let h' := (uOrderStep_end v _ h).le.trans t.2.2
  refine ⟨⟨(v, w, (uOrderStep w _ h')), uOrderStep_le v _ h, uOrderStep_le w _ h'⟩, ?_⟩
  exact Subtype.ext (Prod.ext rfl (Subtype.ext
    (Prod.ext hv (Prod.ext (uOrderStep_end v _ h) (uOrderStep_end w _ h')))))

end FiniteChains.Comb
