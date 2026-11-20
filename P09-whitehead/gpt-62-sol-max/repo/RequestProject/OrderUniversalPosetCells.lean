module

public import RequestProject.OrderUniversalPosetCover

@[expose] public section

/-! Actual edge and triangle coordinates of the universal-cover order complex. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

def uOrderEdge (e : OrdEdge (UOrder P a)) : UE (orderCx P) a :=
  ⟨(e.1.1, ⟨(uOrderEnd e.1.1, uOrderEnd e.1.2), uOrderEnd_monotone e.2⟩), rfl⟩

def uOrderFace (t : OrdTri (UOrder P a)) : UF (orderCx P) a :=
  ⟨(t.1.1, ⟨(uOrderEnd t.1.1, uOrderEnd t.1.2.1, uOrderEnd t.1.2.2),
    uOrderEnd_monotone t.2.1, uOrderEnd_monotone t.2.2⟩), rfl⟩

theorem uOrder_up_injective {v w z : UOrder P a} (hw : v ≤ w) (hz : v ≤ z)
    (he : uOrderEnd w = uOrderEnd z) : w = z := by
  obtain ⟨hvw, ew⟩ := hw
  obtain ⟨hvz, ez⟩ := hz
  exact ew.symm.trans ((uOrderStep_eq_of_target_eq v hvw hvz he).trans ez)

theorem uOrderEdge_injective : Function.Injective (uOrderEdge (P := P) (a := a)) := by
  intro e f h
  have hroot  := congrArg (·.1.1) h
  have hend  :=
    congrArg (·.1.2.1.2) h
  have ht  := uOrder_up_injective e.2 (hroot ▸ f.2) hend
  exact Subtype.ext (Prod.ext hroot ht)

theorem uOrderFace_injective : Function.Injective (uOrderFace (P := P) (a := a)) := by
  intro t s h
  have hroot  := congrArg (·.1.1) h
  have hmid  :=
    congrArg (·.1.2.1.2.1) h
  have htop  :=
    congrArg (·.1.2.1.2.2) h
  have hm  := uOrder_up_injective t.2.1 (hroot ▸ s.2.1) hmid
  have ht  :=
    uOrder_up_injective (t.2.1.trans t.2.2) (hroot ▸ s.2.1.trans s.2.2) htop
  exact Subtype.ext (Prod.ext hroot (Prod.ext hm ht))

theorem uOrderEdge_surjective : Function.Surjective (uOrderEdge (P := P) (a := a)) := by
  rintro ⟨⟨v, e⟩, hv⟩
  have hv' : uOrderEnd (v : UOrder P a) = e.1.1 := hv
  let w := uOrderLiftUp v e.1.2 (hv'.le.trans e.2)
  exact ⟨⟨(v, w.1), w.2.1⟩, Subtype.ext (Prod.ext rfl (Subtype.ext (Prod.ext hv w.2.2)))⟩

theorem uOrderFace_surjective : Function.Surjective (uOrderFace (P := P) (a := a)) := by
  rintro ⟨⟨v, t⟩, hv⟩
  have hv' : uOrderEnd (v : UOrder P a) = t.1.1 := hv
  let w := uOrderLiftUp v t.1.2.1 (hv'.le.trans t.2.1)
  let z := uOrderLiftUp w.1 t.1.2.2 (w.2.2.le.trans t.2.2)
  exact ⟨⟨(v, w.1, z.1), w.2.1, z.2.1⟩, Subtype.ext (Prod.ext rfl
    (Subtype.ext (Prod.ext hv (Prod.ext w.2.2 z.2.2))))⟩

end FiniteChains.Comb
