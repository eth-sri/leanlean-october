module

public import RequestProject.ChamberQuotientCycleGeneration
public import RequestProject.PosetCoverTargetIso
public import RequestProject.UniversalCoverPi1Injection

@[expose] public section

/-! The actual lifted inserted base covers the original base poset. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

noncomputable def qBaseOrderIso : {q : Qpos A X att // InQBase q} ≃o X where
  toFun q := Classical.choose q.2
  invFun x := ⟨qNew x, ⟨x, rfl⟩⟩
  left_inv q := Subtype.ext (Classical.choose_spec q.2)
  right_inv x := Sum.inr.inj (Classical.choose_spec (show InQBase (qNew x) from ⟨x, rfl⟩))
  map_rel_iff' {q r} := by
    have h : qNew (Classical.choose q.2) ≤
        qNew (att := att) (Classical.choose r.2) ↔ q.1 ≤ r.1 := by
      grind
    exact h

variable (a : Qpos A X att)

abbrev QLiftedBase :=
  {p : UOrder _ a // InQBase (uOrderEnd p)}

noncomputable def qBaseCoverEnd (p : QLiftedBase a) :=
  qBaseOrderIso ⟨uOrderEnd p.1, p.2⟩

omit [Fintype V] in
theorem qBaseCoverEnd_isPosetCover
    (hc : IsConnected (orderCx (Qpos A X att))) : IsPosetCover (qBaseCoverEnd a) := by
  have h := IsPosetCover.restriction (uOrderEnd (P := Qpos A X att) (a := a)) ({q | InQBase q})
    (uOrderEnd_isPosetCover hc)
  exact h.postcompose_orderIso qBaseOrderIso

omit [Fintype V] in
theorem qBaseCoverEnd_spec (p : QLiftedBase a) :
    qNew (qBaseCoverEnd a p) = uOrderEnd p.1 := Classical.choose_spec p.2

end FiniteChains.Davis
