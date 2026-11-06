import RequestProject.OrderComponentLabels
import RequestProject.ConeAdjPoset
import RequestProject.CylinderPoset


namespace FiniteChains.Comb
universe u

 theorem cylP_isConnected {X S} [Preorder X] [Preorder S]
    (a : S →o X) (hc : IsConnected (orderCx X)) : IsConnected (orderCx (CylP a)) := by
  intro p q
  cases' hc _ _ with l hl
  have hm : Reach (orderCx (CylP a)) (cylCollapse a p) (cylCollapse a q) :=
    ⟨_, isPath_mapPath (orderCxMap (cylIn a) (cylIn_monotone a)) hl⟩
  exact (orderComponentLabel_eq_iff _ _).mp
    ((orderComponentLabel_eq_of_le (le_cylIn_cylRetr (X := X) a p)).trans
      (((orderComponentLabel_eq_iff _ _).mpr hm).trans
        (orderComponentLabel_eq_of_le (le_cylIn_cylRetr (X := X) a q)).symm))

theorem coneAdj_isConnected {P T} [Preorder P] (S : T → P → Prop)
    (hc : IsConnected (orderCx P)) (hs : ∀ t, ∃ p, S t p) :
    IsConnected (orderCx (ConeAdj S)) := by
  have hv : ∀ v, ∃ p : P,
      orderComponentLabel _ v = orderComponentLabel _ (ConeAdj.inc (S := S) p) := by
    intro v
    cases v with
    | inl p => tauto
    | inr t =>
      cases' hs t with p hp
      exact ⟨p, (orderComponentLabel_eq_of_le (ConeAdj.inc_le_apex_of_mem hp)).symm⟩
  intro v w
  cases' hv v with p hp
  cases' hv w with q hq
  cases' hc p q with l hl
  have hm : Reach (orderCx (ConeAdj S)) (ConeAdj.inc (S := S) p) (ConeAdj.inc (S := S) q) :=
    ⟨_, isPath_mapPath (orderCxMap (ConeAdj.inc (S := S)) (by tauto)) hl⟩
  exact (orderComponentLabel_eq_iff _ _).mp
    (hp.trans (((orderComponentLabel_eq_iff _ _).mpr hm).trans hq.symm))
