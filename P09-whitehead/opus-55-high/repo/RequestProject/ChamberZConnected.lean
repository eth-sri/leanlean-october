import RequestProject.ChamberZPi1Base
import RequestProject.OrderComponentLabels


namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [Preorder X] [Nonempty X] {M : CayGroup A → Prop}
  {att : NeSpx A →o X}

omit [Fintype V] [Nonempty X] in
theorem zChamber_reachable (hc : IsConnected (orderCx X)) (w : CayGroup A)
    {p q : Zpos A X M att} (hp : InZChamber w p) (hq : InZChamber w q) :
    Reach (orderCx (Zpos A X M att)) p q := by
  classical
  apply (orderComponentLabel_eq_iff p q).mp
  by_cases hw : M w
  · let rp := zChamberRetr hw ⟨p, hp⟩
    let rq := zChamberRetr hw ⟨q, hq⟩
    cases' zChamberRetr_mem hw ⟨p, hp⟩ with x hx
    cases' zChamberRetr_mem hw ⟨q, hq⟩ with y hy
    have hpx := orderComponentLabel_eq_of_le
      (show rp.1 ≤ p from zChamberRetr_le hw _)
    have hqy := orderComponentLabel_eq_of_le
      (show rq.1 ≤ q from zChamberRetr_le hw _)
    have hm : Monotone (zNew (A := A) (att := att) ⟨w, hw⟩) :=
      by tauto
    cases' hc x y with l hl
    have hr : Reach (orderCx (Zpos A X M att))
        (zNew (att := att) ⟨w, hw⟩ x) (zNew (att := att) ⟨w, hw⟩ y) :=
      ⟨_, isPath_mapPath (orderCxMap _ hm) hl⟩
    have hxy := (orderComponentLabel_eq_iff _ _).mpr hr
    grind
  · exact (orderComponentLabel_eq_of_le (zApex_le hw hp)).symm.trans
      (orderComponentLabel_eq_of_le (zApex_le hw hq))

omit [Fintype V] in
theorem exists_zChamber_vertex (w : CayGroup A) :
    ∃ p : Zpos A X M att, InZChamber w p := by
  classical
  by_cases hw : M w
  · exact ⟨zNew ⟨w, hw⟩ (Classical.choice inferInstance), rfl⟩
  · exact ⟨zApex (X := X) (att := att) hw, inZChamber_zApex hw⟩

/-- Connectivity follows from the connected base and the actual nonempty attaching
intersections, by induction on chamber word length. -/
theorem zpos_isConnected (hc : IsConnected (orderCx X)) :
    IsConnected (orderCx (Zpos A X M att)) := by
  classical
  cases' exists_zChamber_vertex (A := A) (X := X) (M := M) (att := att) 1 with b hb
  have hr : ∀ n w, RACG.clen A w = n → ∀ p,
      InZChamber w p → orderComponentLabel _ p = orderComponentLabel _ b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw p hp
      by_cases hw1 : w = 1
      · subst w
        exact (orderComponentLabel_eq_iff _ _).mpr (zChamber_reachable hc 1 hp hb)
      · cases' exists_zJSet (X := X) (M := M) (att := att) hw1 with j hj
        have hjw := zJSet_imp_inZChamber hj
        obtain ⟨y, hy, hjy⟩ := (mem_shorter_zchamber_iff hjw).2 hj
        have hnj : RACG.clen A y < n := by omega
        exact ((orderComponentLabel_eq_iff _ _).mpr
          (zChamber_reachable hc w hp hjw)).trans (by grind)
  intro p q
  cases' exists_inZChamber p with w hw
  cases' exists_inZChamber q with v hv
  exact (orderComponentLabel_eq_iff _ _).mp
    ((hr _ w rfl p hw).trans (hr _ v rfl q hv).symm)
