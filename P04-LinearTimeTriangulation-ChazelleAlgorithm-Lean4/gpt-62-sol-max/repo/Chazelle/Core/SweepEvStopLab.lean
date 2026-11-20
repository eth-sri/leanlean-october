module

public import Chazelle.Core.SweepEvStopTasks
public import Chazelle.Core.SweepMachine19

/-!
# The sweep (WP-D), stage 2: the side labels of an anchored stop chord (mathematics, part 1)

* `slb_part1`: a chord of `F₂⁺` inside `c ∈ S₂`, attached at a position of the open right stretch
  other than the split vertex, has the side labels of `c` (`sideLabel_fused`).
* `slb_faced`: a region faced at a position of the open right stretch has the label faced at the
  counterpart position of the walk of `C₂` (`rlabel_of_faced`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Sweep
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

variable {J : Merge.Junction}

theorem slb_evVal {S₂ : Set (Set Point)} {Λ : Set (Set Point)} {G L : Set Point} (hL : L ∈ Λ)
    (hR : L ∈ J.rightModel.regions S₂) (hV : Valid J S₂ G L) : EvVal J S₂ Λ G :=
  ⟨L, Or.inl hL, hR, hV⟩

/-- **A chord inside a chord of `S₂`, away from the split vertex.** -/
theorem slb_part1 (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : J.rightModel.ChordFamily Q S₂)
    (hF : J.wholeModel.ChordFamily Q (F₂plus J S₂)) {e c : Set Point}
    (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂) (hec : e ⊆ c) {d : ℕ} (hd : d < Lst J) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    (hA : SideAttach J.wholeModel.W e ((gW J + d) % J.wholeModel.W.n) t)
    {Vu Vd : Set Point} (hVu : Vu ∈ J.rightModel.regions S₂)
    (hVd : Vd ∈ J.rightModel.regions S₂) (hsu : SideOf J.rightModel 1 c Vu)
    (hsd : SideOf J.rightModel (-1) c Vd) : EvSideLab J S₂ {Vu, Vd} e := by
  intro G hG ρ hρ hS
  rcases hρ with rfl | rfl
  · exact slb_evVal (Set.mem_insert _ _) hVu
      (sideLabel_fused J hP hS₂ hF he hc hec hd ht0 ht1 hsec hA (Or.inl rfl) hVu hsu G hG hS)
  · exact slb_evVal (Set.mem_insert_of_mem _ rfl) hVd
      (sideLabel_fused J hP hS₂ hF he hc hec hd ht0 ht1 hsec hA (Or.inr rfl) hVd hsd G hG hS)

/-- **A faced region** has the label faced at the counterpart position. -/
theorem slb_faced (hP : J.P.Simple) {Q : Polygon} {S₂ : Set (Set Point)}
    (hS₂ : J.rightModel.ChordFamily Q S₂) {d : ℕ} (hd : d < Lst J) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hd1 : t = 0 → 1 ≤ d) {ρ dir : ℝ} {G : Set Point}
    (hG : G ∈ J.wholeModel.regions (F₂plus J S₂))
    (hfac : FacedSide J.wholeModel ((gW J + d) % J.wholeModel.W.n) t ρ dir G)
    (hρd : ρ * dir = 1 ∨ ρ * dir = -1) {Va Vb : Set Point}
    (hVa : Va ∈ J.rightModel.regions S₂) (hVb : Vb ∈ J.rightModel.regions S₂)
    (ha : AfterFaces J.rightModel (cpA J d) t Va)
    (hb0 : 0 < t → BeforeFaces J.rightModel (cpA J d) t Vb)
    (hb1 : t = 0 → BeforeFaces J.rightModel (cpB J d) 0 Vb) :
    EvVal J S₂ {Va, Vb} G := by
  obtain ⟨R1, R2⟩ := rlabel_of_faced J hP hS₂.2.1 hS₂.1 hd ht0 ht1 hfac
  rcases hρd with h | h
  · rcases ht0.lt_or_eq with htp | ht
    · exact slb_evVal (Set.mem_insert_of_mem _ rfl) hVb
        (valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hVb ((R2 h Vb).1 htp (hb0 htp)))
    · subst ht
      exact slb_evVal (Set.mem_insert_of_mem _ rfl) hVb
        (valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hVb ((R2 h Vb).2 rfl (hd1 rfl) (hb1 rfl)))
  · exact slb_evVal (Set.mem_insert _ _) hVa
      (valid_of_rlabel J hP hS₂.2.1 hS₂.1 hG hVa (R1 h Va ha))

end

end SweepEv

end Chazelle.Core
