module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreNodeMath

/-!
# WP-E, the search: a stretch of a kind-1 piece

`Stretch M Cα g g' L`: the walk of the host model `M` from vertex `g` agrees, for `L` edges, with
the walk of the chain model of `Cα` from vertex `g'`, inside the double boundary of `Cα`'s walk
(`6 ≤ g'`, `g' + L ≤ 2 m + 6`).  The points of the stretch lie on `Cα`.

`Stretch.arrive` (M2' in offsets): a ray of `M` from the point of a chain end, towards the other
end `B` of an admissible chord of `Cα`'s model, that stays in `M`'s domain and arrives at a
position strictly inside the stretch, arrives at the position of `B` (same offset).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (sidePt SideAttach sideLeft sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)

/-- **A stretch of a kind-1 piece.** -/
structure Stretch (M : Model) (Cα : Chain) (g g' L : ℕ) : Prop where
  hA : WalkEmbed.Agree M.W (chainModel Cα).W g g' L
  hg : g < M.W.n
  hL0 : 0 < L
  hLn : L < M.W.n
  h6 : 6 ≤ g'
  hgL : g' + L ≤ 2 * Cα.m + 6

namespace Stretch

variable {M : Model} {Cα : Chain} {g g' L : ℕ}

theorem nα (Cα : Chain) : (chainModel Cα).W.n = 2 * Cα.m + 7 := Cα.sideWalk_n _

theorem mod' (hS : Stretch M Cα g g' L) {d : ℕ} (hd : d ≤ L) :
    (g' + d) % (chainModel Cα).W.n = g' + d :=
  Nat.mod_eq_of_lt (by rw [nα]; have := hS.hgL; omega)

section
variable (hS : Stretch M Cα g g' L) {d : ℕ} (hd : d < L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
include hS hd ht0 ht1
/-- The points of `Cα`'s walk inside the stretch lie on `Cα`. -/
theorem memα : sidePt (chainModel Cα).W (g' + d) t ∈ Cα.set := by
  have h := Cα.sideWalk_tour_pt_mem Cα.sideBeta (i := g' + d - 6) (t := t)
    (by have := hS.hgL; omega) (fun h => by exfalso; have := hS.hgL; have := hS.h6; omega) ht0 ht1
  rw [show g' + d - 6 + 6 = g' + d by have := hS.h6; omega] at h
  exact h

/-- The points of `M`'s walk inside the stretch lie on `Cα`. -/
theorem memM : sidePt M.W ((g + d) % M.W.n) t ∈ Cα.set := by
  rw [hS.hA.sidePt_eq hd, hS.mod' hd.le]
  exact hS.memα hd ht0 ht1


end

theorem rayPt_inj {a : Point} {σ s s' : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : rayPt a σ s = rayPt a σ s') : s = s' := by
  grind [rayPt_fst]

/-- **Arrival at the other end (M2' in offsets).** -/
theorem arrive (hS : Stretch M Cα g g' L) (hGα : WalkAx (chainModel Cα)) {c : Set Point}
    (hc : c ∈ (chainModel Cα).Adm) {pB : ℕ} {tB : ℝ} (hB : SideAttach (chainModel Cα).W c pB tB)
    {a : Point} (haC : a ∈ Cα.set) {σ L₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hL₀ : 0 < L₀)
    (hceq : c = Chazelle.segment a (rayPt a σ L₀))
    (hoB : rayPt a σ L₀ = sidePt (chainModel Cα).W pB tB)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a (rayPt a σ L₀) s ∈ Cα.dom)
    (hsetD : ∀ x ∈ Cα.set, x ∉ M.D) {T : ℝ} (hT : 0 < T)
    (hdom : ∀ s, 0 < s → s < T → rayPt a σ s ∈ M.D) {d : ℕ} {t : ℝ} (hd : d < L)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hdt : t = 0 → 1 ≤ d)
    (hfar : sidePt M.W ((g + d) % M.W.n) t = rayPt a σ T)
    (hFA : SideAttach M.W (chordOf a σ T) ((g + d) % M.W.n) t) :
    pB = g' + d ∧ tB = t := by
  set o := rayPt a σ L₀ with ho
  have hoD : o ∉ Cα.dom := by
    rw [hoB]; exact hGα.trace _ hB.1 _ hB.2.1 hB.2.2.1.le
  have hoy : o.2 = a.2 := by grind [rayPt_snd]
  have hdir : 0 < σ * (o.1 - a.1) := by
    rw [ho, rayPt_fst]; rcases hσ with rfl | rfl <;> linarith
  have hfarC : rayPt a σ T ∈ Cα.set := by rw [← hfar]; exact hS.memM hd ht0 ht1
  have harr := arrive_other hsetD hoy haC hkopen hoD hσ hdir hT hdom hfarC
  have hTL : T = L₀ := rayPt_inj hσ harr
  subst hTL
  have hch : chordOf a σ T = c := by rw [chordOf_eq_segment hσ hT, hceq]
  rw [hch] at hFA
  have hn : 0 < M.W.n := by have := hS.hg; omega
  have hnα : 0 < (chainModel Cα).W.n := by grind [nα]
  have hAα := (hS.hA.sideAttach_iff hn hnα hd hdt c).1 hFA
  rw [hS.mod' hd.le] at hAα
  have heq : sidePt (chainModel Cα).W (g' + d) t = sidePt (chainModel Cα).W pB tB := by
    rw [← hS.mod' hd.le, ← hS.hA.sidePt_eq hd, hfar, harr, hoB]
  obtain ⟨h1, h2⟩ := attach_unique hGα hc hAα hB heq
  ram_grind

end Stretch

end

end Restore

end Chazelle.Core
