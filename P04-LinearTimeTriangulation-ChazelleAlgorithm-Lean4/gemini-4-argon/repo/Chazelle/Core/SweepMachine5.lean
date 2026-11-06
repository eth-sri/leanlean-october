module

public import Chazelle.Core.SweepMachine4

/-!
# The sweep (WP-D), part 21: the abstract machine, the acceptance test of a detection shot

The RAM decides whether a hit of a detection shot (in the model of a chain `C`, at the arcs of the
window region `U`) is genuine by the test `Accept` of design §9.3, computed from the arrival
position `(p, t)` of the hit (primitive `arrivalPos`), the turning tests at a walk vertex
(`turnNext`, `turnPrev`), an abscissa test, and at most one more shot (at the arcs of the region
of the arc beginning or ending at the vertex).  `ArcList M F U L`: the list `L` of key pairs is the
list of the arcs of `U` (read from the region record).

* `accept_sound`: an accepted hit is genuine;
* `accept_complete`: a genuine hit whose arrival key lies in an arc of `U` (open, or its end), with
  the lists of the neighbouring regions available, is accepted.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (point_ext)
open WalkEmbed

namespace Sweep

section ChainModel

variable (C : Chain)

/-- **A chord along a ray leaving a walk position is attached there**: if the ray from the point of
the position `(p, t)` in direction `τ'` starts in the left sector and along an admissible chord,
the chord is attached at `(p, t)`. -/
theorem sideAttach_of_along (hP : C.P.Simple) {e : Set Point} (he : e ∈ Merge.augChords C)
    {p : ℕ} {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1) {τ' : ℝ}
    (hτ' : τ' = 1 ∨ τ' = -1)
    (hsec : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) τ' 1))
    (hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt (chainModel C).W p t) τ' s ∈ e) :
    SideAttach (chainModel C).W e p t := by
  have hM : WalkAx (chainModel C) := FactsChain.walkAx C hP
  set z := sidePt (chainModel C).W p t
  have hzD : z ∉ C.dom := hM.trace p hp t ht ht1.le
  have hsec' : ∀ s > 0, sideLeft (chainModel C).W p t (rayPt z τ' s) :=
    fun s hs => (sideLeft_rayPt_iff _ p t τ' one_pos hs).1 hsec
  obtain ⟨y, l, r, hH, -, rfl, -, -⟩ := Merge.augChords_spec he
  obtain ⟨s₁, hs₁, hs₁0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hzy : z.2 = y := by simpa [rayPt] using hs₁.1
  have hzpt : ((z.1, y) : Point) = z := Prod.ext rfl hzy.symm
  refine ⟨hp, ht, ht1, ?_, 1, one_pos, fun x hx hxz _ => ?_⟩
  · rcases hτ' with rfl | rfl
    · have hzl : l ≤ z.1 := by
        by_contra h
        push Not at h
        obtain ⟨s, hs, hs'⟩ :=
          (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < l - z.1 by linarith))).exists
        have := hs.2.1; simp [rayPt] at this; linarith [hs'.2]
      have hzr : z.1 ≤ r := by
        have := hs₁.2.2; simp [rayPt] at this; linarith
      exact ⟨hzy, hzl, hzr⟩
    · have hzr : z.1 ≤ r := by
        by_contra h
        push Not at h
        obtain ⟨s, hs, hs'⟩ :=
          (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < z.1 - r by linarith))).exists
        have := hs.2.2; simp [rayPt] at this; linarith [hs'.2]
      have hzl : l ≤ z.1 := by
        have := hs₁.2.1; simp [rayPt] at this; linarith
      exact ⟨hzy, hzl, hzr⟩
  · obtain ⟨hxy, hxl, hxr⟩ := hx
    rcases hτ' with rfl | rfl
    · have hzl : z.1 = l := by
        have h1 : l ≤ z.1 := by
          by_contra h
          push Not at h
          obtain ⟨s, hs, hs'⟩ :=
            (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < l - z.1 by linarith))).exists
          have := hs.2.1; simp [rayPt] at this; linarith [hs'.2]
        have h2 : z.1 < r := by
          have := hs₁.2.2; simp [rayPt] at this; linarith
        rcases h1.lt_or_eq with h | h
        · exact absurd (by rw [← hzpt]; exact hH.open_mem _ h h2) hzD
        · exact h.symm
      have hxl' : l < x.1 := by
        rcases hxl.lt_or_eq with h | h
        · exact h
        · exfalso; apply hxz; exact Prod.ext (by rw [← h, hzl]) (by rw [hxy, hzy])
      have e : x = rayPt z 1 (x.1 - l) :=
        point_ext (by simp [rayPt, hzl]) (by simp [rayPt, hxy, hzy])
      rw [e]; exact hsec' _ (by linarith)
    · have hzr : z.1 = r := by
        have h1 : z.1 ≤ r := by
          by_contra h
          push Not at h
          obtain ⟨s, hs, hs'⟩ :=
            (hev.and (Ioo_mem_nhdsGT (show (0 : ℝ) < z.1 - r by linarith))).exists
          have := hs.2.2; simp [rayPt] at this; linarith [hs'.2]
        have h2 : l < z.1 := by
          have := hs₁.2.1; simp [rayPt] at this; linarith
        rcases h1.lt_or_eq with h | h
        · exact absurd (by rw [← hzpt]; exact hH.open_mem _ h2 h) hzD
        · exact h
      have hxr' : x.1 < r := by
        rcases hxr.lt_or_eq with h | h
        · exact h
        · exfalso; apply hxz; exact Prod.ext (by rw [h, hzr]) (by rw [hxy, hzy])
      have e : x = rayPt z (-1) (r - x.1) :=
        point_ext (by simp [rayPt, hzr]) (by simp [rayPt, hxy, hzy])
      rw [e]; exact hsec' _ (by linarith)

end ChainModel

end Sweep

end

end Chazelle.Core
