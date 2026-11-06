module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OraclePosSem

/-!
# Lemma 3.6 (WP-H), part 19: moving the origin of a ray to the box

A query origin may be a symbolic point of `Q` off its edge (the point of the line of an edge at
a vertex height), hence outside the box of the chain.  Before the ray enters the box it meets
nothing of the chain, so the first hits from the origin and from the entry point differ by the
distance travelled outside (`firstHitOpt_shift`, `firstHit_unshift`, `noHit_unshift`).  An origin
past the box (the ray leaving it) misses everything inside (`noHit_past`).
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

@[expose] public section

variable {A : Set Point} {z : Point} {σ d R : ℝ}

section
variable (hA : A ⊆ Chain.box R) (hd : 0 ≤ d) (hout : ∀ s, 0 < s → s ≤ d → rayPt z σ s ∉ Chain.box R)
include hA hd hout
/-- First hits from the entry point. -/
theorem firstHitOpt_shift {o : Option ℝ}
    (h : Sweep.FirstHitOpt A z σ o) :
    Sweep.FirstHitOpt A (rayPt z σ d) σ (o.map (· - d)) := by
  cases o with
  | none =>
    intro t ht hm
    rw [rayPt_rayPt] at hm
    exact h (d + t) (by linarith) hm
  | some v =>
    obtain ⟨hv, hm, hfirst⟩ := h
    have hdv : d < v := by
      grind
    refine ⟨by simp_all, ?_, fun t ht hlt hm' => ?_⟩
    all_goals (grind [rayPt_rayPt])

/-- A first hit from the entry point is a first hit from the origin. -/
theorem firstHit_unshift {t : ℝ}
    (h : FirstHit A (rayPt z σ d) σ t) : FirstHit A z σ (t + d) := by
  obtain ⟨ht, hm, hfirst⟩ := h
  refine ⟨by linarith, by simp_all [rayPt_rayPt, add_comm] <;> omega_nf, fun s hs hlt hm' => ?_⟩
  by_cases hsd : s ≤ d
  · grind
  · push Not at hsd
    refine hfirst (s - d) (by linarith) (by linarith) ?_
    simp_all [rayPt_rayPt] <;> omega_nf


end

section
variable (hA : A ⊆ Chain.box R)
include hA
/-- No hit from the entry point is no hit from the origin. -/
theorem noHit_unshift (_hd : 0 ≤ d)
    (hout : ∀ s, 0 < s → s ≤ d → rayPt z σ s ∉ Chain.box R) (h : NoHit A (rayPt z σ d) σ) :
    NoHit A z σ := by
  intro s hs hm
  by_cases hsd : s ≤ d
  · grind
  · push Not at hsd
    refine h (s - d) (by linarith) ?_
    simp_all [rayPt_rayPt] <;> omega_nf

/-- **An origin past the box**: the ray never meets the box. -/
theorem noHit_past (hσ : σ = 1 ∨ σ = -1) (hpast : R ≤ σ * z.1) :
    NoHit A z σ := by
  intro s hs hm
  have := (abs_lt.1 (hA hm).1)
  simp only [rayPt_fst] at this
  rcases hσ with rfl | rfl
  all_goals linarith


end

end

end OracleR

end Chazelle.Core
