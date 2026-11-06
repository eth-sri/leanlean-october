module

public import Chazelle.Core.SweepEvStopTasks3

/-!
# The sweep (WP-D), stage 2: the counterpart of a stretch attachment without a parent (Task N)

`npc_inner_unique`: two chords of an admissible family attached at the same position inside a
walk edge are equal (distinct ones would form a tie, which only happens at a vertex,
`tie_pair`, `tie_shape`).

**`noParCut : NoParCut`**: a chord of `S₂` attached at the counterpart `cpA d + t` contains a chord
of `F₂⁺` attached at `(gW + d, t)` (`Corr0.transfer`), which is then `e`, against the hypothesis.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Sweep WalkEmbed
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

/-- **Two chords attached at the same position inside a walk edge are equal.** -/
theorem npc_inner_unique {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (ht : 0 < t)
    (hA : SideAttach M.W c p t) (hA' : SideAttach M.W c' p t) : c = c' := by
  by_contra hne
  rcases hM.tie_pair hF hc hc' hne hA hA' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (hM.tie_shape hF hc hc' hA hA' h1 h2).1 ht.ne'
  · exact absurd (hM.tie_shape hF hc' hc hA' hA h2 h1).1 ht.ne'

/-- **Task N: no cut at the counterpart of a stretch attachment without a parent.** -/
theorem noParCut : NoParCut := by
  intro J Q S₂ e hP hS₂ he hno d t hd ht0 ht1 heA ⟨c, hc, p, t', hA, hkey⟩
  have hC := corr_right0 J hP hS₂.2.1 hS₂.1
  have hd' : d < rL1 J + rL2 J := hd
  obtain ⟨hp, htt⟩ := Chazelle.Chain.sideKey_inj ht0.le ht1 hA.2.1 hA.2.2.1 hkey
  have hA2 : SideAttach (chainModel J.right).W c
      ((6 + tpos J.right 0 + dq (rL1 J) (rδ J) d) % (chainModel J.right).W.n) t := by
    have h : SideAttach (chainModel J.right).W c (cpA J d) t := by rw [hp, htt]; exact hA
    exact h
  obtain ⟨e', he', he'c, -, he'A⟩ := hC.transfer hd' ht0.le ht1 (fun h => absurd h ht0.ne') hc hA2
  have heA' : SideAttach (chainModel J.whole).W e
      ((6 + tpos J.whole J.m₁ + d) % (chainModel J.whole).W.n) t := heA
  have := npc_inner_unique hC.hM hC.hF he he' ht0 heA' he'A
  subst this
  exact hno c hc he'c

end

end SweepEv

end Chazelle.Core
