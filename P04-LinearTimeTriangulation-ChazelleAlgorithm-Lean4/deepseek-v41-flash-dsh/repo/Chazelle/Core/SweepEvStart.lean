module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvTasks
public import Chazelle.Core.SweepEvKey

/-!
# The sweep (WP-D), stage 3: the invariant at the start (task D2)

`startTask`: when every chord of `F₂⁺` attached at the start key `K` (offset `Lst`, the copy of the
shared vertex on the `C₁` side) is a bracket, the label set `{V}` made of the region `V` of `S₂`
faced in the model of `C₂` just before the end of the right stretch satisfies the invariant of
the event loop at `K`.

Proof: a non-enclosed position `x` beyond `K`, reached through bracket keys only, faces the
region faced at a position `w` just before `K` (`evGL`: `w` is not enclosed, its offset being
below `Lst`, and every chord attached between `w` and `x` is a bracket: none before `K`, the
chords at `K` by hypothesis, the later ones by the hypothesis of `EvInv`).  That region is the
region faced just before `K`, whose label is `V` (`valid_start`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed Sweep

@[expose] public section

/-- The right stretch is shorter than the walk of `C`. -/
theorem Lst_lt_n (J : Merge.Junction) : Lst J < (chainModel J.whole).W.n := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hm : J.whole.m = J.m₁ + J.m₂ := rfl
  have h1 := J.one_le_m₁
  have hL : Lst J = rlen J := rL1_add_rL2 J
  Ξ hn, hL, hm
  unfold rlen
  split_ifs <;> omega

/-- The offset of the start key is `Lst`. -/
theorem oW_start (J : Merge.Junction) (hP : J.P.Simple) {S₂ : Set (Set Point)}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    oW J ((((gW J + Lst J) % (chainModel J.whole).W.n : ℕ) : ℝ) + 0) = (Lst J : ℝ) := by
  have hC := corr_right0 J hP hS₂ hS₂f
  have h := off_key (n := (chainModel J.whole).W.n) (g := gW J) (d := Lst J) hC.hg (Lst_lt_n J)
    (t := 0) le_rfl one_pos
  Ξ oW_def
  simpa only [add_zero] using h

/-- **Task D2: the invariant at the start.** -/
theorem startTask : StartTask := by
  intro J Q S₂ hP hS₂ _hF hbrk V hV hW₂
  have hS₂a := hS₂.2.1
  have hS₂f := hS₂.1
  set n := (chainModel J.whole).W.n with hndef
  have hn0 : 0 < n := by have := Lst_lt_n J; omega
  set pK := (gW J + Lst J) % n with hpKdef
  have hpK : pK < n := Nat.mod_lt _ hn0
  have hoK : oW J ((pK : ℝ) + 0) = (Lst J : ℝ) := oW_start J hP hS₂a hS₂f
  have hL0 := Lst_pos J
  intro p t hp ht hnc ho hbr
  by_cases hEx : EvEncl J S₂ (oW J (p + t))
  · exact Or.inl hEx
  right
  intro G hG hf
  obtain ⟨R, hR, hWR, q, u, hq, hu, hncq, hfq, h1, h2, hgap⟩ :=
    before_region_exists' hP hS₂a hS₂f hpK le_rfl one_pos (by rw [hoK]; exact hL0) hL0
  rw [hoK] at h1 h2 hgap
  -- the position before the start is not enclosed
  have hEq : ¬ EvEncl J S₂ (oW J (q + u)) := by
    rintro ⟨e, -, pa, pb, ta, tb, -, -, -, hLa, hlt, -⟩
    linarith
  -- every chord attached between the two positions is a bracket
  have hbr' : ∀ e ∈ F₂plus J S₂, ∀ (q' : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q' s →
      oW J (q + u) < oW J (q' + s) → oW J (q' + s) < oW J (p + t) → EvBrk J e := by
    intro e he q' s hA ha hb
    rcases lt_trichotomy (oW J (q' + s)) (Lst J) with hlt | heq | hgt
    · obtain ⟨k0, k1⟩ := attach_key_mem hA
      exact absurd ⟨ha, hlt⟩ (hgap _ ⟨e, he, q', s, hA, rfl⟩ k0 k1)
    · rw [← hoK] at heq
      obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hA.1 hpK hA.2.1 hA.2.2.1 le_rfl one_pos heq
      exact hbrk e he hA
    · exact hbr e he q' s hA hgt hb
  have hRG : R = G := evGL hP hS₂a hS₂f hq hp hu ht hncq hnc (⟡) hEq hEx hbr' hR hG hfq hf
  subst hRG
  refine ⟨V, Or.inl rfl, hV, ?_⟩
  exact valid_start J hP hS₂a hS₂f (by have := Lst_pos J; unfold Lst at this; exact_mod_cast this)
    hR hV hWR hW₂

end

end SweepEv

end Chazelle.Core
