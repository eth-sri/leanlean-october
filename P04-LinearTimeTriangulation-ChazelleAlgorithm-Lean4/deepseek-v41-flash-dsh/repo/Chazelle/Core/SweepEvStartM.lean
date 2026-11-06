module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvTasks3
public import Chazelle.Core.SweepEvOrigin
public import Chazelle.Core.SweepEvStart

/-!
# The sweep (WP-D), stage 3: the start key (Task S, mathematics)

The start key `((gW + Lst) % n, 0)` of the walk of `C` (offset `Lst`, the copy of the shared vertex
on the `C₁` side):

* `start_key_ge_six`: its walk edge is at least `6` (it is a vertex of the tour or the box copy
  `2 m + 6` of the top), so it is a word-level position (`PosW`);
* every chord of `F₂⁺` attached there passes through the shared vertex (`start_key_pt`), which is
  off the domain of `C`, so it is the chord seen from the shared vertex (`chord_eq_shoot_of_end`):
  a shared chord, hence a stop chord;
* **`startMathTask : StartMathTask`**.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed Sweep

@[expose] public section

/-- The walk edge of the start key is at least `6`. -/
theorem start_key_ge_six (J : Merge.Junction) :
    6 ≤ (gW J + Lst J) % (chainModel J.whole).W.n := by
  have hn : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
  have hτ' := tpos_lt J.whole (J.m₁ + 2 * J.m₂)
  by_cases hlt : Lst J < lOff J
  · obtain ⟨-, -, hτ, hL⟩ := caseB_facts J hlt
    have hτw := tpos_lt J.whole J.m₁
    have e : (gW J + Lst J) % (chainModel J.whole).W.n = 2 * J.whole.m + 6 := by
      unfold gW
      rw [hL, hn, Nat.mod_eq_of_lt (⋄)]
      omega
    omega
  · have hlo : lOff J = Lst J := by
      by_cases hv : VNotTop J
      · Ξ lOff_of_vnt J hv, Lst_rlen
      · exact (caseC_facts J hv hlt).2.1
    Ξ ← hlo, gL_eq
    omega

/-- **Task S (mathematics): the start key.** -/
theorem startMathTask : StartMathTask := by
  intro P J N hP hN
  have hS₂ : N.F (chainModel J.right) (Qof P) ⊆ Merge.augChords J.right := hN.1.2.1
  refine ⟨⟨Nat.mod_lt _ (by have := Lst_lt_n J; omega), ShootCut.proper_vtx _ _ _ _,
    fun _ => start_key_ge_six J⟩, oW_start J hP (S₂ := ∅) (empty_subset _) finite_empty, ?_⟩
  intro e he hA
  have hvD : J.shared ∉ J.whole.dom := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.left_set_subset J.shared_mem_left)
  have hmem : J.shared ∈ e := by
    have := hA.2.2.2.1
    rwa [start_key_pt hP] at this
  obtain ⟨σ, hσ, hfree, heq⟩ :=
    chord_eq_shoot_of_end J.whole (F₂plus_subset J hS₂ he) hmem hvD
  exact Or.inl (Or.inl ⟨σ, hσ, hfree, heq⟩)

end

end SweepEv

end Chazelle.Core
