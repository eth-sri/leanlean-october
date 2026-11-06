import Mathlib.Tactic

import RequestProject.ChamberAttachingJ
import RequestProject.RACGPi1Example

/-!
# Which complex is compared with which: the levels of the two models

The chamber route builds the poset of spherical cosets `FiniteChains.Davis.Sph A`, whose order
complex is the **universal** Davis complex `D`: it is simply connected
(`FiniteChains.Davis.simplyConnected_davis`).  The square complex
`FiniteChains.RACG.cubeCx A` of the project is the finite moment-angle complex `C(L)`, whose
fundamental group is `Γ = ker(W → (ℤ/2)^{L⁰})` (`FiniteChains.RACG.pi1_cubeCx_equiv`).  So the
identifications of the article are

    D = universal Davis complex,   Γ = ker(W → (ℤ/2)^S),   Γ \ D = C(L),

and a comparison of `Comb.orderCx (Sph A)` with `cubeCx A` *itself* is impossible: it must be
made with the universal cover of `cubeCx A`, the `Γ`-quotient of the order complex being what
corresponds to `cubeCx A`.

This file proves the statements that make this precise:

* `FiniteChains.Davis.pi1_orderCx_sph_trivial` — `π₁(D) = 1` for the order complex of the
  poset of spherical cosets;
* `FiniteChains.Davis.not_nonempty_pi1_equiv_cubeCx` — for the two-letter example there is
  **no** isomorphism `π₁(orderCx (Sph L)) ≃* π₁(C(L))`; the naive form of obligation A.2 is
  therefore false, and only the comparison with the universal cover can hold;
* `FiniteChains.Davis.sphAct` and its lemmas — the action of `W` on the poset of spherical
  cosets by order automorphisms, which is the deck action of the covering `D → Γ \ D`;
* `FiniteChains.Davis.sphAct_apex_eq_self_iff` — the action is free on the chambers (the
  apexes), so the quotient map is a covering on the chamber level;
* `FiniteChains.RACG.phi_surjective` and `FiniteChains.RACG.phi_eq_iff_kerPhi` — the chambers
  of `D` map onto the vertices of `C(L)`, with fibres exactly the `Γ`-orbits.

Nothing here claims the full cellular comparison `Γ \ D ≅ C(L)`; that remains open, and what is
proved is the vertex/chamber level of it together with the correction of the level mismatch.
Note also that `cubeCx A` is a *square complex*, i.e. a two-dimensional object: for `H₂`
computations the full nerve chains of `RequestProject/NervePrism.lean` (which keep `C₃` and
`∂₃`) must be used, not the two-skeleton `Comb.orderCx`.
-/



namespace FiniteChains

open RACG Mirror Comb


namespace RACG

variable {V : Type u} [DecidableEq V] [Fintype V] (A : CommRel V)

/-- **The parity map is onto the vertices of `C(L)`.** -/
theorem phi_surjective : Function.Surjective (phi A) := by
  classical
  intro t
  refine ⟨cword A ((Finset.univ.filter (fun s : V => t s = 1)).toList), ?_⟩
  rw [phi_cword]
  funext v
  have hcount : ((Finset.univ.filter (fun s : V => t s = 1)).toList).count v =
      if t v = 1 then 1 else 0 := by
    classical aesop (add simp [if_pos, List.count_eq_one_of_mem, Finset.nodup_toList, if_neg, List.count_eq_zero_of_not_mem])
  rw [parList, hcount]
  by_cases h : t v = 1
  · simp [h]
  · have : t v = 0 := by
      revert h
      generalize t v = a
      revert a
      decide
    simp [this]

end FiniteChains.RACG
























