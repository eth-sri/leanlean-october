module

public import RequestProject.PresCoverRelatorFanLinks


@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

variable (c : StrictOrdTri P →₀ ℤ)

section
variable (b : StrictOrdEdge {p : P // f p ∈ coneAdjBaseSet} →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx P) c =
      chain1 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) b)
include hb

theorem presCoverConeCircleChain_cycle_of_cylinder_boundary
    (p : PresCoverRelator w f) :
    Comb.bdry1 (strictOrderCx (RelatorCircle w p.1.2))
      (presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c) = 0 := by
  have hr : strictRayChain p.1.1
      (chain1 (strictSubposetIncl _) b) = 0 := by
    classical
    clear hb
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b d hb hd => simp_all
    | single e n =>
      have hn : e.1.2.val ≠ p.1.1 := by
        intro he
        have hm := e.1.2.property
        erw [he, p.2] at hm
        rcases hm with ⟨a, ha⟩
        cases ha
      simp [chain1, strictSubposetIncl, strictOrderCxMap, strictRayChain, strictRayEdge, hn]
  unfold presCoverConeCircleChain
  erw [LinearMap.comp_apply, bdry1_chain1, ← strictTopLink_boundary _
    (presCover_apex_maximal w f hf _ _ p.2), hb, hr, map_zero]

/-- A chain with boundary in the cylinder has exactly one coefficient at each
actual relator apex, just as an absolute two-cycle does. -/
theorem presCover_relative_fan_circle
    (p : PresCoverRelator w f) :
    presCoverConeCircleChain w f hf _ _ p.2 c =
      presCoverConeCircleChain w f hf _ _ p.2
        (presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)) := by
  rw [presCoverRelatorFanChain_circle, presCoverRelatorChain_circle]
  solve_by_elim [relatorCircle_cycle_eq_smul_fundamental, presCoverConeCircleChain_cycle_of_cylinder_boundary]

/-- Subtracting the actual coordinate fans leaves an actual finite cylinder chain. -/
theorem exists_presCover_relative_cone_cylinder_decomposition :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet} →₀ ℤ,
      chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) d =
        c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c) := by
  let S := {p | f p ∈ coneAdjBaseSet}
  let r := c - presCoverRelatorFanChain w f hf (presCoverRelatorChain w f hf hpos c)
  have hs : ∀ t ∈ r.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S := by
    intro t ht
    have hlast : t.1.2.2 ∈ S := by
      by_contra hn
      cases hft : f _ with
      | inl x => solve_by_elim
      | inr j =>
        let p : PresCoverRelator w f := ⟨(t.1.2.2, j), hft⟩
        let e : StrictOrdEdge (StrictBelow t.1.2.2) :=
          ⟨(⟨t.1.1, t.2.1.trans t.2.2⟩, ⟨t.1.2.1, t.2.2⟩), t.2.1⟩
        have he := congrArg
          (fun z => z ((presCoverConeCircleHom w f hf p.1.1 p.1.2 p.2).onE e))
          (presCover_relative_fan_circle w f hf hpos c b hb p)
        erw [presCoverConeCircleChain_apply, presCoverConeCircleChain_apply] at he
        exact (Finsupp.mem_support_iff.mp ht) (sub_eq_zero.mpr he)
    exact ⟨coneAdjBaseSet_down_closed hlast (hf.mono (t.2.1.le.trans t.2.2.le)),
      coneAdjBaseSet_down_closed hlast (hf.mono t.2.2.le), hlast⟩
  exact inducedIncl_lift (· < ·) S r hs

end

/-- The actual relator coordinates detect genuine two-cycles. -/
theorem presCoverRelatorChain_cycle_injective (c d : StrictOrdTri P →₀ ℤ)
    (hc : Comb.bdry2 (strictOrderCx P) c = 0)
    (hd : Comb.bdry2 (strictOrderCx P) d = 0)
    (he : presCoverRelatorChain w f hf hpos c = presCoverRelatorChain w f hf hpos d) :
    c = d := by
  let U := {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}
  have hz : Comb.bdry2 (strictOrderCx P) (c - d) = 0 := by simp [map_sub, hc, hd]
  obtain ⟨e, h⟩ := exists_presCover_relative_cone_cylinder_decomposition w f hf hpos (c - d) 0
    (by simpa using hz)
  have heq : chain2 (strictSubposetIncl U) e = c - d := by simpa [map_sub, he] using h
  have hb : Comb.bdry2 (strictOrderCx U) e = 0 := by
    apply Finsupp.mapDomain_injective (strictSubposetIncl_onE_injective U)
    change chain1 (strictSubposetIncl U) _ = Finsupp.mapDomain _ 0
    erw [← bdry2_chain2 (strictSubposetIncl U) e, heq, hz, Finsupp.mapDomain_zero]
  rwa [presCover_cylinder_preimage_cycle_zero w f hf e hb, map_zero, eq_comm, sub_eq_zero] at heq

theorem presCoverCycleRelatorLinear_injective :
    Function.Injective (presCoverCycleRelatorLinear w f hf hpos) := by
  intro c d he
  apply Subtype.ext
  exact presCoverRelatorChain_cycle_injective w f hf hpos c.val d.val
    (LinearMap.mem_ker.mp c.property) (LinearMap.mem_ker.mp d.property) he


end FiniteChains.PresModel
