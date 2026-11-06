/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/CornerGroup.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathSynchronization

public section

namespace OAI.EuclideanRamsey







theorem exists_group_corner {S : Type*} [Nonempty S] [Semigroup S]
    [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (hc : ∀ y : S, Continuous (· * y)) :
    ∃ p : S, p*p=p ∧ ∀ y : S, p*y=y → y*p=y →
      ∃ v : S, p*v=v ∧ v*p=v ∧ v*y=p := by
  let ideals : Set (Set S) := {N | IsClosed N ∧ N.Nonempty ∧ ∀ x y, y∈N → x*y∈N}
  have hmin : ∃ N, Minimal (· ∈ ideals) N := by
    refine zorn_superset _ fun c hcs hchain => ?_
    refine ⟨⋂₀ c, ⟨isClosed_sInter (fun N hN => (hcs hN).1), ?_, ?_⟩,
      fun N hN => Set.sInter_subset_of_mem hN⟩
    · obtain rfl | hcn := c.eq_empty_or_nonempty
      · simp
      convert! @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        _ _ _ hcn.coe_sort ((↑) : c → Set S) ?_ ?_ ?_ ?_
      · exact Set.sInter_eq_iInter
      · exact DirectedOn.directed_val (IsChain.directedOn hchain.symm)
      · exact fun N => (hcs N.prop).2.1
      · exact fun N => (hcs N.prop).1.isCompact
      · exact fun N => (hcs N.prop).1
    · intro x y hy
      exact Set.mem_sInter.mpr fun N hN => (hcs hN).2.2 x y (Set.mem_sInter.mp hy N hN)
  obtain ⟨N,hN⟩ := hmin
  have hprincipal y (hy : y∈N) : Set.range (·*y) = N := by
    apply hN.eq_of_subset
    · refine ⟨isCompact_range (hc y) |>.isClosed, ⟨y*y,y,rfl⟩, ?_⟩
      rintro a _ ⟨b,rfl⟩
      exact ⟨a*b,mul_assoc a b y⟩
    · rintro _ ⟨a,rfl⟩
      exact hN.prop.2.2 a y hy
  obtain ⟨p,hpN,hp⟩ := exists_idempotent_in_compact_subsemigroup hc N
    hN.prop.2.1 hN.prop.1.isCompact (fun x _ y hy => hN.prop.2.2 x y hy)
  refine ⟨p,hp,?_⟩
  intro y hpy hyp
  have hyN := hyp ▸ hN.prop.2.2 y p hpN
  have hpr := hprincipal y hyN ▸ hpN
  obtain ⟨v,hv⟩ := hpr
  change v*y=p at hv
  refine ⟨p*v*p,?_,?_,?_⟩
  all_goals grind

end OAI.EuclideanRamsey
