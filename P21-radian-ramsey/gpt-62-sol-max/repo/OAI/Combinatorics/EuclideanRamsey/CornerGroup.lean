/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/CornerGroup.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Adapted to the Lean module system and simplified for this proof.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public section

namespace OAI.EuclideanRamsey

open Set

theorem exists_corner_hom {S X : Type*} [Nonempty S] [Semigroup S]
    [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (hc : ∀ y : S, Continuous (· * y)) (f : X → S) :
    ∃ (p : S) (Ψ : FreeGroup X →ₙ* S), ∀ x, Ψ (FreeGroup.of x) = p*f x*p := by
  classical
  let ideals : Set (Set S) := {N | IsClosed N ∧ N.Nonempty ∧ ∀ x y, y∈N → x*y∈N}
  obtain ⟨N,_,hN⟩ := zorn_superset_nonempty ideals (fun c hcs hchain hcn => by
    let := hcn.coe_sort
    refine ⟨⋂₀ c, ⟨isClosed_sInter (fun N hN => (hcs hN).1), ?_, fun x y hy => ?_⟩,
      fun _ => Set.sInter_subset_of_mem⟩
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (IsChain.directedOn (show IsChain (· ⊇ ·) c from hchain.symm))
        (fun N hN => (hcs hN).2.1) (fun N hN => (hcs hN).1.isCompact) (fun N hN => (hcs hN).1)
    · grind) Set.univ
      (by simp [ideals])
  have hprincipal (y : S) (hy : y∈N) : Set.range (·*y) = N := by
    apply hN.eq_of_subset
    · refine ⟨isCompact_range (hc y) |>.isClosed, ⟨y*y,y,rfl⟩, ?_⟩
      rintro a _ ⟨b,rfl⟩
      exact ⟨a*b,mul_assoc a b y⟩
    · rintro _ ⟨a,rfl⟩
      exact hN.prop.2.2 a y hy
  obtain ⟨p,hpN,hp⟩ := exists_idempotent_in_compact_subsemigroup hc N
    hN.prop.2.1 hN.prop.1.isCompact (fun x _ y hy => hN.prop.2.2 x y hy)
  let C := Subsemigroup.corner p
  have eqs (y : C) := (Subsemigroup.mem_corner_iff hp).mp y.2
  let : One C := ⟨⟨p,p,by simp [hp]⟩⟩
  have h (y : C) : ∃ v : C, v*y = 1 := by
    have hy : y.val ∈ N := (eqs y).2 ▸ hN.prop.2.2 y.val p hpN
    obtain ⟨v,hv⟩ : p ∈ Set.range (· * y.val) := hprincipal y.val hy ▸ hpN
    exact ⟨⟨_,v,rfl⟩,Subtype.ext (by change p*v*p*y.val=p; grind [mul_assoc])⟩
  choose inv hinv using h
  let : Inv C := ⟨inv⟩
  let : Group C := Group.ofLeftAxioms (fun x y z : C => mul_assoc x y z)
    (fun x => Subtype.ext (eqs x).1) hinv
  let letter (x : X) : C := ⟨_,f x,rfl⟩
  refine ⟨p,(MulMemClass.subtype C).comp (FreeGroup.lift letter).toMulHom,fun x => ?_⟩
  simp [letter]

end OAI.EuclideanRamsey
