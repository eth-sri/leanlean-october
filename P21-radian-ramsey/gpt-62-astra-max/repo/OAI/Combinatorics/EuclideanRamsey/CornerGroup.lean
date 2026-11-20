/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/CornerGroup.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Ported to the Lean module system; proofs simplified for the radian configuration.
-/
module

public import Mathlib

@[expose] public noncomputable section

namespace OAI.EuclideanRamsey
open Set

universe u
variable {S : Type u} [Semigroup S]
theorem exists_group_corner [Nonempty S]
    [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (hc : ∀ y : S, Continuous (· * y)) :
    ∃ (p : S) (G : Type u) (_ : Group G) (φ : G →ₙ* S), ∀ s, p*s*p ∈ Set.range φ := by
  let I (y : S) := Set.range (·*y)
  have smaller {x y : S} (h : x ∈ I y) : I x ⊆ I y := by
    obtain ⟨b,rfl⟩ := h
    rintro _ ⟨a,rfl⟩; exact ⟨a*b,mul_assoc ..⟩
  let := Preorder.lift I
  obtain ⟨m,hm⟩ := zorn_ge_nonempty (α:=S) (fun c hchain hne => by
    have := hne.coe_sort
    obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (fun y : c => I y)
      hchain.directedOn.directed_val (fun _ => range_nonempty _) (fun y => isCompact_range (hc y))
      (fun y => (isCompact_range (hc y)).isClosed)
    exact ⟨x,fun y hy => smaller (mem_iInter.mp hx ⟨y,hy⟩)⟩)
  obtain ⟨p,hpI,hp⟩ := exists_idempotent_in_compact_subsemigroup hc (I m) (range_nonempty _) (isCompact_range (hc m))
    (fun x _ _ hy => smaller hy ⟨x,rfl⟩)
  let K := Subsemigroup.corner p
  let : One K := ⟨⟨p,p,by simp [hp]⟩⟩
  have left (y : K) := (Subsemigroup.mem_corner_iff hp).mp y.2
  have inv (y : K) : ∃ v : K, v*y=1 := by
    obtain ⟨hpy,hyp⟩ := left y
    have hy : y.val ∈ I m := hyp ▸ smaller hpI ⟨y.val,rfl⟩
    obtain ⟨v,hv⟩ : p ∈ I y.val := hm (smaller hy) hpI
    exact ⟨⟨p*v*p,v,rfl⟩,Subtype.ext (by change (p*v*p)*y.val=p; grind)⟩
  choose f hf using inv
  let : Inv K := ⟨f⟩
  let := Group.ofLeftAxioms mul_assoc (fun x : K => Subtype.ext (left x).1) hf
  exact ⟨p,K,inferInstance,MulMemClass.subtype K,fun s => ⟨⟨_,s,rfl⟩,rfl⟩⟩

end OAI.EuclideanRamsey
