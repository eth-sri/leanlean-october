/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.CornerGroup

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section





attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

def ultraColor {M κ : Type*} [Finite κ] (c : M → κ) (U : Ultrafilter M) :
    {k : κ // {x | c x=k}∈U} :=
  Classical.indefiniteDescription _ (by apply Ultrafilter.eventually_exists_iff.mp; simp)

lemma exists_corner_map : ∃ (p : Ultrafilter Strings) (Ψ : LetterGroup →ₙ* Ultrafilter Strings),
    ∀ z,Ψ (FreeGroup.of z)=p*(pure (FreeMonoid.of z))*p := by
  obtain ⟨p,hp,hi⟩ := exists_group_corner (S:=Ultrafilter Strings) Ultrafilter.continuous_mul_left
  let C := {x : Ultrafilter Strings // p*x=x ∧ x*p=x}
  let : Mul C := ⟨fun x y => ⟨x.val*y.val,by grind⟩⟩
  let : One C := ⟨⟨p,hp,hp⟩⟩
  choose inv hinv hinv' hmul using fun y : C => hi y.val y.property.1 y.property.2
  let : Inv C := ⟨fun y => ⟨inv y,hinv y,hinv' y⟩⟩
  let : Group C := Group.ofLeftAxioms
    (fun x y z => Subtype.ext (mul_assoc x.val y.val z.val))
    (fun x => Subtype.ext x.property.1)
    (fun x => Subtype.ext (hmul x))
  let letter z : C :=
    ⟨p*(pure (FreeMonoid.of z))*p,by
      grind⟩
  let ψ  := FreeGroup.lift letter
  let v : C →ₙ* Ultrafilter Strings := { toFun := Subtype.val, map_mul' _ _ := rfl }
  refine ⟨p,v.comp ψ.toMulHom,?_⟩
  intro z
  change (ψ (FreeGroup.of z)).val=_
  simp [ψ,letter]


namespace FiniteEuclidean

open Filter
def truncate (d : ℕ) (x : FiniteEuclidean) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => x i)

lemma eventually_embed_truncate (x : FiniteEuclidean) :
    ∀ᶠ d : ℕ in atTop,embed (d+1) (truncate (d+1) x)=x := by
  filter_upwards [eventually_ge_atTop (x.support.sup id)] with d hd
  ext n
  by_cases hn : n<d+1
  · exact Finsupp.mapDomain_apply_of_injective Fin.val_injective _ ⟨n,hn⟩
  · trans 0
    · apply Finsupp.mapDomain_of_notMem_range
      simp; omega
    · symm
      apply Finsupp.notMem_support_iff.mp
      intro hm
      have : n ≤ x.support.sup id := Finset.le_sup (f := id) hm
      omega
end FiniteEuclidean


end

end OAI.EuclideanRamsey
