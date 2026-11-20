/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/SignedRows.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Ported to the Lean module system; proofs simplified for the radian configuration.
-/
module

public import Mathlib

public section

namespace OAI.EuclideanRamsey

open Algebra GrothendieckAddGroup Multiset

/-- Extend the statistic from the image, then evaluate the extension on each
singleton coordinate. This applies both to histograms and to tensor moments. -/
theorem coordinate_potentials {G V ι : Type} [AddCommGroup G] [AddCommGroup V] [Fintype ι]
    (T : G →+ (ι → V)) (E : G →+ ℝ) (hk : T.ker ≤ E.ker) :
    ∃ f : ι → V → ℝ, ∀ x, ∑ i, f i (T x i) = E x := by
  classical
  obtain ⟨L,hL⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom _
    (QuotientAddGroup.kerLift_injective T) (QuotientAddGroup.lift _ E hk)
  refine ⟨fun i b => L (Pi.single i b),fun x => ?_⟩
  rw [←map_sum,Finset.univ_sum_single]
  exact DFunLike.congr_fun hL (QuotientAddGroup.mk x)

/-- An additive statistic determined by the separate histograms is a sum of
single-coordinate potentials: pass to the group completions, then extend off
the image, using divisibility of the additive group of reals. -/
theorem represents_of_trades {α β ι : Type} [Fintype ι] (v : ι → α → β) (e : α → ℝ)
    (h : ∀ P Q : Multiset α, (∀ i, P.map (v i) = Q.map (v i)) → (P.map e).sum = (Q.map e).sum) :
    ∃ f : ι → β → ℝ, ∀ x, ∑ i, f i (v i x) = e x := by
  let I := GrothendieckAddGroup (Multiset β)
  let hist : Multiset α →+ (ι → I) := AddMonoidHom.pi fun i => of.comp (mapAddMonoidHom (v i))
  let cost := sumAddMonoidHom.comp (mapAddMonoidHom e)
  obtain ⟨f,hf⟩ := coordinate_potentials (lift hist) (lift cost) (by
    intro x hx
    simp only [AddMonoidHom.mem_ker,lift_apply,sub_eq_zero] at hx ⊢
    exact h _ _ (fun i => of_injective (congrFun hx i)))
  exact ⟨fun i b => f i (of ({b} : Multiset β)),fun x => by
    have h := hf (of ({x} : Multiset α)); simp [lift,cost] at h; exact h⟩

end OAI.EuclideanRamsey
