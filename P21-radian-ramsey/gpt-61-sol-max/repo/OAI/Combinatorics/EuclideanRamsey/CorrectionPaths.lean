/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/CorrectionPaths.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.OrbitAveraging

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section




section
variable {G : Type*} {ι : Type*} [Group G] [Fintype ι] [DecidableEq ι]
namespace GradedPaths
variable (P : GradedPaths ι G) (L : Subgroup G)
variable (hL : ∀ i,L ≤ singleFractions P.monoid P.diagonal i)

def maxCost (g : G) : ℕ := Finset.univ.sup (fun i => P.singleCost i g)
lemma single_le_maxCost (i : ι) (g : G) : P.singleCost i g ≤ P.maxCost g :=
  Finset.le_sup (f := fun j => P.singleCost j g) (Finset.mem_univ i)
def normalCost : NormalCost L where
  cost g := P.maxCost g
  nonneg g := Nat.cast_nonneg _
  one := by simp [maxCost,P.singleCost_one]
  inv g hg := by simp [maxCost,P.singleCost_inv]
  conj g hg k := by simp [maxCost,P.singleCost_conjugate]
  mul g hg h hh := by
    rw [← Nat.cast_add]
    apply Nat.cast_le.mpr
    apply Finset.sup_le
    intro i _
    exact (P.singleCost_mul i (hL i hg) (hL i hh)).trans
      (add_le_add (P.single_le_maxCost i g) (P.single_le_maxCost i h))

end GradedPaths
end


variable {ι : Type*} {H : Type*} {X : Type*}
variable [Group H] [MulAction H X]

lemma OrbitWords.path {a : ι → FiniteEuclidean} (z : X → FiniteEuclidean)
    (f : ι → X) (q : ℝ) (hq : ∀ h : H,CopyPath a q (fun i => z (h • f i)))
    {w : X → LetterGroup} {m : ℕ} (hw : OrbitWords (H:=H) (fun x => FreeGroup.of (z x)) w m) :
    Path a (fun i => w (f i)) (q*m) := by
  induction hw with
  | diag g => simpa using (Path.diag (a:=a) g)
  | point h => simpa using (Path.copy (a:=a) _ (hq h))
  | mul _ _ ihu ihv => simpa [mul_add, Pi.mul_def] using ihu.mul ihv




end

end OAI.EuclideanRamsey
