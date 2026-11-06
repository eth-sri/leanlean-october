/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.PathWords

@[expose] public section

namespace OAI.EuclideanRamsey






attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

/-! Realizing a family of ultrafilters directly avoids an auxiliary language of columns. -/
section Ultrafilters
variable {M : Type*} [Monoid M]
instance ultrafilterMonoid : Monoid (Ultrafilter M) where
  toSemigroup := Ultrafilter.semigroup
  one := pure 1
  one_mul U := by
    change (pure (1:M) : Ultrafilter M)*U=U
    apply Ultrafilter.coe_inj.mp
    apply Filter.ext'
    intro p
    simp [Ultrafilter.eventually_mul]
  mul_one U := by
    change U*(pure (1:M) : Ultrafilter M)=U
    apply Ultrafilter.coe_inj.mp
    apply Filter.ext'
    intro p
    simp [Ultrafilter.eventually_mul]

end Ultrafilters


variable {ι : Type*} {a : ι → FiniteEuclidean}
def UltraFamily (a : ι → FiniteEuclidean) (U : ι → Ultrafilter Strings) (u : ℝ) : Prop :=
  ∀ B : ι → Set Strings, (∀ i, B i ∈ U i) →
    ∃ x : ι → Strings, StringFamily a u x ∧ ∀ i, x i ∈ B i

lemma UltraFamily.common [Finite ι] (a : ι → FiniteEuclidean) (U : Ultrafilter Strings) :
    UltraFamily a (fun _ => U) 0 := by
  intro B h
  have hh  := Filter.eventually_all.mpr h
  obtain ⟨x,hx⟩ := hh.exists
  exact ⟨fun _ => x, StringFamily.common a x, hx⟩

lemma UltraFamily.single {b : ι → FiniteEuclidean} {u : ℝ} (hb : CopyPath a u b) :
    UltraFamily a (fun i => pure (FreeMonoid.of (b i))) u := by
  intro B h
  exact ⟨_, StringFamily.single hb, fun i => by simpa using h i⟩

lemma UltraFamily.mul {U V : ι → Ultrafilter Strings} {u v : ℝ}
    (hu : UltraFamily a U u) (hv : UltraFamily a V v) : UltraFamily a (fun i => U i*V i) (u+v) := by
  intro B h
  have hh (i) : {x | {y | x*y ∈ B i} ∈ V i} ∈ U i :=
    (Ultrafilter.eventually_mul _ _ _).mp (h i)
  obtain ⟨x,hx,hxB⟩ := hu _ hh
  obtain ⟨y,hy,hyB⟩ := hv (fun i => {y | x i*y ∈ B i}) hxB
  exact ⟨x*y,hx.mul hy,hyB⟩

lemma Path.ultra [Finite ι] {w u} (h : Path a w u)
    (Ψ : LetterGroup →ₙ* Ultrafilter Strings) (p : Ultrafilter Strings)
    (hgen : ∀ z, Ψ (FreeGroup.of z) = p*pure (FreeMonoid.of z)*p) :
    UltraFamily a (fun i => Ψ (w i)) u := by
  induction h with
  | diag g => exact UltraFamily.common a _
  | @copy u b hb =>
    simpa only [Pi.mul_apply,zero_add,add_zero,hgen,mul_assoc] using
      (UltraFamily.common a p).mul ((UltraFamily.single hb).mul (UltraFamily.common a p))
  | mul _ _ ihu ihv => simpa only [Pi.mul_apply, Ψ.map_mul] using ihu.mul ihv

lemma UltraFamily.list_prod [Finite ι] {α : Type*} (l : List α)
    (U : α → ι → Ultrafilter Strings) (u : α → ℝ)
    (h : ∀ j ∈ l, UltraFamily a (U j) (u j)) :
    UltraFamily a (fun i => (l.map (fun j => U j i)).prod) ((l.map u).sum) := by
  induction l with
  | nil => simp_all [UltraFamily.common]
  | cons j l ih => simp_all [mul]

end OAI.EuclideanRamsey
