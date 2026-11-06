module

public import OAI.NumberTheory.PrimeGaps.RestrictedWeights

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def extendLabels {n : ℕ} {α : Type*} (a : Fin n → α) (d : ℕ) :
    Fin (n+d) → α ⊕ Fin d := Fin.append (Sum.inl ∘ a) Sum.inr

@[simp] theorem extendLabels_left {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin n) :
    extendLabels a d (i.castAdd d)=Sum.inl (a i) := by simp [extendLabels]

@[simp] theorem extendLabels_right {n d : ℕ} {α : Type*} (a : Fin n → α) (i : Fin d) :
    extendLabels a d (i.natAdd n)=Sum.inr i := by simp [extendLabels]

end LargePrimeGaps

end OAI
