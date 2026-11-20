module

public import OAI.NumberTheory.PrimeGaps.Detectors

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

def permutedLabels {n : ℕ} (e : Equiv.Perm (Fin n)) : Fin (n+n) → Fin n := Fin.append id e

theorem permutedLabels_fiber_sum {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => permutedLabels e i=r), w i)=w (r.castAdd n)+w ((e.symm r).natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [permutedLabels,←Equiv.eq_symm_apply]

@[simp] theorem permutedLabels_fiber_card {n : ℕ} (e : Equiv.Perm (Fin n)) (r : Fin n) :
    (Finset.univ.filter fun i => permutedLabels e i=r).card=2 := by
  simpa using permutedLabels_fiber_sum e r (fun _ => (1:ℕ))

noncomputable def weightedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) (m : ℕ) : ℝ :=
  ∑ b : Fin n → Fin h, k (Setoid.ker b)*divisorSum X F m (fun i => a+(b i:ℕ))

@[simp] theorem append_ker_left {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.castAdd p) (Setoid.ker (Fin.append b c))=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.castAdd p)=Fin.append b c (j.castAdd p) ↔ b i=b j
  simp only [Fin.append_left]

@[simp] theorem append_ker_right {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.natAdd n) (Setoid.ker (Fin.append b c))=Setoid.ker c := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.natAdd n)=Fin.append b c (j.natAdd n) ↔ c i=c j
  simp only [Fin.append_right]

end LargePrimeGaps

end OAI
