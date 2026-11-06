module

public import OAI.NumberTheory.PrimeGaps.CumulativeProfiles

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics



open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def appendMeasurableEquiv (n m : ℕ) :
    ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ (Fin (n+m) → ℝ) :=
  (Fin.appendHomeomorph n m).toMeasurableEquiv

@[simp] theorem appendMeasurableEquiv_apply (n m : ℕ) (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    appendMeasurableEquiv n m p = Fin.append p.1 p.2 := rfl

noncomputable def tensorProfile {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin (n+m) → ℝ) : ℝ :=
  f (fun i => v (i.castAdd m)) * g (fun i => v (i.natAdd n))

@[simp] theorem tensorProfile_append {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    tensorProfile f g (Fin.append v w)=f v*g w := by
  simp [tensorProfile]

@[simp] theorem logCoordinates_append (X : ℕ) {n m : ℕ}
    (d : Fin n → ℕ) (e : Fin m → ℕ) :
    logCoordinates X (Fin.append d e)=Fin.append (logCoordinates X d) (logCoordinates X e) := by
  ext i
  cases i using Fin.addCases <;> simp [logCoordinates]

@[simp] theorem divisorCoefficient_tensor (X : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (d : Fin n → ℕ) (e : Fin m → ℕ) :
    divisorCoefficient X (tensorProfile F G) (Fin.append d e)=
      divisorCoefficient X F d*divisorCoefficient X G e := by
  simp only [divisorCoefficient,logCoordinates_append,tensorProfile_append,Fin.prod_univ_add,
    Fin.append_left,Fin.append_right]
  ring

@[simp] theorem logCoordinates_snoc (X : ℕ) {n : ℕ} (d : Fin n → ℕ) (e : ℕ) :
    logCoordinates X (Fin.snoc d e) = Fin.snoc (logCoordinates X d) (Real.log e/Real.log X) := by
  ext i
  cases i using Fin.lastCases <;> simp [logCoordinates]

@[simp] theorem fiberRay_apply {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (i : ι) : fiberRay b r i=if b i=r then 1 else 0 := by
  classical
  simp [fiberRay,WithLp.ofLp_sum,Finset.sum_apply]

@[simp] theorem append_self_addNat {n : ℕ} {α : Type*} (y z : Fin n → α) (i : Fin n) :
    Fin.append y z (i.addNat n)=z i := by
  rw [←Fin.natAdd_eq_addNat,Fin.append_right]

def duplicateLabels (n : ℕ) : Fin (n+n) → Fin n := Fin.append id id

theorem duplicateLabels_fiber_sum {n : ℕ} (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => duplicateLabels n i=r), w i)=w (r.castAdd n)+w (r.natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [duplicateLabels]

@[simp] theorem duplicateLabels_fiber_card {n : ℕ} (r : Fin n) :
    (Finset.univ.filter fun i => duplicateLabels n i=r).card=2 := by
  simpa using duplicateLabels_fiber_sum r (fun _ => (1:ℕ))

end LargePrimeGaps

end OAI
