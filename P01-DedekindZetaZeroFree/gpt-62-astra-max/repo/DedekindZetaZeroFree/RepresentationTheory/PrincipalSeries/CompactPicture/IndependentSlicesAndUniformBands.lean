module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteHarmonicSampling

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct
namespace DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

def plusTensorEvaluation {ι : Type*} [Fintype ι] :
    PiTensorProduct ℂ (fun _ : ι => KPLiteralTensor.harmonicPlus) →ₗ[ℂ]
      ((ι → KPCplxCharacterHaar.ComplexGL2) → ℂ) :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ ι ((ι → KPCplxCharacterHaar.ComplexGL2) → ℂ)).compLinearMap
      (fun i =>
        { toFun := fun f a => f.val (a i)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }))

@[simp] theorem plusTensorEvaluation_pure {ι : Type*} [Fintype ι]
    (f : ι → KPLiteralTensor.harmonicPlus)
    (a : ι → KPCplxCharacterHaar.ComplexGL2) :
    plusTensorEvaluation (PiTensorProduct.tprod ℂ f) a = ∏ i, (f i).val (a i) := by
  simp [plusTensorEvaluation]

end DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices

end

end

section

noncomputable section
set_option maxHeartbeats 800000
open scoped Topology Classical
namespace DedekindZetaZeroFree.KPLiteralScalarArchUniformBands
open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open KPLiteralScalarArchIndependentSlices

def multiPrincipalSeries (s : ℝ) (ι : Type*) [DecidableEq ι] :
    Submodule ℂ ((ι → KPCplxCharacterHaar.ComplexGL2) → ℂ) where
  carrier := {h | ∀ i a, (fun x => h (Function.update a i x)) ∈ principalSeriesSubmodule s}
  zero_mem' := by intro i a; exact (principalSeriesSubmodule s).zero_mem
  add_mem' := by intro f g hf hg i a; exact (principalSeriesSubmodule s).add_mem (hf i a) (hg i a)
  smul_mem' := by intro c f hf i a; exact (principalSeriesSubmodule s).smul_mem c (hf i a)

section

variable (s : ℝ) {ι : Type*} [DecidableEq ι]

def evaluateSlice (i : ι)
    (a : ι → KPCplxCharacterHaar.ComplexGL2) :
    multiPrincipalSeries s ι →ₗ[ℂ] PrincipalSeries s where
  toFun h := ⟨fun x => h.val (Function.update a i x), h.property i a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def multiTranslate
    (k : ι → KPCplxCharacterHaar.ComplexSU2) :
    multiPrincipalSeries s ι →ₗ[ℂ] multiPrincipalSeries s ι where
  toFun h := ⟨fun a => h.val (fun j => a j * KPCplxCharacterHaar.complexSU2Embedding (k j)), by
    intro i a
    let b := fun j => a j * KPCplxCharacterHaar.complexSU2Embedding (k j)
    have heq : (fun x => h.val (fun j => (Function.update a i x) j *
        KPCplxCharacterHaar.complexSU2Embedding (k j))) =
        (KPCplxPrincipalSeriesCharts.rightTranslate s (KPCplxCharacterHaar.complexSU2Embedding (k i))
          (evaluateSlice s i b h)).val := by
      funext x
      apply congrArg h.val
      funext j
      by_cases hj : j = i
      · subst j; simp [b]
      · simp [Function.update_of_ne hj, b]
    rw [heq]
    exact (KPCplxPrincipalSeriesCharts.rightTranslate s _ _).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem multiTranslate_mul
    (k l : ι → KPCplxCharacterHaar.ComplexSU2) (h : multiPrincipalSeries s ι) :
    multiTranslate s k (multiTranslate s l h) = multiTranslate s (k * l) h := by
  apply Subtype.ext
  funext a
  apply congrArg h.val
  funext j
  simp [mul_assoc]

theorem slice_slot_translate
    (i : ι) (a : ι → KPCplxCharacterHaar.ComplexGL2)
    (k : KPCplxCharacterHaar.ComplexSU2) (h : multiPrincipalSeries s ι) :
    evaluateSlice s i a (multiTranslate s (Function.update (fun _ => 1) i k) h) =
      KPCplxPrincipalSeriesCharts.pi s (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k))
        (evaluateSlice s i a h) := by
  apply Subtype.ext
  funext x
  apply congrArg h.val
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [Function.update_of_ne hj]

end

 theorem harmonicBand_mono (s : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    harmonicBand s N ≤ harmonicBand s M := by
  apply Finset.sup_le
  intro ℓ hℓ
  exact Finset.le_sup ((Finset.range_mono (Nat.add_le_add_right hNM 1)) hℓ)

end DedekindZetaZeroFree.KPLiteralScalarArchUniformBands

end

end
