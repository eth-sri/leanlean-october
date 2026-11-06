module
public import OAI.NumberTheory.DirichletL.Moments.SmoothedRetainedSource
public import OAI.NumberTheory.DirichletL.Moments.SecondLiveEnergy
public import OAI.NumberTheory.DirichletL.Moments.RestrictedSourceNormalization
public import OAI.NumberTheory.DirichletL.Moments.SourceRectangle
public import OAI.NumberTheory.DirichletL.Moments.CommonRawScale

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalRetainedSource
open CenteredMomentFirstSectors

open CenteredMomentSourceRectangle



open CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform

open scoped EisensteinO
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem live_residual_pool (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) (i : liveIndices B) :
    residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val))=S (Sum.inl i.val) := by
  ext I
  rw [mem_residualPool,(Finset.mem_filter.mp i.property).2,one_mul]

omit [DecidableEq ι] in
theorem liveBox_original_pools (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) :
    liveBox S B hB=tuplePool (fun i:liveIndices B=>S (Sum.inl i.val))
      (residualPool (B (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (S (Sum.inr 1))) := by
  rw [liveBox_eq_tuplePool]
  simp_rw [live_residual_pool]







