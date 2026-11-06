import Mathlib.Tactic

import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.ContinuousOn
import RequestProject.ExplicitRelativeAttachment

/-! Transport an existing classical CW structure onto its actual closed
embedded image. The cell indices and all characteristic maps are retained.
This applies in particular to the literal old-space inclusion in an
attachment. Pending Lean verification.
-/

noncomputable section

open Set Topology Metric

namespace FiniteChains.ClosedEmbeddingCW

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
  [CWComplex (Set.univ : Set X)] (f : X → Y) (hf : IsClosedEmbedding f)

def basePartial  :=
  hf.injective.injOn.toPartialEquiv f Set.univ

variable (n : ℕ)
  (j : RelCWComplex.cell (Set.univ : Set X) n)
def imageCharacteristic    :=
  (RelCWComplex.map (C := (Set.univ : Set X)) n j).trans (basePartial f hf)

theorem imageCharacteristic_image 
     (S : Set (Fin n → ℝ)) :
    imageCharacteristic f hf n j '' S =
      f '' (RelCWComplex.map (C := (Set.univ : Set X)) n j '' S) := by
  aesop

theorem imageCharacteristic_source 
     :
    (imageCharacteristic f hf n j).source = ball 0 1 := by
  rw [imageCharacteristic, PartialEquiv.trans_source]
  change (RelCWComplex.map (C := (Set.univ : Set X)) n j).source ∩
    (RelCWComplex.map (C := (Set.univ : Set X)) n j) ⁻¹' Set.univ = _
  simp [RelCWComplex.source_eq]

theorem imageCharacteristic_continuousOn 
     :
    ContinuousOn (imageCharacteristic f hf n j) (closedBall 0 1) :=
  hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n j)

theorem imageCharacteristic_continuousOn_symm 
     :
    ContinuousOn (imageCharacteristic f hf n j).symm
      (imageCharacteristic f hf n j).target := by
  rw [imageCharacteristic, PartialEquiv.trans_target'']
  change ContinuousOn
    ((RelCWComplex.map (C := (Set.univ : Set X)) n j).symm ∘ (basePartial f hf).symm)
    (f '' (Set.univ ∩ (RelCWComplex.map (C := (Set.univ : Set X)) n j).target))
  rw [Set.univ_inter]
  apply hf.isEmbedding.isInducing.continuousOn_image_iff.mpr
  have he : ((RelCWComplex.map (C := (Set.univ : Set X)) n j).symm ∘
      (basePartial f hf).symm) ∘ f =
      (RelCWComplex.map (C := (Set.univ : Set X)) n j).symm := by
    funext x
    exact congrArg (RelCWComplex.map (C := (Set.univ : Set X)) n j).symm
      ((basePartial f hf).left_inv (show x ∈ (basePartial f hf).source from trivial))
  rw [he]
  exact RelCWComplex.continuousOn_symm n j



end FiniteChains.ClosedEmbeddingCW







