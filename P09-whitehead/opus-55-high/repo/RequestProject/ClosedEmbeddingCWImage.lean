import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.ContinuousOn
import RequestProject.ExplicitRelativeAttachment


/-! Transport an existing classical CW structure onto its actual closed
embedded image. The cell indices and all characteristic maps are retained.
This applies in particular to the literal old-space inclusion in an
attachment. Pending Lean verification.
-/

noncomputable section
open scoped Classical
open Set Topology Metric

namespace FiniteChains.ClosedEmbeddingCW

universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
  [CWComplex (Set.univ : Set X)] (f : X → Y) (hf : IsClosedEmbedding f)

def basePartial :=
  hf.injective.injOn.toPartialEquiv f Set.univ

def imageCharacteristic (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n) :=
  (RelCWComplex.map (C := (Set.univ : Set X)) n j).trans (basePartial f hf)

theorem imageCharacteristic_image n
    j S :
    imageCharacteristic f hf n j '' S =
      f '' (RelCWComplex.map (C := Set.univ) n j '' S) := by
  aesop

theorem imageCharacteristic_source n
    j :
    (imageCharacteristic f hf n j).source = ball 0 1 := by
  change (RelCWComplex.map (C := Set.univ) n j).source ∩
    (RelCWComplex.map (C := Set.univ) n j) ⁻¹' Set.univ = _
  simp [Set.preimage_univ, Set.inter_univ, RelCWComplex.source_eq]

theorem imageCharacteristic_continuousOn n
    j :
    ContinuousOn (imageCharacteristic f hf n j) (closedBall 0 1) :=
  hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n j)

theorem imageCharacteristic_continuousOn_symm n
    j :
    ContinuousOn (imageCharacteristic f hf n j).symm
      (imageCharacteristic f hf n j).target := by
  rw [imageCharacteristic, PartialEquiv.trans_target'']
  change ContinuousOn
    ((RelCWComplex.map (C := Set.univ) n j).symm ∘ (basePartial f hf).symm)
    (f '' (Set.univ ∩ (RelCWComplex.map (C := Set.univ) n j).target))
  rw [Set.univ_inter]
  apply hf.isEmbedding.isInducing.continuousOn_image_iff.mpr
  have he : ((RelCWComplex.map (C := Set.univ) n j).symm ∘
      (basePartial f hf).symm) ∘ f =
      (RelCWComplex.map (C := Set.univ) n j).symm := by
    funext x
    exact congrArg _
      ((basePartial f hf).left_inv (by tauto))
  rw [he]
  exact RelCWComplex.continuousOn_symm n j

variable [T2Space X]

end FiniteChains.ClosedEmbeddingCW

namespace FiniteChains.RelativeAttachment

universe u
variable {A X D : Type u} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace D]
  [T2Space X] [Nonempty X] [CWComplex (Set.univ : Set X)]
