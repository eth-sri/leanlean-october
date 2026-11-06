module

public import PottsDiscontinuity.Potts.CylinderColoring

/-! Edwards–Sokal cylinder kernels as functions of finite observed partitions. -/

public section

namespace PottsDiscontinuity.Potts

noncomputable section

variable {A V C : Type*}

section
variable (R : Setoid V) (v : A → V) (ξ : A → C)

/-- The pinned colouring kernel depends only on the observed marked partition. -/
theorem pinnedClusterCylinderProbability_factor (g : V) (i : C) :
    pinnedClusterCylinderProbability R v ξ g i =
      pinnedClusterCylinderProbability (R.comap (markedMap v g)) some ξ none i := by
  have h : (R.comap (markedMap v g)).comap (markedMap some none) = R.comap (markedMap v g) := by
    apply Setoid.ext
    intro a b
    cases a <;> cases b <;> rfl
  grind [pinnedClusterCylinderProbability, observedClassCount]
end

end
end PottsDiscontinuity.Potts
