/- Canonical representatives of common occurrences in the two literal faces. -/
module

public import VaughtConjecture.Knight.SchemeBoundaryFaceMap
public import VaughtConjecture.Knight.CappedDonorFace

@[expose] public section

namespace VaughtConjecture.Knight.SemSchemeBoundaryInput

open CappedDonor

noncomputable section

section

variable {m n : ℕ} (D : SemScheme n) (F : SemScheme m) (f : Fin m ↪ Fin n)
  (hv : Finset.univ.image f ∈ D.scheme.plan) (hf : D.restrictFace f hv = F)

def faceBelow (d : Cell F.scheme) : D.scheme.below (Finset.univ.image f, m) :=
  bC (C := D) f hv m (castBelow hf.symm (Finset.univ, m) ⟨d, Finset.subset_univ _,
    (F.scheme.grade_le_card_scope d).trans (by simpa using Finset.card_le_univ (F.scheme.scope d))⟩)

theorem faceBelow_val (d : Cell F.scheme) :
    (faceBelow D F f hv hf d).1 = faceMap D F f hv hf d := by
  subst F
  rfl

end

theorem commonFace_faceBelow {m nP J : ℕ} {P : SemScheme (nP + 1)}
    {C : SemScheme J} {F : SemScheme m}
    (f : Fin m ↪ Fin (nP + 1)) (hf : Finset.univ.image f ∈ P.scheme.plan) (he : P.restrictFace f hf = F)
    (g : Fin m ↪ Fin J) (hg : Finset.univ.image g ∈ C.scheme.plan) (hd : C.restrictFace g hg = F)
    (d : Cell F.scheme) :
    commonFace f hf he g hg hd m (faceBelow P F f hf he d) = faceBelow C F g hg hd d := by
  unfold faceBelow
  rw [commonFace_apply, Equiv.symm_apply_apply]
  erw [castBelow_castBelow_symm]

end

end VaughtConjecture.Knight.SemSchemeBoundaryInput
