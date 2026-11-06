module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorRealizations

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
local notation "KPFinitePlace" F => HeightOneSpectrum (𝓞 F)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.TorusReference
open KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

theorem localReference_one (q : KPFinitePlace F) :
    (localReference F ζ hζ P C q).val 1 = 1 := by
  simp only [localReference, map_one]
  simp only [Subgroup.one_mem, dite_true]
  change (((C.polarization q).ωL 1 : ℂˣ) : ℂ) = 1
  rw [map_one, Units.val_one]




























end DedekindZetaZeroFree.EisensteinReferenceSections.TorusReference

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
local notation "KPFinitePlace" F => HeightOneSpectrum (𝓞 F)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.TorusReference
open KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

theorem localReference_ne_zero (q : KPFinitePlace F) :
    localReference F ζ hζ P C q ≠ 0 := by
  intro h
  have he := congrArg (fun v : LocalFiber F ζ hζ P C q => v.val 1) h
  rw [localReference_one] at he
  exact one_ne_zero he

end DedekindZetaZeroFree.EisensteinReferenceSections.TorusReference

end
end
