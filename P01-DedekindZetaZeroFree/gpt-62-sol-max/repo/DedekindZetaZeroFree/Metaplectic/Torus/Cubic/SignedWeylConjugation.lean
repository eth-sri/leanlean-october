module

public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.CenterCharacterPolarization
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OpenCellKernel

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualFiniteBorel.Geometry
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
local notation "K" => q.adicCompletion F
local notation "v" => Sum.inr q
export DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.SignedBlockAlgebra.WeylAux (signedW_conjugates_A)

theorem signedW_conjugates_normalWord (e : rootsOfUnity 3 F) (y : Kˣ) :
    (KPPGLLocalCover.signedW F ζ hζ v)⁻¹ * ActualFiniteTorus.normalWord F ζ hζ q e y *
      KPPGLLocalCover.signedW F ζ hζ v = ActualFiniteTorus.normalWord F ζ hζ q e y⁻¹ := by
  have hc := Subgroup.mem_center_iff.mp
    (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ v ⟨e, rfl⟩)
    ((KPPGLLocalCover.signedW F ζ hζ v)⁻¹)
  unfold ActualFiniteTorus.normalWord
  rw [← mul_assoc, hc, mul_assoc, mul_assoc, ← mul_assoc
    ((KPPGLLocalCover.signedW F ζ hζ v)⁻¹), signedW_conjugates_A]

theorem signedW_preserves_torus (t : ActualFiniteTorus.H F ζ hζ q) :
    (KPPGLLocalCover.signedW F ζ hζ v)⁻¹ * t.val * KPPGLLocalCover.signedW F ζ hζ v ∈
      ActualFiniteTorus.H F ζ hζ q := by
  rw [(ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.1 t,
    signedW_conjugates_normalWord]
  exact (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).1 _ _

end
end DedekindZetaZeroFree.ActualFiniteBorel.Geometry
