module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.Cubic.ForwardExceptionalImage

@[expose] public section

set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace DedekindZetaZeroFree.KPRankOneShellRepair.ActualSourcePredicates
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPLocalJacquetImage KPRankOneShellRepair
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

local instance plusAdd : AddCommGroup (sectionSpace S.borel P .plus 0) := inferInstance
local instance minusAdd : AddCommGroup (sectionSpace S.borel P .minus 0) := inferInstance

local instance reverseImageAdd :
    AddCommGroup (actualCanonicalReverseMap F ζ hζ q S P μ hμ).range.toSubmodule :=
  Submodule.addCommGroup _

private alias actual_simple_of_length_two := DedekindZetaZeroFree.KPRankOneShellRepair.ForwardExceptionalImage.simple_of_length_two

private theorem actual_irreducible_of_length_two {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V)
    (h : Module.length ℂ[G] ρ.asModule = 2) (S : Subrepresentation ρ)
    [Nontrivial S.toSubmodule] (hS : S ≠ ⊤) : S.toRepresentation.IsIrreducible := by
  let i : S.toRepresentation.IntertwiningMap ρ :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  let j := Representation.IntertwiningMap.equivLinearMapAsModule _ _ i
  have hj : Function.Injective j := Subtype.val_injective
  have hN : j.range ≠ ⊤ := by
    intro he
    apply hS
    apply top_unique
    intro v _
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp he v
    exact hx ▸ x.property
  letI : Nontrivial S.toRepresentation.asModule := inferInstanceAs (Nontrivial S.toSubmodule)
  letI : Nontrivial j.range := (LinearEquiv.ofInjective j hj).symm.toEquiv.nontrivial
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  apply Module.length_eq_one_iff.mp
  rw [(LinearEquiv.ofInjective j hj).length_eq]
  exact Module.length_eq_one_iff.mpr (actual_simple_of_length_two h j.range hN)

private theorem actual_image_simple {G V W : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap ρ)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hcomp : g.toLinearMap.comp f.toLinearMap = 0)
    (h : Module.length ℂ[G] σ.asModule = 2) :
    Nontrivial f.range.toSubmodule ∧ f.range.toRepresentation.IsIrreducible := by
  haveI : Nontrivial f.range.toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr (by
      exact fun he => (fun he => hf (Representation.IntertwiningMap.ext he)) (LinearMap.range_eq_bot.mp he))
  have hp : f.range ≠ ⊤ := by
    intro he
    apply hg
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    have hw : w ∈ f.range := by rw [he]; trivial
    obtain ⟨v, rfl⟩ := hw
    exact LinearMap.congr_fun hcomp v
  exact ⟨inferInstance, actual_irreducible_of_length_two σ h f.range hp⟩

theorem actual_images_irreducible_of_length :
    ActualImageAlgebra.NonzeroIrreducible (actualCanonicalForwardMap F ζ hζ q S P μ hμ) := by
  have hn := actual_zero_maps_nonzero F ζ hζ q S P μ hμ
  have hc := actual_zero_opposite_compositions F ζ hζ q S P μ hμ
  have hl := actual_principal_series_length_two F ζ hζ q S P
  exact actual_image_simple (IPlus S.borel P) (IMinus S.borel P) _ _ hn.1 hn.2 hc.2 hl.2

end DedekindZetaZeroFree.KPRankOneShellRepair.ActualSourcePredicates

end
