module

public import OAI.NumberTheory.DirichletL.Hecke.PrincipalResidue
public import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
public import OAI.NumberTheory.DirichletL.Detector.RadialMellin
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrincipalNormalizer
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
local notation "O" => HeckeFamily.O

theorem sourceResidueConstant_positive (M : Ideal O) [NeZero M]
    (mw : MellinWindows)
    (hreal0 : ∀y,(mw.left y).im=0) (hreal1 : ∀y,(mw.right y).im=0)
    (hpos0 : ∀y,0≤(mw.left y).re) (hpos1 : ∀y,0≤(mw.right y).re) (hne0 : mw.left≠0) (hne1 : mw.right≠0) :
    ∃c : ℝ,0<c ∧ sourceResidueConstant mw.left mw.right M=(c:ℂ) := by
  obtain ⟨hp0,hi0⟩ := ProbeRadialMellin.radial_mellin_one_sixth_pos mw.left mw.leftLo mw.leftHi mw.left_pos mw.left_support hreal0 hpos0 hne0
  obtain ⟨hp1,hi1⟩ := ProbeRadialMellin.positive_source_mellin mw.right mw.rightLo mw.rightHi mw.right_pos mw.right_support hreal1 hpos1 hne1 1
  obtain ⟨R,hR,hres⟩ := HeckePrincipalResidue.fixed_principal_residue_positive M
  have hr : fixedPrincipalResidue M=(R:ℂ) := by
    rw [fixedPrincipalResidue,←HeckeOrigin.poleRemoved_one]
    exact hres
  have he0 : mellin (EisensteinSchwartzPoisson.paperRadialFourier mw.left) (1/6)=
      ((mellin (EisensteinSchwartzPoisson.paperRadialFourier mw.left) (1/6)).re:ℂ) :=
    Complex.ext (by simp) (by simpa using hi0)
  have he1 : mellin mw.right 1=((mellin mw.right 1).re:ℂ) :=
    Complex.ext (by simp) (by simpa using hi1)
  refine ⟨(mellin mw.right 1).re*(mellin (EisensteinSchwartzPoisson.paperRadialFourier mw.left) (1/6)).re*R^2/6,?_,?_⟩
  · norm_num only [Complex.ofReal_one] at hp1
    positivity
  · unfold sourceResidueConstant
    rw [he0,he1,hr]
    push_cast
    rfl

theorem sourceResidueConstant_ne_zero (M : Ideal O) [NeZero M]
    (mw : MellinWindows)
    (hreal0 : ∀y,(mw.left y).im=0) (hreal1 : ∀y,(mw.right y).im=0)
    (hpos0 : ∀y,0≤(mw.left y).re) (hpos1 : ∀y,0≤(mw.right y).re) (hne0 : mw.left≠0) (hne1 : mw.right≠0) :
    sourceResidueConstant mw.left mw.right M≠0 := by
  obtain ⟨c,hc,he⟩ := sourceResidueConstant_positive M mw
    hreal0 hreal1 hpos0 hpos1 hne0 hne1
  rw [he]
  exact Complex.ofReal_ne_zero.mpr hc.ne'

theorem signed_source_normalizer_ne_zero {κ ι : Type*} [DecidableEq κ]
    (M : Ideal O) [NeZero M] (mw : MellinWindows)
    (hreal0 : ∀y,(mw.left y).im=0) (hreal1 : ∀y,(mw.right y).im=0)
    (hpos0 : ∀y,0≤(mw.left y).re) (hpos1 : ∀y,0≤(mw.right y).re) (hne0 : mw.left≠0) (hne1 : mw.right≠0)
    (S : Finset κ) (T : κ→Finset ι) (w : κ→ι→ℝ) (Z ℓ : ℝ) (hZ : 0<Z)
    (hm : ∀j∈S,0<slotMass T w j) :
    sourceResidueConstant mw.left mw.right M*(Probe.principalScalar S Z ℓ (slotMass T w):ℂ)≠0 :=
  mul_ne_zero (sourceResidueConstant_ne_zero M mw
    hreal0 hreal1 hpos0 hpos1 hne0 hne1) (source_normalizer_ne_zero S T w hZ hm)

end SevenEighths.ProbePrincipalNormalizer
end

end OAI
