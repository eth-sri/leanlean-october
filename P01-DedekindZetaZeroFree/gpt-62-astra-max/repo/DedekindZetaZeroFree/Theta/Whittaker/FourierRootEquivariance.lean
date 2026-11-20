module

public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteWeylPeriods

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

theorem core_rational_root {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)
    (x : RestrictedTensorSimple.Core (actualLocal R C.factorization.finiteData)
      C.factorization.references C.factorization.bad) (t : F) (g : Group R) :
    C.factorization.coreMap x
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (algebraMap F (KPAdeles F) t) * g) = C.factorization.coreMap x g := by
  rw [← KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact (C.factorization.core_same_residue x).2.2.1 _ _

alias fourier_left_root := DedekindZetaZeroFree.ExteriorWhittakerValues.StoredWhittaker.fourier_left_root

alias finite_root_injection := DedekindZetaZeroFree.ExteriorWhittakerValues.StoredWhittaker.finite_root_injection

theorem selected_ell_root {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)
    (v : R.A.UnitQuotient) (s : RestrictedTensorSimple.Level C.factorization.bad)
    (x : ∀ p : s.val, actualLocal R C.factorization.finiteData p)
    (hx : C.factorization.selected v = RestrictedTensorSimple.stageInclusion _
      C.factorization.references C.factorization.bad s (PiTensorProduct.tprod ℂ x))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (t : q.adicCompletion F) (b : actualLocal R C.factorization.finiteData (Sum.inr q)) :
    C.factorization.ell (Sum.inr q)
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
        R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
        (C.factorization.finiteData q).inducing.polarization
        (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
        (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) b) =
      (adelicTraceQuotientCharacter F (QuotientAddGroup.mk
        (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t)) : ℂ) *
        C.factorization.ell (Sum.inr q) b := by
  let i : s.val := ⟨Sum.inr q, hq⟩
  let y := Function.update x i b
  let core := RestrictedTensorSimple.stageInclusion _ C.factorization.references
    C.factorization.bad s (PiTensorProduct.tprod ℂ y)
  letI := C.sources.quotientHaar
  have hf := fourier_left_root R C.sources.dq (C.factorization.coreMap core)
    (core_rational_root R C core)
    (KPRationalAdelicSplitting.localAdele F (Sum.inr q) t) 1
    (by simpa only [mul_one] using C.factorization.product_integrable s y)
  rw [mul_one, ← finite_root_injection R] at hf
  rw [finite_translate_period R C s y q hq,
    C.factorization.product_exact] at hf
  have hu := dependent_prod_update (fun p : s.val => C.factorization.ell p) y i
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
      R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
      (C.factorization.finiteData q).inducing.polarization
      (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
      (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) t) (y i))
  dsimp only [i, KPPGLLocalCover.N] at hu
  rw [hu] at hf
  have hyprod : (∏ p : s.val, C.factorization.ell p (y p)) =
      C.factorization.ell (Sum.inr q) b * ∏ p ∈ Finset.univ.erase i, C.factorization.ell p (y p) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [y, Function.update_self]
    rfl
  rw [hyprod] at hf
  have hrest : (∏ p ∈ Finset.univ.erase i, C.factorization.ell p (y p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    dsimp [y]
    rw [Function.update_of_ne (Finset.mem_erase.mp hp).1]
    exact selected_tensor_nonzero R C v s x hx p
  change _ * (∏ p ∈ Finset.univ.erase i, C.factorization.ell p (y p)) =
    _ * (_ * (∏ p ∈ Finset.univ.erase i, C.factorization.ell p (y p))) at hf
  rw [← mul_assoc] at hf
  have hh := mul_right_cancel₀ hrest hf
  simpa only [y, i, Function.update_self, KPPGLLocalCover.N] using hh

end DedekindZetaZeroFree.SheetRescaling

end
