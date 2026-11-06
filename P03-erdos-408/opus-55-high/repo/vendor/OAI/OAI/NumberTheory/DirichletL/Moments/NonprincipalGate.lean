module

public import OAI.NumberTheory.DirichletL.Moments.SecondReducedPredicate

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentNonprincipalGate
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open ConcretePrimeRowBridge

def unitCharacter : Character := Character.ofResidue ⊤ top_ne_bot 1 (by
  intro u
  exact MulChar.one_apply (IsUnit.map (Ideal.Quotient.mk ⊤) u.isUnit))

theorem unitCharacter_primitive : FiniteFourier.IsPrimitiveOnIdeals unitCharacter.residue := by
  change FiniteFourier.IsPrimitiveOnIdeals (1:MulChar (HeckeFamily.O⧸(⊤:Ideal HeckeFamily.O)) ℂ)
  intro I hI
  exact (hI (Subsingleton.elim _ _)).elim

theorem unitCharacter_ideal (I:Ideal HeckeFamily.O) (hI:I≠0) : idealCoeff unitCharacter I=1 := by
  rw [←span_idealGenerator I,idealCoeff_span _ (idealGenerator_ne_zero I hI)]
  change (1:MulChar (HeckeFamily.O⧸(⊤:Ideal HeckeFamily.O)) ℂ) (Ideal.Quotient.mk _ (idealGenerator I))=1
  rw [show Ideal.Quotient.mk (⊤:Ideal HeckeFamily.O) (idealGenerator I)=1 from Subsingleton.elim _ _]
  simp

theorem principal_inducedBy_unit (χ:Character) (hχ:χ.residue=1) : InducedBy χ unitCharacter := by
  intro I
  by_cases hI:I=0
  · grind
  · have hn:=idealGenerator_ne_zero I hI
    rw [unitCharacter_ideal I hI]
    rw [←span_idealGenerator I,idealCoeff_span χ hn]
    change χ.residue (Ideal.Quotient.mk χ.modulus (idealGenerator I))=_
    rw [hχ]
    by_cases hc:IsCoprime (Ideal.span {idealGenerator I}) χ.modulus
    · rw [ite_eq_left hc]
      exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hc)
    · rw [ite_eq_right hc]
      exact MulChar.map_nonunit _ (fun h=>hc ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp h))

theorem principal_row_fixed (η χ:Character) (Q:Ideal HeckeFamily.O) (m A z:HeckeFamily.O)
    (hrow:∀n:HeckeFamily.O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hχ:χ.residue=1) : FixedInducingRow η Q m A z :=
  ⟨χ,unitCharacter,unitCharacter_primitive,principal_inducedBy_unit χ hχ,le_top,hrow⟩

theorem actual_row_nonprincipal (η χ:Character) (Q:Ideal HeckeFamily.O) (m A z:HeckeFamily.O)
    (hrow:∀n:HeckeFamily.O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hex:¬FixedInducingRow η Q m A z) : χ.residue≠1 :=
  fun h=>hex (principal_row_fixed η χ Q m A z hrow h)

end SevenEighths.CenteredMomentNonprincipalGate

end

end OAI
