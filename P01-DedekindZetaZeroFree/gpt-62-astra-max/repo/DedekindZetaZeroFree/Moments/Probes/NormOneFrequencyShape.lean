module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormOneFourierSheetEstimates

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

namespace ProbePoissonSheet
variable {F : Type} [Field F] [NumberField F]

local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _

local instance (A : SArithmeticData F) : BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _

local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

variable (A : SArithmeticData F)

def principalNorm (h : A.R) : ℝ :=
  (Nat.card (A.R ⧸ Ideal.span ({h} : Set A.R)) : ℝ)

def fieldUnit (h : A.R) (hh : h ≠ 0) : Fˣ :=
  Units.mk0 (h : F) (by exact_mod_cast hh)

def frequency (X : ℝ) (s a h : A.R) :
    SLocalProduct F A.Sf :=
  (ProbeSheet.ell A (principalNorm A s * X)).val *
    sLocalDiagonal F A.Sf ((h : F) / ((s : F) * (a : F)))

theorem principalNorm_eq_modulus (h : A.R) (hh : h ≠ 0) :
    principalNorm A h = A.norm (A.diagonal (fieldUnit A h hh)) ∧
    0 < principalNorm A h := by
  let J : {J : Ideal A.R // J ≠ ⊥} :=
    ⟨Ideal.span {h}, Ideal.span_singleton_eq_bot.not.mpr hh⟩
  let I := A.exteriorIdealEquiv.symm J
  have hI : A.extendIdeal I = Ideal.span {h} := by
    rw [← A.exteriorIdealEquiv_apply I]
    exact congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply J)
  have hnorm : principalNorm A h = A.exteriorNorm I := by
    unfold principalNorm
    rw [← hI, A.exteriorResidue_card]
    rfl
  rw [hnorm]
  exact ⟨(A.generator_norm I h (⟨hh, hI.symm⟩) (fieldUnit A h hh) (rfl)).symm,
    A.exteriorNorm_pos I⟩

end ProbePoissonSheet

end
end DedekindZetaZeroFree
