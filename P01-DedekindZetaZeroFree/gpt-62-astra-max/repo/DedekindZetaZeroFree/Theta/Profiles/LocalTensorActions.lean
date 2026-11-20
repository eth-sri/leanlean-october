module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField IsDedekindDomain
open DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts
open DedekindZetaZeroFree.KPCplxActualImage
open DedekindZetaZeroFree.KPCplxIntertwinerEigenvalues

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction

variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

section

variable (s : ℝ) (g : KPCplxCharacterHaar.ComplexPGL2)

theorem pi_zero :
    KPCplxPrincipalSeriesCharts.pi s g
      (0 : KPCplxPrincipalSeriesCharts.PrincipalSeries s) = 0 := by
  induction g using Quotient.inductionOn with
  | _ g =>
    apply Subtype.ext
    rfl

theorem pi_add
    (f h : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.pi s g (f + h) =
      KPCplxPrincipalSeriesCharts.pi s g f +
        KPCplxPrincipalSeriesCharts.pi s g h := by
  induction g using Quotient.inductionOn with
  | _ g =>
    apply Subtype.ext
    rfl

theorem pi_smul
    (c : ℂ) (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.pi s g (c • f) =
      c • KPCplxPrincipalSeriesCharts.pi s g f := by
  induction g using Quotient.inductionOn with
  | _ g =>
    apply Subtype.ext
    rfl

end

section

variable (k : KPCplxCharacterHaar.ComplexSU2)

theorem complexCore_compact_mem
    (x : KPCplxPrincipalSeriesCharts.PrincipalSeries
      KPCplxPrincipalSeriesCharts.negativeParameter)
    (hx : x ∈ complexCore) :
    KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.negativeParameter
      (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k)) x ∈
        complexCore := by
  have hmem : x ∈ ⨆ ℓ : ℕ,
      KPCplxIntertwinerEigenvalues.harmonicKType
        KPCplxPrincipalSeriesCharts.negativeParameter ℓ := by
    have h := hx
    rw [show complexCore = KPCplxActualImage.imageSubmodule (1 : ℂˣ) ⊓
        ⨆ ℓ : ℕ, KPCplxIntertwinerEigenvalues.harmonicKType
          KPCplxPrincipalSeriesCharts.negativeParameter ℓ from rfl,
      KPCplxActualImage.imageSubmodule_eq_top, top_inf_eq] at h
    exact h
  rw [show complexCore = KPCplxActualImage.imageSubmodule (1 : ℂˣ) ⊓
      ⨆ ℓ : ℕ, KPCplxIntertwinerEigenvalues.harmonicKType
        KPCplxPrincipalSeriesCharts.negativeParameter ℓ from rfl,
    KPCplxActualImage.imageSubmodule_eq_top, top_inf_eq]
  let g := Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k)
  have hg : g ∈ KPCplxPrincipalSeriesCharts.compactSubgroup := ⟨k, rfl⟩
  refine Submodule.iSup_induction (fun ℓ : ℕ =>
      KPCplxIntertwinerEigenvalues.harmonicKType
        KPCplxPrincipalSeriesCharts.negativeParameter ℓ) hmem
    (motive := fun y => KPCplxPrincipalSeriesCharts.pi
      KPCplxPrincipalSeriesCharts.negativeParameter g y ∈ ⨆ ℓ : ℕ,
        KPCplxIntertwinerEigenvalues.harmonicKType
          KPCplxPrincipalSeriesCharts.negativeParameter ℓ) (fun ℓ y hy => ?_) ?_ ?_
  · exact Submodule.mem_iSup_of_mem ℓ
      ((KPCplxIntertwinerEigenvalues.harmonicKType_multiplicity_one
        KPCplxPrincipalSeriesCharts.negativeParameter ℓ).1 ⟨g, hg⟩ y hy)
  · rw [pi_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    rw [pi_add]
    exact Submodule.add_mem _ hy hz

def complexCoreCompactAction
    (x : complexCore) : complexCore :=
  ⟨KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.negativeParameter
    (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k)) x.val,
    complexCore_compact_mem k x.val x.property⟩

@[simp] theorem complexCoreCompactAction_coe
    (x : complexCore) :
    (complexCoreCompactAction k x).val =
      KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.negativeParameter
        (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k)) x.val := rfl

def complexCoreCompactLinearMap :
    complexCore →ₗ[ℂ] complexCore where
  toFun := fun x => complexCoreCompactAction k x
  map_add' := by
    intro x y
    apply Subtype.ext
    simp only [complexCoreCompactAction_coe, Submodule.coe_add]
    rw [pi_add]
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp only [complexCoreCompactAction_coe, SetLike.val_smul]
    rw [pi_smul]
    rfl

end

def complexCoreSU2Action : Representation ℂ KPCplxCharacterHaar.ComplexSU2 complexCore where
  toFun k := complexCoreCompactLinearMap k
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.negativeParameter
      (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding 1)) x.val = x.val
    rw [KPCplxCharacterHaar.complexSU2Embedding.map_one,
      Matrix.ProjGenLinGroup.mk_one, pi_one]
  map_mul' := by
    intro k l
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.negativeParameter
        (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (k * l))) x.val
      = KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.negativeParameter
        (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k))
        (KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.negativeParameter
          (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding l)) x.val)
    rw [KPCplxCharacterHaar.complexSU2Embedding.map_mul, map_mul, pi_mul]

end DedekindZetaZeroFree.KPGlobalResidualConstruction

end
