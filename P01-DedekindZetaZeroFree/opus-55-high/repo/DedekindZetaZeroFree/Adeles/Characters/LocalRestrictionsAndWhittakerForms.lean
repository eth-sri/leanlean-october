module

public import DedekindZetaZeroFree.Adeles.Characters.AdditiveQuotient
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicRationalSplitting

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPInterface.ResidueConstruction.Raw
open NumberField IsDedekindDomain
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

variable (F : Type) [Field F] [NumberField F]

def actualLocalAdditive (v : KPHilbert.Place F) :
    KPHilbert.Completion F v →+ KPAdeles F where
  toFun := KPRationalAdelicSplitting.localAdele F v
  map_zero' := by
    cases v <;> apply Prod.ext <;> simp [KPRationalAdelicSplitting.localAdele]
  map_add' := by
    intro x y
    cases v with
    | inl w =>
      apply Prod.ext
      · change Pi.single w (x + y) = Pi.single w x + Pi.single w y
        exact Pi.single_add _ _ _
      · change (0 : FiniteAdeleRing (𝓞 F) F) = 0 + 0
        simp
    | inr q =>
      apply Prod.ext
      · change (0 : InfiniteAdeleRing F) = 0 + 0
        simp
      · exact RestrictedProduct.single_add _ _ _ _

theorem actualLocalAdditive_continuous (v : KPHilbert.Place F) :
    Continuous (actualLocalAdditive F v) := by
  cases v with
  | inl w =>
    change Continuous (fun x : w.Completion => (Pi.single w x, (0 : FiniteAdeleRing (𝓞 F) F)))
    fun_prop
  | inr q =>
    let s : Set (HeightOneSpectrum (𝓞 F)) := {q}ᶜ
    have hs : Filter.cofinite ≤ Filter.principal s :=
      Filter.le_principal_iff.mpr (Set.finite_singleton q).compl_mem_cofinite
    let f : q.adicCompletion F → RestrictedProduct (fun w => w.adicCompletion F)
        (fun w => (w.adicCompletionIntegers F : Set _)) (Filter.principal s) := fun x =>
      ⟨Pi.single q x, by
        intro w hw
        have hwq : w ≠ q := hw
        simp_all⟩
    have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
      (continuous_single q)
    exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hs).comp hf)

def actualLocalPsi (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (v : KPHilbert.Place F) : ContinuousAddChar (KPHilbert.Completion F v) where
  toAddChar := ψ.toAddChar.compAddMonoidHom
    ((QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)).comp
      (actualLocalAdditive F v))
  continuous_toFun := ψ.continuous_toFun.comp
    (QuotientAddGroup.continuous_mk.comp (actualLocalAdditive_continuous F v))
  unitary := fun x => ψ.unitary _

def actualLocalRoot (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : KPHilbert.Place F) :
    AddChar (KPHilbert.Completion F v) (KPPGLLocalCover.CubicPGL2 F ζ hζ v) where
  toFun := KPPGLLocalCover.N F ζ hζ v
  map_zero_eq_one' := by
    simp [KPPGLLocalCover.N, KPStandardLocalRootLifts.N_zero]
  map_add_eq_mul' := KPPGLLocalCover.N_add F ζ hζ v
