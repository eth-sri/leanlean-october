module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteIntersectionCharacterAdjustment

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

export ProductPolarization (D E LocalD localCoverTopology diagonalHom localOrdinaryTorus localTorus
  LocalE localRatioValue localRatioValue_eq localRatioValue_one localRatioValue_mul localRatio
  localProjection localCenter exists_local_omega localOmega localOmega_raw_formula IsMaximalIsotropic
  localPreimage LocalPolarization IsUnramified CompatibleLocalData restrictedM M pD B J
  localPairingHom FiniteAdjustment adjustedLocalValue rawB raw_coordinate_mem rawCoordinate rawProduct)

export ProductPolarization.FiniteAdjustmentSupport (adjustedLocalValue_outside rawCoordinate_val
  rawProduct_finiteSupport rawProduct_one rawProduct_mul rawProductHom rawProduct_continuous
  rawProduct_productOne rawProduct_splitScalar B_has_raw_lift lambdaValue lambdaValue_raw_formula
  lambdaValue_one lambdaValue_mul lambdaValue_continuous lambdaB M_compact_open J_finite)

attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology localCoverTopology

alias M_maximal_isotropic := ProductPolarization.product_maximal_isotropic

alias exists_compatible_local_data := ProductPolarization.compatible_local_choices

theorem B_maximal_abelian (P : CompatibleLocalData F ζ hζ) :
    KPLocalPolarization.IsMaximalAbelian (B F ζ hζ P) := by
  exact (ProductPolarization.product_polarization F ζ hζ P).1

theorem B_closed (P : CompatibleLocalData F ζ hζ) :
    IsClosed (B F ζ hζ P : Set (E F ζ hζ)) := by
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hB := B_maximal_abelian F ζ hζ P
  letI : CommGroup (B F ζ hζ P) :=
    { (inferInstance : Group (B F ζ hζ P)) with
      mul_comm := fun x y => Subtype.ext (hB.1 x x.property y y.property).eq }
  letI := (B F ζ hζ P).commGroupTopologicalClosure
    (fun x y => mul_comm x y)
  have hc : (B F ζ hζ P).topologicalClosure = B F ζ hζ P := by
    apply hB.2 _ (B F ζ hζ P).le_topologicalClosure
    intro x hx y hy
    exact show Commute x y from
      (congrArg Subtype.val (mul_comm
        (⟨x, hx⟩ : (B F ζ hζ P).topologicalClosure) ⟨y, hy⟩))
  rw [← hc]
  exact (B F ζ hζ P).isClosed_topologicalClosure

theorem center_le_B (P : CompatibleLocalData F ζ hζ) :
    KPGlobalCenterRationalCharacter.Z F ζ hζ ≤ B F ζ hζ P := by
  have hB := B_maximal_abelian F ζ hζ P
  let C := B F ζ hζ P ⊔ KPGlobalCenterRationalCharacter.Z F ζ hζ
  have hcomm : ∀ x ∈ C, ∀ y ∈ C, Commute x y := by
    intro x hx y hy
    obtain ⟨bx, hbx, zx, hzx, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨cy, hcy, zy, hzy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have h1 : Commute bx zy := Subgroup.mem_center_iff.mp hzy bx
    have h2 : Commute zx cy := (Subgroup.mem_center_iff.mp hzx cy).symm
    have h3 : Commute zx zy := Subgroup.mem_center_iff.mp hzy zx
    exact ((hB.1 bx hbx cy hcy).mul_right h1).mul_left (h2.mul_right h3)
  have hCB : C = B F ζ hζ P := hB.2 C le_sup_left hcomm
  rw [← hCB]
  exact le_sup_right

theorem rational_intersection_preimage (P : CompatibleLocalData F ζ hζ) :
    KPGlobalCenterRationalCharacter.R F ζ hζ ⊓ B F ζ hζ P =
      (J F ζ hζ P).comap (pD F ζ hζ) := by
  rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage]
  rfl

theorem lambdaB_extends_center (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (b : B F ζ hζ P)
    (z : KPGlobalCenterRationalCharacter.Z F ζ hζ) (hz : b.val = z.val) :
    lambdaB F ζ hζ P T b = KPGlobalCenterRationalCharacter.omegaA F ζ hζ z := by
  exact (ProductPolarization.product_character_values F ζ hζ P
    T (lambdaValue F ζ hζ P T)
    (lambdaValue_raw_formula F ζ hζ P T)).1 b z hz

theorem lambdaB_norm (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (b : B F ζ hζ P) :
    ‖(lambdaB F ζ hζ P T b : ℂ)‖ =
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ b.val : ℝ≥0) : ℝ) := by
  exact (ProductPolarization.product_character_values F ζ hζ P
    T (lambdaValue F ζ hζ P T)
    (lambdaValue_raw_formula F ζ hζ P T)).2 b

theorem lambdaB_raw_formula (P : CompatibleLocalData F ζ hζ)
    (T : FiniteAdjustment F ζ hζ P) (b : B F ζ hζ P) (x : rawB F ζ hζ P)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = b.val.val) :
    lambdaB F ζ hζ P T b =
      ∏ᶠ v, adjustedLocalValue F ζ hζ P T v (rawCoordinate F ζ hζ P x v) := by
  change lambdaValue F ζ hζ P T b = rawProduct F ζ hζ P T x
  exact lambdaValue_raw_formula F ζ hζ P T b x hx

theorem exists_finite_compatible_adjustment (P : CompatibleLocalData F ζ hζ) :
    ∃ T : FiniteAdjustment F ζ hζ P,
      ∀ (b : B F ζ hζ P) (r : KPGlobalCenterRationalCharacter.R F ζ hζ),
        b.val = r.val →
        lambdaB F ζ hζ P T b = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r := by
  obtain ⟨T, hT⟩ := ProductPolarization.finite_intersection_adjustment F ζ hζ
    P
  refine ⟨T, ?_⟩
  intro b r hbr
  obtain ⟨x, hx⟩ := B_has_raw_lift F ζ hζ P b
  rw [lambdaB_raw_formula F ζ hζ P _ b x hx]
  exact hT x (r) (hx.trans (congrArg Subtype.val hbr))

end
end DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter
