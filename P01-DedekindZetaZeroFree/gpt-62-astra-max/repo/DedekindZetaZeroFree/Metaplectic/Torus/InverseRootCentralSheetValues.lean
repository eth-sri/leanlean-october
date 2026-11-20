module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.DiagonalKernelEvaluation
public import DedekindZetaZeroFree.Metaplectic.Kubota.UniformizerHilbertPowers

@[expose] public section

set_option maxHeartbeats 1000000
noncomputable section
namespace DedekindZetaZeroFree.TameInverseRootValueAudit
open scoped NumberField Classical
open NumberField IsDedekindDomain KPLocalExceptionalConstruction
open KPTameJacquetTestDuality KPTameTransposeKernelUnfolding
open KPTameLiteralNormalizationAtomic.DiagonalArithmetic
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
local notation "W" => KPPGLLocalCover.W F ζ hζ (Sum.inr q)
local notation "N" => KPPGLLocalCover.N F ζ hζ (Sum.inr q)
local notation "A" => KPPGLLocalCover.A F ζ hζ (Sum.inr q)
local notation "C" => KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)
omit [NumberField F] in
private theorem phase_reduction (e : rootsOfUnity 3 F) (i : Fin 3) :
    e ^ (-8 * ((i.val : ℤ)+1)) = e ^ ((i.val : ℤ)+1) := by
  have h3 : e ^ 3 = 1 := by
    apply Subtype.ext
    exact e.property
  calc
    _ = e ^ ((-8 * ((i.val : ℤ)+1)) % 3) := zpow_eq_zpow_emod' _ h3
    _ = e ^ (((i.val : ℤ)+1) % 3) := by congr 1; omega
    _ = _ := (zpow_eq_zpow_emod' _ h3).symm

local notation "LocalCompletion" => LocalField F q

private theorem hilbert_centre_phase (π u : LocalCompletionˣ) (i : Fin 3) :
    (KPHilbert.B3 F ζ hζ (Sum.inr q)
      ((π ^ ((i.val : ℤ)+1) / u)⁻¹ ^ (2 : ℕ))
      (π ^ (2*((i.val : ℤ)+1)))) ^ 2 =
    KPHilbert.B3 F ζ hζ (Sum.inr q) π u ^ ((i.val : ℤ)+1) := by
  let := Fintype.ofFinite (IsLocalRing.ResidueField (KPTameCompact.O F q))
  let B := KPHilbert.B3 F ζ hζ (Sum.inr q)
  obtain ⟨hL, hR, hsk, _, _, ha⟩ := KPHilbert.B3_laws F ζ hζ (Sum.inr q)
  let BL : LocalCompletionˣ →* rootsOfUnity 3 F :=
    { toFun := fun a => B a (π ^ (2*((i.val : ℤ)+1)))
      map_one' := KubotaDefectSymbolAlgebra.one_left _ _ _ hL _
      map_mul' := fun a b => hL a b _ }
  let BR : LocalCompletionˣ →* rootsOfUnity 3 F :=
    { toFun := fun b => B u b
      map_one' := KubotaDefectSymbolAlgebra.one_right _ _ _ hR _
      map_mul' := hR u }
  change BL ((π ^ ((i.val : ℤ)+1) / u)⁻¹ ^ (2 : ℕ)) ^ 2 = _
  rw [map_pow, map_inv, map_div]
  have hp : BL (π ^ ((i.val : ℤ)+1)) = 1 := by
    exact uniformizer_hilbert_powers F ζ hζ q π _ _
  rw [hp, one_div]
  change ((B u (π ^ (2*((i.val : ℤ)+1))))⁻¹⁻¹ ^ 2) ^ 2 = _
  rw [inv_inv]
  change (BR (π ^ (2*((i.val : ℤ)+1))) ^ 2) ^ 2 = _
  rw [map_zpow]
  change ((B u π ^ (2*((i.val : ℤ)+1))) ^ 2) ^ 2 = _
  dsimp only [B]
  rw [hsk u π]
  simp only [← zpow_natCast, ← zpow_mul, inv_zpow, ← zpow_neg]
  convert phase_reduction F (B π u) i using 1
  congr 1
  ring

private theorem A_inv (p : LocalCompletionˣ) : (A p)⁻¹ = A p⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [KPPGLLocalCover.A_mul]
  have hB : KPHilbert.B3 F ζ hζ (Sum.inr q) p p⁻¹ = 1 := by
    obtain ⟨hL, hR, _, _, _, ha⟩ := KPHilbert.B3_laws F ζ hζ (Sum.inr q)
    let R : LocalCompletionˣ →* rootsOfUnity 3 F :=
      { toFun := KPHilbert.B3 F ζ hζ (Sum.inr q) p
        map_one' := KubotaDefectSymbolAlgebra.one_right _ _ _ hR _
        map_mul' := hR p }
    change R p⁻¹ = 1
    rw [map_inv]
    simp [R, (ha p).1]
  rw [hB, one_pow, map_one, one_mul, mul_inv_cancel]
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
    (KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) 1) = 1
  rw [KPStandardLocalRootLifts.A_one, map_one]

private theorem actual_centre_factorization
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (π u : LocalCompletionˣ) (i : Fin 3) :
    KPRankOneShellContinuation.kernelW LocalCompletion S.borel .minus *
      N ((π ^ ((i.val : ℤ)+1) / u : LocalCompletionˣ) : LocalCompletion) *
      (eta F ζ hζ q π i * W * N (-(u : LocalCompletion)/(π : LocalCompletion))) *
      (diagonalLift F ζ hζ q π (-1, (i.val : ℤ)+1) * W)⁻¹ =
    C (KPHilbert.B3 F ζ hζ (Sum.inr q) π u ^ ((i.val : ℤ)+1)) *
      N (-(u : LocalCompletion) / ((π ^ ((i.val : ℤ)+1) : LocalCompletionˣ) : LocalCompletion)) *
      A (u^2) := by
  let := Fintype.ofFinite (IsLocalRing.ResidueField (KPTameCompact.O F q))
  let v := π ^ ((i.val : ℤ)+1) / u
  have hr : -u/π +
      ((π ^ i.val : LocalCompletionˣ) : LocalCompletion)/v = 0 := by
    dsimp [v]
    simp only [zpow_add, zpow_one, Units.val_div_eq_div_val, Units.val_mul,
      zpow_natCast, Units.val_pow_eq_pow_val]
    field_simp
    ring
  rw [KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry.signed_double_kernel_diagonal_index]
  rw [hr]
  have hl : KPPGLLocalCover.LowerN F ζ hζ (Sum.inr q) 0 = 1 := by
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inr q) 0) = 1
    rw [KPStandardLocalRootLifts.LowerN_zero, map_one]
  rw [hl, mul_one, diagonal_lift_scalar F ζ hζ q S, diagonal_lift_scalar F ζ hζ q S]
  simp only [mul_inv_rev]
  have hc : (π ^ ((i.val : ℤ) - 0) : LocalCompletionˣ) *
      (π ^ (-1 - ((i.val : ℤ) + 1)) : LocalCompletionˣ)⁻¹ =
      π ^ (2*((i.val : ℤ)+1)) := by
    rw [← zpow_neg, ← zpow_add]
    congr 1
    ring
  have hb : KPHilbert.B3 F ζ hζ (Sum.inr q)
      (π ^ ((i.val : ℤ) - 0)) (π ^ (-1 - ((i.val : ℤ)+1)))⁻¹ = 1 := by
    rw [← zpow_neg]
    exact uniformizer_hilbert_powers F ζ hζ q π _ _
  have he : N (-(v⁻¹ : LocalCompletionˣ) : LocalCompletion) * A (v⁻¹^2) *
      A (π ^ ((i.val : ℤ) - 0)) * W * W⁻¹ * (A (π ^ (-1 - ((i.val : ℤ) + 1))))⁻¹ =
      N (-(v⁻¹ : LocalCompletionˣ) : LocalCompletion) * A (v⁻¹^2) *
        (A (π ^ ((i.val : ℤ) - 0)) * (A (π ^ (-1 - ((i.val : ℤ) + 1))))⁻¹) := by group
  rw [← mul_assoc, he, A_inv, KPPGLLocalCover.A_mul, hb,
    one_pow, map_one, one_mul, hc]
  rw [mul_assoc, KPPGLLocalCover.A_mul, hilbert_centre_phase]
  have ht : v⁻¹ ^ 2 * π ^ (2*((i.val : ℤ)+1)) = u^2 := by
    dsimp [v]
    rw [inv_div, div_pow]
    have hp : (π ^ ((i.val : ℤ)+1)) ^ 2 = π ^ (2*((i.val : ℤ)+1)) := by
      rw [← zpow_natCast _ 2, ← zpow_mul]
      congr 1
      ring
    rw [hp, div_mul_cancel]
  have hn : (-(v⁻¹ : LocalCompletionˣ) : LocalCompletion) =
      -u/((π ^ ((i.val : ℤ)+1) : LocalCompletionˣ) : LocalCompletion) := by
    simp [v, inv_div, Units.val_div_eq_div_val, neg_div]
  have hcomm : Commute (N (-(v⁻¹ : LocalCompletionˣ) : LocalCompletion))
      (C (KPHilbert.B3 F ζ hζ (Sum.inr q) π u ^ ((i.val : ℤ)+1))) := by
    apply Commute.symm
    exact ((Subgroup.mem_center_iff.mp (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q) ⟨_, rfl⟩))
      (N (-(v⁻¹ : LocalCompletionˣ) : LocalCompletion))).symm
  rw [ht, ← mul_assoc, hcomm.eq, hn]

theorem actual_full_inverse_root_factorization
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (π u w : LocalCompletionˣ) (i : Fin 3) (t : LocalCompletion)
    (hw : (w : LocalCompletion) = (u : LocalCompletion) + (π : LocalCompletion)*t) :
    KPRankOneShellContinuation.kernelW LocalCompletion S.borel .minus *
      N ((π ^ ((i.val : ℤ)+1) / w : LocalCompletionˣ) : LocalCompletion) *
      (eta F ζ hζ q π i * W * N (-(u : LocalCompletion)/(π : LocalCompletion))) =
    C (KPHilbert.B3 F ζ hζ (Sum.inr q) π w ^ ((i.val : ℤ)+1)) *
      N (-(w : LocalCompletion) / ((π ^ ((i.val : ℤ)+1) : LocalCompletionˣ) : LocalCompletion)) *
      A (w^2) * (diagonalLift F ζ hζ q π (-1, (i.val : ℤ)+1) * W * N t) := by
  have hx : -u/π =
      -w/π+t := by
    rw [hw]
    field_simp
    ring
  rw [hx, KPPGLLocalCover.N_add]
  calc
    _ = (KPRankOneShellContinuation.kernelW LocalCompletion S.borel .minus *
        N ((π ^ ((i.val : ℤ)+1) / w : LocalCompletionˣ) : LocalCompletion) *
        (eta F ζ hζ q π i * W * N (-w/π))) * N t := by group
    _ = _ := by rw [((mul_inv_eq_iff_eq_mul).mp (actual_centre_factorization F ζ hζ q S π w i))]; group

theorem hilbert_shift_by_cube
    (π u y w : LocalCompletionˣ) (hw : w = u*y^3) :
    KPHilbert.B3 F ζ hζ (Sum.inr q) π w =
      KPHilbert.B3 F ζ hζ (Sum.inr q) π u := by
  rw [hw, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.1,
    ((KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.1 π y).2, mul_one]

theorem normalized_centre_torus_value
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (hnormalized : KPTameTransposeLiteral.RawNormalizedExtension F ζ hζ q S P)
    (π : LocalCompletionˣ) (u : (KPTameCompact.O F q)ˣ) (i : Fin 3) :
    ∃ h : HL F ζ hζ q S P,
      (h.val : ActualCover F ζ hζ q) =
        C (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u) ^ ((i.val : ℤ)+1)) *
          A ((KPTameCompact.unitInclusion F q u)^2) ∧
      chiH F ζ hζ q S P hP .minus h =
        (ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) π
          (KPTameCompact.unitInclusion F q u) ^ ((i.val : ℤ)+1)) : ℂ) := by
  let e := KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u) ^ ((i.val : ℤ)+1)
  let a : actualTorus F ζ hζ q :=
    ⟨ActualFiniteTorus.normalWord F ζ hζ q e (KPTameCompact.unitInclusion F q (u^2)),
      (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).1 e _⟩
  let h : HL F ζ hζ q S P := ⟨a, (ActualFiniteBorel.LowShellUnitCharts.unit_word_mem_HL F ζ hζ q S P hP e (u^2))⟩
  refine ⟨h, ?_, ?_⟩
  · change C e * A (KPTameCompact.unitInclusion F q (u^2)) = _
    rw [map_pow]
  · exact ActualFiniteBorel.LowShellUnitCharts.normalized_chiH_word F ζ hζ q S
      P hP hnormalized h e (u^2) rfl .minus

end DedekindZetaZeroFree.TameInverseRootValueAudit

end
