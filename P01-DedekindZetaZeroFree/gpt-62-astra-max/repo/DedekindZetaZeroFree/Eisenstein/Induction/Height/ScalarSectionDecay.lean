module

public import DedekindZetaZeroFree.Eisenstein.Induction.Height.TorusRootCoordinates

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField Matrix
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPLiteralRaw KPChamberHeight
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private alias actual_root_projection := TorusRootCoordinates.root_projection

theorem covered_torus_root_upper (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) :
    ∃ B : KPChamberHeight.AdelGL F, B 1 0 = 0 ∧
      Matrix.ProjGenLinGroup.mk B = coveredHeightProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) := by
  obtain ⟨A, hA, h10, h01⟩ := t.property
  let B := A * Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x
  have hB : B 1 0 = 0 := by
    simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection, h10]
  refine ⟨B, hB, ?_⟩
  have he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) := by
    simp only [B, map_mul, actual_root_projection F ζ hζ x, hA]
  change _ = adelicHeightProjection F (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ _)
  rw [← he]
  rfl

theorem actualScalarHeightDecay (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (s : ℂ) (hs : (1 : ℝ) / 3 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : G F ζ hζ,
      ‖f.val s g‖ ≤ B * (KPChamberHeight.height F (actualBaseRowLine F)
        (coveredHeightProjection F ζ hζ g)) ^ (-2 * (2 / 3 + s.re)) := by
  obtain ⟨B, hB, hb⟩ := norm_val_iwasawa_bound F ζ hζ K hK f
  obtain ⟨m, M, hm, hmM, hdist⟩ := actualBaseRowHeight_compact_upper_bounds F ζ hζ K hK.1
  have hM := hm.trans_le hmM
  let a := 2 / 3 + s.re
  refine ⟨B * (M⁻¹) ^ (-2 * a), mul_nonneg hB (Real.rpow_nonneg (inv_nonneg.mpr hM.le) _), fun g => ?_⟩
  obtain ⟨t, x, k, hg⟩ := hK.2.1 g
  obtain ⟨A, hA, hproj⟩ := covered_torus_root_upper F ζ hζ t x
  have hd := (hdist A k hA).2
  rw [hproj, ← map_mul, ← hg] at hd
  let H := KPChamberHeight.height F (actualBaseRowLine F) (coveredHeightProjection F ζ hζ g)
  let Ht := KPChamberHeight.height F (actualBaseRowLine F)
    (coveredHeightProjection F ζ hζ (t.val * KPGlobalTorusFunctionData.N F ζ hζ x))
  have hH : 0 < H := height_pos F _ _
  have hdelta : (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^ a = Ht ^ (-2 * a) := by
    rw [← actualBaseRowHeight_torus_root_modulus F ζ hζ t x]
    simpa only [Int.cast_neg, Int.cast_ofNat] using (Real.rpow_intCast_mul (height_pos F _ _).le (-2) a).symm
  calc
    _ ≤ B * (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^ a := by
      rw [hg]; exact hb s t x k
    _ = B * Ht ^ (-2 * a) := by rw [hdelta]
    _ ≤ B * (M⁻¹ * H) ^ (-2 * a) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (mul_pos (inv_pos.mpr hM) hH) (by
      exact (inv_mul_le_iff₀ hM).mpr hd) (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by dsimp [a]; linarith))) hB
    _ = (B * (M⁻¹) ^ (-2 * a)) * H ^ (-2 * a) := by
      rw [Real.mul_rpow (inv_nonneg.mpr hM.le) hH.le]; ring
end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
