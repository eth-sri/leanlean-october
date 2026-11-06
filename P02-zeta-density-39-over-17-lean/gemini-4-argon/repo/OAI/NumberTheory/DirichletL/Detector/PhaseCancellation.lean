module
public import OAI.NumberTheory.DirichletL.Detector.Phase

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem quadraticRayValue_norm_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : ‖quadraticRayValue r‖ = 1 := by
  rw [quadraticRayValue_eq_fourthRoot r hr]
  simp [fourthRoot]

theorem G_norm_one (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : ‖G a‖ = 1 := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  have hn := Complex.norm_eq_one_of_pow_eq_one hc (by decide : (3 : ℕ) ≠ 0)
  change ‖fixedGValue (residue a)‖ = 1
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift, norm_mul, norm_inv,
    hn, inv_one, one_mul]
  exact quadraticRayValue_norm_one _ ha

theorem cubicTwo_isUnit_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    IsUnit (Ideal.Quotient.mk cubicTwoIdeal a) := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field _
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hd : (2 : O) ∣ a := by
    simpa only [cubicTwoIdeal, Ideal.mem_span_singleton, neg_dvd] using hm
  exact ((odd_residue_iff_not_two_dvd a).mp ha) hd

theorem G_norm_one_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) : ‖G a‖ = 1 :=
  G_norm_one a ha (cubicTwo_isUnit_of_odd a ha)

theorem G_conjugate_cancel (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : star (G a) * G a = 1 := by
  have hn := G_norm_one a ha hu
  have hs : star (G a) = (G a)⁻¹ := (Complex.inv_eq_conj hn).symm
  rw [hs]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; norm_num))

end SevenEighths.ProbePhase
end

end OAI
