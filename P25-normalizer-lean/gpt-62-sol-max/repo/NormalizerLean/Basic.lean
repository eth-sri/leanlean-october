module

public import NormalizerLean.Defs

@[expose] public section

/-! Casting integral matrices and computing in SL₂. -/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

abbrev Mat₂R := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat₂Z := Matrix (Fin 2) (Fin 2) ℤ

abbrev castM : Mat₂Z →+* Mat₂R := (Int.castRingHom ℝ).mapMatrix

theorem cast_entries (a b c d : ℤ) :
    castM !![a,b;c,d] = !![(a : ℝ), b; c, d] := (castM !![a,b;c,d]).eta_fin_two

theorem coe_ofZ (γ : SL(2, ℤ)) :
    (ofZ γ : Mat₂R) = !![(γ 0 0 : ℝ), γ 0 1; γ 1 0, γ 1 1] := (ofZ γ : Mat₂R).eta_fin_two

theorem gamma0_dvd {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ CongruenceSubgroup.Gamma0 N ↔ (N : ℤ) ∣ γ 1 0 :=
  CongruenceSubgroup.Gamma0_mem.trans (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)

theorem coe_inv_of_coe_eq_smul {g : SL(2, ℝ)} {s a b c d : ℝ} (h : (g : Mat₂R) = s • !![a,b;c,d]) :
    (↑g⁻¹ : Mat₂R) = s • !![d,-b;-c,a] := by
  change (g : Mat₂R).adjugate = _
  rw [h, adjugate_smul, adjugate_fin_two_of]
  simp

theorem coe_projSL (A : Mat₂R) (hA : 0 < A.det) : (projSL A : Mat₂R) = (Real.sqrt A.det)⁻¹ • A := by
  simp [projSL, hA]

end

end NormalizerLean
