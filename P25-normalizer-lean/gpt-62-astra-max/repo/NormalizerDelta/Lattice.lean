module

public import NormalizerLean.Basic

@[expose] public section

/-! Integral relations on the entries of a conjugate. Work one output entry at a time: its
allowed lattice is ℤ except in position (1,0), where it is Nℤ. A matrix in Γ_Δ gives
a linear relation in the quotient of ℝ by that lattice. -/

open Matrix

namespace NormalizerLean

variable {N : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ}

/-- Relations in the additive quotient by a prescribed entry lattice. -/
private lemma relations {T : Type*} [AddCommGroup T] (V : Mat₂ T)
    (L : ∀ a b c d : ℤ, a * d - b * c = 1 → (N : ℤ) ∣ c → ∀ u ∈ Δ, (u : ZMod N) = d →
      a • V 0 0 + b • V 0 1 + c • V 1 0 + d • V 1 1 = 0) :
    V 0 1 = 0 ∧ N • V 1 0 = 0 ∧ epsDelta N Δ • V 1 1 = 0 ∧ ∀ i, N • V i 0 = 0 := by
  -- Products of the upper and lower unipotents, followed by a lift of each unit in Δ.
  have U (b c : ℤ) := L 1 b (N * c) (1 + b * (N * c)) (by ring) (dvd_mul_right ..) 1 (one_mem _) (by simp)
  have I : V 0 0 = -V 1 1 := eq_neg_of_add_eq_zero_left (by simpa using U 0 0)
  have Y : V 0 1 = 0 := by simpa [I, add_right_comm] using U 1 0
  have Z : N • V 1 0 = 0 := by simpa [I, add_right_comm] using U 0 1
  have W : N • V 1 1 = 0 := by simpa [I, Y, Z, add_smul] using U 1 1
  refine ⟨Y, Z, ?_, by intro i; fin_cases i <;> simp [I, Z, W]⟩
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, dvd_epsDelta_iff]
  refine ⟨addOrderOf_dvd_iff_nsmul_eq_zero.mpr W, fun u hu => ?_⟩
  obtain ⟨a, b, det⟩ := lift_unit u
  let v := (u : ZMod N).val
  have A : ((v : ℤ) - a) • V 1 1 = 0 := by
    simpa [I, Y, sub_eq_add_neg, add_smul, Z, add_comm, v] using L _ _ _ _ det dvd_rfl u hu (by simp)
  change a * (v : ℤ) - b * N = 1 at det
  change _ ∣ v ^ 2 - 1
  by_cases hv : v = 0
  · simp [hv]
  rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← natCast_zsmul, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
  linear_combination (norm := (match_scalars; push_cast; grobner)) (v : ℤ) • A + b • W

/-- Required multiple for each output entry of a conjugate. -/
def weight (N : ℕ) (r t : Fin 2) : ℤ := if r = 1 ∧ t = 0 then N else 1

lemma newman_entries {g : SL₂ℝ} (hg : g ∈ NormG (GammaDeltaR N Δ)) (r t : Fin 2) :
    let L := AddSubgroup.zmultiples (weight N r t : ℝ)
    let P := fun i j (m : ℕ) => m • (g r i * (g⁻¹ j t : ℝ)) ∈ L
    P 0 1 1 ∧ P 1 0 N ∧ P 1 1 (epsDelta N Δ) ∧ ∀ i, P i 0 N := by
  intro L P
  simp only [P, ← QuotientAddGroup.eq_zero_iff (N := L), ← QuotientAddGroup.mk'_apply L, map_nsmul, one_smul]
  apply relations (fun i j => QuotientAddGroup.mk' L (g r i * (g⁻¹ j t : ℝ)))
  intro a b c d det hc u hu hd
  let A := mkSL _ _ _ _ det
  obtain ⟨B, hB, eq⟩ := (hg (ofZ A)).mp ⟨A, ⟨gamma0_dvd.mpr hc, u, hu, hd⟩, rfl⟩
  have entry := congrArg (fun M : SL₂ℝ => (M r t : ℝ)) eq
  obtain ⟨k, hk⟩ : weight N r t ∣ B r t := by
    fin_cases r <;> fin_cases t <;> first | exact one_dvd _ | exact gamma0_dvd.mp hB.1
  simp only [← map_zsmul, ← map_add]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨k, ?_⟩
  change (B r t : ℝ) = (g.1 * _ * _ : Mat₂ ℝ) r t at entry
  rw [ofZ_mkSL, hk] at entry
  simp [Matrix.mul_apply] at entry
  simp only [zsmul_eq_mul]; linear_combination entry

end NormalizerLean
