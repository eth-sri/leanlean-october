module

public import NormalizerDelta.Lattice
public import NormalizerDelta.Local

@[expose] public section

/-! From the integral relations on conjugation, recover a primitive scaled integral matrix.
The six divisibilities needed for `newman_divisors` then follow using the adjugate. -/

open Matrix

namespace NormalizerLean
noncomputable section
variable {N : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {g : SL₂ℝ}

private abbrev scaled (h : ℕ) (a b c d : ℤ) : Mat₂ ℝ := !![(a : ℝ), b / h; h * c, d]

/-- Clear denominators after diagonal scaling, then remove the gcd of all four entries. -/
private lemma primitive_form (hg : g ∈ NormG (GammaDeltaR N Δ)) (h : ℕ) (hh : 0 < h) :
    ∃ (κ : ℝ) (a b c d : ℤ), (g : Mat₂ ℝ) = κ • scaled h a b c d ∧
      Primitive a b c d := by
  obtain ⟨t, ht⟩ : ∃ t, (g⁻¹ 0 t : ℝ) ≠ 0 := Function.ne_iff.mp ((g⁻¹).row_ne_zero 0)
  -- A nonzero entry of the inverse supplies a common real multiplier.
  set u := (N : ℝ) * g⁻¹ 0 t
  have hu : u ≠ 0 := mul_ne_zero (NeZero.ne _) ht
  have H (r i) : ∃ m : ℤ, u * g r i = m := by
    obtain ⟨k, hk⟩ := (newman_entries hg r t).2.2.2 i
    exact ⟨k * weight N r t, by simpa [u, zsmul_eq_mul, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hk.symm⟩
  choose F hF using H
  let f := ![(h : ℤ) * F 0 0, h ^ 2 * F 0 1, F 1 0, h * F 1 1]
  obtain ⟨A, e, P⟩ := Finset.extract_gcd f Finset.univ_nonempty
  refine ⟨Finset.univ.gcd f / (h * u), A 0, A 1, A 2, A 3, ?_, fun p ⟨p0, p1, p2, p3⟩ => ?_⟩
  · have eqn i := congrArg (fun z : ℤ => (z : ℝ)) (e i (Finset.mem_univ _))
    simp [Fin.forall_fin_succ, f, ← hF] at eqn
    entries <;> simp [scaled] <;> field_simp <;> grind
  · rw [← P]; apply Finset.dvd_gcd; intro i _; fin_cases i <;> assumption

lemma coe_inv_scaled {s a b c d : ℝ} (h : (g : Mat₂ ℝ) = s • !![a, b; c, d]) :
    ((g⁻¹ : SL₂ℝ) : Mat₂ ℝ) = s • !![d, -b; -c, a] := by
  simp [h, adjugate_fin_two_of]

local notation "h" => hDelta N Δ
local notation "n" => nDelta N Δ

lemma newman_delta (hg : g ∈ NormG (GammaDeltaR N Δ)) : IsNewmanFormH N (hDelta N Δ) g := by
  have hh : (h : ℝ) ≠ 0 := NeZero.ne _
  have hn : (n : ℝ) ≠ 0 := NeZero.ne _
  obtain ⟨κ, a, b, c, d, M, prim⟩ := primitive_form hg h (NeZero.pos _)
  have E := g.2
  rw [M, det_smul, det_fin_two_of, Fintype.card_fin] at E
  field_simp at E
  have detR : κ ^ 2 * ((a * d - b * c : ℤ) : ℝ) = 1 := by push_cast; exact E
  have pos := pos_of_mul_pos_right (detR.symm ▸ zero_lt_one) (sq_nonneg κ)
  lift a * d - b * c to ℕ using (by exact_mod_cast pos.le) with e det
  norm_cast at pos detR
  -- The two off-diagonal output positions supply the six local tests.
  obtain ⟨⟨i, I⟩, ⟨j, J⟩, ⟨x, X⟩, _⟩ := newman_entries hg 0 1
  obtain ⟨⟨k, K⟩, ⟨l, L⟩, ⟨y, Y⟩, _⟩ := newman_entries hg 1 0
  simp [coe_inv_scaled M, M, scaled, weight, nsmul_eq_mul, zsmul_eq_mul, cast_level Δ] at I J K L X Y
  field_simp at I J K L X Y
  obtain ⟨en, ⟨c', hc⟩, ⟨a', ha⟩, ⟨d', hd⟩⟩ : e ∣ n ∧ (n : ℤ) ∣ c ∧ (e : ℤ) ∣ a ∧ (e : ℤ) ∣ d := by
    apply newman_divisors (Δ := Δ) pos det.symm prim <;>
      [use i; use -j; use -k; use l; use x; use -y] <;>
      rify <;> grobner
  refine ⟨a', b, c', d', e, pos, en, ?_, κ * Real.sqrt e, ?_, ?_⟩
  · change a' * d' * (e : ℤ) ^ 2 - b * c' * n = _
    rw [ha, hc, hd] at det; linear_combination -det
  · apply sq_eq_one_iff.mp; rwa [mul_pow, Real.sq_sqrt (by positivity)]
  · rw [M, ha, hd, hc]; entries <;> simp [scaled, cast_level Δ] <;> field_simp; simp
end

end NormalizerLean
