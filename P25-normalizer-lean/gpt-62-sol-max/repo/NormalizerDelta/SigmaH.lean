module

public import NormalizerDelta.MDelta

@[expose] public section

/-! Primitive Hermite normal forms for the right cosets of Γ₀(N) in M_Δ. -/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

private theorem cast_mul (a b : SL(2, ℤ)) :
    (ofZ a : Mat₂R) * (ofZ b : Mat₂R) = (ofZ (a*b) : Mat₂R) :=
  (castM.map_mul (a : Mat₂Z) b).symm

private theorem cast_one : (ofZ (1 : SL(2, ℤ)) : Mat₂R) = 1 := castM.map_one

/-- The first column gives `a` by Bézout, then the upper-right entry is reduced modulo `d`. -/
private theorem exists_hermite (x y z w : ℤ) (hW : 0 < x * w - y * z) :
    ∃ σ : SL(2, ℤ), ∃ a b d : ℕ, 0 < a ∧ 0 < d ∧ b < d ∧ (a : ℤ) * d = x * w - y * z ∧
      !![(x : ℝ), y; z, w] = (ofZ σ : Mat₂R) * hermMat a b d := by
  have hg : 0 < Int.gcd x z := Int.gcd_pos_iff.2 (by by_contra! h; simp [h.1, h.2] at hW)
  obtain ⟨G, p, q, hG, hpq, hp, hq⟩ := Int.exists_gcd_one' hg
  obtain ⟨A, B, e⟩ := Int.isCoprime_iff_gcd_eq_one.2 hpq
  let d := p * w - q * y
  have hd : x * w - y * z = G * d := by rw [hp, hq]; ring
  have hd0 : 0 < d := pos_of_mul_pos_right (hd ▸ hW) (Int.natCast_nonneg _)
  let b := A * y + B * w
  let k := b / d
  let r := b % d
  have hr : 0 ≤ r := Int.emod_nonneg _ hd0.ne'
  have hrd : r < d := Int.emod_lt_of_pos _ hd0
  have hdiv : d * k + r = b := Int.mul_ediv_add_emod b d
  let σ := mkSL p (p * k - B) q (q * k + A) (by linear_combination e)
  refine ⟨σ, G, r.toNat, d.toNat, hG, by omega, by omega, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hd0.le, hd]
  have H : (!![x,y;z,w] : Mat₂Z) = (σ : Mat₂Z) * (!![(G : ℤ), ↑r.toNat; 0, ↑d.toNat] : Mat₂Z) := by
    dsimp [σ, mkSL]
    rw [mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Int.toNat_of_nonneg hr, Int.toNat_of_nonneg hd0.le]
    · simp [hp]
    · dsimp [b, d] at hdiv ⊢
      linear_combination -y * e - p * hdiv
    · simp [hq]
    · dsimp [b, d] at hdiv ⊢
      linear_combination -w * e - q * hdiv
  simpa only [map_mul, cast_entries, Int.cast_natCast, Int.cast_zero] using! congrArg castM H

/-- Divide out the content of the integral numerator after taking its Hermite form. -/
theorem exists_sigmaH {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {R : Set SL(2, ℤ)}
    (hR : IsGamma0Reps N R) {g : SL(2, ℝ)} (hg : g ∈ MDelta N Δ) :
    ∃ γ ∈ Gamma0R N, ∃ r ∈ R, ∃ a b d : ℕ, IsHermiteN N a b d ∧ ∃ c : ℝ, c ≠ 0 ∧
      ((γ * g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        c • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) := by
  obtain ⟨a, b, c, d, e, he0, he, hdet, ε, -, hgm⟩ := mem_MDelta_iff.1 hg
  let h := hDelta N Δ
  have hh : 0 < h := hDelta_pos N Δ
  have hNz : (N : ℤ) = nDelta N Δ * (h : ℤ)^2 := by exact_mod_cast (nDelta_mul N Δ).symm
  have hd : (a * e * h) * (d * e * h) - b * (N * c) = (h : ℤ)^2 * e := by
    change a * d * (e : ℤ)^2 - b * c * (nDelta N Δ : ℤ) = e at hdet
    rw [hNz]
    linear_combination (h : ℤ)^2 * hdet
  obtain ⟨σ, A, B, D, hA, hD, hBD, hAD, hmat⟩ := exists_hermite _ _ _ _ (by rw [hd]; positivity)
  set t := Nat.gcd (Nat.gcd A B) D with ht
  have ht0 : 0 < t := Nat.gcd_pos_of_pos_right _ hD
  obtain ⟨A', ea⟩ : t ∣ A := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨B', eb⟩ : t ∣ B := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨D', ed⟩ : t ∣ D := Nat.gcd_dvd_right _ _
  have hAD' : A * D = h ^ 2 * e := by exact_mod_cast hAD.trans hd
  have hHerm : IsHermiteN N A' B' D' := by
    simp only [ea, ed] at hA hD
    rw [eb, ed] at hBD
    refine ⟨Nat.pos_of_mul_pos_left hA, Nat.pos_of_mul_pos_left hD, ?_, Nat.lt_of_mul_lt_mul_left hBD, ?_⟩
    · have h' : A * D ∣ N := by
        rw [hAD', ← nDelta_mul N Δ, mul_comm _ (hDelta N Δ ^ 2)]
        exact mul_dvd_mul_left _ he
      exact (show A' * D' ∣ A * D from ⟨t^2, by rw [ea, ed]; ring⟩).trans h'
    · apply Nat.eq_of_mul_eq_mul_left ht0
      simpa only [ea, eb, ed, Nat.gcd_mul_left, mul_one] using ht.symm
  obtain ⟨r, ⟨hr, hσr⟩, -⟩ := hR σ
  have hhr : (hDelta N Δ : ℝ) ≠ 0 := by positivity
  let k := ε / (Real.sqrt e * h)
  have hg' : (g : Mat₂R) = k • !![(a : ℝ) * e * h, (b : ℝ); N * c, d * e * h] := by
    rw [hgm]
    ext i j; fin_cases i <;> fin_cases j <;> simp [k, h] <;> field_simp
  have eH : hermMat A B D = (t : ℝ) • hermMat A' B' D' := by
    rw [ea, eb, ed]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hermMat]
  have hg'' : (g : Mat₂R) = (k * t) • ((ofZ σ : Mat₂R) * hermMat A' B' D') := by
    push_cast at hmat
    rw [hg', hmat, eH, Matrix.mul_smul, smul_smul]
  refine ⟨ofZ (r * σ⁻¹), Subgroup.mem_map_of_mem _ (by simpa using inv_mem hσr), r, hr, A', B', D', hHerm,
    k * t, ?_, ?_⟩
  · intro hz
    simpa [hg'', hz] using g.2
  · change (ofZ (r * σ⁻¹) : Mat₂R) * (g : Mat₂R) = _
    rw [hg'', Matrix.mul_smul, ← Matrix.mul_assoc, cast_mul, inv_mul_cancel_right]

private theorem cross {s t : ℝ} (h : s ≠ 0) {a b c d : ℤ}
    (e : s * a = t * c) (f : s * b = t * d) : a * d = b * c := by
  have H : (a : ℝ) * d = b * c := mul_left_cancel₀ h (by linear_combination (d : ℝ) * e - (c : ℝ) * f)
  exact_mod_cast H

private theorem hermite_unique {N a b d a' b' d' : ℕ} {s m : ℤ}
    (hH : IsHermiteN N a b d) (hH' : IsHermiteN N a' b' d') (hs : s * s = 1)
    (e : s * a * b' = (s * b + m * d) * a') (f : s * a * d' = s * d * a') :
    a = a' ∧ b = b' ∧ d = d' ∧ m = 0 := by
  obtain ⟨ha, hd, -, hb, hp⟩ := hH
  obtain ⟨-, -, -, hb', hp'⟩ := hH'
  have Y : (a : ℤ) * b' = a' * (b + s * m * d) := by
    linear_combination s * e - ((a : ℤ) * b' - b * a') * hs
  have Z : (a : ℤ) * d' = a' * d := by
    linear_combination s * f - ((a : ℤ) * d' - d * a') * hs
  -- The content is unchanged by adding a multiple of the bottom row.
  have : a = a' := calc
    a = Int.gcd (a * a' : ℤ) (Int.gcd (a * b' : ℤ) (a * d' : ℤ)) := by
      simp [Int.gcd_mul_left, ← Nat.gcd_assoc, hp']
    _ = Int.gcd (a' * a : ℤ) (Int.gcd (a' * (b + s*m*d) : ℤ) (a' * d : ℤ)) := by rw [Y, Z, mul_comm (a : ℤ) a']
    _ = a' := by simp [Int.gcd_mul_left, ← Nat.gcd_assoc, hp]
  subst a'
  have ha0 := Int.natCast_ne_zero.2 ha.ne'
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have : d' = d := by exact_mod_cast mul_left_cancel₀ ha0 Z
  subst d'
  have E := mul_left_cancel₀ ha0 Y
  have eb : (b' : ℤ) = b := by
    have h := congrArg (fun z : ℤ => z % d) E
    simpa only [Int.add_mul_emod_self_right, Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.2 hb'),
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.2 hb)] using h
  exact ⟨rfl, by exact_mod_cast eb.symm, rfl, by simpa [eb, hs0, hd.ne'] using E⟩

theorem sigmaH_unique {N : ℕ} [NeZero N] {R : Set SL(2, ℤ)} (hR : IsGamma0Reps N R)
    {r r' : SL(2, ℤ)} (hr : r ∈ R) (hr' : r' ∈ R) {a b d a' b' d' : ℕ}
    (hH : IsHermiteN N a b d) (hH' : IsHermiteN N a' b' d') {c c' : ℝ} (hc : c ≠ 0) (_hc' : c' ≠ 0)
    {γ : SL(2, ℝ)} (hγ : γ ∈ Gamma0R N)
    (h : c • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) =
      (γ : Matrix (Fin 2) (Fin 2) ℝ) * (c' • ((ofZ r' : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a' b' d'))) :
    r = r' ∧ a = a' ∧ b = b' ∧ d = d' := by
  obtain ⟨γ, hγ, rfl⟩ := hγ
  let u := γ * r'
  let M := u⁻¹ * r
  change _ = (ofZ γ : Mat₂R) * _ at h
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, cast_mul] at h
  have key := congrArg ((ofZ u⁻¹ : Mat₂R) * ·) h
  change _ = (ofZ u⁻¹ : Mat₂R) * (c' • ((ofZ u : Mat₂R) * hermMat a' b' d')) at key
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, cast_mul, inv_mul_cancel, cast_one, Matrix.one_mul] at key
  change c • ((ofZ M : Mat₂R) * hermMat a b d) = c' • hermMat a' b' d' at key
  rw [coe_ofZ, hermMat, mul_fin_two, ← Matrix.ext_iff] at key
  simp [Fin.forall_fin_two, hermMat] at key
  obtain ⟨⟨e00, e01⟩, e10, e11⟩ := key
  have h10 : M 1 0 = 0 := (e10.resolve_left hc).resolve_right hH.1.ne'
  simp [h10] at e11
  have hdM : M 0 0 * M 1 1 = 1 := by
    have hdet := M.2
    rwa [det_fin_two, h10, mul_zero, sub_zero] at hdet
  have hs : M 1 1 = M 0 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdM with ⟨e,f⟩ | ⟨e,f⟩ <;> rw [e,f]
  rw [hs] at hdM e11
  have X := cross hc (a := M 0 0 * a) (b := M 0 0 * b + M 0 1 * d) (c := a') (d := b')
    (by push_cast; exact e00) (by push_cast; exact e01)
  have Y := cross hc (a := M 0 0 * a) (b := M 0 0 * d) (c := a') (d := d')
    (by push_cast; exact e00) (by push_cast; exact e11)
  obtain ⟨ea, eb, ed, h01⟩ := hermite_unique hH hH' hdM X Y
  refine ⟨(hR r).unique ⟨hr, by simp⟩ ⟨hr', ?_⟩, ea, eb, ed⟩
  have hm : M = 1 ∨ M = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdM with ⟨e, -⟩ | ⟨e, -⟩ <;>
      [left; right] <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [e, hs, h10, h01]
  rw [show r * r'⁻¹ = γ * (r' * M * r'⁻¹) by dsimp [M, u]; group]
  apply mul_mem hγ
  rcases hm with e | e <;> simp [e]

end

end NormalizerLean
