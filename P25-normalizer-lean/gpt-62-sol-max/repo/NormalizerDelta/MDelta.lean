module

public import NormalizerDelta.NewmanDelta

@[expose] public section

/-! The union of the Atkin–Lehner cosets is a group, and its diagonal conjugate
is exactly the set described by the generalized Newman bound. -/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

private theorem atkin_of_matrix {N Q : ℕ} {g : SL(2, ℝ)} {a b c d : ℤ} (hQ : 0 < Q)
    (hm : (g : Mat₂R) = (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * a, (b : ℝ); N * c, Q * d]) :
    IsAtkinLehner N Q g := by
  have hd := g.2
  rw [hm, det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), det_fin_two_of,
    inv_mul_eq_one₀ (Nat.cast_ne_zero.2 hQ.ne')] at hd
  refine ⟨a, b, c, d, ?_, hm⟩
  norm_cast at hd
  linear_combination -hd

private theorem atkin_inv {N Q : ℕ} {g : SL(2, ℝ)} (hg : IsAtkinLehner N Q g) :
    IsAtkinLehner N Q g⁻¹ := by
  obtain ⟨a, b, c, d, hd, hm⟩ := hg
  exact ⟨d, -b, -c, a, by linear_combination hd,
    by rw [coe_inv_of_coe_eq_smul hm]; simp [mul_neg]⟩

private theorem atkin_mul {N Q₁ Q₂ : ℕ} [NeZero N] (h₁ : Q₁ ∣ N) (h₂ : Q₂ ∣ N)
    {g₁ g₂ : SL(2, ℝ)} (hg₁ : IsAtkinLehner N Q₁ g₁) (hg₂ : IsAtkinLehner N Q₂ g₂) :
    ∃ Q : ℕ, Q ∣ N ∧ IsAtkinLehner N Q (g₁ * g₂) := by
  let G := Q₁.gcd Q₂
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_left Q₁ Q₂
  obtain ⟨v, hv⟩ := Nat.gcd_dvd_right Q₁ Q₂
  change Q₁ = G * u at hu
  change Q₂ = G * v at hv
  have hG : 0 < G := Nat.pos_of_dvd_of_pos ((Nat.gcd_dvd_left _ _).trans h₁) (NeZero.pos N)
  have hlcm : Q₁.lcm Q₂ = G * (u * v) := by
    have e := Nat.gcd_mul_lcm Q₁ Q₂
    apply Nat.eq_of_mul_eq_mul_left hG
    rw [e, hu, hv]
    ring
  obtain ⟨L, hL⟩ := hlcm ▸ Nat.lcm_dvd h₁ h₂
  have hd : u * v ∣ N := ⟨G * L, by rw [hL]; ring⟩
  obtain ⟨a, b, c, d, -, e₁⟩ := hg₁
  obtain ⟨x, y, z, t, -, e₂⟩ := hg₂
  have hs : Real.sqrt Q₁ * Real.sqrt Q₂ = G * Real.sqrt (u * v : ℕ) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), hu, hv]
    push_cast
    rw [show ((G : ℝ) * u) * ((G : ℝ) * v) = G^2 * (u * v) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]
  refine ⟨u * v, hd, atkin_of_matrix (Nat.pos_of_dvd_of_pos hd (NeZero.pos N))
    (a := G * a * x + L * b * z) (b := u * a * y + v * b * t)
    (c := v * c * x + u * d * z) (d := L * c * y + G * d * t) ?_⟩
  change (g₁ : Mat₂R) * (g₂ : Mat₂R) = _
  rw [e₁, e₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_inv, hs,
    mul_inv, mul_comm (G : ℝ)⁻¹, mul_smul]
  congr 1
  rw [hL, hu, hv]
  push_cast
  rw [mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp

private def atkinSub (N : ℕ) [NeZero N] : Subgroup SL(2, ℝ) where
  carrier := {g | ∃ Q : ℕ, Q ∣ N ∧ IsAtkinLehner N Q g}
  one_mem' := ⟨1, one_dvd _, 1, 0, 0, 1, by simp, by simp [one_fin_two]⟩
  mul_mem' := fun ⟨_, hd, h⟩ ⟨_, hd', h'⟩ => atkin_mul hd hd' h h'
  inv_mem' := fun ⟨Q, hd, h⟩ => ⟨Q, hd, atkin_inv h⟩

private theorem gamma0Plus_eq (n : ℕ) [NeZero n] : Gamma0Plus n = atkinSub n :=
  Subgroup.closure_eq (atkinSub n)

private abbrev Dm (M : ℕ) : SL(2, ℝ) := projSL !![(M : ℝ), 0; 0, 1]

variable {N : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {g : SL(2, ℝ)}

private theorem mem_conj :
    g ∈ MDelta N Δ ↔ MulAut.conj (Dm (hDelta N Δ)) g ∈ Gamma0Plus (nDelta N Δ) := by
  rw [MDelta, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv, ← MulAut.conj_apply]

private theorem conjugated_entries (k a b c d : ℝ) :
    let h := hDelta N Δ
    (↑(MulAut.conj (Dm h) g) : Mat₂R) = k • !![a,b;nDelta N Δ * c,d] ↔
    (g : Mat₂R) = k • !![a,b / h;N * c / h,d] := by
  intro h
  let D := Dm h
  have hh : 0 < h := hDelta_pos N Δ
  have hr : (h : ℝ) ≠ 0 := by positivity
  have hd : (D : Mat₂R) = (Real.sqrt h)⁻¹ • !![(h : ℝ),0;0,1] := by
    change (Dm h : Mat₂R) = _
    rw [Dm, coe_projSL] <;> simp [det_fin_two_of, hh]
  have u : IsUnit (D : Mat₂R) := (SpecialLinearGroup.toGL D).isUnit
  have hi : (↑D⁻¹ : Mat₂R) * (D : Mat₂R) = 1 :=
    (SpecialLinearGroup.toGL D).inv_mul
  change (D : Mat₂R) * (g : Mat₂R) * (↑D⁻¹ : Mat₂R) = _ ↔ _
  -- Cancel the right factor D and the scalar used to normalize it.
  rw [← u.mul_left_inj, Matrix.mul_assoc, hi, Matrix.mul_one, hd, Matrix.smul_mul, Matrix.mul_smul,
    smul_right_inj (by positivity : (Real.sqrt h)⁻¹ ≠ 0), Matrix.smul_mul,
    (g : Mat₂R).eta_fin_two, mul_fin_two, mul_fin_two, ← Matrix.ext_iff, ← Matrix.ext_iff]
  have e : (N : ℝ) * c / h = nDelta N Δ * c * h := by
    have hN : (N : ℝ) = (nDelta N Δ : ℝ) * (h : ℝ)^2 := by exact_mod_cast (nDelta_mul N Δ).symm
    rw [hN]
    field_simp
  simp [Fin.forall_fin_two, e, ← mul_assoc, mul_comm (h : ℝ), mul_left_inj' hr, ← mul_div_assoc, eq_div_iff hr]

theorem mem_MDelta_iff : g ∈ MDelta N Δ ↔ IsNewmanFormH N (hDelta N Δ) g := by
  constructor
  · intro hg
    have hg := mem_conj.1 hg
    rw [gamma0Plus_eq] at hg
    obtain ⟨Q, hQ, a, b, c, d, hd, hm⟩ := hg
    refine ⟨a, b, c, d, Q, Nat.pos_of_dvd_of_pos hQ (NeZero.pos (nDelta N Δ)), hQ, ?_, 1, Or.inl rfl, ?_⟩
    · change a * d * (Q : ℤ)^2 - b * c * nDelta N Δ = Q
      linear_combination hd
    · exact (conjugated_entries _ _ _ _ _).1 (by simpa [one_div, mul_comm] using hm)
  · rintro ⟨a, b, c, d, e, he, hd, -, ε, hε, hm⟩
    have H := (conjugated_entries _ _ _ _ _).2 hm
    refine mem_conj.2 (Subgroup.subset_closure ⟨e, hd, ?_⟩)
    rcases hε with rfl | rfl
    · exact atkin_of_matrix he (a := a) (b := b) (c := c) (d := d) (by simpa [one_div, mul_comm] using H)
    · refine atkin_of_matrix he (a := -a) (b := -b) (c := -c) (d := -d) ?_
      rw [H, neg_div, one_div, neg_smul, ← smul_neg]
      congr 1
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm]

/-- The matrices of the generalized Newman bound form the conjugated subgroup M_Δ. -/
theorem coe_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (MDelta N Δ : Set SL(2, ℝ)) = {g | IsNewmanFormH N (hDelta N Δ) g} :=
  Set.ext fun _ => mem_MDelta_iff

theorem Gamma0R_le_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Gamma0R N ≤ MDelta N Δ := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨c, hc⟩ := gamma0_dvd.1 hg
  let h := hDelta N Δ
  refine mem_conj.2 (Subgroup.subset_closure ⟨1, one_dvd _, atkin_of_matrix one_pos
    (a := g 0 0) (b := g 0 1 * h) (c := c * h) (d := g 1 1) ?_⟩)
  simp only [Nat.cast_one, Real.sqrt_one, inv_one, one_mul]
  apply (conjugated_entries 1 _ _ _ _).2
  have hh : (hDelta N Δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hDelta_pos N Δ).ne'
  rw [coe_ofZ, hc]
  simp [h, hh, mul_div_assoc]

theorem normG_GammaDeltaR_le_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    NormG (GammaDeltaR N Δ) ≤ MDelta N Δ :=
  fun _ hg => mem_MDelta_iff.2 (newman_delta' hg)

end

end NormalizerLean
