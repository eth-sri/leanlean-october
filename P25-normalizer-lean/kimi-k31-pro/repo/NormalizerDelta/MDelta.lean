module

public import NormalizerDelta.Gamma1Count
public import NormalizerDelta.NewmanDelta

@[expose] public section

/-!
# §M: M_Δ = D⁻¹ Γ₀(n_Δ)⁺ D is the set of matrices of the generalized Newman bound

* The Atkin–Lehner elements of level n (Q ∣ n) form a subgroup (`alSub`): products by the general
  product law `isAtkinLehner_mul_gen`, inverses by the adjugate.  So Γ₀(n)⁺ = `alSub n`.
* D⁻¹ w D, for w = (1/√Q)[[Qx, y], [nz, Qw]], is (1/√Q)[[Qx, y/h], [Nz/h, Qw]] (N = n h²): the form of
  `IsNewmanFormH N h_Δ` with e = Q.  Conversely D g D⁻¹ of such a g is ±w_e.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### Γ₀(n)⁺ -/

/-- The Atkin–Lehner elements of level n (Q ∣ n) form a subgroup. -/
def alSub (n : ℕ) [NeZero n] : Subgroup SLℝ where
  carrier := {g | ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g}
  one_mem' := ⟨1, one_dvd n, 1, 0, 0, 1, by norm_num, by
    mat_smp⟩
  mul_mem' := by
    rintro g g' ⟨Q, hQ, hg⟩ ⟨Q', hQ', hg'⟩
    exact ⟨_, mul_div_gcd_dvd hQ hQ', isAtkinLehner_mul_gen hQ hQ' hg hg'⟩
  inv_mem' := by
    rintro g ⟨Q, hQ, x, y, z, w, hdet, hgm⟩
    refine ⟨Q, hQ, w, -y, -z, x, by linear_combination hdet, ?_⟩
    rw [coe_inv_of_coe_eq_smul hgm]
    congr 1
    mat_smp

theorem mem_Gamma0Plus {n : ℕ} [NeZero n] {g : SLℝ} :
    g ∈ Gamma0Plus n ↔ ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g := by
  rw [show Gamma0Plus n = alSub n from Subgroup.closure_eq (alSub n)]
  rfl

/-! ### n_Δ -/

theorem nDelta_mul (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    nDelta N Δ * hDelta N Δ ^ 2 = N :=
  Nat.div_mul_cancel (newmanData_delta N Δ).h_sq_dvd

instance nDelta_neZero (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : NeZero (nDelta N Δ) :=
  ⟨fun h => NeZero.ne N (by rw [← nDelta_mul N Δ, h, zero_mul])⟩

theorem hDelta_pos (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : 0 < hDelta N Δ :=
  Nat.pos_of_ne_zero (hDelta_ne_zero Δ)

/-! ### Conjugation by D⁻¹ -/

/-- Conjugation by D⁻¹: [[a, b], [c, d]] ↦ [[a, b/M], [Mc, d]]. -/
theorem coe_conj_Dm_inv {M : ℕ} (hM : 0 < M) {Y : SLℝ} {a b c d : ℝ}
    (hY : (Y : Matℝ) = !![a, b; c, d]) :
    ((MulAut.conj (Dm M)⁻¹ Y : SLℝ) : Matℝ) =
      !![a, b / M; M * c, d] := by
  have hs : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hM)).ne'
  have hss : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [MulAut.conj_apply, inv_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_Dm hM, hY,
    adjugate_fin_two_of]
  mat_smp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> (try rw [Real.sq_sqrt (Nat.cast_nonneg _)]) <;> ring

/-! ### M_Δ -/

theorem mem_MDelta_iff {N : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {g : SLℝ} :
    g ∈ MDelta N Δ ↔ IsNewmanFormH N (hDelta N Δ) g := by
  have hh := hDelta_pos N Δ
  have hhr : (hDelta N Δ : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hNr : (N : ℝ) = nDelta N Δ * (hDelta N Δ : ℝ) ^ 2 := by
    exact_mod_cast (nDelta_mul N Δ).symm
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨Q, hQ, x, y, z, w', hdet, hwm⟩ := mem_Gamma0Plus.1 hw
    have hQ0 : 0 < Q := Nat.pos_of_dvd_of_pos hQ (Nat.pos_of_ne_zero (NeZero.ne _))
    refine ⟨x, y, z, w', Q, hQ0, hQ, by
      rw [show N / hDelta N Δ ^ 2 = nDelta N Δ from rfl]; linear_combination hdet, 1, Or.inl rfl, ?_⟩
    have hwm' : (w : Matℝ) =
        !![(Real.sqrt Q)⁻¹ * (Q * x), (Real.sqrt Q)⁻¹ * y;
          (Real.sqrt Q)⁻¹ * (nDelta N Δ * z), (Real.sqrt Q)⁻¹ * (Q * w')] := by
      rw [hwm]; mat_smp
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [coe_conj_Dm_inv hh hwm']
    mat_smp [hNr] <;> field_simp <;> ring_nf <;> simp
  · rintro ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩
    refine ⟨MulAut.conj (Dm (hDelta N Δ)) g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hgm' : (g : Matℝ) =
        !![ε / Real.sqrt e * (a * e), ε / Real.sqrt e * (b / hDelta N Δ);
          ε / Real.sqrt e * (N * c / hDelta N Δ), ε / Real.sqrt e * (d * e)] := by
      rw [hgm]; mat_smp
    have hc := coe_conj_Dm hh hgm'
    have hn : N / hDelta N Δ ^ 2 = nDelta N Δ := rfl
    rw [hn] at hdet he
    refine mem_Gamma0Plus.2 ⟨e, he, ?_⟩
    rcases hε with rfl | rfl
    · refine ⟨a, b, c, d, by linear_combination hdet, ?_⟩
      rw [hc]
      mat_smp [hNr] <;> field_simp <;> ring_nf <;> simp
    · refine ⟨-a, -b, -c, -d, by linear_combination hdet, ?_⟩
      rw [hc]
      mat_smp [hNr] <;> field_simp

theorem coe_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (MDelta N Δ : Set SLℝ) = {g | IsNewmanFormH N (hDelta N Δ) g} :=
  Set.ext fun _ => mem_MDelta_iff

theorem Gamma0R_le_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Gamma0R N ≤ MDelta N Δ := by
  intro γ hγ
  obtain ⟨a, b, c', d, hdet, ⟨z, rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
  have hh := hDelta_pos N Δ
  have hhr : (hDelta N Δ : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hNz : (N : ℤ) = nDelta N Δ * (hDelta N Δ : ℤ) ^ 2 := by
    exact_mod_cast (nDelta_mul N Δ).symm
  refine mem_MDelta_iff.2 ⟨a, b * hDelta N Δ, z * hDelta N Δ, d, 1, one_pos, one_dvd _, ?_, 1,
    Or.inl rfl, ?_⟩
  · have hn : N / hDelta N Δ ^ 2 = nDelta N Δ := rfl
    rw [hn]; push_cast; rw [hNz] at hdet; linear_combination hdet
  · rw [hγm]
    mat_smp <;> field_simp

theorem normG_GammaDeltaR_le_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    NormG (GammaDeltaR N Δ) ≤ MDelta N Δ := by
  intro g hg
  apply mem_MDelta_iff.2
  let D := newmanData_delta N Δ
  obtain ⟨κ, α, β, γ, δ, hκ, hprim, hgm⟩ := exists_prim_formG D hg
  have hh : hDelta N Δ ≠ 0 := D.h_pos.ne'
  have hhr : (hDelta N Δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  have hN := NeZero.ne N
  have hgS : (g : Matℝ) = κ • Smat (hDelta N Δ) α β γ δ := by rw [hgm]; rfl
  have hdet : κ ^ 2 * ((detS α β γ δ : ℤ) : ℝ) = 1 := by
    simpa only [hgS, det_smul, Fintype.card_fin, det_Smat hh] using g.2
  have he : detS α β γ δ ≠ 0 := by intro h0; simp [h0] at hdet
  have hepos : 0 < detS α β γ δ := by
    have hκ2 : 0 < κ ^ 2 := by positivity
    have : (0 : ℝ) < ((detS α β γ δ : ℤ) : ℝ) := by
      by_contra hc
      push Not at hc
      nlinarith
    exact_mod_cast this
  have hginv : ((g⁻¹ : SLℝ) : Matℝ) =
      κ • Smat (hDelta N Δ) δ (-β) (-γ) α := by
    rw [coe_inv_of_coe_eq_smul hgm]
    congr 1
    mat_smp [Smat] <;> ring
  have hloc := fun (p : ℕ) (hp : p.Prime) => local_conclusionG D hg hgS he hginv hprim hp
  have hnz : (nOf N (hDelta N Δ) : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (D.n_ne_zero hN)
  have hen : (detS α β γ δ) ∣ (nOf N (hDelta N Δ) : ℤ) := by
    refine dvd_of_forall_vz_le he hnz (fun p hp => ?_)
    have := hloc p hp
    simp only at this
    rw [vz_natCast]
    rcases this with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hnγ : (nOf N (hDelta N Δ) : ℤ) ∣ γ := by
    by_cases hγ : γ = 0
    · rw [hγ]; exact dvd_zero _
    refine dvd_of_forall_vz_le hnz hγ (fun p hp => ?_)
    have := hloc p hp
    simp only [vv_of_ne hγ] at this
    rw [vz_natCast]
    rcases this with ⟨-, h2⟩ | ⟨-, -, h2, -⟩ <;> omega
  have heα : (detS α β γ δ) ∣ α := by
    by_cases hα : α = 0
    · rw [hα]; exact dvd_zero _
    refine dvd_of_forall_vz_le he hα (fun p hp => ?_)
    have := hloc p hp
    simp only [vv_of_ne hα] at this
    rcases this with ⟨h1, -⟩ | ⟨h1, h2, -⟩ <;> omega
  have heδ : (detS α β γ δ) ∣ δ := by
    by_cases hδ : δ = 0
    · rw [hδ]; exact dvd_zero _
    refine dvd_of_forall_vz_le he hδ (fun p hp => ?_)
    have := hloc p hp
    simp only [vv_of_ne hδ] at this
    rcases this with ⟨h1, -⟩ | ⟨h1, -, -, h2⟩ <;> omega
  obtain ⟨a', ha'⟩ := heα
  obtain ⟨d', hd'⟩ := heδ
  obtain ⟨c', hc'⟩ := hnγ
  obtain ⟨m, hm⟩ := hen
  set E := detS α β γ δ
  set e : ℕ := E.toNat
  have hEe : (e : ℤ) = E := Int.toNat_of_nonneg hepos.le
  have he0 : 0 < e := by omega
  have her : (e : ℝ) = (E : ℝ) := by exact_mod_cast hEe
  have hs0 : Real.sqrt e ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 he0)).ne'
  refine ⟨a', β, c', d', e, he0, ⟨m.toNat, ?_⟩, ?_, κ * Real.sqrt e, ?_, ?_⟩
  · have hm0 : 0 ≤ m := by
      by_contra hneg
      push Not at hneg
      have : (nOf N (hDelta N Δ) : ℤ) < 0 := by rw [hm]; exact mul_neg_of_pos_of_neg hepos hneg
      omega
    have : ((nOf N (hDelta N Δ) : ℕ) : ℤ) = ((e * m.toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hm0, hEe]
      exact hm
    exact_mod_cast this
  · rw [hEe]
    have h1 : E = detS α β γ δ := rfl
    rw [ha', hd', hc'] at h1
    simp only [nOf] at h1 ⊢
    linear_combination -h1
  · apply mul_self_eq_one_iff.1
    rw [← pow_two, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), her]
    exact hdet
  · have hNr : (N : ℝ) = nOf N (hDelta N Δ) * (hDelta N Δ : ℝ) ^ 2 := by
      exact_mod_cast D.n_mul_sq.symm
    have hα' : (α : ℝ) = a' * e := by rw [her, ha']; push_cast; ring
    have hγ' : (γ : ℝ) = nOf N (hDelta N Δ) * c' := by rw [hc']; push_cast; ring
    have hδ' : (δ : ℝ) = d' * e := by rw [her, hd']; push_cast; ring
    rw [hgm, mul_div_assoc, div_self hs0, mul_one]
    congr 1
    mat_smp [hα', hγ', hδ', hNr] <;> field_simp

end

end NormalizerLean
