module

public import NormalizerLean.Proofs

@[expose] public section

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-!
# The generalized Newman bound, generic part: Newman's argument for a subgroup Γ ≤ Γ₀(N)

The frozen proof of T2 (`NormalizerLean/NewmanCond`, `NewmanRat`, `NewmanFacts`, `NewmanMain`) uses
Γ₀(N) only through: Γ ≤ Γ₀(N); T, U ∈ Γ; every element of Γ is in the lattice
L_ϵ = {M integral : N ∣ M₁₀, ϵ ∣ M₁₁ − M₀₀} with ϵ = gcd(N, 24); and, for p ∣ N with v_p(ϵ) < v_p(N),
an element γ_p = [[x, y], [N, t]] ∈ Γ with v_p(t − x) = v_p(ϵ).  Here these are hypotheses
(`NewmanData N Γ ϵ η`), with η the h of the conclusion (v_p(η) = min(v_p(ϵ), ⌊v_p(N)/2⌋)).  The local
valuation lemma holds for every j = v_p(ϵ) ≤ v_p(N) (`local_form_gen`, by `omega`).

This file was generated from the frozen files by `scratch/stage1/gen_newmangen.py` (substitutions
Γ₀(N) ↦ Γ, gcd(N, 24) ↦ ϵ, h(N) ↦ η, n(N) ↦ N/η²) and `scratch/stage1/finish_newmangen.py`
(the places listed above), then compiled; the frozen files are unchanged.
-/




/-- n = N / η². -/
def nOf (N η : ℕ) : ℕ := N / η ^ 2

/-- An integer matrix with N ∣ M₁₀ and ϵ ∣ M₁₁ − M₀₀. -/
def InLe (N ϵ : ℕ) (M : M2) : Prop :=
  ∃ a b c d : ℤ, M = !![(a : ℝ), b; c, d] ∧ (N : ℤ) ∣ c ∧ (ϵ : ℤ) ∣ d - a

/-- The hypotheses of Newman's argument for Γ ≤ Γ₀(N), with lattice parameter ϵ and output η. -/
structure NewmanData (N : ℕ) (Γ : Subgroup SL2R) (ϵ η : ℕ) : Prop where
  le : Γ ≤ Gamma0R N
  T_mem : matT ∈ Γ
  U_mem : matU N ∈ Γ
  inL : ∀ Y ∈ Γ, InLe N ϵ (Y : M2)
  eps_dvd : ϵ ∣ N
  h_pos : 0 < η
  h_sq_dvd : η ^ 2 ∣ N
  h_fact : ∀ p, η.factorization p = min (ϵ.factorization p) (N.factorization p / 2)
  gamma : ∀ p : ℕ, p.Prime → p ∣ N → ϵ.factorization p < N.factorization p →
    ∃ x y t : ℤ, x * t - y * N = 1 ∧
      (∃ γ ∈ Γ, (γ : M2) = !![(x : ℝ), y; N, t]) ∧
      t - x ≠ 0 ∧ vz p (t - x) = ϵ.factorization p

variable {Γ : Subgroup SL2R} {ϵ η : ℕ}

theorem NewmanData.n_mul_sq {N : ℕ} (D : NewmanData N Γ ϵ η) : nOf N η * η ^ 2 = N :=
  Nat.div_mul_cancel D.h_sq_dvd

theorem NewmanData.factorization_n {N : ℕ} (D : NewmanData N Γ ϵ η) (hN : N ≠ 0) (p : ℕ) :
    (nOf N η).factorization p + 2 * η.factorization p = N.factorization p := by
  conv_rhs => rw [← D.n_mul_sq]
  rw [Nat.factorization_mul (by intro h0; have := D.n_mul_sq; rw [h0, zero_mul] at this; omega)
    (pow_ne_zero 2 D.h_pos.ne'), Nat.factorization_pow]
  simp [Finsupp.add_apply, Finsupp.smul_apply]

theorem InLe.add {N : ℕ} {M M' : M2} (h : InLe N ϵ M) (h' : InLe N ϵ M') :
    InLe N ϵ (M + M') := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  obtain ⟨a', b', c', d', rfl, hc', hd'⟩ := h'
  refine ⟨a + a', b + b', c + c', d + d', by push_cast; simp, dvd_add hc hc', ?_⟩
  rw [show d + d' - (a + a') = (d - a) + (d' - a') by ring]; exact dvd_add hd hd'

theorem InLe.zsmul {N : ℕ} {M : M2} (h : InLe N ϵ M) (m : ℤ) :
    InLe N ϵ ((m : ℝ) • M) := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  refine ⟨m * a, m * b, m * c, m * d, by push_cast; simp, dvd_mul_of_dvd_right hc _, ?_⟩
  rw [show m * d - m * a = m * (d - a) by ring]; exact dvd_mul_of_dvd_right hd _

theorem InLe.sub {N : ℕ} {M M' : M2} (h : InLe N ϵ M) (h' : InLe N ϵ M') :
    InLe N ϵ (M - M') := by
  have := h.add (h'.zsmul (-1))
  convert this using 1
  simp [sub_eq_add_neg]

theorem InLe.one (N : ℕ) : InLe N ϵ 1 := ⟨1, 0, 0, 1, by mx, dvd_zero _, by simp⟩


/-- The products of entries that are integers. -/
theorem products_intG {N : ℕ} {g : SL2R} (D : NewmanData N Γ ϵ η) (hg : g ∈ NormG Γ) {x y z w : ℝ}
    (hx : (g : M2) 0 0 = x) (hy : (g : M2) 0 1 = y)
    (hz : (g : M2) 1 0 = z) (hw : (g : M2) 1 1 = w) :
    IsIntR (x * x) ∧ IsIntR (x * z) ∧ IsIntR (z * z) ∧ IsIntR (N * (y * y)) ∧
      IsIntR (N * (w * w)) ∧ IsIntR (N * (y * w)) ∧ IsIntR (N * (x * w)) ∧
      IsIntR (N * (x * y)) ∧ IsIntR (N * (z * w)) ∧ IsIntR (N * (y * z)) := by
  have hconj := fun Y hY => (Subgroup.mem_normalizer_iff.1 hg Y).1 hY
  have hT := isIntR_entries_of_mem (D.le (hconj _ D.T_mem))
  have hU := isIntR_entries_of_mem (D.le (hconj _ D.U_mem))
  have hTU := isIntR_entries_of_mem (D.le (hconj _ (mul_mem D.T_mem D.U_mem)))
  have hdet : x * w - y * z = 1 := by
    have := g.2; rwa [det_fin_two, hx, hy, hz, hw] at this
  have eT : ((g * matT * g⁻¹ : SL2R) : M2) =
      !![1 - x * z, x * x; -(z * z), 1 + x * z] := by
    rw [coe_conj, adjugate_fin_two]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [matT, Matrix.mul_apply, Fin.sum_univ_two, hx, hy, hz, hw] <;>
      first | ring1 | (linear_combination hdet) | (linear_combination -hdet)
  have eU : ((g * matU N * g⁻¹ : SL2R) : M2) =
      !![1 + N * (y * w), -(N * (y * y)); N * (w * w), 1 - N * (y * w)] := by
    rw [coe_conj, adjugate_fin_two]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [matU, Matrix.mul_apply, Fin.sum_univ_two, hx, hy, hz, hw] <;>
      first | ring1 | (linear_combination hdet) | (linear_combination -hdet)
  have eTU : ((g * (matT * matU N) * g⁻¹ : SL2R) : M2) =
      !![1 - x * z + N * (y * w) + N * (x * w), x * x - N * (y * y) - N * (x * y);
        -(z * z) + N * (w * w) + N * (z * w), 1 + x * z - N * (y * w) - N * (y * z)] := by
    rw [coe_conj, Matrix.SpecialLinearGroup.coe_mul, adjugate_fin_two]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [matT, matU, Matrix.mul_apply, Fin.sum_univ_two, hx, hy, hz, hw] <;>
      first | ring1 | (linear_combination hdet) | (linear_combination -hdet)
  have t01 := by simpa [eT] using hT 0 1
  have t00 := by simpa [eT] using hT 0 0
  have t10 := by simpa [eT] using hT 1 0
  have u01 := by simpa [eU] using hU 0 1
  have u10 := by simpa [eU] using hU 1 0
  have u00 := by simpa [eU] using hU 0 0
  have v00 := by simpa [eTU] using hTU 0 0
  have v01 := by simpa [eTU] using hTU 0 1
  have v10 := by simpa [eTU] using hTU 1 0
  have v11 := by simpa [eTU] using hTU 1 1
  have hxz := by simpa using IsIntR.one.sub t00
  have hyw := by simpa using u00.sub IsIntR.one
  refine ⟨t01, hxz, by simpa using t10.neg, by simpa using u01.neg, u10, hyw, ?_, ?_, ?_, ?_⟩
  · convert ((v00.sub IsIntR.one).add hxz).sub hyw using 1; ring
  · convert (t01.sub (by simpa using u01.neg)).sub v01 using 1; ring
  · convert (v10.add (by simpa using t10.neg)).sub u10 using 1; ring
  · convert ((IsIntR.one.add hxz).sub hyw).sub v11 using 1; ring

/-- **Step 1** ([Nw §2]): g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ without a common prime
factor. -/
theorem exists_prim_formG {N : ℕ} [NeZero N] {g : SL2R} (D : NewmanData N Γ ϵ η) (hg : g ∈ NormG Γ) :
    ∃ (κ : ℝ) (α β γ δ : ℤ), κ ≠ 0 ∧
      (∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β ∧ (p : ℤ) ∣ γ ∧ (p : ℤ) ∣ δ)) ∧
      (g : M2) =
        κ • !![(α : ℝ), (β : ℝ) / η; (η : ℝ) * γ, (δ : ℝ)] := by
  set x := (g : M2) 0 0 with hx
  set y := (g : M2) 0 1 with hy
  set z := (g : M2) 1 0 with hz
  set w := (g : M2) 1 1 with hw
  obtain ⟨hxx, hxz, hzz, hyy, hww, hyw, hxw, hxy, hzw, hyz⟩ :=
    products_intG D hg hx.symm hy.symm hz.symm hw.symm
  have hdet : x * w - y * z = 1 := by
    have := g.2
    rwa [det_fin_two] at this
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hh : (η : ℝ) ≠ 0 := Nat.cast_ne_zero.2 D.h_pos.ne'
  -- a nonzero t with N t x, N t y, N t z, N t w integral
  obtain ⟨t, ht, htx, hty, htz, htw⟩ : ∃ t : ℝ, t ≠ 0 ∧ IsIntR (N * t * x) ∧ IsIntR (N * t * y) ∧
      IsIntR (N * t * z) ∧ IsIntR (N * t * w) := by
    by_cases hx0 : x = 0
    · have hz0 : z ≠ 0 := by
        intro hz0
        rw [hx0, hz0] at hdet
        simp at hdet
      refine ⟨z, hz0, ?_, ?_, ?_, ?_⟩
      · convert (IsIntR.nat N).mul hxz using 1; ring
      · convert hyz using 1; ring
      · convert (IsIntR.nat N).mul hzz using 1; ring
      · convert hzw using 1; ring
    · refine ⟨x, hx0, ?_, ?_, ?_, ?_⟩
      · convert (IsIntR.nat N).mul hxx using 1; ring
      · convert hxy using 1; ring
      · convert (IsIntR.nat N).mul hxz using 1; ring
      · convert hxw using 1; ring
  obtain ⟨Ix, hIx⟩ := htx
  obtain ⟨Iy, hIy⟩ := hty
  obtain ⟨Iz, hIz⟩ := htz
  obtain ⟨Iw, hIw⟩ := htw
  set h := η
  set M0 : ℤ := h * Ix
  set M1 : ℤ := h ^ 2 * Iy
  set M2 : ℤ := Iz
  set M3 : ℤ := h * Iw
  set G : ℕ := Int.gcd (Int.gcd M0 M1) (Int.gcd M2 M3) with hG
  have hNt := mul_ne_zero hN ht
  have hG0 : G ≠ 0 := by
    intro hG0
    simp only [hG, Int.gcd_eq_zero_iff, Nat.cast_eq_zero] at hG0
    obtain ⟨⟨h0, h1⟩, h2, h3⟩ := hG0
    have hx0 : x = 0 := by
      have : (N : ℝ) * t * x = 0 := by
        rw [hIx]
        have : Ix = 0 := by
          simp only [M0] at h0
          rcases mul_eq_zero.1 h0 with h' | h'
          · exact absurd (by exact_mod_cast h') D.h_pos.ne'
          · exact h'
        simp [this]
      exact (mul_eq_zero.1 this).resolve_left hNt
    have hy0 : y = 0 := by
      have : (N : ℝ) * t * y = 0 := by
        rw [hIy]
        have : Iy = 0 := by
          simp only [M1] at h1
          rcases mul_eq_zero.1 h1 with h' | h'
          · have h'' : (h : ℤ) = 0 := (pow_eq_zero_iff two_ne_zero).1 h'
            exact absurd (by exact_mod_cast h'' : h = 0) D.h_pos.ne'
          · exact h'
        simp [this]
      exact (mul_eq_zero.1 this).resolve_left hNt
    rw [hx0, hy0] at hdet
    simp at hdet
  have hGdvd : ∀ m : ℤ, m = M0 ∨ m = M1 ∨ m = M2 ∨ m = M3 → (G : ℤ) ∣ m := by
    rintro m (rfl | rfl | rfl | rfl)
    · exact (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
    · exact (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
    · exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)
    · exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)
  obtain ⟨α, hα⟩ := hGdvd M0 (Or.inl rfl)
  obtain ⟨β, hβ⟩ := hGdvd M1 (Or.inr (Or.inl rfl))
  obtain ⟨γ, hγ⟩ := hGdvd M2 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨δ, hδ⟩ := hGdvd M3 (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨G / ((h : ℝ) * N * t), α, β, γ, δ, ?_, ?_, ?_⟩
  · exact div_ne_zero (Nat.cast_ne_zero.2 hG0) (mul_ne_zero (mul_ne_zero hh hN) ht)
  · rintro p hp ⟨hpα, hpβ, hpγ, hpδ⟩
    obtain ⟨α', hα'⟩ := hpα
    obtain ⟨β', hβ'⟩ := hpβ
    obtain ⟨γ', hγ'⟩ := hpγ
    obtain ⟨δ', hδ'⟩ := hpδ
    have hpG : ((p * G : ℕ) : ℤ) ∣ (G : ℤ) := by
      have h0 : ((p * G : ℕ) : ℤ) ∣ M0 := ⟨α', by rw [hα, hα']; push_cast; ring⟩
      have h1 : ((p * G : ℕ) : ℤ) ∣ M1 := ⟨β', by rw [hβ, hβ']; push_cast; ring⟩
      have h2 : ((p * G : ℕ) : ℤ) ∣ M2 := ⟨γ', by rw [hγ, hγ']; push_cast; ring⟩
      have h3 : ((p * G : ℕ) : ℤ) ∣ M3 := ⟨δ', by rw [hδ, hδ']; push_cast; ring⟩
      rw [hG]
      exact Int.dvd_coe_gcd (Int.dvd_coe_gcd h0 h1) (Int.dvd_coe_gcd h2 h3)
    have : p * G ∣ G := by exact_mod_cast hpG
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hG0) this
    have := hp.two_le
    nlinarith [Nat.pos_of_ne_zero hG0]
  · have hGr : (G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hG0
    have eα : (G : ℝ) * α = h * (N * t * x) := by rw [hIx]; exact_mod_cast hα.symm
    have eβ : (G : ℝ) * β = h ^ 2 * (N * t * y) := by rw [hIy]; exact_mod_cast hβ.symm
    have eγ : (G : ℝ) * γ = N * t * z := by rw [hIz]; exact_mod_cast hγ.symm
    have eδ : (G : ℝ) * δ = h * (N * t * w) := by rw [hIw]; exact_mod_cast hδ.symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hx, ← hy, ← hz, ← hw]
    · field_simp
      linear_combination -eα
    · field_simp
      linear_combination -eβ
    · field_simp
      linear_combination -eγ
    · field_simp
      linear_combination -eδ

theorem InLe.entries {N : ℕ} {M : M2} (h : InLe N ϵ M) :
    ∃ a b c d : ℤ, M 0 0 = a ∧ M 0 1 = b ∧ M 1 0 = c ∧ M 1 1 = d ∧ (N : ℤ) ∣ c ∧
      (ϵ : ℤ) ∣ d - a := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  exact ⟨a, b, c, d, by simp, by simp, by simp, by simp, hc, hd⟩


theorem phi_InLe {N : ℕ} [NeZero N] {g : SL2R} (D : NewmanData N Γ ϵ η) (hgN : g ∈ NormG Γ) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : M2) = κ • Smat (η) α β γ δ) {Y : SL2R}
    (hY : Y ∈ Γ) : InLe N ϵ (Phi (η) α β γ δ (Y : M2)) := by
  rw [← coe_conj_eq_Phi hg D.h_pos.ne']
  exact D.inL _ ((Subgroup.mem_normalizer_iff.1 hgN Y).1 hY)

theorem InLe.nsmul' {N : ℕ} {M : M2} (h : InLe N ϵ M) (m : ℕ) :
    InLe N ϵ ((m : ℝ) • M) := by
  have := h.zsmul m
  simpa using this

/-- The four basic facts in `InLe` form. -/
theorem InLe_basic {N : ℕ} [NeZero N] {g : SL2R} (D : NewmanData N Γ ϵ η) (hgN : g ∈ NormG Γ) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : M2) = κ • Smat (η) α β γ δ)
    (he : α * δ - β * γ ≠ 0) :
    InLe N ϵ (Phi (η) α β γ δ !![0, 1; 0, 0]) ∧
      InLe N ϵ ((N : ℝ) • Phi (η) α β γ δ !![0, 0; 1, 0]) ∧
      InLe N ϵ ((N : ℝ) • Phi (η) α β γ δ !![0, 0; 0, 1]) := by
  have hh := D.h_pos.ne'
  have h1 : InLe N ϵ (Phi (η) α β γ δ 1) := by rw [Phi_one hh he]; exact InLe.one N
  have hT := phi_InLe D hgN hg D.T_mem
  have hU := phi_InLe D hgN hg D.U_mem
  have hTU := phi_InLe D hgN hg (mul_mem D.T_mem D.U_mem)
  have eE12 : (!![0, 1; 0, 0] : M2) = (matT : M2) - 1 := by
    mx [matT]
  have eE21 : (N : ℝ) • (!![0, 0; 1, 0] : M2) =
      (matU N : M2) - 1 := by
    mx [matU]
  have eE22 : (N : ℝ) • (!![0, 0; 0, 1] : M2) =
      (N : ℝ) • 1 - (((matT * matU N : SL2R) : M2) -
        (matT : M2) - (matU N : M2) + 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    mx [matT, matU, Matrix.mul_apply] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [eE12, Phi_sub]; exact hT.sub h1
  · rw [← Phi_smul, eE21, Phi_sub]; exact hU.sub h1
  · rw [← Phi_smul, eE22, Phi_sub, Phi_smul, Phi_add, Phi_sub, Phi_sub]
    exact (h1.nsmul' N).sub (((hTU.sub hT).sub hU).add h1)

/-- The γ_p fact in `InLe` form, for γ_p = [[x, y], [N, t]] ∈ Γ. -/
theorem InLe_s {N : ℕ} [NeZero N] {g : SL2R} (D : NewmanData N Γ ϵ η) (hgN : g ∈ NormG Γ)
    {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : M2) = κ • Smat (η) α β γ δ)
    (he : α * δ - β * γ ≠ 0) {x y t : ℤ} {γp : SL2R} (hγp : γp ∈ Γ)
    (hγm : (γp : M2) = !![(x : ℝ), y; N, t]) :
    InLe N ϵ (((t - x : ℤ) : ℝ) • Phi (η) α β γ δ !![0, 0; 0, 1]) ∧
      (ϵ : ℤ) ∣ t - x := by
  have hh := D.h_pos.ne'
  have hε : (ϵ : ℤ) ∣ t - x := by
    obtain ⟨a, b, c, d, hm, -, hd⟩ := D.inL _ hγp
    have h00 := congrFun (congrFun hm 0) 0
    have h11 := congrFun (congrFun hm 1) 1
    rw [hγm] at h00 h11
    simp at h00 h11
    have : x = a := by exact_mod_cast h00
    have : t = d := by exact_mod_cast h11
    subst_vars
    exact hd
  refine ⟨?_, hε⟩
  have h1 : InLe N ϵ (Phi (η) α β γ δ 1) := by rw [Phi_one hh he]; exact InLe.one N
  have hP := phi_InLe D hgN hg hγp
  obtain ⟨hE12, hE21, -⟩ := InLe_basic D hgN hg he
  have eE : ((t - x : ℤ) : ℝ) • (!![0, 0; 0, 1] : M2) =
      (γp : M2) - (x : ℝ) • 1 - (y : ℝ) • !![0, 1; 0, 0] -
        (N : ℝ) • !![0, 0; 1, 0] := by
    rw [hγm]
    mx
  rw [← Phi_smul, eE, Phi_sub, Phi_sub, Phi_sub, Phi_smul, Phi_smul, Phi_smul]
  exact ((hP.sub (h1.zsmul x)).sub (hE12.zsmul y)).sub hE21

/-- The integer divisibilities F1–F12. -/
theorem int_factsG {N : ℕ} [NeZero N] {g : SL2R} (D : NewmanData N Γ ϵ η) (hgN : g ∈ NormG Γ) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : M2) = κ • Smat (η) α β γ δ)
    (he : α * δ - β * γ ≠ 0) :
    let E := α * δ - β * γ
    let ηz := (η : ℤ)
    let Nz := (N : ℤ)
    let εz := (ϵ : ℤ)
    let nz := (nOf N η : ℤ)
    E ∣ ηz * (α * γ) ∧ E ∣ 1 * α ^ 2 ∧ E * N ∣ ηz ^ 2 * γ ^ 2 ∧ E * εz ∣ (2 * ηz) * (α * γ) ∧
    E ∣ (nz * ηz) * (β * δ) ∧ E ∣ nz * β ^ 2 ∧ E ∣ 1 * δ ^ 2 ∧ E * εz ∣ (2 * nz * ηz) * (β * δ) ∧
    E ∣ Nz * (β * γ) ∧ E * ηz ∣ Nz * (α * β) ∧ E * N ∣ (Nz * ηz) * (γ * δ) ∧
    E * εz ∣ (2 * Nz) * (β * γ) := by
  dsimp only
  have hh := D.h_pos.ne'
  have hhr : (η : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  have hNr : (N : ℝ) = nOf N η * (η : ℝ) ^ 2 := by
    exact_mod_cast D.n_mul_sq.symm
  have hNz : (N : ℤ) = (nOf N η : ℤ) * (η : ℤ) ^ 2 := by exact_mod_cast D.n_mul_sq.symm
  have hN0 : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  obtain ⟨P12, P21, P22⟩ := InLe_basic D hgN hg he
  -- E₁₂
  obtain ⟨a1, b1, c1, d1, h00, h01, h10, h11, hc1, hd1⟩ := P12.entries
  rw [Phi_E12] at h00 h01 h10 h11
  have r00 := int_eq_of_real (X := -(α * (η : ℤ) * γ)) he (by rw [← h00]; simp)
  have r01 := int_eq_of_real (X := α ^ 2) he (by rw [← h01]; simp)
  have r10 := int_eq_of_real (X := -((η : ℤ) ^ 2 * γ ^ 2)) he (by rw [← h10]; simp)
  have r11 := int_eq_of_real (X := α * (η : ℤ) * γ) he (by rw [← h11]; simp)
  -- E₂₁ (times N)
  obtain ⟨a2, b2, c2, d2, i00, i01, i10, i11, hc2, hd2⟩ := P21.entries
  rw [Phi_E21 hh] at i00 i01 i10 i11
  have s00 := int_eq_of_real (X := (nOf N η : ℤ) * (η : ℤ) * (β * δ)) he
    (by rw [← i00]; simp [hNr]; field_simp)
  have s01 := int_eq_of_real (X := -((nOf N η : ℤ) * β ^ 2)) he
    (by rw [← i01]; simp [hNr]; field_simp)
  have s10 := int_eq_of_real (X := (N : ℤ) * δ ^ 2) he (by rw [← i10]; simp; ring)
  have s11 := int_eq_of_real (X := -((nOf N η : ℤ) * (η : ℤ) * (β * δ))) he
    (by rw [← i11]; simp [hNr]; field_simp)
  -- E₂₂ (times N)
  obtain ⟨a3, b3, c3, d3, j00, j01, j10, j11, hc3, hd3⟩ := P22.entries
  rw [Phi_E22 hh] at j00 j01 j10 j11
  have t00 := int_eq_of_real (X := -((N : ℤ) * (β * γ))) he (by rw [← j00]; simp; ring)
  have t01 := int_eq_of_real (X := (nOf N η : ℤ) * (η : ℤ) * (α * β)) he
    (by rw [← j01]; simp [hNr]; field_simp)
  have t10 := int_eq_of_real (X := -((N : ℤ) * (η : ℤ) * (γ * δ))) he
    (by rw [← j10]; simp; ring)
  have t11 := int_eq_of_real (X := (N : ℤ) * (α * δ)) he (by rw [← j11]; simp; ring)
  obtain ⟨c1', rfl⟩ := hc1
  obtain ⟨c2', rfl⟩ := hc2
  obtain ⟨c3', rfl⟩ := hc3
  obtain ⟨k1, hk1⟩ := hd1
  obtain ⟨k2, hk2⟩ := hd2
  obtain ⟨k3, hk3⟩ := hd3
  have hε := Int.natCast_dvd_natCast.2 D.eps_dvd
  obtain ⟨m, hm⟩ := hε
  have ha1 : a1 = -d1 := mul_left_cancel₀ he (by linear_combination -r00 - r11)
  have ha2 : d2 = -a2 := mul_left_cancel₀ he (by linear_combination -s11 - s00)
  have hd3' : d3 - a3 = N - 2 * a3 := mul_left_cancel₀ he (by linear_combination -t11 - t00)
  refine ⟨⟨d1, by linear_combination r11⟩, ⟨b1, by linear_combination r01⟩,
    ⟨-c1', by linear_combination -r10⟩,
    ⟨k1, by linear_combination 2 * r11 + (α * δ - β * γ) * hk1 + (α * δ - β * γ) * ha1⟩,
    ⟨a2, by linear_combination s00⟩, ⟨-b2, by linear_combination -s01⟩,
    ⟨c2', mul_left_cancel₀ hN0 (by linear_combination s10)⟩,
    ⟨-k2, by linear_combination 2 * s00 - (α * δ - β * γ) * hk2 + (α * δ - β * γ) * ha2⟩,
    ⟨-a3, by linear_combination -t00⟩, ⟨b3, by rw [hNz]; linear_combination (η : ℤ) * t01⟩,
    ⟨-c3', by linear_combination -t10⟩, ?_⟩
  -- F12: ε ∣ N − 2 a3 and ε ∣ N give ε ∣ 2 a3
  have h2a : (ϵ : ℤ) ∣ 2 * a3 := by
    have : (ϵ : ℤ) ∣ (N : ℤ) - (d3 - a3) := dvd_sub ⟨m, hm⟩ ⟨k3, hk3⟩
    rw [hd3'] at this
    simpa using this
  obtain ⟨k4, hk4⟩ := h2a
  exact ⟨-k4, by linear_combination -2 * t00 - (α * δ - β * γ) * hk4⟩


/-- The four facts with s = t − x in place of N. -/
theorem int_facts_sG {N : ℕ} [NeZero N] {g : SL2R} (D : NewmanData N Γ ϵ η) (hgN : g ∈ NormG Γ) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : M2) = κ • Smat (η) α β γ δ)
    (he : α * δ - β * γ ≠ 0) {x y t : ℤ} {γp : SL2R} (hγp : γp ∈ Γ)
    (hγm : (γp : M2) = !![(x : ℝ), y; N, t]) :
    let E := α * δ - β * γ
    let s := t - x
    let ηz := (η : ℤ)
    E ∣ s * (β * γ) ∧ E * ηz ∣ s * (α * β) ∧ E * N ∣ (s * ηz) * (γ * δ) ∧ E * (ϵ : ℤ) ∣ (2 * s) * (β * γ) := by
  dsimp only
  have hh := D.h_pos.ne'
  obtain ⟨P, hε⟩ := InLe_s D hgN hg he hγp hγm
  obtain ⟨a4, b4, c4, d4, j00, j01, j10, j11, hc4, hd4⟩ := P.entries
  rw [Phi_E22 hh] at j00 j01 j10 j11
  have t00 := int_eq_of_real (X := -((t - x) * (β * γ))) he (by rw [← j00]; simp; ring)
  have t01 := int_eq_of_real_div (X := (t - x) * (α * β)) he hh
    (by rw [← j01]; simp; ring)
  have t10 := int_eq_of_real (X := -((t - x) * (η : ℤ) * (γ * δ))) he
    (by rw [← j10]; simp; ring)
  have t11 := int_eq_of_real (X := (t - x) * (α * δ)) he (by rw [← j11]; simp; ring)
  obtain ⟨c4', rfl⟩ := hc4
  obtain ⟨k4, hk4⟩ := hd4
  have hd4' : d4 - a4 = (t - x) - 2 * a4 := mul_left_cancel₀ he (by linear_combination -t11 - t00)
  refine ⟨⟨-a4, by linear_combination -t00⟩, ⟨b4, by linear_combination t01⟩,
    ⟨-c4', by linear_combination -t10⟩, ?_⟩
  have h2a : (ϵ : ℤ) ∣ 2 * a4 := by
    have : (ϵ : ℤ) ∣ (t - x) - (d4 - a4) := dvd_sub hε ⟨k4, hk4⟩
    rw [hd4'] at this
    simpa using this
  obtain ⟨k5, hk5⟩ := h2a
  exact ⟨-k5, by linear_combination -2 * t00 - (α * δ - β * γ) * hk5⟩

set_option maxHeartbeats 4000000 in
/-- The local conclusion at a prime p. -/
theorem local_conclusionG {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (D : NewmanData N Γ ϵ η) (hgN : g ∈ NormG Γ) {κ : ℝ}
    {α β γ δ : ℤ} (hg : (g : M2) = κ • Smat (η) α β γ δ)
    (hginv : ((g⁻¹ : SL(2, ℝ)) : M2) = κ • Smat (η) δ (-β) (-γ) α)
    (he : α * δ - β * γ ≠ 0)
    (hprim : ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β ∧ (p : ℤ) ∣ γ ∧ (p : ℤ) ∣ δ))
    {p : ℕ} (hp : p.Prime) :
    let e := vz p (α * δ - β * γ)
    let n := (nOf N η).factorization p
    let B := e + N.factorization p + 1
    (e = 0 ∧ n ≤ vv B p γ) ∨ (e = n ∧ n ≤ vv B p α ∧ n ≤ vv B p γ ∧ n ≤ vv B p δ) := by
  intro e n B
  have hN := NeZero.ne N
  have hNz : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hhz : (η : ℤ) ≠ 0 := Nat.cast_ne_zero.2 D.h_pos.ne'
  have hn0 : nOf N η ≠ 0 := by intro h0; have := D.n_mul_sq; rw [h0, zero_mul] at this; omega
  have hnz : (nOf N η : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hε0 := (Nat.pos_of_dvd_of_pos D.eps_dvd (Nat.pos_of_ne_zero hN)).ne'
  have hεz : (ϵ : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hε0
  -- the local constants
  set ν := N.factorization p with hν
  set j := (ϵ).factorization p
  set k := (η).factorization p
  set e₂ := (2 : ℕ).factorization p with he₂
  set nν := n
  set δ₀ := e with hδ₀
  have hkj := D.h_fact p
  have hnk := D.factorization_n hN p
  have hjν := (Nat.factorization_le_iff_dvd hε0 hN).2 D.eps_dvd p
  have he₂1 : e₂ ≤ 1 := by rw [he₂, factorization_two]; split_ifs <;> omega
  -- valuations of the constants
  have vN : vz p (N : ℤ) = ν := vz_natCast p N
  have vh : vz p (η : ℤ) = k := vz_natCast p _
  have vn : vz p (nOf N η : ℤ) = nν := vz_natCast p _
  have vε : vz p (ϵ : ℤ) = j := vz_natCast p _
  have v2 : vz p (2 : ℤ) = e₂ := by simpa using vz_natCast p 2
  have v1 : vz p (1 : ℤ) = 0 := by simp [vz]
  have two0 : (2 : ℤ) ≠ 0 := by norm_num
  -- shorthand for the valuations of the entries
  set a := vv B p α
  set b := vv B p β
  set c := vv B p γ
  set d := vv B p δ
  have hb' := vv_neg B p β
  have hc' := vv_neg B p γ
  -- primitivity
  have prim : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
    by_contra hcon
    push Not at hcon
    apply hprim p hp
    have key : ∀ x : ℤ, vv B p x ≠ 0 → (p : ℤ) ∣ x := by
      intro x hx
      by_cases h0 : x = 0
      · rw [h0]; exact dvd_zero _
      · rw [vv_of_ne h0] at hx
        have := (pow_dvd_iff_le_vz hp h0 1).2 (Nat.pos_of_ne_zero hx)
        simpa using this
    exact ⟨key α hcon.1, key β hcon.2.1, key γ hcon.2.2.1, key δ hcon.2.2.2⟩
  -- ultrametric relation
  obtain ⟨u1, u2⟩ := ultra_vv (B := B) hp he (by simp only [B]; omega)
  -- the facts
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12⟩ := int_factsG D hgN hg he
  have he' : δ * α - -β * -γ = α * δ - β * γ := by ring
  have he'0 : δ * α - -β * -γ ≠ 0 := by rw [he']; exact he
  obtain ⟨G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12⟩ :=
    int_factsG D (inv_mem hgN) hginv he'0
  rw [he'] at G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12
  -- valuations of the moduli
  have vX : ∀ X : ℤ, X ≠ 0 → vz p ((α * δ - β * γ) * X) = δ₀ + vz p X := fun X hX =>
    vz_mul he hX
  have hBe : e ≤ B := by simp only [B]; omega
  have hBN : vz p ((α * δ - β * γ) * N) ≤ B := by rw [vX _ hNz, vN]; simp only [B]; omega
  have hBε : vz p ((α * δ - β * γ) * (ϵ : ℤ)) ≤ B := by
    rw [vX _ hεz, vε]; simp only [B]; omega
  have hBh : vz p ((α * δ - β * γ) * (η : ℤ)) ≤ B := by rw [vX _ hhz, vh]; simp only [B]; omega
  -- the inequalities from g
  have c1 := le_vv2 hhz hBe F1
  have c2 := le_vv_sq one_ne_zero hBe F2
  have c3 := le_vv_sq (pow_ne_zero 2 hhz) hBN F3
  have c4 := le_vv2 (mul_ne_zero two0 hhz) hBε F4
  have c5 := le_vv2 (mul_ne_zero hnz hhz) hBe F5
  have c6 := le_vv_sq hnz hBe F6
  have c7 := le_vv_sq one_ne_zero hBe F7
  have c8 := le_vv2 (mul_ne_zero (mul_ne_zero two0 hnz) hhz) hBε F8
  have c9 := le_vv2 hNz hBe F9
  have c10 := le_vv2 hNz hBh F10
  have c11 := le_vv2 (mul_ne_zero hNz hhz) hBN F11
  have c12 := le_vv2 (mul_ne_zero two0 hNz) hBε F12
  -- and from g⁻¹
  have d1 := le_vv2 hhz hBe G1
  have d2 := le_vv_sq one_ne_zero hBe G2
  have d4 := le_vv2 (mul_ne_zero two0 hhz) hBε G4
  have d5 := le_vv2 (mul_ne_zero hnz hhz) hBe G5
  have d7 := le_vv_sq one_ne_zero hBe G7
  have d8 := le_vv2 (mul_ne_zero (mul_ne_zero two0 hnz) hhz) hBε G8
  have d10 := le_vv2 hNz hBh G10
  have d11 := le_vv2 (mul_ne_zero hNz hhz) hBN G11
  simp only [hb', hc', vX _ hNz, vX _ hεz, vX _ hhz, vz_mul two0 hhz, vz_mul hnz hhz, vz_mul (mul_ne_zero two0 hnz) hhz, vz_mul two0 hnz, vz_mul hNz hhz, vz_mul two0 hNz, vz_mul hhz hhz, pow_two, vN, vh, vn, vε, v2, v1] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 d1 d2 d4 d5 d7 d8 d10 d11
  -- the conditions C9–C12, C17, C18 with j: from N if ν = j, from γ_p otherwise
  obtain ⟨C9, C10, C11, C12, C17, C18⟩ : δ₀ ≤ j + b + c ∧ δ₀ + k ≤ j + a + b ∧
      δ₀ + ν ≤ j + k + c + d ∧ δ₀ ≤ e₂ + b + c ∧ δ₀ + k ≤ j + b + d ∧ δ₀ + ν ≤ j + k + c + a := by
    by_cases hνj : ν = j
    · refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    have hpN : p ∣ N := by
      by_contra hpN
      have : ν = 0 := Nat.factorization_eq_zero_of_not_dvd hpN
      omega
    obtain ⟨x, y, t, -, ⟨γp, hγp, hγm⟩, hs0, hvs⟩ := D.gamma p hp hpN (by omega)
    obtain ⟨S9, S10, S11, S12⟩ := int_facts_sG D hgN hg he hγp hγm
    obtain ⟨T9, T10, T11, T12⟩ := int_facts_sG D (inv_mem hgN) hginv he'0 hγp hγm
    rw [he'] at T9 T10 T11 T12
    have s9 := le_vv2 hs0 hBe S9
    have s10 := le_vv2 hs0 hBh S10
    have s11 := le_vv2 (mul_ne_zero hs0 hhz) hBN S11
    have s12 := le_vv2 (mul_ne_zero two0 hs0) hBε S12
    have t10 := le_vv2 hs0 hBh T10
    have t11 := le_vv2 (mul_ne_zero hs0 hhz) hBN T11
    simp only [hb', hc'] at t10 t11
    simp only [vX _ hNz, vX _ hεz, vX _ hhz, vz_mul hs0 hhz, vz_mul two0 hs0, hvs, vh, vN, vε,
      v2] at s9 s10 s11 s12 t10 t11
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hn2 : ν - 2 * k = nν := by omega
  rw [← hn2]
  omega

theorem newmanG {N : ℕ} [NeZero N] {g : SL2R} (D : NewmanData N Γ ϵ η) (hg : g ∈ NormG Γ) :
    IsNewmanFormH N η g := by
  obtain ⟨κ, α, β, γ, δ, hκ, hprim, hgm⟩ := exists_prim_formG D hg
  have hh := D.h_pos.ne'
  have hhr : (η : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  have hN := NeZero.ne N
  have hgS : (g : M2) = κ • Smat (η) α β γ δ := by rw [hgm]; rfl
  have hdet : κ ^ 2 * ((α * δ - β * γ : ℤ) : ℝ) = 1 := by
    have := g.2
    rw [hgS, det_smul, Fintype.card_fin, det_Smat hh] at this
    exact this
  have he : α * δ - β * γ ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have hepos : 0 < α * δ - β * γ := by
    have hκ2 : 0 < κ ^ 2 := by positivity
    have : (0 : ℝ) < ((α * δ - β * γ : ℤ) : ℝ) := by
      by_contra hc
      push Not at hc
      nlinarith
    exact_mod_cast this
  have hginv : ((g⁻¹ : SL2R) : M2) =
      κ • Smat (η) δ (-β) (-γ) α := by
    rw [coe_inv_of_coe_eq_smul hgm]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Smat] <;> ring
  have hloc := fun (p : ℕ) (hp : p.Prime) => local_conclusionG D hg hgS hginv he hprim hp
  have hn0 : nOf N η ≠ 0 := by intro h0; have := D.n_mul_sq; rw [h0, zero_mul] at this; omega
  have hnz : (nOf N η : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  -- e ∣ n, n ∣ γ, e ∣ α, e ∣ δ
  have hen : (α * δ - β * γ) ∣ (nOf N η : ℤ) := by
    refine dvd_of_forall_vz_le he hnz (fun p hp => ?_)
    have := hloc p hp
    simp only at this
    rw [vz_natCast]
    rcases this with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hnγ : (nOf N η : ℤ) ∣ γ := by
    by_cases hγ : γ = 0
    · rw [hγ]; exact dvd_zero _
    refine dvd_of_forall_vz_le hnz hγ (fun p hp => ?_)
    have := hloc p hp
    simp only [vv_of_ne hγ] at this
    rw [vz_natCast]
    rcases this with ⟨-, h2⟩ | ⟨-, -, h2, -⟩ <;> omega
  have heα : (α * δ - β * γ) ∣ α := by
    by_cases hα : α = 0
    · rw [hα]; exact dvd_zero _
    refine dvd_of_forall_vz_le he hα (fun p hp => ?_)
    have := hloc p hp
    simp only [vv_of_ne hα] at this
    rcases this with ⟨h1, -⟩ | ⟨h1, h2, -⟩ <;> omega
  have heδ : (α * δ - β * γ) ∣ δ := by
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
  set E := α * δ - β * γ
  -- e as a natural number
  set e : ℕ := E.toNat
  have hEe : (e : ℤ) = E := Int.toNat_of_nonneg hepos.le
  have he0 : 0 < e := by omega
  have her : (e : ℝ) = (E : ℝ) := by exact_mod_cast hEe
  have hsq : Real.sqrt e * Real.sqrt e = e := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hs0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 he0)).ne'
  refine ⟨a', β, c', d', e, he0, ⟨m.toNat, ?_⟩, ?_, κ * Real.sqrt e, ?_, ?_⟩
  · have hm0 : 0 ≤ m := by
      by_contra hneg
      push Not at hneg
      have : (nOf N η : ℤ) < 0 := by rw [hm]; exact mul_neg_of_pos_of_neg hepos hneg
      omega
    have : ((nOf N η : ℕ) : ℤ) = ((e * m.toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hm0, hEe]
      exact hm
    exact_mod_cast this
  · rw [hEe]
    have h1 : E = α * δ - β * γ := rfl
    rw [ha', hd', hc'] at h1
    simp only [nOf] at h1 ⊢
    linear_combination -h1
  · exact mul_self_eq_one_iff.1 (by
      rw [← pow_two, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), her]; exact hdet)
  · have hNr : (N : ℝ) = nOf N η * (η : ℝ) ^ 2 := by
      exact_mod_cast D.n_mul_sq.symm
    have hα' : (α : ℝ) = a' * e := by rw [her, ha']; push_cast; ring
    have hγ' : (γ : ℝ) = nOf N η * c' := by rw [hc']; push_cast; ring
    have hδ' : (δ : ℝ) = d' * e := by rw [her, hd']; push_cast; ring
    rw [hgm, mul_div_assoc, div_self hs0, mul_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hα', hγ', hδ', hNr] <;> field_simp <;> ring

/-!
# Γ_Δ(N), ε_Δ, h_Δ: basic facts

* membership in Γ_Δ(N) and its image in SL₂(ℝ); T, U ∈ Γ_Δ(N);
* ε_Δ ∣ N and ε_Δ ∣ d² − 1 for d ∈ Δ (`dvd_epsDelta_iff`), hence every element of Γ_Δ(N) lies in the
  lattice L_{ε_Δ} (`inLe_of_mem_GammaDeltaR`);
* v_p(h_Δ) = min(v_p(ε_Δ), ⌊v_p(N)/2⌋) (`factorization_hDelta`);
* the element γ_p ∈ Γ_Δ(N) (`exists_gamma_delta`): if v_p(ε_Δ) < v_p(N), some d ∈ Δ has
  v_p(d² − 1) = v_p(ε_Δ), and [[x, y], [N, d]] has v_p(d − x) = v_p(ε_Δ).
-/




variable {N : ℕ} {Δ : SG N}

theorem mem_toR {Γ : Subgroup SL2Z} {g : SL2R} : g ∈ toR Γ ↔ ∃ γ ∈ Γ, ofZ γ = g :=
  Subgroup.mem_map

theorem ofZ_mem_toR {Γ : Subgroup SL2Z} {γ : SL2Z} (h : γ ∈ Γ) : ofZ γ ∈ toR Γ :=
  Subgroup.mem_map_of_mem _ h

theorem coe_ofZ (γ : SL2Z) :
    (ofZ γ : M2) = !![(γ 0 0 : ℝ), γ 0 1; γ 1 0, γ 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem GammaDelta_le_Gamma0 : GammaDelta N Δ ≤ CongruenceSubgroup.Gamma0 N := fun _ h => h.1

theorem GammaDeltaR_le_Gamma0R : GammaDeltaR N Δ ≤ Gamma0R N :=
  Subgroup.map_mono GammaDelta_le_Gamma0

/-- An integer matrix of determinant 1. -/
def mkSL (a b c d : ℤ) (h : a * d - b * c = 1) : SL2Z := ⟨!![a, b; c, d], by
  rw [det_fin_two_of]; exact h⟩

theorem mkSL_mem_GammaDelta {a b c d : ℤ} (h : a * d - b * c = 1) (hc : (N : ℤ) ∣ c)
    {u : (ZMod N)ˣ} (hu : u ∈ Δ) (hud : (u : ZMod N) = (d : ZMod N)) :
    mkSL a b c d h ∈ GammaDelta N Δ := by
  refine ⟨?_, u, hu, by simpa [mkSL] using hud⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  simpa [mkSL] using (ZMod.intCast_zmod_eq_zero_iff_dvd c N).2 hc

theorem coe_ofZ_mkSL {a b c d : ℤ} (h : a * d - b * c = 1) :
    (ofZ (mkSL a b c d h) : M2) = !![(a : ℝ), b; c, d] := by
  rw [coe_ofZ]; rfl

theorem matT_mem_GammaDeltaR : matT ∈ GammaDeltaR N Δ := by
  have h : (1 : ℤ) * 1 - 1 * 0 = 1 := by norm_num
  refine mem_toR.2 ⟨mkSL 1 1 0 1 h, mkSL_mem_GammaDelta h (dvd_zero _) (Subgroup.one_mem _)
    (by simp), ?_⟩
  apply Subtype.ext
  rw [coe_ofZ_mkSL]
  simp [matT]

theorem matU_mem_GammaDeltaR : matU N ∈ GammaDeltaR N Δ := by
  have h : (1 : ℤ) * 1 - 0 * N = 1 := by norm_num
  refine mem_toR.2 ⟨mkSL 1 0 N 1 h, mkSL_mem_GammaDelta h (dvd_refl _) (Subgroup.one_mem _)
    (by simp), ?_⟩
  apply Subtype.ext
  rw [coe_ofZ_mkSL]
  simp [matU]

/-! ### ε_Δ -/

theorem dvd_epsDelta_iff [NeZero N] {m : ℕ} :
    m ∣ epsDelta N Δ ↔ m ∣ N ∧ ∀ u ∈ Δ, m ∣ (u : ZMod N).val ^ 2 - 1 := by
  classical
  unfold epsDelta
  rw [Nat.dvd_gcd_iff, Finset.dvd_gcd_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem epsDelta_dvd [NeZero N] : epsDelta N Δ ∣ N := (dvd_epsDelta_iff.1 dvd_rfl).1

theorem epsDelta_dvd_val [NeZero N] {u : (ZMod N)ˣ} (hu : u ∈ Δ) :
    epsDelta N Δ ∣ (u : ZMod N).val ^ 2 - 1 := (dvd_epsDelta_iff.1 dvd_rfl).2 u hu

theorem epsDelta_pos [NeZero N] : 0 < epsDelta N Δ :=
  Nat.pos_of_dvd_of_pos epsDelta_dvd (Nat.pos_of_ne_zero (NeZero.ne N))

/-- For N ≥ 2 a unit has a positive representative. -/
theorem one_le_val_unit (hN : 2 ≤ N) (u : (ZMod N)ˣ) : 1 ≤ (u : ZMod N).val := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
  by_contra h
  have h0 : (u : ZMod N).val = 0 := by omega
  rw [ZMod.val_eq_zero] at h0
  exact u.ne_zero h0

/-- The integer form of ε_Δ ∣ val(u)² − 1. -/
theorem epsDelta_dvd_val_int [NeZero N] {u : (ZMod N)ˣ} (hu : u ∈ Δ) :
    (epsDelta N Δ : ℤ) ∣ ((u : ZMod N).val : ℤ) ^ 2 - 1 := by
  by_cases hN : N = 1
  · have : epsDelta N Δ = 1 := Nat.dvd_one.1 (hN ▸ epsDelta_dvd)
    rw [this]; exact one_dvd _
  have h1 := one_le_val_unit (by have := NeZero.ne N; omega) u
  have := Int.natCast_dvd_natCast.2 (epsDelta_dvd_val hu)
  rwa [Nat.cast_sub (Nat.one_le_pow _ _ h1), Nat.cast_pow, Nat.cast_one] at this

/-- Every element of Γ_Δ(N) lies in the lattice L_{ε_Δ}. -/
theorem inLe_of_mem_GammaDeltaR [NeZero N] {Y : SL2R} (hY : Y ∈ GammaDeltaR N Δ) :
    InLe N (epsDelta N Δ) (Y : M2) := by
  obtain ⟨γ, ⟨h0, u, hu, hγ⟩, rfl⟩ := mem_toR.1 hY
  have hc :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 h0)
  refine ⟨γ 0 0, γ 0 1, γ 1 0, γ 1 1, coe_ofZ γ, hc, ?_⟩
  ·
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rwa [det_fin_two] at this
    set v : ℤ := ((u : ZMod N).val : ℤ)
    have hv : (N : ℤ) ∣ γ 1 1 - v := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp only [v, Int.cast_natCast, ZMod.natCast_zmod_val]
      exact hγ
    have hεN : (epsDelta N Δ : ℤ) ∣ N := Int.natCast_dvd_natCast.2 epsDelta_dvd
    obtain ⟨k1, hk1⟩ := hεN.trans hv
    obtain ⟨k2, hk2⟩ := epsDelta_dvd_val_int hu
    obtain ⟨k3, hk3⟩ := hεN.trans hc
    refine ⟨-(γ 1 1 * (γ 0 1 * k3)) + γ 0 0 * ((γ 1 1 + v) * k1 + k2), ?_⟩
    linear_combination -(γ 1 1) * hdet - (γ 1 1) * (γ 0 1) * hk3 + (γ 0 0) * (γ 1 1 + v) * hk1 +
      (γ 0 0) * hk2

/-! ### h_Δ -/

theorem factorization_hDelta [NeZero N] (p : ℕ) :
    (hDelta N Δ).factorization p =
      min ((epsDelta N Δ).factorization p) (N.factorization p / 2) := by
  unfold hDelta
  rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero),
    Finset.sum_apply']
  rw [Finset.sum_congr rfl (fun q hq => by
    rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_apply]),
    Finset.sum_ite_eq']
  split_ifs with hp
  · rfl
  · have : N.factorization p = 0 := by
      rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
    simp [this]

/-!
# The generalized Newman bound (`newman_delta'`)

Γ_Δ(N) satisfies the hypotheses `NewmanData N (Γ_Δ(N)) ε_Δ h_Δ` of the generic Newman argument
(`NewmanGen.lean`); the only new ingredient is the element γ_p (`exists_gamma_delta`):
if j = v_p(ε_Δ) < ν = v_p(N), then p^{j+1} ∣ N, so p^{j+1} ∤ d² − 1 for some d ∈ Δ (otherwise
p^{j+1} ∣ ε_Δ), while p^j ∣ ε_Δ ∣ d² − 1.  With t = d and x t − y N = 1, the matrix
[[x, y], [N, t]] lies in Γ_Δ(N), and t(t − x) ≡ t² − 1 (mod N) gives v_p(t − x) = j (`gamma_val`).
-/




variable {N : ℕ} {Δ : SG N}

/-- The element γ_p of Γ_Δ(N). -/
theorem exists_gamma_delta [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hj : (epsDelta N Δ).factorization p < N.factorization p) :
    ∃ x y t : ℤ, x * t - y * N = 1 ∧
      (∃ γ ∈ GammaDeltaR N Δ, (γ : M2) = !![(x : ℝ), y; N, t]) ∧
      t - x ≠ 0 ∧ vz p (t - x) = (epsDelta N Δ).factorization p := by
  have hN := NeZero.ne N
  have hN2 := le_trans hp.two_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hpN)
  set j := (epsDelta N Δ).factorization p
  set ν := N.factorization p with hν
  have hε0 : epsDelta N Δ ≠ 0 := epsDelta_pos.ne'
  -- some u ∈ Δ with p^{j+1} ∤ val(u)² − 1
  obtain ⟨u, hu, hnd⟩ : ∃ u ∈ Δ, ¬ p ^ (j + 1) ∣ (u : ZMod N).val ^ 2 - 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : p ^ (j + 1) ∣ N := (hp.pow_dvd_iff_le_factorization hN).2 (by omega)
    have h2 : p ^ (j + 1) ∣ epsDelta N Δ := dvd_epsDelta_iff.2 ⟨h1, hcon⟩
    have := (hp.pow_dvd_iff_le_factorization hε0).1 h2
    omega
  have hpj :=
    (Nat.ordProj_dvd (epsDelta N Δ) p).trans (epsDelta_dvd_val hu)
  set v := (u : ZMod N).val
  have hcopN := ZMod.val_coe_unit_coprime u
  -- Bézout: x v − y N = 1
  have hb := Int.gcd_eq_gcd_ab v N
  rw [Int.gcd_natCast_natCast, hcopN] at hb
  set x := Int.gcdA v N
  set y := -Int.gcdB v N
  have hdet : x * v - y * N = 1 := by
    push_cast at hb
    simp only [y]
    linear_combination -hb
  refine ⟨x, y, v, hdet, ?_, ?_⟩
  · exact ⟨ofZ (mkSL x y N v hdet), ofZ_mem_toR (mkSL_mem_GammaDelta hdet (dvd_refl _) hu (by simp [v])),
      coe_ofZ_mkSL hdet⟩
  · -- the valuation, by `gamma_val` with the roles of x and t exchanged
    have hdet2 : (v : ℤ) * x - y * N = 1 := by linear_combination hdet
    have hpν : (p : ℤ) ^ ν ∣ (N : ℤ) := by exact_mod_cast Nat.ordProj_dvd N p
    have hpv : IsCoprime (p : ℤ) (v : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.Coprime.coprime_dvd_right hpN hcopN).symm
    have hcast : (((v ^ 2 - 1 : ℕ)) : ℤ) = (v : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (one_le_val_unit hN2 u))]; push_cast; ring
    have hρ1 : (p : ℤ) ^ j ∣ 1 - (v : ℤ) ^ 2 := by
      simpa [hcast] using (Int.natCast_dvd_natCast.2 hpj).neg_right
    have hρ2 : ¬ (p : ℤ) ^ (j + 1) ∣ 1 - (v : ℤ) ^ 2 := by
      intro hd
      apply hnd
      have hd' : (p : ℤ) ^ (j + 1) ∣ (((v ^ 2 - 1 : ℕ)) : ℤ) := by
        rw [hcast]; have := hd.neg_right; convert this using 1; ring
      exact_mod_cast hd'
    rcases gamma_val hp hdet2 hpν (by simp) hpv hρ1 hρ2 with h | ⟨-, hne, hval⟩
    · omega
    · refine ⟨fun h0 => hne (by linear_combination -h0), ?_⟩
      rw [show (v : ℤ) - x = -(x - v) by ring, vz_neg]
      exact hval

/-- Γ_Δ(N) satisfies the hypotheses of the generic Newman argument. -/
theorem newmanData_delta (N : ℕ) [NeZero N] (Δ : SG N) :
    NewmanData N (GammaDeltaR N Δ) (epsDelta N Δ) (hDelta N Δ) where
  le := GammaDeltaR_le_Gamma0R
  T_mem := matT_mem_GammaDeltaR
  U_mem := matU_mem_GammaDeltaR
  inL := fun _ hY => inLe_of_mem_GammaDeltaR hY
  eps_dvd := epsDelta_dvd
  h_pos := by unfold hDelta; exact Finset.prod_pos (fun q hq => pow_pos (Nat.pos_of_mem_primeFactors hq) _)
  h_sq_dvd := by
    have hN := NeZero.ne N
    have hh : hDelta N Δ ≠ 0 := by
      unfold hDelta
      exact Finset.prod_ne_zero_iff.2 (fun q hq => pow_ne_zero _ (Nat.pos_of_mem_primeFactors hq).ne')
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hh) hN]
    intro p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_hDelta]
    omega
  h_fact := factorization_hDelta
  gamma := fun _ hp hpN hj => exists_gamma_delta hp hpN hj

/-- **The generalized Newman bound.** -/
theorem newman_delta' {N : ℕ} [NeZero N] (Δ : SG N) {g : SL2R}
    (hg : g ∈ NormG (GammaDeltaR N Δ)) : IsNewmanFormH N (hDelta N Δ) g :=
  newmanG (newmanData_delta N Δ) hg

/-!
# §D: the sanity statements for Γ_Δ(N), ε_Δ, h_Δ

* Γ_{(ℤ/N)ˣ}(N) = Γ₀(N) and Γ_{±1}(N) = Γ₁(N) ⊔ {±1};
* ε_⊤ = gcd(N, 24): gcd(N, 24) ∣ ε_Δ for every Δ (units modulo a divisor of 24 square to 1), and
  ε_⊤ ∣ gcd(N, 24) by the element γ_p of the T2 proof (`exists_gamma_p`), whose lower right entry is
  a unit t with v_p(t − x) = v_p(gcd(N, 24));
* ε_{±1} = N; h(N) ∣ h_Δ; h_Δ² ∣ N; h_⊤ = h(N); the form of `newman_delta` with h(N) is (8′).
-/




variable {N : ℕ}

/-! ### ε_Δ -/

/-- Units modulo a divisor of 24 square to 1, so gcd(N, 24) ∣ ε_Δ. -/
theorem gcd24_dvd_epsDelta [NeZero N] (Δ : SG N) : Nat.gcd N 24 ∣ epsDelta N Δ := by
  refine dvd_epsDelta_iff.2 ⟨Nat.gcd_dvd_left _ _, fun u _ => ?_⟩
  set k := Nat.gcd N 24
  by_cases hN : N = 1
  · subst hN; simp [k]
  have hN2 : 2 ≤ N := by have := NeZero.ne N; omega
  have h1 := one_le_val_unit hN2 u
  set a : ℤ := (((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)
  set d : ℤ := ((u : ZMod N).val : ℤ)
  have had : a * d ≡ 1 [ZMOD N] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simp [a, d]
  have hadk : a * d ≡ 1 [ZMOD k] := had.of_dvd (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _))
  have hk := modEq_of_mul_modEq_one (Nat.gcd_dvd_right _ _) hadk
  have hdd : d * d ≡ 1 [ZMOD k] := ((hk.symm.mul_right d).trans (by rw [mul_comm] at hadk ⊢; exact hadk))
  have : (k : ℤ) ∣ d ^ 2 - 1 := by
    have := (Int.ModEq.dvd hdd.symm)
    rw [pow_two]
    exact this
  have h2 : (k : ℤ) ∣ (((u : ZMod N).val ^ 2 - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ h1)]; push_cast; exact this
  exact_mod_cast h2

/-! ### h_Δ -/

theorem hDelta_ne_zero [NeZero N] (Δ : SG N) : hDelta N Δ ≠ 0 :=
  (newmanData_delta N Δ).h_pos.ne'

theorem hDelta_sq_dvd' (N : ℕ) [NeZero N] (Δ : SG N) : hDelta N Δ ^ 2 ∣ N :=
  (newmanData_delta N Δ).h_sq_dvd

/-!
# §D (rest) and §C: Γ₀(N) normalizes Γ_Δ(N); the index i_Δ; Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) and the index

* `Gamma0R_le_normG_GammaDeltaR'`: the lower right entry of g γ g⁻¹ is ≡ γ₁₁ mod N for g, γ ∈ Γ₀(N);
* `relindex_GammaDelta'`: Γ_Δ(N) ∩ Γ₀(N) is the preimage of Δ under the surjection
  Γ₀(N) → (ℤ/N)ˣ, γ ↦ γ₁₁;
* `normG_GammaDeltaR_le_Norm0'`: `newman_delta'` with h_Δ = h(N) gives (8′), and (8′)-matrices normalize Γ₀(N)
  (frozen T1);
* `card_BG_GammaDeltaR'`: Γ_Δ ≤ Γ₀ ≤ Nor(Γ_Δ) ≤ Nor(Γ₀), so [Nor(Γ_Δ) : Γ_Δ] = i_Δ · [Nor(Γ_Δ) : Γ₀(N)],
  and Nor(Γ_Δ)/Γ₀(N) is the set of elements of B(N) normalizing Γ_Δ(N);
* `newman_delta_not_sufficient'`: S₂ at N = 8.
-/




variable {N : ℕ}

/-! ### Γ₀(N) normalizes Γ_Δ(N) -/

theorem toR_le_normG {H Γ : Subgroup SL2Z} (h : ∀ g ∈ H, ∀ γ ∈ Γ, g * γ * g⁻¹ ∈ Γ) :
    toR H ≤ NormG (toR Γ) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro Y
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨g * γ * g⁻¹, h g hg γ hγ, ?_⟩
    simp [map_mul, map_inv]
  · rintro ⟨γ', hγ', hY⟩
    refine ⟨g⁻¹ * γ' * g⁻¹⁻¹, h _ (inv_mem hg) γ' hγ', ?_⟩
    simp only [map_mul, map_inv, inv_inv] at hY ⊢
    rw [hY]
    group

/-- The lower right entry of g γ g⁻¹ mod N, for g, γ ∈ Γ₀(N). -/
theorem conj_entry_11 {g γ : SL2Z} (hg : ((g 1 0 : ℤ) : ZMod N) = 0)
    (hγ : ((γ 1 0 : ℤ) : ZMod N) = 0) :
    (((g * γ * g⁻¹) 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := by
  have hdet : ((g 0 0 : ℤ) : ZMod N) * ((g 1 1 : ℤ) : ZMod N) = 1 := by
    have h1 := congrArg (fun x : ℤ => (x : ZMod N)) g.2
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h1
    rw [hg, mul_zero, sub_zero] at h1
    exact h1
  have e : ((g * γ * g⁻¹) 1 1 : ℤ) = (g 1 0 * γ 0 0 + g 1 1 * γ 1 0) * (-g 0 1) +
      (g 1 0 * γ 0 1 + g 1 1 * γ 1 1) * g 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  rw [e]
  push_cast
  rw [hg, hγ]
  linear_combination ((γ 1 1 : ℤ) : ZMod N) * hdet

theorem conj_mem_GammaDelta {Δ : SG N} {g γ : SL2Z}
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) (hγ : γ ∈ GammaDelta N Δ) :
    g * γ * g⁻¹ ∈ GammaDelta N Δ := by
  obtain ⟨h0, u, hu, hud⟩ := hγ
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg h0) (Subgroup.inv_mem _ hg), u, hu, ?_⟩
  rw [hud, conj_entry_11 (CongruenceSubgroup.Gamma0_mem.1 hg) (CongruenceSubgroup.Gamma0_mem.1 h0)]

theorem Gamma0R_le_normG_GammaDeltaR' (N : ℕ) (Δ : SG N) :
    Gamma0R N ≤ NormG (GammaDeltaR N Δ) :=
  toR_le_normG (fun _ hg _ hγ => conj_mem_GammaDelta hg hγ)

/-! ### The index i_Δ -/

/-- γ ↦ γ₁₁ mod N, as a homomorphism Γ₀(N) → (ℤ/N)ˣ. -/
def unitMap (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

theorem coe_unitMap (γ : CongruenceSubgroup.Gamma0 N) :
    ((unitMap N γ : (ZMod N)ˣ) : ZMod N) = (((γ : SL2Z) 1 1 : ℤ) : ZMod N) := rfl

theorem unitMap_surjective [NeZero N] : Function.Surjective (unitMap N) := by
  intro u
  set v := (u : ZMod N).val
  have hcopN := ZMod.val_coe_unit_coprime u
  have hb := Int.gcd_eq_gcd_ab v N
  rw [Int.gcd_natCast_natCast, hcopN] at hb
  have hdet : Int.gcdA v N * v - (-Int.gcdB v N) * N = 1 := by
    push_cast at hb; linear_combination -hb
  refine ⟨⟨mkSL _ _ _ _ hdet, CongruenceSubgroup.Gamma0_mem.2 (by simp [mkSL])⟩, Units.ext ?_⟩
  rw [coe_unitMap]
  simp [mkSL, v]

theorem GammaDelta_subgroupOf (Δ : SG N) :
    (GammaDelta N Δ).subgroupOf (CongruenceSubgroup.Gamma0 N) = Δ.comap (unitMap N) := by
  ext γ
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  constructor
  · rintro ⟨-, u, hu, hud⟩
    have : unitMap N γ = u := Units.ext (by rw [coe_unitMap, hud])
    rwa [this]
  · intro h
    exact ⟨γ.2, unitMap N γ, h, rfl⟩

theorem relindex_GammaDelta' (N : ℕ) [NeZero N] (Δ : SG N) :
    (GammaDelta N Δ).relIndex (CongruenceSubgroup.Gamma0 N) = Δ.index := by
  rw [Subgroup.relIndex, GammaDelta_subgroupOf, Subgroup.index_comap_of_surjective _ unitMap_surjective]

/-! ### Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) -/

/-! ### The index [Nor(Γ_Δ) : Γ_Δ] = i_Δ · s_Δ -/

theorem ofZ_injective : Function.Injective (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom ℝ)) := by
  intro a b h
  ext i j
  have := congrArg (fun g : SL2R => (g : M2) i j) h
  simpa using this

/-! ### S₂ at N = 8 -/

/-!
# §G: conjugation by diag(M, 1): X_Δ(N) ≅ X₁(M, N/M) and X_Δ(M²) ≅ X(M)

D = projSL diag(M, 1) = diag(√M, 1/√M) acts by D [[a, b], [c, d]] D⁻¹ = [[a, Mb], [c/M, d]].
For M² ∣ N and Δ = {d ≡ ±1 mod N/M} this maps Γ_Δ(N) onto ±(Γ(M) ∩ Γ₁(N/M)): for γ ∈ Γ_Δ(N) with
d ≡ ε (ε = ±1) mod N/M, ε·DγD⁻¹ ∈ Γ(M) ∩ Γ₁(N/M) (M ∣ N/M, and a ≡ d⁻¹); conversely the preimage of
ζ ∈ Γ(M) ∩ Γ₁(N/M) is [[a, b/M], [Mc, d]] ∈ Γ_Δ(N), and −1 ∈ Γ_Δ(N).
-/




/-- D = diag(M, 1) in SL₂(ℝ). -/
abbrev Dm (M : ℕ) : SL2R := projSL !![(M : ℝ), 0; 0, 1]

theorem coe_Dm {M : ℕ} (hM : 0 < M) :
    (Dm M : M2) = !![Real.sqrt M, 0; 0, (Real.sqrt M)⁻¹] := by
  have hdet : 0 < (!![(M : ℝ), 0; 0, 1] : M2).det := by
    rw [det_fin_two_of]; simp; exact_mod_cast hM
  rw [Dm, coe_projSL _ hdet]
  simp only [det_fin_two_of, mul_one, mul_zero, sub_zero]
  mx
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]

/-- Conjugation by D: [[a, b], [c, d]] ↦ [[a, Mb], [c/M, d]]. -/
theorem coe_conj_Dm {M : ℕ} (hM : 0 < M) {Y : SL2R} {a b c d : ℝ}
    (hY : (Y : M2) = !![a, b; c, d]) :
    ((MulAut.conj (Dm M) Y : SL2R) : M2) =
      !![a, M * b; c / M, d] := by
  rw [MulAut.conj_apply, coe_conj, coe_Dm hM, hY, adjugate_fin_two_of]
  mx [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> (try rw [Real.sq_sqrt (Nat.cast_nonneg _)]) <;> ring

/-!
# §G: Nor(±Γ(N)) = Nor(Γ(N)) = SL₂(ℤ); the S₇ example at level 49

* For Δ = {d ≡ ±1 mod M} at level M², M ∣ ε_Δ, so h_Δ = M and n_Δ = 1 (`hDelta_deltaPm_sq`).
* Nor(±Γ(M)) = D Nor(Γ_Δ(M²)) D⁻¹ (`conj_GammaDelta_sq'`, `Subgroup.map_equiv_normalizer_eq`), and by
  `newman_delta'` every element of Nor(Γ_Δ(M²)) is ±[[a, b/M], [Mc, d]] (e ∣ n_Δ = 1), whose D-conjugate
  ±[[a, b], [c, d]] is integral.
* Nor(Γ(N)) ≤ Nor(±Γ(N)) since −1 is central; SL₂(ℤ) normalizes both since Γ(N) is normal.
* S₇ = D⁻¹ T D normalizes Γ_Δ(49) because T normalizes ±Γ(7); S₇ ∉ Nor(Γ₀(49)) by the frozen T2
  (h(49) = 1 would force 7 b = ±1).
-/




theorem ofZ_neg (γ : SL2Z) : ofZ (-γ) = -ofZ γ := by
  ext i j; simp [SpecialLinearGroup.coe_neg]

/-! ### h_Δ for Δ = ±1 mod M at level M² -/

/-! ### Nor(±Γ(N)) and Nor(Γ(N)) -/

/-! ### S₇ at level 49 -/

/-!
# §K, easy part: Γ₀(N) and the w_Q normalize ±Γ₁(N); the case Q = 1; the exception N = 4

* ι_Q fixes ±1, so every w_Q normalizes Γ_{±1}(N) (`al_mem_normG_iff`).
* (ℤ/4)ˣ = {±1}, so ±Γ₁(4) = Γ₀(4), whose normalizer contains S₂ (h(4) = 2); S₂ is not an
  Atkin–Lehner element (its (0,0) entry would be √Q·x = 1, forcing Q = 1, and then y = 1/2).
-/




theorem isAtkinLehner_one_iff' (N : ℕ) (g : SL2R) : IsAtkinLehner N 1 g ↔ g ∈ Gamma0R N := by
  constructor
  · rintro ⟨x, y, z, w, hdet, hgm⟩
    refine mem_Gamma0R_of_entries x y (N * z) w ?_ (dvd_mul_right _ _)
    rw [hgm]
    mx
  · intro hg
    obtain ⟨a, b, c, d, hdet, ⟨z, rfl⟩, hgm⟩ := exists_entries_of_mem_Gamma0R hg
    refine ⟨a, b, z, d, by push_cast; linear_combination hdet, ?_⟩
    rw [hgm]
    mx

/-! ### N = 4 -/

/-!
# §K: the diamonds, the quotient (ℤ/2)^{ω(N)}, and the order 2^{ω(N)} φ(N)/2

* `eq_of_isAtkinLehner_both`: an element is an Atkin–Lehner element for at most one Q ∥ N (the (0,1)
  entries give y²Q' = y'²Q, while p ∣ Q, p ∤ Q' forces p ∤ y).
* `isAtkinLehner_mul_gen`: w_{Q₁} w_{Q₂} is an Atkin–Lehner element for (Q₁/G)(Q₂/G), G = gcd(Q₁, Q₂).
* σ(g) = (p ↦ [p ∣ Q(g)]) is a homomorphism Nor(±Γ₁(N)) → (ℤ/2)^{primes of N} (N ≠ 4), trivial on
  ±Γ₁(N), onto (w_{Q_T}, Q_T = ∏_{p ∈ T} p^{v_p(N)}), with kernel the image of Γ₀(N).
* The diamonds Γ₀(N)/±Γ₁(N) have order [(ℤ/N)ˣ : {±1}] = φ(N)/2, and are normal since
  Nor(±Γ₁(N)) ≤ Nor(Γ₀(N)) (for N = 4 because ±Γ₁(4) = Γ₀(4)).
-/




variable {N : ℕ}

/-! ### Uniqueness of Q -/

/-! ### The general product law -/

theorem isAtkinLehner_mul_gen [NeZero N] {Q₁ Q₂ : ℕ} (hQ₁ : Q₁ ∣ N) (hQ₂ : Q₂ ∣ N)
    {g₁ g₂ : SL2R} (h₁ : IsAtkinLehner N Q₁ g₁) (h₂ : IsAtkinLehner N Q₂ g₂) :
    IsAtkinLehner N (Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂)) (g₁ * g₂) := by
  have hQ10 : Q₁ ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ₁)
  have hQ20 : Q₂ ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ₂)
  obtain ⟨G, hGdef⟩ : ∃ G, G = Nat.gcd Q₁ Q₂ := ⟨_, rfl⟩
  rw [← hGdef]
  have hG0 := hGdef ▸ Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hQ10)
  obtain ⟨q₁, hq₁⟩ : G ∣ Q₁ := hGdef ▸ Nat.gcd_dvd_left Q₁ Q₂
  obtain ⟨q₂, hq₂⟩ : G ∣ Q₂ := hGdef ▸ Nat.gcd_dvd_right Q₁ Q₂
  have e1 : Q₁ / G = q₁ := by rw [hq₁, Nat.mul_div_cancel_left _ hG0]
  have e2 : Q₂ / G = q₂ := by rw [hq₂, Nat.mul_div_cancel_left _ hG0]
  rw [e1, e2]
  have hq10 : q₁ ≠ 0 := by rintro rfl; simp at hq₁; exact hQ10 hq₁
  have hq20 : q₂ ≠ 0 := by rintro rfl; simp at hq₂; exact hQ20 hq₂
  have hL : G * q₁ * q₂ ∣ N := by
    have h := Nat.lcm_dvd hQ₁ hQ₂
    have : Nat.lcm Q₁ Q₂ = G * q₁ * q₂ := by
      rw [Nat.lcm, ← hGdef, hq₁, hq₂]
      rw [show G * q₁ * (G * q₂) = G * (G * q₁ * q₂) by ring, Nat.mul_div_cancel_left _ hG0]
    rwa [this] at h
  obtain ⟨L, hLN⟩ := hL
  obtain ⟨x₁, y₁, z₁, w₁, hd₁, hg₁⟩ := h₁
  obtain ⟨x₂, y₂, z₂, w₂, hd₂, hg₂⟩ := h₂
  have hGz : (G : ℤ) ≠ 0 := by exact_mod_cast hG0.ne'
  have hq1z : (q₁ : ℤ) ≠ 0 := by exact_mod_cast hq10
  have hq2z : (q₂ : ℤ) ≠ 0 := by exact_mod_cast hq20
  have r₁ : (G : ℤ) * q₁ * x₁ * w₁ - q₂ * L * y₁ * z₁ = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hGz hq1z)
    rw [hq₁, hLN] at hd₁; push_cast at hd₁; linear_combination hd₁
  have r₂ : (G : ℤ) * q₂ * x₂ * w₂ - q₁ * L * y₂ * z₂ = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hGz hq2z)
    rw [hq₂, hLN] at hd₂; push_cast at hd₂; linear_combination hd₂
  refine ⟨G * x₁ * x₂ + L * y₁ * z₂, q₁ * x₁ * y₂ + q₂ * y₁ * w₂, q₂ * z₁ * x₂ + q₁ * w₁ * z₂,
    L * z₁ * y₂ + G * w₁ * w₂, ?_, ?_⟩
  · rw [hLN]; push_cast
    linear_combination ((q₁ : ℤ) * q₂ * (G * q₂ * x₂ * w₂ - q₁ * L * y₂ * z₂)) * r₁ +
      ((q₁ : ℤ) * q₂) * r₂
  · have hsq : Real.sqrt Q₁ * Real.sqrt Q₂ = G * Real.sqrt ((q₁ * q₂ : ℕ) : ℝ) := by
      rw [← Real.sqrt_mul (Nat.cast_nonneg _), hq₁, hq₂]
      push_cast
      rw [show (G : ℝ) * q₁ * (G * q₂) = G ^ 2 * (q₁ * q₂) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]
    rw [Matrix.SpecialLinearGroup.coe_mul, hg₁, hg₂, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← mul_inv, hsq, mul_inv, mul_comm (G : ℝ)⁻¹, mul_smul]
    congr 1
    rw [hLN, hq₁, hq₂]
    push_cast
    mx [Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring

/-! ### Exact divisors -/

/-! ### Nor(±Γ₁(N)) ≤ Nor(Γ₀(N)); the diamonds are normal -/

/-! ### The order of the diamonds -/

/-! ### σ : Nor(±Γ₁(N)) → (ℤ/2)^{primes of N} -/

section Sigma

variable [NeZero N] (hN : N ≠ 4)

theorem mul_div_gcd_dvd {Q₁ Q₂ : ℕ} (hQ₁ : Q₁ ∣ N) (hQ₂ : Q₂ ∣ N) :
    Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂) ∣ N := by
  have h1 : Q₁ / Nat.gcd Q₁ Q₂ * (Q₂ / Nat.gcd Q₁ Q₂) ∣ Q₁ / Nat.gcd Q₁ Q₂ * Q₂ :=
    mul_dvd_mul_left _ (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _))
  have h2 : Q₁ / Nat.gcd Q₁ Q₂ * Q₂ = Nat.lcm Q₁ Q₂ := by
    rw [Nat.lcm, Nat.div_mul_right_comm (Nat.gcd_dvd_left _ _)]
  rw [h2] at h1
  exact h1.trans (Nat.lcm_dvd hQ₁ hQ₂)

end Sigma

/-!
# §M: M_Δ = D⁻¹ Γ₀(n_Δ)⁺ D is the set of matrices of the generalized Newman bound

* The Atkin–Lehner elements of level n (Q ∣ n) form a subgroup (`alSub`): products by the general
  product law `isAtkinLehner_mul_gen`, inverses by the adjugate.  So Γ₀(n)⁺ = `alSub n`.
* D⁻¹ w D, for w = (1/√Q)[[Qx, y], [nz, Qw]], is (1/√Q)[[Qx, y/h], [Nz/h, Qw]] (N = n h²): the form of
  `IsNewmanFormH N h_Δ` with e = Q.  Conversely D g D⁻¹ of such a g is ±w_e.
-/




/-! ### Γ₀(n)⁺ -/

theorem isAtkinLehner_inv {n Q : ℕ} {g : SL2R} (hg : IsAtkinLehner n Q g) :
    IsAtkinLehner n Q g⁻¹ := by
  obtain ⟨x, y, z, w, hdet, hgm⟩ := hg
  refine ⟨w, -y, -z, x, by linear_combination hdet, ?_⟩
  rw [coe_inv_of_coe_eq_smul hgm]
  congr 1
  mx

/-- The Atkin–Lehner elements of level n (Q ∣ n) form a subgroup. -/
def alSub (n : ℕ) [NeZero n] : Subgroup SL2R where
  carrier := {g | ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g}
  one_mem' := ⟨1, one_dvd n, (isAtkinLehner_one_iff' n 1).2 (Subgroup.one_mem _)⟩
  mul_mem' := by
    rintro g g' ⟨Q, hQ, hg⟩ ⟨Q', hQ', hg'⟩
    exact ⟨_, mul_div_gcd_dvd hQ hQ', isAtkinLehner_mul_gen hQ hQ' hg hg'⟩
  inv_mem' := by
    rintro g ⟨Q, hQ, hg⟩
    exact ⟨Q, hQ, isAtkinLehner_inv hg⟩

theorem Gamma0Plus_eq (n : ℕ) [NeZero n] : Gamma0Plus n = alSub n :=
  Subgroup.closure_eq (alSub n)

theorem mem_Gamma0Plus {n : ℕ} [NeZero n] {g : SL2R} :
    g ∈ Gamma0Plus n ↔ ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g := by
  rw [Gamma0Plus_eq]; rfl

/-! ### n_Δ -/

theorem nDelta_mul (N : ℕ) [NeZero N] (Δ : SG N) :
    nDelta N Δ * hDelta N Δ ^ 2 = N :=
  Nat.div_mul_cancel (hDelta_sq_dvd' N Δ)

instance nDelta_neZero (N : ℕ) [NeZero N] (Δ : SG N) : NeZero (nDelta N Δ) :=
  ⟨fun h => NeZero.ne N (by rw [← nDelta_mul N Δ, h, zero_mul])⟩

theorem hDelta_pos (N : ℕ) [NeZero N] (Δ : SG N) : 0 < hDelta N Δ :=
  Nat.pos_of_ne_zero (hDelta_ne_zero Δ)

/-! ### Conjugation by D⁻¹ -/

/-- Conjugation by D⁻¹: [[a, b], [c, d]] ↦ [[a, b/M], [Mc, d]]. -/
theorem coe_conj_Dm_inv {M : ℕ} (hM : 0 < M) {Y : SL2R} {a b c d : ℝ}
    (hY : (Y : M2) = !![a, b; c, d]) :
    ((MulAut.conj (Dm M)⁻¹ Y : SL2R) : M2) =
      !![a, b / M; M * c, d] := by
  rw [MulAut.conj_apply, inv_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_Dm hM, hY,
    adjugate_fin_two_of]
  mx [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> (try rw [Real.sq_sqrt (Nat.cast_nonneg _)]) <;> ring

theorem conj_Dm_inv_conj_Dm (M : ℕ) (g : SL2R) :
    MulAut.conj (Dm M)⁻¹ (MulAut.conj (Dm M) g) = g := by
  simp [MulAut.conj_apply, mul_assoc]

/-! ### M_Δ -/

theorem mem_MDelta_iff {N : ℕ} [NeZero N] {Δ : SG N} {g : SL2R} :
    g ∈ MDelta N Δ ↔ IsNewmanFormH N (hDelta N Δ) g := by
  have hh := hDelta_pos N Δ
  have hNr : (N : ℝ) = nDelta N Δ * (hDelta N Δ : ℝ) ^ 2 := by
    exact_mod_cast (nDelta_mul N Δ).symm
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨Q, hQ, x, y, z, w', hdet, hwm⟩ := mem_Gamma0Plus.1 hw
    have hQ0 := Nat.pos_of_dvd_of_pos hQ (Nat.pos_of_ne_zero (NeZero.ne _))
    refine ⟨x, y, z, w', Q, hQ0, hQ, by
      rw [show N / hDelta N Δ ^ 2 = nDelta N Δ from rfl]; linear_combination hdet, 1, Or.inl rfl, ?_⟩
    have hwm' : (w : M2) =
        !![(Real.sqrt Q)⁻¹ * (Q * x), (Real.sqrt Q)⁻¹ * y;
          (Real.sqrt Q)⁻¹ * (nDelta N Δ * z), (Real.sqrt Q)⁻¹ * (Q * w')] := by
      rw [hwm]; mx
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [coe_conj_Dm_inv hh hwm']
    mx [hNr] <;> field_simp <;> (try ring) <;> simp
  · rintro ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩
    refine ⟨MulAut.conj (Dm (hDelta N Δ)) g, ?_, conj_Dm_inv_conj_Dm _ g⟩
    have hgm' : (g : M2) =
        !![ε / Real.sqrt e * (a * e), ε / Real.sqrt e * (b / hDelta N Δ);
          ε / Real.sqrt e * (N * c / hDelta N Δ), ε / Real.sqrt e * (d * e)] := by
      rw [hgm]; mx
    have hc := coe_conj_Dm hh hgm'
    have hn : N / hDelta N Δ ^ 2 = nDelta N Δ := rfl
    rw [hn] at hdet he
    refine mem_Gamma0Plus.2 ⟨e, he, ?_⟩
    rcases hε with rfl | rfl
    · refine ⟨a, b, c, d, by linear_combination hdet, ?_⟩
      rw [hc]; mx [hNr] <;> field_simp <;> (try ring) <;> simp
    · refine ⟨-a, -b, -c, -d, by linear_combination hdet, ?_⟩
      rw [hc]; mx [hNr] <;> field_simp <;> (try ring) <;> simp

theorem coe_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (MDelta N Δ : Set SL(2, ℝ)) = {g | IsNewmanFormH N (hDelta N Δ) g} :=
  Set.ext fun _ => mem_MDelta_iff

theorem Gamma0R_le_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Gamma0R N ≤ MDelta N Δ := by
  intro γ hγ
  obtain ⟨a, b, c', d, hdet, ⟨z, rfl⟩, hγm⟩ := exists_entries_of_mem_Gamma0R hγ
  have hhr : (hDelta N Δ : ℝ) ≠ 0 := by exact_mod_cast (hDelta_pos N Δ).ne'
  have hNz : (N : ℤ) = nDelta N Δ * (hDelta N Δ : ℤ) ^ 2 := by
    exact_mod_cast (nDelta_mul N Δ).symm
  refine mem_MDelta_iff.2 ⟨a, b * hDelta N Δ, z * hDelta N Δ, d, 1, one_pos, one_dvd _, ?_, 1,
    Or.inl rfl, ?_⟩
  · have hn : N / hDelta N Δ ^ 2 = nDelta N Δ := rfl
    rw [hn]; push_cast; rw [hNz] at hdet; linear_combination hdet
  · rw [hγm]
    mx <;> field_simp

theorem normG_GammaDeltaR_le_MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    NormG (GammaDeltaR N Δ) ≤ MDelta N Δ :=
  fun _ hg => mem_MDelta_iff.2 (newman_delta' Δ hg)

/-!
# §M: the σH coset description, finiteness, and the count of `aut_orders.py`

* `exists_hermite`: an integer matrix W of positive determinant is σ·[[a, b], [0, d]] with σ ∈ SL₂(ℤ),
  a d = det W, 0 ≤ b < d (a = gcd of the first column, Bézout, then b reduced mod d).
* `exists_sigmaH`: for g ∈ M_Δ, h√e·g is an integer matrix of determinant h²e ∣ N; dividing its Hermite form
  by gcd(a, b, d) gives a primitive Hermite form, and σ = γ₀ r with r ∈ R, γ₀ ∈ Γ₀(N).
* `sigmaH_unique`: if c σH = γ c' σ'H', then M = σ'⁻¹γ⁻¹σ ∈ SL₂(ℤ) is upper triangular with M H ∝ H';
  primitivity gives a = a', d = d', b' ≡ b mod d, so M = ±1 and σ = σ'.
* The map (σ, H) ↦ (σH)⁻¹ Γ₀(N) is a bijection onto K/Γ₀(N) for Γ₀(N) ≤ K ≤ M_Δ (`relIndex_eq_card_sigmaH`).
-/




/-! ### Hermite normal form of a 2×2 integer matrix -/

theorem exists_hermite (w00 w01 w10 w11 : ℤ) (hW : 0 < w00 * w11 - w01 * w10) :
    ∃ σ : SL2Z, ∃ a b d : ℕ, 0 < a ∧ 0 < d ∧ (a : ℤ) * d = w00 * w11 - w01 * w10 ∧ b < d ∧
      w00 = σ 0 0 * a ∧ w01 = σ 0 0 * b + σ 0 1 * d ∧ w10 = σ 1 0 * a ∧
      w11 = σ 1 0 * b + σ 1 1 * d := by
  have hg0 : 0 < Int.gcd w00 w10 := by
    apply Int.gcd_pos_iff.2
    by_contra h
    push_neg at h
    rw [h.1, h.2] at hW; simp at hW
  have hg0z : ((Int.gcd w00 w10 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  obtain ⟨p, hp⟩ := Int.gcd_dvd_left w00 w10
  obtain ⟨q, hq⟩ := Int.gcd_dvd_right w00 w10
  have hbez0 := Int.gcd_eq_gcd_ab w00 w10
  generalize Int.gcdA w00 w10 = A at hbez0
  generalize Int.gcdB w00 w10 = B at hbez0
  generalize Int.gcd w00 w10 = G at hbez0 hp hq hg0 hg0z
  have hbez : p * A + q * B = 1 := by
    apply mul_left_cancel₀ hg0z
    linear_combination (-1 : ℤ) * hbez0 + (-A) * hp + (-B) * hq

  set δ : ℤ := p * w11 - q * w01 with hδdef
  have hdetW : w00 * w11 - w01 * w10 = G * δ := by rw [hp, hq, hδdef]; ring
  have hδ : 0 < δ := by rw [hdetW] at hW; nlinarith
  set β : ℤ := A * w01 + B * w11 with hβdef
  set k : ℤ := β / δ with hkdef
  set r : ℤ := β % δ with hrdef
  have hβ : δ * k + r = β := by rw [hkdef, hrdef]; exact Int.mul_ediv_add_emod β δ
  have hr0 := hrdef ▸ Int.emod_nonneg β hδ.ne'
  have hrδ := hrdef ▸ Int.emod_lt_of_pos β hδ
  have hr' := Int.toNat_of_nonneg hr0
  have hδ' := Int.toNat_of_nonneg hδ.le
  refine ⟨mkSL p (p * k - B) q (q * k + A) (by linear_combination hbez), G, r.toNat, δ.toNat,
    hg0, by omega, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [hδ', hdetW]
  · change w00 = p * G; rw [hp]; ring
  · change w01 = p * ((r.toNat : ℕ) : ℤ) + (p * k - B) * ((δ.toNat : ℕ) : ℤ)
    rw [hr', hδ']
    linear_combination (-w01) * hbez + (-p) * hβ + (-p) * hβdef + B * hδdef
  · change w10 = q * G; rw [hq]; ring
  · change w11 = q * ((r.toNat : ℕ) : ℤ) + (q * k + A) * ((δ.toNat : ℕ) : ℤ)
    rw [hr', hδ']
    linear_combination (-w11) * hbez + (-q) * hβ + (-q) * hβdef - A * hδdef

/-! ### Existence of σH -/

theorem exists_sigmaH {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {R : Set SL(2, ℤ)}
    (hR : IsGamma0Reps N R) {g : SL(2, ℝ)} (hg : g ∈ MDelta N Δ) :
    ∃ γ ∈ Gamma0R N, ∃ r ∈ R, ∃ a b d : ℕ, IsHermiteN N a b d ∧ ∃ c : ℝ, c ≠ 0 ∧
      ((γ * g : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        c • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) := by
  obtain ⟨a, b, c, d, e, he0, he, hdet, ε, hε, hgm⟩ := mem_MDelta_iff.1 hg
  have hh := hDelta_pos N Δ
  set h := hDelta N Δ
  have hn : N / hDelta N Δ ^ 2 = nDelta N Δ := rfl
  rw [hn] at he hdet
  have hNz : (N : ℤ) = nDelta N Δ * (h : ℤ) ^ 2 := by exact_mod_cast (nDelta_mul N Δ).symm
  have hWdet : (a * e * h) * (d * e * h) - b * (N * c) = (h : ℤ) ^ 2 * e := by
    rw [hNz]; linear_combination (h : ℤ) ^ 2 * hdet
  have hWpos : 0 < (a * e * h : ℤ) * (d * e * h) - b * (N * c) := by rw [hWdet]; positivity
  obtain ⟨σ, A, B, D, hA, hD, hAD, hBD, h00, h01, h10, h11⟩ := exists_hermite _ _ _ _ hWpos
  set t := Nat.gcd (Nat.gcd A B) D with htdef
  have ht0 : 0 < t := Nat.gcd_pos_of_pos_right _ hD
  obtain ⟨A', hA'⟩ : t ∣ A := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨B', hB'⟩ : t ∣ B := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨D', hD'⟩ : t ∣ D := Nat.gcd_dvd_right _ _
  have hADn : A * D = h ^ 2 * e := by
    have : (A : ℤ) * D = (h : ℤ) ^ 2 * e := hAD.trans hWdet
    exact_mod_cast this
  have hHerm : IsHermiteN N A' B' D' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hA'] at hA; exact Nat.pos_of_mul_pos_left hA
    · rw [hD'] at hD; exact Nat.pos_of_mul_pos_left hD
    · have h1 : A' * D' ∣ A * D := ⟨t * t, by rw [hA', hD']; ring⟩
      have h2 : A * D ∣ N := by
        rw [hADn, ← nDelta_mul N Δ, mul_comm (nDelta N Δ)]
        exact mul_dvd_mul_left _ he
      exact h1.trans h2
    · rw [hB', hD'] at hBD; exact Nat.lt_of_mul_lt_mul_left hBD
    · have h1 : t = t * Nat.gcd (Nat.gcd A' B') D' := by
        conv_lhs => rw [htdef, hA', hB', hD', Nat.gcd_mul_left, Nat.gcd_mul_left]
      have h2 : t * Nat.gcd (Nat.gcd A' B') D' = t * 1 := by rw [← h1, mul_one]
      exact Nat.eq_of_mul_eq_mul_left ht0 h2
  obtain ⟨r, ⟨hrR, hσr⟩, -⟩ := hR σ
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hse : Real.sqrt e ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast he0)).ne'
  have hεr : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht0.ne'
  set κ := ε / (Real.sqrt e * h)
  refine ⟨ofZ (r * σ⁻¹), ?_, r, hrR, A', B', D', hHerm, κ * t, ?_, ?_⟩
  · have : r * σ⁻¹ = (σ * r⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.mem_map_of_mem _ (inv_mem hσr)
  · exact mul_ne_zero (div_ne_zero hεr (mul_ne_zero hse hhr)) htr
  · have step1 : (g : M2) =
        κ • !![(a : ℝ) * e * h, b; N * c, d * e * h] := by
      rw [hgm]; mx [κ] <;> field_simp
    have R00 : (a : ℝ) * e * h = σ 0 0 * (t * A') := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h00; push_cast at this; rw [this, hA']; push_cast; ring
    have R01 : (b : ℝ) = σ 0 0 * (t * B') + σ 0 1 * (t * D') := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h01; push_cast at this; rw [this, hB', hD']; push_cast
      ring
    have R10 : (N : ℝ) * c = σ 1 0 * (t * A') := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h10; push_cast at this; rw [this, hA']; push_cast; ring
    have R11 : (d : ℝ) * e * h = σ 1 0 * (t * B') + σ 1 1 * (t * D') := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h11; push_cast at this; rw [this, hB', hD']; push_cast
      ring
    have step2 : !![(a : ℝ) * e * h, b; N * c, d * e * h] =
        (t : ℝ) • ((ofZ σ : M2) * hermMat A' B' D') := by
      rw [coe_ofZ σ, hermMat]
      mx
      · linear_combination R00
      · linear_combination R01
      · linear_combination R10
      · linear_combination R11
    rw [Matrix.SpecialLinearGroup.coe_mul, step1, step2, smul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
      show r * σ⁻¹ * σ = r by group]

/-! ### Uniqueness of σH -/

theorem neg_one_mem_Gamma0 (N : ℕ) : (-1 : SL2Z) ∈ CongruenceSubgroup.Gamma0 N :=
  CongruenceSubgroup.Gamma0_mem.2 (by simp)

/-- Bézout for gcd(x, y, z) = 1. -/
theorem bezout3 {x y z : ℕ} (h : Nat.gcd (Nat.gcd x y) z = 1) :
    ∃ u v w : ℤ, u * x + v * y + w * z = 1 := by
  have h1 := Nat.gcd_eq_gcd_ab (Nat.gcd x y) z
  have h2 := Nat.gcd_eq_gcd_ab x y
  rw [h, h2] at h1
  exact ⟨Nat.gcdA x y * Nat.gcdA (Nat.gcd x y) z, Nat.gcdB x y * Nat.gcdA (Nat.gcd x y) z,
    Nat.gcdB (Nat.gcd x y) z, by push_cast at h1 ⊢; linear_combination -h1⟩

/-- The integer core of the uniqueness: if M = [[s, m], [0, s]] (s = ±1) and M H ∝ H' for primitive
Hermite forms H, H', then H = H' and m = 0. -/
theorem hermite_unique_int {a b d a' b' d' : ℕ} {s m : ℤ} (ha : 0 < a) (hd : 0 < d)
    (hbd : b < d) (hbd' : b' < d') (hprim : Nat.gcd (Nat.gcd a b) d = 1)
    (hprim' : Nat.gcd (Nat.gcd a' b') d' = 1) (hs : s * s = 1)
    (X1 : s * a * b' = (s * b + m * d) * a') (X2 : s * a * d' = s * d * a') :
    a = a' ∧ b = b' ∧ d = d' ∧ m = 0 := by
  set az : ℤ := (a : ℤ)
  set az' : ℤ := (a' : ℤ)
  obtain ⟨u, v, w, huvw⟩ := bezout3 hprim
  obtain ⟨u', v', w', huvw'⟩ := bezout3 hprim'
  set k := s * m with hk
  have Y1 : az * b' = (b + k * d) * a' := by
    linear_combination s * X1 - (az * b' - b * a') * hs
  have Y2 : az * d' = d * a' := by
    linear_combination s * X2 - (az * d' - d * a') * hs
  have hdiv1 : az = a' * (u' * a + v' * (b + k * d) + w' * d) := by
    linear_combination (-az) * huvw' + v' * Y1 + w' * Y2
  have hdiv2 : az' = a * (u * a' + v * (b' - k * d') + w * d') := by
    linear_combination (-az') * huvw - v * Y1 + v * k * Y2 - w * Y2
  have haa : a = a' := by
    have h1 : az' ∣ a := ⟨_, hdiv1⟩
    have h2 : az ∣ a' := ⟨_, hdiv2⟩
    exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.1 h2) (Int.natCast_dvd_natCast.1 h1)
  subst haa
  have haz : az ≠ 0 := by rw [show az = (a : ℤ) from rfl]; exact_mod_cast ha.ne'
  have hdd : d = d' := by
    have : az * d' = a * d := by linear_combination Y2
    exact_mod_cast (mul_left_cancel₀ haz this).symm
  subst hdd
  have hbk : (b' : ℤ) - b = k * d := by
    have : az * b' = a * (b + k * d) := by linear_combination Y1
    linear_combination mul_left_cancel₀ haz this
  have hdvd : (d : ℤ) ∣ (b' : ℤ) - b := ⟨k, by rw [hbk]; ring⟩
  have habs : |(b' : ℤ) - b| < d := by rw [abs_lt]; constructor <;> omega
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hbb : b = b' := by omega
  subst hbb
  have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hk0 : k = 0 := by
    have : k * d = 0 := by rw [← hbk, h0]
    exact (mul_eq_zero.1 this).resolve_right hdz
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact (mul_eq_zero.1 (hk ▸ hk0)).resolve_left hs0

theorem sigmaH_unique {N : ℕ} [NeZero N] {R : Set SL(2, ℤ)} (hR : IsGamma0Reps N R)
    {r r' : SL(2, ℤ)} (hr : r ∈ R) (hr' : r' ∈ R) {a b d a' b' d' : ℕ}
    (hH : IsHermiteN N a b d) (hH' : IsHermiteN N a' b' d') {c c' : ℝ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    {γ : SL(2, ℝ)} (hγ : γ ∈ Gamma0R N)
    (h : c • ((ofZ r : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a b d) =
      (γ : Matrix (Fin 2) (Fin 2) ℝ) * (c' • ((ofZ r' : Matrix (Fin 2) (Fin 2) ℝ) * hermMat a' b' d'))) :
    r = r' ∧ a = a' ∧ b = b' ∧ d = d' := by
  obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
  obtain ⟨ha, hd, -, hbd, hprim⟩ := hH
  obtain ⟨ha', hd', -, hbd', hprim'⟩ := hH'
  obtain ⟨M, hMdef⟩ : ∃ M : SL2Z, M = r'⁻¹ * γ₀⁻¹ * r := ⟨_, rfl⟩
  have key : c • ((ofZ M : M2) * hermMat a b d) = c' • hermMat a' b' d' := by
    calc c • ((ofZ M : M2) * hermMat a b d)
        = (ofZ (r'⁻¹ * γ₀⁻¹) : M2) *
            (c • ((ofZ r : M2) * hermMat a b d)) := by
          rw [hMdef, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
            ← map_mul]
      _ = (ofZ (r'⁻¹ * γ₀⁻¹) : M2) *
            ((ofZ γ₀ : M2) *
              (c' • ((ofZ r' : M2) * hermMat a' b' d'))) := by rw [h]
      _ = c' • hermMat a' b' d' := by
          rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
            ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
            ← map_mul, show r'⁻¹ * γ₀⁻¹ * γ₀ * r' = 1 by group, map_one,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  have entry : ∀ i j, c * ((ofZ M : M2) * hermMat a b d) i j =
      c' * hermMat a' b' d' i j := fun i j => by
    have := congrFun (congrFun key i) j
    simpa using this
  have e00 := entry 0 0
  have e01 := entry 0 1
  have e10 := entry 1 0
  have e11 := entry 1 1
  simp only [coe_ofZ, hermMat, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, mul_zero, add_zero] at e00 e01 e10 e11
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hM10 : M 1 0 = 0 := by
    have h1 := (mul_eq_zero.1 e10).resolve_left hc
    exact_mod_cast (mul_eq_zero.1 h1).resolve_right har
  rw [hM10] at e11
  simp only [Int.cast_zero, zero_mul, zero_add] at e11
  have hdetM : M 0 0 * M 1 1 = 1 := by
    have := M.2; rw [det_fin_two, hM10, mul_zero, sub_zero] at this; exact this
  have X1 : (M 0 0 * a) * b' = (M 0 0 * b + M 0 1 * d) * a' := by
    have := cross_of_prop hc (κ' := c') (x := M 0 0 * a) (y := M 0 0 * b + M 0 1 * d) (x' := a')
      (y' := b') (by push_cast; exact e00) (by push_cast; exact e01)
    exact_mod_cast this
  have X2 : (M 0 0 * a) * d' = (M 1 1 * d) * a' := by
    have := cross_of_prop hc (κ' := c') (x := M 0 0 * a) (y := M 1 1 * d) (x' := a') (y' := d')
      (by push_cast; exact e00) (by push_cast; exact e11)
    exact_mod_cast this
  have hss : M 1 1 = M 0 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdetM with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  rw [hss] at X2 hdetM
  obtain ⟨haa, hbb, hdd, hM01⟩ :=
    hermite_unique_int (s := M 0 0) (m := M 0 1) ha hd hbd hbd' hprim hprim' hdetM X1 X2
  refine ⟨?_, haa, hbb, hdd⟩
  have hr_eq : r = γ₀ * r' * M := by rw [hMdef]; group
  have hrr : r * r'⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdetM with ⟨h1, -⟩ | ⟨h1, -⟩
    · have hM1 : M = 1 := by
        mx [h1, hss, hM01, hM10]
      rw [hr_eq, hM1, mul_one, mul_inv_cancel_right]; exact hγ₀
    · have hM1 : M = -1 := by
        mx [h1, hss, hM01, hM10]
      have : γ₀ * r' * M * r'⁻¹ = γ₀ * -1 := by
        rw [hM1, mul_neg_one, neg_mul, mul_neg_one, mul_inv_cancel_right]
      rw [hr_eq, this]
      exact mul_mem hγ₀ (neg_one_mem_Gamma0 N)
  exact (hR r).unique ⟨hr, by rw [mul_inv_cancel]; exact one_mem _⟩ ⟨hr', hrr⟩

/-!
# §M: [K : Γ₀(N)] = #{(σ, H) : σH ∈ K} for Γ₀(N) ≤ K ≤ M_Δ, finiteness, and the index i_Δ·[Nor : Γ₀]

The map (σ, H) ↦ (σH)⁻¹ Γ₀(N) ∈ K/Γ₀(N) (left cosets; σH rescaled into SL₂(ℝ) by `projSL`) is
* onto: for k ∈ K, `exists_sigmaH` applied to k⁻¹ ∈ M_Δ gives γ k⁻¹ = c σH, and det = 1 forces
  projSL(σH) = ±γ k⁻¹;
* injective: `sigmaH_unique`.
The pairs form a finite set (R is finite since [SL₂(ℤ) : Γ₀(N)] < ∞, and a, b, d ≤ N), so [M_Δ : Γ₀(N)] < ∞.
-/




/-! ### Sets of representatives -/

theorem exists_Gamma0Reps (N : ℕ) : ∃ R : Set SL(2, ℤ), IsGamma0Reps N R := by
  refine ⟨Set.range (fun q : SL2Z ⧸ CongruenceSubgroup.Gamma0 N => (Quotient.out q)⁻¹), ?_⟩
  intro σ
  refine ⟨(Quotient.out (QuotientGroup.mk σ⁻¹ : SL2Z ⧸ CongruenceSubgroup.Gamma0 N))⁻¹,
    ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · have h := QuotientGroup.out_eq' (QuotientGroup.mk σ⁻¹ : SL2Z ⧸ CongruenceSubgroup.Gamma0 N)
    have := QuotientGroup.eq.1 h.symm
    simpa using this
  · rintro r ⟨⟨q, rfl⟩, hq⟩
    congr 1
    have h1 : (QuotientGroup.mk σ⁻¹ : SL2Z ⧸ CongruenceSubgroup.Gamma0 N) = q := by
      rw [← QuotientGroup.out_eq' q]
      apply QuotientGroup.eq.2
      simpa using hq
    rw [h1]

theorem finite_of_isGamma0Reps {N : ℕ} [NeZero N] {R : Set SL2Z} (hR : IsGamma0Reps N R) :
    R.Finite := by
  have : Finite (SL2Z ⧸ CongruenceSubgroup.Gamma0 N) := Subgroup.finite_quotient_of_finiteIndex
  refine Set.finite_coe_iff.1 (Finite.of_injective
    (fun r : R => (QuotientGroup.mk (r : SL2Z)⁻¹ : SL2Z ⧸ CongruenceSubgroup.Gamma0 N)) ?_)
  intro r r' hrr
  have h1 : (r : SL2Z) * (r' : SL2Z)⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
    have := QuotientGroup.eq.1 hrr
    simpa using this
  exact Subtype.ext ((hR r).unique ⟨r.2, by rw [mul_inv_cancel]; exact one_mem _⟩ ⟨r'.2, h1⟩)

/-! ### The pairs (σ, H) -/

/-- The pairs (σ, H), σ ∈ R, H a Hermite form, with σH (rescaled) in K. -/
abbrev SigmaHSet (N : ℕ) (R : Set SL2Z) (K : Subgroup SL2R) : Type :=
  {x : SL2Z × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
    projSL ((ofZ x.1 : M2) * hermMat x.2.1 x.2.2.1 x.2.2.2) ∈ K}

theorem det_sigmaH (r : SL2Z) (a b d : ℕ) :
    ((ofZ r : M2) * hermMat a b d).det = a * d := by
  rw [det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, hermMat, det_fin_two_of]; ring

theorem coe_projSL_sigmaH (r : SL2Z) {a b d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    ((projSL ((ofZ r : M2) * hermMat a b d) : SL2R) :
        M2) =
      (Real.sqrt (a * d))⁻¹ • ((ofZ r : M2) * hermMat a b d) := by
  rw [coe_projSL _ (by rw [det_sigmaH]; positivity), det_sigmaH]

theorem finite_SigmaHSet {N : ℕ} [NeZero N] {R : Set SL2Z} (hR : IsGamma0Reps N R)
    (K : Subgroup SL2R) : Finite (SigmaHSet N R K) := by
  have hRf := finite_of_isGamma0Reps hR
  have hT :=
    hRf.prod ((Set.finite_Iic N).prod ((Set.finite_Iic N).prod (Set.finite_Iic N)))
  have hsub : {x : SL2Z × ℕ × ℕ × ℕ | x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2} ⊆
      R ×ˢ (Set.Iic N ×ˢ (Set.Iic N ×ˢ Set.Iic N)) := by
    rintro ⟨r, a, b, d⟩ ⟨hr, ha, hd, hadN, hbd, -⟩
    have hN := Nat.pos_of_ne_zero (NeZero.ne N)
    have h1 := Nat.le_of_dvd hN hadN
    refine ⟨hr, ?_, ?_, ?_⟩ <;> simp only [Set.mem_Iic] <;> nlinarith
  have := (hT.subset hsub).to_subtype
  exact Finite.of_injective
    (fun x : SigmaHSet N R K => (⟨x.1, x.2.1, x.2.2.1⟩ :
      {x : SL2Z × ℕ × ℕ × ℕ | x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2}))
    (fun x y h => Subtype.ext (by have := congrArg Subtype.val h; exact this))

theorem neg_one_mem_Gamma0R (N : ℕ) : (-1 : SL2R) ∈ Gamma0R N := by
  have h : ofZ (-1) = -1 := by rw [ofZ_neg]; simp
  rw [← h]
  exact Subgroup.mem_map_of_mem _ (neg_one_mem_Gamma0 N)

/-- The map (σ, H) ↦ (σH)⁻¹ Γ₀(N). -/
def sigmaHMap (N : ℕ) (R : Set SL2Z) (K : Subgroup SL2R) :
    SigmaHSet N R K → K ⧸ (Gamma0R N).subgroupOf K :=
  fun x => QuotientGroup.mk ⟨(projSL ((ofZ x.1.1 : M2) *
    hermMat x.1.2.1 x.1.2.2.1 x.1.2.2.2))⁻¹, K.inv_mem x.2.2.2⟩

theorem sigmaHMap_surjective {N : ℕ} [NeZero N] (Δ : SG N) {R : Set SL2Z}
    (hR : IsGamma0Reps N R) {K : Subgroup SL2R} (hK0 : Gamma0R N ≤ K) (hKM : K ≤ MDelta N Δ) :
    Function.Surjective (sigmaHMap N R K) := by
  intro y
  obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective y
  have hgM := hKM (K.inv_mem hk)
  obtain ⟨γ, hγ, r, hr, a, b, d, hH, c, hc, heq⟩ := exists_sigmaH Δ hR hgM
  set P := projSL ((ofZ r : M2) * hermMat a b d)
  have ha := hH.1
  have hd := hH.2.1
  have hP' := coe_projSL_sigmaH r (b := b) ha hd
  -- det = 1 forces c = ±(√(ad))⁻¹
  have hdet : c ^ 2 * (a * d) = 1 := by
    have h1 := congrArg Matrix.det heq
    rw [Matrix.SpecialLinearGroup.det_coe, det_smul, Fintype.card_fin, det_sigmaH] at h1
    exact h1.symm
  have hsq : 0 < (a : ℝ) * d := by positivity
  have hs0 := (Real.sqrt_pos.2 hsq).ne'
  have hcs : (c * Real.sqrt (a * d)) ^ 2 = 1 := by rw [mul_pow, Real.sq_sqrt hsq.le, hdet]
  have hPm : (P : M2) =
      (c * Real.sqrt (a * d)) • ((γ * k⁻¹ : SL2R) : M2) := by
    rw [hP', heq, smul_smul]
    congr 1
    field_simp
    rw [Real.sq_sqrt hsq.le]; linear_combination -hdet
  have hu := mul_self_eq_one_iff.1
    (show (c * Real.sqrt (a * d)) * (c * Real.sqrt (a * d)) = 1 by rw [← sq]; exact hcs)
  have hPK : P ∈ K ∧ P * k ∈ Gamma0R N := by
    rcases hu with hu | hu
    · have hPe : P = γ * k⁻¹ := Subtype.ext (by rw [hPm, hu, one_smul])
      refine ⟨hPe ▸ mul_mem (hK0 hγ) (K.inv_mem hk), ?_⟩
      rw [hPe, inv_mul_cancel_right]; exact hγ
    · have hPe : P = -1 * (γ * k⁻¹) := Subtype.ext (by
        rw [hPm, hu, neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, neg_one_smul])
      refine ⟨hPe ▸ mul_mem (hK0 (neg_one_mem_Gamma0R N)) (mul_mem (hK0 hγ) (K.inv_mem hk)), ?_⟩
      rw [hPe, mul_assoc, inv_mul_cancel_right]
      exact mul_mem (neg_one_mem_Gamma0R N) hγ
  refine ⟨⟨(r, a, b, d), hr, hH, hPK.1⟩, ?_⟩
  apply QuotientGroup.eq.2
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  exact hPK.2

theorem sigmaHMap_injective {N : ℕ} [NeZero N] {R : Set SL2Z} (hR : IsGamma0Reps N R)
    {K : Subgroup SL2R} : Function.Injective (sigmaHMap N R K) := by
  rintro ⟨⟨r, a, b, d⟩, hr, hH, hPK⟩ ⟨⟨r', a', b', d'⟩, hr', hH', hPK'⟩ hxy
  have h1 := QuotientGroup.eq.1 hxy
  rw [Subgroup.mem_subgroupOf] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h1
  set P := projSL ((ofZ r : M2) * hermMat a b d)
  set P' := projSL ((ofZ r' : M2) * hermMat a' b' d')
  obtain ⟨γ, hγdef⟩ : ∃ γ, γ = P * P'⁻¹ := ⟨_, rfl⟩
  rw [← hγdef] at h1
  have hPP : P = γ * P' := by rw [hγdef]; group
  have hm := congrArg (fun g : SL2R => (g : M2)) hPP
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [coe_projSL_sigmaH r hH.1 hH.2.1, coe_projSL_sigmaH r' hH'.1 hH'.2.1] at hm
  have hsq : 0 < (a : ℝ) * d := by have := hH.1; have := hH.2.1; positivity
  have hsq' : 0 < (a' : ℝ) * d' := by have := hH'.1; have := hH'.2.1; positivity
  obtain ⟨h1', h2, h3, h4⟩ := sigmaH_unique hR hr hr' hH hH'
    (inv_ne_zero (Real.sqrt_pos.2 hsq).ne') (inv_ne_zero (Real.sqrt_pos.2 hsq').ne') h1 hm
  subst h1' h2 h3 h4
  rfl

/-- [K : Γ₀(N)] is the number of pairs (σ, H) with σH ∈ K, for Γ₀(N) ≤ K ≤ M_Δ. -/
theorem relIndex_eq_card_sigmaH {N : ℕ} [NeZero N] (Δ : SG N) {R : Set SL2Z}
    (hR : IsGamma0Reps N R) {K : Subgroup SL2R} (hK0 : Gamma0R N ≤ K) (hKM : K ≤ MDelta N Δ) :
    (Gamma0R N).relIndex K = Nat.card (SigmaHSet N R K) :=
  (Nat.card_congr (Equiv.ofBijective _
    ⟨sigmaHMap_injective hR, sigmaHMap_surjective Δ hR hK0 hKM⟩)).symm

theorem relIndex_normG_eq_card_sigmaH {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {R : Set SL(2, ℤ)}
    (hR : IsGamma0Reps N R) :
    (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) =
      Nat.card {x : SL(2, ℤ) × ℕ × ℕ × ℕ // x.1 ∈ R ∧ IsHermiteN N x.2.1 x.2.2.1 x.2.2.2 ∧
        projSL ((ofZ x.1 : Matrix (Fin 2) (Fin 2) ℝ) * hermMat x.2.1 x.2.2.1 x.2.2.2) ∈
          NormG (GammaDeltaR N Δ)} :=
  relIndex_eq_card_sigmaH Δ hR (Gamma0R_le_normG_GammaDeltaR' N Δ) (normG_GammaDeltaR_le_MDelta N Δ)

/-! ### Finiteness and the index -/

theorem relIndex_Gamma0R_MDelta_ne_zero (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (Gamma0R N).relIndex (MDelta N Δ) ≠ 0 := by
  obtain ⟨R, hR⟩ := exists_Gamma0Reps N
  have := finite_SigmaHSet hR (MDelta N Δ)
  have hfin :=
    Finite.of_surjective _ (sigmaHMap_surjective Δ hR (Gamma0R_le_MDelta N Δ) le_rfl)
  exact Subgroup.index_ne_zero_iff_finite.2 hfin

theorem relIndex_GammaDeltaR_Gamma0R (N : ℕ) [NeZero N] (Δ : SG N) :
    (GammaDeltaR N Δ).relIndex (Gamma0R N) = Δ.index := by
  rw [GammaDeltaR, toR, Gamma0R, Subgroup.relIndex_map_map_of_injective _ _ ofZ_injective,
    relindex_GammaDelta']

theorem card_BG_GammaDeltaR_eq (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) := by
  have h1 : GammaDeltaR N Δ ≤ Gamma0R N := GammaDeltaR_le_Gamma0R
  have h2 := Gamma0R_le_normG_GammaDeltaR' N Δ
  have hBG : Nat.card (BG (GammaDeltaR N Δ)) =
      (GammaDeltaR N Δ).relIndex (NormG (GammaDeltaR N Δ)) := rfl
  rw [hBG, ← Subgroup.relIndex_mul_relIndex (hHK := h1) (hKL := h2), relIndex_GammaDeltaR_Gamma0R]

theorem relIndex_Gamma0R_normG_ne_zero (N : ℕ) [NeZero N] (Δ : SG N) :
    (Gamma0R N).relIndex (NormG (GammaDeltaR N Δ)) ≠ 0 := by
  have h := Subgroup.relIndex_mul_relIndex (hHK := Gamma0R_le_normG_GammaDeltaR' N Δ)
    (hKL := normG_GammaDeltaR_le_MDelta N Δ)
  intro h0
  rw [h0, zero_mul] at h
  exact relIndex_Gamma0R_MDelta_ne_zero N Δ h.symm

theorem finite_BG_GammaDeltaR (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    Finite (BG (GammaDeltaR N Δ)) := by
  have h : Nat.card (BG (GammaDeltaR N Δ)) ≠ 0 := by
    rw [card_BG_GammaDeltaR_eq]
    exact mul_ne_zero Subgroup.index_ne_zero_of_finite (relIndex_Gamma0R_normG_ne_zero N Δ)
  exact (Nat.card_ne_zero.1 h).2

/-!
# §H: h_Δ = h(N) unless one of the cases i)–iii) of `hDelta_eq_hPart_iff`, and conversely

Prime by prime: v_p(h_Δ) = min(v_p(ε_Δ), ⌊v_p(N)/2⌋) and v_p(h(N)) = min(v_p(gcd(N, 24)), ⌊v_p(N)/2⌋), with
v_p(gcd(N, 24)) ≤ v_p(ε_Δ) ≤ v_p(N).  So v_p(h_Δ) ≠ v_p(h(N)) iff
* p ≥ 5: p² ∣ N and p ∣ ε_Δ;   * p = 3: 3⁴ ∣ N and 9 ∣ ε_Δ;   * p = 2: 2⁸ ∣ N and 16 ∣ ε_Δ
(`omega`), and m ∣ ε_Δ iff m ∣ d² − 1 for all d ∈ Δ, where p ∣ d² − 1 ⟺ d ≡ ±1 (p), 9 ∣ d² − 1 ⟺ d ≡ ±1 (9),
16 ∣ d² − 1 ⟺ d ≡ ±1 (8) (`decide` on ℤ/9, ℤ/16).
-/




variable {N : ℕ}

theorem isPmOneMod_iff_val [NeZero N] (m : ℕ) (u : (ZMod N)ˣ) :
    IsPmOneMod m u ↔ (((u : ZMod N).val : ℕ) : ZMod m) = 1 ∨ (((u : ZMod N).val : ℕ) : ZMod m) = -1 := by
  unfold IsPmOneMod; rw [ZMod.cast_eq_val]

theorem dvd_sq_sub_one_iff {m x : ℕ} (hx : 1 ≤ x) : m ∣ x ^ 2 - 1 ↔ (x : ZMod m) ^ 2 = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hx), sub_eq_zero]; push_cast; rfl

theorem dvd_val_sq_iff_prime [NeZero N] {p : ℕ} (hp : p.Prime) (hN : 2 ≤ N) (u : (ZMod N)ˣ) :
    p ∣ (u : ZMod N).val ^ 2 - 1 ↔ IsPmOneMod p u := by
  haveI := Fact.mk hp
  rw [dvd_sq_sub_one_iff (one_le_val_unit hN u), isPmOneMod_iff_val, sq]
  exact mul_self_eq_one_iff

theorem zmod9_sq_eq_one : ∀ y : ZMod 9, y ^ 2 = 1 ↔ y = 1 ∨ y = -1 := by decide

theorem dvd_val_sq_iff_nine [NeZero N] (hN : 2 ≤ N) (u : (ZMod N)ˣ) :
    9 ∣ (u : ZMod N).val ^ 2 - 1 ↔ IsPmOneMod 9 u := by
  rw [dvd_sq_sub_one_iff (one_le_val_unit hN u), isPmOneMod_iff_val]
  exact zmod9_sq_eq_one _

theorem zmod16_sq_eq_one : ∀ y : ZMod 16, y ^ 2 = 1 ↔
    (ZMod.castHom (show 8 ∣ 16 by norm_num) (ZMod 8) y = 1 ∨
      ZMod.castHom (show 8 ∣ 16 by norm_num) (ZMod 8) y = -1) := by decide

theorem dvd_val_sq_iff_sixteen [NeZero N] (hN : 2 ≤ N) (u : (ZMod N)ˣ) :
    16 ∣ (u : ZMod N).val ^ 2 - 1 ↔ IsPmOneMod 8 u := by
  rw [dvd_sq_sub_one_iff (one_le_val_unit hN u), isPmOneMod_iff_val, zmod16_sq_eq_one, map_natCast]

/-- The local criterion at a prime p. -/
theorem factorization_hDelta_ne_iff [NeZero N] (Δ : SG N) {p : ℕ} (hp : p.Prime) :
    (hDelta N Δ).factorization p ≠ (hPart N).factorization p ↔
      (5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod p u) ∨ (p = 3 ∧ 3 ^ 4 ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod 9 u) ∨
        (p = 2 ∧ 2 ^ 8 ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod 8 u) := by
  have hN := NeZero.ne N
  have hε0 : epsDelta N Δ ≠ 0 := epsDelta_pos.ne'
  rw [factorization_hDelta, (local_constants (p := p) hN).2]
  have hle : (epsPart N).factorization p ≤ (epsDelta N Δ).factorization p :=
    (Nat.factorization_le_iff_dvd (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hN)).ne' hε0).2
      (gcd24_dvd_epsDelta Δ) p
  -- m ∣ ε_Δ ⟺ ∀ u ∈ Δ, …, given m ∣ N
  have hconv : ∀ {m m' : ℕ}, m ∣ N → 2 ≤ N →
      (∀ u : (ZMod N)ˣ, m ∣ (u : ZMod N).val ^ 2 - 1 ↔ IsPmOneMod m' u) →
      (m ∣ epsDelta N Δ ↔ ∀ u ∈ Δ, IsPmOneMod m' u) := by
    intro m m' hmN _ hiff
    rw [dvd_epsDelta_iff]
    exact ⟨fun h u hu => (hiff u).1 (h.2 u hu), fun h => ⟨hmN, fun u hu => (hiff u).2 (h u hu)⟩⟩
  have hN2 : ∀ {q : ℕ}, 2 ≤ q → q ∣ N → 2 ≤ N := fun hq hqN =>
    le_trans hq (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hqN)
  have hg : (epsPart N).factorization p =
      min (N.factorization p) (if p = 2 then 3 else if p = 3 then 1 else 0) := by
    rw [factorization_epsPart hN, factorization_24]
  by_cases h2 : p = 2
  · -- p = 2
    subst h2
    rw [if_pos rfl] at hg
    rw [hg] at hle ⊢
    have e1 := Nat.prime_two.pow_dvd_iff_le_factorization (k := 8) hN
    have e2 := Nat.prime_two.pow_dvd_iff_le_factorization (k := 4) hε0
    constructor
    · intro hne
      have h256 := e1.2 (by omega)
      have h16 := (pow_dvd_pow 2 (by norm_num : 4 ≤ 8)).trans h256
      refine Or.inr (Or.inr ⟨rfl, h256, ?_⟩)
      exact (hconv h16 (hN2 (by norm_num) h16) (dvd_val_sq_iff_sixteen (hN2 (by norm_num) h16))).1
        (e2.2 (by omega))
    · rintro (⟨h5, -⟩ | ⟨h3, -⟩ | ⟨-, h256, h8⟩)
      · omega
      · omega
      have h16 := (pow_dvd_pow 2 (by norm_num : 4 ≤ 8)).trans h256
      have := e2.1 ((hconv h16 (hN2 (by norm_num) h16)
        (dvd_val_sq_iff_sixteen (hN2 (by norm_num) h16))).2 h8)
      have := e1.1 h256
      omega
  by_cases h3 : p = 3
  · -- p = 3
    subst h3
    rw [if_neg (by norm_num : (3 : ℕ) ≠ 2), if_pos rfl] at hg
    rw [hg] at hle ⊢
    have e1 := Nat.prime_three.pow_dvd_iff_le_factorization (k := 4) hN
    have e2 := Nat.prime_three.pow_dvd_iff_le_factorization (k := 2) hε0
    constructor
    · intro hne
      have h81 := e1.2 (by omega)
      have h9 := (pow_dvd_pow 3 (by norm_num : 2 ≤ 4)).trans h81
      refine Or.inr (Or.inl ⟨rfl, h81, ?_⟩)
      exact (hconv h9 (hN2 (by norm_num) h9) (dvd_val_sq_iff_nine (hN2 (by norm_num) h9))).1
        (e2.2 (by omega))
    · rintro (⟨h5, -⟩ | ⟨-, h81, h9'⟩ | ⟨h3, -⟩)
      · omega
      · have h9 : 9 ∣ N := (pow_dvd_pow 3 (by norm_num : 2 ≤ 4)).trans h81
        have := e2.1 ((hconv h9 (hN2 (by norm_num) h9)
          (dvd_val_sq_iff_nine (hN2 (by norm_num) h9))).2 h9')
        have := e1.1 h81
        omega
      · omega
  · -- p ≥ 5
    rw [if_neg h2, if_neg h3, min_zero] at hg
    rw [hg] at hle ⊢
    have h5 : 5 ≤ p := by
      have := hp.two_le
      have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
      omega
    have e1 := hp.pow_dvd_iff_le_factorization (k := 2) hN
    have e2 := hp.pow_dvd_iff_le_factorization (k := 1) hε0
    rw [pow_one] at e2
    have hp2N : ∀ {q : ℕ}, q ^ 2 ∣ N → q ∣ N := fun h => (dvd_pow_self _ two_ne_zero).trans h
    constructor
    · intro hne
      have hpp := e1.2 (by omega)
      refine Or.inl ⟨h5, hpp, ?_⟩
      exact (hconv (hp2N hpp) (hN2 hp.two_le (hp2N hpp)) (dvd_val_sq_iff_prime hp
        (hN2 hp.two_le (hp2N hpp)))).1 (e2.2 (by omega))
    · rintro (⟨-, hpp, hpm⟩ | ⟨h3', -⟩ | ⟨h2', -⟩)
      · have := e2.1 ((hconv (hp2N hpp) (hN2 hp.two_le (hp2N hpp)) (dvd_val_sq_iff_prime hp
          (hN2 hp.two_le (hp2N hpp)))).2 hpm)
        have := e1.1 hpp
        omega
      · exact absurd h3' h3
      · exact absurd h2' h2

theorem hDelta_eq_hPart_iff (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    hDelta N Δ = hPart N ↔
      ¬ ((∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod p d) ∨
        (3 ^ 4 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 9 d) ∨
        (2 ^ 8 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 8 d)) := by
  constructor
  · intro h habc
    rcases habc with ⟨p, hp, h5, hp2, hpm⟩ | ⟨h81, h9⟩ | ⟨h256, h8⟩
    · exact (factorization_hDelta_ne_iff Δ hp).2 (Or.inl ⟨h5, hp2, hpm⟩) (by rw [h])
    · exact (factorization_hDelta_ne_iff Δ Nat.prime_three).2 (Or.inr (Or.inl ⟨rfl, h81, h9⟩))
        (by rw [h])
    · exact (factorization_hDelta_ne_iff Δ Nat.prime_two).2 (Or.inr (Or.inr ⟨rfl, h256, h8⟩))
        (by rw [h])
  · intro hn
    apply Nat.eq_of_factorization_eq (hDelta_ne_zero Δ) (hPart_pos N).ne'
    intro p
    by_cases hp : p.Prime
    swap
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    by_contra hne
    rcases (factorization_hDelta_ne_iff Δ hp).1 hne with ⟨h5, h2, h⟩ | ⟨rfl, h81, h9⟩ |
      ⟨rfl, h256, h8⟩
    · exact hn (Or.inl ⟨p, hp, h5, h2, h⟩)
    · exact hn (Or.inr (Or.inl ⟨h81, h9⟩))
    · exact hn (Or.inr (Or.inr ⟨h256, h8⟩))

end

end NormalizerLean
