module

public import NormalizerLean.NewmanMain
public import NormalizerLean.Defs

@[expose] public section

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

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- n = N / η². -/
def nOf (N η : ℕ) : ℕ := N / η ^ 2

/-- An integer matrix with N ∣ M₁₀ and ϵ ∣ M₁₁ − M₀₀. -/
def InLe (N ϵ : ℕ) (M : Matℝ) : Prop :=
  ∃ a b c d : ℤ, M = !![(a : ℝ), b; c, d] ∧ (N : ℤ) ∣ c ∧ (ϵ : ℤ) ∣ d - a

/-- The hypotheses of Newman's argument for Γ ≤ Γ₀(N), with lattice parameter ϵ and output η. -/
structure NewmanData (N : ℕ) (Γ : Subgroup SLℝ) (ϵ η : ℕ) : Prop where
  le : Γ ≤ Gamma0R N
  T_mem : matT ∈ Γ
  U_mem : matU N ∈ Γ
  inL : ∀ Y ∈ Γ, InLe N ϵ (Y : Matℝ)
  eps_dvd : ϵ ∣ N
  h_pos : 0 < η
  h_sq_dvd : η ^ 2 ∣ N
  h_fact : ∀ p, η.factorization p = min (ϵ.factorization p) (N.factorization p / 2)
  gamma : ∀ p : ℕ, p.Prime → p ∣ N → ϵ.factorization p < N.factorization p →
    ∃ x y t : ℤ, x * t - y * N = 1 ∧
      (∃ γ ∈ Γ, (γ : Matℝ) = !![(x : ℝ), y; N, t]) ∧
      t - x ≠ 0 ∧ vz p (t - x) = ϵ.factorization p

variable {Γ : Subgroup SLℝ} {ϵ η N : ℕ} [NeZero N] {g : SLℝ} {κ : ℝ} {α β γ δ : ℤ}
  (D : NewmanData N Γ ϵ η) (hgN : g ∈ NormG Γ)
  (hg : (g : Matℝ) = κ • Smat η α β γ δ) (he : detS α β γ δ ≠ 0)

theorem NewmanData.n_mul_sq {N : ℕ} (D : NewmanData N Γ ϵ η) : nOf N η * η ^ 2 = N :=
  Nat.div_mul_cancel D.h_sq_dvd

theorem NewmanData.n_ne_zero {N : ℕ} (D : NewmanData N Γ ϵ η) (hN : N ≠ 0) : nOf N η ≠ 0 :=
  fun h => hN (by rw [← D.n_mul_sq, h, zero_mul])

theorem NewmanData.factorization_n {N : ℕ} (D : NewmanData N Γ ϵ η) (hN : N ≠ 0) (p : ℕ) :
    (nOf N η).factorization p + 2 * η.factorization p = N.factorization p := by
  have h := congrArg (fun m => m.factorization p) D.n_mul_sq
  rw [Nat.factorization_mul (D.n_ne_zero hN) (by have := D.h_pos; positivity),
    Nat.factorization_pow] at h
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h
  omega

theorem InLe.add {N : ℕ} {M M' : Matℝ} (h : InLe N ϵ M) (h' : InLe N ϵ M') :
    InLe N ϵ (M + M') := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  obtain ⟨a', b', c', d', rfl, hc', hd'⟩ := h'
  refine ⟨a + a', b + b', c + c', d + d', ?_, dvd_add hc hc', ?_⟩
  · mat_smp
  · rw [show d + d' - (a + a') = (d - a) + (d' - a') by ring]; exact dvd_add hd hd'

theorem InLe.zsmul {N : ℕ} {M : Matℝ} (h : InLe N ϵ M) (m : ℤ) :
    InLe N ϵ ((m : ℝ) • M) := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  refine ⟨m * a, m * b, m * c, m * d, ?_, dvd_mul_of_dvd_right hc _, ?_⟩
  · mat_smp
  · rw [show m * d - m * a = m * (d - a) by ring]; exact dvd_mul_of_dvd_right hd _

theorem InLe.sub {N : ℕ} {M M' : Matℝ} (h : InLe N ϵ M) (h' : InLe N ϵ M') :
    InLe N ϵ (M - M') := by
  have := h.add (h'.zsmul (-1))
  convert this using 1
  simp [sub_eq_add_neg]

theorem InLe.one (N : ℕ) : InLe N ϵ 1 :=
  ⟨1, 0, 0, 1, by mat_smp, dvd_zero _, by simp⟩


/-- The products of entries that are integers. -/
theorem products_intG {N : ℕ} {g : SLℝ} (D : NewmanData N Γ ϵ η) (hg : g ∈ NormG Γ) {x y z w : ℝ}
    (hx : (g : Matℝ) 0 0 = x) (hy : (g : Matℝ) 0 1 = y)
    (hz : (g : Matℝ) 1 0 = z) (hw : (g : Matℝ) 1 1 = w) :
    IsIntR (x * x) ∧ IsIntR (x * z) ∧ IsIntR (z * z) ∧ IsIntR (N * (y * y)) ∧
      IsIntR (N * (y * w)) ∧ IsIntR (N * (x * w)) ∧
      IsIntR (N * (x * y)) ∧ IsIntR (N * (z * w)) ∧ IsIntR (N * (y * z)) := by
  have hconj : ∀ Y ∈ Γ, g * Y * g⁻¹ ∈ Γ := fun Y hY =>
    (Subgroup.mem_normalizer_iff.1 hg Y).1 hY
  have hT := isIntR_entries_of_mem (D.le (hconj _ D.T_mem))
  have hU := isIntR_entries_of_mem (D.le (hconj _ D.U_mem))
  have hTU := isIntR_entries_of_mem (D.le (hconj _ (mul_mem D.T_mem D.U_mem)))
  have hdet : x * w - y * z = 1 := by
    simpa only [det_fin_two, hx, hy, hz, hw] using g.2
  -- explicit conjugates
  have eT : ∀ i j, ((g * matT * g⁻¹ : SLℝ) : Matℝ) i j =
      !![1 - x * z, x * x; -(z * z), 1 + x * z] i j := by
    intro i j
    rw [coe_conj, adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp [matT, Matrix.mul_apply, Fin.sum_univ_two, hx, hy, hz, hw] <;>
      first | ring1 | (linear_combination hdet)
  have eU : ∀ i j, ((g * matU N * g⁻¹ : SLℝ) : Matℝ) i j =
      !![1 + N * (y * w), -(N * (y * y)); N * (w * w), 1 - N * (y * w)] i j := by
    intro i j
    rw [coe_conj, adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp [matU, Matrix.mul_apply, Fin.sum_univ_two, hx, hy, hz, hw] <;>
      first | ring1 | (linear_combination hdet)
  have eTU : ∀ i j, ((g * (matT * matU N) * g⁻¹ : SLℝ) : Matℝ) i j =
      !![1 - x * z + N * (y * w) + N * (x * w), x * x - N * (y * y) - N * (x * y);
        -(z * z) + N * (w * w) + N * (z * w), 1 + x * z - N * (y * w) - N * (y * z)] i j := by
    intro i j
    rw [coe_conj, Matrix.SpecialLinearGroup.coe_mul, adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp [matT, matU, Matrix.mul_apply, Fin.sum_univ_two, hx, hy, hz, hw] <;>
      first | ring1 | (linear_combination hdet)
  have t01 := hT 0 1; rw [eT] at t01; simp at t01
  have t00 := hT 0 0; rw [eT] at t00; simp at t00
  have t10 := hT 1 0; rw [eT] at t10; simp at t10
  have u01 := hU 0 1; rw [eU] at u01; simp at u01
  have u10 := hU 1 0; rw [eU] at u10; simp at u10
  have u00 := hU 0 0; rw [eU] at u00; simp at u00
  have v00 := hTU 0 0; rw [eTU] at v00; simp at v00
  have v01 := hTU 0 1; rw [eTU] at v01; simp at v01
  have v10 := hTU 1 0; rw [eTU] at v10; simp at v10
  have v11 := hTU 1 1; rw [eTU] at v11; simp at v11
  have hxz : IsIntR (x * z) := by
    have := (IsIntR.one.sub t00)
    simpa using this
  have hzz : IsIntR (z * z) := by simpa using t10.neg
  have hyy : IsIntR (N * (y * y)) := by simpa using u01.neg
  have hyw : IsIntR (N * (y * w)) := by
    have := u00.sub IsIntR.one
    simpa using this
  refine ⟨t01, hxz, hzz, hyy, hyw, ?_, ?_, ?_, ?_⟩
  · have := ((v00.sub IsIntR.one).add hxz).sub hyw
    convert this using 1; ring
  · have := ((t01.sub hyy).sub v01)
    convert this using 1; ring
  · have := ((v10.add hzz).sub u10)
    convert this using 1; ring
  · have := (((IsIntR.one.add hxz).sub hyw).sub v11)
    convert this using 1; ring

/-- **Step 1** ([Nw §2]): g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ without a common prime
factor. -/
theorem exists_prim_formG {N : ℕ} [NeZero N] {g : SLℝ} (D : NewmanData N Γ ϵ η) (hg : g ∈ NormG Γ) :
    ∃ (κ : ℝ) (α β γ δ : ℤ), κ ≠ 0 ∧
      (∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β ∧ (p : ℤ) ∣ γ ∧ (p : ℤ) ∣ δ)) ∧
      (g : Matℝ) =
        κ • !![(α : ℝ), (β : ℝ) / η; (η : ℝ) * γ, (δ : ℝ)] := by
  set x := (g : Matℝ) 0 0 with hx
  set y := (g : Matℝ) 0 1 with hy
  set z := (g : Matℝ) 1 0 with hz
  set w := (g : Matℝ) 1 1 with hw
  obtain ⟨hxx, hxz, hzz, hyy, hyw, hxw, hxy, hzw, hyz⟩ :=
    products_intG D hg hx.symm hy.symm hz.symm hw.symm
  have hdet : x * w - y * z = 1 := by simpa only [det_fin_two] using g.2
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
  have hNt : (N : ℝ) * t ≠ 0 := mul_ne_zero hN ht
  have hG0 : G ≠ 0 := by
    intro hG0
    simp only [hG, Int.gcd_eq_zero_iff, Nat.cast_eq_zero] at hG0
    obtain ⟨⟨h0, h1⟩, -, -⟩ := hG0
    have hIx0 : Ix = 0 := by
      simp only [M0] at h0
      exact (mul_eq_zero.1 h0).resolve_left (by exact_mod_cast D.h_pos.ne')
    have hIy0 : Iy = 0 := by
      simp only [M1] at h1
      exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero 2 (by exact_mod_cast D.h_pos.ne'))
    have hx0 : x = 0 := by
      have : (N : ℝ) * t * x = 0 := by rw [hIx, hIx0]; simp
      exact (mul_eq_zero.1 this).resolve_left hNt
    have hy0 : y = 0 := by
      have : (N : ℝ) * t * y = 0 := by rw [hIy, hIy0]; simp
      exact (mul_eq_zero.1 this).resolve_left hNt
    rw [hx0, hy0] at hdet
    simp at hdet
  obtain ⟨α, hα⟩ : (G : ℤ) ∣ M0 := by
    rw [hG]; exact (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left _ _)
  obtain ⟨β, hβ⟩ : (G : ℤ) ∣ M1 := by
    rw [hG]; exact (Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right _ _)
  obtain ⟨γ, hγ⟩ : (G : ℤ) ∣ M2 := by
    rw [hG]; exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)
  obtain ⟨δ, hδ⟩ : (G : ℤ) ∣ M3 := by
    rw [hG]; exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)
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
    mat_smp [← hx, ← hy, ← hz, ← hw]
    · field_simp
      linear_combination -eα
    · field_simp
      linear_combination -eβ
    · field_simp
      linear_combination -eγ
    · field_simp
      linear_combination -eδ

theorem InLe.entries {N : ℕ} {M : Matℝ} (h : InLe N ϵ M) :
    ∃ a b c d : ℤ, M 0 0 = a ∧ M 0 1 = b ∧ M 1 0 = c ∧ M 1 1 = d ∧ (N : ℤ) ∣ c ∧
      (ϵ : ℤ) ∣ d - a := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  exact ⟨a, b, c, d, by simp, by simp, by simp, by simp, hc, hd⟩


include D hgN hg in
theorem phi_InLe {Y : SLℝ}
    (hY : Y ∈ Γ) : InLe N ϵ (Phi η α β γ δ (Y : Matℝ)) := by
  rw [← coe_conj_eq_Phi hg D.h_pos.ne']
  exact D.inL _ ((Subgroup.mem_normalizer_iff.1 hgN Y).1 hY)

include D hgN hg he in
/-- The four basic facts in `InLe` form. -/
theorem InLe_basic :
    InLe N ϵ (Phi η α β γ δ !![0, 1; 0, 0]) ∧
      InLe N ϵ ((N : ℝ) • Phi η α β γ δ !![0, 0; 1, 0]) ∧
      InLe N ϵ ((N : ℝ) • Phi η α β γ δ !![0, 0; 0, 1]) := by
  have hh : η ≠ 0 := D.h_pos.ne'
  have h1 : InLe N ϵ (Phi η α β γ δ 1) := by rw [Phi_one hh he]; exact InLe.one N
  have hN1 : InLe N ϵ ((N : ℝ) • Phi η α β γ δ 1) := by simpa using h1.zsmul N
  have hT := phi_InLe D hgN hg D.T_mem
  have hU := phi_InLe D hgN hg D.U_mem
  have hTU := phi_InLe D hgN hg (mul_mem D.T_mem D.U_mem)
  have eE12 : (!![0, 1; 0, 0] : Matℝ) = (matT : Matℝ) - 1 := by
    mat_smp [matT]
  have eE21 : (N : ℝ) • (!![0, 0; 1, 0] : Matℝ) =
      (matU N : Matℝ) - 1 := by
    mat_smp [matU]
  have eE22 : (N : ℝ) • (!![0, 0; 0, 1] : Matℝ) =
      (N : ℝ) • 1 - (((matT * matU N : SLℝ) : Matℝ) -
        (matT : Matℝ) - (matU N : Matℝ) + 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    mat_smp [matT, matU]
  refine ⟨?_, ?_, ?_⟩
  · rw [eE12, Phi_sub]; exact hT.sub h1
  · rw [← Phi_smul, eE21, Phi_sub]; exact hU.sub h1
  · rw [← Phi_smul, eE22, Phi_sub, Phi_smul, Phi_add, Phi_sub, Phi_sub]
    exact hN1.sub (((hTU.sub hT).sub hU).add h1)

include D hgN hg he in
/-- The γ_p fact in `InLe` form, for γ_p = [[x, y], [N, t]] ∈ Γ. -/
theorem InLe_s {x y t : ℤ} {γp : SLℝ} (hγp : γp ∈ Γ)
    (hγm : (γp : Matℝ) = !![(x : ℝ), y; N, t]) :
    InLe N ϵ (((t - x : ℤ) : ℝ) • Phi η α β γ δ !![0, 0; 0, 1]) ∧
      (ϵ : ℤ) ∣ t - x := by
  have hh : η ≠ 0 := D.h_pos.ne'
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
  have h1 : InLe N ϵ (Phi η α β γ δ 1) := by rw [Phi_one hh he]; exact InLe.one N
  have hP := phi_InLe D hgN hg hγp
  obtain ⟨hE12, hE21, -⟩ := InLe_basic D hgN hg he
  have eE : ((t - x : ℤ) : ℝ) • (!![0, 0; 0, 1] : Matℝ) =
      (γp : Matℝ) - (x : ℝ) • 1 - (y : ℝ) • !![0, 1; 0, 0] -
        (N : ℝ) • !![0, 0; 1, 0] := by
    rw [hγm]
    mat_smp
  rw [← Phi_smul, eE, Phi_sub, Phi_sub, Phi_sub, Phi_smul, Phi_smul, Phi_smul]
  exact ((hP.sub (h1.zsmul x)).sub (hE12.zsmul y)).sub hE21

include he in
theorem int_facts_E22 {s : ℤ} (hh : η ≠ 0)
    (P : InLe N ϵ ((s : ℝ) • Phi η α β γ δ !![0, 0; 0, 1])) (hε : (ϵ : ℤ) ∣ s) :
    (detS α β γ δ) ∣ s * (β * γ) ∧
      (detS α β γ δ) * (η : ℤ) ∣ s * (α * β) ∧
      (detS α β γ δ) * N ∣ (s * (η : ℤ)) * (γ * δ) ∧
      (detS α β γ δ) * (ϵ : ℤ) ∣ (2 * s) * (β * γ) := by
  obtain ⟨a, b, c, d, j00, j01, j10, j11, hc, hd⟩ := P.entries
  rw [Phi_E22 hh] at j00 j01 j10 j11
  have t00 := int_eq_of_real (X := -(s * (β * γ))) he (by rw [← j00]; simp; ring)
  have t01 := int_eq_of_real_div (X := s * (α * β)) he hh (by rw [← j01]; simp; ring)
  have t10 := int_eq_of_real (X := -(s * (η : ℤ) * (γ * δ))) he
    (by rw [← j10]; simp; ring)
  have t11 := int_eq_of_real (X := s * (α * δ)) he (by rw [← j11]; simp; ring)
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨k, hk⟩ := hd
  have hd' : d - a = s - 2 * a := mul_left_cancel₀ he (by linear_combination -t11 - t00)
  refine ⟨⟨-a, by linear_combination -t00⟩, ⟨b, by linear_combination t01⟩,
    ⟨-c', by linear_combination -t10⟩, ?_⟩
  have h2a : (ϵ : ℤ) ∣ 2 * a := by
    have : (ϵ : ℤ) ∣ s - (d - a) := dvd_sub hε ⟨k, hk⟩
    rw [hd'] at this
    simpa using this
  obtain ⟨k', hk'⟩ := h2a
  exact ⟨-k', by linear_combination -2 * t00 - (detS α β γ δ) * hk'⟩

include D hgN hg he in
/-- The integer divisibilities F1–F12. -/
theorem int_factsG :
    (detS α β γ δ) ∣ 1 * α ^ 2 ∧ (detS α β γ δ) * N ∣ (η : ℤ) ^ 2 * γ ^ 2 ∧ (detS α β γ δ) * (ϵ : ℤ) ∣ (2 * (η : ℤ)) * (α * γ) ∧
    (detS α β γ δ) ∣ ((nOf N η : ℤ) * (η : ℤ)) * (β * δ) ∧ (detS α β γ δ) ∣ (nOf N η : ℤ) * β ^ 2 ∧ (detS α β γ δ) ∣ 1 * δ ^ 2 ∧ (detS α β γ δ) * (ϵ : ℤ) ∣ (2 * (nOf N η : ℤ) * (η : ℤ)) * (β * δ) ∧
    (detS α β γ δ) ∣ (N : ℤ) * (β * γ) ∧ (detS α β γ δ) * (η : ℤ) ∣ (N : ℤ) * (α * β) ∧ (detS α β γ δ) * N ∣ ((N : ℤ) * (η : ℤ)) * (γ * δ) ∧
    (detS α β γ δ) * (ϵ : ℤ) ∣ (2 * (N : ℤ)) * (β * γ) := by
  have hh : η ≠ 0 := D.h_pos.ne'
  have hhr : (η : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  have hNr : (N : ℝ) = nOf N η * (η : ℝ) ^ 2 := by exact_mod_cast D.n_mul_sq.symm
  have hN0 : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  obtain ⟨P12, P21, P22⟩ := InLe_basic D hgN hg he
  obtain ⟨a1, b1, c1, d1, h00, h01, h10, h11, hc1, hd1⟩ := P12.entries
  rw [Phi_E12] at h00 h01 h10 h11
  have r00 := int_eq_of_real (X := -(α * (η : ℤ) * γ)) he (by rw [← h00]; simp)
  have r01 := int_eq_of_real (X := α ^ 2) he (by rw [← h01]; simp)
  have r10 := int_eq_of_real (X := -((η : ℤ) ^ 2 * γ ^ 2)) he (by rw [← h10]; simp)
  have r11 := int_eq_of_real (X := α * (η : ℤ) * γ) he (by rw [← h11]; simp)
  obtain ⟨a2, b2, c2, d2, i00, i01, i10, i11, hc2, hd2⟩ := P21.entries
  rw [Phi_E21 hh] at i00 i01 i10 i11
  have s00 := int_eq_of_real (X := (nOf N η : ℤ) * (η : ℤ) * (β * δ)) he
    (by rw [← i00]; simp [hNr]; field_simp)
  have s01 := int_eq_of_real (X := -((nOf N η : ℤ) * β ^ 2)) he
    (by rw [← i01]; simp [hNr]; field_simp)
  have s10 := int_eq_of_real (X := (N : ℤ) * δ ^ 2) he (by rw [← i10]; simp; ring)
  have s11 := int_eq_of_real (X := -((nOf N η : ℤ) * (η : ℤ) * (β * δ))) he
    (by rw [← i11]; simp [hNr]; field_simp)
  obtain ⟨F9, F10, F11, F12⟩ := int_facts_E22 he hh (by simpa using P22)
    (Int.natCast_dvd_natCast.2 D.eps_dvd)
  obtain ⟨c1', rfl⟩ := hc1
  obtain ⟨c2', rfl⟩ := hc2
  obtain ⟨k1, hk1⟩ := hd1
  obtain ⟨k2, hk2⟩ := hd2
  have ha1 : a1 = -d1 := mul_left_cancel₀ he (by linear_combination -r00 - r11)
  have ha2 : d2 = -a2 := mul_left_cancel₀ he (by linear_combination -s11 - s00)
  exact ⟨⟨b1, by linear_combination r01⟩,
    ⟨-c1', by linear_combination -r10⟩,
    ⟨k1, by linear_combination 2 * r11 + (detS α β γ δ) * hk1 + (detS α β γ δ) * ha1⟩,
    ⟨a2, by linear_combination s00⟩, ⟨-b2, by linear_combination -s01⟩,
    ⟨c2', mul_left_cancel₀ hN0 (by linear_combination s10)⟩,
    ⟨-k2, by linear_combination 2 * s00 - (detS α β γ δ) * hk2 + (detS α β γ δ) * ha2⟩,
    F9, F10, F11, F12⟩


include D hgN hg he in
/-- The four facts with s = t − x in place of N. -/
theorem int_facts_sG {x y t : ℤ} {γp : SLℝ} (hγp : γp ∈ Γ)
    (hγm : (γp : Matℝ) = !![(x : ℝ), y; N, t]) :
    (detS α β γ δ) ∣ (t - x) * (β * γ) ∧
      (detS α β γ δ) * (η : ℤ) ∣ (t - x) * (α * β) ∧
      (detS α β γ δ) * N ∣ ((t - x) * (η : ℤ)) * (γ * δ) ∧
      (detS α β γ δ) * (ϵ : ℤ) ∣ (2 * (t - x)) * (β * γ) := by
  obtain ⟨P, hε⟩ := InLe_s D hgN hg he hγp hγm
  exact int_facts_E22 he D.h_pos.ne' P hε

include D hgN hg he in
/-- The local conclusion at a prime p. -/
theorem local_conclusionG
    (hginv : ((g⁻¹ : SLℝ) : Matℝ) =
      κ • Smat η δ (-β) (-γ) α)
    (hprim : ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β ∧ (p : ℤ) ∣ γ ∧ (p : ℤ) ∣ δ))
    {p : ℕ} (hp : p.Prime) :
    let B := vz p (detS α β γ δ) + N.factorization p + 1
    (vz p (detS α β γ δ) = 0 ∧ (nOf N η).factorization p ≤ vv B p γ) ∨
      (vz p (detS α β γ δ) = (nOf N η).factorization p ∧
        (nOf N η).factorization p ≤ vv B p α ∧ (nOf N η).factorization p ≤ vv B p γ ∧
        (nOf N η).factorization p ≤ vv B p δ) := by
  intro B
  have hN := NeZero.ne N
  have hNz : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hhz : (η : ℤ) ≠ 0 := Nat.cast_ne_zero.2 D.h_pos.ne'
  have hnz : (nOf N η : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (D.n_ne_zero hN)
  have hε0 : ϵ ≠ 0 := (Nat.pos_of_dvd_of_pos D.eps_dvd (Nat.pos_of_ne_zero hN)).ne'
  have hεz : (ϵ : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hε0
  -- the local constants
  set ν := N.factorization p
  set j := ϵ.factorization p
  set k := η.factorization p
  set e₂ := (2 : ℕ).factorization p with he₂
  set nν := (nOf N η).factorization p
  set δ₀ := vz p (detS α β γ δ)
  have hkj : k = min j (ν / 2) := D.h_fact p
  have hnk : nν + 2 * k = ν := D.factorization_n hN p
  have hjν : j ≤ ν := (Nat.factorization_le_iff_dvd hε0 hN).2 D.eps_dvd p
  have he₂1 : e₂ ≤ 1 := by rw [he₂, Nat.prime_two.factorization, Finsupp.single_apply]; split_ifs <;> omega
  -- valuations of the constants
  have vN : vz p (N : ℤ) = ν := vz_natCast p N
  have vh : vz p (η : ℤ) = k := vz_natCast p _
  have vn : vz p (nOf N η : ℤ) = nν := vz_natCast p _
  have vε : vz p (ϵ : ℤ) = j := vz_natCast p _
  have v2 : vz p (2 : ℤ) = e₂ := by
    have := vz_natCast p 2
    simpa using this
  have v1 : vz p (1 : ℤ) = 0 := by simp [vz]
  have two0 : (2 : ℤ) ≠ 0 := by norm_num
  -- shorthand for the valuations of the entries
  set a := vv B p α
  set b := vv B p β
  set c := vv B p γ
  set d := vv B p δ
  have hb' : vv B p (-β) = b := vv_neg B p β
  have hc' : vv B p (-γ) = c := vv_neg B p γ
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
  obtain ⟨F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12⟩ := int_factsG D hgN hg he
  have he' : δ * α - -β * -γ = detS α β γ δ := by ring
  have he'0 : δ * α - -β * -γ ≠ 0 := by rw [he']; exact he
  obtain ⟨G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12⟩ :=
    int_factsG D (inv_mem hgN) hginv he'0
  rw [he'] at G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12
  -- valuations of the moduli
  have vX : ∀ X : ℤ, X ≠ 0 → vz p ((detS α β γ δ) * X) = δ₀ + vz p X := fun X hX =>
    vz_mul he hX
  have hBe : vz p (detS α β γ δ) ≤ B := by simp only [B]; omega
  have hBN : vz p ((detS α β γ δ) * N) ≤ B := by rw [vX _ hNz, vN]; simp only [B]; omega
  have hBε : vz p ((detS α β γ δ) * (ϵ : ℤ)) ≤ B := by
    rw [vX _ hεz, vε]; simp only [B]; omega
  have hBh : vz p ((detS α β γ δ) * (η : ℤ)) ≤ B := by
    rw [vX _ hhz, vh]; simp only [B]
    omega
  have c2 := le_vv_sq (B := B) one_ne_zero hBe F2
  have c3 := le_vv_sq (B := B) (pow_ne_zero 2 hhz) hBN F3
  have c4 := le_vv2 (B := B) (mul_ne_zero two0 hhz) hBε F4
  have c6 := le_vv_sq (B := B) hnz hBe F6
  have c7 := le_vv_sq (B := B) one_ne_zero hBe F7
  have c8 := le_vv2 (B := B) (mul_ne_zero (mul_ne_zero two0 hnz) hhz) hBε F8
  have c9 := le_vv2 (B := B) hNz hBe F9
  have c10 := le_vv2 (B := B) hNz hBh F10
  have c11 := le_vv2 (B := B) (mul_ne_zero hNz hhz) hBN F11
  have c12 := le_vv2 (B := B) (mul_ne_zero two0 hNz) hBε F12
  have d2 := le_vv_sq (B := B) one_ne_zero hBe G2
  have d5 := le_vv2 (B := B) (mul_ne_zero hnz hhz) hBe G5
  have d7 := le_vv_sq (B := B) one_ne_zero hBe G7
  have d8 := le_vv2 (B := B) (mul_ne_zero (mul_ne_zero two0 hnz) hhz) hBε G8
  have d10 := le_vv2 (B := B) hNz hBh G10
  have d11 := le_vv2 (B := B) (mul_ne_zero hNz hhz) hBN G11
  simp only [hb', hc'] at d5 d8 d10 d11
  simp only [vX _ hNz, vX _ hεz, vX _ hhz, vz_mul two0 hhz,
    vz_mul (mul_ne_zero two0 hnz) hhz, vz_mul two0 hnz, vz_mul hNz hhz, vz_mul two0 hNz,
    vz_mul hhz hhz, pow_two, vN, vh, vn, vε, v2, v1] at c2 c3 c4 c6 c7 c8 c9 c10 c11 c12
  simp only [vX _ hNz, vX _ hεz, vX _ hhz, vz_mul hnz hhz,
    vz_mul (mul_ne_zero two0 hnz) hhz, vz_mul two0 hnz, vz_mul hNz hhz,
    vN, vh, vn, vε, v2, v1] at d2 d5 d7 d8 d10 d11
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
    have s9 := le_vv2 (B := B) hs0 hBe S9
    have s10 := le_vv2 (B := B) hs0 hBh S10
    have s11 := le_vv2 (B := B) (mul_ne_zero hs0 hhz) hBN S11
    have s12 := le_vv2 (B := B) (mul_ne_zero two0 hs0) hBε S12
    have t10 := le_vv2 (B := B) hs0 hBh T10
    have t11 := le_vv2 (B := B) (mul_ne_zero hs0 hhz) hBN T11
    simp only [hb', hc'] at t10 t11
    simp only [vX _ hNz, vX _ hεz, vX _ hhz, vz_mul hs0 hhz, vz_mul two0 hs0, hvs, vh, vN, vε,
      v2] at s9 s10 s11 s12 t10 t11
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  omega

end

end NormalizerLean
