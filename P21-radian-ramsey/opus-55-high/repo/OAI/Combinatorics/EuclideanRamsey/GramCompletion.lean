/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/GramCompletion.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.TensorPresentation

public section


open Matrix
open scoped MatrixOrder

set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
local notation "𝔢" => K * (1 + η)
local notation "𝔠" => QuotientAddGroup.mk' (φ i).ker
local notation "𝔟" => (W q)
local notation "𝔞" => (g γ α * g γ β)
notation "𝔡" => (A.den:ℚ)

notation "𝔉" V:max X:max E:max P:max => WithLp.toLp 2 fun y => c * (V ((E).symm y) + ∑ α, P α * X α ((E).symm y))

lemma row_gram_distance [Fintype τ] (e : τ ≃ Fin ℓ) c (v : τ → ℝ) X r
    (hX : X * Xᵀ = r • 1) (a b : Space d) :
    ‖(𝔉 v X e a : Space ℓ) - 𝔉 v X e b‖ ^ 2 = c ^ 2 * r * ‖a - b‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, WithLp.ofLp_sub, Pi.sub_apply, ← mul_sub, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib, ← sub_mul, mul_pow, ← Finset.mul_sum, e.symm.sum_comp fun x => (∑ α, (a α - b α) * X α x) ^ 2]
  rw [show ∑ x, (∑ α, (a α - b α) * X α x) ^ 2 = ((a - b).ofLp ᵥ* X) ⬝ᵥ ((a - b).ofLp ᵥ* X) by
    simp [sq, dotProduct, vecMul], ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hX]
  simp [dotProduct, sq, Finset.mul_sum, smul_mulVec, mul_left_comm, mul_assoc]

lemma gram_complement B (hB : B.PosSemidef) r (h : B.trace ≤ r) : ∃ R : 𝕄 d ℝ, R * Rᵀ = r • 1 - B := by
  have := (posSemidef_diagonal_iff.mpr fun i => sub_nonneg.mpr ((Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i)).trans (hB.1.trace_eq_sum_eigenvalues ▸ h))).mul_mul_conjTranspose_same hB.1.eigenvectorUnitary.1
  replace : (r • 1 - B).PosSemidef := by
    convert this
    conv_lhs => rw [hB.1.spectral_theorem]
    rw [(diagonal_sub ..).symm]
    simp [ mul_sub, sub_mul, ← smul_one_eq_diagonal, -conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
  exact ⟨CFC.sqrt _, by rw [← conjTranspose_eq_transpose_of_trivial, (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (r • 1 - B))).1.eq, CFC.sqrt_mul_sqrt_self _ this.nonneg]⟩

theorem realCriterion_two_scale (a : Fin s → Space d) (hd : 1 ≤ d) (hs : 0 < s) (h : RealCriterion a) η (hη : 0 < η) :
    ∃ ℓ,1 ≤ ℓ ∧ ∃ (f g : Fin s → Space ℓ), (∀ i j,‖f i-f j‖^2=‖a i-a j‖^2) ∧
      (∀ i j,‖g i-g j‖^2=(η/(1+η))*‖a i-a j‖^2) ∧ ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g i (σ x)=f i x := by
  obtain ⟨k, w, C, hC, hU, hquot⟩ := realCriterion_lattice a h
  set φ := fun i => ((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize
  obtain ⟨ν, h1, h2, h3, h4⟩ := finite_lattice_identity _ C hC hquot
  obtain ⟨n, μ, ζ, hζ, hcos, hmom, hneg⟩ := rational_smoothing hd _ ν C _ hC hU h1 h2 h3 h4 η hη
  set U : Matrix (Fin d) (Fin k) ℝ := Matrix.of fun α j => w j (some α)
  set S := μ.coeff.support
  let g γ α := ∑ j, U α j * latticeSample n γ j
  let v (γ : Lattice k) := ∑ j, (γ j:ℝ) / n * w j none
  have hφ i γ : φ i γ / n = v γ + ∑ α, a i α * g γ α := by
    simp [φ, v, g, rowEvaluation, Fintype.linearCombination_apply, rationalize, latticeSample, realAugmented]
    simp [Finset.sum_div, add_div, Finset.sum_add_distrib, Finset.mul_sum, Rat.smul_def]
    rw [Finset.sum_comm]
    ring_nf
    ac_rfl
  let A : Matrix Unit S ℚ := Matrix.of fun _ γ => μ.coeff γ
  have hz γ : ((⌊𝔡 * μ.coeff γ⌋ : ℤ) : ℚ) = A.den * μ.coeff γ := by
    by_cases hγ : γ ∈ S
    · have := A.num_div_den () ⟨γ, hγ⟩
      simp [A] at this
      rw [← this, mul_div_cancel₀ _ (by grind), Int.floor_intCast]
    · simp [Finsupp.notMem_support_iff.mp hγ]
  let p := μ.coeff.mapRange (fun x => ⌊𝔡 * x⌋.toNat) (by simp)
  let q := μ.coeff.mapRange (fun x => (-⌊𝔡 * x⌋).toNat) (by simp)
  have hsum (c : Lattice k →₀ ℕ) (hc : c.support ⊆ S) (G : Lattice k → ℝ) : ∑ x : c.toMultiset, G x = ∑ γ ∈ S, c γ * G γ := by
    rw [Finset.sum_eq_multiset_sum, Multiset.map_univ, Finsupp.toMultiset_map, Finsupp.sum_toMultiset,
      Finsupp.sum_mapDomain_index (by simp) (by grind), Finsupp.sum_of_support_subset _ hc _ (by simp)]
    simp
  have hpq γ : p γ - q γ = A.den * μ.coeff γ := by
    rw [← hz]
    exact_mod_cast Int.toNat_sub_toNat_neg _
  have hq γ : (q γ : ℚ) = A.den * max (-μ.coeff γ) 0 := by
    have := congrArg (Int.cast : ℤ → ℚ) (Int.toNat_eq_max (-⌊𝔡 * μ.coeff γ⌋))
    push_cast [hz] at this
    simp [q, this, mul_max_of_nonneg]
  have he i : ∃ e : p.toMultiset ≃ q.toMultiset, ∀ x, φ i (e x) = φ i x := by
    have hm : p.toMultiset.map (𝔠) = q.toMultiset.map (𝔠) := by
      simp only [Finsupp.toMultiset_map]
      congr 1
      apply Finsupp.mapRange_injective (Nat.cast : ℕ → ℚ) Nat.cast_zero Nat.cast_injective
      rw [← Finsupp.mapDomain_mapRange _ _ _ _ Nat.cast_add, ← Finsupp.mapDomain_mapRange _ _ _ _ Nat.cast_add, ← sub_eq_zero,
        ← Finsupp.mapDomain_sub, show p.mapRange Nat.cast Nat.cast_zero - q.mapRange Nat.cast Nat.cast_zero = 𝔡 • μ.coeff from
        Finsupp.ext fun γ => by simp_all, Finsupp.mapDomain_smul]
      exact smul_eq_zero_of_right _ (hcos i)
    refine ⟨(p.toMultiset.mapEquiv _).trans ((Multiset.cast hm).trans (q.toMultiset.mapEquiv _).symm), fun x => ?_⟩
    have : 𝔠 _ = _ := ((Multiset.mapEquiv_apply _ _ _).symm.trans (congrArg Sigma.fst ((q.toMultiset.mapEquiv _).apply_symm_apply (Multiset.cast hm (p.toMultiset.mapEquiv _ x))))).trans (Multiset.mapEquiv_apply _ _ x)
    exact congrArg (QuotientAddGroup.lift _ (φ i) le_rfl) this
  choose e he using he
  let W (c : Lattice k →₀ ℕ) : Matrix (Fin d) c.toMultiset ℝ := Matrix.of fun α x => g x α
  have hW c hc α β : (W c * (W c)ᵀ) α β = ∑ γ ∈ S, c γ * 𝔞 := hsum c hc fun γ => g γ α * g γ β
  have hM α β : ∑ γ ∈ S, μ.coeff γ * 𝔞 = ζ * (1 : 𝕄 d ℝ) α β := by
    trans ∑ j, ∑ l, U α j * U β l * (secondMoment μ j l / n ^ 2 : ℚ)
    · simp [secondMoment, Finsupp.sum, g, latticeSample, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
      simp_rw [Finset.sum_comm (s := S)]
      exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    · simp [hmom, ← hU, mul_apply, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  set K : ℝ := A.den * ζ
  have hden : (0:ℝ) < A.den := Nat.cast_pos.mpr (Nat.pos_of_ne_zero A.den_ne_zero)
  have hdiff : W p * (W p)ᵀ = W q * 𝔟ᵀ + K • 1 := by
    ext α β
    simp only [Matrix.add_apply, Matrix.smul_apply, hW p Finsupp.support_mapRange, hW q Finsupp.support_mapRange, K, mul_assoc, ← hM, Finset.mul_sum, ← Finset.sum_add_distrib, smul_eq_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have := congrArg (Rat.cast : ℚ → ℝ) (hpq γ)
    push_cast at this
    linear_combination 𝔞 * this
  obtain ⟨R, hR⟩ := gram_complement (W q * 𝔟ᵀ) (by simpa using posSemidef_self_mul_conjTranspose 𝔟) (η * K) (by
    rw [tsum_eq_sum (s := S) (fun γ hγ => by aesop)] at hneg
    have : (W q * 𝔟ᵀ).trace = A.den * ∑ γ ∈ S, max (-(μ.coeff γ:ℝ)) 0 * gradientWeight U (latticeSample n γ) := by
      simp only [trace, diag, hW q Finsupp.support_mapRange, gradientWeight, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun γ _ => ?_
      have := congrArg (Rat.cast : ℚ → ℝ) (hq γ)
      push_cast at this
      simp [this, g, sq, mul_assoc]
    rw [this]
    exact (mul_lt_mul_of_pos_left hneg hden).le.trans_eq (by ring))
  have hK : 0 < K := mul_pos hden (mod_cast hζ)
  have hK1 : 0 < 𝔢 := mul_pos hK (by linarith)
  let ep := Fintype.equivFin (p.toMultiset ⊕ Fin d)
  let eq := ((e ⟨0, hs⟩).sumCongr (Equiv.refl (Fin d))).symm.trans ep
  let c := (√(𝔢))⁻¹
  refine ⟨_, by simp; omega, fun i => 𝔉 (Sum.elim (fun x : p.toMultiset => v x) 0) (fromCols (W p) R) ep (a i),
    fun i => 𝔉 (Sum.elim (fun x : q.toMultiset => v x) 0) (fromCols 𝔟 R) eq (a i), fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · rw [row_gram_distance ep c _ _ (𝔢) (by rw [transpose_fromCols, fromCols_mul_fromRows, hdiff, hR]; module)]
    simp [c, hK1.le]
    field_simp
  · rw [row_gram_distance eq c _ _ (η * K) (by rw [transpose_fromCols, fromCols_mul_fromRows, hR]; abel)]
    simp [c, hK1.le]
    field_simp
    simp
  · refine ⟨ep.symm.trans (((e i).sumCongr (Equiv.refl _)).trans eq), fun y => ?_⟩
    simp
    rcases ep.symm y with x | x <;> simp [W, ← hφ, he]
