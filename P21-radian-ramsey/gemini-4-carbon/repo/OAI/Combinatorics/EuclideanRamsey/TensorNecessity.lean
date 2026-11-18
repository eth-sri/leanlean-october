module

public import OAI.Combinatorics.EuclideanRamsey.Model

@[expose] public section
namespace OAI

noncomputable section
open scoped TensorProduct RealInnerProductSpace BigOperators

namespace EuclideanRamsey

abbrev RealTensor := ℝ ⊗[ℚ] ℝ
abbrev RealArray (d : ℕ) := Matrix (Option (Fin d)) (Option (Fin d)) RealTensor

def realAugmented {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : Option (Fin d) → ℝ
  | none => 1
  | some j => a i j

def arrayEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : RealArray d →ₗ[ℚ] RealTensor where
  toFun P := ∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) * P α β * ((1 : ℝ) ⊗ₜ[ℚ] realAugmented a i β)
  map_add' _ _ := by simp [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum]

def spatialMultiply {d : ℕ} : RealArray d →ₗ[ℚ] Matrix (Fin d) (Fin d) ℝ where
  toFun P α β := Algebra.TensorProduct.lmul' ℚ (P (some α) (some β))
  map_add' _ _ := by ext; exact map_add _ _ _
  map_smul' q _ := by ext; exact (Algebra.TensorProduct.lmul' ℚ).toLinearMap.map_smul q _

def RealCriterion {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∃ P : RealArray d, (∀ i, arrayEvaluation a i P = 0) ∧ spatialMultiply P = 1

theorem ramsey_realCriterion {s d : ℕ} (a : Fin s → Space d)
    (hs : 0 < s) (hspan : affineSpan ℝ (Set.range a) = ⊤) (hR : Ramsey a) : RealCriterion a := by
  classical
  by_contra h
  let i₀ : Fin s := ⟨0, hs⟩
  let arrayMap : RealArray d →ₗ[ℚ] (Fin s → RealTensor) × Matrix (Fin d) (Fin d) ℝ :=
    (LinearMap.pi (arrayEvaluation a)).prod spatialMultiply
  let N := LinearMap.range arrayMap
  have hq : N.mkQ (0, 1) ≠ 0 := fun hz => h <| by
    obtain ⟨P, hP⟩ := (Submodule.Quotient.mk_eq_zero N).mp hz
    exact ⟨P, fun i => congrFun (congrArg Prod.fst hP) i, congrArg Prod.snd hP⟩
  obtain ⟨dual_f, hdf⟩ := Module.Projective.exists_dual_eq_one ℚ hq
  let ℓ := (Algebra.linearMap ℚ ℝ).comp (dual_f.comp N.mkQ)
  have hℓ (P : RealArray d) : ℓ (arrayMap P) = 0 := by
    simp [ℓ, (Submodule.Quotient.mk_eq_zero N).mpr ⟨P, rfl⟩]
  have hℓ1 : ℓ (0, 1) = 1 := by change ((dual_f (N.mkQ (0, 1)) : ℚ) : ℝ) = 1; rw [hdf]; norm_num
  let f (i : Fin s) (x : ℝ) : ℝ := ℓ (Pi.single i (x ⊗ₜ[ℚ] x), 0)
  let L := ℓ.comp (LinearMap.inr ℚ _ _)
  have hsplit (x : Fin s → RealTensor) (M : Matrix (Fin d) (Fin d) ℝ) :
      ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + L M := by
    change ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + ℓ (0, M)
    rw [← map_sum, ← map_add]; congr 1
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  let rk1 (u : Space d) : Matrix (Fin d) (Fin d) ℝ := fun α β => u α * u β
  have heq (v : ℝ) (u : Space d) :
      (∑ i, f i (v + ∑ α, a i α * u α)) + L (rk1 u) = 0 := by
    let w : Option (Fin d) → ℝ := fun α => α.elim v (u ·)
    have hp := hℓ fun α β => w α ⊗ₜ[ℚ] w β
    have h1 (i : Fin s) : arrayEvaluation a i (fun α β => w α ⊗ₜ[ℚ] w β) =
        (v + ∑ α, a i α * u α) ⊗ₜ[ℚ] (v + ∑ α, a i α * u α) := by
      have hw : v + ∑ α, a i α * u α = ∑ α, realAugmented a i α * w α := by
        simp [realAugmented, w, Fintype.sum_option]
      rw [hw, TensorProduct.sum_tmul]; simp only [TensorProduct.tmul_sum]
      change (∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) * (w α ⊗ₜ[ℚ] w β) *
        ((1 : ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
    have h2 : spatialMultiply (fun α β => w α ⊗ₜ[ℚ] w β) = rk1 u := by ext; rfl
    change ℓ (fun i => arrayEvaluation a i _, spatialMultiply _) = 0 at hp
    simp only [h1, h2] at hp; rwa [hsplit] at hp
  have hcancel (x : ℝ) : ∑ i, f i x = 0 := by
    have hz : rk1 0 = 0 := by ext; simp [rk1]
    simpa [hz] using heq x 0
  let K := 2 * s + 1
  let Colors := Fin s → ZMod K
  have hr : 2 ≤ Fintype.card Colors := by
    change 2 ≤ Fintype.card (Fin s → ZMod K)
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    exact Nat.one_lt_pow (by omega) (by dsimp [K]; omega)
  obtain ⟨D, _, hD'⟩ := hR (Fintype.card Colors) hr
  let H (i : Fin s) (z : Space D) : ℝ := ∑ j, f i (z j)
  let color (z : Space D) : Colors := fun i => (⌊(K : ℝ) / 2 * H i z⌋ : ZMod K)
  obtain ⟨b, hb, k, hk⟩ := hD' fun z => Fintype.equivFin Colors (color z)
  obtain ⟨Q, t, hQ⟩ : ∃ Q : Space d →ₗᵢ[ℝ] Space D, ∃ t : Space D, ∀ i, b i = t + Q (a i) := by
    let x := fun i => a i - a i₀
    let y := fun i => b i - b i₀
    have hs' : Submodule.span ℝ (Set.range x) = ⊤ := by
      have hv : vectorSpan ℝ (Set.range a) = ⊤ := by
        simpa [direction_affineSpan] using congrArg AffineSubspace.direction hspan
      rwa [vectorSpan_range_eq_span_range_vsub_right ℝ a i₀] at hv
    have hg (i j : Fin s) : ⟪y i, y j⟫ = ⟪x i, x j⟫ := by
      simp only [x, y, real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
        sub_sub_sub_cancel_right, ← dist_eq_norm, hb i i₀, hb j i₀, hb i j]
    let A := Fintype.linearCombination ℝ x
    let B := Fintype.linearCombination ℝ y
    have hnorm (c : Fin s → ℝ) : ‖B c‖ = ‖A c‖ := by
      have hi : ⟪B c, B c⟫ = ⟪A c, A c⟫ := by
        simp only [A, B, Fintype.linearCombination_apply, sum_inner, inner_sum,
          real_inner_smul_left, inner_smul_right, hg]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
      nlinarith [norm_nonneg (B c), norm_nonneg (A c)]
    obtain ⟨R, hR⟩ := A.exists_rightInverse_of_surjective (by rwa [Fintype.range_linearCombination])
    have hR' (z : Space d) : A (R z) = z := LinearMap.congr_fun hR z
    let Q : Space d →ₗᵢ[ℝ] Space D := ⟨B.comp R, fun z => by change ‖B (R z)‖ = ‖z‖; rw [hnorm, hR']⟩
    refine ⟨Q, b i₀ - Q (a i₀), fun i => ?_⟩
    have hf : Q (x i) = y i := by
      simpa [Q, A, B, sub_eq_zero] using norm_eq_zero.mp
        (by rw [hnorm, map_sub, hR', sub_self, norm_zero] : ‖B (R (A (Pi.single i 1)) - Pi.single i 1)‖ = 0)
    rw [map_sub] at hf
    calc b i = y i + b i₀ := (sub_add_cancel _ _).symm
      _ = (Q (a i) - Q (a i₀)) + b i₀ := by rw [hf]
      _ = b i₀ - Q (a i₀) + Q (a i) := by abel
  have hsum_neg1 : ∑ i, H i (b i) = -1 := by
    simp only [H, hQ]
    rw [Finset.sum_comm]
    let row (j : Fin D) : Space d := WithLp.toLp 2 fun α => Q (EuclideanSpace.single α 1) j
    have heach (j : Fin D) : (∑ i, f i ((t + Q (a i)) j)) = -L (rk1 (row j)) := by
      apply eq_neg_of_add_eq_zero_left
      convert heq (t j) (row j) using 2
      refine Finset.sum_congr rfl fun i _ => congrArg (f i) ?_
      have hx := congrArg (fun z : Space d => Q z j) ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (a i))
      simp only [PiLp.add_apply]; congr 1
      simpa only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
        WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, row, WithLp.ofLp_toLp] using hx.symm
    have hrows : (∑ j : Fin D, rk1 (row j)) = (1 : Matrix (Fin d) (Fin d) ℝ) := by
      ext α β
      have hg := Q.inner_map_map (EuclideanSpace.single β 1) (EuclideanSpace.single α 1)
      rw [EuclideanSpace.inner_single_right] at hg
      rw [Matrix.sum_apply, Matrix.one_apply]
      simpa only [rk1, row, WithLp.ofLp_toLp, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        map_one, one_mul, PiLp.single_apply] using hg
    simp only [heach, Finset.sum_neg_distrib, ← map_sum, hrows]
    exact congrArg Neg.neg hℓ1
  have hmono (i : Fin s) : color (b i) i = color (b i₀) i :=
    congrFun ((Fintype.equivFin Colors).injective ((hk i).trans (hk i₀).symm)) i
  let x (i : Fin s) : ℝ := (K : ℝ) / 2 * H i (b i)
  let y (i : Fin s) : ℝ := (K : ℝ) / 2 * H i (b i₀)
  let fl (g : Fin s → ℝ) : ℤ := ∑ i, ⌊g i⌋
  have hfl (g : Fin s → ℝ) : (∑ i, g i) - s < (fl g : ℝ) ∧ (fl g : ℝ) ≤ ∑ i, g i := by
    have hlt := Finset.sum_lt_sum_of_nonempty ⟨i₀, Finset.mem_univ _⟩ fun i _ => Int.lt_floor_add_one (g i)
    have hle := Finset.sum_le_sum (s := Finset.univ) fun i _ => Int.floor_le (g i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hlt
    exact ⟨by dsimp [fl]; push_cast; linarith, by simpa only [fl, Int.cast_sum] using hle⟩
  obtain ⟨hx1, hx2⟩ := hfl x; obtain ⟨hy1, hy2⟩ := hfl y
  have hx_s : ∑ i, x i = -(K : ℝ) / 2 := by simp [x, ← Finset.mul_sum, hsum_neg1]; ring
  have hy_s : ∑ i, y i = 0 := by
    have hH0 : ∑ i, H i (b i₀) = 0 := by dsimp [H]; rw [Finset.sum_comm]; simp [hcancel]
    simp [y, ← Finset.mul_sum, hH0]
  rw [hx_s] at hx1 hx2; rw [hy_s] at hy1 hy2
  have hdvd : (K : ℤ) ∣ fl y - fl x := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ K).mp <| by
    simpa only [fl, Int.cast_sum] using Finset.sum_congr rfl fun i _ => hmono i
  have hK_eq : (K : ℝ) = 2 * (s : ℝ) + 1 := by simp [K]
  have hpos : (0 : ℤ) < fl y - fl x := by exact_mod_cast (by push_cast; linarith : (0 : ℝ) < (fl y - fl x : ℤ))
  have hlt : fl y - fl x < (K : ℤ) := by exact_mod_cast (by push_cast; linarith : ((fl y - fl x : ℤ) : ℝ) < K)
  exact not_le_of_gt hlt (Int.le_of_dvd hpos hdvd)

end EuclideanRamsey
end
end OAI
