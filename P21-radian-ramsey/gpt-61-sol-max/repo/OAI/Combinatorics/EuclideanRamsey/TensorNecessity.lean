/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/TensorNecessity.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.Congruence

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section

open scoped TensorProduct

private theorem sum_floor_bounds {s : ℕ} (hs : 0 < s) (f : Fin s → ℝ) :
    (∑ i, f i) - s < ((∑ i, ⌊f i⌋ : ℤ) : ℝ) ∧
    ((∑ i, ⌊f i⌋ : ℤ) : ℝ) ≤ ∑ i, f i := by
  have hu : (Finset.univ : Finset (Fin s)).Nonempty := ⟨⟨0, hs⟩, Finset.mem_univ _⟩
  have hlt := Finset.sum_lt_sum_of_nonempty hu (fun i _ => Int.lt_floor_add_one (f i))
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => Int.floor_le (f i))
  simp [Finset.sum_add_distrib] at hlt
  constructor
  · push_cast
    linarith
  · simpa using hle

abbrev RealTensor := ℝ ⊗[ℚ] ℝ
abbrev RealArray (d : ℕ) := Matrix (Option (Fin d)) (Option (Fin d)) RealTensor
abbrev SeparationSpace (s d : ℕ) := (Fin s → RealTensor) × Matrix (Fin d) (Fin d) ℝ

variable {s d : ℕ} (a : Fin s → Space d)

def realAugmented  (i : Fin s) : Option (Fin d) → ℝ
  | none => 1
  | some j => a i j

def arrayEvaluation  (i : Fin s) :
    RealArray d →ₗ[ℚ] RealTensor where
  toFun P := ∑ α, ∑ β, ((realAugmented a i α) ⊗ₜ[ℚ] (1 : ℝ)) * P α β *
    ((1 : ℝ) ⊗ₜ[ℚ] (realAugmented a i β))
  map_add' P Q := by
    simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' q P := by
    simp [Finset.smul_sum]

def spatialMultiply {d : ℕ} : RealArray d →ₗ[ℚ] Matrix (Fin d) (Fin d) ℝ where
  toFun P := fun α β => Algebra.TensorProduct.lmul' ℚ (P (some α) (some β))
  map_add' P Q := by
    aesop
  map_smul' q P := by
    aesop

def arrayMap  :
    RealArray d →ₗ[ℚ] SeparationSpace s d :=
  (LinearMap.pi (arrayEvaluation a)).prod spatialMultiply

def RealCriterion  : Prop :=
  ∃ P : RealArray d, (∀ i, arrayEvaluation a i P = 0) ∧ spatialMultiply P = 1

abbrev AffineVector (d : ℕ) := Option (Fin d) → ℝ

def affineArray {d : ℕ} :
    (AffineVector d ⊗[ℚ] AffineVector d) ≃ₗ[ℚ] RealArray d :=
  (TensorProduct.piLeft ℚ (AffineVector d) (fun _ : Option (Fin d) => ℝ)).trans
    (LinearEquiv.piCongrRight (fun _ => TensorProduct.piRight ℚ ℚ ℝ (fun _ : Option (Fin d) => ℝ)))

@[simp] lemma affineArray_tmul {d : ℕ} (w z : AffineVector d) (α β : Option (Fin d)) :
    affineArray (w ⊗ₜ[ℚ] z) α β = w α ⊗ₜ[ℚ] z β := by
  rfl

def rowEvaluation (i : Fin s) : AffineVector d →ₗ[ℚ] ℝ :=
  dotProductBilin ℚ ℚ (realAugmented a i)

lemma arrayEvaluation_affineArray (i : Fin s)
    (T : AffineVector d ⊗[ℚ] AffineVector d) :
    arrayEvaluation a i (affineArray T) = TensorProduct.map (rowEvaluation a i) (rowEvaluation a i) T := by
  induction T using TensorProduct.inductionOn with
  | tmul w z =>
    simp [-Fintype.sum_option,arrayEvaluation,rowEvaluation,dotProductBilin,dotProduct,
      TensorProduct.sum_tmul,TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  | add x y hx hy => simp [hx,hy]

theorem ramsey_realCriterion 
    (hs : 0 < s) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hR : Ramsey a) : RealCriterion a := by
  classical
  by_contra h
  let N := LinearMap.range (arrayMap a)
  have hy : (0, 1) ∉ N := by
    rintro ⟨P, hP⟩
    apply h
    refine ⟨P, ?_, ?_⟩
    · intro i
      exact congrFun (congrArg Prod.fst hP) i
    · exact congrArg Prod.snd hP
  have hq : N.mkQ (0, 1) ≠ 0 := by
    intro hz
    exact hy ((Submodule.Quotient.mk_eq_zero N).mp hz)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ hq
  let ℓ  :=
    (Algebra.linearMap ℚ ℝ).comp (f.comp N.mkQ)
  have hℓ (P) : ℓ (arrayMap a P) = 0 := by
    have hp : N.mkQ (arrayMap a P) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero N).mpr
      exact ⟨P, rfl⟩
    simp [ℓ, hp]
  have hℓ₀ : ℓ (0, 1) = 1 := by simp_all +zetaDelta
  let f  := fun i x => ℓ (Pi.single i (x ⊗ₜ[ℚ] x), 0)
  let L  := ℓ.comp (LinearMap.inr ℚ _ _)
  have hsplit x M :
      ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + L M := by
    change ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + ℓ (0, M)
    rw [← map_sum, ← map_add]
    congr 1
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  let rankOne (u : Space d) : Matrix (Fin d) (Fin d) ℝ := fun α β => u α*u β
  have heq v u :
      (∑ i, f i (v+∑ j,a i j*u j)) + L (rankOne u) = 0 := by
    let w : AffineVector d := fun α => α.elim v (u ·)
    have hp := hℓ (affineArray (w ⊗ₜ[ℚ] w))
    change ℓ ((fun i => arrayEvaluation a i (affineArray (w ⊗ₜ[ℚ] w))),rankOne u) = 0 at hp
    simp [arrayEvaluation_affineArray,rowEvaluation,dotProductBilin,dotProduct,
      realAugmented,Fintype.sum_option,w] at hp
    rw [hsplit] at hp
    exact hp
  have hL : L 1 = 1 := hℓ₀
  have hcancel x : ∑ i, f i x = 0 := by
    have hz : rankOne (0 : Space d) = 0 := by ext; simp [rankOne]
    simpa [hz] using heq x (0 : Space d)

  let K := 2 * s + 1
  let Colors := Fin s → ZMod K
  have hK : 1 < K := by dsimp [K]; omega
  have hr : 2 ≤ Fintype.card Colors := by
    change 2 ≤ Fintype.card (Fin s → ZMod K)
    simp
    exact Nat.one_lt_pow (by omega) hK
  obtain ⟨D, hD, hD'⟩ := hR (Fintype.card Colors) hr
  let H : Fin s → Space D → ℝ := fun i z => ∑ j, f i (z j)
  have hH z : ∑ i, H i z = 0 := by
    simp [H]
    rw [Finset.sum_comm]
    simp [hcancel]
  let color  := fun z i => (⌊(K : ℝ) / 2 * H i z⌋ : ZMod K)
  obtain ⟨b, hb, k, hk⟩ := hD' (fun z => Fintype.equivFin Colors (color z))
  have hmono : ∀ i, color (b i) = color (b ⟨0, hs⟩) := by
    intro i
    apply (Fintype.equivFin Colors).injective
    exact (hk i).trans (hk ⟨0, hs⟩).symm
  obtain ⟨Q, t, hQ⟩ := congruent_linearIsometry a b ⟨0, hs⟩ hspan hb
  let rows j : Space d := WithLp.toLp 2 (fun α => Q (EuclideanSpace.single α 1) j)
  have hsum : ∑ i, H i (b i) = -1 := by
    simp only [H, hQ]
    have hrows : (∑ j, rankOne (rows j)) = (1 : Matrix (Fin d) (Fin d) ℝ) := by
      ext α β
      simp only [Matrix.sum_apply,Matrix.one_apply]
      have h := Q.inner_map_map (EuclideanSpace.single β 1) (EuclideanSpace.single α 1)
      rw [EuclideanSpace.inner_single_left] at h
      simpa only [rankOne, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, map_one, one_mul, PiLp.single_apply,
        eq_comm (a := α) (b := β), rows, WithLp.ofLp_toLp] using h
    have heach j :
        (∑ i, f i ((t + Q (a i)) j)) = -L (rankOne (rows j)) := by
      have h := heq (t j) (rows j)
      apply eq_neg_of_add_eq_zero_left
      convert h using 2
      congr! 1 with i _
      congr 1
      simp only [PiLp.add_apply]
      congr 1
      have hv := congrArg (fun z : Space d => Q z j)
        ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (a i))
      simpa [rows] using hv.symm
    rw [Finset.sum_comm]
    simp only [heach, Finset.sum_neg_distrib, ← map_sum, hrows, hL]
  let x  := fun i => (K : ℝ) / 2 * H i (b i)
  let y  := fun i => (K : ℝ) / 2 * H i (b ⟨0, hs⟩)
  have hx : ∑ i, x i = -(K : ℝ) / 2 := by
    simp [x, ← Finset.mul_sum, hsum]; ring
  have hy : ∑ i, y i = 0 := by
    simp [y, ← Finset.mul_sum, hH]
  let A  := ∑ i, ⌊x i⌋
  let B  := ∑ i, ⌊y i⌋
  have hAB : (A : ZMod K) = (B : ZMod K) := by
    simp [A, B]
    congr! 1 with i _
    exact congrFun (hmono i) i
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub A B K).mp hAB
  obtain ⟨hxlo, hxhi⟩ := sum_floor_bounds hs x
  obtain ⟨hylo, hyhi⟩ := sum_floor_bounds hs y
  have hKcast : (K : ℝ) = 2 * (s : ℝ) + 1 := by simp [K]
  have hbds : B-A ∈ Set.Ioo (0:ℤ) K := by
    have : (B:ℝ)-(A:ℝ) ∈ Set.Ioo (0:ℝ) K := by
      dsimp only [Set.mem_Ioo,A,B]
      constructor <;> linarith
    simp only [Set.mem_Ioo] at this ⊢
    exact_mod_cast this
  exact (not_le_of_gt hbds.2) (Int.le_of_dvd hbds.1 hdvd)


end

end OAI.EuclideanRamsey
