module

public import OAI.Combinatorics.EuclideanRamsey.Congruence

@[expose] public section

noncomputable section

open scoped TensorProduct RealInnerProductSpace

notation "𝕄" k:max R:max => Matrix (Fin k) (Fin k) R

set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
local notation "𝔟" => affineEvaluation a i v u
local notation "𝔞" => (Fin d)
notation "𝔰" => (2 * s + 1)

variable (a : Fin s → Space d)

abbrev RealTensor := ℝ ⊗[ℚ] ℝ
abbrev RealArray d := Matrix (Option 𝔞) (Option 𝔞) RealTensor

def realAugmented (i : Fin s) : Option 𝔞 → ℝ
  | none => 1
  | some j => a i j

def arrayEvaluation (i : Fin s) :
    RealArray d →ₗ[ℚ] RealTensor where
  toFun P := ∑ α, ∑ β, ((realAugmented a i α) ⊗ₜ[ℚ] (1 : ℝ)) * P α β *
    ((1 : ℝ) ⊗ₜ[ℚ] (realAugmented a i β))
  map_add' P Q := by simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' q P := by simp [Finset.smul_sum]

def spatialMultiply : RealArray d →ₗ[ℚ] 𝕄 d ℝ where
  toFun P α β := Algebra.TensorProduct.lmul' ℚ (P (some α) (some β))
  map_add' P Q := by aesop
  map_smul' q P := by aesop

def RealCriterion : Prop :=
  ∃ P, (∀ i, arrayEvaluation a i P = 0) ∧ spatialMultiply P = 1

def affineEvaluation (i : Fin s)
    (v : ℝ) (u : Fin d → ℝ) : ℝ := v + ∑ j, a i j * u j

theorem exists_separated_functions
    (h : ¬ RealCriterion a) :
    ∃ f : Fin s → ℝ → ℝ, ∃ L : 𝕄 d ℝ →ₗ[ℚ] ℝ,
      L 1 = 1 ∧
      (∀ v u, (∑ i, f i (𝔟)) + L (Matrix.vecMulVec u u) = 0) ∧
      ∀ x, ∑ i, f i x = 0 := by
  classical
  let N := LinearMap.range ((LinearMap.pi (arrayEvaluation a)).prod spatialMultiply)
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one ℚ (x := N.mkQ (0, 1))
    fun hz => h <| by
      obtain ⟨P, hP⟩ := (Submodule.Quotient.mk_eq_zero N).mp hz
      exact ⟨P, fun i => congrFun (congrArg Prod.fst hP) i, congrArg Prod.snd hP⟩
  let ℓ := (Algebra.linearMap ℚ ℝ).comp (g.comp N.mkQ)
  have hℓ P : ℓ (fun i => arrayEvaluation a i P, spatialMultiply P) = 0 := by
    simp [ℓ, (Submodule.Quotient.mk_eq_zero N
      (x := (fun i => arrayEvaluation a i P, spatialMultiply P))).mpr ⟨P, rfl⟩]
  have hsplit x M :
      ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + ℓ (0, M) := by
    rw [← map_sum, ← map_add]
    congr 1
    ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  have heq v u :
      (∑ i, ℓ (Pi.single i (𝔟 ⊗ₜ 𝔟), 0)) +
        ℓ (0, Matrix.vecMulVec u u) = 0 := by
    let w : Option 𝔞 → ℝ := fun α => α.elim v u
    have he i : 𝔟 = ∑ α, realAugmented a i α * w α := by
      simp [affineEvaluation, realAugmented, w, Fintype.sum_option]
    convert (hsplit _ _).symm.trans (hℓ fun α β => w α ⊗ₜ[ℚ] w β)
    · simp only [arrayEvaluation, LinearMap.coe_mk, AddHom.coe_mk, he, TensorProduct.sum_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      simp only [TensorProduct.tmul_sum, mul_comm]
    · ext
      exact (Algebra.TensorProduct.lmul'_apply_tmul _ _).symm
  refine ⟨fun i x => ℓ (Pi.single i (x ⊗ₜ[ℚ] x), 0), ℓ.comp (LinearMap.inr ℚ _ _), by simpa [ℓ] using congrArg (Rat.cast : ℚ → ℝ) hg,
    heq, fun x => ?_⟩
  simpa [affineEvaluation, Prod.mk_zero_zero] using heq x 0

notation:max "𝔮" j:max => fun α => Q (EuclideanSpace.single α 1) j

theorem ramsey_realCriterion
    (hs : 0 < s) (hspan : affineSpan ℝ (Set.range a) = ⊤)
    (hR : Ramsey a) : RealCriterion a := by
  classical
  by_contra h
  obtain ⟨f, L, hL, heq, hcancel⟩ := exists_separated_functions a h
  obtain ⟨D, -, hD⟩ := hR (Fintype.card (Fin s → ZMod 𝔰))
    (by simp; exact Nat.one_lt_pow hs.ne' (by omega))
  let H : Fin s → Space D → ℝ := fun i z => (2 * s + 1 : ℝ) / 2 * ∑ j, f i (z j)
  obtain ⟨b, hb, k, hk⟩ := hD fun z => Fintype.equivFin _ fun i => (⌊H i z⌋ : ZMod 𝔰)
  have i₀ : Fin s := ⟨0, hs⟩
  obtain ⟨Q, t, hQ⟩ := congruent_linearIsometry a b i₀ hspan hb
  have hsum : ∑ i, H i (b i) = -𝔰 / 2 := by
    have heach j : ∑ i, f i ((t + Q (a i)) j) =
        -L (Matrix.vecMulVec 𝔮 j 𝔮 j) := by
      refine eq_neg_of_add_eq_zero_left (.trans ?_ (heq (t j) 𝔮 j))
      congr 2
      ext i
      conv_lhs => rw [← (EuclideanSpace.basisFun 𝔞 ℝ).sum_repr (a i)]
      simp [affineEvaluation]
    have hrows : ∑ j, Matrix.vecMulVec 𝔮 j 𝔮 j = 1 := by
      ext α β
      have := Q.inner_map_map (EuclideanSpace.single β 1) (EuclideanSpace.single α 1)
      rw [EuclideanSpace.inner_single_left] at this
      simpa [-LinearIsometry.inner_map_map, PiLp.inner_apply, eq_comm, mul_comm, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.one_apply] using this
    simp only [H, hQ, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [heach, Finset.sum_neg_distrib, ← map_sum, hrows, hL]
    ring
  have h0 : ∑ i, H i (b i₀) = 0 := by
    simp only [H, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [hcancel]
  have hbd (x : Fin s → ℝ) : (∑ i, x i) - s < ∑ i, (⌊x i⌋ : ℝ) ∧ ∑ i, (⌊x i⌋ : ℝ) ≤ ∑ i, x i := by
    have := Finset.sum_lt_sum_of_nonempty ⟨i₀, Finset.mem_univ _⟩
      fun i _ => Int.lt_floor_add_one (x i)
    exact ⟨by simp [Finset.sum_add_distrib] at this; linarith,
      Finset.sum_le_sum fun i _ => Int.floor_le _⟩
  obtain ⟨h1, h2⟩ := hbd fun i => H i (b i)
  obtain ⟨h3, h4⟩ := hbd fun i => H i (b i₀)
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub (∑ i, ⌊H i (b i)⌋) (∑ i, ⌊H i (b i₀)⌋)
    𝔰).mp <| by
      push_cast
      exact Finset.sum_congr rfl fun i _ => congrFun
        ((Fintype.equivFin (Fin s → ZMod 𝔰)).injective ((hk i).trans (hk _).symm)) i
  have := Int.le_of_dvd (by rify; linarith) hdvd
  rify at this
  linarith
