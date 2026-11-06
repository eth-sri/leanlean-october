module

public import RadianRamsey.RadianAlgebra
public import RadianRamsey.AlgebraicRamsey
public import OAI.Combinatorics.EuclideanRamsey.TensorDescent
public import OAI.Combinatorics.EuclideanRamsey.IndependentTensor
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

@[expose] public section

namespace OAI.EuclideanRamsey.Radian
noncomputable section
open scoped TensorProduct BigOperators RealInnerProductSpace

def radianConfig (θ : ℝ) (k : Fin 9) : Space 2 :=
  WithLp.toLp 2 ![Real.cos ((k : ℕ) * θ), Real.sin ((k : ℕ) * θ)]

@[simp] theorem radianConfig_zero (θ : ℝ) (k : Fin 9) :
    radianConfig θ k 0 = Real.cos ((k : ℕ) * θ) := by simp [radianConfig]

@[simp] theorem radianConfig_one (θ : ℝ) (k : Fin 9) :
    radianConfig θ k 1 = Real.sin ((k : ℕ) * θ) := by simp [radianConfig]

abbrev th (θ : ℝ) := Real.tan (θ / 2)

section Generic
variable {R S : Type*} [CommRing R] [CommRing S]

def rot (z : R) : ℕ → R × R
  | 0 => (1, 0)
  | n + 1 => ((1 - z ^ 2) * (rot z n).1 - 2 * z * (rot z n).2,
      2 * z * (rot z n).1 + (1 - z ^ 2) * (rot z n).2)

def qv (z : R) (n : ℕ) : Fin 3 → R := ![(1 + z ^ 2) ^ n, (rot z n).1, (rot z n).2]

def col (j : Fin 9) : Fin 3 × Fin 3 := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3 * 3)).symm j

def Ecl (z w : R) : Matrix (Fin 9) (Fin 9) R := fun k j =>
  qv z k (col j).1 * qv w k (col j).2

theorem map_rot (f : R →+* S) (z : R) (n : ℕ) :
    f (rot z n).1 = (rot (f z) n).1 ∧ f (rot z n).2 = (rot (f z) n).2 := by
  induction n with
  | zero => simp [rot]
  | succ n ih =>
    constructor <;> simp only [rot, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, ih.1, ih.2]

theorem map_qv (f : R →+* S) (z : R) (n : ℕ) (a : Fin 3) : f (qv z n a) = qv (f z) n a := by
  fin_cases a <;> simp [qv, (map_rot f z n).1, (map_rot f z n).2]

theorem map_Ecl (f : R →+* S) (z w : R) : f.mapMatrix (Ecl z w) = Ecl (f z) (f w) := by
  ext k j; simp [Ecl, map_qv]

end Generic

abbrev Poly₁ := MvPolynomial Unit ℚ
abbrev Rat₁ := FractionRing Poly₁
abbrev Poly := MvPolynomial (Unit ⊕ Unit) ℚ
abbrev JointField := FractionRing Poly

local instance ratAlgebra : Algebra ℚ Rat₁ :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := Poly₁) (S := nonZeroDivisors Poly₁)

local instance jointAlgebra : Algebra ℚ JointField :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := Poly) (S := nonZeroDivisors Poly)

def T : Poly := MvPolynomial.X (Sum.inl ())
def U : Poly := MvPolynomial.X (Sum.inr ())

def polyToRat : Poly₁ →ₐ[ℚ] Rat₁ := IsScalarTower.toAlgHom ℚ _ _
def jointToField : Poly →ₐ[ℚ] JointField := IsScalarTower.toAlgHom ℚ _ _

theorem sideMap_injective {f : Unit → Unit ⊕ Unit} (hf : Function.Injective f) :
    Function.Injective (jointToField.comp (MvPolynomial.rename f)) :=
  (IsFractionRing.injective Poly JointField).comp (MvPolynomial.rename_injective f hf)

def sideMap (f : Unit → Unit ⊕ Unit) (hf : Function.Injective f) : Rat₁ →ₐ[ℚ] JointField :=
  IsFractionRing.liftAlgHom (K := Rat₁) (sideMap_injective hf)

@[simp] theorem sideMap_algebraMap (f : Unit → Unit ⊕ Unit) (hf : Function.Injective f) (p : Poly₁) :
    sideMap f hf (algebraMap Poly₁ Rat₁ p) =
      algebraMap Poly JointField (MvPolynomial.rename f p) :=
  IsFractionRing.lift_algebraMap (K := Rat₁)
    (g := (jointToField.comp (MvPolynomial.rename f)).toRingHom) (sideMap_injective hf) p

abbrev leftMap := sideMap Sum.inl Sum.inl_injective
abbrev rightMap := sideMap Sum.inr Sum.inr_injective

def tensorEmbedding : Rat₁ ⊗[ℚ] Rat₁ →ₐ[ℚ] JointField :=
  Algebra.TensorProduct.lift leftMap rightMap fun _ _ => Commute.all _ _

abbrev incl : Poly →+* JointField := algebraMap Poly JointField

theorem det_Ecl_ne_zero : (Ecl (incl T) (incl U)).det ≠ 0 := by
  intro h0
  rw [← map_Ecl, ← RingHom.map_det] at h0
  have h1 := congrArg (MvPolynomial.eval (Sum.elim (fun _ => (2 : ℚ)) (fun _ => 3)))
    ((IsFractionRing.injective Poly JointField) (h0.trans (map_zero incl).symm))
  rw [RingHom.map_det, map_Ecl, map_zero] at h1
  have h2 : (Int.castRingHom ℚ) (Ecl (2 : ℤ) 3).det = 0 := by
    rw [RingHom.map_det, map_Ecl]
    simpa [T, U] using h1
  let L : Matrix (Fin 9) (Fin 9) ℤ := fun i j =>
    0x3b95d1b34fa4ef815c9835ee4cde055a2d2042839ca2884b449e3cabd69ab2442e911ceacf26e9d19a9b3db7b0d109cc25e358517268682b007be2eda273960934ba6c55be9209086878eacde5a2162a4af29f63fd9a93c878ff4071a8572789c4bb30e931bd0272eaeb67aa908bf2069cf81aa7c11506cbca0d7351b328634ec4b1b6b56ef63b0183312aa17df7aa872bc6083542f447793b076ec678f3ff2bcdd678e2a6384f7e08ef2b50b487438af77b69deece8fddccbba2d576c55d2ce39134f9baaad5aa18889aa3e9edc57b82ee95791a314f78bccacd543af65ce8c2e0d7b2d6caed21d25fb594c609e5c0e09ca7ab0c380c896eb2fe535b69fa5d368d12c59845133844f9552fd70dbce574dec2299f74082d1b0c8f242c5a5b0093e2253cadc8ad79b0ec9f6953a4c7da8c0b5e811a7e2b297978a163c58d8a4395fe6179fcc10462fc57e4fcca597e5201efa878b6733672587d04db542974fed384f313fdc41c1dc33332d934bd73d1a4ca5e108fa791768e4002ab8deb8e4ee8dff51e63afeb7985d31fe2339bad889c9c530b468951acee6a73813b33520b15985f754d04789b19edf7b4038151e63b9b24ad30b4cd829eec66f522b698fb78b6ea7b01cd92dd26e63820e8278947744447be805b9c992ee305c26c66a8fbceac509faac21f487479d5dcf8cb83c1079fbbdf76ba55148ffe94952e30bb8d7a26a05b6fce22127bb8c03258634bb674e8d9a1b58a524c68001 /
      10000000000000000 ^ (9 * i.1 + j.1) % 10000000000000000 - 1000000000000000
  have hLE : (L * Ecl (2 : ℤ) 3).det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular (by decide +kernel)]
    decide +kernel
  exact right_ne_zero_of_mul (Matrix.det_mul L _ ▸ hLE) (by simpa using h2)

section Trig

theorem half_angle {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) :
    (1 + th θ ^ 2) * Real.cos θ = 1 - th θ ^ 2 ∧
      (1 + th θ ^ 2) * Real.sin θ = 2 * th θ := by
  dsimp [th]
  obtain ⟨x, rfl⟩ : ∃ x, θ = 2 * x := ⟨θ / 2, by ring⟩
  rw [show 2 * x / 2 = x by ring] at hc ⊢
  have h1 := Real.sin_sq_add_cos_sq x
  rw [Real.cos_two_mul', Real.sin_two_mul, Real.tan_eq_sin_div_cos]
  exact ⟨by field_simp; linear_combination (Real.cos x ^ 2 - Real.sin x ^ 2) * h1,
    by field_simp; linear_combination Real.sin x * h1⟩

theorem trig_rot {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) (n : ℕ) :
    (1 + th θ ^ 2) ^ n * Real.cos (n * θ) = (rot (th θ) n).1 ∧
      (1 + th θ ^ 2) ^ n * Real.sin (n * θ) = (rot (th θ) n).2 := by
  obtain ⟨h1, h2⟩ := half_angle hc
  induction n with
  | zero => simp [rot]
  | succ n ih =>
    obtain ⟨i1, i2⟩ := ih
    rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add]
    simp only [rot]
    exact ⟨by linear_combination ((1 + th θ ^ 2) * Real.cos θ) * i1 +
        (rot (th θ) n).1 * h1 - ((1 + th θ ^ 2) * Real.sin θ) * i2 -
        (rot (th θ) n).2 * h2,
      by linear_combination ((1 + th θ ^ 2) * Real.cos θ) * i2 +
        (rot (th θ) n).2 * h1 + ((1 + th θ ^ 2) * Real.sin θ) * i1 +
        (rot (th θ) n).1 * h2⟩

theorem one_add_tan_sq_ne (θ : ℝ) : 1 + th θ ^ 2 ≠ 0 := by positivity

theorem cos_eq {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) (n : ℕ) :
    Real.cos (n * θ) = (rot (th θ) n).1 / (1 + th θ ^ 2) ^ n := by
  rw [eq_div_iff (pow_ne_zero n (one_add_tan_sq_ne θ)), mul_comm, (trig_rot hc n).1]

theorem sin_eq {θ : ℝ} (hc : Real.cos (θ / 2) ≠ 0) (n : ℕ) :
    Real.sin (n * θ) = (rot (th θ) n).2 / (1 + th θ ^ 2) ^ n := by
  rw [eq_div_iff (pow_ne_zero n (one_add_tan_sq_ne θ)), mul_comm, (trig_rot hc n).2]

end Trig

set_option maxHeartbeats 400000 in
theorem radian_configuration (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    Function.Injective (radianConfig θ) ∧ (∀ k, dist (radianConfig θ k) 0 = 1) ∧
      ¬ Ramsey (radianConfig θ) := by
  classical
  let a := radianConfig θ
  have hc_half : Real.cos (θ / 2) ≠ 0 := fun h => by
    apply ht; rw [Real.tan_eq_sin_div_cos, h, div_zero]; exact isAlgebraic_zero
  have tan_mem : th θ ∈ coordinateField a := by
    obtain ⟨h1, h2⟩ := half_angle hc_half
    have hne : 1 + Real.cos θ ≠ 0 := fun h => by nlinarith
    have hrec : th θ = Real.sin θ / (1 + Real.cos θ) := by
      rw [eq_div_iff hne]
      apply mul_left_cancel₀ (one_add_tan_sq_ne θ)
      linear_combination th θ * h1 - h2
    rw [hrec]
    let F := coordinateField a
    have hc (j : Fin 2) : a 1 j ∈ F :=
      IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self ((1 : Fin 9), j))
    have h0 := hc 0
    have h1' := hc 1
    simp only [a, radianConfig_zero, radianConfig_one, Fin.val_one, Nat.cast_one, one_mul] at h0 h1'
    exact F.div_mem h1' (F.add_mem F.one_mem h0)
  let tau : Coeff a := ⟨th θ, tan_mem⟩
  have hcf_eq : coordinateField a =
      IntermediateField.adjoin ℚ (Set.range (fun _ : Unit => th θ)) := by
    let E : IntermediateField ℚ ℝ :=
      IntermediateField.adjoin ℚ (Set.range (fun _ : Unit => th θ))
    let σ : E := ⟨th θ, IntermediateField.subset_adjoin ℚ _ ⟨(), rfl⟩⟩
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin_le_iff.mpr ?_)
    · rintro x ⟨⟨k, j⟩, rfl⟩
      have hm := map_rot (algebraMap E ℝ) σ k
      simp only [IntermediateField.algebraMap_apply] at hm
      fin_cases j
      · change a k 0 ∈ E
        rw [show a k 0 = (((rot σ k).1 / (1 + σ ^ 2) ^ (k : ℕ) : E) : ℝ) by
          simp [a, cos_eq hc_half, hm.1, σ]]
        exact Subtype.property _
      · change a k 1 ∈ E
        rw [show a k 1 = (((rot σ k).2 / (1 + σ ^ 2) ^ (k : ℕ) : E) : ℝ) by
          simp [a, sin_eq hc_half, hm.2, σ]]
        exact Subtype.property _
    · rintro x ⟨_, rfl⟩; exact tan_mem
  have tan_indep : AlgebraicIndependent ℚ (fun _ : Unit => th θ) :=
    algebraicIndependent_unique_type_iff.mpr ht
  let coefficientEquiv : Coeff a ≃ₐ[ℚ] Rat₁ :=
    (IntermediateField.equivOfEq hcf_eq).trans tan_indep.aevalEquivField.symm
  have coefficientEquiv_tau : coefficientEquiv tau = algebraMap Poly₁ Rat₁ (MvPolynomial.X ()) := by
    apply tan_indep.aevalEquivField.injective
    change tan_indep.aevalEquivField
        (tan_indep.aevalEquivField.symm ((IntermediateField.equivOfEq hcf_eq) tau)) = _
    rw [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    change th θ = (tan_indep.aevalEquivField (algebraMap Poly₁ Rat₁ (MvPolynomial.X ())) : ℝ)
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]; simp
  have hqv (k : Fin 9) (m : Fin 3) :
      (1 + tau ^ 2) ^ (k : ℕ) * augmented a k (finSuccEquiv 2 m) = qv tau k m := by
    apply Subtype.ext
    have hm := map_rot (algebraMap (Coeff a) ℝ) tau k
    simp only [IntermediateField.algebraMap_apply] at hm
    fin_cases m
    · simp [augmented, qv]
    · change ((1 + tau ^ 2) ^ (k : ℕ) * coordinate a k 0 : Coeff a) = ((rot tau k).1 : ℝ)
      push_cast; exact (trig_rot hc_half k).1.trans hm.1.symm
    · change ((1 + tau ^ 2) ^ (k : ℕ) * coordinate a k 1 : Coeff a) = ((rot tau k).2 : ℝ)
      push_cast; exact (trig_rot hc_half k).2.trans hm.2.symm
  have hmap_qv (g : Coeff a →ₐ[ℚ] JointField) (z : JointField) (hz : g tau = z) (k : Fin 9) (m : Fin 3) :
      qv z k m = (1 + z ^ 2) ^ (k : ℕ) * g (augmented a k (finSuccEquiv 2 m)) := by
    simpa [hz, ← hqv] using (map_qv (g : Coeff a →+* JointField) tau k m).symm
  let tensorMap : TensorRing a →ₐ[ℚ] JointField :=
    tensorEmbedding.comp (Algebra.TensorProduct.congr coefficientEquiv coefficientEquiv).toAlgHom
  let e : Fin 9 ≃ Option (Fin 2) × Option (Fin 2) :=
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin (3 * 3)).symm.trans
      (Equiv.prodCongr (finSuccEquiv 2) (finSuccEquiv 2))
  let M : Matrix (Fin 9) (Fin 9) JointField := fun k j =>
    tensorMap (augmented a k (e j).1 ⊗ₜ[ℚ] 1) * tensorMap (1 ⊗ₜ[ℚ] augmented a k (e j).2)
  have hEq : Ecl (incl T) (incl U) =
      Matrix.diagonal (fun k : Fin 9 => (1 + incl T ^ 2) ^ (k : ℕ) * (1 + incl U ^ 2) ^ (k : ℕ)) * M := by
    have h1 : (leftMap.comp coefficientEquiv.toAlgHom) tau = incl T := by simp [coefficientEquiv_tau, T]
    have h2 : (rightMap.comp coefficientEquiv.toAlgHom) tau = incl U := by simp [coefficientEquiv_tau, U]
    have hL (x : Coeff a) : tensorMap (x ⊗ₜ[ℚ] 1) = leftMap (coefficientEquiv x) := by
      simp [tensorMap, tensorEmbedding]
    have hR (x : Coeff a) : tensorMap (1 ⊗ₜ[ℚ] x) = rightMap (coefficientEquiv x) := by
      simp [tensorMap, tensorEmbedding]
    ext k j
    rw [Matrix.diagonal_mul]
    dsimp [Ecl, M]
    rw [hmap_qv _ _ h1 k (col j).1, hmap_qv _ _ h2 k (col j).2, hL, hR]
    change ((1 + incl T ^ 2) ^ (k : ℕ) * leftMap (coefficientEquiv (augmented a k (e j).1))) *
      ((1 + incl U ^ 2) ^ (k : ℕ) * rightMap (coefficientEquiv (augmented a k (e j).2))) = _
    ring
  have hinj : Function.Injective a := fun i j hij => by
    by_contra hne
    have h0 : M.det = 0 := Matrix.det_zero_of_row_eq hne (funext fun q => by
      have haug (α) : augmented a i α = augmented a j α := by
        cases α with
        | none => rfl
        | some m => exact Subtype.ext (congrArg (fun p : Space 2 => p m) hij)
      simp only [M, haug])
    exact det_Ecl_ne_zero (by rw [hEq, Matrix.det_mul, h0, mul_zero])
  refine ⟨hinj, fun k => by rw [EuclideanSpace.dist_eq]; simp [Fin.sum_univ_two, sq_abs], fun hR => ?_⟩
  have hspan : LinearMap.range
      (Fintype.linearCombination ℝ fun i => a i - a 0) = ⊤ := by
    let u := a 1 - a 0
    let v := a 2 - a 0
    let D := u 0 * v 1 - v 0 * u 1
    have hD : D ≠ 0 := by
      have ht0 : Real.tan (θ / 2) ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
      suffices D = 8 * th θ ^ 3 / (1 + th θ ^ 2) ^ 2 by
        rw [this]
        exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 ht0))
          (pow_ne_zero 2 (one_add_tan_sq_ne θ))
      simp only [D, u, v, a, PiLp.sub_apply, radianConfig_zero, radianConfig_one,
        cos_eq hc_half, sin_eq hc_half, Fin.val_zero, Fin.val_one, Fin.val_two, rot]
      field_simp; ring
    refine LinearMap.range_eq_top.mpr fun w => ⟨Pi.single 1 ((w 0 * v 1 - v 0 * w 1) / D) +
      Pi.single 2 ((u 0 * w 1 - w 0 * u 1) / D), ?_⟩
    rw [map_add, Fintype.linearCombination_apply_single, Fintype.linearCombination_apply_single]
    ext j
    fin_cases j <;> simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;>
      field_simp [hD] <;> dsimp [D, u, v] <;> ring
  have hreal : RealCriterion a := by
    by_contra h
    let arrMap : RealArray 2 →ₗ[ℚ] (Fin 9 → RealTensor) × Matrix (Fin 2) (Fin 2) ℝ :=
      (LinearMap.pi (arrayEvaluation a)).prod spatialMultiply
    let N := LinearMap.range arrMap
    have hq : N.mkQ (0, 1) ≠ 0 := fun hz => h <| by
      obtain ⟨P, hP⟩ := (Submodule.Quotient.mk_eq_zero N).mp hz
      exact ⟨P, fun i => congrFun (congrArg Prod.fst hP) i, congrArg Prod.snd hP⟩
    obtain ⟨f₀, hf₀⟩ := Module.Projective.exists_dual_eq_one ℚ hq
    let ℓ := (Algebra.linearMap ℚ ℝ).comp (f₀.comp N.mkQ)
    let f (i : Fin 9) (x : ℝ) : ℝ := ℓ (Pi.single i (x ⊗ₜ[ℚ] x), 0)
    let L : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℚ] ℝ := ℓ.comp (LinearMap.inr ℚ _ _)
    let gr (u : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun α β => u α * u β
    have heq (v : ℝ) (u : Fin 2 → ℝ) :
        (∑ i, f i (v + ∑ j, a i j * u j)) + L (gr u) = 0 := by
      let w : Option (Fin 2) → ℝ := fun α => α.elim v u
      let P : RealArray 2 := fun α β => w α ⊗ₜ[ℚ] w β
      have hp : ℓ (arrMap P) = 0 := by
        have : N.mkQ (arrMap P) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨P, rfl⟩
        simp [ℓ, this]
      have hdiag (i : Fin 9) : arrayEvaluation a i P =
          (v + ∑ j, a i j * u j) ⊗ₜ[ℚ] (v + ∑ j, a i j * u j) := by
        have he : v + ∑ j, a i j * u j = ∑ α, realAugmented a i α * w α := by
          simp [realAugmented, w, Fintype.sum_option]
        rw [he, TensorProduct.sum_tmul]
        simp only [TensorProduct.tmul_sum, arrayEvaluation, LinearMap.coe_mk, AddHom.coe_mk, P,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
      have hsp : spatialMultiply P = gr u := rfl
      have hsplit (x : Fin 9 → RealTensor) (M : Matrix (Fin 2) (Fin 2) ℝ) :
          ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + L M := by
        change ℓ (x, M) = (∑ i, ℓ (Pi.single i (x i), 0)) + ℓ (0, M)
        rw [← map_sum, ← map_add]
        congr 1; ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
      change ℓ (fun i => arrayEvaluation a i P, spatialMultiply P) = 0 at hp
      simp only [hdiag, hsp] at hp
      rwa [hsplit] at hp
    have hcancel (x : ℝ) : ∑ i, f i x = 0 := by
      simpa [show gr 0 = 0 by ext; simp [gr]] using heq x 0
    let K := 19
    let Colors := Fin 9 → ZMod K
    obtain ⟨D, _, hD'⟩ := hR (Fintype.card Colors) (by simp [Colors, K])
    let H (i : Fin 9) (z : Space D) : ℝ := ∑ j, f i (z j)
    let color (z : Space D) : Colors := fun i => (⌊(K : ℝ) / 2 * H i z⌋ : ZMod K)
    obtain ⟨b, hb, k, hk⟩ := hD' fun z => Fintype.equivFin Colors (color z)
    let A₀ := Fintype.linearCombination ℝ fun i => a i - a 0
    let B₀ := Fintype.linearCombination ℝ fun i => b i - b 0
    have hnorm (c : Fin 9 → ℝ) : ‖B₀ c‖ = ‖A₀ c‖ := by
      have hg (i j : Fin 9) : ⟪b i - b 0, b j - b 0⟫ = ⟪a i - a 0, a j - a 0⟫ := by
        simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
          sub_sub_sub_cancel_right, ← dist_eq_norm, a, hb _ _]
      have hc : ⟪B₀ c, B₀ c⟫ = ⟪A₀ c, A₀ c⟫ := by
        simp only [A₀, B₀, Fintype.linearCombination_apply, sum_inner, inner_sum,
          real_inner_smul_left, inner_smul_right, hg]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
      nlinarith [norm_nonneg (B₀ c), norm_nonneg (A₀ c)]
    obtain ⟨R, hR_inv⟩ := A₀.exists_rightInverse_of_surjective hspan
    have hR' (z : Space 2) : A₀ (R z) = z := LinearMap.congr_fun hR_inv z
    let Q : Space 2 →ₗᵢ[ℝ] Space D := ⟨B₀.comp R, fun z => by
      change ‖B₀ (R z)‖ = ‖z‖; rw [hnorm, hR']⟩
    let t := b 0 - Q (a 0)
    have hQ (i : Fin 9) : b i = t + Q (a i) := by
      have hfactor : Q (a i - a 0) = b i - b 0 := by
        have : B₀ (R (A₀ (Pi.single i 1)) - Pi.single i 1) = 0 := by
          rw [← norm_eq_zero, hnorm, map_sub, hR', sub_self, norm_zero]
        simpa [Q, A₀, B₀, sub_eq_zero] using this
      rw [map_sub, sub_eq_iff_eq_add] at hfactor
      rw [hfactor]; dsimp [t]; abel
    have hsum : ∑ i, H i (b i) = -1 := by
      let row (j : Fin D) (α : Fin 2) : ℝ := Q (EuclideanSpace.single α 1) j
      have hrows : (∑ j : Fin D, gr (row j)) = 1 := by
        ext α β
        have h := Q.inner_map_map (EuclideanSpace.single α 1) (EuclideanSpace.single β 1)
        rw [EuclideanSpace.inner_single_left] at h
        rw [Matrix.sum_apply]
        simpa only [gr, Matrix.one_apply, PiLp.inner_apply, RCLike.inner_apply,
          conj_trivial, map_one, one_mul, PiLp.single_apply, row, mul_comm (row _ β)] using h
      have heach (j : Fin D) : (∑ i, f i ((t + Q (a i)) j)) = -L (gr (row j)) := by
        refine eq_neg_of_add_eq_zero_left (Eq.trans ?_ (heq (t j) (row j)))
        congr 1; refine Finset.sum_congr rfl fun i _ => congrArg (f i) ?_
        have hx := congrArg (fun z : Space 2 => Q z j) ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr (a i))
        simpa only [PiLp.add_apply, map_sum, map_smul, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
          smul_eq_mul, row, add_right_inj] using congrArg (t j + ·) hx.symm
      have hL1 : L 1 = 1 := by
        change ((f₀ (N.mkQ (0, 1)) : ℚ) : ℝ) = 1; rw [hf₀]; norm_num
      simp only [H, hQ]
      rw [Finset.sum_comm]
      simp only [heach, Finset.sum_neg_distrib, ← map_sum, hrows, hL1]
    have hfl (g : Fin 9 → ℝ) : (∑ i, g i) - 9 < ((∑ i, ⌊g i⌋ : ℤ) : ℝ) ∧
        ((∑ i, ⌊g i⌋ : ℤ) : ℝ) ≤ ∑ i, g i := by
      have hlt := Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ _⟩
        fun i _ => Int.lt_floor_add_one (g i)
      have hle := Finset.sum_le_sum (s := Finset.univ) fun i _ => Int.floor_le (g i)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] at hlt
      exact ⟨by push_cast at hlt ⊢; linarith, by simpa only [Int.cast_sum] using hle⟩
    let x (i : Fin 9) : ℝ := (K : ℝ) / 2 * H i (b i)
    let y (i : Fin 9) : ℝ := (K : ℝ) / 2 * H i (b 0)
    have hx : ∑ i, x i = -(K : ℝ) / 2 := by simp [x, ← Finset.mul_sum, hsum]; ring
    have hy : ∑ i, y i = 0 := by
      simp only [y, ← Finset.mul_sum, H]
      rw [Finset.sum_comm]
      simp [hcancel]
    let A : ℤ := ∑ i, ⌊x i⌋
    let B : ℤ := ∑ i, ⌊y i⌋
    have hAB : (A : ZMod K) = (B : ZMod K) := by
      simp only [A, B, Int.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact congrFun ((Fintype.equivFin Colors).injective ((hk i).trans (hk 0).symm)) i
    have hdvd : (K : ℤ) ∣ B - A := (ZMod.intCast_eq_intCast_iff_dvd_sub A B K).mp hAB
    obtain ⟨hxlo, hxhi⟩ := hfl x
    obtain ⟨hylo, hyhi⟩ := hfl y
    change (∑ i, x i) - 9 < (A : ℝ) at hxlo
    change (A : ℝ) ≤ ∑ i, x i at hxhi
    change (∑ i, y i) - 9 < (B : ℝ) at hylo
    change (B : ℝ) ≤ ∑ i, y i at hyhi
    rw [hx] at hxlo hxhi
    rw [hy] at hylo hyhi
    have hK : (K : ℝ) = 19 := rfl
    have hpos : (0 : ℤ) < B - A := by exact_mod_cast (by linarith : (0 : ℝ) < (B : ℝ) - (A : ℝ))
    have hlt : B - A < (K : ℤ) := by exact_mod_cast (by linarith : (B : ℝ) - (A : ℝ) < (K : ℝ))
    exact (not_le_of_gt hlt) (Int.le_of_dvd hpos hdvd)
  let F := coordinateField a
  let b := Module.Free.chooseBasis F ℝ
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : ℝ) ≠ 0)
  let g (m : _) : F →ₗ[ℚ] ℝ →ₗ[ℚ] F ⊗[ℚ] F :=
    ((TensorProduct.mk ℚ F F).comp ((φ.restrictScalars ℚ).comp (LinearMap.mulRight ℚ (b m)))).flip
  let δ : ℝ ⊗[ℚ] ℝ →ₗ[ℚ] F ⊗[ℚ] F :=
    TensorProduct.lift (((Finsupp.lsum ℚ g).comp (b.repr.restrictScalars ℚ).toLinearMap).flip)
  have hsand (x y : F) (T : ℝ ⊗[ℚ] ℝ) :
      δ (((x : ℝ) ⊗ₜ[ℚ] (1 : ℝ)) * T * ((1 : ℝ) ⊗ₜ[ℚ] (y : ℝ))) =
        (x ⊗ₜ[ℚ] (1 : F)) * δ T * ((1 : F) ⊗ₜ[ℚ] y) := by
    induction T using TensorProduct.inductionOn with
    | add U V hU hV => simp [mul_add, add_mul, hU, hV]
    | tmul u v =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, δ,
        TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply]
      have hv : b.repr (v * (y : ℝ)) = y • b.repr v := by
        simpa [mul_comm, Algebra.smul_def] using b.repr.map_smul y v
      have hu (m) : φ ((x : ℝ) * u * b m) = x * φ (u * b m) := by
        simpa [mul_assoc, Algebra.smul_def] using φ.map_smul x (u * b m)
      simp only [hv, Finsupp.lsum_apply]
      rw [Finsupp.sum_smul_index' (by simp)]
      simp only [Finsupp.sum, LinearMap.sum_apply, g, LinearMap.flip_apply, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, LinearMap.mulRight_apply, TensorProduct.mk_apply, hu,
        Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        smul_eq_mul, mul_comm y]
  have hmul (T : ℝ ⊗[ℚ] ℝ) :
      Algebra.TensorProduct.lmul' ℚ (δ T) = φ (Algebra.TensorProduct.lmul' ℚ T) := by
    induction T using TensorProduct.inductionOn with
    | add U V hU hV => simp [hU, hV]
    | tmul u v =>
      have hv := b.linearCombination_repr v
      simp only [Finsupp.linearCombination_apply, Finsupp.sum] at hv
      conv_rhs => rw [Algebra.TensorProduct.lmul'_apply_tmul, ← hv, Finset.mul_sum, map_sum]
      simp only [δ, TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, LinearEquiv.restrictScalars_apply, Finsupp.lsum_apply,
        Finsupp.sum, LinearMap.sum_apply, map_sum, g, LinearMap.restrictScalars_apply,
        LinearMap.mulRight_apply, TensorProduct.mk_apply, Algebra.TensorProduct.lmul'_apply_tmul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_comm _ (b.repr v m), ← smul_eq_mul, ← φ.map_smul]
      simp [Algebra.smul_def, mul_left_comm]
  obtain ⟨P₀, he, hm⟩ := hreal
  let P (α β : Option (Fin 2)) := δ (P₀ α β)
  have hP (i : Fin 9) : ∑ α, ∑ β,
      (augmented a i α ⊗ₜ[ℚ] (1 : F)) * P α β * ((1 : F) ⊗ₜ[ℚ] augmented a i β) = 0 := by
    have haug (α : Option (Fin 2)) : ((augmented a i α : F) : ℝ) = realAugmented a i α := by
      cases α <;> rfl
    simpa only [arrayEvaluation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero, ← haug,
      hsand, P] using congrArg δ (he i)
  have hv : (Ecl (incl T) (incl U)).mulVec (fun j => tensorMap (P (e j).1 (e j).2)) = 0 := by
    have hvM : M.mulVec (fun j => tensorMap (P (e j).1 (e j).2)) = 0 := by
      ext k
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, M]
      rw [e.sum_comp (fun q : Option (Fin 2) × Option (Fin 2) =>
        tensorMap (augmented a k q.1 ⊗ₜ[ℚ] 1) *
          tensorMap (1 ⊗ₜ[ℚ] augmented a k q.2) *
            tensorMap (P q.1 q.2)),
        Fintype.sum_prod_type, ← map_zero tensorMap, ← hP k]
      simp only [map_sum, map_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_right_comm _ _ _
    rw [hEq, ← Matrix.mulVec_mulVec, hvM, Matrix.mulVec_zero]
  have hv0 := (Matrix.mulVec_injective_iff_isUnit.mpr
    ((Ecl (incl T) (incl U)).isUnit_iff_isUnit_det.mpr det_Ecl_ne_zero.isUnit))
    (hv.trans (Matrix.mulVec_zero _).symm)
  have htf : Function.Injective tensorEmbedding := by
    let locL : Poly₁ ⊗[ℚ] Poly₁ →ₐ[ℚ] Rat₁ ⊗[ℚ] Poly₁ :=
      Algebra.TensorProduct.map polyToRat (AlgHom.id ℚ _)
    let locR : Rat₁ ⊗[ℚ] Poly₁ →ₐ[ℚ] Rat₁ ⊗[ℚ] Rat₁ :=
      Algebra.TensorProduct.map (AlgHom.id ℚ _) polyToRat
    let half := tensorEmbedding.comp locR
    let polyEmb := jointToField.comp (MvPolynomial.tensorEquivSum ℚ Unit Unit ℚ).toAlgHom
    have hcomp : half.comp locL = polyEmb := by
      apply Algebra.TensorProduct.ext <;> ext i <;>
        simp [half, locL, locR, polyEmb, polyToRat, jointToField, tensorEmbedding, IsScalarTower.toAlgHom_apply]
    have hhalf : Function.Injective half := by
      let : Algebra (Poly₁ ⊗[ℚ] Poly₁) (Rat₁ ⊗[ℚ] Poly₁) := locL.toAlgebra
      let := IsScalarTower.of_algebraMap_eq
        (R := Poly₁) (S := Poly₁ ⊗[ℚ] Poly₁) (A := Rat₁ ⊗[ℚ] Poly₁) fun p => by
          change algebraMap Poly₁ Rat₁ p ⊗ₜ[ℚ] (1 : Poly₁) = locL (p ⊗ₜ[ℚ] 1)
          simp [locL, polyToRat, IsScalarTower.toAlgHom_apply]
      let : IsLocalization
          (Algebra.algebraMapSubmonoid (Poly₁ ⊗[ℚ] Poly₁) (nonZeroDivisors Poly₁))
          (Rat₁ ⊗[ℚ] Poly₁) :=
        IsLocalization.tensorProduct_tensorProduct ℚ Poly₁ (nonZeroDivisors Poly₁) Rat₁
          (RingHom.ext fun p => by
            change locL (1 ⊗ₜ[ℚ] p) = 1 ⊗ₜ[ℚ] p
            simp [locL, polyToRat, IsScalarTower.toAlgHom_apply])
      refine IsLocalization.injective_of_map_algebraMap_zero
        (M := Algebra.algebraMapSubmonoid (Poly₁ ⊗[ℚ] Poly₁) (nonZeroDivisors Poly₁)) _
        half.toRingHom fun x hx => ?_
      have h0 : polyEmb x = 0 := (AlgHom.congr_fun hcomp x).symm.trans hx
      have hx0 : x = 0 := ((IsFractionRing.injective Poly JointField).comp
        (MvPolynomial.tensorEquivSum ℚ Unit Unit ℚ).injective) (h0.trans (map_zero polyEmb).symm)
      simp [hx0]
    let : Algebra (Rat₁ ⊗[ℚ] Poly₁) (Rat₁ ⊗[ℚ] Rat₁) := locR.toAlgebra
    let := IsScalarTower.of_algebraMap_eq
      (R := Rat₁) (S := Rat₁ ⊗[ℚ] Poly₁) (A := Rat₁ ⊗[ℚ] Rat₁) fun x => by
        change x ⊗ₜ[ℚ] (1 : Rat₁) = locR (x ⊗ₜ[ℚ] 1)
        simp [locR, polyToRat, IsScalarTower.toAlgHom_apply]
    let : IsLocalization
        ((nonZeroDivisors Poly₁).map (Algebra.TensorProduct.includeRight (R := ℚ) (A := Rat₁)))
        (Rat₁ ⊗[ℚ] Rat₁) :=
      IsLocalization.tensorProduct_tensorProduct_right ℚ Rat₁ (nonZeroDivisors Poly₁) Rat₁
        (RingHom.ext fun p => by
          change locR (1 ⊗ₜ[ℚ] p) = 1 ⊗ₜ[ℚ] algebraMap Poly₁ Rat₁ p
          simp [locR, polyToRat, IsScalarTower.toAlgHom_apply])
    refine IsLocalization.injective_of_map_algebraMap_zero
      (M := (nonZeroDivisors Poly₁).map (Algebra.TensorProduct.includeRight (R := ℚ) (A := Rat₁))) _
      tensorEmbedding.toRingHom fun x hx => ?_
    have hx0 : x = 0 := hhalf ((hx : half x = 0).trans (map_zero _).symm)
    simp [hx0]
  have htf' : Function.Injective tensorMap :=
    htf.comp (Algebra.TensorProduct.congr coefficientEquiv coefficientEquiv).injective
  have h0 : P (some 0) (some 0) = 0 := htf' (by
    simpa only [Pi.zero_apply, map_zero, Equiv.apply_symm_apply] using
      congrFun hv0 (e.symm (some 0, some 0)))
  have hab : Algebra.TensorProduct.lmul' ℚ (P₀ (some 0) (some 0)) = 1 :=
    congrFun (congrFun hm 0) 0
  have hbad : Algebra.TensorProduct.lmul' ℚ (P (some 0) (some 0)) = 1 := by
    dsimp [P]; rw [hmul, hab, hφ]
  rw [h0, map_zero] at hbad
  exact zero_ne_one hbad

theorem radian_not_ramsey (θ : ℝ) (ht : Transcendental ℚ (Real.tan (θ / 2))) :
    ¬ Ramsey (radianConfig θ) :=
  (radian_configuration θ ht).2.2

theorem algebraic_of_tan {θ : ℝ} (h : IsAlgebraic ℚ (th θ)) :
    IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  let A := algebraicClosure ℚ ℝ
  simp only [← mem_algebraicClosure_iff] at h ⊢
  by_cases hc : Real.cos (θ / 2) = 0
  · rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul, Real.sin_two_mul, hc]
    simp
  · have h1 := cos_eq hc 1
    have h2 := sin_eq hc 1
    simp only [Nat.cast_one, one_mul, pow_one, rot, mul_one, mul_zero, sub_zero, add_zero] at h1 h2
    rw [h1, h2]
    have hd := A.add_mem A.one_mem (A.pow_mem h 2)
    exact ⟨A.div_mem (A.sub_mem A.one_mem (A.pow_mem h 2)) hd,
      A.div_mem (A.mul_mem (A.natCast_mem 2) h) hd⟩

theorem radian_ramsey_iff (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.cos θ) ∧ IsAlgebraic ℚ (Real.sin θ) := by
  refine ⟨fun hR => not_not.mp fun hna => radian_not_ramsey θ (hna ∘ algebraic_of_tan) hR, ?_⟩
  rintro ⟨hc, hs⟩
  refine ramsey_of_algebraic (radianConfig θ) (by norm_num) (by norm_num) hinj (fun k => ?_)
    (fun k => Subtype.ext (by simp [Fin.sum_univ_two, coordinate, ← sq]))
  let A := algebraicClosure ℚ ℝ
  simp only [← mem_algebraicClosure_iff] at hc hs ⊢
  have hk : Real.cos (k * θ) ∈ A ∧ Real.sin (k * θ) ∈ A := by
    induction (k : ℕ) with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, Real.cos_add, Real.sin_add]
      exact ⟨A.sub_mem (A.mul_mem ih.1 hc) (A.mul_mem ih.2 hs),
        A.add_mem (A.mul_mem ih.2 hc) (A.mul_mem ih.1 hs)⟩
  intro j; fin_cases j <;> [exact hk.1; exact hk.2]

theorem radian_ramsey_iff_tan (θ : ℝ) (hinj : Function.Injective (radianConfig θ)) :
    Ramsey (radianConfig θ) ↔ IsAlgebraic ℚ (Real.tan (θ / 2)) :=
  ⟨fun hR => not_not.mp fun hna => radian_not_ramsey θ hna hR,
    fun h => (radian_ramsey_iff θ hinj).2 (algebraic_of_tan h)⟩

end
end OAI.EuclideanRamsey.Radian
