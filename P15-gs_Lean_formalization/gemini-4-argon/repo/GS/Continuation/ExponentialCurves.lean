module

public import GS.Core
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix Filter
open scoped BigOperators Topology

namespace GS.Extensions

variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

def lift (L R X : Mat n) : Mat n := L * X * R
def pull (L R Z : Mat n) : Mat n := Lᵀ * Z * Rᵀ

theorem pull_lift (L R Y : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    pull L R (lift L R Y) = Y := by
  calc pull L R (lift L R Y) = (Lᵀ * L) * Y * (R * Rᵀ) := by simp only [pull, lift, Matrix.mul_assoc]
    _ = Y := by rw [hL.1, hR.2]; simp

theorem lift_injective (L R : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    Function.Injective (lift L R) := fun _ _ h => by
  simpa only [pull_lift L R _ hL hR] using congrArg (pull L R) h

theorem lift_frobInner (L R X Y : Mat n) (hL : Orthogonal L) (hR : Orthogonal R) :
    frobInner (lift L R X) (lift L R Y) = frobInner X Y := by
  unfold lift
  rw [frobInner_right_orthogonal R hR, frobInner_left_orthogonal L hL]

theorem frobInner_mul_right (A B C : Mat n) :
    frobInner (A * B) C = frobInner A (C * Bᵀ) := by
  calc frobInner (A * B) C = frobInner (A * B)ᵀ Cᵀ := (frobInner_transpose _ _).symm
    _ = frobInner Aᵀ (B * Cᵀ) := by rw [Matrix.transpose_mul, frobInner_mul_left, Matrix.transpose_transpose]
    _ = frobInner A (C * Bᵀ) := by simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using frobInner_transpose A (C * Bᵀ)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_matrix_mul {A B : ℝ → Mat n} {A' B' : Mat n} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  have hs := HasDerivAt.sum (u := Finset.univ) fun k _ =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) k).mul (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB k) j)
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Finset.sum_apply, Finset.sum_fn, Pi.mul_apply] using hs

def TwoFactorDirection (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ X : Mat n) : Prop :=
  ∃ C Ω : Mat n, Supported block₂ C ∧ IsSkew C ∧
    Supported block₁ Ω ∧ IsSkew Ω ∧ X = tangentParam B₂ P B₁ C Ω

theorem isSkew_add {C K : Mat n} (hC : IsSkew C) (hK : IsSkew K) :
    IsSkew (C + K) := by
  unfold IsSkew at *; rw [Matrix.transpose_add, hC, hK]; abel

def OffDiagonalDisjoint (a b : Fin n → ℕ) : Prop :=
  ∀ i j, a i = a j → b i = b j → i = j

theorem OffDiagonalDisjoint.symm {a b : Fin n → ℕ}
    (h : OffDiagonalDisjoint a b) : OffDiagonalDisjoint b a :=
  fun i j hb ha => h i j ha hb

theorem frobInner_disjoint_supported_skew {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (A K : Mat n)
    (hA : Supported a A) (hK : Supported b K) (hk : IsSkew K) :
    frobInner A K = 0 := by
  apply frobInner_eq_zero_of_disjoint
  intro i j
  by_cases ha : a i = a j
  · by_cases hb : b i = b j
    · cases hab i j ha hb
      exact Or.inr (isSkew_diagonal_zero hk i)
    · exact Or.inr (hK i j hb)
  · exact Or.inl (hA i j ha)

def accelerationCore (C K : Mat n) : Mat n := C * C + (2 : ℝ) • (C * K) + K * K

theorem lifted_acceleration_normal {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (L R C K D E : Mat n)
    (hL : Orthogonal L) (hR : Orthogonal R)
    (hCa : Supported a C) (hKb : Supported b K)
    (hDa : Supported a D) (hEb : Supported b E)
    (hC : IsSkew C) (hK : IsSkew K) (hD : IsSkew D) (hE : IsSkew E) :
    frobInner (lift L R (accelerationCore C K)) (lift L R (D + E)) = 0 := by
  rw [lift_frobInner L R _ _ hL hR]
  have hDE : IsSkew (D + E) := isSkew_add hD hE
  have h_sq (M : Mat n) (hM : IsSkew M) : frobInner (M * M) (D + E) = 0 := by
    have hS : (M * M)ᵀ = M * M := by
      change Mᵀ = -M at hM
      simp only [Matrix.transpose_mul, hM, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    have ht := frobInner_transpose (M * M) (D + E)
    have he : frobInner (M * M) (-(D + E)) = -frobInner (M * M) (D + E) := by
      rw [frobInner_comm (M * M) (-(D + E)), frobInner_neg_left, frobInner_comm (D + E) (M * M)]
    rw [hS, hDE, he] at ht; linarith
  have h_mix : frobInner (C * K) (D + E) = 0 := by
    rw [frobInner_add_right, frobInner_mul_left, frobInner_comm K _,
      frobInner_disjoint_supported_skew hab (Cᵀ * D) K (hCa.transpose.mul hDa) hKb hK,
      frobInner_mul_right, frobInner_comm C _,
      frobInner_disjoint_supported_skew hab.symm (E * Kᵀ) C (hEb.mul hKb.transpose) hCa hC, add_zero]
  unfold accelerationCore
  rw [frobInner_add_left, frobInner_add_left, frobInner_smul_left, h_sq C hC, h_sq K hK, h_mix]
  ring

theorem product_curve_velocity (L R : ℝ → Mat n) (C K : Mat n) (t : ℝ)
    (hL : HasDerivAt L (L t * C) t) (hR : HasDerivAt R (K * R t) t) :
    HasDerivAt (fun s => L s * R s) (lift (L t) (R t) (C + K)) t := by
  simpa only [lift, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using
    hasDerivAt_matrix_mul hL hR

theorem product_curve_acceleration (L R : ℝ → Mat n) (C K : Mat n) (t : ℝ)
    (hL : HasDerivAt L (L t * C) t) (hR : HasDerivAt R (K * R t) t) :
    HasDerivAt (fun s => lift (L s) (R s) (C + K))
      (lift (L t) (R t) (accelerationCore C K)) t := by
  have h := hasDerivAt_matrix_mul (hasDerivAt_matrix_mul hL (hasDerivAt_const t (C + K))) hR
  have he : lift (L t) (R t) (accelerationCore C K) =
      (L t * C * (C + K) + L t * 0) * R t + L t * (C + K) * (K * R t) := by
    simp only [lift, accelerationCore, Matrix.mul_zero, add_zero,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  rwa [he]

theorem continuous_frobSq : Continuous (@frobSq ι κ _ _) := by
  unfold frobSq frobInner; fun_prop

theorem abs_entry_le_of_frobSq_le {A : Matrix ι κ ℝ} {η : ℝ}
    (h : frobSq A ≤ η ^ 2) (i : ι) (j : κ) : |A i j| ≤ |η| := by
  have hs : A i j ^ 2 ≤ η ^ 2 := by
    refine le_trans ?_ h
    classical
    have h₁ : A i j * A i j ≤ ∑ l, A i l * A i l :=
      Finset.single_le_sum (fun l _ => mul_self_nonneg (A i l)) (Finset.mem_univ j)
    have h₂ : (∑ l, A i l * A i l) ≤ ∑ r, ∑ l, A r l * A r l :=
      Finset.single_le_sum (fun r _ => Finset.sum_nonneg fun l _ => mul_self_nonneg (A r l)) (Finset.mem_univ i)
    simpa only [frobSq, frobInner, pow_two] using h₁.trans h₂
  nlinarith [sq_abs (A i j), sq_abs η, abs_nonneg (A i j), abs_nonneg η]

theorem isClosed_isSkew (n : ℕ) : IsClosed {A : Mat n | IsSkew A} :=
  isClosed_eq (by fun_prop) (by fun_prop)

theorem isCompact_originalK (q : ℕ) (η : ℝ) : IsCompact (originalK q η) := by
  have h_closed : IsClosed (originalK q η) := by
    have hell : IsClosed {p : OriginalParameters q | ∀ i, |p.1 i| ≤ η} := by
      simp only [Set.ofPred_forall]; exact isClosed_iInter fun _ => isClosed_le (by fun_prop) continuous_const
    have hr : IsClosed {p : OriginalParameters q | ∀ j, |p.2.1 j| ≤ η} := by
      simp only [Set.ofPred_forall]; exact isClosed_iInter fun _ => isClosed_le (by fun_prop) continuous_const
    have hr₀ : IsClosed {p : OriginalParameters q | ∀ j : Fin q, j.val = 0 → p.2.1 j = 0} := by
      simp only [Set.ofPred_forall]; exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const
    have hc : IsClosed {p : OriginalParameters q | IsSkew p.2.2.1} := (isClosed_isSkew q).preimage (by fun_prop)
    have hz : IsClosed {p : OriginalParameters q | IsSkew p.2.2.2.1} := (isClosed_isSkew q).preimage (by fun_prop)
    have hcn : IsClosed {p : OriginalParameters q | frobSq p.2.2.1 ≤ η ^ 2} :=
      isClosed_le (continuous_frobSq.comp (by fun_prop)) continuous_const
    have hzn : IsClosed {p : OriginalParameters q | frobSq p.2.2.2.1 ≤ η ^ 2} :=
      isClosed_le (continuous_frobSq.comp (by fun_prop)) continuous_const
    have hu : IsClosed {p : OriginalParameters q | OnCircle p.2.2.2.2} := by
      unfold OnCircle; exact isClosed_eq (by fun_prop) continuous_const
    exact hell.inter (hr.inter (hr₀.inter (hc.inter (hz.inter (hcn.inter (hzn.inter hu))))))
  let : PartialOrder (Mat q) := inferInstanceAs (PartialOrder (Fin q → Fin q → ℝ))
  let : CompactIccSpace (Mat q) := inferInstanceAs (CompactIccSpace (Fin q → Fin q → ℝ))
  let ρ : ℝ := |η| + 1
  let lo : OriginalParameters q := (fun _ => -ρ, fun _ => -ρ, fun _ _ => -ρ, fun _ _ => -ρ, fun _ => -ρ)
  let hi : OriginalParameters q := (fun _ => ρ, fun _ => ρ, fun _ _ => ρ, fun _ _ => ρ, fun _ => ρ)
  refine (isCompact_Icc (a := lo) (b := hi)).of_isClosed_subset h_closed ?_
  rintro ⟨ell, r, c, z, u⟩ ⟨hell, hr, _, _, _, hcn, hzn, hu⟩
  have hη : η ≤ ρ := by dsimp [ρ]; linarith [le_abs_self η]
  have habsη : |η| ≤ ρ := by dsimp [ρ]; linarith
  have hone : (1 : ℝ) ≤ ρ := by dsimp [ρ]; linarith [abs_nonneg η]
  have he (i) := abs_le.mp ((hell i).trans hη)
  have hr' (i) := abs_le.mp ((hr i).trans hη)
  have hc' (i j) := abs_le.mp ((abs_entry_le_of_frobSq_le hcn i j).trans habsη)
  have hz' (i j) := abs_le.mp ((abs_entry_le_of_frobSq_le hzn i j).trans habsη)
  have hu' (i : Fin 2) : -ρ ≤ u i ∧ u i ≤ ρ := by
    apply abs_le.mp
    refine le_trans ?_ hone
    have heq : u 0 ^ 2 + u 1 ^ 2 = 1 := hu
    have hs : u i ^ 2 ≤ 1 := by
      fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one] <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    nlinarith [sq_abs (u i), abs_nonneg (u i)]
  exact ⟨⟨fun i => (he i).1, fun i => (hr' i).1, fun i j => (hc' i j).1, fun i j => (hz' i j).1, fun i => (hu' i).1⟩,
    ⟨fun i => (he i).2, fun i => (hr' i).2, fun i j => (hc' i j).2, fun i j => (hz' i j).2, fun i => (hu' i).2⟩⟩

theorem rotation_zero : rotation 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotation]

theorem rotation_add (s t : ℝ) : rotation (s + t) = rotation s * rotation t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem matrixExp_zero (n : ℕ) : matrixExp (0 : Mat n) = 1 := by
  rw [matrixExp_eq_exp]; simp

theorem originalPsi_zero {q : ℕ} (Q₀ : Mat q) : originalPsi Q₀ 0 = Q₀ := by
  simp [originalPsi, matrixExp_zero]

theorem originalF_eq_of_originalG_eq {q : ℕ} (Q₀ : Mat q)
    (ell r ell' r' : Fin q → ℝ) (c z c' w : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v)
    (h : originalG (ell, r, c, z, u) = originalG (ell', r', c', w, v)) :
    originalF Q₀ (ell, r, c, z, u) = originalF Q₀ (ell', r', c', w, v) := by
  obtain ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
    (originalG_fibres ell r ell' r' c z c' w u v hu hv).mp h
  · simp only [originalF, add_zero, sub_zero, middleBlock_equal]
  · rfl
  · simp only [originalF, sub_eq_add_neg, neg_neg, middleBlock_swap]

def circleBase : CircleVector := ![1, 0]

theorem circleBase_mem : OnCircle circleBase := by norm_num [circleBase, OnCircle]

def originalBaseParameters (q : ℕ) : OriginalParameters q := (0, 0, 0, 0, circleBase)

theorem originalBaseParameters_mem (q : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    originalBaseParameters q ∈ originalK q η :=
  ⟨fun _ => by simpa [originalBaseParameters] using hη,
   fun _ => by simpa [originalBaseParameters] using hη,
   fun _ _ => rfl,
   by simp [IsSkew],
   by simp [IsSkew],
   by simpa [originalBaseParameters, frobSq, frobInner] using sq_nonneg η,
   by simpa [originalBaseParameters, frobSq, frobInner] using sq_nonneg η,
   circleBase_mem⟩

theorem originalF_basePoint {q : ℕ} (Q₀ : Mat q) :
    originalF Q₀ (originalBaseParameters q) = basePoint Q₀ := by
  ext i j
  simp [originalF, originalBaseParameters, originalPsi_zero, rotation_zero,
    middleBlock_equal, basePoint, finProdFinEquiv]
  exact Or.inl rfl

theorem originalG_basePoint (q : ℕ) :
    originalG (originalBaseParameters q) = (0, 0, 0, 0) := by
  simp only [originalG, originalBaseParameters, Prod.mk.injEq, true_and]
  ext i j; simp [GS.outer]

end GS.Extensions

namespace GS.Continuation
open GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem compact_full_fibre_neighbourhood
    {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
    [T2Space K] [T2Space X] (f : K → X) (hf : Continuous f)
    (s : Set K) (hs : IsCompact s) (U : Set K) (hU : IsOpen U) (x : X)
    (hfull : ∀ k ∈ s, f k = x → k ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ∈ f '' s → y ∈ f '' (s ∩ U) := by
  have hc : IsCompact (s \ U) :=
    hs.of_isClosed_subset (hs.isClosed.inter hU.isClosed_compl) fun _ h => h.1
  refine ⟨(f '' (s \ U))ᶜ, (hc.image hf).isClosed.isOpen_compl,
    fun ⟨k, hk, he⟩ => hk.2 (hfull k hk.1 he),
    fun _ hy ⟨k, hk, he⟩ => ⟨k, ⟨hk, by by_contra hn; exact hy ⟨k, ⟨hk, hn⟩, he⟩⟩, he⟩⟩

theorem supported_pow {block : Fin n → ℕ} {A : Mat n}
    (hA : Supported block A) (k : ℕ) : Supported block (A ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using Supported.one (block := block)
  | succ k ih => simpa only [pow_succ] using ih.mul hA

theorem supported_sum {α : Type*} (s : Finset α) (F : α → Mat n)
    {block : Fin n → ℕ} (hF : ∀ a ∈ s, Supported block (F a)) :
    Supported block (∑ a ∈ s, F a) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty => intro _; simp [Supported.zero]
  | @insert a s ha ih =>
    intro hF; rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

theorem supported_matrixExp {block : Fin n → ℕ} {A : Mat n}
    (hA : Supported block A) : Supported block (matrixExp A) := by
  have hc : IsClosed {A : Mat n | Supported block A} := by
    simp only [Supported, Set.ofPred_forall]
    exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) continuous_const
  exact hc.mem_of_tendsto (matrixExp_hasSum A) (Filter.Eventually.of_forall fun s =>
    supported_sum s _ fun k _ => Supported.smul _ (supported_pow hA k))

theorem matrixExp_transpose (A : Mat n) : matrixExp (Aᵀ) = (matrixExp A)ᵀ := by
  simpa only [matrixExp_eq_exp] using Matrix.exp_transpose A

theorem matrixExp_add_of_commute (A B : Mat n) (h : Commute A B) :
    matrixExp (A + B) = matrixExp A * matrixExp B := by
  let : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  let : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℚ (Mat n) := Matrix.linftyOpNormedAlgebra
  simpa only [matrixExp_eq_exp] using NormedSpace.exp_add_of_commute h

theorem matrixExp_neg_mul (A : Mat n) : matrixExp (-A) * matrixExp A = 1 := by
  have hc : Commute (-A) A := by change (-A) * A = A * (-A); simp only [Matrix.neg_mul, Matrix.mul_neg]
  simpa only [neg_add_cancel, matrixExp_zero] using (matrixExp_add_of_commute (-A) A hc).symm

theorem matrixExp_mul_neg (A : Mat n) : matrixExp A * matrixExp (-A) = 1 := by
  simpa only [neg_neg] using matrixExp_neg_mul (-A)

theorem matrixExp_orthogonal {A : Mat n} (hA : IsSkew A) :
    Orthogonal (matrixExp A) := by
  apply Orthogonal.of_transpose_mul
  rw [← matrixExp_transpose, hA]
  exact matrixExp_neg_mul A

theorem isSkew_smul (t : ℝ) {A : Mat n} (hA : IsSkew A) : IsSkew (t • A) := by
  change (t • A)ᵀ = -(t • A); rw [Matrix.transpose_smul, hA, smul_neg]

def expLine (C : Mat n) (t : ℝ) : Mat n := matrixExp (t • C)

theorem expLine_supported {block : Fin n → ℕ} {C : Mat n}
    (hC : Supported block C) (t : ℝ) : Supported block (expLine C t) :=
  supported_matrixExp (Supported.smul t hC)

theorem expLine_orthogonal {C : Mat n} (hC : IsSkew C) (t : ℝ) :
    Orthogonal (expLine C t) := matrixExp_orthogonal (isSkew_smul t hC)

theorem hasDerivAt_expLine (C : Mat n) (t : ℝ) :
    HasDerivAt (expLine C) (expLine C t * C) t := by
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  let : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  let : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  let ev : Mat n →L[ℝ] ℝ := ⟨⟨⟨fun A => A i j, fun _ _ => rfl⟩, fun _ _ => rfl⟩, by fun_prop⟩
  simpa only [expLine, matrixExp_eq_exp, ev, Function.comp_def,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using
    ev.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) C t)

theorem hasDerivAt_expLine_left (C : Mat n) (t : ℝ) :
    HasDerivAt (expLine C) (C * expLine C t) t := by
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  let : SeminormedRing (Mat n) := Matrix.linftyOpSemiNormedRing
  let : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  let ev : Mat n →L[ℝ] ℝ := ⟨⟨⟨fun A => A i j, fun _ _ => rfl⟩, fun _ _ => rfl⟩, by fun_prop⟩
  simpa only [expLine, matrixExp_eq_exp, ev, Function.comp_def,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using
    ev.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' (𝕂 := ℝ) C t)

def gsExpLeft (B₂ C : Mat n) (t : ℝ) : Mat n := B₂ * expLine C t
def gsExpRight (B₁ Ω : Mat n) (t : ℝ) : Mat n := expLine Ω t * B₁

def gsExpCurve (B₂ P B₁ C Ω : Mat n) (t : ℝ) : Mat n :=
  product2 (gsExpLeft B₂ C t) P (gsExpRight B₁ Ω t)

def gsExpVelocity (B₂ P B₁ C Ω : Mat n) (t : ℝ) : Mat n :=
  lift (gsExpLeft B₂ C t) (P * gsExpRight B₁ Ω t) (C + P * Ω * Pᵀ)

def gsExpAcceleration (B₂ P B₁ C Ω : Mat n) (t : ℝ) : Mat n :=
  lift (gsExpLeft B₂ C t) (P * gsExpRight B₁ Ω t)
    (accelerationCore C (P * Ω * Pᵀ))

theorem gsExpLeft_supported {block : Fin n → ℕ} (B₂ C : Mat n)
    (hB₂ : Supported block B₂) (hC : Supported block C) (t : ℝ) :
    Supported block (gsExpLeft B₂ C t) := hB₂.mul (expLine_supported hC t)

theorem gsExpRight_supported {block : Fin n → ℕ} (B₁ Ω : Mat n)
    (hB₁ : Supported block B₁) (hΩ : Supported block Ω) (t : ℝ) :
    Supported block (gsExpRight B₁ Ω t) := (expLine_supported hΩ t).mul hB₁

theorem gsExpLeft_orthogonal (B₂ C : Mat n) (hB₂ : Orthogonal B₂)
    (hC : IsSkew C) (t : ℝ) : Orthogonal (gsExpLeft B₂ C t) :=
    hB₂.mul (expLine_orthogonal hC t)

theorem gsExpRight_orthogonal (B₁ Ω : Mat n) (hB₁ : Orthogonal B₁)
    (hΩ : IsSkew Ω) (t : ℝ) : Orthogonal (gsExpRight B₁ Ω t) :=
  (expLine_orthogonal hΩ t).mul hB₁

theorem gsExpLeft_hasDerivAt (B₂ C : Mat n) (t : ℝ) :
    HasDerivAt (gsExpLeft B₂ C) (gsExpLeft B₂ C t * C) t := by
  unfold gsExpLeft
  simpa only [Matrix.zero_mul, zero_add, Matrix.mul_assoc] using
    hasDerivAt_matrix_mul (hasDerivAt_const t B₂) (hasDerivAt_expLine C t)

theorem gsExpRight_hasDerivAt (B₁ Ω : Mat n) (t : ℝ) :
    HasDerivAt (gsExpRight B₁ Ω) (Ω * gsExpRight B₁ Ω t) t := by
  unfold gsExpRight
  simpa only [Matrix.mul_zero, add_zero, Matrix.mul_assoc] using
    hasDerivAt_matrix_mul (hasDerivAt_expLine_left Ω t) (hasDerivAt_const t B₁)

theorem gsExpCarrier_hasDerivAt (P B₁ Ω : Mat n) (hP : Orthogonal P) (t : ℝ) :
    HasDerivAt (fun s : ℝ => P * gsExpRight B₁ Ω s)
      ((P * Ω * Pᵀ) * (P * gsExpRight B₁ Ω t)) t := by
  have he : (P * Ω * Pᵀ) * (P * gsExpRight B₁ Ω t) = P * (Ω * gsExpRight B₁ Ω t) := by
    calc _ = P * Ω * (Pᵀ * P) * gsExpRight B₁ Ω t := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP.1]; simp [Matrix.mul_assoc]
  rw [he]
  simpa only [Matrix.zero_mul, zero_add] using
    hasDerivAt_matrix_mul (hasDerivAt_const t P) (gsExpRight_hasDerivAt B₁ Ω t)

theorem gsExpCurve_hasDerivAt (B₂ P B₁ C Ω : Mat n) (hP : Orthogonal P) (t : ℝ) :
    HasDerivAt (gsExpCurve B₂ P B₁ C Ω) (gsExpVelocity B₂ P B₁ C Ω t) t := by
  unfold gsExpCurve product2 gsExpVelocity
  simpa only [Matrix.mul_assoc] using
    product_curve_velocity (gsExpLeft B₂ C)
      (fun s : ℝ => P * gsExpRight B₁ Ω s) C (P * Ω * Pᵀ) t
      (gsExpLeft_hasDerivAt B₂ C t) (gsExpCarrier_hasDerivAt P B₁ Ω hP t)

theorem gsExpVelocity_hasDerivAt (B₂ P B₁ C Ω : Mat n)
    (hP : Orthogonal P) (t : ℝ) :
    HasDerivAt (gsExpVelocity B₂ P B₁ C Ω) (gsExpAcceleration B₂ P B₁ C Ω t) t :=
  product_curve_acceleration (gsExpLeft B₂ C)
    (fun s : ℝ => P * gsExpRight B₁ Ω s) C (P * Ω * Pᵀ) t
    (gsExpLeft_hasDerivAt B₂ C t) (gsExpCarrier_hasDerivAt P B₁ Ω hP t)

theorem gsExpVelocity_eq_tangentParam (B₂ P B₁ C Ω : Mat n)
    (hP : Orthogonal P) (t : ℝ) :
    gsExpVelocity B₂ P B₁ C Ω t =
      tangentParam (gsExpLeft B₂ C t) P (gsExpRight B₁ Ω t) C Ω :=
  (tangentParam_factored _ _ _ _ _ hP).symm

theorem gsExpCurve_acceleration_normal (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ C Ω : Mat n)
    (hab : OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm))
    (hB₂ : Orthogonal B₂) (hB₁ : Orthogonal B₁)
    (hsC : Supported block₂ C) (hsΩ : Supported block₁ Ω)
    (hC : IsSkew C) (hΩ : IsSkew Ω) (t : ℝ) (X : Mat n)
    (hX : TwoFactorDirection block₁ block₂ (gsExpLeft B₂ C t)
      (permMatrix σ) (gsExpRight B₁ Ω t) X) :
    frobInner (gsExpAcceleration B₂ (permMatrix σ) B₁ C Ω t) X = 0 := by
  let P := permMatrix σ
  obtain ⟨D, E, hsD, hD, hsE, hE, rfl⟩ := hX
  rw [tangentParam_factored _ _ _ _ _ (perm_orthogonal σ)]
  exact lifted_acceleration_normal hab (gsExpLeft B₂ C t) (P * gsExpRight B₁ Ω t)
    C (P * Ω * Pᵀ) D (P * E * Pᵀ)
    (gsExpLeft_orthogonal B₂ C hB₂ hC t)
    ((perm_orthogonal σ).mul (gsExpRight_orthogonal B₁ Ω hB₁ hΩ t))
    hsC ((supported_perm_conjugate_iff block₁ σ Ω).mpr hsΩ)
    hsD ((supported_perm_conjugate_iff block₁ σ E).mpr hsE)
    hC (conjugate_skew P Ω hΩ) hD (conjugate_skew P E hE)

theorem gsExpCurve_constant_speed (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (B₂ B₁ C Ω : Mat n)
    (hab : OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm))
    (hB₂ : Orthogonal B₂) (hB₁ : Orthogonal B₁)
    (hsC : Supported block₂ C) (hsΩ : Supported block₁ Ω)
    (hC : IsSkew C) (hΩ : IsSkew Ω) (t : ℝ) :
    frobSq (gsExpVelocity B₂ (permMatrix σ) B₁ C Ω t) = frobSq C + frobSq Ω := by
  rw [gsExpVelocity_eq_tangentParam _ _ _ _ _ (perm_orthogonal σ)]
  exact tangentParam_frobSq _ _ _ _ _ (gsExpLeft_orthogonal B₂ C hB₂ hC t) (perm_orthogonal σ)
    (gsExpRight_orthogonal B₁ Ω hB₁ hΩ t)
    (frobInner_disjoint_supported_skew hab C _ hsC
      ((supported_perm_conjugate_iff block₁ σ Ω).mpr hsΩ) (conjugate_skew _ Ω hΩ))

end GS.Continuation
