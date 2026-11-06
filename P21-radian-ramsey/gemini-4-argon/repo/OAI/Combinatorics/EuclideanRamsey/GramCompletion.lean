module

public import OAI.Combinatorics.EuclideanRamsey.SignedRows

@[expose] public section

namespace OAI.EuclideanRamsey
noncomputable section
open Finset Filter MeasureTheory Matrix
open scoped BigOperators Pointwise Topology TensorProduct MatrixOrder Matrix.Norms.L2Operator

universe uRing uIndex uAlpha uRow

abbrev Lattice (k : ℕ) := Fin k → ℤ
abbrev RationalSpace (k : ℕ) := Fin k → ℚ
abbrev LatticeRing (k : ℕ) := AddMonoidAlgebra ℚ (Lattice k)

def rationalize {k : ℕ} : Lattice k →+ RationalSpace k where
  toFun γ j := γ j
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

def coefficientFunctional {k : ℕ} (g : Lattice k → ℚ) : LatticeRing k →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ g).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] lemma coefficientFunctional_single {k : ℕ} (g : Lattice k → ℚ) (γ : Lattice k) (q : ℚ) :
    coefficientFunctional g (AddMonoidAlgebra.single γ q) = q * g γ := by
  simp [coefficientFunctional, Finsupp.linearCombination_apply]

def mass {k : ℕ} : LatticeRing k →ₐ[ℚ] ℚ :=
  AddMonoidAlgebra.lift ℚ ℚ (Lattice k) 1

abbrev firstMoment {k : ℕ} (a : Fin k) : LatticeRing k →ₗ[ℚ] ℚ :=
  coefficientFunctional fun γ => γ a

abbrev secondMoment {k : ℕ} (a b : Fin k) : LatticeRing k →ₗ[ℚ] ℚ :=
  coefficientFunctional fun γ => γ a * γ b

def cosetMap {k : ℕ} (Λ : AddSubgroup (Lattice k)) :
    LatticeRing k →ₐ[ℚ] AddMonoidAlgebra ℚ (Lattice k ⧸ Λ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (QuotientAddGroup.mk' Λ)

section Algebra
variable {k : ℕ}

lemma mass_eq_sum (x : LatticeRing k) : mass x = x.coeff.sum fun _ q => q := by
  simp [mass, AddMonoidAlgebra.lift_apply]

lemma coefficientFunctional_eq_sum (g : Lattice k → ℚ) (x : LatticeRing k) :
    coefficientFunctional g x = x.coeff.sum fun γ q => q * g γ := by
  simp [coefficientFunctional, Finsupp.linearCombination_apply]

@[simp] lemma mass_single (γ : Lattice k) (q : ℚ) : mass (AddMonoidAlgebra.single γ q) = q := by
  simp [mass]
@[simp] lemma firstMoment_one (a : Fin k) : firstMoment a (1 : LatticeRing k) = 0 := by
  change firstMoment a (AddMonoidAlgebra.single 0 1) = 0; simp

lemma firstMoment_mul (x y : LatticeRing k) (a : Fin k) :
    firstMoment a (x * y) = mass x * firstMoment a y + firstMoment a x * mass y := by
  induction x using AddMonoidAlgebra.induction_on with
  | «of» γ =>
    induction y using AddMonoidAlgebra.induction_on with
    | «of» δ => simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single, mul_add]; ring
    | _ => simp only [mul_add, mul_smul_comm, map_add, map_smul, smul_eq_mul, *]; ring
  | _ => simp only [add_mul, smul_mul_assoc, map_add, map_smul, smul_eq_mul, *]; ring

lemma secondMoment_mul (x y : LatticeRing k) (a b : Fin k) :
    secondMoment a b (x * y) = mass x * secondMoment a b y + secondMoment a b x * mass y +
      firstMoment a x * firstMoment b y + firstMoment b x * firstMoment a y := by
  induction x using AddMonoidAlgebra.induction_on with
  | «of» γ =>
    induction y using AddMonoidAlgebra.induction_on with
    | «of» δ => simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single, mul_add, add_mul]; ring
    | _ => simp only [mul_add, mul_smul_comm, map_add, map_smul, smul_eq_mul, *]; ring
  | _ => simp only [add_mul, smul_mul_assoc, map_add, map_smul, smul_eq_mul, *]; ring

end Algebra

abbrev realLattice (k : ℕ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))
def latticeSample {k : ℕ} (n : ℕ) (γ : Fin k → ℤ) : Fin k → ℝ := fun j => (γ j : ℝ) / n

lemma lattice_tsum_eq_grid {k n : ℕ} (hn : n ≠ 0) (s : Set (Fin k → ℝ))
    (f : (Fin k → ℝ) → ℝ) (hf : Function.support f ⊆ s) :
    (∑' γ : Fin k → ℤ, f (latticeSample n γ)) =
      ∑' x : ↑(s ∩ (n : ℝ)⁻¹ • realLattice k), f x := by
  let : NeZero n := ⟨hn⟩
  have hmem (γ : Fin k → ℤ) : latticeSample n γ ∈ (n : ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)) := by
    rw [← Submodule.coe_pointwise_smul]
    exact BoxIntegral.unitPartition.mem_smul_span_iff.mpr fun j =>
      ⟨γ j, by change (γ j : ℝ) = (n : ℝ) * ((γ j : ℝ) / n); field_simp⟩
  let e : {γ : Fin k → ℤ // latticeSample n γ ∈ s} ≃ ↑(s ∩ (n : ℝ)⁻¹ • realLattice k) :=
    Equiv.ofBijective (fun γ => ⟨latticeSample n γ, γ.2, hmem γ.1⟩) ⟨fun x y h => Subtype.ext <| funext fun j => by
      have he := congr_fun (congr_arg Subtype.val h) j
      dsimp [latticeSample] at he
      exact_mod_cast (div_left_inj' (by exact_mod_cast hn : (n : ℝ) ≠ 0)).mp he, by
      rintro ⟨x, hx1, hx2⟩
      rw [← Submodule.coe_pointwise_smul] at hx2
      choose γ hγ using BoxIntegral.unitPartition.mem_smul_span_iff.mp hx2
      have hγ' : latticeSample n γ = x := funext fun j => by
        simp only [latticeSample]
        have he : (γ j : ℝ) = (n : ℝ) * x j := hγ j
        rw [he, mul_div_cancel_left₀ _ (by exact_mod_cast hn)]
      exact ⟨⟨γ, by simpa [hγ'] using hx1⟩, Subtype.ext hγ'⟩⟩
  rw [← tsum_subtype_eq_of_support_subset (s := {γ | latticeSample n γ ∈ s})
    (f := fun γ => f (latticeSample n γ)) fun _ hγ => hf hγ]
  exact e.tsum_eq fun x => f x

section NilpotentLog
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]

lemma nil_exp_quadratic {a : R} (ha : IsNilpotent a) :
    ∃ c : R, IsNilpotent.exp a = 1 + a + a ^ 2 * c := by
  obtain ⟨n, hn⟩ := ha
  refine ⟨∑ i ∈ range n, ((i + 2).factorial : ℚ)⁻¹ • a ^ i, ?_⟩
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_add_right n 2) hn),
    show n + 2 = 2 + n by omega, sum_range_add]
  have h2 : (∑ i ∈ range 2, (i.factorial : ℚ)⁻¹ • a ^ i) = 1 + a := by simp [sum_range_succ]
  rw [h2, mul_sum]
  congr 1; refine sum_congr rfl fun i _ => ?_
  rw [pow_add, mul_smul_comm, add_comm 2]

lemma nil_exp_eq_one_iff {a : R} (ha : IsNilpotent a) :
    IsNilpotent.exp a = 1 ↔ a = 0 := by
  obtain ⟨c, he⟩ := nil_exp_quadratic ha
  rw [he]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hmul : a * (1 + a * c) = 0 := by linear_combination h
  exact (Commute.all a c).isNilpotent_mul_right ha |>.isUnit_one_add.mul_right_cancel (by simpa using hmul)

lemma nil_exp_sub_one_sub_mem {J : Ideal R} {a : R} (ha : IsNilpotent a) (hJ : a ∈ J) :
    IsNilpotent.exp a - 1 - a ∈ J ^ 2 := by
  obtain ⟨c, he⟩ := nil_exp_quadratic ha
  rw [show IsNilpotent.exp a - 1 - a = a ^ 2 * c by linear_combination he]
  exact Ideal.mul_mem_right c _ (Ideal.pow_mem_pow hJ 2)

omit [Algebra ℚ R] in
lemma nilpotent_of_mem_nil_ideal {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)
    {x : R} (hx : x ∈ I) : IsNilpotent x :=
  ⟨n, by simpa only [hI, Ideal.mem_bot] using Ideal.pow_mem_pow hx n⟩

lemma nil_ideal_exp_surjective {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)
    {z : R} (hz : z ∈ I) : ∃ x ∈ I, IsNilpotent.exp x = 1 + z := by
  have happrox (k : ℕ) : ∃ x ∈ I, IsNilpotent.exp x - (1 + z) ∈ I ^ (k + 1) := by
    induction k with
    | zero => exact ⟨0, I.zero_mem, by simpa using I.neg_mem hz⟩
    | succ k ih =>
      obtain ⟨x, hx, he⟩ := ih
      let e := (1 + z) - IsNilpotent.exp x
      have he' : e ∈ I ^ (k + 1) := by simpa only [e, neg_sub] using (I ^ (k + 1)).neg_mem he
      have hei : e ∈ I := Ideal.pow_le_self (by omega) he'
      have hnx := nilpotent_of_mem_nil_ideal hI hx
      have hne := nilpotent_of_mem_nil_ideal hI hei
      refine ⟨x + e, I.add_mem hx hei, ?_⟩
      rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hne]
      have hle : (I ^ (k + 1)) ^ 2 ≤ I ^ (k + 2) := by
        rw [← pow_mul]; exact Ideal.pow_le_pow_right (by omega)
      have hnx1 : IsNilpotent.exp x - 1 ∈ I := by
        simpa only [sub_add_cancel] using I.add_mem (Ideal.pow_le_self (by omega) (nil_exp_sub_one_sub_mem hnx hx)) hx
      have hterm1 : (IsNilpotent.exp x - 1) * e ∈ I ^ (k + 2) := by
        simpa only [← pow_succ', Nat.add_assoc] using Ideal.mul_mem_mul hnx1 he'
      have hh := (I ^ (k + 2)).add_mem hterm1 (Ideal.mul_mem_left _ (IsNilpotent.exp x) (hle (nil_exp_sub_one_sub_mem hne he')))
      convert hh using 1; dsimp [e]; ring
  obtain ⟨x, hx, he⟩ := happrox n
  rw [show I ^ (n + 1) = ⊥ by simp [pow_succ, hI], Ideal.mem_bot, sub_eq_zero] at he
  exact ⟨x, hx, he⟩

lemma nil_exp_injective {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥) {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    (he : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hna := nilpotent_of_mem_nil_ideal hI ha
  have hnb := nilpotent_of_mem_nil_ideal hI hb
  apply sub_eq_zero.mp
  apply (nil_exp_eq_one_iff (nilpotent_of_mem_nil_ideal hI (I.sub_mem ha hb))).mp
  rw [sub_eq_add_neg, IsNilpotent.exp_add_of_commute (Commute.all _ _) hna hnb.neg,
    he, hnb.exp_mul_exp_neg_self]

end NilpotentLog

def rationalExtension {k : ℕ} {R : Type uRing} [CommRing R] [Algebra ℚ R]
    (f : (Fin k → ℤ) →+ R) : (Fin k → ℚ) →ₗ[ℚ] R where
  toFun v := ∑ j, v j • f (Pi.single j 1)
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [mul_smul, Finset.smul_sum]

def jetOne {k : ℕ} : Ideal (LatticeRing k) where
  carrier := {x | mass x = 0 ∧ ∀ a, firstMoment a x = 0}
  zero_mem' := by simp
  add_mem' hx hy := by simp [hx.1, hx.2, hy.1, hy.2]
  smul_mem' r x hx := by
    change mass (r * x) = 0 ∧ ∀ a, firstMoment a (r * x) = 0
    simp [firstMoment_mul, hx.1, hx.2]

lemma augmentation_sq_le_jetOne {k : ℕ} : (RingHom.ker (mass (k := k))) ^ 2 ≤ jetOne := by
  rw [pow_two]
  refine Ideal.mul_le.mpr fun x hx y hy => ?_
  change mass (x * y) = 0 ∧ ∀ a, firstMoment a (x * y) = 0
  simp [firstMoment_mul, RingHom.mem_ker.mp hx, RingHom.mem_ker.mp hy]

abbrev AffineVector (d : ℕ) := Option (Fin d) → ℝ

def affineArray {d : ℕ} :
    (AffineVector d ⊗[ℚ] AffineVector d) ≃ₗ[ℚ] RealArray d :=
  (TensorProduct.piLeft ℚ (AffineVector d) fun _ : Option (Fin d) => ℝ).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.piRight ℚ ℚ ℝ fun _ : Option (Fin d) => ℝ)

@[simp] lemma affineArray_tmul {d : ℕ} (w z : AffineVector d) (α β : Option (Fin d)) :
    affineArray (w ⊗ₜ[ℚ] z) α β = w α ⊗ₜ[ℚ] z β := rfl

def rowEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : AffineVector d →ₗ[ℚ] ℝ where
  toFun w := ∑ α, realAugmented a i α * w α
  map_add' _ _ := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Rat.smul_def, mul_left_comm, Finset.mul_sum]

lemma arrayEvaluation_affineArray {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (T : AffineVector d ⊗[ℚ] AffineVector d) :
    arrayEvaluation a i (affineArray T) = TensorProduct.map (rowEvaluation a i) (rowEvaluation a i) T := by
  induction T using TensorProduct.inductionOn with
  | tmul w z =>
    simp only [arrayEvaluation, LinearMap.coe_mk, AddHom.coe_mk, affineArray_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.map_tmul,
      rowEvaluation, TensorProduct.sum_tmul, TensorProduct.tmul_sum]
    rw [Finset.sum_comm]; simp only [mul_comm]
  | add x y hx hy => simp [hx, hy]

def positiveCount {α : Type uAlpha} (z : α →₀ ℤ) : α →₀ ℕ := z.mapRange Int.toNat (by simp)
def negativeCount {α : Type uAlpha} (z : α →₀ ℤ) : α →₀ ℕ := z.mapRange (fun n => (-n).toNat) (by simp)

lemma sum_count_elements {α : Type uAlpha} [DecidableEq α] (c : α →₀ ℕ) (f : α → ℝ) :
    (∑ x : c.toMultiset, f x) = c.sum fun a n => (n : ℝ) * f a := by
  change ((Finset.univ : Finset c.toMultiset).val.map fun x : c.toMultiset => f x).sum = _
  rw [Multiset.map_univ, Finsupp.toMultiset_map, Finsupp.sum_toMultiset,
    Finsupp.sum_mapDomain_index (by simp) fun _ _ _ => by simp [add_smul]]
  simp only [nsmul_eq_mul]

lemma row_gram_distance {d : ℕ} {τ : Type uRow} [Fintype τ]
    (v : τ → ℝ) (U : Matrix (Fin d) τ ℝ) (q : ℝ)
    (hU : U * U.transpose = q • (1 : Matrix (Fin d) (Fin d) ℝ)) (a b : Fin d → ℝ) :
    (∑ x, ((v x + ∑ j, a j * U j x) - (v x + ∑ j, b j * U j x)) ^ 2) = q * ∑ j, (a j - b j) ^ 2 := by
  have he (x : τ) : (v x + ∑ j, a j * U j x) - (v x + ∑ j, b j * U j x) = (U.transpose *ᵥ (a - b)) x := by
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Pi.sub_apply,
      mul_sub, Finset.sum_sub_distrib, mul_comm]
    ring
  simp only [he, sq]
  change (U.transpose *ᵥ (a - b)) ⬝ᵥ (U.transpose *ᵥ (a - b)) = _
  have hquad : (U.transpose *ᵥ (a - b)) ⬝ᵥ (U.transpose *ᵥ (a - b)) =
      (a - b) ⬝ᵥ ((U * U.transpose) *ᵥ (a - b)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (a - b) U]
    congr 1; exact (Matrix.vecMul_transpose U.transpose (a - b)).symm
  rw [hquad, hU, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  simp only [smul_eq_mul, dotProduct, Pi.sub_apply]

set_option maxHeartbeats 800000 in
theorem realCriterion_two_scale {s d : ℕ} (a : Fin s → Space d)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (h : RealCriterion a) (η : ℝ) (hη : 0 < η) :
    ∃ (ℓ : ℕ) (f g : Fin s → Space ℓ),
      (∀ i j, ‖f i - f j‖ ^ 2 = ‖a i - a j‖ ^ 2) ∧
      (∀ i j, ‖g i - g j‖ ^ 2 = (η / (1 + η)) * ‖a i - a j‖ ^ 2) ∧
      ∀ i, ∃ σ : Equiv.Perm (Fin ℓ), ∀ x, g i (σ x) = f i x := by
  classical
  obtain ⟨P, hP, hG⟩ := h
  let T : AffineVector d ⊗[ℚ] AffineVector d := affineArray.symm P
  have hT : affineArray T = P := affineArray.apply_symm_apply P
  obtain ⟨k, w, C, hC, hrep⟩ : ∃ (k : ℕ) (w : Fin k → AffineVector d) (C : Matrix (Fin k) (Fin k) ℚ),
      C.IsSymm ∧ (∑ j, ∑ l, C j l • (w j ⊗ₜ[ℚ] w l)) =
        (1 / 2 : ℚ) • (T + TensorProduct.comm ℚ _ _ T) := by
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset T
    let w₀ : ↥S ⊕ ↥S → AffineVector d := Sum.elim (fun z => z.1.1) fun z => z.1.2
    let C₀ : ↥S ⊕ ↥S → ↥S ⊕ ↥S → ℚ := fun j l => match j, l with
      | .inl i, .inr j | .inr i, .inl j => if i = j then 1 / 2 else 0
      | _, _ => 0
    let e := Fintype.equivFin (↥S ⊕ ↥S)
    refine ⟨Fintype.card (↥S ⊕ ↥S), fun j => w₀ (e.symm j), fun j l => C₀ (e.symm j) (e.symm l), ?_, ?_⟩
    · ext j l; change C₀ (e.symm l) (e.symm j) = C₀ (e.symm j) (e.symm l)
      rcases e.symm j with i | i <;> rcases e.symm l with m | m <;> simp [C₀, eq_comm]
    · calc (∑ j, ∑ l, C₀ (e.symm j) (e.symm l) • (w₀ (e.symm j) ⊗ₜ[ℚ] w₀ (e.symm l)))
        _ = ∑ j, ∑ l : ↥S ⊕ ↥S, C₀ (e.symm j) l • (w₀ (e.symm j) ⊗ₜ[ℚ] w₀ l) :=
          Finset.sum_congr rfl fun j _ => e.symm.sum_comp fun l => C₀ (e.symm j) l • (w₀ (e.symm j) ⊗ₜ[ℚ] w₀ l)
        _ = ∑ j : ↥S ⊕ ↥S, ∑ l : ↥S ⊕ ↥S, C₀ j l • (w₀ j ⊗ₜ[ℚ] w₀ l) :=
          e.symm.sum_comp fun j => ∑ l, C₀ j l • (w₀ j ⊗ₜ[ℚ] w₀ l)
        _ = _ := by
          simp only [Fintype.sum_sum_type, C₀, w₀, zero_smul, Finset.sum_const_zero, zero_add, add_zero,
            ite_smul, Sum.elim_inl, Sum.elim_inr, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
          rw [hS]
          simp only [map_sum, TensorProduct.comm_tmul, smul_add, Finset.smul_sum, ← Finset.sum_coe_sort S]
  have hsp_comm : spatialMultiply (affineArray (TensorProduct.comm ℚ _ _ T)) =
      (spatialMultiply (affineArray T)).transpose := by
    ext α β
    change Algebra.TensorProduct.lmul' ℚ (affineArray (TensorProduct.comm ℚ _ _ T) (some α) (some β)) =
      Algebra.TensorProduct.lmul' ℚ (affineArray T (some β) (some α))
    have hc (X : AffineVector d ⊗[ℚ] AffineVector d) :
        affineArray (TensorProduct.comm ℚ _ _ X) (some α) (some β) =
          TensorProduct.comm ℚ ℝ ℝ (affineArray X (some β) (some α)) := by
      induction X using TensorProduct.inductionOn with
      | tmul => rfl
      | add _ _ hx hy => simp [hx, hy]
    rw [hc]
    generalize affineArray T (some β) (some α) = z
    induction z using TensorProduct.inductionOn with
    | tmul => simp [mul_comm]
    | add _ _ hx hy => simp [hx, hy]
  have hs0 : spatialMultiply (affineArray (∑ j, ∑ l, C j l • (w j ⊗ₜ[ℚ] w l))) = 1 := by
    rw [hrep, map_smul, map_add, map_smul, map_add, hsp_comm, hT, hG]
    ext α β
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.one_apply]
    by_cases hh : α = β <;> norm_num [hh, eq_comm, Rat.smul_def]
  let U₀ : Matrix (Fin d) (Fin k) ℝ := fun α j => w j (some α)
  have hU : U₀ * C.map (Rat.cast : ℚ → ℝ) * U₀.transpose = 1 := by
    rw [← hs0]; ext α β
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, spatialMultiply, LinearMap.coe_mk]
    change (∑ l, (∑ j, w j (some α) * (C j l : ℝ)) * w l (some β)) =
      ∑ j, ∑ l, (C j l : ℝ) * (w j (some α) * w l (some β))
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  let f (i : Fin s) : RationalSpace k →ₗ[ℚ] ℝ :=
    (rowEvaluation a i).comp (Fintype.linearCombination ℚ w)
  let φ (i : Fin s) : Lattice k →+ ℝ := (f i).toAddMonoidHom.comp rationalize
  let Λ (i : Fin s) := (φ i).ker
  have hT0 (i : Fin s) : (∑ j, ∑ l, C j l • (f i (Pi.single j 1) ⊗ₜ[ℚ] f i (Pi.single l 1))) = 0 := by
    have hac (X : AffineVector d ⊗[ℚ] AffineVector d) :
        arrayEvaluation a i (affineArray (TensorProduct.comm ℚ _ _ X)) =
          TensorProduct.comm ℚ ℝ ℝ (arrayEvaluation a i (affineArray X)) := by
      simp only [arrayEvaluation_affineArray]
      induction X using TensorProduct.inductionOn with
      | tmul => rfl
      | add _ _ hx hy => simp [hx, hy]
    have h1 : (∑ j, ∑ l, C j l • (f i (Pi.single j 1) ⊗ₜ[ℚ] f i (Pi.single l 1))) =
        arrayEvaluation a i (affineArray (∑ j, ∑ l, C j l • (w j ⊗ₜ[ℚ] w l))) := by
      simp [f, arrayEvaluation_affineArray]
    rw [h1, hrep, map_smul, map_add, map_smul, map_add, hac, hT, hP, map_zero, add_zero, smul_zero]
  let : IsNoetherianRing (LatticeRing k) := Algebra.FiniteType.isNoetherianRing ℚ (LatticeRing k)
  let I : Ideal (LatticeRing k) := RingHom.ker mass
  let J₀ (i : Fin s) : Ideal (LatticeRing k) := RingHom.ker (cosetMap (Λ i))
  let f_adic : LatticeRing k →ₗ[LatticeRing k] ∀ i, LatticeRing k ⧸ J₀ i :=
    LinearMap.pi fun i => Algebra.linearMap (LatticeRing k) (LatticeRing k ⧸ J₀ i)
  obtain ⟨k₀, hk₀⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f_adic)
  let n₀ := k₀ + 3
  let N₀ := n₀ + 3
  let q₀ := Ideal.Quotient.mkₐ ℚ (I ^ N₀)
  let M₀ := Ideal.map (Ideal.Quotient.mk (I ^ N₀)) I
  have hnil : M₀ ^ N₀ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  let χ : Multiplicative (Lattice k) →* (LatticeRing k ⧸ I ^ N₀) :=
    q₀.toMonoidHom.comp (AddMonoidAlgebra.of ℚ (Lattice k))
  have hχ (γ : Lattice k) : χ (Multiplicative.ofAdd γ) - 1 ∈ M₀ := by
    have hm : AddMonoidAlgebra.single γ 1 - 1 ∈ I := by change mass _ = 0; simp [mass]
    simpa [χ, q₀, AddMonoidAlgebra.of_apply, map_sub] using
      Ideal.mem_map_of_mem (Ideal.Quotient.mk (I ^ N₀)) hm
  let cLog (γ : Lattice k) := Classical.choose (nil_ideal_exp_surjective hnil (hχ γ))
  have hcMem (γ : Lattice k) : cLog γ ∈ M₀ :=
    (Classical.choose_spec (nil_ideal_exp_surjective hnil (hχ γ))).1
  have hcExp (γ : Lattice k) : IsNilpotent.exp (cLog γ) = χ (Multiplicative.ofAdd γ) := by
    simpa only [cLog, add_sub_cancel] using
      (Classical.choose_spec (nil_ideal_exp_surjective hnil (hχ γ))).2
  let f₀ : Lattice k →+ (LatticeRing k ⧸ I ^ N₀) :=
    { toFun := cLog
      map_zero' := nil_exp_injective hnil (hcMem 0) M₀.zero_mem
        (by rw [hcExp, IsNilpotent.exp_zero]; exact χ.map_one)
      map_add' := fun a b => nil_exp_injective hnil (hcMem _) (M₀.add_mem (hcMem _) (hcMem _))
        (by rw [hcExp, IsNilpotent.exp_add_of_commute (Commute.all _ _)
              (nilpotent_of_mem_nil_ideal hnil (hcMem _))
              (nilpotent_of_mem_nil_ideal hnil (hcMem _)), hcExp, hcExp, ofAdd_add, χ.map_mul]) }
  have hex (a : Fin k) : ∃ r ∈ I ^ 2,
      Ideal.Quotient.mk (I ^ N₀) (AddMonoidAlgebra.single (Pi.single a 1) 1 - 1 - r) = f₀ (Pi.single a 1) := by
    have h1 := nil_exp_sub_one_sub_mem (nilpotent_of_mem_nil_ideal hnil (hcMem (Pi.single a 1)))
      (hcMem (Pi.single a 1))
    rw [← Ideal.map_pow] at h1
    obtain ⟨r, hr, hqr⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
    refine ⟨r, hr, ?_⟩
    have : Ideal.Quotient.mk (I ^ N₀) (AddMonoidAlgebra.single (Pi.single a 1) 1) =
        IsNilpotent.exp (cLog (Pi.single a 1)) := (hcExp _).symm
    change _ = cLog (Pi.single a 1)
    rw [map_sub, map_sub, map_one, this, hqr]; ring
  choose r hrI hrl using hex
  let l (a : Fin k) : LatticeRing k := AddMonoidAlgebra.single (Pi.single a 1) 1 - 1 - r a
  have hm (a : Fin k) : mass (l a) = 0 := by
    have := (augmentation_sq_le_jetOne (hrI a)).1
    simp [l, this]
  have hfirst_l (a b : Fin k) : firstMoment b (l a) = if a = b then 1 else 0 := by
    have := (augmentation_sq_le_jetOne (hrI a)).2 b
    simp [l, this, Pi.single_apply, eq_comm]
  let x₀ : LatticeRing k := (1 / 2 : ℚ) • ∑ a, ∑ b, C a b • (l a * l b)
  have hx (i : Fin s) : x₀ ∈ J₀ i ⊔ I ^ n₀ := by
    apply (sup_le_sup_left (α := Ideal (LatticeRing k)) (Ideal.pow_le_pow_right (by omega : n₀ ≤ N₀)) (J₀ i))
    let J := J₀ i ⊔ I ^ N₀
    let ψ := Ideal.Quotient.factorₐ ℚ (le_sup_right : I ^ N₀ ≤ J)
    let g := ψ.toLinearMap.comp (rationalExtension f₀)
    have hγ0 {γ : Lattice k} (hγ : γ ∈ Λ i) : g (rationalize γ) = 0 := by
      have hnγ := nilpotent_of_mem_nil_ideal hnil (hcMem γ)
      change ψ (rationalExtension f₀ fun j => (γ j : ℚ)) = 0
      have hlat : rationalExtension f₀ (fun j => (γ j : ℚ)) = f₀ γ := by
        dsimp [rationalExtension]
        simp_rw [Int.cast_smul_eq_zsmul, ← map_zsmul]
        rw [← map_sum]
        congr 1; convert Finset.univ_sum_single γ using 2; ext j; rw [← Pi.single_smul]; simp
      rw [hlat]
      apply (nil_exp_eq_one_iff (hnγ.map ψ)).mp
      rw [← hnγ.map_exp ψ, hcExp]
      change Ideal.Quotient.mk J (AddMonoidAlgebra.single γ 1) = 1
      have hcos_mem : AddMonoidAlgebra.single γ 1 - 1 ∈ J₀ i := by
        change cosetMap (Λ i) (AddMonoidAlgebra.single γ 1 - 1) = 0
        rw [map_sub, map_one]; simp [cosetMap, (QuotientAddGroup.eq_zero_iff γ).mpr hγ, AddMonoidAlgebra.one_def]
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hcos_mem : _ ∈ J)
      simpa only [map_sub, map_one, sub_eq_zero] using hz
    have hg : LinearMap.ker (f i) ≤ LinearMap.ker g := fun x hx => by
      let A : Matrix Unit (Fin k) ℚ := fun _ j => x j
      let γ : Lattice k := fun j => A.num () j
      have hden : (A.den : ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
      have he : rationalize γ = (A.den : ℚ) • x := by
        ext j
        exact ((div_eq_iff hden).mp (A.num_div_den () j : (A.num () j : ℚ) / A.den = x j)).trans (mul_comm _ _)
      have hγ : γ ∈ Λ i := by change f i (rationalize γ) = 0; rw [he, map_smul, hx, smul_zero]
      have h0 := congrArg ((A.den : ℚ)⁻¹ • ·) (hγ0 hγ)
      exact LinearMap.mem_ker.mpr (by simpa only [he, map_smul, smul_smul, inv_mul_cancel₀ hden, one_smul, smul_zero] using h0)
    let j : (RationalSpace k ⧸ (f i).ker) →ₗ[ℚ] ℝ := (f i).range.subtype.comp (f i).quotKerEquivRange.toLinearMap
    obtain ⟨r', hr'⟩ := j.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((f i).range.subtype_injective.comp (f i).quotKerEquivRange.injective))
    let u := ((f i).ker.liftQ g hg).comp r'
    have hu (x : RationalSpace k) : u (f i x) = g x := by
      change (f i).ker.liftQ g hg ((r'.comp j) ((f i).ker.mkQ x)) = g x
      rw [hr', LinearMap.id_apply]; rfl
    let φ' := (Algebra.TensorProduct.lmul' ℚ : (LatticeRing k ⧸ J) ⊗[ℚ] (LatticeRing k ⧸ J) →ₐ[ℚ] _).toLinearMap.comp
      (TensorProduct.map u u)
    have hquad : (∑ a, ∑ b, C a b • (g (Pi.single a 1) * g (Pi.single b 1))) = 0 := by
      simpa [φ', hu, LinearMap.comp_apply] using congrArg φ' (hT0 i)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ ℚ J x₀ = 0
    have hlj (a : Fin k) : Ideal.Quotient.mkₐ ℚ J (l a) = g (Pi.single a 1) := by
      change ψ (Ideal.Quotient.mk (I ^ N₀) (l a)) = ψ (rationalExtension f₀ (Pi.single a 1))
      rw [hrl]; simp [rationalExtension, Pi.single_apply]
    simp only [x₀, map_smul, map_sum, map_mul, hlj, hquad, smul_zero]
  have hz (i : Fin s) : ∃ z ∈ I ^ n₀, Ideal.Quotient.mk (J₀ i) z = Ideal.Quotient.mk (J₀ i) x₀ := by
    obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (hx i)
    exact ⟨z, hz, by rw [← he, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, zero_add]⟩
  choose z hz he using hz
  have hm' : f_adic x₀ ∈ I ^ n₀ • (⊤ : Submodule (LatticeRing k) (∀ i, LatticeRing k ⧸ J₀ i)) := by
    have he' : f_adic x₀ = ∑ i, z i • Pi.single i (1 : LatticeRing k ⧸ J₀ i) := by
      simp_rw [← Pi.single_smul, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, he]
      exact (Finset.univ_sum_single _).symm
    rw [he']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hz i) Submodule.mem_top
  have hfx : f_adic x₀ ∈ I ^ n₀ • (⊤ : Submodule (LatticeRing k) (∀ i, LatticeRing k ⧸ J₀ i)) ⊓ LinearMap.range f_adic := ⟨hm', ⟨x₀, rfl⟩⟩
  rw [hk₀ n₀ (by omega), Nat.add_sub_cancel_left] at hfx
  have hf' : f_adic x₀ ∈ Submodule.map f_adic (I ^ 3 • (⊤ : Submodule (LatticeRing k) (LatticeRing k))) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact smul_mono_right (I ^ 3) (inf_le_right : _ ≤ LinearMap.range f_adic) hfx
  obtain ⟨w₀, hw₀, hew⟩ := hf'
  let ν := x₀ - w₀
  have hcos₀ (i : Fin s) : cosetMap (Λ i) ν = 0 := Ideal.Quotient.eq_zero_iff_mem.mp <| by
    have h0 : f_adic ν = 0 := by dsimp [ν]; rw [map_sub, hew, sub_self]
    exact congrFun h0 i
  have hxy : x₀ - ν ∈ I ^ 3 := by dsimp [ν]; simpa [sub_sub_cancel] using hw₀
  let J : Ideal (LatticeRing k) :=
    { carrier := {z | z ∈ jetOne ∧ ∀ a b, secondMoment a b z = 0}
      zero_mem' := ⟨jetOne.zero_mem, by simp⟩
      add_mem' hx hy := ⟨jetOne.add_mem hx.1 hy.1, by simp [hx.2, hy.2]⟩
      smul_mem' r z hz := ⟨jetOne.smul_mem r hz.1, fun a b => by
        change secondMoment a b (r * z) = 0
        simp [secondMoment_mul, hz.1.1, hz.1.2, hz.2]⟩ }
  have hle : I ^ 3 ≤ J := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ']
    refine Ideal.mul_le.mpr fun a ha b hb => ⟨jetOne.mul_mem_left a (augmentation_sq_le_jetOne hb), fun j l => ?_⟩
    have hb0 := augmentation_sq_le_jetOne hb
    simp [secondMoment_mul, RingHom.mem_ker.mp ha, hb0.1, hb0.2]
  have ⟨h1, h2⟩ := hle hxy
  change mass (x₀ - ν) = 0 ∧ ∀ a, firstMoment a (x₀ - ν) = 0 at h1
  change ∀ a b, secondMoment a b (x₀ - ν) = 0 at h2
  simp only [map_sub, sub_eq_zero] at h1 h2
  have hzero : mass ν = 0 := h1.1.symm.trans (by simp [x₀, hm])
  have hfirst (a : Fin k) : firstMoment a ν = 0 := (h1.2 a).symm.trans (by simp [x₀, firstMoment_mul, hm])
  have hsecond (a b : Fin k) : secondMoment a b ν = C a b := (h2 a b).symm.trans <| by
    simp only [x₀, map_smul, smul_eq_mul, map_sum, secondMoment_mul, hm,
      hfirst_l, zero_mul, mul_zero, zero_add, mul_add, Finset.sum_add_distrib,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [show C b a = C a b from congrFun (congrFun hC a) b]; ring
  let S := ν.coeff.support
  let q (γ : Fin k → ℤ) : ℝ := ν.coeff γ
  let v₀ (γ : Fin k → ℤ) (j : Fin k) : ℝ := γ j
  let CR := C.map (Rat.cast : ℚ → ℝ)
  have hC' : CR.IsSymm := by ext j l; exact congrArg Rat.cast (congrFun (congrFun hC j) l)
  obtain ⟨b, hb, hbc, hbI, hbη⟩ := compact_smoothing k d hd CR U₀ hC' hU η hη
  have hz₀ : ∑ γ ∈ S, q γ = 0 := by dsimp [S, q]; exact_mod_cast (mass_eq_sum ν).symm.trans hzero
  have hf₀ (j : Fin k) : ∑ γ ∈ S, q γ * v₀ γ j = 0 := by
    dsimp [S, q, v₀]; exact_mod_cast (coefficientFunctional_eq_sum _ ν).symm.trans (hfirst j)
  have hs' (j l : Fin k) : ∑ γ ∈ S, q γ * v₀ γ j * v₀ γ l = CR j l := by
    change ∑ γ ∈ S, (ν.coeff γ : ℝ) * (γ j : ℝ) * (γ l : ℝ) = (C j l : ℝ)
    simp only [mul_assoc]
    exact_mod_cast (coefficientFunctional_eq_sum _ ν).symm.trans (hsecond j l)
  obtain ⟨K₀, hK₀⟩ := (hb.continuous_iteratedFDeriv (m := 3) (by norm_cast)).bounded_above_of_compact_support
    (hbc.iteratedFDeriv 3)
  have hK₀0 : 0 ≤ K₀ := (norm_nonneg _).trans (hK₀ 0)
  let K := ∑ γ ∈ S, |q γ| * K₀ * ‖v₀ γ‖ ^ 3
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => by positivity
  have hv₀ (γ : Fin k → ℤ) : v₀ γ = ∑ j, v₀ γ j • Pi.single j (1 : ℝ) := by ext l; simp [Pi.single_apply]
  have hTaylor (t : ℝ) (ht : 0 < t) (x : Fin k → ℝ) :
      |t ^ 2 * (∑ γ ∈ S, q γ * b (x + (-t⁻¹) • v₀ γ)) - stencilDifferential CR b x| ≤ K / t := by
    have hl : ∑ γ ∈ S, q γ * fderiv ℝ b x (v₀ γ) = 0 := by
      conv_lhs => arg 2; intro γ; rw [hv₀ γ]
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]; simp [← Finset.sum_mul, hf₀]
    have hb' : ∑ γ ∈ S, q γ * iteratedFDeriv ℝ 2 b x ![v₀ γ, v₀ γ] =
        ∑ j, ∑ l, CR j l * iteratedFDeriv ℝ 2 b x ![Pi.single j 1, Pi.single l 1] := by
      simp only [← hessianB_eq, ← hs']
      have he (γ : Fin k → ℤ) : q γ * hessianB b x (v₀ γ) (v₀ γ) =
          ∑ j, ∑ l, q γ * v₀ γ j * v₀ γ l * hessianB b x (Pi.single j 1) (Pi.single l 1) := by
        rw [congrArg (fun a => hessianB b x a (v₀ γ)) (hv₀ γ)]
        simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [congrArg (hessianB b x (Pi.single j 1)) (hv₀ γ)]
        simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      simp only [he, Finset.sum_mul]
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    let r (γ : Fin k → ℤ) := b (x + (-t⁻¹) • v₀ γ) - b x - fderiv ℝ b x ((-t⁻¹) • v₀ γ) -
      (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v₀ γ, (-t⁻¹) • v₀ γ]
    have hscale (γ : Fin k → ℤ) : iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v₀ γ, (-t⁻¹) • v₀ γ] =
        (t⁻¹) ^ 2 * iteratedFDeriv ℝ 2 b x ![v₀ γ, v₀ γ] := by
      simp only [← hessianB_eq, map_smul, _root_.smul_apply, smul_eq_mul]; ring
    have hrEq : t ^ 2 * (∑ γ ∈ S, q γ * b (x + (-t⁻¹) • v₀ γ)) - stencilDifferential CR b x =
        t ^ 2 * ∑ γ ∈ S, q γ * r γ := by
      have hz0 : ∑ γ ∈ S, q γ * b x = 0 := by rw [← Finset.sum_mul, hz₀, zero_mul]
      have h1 : ∑ γ ∈ S, q γ * (-t⁻¹ * fderiv ℝ b x (v₀ γ)) = 0 := by
        rw [show (∑ γ ∈ S, q γ * (-t⁻¹ * fderiv ℝ b x (v₀ γ))) = -t⁻¹ * ∑ γ ∈ S, q γ * fderiv ℝ b x (v₀ γ) by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hl, mul_zero]
      have h2 : ∑ γ ∈ S, q γ * ((1 / 2 : ℝ) * ((t⁻¹) ^ 2 * iteratedFDeriv ℝ 2 b x ![v₀ γ, v₀ γ])) =
          (t⁻¹) ^ 2 * stencilDifferential CR b x := by
        unfold stencilDifferential; rw [← hb']; simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      simp only [r, mul_sub, Finset.sum_sub_distrib, map_smul, smul_eq_mul, hscale]
      rw [hz0, h1, h2]; field_simp; ring
    rw [hrEq, abs_mul, abs_of_nonneg (sq_nonneg t)]
    calc
      _ ≤ t ^ 2 * ∑ γ ∈ S, |q γ| * |r γ| := by
        gcongr; simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun γ => q γ * r γ) S
      _ ≤ t ^ 2 * ∑ γ ∈ S, |q γ| * (K₀ * (t⁻¹) ^ 3 * ‖v₀ γ‖ ^ 3) := by
        gcongr with γ _
        let h := (-t⁻¹) • v₀ γ
        have ht' := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (f := b) (x := x) (y := h)
          (fun s _ => (hb.of_le (by norm_cast)).contDiffAt)
        have he : r γ = (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..1, (1 - s) ^ 2 * iteratedFDeriv ℝ 3 b (x + s • h) (fun _ => h) := by
          have hvec : (fun _ : Fin 2 => h) = ![h, h] := by ext i; fin_cases i <;> rfl
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial,
            Nat.cast_one, Nat.cast_mul, inv_one, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, smul_eq_mul, hvec] at ht'
          dsimp [r, h]; linarith
        rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        have hi : |∫ s in (0 : ℝ)..1, (1 - s) ^ 2 * iteratedFDeriv ℝ 3 b (x + s • h) (fun _ => h)| ≤ K₀ * ‖h‖ ^ 3 := by
          have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
            (f := fun s => (1 - s) ^ 2 * iteratedFDeriv ℝ 3 b (x + s • h) fun _ => h) (C := K₀ * ‖h‖ ^ 3) fun s hsb => by
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            have hm := (iteratedFDeriv ℝ 3 b (x + s • h)).le_opNorm (fun _ => h)
            simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hm
            have hs1 : 0 < s := by simpa using hsb.1
            have hs2 : s ≤ 1 := by simpa using hsb.2
            exact (mul_le_mul (by nlinarith) (hm.trans (mul_le_mul_of_nonneg_right (hK₀ _) (by positivity)))
              (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
          simpa using hh
        have hnorm : K₀ * ‖h‖ ^ 3 = K₀ * (t⁻¹) ^ 3 * ‖v₀ γ‖ ^ 3 := by
          simp [h, norm_smul, abs_of_pos ht, mul_pow, mul_assoc]
        linarith [mul_nonneg hK₀0 (pow_nonneg (norm_nonneg h) 3)]
      _ = K / t := by
        rw [Finset.mul_sum, Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by field_simp
  let f₁ := fun x => max (-stencilDifferential CR b x) 0 * gradientWeight U₀ x
  let g₁ := fun (n : ℕ) x => max (-((n : ℝ) ^ 2 * ∑ γ ∈ S, q γ * b (x + (-(n : ℝ)⁻¹) • v₀ γ))) 0 * gradientWeight U₀ x
  have hc : Continuous f₁ := by
    have : Continuous (iteratedFDeriv ℝ 2 b) := hb.continuous_iteratedFDeriv (by norm_cast)
    unfold f₁ stencilDifferential gradientWeight; fun_prop
  obtain ⟨r₀, hr₀, hbr⟩ := hbc.exists_pos_le_norm
  let V₀ := ∑ γ ∈ S, ‖v₀ γ‖
  have hV₀ : 0 ≤ V₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let R₀ := r₀ + V₀ + 1
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith
  let sB := Metric.closedBall (0 : Fin k → ℝ) R₀
  have hbs : Function.support b ⊆ sB := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_not_gt fun h => hx (hbr x (by dsimp [R₀] at h; linarith))
  have hfr : Function.support f₁ ⊆ sB := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    have hi : x ∉ tsupport (iteratedFDeriv ℝ 2 b) := fun hx' =>
      notMem_tsupport_iff_eventuallyEq.mpr
        (by filter_upwards [continuous_norm.continuousAt.eventually (eventually_gt_nhds (by dsimp [R₀] at h; linarith : r₀ < ‖x‖))] with y hy
            exact hbr y hy.le)
        (tsupport_iteratedFDeriv_subset 2 hx')
    exact hx (by simp [f₁, stencilDifferential, image_eq_zero_of_notMem_tsupport hi])
  have hgr (n : ℕ) : Function.support (g₁ n) ⊆ sB := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    refine hx ?_
    by_cases hn : n = 0
    · simp [g₁, hn]
    have hni : |(n : ℝ)⁻¹| ≤ 1 := by
      rw [abs_inv, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    have hsum : ∑ γ ∈ S, q γ * b (x + (-(n : ℝ)⁻¹) • v₀ γ) = 0 :=
      Finset.sum_eq_zero fun γ hγ => by
        have hshift : ‖(-(n : ℝ)⁻¹) • v₀ γ‖ ≤ V₀ := by
          rw [norm_smul, Real.norm_eq_abs, abs_neg]
          exact (mul_le_mul_of_nonneg_right hni (norm_nonneg _)).trans
            (by simpa using Finset.single_le_sum (fun _ _ => norm_nonneg _) hγ)
        have hx' := norm_le_norm_add_norm_sub (x + (-(n : ℝ)⁻¹) • v₀ γ) x
        rw [add_sub_cancel_left] at hx'
        rw [hbr _ (by dsimp [R₀] at h; linarith), mul_zero]
    dsimp only [g₁]; rw [hsum]; simp
  obtain ⟨W, hW⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R₀).exists_bound_of_continuousOn
    (show Continuous (gradientWeight U₀) by unfold gradientWeight; fun_prop).continuousOn
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 (by simp [hR₀.le]))
  have hfront : volume (frontier sB) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere
      (volume.addHaar_sphere_of_ne_zero 0 hR₀.ne')
  have hriem {φ₀ : (Fin k → ℝ) → ℝ} (hφ : Continuous φ₀) (hφs : Function.support φ₀ ⊆ sB) :
      Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, φ₀ (latticeSample n γ)) / (n : ℝ) ^ k)
        atTop (𝓝 (∫ x, φ₀ x)) := by
    have h := tendsto_tsum_div_pow_atTop_integral sB φ₀ hφ Metric.isBounded_closedBall
      measurableSet_closedBall hfront
    rw [Fintype.card_fin, ← integral_indicator measurableSet_closedBall, Set.indicator_eq_self.mpr hφs] at h
    exact h.congr' (by filter_upwards [eventually_ge_atTop 1] with n hn; rw [lattice_tsum_eq_grid (by omega) sB φ₀ hφs])
  have hN : Tendsto (fun n : ℕ => (∑' δ : Fin k → ℤ, g₁ n (latticeSample n δ)) / (n : ℝ) ^ k) atTop (𝓝 (∫ x, f₁ x)) := by
    have hlim := (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => K * W / (n : ℝ)) atTop (𝓝 0)).mul
      (tendsto_card_div_pow_atTop_volume sB Metric.isBounded_closedBall measurableSet_closedBall hfront)
    rw [zero_mul] at hlim
    have hdiff : Tendsto (fun n : ℕ =>
        (∑' γ : Fin k → ℤ, g₁ n (latticeSample n γ)) / (n : ℝ) ^ k -
        (∑' γ : Fin k → ℤ, f₁ (latticeSample n γ)) / (n : ℝ) ^ k) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : n ≠ 0 := by omega
      let G := ↑(sB ∩ (n : ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)))
      have hfin : (sB ∩ (n : ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))).Finite := by
        rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (by exact_mod_cast hn0))]
        exact ZSpan.setFinite_inter _ Metric.isBounded_closedBall
      let : Fintype G := hfin.fintype
      rw [Real.norm_eq_abs, Fintype.card_fin, lattice_tsum_eq_grid hn0 sB (g₁ n) (hgr n),
        lattice_tsum_eq_grid hn0 sB f₁ hfr, ← sub_div, abs_div, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ k)]
      have hsum : |(∑' x : G, g₁ n x) - (∑' x : G, f₁ x)| ≤ (Nat.card G : ℝ) * (K * W / n) := by
        rw [tsum_fintype, tsum_fintype, ← Finset.sum_sub_distrib]
        calc
          _ ≤ ∑ x : G, |g₁ n x - f₁ x| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _x : G, K * W / (n : ℝ) := Finset.sum_le_sum fun x _ => by
            have hw : |gradientWeight U₀ x.1| ≤ W := by simpa [Real.norm_eq_abs] using hW x.1 x.2.1
            have he := hTaylor n (by exact_mod_cast (by omega : 0 < n)) x.1
            have hm' : |max (-((n : ℝ) ^ 2 * ∑ γ ∈ S, q γ * b (x.1 + (-(n : ℝ)⁻¹) • v₀ γ))) 0 -
                max (-stencilDifferential CR b x.1) 0| ≤ K / n :=
              (abs_max_sub_max_le_abs _ _ 0).trans (by simpa only [neg_sub_neg, abs_sub_comm] using he)
            dsimp [g₁, f₁]; rw [← sub_mul, abs_mul]
            exact (mul_le_mul hm' hw (abs_nonneg _) (by positivity)).trans_eq (by ring)
          _ = _ := by simp [Nat.card_eq_fintype_card]
      exact (div_le_div_of_nonneg_right hsum (by positivity)).trans_eq (by ring)
    convert hdiff.add (hriem hc hfr) using 1
    · ext n; ring
    · simp
  have hZ := hriem hb.continuous hbs
  have he := hN.eventually_lt (tendsto_const_nhds.mul hZ) hbη
  have hp := tendsto_const_nhds.eventually_lt hZ hbI
  obtain ⟨n, hn, hp, he⟩ := (eventually_ge_atTop 1 |>.and (hp.and he)).exists
  let a₀ := fun γ : Fin k → ℤ => b (latticeSample n γ)
  have hnf : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hshift (δ γ : Fin k → ℤ) : latticeSample n δ + (-(n : ℝ)⁻¹) • v₀ γ = latticeSample n (δ - γ) := by
    ext j; simp only [latticeSample, v₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Int.cast_sub]; ring
  dsimp [g₁] at he
  simp only [hshift] at he
  have hscale (δ : Fin k → ℤ) :
      max (-((n : ℝ) ^ 2 * ∑ γ ∈ S, q γ * a₀ (δ - γ))) 0 * gradientWeight U₀ (latticeSample n δ) =
      (n : ℝ) ^ 2 * (max (-(∑ γ ∈ S, q γ * a₀ (δ - γ))) 0 * gradientWeight U₀ (latticeSample n δ)) := by
    rw [← mul_neg, ← mul_zero ((n : ℝ) ^ 2), ← mul_max_of_nonneg _ _ (sq_nonneg (n : ℝ)), mul_assoc, mul_zero]
  change (∑' δ, max (-((n : ℝ) ^ 2 * ∑ γ ∈ S, q γ * a₀ (δ - γ))) 0 *
    gradientWeight U₀ (latticeSample n δ)) / (n : ℝ) ^ k < η * ((∑' γ, a₀ γ) / (n : ℝ) ^ k) at he
  simp only [hscale, tsum_mul_left] at he
  have hp' : 0 < ∑' γ, a₀ γ := (div_pos_iff_of_pos_right (pow_pos hnf k)).mp hp
  have han : (∑' δ, max (-(∑ γ ∈ S, q γ * a₀ (δ - γ))) 0 * gradientWeight U₀ (latticeSample n δ)) <
      η * ((∑' γ, a₀ γ) / (n : ℝ) ^ 2) := by
    rw [← mul_div_assoc, lt_div_iff₀ (sq_pos_of_pos hnf), mul_comm]
    exact (div_lt_div_iff_of_pos_right (pow_pos hnf k)).mp (by simpa only [mul_div_assoc] using he)
  have ha : Function.HasFiniteSupport a₀ := by
    let bF := Pi.basisFun ℝ (Fin k)
    have hbB : Bornology.IsBounded ((n : ℝ) • tsupport b) :=
      (hbc.isCompact.image (show Continuous fun x : Fin k → ℝ => (n : ℝ) • x by fun_prop)).isBounded
    have hinj : Function.Injective v₀ := fun x y h => funext fun j => by
      have he : (x j : ℝ) = (y j : ℝ) := congr_fun h j; exact_mod_cast he
    refine ((ZSpan.setFinite_inter bF hbB).preimage hinj.injOn).subset fun γ hγ =>
      ⟨⟨latticeSample n γ, subset_closure hγ, ?_⟩, ?_⟩
    · ext j; change (n : ℝ) * ((γ j : ℝ) / n) = (γ j : ℝ); field_simp
    · exact (bF.mem_span_iff_repr_mem ℤ _).mpr fun j => ⟨γ j, by simp [bF, v₀]⟩
  let E := ha.toFinset
  let : Fintype E := inferInstance
  let w₁ (δ : Lattice k) := gradientWeight U₀ (latticeSample n δ)
  let t := (n : ℝ) ^ 2
  let K' := S + E
  let ext (d : E → ℝ) (γ : Lattice k) := if h : γ ∈ E then d ⟨γ, h⟩ else 0
  let ζf (d : E → ℝ) := (∑ γ : E, d γ) / t
  let N (d : E → ℝ) := ∑ δ ∈ K', max (-(∑ γ ∈ S, q γ * ext d (δ - γ))) 0 * w₁ δ
  have hζf : Continuous ζf := by unfold ζf; fun_prop
  have hExt (γ : Lattice k) : Continuous (fun d : E → ℝ => ext d γ) := by dsimp [ext]; split_ifs <;> fun_prop
  have hN' : Continuous N := by unfold N; fun_prop
  have hNeg (d : E → ℝ) : (∑' δ, max (-(∑ γ ∈ S, q γ * ext d (δ - γ))) 0 * w₁ δ) = N d :=
    tsum_eq_sum fun δ hδ => by
      have hz' : ∑ γ ∈ S, q γ * ext d (δ - γ) = 0 :=
        Finset.sum_eq_zero fun γ hγ => by
          have hE : δ - γ ∉ E := fun h => hδ (Finset.mem_add.mpr ⟨γ, hγ, δ - γ, h, by abel⟩)
          simp [ext, hE]
      simp [hz']
  let aE : E → ℝ := fun γ => a₀ γ
  have haE : ext aE = a₀ := funext fun γ => by
    dsimp [ext, aE]; split_ifs with h
    · rfl
    · exact (not_not.mp fun hh => h (ha.mem_toFinset.mpr hh)).symm
  have hsum : ∑ γ : E, aE γ = ∑' γ, a₀ γ := by
    rw [Finset.sum_coe_sort E a₀, tsum_eq_sum fun γ hγ => Function.notMem_support.mp (ha.mem_toFinset.not.mp hγ)]
  have hpE : 0 < ζf aE := by change 0 < (∑ γ : E, aE γ) / t; rw [hsum]; exact div_pos hp' (sq_pos_of_pos hnf)
  have hnE : N aE < η * ζf aE := by change N aE < η * ((∑ γ : E, aE γ) / t); rw [← hNeg, haE, hsum]; exact han
  have hDense : DenseRange (fun (q' : E → ℚ) (i : E) => (q' i : ℝ)) := DenseRange.piMap fun _ => Rat.denseRange_cast
  have hopen : IsOpen {d : E → ℝ | 0 < ζf d ∧ N d < η * ζf d} :=
    (isOpen_lt continuous_const hζf).inter (isOpen_lt hN' (continuous_const.mul hζf))
  obtain ⟨q', hq0, hqN⟩ := hDense.exists_mem_open hopen ⟨aE, hpE, hnE⟩
  let p : LatticeRing k := ∑ γ : E, AddMonoidAlgebra.single γ.val (q' γ)
  have hp_coeff (γ : Lattice k) : (p.coeff γ : ℝ) = ext (fun i => (q' i : ℝ)) γ := by
    simp only [p, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Rat.cast_sum]
    by_cases h : γ ∈ E
    · rw [Finset.sum_eq_single ⟨γ, h⟩]
      · simp [ext, h]
      · intro β _ hne; simp [show β.val ≠ γ from fun he => hne (Subtype.ext he)]
      · simp
    · simp [ext, h, show ∀ β : E, β.val ≠ γ from fun β hb => h (hb ▸ β.2)]
  have hpMass : ((mass p : ℚ) : ℝ) = ∑ γ : E, (q' γ : ℝ) := by simp [p]
  have hc_mul (δ : Lattice k) : ((ν * p).coeff δ : ℝ) = ∑ γ ∈ S, q γ * ext (fun i => (q' i : ℝ)) (δ - γ) := by
    rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum, Rat.cast_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    have he (β : Lattice k) : γ + β = δ ↔ β = δ - γ := ⟨fun h => eq_sub_iff_add_eq.mpr (by rw [add_comm, h]), fun h => by subst h; abel⟩
    simp only [Finsupp.sum, he, Finset.sum_ite_eq', ← hp_coeff, q]
    split_ifs with h
    · simp
    · simp [Finsupp.notMem_support_iff.mp h]
  let μ := ν * p
  let ζ : ℚ := mass p / (n : ℚ) ^ 2
  have hζ₀ : (ζ : ℝ) = ((mass p : ℚ) : ℝ) / (n : ℝ) ^ 2 := by simp [ζ]
  have hζ' : (0 : ℝ) < ζ := by simpa only [hζ₀, hpMass, ζf, t] using hq0
  have hcos (i : Fin s) : cosetMap (Λ i) μ = 0 := by simp [μ, map_mul, hcos₀ i]
  have hmom (j l : Fin k) : secondMoment j l μ / (n : ℚ) ^ 2 = ζ * C j l := by
    simp only [μ, secondMoment_mul, hzero, hfirst, hsecond, zero_mul, zero_add, add_zero]; dsimp [ζ]; ring
  have hneg : (∑' δ : Lattice k, max (-(μ.coeff δ : ℝ)) 0 * gradientWeight U₀ (latticeSample n δ)) < η * ζ := by
    simpa only [μ, hc_mul, hNeg, hζ₀, hpMass, ζf, t, w₁] using hqN
  let v (γ : Lattice k) : ℝ := ∑ j, (γ j : ℝ) / n * w j none
  let g (γ : Lattice k) (α : Fin d) : ℝ := ∑ j, U₀ α j * latticeSample n γ j
  have heval (i : Fin s) : μ.coeff.mapDomain (fun γ => v γ + ∑ α, a i α * g γ α) = 0 := by
    have heq : (fun γ => v γ + ∑ α, a i α * g γ α) =
        (fun y => QuotientAddGroup.lift (Λ i) (φ i) le_rfl y / (n : ℝ)) ∘ QuotientAddGroup.mk' (Λ i) := by
      ext γ
      simp only [Function.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk',
        φ, f, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
        Fintype.linearCombination_apply, map_sum, map_smul, rationalize, AddMonoidHom.coe_mk,
        Rat.smul_def, rowEvaluation, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_option,
        realAugmented, one_mul, v, g, U₀, latticeSample]
      change _ = (∑ j, (γ j : ℝ) * (w j none + ∑ α, a i α * w j (some α))) / n
      simp only [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun _ _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [heq, Finsupp.mapDomain_comp]
    change Finsupp.mapDomain _ (cosetMap (Λ i) μ).coeff = 0
    rw [hcos i]; simp
  have hmoment (α β : Fin d) : μ.coeff.sum (fun γ q => (q : ℝ) * g γ α * g γ β) =
      (ζ : ℝ) * if α = β then 1 else 0 := by
    have hm (j l : Fin k) : ∑ γ ∈ μ.coeff.support,
        (μ.coeff γ : ℝ) * latticeSample n γ j * latticeSample n γ l = (ζ : ℝ) * (C j l : ℝ) := by
      have h := congrArg (Rat.cast : ℚ → ℝ) (hmom j l)
      simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_mul, coefficientFunctional_eq_sum,
        Finsupp.sum, Rat.cast_sum, Rat.cast_intCast] at h
      rw [← h, Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by simp only [latticeSample]; ring
    simp only [g, Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    have hr (j l : Fin k) : (∑ γ ∈ μ.coeff.support,
        (μ.coeff γ : ℝ) * (U₀ α j * latticeSample n γ j) * (U₀ β l * latticeSample n γ l)) =
        U₀ α j * U₀ β l * ((ζ : ℝ) * (C j l : ℝ)) := by
      rw [← hm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [hr]
    have hU' := congrFun (congrFun hU α) β
    rw [Matrix.one_apply] at hU'
    rw [← hU']
    change _ = (ζ : ℝ) * ∑ l, (∑ j, U₀ α j * (C j l : ℝ)) * U₀ β l
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hnegative : μ.coeff.sum (fun γ q => max (-(q : ℝ)) 0 * ∑ α, (g γ α) ^ 2) < η * (ζ : ℝ) := by
    rw [tsum_eq_sum (s := μ.coeff.support)] at hneg
    · exact hneg
    · intro γ hγ; simp [Finsupp.notMem_support_iff.mp hγ]
  let f₀ := μ.coeff
  obtain ⟨M, z, hM, hz⟩ : ∃ (M : ℕ) (z : Lattice k →₀ ℤ), 0 < M ∧ ∀ x, (z x : ℝ) = M * (f₀ x : ℝ) := by
    let A : Matrix Unit ↥f₀.support ℚ := fun _ x => f₀ x
    refine ⟨A.den, f₀.mapRange (fun q => Int.floor ((A.den : ℚ) * q)) (by simp),
      Nat.pos_of_ne_zero A.den_ne_zero, fun x => ?_⟩
    suffices ((f₀.mapRange (fun q => Int.floor ((A.den : ℚ) * q)) (by simp) x : ℤ) : ℚ) = A.den * f₀ x by
      exact_mod_cast this
    by_cases hx : x ∈ f₀.support
    · have hd0 : (A.den : ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
      have hn0 : (A.num () ⟨x, hx⟩ : ℚ) = A.den * f₀ x :=
        ((div_eq_iff hd0).mp (A.num_div_den () ⟨x, hx⟩)).trans (mul_comm _ _)
      simp only [Finsupp.mapRange_apply, ← hn0, Int.floor_intCast]
    · simp [Finsupp.notMem_support_iff.mp hx]
  have hn_cast (x : Lattice k) : (negativeCount z x : ℝ) = max (-(z x : ℝ)) 0 := by
    change ((-(z x)).toNat : ℝ) = _
    exact_mod_cast Int.toNat_eq_max (-z x)
  have hdiff₀ : (positiveCount z).mapRange (Nat.cast : ℕ → ℝ) (by simp) -
      (negativeCount z).mapRange (Nat.cast : ℕ → ℝ) (by simp) =
      (M : ℝ) • f₀.mapRange (Rat.cast : ℚ → ℝ) (by simp) := by
    ext x
    simp only [Finsupp.sub_apply, Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul,
      ← hz x, hn_cast]
    have hp : (positiveCount z x : ℝ) = max (z x : ℝ) 0 := by
      change ((z x).toNat : ℝ) = _; exact_mod_cast Int.toNat_eq_max (z x)
    rw [hp]
    by_cases h0 : 0 ≤ (z x : ℝ)
    · rw [max_eq_left h0, max_eq_right (neg_nonpos.mpr h0), sub_zero]
    · rw [max_eq_right (le_of_not_ge h0), max_eq_left (neg_nonneg.mpr (le_of_not_ge h0))]; ring
  let m := (positiveCount z).toMultiset
  let nₘ := (negativeCount z).toMultiset
  have hh (i : Fin s) : ∃ e : m ≃ nₘ, ∀ x : m,
      v (e x) + ∑ j, a i j * g (e x) j = v x + ∑ j, a i j * g x j := by
    let φ' (x : Lattice k) := v x + ∑ j, a i j * g x j
    have hmap : m.map φ' = nₘ.map φ' := by
      simp only [m, nₘ, Finsupp.toMultiset_map]
      congr 1
      apply Finsupp.mapRange_injective (Nat.cast : ℕ → ℝ) (by simp) Nat.cast_injective
      apply sub_eq_zero.mp
      rw [← Finsupp.mapDomain_mapRange φ' _ _ _ Nat.cast_add,
        ← Finsupp.mapDomain_mapRange φ' _ _ _ Nat.cast_add,
        ← Finsupp.mapDomain_sub, hdiff₀, Finsupp.mapDomain_smul,
        Finsupp.mapDomain_mapRange φ' _ _ _ Rat.cast_add, heval i]
      simp
    let e := (m.mapEquiv φ').trans ((Multiset.cast hmap).trans (nₘ.mapEquiv φ').symm)
    refine ⟨e, fun x => ?_⟩
    have hh := congrArg (fun y : nₘ.map φ' => (y : ℝ))
      ((nₘ.mapEquiv φ').apply_symm_apply ((Multiset.cast hmap) (m.mapEquiv φ' x)))
    simp only [Multiset.mapEquiv_apply] at hh
    exact hh.trans (Multiset.mapEquiv_apply m φ' x)
  choose e he using hh
  let e₀ := e ⟨0, hs⟩
  let c₀ := (Real.sqrt (M * (ζ : ℝ)))⁻¹
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hsq : c₀ ^ 2 * (M * (ζ : ℝ)) = 1 := by
    dsimp [c₀]; rw [inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  let U : Matrix (Fin d) m ℝ := fun j x => c₀ * g x j
  let V : Matrix (Fin d) m ℝ := fun j x => c₀ * g (e₀ x) j
  have hu (j l : Fin d) : (U * U.transpose) j l = c₀ ^ 2 * ∑ x : m, g x j * g x l := by
    change (∑ x : m, (c₀ * g x j) * (c₀ * g x l)) = _
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hv (j l : Fin d) : (V * V.transpose) j l = c₀ ^ 2 * ∑ x : nₘ, g x j * g x l := by
    change (∑ x : m, (c₀ * g (e₀ x) j) * (c₀ * g (e₀ x) l)) = _
    rw [← e₀.sum_comp fun x : nₘ => g x j * g x l, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hdiff : U * U.transpose - V * V.transpose = 1 := by
    ext j l
    simp only [Matrix.sub_apply, hu, hv, ← mul_sub]
    rw [sum_count_elements (positiveCount z) fun x => g x j * g x l,
      sum_count_elements (negativeCount z) fun x => g x j * g x l]
    have hs1 := congrArg (fun c : Lattice k →₀ ℝ => c.sum fun x q => q * (g x j * g x l)) hdiff₀
    rw [Finsupp.sum_sub_index fun x b d => sub_mul b d _,
      Finsupp.sum_mapRange_index (by simp), Finsupp.sum_mapRange_index (by simp),
      Finsupp.sum_smul_index (by simp), Finsupp.sum_mapRange_index (by simp)] at hs1
    rw [hs1]
    have hm := hmoment j l
    simp only [f₀, Finsupp.sum, ← Finset.mul_sum, mul_assoc] at hm ⊢
    rw [hm]
    calc c₀ ^ 2 * (M * ((ζ : ℝ) * if j = l then 1 else 0))
      _ = (c₀ ^ 2 * (M * (ζ : ℝ))) * if j = l then 1 else 0 := by ring
      _ = _ := by simp [hsq, Matrix.one_apply]
  have htrace : (V * V.transpose).trace < η := by
    have hn_eq : (negativeCount z).mapRange (Nat.cast : ℕ → ℝ) (by simp) =
        (M : ℝ) • f₀.mapRange (fun q : ℚ => max (-(q : ℝ)) 0) (by simp) := by
      ext x
      simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, hn_cast, hz,
        ← mul_neg, mul_max_of_nonneg _ _ (Nat.cast_nonneg M), mul_zero]
    have hs1 := congrArg (fun c : Lattice k →₀ ℝ => c.sum fun x q => q * ∑ j, (g x j) ^ 2) hn_eq
    rw [Finsupp.sum_mapRange_index (by simp), Finsupp.sum_smul_index (by simp),
      Finsupp.sum_mapRange_index (by simp)] at hs1
    have ht : (V * V.transpose).trace = c₀ ^ 2 * M * f₀.sum (fun x q => max (-(q : ℝ)) 0 * ∑ j, (g x j) ^ 2) := by
      change (∑ j, (V * V.transpose) j j) = _
      simp only [hv, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← sq]
      rw [sum_count_elements (negativeCount z) fun x => ∑ j, (g x j) ^ 2, hs1]
      simp only [Finsupp.sum, ← Finset.mul_sum, mul_assoc]
    rw [ht]
    have hc' : 0 < c₀ ^ 2 * M := mul_pos (sq_pos_of_ne_zero (by dsimp [c₀]; positivity)) hMp
    calc c₀ ^ 2 * M * _ < c₀ ^ 2 * M * (η * (ζ : ℝ)) := mul_lt_mul_of_pos_left hnegative hc'
      _ = c₀ ^ 2 * (M * (ζ : ℝ)) * η := by ring
      _ = η := by rw [hsq, one_mul]
  have hB : (V * V.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose V
  have hcompl : (η • (1 : Matrix (Fin d) (Fin d) ℝ) - V * V.transpose).PosSemidef := by
    let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℝ) hB.1.eigenvectorUnitary
    have hD : (diagonal fun i => η - hB.1.eigenvalues i).PosSemidef :=
      posSemidef_diagonal_iff.mpr fun i => sub_nonneg.mpr <| by
        refine le_trans ?_ htrace.le
        rw [hB.1.trace_eq_sum_eigenvalues]
        simpa using Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i)
    have hd : e (diagonal fun i => η - hB.1.eigenvalues i) = η • 1 - V * V.transpose := by
      have hr : (diagonal fun i => η - hB.1.eigenvalues i) =
          η • (1 : Matrix (Fin d) (Fin d) ℝ) - diagonal hB.1.eigenvalues := by
        ext i j; by_cases h : i = j <;> simp [h]
      rw [hr, map_sub, map_smul, map_one]; congr 1; exact hB.1.spectral_theorem.symm
    rw [← hd]; exact hD.mul_mul_conjTranspose_same _
  let R := CFC.sqrt (η • (1 : Matrix (Fin d) (Fin d) ℝ) - V * V.transpose)
  have hR : R * R.transpose = η • 1 - V * V.transpose := by
    have hr : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hr.1.eq]
    exact CFC.sqrt_mul_sqrt_self _ hcompl.nonneg
  let c := (Real.sqrt (1 + η))⁻¹
  have he' (A : Matrix (Fin d) m ℝ) :
      (c • A.fromCols R) * (c • A.fromCols R).transpose = (1 / (1 + η)) • (A * A.transpose + R * R.transpose) := by
    have hg : A.fromCols R * (A.fromCols R).transpose = A * A.transpose + R * R.transpose := by
      ext i j; simp [Matrix.mul_apply, Matrix.fromCols, Matrix.transpose_apply, Fintype.sum_sum_type]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hg]
    congr 1; dsimp [c]; rw [← _root_.mul_inv_rev, ← sq, Real.sq_sqrt (by linarith)]; simp
  let Up := c • U.fromCols R
  let Un := c • V.fromCols R
  have hR1 : Up * Up.transpose = (1 : ℝ) • 1 := by
    rw [he' U, hR, show U * U.transpose + (η • 1 - V * V.transpose) = (1 + η) • 1 by
      rw [add_smul, one_smul, ← hdiff]; abel, smul_smul, one_div_mul_cancel (by linarith)]
  have hR2 : Un * Un.transpose = (η / (1 + η)) • 1 := by
    rw [he' V, hR, add_sub_cancel, smul_smul]; congr 1; ring
  let cp (x : m ⊕ Fin d) : ℝ := c * Sum.elim (fun (y : m) => c₀ * v y) (fun _ => 0) x
  let cn (x : m ⊕ Fin d) : ℝ := c * Sum.elim (fun (y : m) => c₀ * v (e₀ y)) (fun _ => 0) x
  let ip (i : Fin s) (x : m ⊕ Fin d) := cp x + ∑ j, a i j * Up j x
  let ineg (i : Fin s) (x : m ⊕ Fin d) := cn x + ∑ j, a i j * Un j x
  let ℓ := Fintype.card (m ⊕ Fin d)
  let eqF := Fintype.equivFin (m ⊕ Fin d)
  refine ⟨ℓ,
    fun i => WithLp.toLp 2 fun x => ip i (eqF.symm x),
    fun i => WithLp.toLp 2 fun x => ineg i (eqF.symm x),
    fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, WithLp.ofLp_sub, Pi.sub_apply]
    rw [eqF.symm.sum_comp fun x => (ip i x - ip j x) ^ 2, row_gram_distance cp Up 1 hR1 (a i) (a j), one_mul]
  · simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, WithLp.ofLp_sub, Pi.sub_apply]
    rw [eqF.symm.sum_comp fun x => (ineg i x - ineg j x) ^ 2, row_gram_distance cn Un (η / (1 + η)) hR2 (a i) (a j)]
  · refine ⟨eqF.symm.trans ((Equiv.sumCongr ((e i).trans e₀.symm) (Equiv.refl _)).trans eqF), fun x => ?_⟩
    change ineg i (eqF.symm (eqF (Equiv.sumCongr ((e i).trans e₀.symm) (Equiv.refl _) (eqF.symm x)))) = ip i (eqF.symm x)
    rw [eqF.symm_apply_apply]
    generalize eqF.symm x = z
    rcases z with y | y
    · have hσ : c₀ * v (e₀ (((e i).trans e₀.symm) y)) + ∑ j, a i j * V j (((e i).trans e₀.symm) y) =
          c₀ * v y + ∑ j, a i j * U j y := by
        simpa only [U, V, Equiv.trans_apply, e₀.apply_symm_apply, Finset.mul_sum, mul_add, mul_assoc,
          mul_left_comm (a i _)] using congrArg (c₀ * ·) (he i y)
      simpa only [ineg, ip, cn, cp, Up, Un, Equiv.sumCongr_apply, Sum.map_inl, Sum.elim_inl,
        Matrix.smul_apply, Matrix.fromCols_apply_inl, smul_eq_mul, Finset.mul_sum, mul_add,
        mul_assoc, mul_left_comm (a i _)] using congrArg (c * ·) hσ
    · simp [ineg, ip, cn, cp, Up, Un]

end
end OAI.EuclideanRamsey
