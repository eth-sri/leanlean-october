module

public import OAI.Combinatorics.EuclideanRamsey.TensorNecessity
public import OAI.Combinatorics.EuclideanRamsey.StencilConvolution

@[expose] public section

namespace OAI

noncomputable section
open scoped TensorProduct BigOperators MatrixOrder
open Matrix Finset

namespace EuclideanRamsey

abbrev Lattice (k : ℕ) := Fin k → ℤ
abbrev RationalSpace (k : ℕ) := Fin k → ℚ
abbrev LatticeRing (k : ℕ) := AddMonoidAlgebra ℚ (Lattice k)

def rationalize {k : ℕ} : Lattice k →+ RationalSpace k where
  toFun γ j := γ j
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

def latticeSpan {k : ℕ} (Λ : AddSubgroup (Lattice k)) : Submodule ℚ (RationalSpace k) :=
  Submodule.span ℚ (rationalize '' (Λ : Set (Lattice k)))

def matrixTensor {k : ℕ} (C : Matrix (Fin k) (Fin k) ℚ) : RationalSpace k ⊗[ℚ] RationalSpace k :=
  ∑ a, ∑ b, C a b • (Pi.single a (1 : ℚ) ⊗ₜ[ℚ] Pi.single b (1 : ℚ))

instance latticeNoetherian {k : ℕ} : IsNoetherianRing (LatticeRing k) :=
  Algebra.FiniteType.isNoetherianRing ℚ (LatticeRing k)

def augmentation {k : ℕ} : LatticeRing k →ₐ[ℚ] ℚ := AddMonoidAlgebra.lift ℚ ℚ (Lattice k) 1

def cf {k : ℕ} (g : Lattice k → ℚ) : LatticeRing k →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ g).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

abbrev mass {k : ℕ} (ν : LatticeRing k) : ℚ := augmentation ν
abbrev firstMoment {k : ℕ} (ν : LatticeRing k) (a : Fin k) : ℚ := cf (fun γ => γ a) ν
abbrev secondMoment {k : ℕ} (ν : LatticeRing k) (a b : Fin k) : ℚ := cf (fun γ => (γ a : ℚ) * γ b) ν

@[simp] lemma cf_single {k : ℕ} (g : Lattice k → ℚ) (γ : Lattice k) (q : ℚ) :
    cf g (AddMonoidAlgebra.single γ q) = q * g γ := by
  simp [cf, Finsupp.linearCombination_apply]

@[simp] lemma aug_single {k : ℕ} (γ : Lattice k) (q : ℚ) :
    augmentation (AddMonoidAlgebra.single γ q) = q := by
  simp [augmentation]

lemma firstMoment_mul {k : ℕ} (x y : LatticeRing k) (a : Fin k) :
    firstMoment (x * y) a = mass x * firstMoment y a + firstMoment x a * mass y := by
  induction x using AddMonoidAlgebra.induction_on with
  | «of» γ =>
    induction y using AddMonoidAlgebra.induction_on with
    | «of» δ => simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single]; ring
    | add _ _ h1 h2 => simp only [mul_add, map_add, h1, h2]; ring
    | smul r _ h1 => simp only [mul_smul_comm, map_smul, smul_eq_mul, h1]; ring
  | add _ _ h1 h2 => simp only [add_mul, map_add, h1, h2]; ring
  | smul r _ h1 => simp only [smul_mul_assoc, map_smul, smul_eq_mul, h1]; ring

lemma secondMoment_mul {k : ℕ} (x y : LatticeRing k) (a b : Fin k) :
    secondMoment (x * y) a b = mass x * secondMoment y a b + secondMoment x a b * mass y +
      firstMoment x a * firstMoment y b + firstMoment x b * firstMoment y a := by
  induction x using AddMonoidAlgebra.induction_on with
  | «of» γ =>
    induction y using AddMonoidAlgebra.induction_on with
    | «of» δ => simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single]; ring
    | add _ _ h1 h2 => simp only [mul_add, map_add, h1, h2]; ring
    | smul r _ h1 => simp only [mul_smul_comm, map_smul, smul_eq_mul, h1]; ring
  | add _ _ h1 h2 => simp only [add_mul, map_add, h1, h2]; ring
  | smul r _ h1 => simp only [smul_mul_assoc, map_smul, smul_eq_mul, h1]; ring

def augIdeal {k : ℕ} : Ideal (LatticeRing k) := RingHom.ker augmentation

lemma moments_vanish_on_powers {k : ℕ} :
    (∀ x ∈ (augIdeal : Ideal (LatticeRing k)) ^ 2, ∀ a, firstMoment x a = 0) ∧
    (∀ x ∈ (augIdeal : Ideal (LatticeRing k)) ^ 3, mass x = 0 ∧
      (∀ a, firstMoment x a = 0) ∧ ∀ a b, secondMoment x a b = 0) := by
  let J1 : Ideal (LatticeRing k) :=
    { carrier := {x | mass x = 0 ∧ ∀ a, firstMoment x a = 0}
      zero_mem' := by simp
      add_mem' := fun hx hy => ⟨by simp [hx.1, hy.1], fun a => by simp [hx.2 a, hy.2 a]⟩
      smul_mem' := fun r x hx => ⟨by change mass (r * x) = 0; simp [hx.1],
        fun a => by change firstMoment (r * x) a = 0; simp [firstMoment_mul, hx.1, hx.2 a]⟩ }
  have h2 : (augIdeal : Ideal (LatticeRing k)) ^ 2 ≤ J1 := by
    rw [sq, Ideal.mul_le]; intro x hx y hy
    exact ⟨by change mass (x * y) = 0; simp [show mass x = 0 from hx],
      fun a => by simp [firstMoment_mul, show mass x = 0 from hx, show mass y = 0 from hy]⟩
  let J2 : Ideal (LatticeRing k) :=
    { carrier := {x | mass x = 0 ∧ (∀ a, firstMoment x a = 0) ∧ ∀ a b, secondMoment x a b = 0}
      zero_mem' := by simp
      add_mem' := fun hx hy => ⟨by simp [hx.1, hy.1], fun a => by simp [hx.2.1 a, hy.2.1 a],
        fun a b => by simp [hx.2.2 a b, hy.2.2 a b]⟩
      smul_mem' := fun r x hx => ⟨by change mass (r * x) = 0; simp [hx.1],
        fun a => by change firstMoment (r * x) a = 0; simp [firstMoment_mul, hx.1, hx.2.1 a],
        fun a b => by change secondMoment (r * x) a b = 0; simp [secondMoment_mul, hx.1, hx.2.1, hx.2.2 a b]⟩ }
  have h3 : (augIdeal : Ideal (LatticeRing k)) ^ 3 ≤ J2 := by
    rw [show 3 = 2 + 1 from rfl, pow_succ', Ideal.mul_le]; intro x hx y hy
    obtain ⟨hy0, hy1⟩ := h2 hy
    exact ⟨by change mass (x * y) = 0; simp [show mass x = 0 from hx],
      fun a => by simp [firstMoment_mul, show mass x = 0 from hx, hy0],
      fun a b => by simp [secondMoment_mul, show mass x = 0 from hx, hy0, hy1]⟩
  exact ⟨fun x hx => (h2 hx).2, fun x hx => h3 hx⟩

section Nilpotent
variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma nil_exp_sub_one_sub_mem {J : Ideal R} {a : R} (ha : IsNilpotent a) (hJ : a ∈ J) :
    IsNilpotent.exp a - 1 - a ∈ J ^ 2 := by
  obtain ⟨n, hn⟩ := ha
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_add_right n 2) hn), show n + 2 = 2 + n by omega, sum_range_add,
    show (∑ i ∈ range 2, (i.factorial : ℚ)⁻¹ • a ^ i) = 1 + a by simp [sum_range_succ],
    show 1 + a + (∑ x ∈ range n, ((2 + x).factorial : ℚ)⁻¹ • a ^ (2 + x)) - 1 - a =
      ∑ x ∈ range n, ((2 + x).factorial : ℚ)⁻¹ • a ^ (2 + x) by ring]
  refine Submodule.sum_mem _ fun _ _ => ?_
  rw [Algebra.smul_def, pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hJ 2))

lemma nil_exp_eq_one {a : R} (ha : IsNilpotent a) (h : IsNilpotent.exp a = 1) : a = 0 := by
  obtain ⟨n, hn⟩ := ha
  let c : R := ∑ i ∈ range n, ((2 + i).factorial : ℚ)⁻¹ • a ^ i
  have hb : IsNilpotent (a * c) := ⟨n, by rw [mul_pow, hn, zero_mul]⟩
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_add_right n 2) hn),
    show n + 2 = 2 + n by omega, sum_range_add,
    show (∑ i ∈ range 2, (i.factorial : ℚ)⁻¹ • a ^ i) = 1 + a by simp [sum_range_succ],
    show (∑ i ∈ range n, ((2 + i).factorial : ℚ)⁻¹ • a ^ (2 + i)) = a ^ 2 * c by
      simp only [c, mul_sum, pow_add, mul_smul_comm]] at h
  exact hb.isUnit_one_add.mul_right_cancel (by linear_combination h)

lemma nil_ideal_exp_surjective {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥) {z : R} (hz : z ∈ I) :
    ∃ x ∈ I, IsNilpotent.exp x = 1 + z := by
  have nil_mem {y : R} (hy : y ∈ I) : IsNilpotent y := ⟨n, by simpa [hI] using Ideal.pow_mem_pow hy n⟩
  have happrox (k : ℕ) : ∃ x ∈ I, IsNilpotent.exp x - (1 + z) ∈ I ^ (k + 1) := by
    induction k with
    | zero => exact ⟨0, I.zero_mem, by simpa using I.neg_mem hz⟩
    | succ k ih =>
      obtain ⟨x, hx, he⟩ := ih
      let e := 1 + z - IsNilpotent.exp x
      have he' : e ∈ I ^ (k + 1) := by simpa [e, neg_sub] using (I ^ (k + 1)).neg_mem he
      have hei : e ∈ I := Ideal.pow_le_self (by omega) he'
      have hnx := nil_mem hx; have hne := nil_mem hei
      refine ⟨x + e, I.add_mem hx hei, ?_⟩
      rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hne]
      have hr : IsNilpotent.exp e - 1 - e ∈ I ^ (k + 2) :=
        (by rw [← pow_mul]; exact Ideal.pow_le_pow_right (by omega) : (I ^ (k + 1)) ^ 2 ≤ I ^ (k + 2))
          (nil_exp_sub_one_sub_mem hne he')
      have hx1 : IsNilpotent.exp x - 1 ∈ I := by
        simpa using I.add_mem (Ideal.pow_le_self (by omega) (nil_exp_sub_one_sub_mem hnx hx)) hx
      convert (I ^ (k + 2)).add_mem (by simpa [pow_succ'] using Ideal.mul_mem_mul hx1 he')
        (Ideal.mul_mem_left _ (IsNilpotent.exp x) hr) using 1
      dsimp only [e]; ring
  obtain ⟨x, hx, he⟩ := happrox n
  rw [show I ^ (n + 1) = ⊥ by simp [pow_succ, hI], Ideal.mem_bot, sub_eq_zero] at he
  exact ⟨x, hx, he⟩

end Nilpotent

lemma adic_intersection_lifting {R : Type*} [CommRing R] [IsNoetherianRing R]
    {ι : Type*} [Fintype ι] (I : Ideal R) (J : ι → Ideal R) (q : ℕ) :
    ∃ n : ℕ, ∀ x : R, (∀ i, x ∈ J i ⊔ I ^ n) → ∃ y : R, (∀ i, y ∈ J i) ∧ x - y ∈ I ^ q := by
  classical
  let f : R →ₗ[R] ∀ i, R ⧸ J i := LinearMap.pi fun i => Algebra.linearMap R (R ⧸ J i)
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k + q, fun x hx => ?_⟩
  have hfx : f x ∈ I ^ (k + q) • (⊤ : Submodule R (∀ i, R ⧸ J i)) ⊓ LinearMap.range f := by
    refine ⟨?_, x, rfl⟩
    choose z hz he using fun i => show ∃ z ∈ I ^ (k + q), Ideal.Quotient.mk (J i) z = Ideal.Quotient.mk (J i) x from
      let ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hx i)
      ⟨z, hz, by rw [← hyz, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, zero_add]⟩
    rw [show f x = ∑ i, z i • Pi.single i (1 : R ⧸ J i) by
      simp_rw [← Pi.single_smul, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, he]
      exact (Finset.univ_sum_single _).symm]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hz i) Submodule.mem_top
  rw [hk (k + q) (by omega), Nat.add_sub_cancel_left] at hfx
  have hm : I ^ q • LinearMap.range f = Submodule.map f (I ^ q • ⊤) := by rw [Submodule.map_smul'']; simp
  have hle : I ^ q • (I ^ k • ⊤ ⊓ LinearMap.range f) ≤ I ^ q • LinearMap.range f := smul_mono_right _ inf_le_right
  obtain ⟨z, hz, he⟩ : f x ∈ Submodule.map f (I ^ q • ⊤) := hm ▸ hle hfx
  exact ⟨x - z, fun i => Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (by rw [map_sub, he, sub_self] : f (x - z) = 0) i),
    by simpa [Ideal.smul_eq_mul] using hz⟩

theorem finite_lattice_identity {k s : ℕ} (φ : Fin s → Lattice k →+ ℝ) (C : Matrix (Fin k) (Fin k) ℚ)
    (hCs : C.IsSymm) (hC : ∀ i, TensorProduct.map (latticeSpan (φ i).ker).mkQ (latticeSpan (φ i).ker).mkQ (matrixTensor C) = 0) :
    ∃ ν : LatticeRing k, (∀ i, AddMonoidAlgebra.mapDomain (φ i) ν = 0) ∧ mass ν = 0 ∧
      (∀ a, firstMoment ν a = 0) ∧ ∀ a b, secondMoment ν a b = C a b := by
  classical
  let I : Ideal (LatticeRing k) := augIdeal
  let cosIdeal (i : Fin s) : Ideal (LatticeRing k) :=
    RingHom.ker (AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (φ i))
  obtain ⟨n, hn⟩ := adic_intersection_lifting I cosIdeal 3
  let N := n + 3
  let qN := Ideal.Quotient.mk (I ^ N)
  let M := Ideal.map qN I
  have hMN : M ^ N = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have hex (a : Fin k) : ∃ la ∈ I, IsNilpotent.exp (qN la) = qN (AddMonoidAlgebra.single (Pi.single a 1) 1) := by
    obtain ⟨x, hxM, hexp⟩ := nil_ideal_exp_surjective hMN
      (Ideal.mem_map_of_mem qN (show mass (AddMonoidAlgebra.single (Pi.single a 1) 1 - 1) = 0 by simp))
    obtain ⟨la, hlaI, rfl⟩ := (Ideal.mem_map_iff_of_surjective qN Ideal.Quotient.mk_surjective).mp hxM
    exact ⟨la, hlaI, by simpa [map_sub] using hexp⟩
  choose l hlI hlexp using hex
  have hnil_la (a : Fin k) : IsNilpotent (qN (l a)) :=
    ⟨N, Ideal.mem_bot.mp (hMN ▸ Ideal.pow_mem_pow (Ideal.mem_map_of_mem qN (hlI a)) N)⟩
  have hfirst_l (a b : Fin k) : firstMoment (l a) b = if a = b then 1 else 0 := by
    let z : LatticeRing k := AddMonoidAlgebra.single (Pi.single a 1) 1 - 1
    have hdiff : l a - z ∈ I ^ 2 := by
      have hpre : Ideal.comap qN (Ideal.map qN (I ^ 2)) = I ^ 2 := by
        rw [Ideal.comap_map_of_surjective' qN Ideal.Quotient.mk_surjective,
          show RingHom.ker qN = I ^ N by ext; exact Ideal.Quotient.eq_zero_iff_mem]
        exact sup_eq_left.mpr (Ideal.pow_le_pow_right (by omega))
      rw [← hpre, Ideal.mem_comap, Ideal.map_pow]
      convert (M ^ 2).neg_mem (nil_exp_sub_one_sub_mem (hnil_la a) (Ideal.mem_map_of_mem qN (hlI a))) using 1
      dsimp only [z, qN]; rw [hlexp, map_sub, map_sub, map_one]; ring
    have hj : firstMoment (l a) b = firstMoment z b :=
      sub_eq_zero.mp (by simpa only [firstMoment, map_sub] using moments_vanish_on_powers.1 _ hdiff b)
    rw [hj]; simp [z, firstMoment, show (1 : LatticeRing k) = AddMonoidAlgebra.single 0 1 from rfl, Pi.single_apply, eq_comm]
  let st : LatticeRing k := (1 / 2 : ℚ) • ∑ a, ∑ b, C a b • (l a * l b)
  have hx (i : Fin s) : st ∈ cosIdeal i ⊔ I ^ n := by
    apply sup_le_sup_left (Ideal.pow_le_pow_right (show n ≤ N by omega)) (cosIdeal i)
    let J := cosIdeal i ⊔ I ^ N
    let qJ := Ideal.Quotient.mk J
    let ψ := Ideal.Quotient.factorₐ ℚ (le_sup_right : I ^ N ≤ J)
    let MJ := Ideal.map qJ I
    have hMJ_nil {x : LatticeRing k ⧸ J} (hx : x ∈ MJ) : IsNilpotent x := ⟨N, Ideal.mem_bot.mp <| by
      have hm : MJ ^ N = ⊥ := by
        rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
        exact le_sup_right.trans fun _ h => Ideal.Quotient.eq_zero_iff_mem.mpr h
      exact hm ▸ Ideal.pow_mem_pow hx N⟩
    let eu : MJ →+ Additive (LatticeRing k ⧸ J)ˣ :=
      { toFun := fun x => Additive.ofMul ⟨IsNilpotent.exp x.1, IsNilpotent.exp (-x.1),
          by rw [← IsNilpotent.exp_add_of_commute (Commute.all _ _) (hMJ_nil x.2) (hMJ_nil x.2).neg, add_neg_cancel, IsNilpotent.exp_zero],
          by rw [← IsNilpotent.exp_add_of_commute (Commute.all _ _) (hMJ_nil x.2).neg (hMJ_nil x.2), neg_add_cancel, IsNilpotent.exp_zero]⟩
        map_zero' := congrArg Additive.ofMul (Units.ext IsNilpotent.exp_zero)
        map_add' := fun x y => congrArg Additive.ofMul (Units.ext (IsNilpotent.exp_add_of_commute (Commute.all _ _) (hMJ_nil x.2) (hMJ_nil y.2))) }
    let qu : Lattice k →+ Additive (LatticeRing k ⧸ J)ˣ :=
      { toFun := fun γ => Additive.ofMul ⟨qJ (AddMonoidAlgebra.single γ 1), qJ (AddMonoidAlgebra.single (-γ) 1),
          by rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]; exact qJ.map_one,
          by rw [← map_mul, AddMonoidAlgebra.single_mul_single, neg_add_cancel, mul_one]; exact qJ.map_one⟩
        map_zero' := congrArg Additive.ofMul (Units.ext qJ.map_one)
        map_add' := fun _ _ => congrArg Additive.ofMul (Units.ext (by
          change qJ _ = qJ _ * qJ _; rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one])) }
    let rM (a : Fin k) : MJ := ⟨qJ (l a), Ideal.mem_map_of_mem qJ (hlI a)⟩
    have heu_rM (a : Fin k) : eu (rM a) = qu (Pi.single a 1) := congrArg Additive.ofMul <| Units.ext <| by
      change IsNilpotent.exp (ψ (qN (l a))) = qJ (AddMonoidAlgebra.single (Pi.single a 1) 1)
      rw [← (hnil_la a).map_exp ψ, hlexp]; rfl
    let g : RationalSpace k →ₗ[ℚ] (LatticeRing k ⧸ J) := Fintype.linearCombination ℚ fun a => (rM a).1
    have hg_ker : latticeSpan (φ i).ker ≤ LinearMap.ker g := Submodule.span_le.mpr <| by
      rintro _ ⟨γ, hγ : φ i γ = 0, rfl⟩
      let S : MJ := ∑ a, γ a • rM a
      have heq : eu S = qu γ := by
        rw [map_sum]; simp_rw [map_zsmul, heu_rM, ← map_zsmul, ← map_sum,
          show (∑ a : Fin k, γ a • Pi.single a (1 : ℤ)) = γ by ext b; simp [Pi.single_apply]]
      have hmem : AddMonoidAlgebra.single γ (1 : ℚ) - 1 ∈ J := Ideal.mem_sup_left <| by
        change AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (φ i) _ = 0
        rw [map_sub, map_one, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single, hγ]
        exact sub_self _
      have hexp1 : IsNilpotent.exp (S : LatticeRing k ⧸ J) = 1 :=
        (congrArg (fun u : Additive (LatticeRing k ⧸ J)ˣ => ((Additive.toMul u : (LatticeRing k ⧸ J)ˣ) : LatticeRing k ⧸ J)) heq).trans
          (by simpa [qu, sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
      change g (rationalize γ) = 0
      rw [show g (rationalize γ) = (S : LatticeRing k ⧸ J) by
        simp [S, g, Fintype.linearCombination_apply, rationalize, Int.cast_smul_eq_zsmul]]
      exact nil_exp_eq_one (hMJ_nil S.2) hexp1
    let u := (latticeSpan (φ i).ker).liftQ g hg_ker
    let Φ := (Algebra.TensorProduct.lmul' ℚ : (LatticeRing k ⧸ J) ⊗[ℚ] _ →ₐ[ℚ] _).toLinearMap.comp (TensorProduct.map u u)
    have hquad : (∑ a, ∑ b, C a b • ((rM a).1 * (rM b).1)) = 0 := by simpa [Φ, u, matrixTensor, g] using congrArg Φ (hC i)
    rw [← Ideal.Quotient.eq_zero_iff_mem]; change Ideal.Quotient.mkₐ ℚ J st = 0
    simp only [st, map_smul, map_sum, map_mul]; exact smul_eq_zero_of_right _ hquad
  obtain ⟨y, hy, hxy⟩ := hn st hx
  obtain ⟨hm0, hf0, hs0⟩ := moments_vanish_on_powers.2 _ hxy
  refine ⟨y, hy, ?_, fun a => ?_, fun a b => ?_⟩
  · have hm' : mass st = mass y := sub_eq_zero.mp (by simpa only [mass, map_sub] using hm0)
    rw [← hm']; simp [st, mass, show ∀ a, augmentation (l a) = 0 from hlI]
  · have ha : firstMoment st a = firstMoment y a := sub_eq_zero.mp (by simpa only [firstMoment, map_sub] using hf0 a)
    rw [← ha]
    have h0 (c : Fin k) : mass (l c) = 0 := hlI c
    have hf_sum (x : Fin k → LatticeRing k) : firstMoment (∑ i, x i) a = ∑ i, firstMoment (x i) a := map_sum _ x univ
    have hf_smul (q : ℚ) (x : LatticeRing k) : firstMoment (q • x) a = q * firstMoment x a := by simp [firstMoment]
    simp [st, hf_smul, hf_sum, firstMoment_mul, h0]
  · have hab : secondMoment st a b = secondMoment y a b := sub_eq_zero.mp (by simpa only [secondMoment, map_sub] using hs0 a b)
    rw [← hab]
    have h0 (c : Fin k) : mass (l c) = 0 := hlI c
    have hs2 (x : Fin k → LatticeRing k) : secondMoment (∑ i, x i) a b = ∑ i, secondMoment (x i) a b := map_sum _ x univ
    have hsm2 (q : ℚ) (x : LatticeRing k) : secondMoment (q • x) a b = q * secondMoment x a b := by simp [secondMoment]
    simp only [st, hsm2, hs2, secondMoment_mul, h0, hfirst_l, zero_mul, mul_zero,
      zero_add, mul_add, sum_add_distrib, mul_ite, mul_one, sum_ite_eq', mem_univ, ite_true]
    rw [show C b a = C a b from congrFun (congrFun hCs a) b]; ring

abbrev AffineVector (d : ℕ) := Option (Fin d) → ℝ

def affineArray {d : ℕ} : (AffineVector d ⊗[ℚ] AffineVector d) ≃ₗ[ℚ] RealArray d :=
  (TensorProduct.piLeft ℚ (AffineVector d) fun _ : Option (Fin d) => ℝ).trans
    (LinearEquiv.piCongrRight fun _ => TensorProduct.piRight ℚ ℚ ℝ fun _ : Option (Fin d) => ℝ)

def rowEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : AffineVector d →ₗ[ℚ] ℝ where
  toFun w := ∑ α, realAugmented a i α * w α
  map_add' _ _ := by simp [mul_add, sum_add_distrib]
  map_smul' _ _ := by simp [Rat.smul_def, mul_left_comm, mul_sum]

theorem realCriterion_lattice {s d : ℕ} (a : Fin s → Space d) (h : RealCriterion a) :
    ∃ (k : ℕ) (w : Fin k → AffineVector d) (C : Matrix (Fin k) (Fin k) ℚ),
      C.IsSymm ∧
      (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)) * C.map (Rat.cast : ℚ → ℝ) *
        (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)).transpose = 1 ∧
      ∀ i, TensorProduct.map
        (latticeSpan (AddMonoidHom.ker (((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize))).mkQ
        (latticeSpan (AddMonoidHom.ker (((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize))).mkQ
        (matrixTensor C) = 0 := by
  classical
  obtain ⟨P, hP, hG⟩ := h
  let T : AffineVector d ⊗[ℚ] AffineVector d := affineArray.symm P
  have hT : affineArray T = P := affineArray.apply_symm_apply P
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset T
  let w₀ : ↥S ⊕ ↥S → AffineVector d := Sum.elim (fun z => z.1.1) fun z => z.1.2
  let C₀ : ↥S ⊕ ↥S → ↥S ⊕ ↥S → ℚ := fun j l => match j, l with
    | .inl i, .inr j | .inr i, .inl j => if i = j then 1 / 2 else 0
    | _, _ => 0
  let e := Fintype.equivFin (↥S ⊕ ↥S)
  let k := Fintype.card (↥S ⊕ ↥S)
  let w : Fin k → AffineVector d := fun j => w₀ (e.symm j)
  let C : Matrix (Fin k) (Fin k) ℚ := fun j l => C₀ (e.symm j) (e.symm l)
  have hC : C.IsSymm := by
    ext j l; change C₀ (e.symm l) (e.symm j) = C₀ (e.symm j) (e.symm l)
    rcases e.symm j with _ | _ <;> rcases e.symm l with _ | _ <;> simp [C₀, eq_comm]
  have hrep : (∑ j, ∑ l, C j l • (w j ⊗ₜ[ℚ] w l)) = (1 / 2 : ℚ) • (T + TensorProduct.comm ℚ _ _ T) := by
    have hs : (∑ j, ∑ l, C₀ j l • (w₀ j ⊗ₜ[ℚ] w₀ l)) = (1 / 2 : ℚ) • (T + TensorProduct.comm ℚ _ _ T) := by
      simp only [Fintype.sum_sum_type, C₀, w₀, zero_smul, sum_const_zero, zero_add, add_zero,
        ite_smul, Sum.elim_inl, Sum.elim_inr, sum_ite_eq, mem_univ, ite_true, hS, map_sum,
        TensorProduct.comm_tmul, smul_add, smul_sum]
      rw [Finset.sum_subtype S (fun _ => Iff.rfl) fun z => (1 / 2 : ℚ) • (z.1 ⊗ₜ[ℚ] z.2),
        Finset.sum_subtype S (fun _ => Iff.rfl) fun z => (1 / 2 : ℚ) • (z.2 ⊗ₜ[ℚ] z.1)]
    exact (Finset.sum_congr rfl fun j _ => e.symm.sum_comp fun l => C₀ (e.symm j) l • (w₀ (e.symm j) ⊗ₜ[ℚ] w₀ l)).trans
      ((e.symm.sum_comp fun j => ∑ l, C₀ j l • (w₀ j ⊗ₜ[ℚ] w₀ l)).trans hs)
  have hcomm_mul (Z : AffineVector d ⊗[ℚ] AffineVector d) :
      spatialMultiply (affineArray (TensorProduct.comm ℚ _ _ Z)) = (spatialMultiply (affineArray Z)).transpose := by
    ext α β
    change Algebra.TensorProduct.lmul' ℚ (affineArray (TensorProduct.comm ℚ _ _ Z) (some α) (some β)) =
      Algebra.TensorProduct.lmul' ℚ (affineArray Z (some β) (some α))
    have hc : affineArray (TensorProduct.comm ℚ _ _ Z) (some α) (some β) =
        TensorProduct.comm ℚ ℝ ℝ (affineArray Z (some β) (some α)) := by
      induction Z using TensorProduct.inductionOn with | tmul => rfl | add _ _ hx hy => simp [hx, hy]
    rw [hc]
    induction affineArray Z (some β) (some α) using TensorProduct.inductionOn with
    | tmul => simp [mul_comm] | add _ _ hx hy => simp [hx, hy]
  have hU : (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)) * C.map (Rat.cast : ℚ → ℝ) *
      (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)).transpose = 1 := by
    have hs1 : spatialMultiply (affineArray (∑ j, ∑ l, C j l • (w j ⊗ₜ[ℚ] w l))) = 1 := by
      rw [hrep, map_smul, map_add, map_smul, map_add, hcomm_mul, hT, hG]
      ext α β; simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.one_apply]
      by_cases hh : α = β <;> norm_num [hh, eq_comm, Rat.smul_def]
    refine Eq.trans ?_ hs1; ext α β
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, spatialMultiply, LinearMap.coe_mk]
    change ∑ l, (∑ j, w j (some α) * (C j l : ℝ)) * w l (some β) =
      ∑ j, ∑ l, (C j l : ℝ) * (w j (some α) * w l (some β))
    simp only [sum_mul]; rw [sum_comm]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  refine ⟨k, w, C, hC, hU, fun i => ?_⟩
  let f : RationalSpace k →ₗ[ℚ] ℝ := (rowEvaluation a i).comp (Fintype.linearCombination ℚ w)
  have hker : latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) = f.ker := by
    refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx => ?_
    · rintro _ ⟨γ, hγ, rfl⟩; exact hγ
    let A : Matrix Unit (Fin k) ℚ := fun _ j => x j
    let γ : Lattice k := fun j => A.num () j
    have hden : (A.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr A.den_ne_zero
    have he : rationalize γ = (A.den : ℚ) • x := by
      ext j; exact ((div_eq_iff hden).mp (A.num_div_den () j)).trans (mul_comm _ _)
    have hγ : γ ∈ AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize) := by
      change f (rationalize γ) = 0; rw [he, map_smul, hx, smul_zero]
    simpa [he, smul_smul, inv_mul_cancel₀ hden] using
      Submodule.smul_mem (latticeSpan _) (A.den : ℚ)⁻¹ (Submodule.subset_span ⟨γ, hγ, rfl⟩)
  rw [hker]
  let eqv := f.quotKerEquivRange
  let jMap : (RationalSpace k ⧸ f.ker) →ₗ[ℚ] ℝ := f.range.subtype.comp eqv.toLinearMap
  obtain ⟨r, hr⟩ := jMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (f.range.subtype_injective.comp eqv.injective))
  have hfam : TensorProduct.map (Fintype.linearCombination ℚ w) (Fintype.linearCombination ℚ w) (matrixTensor C) =
      ∑ j, ∑ l, C j l • (w j ⊗ₜ[ℚ] w l) := by
    simp only [matrixTensor, map_sum, map_smul, TensorProduct.map_tmul, Fintype.linearCombination_apply,
      Pi.single_apply, ite_smul, one_smul, zero_smul, sum_ite_eq', mem_univ, ite_true]
  have hev (Z : AffineVector d ⊗[ℚ] AffineVector d) :
      TensorProduct.map (rowEvaluation a i) (rowEvaluation a i) Z = arrayEvaluation a i (affineArray Z) := by
    induction Z using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [arrayEvaluation, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.map_tmul,
        rowEvaluation, TensorProduct.sum_tmul, TensorProduct.tmul_sum]
      change _ = ∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) * (x α ⊗ₜ[ℚ] y β) * (1 ⊗ₜ[ℚ] realAugmented a i β)
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]; rw [sum_comm]; simp only [mul_comm]
    | add _ _ hx hy => simp [hx, hy]
  have hcomm_ev : arrayEvaluation a i (affineArray (TensorProduct.comm ℚ _ _ T)) =
      TensorProduct.comm ℚ ℝ ℝ (arrayEvaluation a i (affineArray T)) := by
    rw [← hev, ← hev]; induction T using TensorProduct.inductionOn with | tmul => simp | add _ _ hx hy => simp [hx, hy]
  have hmap0 : TensorProduct.map f f (matrixTensor C) = 0 := by
    dsimp [f]; rw [TensorProduct.map_comp, LinearMap.comp_apply, hfam, hev, hrep, map_smul, map_add,
      map_smul, map_add, hcomm_ev, hT, hP i, map_zero, add_zero, smul_zero]
  have htmp : TensorProduct.map jMap jMap (TensorProduct.map f.ker.mkQ f.ker.mkQ (matrixTensor C)) = 0 := by
    rwa [← LinearMap.comp_apply, ← TensorProduct.map_comp, show jMap.comp f.ker.mkQ = f by ext; rfl]
  simpa only [map_zero, ← LinearMap.comp_apply, ← TensorProduct.map_comp, ← LinearMap.comp_assoc,
    hr, LinearMap.id_comp, TensorProduct.map_id, LinearMap.id_apply] using congrArg (TensorProduct.map r r) htmp

theorem realCriterion_two_scale {s d : ℕ} (a : Fin s → Space d)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (h : RealCriterion a) (η : ℝ) (hη : 0 < η) :
    ∃ (ℓ : ℕ) (f g : Fin s → Space ℓ),
      (∀ i j, ‖f i - f j‖ ^ 2 = ‖a i - a j‖ ^ 2) ∧
      (∀ i j, ‖g i - g j‖ ^ 2 = (η / (1 + η)) * ‖a i - a j‖ ^ 2) ∧
      ∀ i, ∃ σ : Equiv.Perm (Fin ℓ), ∀ x, g i (σ x) = f i x := by
  classical
  obtain ⟨k, w, C, hC, hU_eq, hquot⟩ := realCriterion_lattice a h
  let U₀ : Matrix (Fin d) (Fin k) ℝ := fun α j => w j (some α)
  let φ (i : Fin s) : Lattice k →+ ℝ :=
    ((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize
  obtain ⟨ν, hcos, hzero, hfirst, hsecond⟩ := finite_lattice_identity φ C hC hquot
  have hC' : (C.map (Rat.cast : ℚ → ℝ)).IsSymm := by
    ext j l; exact congrArg Rat.cast (congrFun (congrFun hC j) l)
  obtain ⟨n, p, hn, hp0, hneg0⟩ := exists_rational_stencil hd ν (C.map (Rat.cast : ℚ → ℝ)) U₀ hC' hU_eq
    (by simp [mass, augmentation, AddMonoidAlgebra.lift_apply] at hzero; exact_mod_cast hzero)
    (fun j => by exact_mod_cast (hfirst j : ν.coeff.sum (fun γ q => q * γ j) = 0))
    (fun j l => by
      have hjl : ν.coeff.sum (fun γ q => q * ((γ j : ℚ) * γ l)) = C j l := hsecond j l
      simpa [Finsupp.sum, mul_assoc] using congrArg (Rat.cast : ℚ → ℝ) hjl) hη
  let μ := ν * p
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hn)
  let ζ : ℝ := ((p.coeff.sum fun _ q => q : ℚ) : ℝ) / (n : ℝ) ^ 2
  have hζ : 0 < ζ := div_pos (by exact_mod_cast hp0) hn2
  have hneg : μ.coeff.sum (fun δ q => max (-(q : ℝ)) 0 * gradientWeight U₀ (latticeSample n δ)) < η * ζ := by
    simpa only [μ, ζ, mul_div_assoc] using (lt_div_iff₀' hn2).mpr hneg0
  let f : Lattice k →₀ ℚ := μ.coeff
  let v (γ : Lattice k) : ℝ := ∑ j, (γ j : ℝ) / n * w j none
  let g (γ : Lattice k) (α : Fin d) : ℝ := ∑ j, U₀ α j * latticeSample n γ j
  let A : Matrix Unit ↥f.support ℚ := fun _ x => f x
  let M : ℕ := A.den
  have hM : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero A.den_ne_zero)
  let z (γ : ↥f.support) : ℤ := A.num () γ
  have hz (γ : ↥f.support) : (z γ : ℚ) = M * f γ :=
    ((div_eq_iff (Nat.cast_ne_zero.mpr A.den_ne_zero)).mp (A.num_div_den () γ)).trans (mul_comm _ _)
  let zp (γ : ↥f.support) : ℕ := (z γ).toNat
  let zn (γ : ↥f.support) : ℕ := (-z γ).toNat
  have hzp_zn (γ : ↥f.support) : (zp γ : ℤ) - zn γ = z γ := by dsimp [zp, zn]; omega
  let mp := Σ γ : ↥f.support, Fin (zp γ)
  let mn := Σ γ : ↥f.support, Fin (zn γ)
  have hbij (i : Fin s) : ∃ e : mp ≃ mn, ∀ x : mp,
      v (e x).1 + ∑ α, a i α * g (e x).1 α = v x.1 + ∑ α, a i α * g x.1 α := by
    have hcos_i : Finsupp.mapDomain (φ i) f = 0 := by
      change (AddMonoidAlgebra.mapDomain (φ i) (ν * p)).coeff = 0
      rw [AddMonoidAlgebra.mapDomain_mul, hcos i, zero_mul]; rfl
    have hsum (r : ℝ) : (∑ γ : ↥f.support with φ i γ.1 = r, (zp γ : ℤ)) =
        ∑ γ : ↥f.support with φ i γ.1 = r, (zn γ : ℤ) := sub_eq_zero.mp <| by
      rw [← Finset.sum_sub_distrib]; simp_rw [hzp_zn]
      have hq0 : ((∑ γ : ↥f.support with φ i γ.1 = r, z γ : ℤ) : ℚ) = 0 := by
        push_cast; simp_rw [hz, ← Finset.mul_sum, Finset.sum_filter]
        have hf0 : (Finsupp.mapDomain (φ i) f) r = 0 := by rw [hcos_i]; rfl
        simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply] at hf0
        rw [Finset.sum_coe_sort f.support (fun x => if φ i x = r then f x else 0), hf0, mul_zero]
      exact_mod_cast hq0
    let fp (x : mp) : ℝ := φ i x.1.1
    let fn (x : mn) : ℝ := φ i x.1.1
    have hcard (m : ↥f.support → ℕ) (r : ℝ) : Fintype.card {x : Σ s, Fin (m s) // φ i x.1.1 = r} =
        ∑ s with φ i s.1 = r, m s := by
      rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sigma]; simp [Finset.sum_filter, apply_ite Finset.card]
    have heq (r : ℝ) : Fintype.card {x : mp // fp x = r} = Fintype.card {x : mn // fn x = r} := by
      dsimp [fp, fn, mp, mn]; rw [hcard zp r, hcard zn r]; exact_mod_cast hsum r
    let e := (Equiv.sigmaFiberEquiv fp).symm.trans
      ((Equiv.sigmaCongrRight fun r => Fintype.equivOfCardEq (heq r)).trans (Equiv.sigmaFiberEquiv fn))
    refine ⟨e, fun x => ?_⟩
    have hφ_eq : φ i (e x).1.1 = φ i x.1.1 := (Fintype.equivOfCardEq (heq (fp x)) ⟨x, rfl⟩).2
    have hevi (γ : Lattice k) : v γ + ∑ α, a i α * g γ α = φ i γ / n := by
      simp only [v, g, U₀, latticeSample, φ, AddMonoidHom.comp_apply,
        LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, Fintype.linearCombination_apply,
        map_sum, map_smul, show rationalize γ = fun j => (γ j : ℚ) from rfl, Rat.smul_def,
        rowEvaluation, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_option, realAugmented,
        one_mul, Rat.cast_intCast, div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => by ring) ?_
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hevi, hevi, hφ_eq]
  choose e he using hbij
  let e₀ := e ⟨0, hs⟩
  let c₀ := (Real.sqrt (M * ζ))⁻¹
  have hc₀_sq : c₀ ^ 2 * (M * ζ) = 1 := by
    rw [inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  let U : Matrix (Fin d) mp ℝ := fun α x => c₀ * g x.1.1 α
  let V : Matrix (Fin d) mp ℝ := fun α x => c₀ * g (e₀ x).1.1 α
  have hUV (α β : Fin d) : (U * U.transpose - V * V.transpose) α β = if α = β then 1 else 0 := by
    change (∑ x : mp, c₀ * g x.1.1 α * (c₀ * g x.1.1 β)) - (∑ x : mp, c₀ * g (e₀ x).1.1 α * (c₀ * g (e₀ x).1.1 β)) = _
    rw [e₀.sum_comp fun x : mn => c₀ * g x.1.1 α * (c₀ * g x.1.1 β)]
    have hpull {m : ↥f.support → ℕ} : (∑ x : Σ γ, Fin (m γ), c₀ * g x.1.1 α * (c₀ * g x.1.1 β)) =
        c₀ ^ 2 * ∑ γ : ↥f.support, (m γ : ℝ) * (g γ.1 α * g γ.1 β) := by
      simp only [Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hpull, hpull, ← mul_sub, ← Finset.sum_sub_distrib]
    have hdiff : (∑ γ : ↥f.support, ((zp γ : ℝ) * (g γ.1 α * g γ.1 β) - (zn γ : ℝ) * (g γ.1 α * g γ.1 β))) =
        ∑ γ ∈ f.support, (M : ℝ) * (f γ : ℝ) * (g γ α * g γ β) := by
      rw [← Finset.sum_coe_sort f.support]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [← sub_mul, show (zp γ : ℝ) - zn γ = (z γ : ℝ) by exact_mod_cast hzp_zn γ,
        show (z γ : ℝ) = M * (f γ : ℝ) by exact_mod_cast hz γ]
    rw [hdiff]
    have hm_jl (j l : Fin k) : ∑ γ ∈ f.support, (f γ : ℝ) * latticeSample n γ j * latticeSample n γ l = ζ * C j l := by
      have h2 : (secondMoment μ j l : ℝ) = ((p.coeff.sum fun _ q => q : ℚ) : ℝ) * C j l := by
        have hm : secondMoment μ j l = mass p * C j l := by simp [μ, secondMoment_mul, hzero, hfirst, hsecond, mul_comm]
        simpa [mass, augmentation, AddMonoidAlgebra.lift_apply] using congrArg (Rat.cast : ℚ → ℝ) hm
      have hsm : (secondMoment μ j l : ℝ) = ∑ γ ∈ f.support, (f γ : ℝ) * (γ j : ℝ) * (γ l : ℝ) := by
        change ((f.sum fun γ q => q * ((γ j : ℚ) * γ l) : ℚ) : ℝ) = _; simp [Finsupp.sum, mul_assoc]
      rw [hsm] at h2; dsimp only [ζ]; rw [div_mul_eq_mul_div, ← h2, Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by simp [latticeSample]; ring
    have hr (j l : Fin k) : (∑ γ ∈ f.support,
        (M : ℝ) * (f γ : ℝ) * ((U₀ α j * latticeSample n γ j) * (U₀ β l * latticeSample n γ l))) =
        (M : ℝ) * U₀ α j * U₀ β l * (ζ * C j l) := by
      rw [← hm_jl j l, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have hm2 : (∑ γ ∈ f.support, (M : ℝ) * (f γ : ℝ) * (g γ α * g γ β)) = M * ζ * (if α = β then 1 else 0) := by
      have hU1 : (U₀ * C.map (Rat.cast : ℚ → ℝ) * U₀.transpose) α β = if α = β then 1 else 0 := by rw [hU_eq]; simp [Matrix.one_apply]
      simp only [g, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]; conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
      simp only [hr, ← hU1]
      change _ = (M : ℝ) * ζ * ∑ l, (∑ j, U₀ α j * (C j l : ℝ)) * U₀ β l
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hm2]; by_cases hab : α = β <;> simp [hab, hc₀_sq]
  have hV_tr : (V * V.transpose).trace < η := by
    have htr : (V * V.transpose).trace = c₀ ^ 2 * M * f.sum (fun γ q => max (-(q : ℝ)) 0 * ∑ α, g γ α ^ 2) := by
      change (∑ α, ∑ x : mp, c₀ * g (e₀ x).1.1 α * (c₀ * g (e₀ x).1.1 α)) = _
      simp_rw [show ∀ α, (∑ x : mp, c₀ * g (e₀ x).1.1 α * (c₀ * g (e₀ x).1.1 α)) = ∑ x : mn, c₀ * g x.1.1 α * (c₀ * g x.1.1 α)
        from fun α => e₀.sum_comp fun x : mn => c₀ * g x.1.1 α * (c₀ * g x.1.1 α)]
      rw [Finset.sum_comm]
      simp only [mn, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hzn (γ : ↥f.support) : (zn γ : ℝ) = M * max (-(f γ : ℝ)) 0 := by
        have hn : ((zn γ : ℤ) : ℝ) = max (-(z γ : ℝ)) 0 := by exact_mod_cast Int.toNat_eq_max (-z γ)
        simpa [show (z γ : ℝ) = M * (f γ : ℝ) by exact_mod_cast hz γ, ← mul_neg, mul_max_of_nonneg _ _ hM.le] using hn
      rw [Finsupp.sum, ← Finset.sum_coe_sort f.support, Finset.mul_sum]
      simp only [Finset.mul_sum, hzn]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hcM : 0 < c₀ ^ 2 * M := by dsimp [c₀]; positivity
    calc (V * V.transpose).trace < c₀ ^ 2 * M * (η * ζ) := htr ▸ mul_lt_mul_of_pos_left hneg hcM
      _ = c₀ ^ 2 * (M * ζ) * η := by ring
      _ = η := by rw [hc₀_sq, one_mul]
  have hpsd : (η • (1 : Matrix (Fin d) (Fin d) ℝ) - V * V.transpose).PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨by
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_one, transpose_mul, transpose_transpose], fun x => ?_⟩
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_nonneg]
    rw [show x ⬝ᵥ ((V * V.transpose) *ᵥ x) = ∑ t : mp, (∑ α, x α * V α t) ^ 2 by
      rw [← mulVec_mulVec, dotProduct_mulVec]
      simp only [dotProduct, vecMul, mulVec, transpose_apply, sq]
      exact Finset.sum_congr rfl fun t _ => by simp only [mul_comm (V _ t)]]
    calc ∑ t : mp, (∑ α, x α * V α t) ^ 2
      _ ≤ ∑ t : mp, (∑ α, x α ^ 2) * ∑ α, V α t ^ 2 :=
        Finset.sum_le_sum fun t _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (V · t)
      _ = (x ⬝ᵥ x) * (V * V.transpose).trace := by
        rw [← Finset.mul_sum, Finset.sum_comm]; congr 1
        · simp [dotProduct, sq]
        · simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]
      _ ≤ η * (x ⬝ᵥ x) := by nlinarith [hV_tr.le, show 0 ≤ x ⬝ᵥ x from Finset.sum_nonneg fun α _ => mul_self_nonneg (x α)]
  let R := CFC.sqrt (η • (1 : Matrix (Fin d) (Fin d) ℝ) - V * V.transpose)
  have hR_sq : R * R.transpose = η • 1 - V * V.transpose := by
    rw [show R.transpose = R by
      rw [← conjTranspose_eq_transpose_of_trivial]
      exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).1.eq]
    exact CFC.sqrt_mul_sqrt_self _ hpsd.nonneg
  let cs := (Real.sqrt (1 + η))⁻¹
  let Up := cs • U.fromCols R
  let Un := cs • V.fromCols R
  have hgram (W : Matrix (Fin d) mp ℝ) :
      (cs • W.fromCols R) * (cs • W.fromCols R).transpose =
      (1 + η)⁻¹ • (W * W.transpose + (η • 1 - V * V.transpose)) := by
    have hfc : W.fromCols R * (W.fromCols R).transpose = W * W.transpose + R * R.transpose := by
      ext α β; simp [Matrix.mul_apply, fromCols, Fintype.sum_sum_type]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hfc, hR_sq]
    congr 1; dsimp [cs]; rw [← _root_.mul_inv_rev, ← sq, Real.sq_sqrt (by positivity)]
  have hUp : Up * Up.transpose = (1 : ℝ) • 1 := by
    rw [hgram U, show U * U.transpose + (η • 1 - V * V.transpose) = (1 + η) • 1 by
      ext α β; have hab := hUV α β
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hab ⊢
      split_ifs at hab ⊢ <;> linarith, smul_smul, inv_mul_cancel₀ (by positivity)]
  have hUn : Un * Un.transpose = (η / (1 + η)) • 1 := by rw [hgram V, add_sub_cancel, smul_smul, div_eq_inv_mul]
  let ℓ := Fintype.card (mp ⊕ Fin d)
  let _ : NeZero ℓ := ⟨(Fintype.card_pos_iff.mpr ⟨Sum.inr ⟨0, hd⟩⟩).ne'⟩
  let eqv := Fintype.equivFin (mp ⊕ Fin d)
  let cp (x : mp ⊕ Fin d) : ℝ := cs * Sum.elim (fun t : mp => c₀ * v t.1.1) (fun _ => 0) x
  let cn (x : mp ⊕ Fin d) : ℝ := cs * Sum.elim (fun t : mp => c₀ * v (e₀ t).1.1) (fun _ => 0) x
  let fp (i : Fin s) : Space ℓ := WithLp.toLp 2 fun x => cp (eqv.symm x) + ∑ α, a i α * Up α (eqv.symm x)
  let fn (i : Fin s) : Space ℓ := WithLp.toLp 2 fun x => cn (eqv.symm x) + ∑ α, a i α * Un α (eqv.symm x)
  have hdist (cv : mp ⊕ Fin d → ℝ) (W : Matrix (Fin d) (mp ⊕ Fin d) ℝ) (q : ℝ)
      (hW : W * W.transpose = q • (1 : Matrix (Fin d) (Fin d) ℝ)) (i j : Fin s) :
      (∑ x : Fin ℓ, ((cv (eqv.symm x) + ∑ α, a i α * W α (eqv.symm x)) -
        (cv (eqv.symm x) + ∑ α, a j α * W α (eqv.symm x))) ^ 2) = q * ‖a i - a j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, eqv.symm.sum_comp fun y => ((cv y + ∑ α, a i α * W α y) - (cv y + ∑ α, a j α * W α y)) ^ 2]
    have hvec (y : mp ⊕ Fin d) : (cv y + ∑ α, a i α * W α y) - (cv y + ∑ α, a j α * W α y) =
        (W.transpose *ᵥ (a i - a j).ofLp) y := by
      simp [mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, mul_comm]
    simp_rw [hvec, sq]
    change (W.transpose *ᵥ (a i - a j).ofLp) ⬝ᵥ (W.transpose *ᵥ (a i - a j).ofLp) = _
    have hq2 : (W.transpose *ᵥ (a i - a j).ofLp) ⬝ᵥ (W.transpose *ᵥ (a i - a j).ofLp) =
        (a i - a j).ofLp ⬝ᵥ ((W * W.transpose) *ᵥ (a i - a j).ofLp) := by
      rw [← mulVec_mulVec, dotProduct_mulVec (a i - a j).ofLp W]
      congr 1; exact (vecMul_transpose W.transpose _).symm
    rw [hq2, hW, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    simp [dotProduct, Real.norm_eq_abs]
  have hperm_sum (i : Fin s) (y : mp ⊕ Fin d) :
      let σ : Equiv.Perm (mp ⊕ Fin d) := Equiv.sumCongr ((e i).trans e₀.symm) (.refl _)
      cn (σ y) + ∑ α, a i α * Un α (σ y) = cp y + ∑ α, a i α * Up α y := by
    cases y with
    | inl t =>
      have ht := congrArg (fun r => cs * (c₀ * r)) (he i t)
      change cs * (c₀ * v (e₀ (e₀.symm (e i t))).1.1) + ∑ α, a i α * (cs * (c₀ * g (e₀ (e₀.symm (e i t))).1.1 α)) =
        cs * (c₀ * v t.1.1) + ∑ α, a i α * (cs * (c₀ * g t.1.1 α))
      rw [e₀.apply_symm_apply]
      have hlin (u : Lattice k) : cs * (c₀ * v u) + ∑ α, a i α * (cs * (c₀ * g u α)) =
          cs * (c₀ * (v u + ∑ α, a i α * g u α)) := by
        rw [mul_add, mul_add]; congr 1; simp_rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hlin (e i t).1.1, ht, ← hlin t.1.1]
    | inr _ => simp [cp, cn, Up, Un]
  refine ⟨ℓ, fp, fn,
    fun i j => by simpa [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, fp] using hdist cp Up 1 hUp i j,
    fun i j => by simpa [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, fn] using hdist cn Un (η / (1 + η)) hUn i j,
    fun i => ⟨eqv.symm.trans ((Equiv.sumCongr ((e i).trans e₀.symm) (.refl _)).trans eqv), fun x => ?_⟩⟩
  simpa [fp, fn, Equiv.trans_apply] using hperm_sum i (eqv.symm x)

end EuclideanRamsey
end
end OAI
