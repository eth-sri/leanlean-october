module

public import CCDN.ClassGroup.NumberFieldEuclideanLattice
import CCDN.ForMathlib.ZLattice
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section
namespace CCDN
noncomputable section
open Module Submodule InnerProductSpace MeasureTheory NumberField
open scoped NumberField

private theorem field_basis_multiplication_minimum_product
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (b : Basis (Fin (n + 2)) ℚ K) (hb0 : b 0 = 1)
    (N : K → ℝ) (hN : ∀ x, 0 ≤ N x) (hmul : ∀ x y, N (x * y) ≤ N x * N y)
    (hunit : 1 ≤ N (b 0))
    (hmin : ∀ i j : {i : Fin (n + 2) // i ≠ 0 ∧ i ≠ Fin.last (n + 1)},
      b.coord (Fin.last (n + 1)) (b i * b j) ≠ 0 → N (b (Fin.last (n + 1))) ≤ N (b i * b j)) :
    N (b (Fin.last (n + 1))) ^ (n + 2) ≤ (∏ i, N (b i)) ^ 2 := by
  classical
  let p : Fin (n + 2) := 0
  let q : Fin (n + 2) := Fin.last (n + 1)
  have hpq : p ≠ q := fun he => by have := congrArg Fin.val he; simp [p, q] at this
  let ℓ := b.coord q
  let μ := b.coord p
  have hℓ : ℓ ≠ 0 := fun h => by simpa [ℓ] using LinearMap.congr_fun h (b q)
  have hℓ1 : ℓ 1 = 0 := by rw [← hb0]; simp [ℓ, p, Basis.coord_apply, hpq]
  have hμ1 : μ 1 = 1 := by rw [← hb0]; simp [μ, p, Basis.coord_apply]
  let W : Submodule ℚ K := LinearMap.ker ℓ ⊓ LinearMap.ker μ
  let B_form : LinearMap.BilinForm ℚ W :=
    { toFun := fun a =>
        { toFun := fun x => ℓ ((a : K) * (x : K))
          map_add' := fun _ _ => by simp [mul_add]
          map_smul' := fun _ _ => by simp }
      map_add' := fun _ _ => by ext; simp [add_mul]
      map_smul' := fun _ _ => by ext; simp }
  have hnondeg : B_form.Nondegenerate := by
    have hl (a : W) (ha : ∀ x, B_form a x = 0) : a = 0 := by
      by_contra hn
      have hav : (a : K) ≠ 0 := fun h => hn (Subtype.ext h)
      have ha_not_scalar : (a : K) ∉ Set.range (algebraMap ℚ K) := by
        rintro ⟨c, hc⟩
        have hμa : μ a = 0 := a.property.2
        rw [← hc, Algebra.algebraMap_eq_smul_one, map_smul, hμ1, smul_eq_mul, mul_one] at hμa
        exact hav (by rw [← hc, hμa, map_zero])
      have hex : ∃ y : K, ℓ y = 0 ∧ ℓ ((a : K) * y) ≠ 0 := by
        by_contra h
        push Not at h
        obtain ⟨z, hz⟩ : ∃ z : K, ℓ z ≠ 0 := by
          by_contra hz0; push Not at hz0; exact hℓ (LinearMap.ext hz0)
        let u : K := (ℓ z)⁻¹ • z
        have hu : ℓ u = 1 := by simp [u, hz]
        let c : ℚ := ℓ ((a : K) * u)
        have hp_c (t : K) : ℓ ((a : K) * t) = c * ℓ t := by
          have ht := h (t - ℓ t • u) (by simp [hu])
          rw [mul_sub, mul_smul_comm, map_sub, map_smul] at ht
          exact (sub_eq_zero.mp ht).trans (mul_comm _ _)
        refine ha_not_scalar ⟨c, ?_⟩
        by_contra hne
        have hh : ℓ (((a : K) - algebraMap ℚ K c) * (((a : K) - algebraMap ℚ K c)⁻¹ * u)) = 0 := by
          rw [sub_mul, ← Algebra.smul_def, map_sub, map_smul, hp_c]; simp
        rw [mul_inv_cancel_left₀ (sub_ne_zero.mpr (Ne.symm hne)), hu] at hh
        exact one_ne_zero hh
      obtain ⟨y, hy, hay⟩ := hex
      have haℓ : ℓ a = 0 := a.property.1
      refine hay ?_
      simpa only [B_form, LinearMap.coe_mk, AddHom.coe_mk, mul_sub, mul_smul_comm, mul_one,
        map_sub, map_smul, haℓ, smul_zero, sub_zero] using
        ha ⟨y - μ y • (1 : K), by simp [hy, hℓ1], by simp [hμ1]⟩
    exact ⟨hl, fun x hx => hl x fun a => by
      simpa only [B_form, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using hx a⟩
  let J := {i : Fin (n + 2) // i ≠ p ∧ i ≠ q}
  have hspan : span ℚ (Set.range fun i : J => b i) = W := by
    rw [show (Set.range fun i : J => b i) = b '' {i | i ≠ p ∧ i ≠ q} by ext; simp [J]]
    ext x; rw [b.mem_span_image]
    change (↑(b.repr x).support ⊆ {i | i ≠ p ∧ i ≠ q}) ↔ b.repr x q = 0 ∧ b.repr x p = 0
    exact ⟨fun hx => ⟨by by_contra hq; exact (hx (Finsupp.mem_support_iff.mpr hq)).2 rfl,
      by by_contra hp; exact (hx (Finsupp.mem_support_iff.mpr hp)).1 rfl⟩,
      fun ⟨hq, hp⟩ i hi => by
        have hi' := Finsupp.mem_support_iff.mp hi
        exact ⟨fun h => hi' (h ▸ hp), fun h => hi' (h ▸ hq)⟩⟩
  let bW : Basis J ℚ W := (Basis.span (b.linearIndependent.comp (fun i : J => (i : Fin (n + 2)))
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ hspan)
  have hbW (i : J) : (bW i : K) = b i := by simp [bW]
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bW).mp hnondeg
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm J, ∀ i, B_form.toMatrix bW (σ i) i ≠ 0 := by
    by_contra h; push Not at h; apply hdet; rw [Matrix.det_apply]
    refine Finset.sum_eq_zero fun σ _ => ?_
    obtain ⟨i, hi⟩ := h σ
    rw [Finset.prod_eq_zero (f := fun j => B_form.toMatrix bW (σ j) j) (Finset.mem_univ i) hi, smul_zero]
  have hprod_J : N (b q) ^ Fintype.card J ≤ (∏ i : J, N (b i)) ^ 2 := calc
    N (b q) ^ Fintype.card J = ∏ _i : J, N (b q) := by simp
    _ ≤ ∏ i : J, N (b (σ i)) * N (b i) := Finset.prod_le_prod₀ (fun _ _ => hN _) fun i _ => by
      have hij : ℓ (b (σ i) * b i) ≠ 0 := by
        simpa only [LinearMap.BilinForm.toMatrix_apply, B_form, LinearMap.coe_mk, AddHom.coe_mk,
          hbW] using hσ i
      exact (hmin (σ i) i hij).trans (hmul _ _)
    _ = (∏ i : J, N (b i)) ^ 2 := by
      rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i : J => N (b i)), sq]
  have hs (i : Fin (n + 2)) : i ∈ (Finset.univ.erase p).erase q ↔ i ≠ p ∧ i ≠ q := by
    simp [and_comm]
  have hq_mem : q ∈ Finset.univ.erase p := by simp [hpq.symm]
  have hcard : Fintype.card J + 2 = n + 2 := by
    rw [Fintype.card_of_subtype _ hs]
    have h1 := Finset.card_erase_add_one hq_mem
    have h2 := Finset.card_erase_add_one (Finset.mem_univ p)
    simp only [Finset.card_univ, Fintype.card_fin] at h1 h2; omega
  have hprod_eq : ∏ i, N (b i) = N (b p) * N (b q) * ∏ i : J, N (b i) := by
    rw [← Finset.prod_subtype _ hs (fun i => N (b i)), mul_assoc,
      Finset.mul_prod_erase _ (fun i => N (b i)) hq_mem,
      Finset.mul_prod_erase _ (fun i => N (b i)) (Finset.mem_univ p)]
  have hp0 : 0 ≤ N (b q) * ∏ i : J, N (b i) :=
    mul_nonneg (hN _) (Finset.prod_nonneg fun _ _ => hN _)
  have hfull : N (b q) * ∏ i : J, N (b i) ≤ ∏ i, N (b i) := by
    rw [hprod_eq, mul_assoc]; exact le_mul_of_one_le_left hp0 hunit
  have hc_pow : N (b q) ^ (n + 2) = N (b q) ^ (Fintype.card J + 2) :=
    congrArg (N (b q) ^ ·) hcard.symm
  calc N (b q) ^ (n + 2) = N (b q) ^ Fintype.card J * N (b q) ^ 2 := by rw [hc_pow, pow_add]
    _ ≤ (∏ i : J, N (b i)) ^ 2 * N (b q) ^ 2 := mul_le_mul_of_nonneg_right hprod_J (sq_nonneg _)
    _ = (N (b q) * ∏ i : J, N (b i)) ^ 2 := by ring
    _ ≤ (∏ i, N (b i)) ^ 2 := pow_le_pow_left₀ hp0 hfull 2

private def IsPrescribedGreedy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) (w : E) {k : ℕ} (v : Fin (k + 1) → E) : Prop :=
  LinearIndependent ℝ v ∧ v 0 = w ∧ (∀ i, v i ∈ L) ∧
    ∀ i, i ≠ 0 → ∀ x, x ∈ L → x ∉ span ℝ (v '' Set.Iio i) → ‖v i‖ ≤ ‖x‖

private theorem exists_prescribed_greedy_basis_and_product
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (w : E) (hw : w ∈ L) (hw0 : w ≠ 0)
    (hlower : ∀ x, x ∈ L → x ≠ 0 → 1 ≤ ‖x‖)
    {n : ℕ} (hn : Module.finrank ℝ E = n + 1) :
    ∃ b : Basis (Fin (n + 1)) ℝ E, IsPrescribedGreedy L w b ∧
      (∏ i, ‖b i‖) ≤ ‖w‖ * (n + 1 : ℝ) ^ (n + 1) * ZLattice.covolume L := by
  classical
  have hfam (k : ℕ) (hk : k + 1 ≤ n + 1) : ∃ v : Fin (k + 1) → E, IsPrescribedGreedy L w v := by
    induction k with
    | zero =>
      let : Subsingleton (Fin (0 + 1)) := Fin.subsingleton_iff_le_one.mpr (by omega)
      exact ⟨fun _ => w, (linearIndependent_subsingleton_index_iff _).mpr fun _ => hw0, rfl,
        fun _ => hw, fun i hi => (hi (Subsingleton.elim _ _)).elim⟩
    | succ k ih =>
      obtain ⟨v, hli, hv0, hvm, hvmin⟩ := ih (by omega)
      have hU : span ℝ (Set.range v) ≠ ⊤ := fun he => by
        have hdim := finrank_span_eq_card hli
        rw [he, finrank_top, hn, Fintype.card_fin] at hdim; omega
      obtain ⟨x, hx, hxU, hmin⟩ := ZLattice.exists_shortest_vector_notMem L _ hU
      refine ⟨Fin.snoc v x, hli.finSnoc hxU, by simpa using hv0,
        fun i => Fin.lastCases (by simpa using hx) (fun j => by simpa using hvm j) i,
        fun i => Fin.lastCases (fun _ => by simpa only [Fin.snoc_last, Fin.snoc_image_Iio_last] using hmin)
          (fun j hj => by
            have hj0 : j ≠ 0 := fun hz => hj (by simp [hz])
            simpa only [Fin.snoc_castSucc, Fin.snoc_image_Iio_castSucc] using hvmin j hj0) i⟩
  obtain ⟨v, hv⟩ := hfam n le_rfl
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv.1 (by simpa using hn.symm)
  have hb : IsPrescribedGreedy L w b := by
    simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv
  have hdim_b : Module.finrank ℝ E = Fintype.card (Fin (n + 1)) := Module.finrank_eq_card_basis b
  let c := gramSchmidtOrthonormalBasis hdim_b b
  have hflag (i : Fin (n + 1)) : span ℝ (c '' Set.Iio i) = span ℝ (b '' Set.Iio i) := by
    have hc : (c : Fin (n + 1) → E) = gramSchmidtNormed ℝ b := funext fun j => by
      apply gramSchmidtOrthonormalBasis_apply
      intro he
      have h1 := gramSchmidtNormed_unit_length j b.linearIndependent
      rw [he, norm_zero] at h1; norm_num at h1
    rw [hc, span_gramSchmidtNormed, span_gramSchmidt_Iio]
  let a : Fin (n + 1) → ℝ := fun i => if i = 0 then 1 else ‖b i‖
  have ha_pos (i) : 0 < a i := by
    dsimp [a]; split_ifs; · exact one_pos
    · exact norm_pos_iff.mpr (hb.1.ne_zero i)
  have ha_mono : Monotone a := fun i j hij => by
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [a, hi, hj]
      · simpa [a, hi, hj] using hlower (b j) (hb.2.2.1 j) (hb.1.ne_zero j)
    · have hj : j ≠ 0 := fun hz => hi (le_antisymm (hz ▸ hij) (Fin.zero_le i))
      simp only [a, ite_eq_right hi, ite_eq_right hj]
      exact hb.2.2.2 i hi (b j) (hb.2.2.1 j) (hb.1.notMem_span_image (not_lt_of_ge hij))
  have ha_out (i) (x : E) (hx : x ∈ L) (hxU : x ∉ span ℝ (c '' Set.Iio i)) : a i ≤ ‖x‖ := by
    rw [hflag] at hxU
    by_cases hi : i = 0
    · simpa [a, hi] using hlower x hx fun hz => hxU (hz ▸ Submodule.zero_mem _)
    · simpa [a, hi] using hb.2.2.2 i hi x hx hxU
  have hnR : (0 : ℝ) < n + 1 := by positivity
  let r : Fin (n + 1) → ℝ := fun i => a i / (n + 1 : ℕ)
  have hr (i) : 0 < r i := div_pos (ha_pos i) (mod_cast Nat.succ_pos n)
  let u := c.toBasis.unitsSMul fun i => Units.mk0 (r i) (hr i).ne'
  have hcoord (x : E) (hx : x ∈ ZSpan.fundamentalDomain u) (i) :
      0 ≤ c.toBasis.repr x i ∧ c.toBasis.repr x i < r i := by
    have hi := (ZSpan.mem_fundamentalDomain u).mp hx i
    have hrep : c.toBasis.repr x i = r i * u.repr x i := by
      simp only [u, Basis.repr_unitsSMul, Units.smul_def, Units.val_inv_eq_inv_val,
        Units.val_mk0, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (hr i).ne', one_mul]
    rw [hrep]
    exact ⟨mul_nonneg (hr i).le hi.1, by simpa using mul_lt_mul_of_pos_left hi.2 (hr i)⟩
  have hsep : ∀ x ∈ ZSpan.fundamentalDomain u, ∀ y ∈ ZSpan.fundamentalDomain u,
      x - y ∈ L → x = y := fun x hx y hy hxy => sub_eq_zero.mp <| by
    by_contra hne
    let S := (c.toBasis.repr (x - y)).support
    have hS : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun he =>
      hne (c.toBasis.repr.injective (by simpa using Finsupp.support_eq_empty.mp he))
    let j := S.max' hS
    have hnot : x - y ∉ span ℝ (c '' Set.Iio j) := fun h =>
      lt_irrefl j (c.toBasis.repr_support_subset_of_mem_span (Set.Iio j) h (Finset.max'_mem _ hS))
    have hmin := ha_out j (x - y) hxy hnot
    have hterm (i) : ‖c.toBasis.repr (x - y) i • c i‖ < r j := by
      rw [norm_smul, c.orthonormal.1 i, mul_one, Real.norm_eq_abs]
      by_cases hi : i ≤ j
      · have hxi := hcoord x hx i; have hyi := hcoord y hy i
        rw [map_sub, Finsupp.sub_apply]
        exact (abs_lt.mpr ⟨by linarith, by linarith⟩).trans_le
          (div_le_div_of_nonneg_right (ha_mono hi) (by positivity))
      · have hz : c.toBasis.repr (x - y) i = 0 :=
          Finsupp.notMem_support_iff.mp fun him => hi (Finset.le_max' _ _ him)
        rw [hz, abs_zero]; exact hr j
    have hstrict : ∑ i : Fin (n + 1), ‖c.toBasis.repr (x - y) i • c i‖ < a j := by
      have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hterm i
      simpa only [r, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one, mul_div_cancel₀ _ hnR.ne'] using hsum
    have hnorm : ‖x - y‖ ≤ ∑ i : Fin (n + 1), ‖c.toBasis.repr (x - y) i • c i‖ :=
      (congrArg norm (c.toBasis.sum_repr (x - y)).symm).trans_le (norm_sum_le _ _)
    exact (not_lt_of_ge hmin) (hnorm.trans_lt hstrict)
  have hbound := ZLattice.measureReal_le_covolume L volume
    (ZSpan.fundamentalDomain_measurableSet u) hsep
  have hunit : volume.real (ZSpan.fundamentalDomain c.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped c.toBasis volume)]
    change (volume (parallelepiped c)).toReal = 1
    rw [c.volume_parallelepiped, ENNReal.toReal_one]
  have hvol : volume.real (ZSpan.fundamentalDomain u) = (∏ i, a i) / (n + 1 : ℝ) ^ (n + 1) := by
    rw [ZSpan.measureReal_fundamentalDomain u volume c.toBasis, hunit, mul_one]
    change |c.toBasis.det (c.toBasis.unitsSMul _)| = _
    rw [Basis.det_unitsSMul_self]
    simp only [Units.val_mk0]
    rw [abs_of_pos (Finset.prod_pos fun i _ => hr i)]
    simp only [r, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one]
  rw [hvol] at hbound
  have ha_prod : ∏ i, a i ≤ (n + 1 : ℝ) ^ (n + 1) * ZLattice.covolume L :=
    ((div_le_iff₀ (pow_pos hnR _)).mp hbound).trans_eq (mul_comm _ _)
  have hb_prod : ∏ i, ‖b i‖ = ‖w‖ * ∏ i, a i := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [a, hb.2.1]
  refine ⟨b, hb, ?_⟩
  rw [hb_prod]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ha_prod (norm_nonneg w)

open Classical in
theorem exists_numberField_short_basis (K : Type*) [Field K] [NumberField K]
    (hd : 2 ≤ Module.finrank ℚ K) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℝ (mixedEmbedding.euclidean.mixedSpace K),
      (∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K) ∧
      ∀ i, ‖b i‖ ≤ (Module.finrank ℚ K : ℝ) ^ 3 *
        |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank ℚ K = n + 2 := ⟨Module.finrank ℚ K - 2, by omega⟩
  rw [hn]
  let L := mixedEmbedding.euclidean.integerLattice K
  let w := euclideanNumberFieldEmbedding K 1
  have hdim : Module.finrank ℝ (mixedEmbedding.euclidean.mixedSpace K) = (n + 1) + 1 := by
    rw [mixedEmbedding.euclidean.finrank, hn]
  obtain ⟨b, hb, hprod⟩ := exists_prescribed_greedy_basis_and_product L w
    (euclideanNumberFieldEmbedding_mem_integerLattice K 1)
    ((map_ne_zero (euclideanNumberFieldEmbedding K)).mpr one_ne_zero)
    (fun x hx hx0 => one_le_euclidean_integerLattice_norm K hx hx0) hdim
  choose v hv using fun i => (mem_euclidean_integerLattice_iff K (b i)).mp (hb.2.2.1 i)
  have hli_q : LinearIndependent ℚ (fun i => (v i : K)) :=
    LinearIndependent.of_comp (euclideanNumberFieldLinearMap K)
      (by simpa only [Function.comp_def, euclideanNumberFieldLinearMap_apply, hv] using
        b.linearIndependent.restrict_scalars' ℚ)
  let q := basisOfLinearIndependentOfCardEqFinrank' (fun i => (v i : K)) hli_q
    (by simp [hn])
  have hq (i) : q i = (v i : K) :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ hli_q _) i
  have hmap (i) : euclideanNumberFieldEmbedding K (q i) = b i :=
    (congrArg (euclideanNumberFieldEmbedding K) (hq i)).trans (hv i)
  have hq0 : q 0 = 1 := euclideanNumberFieldEmbedding_injective K (by rw [hmap, hb.2.1])
  have hpq : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := fun he => by
    have := congrArg Fin.val he; simp at this
  have hmin_pow : ‖b (Fin.last (n + 1))‖ ^ (n + 2) ≤ (∏ i, ‖b i‖) ^ 2 := by
    have hh := field_basis_multiplication_minimum_product q hq0
      (fun x => ‖euclideanNumberFieldEmbedding K x‖) (fun _ => norm_nonneg _)
      (euclideanNumberFieldEmbedding_norm_mul_le K)
      (hq0 ▸ one_le_euclidean_norm_integer K (x := 1) one_ne_zero)
      fun i j hij => by
        rw [hmap]
        refine hb.2.2.2 _ hpq.symm _ ?_ fun hmem => ?_
        · simpa only [hq, RingOfIntegers.coe_eq_algebraMap, map_mul] using
            euclideanNumberFieldEmbedding_mem_integerLattice K (v i * v j)
        · have hrep : b.repr (euclideanNumberFieldEmbedding K (q i * q j)) (Fin.last (n + 1)) =
              (q.repr (q i * q j) (Fin.last (n + 1)) : ℝ) := by
            have hmaps : ((b.coord (Fin.last (n + 1))).restrictScalars ℚ).comp
                (euclideanNumberFieldLinearMap K) =
                (Algebra.linearMap ℚ ℝ).comp (q.coord (Fin.last (n + 1))) :=
              q.ext fun k => by
                simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
                  euclideanNumberFieldLinearMap_apply, hmap, Basis.coord_apply, Basis.repr_self,
                  Finsupp.single_apply]
                split_ifs <;> norm_num
            exact congrArg (fun f => f (q i * q j)) hmaps
          have hsup := b.repr_support_subset_of_mem_span _ hmem
            (Finsupp.mem_support_iff.mpr (by rw [hrep]; exact_mod_cast hij))
          simp at hsup
    simpa only [hmap] using hh
  let D := |(discr K : ℝ)|
  have hD0 : 0 ≤ D := abs_nonneg _
  have hD1 : 1 ≤ D := by
    have hz : (0 : ℤ) < |discr K| := abs_pos.mpr (discr_ne_zero K)
    dsimp [D]; exact_mod_cast (show (1 : ℤ) ≤ |discr K| by omega)
  have hcov : ZLattice.covolume L ≤ Real.sqrt D := by
    change ZLattice.covolume (mixedEmbedding.euclidean.integerLattice K) ≤ _
    rw [euclidean_integerLattice_covolume]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
  have hw_le : ‖w‖ ≤ Real.sqrt (n + 2 : ℕ) := by
    simpa only [hn] using euclideanNumberFieldEmbedding_one_norm_le K
  have hprod' : (∏ i, ‖b i‖) ≤ Real.sqrt (n + 2 : ℕ) * ((n + 2 : ℕ) : ℝ) ^ (n + 2) * Real.sqrt D := by
    have hp : (∏ i, ‖b i‖) ≤ ‖w‖ * ((n + 2 : ℕ) : ℝ) ^ (n + 2) * ZLattice.covolume L := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
        show n + 1 + 1 = n + 2 by omega, show (n : ℝ) + 1 + 1 = n + 2 by ring] using hprod
    exact hp.trans (mul_le_mul (mul_le_mul_of_nonneg_right hw_le (by positivity)) hcov
      (ZLattice.covolume_pos L _).le (by positivity))
  let m := n + 2
  have hm_ne : m ≠ 0 := by dsimp [m]; omega
  have hm0 : (0 : ℝ) < m := by dsimp [m]; positivity
  have hm1 : (1 : ℝ) ≤ m := by dsimp [m]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hlast : ‖b (Fin.last (n + 1))‖ ≤ (m : ℝ) ^ 3 * D ^ (1 / (m : ℝ)) := by
    have hP0 : 0 ≤ ∏ i, ‖b i‖ := Finset.prod_nonneg fun i _ => norm_nonneg (b i)
    have hsq := (sq_le_sq₀ hP0 (by positivity)).mpr hprod'
    have hsq' : (∏ i, ‖b i‖) ^ 2 ≤ (m : ℝ) ^ (2 * m + 1) * D := by
      convert hsq using 1
      dsimp only [m]
      rw [mul_pow, mul_pow, Real.sq_sqrt hm0.le, Real.sq_sqrt hD0, pow_succ, pow_mul]
      ring
    have hdeg_le : (m : ℝ) ^ (2 * m + 1) ≤ (m : ℝ) ^ (3 * m) :=
      pow_le_pow_right₀ hm1 (by dsimp [m]; omega)
    have hrt : (D ^ (1 / (m : ℝ))) ^ m = D := by
      rw [← Real.rpow_mul_natCast hD0, one_div_mul_cancel hm0.ne', Real.rpow_one]
    refine le_of_pow_le_pow_left₀ hm_ne (by positivity) ?_
    rw [mul_pow, ← pow_mul, hrt]
    exact hmin_pow.trans (hsq'.trans (mul_le_mul_of_nonneg_right hdeg_le hD0))
  refine ⟨b, hb.2.2.1, fun i => ?_⟩
  change ‖b i‖ ≤ (m : ℝ) ^ 3 * D ^ (1 / (m : ℝ))
  by_cases hi : i = 0
  · rw [hi, hb.2.1]
    have hsq_m : Real.sqrt m ≤ (m : ℝ) := (sq_le_sq₀ (Real.sqrt_nonneg _) hm0.le).mp
      (by rw [Real.sq_sqrt hm0.le]; nlinarith)
    have hcube : (m : ℝ) ≤ (m : ℝ) ^ 3 := by simpa using pow_le_pow_right₀ hm1 (by omega : 1 ≤ 3)
    have hrt1 : 1 ≤ D ^ (1 / (m : ℝ)) := Real.one_le_rpow hD1 (by positivity)
    exact (hw_le.trans (hsq_m.trans hcube)).trans
      (le_mul_of_one_le_right (by positivity) hrt1)
  · exact (hb.2.2.2 i hi (b (Fin.last (n + 1))) (hb.2.2.1 _)
      (b.linearIndependent.notMem_span_image (not_lt_of_ge (Fin.le_last i)))).trans hlast

end
end CCDN
