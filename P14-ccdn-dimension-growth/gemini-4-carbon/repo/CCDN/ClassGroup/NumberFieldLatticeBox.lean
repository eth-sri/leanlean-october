module

public import CCDN.ClassGroup.BalancedGenerator
public import CCDN.ClassGroup.NumberFieldEuclideanLattice
import Mathlib.Algebra.Module.ZLattice.Covolume

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory MeasureTheory.Measure
open scoped Pointwise NNReal

private theorem superlattice_finite_packing_polynomial
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [FiniteDimensional ℝ E]
    (b : Module.Basis ι ℝ E) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hb : ∀ i, b i ∈ L) (s : Finset L) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hs : ∀ x ∈ s, ‖(x : E)‖ ≤ B) (hnorm : ∀ i, ‖b i‖ ≤ M) :
    (s.card : ℝ) * ZLattice.covolume L ≤
      (2 * B + Fintype.card ι * M) ^ Module.finrank ℝ E * volume.real (Metric.ball (0 : E) 1) := by
  classical
  let L₀ := Submodule.span ℤ (Set.range b)
  have : MeasurableVAdd L₀ E := inferInstanceAs (MeasurableVAdd L₀.toAddSubgroup E)
  have : VAddInvariantMeasure L₀ E volume :=
    inferInstanceAs (VAddInvariantMeasure L₀.toAddSubgroup E volume)
  have hF := ZSpan.isAddFundamentalDomain b volume
  have hcoset (t : Finset E) (ht : ∀ x ∈ t, ‖x‖ ≤ B)
      (hsub : ∀ x ∈ t, ∀ y ∈ t, x - y ∈ L₀) :
      (t.card : ℝ) * volume.real (ZSpan.fundamentalDomain b) ≤
        volume.real (Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖)) := by
    obtain rfl | ⟨y, hy⟩ := t.eq_empty_or_nonempty
    · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]; exact ENNReal.toReal_nonneg
    let emb : t ↪ L₀ := ⟨fun x => ⟨x.val - y, hsub x.val x.property y hy⟩,
      fun x z h => Subtype.ext (sub_left_injective (congrArg Subtype.val h))⟩
    let u := Finset.univ.map emb
    have hd : Pairwise (Function.onFun (AEDisjoint volume) fun g : u => g.val +ᵥ ZSpan.fundamentalDomain b) :=
      fun x z hxz => hF.aedisjoint fun h => hxz (Subtype.ext h)
    have hm := measure_iUnion₀ hd fun g : u => hF.nullMeasurableSet.vadd g.val
    rw [show (∑' g : u, volume (g.val +ᵥ ZSpan.fundamentalDomain b)) =
      (u.card : ENNReal) * volume (ZSpan.fundamentalDomain b) by simp [measure_vadd, tsum_fintype]] at hm
    have hpack : (u.card : ENNReal) * volume (ZSpan.fundamentalDomain b) ≤
        volume (Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖)) := by
      rw [← hm]
      refine measure_mono (Set.iUnion_subset fun g w hw => ?_)
      obtain ⟨z, hz, rfl⟩ := Set.mem_vadd_set.mp hw
      obtain ⟨x, _, hg⟩ := Finset.mem_map.mp g.property
      apply mem_closedBall_zero_iff.mpr
      change ‖(g.val : E) + z‖ ≤ _
      have hg' : (g.val : E) = x.val - y := congrArg Subtype.val hg.symm
      rw [hg']
      have hz_le : ‖z‖ ≤ ∑ i, ‖b i‖ := by
        rw [← ZSpan.fract_eq_self.mpr hz]; exact ZSpan.norm_fract_le b z
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (by linarith [ht x.val x.property, ht y hy])) hz_le)
    have htr := ENNReal.toReal_mono (isCompact_closedBall (0 : E) _).measure_lt_top.ne hpack
    simpa [u, Measure.real, ENNReal.toReal_mul, ENNReal.toReal_natCast] using htr
  have hle : L₀ ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hratio := ZLattice.covolume_div_covolume_eq_relIndex' L₀ L hle
  have hpos : (0 : ℝ) < L₀.toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [← hratio]; exact div_pos (ZLattice.covolume_pos L₀) (ZLattice.covolume_pos L)
  have hindex : L₀.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := mod_cast hpos.ne'
  let H := L₀.toAddSubgroup.addSubgroupOf L.toAddSubgroup
  let Q := L ⧸ H
  let : Fintype Q := H.fintypeOfIndexNeZero hindex
  let q : L → Q := QuotientAddGroup.mk
  have hfib (a : Q) : ((s.filter fun x => q x = a).card : ℝ) *
      volume.real (ZSpan.fundamentalDomain b) ≤
      volume.real (Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖)) := by
    have ht := hcoset ((s.filter fun x => q x = a).image fun x : L => (x : E))
      (fun x hx => by obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx; exact hs y (Finset.mem_filter.mp hy).1)
      (fun x hx y hy => by
        obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
        exact QuotientAddGroup.eq_iff_sub_mem.mp
          ((Finset.mem_filter.mp hx').2.trans (Finset.mem_filter.mp hy').2.symm))
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using ht
  have hp : (s.card : ℝ) * volume.real (ZSpan.fundamentalDomain b) ≤
      (L₀.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) *
        volume.real (Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖)) := by
    have hi : Fintype.card Q = L₀.toAddSubgroup.relIndex L.toAddSubgroup :=
      (Nat.card_eq_fintype_card (α := Q)).symm
    rw [Finset.card_eq_sum_card_fiberwise (f := q) (fun _ _ => Finset.mem_univ _),
      Nat.cast_sum, Finset.sum_mul]
    exact (Finset.sum_le_sum fun a _ => hfib a).trans_eq (by simp [hi])
  have hvol : ZLattice.covolume L₀ = volume.real (ZSpan.fundamentalDomain b) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L₀ volume hF
  have hc : ZLattice.covolume L₀ =
      (L₀.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L :=
    (div_eq_iff (ZLattice.covolume_pos L).ne').mp hratio
  rw [← hvol, hc] at hp
  have hp' : (s.card : ℝ) * ZLattice.covolume L ≤
      volume.real (Metric.closedBall (0 : E) (2 * B + ∑ i, ‖b i‖)) :=
    (mul_le_mul_iff_right₀ hpos).mp (by nlinarith only [hp])
  have hsum : ∑ i, ‖b i‖ ≤ Fintype.card ι * M := by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hnorm i
  have hR : 0 ≤ 2 * B + (Fintype.card ι : ℝ) * M := by positivity
  exact (hp'.trans (measureReal_mono (Metric.closedBall_subset_closedBall (by linarith))
    (isCompact_closedBall (0 : E) _).measure_lt_top.ne)).trans_eq
    (volume.addHaar_real_closedBall (0 : E) hR)

private theorem unitBall_volume_le_two_pow_finrank
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    volume.real (Metric.ball (0 : E) 1) ≤ (2 : ℝ) ^ Module.finrank ℝ E := by
  let c := stdOrthonormalBasis ℝ E
  let f_lp : E → (Fin (Module.finrank ℝ E) → ℝ) := fun x =>
    (MeasurableEquiv.toLp 2 _).symm (c.repr x)
  have hm : MeasurePreserving f_lp :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).comp c.measurePreserving_repr
  let U : Set (Fin (Module.finrank ℝ E) → ℝ) := Set.Icc (fun _ => -1) (fun _ => 1)
  have hvol : volume (f_lp ⁻¹' U) = (2 : ENNReal) ^ Module.finrank ℝ E := by
    rw [hm.measure_preimage (show MeasurableSet U from measurableSet_Icc).nullMeasurableSet]
    norm_num [U, Real.volume_Icc_pi]
  have hsub : Metric.ball (0 : E) 1 ⊆ f_lp ⁻¹' U := fun x hx => by
    have hnorm_x : ‖x‖ < 1 := by simpa using hx
    have hcoord (i) : |f_lp x i| ≤ 1 := by
      have hi := PiLp.norm_apply_le (c.repr x) i
      rw [c.repr.norm_map] at hi; exact hi.trans hnorm_x.le
    exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
  have hp : volume (Metric.ball (0 : E) 1) ≤ volume (f_lp ⁻¹' U) := measure_mono hsub
  rw [hvol] at hp
  simpa only [Measure.real, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using
    ENNReal.toReal_mono (by finiteness) hp

def numberFieldLatticeBoxConstant (n : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 * Real.sqrt n + n * C) ^ n

lemma numberFieldLatticeBoxConstant_nonneg (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ numberFieldLatticeBoxConstant n C := by
  unfold numberFieldLatticeBoxConstant; positivity

open Classical in
theorem boundedSquareNormTranslationClasses_count_of_relative_short_basis
    (K : Type*) [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : ∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C) (hnorm : ∀ i, ‖b i‖ ≤ C * B) :
    ((boundedSquareNormTranslationClasses K B).card : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      (numberFieldLatticeBoxConstant (Module.finrank ℚ K) C *
        (2 : ℝ) ^ Module.finrank ℚ K) * B ^ (Module.finrank ℚ K - 1) := by
  have hunit : volume.real (Metric.ball (0 : mixedEmbedding.euclidean.mixedSpace K) 1) ≤
      (2 : ℝ) ^ Module.finrank ℚ K := by
    simpa only [mixedEmbedding.euclidean.finrank] using
      unitBall_volume_le_two_pow_finrank (E := mixedEmbedding.euclidean.mixedSpace K)
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let emb : 𝓞 K → mixedEmbedding.euclidean.integerLattice K := fun x =>
    ⟨euclideanNumberFieldEmbedding K (x : K), euclideanNumberFieldEmbedding_mem_integerLattice K x⟩
  have hemb : Function.Injective emb := fun x y h =>
    RingOfIntegers.coe_injective (euclideanNumberFieldEmbedding_injective K (congrArg Subtype.val h))
  let R := 2 * B
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  let s := (boundedArchimedeanIntegers_finite K R).toFinset.image emb
  have hs : ∀ x ∈ s, ‖(x : mixedEmbedding.euclidean.mixedSpace K)‖ ≤
      Real.sqrt (Module.finrank ℚ K) * R := fun x hx => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact euclideanNumberFieldEmbedding_norm_le K hR0 (z : K)
      ((boundedArchimedeanIntegers_finite K R).mem_toFinset.mp hz)
  have hcard_s : s.card = (boundedArchimedeanIntegers K R).ncard :=
    (Finset.card_image_of_injective _ hemb).trans
      (Set.ncard_eq_toFinset_card _ (boundedArchimedeanIntegers_finite K R)).symm
  have hp := superlattice_finite_packing_polynomial b
    (mixedEmbedding.euclidean.integerLattice K) hb s
    (mul_nonneg (Real.sqrt_nonneg _) hR0) (mul_nonneg hC hR0) hs
    fun i => (hnorm i).trans (by dsimp [R]; nlinarith [mul_nonneg hC hBpos.le])
  rw [hcard_s, euclidean_integerLattice_covolume, mixedEmbedding.euclidean.finrank,
    show Fintype.card ι = Module.finrank ℚ K by
      rw [← Module.finrank_eq_card_basis b, mixedEmbedding.euclidean.finrank]] at hp
  have hRad0 : 0 ≤ 2 * (Real.sqrt (Module.finrank ℚ K) * R) +
      (Module.finrank ℚ K : ℝ) * (C * R) := by positivity
  have hp2 : ((boundedArchimedeanIntegers K R).ncard : ℝ) *
      ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) ≤
      (2 : ℝ) ^ Module.finrank ℚ K *
        (2 * Real.sqrt (Module.finrank ℚ K) * R + (Module.finrank ℚ K : ℝ) * (C * R)) ^
          Module.finrank ℚ K :=
    hp.trans ((mul_le_mul_of_nonneg_left hunit (pow_nonneg hRad0 _)).trans_eq (by ring))
  have hr_pl : nrComplexPlaces K ≤ Module.finrank ℚ K := by
    have := card_add_two_mul_card_eq_rank K; omega
  have hpow2 : (2 : ℝ)⁻¹ ^ Module.finrank ℚ K ≤ (2 : ℝ)⁻¹ ^ nrComplexPlaces K :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hr_pl
  have hs2 := (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hpow2 (Real.sqrt_nonneg |(discr K : ℝ)|))
    (Nat.cast_nonneg (boundedArchimedeanIntegers K R).ncard)).trans hp2
  rw [show ((boundedArchimedeanIntegers K R).ncard : ℝ) *
      ((2 : ℝ)⁻¹ ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)|) =
      (((boundedArchimedeanIntegers K R).ncard : ℝ) * Real.sqrt |(discr K : ℝ)|) /
        (2 : ℝ) ^ Module.finrank ℚ K by rw [inv_pow, div_eq_mul_inv]; ring] at hs2
  have hcount : ((boundedArchimedeanIntegers K R).ncard : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      numberFieldLatticeBoxConstant (Module.finrank ℚ K) C * R ^ Module.finrank ℚ K := by
    have ht := (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mp hs2
    rw [show 2 * Real.sqrt (Module.finrank ℚ K) * R + (Module.finrank ℚ K : ℝ) * (C * R) =
      (2 * Real.sqrt (Module.finrank ℚ K) + Module.finrank ℚ K * C) * R by ring, mul_pow] at ht
    exact ht.trans_eq (by unfold numberFieldLatticeBoxConstant; ring)
  have hpR : ((boundedSquareNormTranslationClasses K B).card : ℝ) *
      ((2 * ⌊B⌋ + 1).toNat : ℝ) ≤ (boundedArchimedeanIntegers K R).ncard :=
    mod_cast (by simpa only [R, two_mul] using boundedSquareNormTranslationClasses_packing K B B)
  have hfloor : (0 : ℤ) ≤ 2 * ⌊B⌋ + 1 := by
    have : (0 : ℤ) ≤ ⌊B⌋ := Int.floor_nonneg.mpr hBpos.le; omega
  have htrans : B ≤ ((2 * ⌊B⌋ + 1).toNat : ℝ) := by
    rw [show ((2 * ⌊B⌋ + 1).toNat : ℝ) = ((2 * ⌊B⌋ + 1 : ℤ) : ℝ) from
      mod_cast Int.toNat_of_nonneg hfloor]
    push_cast; linarith [Int.lt_floor_add_one B]
  have hh := (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left htrans (Nat.cast_nonneg _)).trans hpR)
    (Real.sqrt_nonneg |(discr K : ℝ)|)).trans hcount
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hpowB : B ^ Module.finrank ℚ K = B ^ (Module.finrank ℚ K - 1) * B := by
    rw [← pow_succ]; congr 1; omega
  dsimp only [R] at hh
  rw [mul_pow, hpowB] at hh
  exact (mul_le_mul_iff_left₀ hBpos).mp (by nlinarith only [hh])

end
end CCDN
