module

public import CCDN.ClassGroup.BalancedGenerator
import CCDN.ClassGroup.NumberFieldEuclideanLattice
import CCDN.ForMathlib.FieldTheory

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory MeasureTheory.Measure

private theorem boundedArchimedeanIntegers_separated_count
    (L : Type*) [Field L] [NumberField L] {B : ℝ} (hB : 0 ≤ B) :
    ((boundedArchimedeanIntegers L B).ncard : ℝ) ≤
      (2 * Real.sqrt (Module.finrank ℚ L) * B + 1) ^ Module.finrank ℚ L := by
  classical
  let E := mixedEmbedding.euclidean.mixedSpace L
  let e : 𝓞 L → E := fun x => euclideanNumberFieldEmbedding L (x : L)
  have he : Function.Injective e := fun x y h =>
    RingOfIntegers.coe_injective (euclideanNumberFieldEmbedding_injective L h)
  let s := (boundedArchimedeanIntegers_finite L B).toFinset.image e
  let R := Real.sqrt (Module.finrank ℚ L) * B
  have hR : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg _) hB
  have hs : ∀ x ∈ s, ‖x‖ ≤ R := fun x hx => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact euclideanNumberFieldEmbedding_norm_le L hB (z : L)
      ((boundedArchimedeanIntegers_finite L B).mem_toFinset.mp hz)
  have hd : Set.PairwiseDisjoint (s : Set E) (fun x => Metric.ball x (1 / 2 : ℝ)) :=
    fun x hx y hy hxy => Set.disjoint_left.mpr fun z hzx hzy => by
      obtain ⟨zx, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨zy, _, rfl⟩ := Finset.mem_image.mp hy
      have hzw : zx - zy ≠ 0 := sub_ne_zero.mpr fun h => hxy (congrArg e h)
      have hh : 1 ≤ dist (e zx) (e zy) := by
        rw [dist_eq_norm]
        simpa only [e, map_sub] using one_le_euclidean_norm_integer L hzw
      have h1 := Metric.mem_ball.mp hzx; rw [dist_comm] at h1
      have h2 : dist z (e zy) < 1 / 2 := Metric.mem_ball.mp hzy
      linarith [dist_triangle (e zx) z (e zy)]
  have hsub : (⋃ x ∈ s, Metric.ball x (1 / 2 : ℝ)) ⊆ Metric.ball (0 : E) (R + 1 / 2) :=
    fun z hz => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
      have hz' := Metric.mem_ball.mp hzx; rw [dist_eq_norm] at hz'
      exact mem_ball_zero_iff.mpr (by linarith [hs x hx, norm_le_norm_sub_add z x])
  have hm : (s.card : ENNReal) * volume (Metric.ball (0 : E) (1 / 2 : ℝ)) ≤
      volume (Metric.ball (0 : E) (R + 1 / 2)) := by
    have hu := measure_biUnion_finset (μ := volume) hd fun _ _ => measurableSet_ball
    have hmono : volume (⋃ x ∈ s, Metric.ball x (1 / 2 : ℝ)) ≤
        volume (Metric.ball (0 : E) (R + 1 / 2)) := measure_mono hsub
    rw [hu] at hmono
    simpa only [addHaar_ball_center volume, Finset.sum_const, nsmul_eq_mul] using hmono
  have ht := ENNReal.toReal_mono (ne_of_lt measure_ball_lt_top) hm
  rw [addHaar_ball_of_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1 / 2),
    addHaar_ball_of_pos volume (0 : E) (by linarith : 0 < R + 1 / 2)] at ht
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1 / 2) ^ Module.finrank ℝ E),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (R + 1 / 2) ^ Module.finrank ℝ E)] at ht
  have hv : 0 < (volume (Metric.ball (0 : E) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 zero_lt_one))
      (ne_of_lt measure_ball_lt_top)
  have hpow : (s.card : ℝ) * (1 / 2) ^ Module.finrank ℝ E ≤ (R + 1 / 2) ^ Module.finrank ℝ E := by
    nlinarith only [ht, hv]
  have hscale := mul_le_mul_of_nonneg_right hpow (by positivity : (0 : ℝ) ≤ 2 ^ Module.finrank ℝ E)
  rw [mul_assoc, ← mul_pow, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_pow, mul_one,
    ← mul_pow, show (R + 1 / 2) * 2 = 2 * R + 1 by ring] at hscale
  have hcard : s.card = (boundedArchimedeanIntegers L B).ncard :=
    (Finset.card_image_of_injective _ he).trans
      (Set.ncard_eq_toFinset_card _ (boundedArchimedeanIntegers_finite L B)).symm
  simpa only [hcard, E, mixedEmbedding.euclidean.finrank, R, mul_assoc] using hscale

variable (K : Type*) [Field K] [NumberField K]

def boundedSmallSubfieldIntegers (B : ℝ) : Set (𝓞 K) :=
  {β | β ∈ boundedArchimedeanIntegers K B ∧
    ∃ L : IntermediateField ℚ K,
      4 * Module.finrank ℚ L ≤ Module.finrank ℚ K ∧ (β : K) ∈ L}

lemma boundedSmallSubfieldIntegers_finite (B : ℝ) :
    (boundedSmallSubfieldIntegers K B).Finite :=
  (boundedArchimedeanIntegers_finite K B).subset fun _ h => h.1

def smallSubfieldIntegerCountConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (2 * Real.sqrt (n : ℝ) + 1) ^ n

lemma smallSubfieldIntegerCountConstant_pos (n : ℕ) :
    0 < smallSubfieldIntegerCountConstant n := by
  unfold smallSubfieldIntegerCountConstant; positivity

theorem boundedSmallSubfieldIntegers_balanced_count {D : ℝ} (hD : 1 ≤ D) :
    ((boundedSmallSubfieldIntegers K
        (9 * D ^ (1 / (Module.finrank ℚ K : ℝ)))).ncard : ℝ) ≤
      (smallSubfieldIntegerCountConstant (Module.finrank ℚ K) *
        (9 : ℝ) ^ ((Module.finrank ℚ K : ℝ) / 4)) * D ^ (1 / 4 : ℝ) := by
  classical
  let n := Module.finrank ℚ K
  have hn : (0 : ℝ) < n := mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let B := 9 * D ^ (1 / (n : ℝ))
  have hB : 1 ≤ B := by
    dsimp [B]; linarith [Real.one_le_rpow hD (by positivity : 0 ≤ 1 / (n : ℝ))]
  let T := {L : IntermediateField ℚ K // 4 * Module.finrank ℚ L ≤ n}
  let : Finite (IntermediateField ℚ K) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ K
      (Field.exists_primitive_element ℚ K)
  let : Fintype (IntermediateField ℚ K) := Fintype.ofFinite _
  let : Fintype T := Fintype.ofFinite _
  let subSet (L : IntermediateField ℚ K) : Set (𝓞 K) :=
    {β | β ∈ boundedArchimedeanIntegers K B ∧ (β : K) ∈ L}
  have hsub_fin (L) : (subSet L).Finite :=
    (boundedArchimedeanIntegers_finite K B).subset fun _ h => h.1
  let sf := (boundedSmallSubfieldIntegers_finite K B).toFinset
  let tf (L : T) := (hsub_fin L.val).toFinset
  have hcover : sf ⊆ Finset.univ.biUnion tf := fun β hβ => by
    obtain ⟨hβB, L, hL, hβL⟩ := (boundedSmallSubfieldIntegers_finite K B).mem_toFinset.mp hβ
    exact Finset.mem_biUnion.mpr ⟨⟨L, hL⟩, Finset.mem_univ _,
      (hsub_fin L).mem_toFinset.mpr ⟨hβB, hβL⟩⟩
  have hterm (L : T) : ((tf L).card : ℝ) ≤
      (2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4) := by
    let toL : subSet L.val → boundedArchimedeanIntegers L.val B := fun β => by
      let γ : L.val := ⟨(β.val : K), β.property.2⟩
      have hγ : γ ∈ integralClosure ℤ L.val :=
        (isIntegral_algebraMap_iff (R := ℤ) (A := L.val) (B := K)).mp β.val.isIntegral_coe
      let z : 𝓞 L.val := ⟨γ, hγ⟩
      refine ⟨z, fun w => ?_⟩
      obtain ⟨v, rfl⟩ := InfinitePlace.comap_surjective (K := K) w
      rw [InfinitePlace.comap_apply]
      change v (algebraMap L.val K (z : L.val)) ≤ B
      rw [show (z : L.val) = γ from RingOfIntegers.coe_mk hγ]
      exact β.property.1 v
    have hinj : Function.Injective toL := fun x y h => by
      apply Subtype.ext; apply RingOfIntegers.coe_injective
      exact congrArg (fun z : boundedArchimedeanIntegers L.val B => ((z.val : L.val) : K)) h
    let := (hsub_fin L.val).fintype
    let := (boundedArchimedeanIntegers_finite L.val B).fintype
    have hncard : ((tf L).card : ℝ) ≤ (boundedArchimedeanIntegers L.val B).ncard := by
      rw [← Set.ncard_eq_toFinset_card _ (hsub_fin L.val),
        ← Set.fintypeCard_eq_ncard (subSet L.val),
        ← Set.fintypeCard_eq_ncard (boundedArchimedeanIntegers L.val B)]
      exact_mod_cast Fintype.card_le_of_injective toL hinj
    let m := Module.finrank ℚ L.val
    have hm : 4 * m ≤ n := L.property
    have hmn : m ≤ n := by omega
    have hsq : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (Nat.cast_le.mpr hmn)
    have hc : 1 ≤ 2 * Real.sqrt (n : ℝ) + 1 := by linarith [Real.sqrt_nonneg (n : ℝ)]
    have hbase : 2 * Real.sqrt (m : ℝ) * B + 1 ≤ (2 * Real.sqrt (n : ℝ) + 1) * B := by nlinarith
    have hexp : (m : ℝ) ≤ (n : ℝ) / 4 := by have : 4 * (m : ℝ) ≤ n := mod_cast hm; linarith
    refine (hncard.trans (boundedArchimedeanIntegers_separated_count L.val (by linarith))).trans ?_
    calc (2 * Real.sqrt (m : ℝ) * B + 1) ^ m
        ≤ ((2 * Real.sqrt (n : ℝ) + 1) * B) ^ m := pow_le_pow_left₀ (by positivity) hbase m
      _ = (2 * Real.sqrt (n : ℝ) + 1) ^ m * B ^ m := mul_pow _ _ _
      _ ≤ (2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4) :=
        mul_le_mul (pow_le_pow_right₀ hc hmn)
          (by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hB hexp)
          (by positivity) (by positivity)
  have hcard : Fintype.card T ≤ 2 ^ n :=
    (Fintype.card_subtype_le _).trans
      ((Nat.card_eq_fintype_card (α := IntermediateField ℚ K)).symm ▸
        IntermediateField.card_le_two_pow_finrank ℚ K)
  have hcount : ((boundedSmallSubfieldIntegers K B).ncard : ℝ) ≤
      smallSubfieldIntegerCountConstant n * B ^ ((n : ℝ) / 4) := calc
    ((boundedSmallSubfieldIntegers K B).ncard : ℝ) = sf.card := by
        rw [Set.ncard_eq_toFinset_card _ (boundedSmallSubfieldIntegers_finite K B)]
    _ ≤ ∑ L : T, ((tf L).card : ℝ) :=
        mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ _L : T, (2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4) :=
        Finset.sum_le_sum fun L _ => hterm L
    _ = (Fintype.card T : ℝ) * ((2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4)) := by simp
    _ ≤ (2 : ℝ) ^ n * ((2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_right (mod_cast hcard) (by positivity)
    _ = smallSubfieldIntegerCountConstant n * B ^ ((n : ℝ) / 4) := by
        unfold smallSubfieldIntegerCountConstant; ring
  dsimp only [B] at hcount
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) (Real.rpow_nonneg hD0.le _),
    ← Real.rpow_mul hD0.le, show 1 / (n : ℝ) * ((n : ℝ) / 4) = 1 / 4 by field_simp] at hcount
  convert hcount using 1; ring

end
end CCDN
