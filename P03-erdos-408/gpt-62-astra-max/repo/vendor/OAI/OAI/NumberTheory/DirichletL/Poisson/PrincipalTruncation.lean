module

public import OAI.NumberTheory.DirichletL.Eisenstein.PrimitiveRows

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

theorem mem_rowNormDisk_floor {lengthScale : ℝ} (hL : 0 ≤ lengthScale) (z : O) :
    z ∈ rowNormDisk ⌊lengthScale⌋₊ ↔ z ≠ 0 ∧ ‖eisEmbedding z‖ ^ 2 ≤ lengthScale := by
  rw [mem_rowNormDisk]
  constructor
  · rintro ⟨hp, hN⟩
    refine ⟨?_, ?_⟩
    · intro hz
      subst z
      simp at hp
    · rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hL)
  · rintro ⟨hz, hN⟩
    have hp := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hz))
    rw [eisEmbedding_norm_sq_eq_absNorm_span] at hp hN
    exact ⟨by exact_mod_cast hp, Nat.le_floor hN⟩

theorem dualNear_eq_finite (W : ℝ → ℂ) (X lengthScale : ℝ) (hL : 0 ≤ lengthScale) :
    dualNear W X lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2) := by
  unfold dualNear
  rw [tsum_eq_sum (s := rowNormDisk ⌊lengthScale⌋₊) (fun h hh => ?_)]
  · apply Finset.sum_congr rfl
    intro h hh
    have hd := (mem_rowNormDisk_floor hL h).mp hh
    simp only [ite_eq_left hd.2, ite_eq_right hd.1]
  · by_cases hz : h = 0
    · simp [hz]
    · have hn : ¬ ‖eisEmbedding h‖ ^ 2 ≤ lengthScale := fun hn => hh ((mem_rowNormDisk_floor hL h).mpr ⟨hz, hn⟩)
      simp only [ite_eq_right hn]

theorem dualFar_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K lengthScale : ℝ), 0 < K → 0 ≤ lengthScale →
        ‖dualFar W K lengthScale‖ ≤ (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + K * lengthScale) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K lengthScale hK hL
  have he : dualFar W K lengthScale =
      ∑' h : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    unfold dualFar
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | lengthScale < ‖eisEmbedding h‖ ^ 2}) (by
      intro h hh
      by_contra hn
      change ¬ lengthScale < ‖eisEmbedding h‖ ^ 2 at hn
      exact hh (by simp only [ite_eq_right hn]))]
    apply tsum_congr
    intro h
    have hqh : lengthScale < ‖eisEmbedding h.val‖ ^ 2 := h.property
    have hz : h.val ≠ 0 := by
      intro hz
      have hp := hqh
      simp only [hz, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hp
      linarith
    simp only [ite_eq_left hqh, ite_eq_right hz]
  rw [he]
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  let f : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2} →
      {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, mul_le_mul_of_nonneg_left h.property.le hK.le⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // lengthScale < ‖eisEmbedding h‖ ^ 2},
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      ∑' h : {h : O // K * lengthScale ≤ K * ‖eisEmbedding h‖ ^ 2},
        ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
    (hs.subtype _).tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hi.trans (hb W K (K * lengthScale) hK (mul_nonneg hK.le hL)))

end

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem middle_divisor_frequency_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ Z → 0 ≤ lengthScale →
        ‖(X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
          (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (X / Y) * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := dualFar_decay A
  refine ⟨s, C, hC, ?_⟩
  intro ι _ P _ S W X Y Z lengthScale hX hY hYZ hL
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let Q := (min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hZ : 0 < Z := hY.trans_le hYZ
  have hQ : 0 < Q := by dsimp [Q]; positivity
  rw [Finset.mul_sum]
  have hf (E : Finset ι) (hE : E ∈ middleDivisors P S Y Z) :
      ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) *
        dualFar W (X / subsetNorm P E) lengthScale)‖ ≤ (X / Y) * (B / Q) := by
    have hn := subsetNorm_pos P E
    have hEY : Y < subsetNorm P E := (Finset.mem_filter.mp hE).2
    have hEZ : subsetNorm P E ≤ Z := (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).2
    have hk : X / Z ≤ X / subsetNorm P E := div_le_div_of_nonneg_left hX.le hn hEZ
    have hden : Q ≤ (min 1 (X / subsetNorm P E)) ^ 2 *
        (1 + (X / subsetNorm P E) * lengthScale) ^ A := by
      dsimp [Q]
      have hmul : X * lengthScale / Z ≤ (X / subsetNorm P E) * lengthScale := by
        calc
          _ = (X / Z) * lengthScale := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hk hL
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) (min_le_min_left _ hk) 2
      · exact pow_le_pow_left₀ (by positivity) (by linarith) A
      · positivity
      · positivity
    have hh : ‖dualFar W (X / subsetNorm P E) lengthScale‖ ≤ B / Q :=
      (hb W _ lengthScale (div_pos hX hn) hL).trans (div_le_div_of_nonneg_left hB hQ hden)
    calc
      _ = (X / subsetNorm P E) * ‖subsetMobius P E‖ * ‖dualFar W (X / subsetNorm P E) lengthScale‖ := by
        simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hX, abs_of_pos hn]
        ring
      _ ≤ (X / Y) * 1 * (B / Q) := by
        apply mul_le_mul
        · exact mul_le_mul (div_le_div_of_nonneg_left hX.le hY hEY.le)
            (subsetMobius_norm_le_one P E) (norm_nonneg _) (by positivity)
        · exact hh
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑ E ∈ middleDivisors P S Y Z,
        ‖(X : ℂ) * ((subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale)‖ := norm_sum_le _ _
    _ ≤ ∑ E ∈ middleDivisors P S Y Z, (X / Y) * (B / Q) := Finset.sum_le_sum hf
    _ = ((middleDivisors P S Y Z).card : ℝ) * ((X / Y) * (B / Q)) := by simp
    _ ≤ (2 : ℝ) ^ S.card * ((X / Y) * (B / Q)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hsub : middleDivisors P S Y Z ⊆ S.powerset :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_powerset] at hc
      exact_mod_cast hc
    _ = _ := by dsimp [B, Q]; ring

end

local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

def principalTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Z : ℝ) : ℂ :=
  (X : ℂ) * paperRadialFourier W 0 * (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
  (X : ℂ) * paperRadialFourier W 0 *
    (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
  W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E)

def middleTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) *
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W ((X / subsetNorm P E) * ‖eisEmbedding h‖ ^ 2)

def truncationError {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (∑' z : O, rowCoprimeMask P S z * (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) -
    (principalTruncation P S W X Z + middleTruncation P S W X Y Z lengthScale)

theorem truncationError_eq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) (hYZ : Y ≤ Z) (hL : 0 ≤ lengthScale) :
    truncationError P S W X Y Z lengthScale =
      (X : ℂ) * (∑ E ∈ smallDivisors P S Y,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)) +
      (X : ℂ) * (∑ E ∈ middleDivisors P S Y Z,
        (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale) +
      (∑ E ∈ largeDivisors P S Z, subsetMobius P E * radialSource W (X / subsetNorm P E)) := by
  unfold truncationError principalTruncation middleTruncation
  rw [masked_radialSource_five_pieces P hinj S W X Y Z lengthScale hX hYZ]
  simp_rw [dualNear_eq_finite W _ lengthScale hL]
  ring

theorem truncationError_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ X → X ≤ Z → 0 ≤ lengthScale →
        ‖truncationError P S W X Y Z lengthScale‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Y / X) ^ A + (1 / (1 + Z / X) ^ A) +
              (X / Y) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A)) := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := small_divisor_dual_tail A
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := large_divisor_source_tail A
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := middle_divisor_frequency_tail A
  refine ⟨(s₀ ∪ s₁) ∪ s₂, C₀ + C₁ + C₂, by positivity, ?_⟩
  intro ι _ P _ hinj S W X Y Z lengthScale hX hY hYX hXZ hL
  let Q := ((s₀ ∪ s₁) ∪ s₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C := C₀ + C₁ + C₂
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hc₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hc₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hc₂ : C₂ ≤ C := by dsimp [C]; linarith
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left.trans Finset.subset_union_left)) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right.trans Finset.subset_union_left)) W
  have hq₂ : s₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hz : 0 < Z := hX.trans_le hXZ
  let lo : ℂ := (X : ℂ) * ∑ E ∈ smallDivisors P S Y,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * radialDual W (X / subsetNorm P E)
  let mid : ℂ := (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) * dualFar W (X / subsetNorm P E) lengthScale
  let hi : ℂ := ∑ E ∈ largeDivisors P S Z,
    subsetMobius P E * radialSource W (X / subsetNorm P E)
  have hlo : ‖lo‖ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A := by
    apply (h₀ P S W X Y hX hY.le hYX).trans
    gcongr
  have hhi : ‖hi‖ ≤ (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := by
    apply (h₁ P S W X Z hX hXZ).trans
    gcongr
  have hmid : ‖mid‖ ≤ (2 : ℝ) ^ S.card * (X / Y) * (C * Q) /
      ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) := by
    apply (h₂ P S W X Y Z lengthScale hX hY (hYX.trans hXZ) hL).trans
    gcongr
  rw [truncationError_eq P hinj S W X Y Z lengthScale hX (hYX.trans hXZ) hL]
  change ‖lo + mid + hi‖ ≤ _
  calc
    _ ≤ ‖lo‖ + ‖mid‖ + ‖hi‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le lo mid) le_rfl)
    _ ≤ (2 : ℝ) ^ S.card * (C * Q) * (Y / X) ^ A +
        (2 : ℝ) ^ S.card * (X / Y) * (C * Q) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A) +
        (2 : ℝ) ^ S.card * (C * Q) / (1 + Z / X) ^ A := add_le_add (add_le_add hlo hmid) hhi
    _ = _ := by change _ = (2 : ℝ) ^ S.card * (C * Q) * _; ring

end TruncatedPrincipalPoisson

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

section
open FourierBridge FirstPassCubeLabels

lemma schwartz_phase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  simpa only [logPhase, Real.inner_apply, mul_assoc, mul_comm, mul_left_comm] using
    FourierBridge.schwartz_log_inversion g x

def profileSourceBound (g : 𝓢(ℝ, ℂ)) (J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (J + 1),
    ((SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)

lemma source_le_profileSourceBound (g : 𝓢(ℝ, ℂ)) (J i : ℕ) (hi : i ≤ J) :
    (SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g ≤
      profileSourceBound g J := by
  unfold profileSourceBound
  apply Finset.single_le_sum (s := Finset.range (J + 1)) (a := i)
    (f := fun k : ℕ => (SchwartzMap.seminorm ℝ 0 k) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower k) g)
  · intro j hj
    positivity
  · exact Finset.mem_range.mpr (by omega)

def outerWindow (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : ℝ) : ℂ :=
  V 0 z * V 1 ud * V 2 ue * V 3 uv * V 4 kap

def fixedColumnTest (V : ℝ → ℂ) (t : ℝ) (x : ℝ) : ℂ := V x * logPhase t x

end

open FirstPassCubeLabels

lemma weighted_schwartz_integrable (b : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
  simpa using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J

end JointLogSeparation

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

abbrev Triple (ι : Type*) := Σ _ : Finset ι, Finset ι × Finset ι

def triples (F : Finset ι) : Finset (Triple ι) :=
  F.powerset.sigma fun G => ((F \ G).powerset ×ˢ (F \ G).powerset).filter fun UV => Disjoint UV.1 UV.2

def split (ST : Finset ι × Finset ι) : Triple ι :=
  ⟨ST.1 ∩ ST.2, ST.1 \ ST.2, ST.2 \ ST.1⟩

def join (GUV : Triple ι) : Finset ι × Finset ι :=
  (GUV.1 ∪ GUV.2.1, GUV.1 ∪ GUV.2.2)

lemma join_split (ST : Finset ι × Finset ι) : join (split ST) = ST := by
  apply Prod.ext
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  · ext i
    simp only [join, split, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

lemma split_mem {F : Finset ι} {ST : Finset ι × Finset ι}
    (hST : ST ∈ F.powerset ×ˢ F.powerset) : split ST ∈ triples F := by
  rcases Finset.mem_product.mp hST with ⟨hS, hT⟩
  have hSF := Finset.mem_powerset.mp hS
  have hTF := Finset.mem_powerset.mp hT
  simp only [triples, split, Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨Finset.inter_subset_left.trans hSF, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hSF hi.1, by tauto⟩
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hi ⊢
    exact ⟨hTF hi.1, by tauto⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

lemma join_mem {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    join GUV ∈ F.powerset ×ˢ F.powerset := by
  rcases (by simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
    Finset.mem_product, Finset.mem_powerset] using h) with ⟨hG, ⟨hU, hV⟩, _⟩
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_powerset.mpr
  · exact Finset.union_subset hG (hU.trans Finset.sdiff_subset)
  · exact Finset.union_subset hG (hV.trans Finset.sdiff_subset)

lemma split_join {F : Finset ι} {GUV : Triple ι} (h : GUV ∈ triples F) :
    split (join GUV) = GUV := by
  rcases GUV with ⟨G, U, V⟩
  have hh : G ⊆ F ∧ (U ⊆ F \ G ∧ V ⊆ F \ G) ∧ Disjoint U V := by
    simpa only [triples, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powerset] using h
  rcases hh with ⟨_, ⟨hU, hV⟩, hd⟩
  have hUG : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hU hi)).2 hg)
  have hVG : Disjoint V G := Finset.disjoint_left.mpr (fun i hi hg => (Finset.mem_sdiff.mp (hV hi)).2 hg)
  have h₀ : (G ∪ U) ∩ (G ∪ V) = G := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have h₁ : (G ∪ U) \ (G ∪ V) = U := by
    ext i
    have hi : i ∈ U → i ∈ V → False := fun hi hj => Finset.disjoint_left.mp hd hi hj
    have hj : i ∈ U → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hUG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have h₂ : (G ∪ V) \ (G ∪ U) = V := by
    ext i
    have hi : i ∈ V → i ∈ U → False := fun hi hj => Finset.disjoint_left.mp hd.symm hi hj
    have hj : i ∈ V → i ∈ G → False := fun hi hj => Finset.disjoint_left.mp hVG hi hj
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  simp only [split, join, h₀, h₁, h₂]

theorem sum_pair_eq_overlap {β : Type*} [AddCommMonoid β]
    (F : Finset ι) (C : Finset ι → Finset ι → β) :
    (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, C S T) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then C (G ∪ U) (G ∪ V) else 0 := by
  classical
  have hs : (∑ ST ∈ F.powerset ×ˢ F.powerset, C ST.1 ST.2) =
      ∑ GUV ∈ triples F, C (join GUV).1 (join GUV).2 := by
    apply Finset.sum_bij (fun ST _ => split ST)
    · intro ST hST
      exact split_mem hST
    · intro ST hST SU hSU heq
      have hh := congrArg join heq
      simpa only [join_split] using hh
    · intro GUV hGUV
      exact ⟨join GUV, join_mem hGUV, split_join hGUV⟩
    · intro ST hST
      rw [join_split]
  simpa only [triples, Finset.sum_sigma, Finset.sum_filter, Finset.sum_product, join] using hs

end FiniteOverlapDecomposition

end

end OAI
