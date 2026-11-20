module
public import MathCollab.Density.Stronger.ShortPoweredHeight
public import MathCollab.Density.Stronger.PowerScales

/-! A single Taylor/powering family for arbitrary exponential smoothing length.
Only the dyadic list depends on the smoothing. The power is chosen from the
short scale, independently of how the block was detected. -/
@[expose] public section
open Real Filter Finset
noncomputable section
namespace MathCollab.Density.Stronger.BlockFamily

abbrev Index := (ℤ × ℕ × ℕ) × ℕ × ℕ
abbrev bound (a δ : ℝ) := ⌈2*a/δ⌉₊
def base (q : Index) := smoothHalfScale q.1.1 q.1.2.1
def length (q : Index) := 2^q.2.2*(base q)^q.2.1
def coeff (η T X Y : ℝ) (q : Index) :=
  normalizedSmoothPoweredCoefficient η T X Y q.1.1 q.1.2.1 q.1.2.2 q.2.1

def list (Y T a δ : ℝ) :=
  let J := (smoothScaleIndices (Y*(log T)^2)).product
    ((range 2).product (range (detectorTaylorCutoff T+1)))
  (J.product ((Icc 1 (bound a δ)).product (range (bound a δ)))).filter
    fun q => q.2.2 < q.2.1 ∧ T^a ≤ (base q:ℝ)^q.2.1 ∧ (base q:ℝ)^q.2.1 ≤ T^(3*a/2)

theorem size (a δ : ℝ) : ∀ᶠ T : ℝ in atTop, ∀ {Y : ℝ}, 1 ≤ Y → Y ≤ T →
    ((list Y T a δ).card:ℝ) ≤ 144*(bound a δ:ℝ)^2*(log T)^2 := by
  filter_upwards [eventually_ge_atTop (1:ℝ), tendsto_log_atTop.eventually_ge_atTop 1,
    log_sq_eventually_le_height] with T hT hlog hsq
  intro Y hY hYT
  have hj := smoothScaleIndices_card_le_log hT hlog (show 1≤Y*(log T)^2 by nlinarith)
    (show Y*(log T)^2 ≤ T^2 by nlinarith [mul_le_mul hYT hsq (sq_nonneg _) (by linarith : 0≤T)])
  have hr := detectorTaylorCutoff_le_log hlog
  have h := card_le_card (t := (smoothScaleIndices (Y*(log T)^2) ×ˢ
    (range 2 ×ˢ range (detectorTaylorCutoff T+1))) ×ˢ (Icc 1 (bound a δ) ×ˢ range (bound a δ)))
    (s := list Y T a δ) (filter_subset _ _)
  calc
    _ ≤ _ := (Nat.cast_le (α:=ℝ)).mpr h
    _ ≤ (6*log T*(2*(12*log T)))*((bound a δ:ℝ)*(bound a δ:ℝ)) := by simp only [card_product,card_range,Nat.card_Icc,Nat.add_sub_cancel]; push_cast; gcongr
    _ = _ := by ring

theorem valid {a δ η : ℝ} (hη : 0 < η) (ha : a < 4/3) :
    ∀ᶠ T : ℝ in atTop, ∀ {X Y : ℝ} {q : Index}, 0 < Y → q ∈ list Y T a δ →
      T^a ≤ (length q:ℝ) ∧ (length q:ℝ) ≤ (2:ℝ)^(bound a δ)*T^(3*a/2) ∧
        ∀ n, ‖coeff η T X Y q n‖ ≤ 1 := by
  filter_upwards [eventually_gt_atTop (1:ℝ), normalizedSmoothPoweredCoefficient_eventually hη (bound a δ),
    (tendsto_rpow_atTop (show 0 < 2-3*a/2 by linarith)).eventually_ge_atTop ((2:ℝ)^bound a δ)] with T hT hn h2
  intro X Y q hY hq
  obtain ⟨hp,hl,hlo,hhi⟩ := mem_filter.mp hq
  have hk := (mem_Icc.mp (mem_product.mp (mem_product.mp hp).2).1).2
  have hs := bounded_power_piece_scales (Nat.cast_nonneg (base q)) hk hl hlo hhi
  simp only [length,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  refine ⟨hs.1, hs.2, hn X Y _ _ _ _ hY hk ?_⟩
  apply (bounded_power_support_scale (Nat.cast_nonneg (base q)) hk hhi).trans
  calc
    _ ≤ T^(2-3*a/2)*T^(3*a/2) := by gcongr
    _ = _ := by rw [← rpow_add (by linarith : 0<T)]; ring_nf; norm_num

/-- A short large block at *any* smoothing length yields a large member. -/
theorem covers {a δ η : ℝ} (ha : 0 < a) (ha' : a < 4/3) (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ {s Y : ℝ} {ρ : ℂ} {j : ℤ}, 0 ≤ s → s ≤ ρ.re → ρ.re ≤ 1 → 0 < Y →
      j ∈ smoothScaleIndices (Y*(log T)^2) → T^δ/2 < (2:ℝ)^j → (2:ℝ)^j ≤ T^(3*a/4) →
      1/(24*log T) ≤ ‖smoothDetectorBlock ρ (T^δ) Y j‖ →
      ∃ q ∈ list Y T a δ, (length q:ℝ)^s*T^(-2*η) ≤ ‖detectingPolynomial (length q) (coeff η T (T^δ) Y q) ρ.im‖ := by
  filter_upwards [shortTaylor_cutoff_error_eventually, short_scale_bounded_power ha hδ,
    exists_normalizedSmoothPowered_height hη (bound a δ)] with T hcut hp hh
  intro s Y ρ j hs hβ hβ' hY hj hlow hhi hd
  obtain ⟨hT,hlog,herr⟩ := hcut
  have hN := hhi.trans ((rpow_le_rpow_of_exponent_le hT (by linarith : 3*a/4 ≤ 2)).trans_eq (rpow_two T))
  obtain ⟨hjpos,e,he,r,hr,hdet⟩ := exists_smoothBlock_Taylor_member hY hT (by positivity : 0 < 24*log T)
    (hs.trans hβ) hβ' hN (by convert herr using 1; ring) hd
  obtain ⟨hm,hm'⟩ := smoothHalfScale_bounds hjpos (mem_range.mp he)
  obtain ⟨k,hk,hk',hlo,hup⟩ := hp (smoothHalfScale j e) (by linarith) (hm'.trans hhi)
  have hv := rpow_le_rpow_of_exponent_le (by exact_mod_cast smoothHalfScale_pos j e : (1:ℝ) ≤ smoothHalfScale j e) hβ
  obtain ⟨l,hl,hlg⟩ := hh s _ _ ρ.im j e r k (hβ.trans hβ') hk hk' <|
    (div_le_div_of_nonneg_right hv (by positivity : 0 ≤ 192*log T)).trans (by convert hdet using 1; ring)
  refine ⟨((j,e,r),k,l),mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨hj,mem_product.mpr ⟨he,hr⟩⟩,
    mem_product.mpr ⟨mem_Icc.mpr ⟨hk,hk'⟩,mem_range.mpr ((mem_range.mp hl).trans_le hk')⟩⟩,mem_range.mp hl,hlo,hup⟩,hlg⟩

end MathCollab.Density.Stronger.BlockFamily
