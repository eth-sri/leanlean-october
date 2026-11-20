module
public import GeneralDetectorCover
public import GuthMaynard.Improvement.SlabAssembly
public import GuthMaynard.Improvement.RealIntegerSource

@[expose] public section

open Real Complex Set Filter Finset MathCollab.Density GuthMaynard.Improvement
open scoped BigOperators Topology
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment

/-- The analytic input to Type-I detection on a powered length window. -/
abbrev WindowLargeValues (σ a p δ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (T N t₀ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
    2 ≤ T → 2 ≤ N → T^a ≤ N → N ≤ T^(3*a/2+δ) →
    (∀ n ∈ sourceRatioIndices N, ‖b n‖ ≤ 1) →
    (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) → oneSeparated W →
    (∀ t ∈ W, N^σ*T^(-2*δ) ≤ ‖boundedPolynomial N b t‖) →
    (W.card:ℝ) ≤ C*T^(p+18*δ)

private theorem window_typeI {σ a p ε : ℝ} (hσ : 9/13 ≤ σ)
    (ha : 69/100 ≤ a) (ha' : a ≤ 4/5) (hε : 0 < ε)
    (hlargeValues : ∀ δ, 0 < δ → δ ≤ 1/100 → WindowLargeValues σ a p δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, SeparatedTypeI σ H (C*H^(p+ε)) := by
  classical
  let η : ℝ := min (ε/1000) (1/100)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ 1/100 := min_le_right _ _
  have hηeps : η ≤ ε/1000 := min_le_left _ _
  obtain ⟨C,hC,hLV⟩ := hlargeValues η hη hηsmall
  have hloglim := (isLittleO_log_rpow_rpow_atTop (2:ℝ) hη).tendsto_div_nhds_zero
  norm_num at hloglim
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ), general_powered_cover hη,
    shortPoweredDetectorFamily_coefficients hη,
    (tendsto_rpow_atTop hη).eventually_ge_atTop ((2:ℝ)^99),
    (tendsto_rpow_atTop (show (0:ℝ)<69/100 by norm_num)).eventually_ge_atTop 2,
    hloglim.eventually (gt_mem_nhds (show (0:ℝ)<1/600000 by norm_num))]
    with H hH hfamily hcoeff hconst hlength hlog
  intro R hR₀ hcard hsep hlarge
  have hR ρ (hρ : ρ ∈ R) : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ.im ∈ Icc H (H+H) ∧
      (1/3:ℝ) ≤ ‖shortFiniteDetector ρ H‖ := by
    obtain ⟨hz,hβ,hlo,hhi⟩ := mem_zetaZeroFinset.mp (hR₀ hρ)
    exact ⟨hβ,hz.2.2.le,⟨hlo,by linarith⟩,hlarge ρ hρ⟩
  have hHpos : 0 < H := by linarith
  have hHa : 1 ≤ H := by linarith
  let J := (shortPoweredDetectorIndices H).filter (fun q =>
    H^(a) ≤ (shortPoweredDetectorScale q:ℝ) ∧
    (shortPoweredDetectorScale q:ℝ) ≤ (2:ℝ)^99*H^(3*a/2) ∧
    2*(shortPoweredDetectorScale q:ℝ) ≤ H^2)
  let W := R.image Complex.im
  let Wj := fun q => W.filter (fun t =>
    (shortPoweredDetectorScale q:ℝ)^σ*H^(-2*η) ≤
      ‖detectingPolynomial (shortPoweredDetectorScale q) (shortPoweredDetectorFamilyCoeff η H q) t‖)
  have hWj : ∀ q ∈ J, ((Wj q).card:ℝ) ≤ C*H^(p+18*η) := by
    intro q hp
    obtain ⟨hp,hlow,hhigh,hsupport⟩ := Finset.mem_filter.mp hp
    have hN : 2 ≤ (shortPoweredDetectorScale q:ℝ) :=
      hlength.trans ((Real.rpow_le_rpow_of_exponent_le hHa ha).trans hlow)
    have hupper : (shortPoweredDetectorScale q:ℝ) ≤ H^(3*a/2+η) := by
      calc
        _ ≤ (2:ℝ)^99*H^(3*a/2) := hhigh
        _ ≤ H^η*H^(3*a/2) := mul_le_mul_of_nonneg_right hconst (by positivity)
        _ = _ := by rw [← Real.rpow_add hHpos]; congr 1; ring
    have hc : ∀ n ∈ sourceRatioIndices (shortPoweredDetectorScale q:ℝ),
        ‖shortPoweredDetectorFamilyCoeff η H q n‖ ≤ 1 := by
      intro n hn
      apply hcoeff q hp hsupport n
      simpa only [sourceRatioIndices, show 2*(shortPoweredDetectorScale q:ℝ) =
        ((2*shortPoweredDetectorScale q:ℕ):ℝ) by push_cast; rfl, Nat.floor_natCast] using hn
    apply hLV H (shortPoweredDetectorScale q:ℝ) H
      (shortPoweredDetectorFamilyCoeff η H q) (Wj q) hH hN hlow hupper hc
    · intro t ht
      obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
      exact (hR ρ hρ).2.2.1
    · intro t ht s hs hne
      exact hsep t (Finset.mem_filter.mp ht).1 s (Finset.mem_filter.mp hs).1 hne
    · intro t ht
      simpa only [← detectingPolynomial_eq_boundedPolynomial] using (Finset.mem_filter.mp ht).2
  have hcover : W ⊆ J.biUnion Wj := by
    intro t ht
    obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hβ,hβ',_hloc,hd⟩ := hR ρ hρ
    obtain ⟨q,hp,hlo,hhi,hsupport,hlarge⟩ := hfamily.2 (a) σ ρ
      ha ha' (by linarith [hσ]) hβ hβ' hd
    apply Finset.mem_biUnion.mpr
    refine ⟨q,Finset.mem_filter.mpr ⟨hp,hlo,hhi,hsupport⟩,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨ρ,hρ,rfl⟩,hlarge⟩
  have hJ : (J.card:ℝ) ≤ H^η := by
    have hsmall : 600000*(Real.log H)^2 ≤ H^η := by
      have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hHpos η)).mp hlog
      linarith
    exact (show (J.card:ℝ) ≤ (shortPoweredDetectorIndices H).card by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)).trans (hfamily.1.trans hsmall)
  have hsum : (W.card:ℝ) ≤ (J.card:ℝ)*(C*H^(p+18*η)) := by
    calc
      _ ≤ ∑ q ∈ J, ((Wj q).card:ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ J, C*H^(p+18*η) := Finset.sum_le_sum hWj
      _ = _ := by simp
  have hpow : H^(p+19*η) ≤ H^(p+ε) :=
    Real.rpow_le_rpow_of_exponent_le hHa (by linarith)
  calc
    _ = (W.card:ℝ) := by rw [hcard]
    _ ≤ (J.card:ℝ)*(C*H^(p+18*η)) := hsum
    _ ≤ H^η*(C*H^(p+18*η)) :=
      mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = C*H^(p+19*η) := by
      rw [← mul_left_comm, ← Real.rpow_add hHpos]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hC.le

/-- A single covering and counting argument for all three energy estimates. -/
theorem density_of_window_large_values {σ a p ε : ℝ} (hσ : 9/13 ≤ σ)
    (ha : 69/100 ≤ a) (ha' : a ≤ 4/5) (hp : 0 ≤ p) (hII : 2-2*σ+1/50 ≤ p)
    (hε : 0 < ε) (hLV : ∀ δ, 0 < δ → δ ≤ 1/100 → WindowLargeValues σ a p δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (zetaDensityCount σ T:ℝ) ≤ C*T^(p+ε) :=
  short_density_of_typeI hσ hp hII hε fun _ hδ => window_typeI hσ ha ha' hδ hLV

end Montgomery.RationalMoment
