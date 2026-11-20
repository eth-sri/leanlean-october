module

public import OAI.NumberTheory.DirichletL.PrimeRows.DetectorZeros

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily
variable {ι : Type*} [Fintype ι]

lemma detector_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e))
    (hpole : ¬((χ j).residue=1 ∧ s=1)) : LFunction (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr hi
  have hre : a+2*e≤s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  refine detector_nonzero_above_maximum χ _ j (hmax.trans_le hre) ?_ hpole
  have ht' := abs_add_le (s.im-t) t
  rw [sub_add_cancel] at ht'
  push_cast at ht ⊢
  nlinarith [hi.trans hn]

lemma detectorEntire_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e)) :
    detectorEntire (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr
  have hre : 0<s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  intro hz
  obtain ⟨hL,hpole⟩ := (detectorEntire_zero_iff (χ j) hre).mp hz
  exact detector_nonzero_on_buffered_disk χ T a e i hT ha he hmax j t ht hs hpole hL

/-- The bin indices and zero bounds needed to estimate the high rows. -/
structure CubeBin (χ : ι → Character) (T e : ℝ) (n i k : ℕ) : Prop where
  height_index : i ≤ n
  grid_index : k ≤ ⌊(49/100:ℝ)/e⌋₊
  alpha_le_one : (51/100:ℝ) + e*k ≤ 1
  lower : (51/100:ℝ) + e*k ≤ detectorMaximum χ ((3*i:ℕ)*T)
  next : detectorMaximum χ (3*(i+1:ℕ)*T) < (51/100:ℝ) + e*k + 2*e

lemma exists_detector_buffered_bin (χ : ι → Character) (T e : ℝ) (he : 0<e)
    (n : ℕ) (hn : 0<n) (hwidth : (49/100:ℝ)≤n*e) :
    ∃ i k, CubeBin χ T e n i k := by
  obtain ⟨i, hi, k, ha, hlo, _, hnext⟩ := Detector.exists_buffered_bin
    (fun j => detectorMaximum χ ((3*(j+1):ℕ)*T)) hn he
    (fun j _ => detectorMaximum_bounds χ _) hwidth
  refine ⟨i+1, k, by omega, Nat.le_floor ((le_div_iff₀ he).2 ?_), ha, hlo, ?_⟩
  · nlinarith
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnext

lemma detectorMaximum_eq_nonprincipal (χ : ι→Character) (hχ : ∀i,(χ i).residue≠1) (T : ℝ) :
    detectorMaximum χ T=HeckeDetectorZeros.zeroMaximum χ hχ T := by
  have hz (i : ι) : detectorZeroFinset (χ i) T=HeckeDetectorZeros.zeroFinset (χ i) (hχ i) T := by
    ext s
    simp [hχ i]
  have hr : detectorRealParts χ T=HeckeDetectorZeros.realParts χ hχ T := by
    simp only [detectorRealParts,HeckeDetectorZeros.realParts,detectorFamilyZeros,HeckeDetectorZeros.familyZeros,hz]
  unfold detectorMaximum HeckeDetectorZeros.zeroMaximum
  simp only [hr]

end SevenEighths.ProbeHighRowFamily

end

end OAI
