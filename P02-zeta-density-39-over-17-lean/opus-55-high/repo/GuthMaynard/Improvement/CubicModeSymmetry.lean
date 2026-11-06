module
public import GuthMaynard.Improvement.CubicMixedBox
import WeylPort.Analytic.RealLaplace

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace GuthMaynard.Improvement

def negateCubicMode (m : ℤ × (ℤ × ℤ)) : ℤ × (ℤ × ℤ) := (-m.1,-m.2.1,-m.2.2)
def InSignedCubicBox (B K D : ℝ) (m : ℤ × (ℤ × ℤ)) : Prop :=
  B ≤ |(m.1:ℝ)| ∧ |(m.1:ℝ)| ≤ 2*B ∧ K ≤ |(m.2.1:ℝ)| ∧
    |(m.2.1:ℝ)| ≤ 2*K ∧ D ≤ |(m.2.2:ℝ)| ∧ |(m.2.2:ℝ)| ≤ 2*D

theorem negateCubicMode_involutive : Function.Involutive negateCubicMode := by
  intro m
  simp [negateCubicMode]

theorem negateCubicMode_injective : Function.Injective negateCubicMode :=
  negateCubicMode_involutive.injective

theorem cubicStripMass_negate (r : ℝ → ℝ) (L H : ℝ) (m : ℤ × (ℤ × ℤ)) (v : ℝ) :
    cubicStripMass r L H (negateCubicMode m) v = cubicStripMass r L H m v := by
  unfold cubicStripMass negateCubicMode
  have hlin (y : ℝ) : L*(((-m.1:ℤ):ℝ)*v+((-m.2.1:ℤ):ℝ)*y+((-m.2.2:ℤ):ℝ)) =
      -(L*((m.1:ℝ)*v+(m.2.1:ℝ)*y+(m.2.2:ℝ))) := by push_cast; ring
  grind

theorem cubicStripMass_sum_negate (S : Finset (ℤ × (ℤ × ℤ))) (r : ℝ → ℝ) (L H v : ℝ) :
    (∑ m ∈ S.image negateCubicMode, cubicStripMass r L H m v) =
      ∑ m ∈ S, cubicStripMass r L H m v := by
  pm_555 negateCubicMode_injective
  simp only [cubicStripMass_negate]

section
variable {B K D : ℝ} {m : ℤ × (ℤ × ℤ)} (hbox : InSignedCubicBox B K D m)
include B K D m hbox
theorem signed_box_positive (hm : 0 < m.2.1) : InCubicBox B K D m := by
  have hm' : (0:ℝ) < (m.2.1:ℝ) := by exact_mod_cast hm
  simpa only [InSignedCubicBox,InCubicBox,abs_of_pos hm'] using hbox

theorem signed_box_negative (hm : m.2.1 < 0) : InCubicBox B K D (negateCubicMode m) := by
  have hm' : (m.2.1:ℝ) < 0 := by exact_mod_cast hm
  simpa only [InSignedCubicBox,InCubicBox,negateCubicMode,Int.cast_neg,abs_neg,abs_of_neg hm'] using hbox
end

/-- Two sign pieces, counted separately even when normalized images overlap.
There is no injectivity claim across the union of the two pieces. -/
theorem cubicStripMass_sign_split (S : Finset (ℤ × (ℤ × ℤ)))
    (hS : ∀ m ∈ S, m.2.1 ≠ 0) (r : ℝ → ℝ) (L H v : ℝ) :
    (∑ m ∈ S, cubicStripMass r L H m v) =
      (∑ m ∈ S.filter (fun m => 0 < m.2.1), cubicStripMass r L H m v) +
      ∑ m ∈ (S.filter (fun m => m.2.1 < 0)).image negateCubicMode, cubicStripMass r L H m v := by
  rw [cubicStripMass_sum_negate]
  have hfilters : S.filter (fun m => ¬ 0 < m.2.1) = S.filter (fun m => m.2.1 < 0) := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · intro hm; exact ⟨hm.1,lt_of_le_of_ne (le_of_not_gt hm.2) (hS m hm.1)⟩
    · intro hm; exact ⟨hm.1,not_lt_of_ge hm.2.le⟩
  simpa only [hfilters] using
    (Finset.sum_filter_add_sum_filter_not S (fun m => 0 < m.2.1) (fun m => cubicStripMass r L H m v)).symm

/-- Actual mixed strip-box bound for arbitrary signs in all three modes.
Exactly two denominator-sign pieces account for the factor two in the
constant; the designated Fourier mask remains unchanged. -/
theorem signed_cubic_mixed_box (a b c d : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T R K B D L H : ℝ) (r₀ r : ℝ → ℝ)
      (A₀ : Set ℝ) (S : Finset (ℤ × (ℤ × ℤ))),
      2 ≤ T → 1 ≤ K → K ≤ R → 1 ≤ B → B ≤ R → 1 ≤ D → D ≤ R → R ≤ T^4 →
      0 < L → 0 < H →
      max 1 (1/a)*(H/(L*K)) ≤ 1 → max 1 (1/a)*(H/(L*K)) ≤ c/4 →
      (max 1 (1/a)*(H/(L*K)))⁻¹ ≤ T →
      MeasurableSet A₀ → Measurable r₀ → MemLp r₀ 2 → (∀ v, 0 ≤ r₀ v) →
      Measurable r → Integrable (fun x => r x^2) → Integrable (fun x => r x^4) →
      (∀ x, 0 ≤ r x) → (∀ x, x ∉ Icc c d → r x = 0) →
      (∀ m ∈ S, InSignedCubicBox B K D m) →
      IntegrableOn (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) (Icc a b) ∧
      (∫ v in Icc a b, A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) ≤
        C*(H/(L*K))*Real.sqrt (∫ v in A₀, r₀ v^2 ∂volume.restrict (Icc a b))*
          Real.sqrt (T^ε*(R^2*K^4*(∫ x, r x^2)^2+R*K^3*(∫ x, r x^4))) := by
  obtain ⟨C,hC,h⟩ := cubic_mixed_box a b c d ha hab hc hcd hε
  refine ⟨2*C,by positivity,?_⟩
  pm_4592
  let P := S.filter (fun m => 0 < m.2.1)
  let N := (S.filter (fun m => m.2.1 < 0)).image negateCubicMode
  have hP : ∀ m ∈ P, InCubicBox B K D m := by
    pm_161 m hm hmS hm0 Finset.mem_filter.mp
    exact signed_box_positive (hbox m hmS) hm0
  have hN : ∀ m ∈ N, InCubicBox B K D m := by
    pm_67 m hm n hn Finset.mem_image.mp
    obtain ⟨hnS,hn0⟩ := Finset.mem_filter.mp hn
    exact signed_box_negative (hbox n hnS) hn0
  have hnonzero : ∀ m ∈ S, m.2.1 ≠ 0 := by
    intro m hm hz
    have hh := (hbox m hm).2.2.1
    rw [hz,Int.cast_zero,abs_zero] at hh
    linarith
  pm_5198 hiP hbP P hP
  pm_5198 hiN hbN N hN
  have heq : (fun v => A₀.indicator r₀ v * ∑ m ∈ S, cubicStripMass r L H m v) =
      (fun v => A₀.indicator r₀ v * ∑ m ∈ P, cubicStripMass r L H m v) +
      (fun v => A₀.indicator r₀ v * ∑ m ∈ N, cubicStripMass r L H m v) := by
    funext v
    rw [cubicStripMass_sign_split S hnonzero r L H v,mul_add]
    rfl
  refine ⟨by rw [heq]; exact hiP.add hiN,?_⟩
  rw [heq]
  simp only [Pi.add_def]
  rw [integral_add hiP hiN]
  nlinarith only [hbP,hbN]

end GuthMaynard.Improvement
