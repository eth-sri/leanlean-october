module
public import MathCollab.Density.Stronger.ShortExponentAccounting
public import MathCollab.Density.IndexedZeroLargeValues
public import MathCollab.Density.LocalZeroCount
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Real Complex Filter
open scoped Topology


noncomputable section
namespace MathCollab.Density.Stronger

/-- The actual-multiplicity large-values bridge for an explicit finite subset
of slab zeros. Only the selected subset needs to be covered; it is never silently
replaced by the whole zero set. The displayed local and detection premises remain explicit. -/
theorem zetaSubset_large_values_cover_indexed {ι : Type*} {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ lo hi H B : ℝ) (J : Finset ι)
      (N : ι → ℕ) (V : ι → ℝ) (coeff : ι → ℕ → ℂ) (S : Finset ℂ),
      S ⊆ zetaZeroFinset σ lo hi →
      2 ≤ H → 0 ≤ B → hi ≤ lo+H →
      (∀ k : ℤ, (∑ ρ ∈ (zetaZeroFinset σ lo hi).filter
        (fun ρ => ordinateBin ρ = k), (zetaMultiplicity ρ : ℝ)) ≤ B) →
      (∀ j ∈ J, 0 < N j ∧ 0 < V j ∧ H^(1/3 : ℝ) ≤ (N j : ℝ) ∧
        (N j : ℝ) ≤ H ∧ (N j : ℝ)^(3/4+κ) ≤ V j ∧
        ∀ n ∈ Finset.Ioc (N j) (2*N j), ‖coeff j n‖ ≤ 1) →
      (∀ ρ ∈ S, ∃ j ∈ J,
        V j ≤ ‖detectingPolynomial (N j) (coeff j) ρ.im‖) →
      (∑ ρ ∈ S, (zetaMultiplicity ρ : ℝ)) ≤ C*B*H^ε*
        ∑ j ∈ J, ((N j : ℝ)^2/(V j)^2+(N j : ℝ)^3*Real.sqrt H/(V j)^4) := by
  classical
  pm_98 C hC hLV large_values hκ hε
  refine ⟨2*C, by positivity, ?_⟩
  intro σ lo hi H B J N V coeff S hS hH hB hhi hlocal hadm hcover
  have hbin (k : ℤ) : (∑ ρ ∈ S.filter (fun ρ => ordinateBin ρ = k),
      (zetaMultiplicity ρ : ℝ)) ≤ B := by
    have hs : S.filter (fun ρ => ordinateBin ρ = k) ⊆
        (zetaZeroFinset σ lo hi).filter (fun ρ => ordinateBin ρ = k) := by
      intro ρ hρ
      exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hρ).1, (Finset.mem_filter.mp hρ).2⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)).trans (hlocal k)
  obtain ⟨R, hR, hcard, hsep, hcount⟩ := weighted_separated_extraction S
    (fun ρ => (zetaMultiplicity ρ : ℝ)) hB hbin
  pm_4292
  have hWj : ∀ j ∈ J, ((Wj j).card : ℝ) ≤ C*H^ε*F j := by
    pm_4293
    · refine ⟨lo, ?_⟩
      pm_6294
      have hz := mem_zetaZeroFinset.mp (hS (hR hρ))
      exact ⟨hz.2.2.1, hz.2.2.2.trans hhi⟩
    pm_4294
  pm_4291

/-- Actual slab zeros detected by the fixed normalized short family. -/
def smoothShortZeroFinset (η σ δ T : ℝ) : Finset ℂ := by
  classical
  exact (zetaZeroFinset σ T (2*T)).filter (fun ρ =>
    ∃ q ∈ smoothPoweredIndices σ δ T,
      (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η) ≤
        ‖detectingPolynomial (smoothPoweredFamilyScale q)
          (smoothPoweredFamilyCoefficient η σ δ T q) ρ.im‖)

/-- Count this explicit subset with the original analytic multiplicities. -/
def smoothShortZeroCount (η σ δ T : ℝ) : ℕ :=
  ∑ ρ ∈ smoothShortZeroFinset η σ δ T, zetaMultiplicity ρ

theorem smoothShortZeroFinset_subset (η σ δ T : ℝ) :
    smoothShortZeroFinset η σ δ T ⊆ zetaZeroFinset σ T (2*T) := by
  classical
  exact Finset.filter_subset _ _

/-- The short part of the actual analytic-multiplicity count has the stronger
exponent. No assertion about the number of long zeros is used. -/
theorem smoothShortZeroCount_bound {σ η : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hη : 0 < η) (hmargin : 8*η < σ-3/4) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothShortZeroCount η σ δ T : ℝ) ≤ C*T^(densityExponent σ+12*η) := by
  classical
  pm_7846
  let K := smoothPowerBound σ δ
  let A : ℝ := 288*(K : ℝ)^2*((2 : ℝ)^K+32)
  pm_61 hA A
  pm_358 hκ κ
  pm_1583
  obtain ⟨Cv, hCv, hbound⟩ := zetaSubset_large_values_cover_indexed
    (ι := (ℤ × ℕ × ℕ) × ℕ × ℕ) hκ hη
  obtain ⟨Cb, hCb, hlocal⟩ := zeta_local_multiplicity_bound
  refine ⟨(A+1)*Cv*Cb, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    smoothPoweredFamily_largeValues_admissible hσ hσ'.le hη hm δ,
    smooth_family_sum_eventually hη hσ hσ'.le δ] with T hT hadm hsum
  pm_233 hlog T
  have hcount := hbound σ T (2*T) (densityAmbient T) (Cb*Real.log (2*T))
    (smoothPoweredIndices σ δ T) smoothPoweredFamilyScale
    (fun q => (smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η))
    (smoothPoweredFamilyCoefficient η σ δ T) (smoothShortZeroFinset η σ δ T)
    (smoothShortZeroFinset_subset η σ δ T) hadm.1 (by positivity) hadm.2.1
    (hlocal σ T hσ.le hT) hadm.2.2
    (by intro ρ hρ; exact (Finset.mem_filter.mp hρ).2)
  have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ Cv*Cb by positivity)
  calc
    _ = ∑ ρ ∈ smoothShortZeroFinset η σ δ T, (zetaMultiplicity ρ : ℝ) := by
      rw [smoothShortZeroCount, Nat.cast_sum]
    _ ≤ _ := hcount
    _ = (Cv*Cb)*(Real.log (2*T)*(densityAmbient T)^η*
        (∑ q ∈ smoothPoweredIndices σ δ T,
          ((smoothPoweredFamilyScale q : ℝ)^2/((smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η))^2+
          (smoothPoweredFamilyScale q : ℝ)^3*Real.sqrt (densityAmbient T)/
            ((smoothPoweredFamilyScale q : ℝ)^σ*T^(-2*η))^4))) := by ring
    _ ≤ (Cv*Cb)*(A*T^(densityExponent σ+12*η)) := hh
    _ ≤ ((A+1)*Cv*Cb)*T^(densityExponent σ+12*η) := by
      have hp : 0 ≤ (Cv*Cb)*T^(densityExponent σ+12*η) := by positivity
      nlinarith

end MathCollab.Density.Stronger
