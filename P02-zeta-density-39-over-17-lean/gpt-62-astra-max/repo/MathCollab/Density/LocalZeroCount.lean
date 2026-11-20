module
/-
The Jensen proof is adapted from Scott McColm's ExtractSeparated.lean at
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT. The original Type-I set is
replaced by the existing actual-zero set; only rectangle membership is used.
-/
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalDensity
public import MathCollab.Density.ZeroSeparation

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators


set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

open GuthMaynard.NativeMoment

/-- Identify the two finite support conventions before summing the same
analytic orders. On a positive cutoff zeta has no zeros on the right edge. -/
theorem zerosInRect_eq {σ a b : ℝ} (hs : 0 < σ) :
    zerosInRect σ 1 a b = zetaZeroFinset σ a b := by
  ext z
  simp only [zerosInRect, Set.Finite.mem_toFinset, mem_inter_iff, mem_ZeroRectangle,
    mem_zetaZeroFinset, IsNontrivialZetaZero]
  constructor
  · rintro ⟨⟨hl,_,ha,hb⟩,hz⟩
    exact ⟨⟨hz,hs.trans_le hl,lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz)⟩,hl,ha,hb⟩
  · rintro ⟨⟨hz,_,hr⟩,hl,ha,hb⟩; exact ⟨⟨hl,hr.le,ha,hb⟩,hz⟩

theorem zeta_local_multiplicity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → 2 ≤ T → ∀ k : ℤ,
      (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ C*Real.log (2*T) := by
  classical
  let D : ℝ := Real.log ((7/4 : ℝ)/(8/5 : ℝ))
  let K : ℝ := 100/D
  let T₀ : ℝ := max (Real.exp 2) 8
  have hD : 0 < D := by dsimp [D]; apply Real.log_pos; norm_num
  have hK : 0 < K := div_pos (by norm_num) hD
  have hT₀ : 8 ≤ T₀ := le_max_right _ _
  have hlarge : ∀ σ T : ℝ, 1/2 ≤ σ → T₀ ≤ T → ∀ k : ℤ,
      (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ K*Real.log (2*T) := by
    intro σ T hσ hT k
    have hT8 : 8 ≤ T := hT₀.trans hT
    have hTexp : Real.exp 2 ≤ T := (le_max_left _ _).trans hT
    have hTpos : 0 < T := by linarith
    have hlog : 2 ≤ Real.log T := by
      simpa using Real.log_le_log (Real.exp_pos 2) hTexp
    have hraw := zeroUnitBin_multiplicity_le_jensen σ T k hσ hT8
    rw [zeroUnitBin, zerosInRect_eq (by linarith)] at hraw
    have hnum : Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ)) ≤ 100*Real.log T := by
      have hconst := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500/3 by norm_num)
      calc
        Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ)) =
            Real.log ((500/3 : ℝ)*T^(3 : ℝ)) := by congr 1; ring
        _ = Real.log (500/3 : ℝ)+3*Real.log T := by
          rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTpos 3).ne',
            Real.log_rpow hTpos]
        _ ≤ _ := by nlinarith
    have hcast :
        (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
          (zetaMultiplicity ρ : ℝ)) ≤
          Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ))/D := by
      simpa only [D, Nat.cast_sum, ordinateBin_eq_iff, analyticVanishingOrder, zetaMultiplicity] using hraw
    calc
      _ ≤ Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ))/D := hcast
      _ ≤ (100*Real.log T)/D := div_le_div_of_nonneg_right hnum hD.le
      _ = K*Real.log T := by dsimp [K]; ring
      _ ≤ K*Real.log (2*T) := mul_le_mul_of_nonneg_left
        (Real.log_le_log hTpos (by linarith)) hK.le
  let Q : ℝ := zetaDensityCount (1/2) (2*T₀)
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨K+Q/Real.log 4+1, by positivity, ?_⟩
  intro σ T hσ hT k
  have hTpos : 0 < T := by linarith
  have hloglow : Real.log 4 ≤ Real.log (2*T) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlognonneg : 0 ≤ Real.log (2*T) := hlog4.le.trans hloglow
  by_cases hlargeT : T₀ ≤ T
  · exact (hlarge σ T hσ hlargeT k).trans
      (mul_le_mul_of_nonneg_right (by
        have hq := div_nonneg hQ hlog4.le
        linarith) hlognonneg)
  · have hTupper : T ≤ T₀ := (not_le.mp hlargeT).le
    have hcount : zetaSlabCount σ T (2*T) ≤ zetaDensityCount (1/2) (2*T₀) :=
      zetaSlabCount_mono hσ (by linarith) (by linarith)
    have hfilter :
        (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
          zetaMultiplicity ρ) ≤ zetaSlabCount σ T (2*T) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hsum :
        (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
          (zetaMultiplicity ρ : ℝ)) ≤ Q := by
      dsimp [Q]
      exact_mod_cast hfilter.trans hcount
    calc
      _ ≤ Q := hsum
      _ = (Q/Real.log 4)*Real.log 4 := (div_mul_cancel₀ Q hlog4.ne').symm
      _ ≤ (Q/Real.log 4)*Real.log (2*T) :=
        mul_le_mul_of_nonneg_left hloglow (div_nonneg hQ hlog4.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlognonneg

end MathCollab.Density
