module
public import PottsDiscontinuity.RCMProof.SectorUpper
public import PottsDiscontinuity.SixVertex.Sec33Dominance

/-! # From fixed-sector rates to the centered Perron root

For `q > 4`, the corrected loop expectation costs zero on the height
exponential scale as the width tends to infinity. The sector tail estimate
then excludes *all* maximizers at distance at least two. The Bethe ratio at
one excludes distance one. Finally we can send the fixed sector to infinity.
-/
@[expose] public section
open Finset Filter Topology
namespace PottsDiscontinuity.RCMProof
open SixVertex Torus TorusRC

variable (h₁ : contract_cor313_i) (h₃ : contract_cor313_iii) (h₆ : contract_eq316)
    (q : Set.Ici (1:ℝ)) (hh319 : h319 q) (hq : 4 < q.val)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ)
    (ξ : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0,0) (diagonalSite n))) / (n:ℝ)) atTop (𝓝 ξ)) {S : ℝ}
    (hS : Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val/2))) atTop (𝓝 S))
include hq hS

private lemma log_bethe_ratio (r : ℕ) (hr : 1 ≤ r) :
    let c := criticalSixVertexParameter q
    Tendsto (fun i : ℕ => Real.log (Lambda c (4*i) r / Lambda c (4*i) 0)) atTop
      (𝓝 (-(r:ℝ)*(Real.arcosh (Real.sqrt q.val/2) + 2*S))) := by
  obtain ⟨B,T,hT,hratio⟩ := apply_17_at_critical_c hq hr
  obtain rfl := tendsto_nhds_unique hT hS
  apply (tendsto_add_atTop_iff_nat B).mp
  simpa only [Function.comp_def, criticalSixVertexParameter, Real.log_exp] using
    (Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp hratio

include h₁ h₃ h₆ hh319 hμ hRate in
theorem rc_xi_inverse_le_critical_rate
    (hpos : 0 < Real.arcosh (Real.sqrt q.val/2) + 2*S)
    (hlo : Real.arcosh (Real.sqrt q.val/2) + 2*S ≤ ξ) : ξ ≤ Real.arcosh (Real.sqrt q.val/2) + 2*S := by
  let c := criticalSixVertexParameter q
  let R := Real.arcosh (Real.sqrt q.val/2) + 2*S
  have hc : 0 < c := by dsimp [c,criticalSixVertexParameter]; positivity
  have gaps := sector_gaps_eventually h₁ h₃ h₆ q hq hh319 μ hμ ξ hRate
  have hlog := log_bethe_ratio q hq hS
  have hb : Tendsto (fun i : ℕ => 4*i) atTop atTop := by
    apply tendsto_atTop.2; intro k; filter_upwards [eventually_ge_atTop k] with i hi; omega
  have first : ∀ᶠ i : ℕ in atTop, Real.log (Lambda c (4*i) 1 / Lambda c (4*i) 0) < 0 :=
    (hlog 1 le_rfl).eventually (Iio_mem_nhds (by simpa using neg_lt_zero.mpr hpos))
  have hξ := hpos.trans_le hlo
  have center : ∀ᶠ i : ℕ in atTop, LambdaMax c (4*i) = Lambda c (4*i) 0 := by
    filter_upwards [first,hb.eventually (gaps 2 (by decide) (ξ/2) (half_pos hξ))] with i h₁ h₂
    have he : Even (4*i) := ⟨2*i,by omega⟩
    obtain ⟨n,hn,hmax⟩ := exists_pfRoot_eq_LambdaMax (c := c) (N := 4*i)
    obtain ⟨r,hr,hroot⟩ := exists_Lambda_offset_eq_pfRoot he hn (c := c)
    have hmr := hmax.symm.trans hroot
    rcases r with _|(_|r)
    · exact hmr
    · have hm : Lambda c (4*i) 0 ≤ LambdaMax c (4*i) := pfRoot_transferBlock_le_LambdaMax (by omega)
      have hp := Lambda_pos (N := 4*i) hc (r := 0) (by omega)
      exact (not_le_of_gt (div_lt_one hp |>.mp ((Real.log_neg_iff (div_pos (Lambda_pos hc hr) hp)).mp h₁)) (hmr ▸ hm)).elim
    · have h := h₂ he (r+2) (by omega) hr
      rw [← hmr, sub_self] at h; norm_num at h; linarith
  have bound (s : ℕ) (hs : 1 ≤ s) : -(s:ℝ)*R ≤ -((s-1:ℕ):ℝ)*ξ + 1 := by
    apply le_of_tendsto (hlog s hs)
    filter_upwards [center,hb.eventually (gaps s hs 1 zero_lt_one),eventually_ge_atTop s] with i hi hg hsi
    have hr : s ≤ 4*i/2 := by omega
    have h := hg ⟨2*i,by omega⟩ s le_rfl hr
    change Real.log (Lambda c (4*i) s / Lambda c (4*i) 0) ≤ _
    rw [Real.log_div (Lambda_pos hc hr).ne' (Lambda_pos hc (by omega)).ne', ← hi]; exact h
  by_contra! h
  obtain ⟨k,hk⟩ := exists_nat_gt ((R+1)/(ξ-R))
  have h' := (div_lt_iff₀ (show 0 < ξ-R by dsimp [R]; linarith)).mp hk
  have hbound := bound (k+1) (by omega)
  simp only [Nat.add_sub_cancel, Nat.cast_add,Nat.cast_one] at hbound
  nlinarith

end PottsDiscontinuity.RCMProof
