module
/- Generalized from the attributed McColm peak-cluster proof in the verified baseline.
The actual native point-mean theorem is supplied here; the general-pair local count
remains an internal interface to be discharged by the analytic pair producer. -/
public import GenericMeanCounting
public import MathCollab.Density.Stronger.PointMean.PeaksInput
import WeylPort.Analytic.RealLaplace

public section
open Finset MeasureTheory
namespace Montgomery.CriticalPeak
open MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
theorem exists_pointCluster_superlevel_count
    {a g b : ℝ} (hCount : LocalMeanCount a g b)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ) (m : ℕ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) → 0 < m →
        ((pointClusterSuperlevel H G W m).card:ℝ) ≤
          2*D*H^ν*
            (H/(G*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^2) +
              H^a/(G^g*((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^b)) := by
  obtain ⟨P,hP,hentry⟩ := (exists_pointCluster_superlevel_entry PointMean.pointMeanInput_native)
  obtain ⟨C,hC,D,hD,H₀,hH₀,hcount⟩ :=
    hCount δ κ ν hδ hκ hν
  pm_4486
  have hcolor : ∀ e : ℕ,
      ((S.filter (fun n => n%2 = e)).card:ℝ) ≤
        D*H^ν*(H/(G*Y^2)+H^a/(G^g*Y^b)) := by
    pm_4485
  pm_4487
  change (S.card:ℝ) ≤ 2*D*H^ν*(H/(G*Y^2)+H^a/(G^g*Y^b))
  pm_6938

theorem occupancy_inverse_power_budget {a g b H G A m : ℝ}
    (hH : 0 < H) (hG : 0 < G) (hA : 0 < A) (hm : 1 ≤ m) (hb : 2 ≤ b) :
    H/(G*(m*A)^2)+H^a/(G^g*(m*A)^b) ≤
      (H/(G*A^2)+H^a/(G^g*A^b))/m^2 := by
  have hm0 : 0 < m := by linarith
  have hp : m^2 ≤ m^b := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hm hb
  rw [mul_pow, Real.mul_rpow hm0.le hA.le]
  calc
    _ ≤ H/(G*(m^2*A^2))+H^a/(G^g*(m^2*A^b)) := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hH a).le (by positivity)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
    _ = _ := by field_simp

theorem exists_pointValue_card_le_with_width
    {a g b : ℝ} (hb : 2 ≤ b) (hCount : LocalMeanCount a g b)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ P C D H₀ : ℝ, 0 < P ∧ 0 < C ∧ 0 < D ∧ 40000 ≤ H₀ ∧
      ∀ (H G V : ℝ) (W : Finset ℝ),
        H₀ ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        (∀ t : ℝ, H ≤ t → t ≤ 2*H →
          t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
        2*P*Real.log (3*H) ≤ V^2 →
        C*G*Real.log (3*H) ≤ V^2/(16*P*Real.log (3*H)) →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        (W.card:ℝ) ≤ D*H^ν*
          (H/(G*(V^2/(16*P*Real.log (3*H)))^2) +
            H^a/(G^g*(V^2/(16*P*Real.log (3*H)))^b)) := by
  obtain ⟨P,C,D,H₀,hP,hC,hD,hH₀,hcount⟩ :=
    (exists_pointCluster_superlevel_count hCount) hδ hκ hν
  pm_4490
  let B : ℝ := 2*D*H^ν*(H/(G*A^2)+H^a/(G^g*A^b))
  pm_4489
  have hsuper : ∀ m : ℕ, 0 < m →
      (((pointClusterBins H G W).filter
        (fun n => m ≤ (pointCluster H G W n).card)).card:ℝ) ≤ B/(m:ℝ)^2 := by
    pm_4491
    have hp := occupancy_inverse_power_budget (a := a) (g := g) hHpos hG hA hm1 hb
    calc
      _ ≤ 2*D*H^ν*(H/(G*((m:ℝ)*A)^2)+H^a/(G^g*((m:ℝ)*A)^b)) := hc
      _ ≤ 2*D*H^ν*((H/(G*A^2)+H^a/(G^g*A^b))/(m:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = B/(m:ℝ)^2 := by dsimp only [B]; ring
  pm_4488
  calc
    (W.card:ℝ) ≤ 2*B := hsum
    _ = (4*D)*H^ν*(H/(G*A^2)+H^a/(G^g*A^b)) := by dsimp only [B]; ring



end Montgomery.CriticalPeak
