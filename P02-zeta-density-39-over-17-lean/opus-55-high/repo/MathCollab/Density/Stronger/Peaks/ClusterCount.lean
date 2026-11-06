module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Selected exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/PEAK_AGGREGATION_MANIFEST.json.
Mathlib dependencies retain their Apache-2.0 attribution.
PointMeanInput and LocalMeanPacketInput remain explicit unproved analytic inputs.
No unconditional high-value, twelfth-moment or stronger-density bound is asserted.
-/
public import MathCollab.Density.Stronger.Peaks.Clusters
public import MathCollab.Density.Stronger.FiniteOccupancy
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter MeasureTheory Set Topology Finset
open scoped Interval
open MathCollab.Density MathCollab.Density.Stronger
open TaoTrudgianYang2025 (eventually_const_log_pow_le_rpow
  eventually_const_height_log_pow_mul_rpow_le_rpow
  eventually_pointValue_sixth_power_source_range)
noncomputable section
namespace MathCollab.Density.Stronger.Peaks
theorem atkinsonLocalMeanExcess_threshold_iff {G t error Y : ℝ} (hY : 0 < Y) :
    Y ≤ atkinsonLocalMeanExcess G t error ↔
      error+Y ≤ ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2 := by
  unfold atkinsonLocalMeanExcess
  rw [le_max_iff]
  constructor
  grind
  grind
theorem exists_atkinsonLocalMeanExcess_card_le_above_fourthRoot
    (hPacket : LocalMeanPacketInput)
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → separatedAt G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t)) →
      (W.card:ℝ) ≤ D*H^ν*(H/(G*Y^2)+H^2/Y^6) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    hPacket δ κ (ν/3) hδ hκ (show 0 < ν/3 by linarith)
  refine ⟨C,hC,2*D+32*D^3,by positivity,B,hB,?_⟩
  intro H G Y W hH hG hY hSep hrange hlarge
  pm_4484
  have hH0 : 0 < H := by linarith
  have hA : 0 < D*H^(ν/3) := by positivity
  have hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ A : ℝ, (∀ t ∈ U, A ≤ t ∧ t ≤ A+atkinsonAbsorptionLength (D*H^(ν/3)) G Y) →
      (∑ t ∈ U, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        (D*H^(ν/3))*((U.card:ℝ)*H/G+(U.card:ℝ)^2*
          Real.sqrt (G*atkinsonAbsorptionLength (D*H^(ν/3)) G Y)) := by
    intro U hsub A hlocal
    have hsepU : separatedAt G U := by
      pm_203 hSep hsub
    exact hsource H G A (atkinsonAbsorptionLength (D*H^(ν/3)) G Y)
      U hH hG hsepU (fun t ht => hrange t (hsub ht)) hlocal
  have hc := atkinson_card_le_of_local_packets hA hH0.le hG hY
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hlarge hpacket
  exact hc.trans (atkinson_count_exponent_budget hD.le hH1 hG hY hν.le)


theorem exists_pointCluster_localMean_bound
    (hPointMean : PointMeanInput) :
    ∃ P : ℝ, 0 < P ∧ ∀ (H G V : ℝ) (W : Finset ℝ) (n : ℕ),
      20 ≤ H → 0 < G → G ≤ H → 0 < V →
      2*(Real.log (3*H))^2 ≤ G →
      oneSeparated W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      n ∈ pointClusterBins H G W →
      V^2*((pointCluster H G W n).card:ℝ) ≤
        P*Real.log (3*H)*(((pointCluster H G W n).card:ℝ) +
          4*(∫ u in pointClusterCenter H G n-G..pointClusterCenter H G n+G,
            zetaMomentCriticalNorm u^2)) := by
  pm_155 P hP hsource hPointMean
  intro H G V W n hH hG hGH hV hfit hsep hrange hlarge hn
  have hc := pointClusterCenter_range hG hrange hn
  have hsub := pointCluster_subset H G W n
  have hsep' : oneSeparated (pointCluster H G W n) := by
    pm_203 hsep hsub
  apply hsource (3*H) V (pointClusterCenter H G n) G
    ((Real.log (3*H))^2) (pointCluster H G W n)
    (by linarith) hV hG.le (sq_nonneg _) hsep'
    (pointCluster_symmetric_interval n hG (fun t ht => (hrange t ht).1))
    (by linarith [hc.1]) (by linarith [hc.2])
  · intro t ht
    have htR := hrange t (hsub ht)
    pm_301 hlt t
    have hmono : Real.log t ≤ Real.log (3*H) :=
      Real.log_le_log (by linarith) (by linarith)
    exact pow_le_pow_left₀ hlt hmono 2
  · linarith
  · intro t ht
    exact hlarge t (hsub ht)

theorem localMean_lower_bound_of_peak_mass
    {P L V R I : ℝ} (hP : 0 < P) (hL : 0 < L) (hR : 0 ≤ R)
    (hV : 2*P*L ≤ V^2)
    (hsource : V^2*R ≤ P*L*(R+4*I)) :
    2*R*(V^2/(16*P*L)) ≤ I := by
  have hmul := mul_le_mul_of_nonneg_right hV hR
  have hm : V^2*R ≤ 8*P*L*I := by nlinarith
  have hden : 0 < 8*P*L := by positivity
  calc
    2*R*(V^2/(16*P*L)) = (V^2*R)/(8*P*L) := by field_simp; ring
    _ ≤ I := (div_le_iff₀ hden).mpr (by nlinarith [hm])

theorem exists_pointCluster_superlevel_entry
    (hPointMean : PointMeanInput) :
    ∃ P : ℝ, 0 < P ∧
      ∀ (H G V error : ℝ) (W : Finset ℝ) (n m : ℕ),
        20 ≤ H → 0 < G → G ≤ H → 0 < V →
        2*(Real.log (3*H))^2 ≤ G →
        oneSeparated W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
        n ∈ pointClusterBins H G W → 0 < m →
        m ≤ (pointCluster H G W n).card →
        2*P*Real.log (3*H) ≤ V^2 →
        error ≤ V^2/(16*P*Real.log (3*H)) →
        error+(m:ℝ)*(V^2/(16*P*Real.log (3*H))) ≤
          ∫ u in pointClusterCenter H G n-G..pointClusterCenter H G n+G,
            zetaMomentCriticalNorm u^2 := by
  obtain ⟨P,hP,hsource⟩ := (exists_pointCluster_localMean_bound hPointMean)
  refine ⟨P,hP,?_⟩
  intro H G V error W n m hH hG hGH hV hfit hsep hrange hlarge hn hm hocc hVsize herr
  have hL : 0 < Real.log (3*H) := Real.log_pos (by linarith)
  have hI := localMean_lower_bound_of_peak_mass hP hL (Nat.cast_nonneg _)
    hVsize (hsource H G V W n hH hG hGH hV hfit hsep hrange hlarge hn)
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmr : (m:ℝ) ≤ ((pointCluster H G W n).card:ℝ) := by exact_mod_cast hocc
  have hA : 0 ≤ V^2/(16*P*Real.log (3*H)) := by positivity
  pm_194 hma mul_le_mul_of_nonneg_right hmr hA hmin hm1
  nlinarith



def pointClusterSuperlevel (H G : ℝ) (W : Finset ℝ) (m : ℕ) : Finset ℕ :=
  (pointClusterBins H G W).filter (fun n => m ≤ (pointCluster H G W n).card)

theorem exists_pointCluster_superlevel_count
    (hPointMean : PointMeanInput) (hPacket : LocalMeanPacketInput)
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
              H^2/((m:ℝ)*(V^2/(16*P*Real.log (3*H))))^6) := by
  obtain ⟨P,hP,hentry⟩ := (exists_pointCluster_superlevel_entry hPointMean)
  obtain ⟨C,hC,D,hD,H₀,hH₀,hcount⟩ :=
    (exists_atkinsonLocalMeanExcess_card_le_above_fourthRoot hPacket) hδ hκ hν
  pm_4486
  have hcolor : ∀ e : ℕ,
      ((S.filter (fun n => n%2 = e)).card:ℝ) ≤
        D*H^ν*(H/(G*Y^2)+H^2/Y^6) := by
    pm_4485
  pm_4487
  change (S.card:ℝ) ≤ 2*D*H^ν*(H/(G*Y^2)+H^2/Y^6)
  pm_6938

theorem occupancy_inverse_power_budget {H G A m : ℝ}
    (hG : 0 < G) (hA : 0 < A) (hm : 1 ≤ m) :
    H/(G*(m*A)^2)+H^2/(m*A)^6 ≤
      (H/(G*A^2)+H^2/A^6)/m^2 := by
  have hm0 : 0 < m := by linarith
  have hp : m^2 ≤ m^6 := pow_le_pow_right₀ hm (by omega)
  rw [mul_pow, mul_pow]
  calc
    H/(G*(m^2*A^2))+H^2/(m^6*A^6) ≤
        H/(G*(m^2*A^2))+H^2/(m^2*A^6) := by
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_left (sq_nonneg H) (by positivity)
          (mul_le_mul_of_nonneg_right hp (by positivity)))
    _ = (H/(G*A^2)+H^2/A^6)/m^2 := by field_simp

theorem exists_pointValue_card_le_with_width
    (hPointMean : PointMeanInput) (hPacket : LocalMeanPacketInput)
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
            H^2/(V^2/(16*P*Real.log (3*H)))^6) := by
  pm_5010 H₀ hH₀ exists_pointCluster_superlevel_count hPointMean hPacket
  pm_4490
  let B : ℝ := 2*D*H^ν*(H/(G*A^2)+H^2/A^6)
  pm_4489
  have hsuper : ∀ m : ℕ, 0 < m →
      (((pointClusterBins H G W).filter
        (fun n => m ≤ (pointCluster H G W n).card)).card:ℝ) ≤ B/(m:ℝ)^2 := by
    pm_4491
    have hp := occupancy_inverse_power_budget (H := H) hG hA hm1
    calc
      _ ≤ 2*D*H^ν*(H/(G*((m:ℝ)*A)^2)+H^2/((m:ℝ)*A)^6) := hc
      _ ≤ 2*D*H^ν*((H/(G*A^2)+H^2/A^6)/(m:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = B/(m:ℝ)^2 := by dsimp only [B]; ring
  pm_4488
  calc
    (W.card:ℝ) ≤ 2*B := hsum
    _ = (4*D)*H^ν*(H/(G*A^2)+H^2/A^6) := by dsimp only [B]; ring


end MathCollab.Density.Stronger.Peaks
