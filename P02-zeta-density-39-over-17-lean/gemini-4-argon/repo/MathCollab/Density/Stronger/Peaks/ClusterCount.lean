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

@[expose] public section

open Complex Filter MeasureTheory Set Topology Finset MathCollab.Density MathCollab.Density.Stronger
open scoped Interval
open TaoTrudgianYang2025 (eventually_const_log_pow_le_rpow
  eventually_const_height_log_pow_mul_rpow_le_rpow
  eventually_pointValue_sixth_power_source_range)
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Peaks
theorem atkinsonLocalMeanExcess_threshold_iff {G t error Y : ℝ} (hY : 0 < Y) :
    Y ≤ atkinsonLocalMeanExcess G t error ↔
      error+Y ≤ ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2 := by
  unfold atkinsonLocalMeanExcess
  rw [le_max_iff]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h
    right
    linarith


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
  obtain ⟨P,hP,hsource⟩ := hPointMean
  refine ⟨P,hP,?_⟩
  intro H G V W n hH hG hGH hV hfit hsep hrange hlarge hn
  have hc := pointClusterCenter_range hG hrange hn
  have hsub := pointCluster_subset H G W n
  have hsep' : oneSeparated (pointCluster H G W n) := by
    intro x hx y hy hxy
    exact hsep x (hsub hx) y (hsub hy) hxy
  apply hsource (3*H) V (pointClusterCenter H G n) G
    ((Real.log (3*H))^2) (pointCluster H G W n)
    (by linarith) hV hG.le (sq_nonneg _) hsep'
    (pointCluster_symmetric_interval n hG (fun t ht => (hrange t ht).1))
    (by linarith [hc.1]) (by linarith [hc.2])
  · intro t ht
    have htR := hrange t (hsub ht)
    have hlt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
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
  have hma := mul_le_mul_of_nonneg_right hmr hA
  have hmin := mul_le_mul_of_nonneg_right hm1 hA
  nlinarith



def pointClusterSuperlevel (H G : ℝ) (W : Finset ℝ) (m : ℕ) : Finset ℕ :=
  (pointClusterBins H G W).filter (fun n => m ≤ (pointCluster H G W n).card)





