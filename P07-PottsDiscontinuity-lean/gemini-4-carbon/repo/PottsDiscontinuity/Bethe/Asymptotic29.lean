module

public import PottsDiscontinuity.Bethe.Asymptotic26Cast
public import PottsDiscontinuity.Bethe.AsymptoticBoundary
public import PottsDiscontinuity.Bethe.AsymptoticEndpoint
public import PottsDiscontinuity.Bethe.AsymptoticGeometry
public import PottsDiscontinuity.Bethe.AsymptoticLimitTools
public import PottsDiscontinuity.Bethe.AsymptoticOffsetControl
public import PottsDiscontinuity.Bethe.AsymptoticSpatial
public import PottsDiscontinuity.Bethe.AsymptoticTaylor
public import PottsDiscontinuity.Bethe.AsymptoticUniformOffset
public import PottsDiscontinuity.Bethe.Prop21Tau

/-! # Theorem 2.9 for `N ∈ 4ℕ`: Arzelà--Ascoli and subsequential limit identification -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators UniformConvergence BoundedContinuousFunction

namespace PottsDiscontinuity.Bethe

private noncomputable def rootOffsetExtension {n : ℕ} (hn : 0 < n)
    (q u : Fin n → ℝ) (K : NNReal) (x : ℝ) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun j => u j + K * |x - q j|

private theorem rootOffsetExtension_lipschitz {n : ℕ} (hn : 0 < n)
    (q u : Fin n → ℝ) (K : NNReal) :
    LipschitzWith K (rootOffsetExtension hn q u K) := by
  classical
  refine LipschitzWith.of_le_add_mul K fun x y => ?_
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun j => u j + K * |y - q j|
  have hup : rootOffsetExtension hn q u K x ≤ u j + K * |x - q j| := Finset.inf'_le _ hj
  change rootOffsetExtension hn q u K y = u j + K * |y - q j| at he
  rw [he, Real.dist_eq]
  have htri : |x - q j| ≤ |y - q j| + |x - y| := by
    have := abs_add_le (x - y) (y - q j); rw [sub_add_sub_cancel] at this; linarith
  linarith [mul_le_mul_of_nonneg_left htri K.coe_nonneg]

private theorem offsetFunction_sub_extension_le {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hn : 0 < N / 2 - r) (hq : q ∈ S_n (N / 2 - r)) (K : NNReal)
    (hpair : ∀ i j, |offsetDisplacement N r h4 hr p q i - offsetDisplacement N r h4 hr p q j| ≤ (K : ℝ) * |q i - q j|)
    {d : ℝ} (hmesh : ∀ j : Fin (N / 2 - r + 1),
      rootPartitionPoint (N / 2 - r) q hn j.succ - rootPartitionPoint (N / 2 - r) q hn j.castSucc ≤ d)
    {x : ℝ} (hx : x ∈ Icc (-Real.pi) Real.pi) :
    |offsetFunction N r h4 hr p q hn x -
      rootOffsetExtension hn q (offsetDisplacement N r h4 hr p q) K x| ≤ (K : ℝ) * d := by
  obtain ⟨j, hj, hd⟩ := offsetFunction_near_root h4 hr hn hq hmesh hx
  have hat : rootOffsetExtension hn q (offsetDisplacement N r h4 hr p q) K (q j) =
      offsetDisplacement N r h4 hr p q j := by
    unfold rootOffsetExtension
    refine le_antisymm ?_ (Finset.le_inf' _ _ fun i _ => by linarith [(abs_le.mp (hpair j i)).2])
    simpa only [sub_self, abs_zero, mul_zero, add_zero] using
      (Finset.inf'_le (fun i => offsetDisplacement N r h4 hr p q i + K * |q j - q i|) (Finset.mem_univ j))
  rw [hj, ← hat]
  have hl := (rootOffsetExtension_lipschitz hn q (offsetDisplacement N r h4 hr p q) K).dist_le_mul (q j) x
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (q j) x] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left hd K.coe_nonneg)

private theorem offsetFunction_at_root {N r : ℕ} (h4 : 4 ∣ N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ}
    (hn : 0 < N / 2 - r) (hq : StrictMono q) (j : Fin (N / 2 - r)) :
    offsetFunction N r h4 hr p q hn (q j) = offsetDisplacement N r h4 hr p q j := by
  by_cases hj : j.val + 1 < N / 2 - r
  · exact offsetFunction_on_cell h4 hr hn hq j hj ⟨le_rfl, hq (show j.val < j.val + 1 by omega)⟩
  · have hlast : j = ⟨N / 2 - r - 1, by omega⟩ := Fin.ext (show j.val = N / 2 - r - 1 by omega)
    have hfirst : ¬ q j < q ⟨0, hn⟩ := not_lt.mpr (hq.monotone (show 0 ≤ j.val by omega))
    rw [hlast] at hfirst ⊢; simp [offsetFunction, hfirst]

private theorem tendstoUniformlyOn_mul_of_bounds {ι : Type*} {l : Filter ι}
    {F G : ι → ℝ → ℝ} {f g : ℝ → ℝ} {s : Set ℝ}
    (hF : TendstoUniformlyOn F f l s) (hG : TendstoUniformlyOn G g l s)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hboundF : ∀ i, ∀ x ∈ s, |F i x| ≤ M) (hboundg : ∀ x ∈ s, |g x| ≤ B) :
    TendstoUniformlyOn (fun i x => F i x * G i x) (fun x => f x * g x) l s := by
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  let δ := ε / (M + B + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hid : (M + B + 1) * δ = ε := by dsimp [δ]; field_simp
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF δ hδ, Metric.tendstoUniformlyOn_iff.mp hG δ hδ] with i hiF hiG x hx
  have h₁ : |F i x - f x| ≤ δ := by simpa only [Real.dist_eq, abs_sub_comm] using (hiF x hx).le
  have h₂ : |G i x - g x| ≤ δ := by simpa only [Real.dist_eq, abs_sub_comm] using (hiG x hx).le
  have hbd : |F i x * G i x - f x * g x| ≤ M * δ + δ * B := by
    rw [show F i x * G i x - f x * g x = F i x * (G i x - g x) + (F i x - f x) * g x by ring]
    refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul (hboundF i x hx) h₂ (abs_nonneg _) hM)
      (mul_le_mul h₁ (hboundg x hx) (abs_nonneg _) hδ.le)
  rw [Real.dist_eq, abs_sub_comm]; nlinarith only [hbd, hid, hδ]

private theorem tendsto_of_abs_sub_le {ι : Type*} {l : Filter ι} {u v E : ι → ℝ} {a : ℝ}
    (hv : Tendsto v l (𝓝 a)) (hE : Tendsto E l (𝓝 0))
    (hb : ∀ i, |u i - v i| ≤ E i) : Tendsto u l (𝓝 a) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  filter_upwards [Metric.tendsto_nhds.mp hv (ε / 2) (by positivity),
    hE.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))] with i hi hEi
  have hd := dist_triangle (u i) (v i) a; have he := hb i
  simp only [Real.dist_eq] at hd hi ⊢; linarith

private theorem tendsto_offsetBoundarySum {ι : Type*} {l : Filter ι} {Δ : ℝ}
    (hΔ : Δ < -1) (r : ℕ) (N : ι → ℕ) (hr : ∀ i, r ≤ N i / 2)
    (hn : ∀ i, 0 < N i / 2) (p : ∀ i, Fin (N i / 2) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (d : ι → ℝ) (hd : Tendsto d l (𝓝 0))
    (hdnonneg : ∀ i, 0 ≤ d i)
    (hmesh : ∀ i, ∀ j : Fin (N i / 2 + 1),
      rootPartitionPoint (N i / 2) (p i) (hn i) j.succ - rootPartitionPoint (N i / 2) (p i) (hn i) j.castSucc ≤ d i)
    {x : ι → ℝ} {a : ℝ} (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun i => offsetBoundarySum Δ (N i) r (hr i) (p i) (x i)) l
      (𝓝 ((r : ℝ) / 2 * (theta Δ a (-Real.pi) + theta Δ a Real.pi))) := by
  have hθleft (s : ℕ) (hs : s ≤ r) (k : Fin s) :
      Tendsto (fun i => theta Δ (x i) (p i ⟨k.val, by have := hr i; omega⟩)) l (𝓝 (theta Δ a (-Real.pi))) := by
    have hl := tendsto_root_at_left_of_mesh (fun i => N i / 2) hn p hp d hd hdnonneg hmesh
      (fun i => (⟨k.val, by have := hr i; omega⟩ : Fin (N i / 2))) r
      fun i => show k.val ≤ r by omega
    simpa only [Function.comp_def] using (continuous_theta hΔ).continuousAt.tendsto.comp (hx.prodMk_nhds hl)
  have hθright (s t : ℕ) (hst : s + t = r) (k : Fin t) :
      Tendsto (fun i => theta Δ (x i) (p i ⟨s + (N i / 2 - r) + k.val, by have := hr i; omega⟩)) l (𝓝 (theta Δ a Real.pi)) := by
    have hr' := tendsto_root_at_right_of_mesh (fun i => N i / 2) hn p hp d hd hdnonneg hmesh
      (fun i => (⟨s + (N i / 2 - r) + k.val, by have := hr i; omega⟩ : Fin (N i / 2))) r
      fun i => show N i / 2 - 1 - (s + (N i / 2 - r) + k.val) ≤ r by have := hr i; omega
    simpa only [Function.comp_def] using (continuous_theta hΔ).continuousAt.tendsto.comp (hx.prodMk_nhds hr')
  have hL₀ := tendsto_finsetSum Finset.univ (fun k _ => hθleft (r / 2) (by omega) k)
  have hR₀ := tendsto_finsetSum Finset.univ (fun k _ => hθright (r / 2) (r - r / 2) (by omega) k)
  have hL₁ := tendsto_finsetSum Finset.univ (fun k _ => hθleft (r - r / 2) (by omega) k)
  have hR₁ := tendsto_finsetSum Finset.univ (fun k _ => hθright (r - r / 2) (r / 2) (by omega) k)
  have ht := (((hL₀.add hR₀).add hL₁).add hR₁).div_const 2
  have hr_eq : ((r / 2 : ℕ) : ℝ) + ((r - r / 2 : ℕ) : ℝ) = (r : ℝ) := by
    exact_mod_cast (show r / 2 + (r - r / 2) = r by omega)
  convert ht using 1
  · rfl
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1; rw [← hr_eq]; ring

private lemma abs_avg4 {a b c d R : ℝ} (ha : |a| ≤ R) (hb : |b| ≤ R) (hc : |c| ≤ R) (hd : |d| ≤ R) :
    |(a + b + c + d) / 4| ≤ R :=
  abs_le.mpr ⟨by linarith [(abs_le.mp ha).1, (abs_le.mp hb).1, (abs_le.mp hc).1, (abs_le.mp hd).1],
    by linarith [(abs_le.mp ha).2, (abs_le.mp hb).2, (abs_le.mp hc).2, (abs_le.mp hd).2]⟩

private theorem offset_bethe_taylor {Δ : ℝ} (hΔ : Δ < -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N r : ℕ) (h4 : 4 ∣ N) (hr : r ≤ N / 2), 0 < N →
      ∀ (p : Fin (N / 2) → ℝ) (q : Fin (N / 2 - r) → ℝ),
      p ∈ S_n (N / 2) → q ∈ S_n (N / 2 - r) →
      DiscreteBetheEquation Δ N (N / 2) p → DiscreteBetheEquation Δ N (N / 2 - r) q →
      ∀ B : ℝ, 0 ≤ B →
      (∀ k, |offsetLowerRoot N r hr p k - q k| ≤ B / N ∧ |offsetUpperRoot N r hr p k - q k| ≤ B / N) →
      ∀ j, |offsetDisplacement N r h4 hr p q j -
        (offsetBoundarySum Δ N r hr p (offsetLowerRoot N r hr p j) +
          offsetBoundarySum Δ N r hr p (offsetUpperRoot N r hr p j)) / 2 +
        ((∑ k, d1Theta Δ (q j) (q k)) / N) * offsetDisplacement N r h4 hr p q j +
        (∑ k, d2Theta Δ (q j) (q k) * offsetDisplacement N r h4 hr p q k) / N| ≤ K * B ^ 2 / N := by
  obtain ⟨K, hK, hTaylor⟩ := theta_sum_linearized_remainder hΔ
  refine ⟨K, hK, fun N r h4 hr hN p q hp hq hpBE hqBE B hB hnear j => ?_⟩
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmem (k : Fin (N / 2)) : p k ∈ Icc (-Real.pi) Real.pi := ⟨(hp.1 k).1.le, (hp.1 k).2.le⟩
  have hqmem (k : Fin (N / 2 - r)) : q k ∈ Icc (-Real.pi) Real.pi := ⟨(hq.1 k).1.le, (hq.1 k).2.le⟩
  let x₀ := offsetLowerRoot N r hr p j; let x₁ := offsetUpperRoot N r hr p j
  let y₀ := offsetLowerRoot N r hr p; let y₁ := offsetUpperRoot N r hr p
  have h₀₀ := hTaylor N (N / 2 - r) hN (by omega) (q j) x₀ q y₀ (hqmem j) (hmem _) hqmem (fun k => hmem _) B hB (hnear j).1 fun k => (hnear k).1
  have h₀₁ := hTaylor N (N / 2 - r) hN (by omega) (q j) x₀ q y₁ (hqmem j) (hmem _) hqmem (fun k => hmem _) B hB (hnear j).1 fun k => (hnear k).2
  have h₁₀ := hTaylor N (N / 2 - r) hN (by omega) (q j) x₁ q y₀ (hqmem j) (hmem _) hqmem (fun k => hmem _) B hB (hnear j).2 fun k => (hnear k).1
  have h₁₁ := hTaylor N (N / 2 - r) hN (by omega) (q j) x₁ q y₁ (hqmem j) (hmem _) hqmem (fun k => hmem _) B hB (hnear j).2 fun k => (hnear k).2
  have hb := abs_avg4 h₀₀ h₀₁ h₁₀ h₁₁
  have heps (k : Fin (N / 2 - r)) : (y₀ k + y₁ k) / 2 - q k = -offsetDisplacement N r h4 hr p q k / (N : ℝ) := by
    dsimp [y₀, y₁]; rw [offsetDisplacement_eq_alignedRoot, alignedRoot_eq_mean hr]; field_simp; ring
  have hmean : (∑ k, d2Theta Δ (q j) (q k) * ((y₀ k + y₁ k) / 2 - q k)) =
      ((∑ k, d2Theta Δ (q j) (q k) * (y₀ k - q k)) + ∑ k, d2Theta Δ (q j) (q k) * (y₁ k - q k)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by ring
  have he : |(∑ k, ((theta Δ x₀ (y₀ k) + theta Δ x₀ (y₁ k) + theta Δ x₁ (y₀ k) + theta Δ x₁ (y₁ k)) / 4 - theta Δ (q j) (q k))) -
      (∑ k, d1Theta Δ (q j) (q k)) * ((x₀ + x₁) / 2 - q j) -
      ∑ k, d2Theta Δ (q j) (q k) * ((y₀ k + y₁ k) / 2 - q k)| ≤ K * B ^ 2 / N := by
    rw [hmean]; simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib] at hb ⊢
    convert hb using 1; ring_nf
  have hbulk : (∑ k, ((theta Δ x₀ (y₀ k) + theta Δ x₀ (y₁ k) + theta Δ x₁ (y₀ k) + theta Δ x₁ (y₁ k)) / 4 - theta Δ (q j) (q k))) =
      offsetDisplacement N r h4 hr p q j - (offsetBoundarySum Δ N r hr p x₀ + offsetBoundarySum Δ N r hr p x₁) / 2 := by
    linarith [offsetDisplacement_bethe_bulk_boundary h4 hr hpBE hqBE j]
  rw [hbulk, show (x₀ + x₁) / 2 - q j = -offsetDisplacement N r h4 hr p q j / (N : ℝ) from heps j] at he
  simp_rw [heps, mul_div, mul_neg, neg_div] at he
  rw [Finset.sum_neg_distrib, ← Finset.sum_div] at he
  dsimp only [x₀, x₁] at he
  convert he using 2; ring

section

variable {Δ : ℝ} (hΔ : Δ < -1) (r : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i)
    (hr : ∀ i, r ≤ N i / 2) (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hpBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2) (p i))
    (hqBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2 - r) (q i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (hbp : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hbq : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    {K : ℝ} (hK : 0 ≤ K)
    (hrate : ∀ᶠ i in atTop,
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2) (p i) (hp i)
        (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x - rho Δ x) (hbp i) ≤ K / N i ∧
      densityNorm Δ hΔ (fun x => rootStepDensity (N i) (N i / 2 - r) (q i) (hq i)
        (hn i) (two_mul_half_sub_le N r i) x - rho Δ x) (hbq i) ≤ K / N i)

include hΔ hN hp hq hpBE hqBE hNlim hbp hbq hK hrate

/-- **Theorem 2.9, item 1.** Uniform convergence on the closed interval to
the continuous representative of the offset-equation solution. -/
theorem theorem29_convergence :
    TendstoUniformlyOn (fun i x => rho Δ x * offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x)
      (fun x => (r : ℝ) * tauCont Δ x) atTop (Icc (-Real.pi) Real.pi) := by
  let w := Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1)
  have hw : 0 < w := density_weight_lower_pos hΔ
  have herror : ∀ᶠ i in atTop, ∀ x ∈ Icc (-Real.pi) Real.pi,
      |rootStepDensity (N i) (N i / 2) (p i) (hp i) (half_pos_of_half_sub_pos N r hn i) (two_mul_half_le N i) x - rho Δ x| ≤
        (K / w) / N i ∧
      |rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x - rho Δ x| ≤
        (K / w) / N i := by
    filter_upwards [hrate] with i hi x hx
    exact ⟨(abs_le_densityNorm_div hΔ _ (hbp i) hx).trans ((div_le_div_of_nonneg_right hi.1 hw.le).trans_eq (by ring)),
      (abs_le_densityNorm_div hΔ _ (hbq i) hx).trans ((div_le_div_of_nonneg_right hi.2 hw.le).trans_eq (by ring))⟩
  obtain ⟨B, R, DP, DQ, _, hR, hDP, _, L, hgeom⟩ :=
    eventually_offset_estimates_of_density_rate hΔ r N h4 hr hN hn p q hp hq hNlim (div_nonneg hK hw.le) herror
  have hnormlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (N i / 2 - r) (q i) (hq i) (hn i) (two_mul_half_sub_le N r i) x - rho Δ x)
      (hbq i)) atTop (𝓝 0) := by
    have hKlim : Tendsto (fun i => K / (N i : ℝ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp hNlim).const_mul K
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [hrate, hKlim.eventually (gt_mem_nhds hε)] with i hi hKi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (densityNorm_nonneg hΔ _ (hbq i))]
    exact hi.2.trans_lt hKi
  have hweak (g : ℝ → ℝ) (hg : Continuous g) :
      Tendsto (fun i => (∑ j, g (q i j)) / (N i : ℝ)) atTop (𝓝 (∫ y in (-Real.pi)..Real.pi, g y * rho Δ y)) :=
    theorem26_sums_of_pos hΔ r N (fun i => N i / 2 - r) q hq hn (fun _ => by omega)
      (fun i => by obtain ⟨z, _⟩ := h4 i; have := hr i; omega) hNlim hbq hnormlim g hg
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp hgeom
  let X := Icc (-Real.pi) Real.pi
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  let sh : ℕ → ℕ := fun i => i₀ + i
  have hsh : Tendsto sh atTop atTop := tendsto_atTop.mpr fun a => eventually_atTop.mpr ⟨a, fun b hb => by dsimp [sh]; omega⟩
  suffices htail : TendstoUniformlyOn
      (fun i x => rho Δ x * offsetFunction (N (sh i)) r (h4 (sh i)) (hr (sh i)) (p (sh i)) (q (sh i)) (hn (sh i)) x)
      (fun x => (r : ℝ) * tauCont Δ x) atTop X by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp htail ε hε)
    refine eventually_atTop.mpr ⟨i₀ + j₀, fun i hi x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show i₀ ≤ i by omega)
    exact hj₀ k (by omega) x hx
  have hgt (i : ℕ) : OffsetEstimatesAt (N (sh i)) r (h4 (sh i)) (hr (sh i)) (hn (sh i))
      (p (sh i)) (q (sh i)) B R DP DQ L := hi₀ (sh i) (by dsimp [sh]; omega)
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  let s1 : ℕ → ℕ := fun i => sh (ns i)
  have hs1 : Tendsto s1 atTop atTop := hsh.comp hns
  -- Step 1: Arzelà--Ascoli along `s1`
  let G : ℕ → ℝ → ℝ := fun i => rootOffsetExtension (hn (s1 i)) (q (s1 i))
    (offsetDisplacement (N (s1 i)) r (h4 (s1 i)) (hr (s1 i)) (p (s1 i)) (q (s1 i))) L
  have hGLip (i : ℕ) : LipschitzWith L (G i) := rootOffsetExtension_lipschitz _ _ _ _
  have hGBound (i : ℕ) (x : ℝ) (hx : x ∈ X) : |G i x| ≤ B + (L : ℝ) * (2 * Real.pi) := by
    dsimp only [G]; unfold rootOffsetExtension
    refine abs_le.mpr ⟨Finset.le_inf' _ _ fun j _ => ?_, ?_⟩
    · linarith [(abs_le.mp ((hgt (ns i)).bound j)).1, mul_nonneg L.coe_nonneg (abs_nonneg (x - q (s1 i) j)),
        mul_nonneg L.coe_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    · let j : Fin (N (s1 i) / 2 - r) := ⟨0, hn (s1 i)⟩
      have he := Finset.inf'_le
        (fun j => offsetDisplacement (N (s1 i)) r (h4 (s1 i)) (hr (s1 i)) (p (s1 i)) (q (s1 i)) j +
          L * |x - q (s1 i) j|) (Finset.mem_univ j)
      have hqj := (hq (s1 i)).1 j
      have hd : |x - q (s1 i) j| ≤ 2 * Real.pi := abs_le.mpr ⟨by linarith [hqj.2, hx.1], by linarith [hqj.1, hx.2]⟩
      linarith [he, mul_le_mul_of_nonneg_left hd L.coe_nonneg, (abs_le.mp ((hgt (ns i)).bound j)).2]
  let GB : ℕ → X →ᵇ ℝ := fun i => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => G i x, (hGLip i).continuous.comp continuous_subtype_val⟩
  have hComp : IsCompact (closure (range GB)) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-(B + (L : ℝ) * (2 * Real.pi))) (B + (L : ℝ) * (2 * Real.pi)))
      isCompact_Icc (range GB)
      (fun g x ⟨i, hi⟩ => hi ▸ abs_le.mp (hGBound i x x.2))
      ((LipschitzWith.uniformEquicontinuous _ L fun g => by
        obtain ⟨i, hi⟩ := g.2; rw [← hi]
        change LipschitzWith L (fun x : X => G i x)
        simpa only [mul_one, Function.comp_def] using (hGLip i).comp (LipschitzWith.subtype_val X)).equicontinuous)
  obtain ⟨fB, _, φ, hφ, htB⟩ := hComp.tendsto_subseq fun i => subset_closure ⟨i, rfl⟩
  let f : ℝ → ℝ := IccExtend hpi fun x => fB x
  have hf : Continuous f := continuous_IccExtend_iff.mpr fB.continuous
  let t : ℕ → ℕ := fun i => s1 (φ i)
  have ht : Tendsto t atTop atTop := hs1.comp hφ.tendsto_atTop
  have hNt : Tendsto (fun i => (N (t i) : ℝ)) atTop atTop := hNlim.comp ht
  have hinvt : Tendsto (fun i => (N (t i) : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hNt
  have hdPt : Tendsto (fun i => DP / (N (t i) : ℝ)) atTop (𝓝 0) := by simpa only [div_eq_mul_inv, mul_zero] using hinvt.const_mul DP
  have hdQt : Tendsto (fun i => DQ / (N (t i) : ℝ)) atTop (𝓝 0) := by simpa only [div_eq_mul_inv, mul_zero] using hinvt.const_mul DQ
  have hF : TendstoUniformlyOn
      (fun i x => offsetFunction (N (t i)) r (h4 (t i)) (hr (t i)) (p (t i)) (q (t i)) (hn (t i)) x) f atTop X := by
    have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htB
    have hEL : Tendsto (fun i => (L : ℝ) * (DQ / (N (t i) : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hdQt.const_mul (L : ℝ)
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    filter_upwards [Metric.tendstoUniformly_iff.mp hu (ε / 2) (by positivity),
      hEL.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))] with i hi hEi x hx
    have hclose := offsetFunction_sub_extension_le (h4 (t i)) (hr (t i)) (hn (t i)) (hq (t i)) L
      (hgt (ns (φ i))).pair (hgt (ns (φ i))).meshQ hx
    have htri := dist_triangle (f x) (G (φ i) x)
      (offsetFunction (N (t i)) r (h4 (t i)) (hr (t i)) (p (t i)) (q (t i)) (hn (t i)) x)
    have hnearG : dist (fB ⟨x, hx⟩) (G (φ i) x) < ε / 2 := hi ⟨x, hx⟩
    dsimp [f] at htri ⊢; rw [IccExtend_of_mem hpi _ hx] at htri ⊢
    simp only [Real.dist_eq] at htri hnearG ⊢
    change |offsetFunction (N (t i)) r (h4 (t i)) (hr (t i)) (p (t i)) (q (t i)) (hn (t i)) x - G (φ i) x| ≤
      (L : ℝ) * (DQ / (N (t i) : ℝ)) at hclose
    rw [abs_sub_comm _ (G (φ i) x)] at hclose; linarith
  -- Step 2: Identify `rho Δ x * f x = r * tauCont Δ x`
  have hid : ∀ x ∈ X, rho Δ x * f x = (r : ℝ) * tauCont Δ x := by
    let g := fun x => rho Δ x * f x
    have hg : Continuous g := (continuous_rho hΔ).mul hf
    suffices hsc : ∀ x ∈ X, 2 * Real.pi * g x =
        (r : ℝ) * (theta Δ x (-Real.pi) + theta Δ x Real.pi) / 2 - ∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y * g y by
      let hm := fun x => g x + (1 - (r : ℝ)) * tauCont Δ x
      have hhm : Continuous hm := hg.add ((continuous_tauCont hΔ).const_mul _)
      have heq_m := eq_tauCont_of_isCOESolution_of_integrableOn hΔ (integrableOn_Icc_of_continuous hhm) fun x hx => by
        have hθ : Continuous (fun y => d2Theta Δ x y) := (continuous_d2Theta_pair hΔ).comp (continuous_const.prodMk continuous_id)
        have hτ := tauCont_isCOESolution hΔ x hx
        unfold cOEop at hτ ⊢
        have hτ' := congrArg ((1 - (r : ℝ)) * ·) hτ
        have hInt1 : IntervalIntegrable (fun y => d2Theta Δ x y * g y) volume (-Real.pi) Real.pi :=
          (hθ.mul hg).intervalIntegrable _ _
        have hInt2 : IntervalIntegrable (fun y => (1 - (r : ℝ)) * (d2Theta Δ x y * tauCont Δ y)) volume (-Real.pi) Real.pi :=
          ((hθ.mul (continuous_tauCont hΔ)).const_mul _).intervalIntegrable _ _
        rw [show (fun y => d2Theta Δ x y * hm y) = fun y => d2Theta Δ x y * g y + (1 - (r : ℝ)) * (d2Theta Δ x y * tauCont Δ y)
            from funext fun _ => by dsimp [hm]; ring,
          intervalIntegral.integral_add hInt1 hInt2,
          intervalIntegral.integral_const_mul]
        dsimp [hm]; linarith [hsc x hx, hτ']
      intro x hx; have := heq_m x hx; dsimp [hm, g] at this; linarith
    intro x hx
    choose j hj hdist using fun i => offsetFunction_near_root (h4 (t i)) (hr (t i)) (hn (t i)) (hq (t i)) (hgt (ns (φ i))).meshQ hx
    let a : ℕ → ℝ := fun i => q (t i) (j i)
    have ha : Tendsto a atTop (𝓝 x) :=
      tendsto_of_abs_sub_le tendsto_const_nhds hdQt fun i => by simpa only [abs_sub_comm] using hdist i
    have hqmem (i : ℕ) (k : Fin (N (t i) / 2 - r)) : q (t i) k ∈ X := ⟨((hq (t i)).1 k).1.le, ((hq (t i)).1 k).2.le⟩
    have hamem (i : ℕ) : a i ∈ X := hqmem i (j i)
    have hRlim : Tendsto (fun i => R / (N (t i) : ℝ)) atTop (𝓝 0) := by simpa only [div_eq_mul_inv, mul_zero] using hinvt.const_mul R
    have hL := tendsto_of_abs_sub_le ha hRlim fun i => ((hgt (ns (φ i))).near (j i)).1
    have hU := tendsto_of_abs_sub_le ha hRlim fun i => ((hgt (ns (φ i))).near (j i)).2
    have hε : Tendsto (fun i => offsetDisplacement (N (t i)) r (h4 (t i)) (hr (t i)) (p (t i)) (q (t i)) (j i)) atTop (𝓝 (f x)) := by
      convert hF.tendsto_at hx using 1; funext i; exact (hj i).symm
    let boundary : ℕ → ℝ := fun i =>
      (offsetBoundarySum Δ (N (t i)) r (hr (t i)) (p (t i)) (offsetLowerRoot (N (t i)) r (hr (t i)) (p (t i)) (j i)) +
        offsetBoundarySum Δ (N (t i)) r (hr (t i)) (p (t i)) (offsetUpperRoot (N (t i)) r (hr (t i)) (p (t i)) (j i))) / 2
    have hBL := tendsto_offsetBoundarySum hΔ r (fun i => N (t i)) (fun i => hr (t i))
      (fun i => by have := hn (t i); omega) (fun i => p (t i)) (fun i => hp (t i)) _ hdPt
      (fun _ => div_nonneg hDP (Nat.cast_nonneg _)) (fun i => (hgt (ns (φ i))).meshP) hL
    have hBU := tendsto_offsetBoundarySum hΔ r (fun i => N (t i)) (fun i => hr (t i))
      (fun i => by have := hn (t i); omega) (fun i => p (t i)) (fun i => hp (t i)) _ hdPt
      (fun _ => div_nonneg hDP (Nat.cast_nonneg _)) (fun i => (hgt (ns (φ i))).meshP) hU
    have hboundary : Tendsto boundary atTop (𝓝 ((r : ℝ) / 2 * (theta Δ x (-Real.pi) + theta Δ x Real.pi))) := by
      convert (hBL.add hBU).div_const 2 using 2; ring
    let S₁ : ℕ → ℝ := fun i => (∑ k, d1Theta Δ (a i) (q (t i) k)) / (N (t i) : ℝ)
    let S₂ : ℕ → ℝ := fun i =>
      (∑ k, d2Theta Δ (a i) (q (t i) k) * offsetDisplacement (N (t i)) r (h4 (t i)) (hr (t i)) (p (t i)) (q (t i)) k) / (N (t i) : ℝ)
    have hK₁ := tendstoUniformlyOn_continuous_slice (d1Theta Δ) (continuous_d1Theta_pair hΔ) ha (Eventually.of_forall hamem) hx
    have hK₂ := tendstoUniformlyOn_continuous_slice (d2Theta Δ) (continuous_d2Theta_pair hΔ) ha (Eventually.of_forall hamem) hx
    have hS₁ : Tendsto S₁ atTop (𝓝 (∫ y in (-Real.pi)..Real.pi, d1Theta Δ x y * rho Δ y)) :=
      empirical_sum_tendsto_of_uniformlyOn (fun i => N (t i)) (fun i => N (t i) / 2 - r) (fun i => hN (t i))
        (fun _ => by omega) (fun i => q (t i)) hqmem _ _
        ((hweak _ ((continuous_d1Theta_pair hΔ).comp (continuous_const.prodMk continuous_id))).comp ht) hK₁
    obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (show ContinuousOn (fun z : ℝ × ℝ => d2Theta Δ z.1 z.2) (X ×ˢ X) from (continuous_d2Theta_pair hΔ).continuousOn)
    obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
    have hprod := tendstoUniformlyOn_mul_of_bounds hK₂ hF
      (show 0 ≤ max M₀ 1 by linarith [le_max_right M₀ 1]) (show 0 ≤ max C₀ 1 by linarith [le_max_right C₀ 1])
      (fun i y hy => (show |d2Theta Δ (a i) y| ≤ M₀ by simpa only [Real.norm_eq_abs] using hM₀ (a i, y) ⟨hamem i, hy⟩).trans (le_max_left _ _))
      (fun y hy => (show |f y| ≤ C₀ by simpa only [Real.norm_eq_abs] using hC₀ y hy).trans (le_max_left _ _))
    have hS₂ : Tendsto S₂ atTop (𝓝 (∫ y in (-Real.pi)..Real.pi, (d2Theta Δ x y * f y) * rho Δ y)) := by
      have ht2 := empirical_sum_tendsto_of_uniformlyOn (fun i => N (t i)) (fun i => N (t i) / 2 - r) (fun i => hN (t i))
        (fun _ => by omega) (fun i => q (t i)) hqmem _ _
        ((hweak _ (((continuous_d2Theta_pair hΔ).comp (continuous_const.prodMk continuous_id)).mul hf)).comp ht) hprod
      refine ht2.congr fun i => ?_
      dsimp only [S₂]; congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [offsetFunction_at_root (h4 (t i)) (hr (t i)) (hn (t i)) (hq (t i)).2.1 k]
    obtain ⟨KT, _, hTaylor⟩ := offset_bethe_taylor hΔ
    have hzero : Tendsto (fun i =>
        offsetDisplacement (N (t i)) r (h4 (t i)) (hr (t i)) (p (t i)) (q (t i)) (j i) - boundary i +
          S₁ i * offsetDisplacement (N (t i)) r (h4 (t i)) (hr (t i)) (p (t i)) (q (t i)) (j i) + S₂ i) atTop (𝓝 0) :=
      tendsto_of_abs_sub_le tendsto_const_nhds
        (by simpa only [div_eq_mul_inv, mul_zero] using hinvt.const_mul (KT * R ^ 2))
        fun i => by
          rw [sub_zero, ← div_eq_mul_inv]
          exact hTaylor (N (t i)) r (h4 (t i)) (hr (t i)) (hN (t i))
            (p (t i)) (q (t i)) (hp (t i)) (hq (t i)) (hpBE (t i)) (hqBE (t i)) R hR (hgt (ns (φ i))).near (j i)
    have hident := tendsto_nhds_unique (((hε.sub hboundary).add (hS₁.mul hε)).add hS₂) hzero
    have hcbe := congrArg (· * f x) (rho_isCBESolution hΔ x hx)
    unfold cBEop at hcbe
    have hInt : (∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y * (rho Δ y * f y)) =
        ∫ y in (-Real.pi)..Real.pi, (d2Theta Δ x y * f y) * rho Δ y :=
      intervalIntegral.integral_congr fun _ _ => by ring
    dsimp [g]; rw [hInt]; nlinarith only [hident, hcbe]
  -- Step 3: Multiply by `rho Δ`
  obtain ⟨Mρ, hMρ⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_rho hΔ).continuousOn
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  have hρ_unif : TendstoUniformlyOn (fun _ : ℕ => rho Δ) (rho Δ) atTop X :=
    Metric.tendstoUniformlyOn_iff.mpr fun _ hε => Eventually.of_forall fun _ _ _ => by simpa using hε
  have hfinal := (tendstoUniformlyOn_mul_of_bounds hρ_unif hF
    (show 0 ≤ max Mρ 1 by linarith [le_max_right Mρ 1]) (show 0 ≤ max Cf 1 by linarith [le_max_right Cf 1])
    (fun _ x hx => (show |rho Δ x| ≤ Mρ by simpa only [Real.norm_eq_abs] using hMρ x hx).trans (le_max_left _ _))
    (fun x hx => (show |f x| ≤ Cf by simpa only [Real.norm_eq_abs] using hCf x hx).trans (le_max_left _ _))).congr_right hid
  exact ⟨φ, UniformFun.tendsto_iff_tendstoUniformly.mpr (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hfinal)⟩

end

end PottsDiscontinuity.Bethe
