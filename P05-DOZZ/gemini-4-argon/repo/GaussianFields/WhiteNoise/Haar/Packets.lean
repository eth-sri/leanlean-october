/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.WhiteNoise.Haar.OneDimensional

/-!
# GaussianFields multidimensional Haar packets

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

namespace GaussianFields

/-- The tensor-product Haar packet on `R^d`. -/
@[expose]
noncomputable def haarPacket {d : Nat} (idx : HaarIndex d) : Vec d → ℝ :=
  fun x => ∏ r : Fin d, haar1D idx.scale (idx.cell r) (idx.signature r) (x r)

/-- The child cell selected by a Boolean left/right side vector. -/
@[expose]
def haarChildCell {d : Nat} (cell : Fin d → ℤ) (side : Fin d → Bool) : Fin d → ℤ :=
  fun r => (2 : ℤ) * cell r + if side r then 1 else 0

/-- The coefficient of a parent packet in the tensor expansion of a father child. -/
@[expose]
noncomputable def haarChildCoefficient {d : Nat}
    (side signature : Fin d → Bool) : ℝ :=
  ∏ r : Fin d,
    (Real.sqrt 2)⁻¹ * (if side r && signature r then (-1 : ℝ) else 1)

theorem haarPacket_child_father_refine_pointwise {d} j
    (cell : Fin d → ℤ) side x :
    haarPacket
        { scale := j + 1
          cell := haarChildCell cell side
          signature := fun _ => false } x =
      ∑ signature : Fin d → Bool,
        haarChildCoefficient side signature *
          haarPacket { scale := j, cell := cell, signature := signature } x := by
  unfold haarPacket haarChildCell haarChildCoefficient
  simp_rw [haar1D_child_father_refine_bool]
  rw [Finset.prod_univ_sum]
  congr
  ext signature
  rw [← Finset.prod_mul_distrib]

/-- The dyadic box in `R^d` associated with scale `j` and integer cell `cell`. -/
@[expose]
def dyadicBox {d : Nat} (j : ℤ) (cell : Fin d → ℤ) : Set (Vec d) :=
  Set.pi Set.univ fun r => dyadicInterval j (cell r)

theorem measurableSet_dyadicBox {d : Nat} (j : ℤ) (cell : Fin d → ℤ) :
    MeasurableSet (dyadicBox j cell) := by
  unfold dyadicBox
  exact MeasurableSet.pi Set.countable_univ fun r _ => measurableSet_dyadicInterval j (cell r)

theorem volume_dyadicBox_ne_top {d : Nat} (j : ℤ) (cell : Fin d → ℤ) :
    volume (dyadicBox j cell) ≠ ∞ := by
  unfold dyadicBox dyadicInterval
  rw [Real.volume_pi_Ico]
  exact ENNReal.prod_ne_top fun r _ => ENNReal.ofReal_ne_top

theorem haarPacket_father_eq_indicator_dyadicBox {d}
    j (cell : Fin d → ℤ) x :
    haarPacket { scale := j, cell := cell, signature := fun _ => false } x =
      (∏ _r : Fin d, haarScaleFactor j) *
        Set.indicator (dyadicBox j cell) (fun _ : Vec d => (1 : ℝ)) x := by
  unfold haarPacket
  calc
    ∏ r : Fin d, haar1D j (cell r) false (x r) =
        ∏ r : Fin d,
          haarScaleFactor j *
            Set.indicator (dyadicInterval j (cell r)) (fun _ => (1 : ℝ)) (x r) := by
          refine Finset.prod_congr rfl ?_
          intro r _hr
          exact haar1D_father_eq_indicator_dyadicInterval j (cell r) (x r)
    _ = (∏ _r : Fin d, haarScaleFactor j) *
        ∏ r : Fin d,
          Set.indicator (dyadicInterval j (cell r)) (fun _ : ℝ => (1 : ℝ)) (x r) := by
          rw [← Finset.prod_mul_distrib]
    _ = (∏ _r : Fin d, haarScaleFactor j) *
        Set.indicator (dyadicBox j cell) (fun _ : Vec d => (1 : ℝ)) x := by
          congr 1
          rw [(show (fun _ : ℝ => (1 : ℝ)) = (1 : ℝ → ℝ) by funext y; rfl), (show (fun _ : Vec d => (1 : ℝ)) = (1 : Vec d → ℝ) by funext y; rfl), dyadicBox]
          simpa only [Finset.coe_univ] using (Set.indicator_pi_one_apply (M₀ := ℝ) (s := (Finset.univ : Finset (Fin d))) (t := fun r => dyadicInterval j (cell r)) (f := x)).symm

@[fun_prop]
theorem measurable_haarPacket {d : Nat} (idx : HaarIndex d) :
    Measurable (haarPacket idx) := by
  unfold haarPacket
  fun_prop

theorem haarPacket_sq {d} (idx : HaarIndex d) x :
    haarPacket idx x ^ (2 : Nat) =
      ∏ r : Fin d, haar1D idx.scale (idx.cell r) (idx.signature r) (x r) ^ (2 : Nat) := by
  unfold haarPacket
  rw [pow_two, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro r _hr
  rw [pow_two]

theorem integrable_haarPacket_sq {d} idx :
    Integrable (fun x : Vec d => haarPacket idx x ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
  refine (show Integrable (fun x => ∏ r : Fin d, haar1D idx.scale (idx.cell r) (idx.signature r) (x r) ^ (2 : Nat)) (volume : Measure (Vec d)) by rw [MeasureTheory.volume_pi]; exact MeasureTheory.Integrable.fintype_prod (𝕜 := ℝ) (ι := Fin d) (E := ℝ) (μ := fun _ => (volume : Measure ℝ)) (f := fun r y => haar1D idx.scale (idx.cell r) (idx.signature r) y ^ (2 : Nat)) (fun r => integrable_haar1D_sq idx.scale (idx.cell r) (idx.signature r))).congr (ae_of_all _ ?_)
  intro x
  exact (haarPacket_sq idx x).symm

theorem memLp_haarPacket {d} (idx : HaarIndex d) :
    MemLp (haarPacket idx) 2 (volume : Measure (Vec d)) := by
  rw [memLp_two_iff_integrable_sq]
  · exact integrable_haarPacket_sq idx
  · exact (measurable_haarPacket idx).aestronglyMeasurable

/-- The tensor-product Haar packet as an `L²(R^d)` vector. -/
@[expose]
noncomputable def haarPacketLp {d : Nat} (idx : HaarIndex d) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  (memLp_haarPacket idx).toLp (haarPacket idx)


private theorem coeFn_finset_sum_lp_real {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} s (f : ι → Lp ℝ 2 μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction with
  | empty =>
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
      simpa using hx
  | insert i s hi ih =>
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hadd hsum
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, Pi.add_apply, hsum]

theorem haarPacketLp_child_father_refine {d} j
    (cell : Fin d → ℤ) side :
    haarPacketLp
        { scale := j + 1
          cell := haarChildCell cell side
          signature := fun _ => false } =
      ∑ signature : Fin d → Bool,
        haarChildCoefficient side signature •
          haarPacketLp { scale := j, cell := cell, signature := signature } := by
  refine Lp.ext ?_
  let child : HaarIndex d :=
    { scale := j + 1
      cell := haarChildCell cell side
      signature := fun _ => false }
  let parent : (Fin d → Bool) → HaarIndex d :=
    fun signature => { scale := j, cell := cell, signature := signature }
  filter_upwards [(memLp_haarPacket child).coeFn_toLp,
    coeFn_finset_sum_lp_real (Finset.univ : Finset (Fin d → Bool))
      (fun signature =>
        haarChildCoefficient side signature • haarPacketLp (parent signature)),
    ae_all_iff.2 fun signature =>
      Lp.coeFn_smul (haarChildCoefficient side signature) (haarPacketLp (parent signature)),
    ae_all_iff.2 fun signature => (memLp_haarPacket (parent signature)).coeFn_toLp] with
    x hchild hsum hsmul hparent
  change (haarPacketLp child) x =
    (∑ signature : Fin d → Bool,
      haarChildCoefficient side signature • haarPacketLp (parent signature)) x
  change ((memLp_haarPacket child).toLp (haarPacket child)) x =
    (∑ signature : Fin d → Bool,
      haarChildCoefficient side signature • haarPacketLp (parent signature)) x
  rw [hchild, hsum]
  simp_rw [hsmul]
  change haarPacket child x =
    ∑ signature : Fin d → Bool,
      haarChildCoefficient side signature * (haarPacketLp (parent signature)) x
  unfold haarPacketLp
  simp_rw [hparent]
  exact haarPacket_child_father_refine_pointwise j cell side x



theorem integral_haarPacket_mul_finer_of_signature_true_nat_succ {d}
    (idx₁ idx₂ : HaarIndex d) n
    (hscale : idx₂.scale = idx₁.scale + ((n + 1 : ℕ) : ℤ))
    {r} (hsig : idx₂.signature r = true) :
    ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume = 0 := by
  have integral_haarPacket_mul_product : ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume = ∏ r : Fin d, ∫ y : ℝ, haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y * haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y ∂volume := by
    have haarPacket_mul_product x : haarPacket idx₁ x * haarPacket idx₂ x = ∏ r : Fin d, haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) (x r) * haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) (x r) := by
      unfold haarPacket
      rw [← Finset.prod_mul_distrib]
    calc
      ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume =
          ∫ x : Vec d,
            ∏ r : Fin d,
              haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) (x r) *
                haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) (x r) ∂volume := by
            refine integral_congr_ae (ae_of_all _ ?_)
            intro x
            exact haarPacket_mul_product x
      _ = ∏ r : Fin d,
          ∫ y : ℝ,
            haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
              haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y ∂volume := by
            change ∫ x : (Fin d → ℝ),
                ∏ r : Fin d,
                  (fun y =>
                    haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                      haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y) (x r)
                =
              ∏ r : Fin d,
                ∫ y : ℝ,
                  (fun y =>
                    haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                      haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y) y
            exact MeasureTheory.integral_fintype_prod_volume_eq_prod
              (𝕜 := ℝ) (ι := Fin d) (E := fun _ => ℝ)
              (fun r y =>
                haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                  haar1D idx₂.scale (idx₂.cell r) (idx₂.signature r) y)
  rw [integral_haarPacket_mul_product]
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  rw [hscale, hsig]
  exact integral_haar1D_mul_finer_mother_nat_succ idx₁.scale
    (idx₁.cell r) (idx₂.cell r) (idx₁.signature r) n

theorem inner_haarPacketLp_finer_of_signature_true_nat_succ {d}
    (idx₁ idx₂ : HaarIndex d) n
    (hscale : idx₂.scale = idx₁.scale + ((n + 1 : ℕ) : ℤ))
    {r} (hsig : idx₂.signature r = true) :
    ⟪haarPacketLp idx₁, haarPacketLp idx₂⟫_ℝ = 0 := by
  have inner_haarPacketLp_eq_integral {d} idx₁ idx₂ : ⟪haarPacketLp idx₁, haarPacketLp idx₂⟫_ℝ = ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume := by
    rw [haarPacketLp, haarPacketLp, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_haarPacket idx₁).coeFn_toLp,
      (memLp_haarPacket idx₂).coeFn_toLp] with x hx₁ hx₂
    simp [hx₁, hx₂, mul_comm]
  rw [inner_haarPacketLp_eq_integral]
  exact integral_haarPacket_mul_finer_of_signature_true_nat_succ idx₁ idx₂ n hscale hsig




theorem integral_haarPacket_mul_same_scale_ite {d} (idx₁ idx₂ : HaarIndex d)
    (hscale : idx₁.scale = idx₂.scale) :
    ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume =
      if idx₁ = idx₂ then 1 else 0 := by
  have prod_haarPacket_same_scale_inner_eq_ite : (∏ r : Fin d, (if idx₁.cell r = idx₂.cell r then if idx₁.signature r = idx₂.signature r then (1 : ℝ) else 0 else 0)) = if idx₁ = idx₂ then 1 else 0 := by
    by_cases hidx : idx₁ = idx₂
    · subst idx₂
      simp
    · have hne : ∃ r : Fin d, idx₁.cell r ≠ idx₂.cell r ∨
          idx₁.signature r ≠ idx₂.signature r := by
        by_contra hnot
        push Not at hnot
        apply hidx
        have hcell := funext fun r => (hnot r).1
        have hsig := funext fun r => (hnot r).2
        cases idx₁
        cases idx₂
        simp at hscale hcell hsig ⊢
        exact ⟨hscale, hcell, hsig⟩
      rcases hne with ⟨r, hrcell | hrsig⟩
      · rw [ite_eq_right hidx]
        apply Finset.prod_eq_zero (Finset.mem_univ r)
        simp [hrcell]
      · rw [ite_eq_right hidx]
        apply Finset.prod_eq_zero (Finset.mem_univ r)
        simp [hrsig]
  have integral_haarPacket_mul_same_scale : ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume = ∏ r : Fin d, (if idx₁.cell r = idx₂.cell r then if idx₁.signature r = idx₂.signature r then (1 : ℝ) else 0 else 0) := by
    have haarPacket_mul_same_scale x : haarPacket idx₁ x * haarPacket idx₂ x = ∏ r : Fin d, haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) (x r) * haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) (x r) := by
      unfold haarPacket
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl ?_
      intro r _hr
      rw [← hscale]
    calc
      ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume =
          ∫ x : Vec d,
            ∏ r : Fin d,
              haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) (x r) *
                haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) (x r) ∂volume := by
            refine integral_congr_ae (ae_of_all _ ?_)
            intro x
            exact haarPacket_mul_same_scale x
      _ = ∏ r : Fin d,
          ∫ y : ℝ,
            haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
              haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) y ∂volume := by
            change ∫ x : (Fin d → ℝ),
                ∏ r : Fin d,
                  (fun y =>
                    haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                      haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) y) (x r)
                =
              ∏ r : Fin d,
                ∫ y : ℝ,
                  (fun y =>
                    haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                      haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) y) y
            exact MeasureTheory.integral_fintype_prod_volume_eq_prod
              (𝕜 := ℝ) (ι := Fin d) (E := fun _ => ℝ)
              (fun r y =>
                haar1D idx₁.scale (idx₁.cell r) (idx₁.signature r) y *
                  haar1D idx₁.scale (idx₂.cell r) (idx₂.signature r) y)
      _ = ∏ r : Fin d,
          (if idx₁.cell r = idx₂.cell r then
            if idx₁.signature r = idx₂.signature r then (1 : ℝ) else 0
          else 0) := by
            congr 1
            ext r
            exact integral_haar1D_mul_haar1D_same_scale idx₁.scale
              (idx₁.cell r) (idx₂.cell r) (idx₁.signature r) (idx₂.signature r)
  rw [integral_haarPacket_mul_same_scale]
  exact prod_haarPacket_same_scale_inner_eq_ite

/-- Same-scale tensor Haar `L²` inner products reduce to equality of full packet indices. -/
theorem inner_haarPacketLp_same_scale {d} (idx₁ idx₂ : HaarIndex d)
    (hscale : idx₁.scale = idx₂.scale) :
    ⟪haarPacketLp idx₁, haarPacketLp idx₂⟫_ℝ =
      if idx₁ = idx₂ then 1 else 0 := by
  rw [haarPacketLp, haarPacketLp, MeasureTheory.L2.inner_def]
  calc
    ∫ x : Vec d,
        inner (𝕜 := ℝ)
          ((memLp_haarPacket idx₁).toLp (haarPacket idx₁) x)
          ((memLp_haarPacket idx₂).toLp (haarPacket idx₂) x)
        ∂volume =
        ∫ x : Vec d, haarPacket idx₁ x * haarPacket idx₂ x ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_haarPacket idx₁).coeFn_toLp,
            (memLp_haarPacket idx₂).coeFn_toLp] with x hx₁ hx₂
          simp [hx₁, hx₂, mul_comm]
    _ = if idx₁ = idx₂ then 1 else 0 :=
      integral_haarPacket_mul_same_scale_ite idx₁ idx₂ hscale

/-- The corrected tensor-product Haar wavelet packet. -/
@[expose]
noncomputable def haarWaveletPacket {d : Nat} (idx : HaarWaveletIndex d) : Vec d → ℝ :=
  haarPacket idx.toHaarIndex

@[fun_prop]
theorem measurable_haarWaveletPacket {d : Nat} (idx : HaarWaveletIndex d) :
    Measurable (haarWaveletPacket idx) :=
  measurable_haarPacket idx.toHaarIndex

theorem exists_true_of_ne_false_signature {d} {signature}
    (h : signature ≠ fun _ => false) :
    ∃ r : Fin d, signature r = true := by
  by_contra hnot
  push Not at hnot
  apply h
  funext r
  cases hsig : signature r
  · rfl
  · exact False.elim (hnot r hsig)


theorem memLp_haarWaveletPacket {d} idx :
    MemLp (haarWaveletPacket idx) 2 (volume : Measure (Vec d)) := by
  change MemLp (haarPacket idx.toHaarIndex) 2 (volume : Measure (Vec d))
  exact memLp_haarPacket idx.toHaarIndex

/-- The corrected tensor-product Haar wavelet packet as an `L²(R^d)` vector. -/
@[expose]
noncomputable def haarWaveletPacketLp {d : Nat} (idx : HaarWaveletIndex d) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  (memLp_haarWaveletPacket idx).toLp (haarWaveletPacket idx)

theorem haarWaveletPacketLp_eq_haarPacketLp {d} (idx : HaarWaveletIndex d) :
    haarWaveletPacketLp idx = haarPacketLp idx.toHaarIndex :=
  rfl


theorem inner_haarWaveletPacketLp_finer_nat_succ {d}
    (idx₁ idx₂ : HaarWaveletIndex d) n
    (hscale : idx₂.scale = idx₁.scale + ((n + 1 : ℕ) : ℤ)) :
    ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ = 0 := by
  have integral_haarWaveletPacket_mul_finer_nat_succ : ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume = 0 := by
    rcases exists_true_of_ne_false_signature idx₂.signature.property with ⟨r, hsig⟩
    exact integral_haarPacket_mul_finer_of_signature_true_nat_succ
      idx₁.toHaarIndex idx₂.toHaarIndex n hscale hsig
  rw [haarWaveletPacketLp, haarWaveletPacketLp, MeasureTheory.L2.inner_def]
  calc
    ∫ x : Vec d,
        inner (𝕜 := ℝ)
          ((memLp_haarWaveletPacket idx₁).toLp (haarWaveletPacket idx₁) x)
          ((memLp_haarWaveletPacket idx₂).toLp (haarWaveletPacket idx₂) x)
        ∂volume =
        ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_haarWaveletPacket idx₁).coeFn_toLp,
            (memLp_haarWaveletPacket idx₂).coeFn_toLp] with x hx₁ hx₂
          simp [hx₁, hx₂, mul_comm]
    _ = 0 := integral_haarWaveletPacket_mul_finer_nat_succ


theorem exists_nat_succ_scale_gap {j₁ j₂} (h : j₁ < j₂) :
    ∃ n : ℕ, j₂ = j₁ + ((n + 1 : ℕ) : ℤ) := by
  let m : ℕ := (j₂ - j₁).toNat
  have hm_cast : (m : ℤ) = j₂ - j₁ := Int.toNat_sub_of_le (show j₁ ≤ j₂ from le_of_lt h)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (by exact_mod_cast (show 0 < (m : ℤ) by simpa [hm_cast] using (sub_pos.mpr h))))
  refine ⟨n, ?_⟩
  omega



theorem inner_haarWaveletPacketLp (d : Nat) (idx₁ idx₂ : HaarWaveletIndex d) :
    ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ =
      if idx₁ = idx₂ then 1 else 0 := by
  have inner_haarWaveletPacketLp_same_scale (hscale : idx₁.scale = idx₂.scale) : ⟪haarWaveletPacketLp idx₁, haarWaveletPacketLp idx₂⟫_ℝ = if idx₁ = idx₂ then 1 else 0 := by
    rw [haarWaveletPacketLp, haarWaveletPacketLp, MeasureTheory.L2.inner_def]
    calc
      ∫ x : Vec d,
          inner (𝕜 := ℝ)
            ((memLp_haarWaveletPacket idx₁).toLp (haarWaveletPacket idx₁) x)
            ((memLp_haarWaveletPacket idx₂).toLp (haarWaveletPacket idx₂) x)
          ∂volume =
          ∫ x : Vec d, haarWaveletPacket idx₁ x * haarWaveletPacket idx₂ x ∂volume := by
            refine integral_congr_ae ?_
            filter_upwards [(memLp_haarWaveletPacket idx₁).coeFn_toLp,
              (memLp_haarWaveletPacket idx₂).coeFn_toLp] with x hx₁ hx₂
            simp [hx₁, hx₂, mul_comm]
      _ = if idx₁ = idx₂ then 1 else 0 := by
            change ∫ x : Vec d, haarPacket idx₁.toHaarIndex x * haarPacket idx₂.toHaarIndex x
                ∂volume = if idx₁ = idx₂ then 1 else 0
            rw [integral_haarPacket_mul_same_scale_ite idx₁.toHaarIndex idx₂.toHaarIndex hscale]
            by_cases hidx : idx₁ = idx₂
            · simp [hidx]
            · have hraw : idx₁.toHaarIndex ≠ idx₂.toHaarIndex := by
                intro hraw
                exact hidx (HaarWaveletIndex.toHaarIndex_injective hraw)
              simp [hidx, hraw]
  by_cases hscale_eq : idx₁.scale = idx₂.scale
  · rw [inner_haarWaveletPacketLp_same_scale hscale_eq]
  · have hlt_or_gt : idx₁.scale < idx₂.scale ∨ idx₂.scale < idx₁.scale :=
      lt_or_gt_of_ne hscale_eq
    rw [ite_eq_right]
    · rcases hlt_or_gt with hlt | hgt
      · exact (fun hscale => by obtain ⟨n, hn⟩ := exists_nat_succ_scale_gap hscale; exact inner_haarWaveletPacketLp_finer_nat_succ idx₁ idx₂ n hn) hlt
      · exact (fun hscale => by obtain ⟨n, hn⟩ := exists_nat_succ_scale_gap hscale; exact (fun n (hscale : idx₁.scale = idx₂.scale + ((n + 1 : ℕ) : ℤ)) => by rw [← inner_conj_symm]; simp [inner_haarWaveletPacketLp_finer_nat_succ idx₂ idx₁ n hscale]) n hn) hgt
    · intro hidx
      exact hscale_eq (by rw [hidx])

end GaussianFields

end
