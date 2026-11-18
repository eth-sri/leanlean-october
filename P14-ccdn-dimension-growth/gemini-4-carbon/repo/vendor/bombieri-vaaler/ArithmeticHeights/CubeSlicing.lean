/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

public section

open MeasureTheory Set
open scoped ENNReal Real Pointwise

private theorem iSup_rpow {ι : Sort*} (u : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, u i) ^ p = ⨆ i, u i ^ p := by
  simpa only [ENNReal.orderIsoRpow_apply] using (ENNReal.orderIsoRpow p hp).map_iSup u

private theorem volume_add_le {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsne : s.Nonempty) (htne : t.Nonempty) : volume s + volume t ≤ volume (s + t) := by
  obtain ⟨x₀, hx₀⟩ := hsne
  obtain ⟨y₀, hy₀⟩ := htne
  rcases eq_or_ne (volume (s + t)) ⊤ with hst | hst; · simp [hst]
  have hle_sum {u v : Set ℝ} {y : ℝ} (hy : y ∈ v) : volume u ≤ volume (u + v) := by
    have h : volume ((· + y) '' u) ≤ volume (u + v) :=
      measure_mono (by rintro _ ⟨x, hx, rfl⟩; exact Set.add_mem_add hx hy)
    simpa using h
  have hsv : volume s ≠ ⊤ := ne_top_of_le_ne_top hst (hle_sum hy₀)
  have htv : volume t ≠ ⊤ := ne_top_of_le_ne_top (add_comm s t ▸ hst) (hle_sum hx₀)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have h2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by simp [ENNReal.div_eq_zero_iff, hε.ne']
  obtain ⟨K, hKs, hKc, hK⟩ := hs.exists_isCompact_lt_add hsv h2
  obtain ⟨L, hLt, hLc, hL⟩ := ht.exists_isCompact_lt_add htv h2
  set K' := insert x₀ K
  set L' := insert y₀ L
  have hK'c : IsCompact K' := hKc.insert x₀
  have hL'c : IsCompact L' := hLc.insert y₀
  set a := sSup K'
  set b := sInf L'
  have ha : a ∈ s := insert_subset hx₀ hKs (hK'c.sSup_mem ⟨x₀, mem_insert _ _⟩)
  have hb : b ∈ t := insert_subset hy₀ hLt (hL'c.sInf_mem ⟨y₀, mem_insert _ _⟩)
  set A := (· + b) '' K'
  set B := (a + ·) '' L'
  have h0 : volume (A ∩ B) = 0 := measure_mono_null (by
    rintro x ⟨⟨u, hu, rfl⟩, ⟨v, hv, hx⟩⟩
    change u + b = a + b
    linarith [le_csSup hK'c.bddAbove hu, csInf_le hL'c.bddBelow hv, show a + v = u + b from hx])
    (measure_singleton _)
  have hAB : volume K' + volume L' ≤ volume (s + t) := by
    calc volume K' + volume L' = volume A + volume B := by simp [A, B]
      _ = volume (A ∪ B) := by
          rw [← measure_union_add_inter A (hL'c.image (by fun_prop)).measurableSet, h0, add_zero]
      _ ≤ volume (s + t) := measure_mono (union_subset
          (by rintro _ ⟨u, hu, rfl⟩; exact Set.add_mem_add (insert_subset hx₀ hKs hu) hb)
          (by rintro _ ⟨v, hv, rfl⟩; exact Set.add_mem_add ha (insert_subset hy₀ hLt hv)))
  calc volume s + volume t ≤ (volume K + ε / 2) + (volume L + ε / 2) := add_le_add hK.le hL.le
    _ ≤ (volume K' + volume L') + (ε / 2 + ε / 2) := by
        rw [add_add_add_comm]
        exact add_le_add (add_le_add (measure_mono (subset_insert _ _))
          (measure_mono (subset_insert _ _))) le_rfl
    _ ≤ volume (s + t) + ε := by rw [ENNReal.add_halves]; gcongr

private theorem lintegral_eq_meas_lt {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} := by
  have hS : MeasurableSet {p : α × ℝ | 0 < p.2 ∧ ENNReal.ofReal p.2 < f p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hf.comp measurable_fst))
  set F : α → ℝ → ℝ≥0∞ := fun x t =>
    {p : α × ℝ | 0 < p.2 ∧ ENNReal.ofReal p.2 < f p.1}.indicator 1 (x, t)
  have h1 (x : α) : ∫⁻ t, F x t = f x := by
    have hm : MeasurableSet {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f x} :=
      (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
    rw [show F x = {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f x}.indicator 1 from
      funext fun _ => by simp [F, indicator_apply], lintegral_indicator_one hm]
    rcases eq_or_ne (f x) ⊤ with hc | hc
    · rw [hc, show {t : ℝ | 0 < t ∧ ENNReal.ofReal t < ⊤} = Ioi 0 by
        ext; simp [ENNReal.ofReal_lt_top], Real.volume_Ioi]
    · rw [show {t : ℝ | 0 < t ∧ ENNReal.ofReal t < f x} = Ioo 0 (f x).toReal by
        ext; exact and_congr_right fun ht => ENNReal.ofReal_lt_iff_lt_toReal ht.le hc,
        Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hc]
  calc ∫⁻ x, f x ∂μ = ∫⁻ x, (∫⁻ t, F x t) ∂μ := by simp_rw [h1]
    _ = ∫⁻ t, (∫⁻ x, F x t ∂μ) :=
        lintegral_lintegral_swap (f := F) (measurable_one.indicator hS).aemeasurable
    _ = ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun t => ?_
        by_cases ht : 0 < t
        · rw [show (fun x => F x t) = {x | ENNReal.ofReal t < f x}.indicator 1 from
            funext fun _ => by simp [F, indicator_apply, ht],
            lintegral_indicator_one (measurableSet_lt measurable_const hf),
            indicator_of_mem (mem_Ioi.mpr ht)]
        · rw [show (fun x => F x t) = fun _ => (0 : ℝ≥0∞) from
            funext fun _ => by simp [F, indicator_apply, ht],
            lintegral_zero, indicator_of_notMem (by simpa using ht)]

private theorem prekopaLeindler_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (key : ∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y)) :
    (∫⁻ x, f x) ^ a * (∫⁻ y, g y) ^ b ≤ ∫⁻ z, h z := by
  have hunit {u v w : ℝ → ℝ≥0∞} (hu : Measurable u) (hv : Measurable v) (hw : Measurable w)
      (hu1 : ∀ x, u x ≤ 1) (hv1 : ∀ y, v y ≤ 1)
      (hune : ∀ t, 0 < t → t < 1 → {x | ENNReal.ofReal t < u x}.Nonempty)
      (hvne : ∀ t, 0 < t → t < 1 → {y | ENNReal.ofReal t < v y}.Nonempty)
      (hkey : ∀ x y, u x ^ a * v y ^ b ≤ w (a • x + b • y)) :
      ENNReal.ofReal a * (∫⁻ x, u x) + ENNReal.ofReal b * (∫⁻ y, v y) ≤ ∫⁻ z, w z := by
    rw [lintegral_eq_meas_lt _ hu, lintegral_eq_meas_lt _ hv, lintegral_eq_meas_lt _ hw,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (le_lintegral_add _ _).trans (lintegral_mono_ae ?_)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t (ht : 0 < t)
    rcases lt_or_ge t 1 with ht1 | ht1
    · obtain ⟨x₀, hx₀⟩ := hune t ht ht1
      obtain ⟨y₀, hy₀⟩ := hvne t ht ht1
      have hc0 : ENNReal.ofReal t ≠ 0 := by simp [ENNReal.ofReal_eq_zero, not_le.mpr ht]
      have hBM := volume_add_le ((measurableSet_lt measurable_const hu).const_smul₀ a)
        ((measurableSet_lt measurable_const hv).const_smul₀ b)
        ⟨a • x₀, x₀, hx₀, rfl⟩ ⟨b • y₀, y₀, hy₀, rfl⟩
      simp only [Measure.addHaar_smul, Module.finrank_self, pow_one, abs_of_pos ha,
        abs_of_pos hb] at hBM
      refine hBM.trans (measure_mono ?_)
      rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      refine lt_of_lt_of_le ?_ (hkey x y)
      rw [show ENNReal.ofReal t = ENNReal.ofReal t ^ b * ENNReal.ofReal t ^ a by
        rw [← ENNReal.rpow_add _ _ hc0 ENNReal.ofReal_ne_top, add_comm, hab, ENNReal.rpow_one]]
      calc ENNReal.ofReal t ^ b * ENNReal.ofReal t ^ a < ENNReal.ofReal t ^ b * u x ^ a :=
            ENNReal.mul_lt_mul_right (ENNReal.rpow_pos hc0.bot_lt ENNReal.ofReal_ne_top).ne'
              (ENNReal.rpow_ne_top_of_nonneg hb.le ENNReal.ofReal_ne_top)
              (ENNReal.rpow_lt_rpow hx ha)
        _ = u x ^ a * ENNReal.ofReal t ^ b := mul_comm _ _
        _ ≤ u x ^ a * v y ^ b := by gcongr; exact hy.le
    · have hAe : {x | ENNReal.ofReal t < u x} = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx =>
        hx.not_ge ((hu1 x).trans (ENNReal.one_le_ofReal.mpr ht1))
      have hBe : {y | ENNReal.ofReal t < v y} = ∅ := eq_empty_iff_forall_notMem.mpr fun y hy =>
        hy.not_ge ((hv1 y).trans (ENNReal.one_le_ofReal.mpr ht1))
      simp [hAe, hBe]
  rcases eq_or_ne (∫⁻ x, f x) 0 with h0 | hf0; · simp [h0, ENNReal.zero_rpow_of_pos ha]
  rcases eq_or_ne (∫⁻ y, g y) 0 with h0 | hg0; · simp [h0, ENNReal.zero_rpow_of_pos hb]
  obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by contrapose! hf0; simp [hf0]
  obtain ⟨y₀, hy₀⟩ : ∃ y, g y ≠ 0 := by contrapose! hg0; simp [hg0]
  let tr (u : ℝ → ℝ≥0∞) (n : ℕ) (x : ℝ) := min (u x) ((n : ℝ≥0∞) + 1)
  have hnorm {u : ℝ → ℝ≥0∞} {z₀ : ℝ} (hz : u z₀ ≠ 0) (n : ℕ) :
      (⨆ x, tr u n x) ≠ 0 ∧ (⨆ x, tr u n x) ≠ ⊤ ∧
        (∀ x, (⨆ x, tr u n x)⁻¹ * tr u n x ≤ 1) ∧
        ∀ t, 0 < t → t < 1 → {x | ENNReal.ofReal t < (⨆ x, tr u n x)⁻¹ * tr u n x}.Nonempty := by
    set M := ⨆ x, tr u n x
    have hMT : M ≠ ⊤ := ne_top_of_le_ne_top (by simp) (iSup_le fun _ => min_le_right _ _)
    have hM0 : M ≠ 0 := (lt_of_lt_of_le (by simp [tr, pos_iff_ne_zero, hz]) (le_iSup (tr u n) z₀)).ne'
    refine ⟨hM0, hMT, fun x => (mul_le_mul_right (le_iSup (tr u n) x) M⁻¹).trans_eq
      (ENNReal.inv_mul_cancel hM0 hMT), fun t _ ht1 => ?_⟩
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp (mul_comm (ENNReal.ofReal t) M ▸
      (ENNReal.mul_lt_mul_right hM0 hMT (ENNReal.ofReal_lt_one.mpr ht1)).trans_eq (mul_one M))
    refine ⟨x, ?_⟩
    rw [show ENNReal.ofReal t = M⁻¹ * (ENNReal.ofReal t * M) by
      rw [mul_comm _ M, ← mul_assoc, ENNReal.inv_mul_cancel hM0 hMT, one_mul]]
    exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hMT) (ENNReal.inv_ne_top.mpr hM0) hx
  have hbdd (n : ℕ) : (∫⁻ x, tr f n x) ^ a * (∫⁻ y, tr g n y) ^ b ≤ ∫⁻ z, h z := by
    obtain ⟨hM0, hMT, hMf1, hMfne⟩ := hnorm hx₀ n
    obtain ⟨hN0, hNT, hNg1, hNgne⟩ := hnorm hy₀ n
    set M := ⨆ x, tr f n x
    set N := ⨆ y, tr g n y
    have hMa0 : M ^ a ≠ 0 := (ENNReal.rpow_pos hM0.bot_lt hMT).ne'
    have hMaT : M ^ a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ha.le hMT
    have hNb0 : N ^ b ≠ 0 := (ENNReal.rpow_pos hN0.bot_lt hNT).ne'
    have hNbT : N ^ b ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hb.le hNT
    set c := (M ^ a * N ^ b)⁻¹ with hc
    have hcT : c ≠ ⊤ := ENNReal.inv_ne_top.mpr (mul_ne_zero hMa0 hNb0)
    have hcomp (u v : ℝ≥0∞) : (M⁻¹ * u) ^ a * (N⁻¹ * v) ^ b = c * (u ^ a * v ^ b) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le, ENNReal.mul_rpow_of_nonneg _ _ hb.le,
        ENNReal.inv_rpow, ENNReal.inv_rpow, hc, ENNReal.mul_inv (Or.inl hMa0) (Or.inl hMaT)]
      ring
    have hu := hunit (u := fun x => M⁻¹ * tr f n x) (v := fun y => N⁻¹ * tr g n y)
      (w := fun z => c * h z) (measurable_const.mul (hf.min measurable_const))
      (measurable_const.mul (hg.min measurable_const)) (measurable_const.mul hh)
      hMf1 hNg1 hMfne hNgne fun x y => by
        rw [hcomp]; gcongr
        exact (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ha.le)
          (ENNReal.rpow_le_rpow (min_le_left _ _) hb.le)).trans (key x y)
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hM0),
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hN0),
      lintegral_const_mul' _ _ hcT] at hu
    have hAM := ENNReal.geom_mean_le_arith_mean2_weighted a.toNNReal b.toNNReal
      (M⁻¹ * ∫⁻ x, tr f n x) (N⁻¹ * ∫⁻ y, tr g n y)
      (NNReal.coe_injective (by push_cast [Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ hb.le]; exact hab))
    rw [Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ hb.le, hcomp] at hAM
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top hMaT hNbT))
      hcT).mp (hAM.trans hu)
  have htop : (⨆ n : ℕ, ((n : ℝ≥0∞) + 1)) = ⊤ :=
    top_le_iff.mp (ENNReal.iSup_natCast ▸ iSup_mono fun _ => le_self_add)
  have hlim (u : ℝ → ℝ≥0∞) (hu : Measurable u) : ∫⁻ x, u x = ⨆ n, ∫⁻ x, tr u n x := by
    rw [← lintegral_iSup (fun _ => hu.min measurable_const) fun _ _ hnm _ => min_le_min le_rfl (by gcongr)]
    refine lintegral_congr fun x => le_antisymm (le_of_forall_lt fun c hc => ?_)
      (iSup_le fun _ => min_le_left _ _)
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp (htop ▸ hc.trans_le le_top : c < ⨆ n : ℕ, ((n : ℝ≥0∞) + 1))
    exact (lt_min hc hn).trans_le (le_iSup (fun n => tr u n x) n)
  rw [hlim f hf, hlim g hg, iSup_rpow _ ha, iSup_rpow _ hb, ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  exact iSup_le fun m => (mul_le_mul'
    (ENNReal.rpow_le_rpow (lintegral_mono fun _ => min_le_min le_rfl (by gcongr; exact le_max_left n m)) ha.le)
    (ENNReal.rpow_le_rpow (lintegral_mono fun _ => min_le_min le_rfl (by gcongr; exact le_max_right n m)) hb.le)).trans
      (hbdd (max n m))

private def HasPL {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 → ∀ f g h : E → ℝ≥0∞,
    Measurable f → Measurable g → Measurable h →
      (∀ x y, f x ^ a * g y ^ b ≤ h (a • x + b • y)) →
      (∫⁻ x, f x ∂μ) ^ a * (∫⁻ y, g y ∂μ) ^ b ≤ ∫⁻ z, h z ∂μ

private theorem HasPL.of_mp {E F : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {μ : Measure E} {ν : Measure F}
    (e : E ≃ₗ[ℝ] F) (he : MeasurePreserving e μ ν) (hs : Measurable e.symm) (hF : HasPL ν) :
    HasPL μ := fun a b ha hb hab f g h hf hg hh key => by
  have htr {u : E → ℝ≥0∞} (hu : Measurable u) : ∫⁻ x, (u ∘ e.symm) x ∂ν = ∫⁻ x, u x ∂μ := by
    rw [← he.lintegral_comp (hu.comp hs)]; exact lintegral_congr fun _ => by simp
  rw [← htr hf, ← htr hg, ← htr hh]
  exact hF a b ha hb hab _ _ _ (hf.comp hs) (hg.comp hs) (hh.comp hs) fun u v => by
    simpa [map_add, map_smul] using key (e.symm u) (e.symm v)

private noncomputable def consEquiv (n : ℕ) : (Fin (n + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin n → ℝ) :=
  (Fin.consLinearEquiv ℝ fun _ : Fin (n + 1) => ℝ).symm

private theorem mp_consEquiv (n : ℕ) : MeasurePreserving (consEquiv n) volume volume :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0

private theorem meas_consEquiv_symm (n : ℕ) : Measurable (consEquiv n).symm :=
  Measurable.of_eval fun i => Fin.cases measurable_fst (fun j => (measurable_pi_apply j).comp measurable_snd) i

private theorem hasPL_pi : ∀ n : ℕ, HasPL (volume : Measure (Fin n → ℝ))
  | 0 => fun _ _ _ _ _ f g h _ _ _ key => by
      have hint (u : (Fin 0 → ℝ) → ℝ≥0∞) : ∫⁻ x, u x = u 0 := by
        rw [show u = fun _ => u 0 from funext fun x => congrArg u (Subsingleton.elim _ _),
          lintegral_const, volume_pi, Measure.pi_univ]; simp
      rw [hint f, hint g, hint h]; simpa using key 0 0
  | n + 1 => by
      refine HasPL.of_mp (consEquiv n) (mp_consEquiv n) (meas_consEquiv_symm n) ?_
      rw [Measure.volume_eq_prod]
      intro a b ha hb hab f g h hf hg hh key
      have hm := prekopaLeindler_real ha hb hab hf.lintegral_prod_right'
        hg.lintegral_prod_right' hh.lintegral_prod_right' fun x₁ y₁ =>
        hasPL_pi n a b ha hb hab _ _ _ (hf.comp measurable_prodMk_left)
          (hg.comp measurable_prodMk_left) (hh.comp measurable_prodMk_left)
          fun x₂ y₂ => key (x₁, x₂) (y₁, y₂)
      rwa [← lintegral_prod _ hf.aemeasurable, ← lintegral_prod _ hg.aemeasurable,
        ← lintegral_prod _ hh.aemeasurable] at hm

private theorem hasPL_ips {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : HasPL (volume : Measure E) :=
  let b := stdOrthonormalBasis ℝ E
  HasPL.of_mp b.repr.toLinearEquiv b.measurePreserving_repr
    (LinearMap.continuous_of_finiteDimensional b.repr.toLinearEquiv.symm.toLinearMap).measurable <|
    HasPL.of_mp (WithLp.linearEquiv 2 ℝ _) (PiLp.volume_preserving_ofLp _)
      (PiLp.volume_preserving_toLp _).measurable (hasPL_pi _)

private def LogConcave {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → ℝ≥0∞) : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 → ∀ x y, f x ^ a * f y ^ b ≤ f (a • x + b • y)

private theorem LogConcave.convex_lt {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ℝ≥0∞}
    (hf : LogConcave f) (c : ℝ≥0∞) : Convex ℝ {x | c < f x} := by
  intro x hx y hy a b ha hb hab
  rcases eq_or_lt_of_le ha with rfl | ha0; · simpa [show b = 1 by linarith] using hy
  rcases eq_or_lt_of_le hb with rfl | hb0; · simpa [show a = 1 by linarith] using hx
  refine (lt_min hx hy).trans_le (le_trans ?_ (hf a b ha0 hb0 hab x y))
  rw [show min (f x) (f y) = min (f x) (f y) ^ (a + b) by rw [hab, ENNReal.rpow_one],
    ENNReal.rpow_add_of_nonneg a b ha0.le hb0.le]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ha0.le)
    (ENNReal.rpow_le_rpow (min_le_right _ _) hb0.le)

private theorem logConcave_section {E F : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {ν : Measure F} (hF : HasPL ν)
    {S : Set (E × F)} (hSm : MeasurableSet S) (hSc : Convex ℝ S) :
    LogConcave fun x => ν {y | (x, y) ∈ S} := by
  intro a b ha hb hab x₁ x₂
  have hs (x : E) : MeasurableSet {y | (x, y) ∈ S} := hSm.preimage measurable_prodMk_left
  dsimp only
  rw [← lintegral_indicator_one (hs x₁), ← lintegral_indicator_one (hs x₂),
    ← lintegral_indicator_one (hs _)]
  refine hF a b ha hb hab _ _ _ (measurable_one.indicator (hs x₁))
    (measurable_one.indicator (hs x₂)) (measurable_one.indicator (hs _)) fun y₁ y₂ => ?_
  by_cases h₁ : y₁ ∈ {y | (x₁, y) ∈ S} <;> by_cases h₂ : y₂ ∈ {y | (x₂, y) ∈ S}
  · simp [indicator_of_mem h₁, indicator_of_mem h₂,
      indicator_of_mem (show a • y₁ + b • y₂ ∈ {y | (a • x₁ + b • x₂, y) ∈ S} from
        hSc h₁ h₂ ha.le hb.le hab)]
  · simp [indicator_of_notMem h₂, ENNReal.zero_rpow_of_pos hb]
  · simp [indicator_of_notMem h₁, ENNReal.zero_rpow_of_pos ha]
  · simp [indicator_of_notMem h₁, ENNReal.zero_rpow_of_pos ha]

private lemma measure_symm {α : Type*} [InvolutiveNeg α] [MeasurableSpace α] [MeasurableNeg α]
    (μ : Measure α) [μ.IsNegInvariant] {s t : Set α} (h : ∀ x, -x ∈ s ↔ x ∈ t) : μ s = μ t := by
  rw [← Measure.measure_neg, show -s = t from Set.ext h]

private def HasSliceBound {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) (g : E → ℝ≥0∞) (Q : Set E) : Prop :=
  ∀ A : Set E, MeasurableSet A → Convex ℝ A → (∀ x ∈ A, -x ∈ A) → ∫⁻ x in A, g x ∂μ ≤ μ (A ∩ Q)

private theorem HasSliceBound.lintegral_le {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [Module ℝ E] {μ : Measure E} [SFinite μ] {g : E → ℝ≥0∞} {Q : Set E}
    (hb : HasSliceBound μ g Q) (hg : Measurable g)
    {f : E → ℝ≥0∞} (hf : Measurable f) (hfe : ∀ x, f (-x) = f x) (hflc : LogConcave f) :
    ∫⁻ x, f x * g x ∂μ ≤ ∫⁻ x in Q, f x ∂μ := by
  have hK (t : ℝ) : MeasurableSet {x : E | ENNReal.ofReal t < f x} :=
    measurableSet_lt measurable_const hf
  calc ∫⁻ x, f x * g x ∂μ = ∫⁻ x, f x ∂(μ.withDensity g) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hg hf]; exact lintegral_congr fun _ => mul_comm _ _
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in {x | ENNReal.ofReal t < f x}, g x ∂μ := by
        rw [lintegral_eq_meas_lt _ hf]; exact lintegral_congr fun t => withDensity_apply g (hK t)
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), μ ({x | ENNReal.ofReal t < f x} ∩ Q) :=
        lintegral_mono fun t => hb _ (hK t) (hflc.convex_lt _) fun x hx => by
          change _ < f (-x); rwa [hfe]
    _ = ∫⁻ x in Q, f x ∂μ := by
        rw [lintegral_eq_meas_lt _ hf]
        exact lintegral_congr fun t => (Measure.restrict_apply (hK t)).symm

private theorem HasSliceBound.of_mp {E F : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    [MeasurableSpace F] [AddCommGroup F] [Module ℝ F] {μ : Measure E} {ν : Measure F}
    (e : E ≃ₗ[ℝ] F) (he : MeasurePreserving e μ ν) (hs : Measurable e.symm)
    {g : F → ℝ≥0∞} (hg : Measurable g) {Q : Set F} (hQ : MeasurableSet Q)
    (hb : HasSliceBound ν g Q) : HasSliceBound μ (fun x => g (e x)) (e ⁻¹' Q) := by
  intro A hA hAc hAs
  have hBm : MeasurableSet (e.symm ⁻¹' A) := hs hA
  have h1 : ∫⁻ x in A, g (e x) ∂μ = ∫⁻ y in e.symm ⁻¹' A, g y ∂ν := by
    rw [← lintegral_indicator hBm, ← he.lintegral_comp (hg.indicator hBm), ← lintegral_indicator hA]
    exact lintegral_congr fun x => by by_cases hx : x ∈ A <;> simp [hx]
  rw [h1, show A ∩ e ⁻¹' Q = e ⁻¹' (e.symm ⁻¹' A ∩ Q) by ext; simp,
    he.measure_preimage (hBm.inter hQ).nullMeasurableSet]
  exact hb _ hBm (hAc.linear_preimage e.symm.toLinearMap) fun y hy => by simpa [map_neg] using hAs _ hy

private lemma integral_gauss_one : ∫ t : ℝ, Real.exp (-π * t ^ 2) = 1 := by
  rw [_root_.integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one]

private theorem hasSliceBound_real :
    HasSliceBound (volume : Measure ℝ) (fun x => ENNReal.ofReal (Real.exp (-π * x ^ 2)))
      (Icc (-2⁻¹) 2⁻¹) := by
  intro A _ hAc hAs
  by_cases hc : (2⁻¹ : ℝ) ∈ A
  · have hsub : Icc (-2⁻¹ : ℝ) 2⁻¹ ⊆ A := fun x hx => by
      convert hAc (hAs _ hc) hc (a := 2⁻¹ - x) (b := 2⁻¹ + x) (by linarith [hx.2])
        (by linarith [hx.1]) (by ring) using 1; ring
    calc ∫⁻ x in A, ENNReal.ofReal (Real.exp (-π * x ^ 2))
        ≤ ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-π * x ^ 2)) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ t : ℝ, Real.exp (-π * t ^ 2)) :=
          (ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq Real.pi_pos)
            (.of_forall fun _ => (Real.exp_pos _).le)).symm
      _ = volume (A ∩ Icc (-2⁻¹ : ℝ) 2⁻¹) := by
          rw [integral_gauss_one, ENNReal.ofReal_one, inter_eq_self_of_subset_right hsub,
            Real.volume_Icc]; norm_num
  · have hsub : A ⊆ Icc (-2⁻¹ : ℝ) 2⁻¹ := fun x hx => abs_le.mp <| by
      by_contra! hgt
      have h0 : (0 : ℝ) ∈ A := by
        simpa using hAc hx (hAs _ hx) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
      have habs : |x| ∈ A := by rcases abs_choice x with h | h <;> rw [h]; exacts [hx, hAs _ hx]
      have hpos : 0 < |x| := by linarith
      have := hAc habs h0 (a := 2⁻¹ / |x|) (b := 1 - 2⁻¹ / |x|) (by positivity)
        (by rw [sub_nonneg, div_le_one hpos]; exact hgt.le) (by ring)
      simp [smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this; exact hc this
    refine (lintegral_mono fun x => ENNReal.ofReal_le_one.mpr <|
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])).trans_eq ?_
    rw [setLIntegral_one, inter_eq_self_of_subset_left hsub]

private def cubeHalf (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, |x i| ≤ 2⁻¹}

private lemma meas_cubeHalf {ι : Type*} [Countable ι] : MeasurableSet (cubeHalf ι) := by
  rw [show cubeHalf ι = ⋂ i, {x | |x i| ≤ 2⁻¹} by ext; simp [cubeHalf]]
  exact MeasurableSet.iInter fun _ => measurableSet_le (by fun_prop) measurable_const

private lemma conv_cubeHalf (ι : Type*) : Convex ℝ (cubeHalf ι) := fun x hx y hy a b ha hb hab i => by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact (abs_add_le _ _).trans <| by
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    exact (add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hb)).trans_eq (by linarith)

private theorem hasSliceBound_cubePi : ∀ n : ℕ,
    HasSliceBound (volume : Measure (Fin n → ℝ))
      (fun x => ENNReal.ofReal (Real.exp (-π * ∑ i, (x i) ^ 2))) (cubeHalf (Fin n))
  | 0 => fun A _ _ _ => by
      rw [show cubeHalf (Fin 0) = univ by ext; simp [cubeHalf], inter_univ]
      exact (lintegral_mono fun _ => by simp).trans_eq (setLIntegral_one A)
  | n + 1 => by
      let g1 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-π * x ^ 2))
      let gn : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-π * ∑ i, (x i) ^ 2))
      have hg1 : Measurable g1 := by unfold g1; fun_prop
      have hgn : Measurable gn := by unfold gn; fun_prop
      have hlc1 : LogConcave g1 := fun a b ha hb hab x y => by
        dsimp only [g1]
        have hkv : (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
          nlinarith [sq_nonneg (x - y), mul_nonneg ha.le hb.le]
        rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
        simp only [smul_eq_mul]
        nlinarith [Real.pi_pos, hkv]
      have : (volume : Measure (Fin n → ℝ)).IsNegInvariant := by rw [volume_pi]; infer_instance
      have hprod : HasSliceBound (volume : Measure (ℝ × (Fin n → ℝ)))
          (fun p => g1 p.1 * gn p.2) (Icc (-2⁻¹) 2⁻¹ ×ˢ cubeHalf (Fin n)) := by
        rw [Measure.volume_eq_prod]
        set μ := (volume : Measure ℝ)
        set ν := (volume : Measure (Fin n → ℝ))
        set R := cubeHalf (Fin n)
        have hRm : MeasurableSet R := meas_cubeHalf
        intro A hA hAc hAs
        set K : ℝ → Set ℝ := fun s => {y | ENNReal.ofReal s < g1 y}
        have hKm (s : ℝ) : MeasurableSet (K s) := measurableSet_lt measurable_const hg1
        have hAsecE (z : Fin n → ℝ) : MeasurableSet {y | (y, z) ∈ A} :=
          hA.preimage measurable_prodMk_right
        have hAsecF (y : ℝ) : MeasurableSet {z | (y, z) ∈ A} :=
          hA.preimage measurable_prodMk_left
        set f : ℝ → ℝ≥0∞ := fun y => (ν.restrict R) {z | (y, z) ∈ A}
        set θ : ℝ → (Fin n → ℝ) → ℝ≥0∞ := fun s z => (μ.restrict (K s)) {y | (y, z) ∈ A}
        have hΘm : Measurable fun p : (Fin n → ℝ) × ℝ => θ p.2 p.1 := by
          have heq : (fun p : (Fin n → ℝ) × ℝ => θ p.2 p.1) = fun p => μ ((fun y => (y, p)) ⁻¹'
              {q : ℝ × ((Fin n → ℝ) × ℝ) | ENNReal.ofReal q.2.2 < g1 q.1 ∧ (q.1, q.2.1) ∈ A}) := by
            ext p; simp only [θ, Measure.restrict_apply' (hKm p.2)]; congr 1; ext; exact and_comm
          rw [heq]; exact measurable_measure_prodMk_right <|
            (measurableSet_lt (ENNReal.measurable_ofReal.comp (measurable_snd.comp measurable_snd))
              (hg1.comp measurable_fst)).inter (hA.preimage (by fun_prop))
        have hfe (y : ℝ) : f (-y) = f y := by
          simp only [f, Measure.restrict_apply' hRm]
          exact measure_symm ν fun z => and_congr
            ⟨fun h => by simpa using hAs (-y, -z) h, fun h => by simpa using hAs (y, z) h⟩
            (by simp [R, cubeHalf])
        have hθe (s : ℝ) (z : Fin n → ℝ) : θ s (-z) = θ s z := by
          simp only [θ, Measure.restrict_apply' (hKm s)]
          exact measure_symm μ fun y => and_congr
            ⟨fun h => by simpa using hAs (-y, -z) h, fun h => by simpa using hAs (y, z) h⟩
            (by simp [K, g1])
        have hflc : LogConcave f := by
          have : f = fun y => ν {z | (y, z) ∈ A ∩ univ ×ˢ R} := by
            funext y; simp only [f, Measure.restrict_apply' hRm]; congr 1; ext; simp
          rw [this]
          exact logConcave_section (hasPL_pi n) (hA.inter (MeasurableSet.univ.prod hRm))
            (hAc.inter (convex_univ.prod (conv_cubeHalf _)))
        have hθlc (s : ℝ) : LogConcave (θ s) := by
          have : θ s = fun z => μ {y | (z, y) ∈ Prod.swap ⁻¹' A ∩ univ ×ˢ K s} := by
            funext z; simp only [θ, Measure.restrict_apply' (hKm s)]; congr 1; ext; simp
          rw [this]
          exact logConcave_section (fun _ _ => prekopaLeindler_real)
            ((hA.preimage measurable_swap).inter (MeasurableSet.univ.prod (hKm s)))
            ((hAc.linear_preimage (LinearEquiv.prodComm ℝ _ _).toLinearMap).inter
              (convex_univ.prod (hlc1.convex_lt _)))
        have hlayer (S : Set ℝ) : ∫⁻ y in S, g1 y ∂μ = ∫⁻ s in Ioi (0 : ℝ), (μ.restrict (K s)) S := by
          rw [lintegral_eq_meas_lt (μ.restrict S) hg1]
          exact lintegral_congr fun s => by
            rw [Measure.restrict_apply (hKm s), Measure.restrict_apply' (hKm s), inter_comm]
        have hW1 : Measurable (A.indicator fun p : ℝ × (Fin n → ℝ) => g1 p.1 * gn p.2) :=
          ((hg1.comp measurable_fst).mul (hgn.comp measurable_snd)).indicator hA
        have hW2 : Measurable (A.indicator fun p : ℝ × (Fin n → ℝ) => g1 p.1) :=
          (hg1.comp measurable_fst).indicator hA
        calc ∫⁻ x in A, g1 x.1 * gn x.2 ∂(μ.prod ν)
            = ∫⁻ z, (∫⁻ y in {y | (y, z) ∈ A}, g1 y ∂μ) * gn z ∂ν := by
              rw [← lintegral_indicator hA, lintegral_prod _ hW1.aemeasurable,
                lintegral_lintegral_swap
                  (f := fun y z => A.indicator (fun p : ℝ × _ => g1 p.1 * gn p.2) (y, z))
                  hW1.aemeasurable]
              refine lintegral_congr fun z => ?_
              rw [show (fun y => A.indicator (fun p : ℝ × _ => g1 p.1 * gn p.2) (y, z))
                  = {y | (y, z) ∈ A}.indicator (fun y => g1 y * gn z) from rfl,
                lintegral_indicator (hAsecE z), lintegral_mul_const _ hg1]
          _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ z, θ s z * gn z ∂ν := by
              simp_rw [hlayer]
              rw [← lintegral_lintegral_swap
                (f := fun z s => θ s z * gn z) (hΘm.mul (hgn.comp measurable_fst)).aemeasurable]
              exact lintegral_congr fun z =>
                (lintegral_mul_const _ (hΘm.comp measurable_prodMk_left)).symm
          _ ≤ ∫⁻ s in Ioi (0 : ℝ), ∫⁻ z in R, θ s z ∂ν :=
              lintegral_mono fun s => (hasSliceBound_cubePi n).lintegral_le hgn
                (measurable_measure_prodMk_right hA) (hθe s) (hθlc s)
          _ = ∫⁻ z in R, ∫⁻ y in {y | (y, z) ∈ A}, g1 y ∂μ ∂ν := by
              rw [lintegral_lintegral_swap (f := fun s z => θ s z)
                (hΘm.comp measurable_swap).aemeasurable]
              exact lintegral_congr fun _ => (hlayer _).symm
          _ = ∫⁻ y, f y * g1 y ∂μ := by
              simp_rw [← lintegral_indicator (hAsecE _)]
              rw [show (fun z => ∫⁻ y, {y | (y, z) ∈ A}.indicator g1 y ∂μ) =
                fun z => ∫⁻ y, A.indicator (fun p : ℝ × _ => g1 p.1) (y, z) ∂μ from rfl,
                lintegral_lintegral_swap (μ := ν.restrict R) (ν := μ)
                  (f := fun z y => A.indicator (fun p : ℝ × _ => g1 p.1) (y, z))
                  (hW2.comp measurable_swap).aemeasurable]
              refine lintegral_congr fun y => ?_
              rw [show (fun z => A.indicator (fun p : ℝ × _ => g1 p.1) (y, z)) =
                {z | (y, z) ∈ A}.indicator fun _ => g1 y from rfl,
                lintegral_indicator (hAsecF y), setLIntegral_const, mul_comm]
          _ ≤ ∫⁻ y in Icc (-2⁻¹) 2⁻¹, f y ∂μ :=
              hasSliceBound_real.lintegral_le hg1 (measurable_measure_prodMk_left hA) hfe hflc
          _ = (μ.prod ν) (A ∩ (Icc (-2⁻¹) 2⁻¹ ×ˢ R)) := by
              rw [← Measure.restrict_apply hA, ← Measure.prod_restrict, Measure.prod_apply hA]; rfl
      convert HasSliceBound.of_mp (consEquiv n) (mp_consEquiv n) (meas_consEquiv_symm n)
        ((hg1.comp measurable_fst).mul (hgn.comp measurable_snd))
        (measurableSet_Icc.prod meas_cubeHalf) hprod using 1
      · funext x
        change ENNReal.ofReal (Real.exp (-π * ∑ i, (x i) ^ 2)) =
          g1 (consEquiv n x).1 * gn (consEquiv n x).2
        dsimp only [g1, gn]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Fin.sum_univ_succ]
        congr 2; simp [consEquiv, Fin.consLinearEquiv, Fin.tail]; ring
      · ext x; simp only [cubeHalf, mem_preimage, mem_prod, mem_Icc, mem_ofPred_eq,
          Fin.forall_fin_succ, ← abs_le, consEquiv, Fin.consLinearEquiv]; rfl

private noncomputable def gaussDensity {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-π * ‖x‖ ^ 2))

private theorem lintegral_gaussDensity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫⁻ x : E, gaussDensity x = 1 := by
  let b := stdOrthonormalBasis ℝ E
  set ι := Fin (Module.finrank ℝ E)
  have hm2 : Measurable fun y : ι → ℝ => ENNReal.ofReal (Real.exp (-π * ∑ i, (y i) ^ 2)) := by
    fun_prop
  calc ∫⁻ x : E, gaussDensity x
      = ∫⁻ x : EuclideanSpace ℝ ι, gaussDensity x := by
        rw [← b.measurePreserving_repr.lintegral_comp (by unfold gaussDensity; fun_prop)]
        exact lintegral_congr fun x => by simp [gaussDensity, b.repr.norm_map]
    _ = ∫⁻ y : ι → ℝ, ENNReal.ofReal (Real.exp (-π * ∑ i, (y i) ^ 2)) := by
        rw [← (PiLp.volume_preserving_ofLp ι).lintegral_comp hm2]
        exact lintegral_congr fun x => by
          rw [gaussDensity, EuclideanSpace.norm_eq,
            Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]; simp
    _ = ∫⁻ y : ι → ℝ, ENNReal.ofReal (∏ i, Real.exp (-π * (y i) ^ 2)) :=
        lintegral_congr fun _ => by rw [← Real.exp_sum, Finset.mul_sum]
    _ = ENNReal.ofReal (∫ y : ι → ℝ, ∏ i, Real.exp (-π * (y i) ^ 2)) :=
        (ofReal_integral_eq_lintegral_ofReal
          (.fintype_prod fun _ => integrable_exp_neg_mul_sq Real.pi_pos)
          (.of_forall fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)).symm
    _ = 1 := by
        rw [integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-π * t ^ 2)),
          integral_gauss_one, one_pow, ENNReal.ofReal_one]

/-- Vaaler's cube-slicing theorem: every central slice of `[-1, 1]^ι` by a subspace `V`
has volume at least `2 ^ dim V`. -/
theorem two_pow_finrank_le_volume_inter_cube {ι : Type*} [Fintype ι]
    (V : Submodule ℝ (EuclideanSpace ℝ ι)) :
    (2 : ℝ≥0∞) ^ Module.finrank ℝ V ≤
      volume {y : V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1} := by
  let σ := Fintype.equivFin ι
  let e₀ : EuclideanSpace ℝ ι ≃ₗ[ℝ] (Fin (Fintype.card ι) → ℝ) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toLinearEquiv ≪≫ₗ WithLp.linearEquiv 2 ℝ _
  have hMP₀ : MeasurePreserving e₀ volume volume :=
    (PiLp.volume_preserving_ofLp _).comp
      (LinearIsometryEquiv.measurePreserving (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ))
  set Q : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' cubeHalf ι
  have hQm : MeasurableSet Q := meas_cubeHalf.preimage (PiLp.continuous_ofLp _ _).measurable
  have hQc : Convex ℝ Q := (conv_cubeHalf ι).linear_preimage (WithLp.linearEquiv 2 ℝ _).toLinearMap
  have hQ : HasSliceBound (volume : Measure (EuclideanSpace ℝ ι)) gaussDensity Q := by
    convert HasSliceBound.of_mp e₀ hMP₀
      (LinearMap.continuous_of_finiteDimensional e₀.symm.toLinearMap).measurable
      (by fun_prop) meas_cubeHalf (hasSliceBound_cubePi (Fintype.card ι)) using 1
    · funext x; rw [gaussDensity, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      congr 2
      have hsum : ∑ i : Fin (Fintype.card ι), (e₀ x i) ^ 2 = ∑ j : ι, (x j) ^ 2 :=
        Fintype.sum_equiv σ.symm _ _ fun i => by simp [e₀]
      rw [hsum]; simp
    · ext x; exact ⟨fun h i => by simpa [e₀, Q, cubeHalf] using h (σ.symm i),
        fun h j => by simpa [e₀, Q, cubeHalf] using h (σ j)⟩
  set W := (Vᗮ : Submodule ℝ (EuclideanSpace ℝ ι))
  let e : EuclideanSpace ℝ ι ≃ₗ[ℝ] (V × W) :=
    V.orthogonalDecomposition.toLinearEquiv ≪≫ₗ WithLp.linearEquiv 2 ℝ (V × W)
  have hMP : MeasurePreserving e volume ((volume : Measure V).prod (volume : Measure W)) := by
    rw [← Measure.volume_eq_prod]
    exact (WithLp.volume_preserving_ofLp (V : Type _) (W : Type _)).comp
      (LinearIsometryEquiv.measurePreserving V.orthogonalDecomposition)
  have hsymm : Measurable e.symm :=
    (LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap).measurable
  have hQ' := HasSliceBound.of_mp e.symm
    (hMP.symm ⟨e.toEquiv, hMP.measurable, hsymm⟩) hMP.measurable
    (by unfold gaussDensity; fun_prop) hQm hQ
  set QQ : Set (V × W) := e.symm ⁻¹' Q
  have hQQm : MeasurableSet QQ := hsymm hQm
  set f : W → ℝ≥0∞ := fun z => (volume : Measure V) {y : V | (y, z) ∈ QQ}
  have hflc : LogConcave f :=
    logConcave_section hasPL_ips (hQQm.preimage measurable_swap)
      ((hQc.linear_preimage e.symm.toLinearMap).linear_preimage
        (LinearEquiv.prodComm ℝ _ _).toLinearMap)
  have hfle (z : W) : f z ≤ f 0 := by
    have hfe : f (-z) = f z := measure_symm _ fun y => by
      have hneg (u : V) (v : W) : e.symm (-u, v) = -e.symm (u, -v) := by
        rw [← map_neg]; congr 1; simp
      change (-y, -z) ∈ QQ ↔ (y, z) ∈ QQ
      simp only [QQ, mem_preimage, Q, cubeHalf, mem_ofPred_eq, hneg]
      exact forall_congr' fun i => by simp
    have h := hflc 2⁻¹ 2⁻¹ (by norm_num) (by norm_num) (by norm_num) z (-z)
    rwa [hfe, show (2⁻¹ : ℝ) • z + (2⁻¹ : ℝ) • (-z) = 0 by module,
      ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
      show (2⁻¹ : ℝ) + 2⁻¹ = 1 by norm_num, ENNReal.rpow_one] at h
  have hf0 : f 0 = volume {y : V | (y : EuclideanSpace ℝ ι) ∈ Q} := by
    dsimp only [f]; congr 1; ext y; simp [QQ, e]
  have key (ε : ℝ) (hε : 0 < ε) : ENNReal.ofReal (Real.exp (-π * ε ^ 2)) ≤ f 0 := by
    set B := Metric.closedBall (0 : W) ε
    have hBm : MeasurableSet B := measurableSet_closedBall
    have hApp := hQ' (univ ×ˢ B) (MeasurableSet.univ.prod hBm)
      (convex_univ.prod (convex_closedBall _ _)) fun q hq => ⟨trivial, by simpa [B] using hq.2⟩
    have hdens (q : V × W) : gaussDensity (e.symm q) = gaussDensity q.1 * gaussDensity q.2 := by
      have hn : ‖e.symm q‖ ^ 2 = ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
        change ‖V.orthogonalDecomposition.symm (WithLp.toLp 2 q)‖ ^ 2 = _
        rw [V.orthogonalDecomposition.symm.norm_map, WithLp.prod_norm_sq_eq_of_L2]; simp
      rw [gaussDensity, gaussDensity, gaussDensity, hn, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]; congr 2; ring
    have hlhs : ∫⁻ q in univ ×ˢ B, gaussDensity (e.symm q)
        ∂((volume : Measure V).prod (volume : Measure W)) = ∫⁻ z in B, gaussDensity z := by
      have hgV : Measurable (gaussDensity : V → ℝ≥0∞) := by unfold gaussDensity; fun_prop
      have hgW : Measurable (gaussDensity : W → ℝ≥0∞) := by unfold gaussDensity; fun_prop
      rw [← Measure.prod_restrict, Measure.restrict_univ, lintegral_congr hdens,
        lintegral_prod_mul hgV.aemeasurable hgW.aemeasurable, lintegral_gaussDensity, one_mul]
    have hlow : ENNReal.ofReal (Real.exp (-π * ε ^ 2)) * volume B ≤ ∫⁻ z in B, gaussDensity z := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono' hBm fun z hz => ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr ?_
      have hzn : ‖z‖ ≤ ε := by simpa [B] using hz
      have hsq : ‖z‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg z]
      nlinarith [Real.pi_pos, hsq]
    have hrhs : ((volume : Measure V).prod (volume : Measure W)) ((univ ×ˢ B) ∩ QQ)
        ≤ f 0 * volume B := by
      rw [Measure.prod_apply_symm ((MeasurableSet.univ.prod hBm).inter hQQm),
        ← setLIntegral_const, ← lintegral_indicator hBm]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ B
      · rw [indicator_of_mem hz]
        exact (le_of_eq (by dsimp only [f]; congr 1; ext y; simp [hz])).trans (hfle z)
      · simp [hz, show (fun y => (y, z)) ⁻¹' ((univ ×ˢ B) ∩ QQ) = ∅ by ext y; simp [hz]]
    have hcomb := hlow.trans (hlhs ▸ hApp.trans hrhs)
    rw [mul_comm, mul_comm (f 0)] at hcomb
    exact (ENNReal.mul_le_mul_iff_right (Metric.measure_closedBall_pos volume 0 hε).ne'
      measure_closedBall_lt_top.ne).mp hcomb
  have h1 : 1 ≤ volume {y : V | (y : EuclideanSpace ℝ ι) ∈ Q} := by
    rw [← hf0]
    have hc : Continuous fun ε : ℝ => ENNReal.ofReal (Real.exp (-π * ε ^ 2)) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
    have hcont : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (-π * ε ^ 2)))
        (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact le_of_tendsto hcont (Filter.eventually_of_mem self_mem_nhdsWithin key)
  rw [show {y : V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1} =
      (2 : ℝ) • {y : V | (y : EuclideanSpace ℝ ι) ∈ Q} by
    ext y; rw [Set.mem_smul_set_iff_inv_smul_mem₀ two_ne_zero]
    refine forall_congr' fun i => ?_
    have h : (((2 : ℝ)⁻¹ • y : V) : EuclideanSpace ℝ ι) i = 2⁻¹ * (y : EuclideanSpace ℝ ι) i := by
      simp
    change _ ↔ |(((2 : ℝ)⁻¹ • y : V) : EuclideanSpace ℝ ι) i| ≤ 2⁻¹
    rw [h, abs_mul, show |(2 : ℝ)⁻¹| = 2⁻¹ by norm_num]
    exact ⟨fun hi => by linarith, fun hi => by linarith⟩, Measure.addHaar_smul]
  calc (2 : ℝ≥0∞) ^ Module.finrank ℝ V
      = ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ (V : Type _)| * 1 := by
        rw [mul_one, abs_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two]; norm_num
    _ ≤ _ := by gcongr

end
