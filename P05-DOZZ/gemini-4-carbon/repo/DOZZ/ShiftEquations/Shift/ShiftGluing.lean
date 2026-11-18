/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Meromorphic continuation by a shift equation
-/

@[expose] public section

noncomputable section
open Filter Topology Set

namespace DOZZ.Proofs

namespace ShiftGluing

/-- Local meromorphic identity theorem: two functions meromorphic on a preconnected set which
agree frequently near one point of the set agree near every point of the set (punctured). -/
theorem meromorphicOn_eventuallyEq_of_frequently {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsPreconnected U)
    {x₀ y : ℂ} (hx₀ : x₀ ∈ U) (hy : y ∈ U) (hfreq : ∃ᶠ z in 𝓝[≠] x₀, f z = g z) :
    f =ᶠ[𝓝[≠] y] g := by
  have hsub := hf.sub hg
  have h0 : (f - g) =ᶠ[𝓝[≠] x₀] 0 :=
    ((hsub x₀ hx₀).frequently_zero_iff_eventuallyEq_zero).mp (hfreq.mono fun _ hz => by simp [hz])
  exact (meromorphicOrderAt_eq_top_iff.mp
    (hsub.meromorphicOrderAt_eq_top_of_isPreconnected hU hx₀ hy (meromorphicOrderAt_eq_top_iff.mpr h0))).mono
    fun _ hz => sub_eq_zero.mp hz

/-- Punctured germs are transported by the translation `w ↦ w - c`. -/
theorem eventually_comp_sub {p : ℂ → Prop} {z : ℂ} (c : ℂ)
    (h : ∀ᶠ w in 𝓝[≠] (z - c), p w) : ∀ᶠ w in 𝓝[≠] z, p (w - c) :=
  (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_sub_right c).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun _ hw => by simpa using hw)).eventually h

/-- Punctured germs are transported by the translation `w ↦ w + c`. -/
theorem eventually_comp_add {p : ℂ → Prop} {z : ℂ} (c : ℂ)
    (h : ∀ᶠ w in 𝓝[≠] (z + c), p w) : ∀ᶠ w in 𝓝[≠] z, p (w + c) :=
  (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_id.add continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun _ hw => by simpa using hw)).eventually h

private def sRect (a b h t : ℝ) : Set ℂ := {z : ℂ | a + t < z.re ∧ z.re < b + t ∧ |z.im| < h}





private def sUp (c : ℝ) (m g : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => g
  | k + 1 => fun z => sUp c m g k (z - c) / m z

private def sDown (c : ℝ) (m g : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => g
  | k + 1 => fun z => m (z + c) * sDown c m g k (z + c)

private def sPiece (c : ℝ) (m g : ℂ → ℂ) : ℤ → ℂ → ℂ
  | Int.ofNat k => sUp c m g k
  | Int.negSucc k => sDown c m g (k + 1)


end ShiftGluing

open ShiftGluing

/-- **Meromorphic continuation by a shift equation.** A function holomorphic on an open set `W`
containing a real interval `(a, b)` longer than the step `c`, satisfying the shift equation
`g (x - c) = m x * g x` on a real subinterval, extends to a meromorphic function on a horizontal
strip which agrees with `g` on `(a, b)` and satisfies the shift equation near every point. -/
theorem exists_meromorphicOn_strip_of_shift {c a b d₁ d₂ : ℝ} (hc : 0 < c) (hab : c < b - a)
    (hd₁ : a + c ≤ d₁) (hd : d₁ < d₂) (hd₂ : d₂ ≤ b)
    {W : Set ℂ} (hW : IsOpen W) (hWab : ∀ x : ℝ, a < x → x < b → (x : ℂ) ∈ W)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g W)
    {m : ℂ → ℂ} (hm : MeromorphicOn m Set.univ) (hm0 : ∃ z₀ : ℂ, AnalyticAt ℂ m z₀ ∧ m z₀ ≠ 0)
    (hrel : ∀ x : ℝ, d₁ < x → x < d₂ → g ((x : ℂ) - c) = m x * g x) :
    ∃ h : ℝ, 0 < h ∧ ∃ G : ℂ → ℂ, MeromorphicOn G (horizontalStrip h) ∧
      (∀ x : ℝ, a < x → x < b → G x = g x) ∧
      ∀ z ∈ horizontalStrip h, ∀ᶠ w in 𝓝[≠] z, G (w - c) = m w * G w := by
  have sPiece_neg_nat (c : ℝ) (m g : ℂ → ℂ) (k : ℕ) : sPiece c m g (-(k : ℤ)) = sDown c m g k := by cases k <;> rfl
  have add_mem_sRect {a b h t t' c : ℝ} {z : ℂ} (hz : z ∈ sRect a b h t) (ht : t' = t + c) : z + (c : ℂ) ∈ sRect a b h t' := by
    obtain ⟨h1, h2, h3⟩ := hz
    exact ⟨by simp; linarith, by simp; linarith, by simpa using h3⟩
  have sub_mem_sRect {a b h t t' c : ℝ} {z : ℂ} (hz : z ∈ sRect a b h t) (ht : t' = t - c) : z - (c : ℂ) ∈ sRect a b h t' := by
    simpa [sub_eq_add_neg] using add_mem_sRect hz (by linarith : t' = t + -c)
  have convex_sRect (a b h t : ℝ) : Convex ℝ (sRect a b h t) := by
    rw [show sRect a b h t = Complex.reCLM ⁻¹' Ioo (a + t) (b + t) ∩ Complex.imCLM ⁻¹' Ioo (-h) h
      by ext; simp [sRect, abs_lt, and_assoc]]
    exact ((convex_Ioo (a + t) (b + t)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioo (-h) h).linear_preimage Complex.imCLM.toLinearMap)
  have isOpen_sRect (a b h t : ℝ) : IsOpen (sRect a b h t) := 
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt Complex.continuous_im.abs continuous_const))
  classical
  have hgan : AnalyticOnNhd ℂ g W := hg.analyticOnNhd hW
  have hm0' (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, m w ≠ 0 := by
    obtain ⟨z₀, han, hne⟩ := hm0
    have h0 : meromorphicOrderAt m z₀ ≠ ⊤ :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm z₀ (mem_univ _))).2
        (eventually_nhdsWithin_of_eventually_nhds (han.continuousAt.eventually_ne hne))
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm z (mem_univ _))).1
      (hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₀) (mem_univ z) h0)
  -- Subinterval `(a', b')` with `c < b' - a' < 2 * c` and rectangle inside `W`
  let L := (c + min (b - a) (2 * c)) / 2
  have hL1 : c < L := by dsimp [L]; linarith [lt_min hab (by linarith : c < 2 * c)]
  have hL2 : L < min (b - a) (2 * c) := by dsimp [L]; linarith [lt_min hab (by linarith : c < 2 * c)]
  let a' := a + (b - a - L) / 2
  let b' := a' + L
  have haa' : a < a' := by dsimp [a']; linarith [min_le_left (b - a) (2 * c)]
  have hb'b : b' < b := by dsimp [b', a']; linarith [min_le_left (b - a) (2 * c)]
  have hlen : c < b' - a' := by dsimp [b']; linarith
  have hlen2 : b' - a' < 2 * c := by dsimp [b']; linarith [min_le_right (b - a) (2 * c)]
  obtain ⟨h, hh, hthick⟩ := (isCompact_Icc.image Complex.continuous_ofReal).exists_thickening_subset_open hW
    (by rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩; exact hWab t (by linarith) (by linarith) :
      ((fun t : ℝ => (t : ℂ)) '' Icc a' b') ⊆ W)
  have hrectW : sRect a' b' h 0 ⊆ W := fun z ⟨h1, h2, h3⟩ => hthick (Metric.mem_thickening_iff.2
    ⟨(z.re : ℂ), ⟨z.re, ⟨by linarith, by linarith⟩, rfl⟩, by
      rw [Complex.dist_eq_re_im]; simpa [Real.sqrt_sq_eq_abs] using h3⟩)
  -- Propagate shift relation to `P = sRect a' b' h 0 ∩ sRect a' b' h c`
  let P := sRect a' b' h 0 ∩ sRect a' b' h c
  have hrelP : ∀ y ∈ P, ∀ᶠ w in 𝓝[≠] y, g (w - c) = m w * g w := by
    let O := W ∩ (fun z : ℂ => z - c) ⁻¹' W
    have hL : MeromorphicOn (fun z : ℂ => g (z - c)) O := fun z hz =>
      ((hgan (z - c) hz.2).comp_of_eq (analyticAt_id.sub analyticAt_const) rfl).meromorphicAt
    have hR : MeromorphicOn (fun z : ℂ => m z * g z) O := fun z hz =>
      (hm z (mem_univ z)).mul (hgan z hz.1).meromorphicAt
    let Seg := (fun t : ℝ => (t : ℂ)) '' Ioo (a + c) b
    have hPO : P ∪ Seg ⊆ O := union_subset
      (fun z hz => ⟨hrectW hz.1, hrectW (sub_mem_sRect hz.2 (by ring))⟩)
      (by rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
          refine ⟨hWab t (by linarith) ht2, ?_⟩
          show ((t : ℂ) - c) ∈ W
          rw [show (t : ℂ) - c = ((t - c : ℝ) : ℂ) by push_cast; ring]
          exact hWab _ (by linarith) (by linarith))
    let x₁ := (a' + c + b') / 2
    have hx₁P : (x₁ : ℂ) ∈ P := ⟨⟨by simp [x₁]; linarith, by simp [x₁]; linarith, by simp [hh]⟩,
      ⟨by simp [x₁]; linarith, by simp [x₁]; linarith, by simp [hh]⟩⟩
    have hconn : IsPreconnected (P ∪ Seg) :=
      ((convex_sRect _ _ _ _).inter (convex_sRect _ _ _ _)).isPreconnected.union (x₁ : ℂ) hx₁P
        ⟨x₁, ⟨by dsimp [x₁]; linarith, by dsimp [x₁]; linarith⟩, rfl⟩
        (isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn)
    let x₀ := (d₁ + d₂) / 2
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun _ ht => by simpa [Complex.ofReal_inj] using ht)
    have hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), g (z - c) = m z * g z :=
      htend.frequently (p := fun z => g (z - c) = m z * g z)
        (eventually_nhdsWithin_of_eventually_nhds
          (Filter.mem_of_superset (Ioo_mem_nhds (by dsimp [x₀]; linarith) (by dsimp [x₀]; linarith))
            fun t ht => hrel t ht.1 ht.2)).frequently
    intro y hy
    exact meromorphicOn_eventuallyEq_of_frequently (hL.mono_set hPO) (hR.mono_set hPO) hconn
      (Or.inr ⟨x₀, ⟨by dsimp [x₀]; linarith, by dsimp [x₀]; linarith⟩, rfl⟩) (Or.inl hy) hfreq
  -- Meromorphy and compatibility of `sPiece`
  have hg0 : MeromorphicOn g (sRect a' b' h 0) := hgan.meromorphicOn.mono_set hrectW
  have hm_piece (n : ℤ) : MeromorphicOn (sPiece c m g n) (sRect a' b' h (n * c)) := by
    have hm_up (k : ℕ) : MeromorphicOn (sUp c m g k) (sRect a' b' h (k * c)) := by
      induction k with
      | zero => simpa [sUp] using hg0
      | succ k ih =>
        exact fun z hz => (meromorphicAt_fun_comp_sub_const_iff_meromorphicAt.2
          (ih _ (sub_mem_sRect hz (by push_cast; ring)))).div (hm z (mem_univ z))
    have hm_dn (k : ℕ) : MeromorphicOn (sDown c m g k) (sRect a' b' h (-(k * c))) := by
      induction k with
      | zero => simpa [sDown] using hg0
      | succ k ih =>
        exact fun z hz => (meromorphicAt_fun_comp_add_const_iff_meromorphicAt.2 (hm _ (mem_univ _))).mul
          (meromorphicAt_fun_comp_add_const_iff_meromorphicAt.2 (ih _ (add_mem_sRect hz (by push_cast; ring))))
    cases n with
    | ofNat k =>
      rw [show ((Int.ofNat k : ℤ) : ℝ) * c = k * c by simp]
      exact hm_up k
    | negSucc k =>
      rw [show ((Int.negSucc k : ℤ) : ℝ) * c = -(((k + 1 : ℕ) : ℝ) * c) by rw [Int.cast_negSucc]; push_cast; ring]
      exact hm_dn (k + 1)
  have hadj (n : ℤ) {z : ℂ} (hz₁ : z ∈ sRect a' b' h (n * c)) (hz₂ : z ∈ sRect a' b' h ((n + 1 : ℤ) * c)) :
      ∀ᶠ w in 𝓝[≠] z, sPiece c m g n w = sPiece c m g (n + 1) w := by
    have hup (k : ℕ) : ∀ z ∈ sRect a' b' h (k * c), z ∈ sRect a' b' h ((k + 1) * c) →
        ∀ᶠ w in 𝓝[≠] z, sUp c m g (k + 1) w = sUp c m g k w := by
      induction k with
      | zero =>
        intro z h1 h2
        filter_upwards [hrelP z ⟨by simpa using h1, by simpa using h2⟩, hm0' z] with w hw hmw
        show g (w - c) / m w = g w; rw [hw, mul_div_cancel_left₀ _ hmw]
      | succ k ih =>
        intro z h1 h2
        filter_upwards [eventually_comp_sub (p := fun w => sUp c m g (k + 1) w = sUp c m g k w) c
          (ih _ (sub_mem_sRect h1 (by push_cast; ring)) (sub_mem_sRect h2 (by push_cast; ring)))] with w hw
        show sUp c m g (k + 1) (w - c) / m w = sUp c m g k (w - c) / m w; rw [hw]
    have hdn (k : ℕ) : ∀ z ∈ sRect a' b' h (-((k + 1) * c)), z ∈ sRect a' b' h (-(k * c)) →
        ∀ᶠ w in 𝓝[≠] z, sDown c m g (k + 1) w = sDown c m g k w := by
      induction k with
      | zero =>
        intro z h1 h2
        filter_upwards [eventually_comp_add (p := fun w => g (w - c) = m w * g w) c
          (hrelP _ ⟨add_mem_sRect h1 (by push_cast; ring), add_mem_sRect h2 (by push_cast; ring)⟩)] with w hw
        show m (w + c) * g (w + c) = g w; rw [← hw, add_sub_cancel_right]
      | succ k ih =>
        intro z h1 h2
        filter_upwards [eventually_comp_add (p := fun w => sDown c m g (k + 1) w = sDown c m g k w) c
          (ih _ (add_mem_sRect h1 (by push_cast; ring)) (add_mem_sRect h2 (by push_cast; ring)))] with w hw
        show m (w + c) * sDown c m g (k + 1) (w + c) = m (w + c) * sDown c m g k (w + c); rw [hw]
    cases n with
    | ofNat k =>
      exact (hup k z (by simpa using hz₁) (by simpa [add_mul] using hz₂)).mono fun _ hw => hw.symm
    | negSucc k =>
      rw [show (Int.negSucc k : ℤ) + 1 = -(k : ℤ) by omega, sPiece_neg_nat]
      exact hdn k z (by rw [Int.cast_negSucc] at hz₁; convert hz₁ using 2; push_cast; ring)
        (by rw [show (Int.negSucc k : ℤ) + 1 = -(k : ℤ) by omega] at hz₂; convert hz₂ using 2; push_cast; ring)
  have hcov : (⋃ n : ℤ, sRect a' b' h (n * c)) = horizontalStrip h := by
    ext z; simp only [mem_iUnion]; constructor
    · rintro ⟨_, _, _, hz⟩; exact hz
    · intro hz
      refine ⟨⌊(z.re - b') / c⌋ + 1, ?_, ?_, hz⟩
      · have := (le_div_iff₀ hc).1 (Int.floor_le ((z.re - b') / c)); push_cast; nlinarith
      · have := (div_lt_iff₀ hc).1 (Int.lt_floor_add_one ((z.re - b') / c)); push_cast; nlinarith
  obtain ⟨F, hF, hpiece, -⟩ := exists_meromorphicOn_strip_gluing h hh
    (fun n : ℤ => sRect a' b' h (n * c)) (fun _ => isOpen_sRect _ _ _ _) hcov (sPiece c m g) hm_piece
    fun i j z hi hj => by
      wlog hij : i ≤ j generalizing i j
      · exact (this j i hj hi (le_of_not_ge hij)).mono fun _ hw => hw.symm
      have : j ≤ i + 1 := by
        by_contra hc'
        have : (i : ℝ) + 2 ≤ j := mod_cast (by omega : i + 2 ≤ j)
        nlinarith [hi.2.1, hj.1, mul_nonneg (by linarith : (0 : ℝ) ≤ j - i - 2) hc.le]
      rcases (by omega : j = i ∨ j = i + 1) with rfl | rfl
      · exact Eventually.of_forall fun _ => rfl
      · exact hadj i hi hj
  have hFrel : ∀ z ∈ horizontalStrip h, ∀ᶠ w in 𝓝[≠] z, F (w - c) = m w * F w := fun z hz => by
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov.symm ▸ hz)
    filter_upwards [hpiece n z hn,
      eventually_comp_sub c (hpiece (n - 1) (z - c) (sub_mem_sRect hn (by push_cast; ring))), hm0' z] with w h1 h2 hmw
    rw [h2, h1]
    cases n with
    | ofNat k =>
      cases k with
      | zero => show m (w - c + c) * g (w - c + c) = m w * g w; rw [sub_add_cancel]
      | succ k =>
        have e : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
        change sPiece c m g (((k + 1 : ℕ) : ℤ) - 1) (w - c) = _
        rw [e]; show sUp c m g k (w - c) = m w * (sUp c m g k (w - c) / m w)
        rw [mul_div_cancel₀ _ hmw]
    | negSucc k =>
      rw [show (Int.negSucc k : ℤ) - 1 = -((k + 2 : ℕ) : ℤ) by omega, sPiece_neg_nat]
      show m (w - c + c) * sDown c m g (k + 1) (w - c + c) = m w * sDown c m g (k + 1) w
      rw [sub_add_cancel]
  -- Override on real segment `(a, b)`
  have hFseg : ∀ x : ℝ, a < x → x < b → F =ᶠ[𝓝[≠] (x : ℂ)] g := fun x hx1 hx2 => by
    let Seg := (fun t : ℝ => (t : ℂ)) '' Ioo a b
    have hx₂R : (((a' + b') / 2 : ℝ) : ℂ) ∈ sRect a' b' h 0 :=
      ⟨by simp; linarith, by simp; linarith, by simp [hh]⟩
    exact meromorphicOn_eventuallyEq_of_frequently
      (hF.mono_set (by rintro _ ⟨_, _, rfl⟩; simpa [horizontalStrip] using hh : Seg ⊆ _))
      (hgan.meromorphicOn.mono_set (by rintro _ ⟨t, ht, rfl⟩; exact hWab t ht.1 ht.2 : Seg ⊆ _))
      (isPreconnected_Ioo.image _ Complex.continuous_ofReal.continuousOn)
      ⟨(a' + b') / 2, ⟨by linarith, by linarith⟩, rfl⟩ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      (hpiece 0 _ (by simpa using hx₂R)).frequently
  let G (z : ℂ) := if z.im = 0 ∧ a < z.re ∧ z.re < b then g z else F z
  have hGF : ∀ z ∈ horizontalStrip h, G =ᶠ[𝓝[≠] z] F := fun z hz => by
    filter_upwards [(hF z hz).eventually_analyticAt] with w hw
    dsimp [G]
    split_ifs with hcond
    · obtain ⟨him, hwa, hwb⟩ := hcond
      have hwe : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [him])
      have hFgw : F =ᶠ[𝓝[≠] w] g := hwe ▸ hFseg w.re hwa hwb
      have hcF : Tendsto F (𝓝[≠] w) (𝓝 (F w)) := hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hcg : Tendsto g (𝓝[≠] w) (𝓝 (g w)) :=
        (hwe ▸ (hgan _ (hWab w.re hwa hwb)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique hcg (hcF.congr' hFgw)
    · rfl
  refine ⟨h, hh, G, ?_, ?_, ?_⟩
  · exact fun z hz => (hF z hz).congr (hGF z hz).symm
  · exact fun x hx1 hx2 => by simp [G, hx1, hx2]
  · intro z hz
    have hzc : z - (c : ℂ) ∈ horizontalStrip h := by simpa [horizontalStrip] using hz
    filter_upwards [hGF z hz, eventually_comp_sub c (hGF (z - c) hzc), hFrel z hz] with w h1 h2 h3
    rw [h2, h1, h3]

end DOZZ.Proofs

end
