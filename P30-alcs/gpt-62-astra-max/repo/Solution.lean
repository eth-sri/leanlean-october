module

public import ALCS.Background.Lp
public import ALCS.Background.Semigroup
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Zero-class property by a sign flip

Write `κ(t) = ‖Φ t‖`. Prepending silence makes `κ` monotone. If its infimum on
positive times were `6d > 0`, all gains on a short interval `[0,H]` would be
less than `7d`. Set `b = H/2`. At times `tᵢ` tending to zero take unit-ball
inputs `uᵢ` with states `xᵢ = Φ(tᵢ) uᵢ` of norm greater than `5d`.

Plant each pulse just before `b`, with a free evolution gap small enough that
its state `yᵢ` at `b` still satisfies `‖yᵢ + yᵢ + xᵢ‖ > 15d`. After thinning,
the pulses `vᵢ` have disjoint supports. Their union `f` and each sign flip
`vᵢ + vᵢ - f` are all in the unit ball. Put `Y = Φ(b) f`. The flipped input
bounds `‖yᵢ + yᵢ - Y‖` by `7d`; playing `f` followed by `uᵢ` bounds
`‖T(tᵢ)Y + xᵢ‖` by `7d`. But `dist (T(tᵢ)Y) Y < d` for large `i`, contradicting
the triangle inequality. Only the **single state** `Y` needs to move little
at times `tᵢ`; no uniform continuity on a sequence of states is needed.
-/

public section
open MeasureTheory Filter Topology Set Function

namespace PalomarALCS
open scoped ENNReal Control

private lemma small_times {s : ℝ} (hs : 0 < s) : ∃ᶠ r in 𝓝₊, r ∈ Ioo 0 s :=
  (Filter.Eventually.frequently (Ioo_mem_nhdsGT hs)).filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)

variable {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace U]
  (T : ℝ → X →L[𝕜] X) (Φ : ℝ → L∞(U) →L[𝕜] X)
  (id : T 0 = ContinuousLinearMap.id 𝕜 X)
  (add : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = (T a).comp (T b))
  (cont : ∀ x, Tendsto (fun t => T t x) 𝓝₊ (𝓝 x))
  (join : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ∀ u v w : L∞(U),
    ⇑w =ᵐ[μ₊] (fun s => if s < a then u s else v (s - a)) → Φ (a + b) w = T b (Φ a u) + Φ b v)

section
variable {T Φ}
omit [CompleteSpace X] [CompleteSpace U]
include join

private lemma cat_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {C} (f g : Control U C) :
    Φ (a + b) (f.cat g a) = T b (Φ a f) + Φ b g := by
  apply join _ _ ha hb
  have h := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ici).mp g.mem.coeFn_toLp)
  apply (f.cat g a).mem.coeFn_toLp.trans
  filter_upwards [f.mem.coeFn_toLp, ae_restrict_of_ae h] with t hf hg
  dsimp [Control.cat]; grind

private lemma delay {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {C} (u : Control U C) :
    Φ t (Control.cat 0 u (t - s)) = Φ s u := by
  simpa using cat_eq join (sub_nonneg.mpr hst) hs 0 u

private lemma gain_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : ‖Φ s‖ ≤ ‖Φ t‖ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _); intro u hu
  obtain ⟨u, rfl⟩ := Control.rep u (C := 1) hu.le
  rw [← delay join hs hst u]; apply (Φ t).unit_le_opNorm _ (Control.norm_lp _)

include cont in
/-- Plant a near-extremal pulse just before `H`. There is room for later pulses
because `r` can be chosen strictly positive while barely moving the state. -/
private lemma pulse {H K s : ℝ} (hs : s ∈ Ioo 0 (H / 2))
    (high : K < ‖Φ s‖) :
    ∃ r > 0, ∃ u w : Control U 1, support w ⊆ Ico (H - 2 * s) (H - r) ∧
      3 * K < ‖Φ H w + Φ H w + Φ s u‖ := by
  obtain ⟨u, hu, high⟩ := (Φ s).exists_lt_apply_of_lt_opNorm high
  obtain ⟨u, rfl⟩ := Control.rep u (C := 1) hu.le
  set x := Φ s u
  have big : 3 * K < ‖x + x + x‖ := by
    have := RCLike.norm_nsmul (K := 𝕜) 3 x
    grind [three_nsmul]
  have lim := (((cont x).add (cont x)).add_const x).norm.eventually_const_lt big
  obtain ⟨r, ⟨hr, hrs⟩, hm⟩ := ((small_times hs.1).and_eventually lim).exists
  refine ⟨r, hr, u, Control.cat 0 (u.cat 0 s) (H - (s + r)), fun t ht => ?_, ?_⟩
  · simp [Control.cat] at ht; grind
  · rw [delay join (add_nonneg hs.1.le hr.le) (by linarith [hs.2]), cat_eq join hs.1.le hr.le]
    simpa using hm

end
include id add cont join

-- The limit argument needs only strong convergence and the join law, but the
-- statement retains the full semigroup hypotheses.
set_option linter.unusedSectionVars false in
/-- Theorem 1.5: the gain tends to zero at the origin. -/
theorem zero_class : Tendsto (fun t => ‖Φ t‖) 𝓝₊ (𝓝 0) := by
  let V := (‖Φ ·‖) '' Ioi 0
  have glb := isGLB_csInf (s := V) (nonempty_Ioi.image _) ⟨0, by simp [V, lowerBounds]⟩
  have smallGain {c} (hc : sInf V < c) : ∀ᶠ t in 𝓝₊, ‖Φ t‖ < c := by
    obtain ⟨_, ⟨H, hH, rfl⟩, h⟩ := (isGLB_lt_iff glb).mp hc
    filter_upwards [Ico_mem_nhdsGE hH] with t ht using (gain_mono join ht.1 ht.2.le).trans_lt h
  suffices z : sInf V ≤ 0 by
    exact Metric.tendsto_nhds.mpr fun ε hε => by simpa using smallGain (z.trans_lt hε)
  by_contra! pos
  set d := sInf V / 6 with eq
  have hd : 0 < d := by linarith
  obtain ⟨H, hH, h⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp
    (smallGain (show sInf V < 7 * d by linarith))
  have bound {s u} (hs : s ∈ Icc 0 H) (hu : ‖u‖ ≤ 1) :=
    ((Φ s).unit_le_opNorm u hu).trans_lt (h hs)
  set b := H / 2 with beq
  have hb := half_pos hH
  obtain ⟨t, lim, ht⟩ := exists_seq_forall_of_frequently (small_times (half_pos hb))
  choose r hr u v hv big using fun n => pulse cont join (K := 5 * d) (ht n)
    (by linarith [glb.1 (mem_image_of_mem _ (ht n).1)])
  -- Extract pairwise disjoint windows accumulating at b.
  obtain ⟨j, hj, sep, -⟩ := hasAntitoneBasis_atTop.subbasis_with_rel fun i =>
    lim.eventually_mem (Ico_mem_nhdsGE (half_pos (hr i)))
  obtain ⟨f, flip⟩ := Control.pack (v ∘ j) fun hi hk => by
    have := hv _ hi; have := hv _ hk
    by_contra ne
    rcases lt_or_gt_of_ne ne with h | h <;> have := sep h <;> grind
  let Y := Φ b f
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp ((cont Y).comp (lim.comp hj.tendsto_atTop)) d hd).exists
  let i := j n
  -- Compare the flipped input at b and the packed input followed by uᵢ.
  have hf := bound (s := b) (by grind) (flip n)
  have hu := bound (s := b + t i) (by have := ht i; grind) ((f.cat (u i) b).norm_lp)
  rw [cat_eq join hb.le (ht i).1.le] at hu
  have B := big i
  rw [← sub_neg_eq_add, ← dist_eq_norm] at B
  grw [dist_triangle4 _ Y (T (t i) Y)] at B
  rw [dist_comm Y] at B
  simp [dist_eq_norm, comp_def] at B hn hf
  linarith

/-- Corollary 1.6. Compare free evolution with the response to a shifted input. -/
theorem continuousOn_Phi (u : L∞(U)) : ContinuousOn (fun t => Φ t u) (Ici 0) := by
  obtain ⟨f, hf⟩ := Control.rep u (C := ‖u‖₊) le_rfl
  apply continuous_approx cont _ (w := fun r => ‖Φ r‖ * ‖u‖)
  · simpa using (zero_class T Φ id add cont join).mul_const ‖u‖
  intro a ha r hr
  let g : Control U ‖u‖₊ := ⟨fun t => f (t + a), by fun_prop, fun _ => f.bound _⟩
  have eq := cat_eq join ha hr f g
  rw [show f.cat g a = f by ext; simp [g, Control.cat], hf] at eq
  simpa [eq] using (Φ r).le_opNorm_of_le g.norm_lp

end PalomarALCS
