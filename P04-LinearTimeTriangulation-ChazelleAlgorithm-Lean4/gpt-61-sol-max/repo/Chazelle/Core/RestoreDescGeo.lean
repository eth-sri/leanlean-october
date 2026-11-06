module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreDescent
public import Chazelle.Core.RestoreComplete

/-!
# WP-E, Lemma 3.2 part 17: rays from inside an arc

The descent tests positions strictly inside the arc `Aᵢ` of the region `R` (the ends of node
chords of a piece's canonical normal form).  For the completeness clause of the test, the ray
from such a position into its left sector must give an admissible chord outside `S` whose domain
part lies in `R`.

* `sector_sub_region`: near the point of a position strictly inside an arc of `R`, its left
  sector lies in `R`;
* `ray_avoids`: a ray into the left sector of a non-cut position meets no chord of `S` before it
  leaves the domain (such a chord would be attached at the position);
* `ray_in_region`: the ray's chord is not in `S` and its domain part lies in `R`;
* `ray_adm`: the ray's chord is admissible (chain models: at a height not above the chain top).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (sidePt SideAttach sideLeft sideLeftOf sideCcw sidePrev sideNext sideInArc
  freeIn regionsIn TouchesIn sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset)

variable {M : Model}

/-- **The left sector at a position strictly inside an arc of `R` lies in `R`** near its
point. -/
theorem sector_sub_region (hM : WalkAx M) {S : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ M.regions S) {l r : ℝ} (harc : M.IsArc S R l r)
    {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (hin : sideInArc l r (p + t)) :
    ∃ r₁ > 0, ∀ x ∈ ball (sidePt M.W p t) r₁, sideLeft M.W p t x → x ∈ R := by
  have hcut : ¬ M.IsCut S (p + t) := harc.2.2.2.2.2.1 _ hin
  have hB : ∀ c ∈ S, ¬ SideAttach M.W c p t := fun c hc hA => hcut ⟨c, hc, p, t, hA, rfl⟩
  obtain ⟨r₁, hr₁, hfree⟩ := Sweep.sector_free hM hS hfin hp ht0 ht1
  have hav := sidePrev_ne hM hp ht0
  have hbv := Chazelle.Chain.sideNext_ne_pt (hM.nd p hp) ht1
  obtain ⟨-, hpre, hoff⟩ := Chazelle.Chain.sideSector (S := (freeIn M.D S)ᶜ) hav hbv hr₁ (by
    intro x hx hxS hxl
    apply hxS
    obtain ⟨hxD, hxc⟩ := hfree x hx hxl
    exact ⟨hxD, fun ⟨c, hc, hxc'⟩ => hB c hc (hxc c hc hxc')⟩)
  set L := ball (sidePt M.W p t) r₁ ∩
    {x | sideLeftOf (sidePrev M.W p t) (sidePt M.W p t) (sideNext M.W p) x} with hL
  have hLfree : L ⊆ freeIn M.D S := by
    intro x hx
    obtain ⟨hxD, hxc⟩ := hfree x hx.1 hx.2
    exact ⟨hxD, fun ⟨c, hc, hxc'⟩ => hB c hc (hxc c hc hxc')⟩
  have hscale : Tendsto (fun s : ℝ => s * (1 - t)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
    · have : Tendsto (fun δ : ℝ => δ * (1 - t)) (𝓝 0) (𝓝 (0 * (1 - t))) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact mul_pos hx (by linarith)
  have hfR : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 ∧ M.Faces p (t + s * (1 - t)) R := by
    filter_upwards [Ioo_mem_nhdsGT one_pos, hscale.eventually (cyc_open hin)] with s hs hk
    have hs0 : (0 : ℝ) < s := hs.1
    refine ⟨hs.2, harc.2.2.2.2.2.2 p _ hp (by nlinarith)
      (by nlinarith [mul_pos (sub_pos.2 hs.2) (sub_pos.2 ht1)]) ?_⟩
    grind
  obtain ⟨s, hs1, hs2⟩ := (hoff.and hfR).exists
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset (M.wa p) (M.wb p) (t + s * (1 - t)) (δ * (1 - t)) ∈ R :=
    hscale.eventually hs2.2
  obtain ⟨δ, hδ1, hδ2⟩ := (hs1.and h2).exists
  have e : offset (sidePt M.W p t) (sideNext M.W p) s (1 * δ) =
      offset (M.wa p) (M.wb p) (t + s * (1 - t)) (δ * (1 - t)) := by
    rw [one_mul]; unfold sidePt sideNext
    exact Chazelle.Chain.offset_lerp_left _ _ _ _ _
  have hLR : L ⊆ R :=
    Chazelle.Chain.subset_regionsIn_of_inter hR hpre hLfree ⟨_, hδ1.2, e ▸ hδ2⟩
  exact ⟨r₁, hr₁, fun x hx hxl => hLR ⟨hx, hxl⟩⟩

/-- A point level with `w` whose signed offset `σ (x.1 - w.1)` is `s` is the ray point at `s`. -/
theorem eq_rayPt {w x : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hx : x.2 = w.2) :
    x = rayPt w σ (σ * (x.1 - w.1)) := by
  aesop (add simp [rayPt_fst, mul_assoc, rayPt_snd]) (add safe (by omega))

/-- The signed offset is affine along a level segment. -/
theorem off_lerp (w u v : Point) (σ μ : ℝ) :
    σ * ((lerp u v μ).1 - w.1) = (1 - μ) * (σ * (u.1 - w.1)) + μ * (σ * (v.1 - w.1)) := by
  core_grind

section
variable (hM : WalkAx M) {S : Set (Set Point)} (hS : S ⊆ M.Adm)
include hM hS
/-- **A ray into the left sector of a non-cut position meets no chord of `S`** before it leaves
the domain. -/
theorem ray_avoids {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (hcut : ¬ M.IsCut S (p + t)) {σ T : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hsec : sideLeft M.W p t (rayPt (sidePt M.W p t) σ 1))
    (hdom : ∀ s, 0 < s → s < T → rayPt (sidePt M.W p t) σ s ∈ M.D) :
    ∀ c ∈ S, ∀ s, 0 < s → s < T → rayPt (sidePt M.W p t) σ s ∉ c := by
  intro c hc s₀ hs₀ hs₀T hz
  set w := sidePt M.W p t with hw
  have hwD : w ∉ M.D := hM.trace p hp t ht0 ht1.le
  obtain ⟨u, v, huv, hcuv, hy, hopen, hu, hv⟩ := hM.ends c (hS hc)
  have hout : ∀ x, WalkEnd M.W c x → x ∉ M.D := by
    rintro x ⟨⟨p', t', hA'', rfl⟩, -⟩
    exact hM.trace p' hA''.1 t' hA''.2.1 hA''.2.2.1.le
  have huD := hout u hu
  have hvD := hout v hv
  rw [hcuv] at hz
  obtain ⟨μ₀, hμ0, hμ1, hz⟩ := Geometry.mem_segment_iff_lerp.1 hz
  -- the chord is level with `w`
  have hu2 : u.2 = w.2 := by
    grind [rayPt_snd, lerp_snd, sub_self, mul_zero, add_zero]
  have hv2 : v.2 = w.2 := hy ▸ hu2
  set f : Point → ℝ := fun x => σ * (x.1 - w.1) with hf
  -- the ends are not ray points before the exit
  have hnot : ∀ x, x.2 = w.2 → x ∉ M.D → f x ≤ 0 ∨ T ≤ f x := by
    intro x hx hxD
    by_contra hh
    push Not at hh
    exact hxD (by rw [eq_rayPt hσ hx]; grind)
  have hfz : f (rayPt w σ s₀) = s₀ := by
    grind [rayPt_fst]
  have hlin : s₀ = (1 - μ₀) * f u + μ₀ * f v := by
    rw [← hfz, hz]; exact off_lerp w u v σ μ₀
  -- the key step, for the end `a` before the ray and `b` after it
  have key : ∀ a b : Point, c = Chazelle.segment a b → a.2 = w.2 → b.2 = w.2 →
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ M.D) → f a ≤ 0 → T ≤ f b → False := by
    intro a b hcab ha2 hb2 hab hfa hfb
    
    -- `w` is on the segment, hence its end `a`
    have hfa0 : f a = 0 := by
      by_contra hne
      have hneg : f a < 0 := lt_of_le_of_ne hfa hne
      set μ := - f a / (f b - f a) with hμ
      have hden : 0 < f b - f a := by linarith
      have hμ0 : 0 < μ := div_pos (by linarith) hden
      have hμ1 : μ < 1 := (div_lt_one hden).2 (by linarith)
      have hwl : lerp a b μ = w := by
        have hf0 : f (lerp a b μ) = 0 := by
          show σ * ((lerp a b μ).1 - w.1) = 0
          rw [off_lerp]
          grind
        grind [lerp_snd]
      grind
    have haw : a = w := by
      grind
    -- so the chord is attached at the position: a cut
    apply hcut
    refine ⟨c, hc, p, t, ⟨hp, ht0, ht1, ?_, 1, one_pos, ?_⟩, rfl⟩
    · rw [hcab, haw]; exact Geometry.left_mem_segment _ _
    · intro x hx hxw _
      rw [hcab] at hx
      obtain ⟨l₁, hl0, hl1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
      have hl : 0 < l₁ := by
        grind [Geometry.lerp_zero]
      have h2 : (lerp a b l₁).2 = w.2 := by grind [lerp_snd]
      have hfx : 0 < f (lerp a b l₁) := by
        show 0 < σ * ((lerp a b l₁).1 - w.1)
        rw [off_lerp]
        show 0 < (1 - l₁) * f a + l₁ * f b
        rw [hfa0]; nlinarith
      rw [eq_rayPt hσ h2]
      exact (Sweep.sideLeft_rayPt_iff M.W p t σ hfx one_pos).2 hsec
  rcases hnot u hu2 huD with hfu | hfu
  · have hfv : T ≤ f v := by
      rcases hnot v hv2 hvD with hfv | hfv
      · nlinarith
      · exact hfv
    exact key u v hcuv hu2 hv2 hopen hfu hfv
  · have hfv : f v ≤ 0 := by
      rcases hnot v hv2 hvD with hfv | hfv
      · exact hfv
      · nlinarith
    refine key v u (by grind [Geometry.segment_comm]) hv2 hu2 (fun s hs => ?_) hfv hfu
    rw [Geometry.lerp_symm]
    grind

/-- **The chord of a ray from a position strictly inside an arc of `R`** is not in `S` and its
domain part lies in `R`. -/
theorem ray_in_region (hfin : S.Finite)
    {R : Set Point} (hR : R ∈ M.regions S) {l r : ℝ} (harc : M.IsArc S R l r) {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (hin : sideInArc l r (p + t)) {σ T : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T) (hsec : sideLeft M.W p t (rayPt (sidePt M.W p t) σ 1))
    (hdom : ∀ s, 0 < s → s < T → rayPt (sidePt M.W p t) σ s ∈ M.D)
    (hout : rayPt (sidePt M.W p t) σ T ∉ M.D) :
    chordOf (sidePt M.W p t) σ T ∉ S ∧ chordOf (sidePt M.W p t) σ T ∩ M.D ⊆ R := by
  set w := sidePt M.W p t with hw
  have hcut : ¬ M.IsCut S (p + t) := harc.2.2.2.2.2.1 _ hin
  have hav := ray_avoids hM hS hp ht0 ht1 hcut hσ hsec hdom
  constructor
  · intro hmem
    exact hav _ hmem (T / 2) (by linarith) (by linarith)
      ((mem_chordOf hσ hT.le).2 ⟨T / 2, by linarith, by linarith, rfl⟩)
  · -- the open ray is connected, free, and starts in `R`
    set I : Set Point := (fun s => rayPt w σ s) '' Ioo 0 T with hI
    have hIc : IsPreconnected I := by
      refine isPreconnected_Ioo.image _ (Continuous.continuousOn ?_)
      unfold rayPt; fun_prop
    have hIf : I ⊆ freeIn M.D S := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨hdom s hs.1 hs.2, fun ⟨c, hc, hxc⟩ => hav c hc s hs.1 hs.2 hxc⟩
    obtain ⟨r₁, hr₁, hsub⟩ := sector_sub_region hM hS hfin hR harc hp ht0 ht1 hin
    set s₁ := min (T / 2) (r₁ / 2) with hs₁
    have hs₁0 : 0 < s₁ := lt_min (by linarith) (by linarith)
    have hs₁T : s₁ < T := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hs₁r : s₁ < r₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hmeet : (I ∩ R).Nonempty := by
      refine ⟨rayPt w σ s₁, ⟨s₁, ⟨hs₁0, hs₁T⟩, rfl⟩, hsub _ ?_ ?_⟩
      · rw [mem_ball, Prod.dist_eq, rayPt_fst, rayPt_snd, dist_self, Real.dist_eq,
          add_sub_cancel_left]
        rcases hσ with rfl | rfl
        · rw [one_mul, abs_of_pos hs₁0, max_eq_left hs₁0.le]; exact hs₁r
        · rw [neg_one_mul, abs_neg, abs_of_pos hs₁0, max_eq_left hs₁0.le]; exact hs₁r
      · exact (Sweep.sideLeft_rayPt_iff M.W p t σ hs₁0 one_pos).2 hsec
    have hIR := Chazelle.Chain.subset_regionsIn_of_inter hR hIc hIf hmeet
    rintro x ⟨hx, hxD⟩
    obtain ⟨s, hs0, hsT, rfl⟩ := (mem_chordOf hσ hT.le).1 hx
    have hs0' : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h, rayPt_zero'] at hxD
        exact hM.trace p hp t ht0 ht1.le hxD
    grind

/-! ## Arrival on the piece's chain (M2') -/


end

/-- The point of a level segment is the ray point at the proportional offset. -/
theorem lerp_rayPt (a : Point) (σ L μ : ℝ) : lerp a (rayPt a σ L) μ = rayPt a σ (μ * L) := by
  grind [lerp_fst, rayPt_fst, lerp_snd, rayPt_snd]

/-- The chord of a ray up to `T` is the segment to the ray point at `T`. -/
theorem chordOf_eq_segment {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T) :
    chordOf z σ T = Chazelle.segment z (rayPt z σ T) := by
  ext x
  rw [mem_chordOf hσ hT.le, Geometry.mem_segment_iff_lerp]
  constructor
  · rintro ⟨s, hs0, hsT, rfl⟩
    refine ⟨s / T, div_nonneg hs0 hT.le, (div_le_one hT).2 hsT, ?_⟩
    grind [lerp_rayPt]
  · rintro ⟨μ, hμ0, hμ1, rfl⟩
    exact ⟨μ * T, by positivity, by nlinarith, lerp_rayPt _ _ _ _⟩

/-- The chain avoids the domain of its model. -/
theorem set_not_dom {C : Chain} {x : Point} (hx : x ∈ C.set) : x ∉ C.dom :=
  fun h => h.2 (Or.inl hx)

/-- **Arrival on the chain (M2').**  Let `k = [a, o]` be a level chord of the chain model of `Cα`
from the chain point `a`, and let a ray from `a` in the direction of `o` stay in the domain of a
model `M` (in which the chain points are outside the domain) up to `T`, where it reaches a chain
point.  Then it reaches `o`: before `o` it is in `Cα`'s domain, and beyond `o` it would leave the
box of `Cα`'s model (`o` is not on the slit: the slit is above the chain). -/
theorem arrive_other {D : Set Point} {Cα : Chain} (hsetD : ∀ x ∈ Cα.set, x ∉ D)
    {a o : Point} (hoy : o.2 = a.2) (haC : a ∈ Cα.set)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a o s ∈ Cα.dom) (hoD : o ∉ Cα.dom)
    {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hdir : 0 < σ * (o.1 - a.1)) (hT : 0 < T)
    (hdom : ∀ s, 0 < s → s < T → rayPt a σ s ∈ D) (hfar : rayPt a σ T ∈ Cα.set) :
    rayPt a σ T = o := by
  set L₀ := σ * (o.1 - a.1) with hL₀
  have ho : o = rayPt a σ L₀ := eq_rayPt hσ hoy
  rcases lt_trichotomy T L₀ with h | h | h
  · exfalso
    have hin := hkopen (T / L₀) ⟨div_pos hT hdir, (div_lt_one hdir).2 h⟩
    rw [ho, lerp_rayPt, div_mul_cancel₀ _ hdir.ne'] at hin
    exact set_not_dom hfar hin
  · rw [h, ← ho]
  · exfalso
    have hoM : o ∈ D := by grind
    -- `o` is not a chain point
    have hoC : o ∉ Cα.set := fun hh => hsetD o hh hoM
    -- `o` is not on the slit
    have hoS : o ∉ Cα.slit := by
      intro hs
      obtain ⟨h1, h2, -⟩ := Cα.mem_slit_iff.1 hs
      have h3 : o.2 ≤ Cα.top.2 := hoy ▸ Cα.snd_le_top_of_mem_set haC
      exact hoC (by
        have : o = Cα.top := point_ext h1 (le_antisymm h3 h2)
        rw [this]; exact Cα.top_mem_set)
    -- so `o` is off the box, and so is the farther ray point
    have hob : o ∉ Chazelle.Chain.box Cα.radius := fun hb =>
      hoD ⟨hb, fun hh => hh.elim hoC hoS⟩
    have hab := Cα.set_subset_box haC
    have hfb := Cα.set_subset_box hfar
    rw [Chazelle.Chain.mem_box_iff] at hab hfb
    rw [Chazelle.Chain.mem_box_iff, hoy] at hob
    push Not at hob
    
    have e1 : o.1 = a.1 + σ * L₀ := by grind
    rw [rayPt_fst] at hfb
    rcases hσ with rfl | rfl
    · grind
    grind

/-! ## Choosing the child (cyclic order in offsets) -/



/-! ## The arc just after a walk vertex (the leaf) -/

/-- A key interval containing `x` and no end in `(p, x]` contains `(p, x]`, and `p` is its start
or inside it. -/
theorem cyc_after_vertex {a b p x : ℝ} (hin : sideInArc a b x) (ha : ¬ (p < a ∧ a ≤ x))
    (hb : ¬ (p < b ∧ b ≤ x)) (hpx : p < x) :
    ClosedArc a b p ∧ ∀ y, p < y → y ≤ x → sideInArc a b y := by
  refine ⟨?_, fun y hy1 hy2 => ?_⟩
  · by_cases hpa : p = a
    · exact Or.inr (Or.inl hpa)
    · left
      core_grind
  core_grind

section
variable (hGM : GoodModel M)
include hGM
/-- **The arc just after a walk vertex**: the keys just after the vertex `p` are inside an arc
of a region `U` of `F`, and `p` is on the closed arc. -/
theorem arc_after {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {p : ℕ} (hp : p < M.W.n) :
    ∃ U ∈ M.regions F, ∃ a b : ℝ, M.IsArc F U a b ∧ ClosedArc a b p ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b (p + ε) := by
  have hM := walkAx_of_goodModel hGM
  obtain ⟨t', ht', hno⟩ := hM.exists_after hFam.2.1 hFam.1 hp le_rfl zero_lt_one
  rw [add_zero] at hno
  have hx0 : (0 : ℝ) < p + t' := by grind
  have hxcut : ¬ M.IsCut F (p + t') := fun h => hno _ h ⟨by simp_all, le_rfl⟩
  obtain ⟨U, hU, a, b, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hFam hx0 hxcut
  refine ⟨U, hU, a, b, harc, ?_⟩
  rcases F.eq_empty_or_nonempty with hF | hne
  · -- the arc of the empty family is the whole walk
    rcases harc.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, rfl, rfl⟩
    · simp_all
    · refine ⟨?_, ?_⟩
      · by_cases h0 : (p : ℝ) = 0
        · exact Or.inr (Or.inl h0)
        · left; core_grind
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        core_grind
  · obtain ⟨hca, hcb, -⟩ := WalkAx.arc_cuts hne harc
    have hpx : (p : ℝ) < p + t' := by simp_all
    obtain ⟨h1, h2⟩ := cyc_after_vertex hin (fun h => hno _ hca h) (fun h => hno _ hcb h) hpx
    refine ⟨h1, ?_⟩
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ht'.1] with ε hε hε'
    grind

/-! ## The test at a node end is valid and hits (M1) -/

/-- The domain of a good model is bounded in abscissa. -/
theorem goodModel_bounded : ∃ B : ℝ, ∀ x ∈ M.D, |x.1| < B := by
  rcases hGM with ⟨C, -, rfl⟩ | ⟨Q, -, rfl⟩
  · exact ⟨C.radius, fun x hx => hx.1.1⟩
  · refine ⟨Chazelle.Jordan.coordBound Q + 1, fun x hx => ?_⟩
    have := (Chazelle.Jordan.filled_subset_square Q hx.1).1
    linarith

/-- A horizontal ray leaves a good model's domain. -/
theorem ray_leaves (z : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ t₁ > (0 : ℝ), rayPt z σ t₁ ∉ M.D := by
  obtain ⟨B, hB⟩ := goodModel_bounded hGM
  refine ⟨|B| + |z.1| + 1, by positivity, fun h => ?_⟩
  have h1 := hB _ h
  rw [rayPt_fst, abs_lt] at h1
  have h2 := le_abs_self B
  have h3 := neg_abs_le z.1
  have h4 := le_abs_self z.1
  rcases hσ with rfl | rfl <;> linarith

/-- **The test at a position strictly inside an arc of `R`, in a direction of its left sector,
finds an exit** whose chord is admissible, not in `S`, with its domain part in `R` (the
hypotheses of the test's completeness clause). -/
theorem inner_exit {Q : Polygon} {S : Set (Set Point)}
    (hFam : M.ChordFamily Q S) {R : Set Point} (hR : R ∈ M.regions S) {l r : ℝ}
    (harc : M.IsArc S R l r) {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hin : sideInArc l r (p + t)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : sideLeft M.W p t (rayPt (sidePt M.W p t) σ 1))
    (htop : ∀ C : Chain, M = chainModel C → (sidePt M.W p t).2 ≤ C.top.2) :
    ∃ T > (0 : ℝ), (∀ s, 0 < s → s < T → rayPt (sidePt M.W p t) σ s ∈ M.D) ∧
      rayPt (sidePt M.W p t) σ T ∉ M.D ∧ chordOf (sidePt M.W p t) σ T ∈ M.Adm ∧
      chordOf (sidePt M.W p t) σ T ∉ S ∧ chordOf (sidePt M.W p t) σ T ∩ M.D ⊆ R := by
  have hM := walkAx_of_goodModel hGM
  set w := sidePt M.W p t with hw
  obtain ⟨r₁, hr₁, hsub⟩ := sector_sub_region hM hFam.2.1 hFam.1 hR harc hp ht0 ht1 hin
  have hini : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w σ s ∈ R := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr₁] with s hs hs'
    have hs0 : (0 : ℝ) < s := hs
    refine hsub _ ?_ ((Sweep.sideLeft_rayPt_iff M.W p t σ hs0 one_pos).2 hsec)
    rw [mem_ball, Prod.dist_eq, rayPt_fst, rayPt_snd, dist_self, Real.dist_eq,
      add_sub_cancel_left]
    grind
  obtain ⟨t₁, ht₁, hout₁⟩ := ray_leaves hGM w hσ
  obtain ⟨T, hT, -, hTD, hRT, hadm, -⟩ := local_exit hGM hFam hR hσ
    (hM.trace p hp t ht0 ht1.le) hini ht₁ hout₁ htop
  have hdom : ∀ s, 0 < s → s < T → rayPt w σ s ∈ M.D := fun s h1 h2 =>
    (Chazelle.Chain.regionsIn_subset hR (hRT s h1 h2)).1
  obtain ⟨h1, h2⟩ := ray_in_region hM hFam.2.1 hFam.1 hR harc hp ht0 ht1 hin hσ hT hsec hdom hTD
  grind

/-! ## Agreeing stretches: positions -/


end

/-- Positions at the same offset of agreeing stretches have the same parameter. -/
theorem param_agree {M M' : Model} {Q : Polygon} {g g' L : ℕ}
    (hA : WalkEmbed.Agree M.W M'.W g g' L) {d : ℕ} (hd : d < L) (h : ℕ) :
    M.param Q ⟨(g + d) % M.W.n, h⟩ = M'.param Q ⟨(g' + d) % M'.W.n, h⟩ := by
  unfold Model.param Model.wa Model.wb
  simp only
  rw [WalkEmbed.mod_succ_mod, WalkEmbed.mod_succ_mod, hA d hd.le, hA (d + 1) hd]

/-- Positions at the same offset of agreeing stretches have the same point. -/
theorem pos_agree {M M' : Model} {Q : Polygon} {g g' L : ℕ}
    (hA : WalkEmbed.Agree M.W M'.W g g' L) {d : ℕ} (hd : d < L) (h : ℕ) :
    M.pos Q ⟨(g + d) % M.W.n, h⟩ = M'.pos Q ⟨(g' + d) % M'.W.n, h⟩ := by
  unfold Model.pos
  rw [param_agree hA hd h]
  unfold Model.wa Model.wb
  simp only
  rw [WalkEmbed.mod_succ_mod, WalkEmbed.mod_succ_mod, hA d hd.le, hA (d + 1) hd]

/-- The point of a position is the walk point at its edge and parameter. -/
theorem pos_eq_sidePt (M : Model) (Q : Polygon) (x : WPos) :
    M.pos Q x = sidePt M.W x.edge (M.param Q x) := rfl

/-- The distance from `w` of a ray point. -/
theorem dist_rayPt (w : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {s : ℝ} (hs : 0 ≤ s) :
    dist (rayPt w σ s) w = s := by
  rw [Prod.dist_eq, rayPt_fst, rayPt_snd, dist_self, Real.dist_eq, add_sub_cancel_left]
  rcases hσ with rfl | rfl
  all_goals simp_all

/-- **An attached level segment leaves into the left sector**: the ray towards its other end is
in the left sector of the attachment. -/
theorem attach_ray_left {W : Polygon} {c : Set Point} {p : ℕ} {t : ℝ} (hA : SideAttach W c p t)
    {σ L₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hL₀ : 0 < L₀)
    (hc : c = Chazelle.segment (sidePt W p t) (rayPt (sidePt W p t) σ L₀)) :
    sideLeft W p t (rayPt (sidePt W p t) σ 1) := by
  obtain ⟨-, -, -, -, r, hr, hleft⟩ := hA
  set w := sidePt W p t
  set s := min (L₀ / 2) (r / 2) with hs
  have hs0 : 0 < s := lt_min (by linarith) (by linarith)
  have hsL : s < L₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsr : s < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmem : rayPt w σ s ∈ c := by
    rw [hc, Geometry.mem_segment_iff_lerp]
    refine ⟨s / L₀, by positivity, (div_le_one hL₀).2 hsL.le, ?_⟩
    grind [lerp_rayPt]
  have hd := dist_rayPt w hσ hs0.le
  have hne : rayPt w σ s ≠ w := fun h => by grind [dist_self]
  exact (Sweep.sideLeft_rayPt_iff W p t σ hs0 one_pos).1 (hleft _ hmem hne (by grind))

end

end Restore

end Chazelle.Core
