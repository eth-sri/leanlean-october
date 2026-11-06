module

public import Chazelle.Core.RestoreSearchGood
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.FactsTree
public import Chazelle.Core.SweepLocal

/-!
# WP-E, Lemma 3.2 part 15: the ends of a new chord lie on closed arcs of its region

The pruning lemma of the search needs the two ends of the good candidate's chord `e` (a chord
not in `S`, inside the region `R`) on closed arcs of `R`.

* `ccw_half`: a sector containing both horizontal directions contains all directions of an open
  half-plane (above or below);
* `vertex_half`: at a walk vertex whose left sector contains both horizontal rays, the left
  sector contains a half-disk (all points above, or all points below, the vertex);
* `attach_closedArc`: an admissible chord `e ∉ S` with `e ∩ D ⊆ R`, attached at a position, has
  the position's key on a closed arc of `R`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (sidePt SideAttach sideLeft sideLeftOf sideCcw sideCross sideDot sidePrev
  sideNext sideInArc freeIn regionsIn TouchesIn halfDisk mem_halfDisk_iff isPreconnected_halfDisk
  sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset)

/-- **A sector containing both horizontal directions contains an open half-plane.** -/
theorem ccw_half {B A : Point} (hB : B ≠ 0) (hA : A ≠ 0)
    (hE : sideCcw B ((1, 0) : Point) A) (hW : sideCcw B ((-1, 0) : Point) A) :
    (∀ X : Point, 0 < X.2 → sideCcw B X A) ∨ (∀ X : Point, X.2 < 0 → sideCcw B X A) := by
  unfold sideCcw sideCross sideDot at *
  simp only at hE hW
  
  
  rcases lt_trichotomy (B.1 * A.2 - B.2 * A.1) 0 with hc | hc | hc
  · -- a reflex sector
    have e1 : B.2 < 0 ∨ 0 < A.2 := by
      grind
    have e2 : 0 < B.2 ∨ A.2 < 0 := by
      grind
    rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2
    · linarith
    · -- both edges point down: the upper half-plane is in the sector
      left
      intro X hX
      right; left
      refine ⟨hc, ?_⟩
      by_contra hn
      push Not at hn
      nlinarith
    · -- both edges point up: the lower half-plane is in the sector
      right
      intro X hX
      right; left
      refine ⟨hc, ?_⟩
      by_contra hn
      push Not at hn
      nlinarith
    · linarith
  · -- a straight or full sector
    rcases lt_trichotomy (B.1 * A.1 + B.2 * A.2) 0 with hd | hd | hd
    · grind
    · simp_all
    · -- `A`, `B` in the same direction: every direction but theirs is in the sector
      rcases le_or_gt B.2 0 with hb | hb
      · left
        intro X hX
        right; right; right
        refine ⟨hc, hd, ?_⟩
        by_cases hx : B.1 * X.2 - B.2 * X.1 = 0
        · right
          -- `X` parallel to `B`, pointing up while `B` does not: opposite directions
          have key : (B.1 * X.1 + B.2 * X.2) * X.2 = B.2 * (X.1 ^ 2 + X.2 ^ 2) := by
            grind
          rcases hb.lt_or_eq with hb | hb
          · have : B.2 * (X.1 ^ 2 + X.2 ^ 2) < 0 :=
              mul_neg_of_neg_of_pos hb (by positivity)
            by_contra hn; push Not at hn; nlinarith
          grind
        grind
      · right
        intro X hX
        right; right; right
        refine ⟨hc, hd, ?_⟩
        by_cases hx : B.1 * X.2 - B.2 * X.1 = 0
        · right
          have key : (B.1 * X.1 + B.2 * X.2) * X.2 = B.2 * (X.1 ^ 2 + X.2 ^ 2) := by
            grind
          have : 0 < B.2 * (X.1 ^ 2 + X.2 ^ 2) :=
            mul_pos hb (by nlinarith [sq_nonneg X.1, mul_pos (neg_pos.2 hX) (neg_pos.2 hX)])
          by_contra hn; push Not at hn; nlinarith
        grind
  grind

variable {M : Model}

/-- **An attached admissible chord is a horizontal segment from the attachment point**, whose
other end `o` is a walk point (outside the domain) and whose open part is in the domain. -/
theorem attach_ray (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) :
    ∃ o : Point, o ≠ sidePt M.W p t ∧ o.2 = (sidePt M.W p t).2 ∧
      c = Chazelle.segment (sidePt M.W p t) o ∧ o ∉ M.D ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, lerp (sidePt M.W p t) o s ∈ M.D := by
  obtain ⟨a, b, hab, hcab, hy, hopen, ha, hb⟩ := hM.ends c hc
  have hA' := hA
  rw [hcab] at hA'
  have hout : ∀ x, WalkEnd M.W c x → x ∉ M.D := by
    rintro x ⟨⟨p', t', hA'', rfl⟩, -⟩
    exact hM.trace p' hA''.1 t' hA''.2.1 hA''.2.2.1.le
  rcases hM.attach_endpoint hopen hA' with h | h
  · grind
  grind [Geometry.segment_comm, Geometry.lerp_symm]

/-- A point of the segment `[w, v]` between `w` and `v` on a horizontal line. -/
theorem lerp_hit {w u v : Point} (hu : u.2 = w.2) (hv : v.2 = w.2) {s : ℝ}
    (hs : u.1 = w.1 + s * (v.1 - w.1)) : lerp w v s = u :=
  point_ext (by simp_all) (by simp_all)

/-- **Two horizontal segments from `w` in the same direction, with open parts in `D` and far ends
outside `D`, are equal.** -/
theorem ray_eq {D : Set Point} {w o o' : Point} (ho : o.2 = w.2) (ho' : o'.2 = w.2)
    (hsame : 0 < (o.1 - w.1) * (o'.1 - w.1)) (hoD : o ∉ D) (ho'D : o' ∉ D)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w o s ∈ D)
    (hopen' : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w o' s ∈ D) : o = o' := by
  rcases lt_trichotomy o.1 o'.1 with h | h | h
  · exfalso
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `o` inside `[w, o']`
      have hs : (o.1 - w.1) / (o'.1 - w.1) ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos h1 h2, (div_lt_one h2).2 (by linarith)⟩
      refine hoD ?_
      rw [← lerp_hit ho ho' (s := (o.1 - w.1) / (o'.1 - w.1)) (by grind)]
      grind
    · -- `o'` inside `[w, o]`
      have hs : (o'.1 - w.1) / (o.1 - w.1) ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos_of_neg_of_neg h2 h1, (div_lt_one_of_neg h1).2 (by linarith)⟩
      refine ho'D ?_
      rw [← lerp_hit ho' ho (s := (o'.1 - w.1) / (o.1 - w.1)) (by grind)]
      grind
  · grind
  · exfalso
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hs : (o'.1 - w.1) / (o.1 - w.1) ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos h2 h1, (div_lt_one h1).2 (by linarith)⟩
      refine ho'D ?_
      rw [← lerp_hit ho' ho (s := (o'.1 - w.1) / (o.1 - w.1)) (by grind)]
      grind
    · have hs : (o.1 - w.1) / (o'.1 - w.1) ∈ Ioo (0 : ℝ) 1 :=
        ⟨div_pos_of_neg_of_neg h1 h2, (div_lt_one_of_neg h2).2 (by linarith)⟩
      refine hoD ?_
      rw [← lerp_hit ho ho' (s := (o.1 - w.1) / (o'.1 - w.1)) (by grind)]
      grind

/-- The points of a segment from `w` eventually approach `w`. -/
theorem lerp_near (w o : Point) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 ∧ dist (lerp w o s) w < r := by
  have hc : Continuous (fun s : ℝ => lerp w o s) := by
    unfold lerp; fun_prop
  have ht : Tendsto (fun s : ℝ => lerp w o s) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have := hc.tendsto 0
    rw [Geometry.lerp_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  filter_upwards [Ioo_mem_nhdsGT one_pos, ht.eventually (ball_mem_nhds w hr)] with s hs hd
  simp_all

/-- **The direction of an attached chord is in the left sector at its attachment.** -/
theorem attach_ccw (_hM : WalkAx M) {c : Set Point} {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) {o : Point} (ho : o ≠ sidePt M.W p t)
    (hco : c = Chazelle.segment (sidePt M.W p t) o) :
    sideCcw (sideNext M.W p - sidePt M.W p t) (o - sidePt M.W p t)
      (sidePrev M.W p t - sidePt M.W p t) := by
  obtain ⟨-, -, -, -, r, hr, hleft⟩ := hA
  obtain ⟨s, ⟨hs1, hd⟩, hs0⟩ := ((lerp_near (sidePt M.W p t) o hr).and self_mem_nhdsWithin).exists
  have hs0' : (0 : ℝ) < s := hs0
  have hx : lerp (sidePt M.W p t) o s ∈ c := by
    rw [hco]; exact Geometry.mem_segment_iff_lerp.2 ⟨s, hs0'.le, hs1.le, rfl⟩
  have hl := hleft _ hx (Chazelle.Jordan.lerp_ne_left (Ne.symm ho) hs0') hd
  unfold sideLeft sideLeftOf at hl
  have e : lerp (sidePt M.W p t) o s - sidePt M.W p t = s • (o - sidePt M.W p t) := by
    apply point_ext <;> simp_all
  rw [e, Chazelle.Chain.sideCcw_smul hs0'] at hl
  exact hl

/-- A horizontal direction vector is a positive multiple of `(1, 0)` or `(-1, 0)`. -/
theorem ccw_unit {B A o w : Point} (h : sideCcw B (o - w) A) (ho : o.2 = w.2) :
    (0 < o.1 - w.1 → sideCcw B ((1, 0) : Point) A) ∧
      (o.1 - w.1 < 0 → sideCcw B ((-1, 0) : Point) A) := by
  constructor
  · intro hpos
    have e : o - w = (o.1 - w.1) • ((1, 0) : Point) := by
      aesop
    rw [e, Chazelle.Chain.sideCcw_smul hpos] at h
    exact h
  · intro hneg
    have e : o - w = (w.1 - o.1) • ((-1, 0) : Point) := by
      aesop
    rw [e, Chazelle.Chain.sideCcw_smul (by linarith)] at h
    exact h

/-- Points level with the centre of a half-disk and inside its square are in its closure. -/
theorem mem_closure_halfDisk' {w z : Point} {r τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (hr : 0 < r)
    (hz : z.2 = w.2) (hz1 : |z.1 - w.1| < r) : z ∈ closure (halfDisk w r τ) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ := min ε r / 2 with hδ
  have hδ0 : 0 < δ := by simp_all
  have hδε : δ < ε := by grind
  have hδr : δ < r := by grind
  have habs : |τ * δ| = δ := by
    rcases hτ with rfl | rfl
    · grind
    grind
  refine ⟨(z.1, w.2 + τ * δ), ?_, ?_⟩
  · rw [mem_halfDisk_iff]
    refine ⟨⟨hz1, ?_⟩, ?_⟩
    · simp_all
    · show 0 < τ * (w.2 + τ * δ - w.2)
      rw [add_sub_cancel_left, ← mul_assoc]
      rcases hτ with rfl | rfl <;> norm_num <;> exact hδ0
  grind [Prod.dist_eq, dist_self, Real.dist_eq, sub_add_cancel_left, abs_neg]

section
variable (hM : WalkAx M)
include hM
/-- The point before a position is not its point. -/
theorem sidePrev_ne {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t) :
    sidePrev M.W p t ≠ sidePt M.W p t := by
  have hnd := hM.nd p hp
  unfold sidePrev
  split_ifs with ht
  · subst ht
    rw [Chazelle.Chain.sidePt_zero]
    have hn : 0 < M.W.n := by omega
    have hq := hM.nd ((p + M.W.n - 1) % M.W.n) (Nat.mod_lt _ hn)
    rw [Sweep.prev_succ_mod hp] at hq
    exact hq
  · unfold sidePt
    exact (Chazelle.Jordan.lerp_ne_left hnd (lt_of_le_of_ne ht0 (Ne.symm ht))).symm

/-- **The ends of a new chord lie on closed arcs of its region.**  An admissible chord `e ∉ S`
whose domain part lies in the region `R` of `S`, attached at `(p, t)`, has the key `p + t` on the
closed key interval of an arc of `R`. -/
theorem attach_closedArc {S : Set (Set Point)} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) (hne : S.Nonempty) {R : Set Point} (hR : R ∈ M.regions S)
    {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) (heR : e ∩ M.D ⊆ R) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W e p t) :
    ∃ a b, M.IsArc S R a b ∧ ClosedArc a b (p + t) := by
  obtain ⟨hp, ht0, ht1, -, rA, hrA, hleftA⟩ := id hA
  have hsys := hM.sys S hS hfin
  have hRo : IsOpen R := hsys.regionsIn_open subset_rfl hR
  obtain ⟨oe, hoe, hoe2, hes, hoeD, hoeo⟩ := attach_ray hM he hA
  obtain ⟨r₁, hr₁, hfree⟩ := Sweep.sector_free hM hS hfin hp ht0 ht1
  have hav := sidePrev_ne hM hp ht0
  have hbv := Chazelle.Chain.sideNext_ne_pt (hM.nd p hp) ht1
  -- a point of `e` near the attachment, in `R`
  obtain ⟨se, ⟨hse1, hsed⟩, hse0⟩ := ((lerp_near (sidePt M.W p t) oe (lt_min hr₁ hrA)).and
    self_mem_nhdsWithin).exists
  have hse0' : (0 : ℝ) < se := hse0
  set ze := lerp (sidePt M.W p t) oe se with hze
  have hzeD : ze ∈ M.D := hoeo se ⟨hse0', hse1⟩
  have hzee : ze ∈ e := by
    rw [hes]; exact Geometry.mem_segment_iff_lerp.2 ⟨se, hse0'.le, hse1.le, rfl⟩
  have hzeR : ze ∈ R := heR ⟨hzee, hzeD⟩
  have hzel : sideLeft M.W p t ze :=
    hleftA ze hzee (Chazelle.Jordan.lerp_ne_left (Ne.symm hoe) hse0')
      (lt_of_lt_of_le hsed (min_le_right _ _))
  replace hsed : dist ze (sidePt M.W p t) < r₁ := lt_of_lt_of_le hsed (min_le_left _ _)
  by_cases hB : ∃ c ∈ S, SideAttach M.W c p t
  · -- **a chord `c` of `S` is attached at the same position**
    obtain ⟨c, hc, hAc⟩ := hB
    obtain ⟨oc, hoc, hoc2, hcs, hocD, hoco⟩ := attach_ray hM (hS hc) hAc
    set w := sidePt M.W p t with hw
    
    -- `e` and `c` leave in opposite directions
    have hopp : (oe.1 - w.1) * (oc.1 - w.1) < 0 := by
      rcases lt_trichotomy ((oe.1 - w.1) * (oc.1 - w.1)) 0 with h | h | h
      · exact h
      · rcases mul_eq_zero.1 h with h | h
        · grind
        grind
      · have := ray_eq hoe2 hoc2 h hoeD hocD hoeo hoco
        simp_all
    -- so `c` is the only chord of `S` attached there
    have hsole : ∀ c' ∈ S, SideAttach M.W c' p t → c' = c := by
      intro c' hc' hA'
      obtain ⟨o', ho', ho'2, hc's, ho'D, ho'o⟩ := attach_ray hM (hS hc') hA'
      rcases lt_trichotomy ((oe.1 - w.1) * (o'.1 - w.1)) 0 with h | h | h
      · have hpos : 0 < (oc.1 - w.1) * (o'.1 - w.1) := by
          have h3 := mul_pos_of_neg_of_neg hopp h
          have h4 : (oe.1 - w.1) * (oc.1 - w.1) * ((oe.1 - w.1) * (o'.1 - w.1)) =
              (oe.1 - w.1) ^ 2 * ((oc.1 - w.1) * (o'.1 - w.1)) := by ring
          rw [h4] at h3
          exact pos_of_mul_pos_right h3 (sq_nonneg _)
        rw [hc's, hcs, ray_eq hoc2 ho'2 hpos hocD ho'D hoco ho'o]
      · rcases mul_eq_zero.1 h with h | h
        · grind
        grind
      · exact absurd (by rw [hes, hc's, ray_eq hoe2 ho'2 h hoeD ho'D hoeo ho'o] : e = c')
          (fun h => heS (h ▸ hc'))
    -- the sector contains both horizontal directions, hence a half-plane
    have hse := ccw_unit (attach_ccw hM hA hoe hes) hoe2
    have hsc := ccw_unit (attach_ccw hM hAc hoc hcs) hoc2
    have hE : sideCcw (sideNext M.W p - w) ((1, 0) : Point) (sidePrev M.W p t - w) := by
      rcases mul_neg_iff.1 hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · grind
      grind
    have hW : sideCcw (sideNext M.W p - w) ((-1, 0) : Point) (sidePrev M.W p t - w) := by
      rcases mul_neg_iff.1 hopp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · grind
      grind
    obtain ⟨τ, hτ, hhalf⟩ : ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧ ∀ X : Point, 0 < τ * X.2 →
        sideCcw (sideNext M.W p - w) X (sidePrev M.W p t - w) := by
      rcases ccw_half (sub_ne_zero_of_ne hbv) (sub_ne_zero_of_ne hav) hE hW with h | h
      · exact ⟨1, Or.inl rfl, fun X hX => h X (by linarith)⟩
      · exact ⟨-1, Or.inr rfl, fun X hX => h X (by linarith)⟩
    -- the half-disk is free
    have hH : halfDisk w r₁ τ ⊆ freeIn M.D S := by
      intro x hx
      have hxl : sideLeft M.W p t x := by
        unfold sideLeft sideLeftOf
        exact hhalf _ (by simpa using hx.2)
      obtain ⟨hxD, hxc⟩ := hfree x hx.1 hxl
      refine ⟨hxD, ?_⟩
      rintro ⟨c', hc', hxc'⟩
      have hc'c := hsole c' hc' (hxc c' hc' hxc')
      rw [hc'c, hcs] at hxc'
      obtain ⟨s, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hxc'
      have := hx.2
      simp only [mem_ofPred_eq, lerp_snd, hoc2, sub_self, mul_zero, add_zero] at this
      simp at this
    have hx1 : ∀ s : ℝ, ∀ o : Point, o.2 = w.2 → dist (lerp w o s) w < r₁ →
        |(lerp w o s).1 - w.1| < r₁ := by
      intro s o _ hd
      refine lt_of_le_of_lt ?_ hd
      rw [Prod.dist_eq, ← Real.dist_eq]
      exact le_max_left _ _
    have hy2 : ∀ s : ℝ, ∀ o : Point, o.2 = w.2 → (lerp w o s).2 = w.2 := by
      grind [lerp_snd]
    -- the half-disk is in `R`
    have hHR : halfDisk w r₁ τ ⊆ R := by
      refine Chazelle.Chain.subset_regionsIn_of_inter hR (isPreconnected_halfDisk _ _ _) hH ?_
      have hcl := mem_closure_halfDisk' hτ hr₁ (hy2 se oe hoe2) (hx1 se oe hoe2 hsed)
      obtain ⟨y, hyR, hyH⟩ := mem_closure_iff_nhds.1 hcl R (hRo.mem_nhds hzeR)
      exact ⟨y, hyH, hyR⟩
    -- `R` touches `c`
    obtain ⟨sc, ⟨hsc1, hscd⟩, hsc0⟩ := ((lerp_near w oc hr₁).and
      self_mem_nhdsWithin).exists
    have hsc0' : (0 : ℝ) < sc := hsc0
    have htR : TouchesIn M.D c R := by
      refine ⟨lerp w oc sc, ⟨?_, hoco sc ⟨hsc0', hsc1⟩⟩, closure_mono hHR
        (mem_closure_halfDisk' hτ hr₁ (hy2 sc oc hoc2) (hx1 sc oc hoc2 hscd))⟩
      rw [hcs]; exact Geometry.mem_segment_iff_lerp.2 ⟨sc, hsc0'.le, hsc1.le, rfl⟩
    -- the two sides of `c` are the regions faced next to the attachment
    obtain ⟨U, V, l, r, hU, hV, hUV, harcU, harcV, htouch⟩ := hM.attach_face hS hfin hc hAc
    obtain ⟨tU, tV⟩ := htouch hsole
    obtain ⟨U₀, V₀, -, -, -, -, hiff⟩ := chordSides_of_system hsys hc
    have h1 := (hiff R hR).1 htR
    have h2 := (hiff U hU).1 tU
    have h3 := (hiff V hV).1 tV
    have hRUV : R = U ∨ R = V := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
        first
        | exact absurd (h2.trans h3.symm) hUV
        | exact Or.inl (h1.trans h2.symm)
        | exact Or.inr (h1.trans h3.symm)
    rcases hRUV with rfl | rfl
    · exact ⟨p + t, r, harcU, Or.inr (Or.inl rfl)⟩
    · exact ⟨l, p + t, harcV, Or.inr (Or.inr rfl)⟩
  · -- **no chord of `S` is attached there: the key is inside an arc of `R`**
    push Not at hB
    have hcut : ¬ M.IsCut S (p + t) := by
      rintro ⟨c, hc, p', t', hA', hk⟩
      obtain ⟨rfl, rfl⟩ := sideKey_inj ht0 ht1 hA'.2.1 hA'.2.2.1 hk
      grind
    -- the small sector is free, hence in `R`
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
    have hzeL : ze ∈ L := ⟨hsed, hzel⟩
    have hLR : L ⊆ R :=
      Chazelle.Chain.subset_regionsIn_of_inter hR hpre hLfree ⟨ze, hzeL, hzeR⟩
    -- the arc around the key
    obtain ⟨X, hX, l, r, harc, hin⟩ := hM.arc_around hS hfin hne hcut
    have hscale : Tendsto (fun s : ℝ => s * (1 - t)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
      · have : Tendsto (fun δ : ℝ => δ * (1 - t)) (𝓝 0) (𝓝 (0 * (1 - t))) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact mul_pos hx (by linarith)
    have hfX : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 ∧ M.Faces p (t + s * (1 - t)) X := by
      filter_upwards [Ioo_mem_nhdsGT one_pos, hscale.eventually (cyc_open hin)] with s hs hk
      have hs0 : (0 : ℝ) < s := hs.1
      refine ⟨hs.2, harc.2.2.2.2.2.2 p _ hp (by nlinarith) (by nlinarith [mul_pos (sub_pos.2 hs.2) (sub_pos.2 ht1)]) ?_⟩
      grind
    obtain ⟨s, hs1, hs2⟩ := (hoff.and hfX).exists
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset (M.wa p) (M.wb p) (t + s * (1 - t)) (δ * (1 - t)) ∈ X :=
      hscale.eventually hs2.2
    obtain ⟨δ, hδ1, hδ2⟩ := (hs1.and h2).exists
    have e : offset (sidePt M.W p t) (sideNext M.W p) s (1 * δ) =
        offset (M.wa p) (M.wb p) (t + s * (1 - t)) (δ * (1 - t)) := by
      rw [one_mul]; unfold sidePt sideNext
      exact Chazelle.Chain.offset_lerp_left _ _ _ _ _
    have hXR : X = R := by
      rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hR with h | h
      · exact h
      · exact absurd (h.le_bot ⟨hδ2, hLR (e ▸ hδ1.2)⟩) (fun h => h)
    rw [hXR] at harc
    exact ⟨l, r, harc, Or.inl hin⟩


end

end

end Restore

end Chazelle.Core
