module

public import Chazelle.Core.RestoreShoot
public import Chazelle.Core.RestoreSearch

/-!
# WP-E, Lemma 3.2 part 3: when does a candidate ray start in the region?

Local shooting (`local_exit`) needs the ray from a candidate point to *start* in the region `R`
being split.  The search checks this with a constant number of sign tests and a scan of the exit
chords of `R`; this file proves that the checks suffice.

* `valid_inside`: the key of the position is inside an arc of `R` and the direction points into
  its left sector (`Sweep.ray_mem_region_of_arc`).
* `valid_after`: the position is a walk vertex where an arc of `R` begins, the direction is in its
  left sector, strictly counterclockwise from the next walk edge, and no exit chord of `R` runs
  along the ray.
* `valid_before`: the mirror case, an arc of `R` ending at the vertex (`ray_mem_region_before'`,
  `Sweep.ray_mem_region_before` for any key).
* The "no exit along the ray" condition comes from the chord records: `exit_avoid` shows that an
  attached chord record whose endpoint position is not the candidate vertex (with the ray
  leaving that endpoint along the chord) does not contain the initial part of the ray;
  `touches_of_along_after`/`_before` show that a chord of the family running along the ray at
  such a vertex is an exit chord of `R`, so scanning the exits of `R` is enough.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideCcw sideCross sideDot
  freeIn regionsIn TouchesIn sideLeft_zero sideCcw_smul sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (point_ext)
open Chazelle.Jordan (offset SectorSide)
open Sweep

section Valid

variable {M : Model}

/-- **The ray leaving a cut vertex on the side of the previous edge** starts in the region of the
arc ending at the vertex (`Sweep.ray_mem_region_before` for any key). -/
theorem ray_mem_region_before' (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
    {a : ℝ} (harc : M.IsArc F U a (p + 0)) {c : Set Point} (hc : c ∈ F)
    (hA : SideAttach M.W c p 0) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hnot : ∀ c ∈ F, SideAttach M.W c p 0 → ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∉ c)
    (hcross : 0 < sideCross ((τ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∈ U := by
  have hM := walkAx_of_goodModel hGM
  obtain ⟨r, hr, -, hbefore⟩ := sub_sector hM hFam.2.1 hFam.1 hp hτ hsec hnot hc hA
  obtain ⟨⟨hS1, hHc, hoff⟩, hrayH⟩ := hbefore hcross
  have hne : F.Nonempty := ⟨c, hc⟩
  obtain ⟨-, -, hak⟩ := WalkAx.arc_cuts hne harc
  have hn : 0 < M.W.n := by omega
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and (before_eventually hp harc.1 harc.2.1 hak)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hq : (p + M.W.n - 1) % M.W.n < M.W.n := Nat.mod_lt _ hn
  have hf : M.Faces ((p + M.W.n - 1) % M.W.n) (1 - s) U :=
    harc.2.2.2.2.2.2 _ (1 - s) hq (by linarith) (by linarith) hs2
  obtain ⟨δ, hδU, hδ⟩ := (hf.and hs1).exists
  have hfree : ball (M.W.vtx p) r ∩ {x | sideLeftOf (M.W.vtx ((p + M.W.n - 1) % M.W.n))
      (M.W.vtx p) (M.W.vtx p + ((-τ, 0) : Point)) x} ⊆ freeIn M.D F := fun x hx => by
    simpa using hS1 hx
  have hδU' : offset (M.W.vtx ((p + M.W.n - 1) % M.W.n)) (M.W.vtx p) (1 - s) (1 * δ) ∈ U := by
    rw [one_mul]
    have e : M.W.vtx p = M.W.vtx (((p + M.W.n - 1) % M.W.n + 1) % M.W.n) := by
      rw [prev_succ_mod hp]
    rw [e]; exact hδU
  have hsub := subset_region hU hHc hfree hδ.1 hδU'
  have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hsr
  rw [hwv]
  exact hsub (hrayH s hs hsr.2)

theorem sideCross_pair (u : Point) (a b : ℝ) : sideCross u ((a, b) : Point) = u.1 * b - u.2 * a :=
  rfl

theorem sideCross_pair_left (a b : ℝ) (u : Point) :
    sideCross ((a, b) : Point) u = a * u.2 - b * u.1 := rfl

section
variable (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
include hM hF hfin hU hp
/-- **A chord running along the ray at the start of an arc is an exit chord.**  At a walk vertex
where an arc of `U` begins, if the direction `τ` is in the left sector strictly counterclockwise
from the next walk edge, a chord of the family containing ray points arbitrarily close to the
vertex touches `U`. -/
theorem touches_of_along_after {b : ℝ}
    (harc : M.IsArc F U (p + 0) b) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hcross : 0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((τ, 0) : Point))
    {c : Set Point} (hc : c ∈ F) (hfr : ∃ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∈ c) :
    TouchesIn M.D c U := by
  have hsys := hM.sys F hF hfin
  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hfin hp le_rfl one_pos
  have hne := hM.nd p hp
  have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
  set v := M.W.vtx p with hv
  set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha
  set b' := M.W.vtx ((p + 1) % M.W.n) with hb
  have hbv : b' ≠ v := fun h => hne h.symm
  have hB0 : b' - v ≠ 0 := sub_ne_zero.2 hbv
  have hκ0 : 0 < -((b' - v).2 * τ) := by
    have := hcross; rw [sideCross_pair] at this; linarith
  set A : Point := ((τ, 0) : Point) with hAdef
  have hvA : v + A ≠ v := by
    intro h
    have := congrArg Prod.fst h
    simp only [Prod.fst_add, hAdef, add_eq_left] at this
    simp_all
  have hsecv : ∀ x, sideLeft M.W p 0 x ↔ sideCcw (b' - v) (x - v) (a - v) :=
    fun x => sideLeft_zero _ _ _
  have hdp : sideCcw (b' - v) A (a - v) := by
    have := (hsecv _).1 hsec
    rwa [hwv, rayPt_sub, one_smul] at this
  set Wg := ball v r ∩ {x | sideLeftOf (v + A) v b' x} with hWg
  have hWsec : ∀ x ∈ Wg, sideCcw (b' - v) (x - v) A := fun x hx => by
    have : sideLeftOf (v + A) v b' x := hx.2
    rwa [sideLeftOf_iff, add_sub_cancel_left] at this
  have hWleft : ∀ x ∈ Wg, sideLeft M.W p 0 x := fun x hx =>
    (hsecv x).2 (Chazelle.Chain.sideCcw_sub_left hB0 hdp (hWsec x hx))
  have hWfree : ∀ x ∈ ball v r, x ∈ (freeIn M.D F)ᶜ → ¬ sideLeftOf (v + A) v b' x := by
    intro x hx hxS hxW
    have hxW' : x ∈ Wg := ⟨hx, hxW⟩
    obtain ⟨hxD, hxc⟩ := hsf x (by grind) (hWleft x hxW')
    apply hxS
    refine ⟨hxD, ?_⟩
    rintro ⟨c', hc', hxc'⟩
    have hA' := hxc c' hc' hxc'
    have hvc' : v ∈ c' := by have := hA'.2.2.2.1; grind
    have hy : x.2 = v.2 := hsys.snd_eq hc' hxc' hvc'
    rcases hWsec x hxW' with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [hAdef, sideCross_pair, Prod.snd_sub, hy, sub_self] at h; simp at h
    all_goals linarith
  obtain ⟨hS1, hHc, hoff⟩ := Chazelle.Chain.sideSector hvA hbv hr hWfree
  obtain ⟨-, -, hkb⟩ := WalkAx.arc_cuts ⟨c, hc⟩ harc
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and (WalkAx.eventually_after_start hkb)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hf : M.Faces p s U :=
    harc.2.2.2.2.2.2 p s hp hs3.1 hs3.2 (by grind [add_zero])
  obtain ⟨δ, hδU, hδ⟩ := (hf.and hs1).exists
  have hWU : Wg ⊆ U :=
    subset_region hU hHc (fun x hx => by simpa using hS1 hx) hδ.2 (by rw [one_mul]; exact hδU)
  -- a point of the chord on the ray, close to the vertex
  obtain ⟨s₀, hs₀c, hs₀⟩ := (hfr.and_eventually (Ioo_mem_nhdsGT (half_pos hr))).exists
  have hs₀0 : 0 < s₀ := hs₀.1
  
  refine ⟨rayPt (sidePt M.W p 0) τ s₀, ⟨hs₀c, ?_⟩, ?_⟩
  · refine (hsf _ ?_ ((sideLeft_rayPt_iff _ p 0 τ one_pos hs₀0).1 hsec)).1
    rw [mem_ball, dist_rayPt _ hτ hs₀0.le]; linarith
  · rw [hwv]
    set κ := -((b' - v).2 * τ) with hκ
    set K := |(b' - v).1| + 1 with hK
    have hK0 : 0 < K := by positivity
    have hlim : Tendsto (fun ε : ℝ => ((v.1 + τ * s₀, v.2 - τ * ε) : Point)) (𝓝[>] (0 : ℝ))
        (𝓝 (rayPt v τ s₀)) := by
      have hc' : Continuous (fun ε : ℝ => ((v.1 + τ * s₀, v.2 - τ * ε) : Point)) := by fun_prop
      have h0 : ((v.1 + τ * s₀, v.2 - τ * 0) : Point) = rayPt v τ s₀ :=
        point_ext (by simp) (by simp)
      have := hc'.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    have hbd : 0 < min (r / 2) (s₀ * κ / K) := lt_min (half_pos hr) (by positivity)
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hbd] with ε hε hε'
    have hε0 : (0 : ℝ) < ε := hε
    have hε1 : ε < r / 2 := hε'.2.trans_le (min_le_left _ _)
    have hε2 : ε * K < s₀ * κ := by
      have := hε'.2.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ hK0] at this
    apply hWU
    refine ⟨?_, ?_⟩
    · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
      rcases hτ with rfl | rfl
      · constructor
        · rw [show v.1 + 1 * s₀ - v.1 = s₀ by ring, abs_of_pos hs₀0]; linarith
        · rw [show v.2 - 1 * ε - v.2 = -ε by ring, abs_neg, abs_of_pos hε0]; linarith
      · constructor
        · rw [show v.1 + -1 * s₀ - v.1 = -s₀ by ring, abs_neg, abs_of_pos hs₀0]; linarith
        · rw [show v.2 - -1 * ε - v.2 = ε by ring, abs_of_pos hε0]; linarith
    · show sideLeftOf (v + A) v b' _
      rw [sideLeftOf_iff, add_sub_cancel_left]
      have hX : ((v.1 + τ * s₀, v.2 - τ * ε) : Point) - v = ((τ * s₀, -(τ * ε)) : Point) := by
        ext <;> simp
      rw [hX]
      left
      have hab := le_abs_self (b' - v).1
      have hab' := neg_abs_le (b' - v).1
      have q1 := mul_le_mul_of_nonneg_left hab hε0.le
      have q2 := mul_le_mul_of_nonneg_left hab' hε0.le
      refine ⟨hcross, ?_, ?_⟩
      · rw [sideCross_pair]
        
        rcases hτ with rfl | rfl
        · linarith
        linarith
      · rw [hAdef, sideCross_pair]
        rcases hτ with rfl | rfl <;> simp <;> linarith

/-- **A chord running along the ray at the end of an arc is an exit chord** (mirror of
`touches_of_along_after`: the direction is strictly clockwise from the previous walk edge). -/
theorem touches_of_along_before {l : ℝ}
    (harc : M.IsArc F U l (p + 0)) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hcross : 0 < sideCross ((τ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p))
    {c : Set Point} (hc : c ∈ F) (hfr : ∃ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∈ c) :
    TouchesIn M.D c U := by
  have hsys := hM.sys F hF hfin
  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hfin hp le_rfl one_pos
  have hne := hM.nd p hp
  have hn0 : 0 < M.W.n := by omega
  have hwv : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero _ _
  set v := M.W.vtx p with hv
  set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha
  set b' := M.W.vtx ((p + 1) % M.W.n) with hb
  have hbv : b' ≠ v := fun h => hne h.symm
  have hav : a ≠ v := by
    have := hM.nd _ (Nat.mod_lt (p + M.W.n - 1) hn0)
    rwa [prev_succ_mod hp] at this
  have hB0 : b' - v ≠ 0 := sub_ne_zero.2 hbv
  have hA0 : a - v ≠ 0 := sub_ne_zero.2 hav
  have hκ0 : 0 < τ * (a - v).2 := by
    grind [sideCross_pair_left]
  set A : Point := ((τ, 0) : Point) with hAdef
  have hAne : A ≠ 0 := by
    intro h
    have := congrArg Prod.fst h
    simp only [hAdef, Prod.fst_zero] at this
    simp_all
  have hvA : v + A ≠ v := by
    grind
  have hsecv : ∀ x, sideLeft M.W p 0 x ↔ sideCcw (b' - v) (x - v) (a - v) :=
    fun x => sideLeft_zero _ _ _
  have hdp : sideCcw (b' - v) A (a - v) := by
    have := (hsecv _).1 hsec
    grind [rayPt_sub, one_smul]
  set Wg := ball v r ∩ {x | sideLeftOf a v (v + A) x} with hWg
  have hWsec : ∀ x ∈ Wg, sideCcw A (x - v) (a - v) := fun x hx => by
    have : sideLeftOf a v (v + A) x := hx.2
    grind [sideLeftOf_iff, add_sub_cancel_left]
  have hWleft : ∀ x ∈ Wg, sideLeft M.W p 0 x := fun x hx =>
    (hsecv x).2 (Chazelle.Chain.sideCcw_sub_right hB0 hAne hA0 hdp (hWsec x hx))
  have hWfree : ∀ x ∈ ball v r, x ∈ (freeIn M.D F)ᶜ → ¬ sideLeftOf a v (v + A) x := by
    intro x hx hxS hxW
    have hxW' : x ∈ Wg := ⟨hx, hxW⟩
    obtain ⟨hxD, hxc⟩ := hsf x (by grind) (hWleft x hxW')
    apply hxS
    refine ⟨hxD, ?_⟩
    rintro ⟨c', hc', hxc'⟩
    have hA' := hxc c' hc' hxc'
    have hvc' : v ∈ c' := by have := hA'.2.2.2.1; grind
    have hy : x.2 = v.2 := hsys.snd_eq hc' hxc' hvc'
    rcases hWsec x hxW' with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [hAdef, sideCross_pair_left, Prod.snd_sub, hy, sub_self] at h; simp at h
    all_goals linarith
  obtain ⟨hS1, hHc, hoff⟩ := Chazelle.Chain.sideSector hav hvA hr hWfree
  obtain ⟨-, -, hak⟩ := WalkAx.arc_cuts ⟨c, hc⟩ harc
  obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
    ((hoff.and (before_eventually hp harc.1 harc.2.1 hak)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hq : (p + M.W.n - 1) % M.W.n < M.W.n := Nat.mod_lt _ hn0
  have hf : M.Faces ((p + M.W.n - 1) % M.W.n) (1 - s) U :=
    harc.2.2.2.2.2.2 _ (1 - s) hq (by linarith) (by linarith) hs2
  obtain ⟨δ, hδU, hδ⟩ := (hf.and hs1).exists
  have hδU' : offset a v (1 - s) (1 * δ) ∈ U := by
    rw [one_mul]
    have e : v = M.W.vtx (((p + M.W.n - 1) % M.W.n + 1) % M.W.n) := by
      rw [prev_succ_mod hp]
    rw [e]; exact hδU
  have hWU : Wg ⊆ U :=
    subset_region hU hHc (fun x hx => by simpa using hS1 hx) hδ.1 hδU'
  obtain ⟨s₀, hs₀c, hs₀⟩ := (hfr.and_eventually (Ioo_mem_nhdsGT (half_pos hr))).exists
  have hs₀0 : 0 < s₀ := hs₀.1
  
  refine ⟨rayPt (sidePt M.W p 0) τ s₀, ⟨hs₀c, ?_⟩, ?_⟩
  · refine (hsf _ ?_ ((sideLeft_rayPt_iff _ p 0 τ one_pos hs₀0).1 hsec)).1
    rw [mem_ball, dist_rayPt _ hτ hs₀0.le]; linarith
  · rw [hwv]
    set κ := τ * (a - v).2 with hκ
    set K := |(a - v).1| + 1 with hK
    have hK0 : 0 < K := by positivity
    have hlim : Tendsto (fun ε : ℝ => ((v.1 + τ * s₀, v.2 + τ * ε) : Point)) (𝓝[>] (0 : ℝ))
        (𝓝 (rayPt v τ s₀)) := by
      have hc' : Continuous (fun ε : ℝ => ((v.1 + τ * s₀, v.2 + τ * ε) : Point)) := by fun_prop
      have h0 : ((v.1 + τ * s₀, v.2 + τ * 0) : Point) = rayPt v τ s₀ :=
        point_ext (by simp) (by simp)
      have := hc'.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    have hbd : 0 < min (r / 2) (s₀ * κ / K) := lt_min (half_pos hr) (by positivity)
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hbd] with ε hε hε'
    have hε0 : (0 : ℝ) < ε := hε
    have hε1 : ε < r / 2 := hε'.2.trans_le (min_le_left _ _)
    have hε2 : ε * K < s₀ * κ := by
      have := hε'.2.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ hK0] at this
    apply hWU
    refine ⟨?_, ?_⟩
    · rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
      rcases hτ with rfl | rfl
      · constructor
        · rw [show v.1 + 1 * s₀ - v.1 = s₀ by ring, abs_of_pos hs₀0]; linarith
        · rw [show v.2 + 1 * ε - v.2 = ε by ring, abs_of_pos hε0]; linarith
      · constructor
        · rw [show v.1 + -1 * s₀ - v.1 = -s₀ by ring, abs_neg, abs_of_pos hs₀0]; linarith
        · rw [show v.2 + -1 * ε - v.2 = -ε by ring, abs_neg, abs_of_pos hε0]; linarith
    · show sideLeftOf a v (v + A) _
      rw [sideLeftOf_iff, add_sub_cancel_left]
      have hX : ((v.1 + τ * s₀, v.2 + τ * ε) : Point) - v = ((τ * s₀, τ * ε) : Point) := by
        ext <;> simp
      rw [hX]
      left
      have hab := le_abs_self (a - v).1
      have hab' := neg_abs_le (a - v).1
      have q1 := mul_le_mul_of_nonneg_left hab hε0.le
      have q2 := mul_le_mul_of_nonneg_left hab' hε0.le
      refine ⟨hcross, ?_, ?_⟩
      · rw [hAdef, sideCross_pair_left]
        rcases hτ with rfl | rfl <;> simp <;> linarith
      · rw [sideCross_pair_left]
        
        rcases hτ with rfl | rfl
        · 
          nlinarith
        · 
          nlinarith


end

/-- A chord of the family attached at a walk vertex is attached at the position of the vertex
when some chord is attached at its key. -/
theorem attach_of_cut (_hM : WalkAx M) {F : Set (Set Point)} {p : ℕ} (hk : M.IsCut F ((p : ℝ) + 0)) :
    ∃ c ∈ F, SideAttach M.W c p 0 := by
  obtain ⟨c, hc, p', t', hA', hkey⟩ := hk
  obtain ⟨hpp, htt⟩ := sideKey_inj le_rfl one_pos hA'.2.1 hA'.2.2.1 hkey
  grind

section
variable (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)} (hFam : M.ChordFamily Q F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n)
include hGM Q hFam hU hp
/-- **Validity at the start of an arc.** -/
theorem valid_after
    {b : ℝ} (harc : M.IsArc F U (p + 0) b) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hcross : 0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p) ((τ, 0) : Point))
    (hex : ∀ c ∈ F, TouchesIn M.D c U →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∉ c) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∈ U := by
  have hM := walkAx_of_goodModel hGM
  rcases F.eq_empty_or_nonempty with rfl | hne
  · -- the empty family: the region is the domain
    have hUD : U = M.D := by
      have := Chazelle.Chain.regionsIn_empty (D := M.D) hM.preconn hM.nonempty
      have hU' : U ∈ regionsIn M.D ∅ := hU
      simp_all
    obtain ⟨r, hr, hsf⟩ := sector_free hM hFam.2.1 hFam.1 hp le_rfl one_pos
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hsr
    have hs0 : (0 : ℝ) < s := hs
    rw [hUD]
    refine (hsf _ ?_ ((sideLeft_rayPt_iff _ p 0 τ one_pos hs0).1 hsec)).1
    rw [mem_ball, dist_rayPt _ hτ hs0.le]; exact hsr.2
  · obtain ⟨hk, -, -⟩ := WalkAx.arc_cuts hne harc
    obtain ⟨c, hc, hA⟩ := attach_of_cut hM hk
    refine ray_mem_region_after hGM hFam hU hp harc hc hA hτ hsec ?_ hcross
    intro c' hc' _
    by_contra hfr
    rw [Filter.not_eventually] at hfr
    simp only [not_not] at hfr
    have ht := touches_of_along_after hM hFam.2.1 hFam.1 hU hp harc hτ hsec hcross hc' hfr
    obtain ⟨s, h1, h2⟩ := (hfr.and_eventually (hex c' hc' ht)).exists
    exact h2 h1

/-- **Validity at the end of an arc.** -/
theorem valid_before
    {l : ℝ} (harc : M.IsArc F U l (p + 0)) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hcross : 0 < sideCross ((τ, 0) : Point) (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p))
    (hex : ∀ c ∈ F, TouchesIn M.D c U →
      ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∉ c) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∈ U := by
  have hM := walkAx_of_goodModel hGM
  rcases F.eq_empty_or_nonempty with rfl | hne
  · have hUD : U = M.D := by
      have := Chazelle.Chain.regionsIn_empty (D := M.D) hM.preconn hM.nonempty
      have hU' : U ∈ regionsIn M.D ∅ := hU
      simp_all
    obtain ⟨r, hr, hsf⟩ := sector_free hM hFam.2.1 hFam.1 hp le_rfl one_pos
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with s hs hsr
    have hs0 : (0 : ℝ) < s := hs
    rw [hUD]
    refine (hsf _ ?_ ((sideLeft_rayPt_iff _ p 0 τ one_pos hs0).1 hsec)).1
    rw [mem_ball, dist_rayPt _ hτ hs0.le]; exact hsr.2
  · obtain ⟨-, hk, -⟩ := WalkAx.arc_cuts hne harc
    obtain ⟨c, hc, hA⟩ := attach_of_cut hM hk
    refine ray_mem_region_before' hGM hFam hU hp harc hc hA hτ hsec ?_ hcross
    intro c' hc' _
    by_contra hfr
    rw [Filter.not_eventually] at hfr
    simp only [not_not] at hfr
    have ht := touches_of_along_before hM hFam.2.1 hFam.1 hU hp harc hτ hsec hcross hc' hfr
    obtain ⟨s, h1, h2⟩ := (hfr.and_eventually (hex c' hc' ht)).exists
    exact h2 h1

/-- **Validity inside an arc.** -/
theorem valid_inside
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {a b : ℝ} (harc : M.IsArc F U a b)
    (hin : sideInArc a b (p + t)) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p t (rayPt (sidePt M.W p t) τ 1)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p t) τ s ∈ U :=
  ray_mem_region_of_arc hGM hFam hU hp ht ht1 harc hin hτ hsec


end

/-- **The exit scan.**  An attached chord record whose left end is not the walk vertex `(p, 0)`
(for `τ = 1`), or whose right end is not (for `τ = -1`), contains no ray points arbitrarily
close to the vertex, when the ray leaves the vertex into its left sector. -/
theorem exit_avoid (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hFam : M.ChordFamily Q F) {cr : CRec} (hcF : cr.toSet M Q ∈ F) (hat : cr.Attached M Q)
    {p : ℕ} (hp : p < M.W.n) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hsec : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ 1))
    (hL : τ = 1 → ¬ (cr.lp = p ∧ M.param Q cr.lpos = 0))
    (hR : τ = -1 → ¬ (cr.rp = p ∧ M.param Q cr.rpos = 0)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) τ s ∉ cr.toSet M Q := by
  have hM := walkAx_of_goodModel hGM
  have hF := hFam.2.1
  obtain ⟨r, hr, hsf⟩ := sector_free hM hF hFam.1 hp le_rfl one_pos
  by_contra hfr
  rw [Filter.not_eventually] at hfr
  simp only [not_not] at hfr
  obtain ⟨s, hsc, hs⟩ := (hfr.and_eventually (Ioo_mem_nhdsGT hr)).exists
  have hs0 : 0 < s := hs.1
  have hsl : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) τ s) :=
    (sideLeft_rayPt_iff _ p 0 τ one_pos hs0).1 hsec
  have hball : rayPt (sidePt M.W p 0) τ s ∈ ball (sidePt M.W p 0) r := by
    rw [mem_ball, dist_rayPt _ hτ hs0.le]; exact hs.2
  have hA := (hsf _ hball hsl).2 _ hcF hsc
  have hadm := hF hcF
  set v := sidePt M.W p 0 with hv
  -- the vertex is an end of the chord: its left end if `τ = 1`, its right end if `τ = -1`
  have hvc : v ∈ cr.toSet M Q := hA.2.2.2.1
  have hvD : v ∉ M.D := hM.trace p hp 0 le_rfl zero_le_one
  obtain ⟨hL1, hL2⟩ := hat
  have hlmem : sidePt M.W cr.lp (M.param Q cr.lpos) ∈ cr.toSet M Q := hL1.2.2.2.1
  have hrmem : sidePt M.W cr.rp (M.param Q cr.rpos) ∈ cr.toSet M Q := hL2.2.2.2.1
  obtain ⟨y, xa, xb, hH, hcr⟩ := adm_hchord hGM hadm
  have hts : cr.toSet M Q =
      Visibility.hseg (Q.vtx cr.h).2 (M.pos Q cr.lpos).1 (M.pos Q cr.rpos).1 := rfl
  have hxy : ∀ z ∈ cr.toSet M Q, z.2 = y ∧ xa ≤ z.1 ∧ z.1 ≤ xb := fun z hz => by
    rw [hcr] at hz; exact hz
  have hend : ∀ z ∈ cr.toSet M Q, z ∉ M.D → z = ((xa, y) : Point) ∨ z = ((xb, y) : Point) := by
    intro z hz hzD
    obtain ⟨hzy, hz1, hz2⟩ := hxy z hz
    rcases hz1.lt_or_eq with h1 | h1
    · rcases hz2.lt_or_eq with h2 | h2
      · exfalso; apply hzD
        have := hH.open_mem z.1 h1 h2
        grind
      grind
    grind
  have hmemA : ((xa, y) : Point) ∈ cr.toSet M Q := by
    rw [hcr]; exact ⟨rfl, le_rfl, hH.lt.le⟩
  have hmemB : ((xb, y) : Point) ∈ cr.toSet M Q := by
    rw [hcr]; exact ⟨rfl, hH.lt.le, le_rfl⟩
  have epl : sidePt M.W cr.lp (M.param Q cr.lpos) = M.pos Q cr.lpos := rfl
  have epr : sidePt M.W cr.rp (M.param Q cr.rpos) = M.pos Q cr.rpos := rfl
  have hlA : sidePt M.W cr.lp (M.param Q cr.lpos) = ((xa, y) : Point) := by
    have h1 : (M.pos Q cr.lpos).1 ≤ xa := by
      have := hmemA; rw [hts] at this; exact this.2.1
    grind
  have hrB : sidePt M.W cr.rp (M.param Q cr.rpos) = ((xb, y) : Point) := by
    have h1 : xb ≤ (M.pos Q cr.rpos).1 := by
      have := hmemB; rw [hts] at this; exact this.2.2
    grind
  have hsx := (hxy _ hsc).2
  simp only [rayPt_fst] at hsx
  rcases hτ with rfl | rfl
  · have hvA : v = ((xa, y) : Point) := by
      grind
    have hu := attach_unique hM hadm hA hL1 (hvA.trans hlA.symm)
    grind
  · have hvB : v = ((xb, y) : Point) := by
      grind
    have hu := attach_unique hM hadm hA hL2 (hvB.trans hrB.symm)
    grind

end Valid

end

end Restore

end Chazelle.Core
