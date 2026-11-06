module

public import Chazelle.MacT
public import Chazelle.Chain.Chord
public import Chazelle.Final.Wedge

namespace Chazelle.Chain
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Geometry (lerp lerp_fst lerp_snd lerp_zero lerp_one lerp_mem_segment point_ext
  point_ext_iff det_lerp det_lerp_self)
variable (C : Chain)

/-! ### The winding number of the boundary walk -/

/-! ### The split walks of a chord (Lemma 2.1, winding form) -/

/-! ### Circular order of directions -/
omit C in
/-- The cross product `u.1 v.2 - u.2 v.1`. -/
def sideCross (u v : Point) : ℝ := u.1 * v.2 - u.2 * v.1
omit C in
/-- The dot product. -/
def sideDot (u v : Point) : ℝ := u.1 * v.1 + u.2 * v.2
omit C in
/-- `X` lies strictly inside the counterclockwise arc of directions from `B` to `A`: the convex
case (`A` less than a half-turn from `B`), the reflex case, the half-turn case, and the full-turn
case (`A` in the direction of `B`: every direction except that of `B`). -/
def sideCcw (B X A : Point) : Prop :=
  ztgbt ∨
  ztfuo ∨
  ztgmc ∨
  ztecu
omit C in
theorem sideCross_self (u : Point) : sideCross u u = 0 := by unfold sideCross; ring
omit C in
theorem sideCross_swap (u v : Point) : sideCross v u = -sideCross u v := by unfold sideCross; ring
omit C in
theorem sideDot_comm (u v : Point) : sideDot v u = sideDot u v := by unfold sideDot; ring
omit C in
/-- The Plücker relation for four vectors of the plane. -/
theorem side_plucker (B X Y A : Point) :
    sideCross B X * sideCross Y A = sideCross B Y * sideCross X A + sideCross B A * sideCross Y X := by
  zujqx
omit C in
theorem side_dotCross (B X A : Point) :
    sideDot B X * sideCross B A = sideDot B B * sideCross X A + sideCross B X * sideDot B A := by
  zuhrb
omit C in
theorem side_lagrange (B X : Point) :
    sideCross B X ^ 2 + sideDot B X ^ 2 = sideDot B B * sideDot X X := by
  zuhrb
omit C in
theorem sideDot_self_pos {u : Point} (h : u ≠ 0) : 0 < sideDot u u := by
  unfold sideDot
  zudxc
  zuhrs
  have h1 : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
  have h2 : u.2 = 0 := by_simp_all
  zulxg
omit C in
/-- `B` is not in the direction of `A` (the arc from `B` to `A` is not a full turn). -/
def sideNonSpike (B A : Point) : Prop := ¬ ztkfb
set_option hygiene false
local macro "zqdb" : tactic => `(tactic| (obtain ⟨hx1, hx2⟩ := hx; zvncj at hx1 hx2))
local macro "zqdc" : tactic => `(tactic| (refine C.sideClean_box_edge_aux by_simp_all hne hset hr (fun x hx hxl => ?_); rw [hq, mem_ball_iff_abs] at hx))
local macro "zqdd" : tactic => `(tactic| (have hm3 := min_le_left ztblo ztzau; have hm4 := min_le_right ztblo ztzau))
local macro "zqde" : tactic => `(tactic| (rw [sideLeftOf_iff_pos hdet] at hxl; obtain ⟨h1, h2⟩ := hxl; simp only [det, slitTop, one_mul] at h1 h2 hx))
local macro "zqdf" : tactic => `(tactic| have hnext : ztxao = p + 1 := C.sideWalk_mod_small β by_omega)
local macro "zqdg" : tactic => `(tactic| (refine ⟨r, hr, fun x hx hxd hxl => ?_⟩; rw [sidePt_zero, hcur] at hx; rw [sideLeft_zero, hprev, hcur, hnext] at hxl))
local macro "zqdh" : tactic => `(tactic| rcases C.sideWalk_lt_cases β hp with h5 | ⟨i, hi, rfl⟩ | rfl)
local macro "zqdi" : tactic => `(tactic| apply point_ext <;> simp [lerp, slitTop])
local macro "zqdj" : tactic => `(tactic| apply point_ext <;> zundk)
local macro "zqdk" : tactic => `(tactic| (have hm3 := min_le_left ztzye ztzyx; have hm4 := min_le_right ztzye ztzyx))
local macro "zqdl" : tactic => `(tactic| (by_contra hc; push Not at hc))
local macro "zqdm" : tactic => `(tactic| (refine ⟨i + 6, 0, by rw [sideWalk_n]; omega, le_rfl, one_pos, ?_, ?_⟩))
local macro "zqdn" : tactic => `(tactic| (refine C.sideClean_box hset hr ?_; intro x hx hxl))
local macro "zqdq" : tactic => `(tactic| (have hR := C.radius_pos; have hta := abs_lt.1 C.abs_top_fst_lt_radius; have htop := C.top_snd_lt_radius; have htb := abs_le.1 (C.abs_le_coordBound_of_mem_set C.top_mem_set).2; have hcR := C.coordBound_lt_radius; obtain ⟨ht0, ht1⟩ := ht))
local macro "zqdr" : tactic => `(tactic| refine ⟨C.sideNot_mem_set_of_abs by_grind, ?_⟩)
local macro "zqds" : tactic => `(tactic| rcases hβ with h | h | h)
local macro "zqdt" : tactic => `(tactic| (unfold sideCcw; rintro (⟨h1, h2, h3⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)))
local macro "zqdu" : tactic => `(tactic| (have hle1 := C.sideIdx_le β 1; have hle2 := C.sideIdx_le β ztdl))
local macro "zqdv" : tactic => `(tactic| (have k1 : C.sideIdx β i = j := by zvmwp; unfold sideE; grind))
local macro "zqdw" : tactic => `(tactic| (rw [C.sideLeft_tour_inner β hi0 hi]; unfold sideTour; rw [k1, k2, k3]))
local macro "zqdx" : tactic => `(tactic| (have D := side_dotCross B A X; rw [hbA, zero_mul, add_zero] at D))
local macro "zqdy" : tactic => `(tactic| (refine ⟨r, hr, fun x hx hxd => ?_⟩; rcases h x hx hxd with ⟨j, hj, hkj, hxj⟩ | ⟨hks, hxs⟩))
local macro "zqdz" : tactic => `(tactic| (intro h; have := congrArg Prod.fst h; simp only [slitTop] at this; linarith))
local macro "zqea" : tactic => `(tactic| rw [C.sideWalk_next_tour β hi, C.sideWalk_vtx_tour β hi.le, C.sideWalk_vtx_tour β by_omega])
local macro "zqeb" : tactic => `(tactic| rcases h1 with ⟨hbA, hbX, hxA⟩ | ⟨hbA, hX⟩ | ⟨hbA, hdA, hbX⟩ | ⟨hbA, hdA, hX⟩)
local macro "zqec" : tactic => `(tactic| rcases h1 with ⟨hbA, hbX, hxA⟩ | ⟨hbA, hX1⟩ | ⟨hbA, hdA, hbX⟩ | ⟨hbA, hdA, hX1⟩)
local macro "zqed" : tactic => `(tactic| rcases h2 with ⟨-, hxY, hyA⟩ | ⟨hxA', -⟩ | ⟨hxA', -, -⟩ | ⟨hxA', -, -⟩)
local macro "zqee" : tactic => `(tactic| have hx0 : x ∈ ball _ r0 := ball_subset_ball ztff hx)
local macro "zqef" : tactic => `(tactic| have hm := C.one_le)
local macro "zqeg" : tactic => `(tactic| (zvmyz at hne; generalize ztty % ztbb = j at hne hiT hj; unfold sideE at hiT; grind))
local macro "zqeh" : tactic => `(tactic| (have eBA : ztori := sideCross_swap _ _; have eBX : ztieb := sideCross_swap _ _))
local macro "zqei" : tactic => `(tactic| rcases C.sideTour_step β i with h | h)
local macro "zqej" : tactic => `(tactic| (rw [sidePt_zero, C.sideWalk_vtx_tour β hi.le]; unfold sideTour; rw [k1]))
local macro "zqek" : tactic => `(tactic| (rw [show C.sideIdx β _ = C.sideIdx β i - 1 by omega] at hxl; exact sideLeftOf_not_seg_prev ztswb hxs hxl))
local macro "zqel" : tactic => `(tactic| simp only [det, slitTop] at hxl hx)
local macro "zqem" : tactic => `(tactic| (zvnbk at hss; exact ⟨hsub, hss.2.1, hss.2.2⟩))
local macro "zqen" : tactic => `(tactic| (rw [sideLeftOf_iff_pos hdet] at hxl; obtain ⟨h1, h2⟩ := hxl; simp only [det, one_mul] at h1 h2 hx))
local macro "zqeo" : tactic => `(tactic| obtain ⟨i, hi, h1, h2, h3, h4⟩ := C.sideIdx_visit β (j := j) by_omega)
local macro "zqep" : tactic => `(tactic| rcases Nat.eq_zero_or_pos j with h0 | h0)
local macro "zqeq" : tactic => `(tactic| apply point_ext <;> zundk <;> ring)
local macro "zqer" : tactic => `(tactic| obtain ⟨μ, hμ0, hμ1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx)
local macro "zqes" : tactic => `(tactic| have hm2 := C.two_m_pos)
local macro "zqet" : tactic => `(tactic| have e1 : ztsna := by_nlinarith)
local macro "zqeu" : tactic => `(tactic| rw [C.sideWalk_next_last β, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m, C.sideWalk_vtx_zero])
local macro "zqev" : tactic => `(tactic| (rw [c1, c2, d1, d2]; rintro ⟨h1, h2⟩; rw [Geometry.det_swap12] at h2; linarith))
local macro "zqew" : tactic => `(tactic| (unfold sideCross det; zvnhb; ring))
local macro "zqex" : tactic => `(tactic| rcases hloc x hx hxd with ⟨-, hxs⟩ | ⟨-, hxs⟩ | ⟨hkT, hxs⟩)
local macro "zqey" : tactic => `(tactic| rcases hloc x hx hxd with ⟨h1, hxs⟩ | ⟨h1, hxs⟩ | ⟨-, hxs⟩)
local macro "zqez" : tactic => `(tactic| (simp only [det, slitTop]; nlinarith))
local macro "zqfa" : tactic => `(tactic| (exfalso; have := h3 h0; unfold sideE at this; grind))
local macro "zqfb" : tactic => `(tactic| refine hdis x (ball_subset_ball ztxju hx) ?_ hxl)
local macro "zqfc" : tactic => `(tactic| have hBB := sideDot_self_pos hB)
local macro "zqfd" : tactic => `(tactic| exact Or.inr by_simp_all)
local macro "zqfe" : tactic => `(tactic| rw [segment_comm] at hxs)
local macro "zqff" : tactic => `(tactic| exact lt_of_lt_of_le (mem_ball.1 hx) ztxjv)
local macro "zqfg" : tactic => `(tactic| have hT := C.topIdx_le)
local macro "zqfh" : tactic => `(tactic| rw [C.sideWalk_vtx_zero, show (0 + 1 : ℕ) = 1 from rfl, C.sideWalk_vtx_one])
local macro "zqfi" : tactic => `(tactic| rw [C.sideWalk_vtx_one, show (1 + 1 : ℕ) = 2 from rfl, C.sideWalk_vtx_two])
local macro "zqfj" : tactic => `(tactic| rw [C.sideWalk_vtx_two, show (2 + 1 : ℕ) = 3 from rfl, C.sideWalk_vtx_three])
local macro "zqfk" : tactic => `(tactic| rw [C.sideWalk_vtx_three, show (3 + 1 : ℕ) = 4 from rfl, C.sideWalk_vtx_four])
local macro "zqfl" : tactic => `(tactic| rw [C.sideWalk_vtx_four, show (4 + 1 : ℕ) = 5 from rfl, C.sideWalk_vtx_five])
local macro "zqfm" : tactic => `(tactic| rw [C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 6 from rfl, C.sideWalk_vtx_six])
local macro "zqfn" : tactic => `(tactic| rcases Nat.eq_zero_or_pos i with h0 | h0)
local macro "zqfo" : tactic => `(tactic| (rw [C.sideWalk_next_tour β hi, C.sideWalk_vtx_tour β by_omega]; unfold sideTour; zuotn))
local macro "zqfp" : tactic => `(tactic| rw [show pa + (p - pa) = p by omega, Nat.mod_eq_of_lt hp])
local macro "zqfr" : tactic => `(tactic| rcases lt_or_eq_of_le (show j + 1 ≤ 2 * C.m by omega) with h | h)
local macro "zqfs" : tactic => `(tactic| exact hnb _ by_omega by_omega (hn1 h1) x hxs hxl)
local macro "zqft" : tactic => `(tactic| exact hnb _ ztbt by_omega (hn2 h1) x hxs hxl)
local macro "zqfu" : tactic => `(tactic| have e1 : x.1 < C.radius := by_nlinarith)
local macro "zqfv" : tactic => `(tactic| have hxA : ztgtv := by zuohh)
local macro "zqfw" : tactic => `(tactic| (have hxc : ztsmy := by by_contra h; exact hxD ⟨hxD0, h⟩))
local macro "zqfx" : tactic => `(tactic| have := C.sideVertex_inj hP by_omega by_omega (h1'.symm.trans h2))
local macro "zqfy" : tactic => `(tactic| have hR := C.radius_pos)
local macro "zqfz" : tactic => `(tactic| (zvnck; apply C.sideNot_mem_set_of_abs; right; simp only; zuoqo))
local macro "zqga" : tactic => `(tactic| (intro _ h; refine ⟨by_simp_all, ?_⟩; rcases ht.lt_or_eq with h' | h'))
set_option hygiene true
variable {B A Y : Point} {a v b x : Point} {W : Polygon} {p : ℕ} {t : ℝ} {D : Set Point} {c₀ : Point} {N : ℕ} {D₀ : Set Point} {q : Point}
omit C in
/-- A direction on the closed ray of `A` is not strictly inside an arc ending at `A`. -/
theorem sideCcw_not_ray_right (hA : A ≠ 0) (hY : sideCross Y A = 0)
    (hYd : 0 ≤ sideDot Y A) : ¬ sideCcw B Y A := by
  zuheb
  -- `B × Y` is a nonnegative multiple of `B × A`
  have e1 : sideDot A A * sideCross B Y = sideDot Y A * sideCross B A := by
    zujqw
  zqdt
  · simp_all
  · zukkb
  · simp_all
  · zuiig
    have : ztsmh := by
      grind
    simp_all
  · zuiig
    have hBY : ztsmh := by
      grind
    -- `B · Y ≥ 0`
    have e2 : sideDot A A * sideDot B Y = sideDot Y A * sideDot B A := by
      zujqw
    zujh
    · simp_all
    · nlinarith [mul_nonneg hYd h2.le]
omit C in
theorem side_dotDot (B Y A : Point) :
    sideDot B Y * sideDot B A + sideCross B Y * sideCross B A = sideDot B B * sideDot Y A := by
  zuhrb
omit C in
/-- A direction on the closed ray of `B` is not strictly inside an arc starting at `B`. -/
theorem sideCcw_not_ray_left (hB : B ≠ 0) (hY : sideCross B Y = 0)
    (hYd : 0 ≤ sideDot B Y) : ¬ sideCcw B Y A := by
  zqfc
  have e1 := side_dotCross B Y A
  rw [hY, zero_mul, add_zero] at e1
  zqdt
  · simp_all
  · simp_all
  · zukkb
  · simp_all
  grind
omit C in
/-- **Sub-arc (left part).**  If `X` is inside the arc from `B` to `A`, the arc from `B` to `X`
is contained in it. -/
theorem sideCcw_sub_left {B X Y A : Point} (hB : B ≠ 0) (h1 : sideCcw B X A)
    (h2 : sideCcw B Y X) : sideCcw B Y A := by
  zqfc
  zuhvn
  have D1 := side_dotCross B X A
  zqeb
  · rcases h2 with ⟨-, hbY, hyX⟩ | ⟨hbX', -⟩ | ⟨hbX', -, -⟩ | ⟨hbX', -, -⟩
    · refine Or.inl ⟨hbA, hbY, ?_⟩
      zqdl
      nlinarith [mul_pos hbY hxA, mul_pos hbA hyX, mul_nonpos_of_nonneg_of_nonpos hbX.le hc]
    · linarith
    · linarith
    simp_all
  · refine Or.inr ztoxh
    rcases h2 with ⟨-, hbY, -⟩ | ⟨hbX, h2⟩ | ⟨-, -, hbY⟩ | ⟨hbX, hdX, -⟩
    · simp_all
    · rcases h2 with hbY | hyX
      · simp_all
      · by_cases hbY : 0 < sideCross B Y
        · simp_all
        · push Not at hbY
          right
          have hxA : ztgtv := by
            grind
          zqdl
          nlinarith [mul_nonpos_of_nonpos_of_nonneg hbY hxA.le, mul_pos ztkbj hyX,
            mul_nonneg (neg_pos.2 hbX).le ztqtv]
    · simp_all
    · exfalso
      have hxA : ztgtv := by
        simp_all
      rw [hbX, zero_mul, add_zero] at D1
      nlinarith [mul_pos hdX ztkbj, mul_pos hBB hxA]
  · rcases h2 with ⟨-, hbY, -⟩ | ⟨hbX', -⟩ | ⟨hbX', -, -⟩ | ⟨hbX', -, -⟩
    · zqfd
    · linarith
    · linarith
    simp_all
  · refine Or.inr ztjkt
    zqdl
    exact sideCcw_not_ray_left hB hc.1 hc.2 h2
omit C in
/-- **Sub-arc (right part).**  If `X` is inside the arc from `B` to `A`, the arc from `X` to `A`
is contained in it. -/
theorem sideCcw_sub_right {B X Y A : Point} (hB : B ≠ 0) (hX : X ≠ 0) (hA : A ≠ 0)
    (h1 : sideCcw B X A) (h2 : sideCcw X Y A) : sideCcw B Y A := by
  zqfc
  have hXX := sideDot_self_pos hX
  zuheb
  zuhvn
  zqec
  · zqed
    · refine Or.inl ⟨hbA, ?_, hyA⟩
      zufhi
      zqdl
      nlinarith [mul_pos hbX hyA, mul_neg_of_pos_of_neg hbA hxY',
        mul_nonpos_of_nonpos_of_nonneg hc hxA.le]
    · linarith
    · linarith
    simp_all
  · refine Or.inr ztoxh
    rcases h2 with ⟨-, -, hyA⟩ | ⟨hxA, h2⟩ | ⟨hxA, hdXA, hxY⟩ | ⟨hxA, hdXA, -⟩
    · simp_all
    · have hbX : ztrzl := by
        grind
      rcases h2 with hxY | hyA
      · by_cases hyA : 0 < sideCross Y A
        · simp_all
        · push Not at hyA
          left
          have hyX : ztmws := by rw [sideCross_swap]; linarith
          zqdl
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hbX.le hyA, mul_pos ztkbj
            (neg_pos.2 hyX), mul_nonneg ztqtv (neg_pos.2 hxA).le]
      simp_all
    · right
      have D := side_dotCross X A Y
      rw [hxA, zero_mul, add_zero] at D
      have e : sideCross A Y = -sideCross Y A := sideCross_swap _ _
      zukrb
      nlinarith [mul_neg_of_neg_of_pos hdXA hxY]
    · exfalso
      have hbX : ztrzl := by
        simp_all
      have D := side_dotCross A X B
      have e1 : ztfdr := sideCross_swap _ _
      have e2 : ztori := sideCross_swap _ _
      have e3 : ztieb := sideCross_swap _ _
      have e4 : sideDot A X = sideDot X A := sideDot_comm _ _
      rw [e1, e2, e3, e4, hxA] at D
      nlinarith [mul_pos hdXA ztkbj]
  · zqdx
    have e : ztfdr := sideCross_swap _ _
    zukrb
    zqfv
    zqed
    · refine Or.inr (Or.inr (Or.inl ⟨hbA, hdA, ?_⟩))
      zufhi
      rw [hbA, zero_mul, add_zero] at P1
      zqdl
      nlinarith [mul_pos hbX hyA, mul_nonpos_of_nonpos_of_nonneg hc hxA.le]
    · linarith
    · linarith
    simp_all
  · refine Or.inr ztjkt
    zqdl
    obtain ⟨hbY, hdY⟩ := hc
    have D := side_dotCross B Y A
    rw [hbA, mul_zero, hbY, zero_mul, add_zero] at D
    have hyA : sideCross Y A = 0 := by
      grind
    have DD := side_dotDot B Y A
    rw [hbY, zero_mul, add_zero] at DD
    have hdYA : 0 ≤ sideDot Y A := by nlinarith [mul_nonneg hdY hdA.le]
    exact sideCcw_not_ray_right hA hyA hdYA h2
omit C in
/-- **Complementary arcs are disjoint** (unless the arc is a full turn). -/
theorem sideCcw_asymm {B X A : Point} (hB : B ≠ 0) (hns : sideNonSpike B A)
    (h1 : sideCcw B X A) : ¬ sideCcw A X B := by
  zqfc
  zqeh
  zuhvv
  zukji
  zqeb
  · rcases h2 with ⟨h, -, -⟩ | ⟨-, h | h⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
    · linarith
    · linarith
    · linarith
    · linarith
    simp_all
  · rcases h2 with ⟨-, h, h'⟩ | ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
    · grind
    · linarith
    · linarith
    simp_all
  · zqdx
    rcases h2 with ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
    · linarith
    · linarith
    · zuohh
    · rw [sideDot_comm] at h; linarith
  tauto
omit C in
/-- **Rotation**: if `X` is inside the arc from `B` to `A`, then `A` is inside the arc from `X`
to `B` (unless the arc is a full turn). -/
theorem sideCcw_rotate {B X A : Point} (hB : B ≠ 0) (hX : X ≠ 0) (hns : sideNonSpike B A)
    (h1 : sideCcw B X A) : sideCcw X A B := by
  zqfc
  have hXX := sideDot_self_pos hX
  zqeh
  zqec
  · zqfd
  · rcases lt_trichotomy (sideCross B X) 0 with hbX | hbX | hbX
    · have hxA : ztgtv := by
        grind
      zudxj
    · have hxA : ztgtv := by
        simp_all
      have D := side_dotCross B X A
      rw [hbX, zero_mul, add_zero] at D
      have hL := side_lagrange B X
      rw [hbX] at hL
      rcases lt_trichotomy (sideDot X B) 0 with hd | hd | hd
      · zqfd
      · exfalso
        zugfi
        zvnej at hL
        nlinarith [mul_pos hBB hXX]
      · exfalso
        zugfi
        nlinarith [mul_pos hd ztkbj, mul_pos hBB hxA]
    · zqfd
  · zqdx
    zuhvv
    rw [eXA] at D
    zqfv
    zqfd
  · exact absurd by_simp_all hns

/-! ### Left sectors at a corner -/
omit C in
/-- `x` lies in the open left sector of the corner `a → v → b`: the direction of `x - v` is
strictly inside the counterclockwise arc from the direction of `b - v` to that of `a - v`. -/
def sideLeftOf (a v b x : Point) : Prop := sideCcw ztfd ztsq ztgg
omit C in
theorem sideCross_corner (a v b : Point) : sideCross ztfd ztgg = det a v b := by
  zqew
omit C in
theorem sideCross_out (v b x : Point) : sideCross ztfd ztsq = det v b x := by
  zqew
omit C in
theorem sideCross_in (a v x : Point) : sideCross ztsq ztgg = det a v x := by
  zqew
omit C in
theorem sub_ne_zero_of_ne' {a v : Point} (h : a ≠ v) : a - v ≠ 0 := sub_ne_zero.2 h
omit C in
/-- Left sector of a left turn: the intersection of the two left half-planes. -/
theorem sideLeftOf_iff_pos (h : 0 < det a v b) :
    sideLeftOf a v b x ↔ 0 < 1 * det a v x ∧ 0 < 1 * det v b x := by
  zueez
  rw [sideCross_corner a v b, sideCross_out v b x, sideCross_in a v x, one_mul, one_mul]
  grind
omit C in
/-- Left sector of a right turn: the union of the two left half-planes. -/
theorem sideLeftOf_iff_neg (h : det a v b < 0) :
    sideLeftOf a v b x ↔ 0 < (-1) * det b v x ∨ 0 < (-1) * det v a x := by
  zueez
  rw [sideCross_corner a v b, sideCross_out v b x, sideCross_in a v x]
  have e1 : det b v x = -det v b x := Geometry.det_swap12 _ _ _
  have e2 : det v a x = -det a v x := Geometry.det_swap12 _ _ _
  grind
omit C in
/-- Left sector of a straight corner: the left half-plane. -/
theorem sideLeftOf_iff_zero (hbv : b ≠ v) (h : det a v b = 0)
    (hd : sideDot ztfd ztgg < 0) : sideLeftOf a v b x ↔ 0 < 1 * det a v x := by
  zulho
  have D := side_dotCross ztfd ztsq ztgg
  rw [sideCross_corner a v b, h, mul_zero, sideCross_out v b x, sideCross_in a v x] at D
  zueez
  rw [sideCross_corner a v b, sideCross_out v b x, sideCross_in a v x, h, one_mul]
  constructor
  · zubjr
    · simp_all
    · simp_all
    · nlinarith [mul_pos h3 (neg_pos.2 hd)]
    grind
  · zudqd
    refine Or.inr (Or.inr (Or.inl ⟨rfl, hd, ?_⟩))
    zqdl
    nlinarith [mul_pos hBB h1, mul_nonneg ztqtv (neg_pos.2 hd).le]
omit C in
/-- **Sector lemma.**  At a corner `a → v → b` with `a ≠ v ≠ b`, if no point of `S` near `v`
lies in the open left sector, then the left sector near `v` is a preconnected set avoiding `S`
which contains the left offset points of both edges near `v` (including the full-turn case
`a = b`). -/
theorem sideSector {a v b : Point} (hav : a ≠ v) (hbv : b ≠ v) {S : Set Point} {r : ℝ}
    (hr : 0 < r) (hS : ∀ x ∈ ball v r, x ∈ S → ¬ sideLeftOf a v b x) :
    SectorSide S (ball v r ∩ {x | sideLeftOf a v b x}) a v b 1 := by
  have hsub : ball v r ∩ {x | sideLeftOf a v b x} ⊆ Sᶜ := by_grind
  have hS0 : ∀ x ∈ ball v r, x ∈ (∅ : Set Point) →
      x ∈ Chazelle.segment a v ∨ x ∈ Chazelle.segment v b := by_simp_all
  zugsf
  · zufhb
    have hS0' : ∀ x ∈ ball v r, x ∈ (∅ : Set Point) →
        x ∈ Chazelle.segment b v ∨ x ∈ Chazelle.segment v a := by_simp_all
    have hss := (sectorSide_pos_right hpos' hbv hav.symm hr hS0').reverse
    rw [neg_neg] at hss
    have heq : (ball v r ∩ {x | 0 < (-1) * det b v x}) ∪ (ball v r ∩ {x | 0 < (-1) * det v a x}) =
        ball v r ∩ {x | sideLeftOf a v b x} := by
      zumx
      simp only [mem_union, mem_inter_iff, mem_ofPred_eq, sideLeftOf_iff_neg hneg]
      tauto
    zqem
  · by_cases hd : sideDot ztfd ztgg < 0
    · have hdir : 0 < ztdin * ztry + ztdio * ztcet := by
        unfold sideDot at hd; zvnhb at hd; linarith
      have hss := sectorSide_zero hzero hdir hav hr hS0 one_ne_zero
      have heq : ball v r ∩ {x | 0 < 1 * det a v x} = ball v r ∩ {x | sideLeftOf a v b x} := by
        zumx
        simp only [mem_inter_iff, mem_ofPred_eq, sideLeftOf_iff_zero hbv hzero hd]
      zqem
    · -- the full turn: `b` in the direction of `a`
      zumil
      zulho
      set B : Point := b - v with hB
      have hL := side_lagrange B ztgg
      rw [sideCross_corner, hzero] at hL
      have hAA := sideDot_self_pos ztwfi
      have hdpos : 0 < sideDot B ztgg := by
        rcases hd.lt_or_eq with h | h
        · zubh
        · exfalso; zvmzi at hL; nlinarith [mul_pos hBB hAA]
      have hspike : ∀ x, sideLeftOf a v b x ↔ (sideCross B ztsq ≠ 0 ∨ sideDot B ztsq < 0) := by
        zugop
        zueez
        rw [sideCross_corner a v b, hzero]
        simp_all
      -- the three convex pieces
      set J : Point := (-B.2, B.1) with hJ
      have hcrossJ : ∀ x : Point, sideCross B _ = det v b x := (sideCross_out v b)
      have hdotJ : ∀ x : Point, sideDot B ztsq = -det v ztojg x := by
        intro x; unfold sideDot det; simp only [hJ, hB, Prod.fst_sub, Prod.snd_sub,
          Prod.fst_add, Prod.snd_add]; ring
      set H1 : Set Point := ball v r ∩ {x | 0 < 1 * det v b x}
      set H2 : Set Point := ball v r ∩ {x | 0 < (-1) * det v b x}
      set F : Set Point := ball v r ∩ {x | 0 < 1 * det v ztojg x}
      have hU : ball v r ∩ {x | sideLeftOf a v b x} = ztsxv ∪ ztsxw := by
        zumx
        simp only [H1, H2, F, mem_union, mem_inter_iff, mem_ofPred_eq, hspike, hcrossJ, hdotJ,
          one_mul, neg_one_mul]
        constructor
        · grind
        · rintro ((⟨hx, h⟩ | ⟨hx, h⟩) | (⟨hx, h⟩ | ⟨hx, h⟩))
          · grind
          · grind
          · grind
          grind
      have hcH1 :=
        ((convex_ball v r).inter ztrnv).isPreconnected
      have hcH2 : IsPreconnected H2 :=
        ((convex_ball v r).inter ztrnw).isPreconnected
      have hcF : IsPreconnected F :=
        ((convex_ball v r).inter (convex_det_pos v _ 1)).isPreconnected
      -- common points
      have hBn : 0 < ‖(-B + J : Point)‖ + ‖(-B - J : Point)‖ + 1 := by_positivity
      set ε := r / (‖(-B + J : Point)‖ + ‖(-B - J : Point)‖ + 1) with hε
      have hε0 := div_pos hr hBn
      have hεb : ∀ w : Point, ‖w‖ ≤ ‖(-B + J : Point)‖ + ‖(-B - J : Point)‖ → v + ε • w ∈ ball v r := by
        zucdk
        rw [mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
        calc ε * ‖w‖ ≤ ε * (‖(-B + J : Point)‖ + ‖(-B - J : Point)‖) :=
              mul_le_mul_of_nonneg_left hw hε0.le
          _ < ε * (‖(-B + J : Point)‖ + ‖(-B - J : Point)‖ + 1) := by_nlinarith
          _ = r := div_mul_cancel₀ _ hBn.ne'
      have hdetvb : ∀ w : Point, det v b ztqya = ε * sideCross B w := by
        intro w; unfold det sideCross; simp only [hB, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]; ring
      have hdetJ : ∀ w : Point, det v ztojg ztqya = -(ε * sideDot B w) := by
        intro w; unfold det sideDot; simp only [hJ, hB, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]; ring
      have hcr1 : sideCross B ztldb = sideDot B B := by
        unfold sideCross sideDot; simp only [hJ, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
          Prod.snd_neg]; ring
      have hdt1 : sideDot B ztldb = -sideDot B B := by
        unfold sideDot; simp only [hJ, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]; ring
      have hcr2 : sideCross B ztldc = -sideDot B B := by
        unfold sideCross sideDot; simp only [hJ, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg,
          Prod.snd_neg]; ring
      have hdt2 : sideDot B ztldc = -sideDot B B := by
        unfold sideDot; simp only [hJ, Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]; ring
      have hp1 : v + ε • ztldb ∈ H1 ∩ F := by
        refine ⟨ztrdg,
          ⟨hεb _ by_simp, ?_⟩⟩
        · show 0 < 1 * det v b _
          rw [one_mul, hdetvb, hcr1]; positivity
        · show 0 < 1 * det v _ _
          rw [one_mul, hdetJ, hdt1]; zunnl
      have hp2 : v + ε • ztldc ∈ H2 ∩ F := by
        refine ⟨ztrdg,
          ⟨hεb _ by_simp, ?_⟩⟩
        · show 0 < (-1) * det v b _
          rw [hdetvb, hcr2]; zunnl
        · show 0 < 1 * det v _ _
          rw [one_mul, hdetJ, hdt2]; zunnl
      have hc1 : ztrfr := hcH1.union _ hp1.1 hp1.2 hcF
      have hc2 : ztrfr := hcH2.union _ hp2.1 hp2.2 hcF
      have hc : IsPreconnected (ztsxv ∪ ztsxw) :=
        hc1.union _ ztvck ztvck hc2
      refine ⟨hsub, by_grind, ?_⟩
      -- the offset points
      have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), lerp a v _ ∈ ball v r :=
        (tendsto_lerp_one_sub a v).eventually ztsd
      have h2 :=
        (tendsto_lerp_zero v b).eventually ztsd
      filter_upwards [h1, h2] with s hs1 hs2
      filter_upwards [eventually_offset_mem 1 isOpen_ball hs1,
        eventually_offset_mem 1 isOpen_ball hs2, self_mem_nhdsWithin] with δ hδ1 hδ2 hδ0
      have hδ0' : ztblc := hδ0
      refine ztbabp
      · show sideLeftOf a v b _
        zulpu

        rw [hcrossJ, det_offset_gen, det_lerp, Geometry.det_self_outer]
        have e1 := Geometry.det_cyclic a v b
        have e2 : det v b (v + nrm a v) = -sideDot B ztgg := by
          unfold det nrm sideDot; simp only [hB, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
            Prod.snd_sub]; ring
        rw [e1, hzero, e2]
        have : (1 - zteb) * 0 + zteb * 0 + 1 * δ * -sideDot B ztgg =
            -(δ * sideDot B ztgg) := by_ring
        zubk
        exact neg_ne_zero.2 (mul_pos hδ0' hdpos).ne'
      · show sideLeftOf a v b _
        zulpu

        rw [hcrossJ, det_offset]
        exact (mul_pos by_linarith (sqLen_pos hbv.symm)).ne'
  · have hss := sectorSide_pos_left hpos hav hbv.symm hr hS0
    have heq : ball v r ∩ ztecy =
        ball v r ∩ {x | sideLeftOf a v b x} := by
      zumx
      simp only [mem_inter_iff, mem_ofPred_eq, sideLeftOf_iff_pos hpos]
    zqem

/-! ### Chaining left sides along edges and around corners -/
omit C in
/-- **Parallelogram lemma.**  If near every point of the segment `u v` with parameter in
`[t₁, t₂]` the set `S` lies in the closed right half-plane of `u → v`, then a thin
parallelogram of left offset points over `(t₁, t₂)` avoids `S`. -/
theorem sideEdge_par {u v : Point} (huv : u ≠ v) {S : Set Point} {t₁ t₂ : ℝ}
    (hS : ∀ t ∈ Icc t₁ t₂, ∃ r > 0, ∀ x ∈ ball ztcnw r, x ∈ S → det u v x ≤ 0) :
    ∃ δ₀ > 0, par u v 1 t₁ t₂ δ₀ ⊆ Sᶜ := by
  zueee
  have hKc : IsCompact K := isCompact_Icc.image (Geometry.continuous_lerp u v)
  set O : Set Point := {y | ∃ t ∈ Icc t₁ t₂, ∃ r > 0, y ∈ ball ztcnw r ∧
    ∀ x ∈ ball ztcnw r, x ∈ S → det u v x ≤ 0} with hO
  have hOo : IsOpen O := by
    zujgz
    rintro y ⟨t, ht, r, hr, hy, hball⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 isOpen_ball y hy
    grind
  have hKO : K ⊆ O := by
    zupc
    obtain ⟨r, hr, hball⟩ := hS t ht
    exact ⟨t, ht, r, hr, mem_ball_self hr, hball⟩
  zufld
  have hden : 0 < ‖nrm u v‖ + 1 := by_positivity
  refine ⟨δ' / (‖nrm u v‖ + 1), by_positivity, ?_⟩
  rintro x ⟨t, δ, ht1, ht2, hδ1, hδ2, rfl⟩ hxS
  have hmem : offset u v t ztckn ∈ thickening δ' K := by
    zuiln

    rw [dist_self_add_left, norm_smul, Real.norm_eq_abs, one_mul, abs_of_pos hδ1]
    calc δ * ‖nrm u v‖ ≤ δ * (‖nrm u v‖ + 1) := by_nlinarith
      _ < δ' / (‖nrm u v‖ + 1) * (‖nrm u v‖ + 1) := mul_lt_mul_of_pos_right hδ2 hden
      _ = δ' := div_mul_cancel₀ _ hden.ne'
  obtain ⟨t', -, r, -, hy, hball⟩ := hthick hmem
  have := hball _ hy hxS
  rw [det_offset, one_mul] at this
  nlinarith [mul_pos hδ1 ztqwq]
omit C in
/-- The left offset points of the segment `u → v` at parameter `t` lie in `K` for all small
offsets. -/
def SideFaces (K : Set Point) (u v : Point) (t : ℝ) : Prop :=
  ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset u v t δ ∈ K
omit C in
/-- **Along an edge.**  If the complement of `D` stays in the closed right half-plane of
`u → v` near the points of parameter in `[t₁, t₂]`, then the left offset points at all
parameters in `(t₁, t₂)` lie in one component of `D`. -/
theorem sideFaces_edge {u v : Point} (huv : u ≠ v) {D : Set Point} {c₀ : Point} {t₁ t₂ t t' : ℝ}
    (hS : ∀ s ∈ Icc t₁ t₂, ∃ r > 0, ∀ x ∈ ball ztlqw r, x ∉ D → det u v x ≤ 0)
    (ht : t ∈ Ioo t₁ t₂) (ht' : t' ∈ Ioo t₁ t₂)
    (h : SideFaces ztbtx u v t) :
    SideFaces ztbtx u v t' := by
  obtain ⟨δ₀, hδ₀, hpar⟩ := sideEdge_par huv (S := Dᶜ) hS
  have hparD : par u v 1 t₁ t₂ δ₀ ⊆ D := by_simp_all
  obtain ⟨δ, hδK, hδ⟩ := (h.and (Ioo_mem_nhdsGT hδ₀)).exists
  have hx : offset u v t _ ∈ par u v 1 t₁ t₂ δ₀ := offset_mem_par ht.1 ht.2 hδ.1 hδ.2
  zvohi at hx
  have hsub : par u v 1 t₁ t₂ δ₀ ⊆ connectedComponentIn D c₀ := by
    rw [connectedComponentIn_eq hδK]
    exact (convex_par u v 1 t₁ t₂ δ₀).isPreconnected.subset_connectedComponentIn hx hparD
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ' hδ'
  have := offset_mem_par (u := u) (v := v) (σ := 1) ht'.1 ht'.2 hδ'.1 hδ'.2
  grind
omit C in
/-- **Around a corner.**  If the left sector at the corner `a → v → b` is joined by a
preconnected set avoiding `Dᶜ`, and the left offset points of `a → v` near `v` lie in a
component of `D`, then so do those of `v → b` near `v`, and the whole sector. -/
theorem sideFaces_corner {a v b : Point} {D U : Set Point} {c₀ : Point}
    (hU : SectorSide Dᶜ U a v b 1)
    (h : ∀ᶠ s in 𝓝[>] (0 : ℝ), SideFaces ztbtx a v zteb) :
    U ⊆ connectedComponentIn D c₀ ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ), SideFaces ztbtx v b s := by
  obtain ⟨hUS, hUc, hoff⟩ := hU
  have hUD : U ⊆ D := by_simp_all
  obtain ⟨s, hs1, hs2⟩ := (hoff.and h).exists
  obtain ⟨δ, hδ1, hδ2⟩ := (hs1.and hs2).exists
  zvohi at hδ1
  have hUK : U ⊆ connectedComponentIn D c₀ := by
    rw [connectedComponentIn_eq hδ2]
    exact hUc.subset_connectedComponentIn hδ1.1 hUD
  refine ⟨hUK, ?_⟩
  zuefs

  grind

/-! ### Positions on a closed walk and their left sectors -/
omit C in
/-- The point of the closed walk `W` at position `(p, t)`: parameter `t` on edge `p`. -/
noncomputable def sidePt (W : Polygon) (p : ℕ) (t : ℝ) : Point :=
  lerp ztbbv ztbajj t
omit C in
/-- The point before position `(p, t)`: the previous vertex if `t = 0` (a vertex of the walk),
the start of edge `p` otherwise. -/
noncomputable def sidePrev (W : Polygon) (p : ℕ) (t : ℝ) : Point :=
  if t = 0 then W.vtx ztbvk else W.vtx p
omit C in
/-- The point after position `(p, t)`: the end of edge `p`. -/
noncomputable def sideNext (W : Polygon) (p : ℕ) : Point := W.vtx ztwjb
omit C in
/-- `x` lies in the open left sector of the walk `W` at position `(p, t)`: the left sector of the
corner `sidePrev → sidePt → sideNext` (for `0 < t < 1` the open left half-plane of edge `p`). -/
def sideLeft (W : Polygon) (p : ℕ) (t : ℝ) (x : Point) : Prop :=
  sideLeftOf ztltl ztia ztevm x
omit C in
/-- Position `(p, t)` is clean for `D`: near its point, no point outside `D` lies in its left
sector. -/
def SideClean (W : Polygon) (D : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  ∃ r > 0, ∀ x ∈ ball ztia r, x ∉ D → ¬ sideLeft W p t x
omit C in
/-- The small left sector of `W` at position `(p, t)` lies in `K`. -/
def SideSectorIn (W : Polygon) (K : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  ∃ r > 0, ∀ x ∈ ball ztia r, sideLeft W p t x → x ∈ K
omit C in
/-- The set `d` **attaches** to the walk `W` at position `(p, t)`: the point of the position lies
on `d`, and the points of `d` near it lie in the open left sector of the walk there. -/
def SideAttach (W : Polygon) (d : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  p < W.n ∧ 0 ≤ t ∧ t < 1 ∧ sidePt W p t ∈ d ∧
    ∃ r > 0, ∀ x ∈ d, x ≠ sidePt W p t → dist x ztia < r → sideLeft W p t x
omit C in
/-- Cyclic betweenness of keys: `x` is strictly between `a` and `b` going up from `a` (and
wrapping around). -/
def sideInArc (a b x : ℝ) : Prop := if a < b then a < x ∧ x < b else zthdj
omit C in
theorem sidePt_zero (W : Polygon) (p : ℕ) : sidePt W p 0 = W.vtx p := by
  zufdr
omit C in
/-- At a vertex position the left sector is that of the corner of the walk. -/
theorem sideLeft_zero (W : Polygon) (p : ℕ) (x : Point) :
    sideLeft W p 0 x ↔
      sideLeftOf (W.vtx ztbvk) ztbbv ztbajj x := by
  zumut
  rw [sidePt_zero, ite_eq_left rfl]
omit C in
/-- At a position inside an edge the left sector is the open left half-plane of the edge. -/
theorem sideLeft_edge (hne : W.vtx p ≠ W.vtx ztwjb)
    (ht : t ∈ Ioo (0 : ℝ) 1) (x : Point) :
    sideLeft W p t x ↔ 0 < det ztbbv ztbajj x := by
  zugyv

  zumut
  rw [ite_eq_right ht.1.ne']
  zucky
  have hvq := (lerp_ne_right hne ht.2).symm
  have h0 : det u ztcnw v = 0 := by
    rw [Geometry.det_lerp_mid, Geometry.det_self_left, Geometry.det_self_right]; ring
  have hd : sideDot (v - lerp u v t) (u - lerp u v t) < 0 := by
    have := sqLen_pos hne
    unfold sideDot sqLen at *
    zvnuo
    nlinarith [mul_pos (mul_pos ht.1 ztwgb) this]
  rw [sideLeftOf_iff_zero hvq h0 hd, one_mul, Geometry.det_lerp_mid, Geometry.det_self_left]
  simp_all
omit C in
/-- From the left offsets at a clean position inside an edge to the whole small sector. -/
theorem sideSectorIn_of_faces {p : ℕ} {t : ℝ}
    (hne : W.vtx p ≠ W.vtx ztwjb) (ht : t ∈ Ioo (0 : ℝ) 1) (hcl : SideClean W D p t)
    (hf : SideFaces ztbtx ztbbv ztbajj t) :
    SideSectorIn W ztbtx p t := by
  obtain ⟨r, hr, hcl⟩ := hcl
  set H : Set Point := ball ztia r ∩ {x | 0 < 1 * det ztbbv ztbajj x}
  have hHc : ztrfq :=
    ((convex_ball _ r).inter zteev).isPreconnected
  have hHD : H ⊆ D := by
    zuh
    zujuk
    apply hcl x hx.1 hxD
    rw [sideLeft_edge hne ht]
    grind
  have hoff : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset ztbbv ztbajj t ztckn ∈ H := by
    filter_upwards [eventually_offset_mem 1 isOpen_ball zteal, self_mem_nhdsWithin]
      with δ hδ hδ0
    refine ztklv
    show 0 < 1 * det _ _ _
    zujhs
    zuyx
    nlinarith [mul_pos hδ0' ztwer]
  obtain ⟨δ, h1, h2⟩ := (hoff.and hf).exists
  zukyb
  have hHK : H ⊆ connectedComponentIn D c₀ := by
    rw [connectedComponentIn_eq h2]
    exact hHc.subset_connectedComponentIn h1 hHD
  refine ⟨r, hr, fun x hx hxl => hHK zthne⟩
  show 0 < 1 * det _ _ _
  rw [one_mul, ← sideLeft_edge hne ht]
  omega
omit C in
/-- Decomposition of an arc of positions: a position strictly between `A = (pa, ta)` and
`B = (pb, tb)` lies on edge `(pa + j) % N` for some `j ≤ L = (pb + N - pa) % N`, after `A` if
`j = 0`, before `B` if `j = L`. -/
theorem sideInArc_cases {N pa pb p : ℕ} {ta tb t : ℝ} (hpa : pa < N) (hpb : pb < N)
    (hp : p < N) (hab : pa ≠ pb) (hta : 0 ≤ ta) (hta1 : ta < 1) (htb : 0 ≤ tb) (htb1 : tb < 1)
    (ht : 0 ≤ t) (ht1 : t < 1) (h : sideInArc ztbf ztbd ztk) :
    ∃ j, j ≤ ztcar % N ∧ p = ztcwf % N ∧ (j = 0 → ta < t) ∧
      (j = ztcar % N → t < tb) := by
  -- natural-number consequences of real key inequalities
  have key1 : ∀ {q r : ℕ} {u w : ℝ}, 0 ≤ u → w < 1 → (q : ℝ) + u < r + w → q ≤ r := by
    intro q r u w hu hw h
    zqdl
    have : (r : ℝ) + 1 ≤ q := by exact_mod_cast hc
    linarith
  have key2 : ∀ {q : ℕ} {u w : ℝ}, (q : ℝ) + u < q + w → u < w := by
    simp
  zujqy
  zujec
  · have hk : (pa : ℝ) + ta < pb + tb := by
      have : (pa : ℝ) + 1 ≤ pb := by exact_mod_cast hlt
      linarith
    rw [ite_eq_left hk] at h
    zubkx
    zuhzq
    zuhzs
    have hL : ztcar % N = pb - pa := by
      rw [show pb + N - pa = (pb - pa) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    refine ztkmh
    · zqfp
    · zuibs

    · zudqf

  · have hk : ¬ ((pa : ℝ) + ta < pb + tb) := by
      grind
    rw [ite_eq_right hk] at h
    have hL : ztcar % N = pb + N - pa := Nat.mod_eq_of_lt by_omega
    rcases h with h1 | h2
    · zuhzq
      refine ztkmh
      · zqfp
      · zuibs

      omega
    · zuhzs
      refine ⟨p + N - pa, by_omega, ?_, ?_, ?_⟩
      · rw [show pa + (p + N - pa) = p + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hp]
      · grind
      · zudqf
omit C in
/-- Along an edge of a walk: if all positions `(q, s)` with `s ∈ (lo, hi)` are clean for `D`,
the left offsets at all parameters in `(lo, hi)` lie in one component of `D`. -/
theorem sideFaces_walk_edge {q : ℕ} {lo hi : ℝ}
    (hne : W.vtx q ≠ W.vtx ztysy) (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hcl : ∀ s ∈ Ioo lo hi, SideClean W D q s) {t : ℝ} (ht : t ∈ Ioo lo hi)
    (hf : SideFaces ztbtx ztvec ztbask t)
    {t' : ℝ} (ht' : t' ∈ Ioo lo hi) :
    SideFaces ztbtx ztvec ztbask t' := by
  set t₁ := (lo + min t t') / 2
  set t₂ := (hi + max t t') / 2
  have h1 : lo < t₁ := by_grind
  have h2 : t₂ < hi := by_grind
  zubnn

  refine sideFaces_edge hne ?_ by_simp_all ztugt hf
  zugg
  have hs' : ztgut := by_grind
  obtain ⟨r, hr, hcl'⟩ := hcl s ztsr
  zumkn
  have := hcl' x hx hxD
  rw [sideLeft_edge hne hs'] at this
  simp_all
omit C in
theorem side_mod_cases {x N : ℕ} (hx : x < 2 * N) :
    (x < N ∧ x % N = x) ∨ (N ≤ x ∧ x % N = x - N) := by
  rcases lt_or_ge x N with h | h
  · zulem
  · zugao
omit C in
theorem side_idx_succ (_hN : 0 < N) (a j : ℕ) :
    (ztdgj % N + 1) % N = ztzva % N := by
  grind
omit C in
theorem side_idx_prev (hN : 0 < N) (a j : ℕ) :
    (ztzva % N + N - 1) % N = ztdgj % N := by
  rw [← side_idx_succ hN]
  have hy := Nat.mod_lt ztdgj hN
  rcases lt_or_eq_of_le (show ztdgj % N + 1 ≤ N by omega) with h | h
  · rw [Nat.mod_eq_of_lt h, show ztdgj % N + 1 + N - 1 = ztdgj % N + N by omega,
      Nat.add_mod_right, Nat.mod_mod]
  · rw [h, Nat.mod_self, show 0 + N - 1 = ztdgj % N by omega, Nat.mod_mod]
omit C in
theorem side_arcLen_pos {N pa pb : ℕ} (hpa : pa < N) (hpb : pb < N) (hab : pa ≠ pb) :
    1 ≤ ztcar % N := by
  rcases side_mod_cases ztect with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
omit C in
theorem side_arcLen_end {N pa pb : ℕ} (hpa : pa < N) (hpb : pb < N) :
    (pa + ztcar % N) % N = pb := by
  rcases side_mod_cases ztect with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · zuczw
    rcases side_mod_cases (show pa + ztcar < 2 * N by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      omega
  · zuczw
    rcases side_mod_cases (show pa + (pb + N - pa - N) < 2 * N by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      omega
omit C in
theorem side_arc_ne_start {N pa j : ℕ} (hpa : pa < N) (hj1 : 1 ≤ j) (hjN : j < N) :
    ztcwf % N ≠ pa := by
  rcases side_mod_cases ztkxr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
omit C in
theorem side_arc_eq_end {N pa pb j : ℕ} (hpa : pa < N) (hpb : pb < N) (hjN : j < N)
    (hLN : ztcar % N < N) (h : ztcwf % N = pb) : j = ztcar % N := by
  have e := side_arcLen_end hpa hpb
  rcases side_mod_cases ztect with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    zvmxx at e hLN ⊢ <;>
    rcases side_mod_cases ztkxr with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    omega
omit C in
/-- **Chaining the left sides of a closed walk along an arc.**  Let `A = (pa, ta)` and
`B = (pb, tb)` be positions of a closed walk `W` on distinct edges, let every other position be
clean for an open set `D`, and suppose the left offsets just after `A` lie in the component `K` of
`D`.  Then the small left sector of every position strictly between `A` and `B` lies in `K`. -/
theorem sideArc_chain (W : Polygon) {D : Set Point} {pa pb : ℕ} {ta tb : ℝ}
    (hnd : ∀ p < W.n, W.vtx p ≠ W.vtx ztwjb)
    (hpa : pa < W.n) (hpb : pb < W.n) (hab : pa ≠ pb) (hta : 0 ≤ ta) (hta1 : ta < 1)
    (htb : 0 ≤ tb) (htb1 : tb < 1)
    (hclean : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → zthja → zthjb →
      SideClean W D p t)
    {c₀ : Point}
    (hstart : ∃ s₀ > 0, ∀ s ∈ Ioo 0 s₀,
      SideFaces ztbtx ztveb ztkqm (ta + s)) :
    ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc ztbf ztbd ztk →
      SideSectorIn W ztbtx p t := by
  have hN0 : ztmsm := by_omega
  obtain ⟨L, hL⟩ : ∃ L, L = (pb + W.n - pa) % W.n := by_grind
  have hLlt := hL ▸ Nat.mod_lt _ hN0
  have hL1 := hL ▸ side_arcLen_pos hpa hpb hab
  have hDL := hL ▸ side_arcLen_end hpa hpb
  have hD0 : zteuk % W.n = pa := by zvncl; exact Nat.mod_eq_of_lt hpa
  have hDlt : ∀ j, ztcwf % W.n < W.n := fun j => Nat.mod_lt _ hN0
  have hDne : ∀ j, 1 ≤ j → j ≤ L → ztcwf % W.n ≠ pa := fun j h1 h2 =>
    side_arc_ne_start hpa h1 by_omega
  have hDpb : ∀ j, j ≤ L → ztcwf % W.n = pb → j = L := fun j hj h => by
    zvnlm; exact side_arc_eq_end hpa hpb by_omega by_omega h
  -- the base edge `pa` after `ta`
  have hbase : ∀ t ∈ Ioo ta 1, SideFaces ztbtx ztveb
      ztkqm t := by
    obtain ⟨s₀, hs₀, hstart⟩ := hstart
    obtain ⟨s, hs⟩ : ∃ s, s = min s₀ (1 - ta) / 2 := by_grind
    have hs0 : ztxx := by zvmyz; positivity
    have hss : s < s₀ := by zvmyz; have := min_le_left s₀ ztsqr; linarith
    have hs1 : s < 1 - ta := by zvmyz; have := min_le_right s₀ ztsqr; linarith
    zucj
    have hcl : ∀ s' ∈ Ioo ta 1, SideClean W D pa s' := fun s' hs' =>
      hclean pa hpa s' (by linarith [hs'.1]) hs'.2 (fun _ => ne_of_gt hs'.1)
        by_omega
    exact sideFaces_walk_edge by_grind hta le_rfl hcl ztbcx
      (hstart s ⟨hs0, hss⟩) ht
  -- the induction along the arc
  have hstep : ∀ j, 1 ≤ j → j ≤ L → (j < L ∨ 0 < tb) →
      SideSectorIn W ztbtx ztysn 0 ∧
        ∀ t ∈ Ioo 0 (if j < L then (1 : ℝ) else tb),
          SideFaces ztbtx (W.vtx ztysn)
            (W.vtx ((ztcwf % W.n + 1) % W.n)) t := by
    intro j hj1
    induction j with
    | zero => omega
    | succ i ih =>
      intro hjL hcase
      -- the edge before the vertex
      have hprev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
          SideFaces ztbtx (W.vtx ztmzk)
            (W.vtx (((pa + i) % W.n + 1) % W.n)) zteb := by
        rcases Nat.eq_zero_or_pos i with hi0 | hi0
        · zufpy
          rw [hD0]
          filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hta1)] with s hs
          exact hbase _ ztexq
        · have hi := (ih hi0 by_omega by_omega).2
          rw [ite_eq_left by_grind] at hi
          zuhur
          exact hi _ ztexq
      rw [side_idx_succ hN0] at hprev
      -- the corner
      have hcl0 : SideClean W D _ 0 :=
        hclean _ ztmkn 0 le_rfl one_pos ztjvv
          (fun h => by
            have := hDpb _ hjL h
            grind)
      obtain ⟨r, hr, hcl0⟩ := hcl0
      have hne1 : W.vtx ztmzk ≠ W.vtx (ztzxn % W.n) := by
        have := hnd _ (hDlt i); grind
      have hne2 : W.vtx _ ≠ W.vtx ((ztzxn % W.n + 1) % W.n) :=
        hnd _ ztmkn
      have hsec := sideSector hne1 hne2.symm hr (fun x hx hxS => by
        have := hcl0 x (by rw [sidePt_zero]; exact hx) hxS
        rwa [sideLeft_zero, side_idx_prev hN0] at this)
      obtain ⟨hUK, hnext⟩ := sideFaces_corner hsec hprev
      refine ⟨⟨r, hr, fun x hx hxl => hUK ⟨by rw [sidePt_zero] at hx; exact hx, ?_⟩⟩, ?_⟩
      · rw [sideLeft_zero, side_idx_prev hN0] at hxl; tauto
      · have hhi : (0 : ℝ) < zthyg := by
          zus
          · simp
          grind
        have hhi1 : zthyg ≤ 1 := by
          split_ifs
          · simp
          grind
        obtain ⟨s, hs1, hs2⟩ := (hnext.and (Ioo_mem_nhdsGT hhi)).exists
        zucj
        refine sideFaces_walk_edge hne2 le_rfl hhi1 ?_ hs2 hs1 ht
        intro s' hs'
        refine hclean _ ztmkn s' hs'.1.le (lt_of_lt_of_le hs'.2 hhi1)
          ztjvv ztep
        have := hDpb _ hjL h
        rw [ite_eq_right (show ¬ (i + 1 < L) by omega)] at hs'
        exact hs'.2.ne
  -- conclusion
  intro p hp t ht ht1 harc
  obtain ⟨j, hjL, hpj, hj0, hjL'⟩ := sideInArc_cases hpa hpb hp hab hta hta1 htb htb1 ht ht1 harc
  rw [← hL] at hjL hjL'
  subst hpj
  rcases ht.lt_or_eq with htpos | htz
  · -- inside an edge
    have hclp : SideClean W D ztysn t := by
      refine hclean _ ztmkn t ht ht1 ztep ztep
      · zqep
        · grind
        · exact absurd h (hDne j h0 hjL)
      · exact (hjL' (hDpb j hjL h)).ne
    zqep
    · zubvi
      have hf := hbase t ⟨hj0 rfl, ht1⟩
      rw [← hD0] at hf
      zujvk
    · have hcase : ztpoy := by
        grind
      have hf := (hstep j h0 hjL hcase).2 t ⟨htpos, by
        zus
        · omega
        grind⟩
      zujvk
  · -- a vertex
    subst htz
    zqep
    · grind
    · have hcase : ztpoy := by
        grind
      exact (hstep j h0 hjL hcase).1
omit C in
/-- The circular order depends only on the direction of the middle vector. -/
theorem sideCcw_smul {B X A : Point} {ε : ℝ} (hε : 0 < ε) :
    sideCcw B ztkhu A ↔ sideCcw B X A := by
  have e1 : sideCross B ztkhu = ε * sideCross B X := by
    zubsv
  have e2 : sideCross ztkhu A = ε * sideCross X A := by
    zubsv
  have e3 : sideDot B ztkhu = ε * sideDot B X := by
    zuenx
  have hpos : ∀ x : ℝ, 0 < ε * x ↔ 0 < x := by_simp_all
  have hneg : ∀ x : ℝ, ε * x < 0 ↔ x < 0 := fun x => by
    constructor
    · intro h; by_contra h'; push Not at h'; nlinarith
    · intro h; nlinarith
  have hne : ∀ x : ℝ, ε * x ≠ 0 ↔ x ≠ 0 := fun x => by
    grind
  zufqe
  zuihm
  simp only [hpos, hneg, hne]
omit C in
/-- Reparametrising offsets on a final piece of a segment. -/
theorem offset_lerp_left (u v : Point) (t s δ : ℝ) :
    offset ztcnw v s δ = offset u v ztwlx ztxlw := by
  apply point_ext <;> simp only [offset_fst, offset_snd, lerp_fst, lerp_snd] <;> ring
omit C in
/-- **Cutting the walk at an attachment.**  Let the segment `c = [q, q']` (`q ≠ q'`) attach to
the walk `W` at the position `A = (p, t)` of point `q`, and let `A` be clean for `D₀`.  Then
there is a component `K` of `D₀ \ c` containing the left offsets of the walk just after `A` and
the left offsets of `q' → q` near `q`. -/
theorem sideCut {p : ℕ} {t : ℝ} {q' : Point}
    (hA : SideAttach W (Chazelle.segment ztia q') p t) (hq : sidePt W p t ≠ q')
    (hne : W.vtx p ≠ W.vtx ztwjb) (hcl : SideClean W D₀ p t) :
    ∃ c₀ : Point,
      (∃ s₀ > 0, ∀ s ∈ Ioo 0 s₀,
        SideFaces ztyel
          ztbbv ztbajj ztuf) ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        SideFaces ztyel
          q' ztia zteb := by
  set q := sidePt W p t with hqdef
  set c := Chazelle.segment q q' with hc
  zuins
  obtain ⟨hp, ht0, ht1, -, ra, hra, hatt⟩ := hA
  obtain ⟨rc, hrc, hcl⟩ := hcl
  have hnext : sideNext W p ≠ q := by
    unfold sideNext; zuoto; unfold sidePt
    zuiso
  -- the direction of `c` is in the left sector at `A`
  have hdir : sideCcw (sideNext W p - q) ztcod (sidePrev W p t - q) := by
    set ε := min ra 1 / (2 * (‖q' - q‖ + 1)) with hε
    have hε0 : ztbad := by
      positivity
    have hεx : q + ε • ztcod ∈ c := by
      zuktp
      refine ⟨ε, hε0.le, ?_, ?_⟩
      · rw [hε, div_le_one by_positivity]
        have := min_le_right ra 1
        zulnu
      rfl
    have hεne : q + ε • ztcod ≠ q := by
      zuq
      have : ε • ztcod = 0 := by
        grind
      rcases smul_eq_zero.1 this with h1 | h1
      · simp_all
      grind
    have hεd : dist (q + ε • ztcod) q < ra := by
      rw [dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
      have hden : 0 < 2 * (‖q' - q‖ + 1) := by_positivity
      calc ε * ‖q' - q‖ < ε * (2 * (‖q' - q‖ + 1)) := by
            zulnu
        _ = min ra 1 := by zunbb; field_simp
        _ ≤ ra := min_le_left ra 1
    have := hatt _ hεx hεne hεd
    unfold sideLeft sideLeftOf at this
    rw [show q + ε • ztcod - q = ε • ztcod by abel, sideCcw_smul hε0] at this
    omega
  -- the sector of the sub-corner `q' → q → next`
  have hsec : SectorSide Dᶜ (ball q rc ∩ {x | sideLeftOf q' q ztevm x}) q' q
      ztevm 1 := by
    refine sideSector hq.symm hnext hrc ?_
    zulnp
    by_cases hx0 : x ∈ D₀
    · have hxc : ztsmy := by
        simp_all
      -- `x` on the chord: its direction is that of `q'`
      obtain ⟨μ, hμ0, hμ1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hxc
      apply sideCcw_not_ray_right by_grind ?_ ?_ hxl
      · have e : ztygs := by
          zqdj
        zvmwe; unfold sideCross; zumzm; ring
      · have e : ztygs := by
          zqdj
        zvmwe; unfold sideDot; zumzm
        nlinarith [sq_nonneg (q' - q).1, sq_nonneg (q' - q).2]
    · apply hcl x hx hx0
      exact sideCcw_sub_left (sub_ne_zero_of_ne' hnext) hdir hxl
  obtain ⟨hUS, hUc, hoff⟩ := hsec
  have hUD : ball q rc ∩ {x | sideLeftOf q' q _ x} ⊆ D :=
    fun x hx => by simpa using hUS hx
  obtain ⟨s, hs⟩ := hoff.exists
  obtain ⟨δ, hδ⟩ := hs.exists
  set c₀ := offset q' q _ _ with hc₀
  have hUK : ball q rc ∩ {x | sideLeftOf q' q _ x} ⊆ connectedComponentIn D c₀ :=
    hUc.subset_connectedComponentIn hδ.1 hUD
  refine ⟨c₀, ?_, ?_⟩
  · -- the walk just after `A`, reparametrised
    obtain ⟨s₁, hs₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hoff
    have h1t := sub_pos.2 ht1
    refine ⟨s₁ * ztca, mul_pos (mem_Ioi.1 hs₁) h1t, fun s' hs' => ?_⟩
    have hs'' : s' / ztca ∈ Ioo 0 s₁ :=
      ⟨div_pos hs'.1 h1t, (div_lt_iff₀ h1t).2 hs'.2⟩
    have hev := hsub hs''
    obtain ⟨δ₁, hδ₁, hsubδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨δ₁ * ztca, mul_pos (mem_Ioi.1 hδ₁) h1t,
      fun δ' hδ' => ?_⟩
    have hδ'' : δ' / ztca ∈ Ioo 0 δ₁ :=
      ⟨div_pos hδ'.1 h1t, (div_lt_iff₀ h1t).2 hδ'.2⟩
    have := (hsubδ hδ'').2
    zucqb
    have e : offset q ztevm (s' / ztca) (δ' / ztca) =
        offset ztbbv ztbajj ztubs δ' := by
      zuoto; unfold sidePt sideNext
      rw [offset_lerp_left]
      zucr
      · field_simp
      · field_simp
    zudtu
    tauto
  · zuefs

    zukyc
    tauto
omit C in
theorem sideNext_ne_pt (hne : W.vtx p ≠ W.vtx ztwjb)
    (ht1 : t < 1) : sideNext W p ≠ sidePt W p t := by
  unfold sideNext sidePt
  zuiso
omit C in
/-- The point of a position is not in its own open left sector. -/
theorem sideLeft_not_self (hne : W.vtx p ≠ W.vtx ztwjb)
    (ht1 : t < 1) : ¬ sideLeft W p t ztia := by
  zuhrd
  rw [sub_self]
  exact sideCcw_not_ray_left (sub_ne_zero_of_ne' (sideNext_ne_pt hne ht1))
    (by unfold sideCross; simp) (by unfold sideDot; simp)
omit C in
/-- The left offsets of a segment whose open part lies in the open set `D₀` all lie in one
component of `D₀ \ segment`. -/
theorem sideFaces_chord (hD₀ : IsOpen D₀) {a b : Point} (hab : a ≠ b)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ D₀) {c₀ : Point} {t t' : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (h : SideFaces ztzvi a b t) :
    SideFaces ztzvi a b t' := by
  set t₁ := min t t' / 2
  set t₂ := (max t t' + 1) / 2
  have h1 : 0 < t₁ := by_grind
  have h2 : ztpqf := by_grind
  zubnn

  refine sideFaces_edge hab ?_ by_simp_all ztugt h
  zugg
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hD₀ _ (hopen s ztsr)
  zumkn
  have hxc : x ∈ Chazelle.segment a b := by
    grind
  exact (Geometry.det_eq_zero_of_mem_segment hxc).le
omit C in
/-- **Splitting a closed walk by a chord (generic form of the side-aware Lemma 2.1).**
Let `W` be a closed walk with nondegenerate edges, `D₀` an open set avoiding the walk in which
every position of `W` is clean, and `c = [a, b]` a segment whose open part lies in `D₀`, meeting
the walk only at `a` and `b`, attached to the walk at positions `A` (point `a`) and `B` (point
`b`).  Suppose that the other positions at `a` (resp. `b`) have left sectors disjoint near `a`
(resp. `b`) from that of `A` (resp. `B`), and that the two sides of `c` at its midpoint lie in
different components of `D₀ \ c`.  Then there are two distinct components `K₁ ≠ K₂` of
`D₀ \ c` such that the small left sector of every position strictly between `A` and `B` lies in
`K₁`, and that of every position strictly between `B` and `A` lies in `K₂`; moreover `K₁` is on
the left of `b → a` and `K₂` on the left of `a → b` (at the midpoint of `c`). -/
theorem sideArc_split (W : Polygon) {D₀ : Set Point} (hD₀ : IsOpen D₀) {a b : Point}
    (hab : a ≠ b) (hnd : ∀ p < W.n, W.vtx p ≠ W.vtx ztwjb)
    (htrace : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → sidePt W p t ∉ D₀)
    (hclean0 : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → SideClean W D₀ p t)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ D₀)
    {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach W ztemf pa ta) (hAa : sidePt W pa ta = a)
    (hB : SideAttach W ztemf pb tb) (hBb : sidePt W pb tb = b)
    (hdisjA : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → zthja → sidePt W p t = a →
      ∃ r > 0, ∀ x ∈ ball a r, sideLeft W pa ta x → ¬ sideLeft W p t x)
    (hdisjB : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → zthjb → sidePt W p t = b →
      ∃ r > 0, ∀ x ∈ ball b r, sideLeft W pb tb x → ¬ sideLeft W p t x)
    (hsep : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      connectedComponentIn ztdkw ztzgp ≠
        connectedComponentIn ztdkw ztzgq) :
    ∃ K₁ K₂ : Set Point, K₁ ≠ K₂ ∧
      (∃ c₁, K₁ = connectedComponentIn ztdkw c₁) ∧
      (∃ c₂, K₂ = connectedComponentIn ztdkw c₂) ∧
      (∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc ztbf ztbd ztk →
        SideSectorIn W K₁ p t) ∧
      (∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc ztbd ztbf ztk →
        SideSectorIn W K₂ p t) ∧
      SideFaces K₁ b a ztcn ∧ SideFaces K₂ a b ztcn := by
  set c := Chazelle.segment a b with hc
  zuins
  obtain ⟨hpa, hta, hta1, haA, ra, hra, hattA⟩ := hA
  obtain ⟨hpb, htb, htb1, hbB, rb, hrb, hattB⟩ := hB
  -- `A` and `B` are on distinct edges
  have hpab : pa ≠ pb := by
    zuq
    zubst
    have hmid := hopen ztcn ztfm
    apply htrace pa hpa ztmzv by_linarith by_linarith
    have e : sidePt W pa ztmzv = lerp a b ztcn := by
      rw [← hAa, ← hBb]; unfold sidePt
      zqeq
    grind
  -- cleanness for `D`
  have hclean : ∀ p < W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → zthja → zthjb →
      SideClean W D p t := by
    intro p hp t ht ht1 hnA hnB
    obtain ⟨r0, hr0, hcl0⟩ := hclean0 p hp t ht ht1
    by_cases hpc : sidePt W p t ∈ c
    · -- the point is an endpoint of `c`
      have hcpt : sidePt W p t = a ∨ sidePt W p t = b := by
        obtain ⟨μ, hμ0, hμ1, he⟩ := Geometry.mem_segment_iff_lerp.1 hpc
        rcases hμ0.lt_or_eq with hμ0 | hμ0
        · rcases hμ1.lt_or_eq with hμ1 | hμ1
          · exact absurd (he ▸ hopen μ ⟨hμ0, hμ1⟩) by_grind
          · right; rw [he, hμ1, lerp_one]
        · left; rw [he, ← hμ0, lerp_zero]
      rcases hcpt with hq | hq
      · obtain ⟨r1, hr1, hdis⟩ := hdisjA p hp t ht ht1 hnA hq
        refine ⟨min r0 _, lt_min hr0 (lt_min hr1 hra), fun x hx hxD hxl => ?_⟩
        zqee
        rw [hq] at hx
        by_cases hxD0 : x ∈ D₀
        · zqfw
          zudmi
          · -- the point itself is not in any open sector
            grind
          · zqfb
            refine hattA x hxc by_grind ?_
            zuotp
            zqff
        · zufse
      · obtain ⟨r1, hr1, hdis⟩ := hdisjB p hp t ht ht1 hnB hq
        refine ⟨min r0 _, lt_min hr0 (lt_min hr1 hrb), fun x hx hxD hxl => ?_⟩
        zqee
        rw [hq] at hx
        by_cases hxD0 : x ∈ D₀
        · zqfw
          zujud
          · grind
          · zqfb
            refine hattB x hxc by_grind ?_
            rw [hBb]
            zqff
        · zufse
    · -- away from `c`
      obtain ⟨r1, hr1, hball⟩ := Metric.isOpen_iff.1
        (Geometry.isClosed_segment a b).isOpen_compl _ hpc
      refine ⟨min r0 r1, lt_min hr0 hr1, fun x hx hxD hxl => ?_⟩
      zqee
      have hx1 := hball (ball_subset_ball ztgh hx)
      have hxD0 := fun h => hxD ⟨h, hx1⟩
      zufse
  -- cutting at `A` and at `B`
  have hsegA : Chazelle.segment ztrwz b = c := by zuotp
  have hsegB : Chazelle.segment ztrxa a = c := by rw [hBb, hc, segment_comm]
  have hA' : SideAttach W (Chazelle.segment ztrwz b) pa ta :=
    ⟨hpa, hta, hta1, by_grind, ra, hra, by_grind⟩
  have hB' : SideAttach W (Chazelle.segment ztrxa a) pb tb :=
    ⟨hpb, htb, htb1, by_grind, rb, hrb, by_grind⟩
  obtain ⟨c₁, hstart₁, hleft₁⟩ := sideCut hA' by_grind (hnd pa hpa)
    (hclean0 pa hpa ta hta hta1)
  obtain ⟨c₂, hstart₂, hleft₂⟩ := sideCut hB' by_grind (hnd pb hpb)
    (hclean0 pb hpb tb htb htb1)
  rw [hsegA] at hstart₁
  rw [hsegA, hAa] at hleft₁
  rw [hsegB] at hstart₂
  rw [hsegB, hBb] at hleft₂
  -- the two sides of the chord
  have hopen' : ∀ s ∈ Ioo (0 : ℝ) 1, lerp b a s ∈ D₀ := by
    zugg
    have : ztylr := by
      zqeq
    zvmwk; exact hopen _ by_grind
  have hDba : D₀ \ Chazelle.segment b a = D := by_grind
  obtain ⟨s₁, hs₁, hs₁'⟩ := (hleft₁.and ztxgc).exists
  obtain ⟨s₂, hs₂, hs₂'⟩ := (hleft₂.and ztxgc).exists
  have h1 : SideFaces (connectedComponentIn D c₁) b a ztcn := by
    have := sideFaces_chord (c₀ := c₁) hD₀ hab.symm hopen'
      (t := 1 - s₁) (t' := 1 / 2) by_grind
      ⟨by_norm_num, by_norm_num⟩ by_grind
    grind
  have h2 : SideFaces (connectedComponentIn D c₂) a b ztcn :=
    sideFaces_chord hD₀ hab hopen by_grind
      ⟨by_norm_num, by_norm_num⟩ hs₂
  refine ⟨connectedComponentIn D c₁, connectedComponentIn D c₂, ?_, by_grind, by_grind, ?_, ?_,
    h1, h2⟩
  · -- the two sides of the chord are in different components
    obtain ⟨δ, ⟨hδ1, hδ2⟩, hδ3⟩ := ((h1.and h2).and hsep).exists
    zudii
    apply hδ3
    rw [← connectedComponentIn_eq hδ1, ← connectedComponentIn_eq hδ2, heq]
  · exact sideArc_chain W hnd hpa hpb hpab hta hta1 htb htb1 hclean hstart₁
  · exact sideArc_chain W hnd hpb hpa hpab.symm htb htb1 hta hta1
      (fun p hp t ht ht1 hB hA => hclean p hp t ht ht1 hA hB) hstart₂

/-! ### The corrected boundary walk -/
omit C in
/-- The Euler tour of the path `0, 1, …, m` rooted at `0`: tour position `j ≤ 2m` visits vertex
`j` for `j ≤ m` and `2m - j` for `j ≥ m`. -/
def sideE (m j : ℕ) : ℕ := if j ≤ m then j else 2 * m - j

/-- The tour position at which the box block is inserted (the top vertex `T` is visited at the
tour positions `T` and `2m - T`): `T` if `β`, else `2m - T`. -/
noncomputable def sideS (β : Bool) : ℕ := if β then C.topIdx else 2 * C.m - C.topIdx

/-- The chain vertex index at position `i ≤ 2m` of the tour of the double boundary starting (and
ending) at the top vertex. -/
noncomputable def sideIdx (β : Bool) (i : ℕ) : ℕ := sideE C.m ztbaba

/-- The tour of the double boundary from the top vertex. -/
noncomputable def sideTour (β : Bool) (i : ℕ) : Point := C.vertex ztjhk

/-- **The corrected boundary walk of `dom C`**: the box block (as in `boundaryWalk`: top of the
slit, the four corners counterclockwise, top of the slit, down the slit) followed by the tour of
the double boundary of the chain from the top vertex, in which the top vertex is left towards
`v_{T+1}` (`β = true`, as in `boundaryWalk`) or towards `v_{T-1}` (`β = false`); the closing edge
goes up the slit.  With `β = C.sideBeta` the walk keeps `dom C` on its left at every corner. -/
noncomputable def sideWalk (β : Bool) : Polygon :=
  ⟨C.boxList ++ C.slitTop :: (List.range ztyw).map (C.sideTour β)⟩
theorem sideWalk_n (β : Bool) : (C.sideWalk β).n = 2 * C.m + 7 := by
  simp [Polygon.n, sideWalk, boxList]
theorem sideWalk_vtx_zero (β : Bool) : (C.sideWalk β).vtx 0 = C.slitTop := rfl
theorem sideWalk_vtx_one (β : Bool) : (C.sideWalk β).vtx 1 = ztvx := rfl
theorem sideWalk_vtx_two (β : Bool) : (C.sideWalk β).vtx 2 = ztru := rfl
theorem sideWalk_vtx_three (β : Bool) : (C.sideWalk β).vtx 3 = ztyn := rfl
theorem sideWalk_vtx_four (β : Bool) : (C.sideWalk β).vtx 4 = ztbjg := rfl
theorem sideWalk_vtx_five (β : Bool) : (C.sideWalk β).vtx 5 = C.slitTop := rfl
theorem sideWalk_vtx_tour (β : Bool) {i : ℕ} (hi : i ≤ 2 * C.m) :
    (C.sideWalk β).vtx ztcy = C.sideTour β i := by
  unfold Polygon.vtx sideWalk boxList
  simp_all
theorem sideWalk_vtx_wrap (β : Bool) :
    (C.sideWalk β).vtx ztxal = C.slitTop := by
  zunbn; rfl
theorem two_m_pos : 0 < 2 * C.m := by have := C.one_le; omega
omit C in
theorem sideE_le {m j : ℕ} (hj : j ≤ 2 * m) : sideE m j ≤ m := by
  zumu
omit C in
theorem sideE_zero (m : ℕ) : sideE m 0 = 0 := by_rfl
omit C in
theorem sideE_two_m (m : ℕ) : sideE m ztdk = 0 := by
  zumu
theorem sideS_lt (β : Bool) : C.sideS β ≤ 2 * C.m := by
  unfold sideS; have := C.topIdx_le; grind
theorem sideE_sideS (β : Bool) : sideE C.m (C.sideS β % ztbb) = C.topIdx := by
  zqfg
  zubco
  unfold sideS
  cases β
  · zueel

    · rw [h0, Nat.sub_zero, Nat.mod_self, sideE_zero]
    · zvmyc; unfold sideE; grind
  · zubvh
    zvmyc; unfold sideE; simp_all
theorem sideIdx_zero (β : Bool) : C.sideIdx β 0 = C.topIdx := by
  unfold sideIdx; rw [add_zero, sideE_sideS]
theorem sideIdx_two_m (β : Bool) : C.sideIdx β ztbb = C.topIdx := by
  unfold sideIdx; rw [Nat.add_mod_right, sideE_sideS]
theorem sideIdx_le (β : Bool) (i : ℕ) : C.sideIdx β i ≤ C.m :=
  sideE_le (Nat.mod_lt _ C.two_m_pos).le
theorem sideTour_zero (β : Bool) : C.sideTour β 0 = C.top := by
  unfold sideTour top; rw [sideIdx_zero]
theorem sideTour_two_m (β : Bool) : C.sideTour β ztbb = C.top := by
  unfold sideTour top; rw [sideIdx_two_m]

/-- The tour index one step later, in terms of the tour position `j = (s + i) mod 2m`. -/
theorem sideIdx_succ (β : Bool) (i : ℕ) :
    C.sideIdx β ztg = sideE C.m ztzhv := by
  unfold sideIdx
  zubco
  have hlt := Nat.mod_lt ztty hm
  have e : (C.sideS β + ztg) % ztbb = ztzhv % ztbb :=
    by_grind
  zui
  rcases lt_or_eq_of_le (show ztty % ztbb + 1 ≤ 2 * C.m by omega) with h | h
  · zukp
  · rw [h, Nat.mod_self, sideE_zero, sideE_two_m]

/-! ### Local structure of the chain -/
theorem sideEdgeIdx_inj {j k : ℕ} (hj : j ≤ C.m) (hk : k ≤ C.m) (h : C.edgeIdx j = C.edgeIdx k) :
    j = k := by
  zumsm
  zumec
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' C.s h) by_omega by_omega

/-- Distinct chain vertex indices give distinct vertices. -/
theorem sideVertex_inj (hP : C.P.Simple) {j k : ℕ} (hj : j ≤ C.m) (hk : k ≤ C.m)
    (h : C.vertex j = C.vertex k) : j = k :=
  C.sideEdgeIdx_inj hj hk (simple_vtx_inj hP ztdyj ztcsx h)

/-- Consecutive chain vertices are distinct. -/
theorem sideVertex_succ_ne (hP : C.P.Simple) (k : ℕ) : C.vertex k ≠ C.vertex zts := by
  have := simple_vtx_succ_ne hP ztcsx
  zuewk

/-- A chain vertex lies exactly on its incident chain edges. -/
theorem sideVertex_mem_chainEdge_iff (hP : C.P.Simple) {j k : ℕ} (hj : j ≤ C.m) (hk : k < C.m) :
    C.vertex j ∈ C.chainEdge k ↔ j = k ∨ j = k + 1 := by
  constructor
  · zuq
    rcases (simple_vtx_mem_edge_iff hP ztdyj ztcsx).1 h with h1 | h1
    · exact Or.inl (C.sideEdgeIdx_inj hj hk.le h1.symm)
    · right
      have h2 : ztlec % C.P.n = C.edgeIdx j := by
        zvmwp; exact prevIdx_succ C.P ztdyj
      zukop
      exact (C.sideEdgeIdx_inj by_omega hj h2).symm
  · zucpg
    · exact C.vertex_mem_chainEdge j
    · exact C.vertex_succ_mem_chainEdge k

/-- A point of an open chain edge lies on no other chain edge. -/
theorem sideOpen_not_mem_chainEdge (hP : C.P.Simple) {k j : ℕ} (hk : k < C.m) (hj : j < C.m)
    (hjk : j ≠ k) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    lerp ztib ztwkj t ∉ C.chainEdge j := by
  have := simple_openEdge_not_mem_other hP ztcsx ht ztdyj
    (fun h => hjk (C.sideEdgeIdx_inj hj.le hk.le h))
  zuewk

/-- A point of an open chain edge is not a chain vertex. -/
theorem sideOpen_ne_vertex (hP : C.P.Simple) {k j : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    lerp ztib ztwkj t ≠ C.vertex j := by
  have := simple_openEdge_ne_vtx hP ztcsx ht ztdyj
  zuewk

/-- The chain meets the slit only at the top vertex. -/
theorem sideSet_inter_slit {x : Point} (hx : x ∈ C.set) (hs : x ∈ C.slit) : x = C.top := by
  have h1 := C.snd_le_top_of_mem_set hx
  obtain ⟨h2, h3, -⟩ := C.mem_slit_iff.1 hs
  grind

/-- **Local obstacles near a point of the box**: near `q`, the points outside the domain lie on
the chain edges through `q`, or on the slit if `q` is on it. -/
theorem sideLocal (q : Point) (hq : q ∈ box C.radius) :
    ∃ r > 0, ∀ x ∈ ball q r, x ∉ C.dom →
      (∃ k < C.m, q ∈ C.chainEdge k ∧ x ∈ C.chainEdge k) ∨ (q ∈ C.slit ∧ x ∈ C.slit) := by
  classical
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 (isOpen_box C.radius) q hq
  set F : Set Point := ⋃ k ∈ (Finset.range C.m).filter (fun k => q ∉ C.chainEdge k), C.chainEdge k
    with hF
  have hFc : IsClosed F := isClosed_biUnion_finset fun k _ => isClosed_edge C.P _
  have hqF : q ∉ F := by
    simp_all
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl q hqF
  obtain ⟨r₃, hr₃, hb₃⟩ : ∃ r₃ > 0, q ∉ C.slit → ∀ x ∈ ball q r₃, x ∉ C.slit := by
    zujts
    · grind
    · obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 (Geometry.isClosed_segment _ _).isOpen_compl q hqs
      tauto
  refine ⟨min r₁ _, lt_min hr₁ (lt_min hr₂ hr₃), fun x hx hxd => ?_⟩
  have hx1 : x ∈ ball q r₁ := ball_subset_ball by_grind hx
  have hx2 : x ∈ ball q r₂ := ball_subset_ball by_grind hx
  have hx3 : x ∈ ball q r₃ := ball_subset_ball by_grind hx
  rw [C.mem_dom_iff] at hxd
  push Not at hxd
  by_cases hxs : x ∈ C.set
  · left
    obtain ⟨k, hk, hxk⟩ := hxs
    refine ⟨k, hk, ?_, hxk⟩
    by_contra hqk
    apply hb₂ hx2
    simp only [hF, mem_iUnion, Finset.mem_filter, Finset.mem_range]
    grind
  · grind

/-- Near a chain vertex, the points outside the domain lie on its (at most two) chain edges, or on
the slit if it is the top vertex. -/
theorem sideLocal_vertex (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) :
    ∃ r > 0, ∀ x ∈ ball ztib r, x ∉ C.dom →
      (1 ≤ k ∧ x ∈ Chazelle.segment ztyhj ztib) ∨
      (k < C.m ∧ x ∈ Chazelle.segment ztib ztwkj) ∨
      (k = C.topIdx ∧ x ∈ C.slit) := by
  obtain ⟨r, hr, h⟩ := C.sideLocal ztib ztyhi
  zqdy
  · rw [C.chainEdge_eq] at hxj
    rcases (C.sideVertex_mem_chainEdge_iff hP hk hj).1 hkj with rfl | rfl
    · simp_all
    simp_all
  · zulw
    refine ⟨?_, hxs⟩
    have := C.sideSet_inter_slit ztdkv hks
    exact C.sideVertex_inj hP hk C.topIdx_le this

/-- Near a point of an open chain edge, the points outside the domain lie on that edge. -/
theorem sideLocal_open (hP : C.P.Simple) {k : ℕ} (hk : k < C.m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ r > 0, ∀ x ∈ ball (lerp ztib ztwkj t) r, x ∉ C.dom →
      x ∈ Chazelle.segment ztib ztwkj := by
  have hq : lerp ztib ztwkj t ∈ C.set := by
    zulow
    rw [C.chainEdge_eq]; exact lerp_mem_segment _ _ ht.1.le ht.2.le
  obtain ⟨r, hr, h⟩ := C.sideLocal _ (C.set_subset_box hq)
  zqdy
  · by_cases hjk : j = k
    · subst hjk; rwa [C.chainEdge_eq] at hxj
    · exact absurd hkj (C.sideOpen_not_mem_chainEdge hP hk hj hjk ht)
  · exfalso
    have := C.sideSet_inter_slit hq hks
    exact C.sideOpen_ne_vertex hP ht this

/-! ### Left sectors and segments -/
omit C in
theorem sideCcw_zero (B A : Point) : ¬ sideCcw B 0 A := by
  zumun
  simp
omit C in
/-- The segments of a corner are not in its open left sector. -/
theorem sideLeftOf_not_seg_prev (hav : a ≠ v)
    (hx : x ∈ Chazelle.segment a v) : ¬ sideLeftOf a v b x := by
  zqer
  zucfg
  apply sideCcw_not_ray_right ztwfi
  · zudwj
  · zuenw
    nlinarith [mul_nonneg (sub_nonneg.2 hμ1) (add_nonneg (sq_nonneg ztcts)
      (sq_nonneg ztclz))]
omit C in
theorem sideLeftOf_not_seg_next (hbv : b ≠ v)
    (hx : x ∈ Chazelle.segment v b) : ¬ sideLeftOf a v b x := by
  zqer
  zucfg
  apply sideCcw_not_ray_left ztqxb
  · zudwj
  · zuenw
    nlinarith [mul_nonneg hμ0 (add_nonneg (sq_nonneg ztry) (sq_nonneg ztcet))]
omit C in
/-- If a point `w` is not in the open left sector, neither is any point of `[v, w]`. -/
theorem sideLeftOf_not_seg {a v b w x : Point} (hw : ¬ sideLeftOf a v b w)
    (hx : x ∈ Chazelle.segment v w) : ¬ sideLeftOf a v b x := by
  zqer
  unfold sideLeftOf at *
  have e : ztygt := by
    zqdj
  zui
  rcases hμ0.lt_or_eq with hμ | hμ
  · rwa [sideCcw_smul hμ]
  · rw [← hμ, zero_smul]; exact sideCcw_zero _ _

/-! ### The corners of the tour -/
theorem sideIdx_eq (β : Bool) (i : ℕ) : C.sideIdx β i = sideE C.m ztbaba :=
  rfl
theorem sideS_mod (β : Bool) :
    (C.sideS β % ztbb = C.topIdx ∧ (β = true ∨ C.topIdx = 0 ∨ C.topIdx = C.m)) ∨
      (C.sideS β % ztbb = 2 * C.m - C.topIdx ∧ 0 < C.topIdx ∧ β = false) := by
  zqfg
  zqef
  unfold sideS
  cases β
  · zueel

    · simp_all
    · right; zvmyc; simp_all
  · zubvh
    left; zvmyc; simp

/-- **Classification of the corners of the tour**: at an inner position of the tour the walk
passes a chain vertex `k` forwards (`k-1, k, k+1`) or backwards (`k+1, k, k-1`), or turns around
a chain endpoint. -/
theorem sideTour_corner (β : Bool) {i : ℕ} (hi0 : 0 < i) (_hi : i < 2 * C.m) :
    (0 < C.sideIdx β i ∧ C.sideIdx β i < C.m ∧ C.sideIdx β ztei + 1 = C.sideIdx β i ∧
        C.sideIdx β ztg = C.sideIdx β i + 1) ∨
      (0 < C.sideIdx β i ∧ C.sideIdx β i < C.m ∧ C.sideIdx β ztei = C.sideIdx β i + 1 ∧
        C.sideIdx β ztg + 1 = C.sideIdx β i) ∨
      (C.sideIdx β i = 0 ∧ C.sideIdx β ztei = 1 ∧ C.sideIdx β ztg = 1) ∨
      (C.sideIdx β i = C.m ∧ C.sideIdx β ztei + 1 = C.m ∧ C.sideIdx β ztg + 1 = C.m) := by
  zqef
  zqes
  have e1 : C.sideIdx β i = sideE C.m ztbapq := by
    have := C.sideIdx_succ β ztei; grind
  have e2 := C.sideIdx_succ β i
  have e0 := C.sideIdx_eq β ztei
  have hj' := Nat.mod_lt ztwxx hm2
  have hj : ztty % ztbb = ztbapq % ztbb := by
    grind
  rw [e1, e2, e0, hj]
  generalize ztwxx % ztbb = j at hj' ⊢
  zqfr
  · zukp
    unfold sideE
    zuwd
  · zuohj
    unfold sideE
    zuwd

/-- The tour positions other than the ends that visit the top vertex: the middle passage, with
the same neighbours as the ends but traversed from the first neighbour to the last. -/
theorem sideTour_top_mid (β : Bool) {i : ℕ} (hi0 : 0 < i) (hi : i < 2 * C.m)
    (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) (hiT : C.sideIdx β i = C.topIdx) :
    C.sideIdx β ztei = C.sideIdx β 1 ∧ C.sideIdx β ztg = C.sideIdx β ztdl := by
  zqes
  obtain ⟨S, hSdef⟩ : ∃ S, S = C.sideS β % (2 * C.m) := by_simp_all
  have hS : S = C.topIdx ∨ S = 2 * C.m - C.topIdx := by
    rcases C.sideS_mod β with ⟨h, -⟩ | ⟨h, -⟩
    · omega
    omega
  have f1 : C.sideIdx β 1 = sideE C.m ztbgu := by
    zunre; have := C.sideIdx_succ β 0; omega
  have f2 : C.sideIdx β ztdl = sideE C.m (S - 1) := by
    zujlm
    rw [Nat.add_mod, ← hSdef, Nat.mod_eq_of_lt (show 2 * C.m - 1 < 2 * C.m by omega)]
    rcases side_mod_cases (show S + ztdl < 2 * ztbb by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    omega
  obtain ⟨j, hjdef⟩ : ∃ j, j = (C.sideS β + (i - 1)) % (2 * C.m) := by_simp_all
  have hj2 := hjdef ▸ Nat.mod_lt _ hm2
  have e1 : C.sideIdx β i = sideE C.m ztl := by
    rw [hjdef]; have := C.sideIdx_succ β ztei; grind
  have e0 : C.sideIdx β ztei = sideE C.m j := by rw [hjdef]; rfl
  have hji : ztty % ztbb = ztl % ztbb := by
    rw [hjdef, side_idx_succ hm2, Nat.sub_add_cancel hi0]
  have e2 : C.sideIdx β ztg = sideE C.m (ztl % ztbb + 1) := by
    rw [C.sideIdx_succ, hji]
  have hne : ztl % ztbb ≠ S := by
    rw [← hji, hSdef]; intro h
    zujxx
    have := Nat.ModEq.add_left_cancel' _ h'
    zulxv
  zvmxy at hiT
  rw [e0, e2, f1, f2]
  zqfg
  have key : j + 1 < 2 * C.m ∧ j + 1 = 2 * C.m - S := by
    unfold sideE at hiT
    zqfr
    · zvnnm at hne
      grind
    grind
  rw [Nat.mod_eq_of_lt key.1]
  constructor <;> unfold sideE <;> split_ifs <;> omega
theorem sideIdx_one (β : Bool) : C.sideIdx β 1 = sideE C.m (C.sideS β % ztbb + 1) := by
  have := C.sideIdx_succ β 0; omega
theorem sideIdx_last (β : Bool) :
    C.sideIdx β ztdl = sideE C.m ((C.sideS β % ztbb + ztdl) % ztbb) := by
  rw [sideIdx_eq, Nat.add_mod _, Nat.mod_eq_of_lt (show 2 * C.m - 1 < 2 * C.m by
    have := C.two_m_pos; omega)]

/-- The neighbours of the top vertex along the walk: the first and the last chain vertex of the
tour are the chain neighbours of the top vertex (the same one if the top vertex is an endpoint of
the chain, different ones otherwise). -/
theorem sideTour_nbrs (β : Bool) :
    (1 ≤ C.topIdx → C.topIdx - 1 = C.sideIdx β 1 ∨ C.topIdx - 1 = C.sideIdx β ztdl) ∧
    (C.topIdx < C.m → C.topIdx + 1 = C.sideIdx β 1 ∨ C.topIdx + 1 = C.sideIdx β ztdl) ∧
    (C.sideIdx β 1 + 1 = C.topIdx ∨ C.sideIdx β 1 = C.topIdx + 1) ∧
    (C.sideIdx β ztdl + 1 = C.topIdx ∨ C.sideIdx β ztdl = C.topIdx + 1) ∧
    (0 < C.topIdx → C.topIdx < C.m → C.sideIdx β 1 ≠ C.sideIdx β ztdl) := by
  zqef
  zqfg
  zugbp
  rcases C.sideS_mod β with ⟨hs, -⟩ | ⟨hs, h0, -⟩ <;> zvmyz
  · rcases side_mod_cases ztybe with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zvmxx <;> unfold sideE <;> split_ifs <;> omega
  · rcases side_mod_cases ztxor with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zvmxx <;> unfold sideE <;> split_ifs <;> omega

/-- An inner tour position visits the top vertex only if it is not an endpoint of the chain. -/
theorem sideTour_top_inner (β : Bool) {i : ℕ} (hi0 : 0 < i) (hi : i < 2 * C.m)
    (hiT : C.sideIdx β i = C.topIdx) : 0 < C.topIdx ∧ C.topIdx < C.m := by
  zqes
  zqfg
  have hne : ztty % ztbb ≠ C.sideS β % ztbb := by
    zuq
    zujxx
    have := Nat.ModEq.add_left_cancel' _ h'
    zulxv
  rw [sideIdx_eq] at hiT
  zukcr
  rcases C.sideS_mod β with ⟨hs, -⟩ | ⟨hs, h0, -⟩
  · zqeg
  · zqeg

/-- One step of the tour moves to an adjacent chain vertex. -/
theorem sideTour_step (β : Bool) (i : ℕ) :
    C.sideIdx β ztg = C.sideIdx β i + 1 ∨ C.sideIdx β ztg + 1 = C.sideIdx β i := by
  zqes
  rw [C.sideIdx_succ, sideIdx_eq]
  zukcr
  generalize ztty % ztbb = j at hj ⊢
  zumu

/-! ### The order at the top vertex -/

/-- The two chain edges at an inner chain vertex meet only at it. -/
theorem sideChain_meet (hP : C.P.Simple) {k : ℕ} (hk0 : 0 < k) (hkm : k < C.m) :
    Chazelle.segment ztyhj ztib ∩
      Chazelle.segment ztib ztwkj ⊆ {C.vertex k} := by
  rintro x ⟨hx1, hx2⟩
  have e1 : C.chainEdge ztie = Chazelle.segment ztyhj ztib := by
    rw [C.chainEdge_eq, Nat.sub_add_cancel hk0]
  have hx1' : x ∈ C.P.edge (C.edgeIdx ztie) := by
    show x ∈ C.chainEdge _; simp_all
  have hx2' : x ∈ C.P.edge zthqt := by
    show x ∈ C.chainEdge k; rw [C.chainEdge_eq]; omega
  have hne : C.edgeIdx ztie ≠ C.edgeIdx k := fun h =>
    absurd ztris by_omega
  have hmem : x ∈ C.P.edge _ ∩ C.P.edge _ := ⟨hx1', hx2'⟩
  rw [simple_edge_inter hP ztmal ztmal hne] at hmem
  zuchx
  rw [C.edgeIdx_succ, Nat.sub_add_cancel hk0] at h1
  zukop
  zukko
  · exfalso
    have h1' : x = C.vertex _ := h1
    zukkq
    · zqfx
      omega
    · zqfx
      omega
  tauto

/-- The two chain edges at an inner chain vertex do not leave it in the same direction. -/
theorem sideChain_nonSpike (hP : C.P.Simple) {k : ℕ} (hk0 : 0 < k) (hkm : k < C.m) :
    sideNonSpike ztwuh ztxfy ∧
      sideNonSpike ztxfy ztwuh := by
  have hav : C.vertex ztie ≠ C.vertex k := by
    have := C.sideVertex_succ_ne hP ztie; grind
  have hvb : C.vertex k ≠ C.vertex _ := C.sideVertex_succ_ne hP k
  have key : sideCross ztwuh ztxfy = 0 →
      sideDot ztwuh ztxfy < 0 := by
    zuchg
    rw [sideCross_corner] at hc
    have := dir_pos_of_collinear hav hvb (C.sideChain_meet hP hk0 hkm) hc
    unfold sideDot; zvnhb; linarith
  refine ⟨fun ⟨hc, hd⟩ => absurd (key hc) (not_lt.2 hd.le), fun ⟨hc, hd⟩ => ?_⟩
  rw [sideCross_swap] at hc
  zugfi
  grind

/-- **The walk turns correctly at the top vertex**: the top vertex is an endpoint of the chain,
or, going down the slit, the direction of the slit lies strictly inside the counterclockwise arc
from the first chain neighbour of the walk to the last one. -/
def SideGood (β : Bool) : Prop :=
  C.topIdx = 0 ∨ C.topIdx = C.m ∨
    sideCcw ztblu ztyy ztwmj
theorem sideSlitTop_ne_top : C.slitTop ≠ C.top := by
  zuq
  have := congrArg Prod.snd h
  simp only [slitTop] at this
  zujca
theorem sideTour_one_ne_top (hP : C.P.Simple) (β : Bool) : C.sideTour β 1 ≠ C.top := by
  zuq
  have := C.sideVertex_inj hP ztnjx C.topIdx_le h
  rcases (C.sideTour_nbrs β).2.2.1 with h' | h' <;> omega
theorem sideTour_last_ne_top (hP : C.P.Simple) (β : Bool) :
    C.sideTour β ztdl ≠ C.top := by
  zuq
  have := C.sideVertex_inj hP ztemb C.topIdx_le h
  rcases (C.sideTour_nbrs β).2.2.2.1 with h' | h' <;> omega
theorem sideTop_nonSpike (hP : C.P.Simple) (β : Bool) (hT0 : 0 < C.topIdx)
    (hTm : C.topIdx < C.m) :
    sideNonSpike ztblu ztwmj := by
  obtain ⟨-, -, h1, h2, h3⟩ := C.sideTour_nbrs β
  have hne := h3 hT0 hTm
  have hns := C.sideChain_nonSpike hP hT0 hTm
  unfold sideTour top
  grind

/-- At the middle passage through the top vertex, the slit is not in the left sector. -/
theorem sideTop_mid_slit (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) (hT0 : 0 < C.topIdx)
    (hTm : C.topIdx < C.m) :
    ¬ sideLeftOf ztdfk C.top ztwto C.slitTop := by
  have hord : sideCcw ztblu ztyy
      ztwmj := by
    zqds
    · omega
    · omega
    omega
  zucfg
  exact sideCcw_asymm ztxou
    ztjhl hord

/-- At the first corner of the top vertex (down the slit, then to the first neighbour), the
last neighbour is not in the left sector. -/
theorem sideTop_first_other (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β)
    (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) :
    ¬ sideLeftOf C.slitTop C.top ztdfk ztwto := by
  have hord : sideCcw ztblu ztyy
      ztwmj := by
    zqds
    · omega
    · omega
    omega
  zucfg
  zuq
  have := sideCcw_sub_left ztxou hord h
  exact sideCcw_not_ray_right ztykb
    ztwdw (sideDot_self_pos ztykb).le
    this

/-- At the last corner of the top vertex (from the last neighbour, then up the slit), the first
neighbour is not in the left sector. -/
theorem sideTop_last_other (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β)
    (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) :
    ¬ sideLeftOf ztwto C.top C.slitTop ztdfk := by
  have hord : sideCcw ztblu ztyy
      ztwmj := by
    zqds
    · omega
    · omega
    omega
  zucfg
  zuq
  have := sideCcw_sub_right ztxou
    (sub_ne_zero_of_ne' C.sideSlitTop_ne_top) ztykb
    hord h
  exact sideCcw_not_ray_left ztxou
    ztwdw (sideDot_self_pos ztxou).le
    this

/-! ### Cleanness of the tour positions of the corrected walk -/
theorem sideWalk_prev_tour (β : Bool) {i : ℕ} (hi : 1 ≤ i) (hi2 : i ≤ 2 * C.m) :
    ztjyj % (C.sideWalk β).n = ztei + 6 := by
  rw [sideWalk_n, show i + 6 + ztz - 1 = ztqrc + ztz by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
theorem sideWalk_next_tour (β : Bool) {i : ℕ} (hi : i < 2 * C.m) :
    ztcim % (C.sideWalk β).n = ztg + 6 := by
  rw [sideWalk_n, Nat.mod_eq_of_lt by_omega]
theorem sideWalk_prev_six (β : Bool) : ztjea % (C.sideWalk β).n = 5 := by
  rw [sideWalk_n, show 0 + 6 + ztz - 1 = 5 + ztz by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt by_omega]
theorem sideWalk_next_last (β : Bool) : ztbjc % (C.sideWalk β).n = 0 := by
  zunbn
theorem sideVertex_pred_ne (hP : C.P.Simple) {k : ℕ} (hk : 1 ≤ k) :
    C.vertex ztie ≠ C.vertex k := by
  have := C.sideVertex_succ_ne hP ztie; simp_all

/-- **Cleanness at an inner corner of the tour.** -/
theorem sideClean_tour_vertex (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) {i : ℕ}
    (hi0 : 0 < i) (hi : i < 2 * C.m) : SideClean ztft C.dom ztcy 0 := by
  have hprev : (C.sideWalk β).vtx (ztjyj % (C.sideWalk β).n) =
      C.vertex (C.sideIdx β ztei) := by
    rw [C.sideWalk_prev_tour β hi0 hi.le, C.sideWalk_vtx_tour β by_omega]; rfl
  have hcur : ztmqz :=
    C.sideWalk_vtx_tour β hi.le
  have hnext : (C.sideWalk β).vtx ztyt =
      C.vertex ztwtn := by
    zufmk
  obtain ⟨r, hr, hloc⟩ := C.sideLocal_vertex hP ztdfj
  zqdg
  -- the middle passage through the top vertex
  have hmid : C.sideIdx β i = C.topIdx → x ∈ C.slit → False := by
    intro hkT hxs
    obtain ⟨hT0, hTm⟩ := C.sideTour_top_inner β hi0 hi hkT
    obtain ⟨hp, hn⟩ := C.sideTour_top_mid β hi0 hi hT0 hTm hkT
    rw [hp, hn, hkT] at hxl
    exact sideLeftOf_not_seg (C.sideTop_mid_slit hP hβ hT0 hTm) hxs hxl
  rcases C.sideTour_corner β hi0 hi with ⟨h0, hm, hp, hn⟩ | ⟨h0, hm, hp, hn⟩ | ⟨h0, hp, hn⟩ |
      ⟨h0, hp, hn⟩
  · zqex
    · zqek
    · zvmxq at hxl
      exact sideLeftOf_not_seg_next (C.sideVertex_succ_ne hP _).symm hxs hxl
    simp_all
  · zqex
    · rw [show C.sideIdx β ztg = C.sideIdx β i - 1 by omega] at hxl
      zqfe
      exact sideLeftOf_not_seg_next ztswb hxs hxl
    · zvohk at hxl
      zqfe
      exact sideLeftOf_not_seg_prev (C.sideVertex_succ_ne hP _).symm hxs hxl
    simp_all
  · rcases hloc x hx hxd with ⟨h1, -⟩ | ⟨-, hxs⟩ | ⟨hkT, hxs⟩
    · omega
    · rw [hn, h0] at hxl
      zvmzn at hxs
      exact sideLeftOf_not_seg_next (C.sideVertex_succ_ne hP 0).symm hxs hxl
    simp_all
  · rcases hloc x hx hxd with ⟨-, hxs⟩ | ⟨h1, -⟩ | ⟨hkT, hxs⟩
    · zqek
    · omega
    grind

/-- **Cleanness at the first corner of the top vertex** (down the slit, then along the chain). -/
theorem sideClean_top_first (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) :
    SideClean ztft C.dom ztfmo 0 := by
  zqef
  have hprev : (C.sideWalk β).vtx (ztjea % (C.sideWalk β).n) =
      C.slitTop := by rw [C.sideWalk_prev_six β]; rfl
  have hcur : (C.sideWalk β).vtx ztfmo = C.top := by
    rw [C.sideWalk_vtx_tour β by_omega, sideTour_zero]
  have hnext : (C.sideWalk β).vtx (ztpsi % (C.sideWalk β).n) = C.sideTour β 1 := by
    zugtn
  obtain ⟨r, hr, hloc⟩ := C.sideLocal_vertex hP C.topIdx_le
  zqdg
  obtain ⟨hn1, hn2, hn3, -, -⟩ := C.sideTour_nbrs β
  zqdu
  -- a chain neighbour `w` of the top vertex is not in the left sector
  have hnb : ∀ w, w + 1 = C.topIdx ∨ w = C.topIdx + 1 → w ≤ C.m →
      w = C.sideIdx β 1 ∨ w = C.sideIdx β ztdl →
      ∀ y ∈ Chazelle.segment C.top ztuxj, ¬ sideLeftOf C.slitTop C.top ztdfk y := by
    zujbs
    by_cases h1 : w = C.sideIdx β 1
    · zucuj
      exact sideLeftOf_not_seg_next ztcld hy
    · have h2 : w = C.sideIdx β _ := hw'.resolve_left h1
      have hT0 : ztphp := by
        omega
      have hTm : ztmsx := by
        omega
      zvmxx at hy
      exact sideLeftOf_not_seg (C.sideTop_first_other hP hβ hT0 hTm) hy
  zqey
  · zqfe
    zqfs
  · zqft
  · have : x ∈ Chazelle.segment C.slitTop C.top := by zvnln; tauto
    exact sideLeftOf_not_seg_prev C.sideSlitTop_ne_top this hxl

/-- **Cleanness at the last corner of the top vertex** (along the chain, then up the slit). -/
theorem sideClean_top_last (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) :
    SideClean ztft C.dom ztcc 0 := by
  zqef
  have hprev : (C.sideWalk β).vtx ((2 * C.m + 6 + (C.sideWalk β).n - 1) % (C.sideWalk β).n) =
      C.sideTour β ztdl := by
    rw [C.sideWalk_prev_tour β by_omega le_rfl, C.sideWalk_vtx_tour β by_omega]
  have hcur : ztytm := by
    zuigc
  have hnext : ztbaoh := by
    zujgl
  obtain ⟨r, hr, hloc⟩ := C.sideLocal_vertex hP C.topIdx_le
  zqdg
  obtain ⟨hn1, hn2, -, hn4, -⟩ := C.sideTour_nbrs β
  zqdu
  have hnb : ∀ w, w + 1 = C.topIdx ∨ w = C.topIdx + 1 → w ≤ C.m →
      w = C.sideIdx β 1 ∨ w = C.sideIdx β ztdl →
      ∀ y ∈ Chazelle.segment ztuxj C.top,
        ¬ sideLeftOf ztwto C.top C.slitTop y := by
    zujbs
    by_cases h2 : w = C.sideIdx β ztdl
    · zuhqi
      exact sideLeftOf_not_seg_prev ztdsw hy
    · have h1 := hw'.resolve_right h2
      have hT0 : ztphp := by
        omega
      have hTm : ztmsx := by
        omega
      rw [h1, segment_comm] at hy
      exact sideLeftOf_not_seg (C.sideTop_last_other hP hβ hT0 hTm) hy
  zqey
  · zqfs
  · zqfe
    zqft
  · exact sideLeftOf_not_seg_next C.sideSlitTop_ne_top hxs hxl

/-- **Cleanness inside an edge of the tour.** -/
theorem sideClean_tour_edge (hP : C.P.Simple) (β : Bool) {i : ℕ} (hi : i < 2 * C.m) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : SideClean ztft C.dom ztcy t := by
  have hcur : ztmqz :=
    C.sideWalk_vtx_tour β hi.le
  have hnext : (C.sideWalk β).vtx ztyt =
      C.vertex ztwtn := by
    zufmk
  zufgw

  zqei
  · have hne : ztxsu := by
      rw [hcur, hnext, h]; exact C.sideVertex_succ_ne hP _
    obtain ⟨r, hr, hloc⟩ := C.sideLocal_open hP (k := C.sideIdx β i) by_omega ht
    refine ztkmn
    rw [sideLeft_edge hne ht, hcur, hnext, h] at hxl
    zumuw
    rw [hcur, hnext, h] at hx
    rw [Geometry.det_eq_zero_of_mem_segment by_simp_all] at hxl
    simp_all
  · have hne : ztxsu := by
      rw [hcur, hnext, ← h]; exact (C.sideVertex_succ_ne hP _).symm
    zukgd
    obtain ⟨r, hr, hloc⟩ := C.sideLocal_open hP (k := C.sideIdx β ztg) by_omega ht'
    refine ztkmn
    rw [sideLeft_edge hne ht, hcur, hnext, ← h] at hxl
    zumuw
    rw [hcur, hnext, ← h] at hx
    have e : lerp ztwww ztbalx t =
        lerp ztbalx ztwww ztca := by
      zqeq
    zvmwe at hx
    have hxs := hloc x hx hxd
    zqfe
    rw [Geometry.det_eq_zero_of_mem_segment hxs] at hxl
    simp_all

/-! ### Cleanness of the box block of the corrected walk -/
theorem sideClean_box (hset : sidePt W p t ∉ C.set) {r : ℝ}
    (hr : 0 < r)
    (h : ∀ x ∈ ball ztia r, sideLeft W p t x → x ∈ box C.radius ∧ x ∉ C.slit) :
    SideClean W C.dom p t := by
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 C.isClosed_set.isOpen_compl _ hset
  refine ⟨min r r₁, by_simp_all, fun x hx hxd hxl => ?_⟩
  have hx1 : x ∈ ball _ r := ball_subset_ball by_simp_all hx
  have hx2 : x ∉ C.set := hb₁ by_simp_all
  obtain ⟨hb, hs⟩ := h x hx1 hxl
  exact hxd ztuxe
theorem sideNot_mem_set_of_abs (h : C.radius ≤ |q.1| ∨ C.radius ≤ |q.2|) :
    q ∉ C.set := by
  intro hq
  have h1 := C.abs_le_coordBound_of_mem_set hq
  have h2 := C.coordBound_lt_radius
  grind
theorem sideNot_mem_set_of_high (h : C.top.2 < q.2) : q ∉ C.set := fun hq =>
  absurd (C.snd_le_top_of_mem_set hq) ztmmp
theorem sideNot_mem_slit_of_fst {x : Point} (h : x.1 ≠ C.top.1) : x ∉ C.slit := fun hs =>
  h (C.mem_slit_iff.1 hs).1
theorem sideNot_mem_slit_of_low {x : Point} (h : x.2 < C.top.2) : x ∉ C.slit := fun hs =>
  absurd (C.mem_slit_iff.1 hs).2.1 ztmmp
theorem sideWalk_mod_small (β : Bool) {p : ℕ} (hp : p < 2 * C.m + 7) :
    p % (C.sideWalk β).n = p := by rw [sideWalk_n]; simp_all
theorem sideWalk_prev_zero (β : Bool) :
    (C.sideWalk β).vtx ((0 + (C.sideWalk β).n - 1) % (C.sideWalk β).n) = C.top := by
  rw [sideWalk_n, show 0 + ztz - 1 = 2 * C.m + 6 by omega,
    Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
theorem sideWalk_prev_small (β : Bool) {p : ℕ} (hp1 : 1 ≤ p) (hp : p ≤ 5) :
    ztlro % (C.sideWalk β).n = p - 1 := by
  rw [sideWalk_n, show p + ztz - 1 = ztoq + ztz by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
theorem sideWalk_vtx_six (β : Bool) : (C.sideWalk β).vtx 6 = C.top := by
  have := C.sideWalk_vtx_tour β (i := 0) by_omega; rwa [zero_add, sideTour_zero] at this

/-- **Cleanness of the box block**: the corners of the box and the two corners at the top of the
slit. -/
theorem sideClean_box_vertex (β : Bool) {p : ℕ} (hp : p ≤ 5) :
    SideClean ztft C.dom p 0 := by
  zqfy
  have ht := abs_lt.1 C.abs_top_fst_lt_radius
  zubnz
  have hr : 0 < C.radius - |C.top.1| := by_grind
  have hta := abs_le.1 (le_refl |C.top.1|)
  zqdf
  interval_cases p
  · -- the top of the slit, from the slit to the top side
    have hset : sidePt ztft 0 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_zero]
      zufqk

    zqdn
    rw [sidePt_zero, C.sideWalk_vtx_zero, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_zero, C.sideWalk_vtx_zero, hnext] at hxl
    change sideLeftOf C.top C.slitTop ztvx x at hxl
    have hdet : 0 < det C.top C.slitTop ztvx := by
      zqez
    zqde
    zqdb
    zuhvq
    zujxh
    exact ⟨ztsr,
      C.sideNot_mem_slit_of_fst ztvzq⟩
  · have hset : sidePt ztft 1 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_one]
      zugja
    zqdn
    rw [sidePt_zero, C.sideWalk_vtx_one, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β le_rfl by_norm_num, C.sideWalk_vtx_one,
      hnext] at hxl
    change sideLeftOf C.slitTop ztvx ztru x at hxl
    have hdet : 0 < det C.slitTop ztvx ztru := by
      zqez
    zqde
    zqdb
    zqet
    have e2 : ztphi := by_nlinarith
    exact ⟨ztsr,
      C.sideNot_mem_slit_of_fst by_linarith⟩
  · have hset : sidePt ztft 2 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_two]
      zugja
    zqdn
    rw [sidePt_zero, C.sideWalk_vtx_two, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β by_norm_num by_norm_num, C.sideWalk_vtx_two,
      hnext] at hxl
    change sideLeftOf ztvx ztru ztyn x at hxl
    have hdet : 0 < det ztvx ztru ztyn := by
      zujoj
    zqen
    zqdb
    zujxe
    zujxg
    exact ⟨ztsr,
      C.sideNot_mem_slit_of_fst by_linarith⟩
  · have hset : sidePt ztft 3 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_three]
      zugja
    zqdn
    rw [sidePt_zero, C.sideWalk_vtx_three, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β by_norm_num by_norm_num, C.sideWalk_vtx_three,
      hnext] at hxl
    change sideLeftOf ztru ztyn ztbjg x at hxl
    have hdet : 0 < det ztru ztyn ztbjg := by
      zujoj
    zqen
    zqdb
    zqfu
    zujxg
    exact ⟨ztsr,
      C.sideNot_mem_slit_of_fst by_linarith⟩
  · have hset : sidePt ztft 4 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_four]
      zugja
    zqdn
    rw [sidePt_zero, C.sideWalk_vtx_four, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β by_norm_num by_norm_num, C.sideWalk_vtx_four,
      hnext] at hxl
    change sideLeftOf ztyn ztbjg C.slitTop x at hxl
    have hdet : 0 < det ztyn ztbjg C.slitTop := by
      zqez
    zqde
    zqdb
    zqfu
    zujxh
    exact ⟨ztsr,
      C.sideNot_mem_slit_of_fst by_linarith⟩
  · have hset : sidePt ztft 5 0 ∉ C.set := by
      rw [sidePt_zero, C.sideWalk_vtx_five]
      zufqk

    zqdn
    rw [sidePt_zero, C.sideWalk_vtx_five, mem_ball_iff_abs] at hx
    rw [sideLeft_zero, C.sideWalk_prev_small β by_norm_num by_norm_num, C.sideWalk_vtx_five,
      hnext, C.sideWalk_vtx_six] at hxl
    change sideLeftOf ztbjg C.slitTop C.top x at hxl
    have hdet : 0 < det ztbjg C.slitTop C.top := by
      zqez
    zqde
    zqdb
    zqet
    have e2 : C.top.1 < x.1 := by_nlinarith
    exact ⟨ztsr,
      C.sideNot_mem_slit_of_fst (ne_of_gt e2)⟩
theorem sideClean_box_edge_aux (ht : t ∈ Ioo (0 : ℝ) 1)
    (hne : W.vtx p ≠ W.vtx ztwjb) (hset : sidePt W p t ∉ C.set) {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ ball ztia r, 0 < det ztbbv ztbajj x →
      x ∈ box C.radius ∧ x ∉ C.slit) :
    SideClean W C.dom p t :=
  C.sideClean_box hset hr (fun x hx hxl => h x hx ((sideLeft_edge hne ht x).1 hxl))

/-- Cleanness inside the closing edge (up the slit). -/
theorem sideClean_slit_up (β : Bool) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    SideClean ztft C.dom ztcc t := by
  zqdq
  have hcur : ztytm := by
    zuigc
  have hnext : ztbaoh := by
    zujgl
  have hne : (C.sideWalk β).vtx ztcc ≠
      (C.sideWalk β).vtx ztxal := by
    rw [hcur, hnext]; exact C.sideSlitTop_ne_top.symm
  have hq : sidePt ztft ztcc t =
      ztyor := by
    unfold sidePt; rw [hcur, hnext]
    zqdi
  have hpos : 0 < t * ztox := by_simp_all
  have hpos' : ztzoj := by_simp_all
  have hset : sidePt ztft ztcc t ∉ C.set := by
    zvnck; apply C.sideNot_mem_set_of_high; simp_all
  have hr : 0 < min (min _ _)
      ztfnf :=
    lt_min (lt_min hpos hpos') by_linarith
  zqdc
  rw [hcur, hnext] at hxl
  zqel
  zqdb
  have hm1 := min_le_left ztwox
    ztfnf
  have hm2 := min_le_right ztwox
    ztfnf
  zqdk
  zuhvq
  exact ⟨⟨abs_lt.2 by_grind, abs_lt.2 by_grind⟩,
    C.sideNot_mem_slit_of_fst ztvzq⟩

/-- **Cleanness inside the edges of the box block** (the sides of the box and the slit). -/
theorem sideClean_box_edge (β : Bool) {p : ℕ} (hp : p ≤ 5 ∨ p = 2 * C.m + 6) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : SideClean ztft C.dom p t := by
  zqdq
  zudsh
  · zqdf
    interval_cases p
    · -- the top side, west of the slit
      have hne : (C.sideWalk β).vtx 0 ≠ (C.sideWalk β).vtx (ztbgo % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_zero]
        intro h; have := congrArg Prod.fst h; simp only [slitTop] at this
        change C.top.1 = -C.radius at this; linarith
      have hq : sidePt ztft 0 t = ztipy := by
        have e1 := C.sideWalk_vtx_one β
        unfold sidePt; rw [hnext, C.sideWalk_vtx_zero, e1]
        zqdi
      have hset : sidePt ztft 0 t ∉ C.set := by
        zqfz
      have hr : 0 < min ztyry ztysj :=
        lt_min by_nlinarith by_nlinarith
      zqdc
      rw [hnext, C.sideWalk_vtx_zero] at hxl
      change 0 < det C.slitTop ztvx x at hxl
      zqel
      zqdb
      have hm1 := min_le_left ztyry ztysj
      have hm2 := min_le_right ztyry ztysj
      zqet
      exact ⟨ztsr,
        C.sideNot_mem_slit_of_fst by_nlinarith⟩
    · -- the left side
      have hne : ztxcw := by
        rw [hnext, C.sideWalk_vtx_one]
        intro h; have := congrArg Prod.snd h
        change C.radius = -C.radius at this; linarith
      have hq : sidePt ztft 1 t = ztkpp := by
        have e2 := C.sideWalk_vtx_two β
        unfold sidePt; rw [hnext, C.sideWalk_vtx_one, e2]
        zqdj
        ring
      have hset : sidePt ztft 1 t ∉ C.set := by
        zvnck; apply C.sideNot_mem_set_of_abs; left; simp only; zuoch
      have hr : 0 < min ztwkz ztfnf :=
        lt_min by_simp_all by_linarith
      zqdc
      rw [hnext, C.sideWalk_vtx_one] at hxl
      change 0 < det ztvx _ x at hxl
      rw [C.sideWalk_vtx_two] at hxl
      simp only [det] at hxl hx
      zqdb
      have hm1 := min_le_left ztwkz ztfnf
      have hm2 := min_le_right ztwkz ztfnf
      zqdd
      zujxe
      exact ⟨ztsr,
        C.sideNot_mem_slit_of_fst by_nlinarith⟩
    · -- the bottom side
      have hne : (C.sideWalk β).vtx 2 ≠ (C.sideWalk β).vtx (ztssp % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_two]
        intro h; have := congrArg Prod.fst h
        change -C.radius = (C.sideWalk β |>.vtx 3).1 at this
        rw [C.sideWalk_vtx_three] at this; simp only at this; linarith
      have hq : sidePt ztft 2 t = ztjct := by
        unfold sidePt; rw [hnext, C.sideWalk_vtx_two, C.sideWalk_vtx_three]
        zqdj
        ring
      have hset : sidePt ztft 2 t ∉ C.set := by
        zvnck; apply C.sideNot_mem_set_of_abs; right; simp only; zuoch
      have hr : 0 < min ztwkz ztnkb :=
        lt_min by_simp_all by_linarith
      zqdc
      rw [hnext, C.sideWalk_vtx_two, C.sideWalk_vtx_three] at hxl
      simp only [det] at hxl hx
      zqdb
      have hm1 := min_le_left ztwkz ztnkb
      have hm2 := min_le_right ztwkz ztnkb
      zqdd
      have e1 : ztphj := by_nlinarith
      exact ⟨ztsr,
        C.sideNot_mem_slit_of_low by_nlinarith⟩
    · -- the right side
      have hne : ztehh := by
        rw [hnext, C.sideWalk_vtx_three, C.sideWalk_vtx_four]
        intro h; have := congrArg Prod.snd h; simp only at this; linarith
      have hq : sidePt ztft 3 t = ztkpy := by
        unfold sidePt; rw [hnext, C.sideWalk_vtx_three, C.sideWalk_vtx_four]
        zqdj
        ring
      have hset : sidePt ztft 3 t ∉ C.set := by
        zvnck; apply C.sideNot_mem_set_of_abs; left; simp only; zuoqo
      have hr : 0 < min ztwkz ztcej :=
        by_simp_all
      zqdc
      rw [hnext, C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hxl
      simp only [det] at hxl hx
      zqdb
      have hm1 := min_le_left ztwkz ztcej
      have hm2 := min_le_right ztwkz ztcej
      zqdd
      zqfu
      exact ⟨ztsr,
        C.sideNot_mem_slit_of_fst by_nlinarith⟩
    · -- the top side, east of the slit
      have hne : (C.sideWalk β).vtx 4 ≠ (C.sideWalk β).vtx (ztstc % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_four, C.sideWalk_vtx_five]
        zqdz
      have hq : sidePt ztft 4 t = ztjhi := by
        unfold sidePt; rw [hnext, C.sideWalk_vtx_four, C.sideWalk_vtx_five]
        zqdi
      have hset : sidePt ztft 4 t ∉ C.set := by
        zqfz
      have hr : 0 < min ztyrx ztysi :=
        by_simp_all
      zqdc
      rw [hnext, C.sideWalk_vtx_four, C.sideWalk_vtx_five] at hxl
      zqel
      zqdb
      have hm1 := min_le_left ztyrx ztysi
      have hm2 := min_le_right ztyrx ztysi
      zqet
      exact ⟨ztsr,
        C.sideNot_mem_slit_of_fst by_nlinarith⟩
    · -- down the slit
      have hne : (C.sideWalk β).vtx 5 ≠ (C.sideWalk β).vtx (ztngt % (C.sideWalk β).n) := by
        rw [hnext, C.sideWalk_vtx_five, C.sideWalk_vtx_six]; exact C.sideSlitTop_ne_top
      have hq : sidePt ztft 5 t = ztjho := by
        unfold sidePt; rw [hnext, C.sideWalk_vtx_five, C.sideWalk_vtx_six]
        zqdi
      have hset : sidePt ztft 5 t ∉ C.set := by
        zvnck; apply C.sideNot_mem_set_of_high; simp only; nlinarith
      have hr : 0 < min ztwox
          ztcej :=
        by_simp_all
      zqdc
      rw [hnext, C.sideWalk_vtx_five, C.sideWalk_vtx_six] at hxl
      zqel
      zqdb
      have hm1 := min_le_left ztwox
        ztcej
      have hm2 := min_le_right ztwox
        ztcej
      zqdk
      have e1 : C.top.1 < x.1 := by_nlinarith
      exact ⟨⟨by_grind, abs_lt.2 by_grind⟩,
        C.sideNot_mem_slit_of_fst (ne_of_gt e1)⟩
  · zvohk; exact C.sideClean_slit_up β by_simp_all

/-! ### The corrected walk: nondegeneracy, trace and cleanness of every position -/
theorem sideWalk_lt_cases (β : Bool) {p : ℕ} (hp : p < (C.sideWalk β).n) :
    p ≤ 5 ∨ (∃ i, i < 2 * C.m ∧ p = i + 6) ∨ p = 2 * C.m + 6 := by
  rw [sideWalk_n] at hp
  zujst
  · omega
  · zugjn
    · omega
    · exact Or.inr (Or.inl ⟨p - 6, by_omega, by_omega⟩)

/-- The corrected walk has nondegenerate edges. -/
theorem sideWalk_nd (hP : C.P.Simple) (β : Bool) :
    ∀ p < (C.sideWalk β).n, (C.sideWalk β).vtx p ≠ (C.sideWalk β).vtx ztxao := by
  zuda
  zqfy
  have hta := abs_lt.1 C.abs_top_fst_lt_radius
  zqdh
  · zqdf
    zumnr
    interval_cases p
    · zqfh
      zqdz
    · zqfi
      grind
    · zqfj
      grind
    · zqfk
      grind
    · zqfl
      zqdz
    · zqfm
      exact C.sideSlitTop_ne_top
  · zqea
    unfold sideTour
    zqei
    · zuhlm
    · zuezv
  · zqeu
    exact C.sideSlitTop_ne_top.symm
theorem sideLerp_mem_set {a b : ℕ} (hab : b = a + 1 ∨ b + 1 = a) (hle : a ≤ C.m) (hle' : b ≤ C.m)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : lerp (C.vertex a) ztgdi t ∈ C.set := by
  zufzu
  · exact ⟨a, by_omega, by rw [C.chainEdge_eq]; exact lerp_mem_segment _ _ ht0 ht1⟩
  · refine ⟨b, by_omega, ?_⟩
    rw [C.chainEdge_eq, segment_comm]
    zujve
theorem sideNot_mem_dom_of_abs {x : Point} (h : |x.1| = C.radius ∨ |x.2| = C.radius) :
    x ∉ C.dom := fun hx => by
  have := hx.1
  zuy
  · exact absurd this.1 by_simp_all
  · exact absurd this.2 by_simp_all

/-- **The corrected walk avoids the domain.** -/
theorem sideWalk_trace (β : Bool) :
    ∀ p < (C.sideWalk β).n, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → sidePt ztft p t ∉ C.dom := by
  zukjr
  zqfy
  zqdh
  · zqdf
    zucky
    zumnr
    interval_cases p
    · zqfh
      zueff
    · zqfi
      zufdz
    · zqfj
      apply C.sideNot_mem_dom_of_abs; right; simp [lerp, abs_of_pos hR]
    · zqfk
      zufdz
    · zqfl
      zueff
    · zqfm
      zudqe
      apply C.not_mem_slit_of_mem_dom hd
      rw [slit, segment_comm]; exact lerp_mem_segment _ _ ht0 ht1
  · zucky
    zqea
    zudqe
    apply C.not_mem_set_of_mem_dom hd
    unfold sideTour
    zqei
    · exact C.sideLerp_mem_set zteg ztdfj ztemb ht0 ht1
    · exact C.sideLerp_mem_set ztbho ztdfj ztemb ht0 ht1
  · zucky
    zqeu
    zudqe
    apply C.not_mem_slit_of_mem_dom hd
    zujve

/-- **Every position of the corrected walk is clean for the domain**: near every point of the
walk, no point outside `dom C` lies in the open left sector of the walk there. -/
theorem sideWalk_clean (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) :
    ∀ p < (C.sideWalk β).n, ∀ t : ℝ, 0 ≤ t → t < 1 → SideClean ztft C.dom p t := by
  zukjr
  rcases ht0.lt_or_eq with htp | htz
  · zqdh
    · exact C.sideClean_box_edge β ztmbw by_simp_all
    · exact C.sideClean_tour_edge hP β hi by_simp_all
    · exact C.sideClean_slit_up β by_simp_all
  · subst htz
    zqdh
    · exact C.sideClean_box_vertex β h5
    · zqfn
      · subst h0; exact C.sideClean_top_first hP hβ
      · exact C.sideClean_tour_vertex hP hβ h0 hi
    · exact C.sideClean_top_last hP hβ

/-! ### Disjointness of the left sectors of distinct positions at a common point -/

/-- Two distinct inner visits of the same chain vertex leave it in opposite directions. -/
theorem sideTour_two_visits (β : Bool) {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m)
    (hne : i ≠ i') (heq : C.sideIdx β i = C.sideIdx β i') :
    (C.sideIdx β ztg = C.sideIdx β i + 1 ∧ C.sideIdx β ztduy + 1 = C.sideIdx β i) ∨
      (C.sideIdx β ztg + 1 = C.sideIdx β i ∧ C.sideIdx β ztduy = C.sideIdx β i + 1) := by
  zqes
  have hj : ztty % ztbb ≠ ztlee % ztbb := by
    zuq
    exact hne (Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' _ h) hi hi')
  rw [C.sideIdx_succ, C.sideIdx_succ]
  rw [sideIdx_eq, sideIdx_eq] at heq
  rw [sideIdx_eq]
  have h1 := Nat.mod_lt ztty hm2
  have h2 := Nat.mod_lt ztlee hm2
  generalize ztty % ztbb = j at hj heq h1 ⊢
  generalize ztlee % ztbb = j' at hj heq h2 ⊢
  unfold sideE at *
  grind
theorem sideTop_nonSpike_up (k : ℕ) (hk : k ≤ C.m) :
    sideNonSpike ztlef ztyy := by
  zugbj
  zullq
  zubnz
  unfold sideCross sideDot at *
  simp only [Prod.fst_sub, Prod.snd_sub, slitTop, sub_self, mul_zero, sub_zero] at hc hd
  nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hy) (sub_pos.2 htop).le]
theorem sideTour_one_eq_last (β : Bool) (hT : C.topIdx = 0 ∨ C.topIdx = C.m) :
    C.sideTour β 1 = C.sideTour β ztdl := by
  obtain ⟨-, -, h3, h4, -⟩ := C.sideTour_nbrs β
  zqdu
  unfold sideTour
  grind

/-- The three corners at the top vertex have pairwise disjoint left sectors. -/
theorem sideTop_disj (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) (x : Point) :
    ¬ (sideLeftOf C.slitTop C.top ztdfk x ∧
        sideLeftOf ztwto C.top C.slitTop x) ∧
      (ztndg →
        ¬ (sideLeftOf C.slitTop C.top ztdfk x ∧
          sideLeftOf ztdfk C.top ztwto x)) ∧
      (ztndg →
        ¬ (sideLeftOf ztwto C.top C.slitTop x ∧
          sideLeftOf ztdfk C.top ztwto x)) := by
  have hn0 := sub_ne_zero_of_ne' ztcld
  have hp0 : ztpix :=
    sub_ne_zero_of_ne' ztdsw
  have hU0 := sub_ne_zero_of_ne' C.sideSlitTop_ne_top
  have hnU := C.sideTop_nonSpike_up _ ztnjx
  zucfg
  zusk
  · zubf
    zucuq
    · rw [← C.sideTour_one_eq_last β hT] at h2
      exact sideCcw_asymm hn0 hnU h1 h2
    · have hord : sideCcw ztblu ztyy
          ztwmj := by
        zqds
        · omega
        · omega
        omega
      have hT' : 0 < C.topIdx ∧ C.topIdx < C.m := by
        have := C.topIdx_le; omega
      have hns := C.sideTop_nonSpike hP β hT'.1 hT'.2
      have h3 := sideCcw_rotate hn0 hU0 hns hord
      have h4 := sideCcw_sub_left hU0 h3 h2
      exact sideCcw_asymm hn0 hnU h1 h4
  · zugbi
    have hord : sideCcw ztblu ztyy
        ztwmj := by
      zqds
      · omega
      · omega
      omega
    have h3 := sideCcw_sub_left hn0 hord h1
    zujvi
  · zugbi
    have hord : sideCcw ztblu ztyy
        ztwmj := by
      zqds
      · omega
      · omega
      omega
    have h3 := sideCcw_sub_right hn0 hU0 hp0 hord h1
    zujvi

/-- The points of the box block of the walk. -/
theorem sidePt_box (β : Bool) (t : ℝ) :
    sidePt ztft 0 t = ztipy ∧
    sidePt ztft 1 t = ztkpp ∧
    sidePt ztft 2 t = ztjct ∧
    sidePt ztft 3 t = ztkpy ∧
    sidePt ztft 4 t = ztjhi ∧
    sidePt ztft 5 t = ztjho ∧
    sidePt ztft ztcc t = ztyor := by
  zqef
  have h1 : ∀ p, p ≤ 5 → ztr % (C.sideWalk β).n = p + 1 := fun p hp =>
    C.sideWalk_mod_small β by_omega
  zucky
  refine ztuv
  · rw [h1 0 by_norm_num, C.sideWalk_vtx_zero, show (0 + 1 : ℕ) = 1 from rfl, C.sideWalk_vtx_one]
    zqdi
  · rw [h1 1 by_norm_num, C.sideWalk_vtx_one, show (1 + 1 : ℕ) = 2 from rfl, C.sideWalk_vtx_two]
    zqdj
    ring
  · rw [h1 2 by_norm_num, C.sideWalk_vtx_two, show (2 + 1 : ℕ) = 3 from rfl,
      C.sideWalk_vtx_three]
    zqdj
    ring
  · rw [h1 3 by_norm_num, C.sideWalk_vtx_three, show (3 + 1 : ℕ) = 4 from rfl,
      C.sideWalk_vtx_four]
    zqdj
    ring
  · rw [h1 4 by_norm_num, C.sideWalk_vtx_four, show (4 + 1 : ℕ) = 5 from rfl,
      C.sideWalk_vtx_five]
    zqdi
  · rw [h1 5 by_norm_num, C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 6 from rfl,
      C.sideWalk_vtx_six]
    zqdi
  · zqeu
    zqdi

/-- The points of the box block are off the chain, and those on the open vertical sides of the
box are on the edges `1` or `3`. -/
theorem sideWalk_box_pt (β : Bool) {p : ℕ} {t : ℝ} (hp : p ≤ 5 ∨ ztcap)
    (ht : 0 ≤ t) (ht1 : t < 1) :
    sidePt ztft p t ∉ C.set ∧
      (|(sidePt ztft p t).1| = C.radius → |(sidePt ztft p t).2| < C.radius →
        ((p = 1 ∧ (sidePt ztft p t).1 = -C.radius) ∨
          (p = 3 ∧ (sidePt ztft p t).1 = C.radius)) ∧ 0 < t) := by
  zqfy
  have hta := abs_lt.1 C.abs_top_fst_lt_radius
  zubnz
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := C.sidePt_box β t
  rcases hp with hp | ⟨rfl, htp⟩
  · interval_cases p
    · zujhv
      zqdr
      grind
    · zukd
      zqdr
      zqga
      · zuclh
      grind
    · zucjj
      zqdr
      grind
    · zvnak
      zqdr
      zqga
      · zuclh
      grind
    · zujhw
      zqdr
      grind
    · zujhx
      refine ⟨C.sideNot_mem_set_of_high (by simp only; nlinarith), ?_⟩
      grind
  · zummg
    refine ⟨C.sideNot_mem_set_of_high by_simp_all, ?_⟩
    grind
theorem sidePt_tour (β : Bool) {i : ℕ} (hi : i < 2 * C.m) (t : ℝ) :
    sidePt ztft ztcy t = lerp ztnjz ztztb t := by
  zucky
  zqea
theorem sideLeft_tour_first (β : Bool) (x : Point) :
    sideLeft ztft ztfmo 0 x ↔ sideLeftOf C.slitTop C.top ztdfk x := by
  zqef
  rw [sideLeft_zero, C.sideWalk_prev_six β, C.sideWalk_next_tour β by_omega,
    C.sideWalk_vtx_tour β by_omega, C.sideWalk_vtx_tour β by_omega, sideTour_zero]
  rfl
theorem sideLeft_tour_inner (β : Bool) {i : ℕ} (hi0 : 0 < i) (hi : i < 2 * C.m) (x : Point) :
    sideLeft ztft ztcy 0 x ↔
      sideLeftOf (C.sideTour β ztei) ztnjz ztztb x := by
  rw [sideLeft_zero, C.sideWalk_prev_tour β hi0 hi.le, C.sideWalk_next_tour β hi,
    C.sideWalk_vtx_tour β by_omega, C.sideWalk_vtx_tour β hi.le, C.sideWalk_vtx_tour β by_omega]
theorem sideLeft_tour_last (β : Bool) (x : Point) :
    sideLeft ztft ztcc 0 x ↔
      sideLeftOf ztwto C.top C.slitTop x := by
  zqef
  rw [sideLeft_zero, C.sideWalk_prev_tour β by_omega le_rfl, C.sideWalk_next_last β,
    C.sideWalk_vtx_tour β by_omega, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
  rfl

/-- A point inside a tour edge is a point of an open chain edge. -/
theorem sideTour_open (β : Bool) {i : ℕ} (hi : i < 2 * C.m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ k, k < C.m ∧ ∃ s ∈ Ioo (0 : ℝ) 1,
      sidePt ztft ztcy t = lerp ztib ztwkj s ∧
      ((C.sideIdx β i = k ∧ C.sideIdx β ztg = k + 1) ∨
        (C.sideIdx β i = k + 1 ∧ C.sideIdx β ztg = k)) := by
  zukor
  zufgw

  unfold sideTour
  zqei
  · exact ⟨C.sideIdx β i, by_omega, t, ht, by zvmwc, by_omega⟩
  · refine ⟨C.sideIdx β _, by_omega, 1 - t, by_simp_all, ?_,
      Or.inr ⟨h.symm, rfl⟩⟩
    zuezu
    zqeq

/-- **Disjointness at the chain**: two distinct positions of the corrected walk at the same point
of the chain have disjoint open left sectors. -/
theorem sideDisj_tour (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) {i i' : ℕ} {t t' : ℝ}
    (hi : i ≤ 2 * C.m) (hi' : i' ≤ 2 * C.m) (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (hit : i = 2 * C.m → t = 0) (hit' : i' = 2 * C.m → t' = 0) (hne : i = i' → t ≠ t')
    (heq : sidePt ztft ztcy t = sidePt ztft ztetl t') (x : Point) :
    ¬ (sideLeft ztft ztcy t x ∧ sideLeft ztft ztetl t' x) := by
  zqef
  -- the vertex case
  have hvv : ∀ j j' : ℕ, j < j' → j' ≤ 2 * C.m → C.sideIdx β j = C.sideIdx β j' →
      ¬ (sideLeft ztft ztjza 0 x ∧ sideLeft ztft ztocb 0 x) := by
    intro j j' hjj hj' hidx
    by_cases hT : C.sideIdx β j = C.topIdx
    · obtain ⟨d1, d2, d3⟩ := C.sideTop_disj hP hβ x
      zqep
      · zubvi
        rw [C.sideLeft_tour_first]
        zujdx
        · zukal
          obtain ⟨hT0, hTm⟩ := C.sideTour_top_inner β hjj h2 hT'
          obtain ⟨hp1, hn1⟩ := C.sideTour_top_mid β hjj h2 hT0 hTm hT'
          rw [C.sideLeft_tour_inner β hjj h2]
          unfold sideTour at *
          rw [hp1, hn1, hT']
          exact d2 by_omega
        · subst h2; rw [C.sideLeft_tour_last]; exact d1
      · zujdx
        · -- two inner visits of the top vertex: impossible
          exfalso
          zukal
          obtain ⟨hT0, hTm⟩ := C.sideTour_top_inner β h0 by_omega hT
          have e1 := (C.sideTour_top_mid β h0 by_omega hT0 hTm hT).2
          have e2 := (C.sideTour_top_mid β by_omega h2 hT0 hTm hT').2
          rcases C.sideTour_two_visits β by_omega h2 by_omega hidx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
            omega
        · zuhqi
          have hjm : ztmwb := by_omega
          obtain ⟨hT0, hTm⟩ := C.sideTour_top_inner β h0 hjm hT
          obtain ⟨hp1, hn1⟩ := C.sideTour_top_mid β h0 hjm hT0 hTm hT
          rw [C.sideLeft_tour_inner β h0 hjm, C.sideLeft_tour_last]
          unfold sideTour at *
          rw [hp1, hn1, hT]
          exact fun h => d3 by_omega ⟨h.2, h.1⟩
    · -- a chain vertex other than the top vertex: two inner visits, forwards and backwards
      have hj0 : ztpht := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; exact absurd (C.sideIdx_zero β) hT
        omega
      have hj2 : j' < 2 * C.m := by
        rcases lt_or_eq_of_le hj' with h | h
        · zubh
        · subst h; exact absurd (hidx.trans (C.sideIdx_two_m β)) hT
      rw [C.sideLeft_tour_inner β hj0 by_omega, C.sideLeft_tour_inner β by_omega hj2]
      have hv := C.sideTour_two_visits β by_omega hj2 by_omega hidx
      have hk := C.sideIdx_le β j
      have hk1 := C.sideIdx_le β ztl
      have hk1' := C.sideIdx_le β ztdhr
      rcases C.sideTour_corner β hj0 by_omega with ⟨a0, am, ap, an⟩ | ⟨a0, am, ap, an⟩ |
          ⟨a0, ap, an⟩ | ⟨a0, ap, an⟩ <;>
        rcases C.sideTour_corner β by_omega hj2 with ⟨b0, bm, bp, bn⟩ |
          ⟨b0, bm, bp, bn⟩ | ⟨b0, bp, bn⟩ | ⟨b0, bp, bn⟩
      all_goals first
        | (exfalso; rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
        | skip
      all_goals unfold sideTour sideLeftOf
      · -- forward then backward
        have e1 : C.sideIdx β zthv = C.sideIdx β j - 1 := by_omega
        have e2 : C.sideIdx β zttpz = C.sideIdx β j + 1 := by_omega
        have e3 : C.sideIdx β ztdhr = C.sideIdx β j - 1 := by_omega
        rw [e1, e2, e3, an, ← hidx]
        have hns := (C.sideChain_nonSpike hP a0 am).1
        exact fun h => sideCcw_asymm (sub_ne_zero_of_ne' (C.sideVertex_succ_ne hP _).symm)
          hns h.1 h.2
      · -- backward then forward
        have e1 : C.sideIdx β ztl = C.sideIdx β j - 1 := by_omega
        have e2 : C.sideIdx β zttpz = C.sideIdx β j - 1 := by_omega
        have e3 : C.sideIdx β ztdhr = C.sideIdx β j + 1 := by_omega
        rw [ap, e1, e2, e3, ← hidx]
        have hns := (C.sideChain_nonSpike hP a0 am).2
        exact fun h => sideCcw_asymm (sub_ne_zero_of_ne' (C.sideVertex_pred_ne hP a0))
          hns h.1 h.2
  -- the edge case
  have hee : ∀ j j' : ℕ, j < 2 * C.m → j' < 2 * C.m → ∀ s s' : ℝ, s ∈ Ioo (0 : ℝ) 1 →
      s' ∈ Ioo (0 : ℝ) 1 → (j = j' → s ≠ s') →
      sidePt ztft ztjza s = sidePt ztft ztocb s' →
      ¬ (sideLeft ztft ztjza s x ∧ sideLeft ztft ztocb s' x) := by
    intro j j' hj hj' s s' hs hs' hne' heq'
    obtain ⟨k, hk, r, hr, hpk, hk1⟩ := C.sideTour_open β hj hs
    obtain ⟨k', hk', r', hr', hpk', hk1'⟩ := C.sideTour_open β hj' hs'
    have hkk : k = k' := by
      by_contra hkk
      have hmem : lerp ztib ztwkj r ∈ C.chainEdge k' := by
        rw [← hpk, heq', hpk', C.chainEdge_eq]; exact lerp_mem_segment _ _ hr'.1.le hr'.2.le
      exact C.sideOpen_not_mem_chainEdge hP hk hk' ztvbi hr hmem
    subst hkk
    have hnd := C.sideWalk_nd hP β
    rw [sideLeft_edge ztzwb hs,
      sideLeft_edge ztzwb hs',
      C.sideWalk_next_tour β hj, C.sideWalk_next_tour β hj', C.sideWalk_vtx_tour β hj.le,
      C.sideWalk_vtx_tour β by_omega, C.sideWalk_vtx_tour β hj'.le,
      C.sideWalk_vtx_tour β by_omega]
    unfold sideTour
    have hsame : ¬ (C.sideIdx β j = C.sideIdx β j') := by
      intro hidx
      by_cases hjj : j = j'
      · subst hjj
        apply hne' rfl
        rw [C.sidePt_tour β hj, C.sidePt_tour β hj] at heq'
        exact Geometry.lerp_injective (by
          have := hnd ztjza zthfc
          rwa [C.sideWalk_next_tour β hj, C.sideWalk_vtx_tour β hj.le,
            C.sideWalk_vtx_tour β by_omega] at this) heq'
      · rcases C.sideTour_two_visits β hj hj' hjj hidx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          rcases hk1 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> rcases hk1' with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;> omega
    rcases hk1 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> rcases hk1' with ⟨d1, d2⟩ | ⟨d1, d2⟩
    · omega
    · zqev
    · zqev
    omega
  -- assembling the cases
  rcases ht.lt_or_eq with htp | htz <;> rcases ht'.lt_or_eq with htp' | htz'
  · exact hee i i' (lt_of_le_of_ne hi by_grind)
      (lt_of_le_of_ne hi' by_grind) t t' by_grind by_grind hne heq
  · -- a vertex and an open edge point cannot coincide
    exfalso
    subst htz'
    have hil : ztdrl := by_grind
    obtain ⟨k, hk, r, hr, hpk, -⟩ := C.sideTour_open β hil ztuij
    rw [hpk, sidePt_zero, C.sideWalk_vtx_tour β hi'] at heq
    exact C.sideOpen_ne_vertex hP hr heq
  · exfalso
    subst htz
    have hil : ztsjj := by_grind
    obtain ⟨k, hk, r, hr, hpk, -⟩ := C.sideTour_open β hil ⟨htp', ht1'⟩
    rw [hpk, sidePt_zero, C.sideWalk_vtx_tour β hi] at heq
    exact C.sideOpen_ne_vertex hP hr heq.symm
  · subst htz htz'
    have hii : i ≠ i' := by_grind
    rw [sidePt_zero, sidePt_zero, C.sideWalk_vtx_tour β hi, C.sideWalk_vtx_tour β hi'] at heq
    have hidx := C.sideVertex_inj hP ztdfj (C.sideIdx_le β i') heq
    grind
theorem sideWalk_pos_cases (β : Bool) {p : ℕ} (hp : p < (C.sideWalk β).n) {t : ℝ} (ht : 0 ≤ t) :
    ztzgr ∨ (∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ (i = 2 * C.m → t = 0)) := by
  zqdh
  · omega
  · exact Or.inr ⟨i, hi.le, rfl, by_grind⟩
  · zukmi
    · simp_all
    simp_all
theorem sideWalk_tour_pt_mem (β : Bool) {i : ℕ} {t : ℝ} (hi : i ≤ 2 * C.m) (hit : i = 2 * C.m → t = 0)
    (ht : 0 ≤ t) (ht1 : t < 1) : sidePt ztft ztcy t ∈ C.set := by
  rcases lt_or_eq_of_le hi with hi | hi
  · zukor
    unfold sideTour
    zqei
    · exact C.sideLerp_mem_set zteg ztdfj ztemb ht ht1.le
    · exact C.sideLerp_mem_set ztbho ztdfj ztemb ht ht1.le
  · zuipx
    rw [hit rfl, sidePt_zero, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
    exact C.top_mem_set

/-- **Disjointness of the left sectors at a chord endpoint.**  Two distinct positions of the
corrected walk at a common point of the chain, or of an open vertical side of the box, have
disjoint open left sectors. -/
theorem sideWalk_disj (hP : C.P.Simple) {β : Bool} (hβ : C.SideGood β) {pa p : ℕ} {ta t : ℝ}
    (hpa : pa < (C.sideWalk β).n) (hta : 0 ≤ ta) (hta1 : ta < 1)
    (hp : p < (C.sideWalk β).n) (ht : 0 ≤ t) (ht1 : t < 1) (hne : p = pa → t ≠ ta)
    (heq : sidePt ztft p t = sidePt ztft pa ta)
    (hq : sidePt ztft pa ta ∈ C.set ∨
      (|(sidePt ztft pa ta).1| = C.radius ∧ |(sidePt ztft pa ta).2| < C.radius))
    (x : Point) : ¬ (sideLeft ztft pa ta x ∧ sideLeft ztft p t x) := by
  zugma
  -- a point of the chain is not on an open vertical side
  have hsetv : ∀ y ∈ C.set, |y.1| = C.radius → False := fun y hy h => by
    have := (C.abs_le_coordBound_of_mem_set hy).1; linarith
  rcases C.sideWalk_pos_cases β hpa hta with hA | ⟨ia, hia, rfl, hiat⟩ <;>
    rcases C.sideWalk_pos_cases β hp ht with hX | ⟨i, hi, rfl, hit⟩
  · -- two positions of the box block
    zufjd
    obtain ⟨hX1, hX2⟩ := C.sideWalk_box_pt β hX ht ht1
    rcases hq with hq | ⟨hq1, hq2⟩
    · simp_all
    · obtain ⟨hA3, hA4⟩ := hA2 hq1 hq2
      zvnbo at hq1 hq2
      obtain ⟨hX3, hX4⟩ := hX2 hq1 hq2
      zqfy
      have hpp : ztskw := by
        grind
      subst hpp
      exfalso
      apply hne rfl
      exact Geometry.lerp_injective (C.sideWalk_nd hP β p hp) heq
  · exfalso
    zufjd
    have hmem := C.sideWalk_tour_pt_mem β hi hit ht ht1
    simp_all
  · exfalso
    obtain ⟨hX1, -⟩ := C.sideWalk_box_pt β hX ht ht1
    have hmem := C.sideWalk_tour_pt_mem β hia hiat hta hta1
    simp_all
  · exact C.sideDisj_tour hP hβ hia hi hta hta1 ht ht1 hiat hit
      ztbay heq.symm x

/-! ### Chords as segments of the walk's complement -/
omit C in
theorem sideKey_inj {p p' : ℕ} {t t' : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h : (p : ℝ) + t = p' + t') : p = p' ∧ t = t' := by
  have hpp : p = p' := by
    rcases lt_trichotomy p p' with hlt | heq | hgt
    · exfalso
      have : (p : ℝ) + 1 ≤ p' := by exact_mod_cast hlt
      linarith
    · omega
    · exfalso
      have : (p' : ℝ) + 1 ≤ p := by exact_mod_cast hgt
      linarith
  simp_all
omit C in
/-- The two arcs cut by two distinct keys partition the other keys. -/
theorem sideInArc_swap {a b x : ℝ} (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    sideInArc a b x ↔ ¬ sideInArc b a x := by
  zuiq

/-! ### A correct turn at the top vertex always exists -/
omit C in
/-- **Coverage**: a direction `X` that lies on neither closed ray of the (non-spike) directions
`A`, `B` is strictly inside one of the two complementary counterclockwise arcs between them. -/
theorem sideCcw_or {A B X : Point} (hA : A ≠ 0) (hB : B ≠ 0) (hns : sideNonSpike A B)
    (hXA : ¬ ztevl)
    (hXB : ¬ ztkfc) : sideCcw A X B ∨ sideCcw B X A := by
  zuheb
  zqfc
  have eAB : sideCross B A = -sideCross A B := sideCross_swap _ _
  have eXA : sideCross X A = -sideCross A X := sideCross_swap _ _
  have eXB : ztieb := sideCross_swap _ _
  have D1 := side_dotCross A X B
  have D2 := side_dotCross B X A
  rw [eXB] at D1
  rw [eAB, eXA] at D2
  zufqe
  rw [eAB, eXA, eXB]
  push Not at hXA hXB
  rcases lt_trichotomy (sideCross A B) 0 with hab | hab | hab
  · -- `B` is clockwise from `A`: the arc from `B` to `A` is convex
    by_cases h1 : 0 < sideCross B X ∧ 0 < -sideCross A X
    · simp_all
    · left; right; left
      refine ⟨hab, ?_⟩
      zukr
      zueuy

      rcases lt_or_eq_of_le (show 0 ≤ sideCross B X by linarith) with hy | hy
      · have hx : sideCross A X = 0 := by_grind
        zugvq
        nlinarith [mul_pos_of_neg_of_neg ztvui hab, mul_pos hAA hy]
      · rw [← hy, zero_mul, add_zero] at D2
        nlinarith [mul_neg_of_neg_of_pos (hXB hy.symm) (neg_pos.2 hab),
          mul_nonneg hBB.le ztvzu]
  · -- straight
    have hL := side_lagrange A B
    have hd : sideDot A B < 0 := by
      rcases lt_trichotomy (sideDot A B) 0 with h | h | h
      · zubh
      · rw [hab, h] at hL; nlinarith [mul_pos hAA hBB]
      · exact absurd by_grind hns
    rw [hab, mul_zero] at D1
    rcases lt_trichotomy (sideCross A X) 0 with hx | hx | hx
    · right; right; right; left
      refine ⟨by_linarith, by rw [sideDot_comm]; exact hd, ?_⟩
      nlinarith [mul_pos_of_neg_of_neg hx hd]
    · exfalso
      zugvq
      have hy : ztsmg := by
        grind
      have DD := side_dotDot A X B
      rw [hx, zero_mul, add_zero] at DD
      have h5 := hXB hy
      rw [sideDot_comm] at h5
      nlinarith [mul_pos_of_neg_of_neg ztvui hd, mul_neg_of_pos_of_neg hAA h5]
    grind
  · -- `B` is counterclockwise from `A`: the arc from `A` to `B` is convex
    by_cases h1 : 0 < sideCross A X ∧ 0 < -sideCross B X
    · simp_all
    · zurx
      refine ztkix
      zukr
      zueuy

      rcases lt_or_eq_of_le (show 0 ≤ sideCross A X by linarith) with hx | hx
      · have hy : ztsmg := by_grind
        rw [hy, zero_mul, add_zero] at D2
        nlinarith [mul_pos_of_neg_of_neg (hXB hy) (neg_neg_of_pos hab), mul_pos hBB hx]
      · rw [← hx, zero_mul, add_zero] at D1
        nlinarith [mul_neg_of_neg_of_pos (hXA hx.symm) hab,
          mul_nonneg hAA.le ztvzu]
theorem sideIdx_nbrs_true (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) :
    C.sideIdx true 1 = C.topIdx + 1 ∧ C.sideIdx true ztdl = C.topIdx - 1 := by
  zugbp
  have hs : C.sideS true % ztbb = C.topIdx := by
    unfold sideS; zuohl; exact Nat.mod_eq_of_lt by_omega
  zubqb
  rcases side_mod_cases ztybe with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zvmxx <;> unfold sideE <;> split_ifs <;> omega
theorem sideIdx_nbrs_false (hT0 : 0 < C.topIdx) (hTm : C.topIdx < C.m) :
    C.sideIdx false 1 = C.topIdx - 1 ∧ C.sideIdx false ztdl = C.topIdx + 1 := by
  zugbp
  have hs : C.sideS false % ztbb = 2 * C.m - C.topIdx := by
    unfold sideS; simp only [Bool.false_eq_true, ↓reduceIte]; exact Nat.mod_eq_of_lt by_omega
  zubqb
  rcases side_mod_cases ztxor with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zvmxx <;> unfold sideE <;> split_ifs <;> omega
open Classical in
/-- **The correct choice of the turn at the top vertex**: `true` (leave the top vertex towards
`v_{T+1}`, as `boundaryWalk` does) iff the slit direction lies strictly inside the
counterclockwise arc from `v_{T+1}` to `v_{T-1}` around the top vertex. -/
noncomputable def sideBeta : Bool :=
  decide (sideCcw ztydq ztyy
    ztydr)
open Classical in
/-- Characterization of `sideBeta`. -/
theorem sideBeta_eq_true_iff : C.sideBeta = true ↔ sideCcw ztydq
    ztyy ztydr := by
  unfold sideBeta; simp
theorem sideVertex_sub_top_ne (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) (hkT : k ≠ C.topIdx) :
    C.vertex k - C.top ≠ 0 :=
  sub_ne_zero_of_ne' (fun h => hkT (C.sideVertex_inj hP hk C.topIdx_le h))
theorem sideUp_not_ray (k : ℕ) (hk : k ≤ C.m) (hne : C.vertex k - C.top ≠ 0) :
    ¬ (sideCross ztlef ztyy = 0 ∧
      0 ≤ sideDot ztlef ztyy) := by
  zugbj
  zullq
  zubnz
  zufqo
  unfold sideCross at hc
  zumup
  simp only [Prod.fst_sub, Prod.snd_sub, slitTop, sub_self, mul_zero, sub_zero,
    zero_add] at hc hd
  have h1 : (C.vertex k).1 - C.top.1 = 0 := by
    grind
  have h2 : (C.vertex k).2 - C.top.2 = 0 := by_nlinarith
  grind

/-- **The corrected walk turns correctly at the top vertex**: `C.sideBeta` satisfies the order
condition `SideGood` needed by `side_lemma21`. -/
theorem sideGood_sideBeta (hP : C.P.Simple) : C.SideGood C.sideBeta := by
  unfold SideGood
  zujsx
  · omega
  by_cases hTm : C.topIdx = C.m
  · omega
  zqfg
  have h0 := Nat.pos_of_ne_zero hT0
  have hm : ztmsx := by_omega
  zulw
  have hA := C.sideVertex_sub_top_ne hP (k := C.topIdx + 1) by_omega by_omega
  have hB := C.sideVertex_sub_top_ne hP (k := C.topIdx - 1) by_omega by_omega
  have hns : sideNonSpike ztriv ztriv :=
    (C.sideChain_nonSpike hP h0 hm).1
  have hor := sideCcw_or hA hB hns ztrit
    ztriu
  cases hb : C.sideBeta with
  | true =>
    have h := C.sideBeta_eq_true_iff.1 hb
    obtain ⟨e1, e2⟩ := C.sideIdx_nbrs_true h0 hm
    unfold sideTour; zvmws; exact h
  | false =>
    have h : ¬ sideCcw _ _
        _ := fun h' => by
      have := C.sideBeta_eq_true_iff.2 h'
      simp_all
    obtain ⟨e1, e2⟩ := C.sideIdx_nbrs_false h0 hm
    unfold sideTour; zvmws
    exact hor.resolve_left h

/-! ### Every chord endpoint is attached to the corrected walk -/
omit C in
/-- A segment leaving a point of a segment `[v, w]` along the line of `[v, w]` (forwards when
the point is `v`) starts inside `[v, w]`. -/
theorem side_overlap {v w e e' : Point} {s₀ : ℝ} (hvw : v ≠ w) (hs0 : 0 ≤ s₀) (hs1 : s₀ < 1)
    (he : e = lerp v w s₀) (hee : e' ≠ e) (hc : sideCross ztbez ztert = 0)
    (hd : s₀ = 0 → 0 ≤ sideDot ztbez ztert) :
    ∃ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ Chazelle.segment v w := by
  have hAA := sideDot_self_pos (sub_ne_zero_of_ne' hvw.symm)
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = sideDot (w - v) (e' - e) / sideDot (w - v) (w - v) := by_simp_all
  have hX1 : e'.1 - e.1 = μ * ztcww := by
    have key : sideDot ztbez ztbez * (e'.1 - e.1) =
        sideDot ztbez ztert * ztcww - sideCross ztbez ztert * ztcfj := by
      zufdp
    grind
  have hX2 : e'.2 - e.2 = μ * ztcfj := by
    have key : sideDot ztbez ztbez * (e'.2 - e.2) =
        sideDot ztbez ztert * ztcfj + sideCross ztbez ztert * ztcww := by
      zufdp
    grind
  have hμ0 : μ ≠ 0 := by
    grind
  obtain ⟨s, hs, hlo, hhi⟩ : ∃ s ∈ Ioo (0 : ℝ) 1, 0 ≤ s₀ + s * μ ∧ s₀ + s * μ ≤ 1 := by
    rcases lt_or_gt_of_ne hμ0 with hneg | hpos
    · have hs0' : ztphv := by
        zuvl
        · zubh
        · exfalso
          have h1 := hd h.symm
          have : 0 ≤ μ := by zvnhc; positivity
          linarith
      have hpos' : 0 < min ztcn (s₀ / -μ) := by_simp_all
      refine ⟨min _ _, ztzil,
        ?_, ?_⟩
      · have h1 : min ztcn _ ≤ s₀ / -μ := min_le_right _ _
        have h2 : min _ _ * -μ ≤ s₀ :=
          calc _ ≤ s₀ / -μ * -μ := mul_le_mul_of_nonneg_right h1 by_linarith
            _ = s₀ := by_grind
        linarith
      · nlinarith
    · have hpos' : 0 < min ztcn (ztndm / μ) := by_simp_all
      refine ⟨min _ _, ztzil,
        ?_, ?_⟩
      · nlinarith
      · have h1 : min ztcn _ ≤ ztndm / μ := min_le_right _ _
        have h2 : min _ _ * μ ≤ 1 - s₀ :=
          calc _ ≤ ztndm / μ * μ := mul_le_mul_of_nonneg_right h1 hpos.le
            _ = 1 - s₀ := div_mul_cancel₀ _ hpos.ne'
        linarith
  have he1 : e.1 = v.1 + s₀ * ztcww := by_simp_all
  have he2 : e.2 = v.2 + s₀ * ztcfj := by_simp_all
  refine ⟨s, hs, s₀ + s * μ, hlo, hhi, ?_⟩
  zubjw
  · zufbq
  · zujop

/-- **A chord leaves a chain vertex off the closed rays of its chain edges.** -/
theorem sideRay_free (hP : C.P.Simple) {j j' : ℕ} (hjj : j' = j + 1 ∨ j' + 1 = j) (hj : j ≤ C.m)
    (hj' : j' ≤ C.m) {e' : Point} (hee : e' ≠ C.vertex j)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztemc e' s ∈ C.dom) :
    ¬ (sideCross ztpwp ztrox = 0 ∧
      0 ≤ sideDot ztpwp ztrox) := by
  zugbj
  have hne : C.vertex j ≠ C.vertex j' := by
    zuklm
    · exact C.sideVertex_succ_ne hP j
    · exact (C.sideVertex_succ_ne hP j').symm
  obtain ⟨s, hs, hmem⟩ := side_overlap hne le_rfl zero_lt_one (lerp_zero _ _).symm hee hc
    (fun _ => hd)
  obtain ⟨t, ht0, ht1, ht⟩ := hmem
  have hset : lerp ztemc e' s ∈ C.set := by
    zvnup; exact C.sideLerp_mem_set hjj hj hj' ht0 ht1
  zulww
omit C in
/-- The left sector of the walk at the top vertex coming down the slit and leaving along a chain
edge going down contains the direction east. -/
theorem sideCcw_east {A U X : Point} (hU1 : U.1 = 0) (hU2 : 0 < U.2) (hX2 : X.2 = 0)
    (hX1 : 0 < X.1) (hA2 : A.2 ≤ 0) (hA : A ≠ 0)
    (hray : ¬ ztevl) : sideCcw A X U := by
  have hc1 : sideCross A U = A.1 * U.2 := by unfold sideCross; simp_all
  have hc2 : sideCross A X = -(A.2 * X.1) := by unfold sideCross; simp_all
  have hc3 : sideCross X U = X.1 * U.2 := by unfold sideCross; simp_all
  have hd1 : sideDot A U = A.2 * U.2 := by unfold sideDot; simp_all
  have hd2 : sideDot A X = A.1 * X.1 := by unfold sideDot; simp_all
  rw [hc2, hd2] at hray
  zufqe
  zuguu
  rcases lt_trichotomy A.1 0 with h | h | h
  · right; left; exact ztugb
  · have hA2' : ztmsv := by
      grind
    zurx
    exact ztrav
  · have hA2' : ztmsv := by
      rcases hA2.lt_or_eq with h' | h'
      · zuclh
      · exfalso; apply hray; zvmxl; exact ⟨by_ring, by_positivity⟩
    left; exact ⟨by_positivity, by_nlinarith, by_positivity⟩
omit C in
/-- The left sector of the walk at the top vertex arriving along a chain edge from below and
going up the slit contains the direction west. -/
theorem sideCcw_west {B U X : Point} (hU1 : U.1 = 0) (hU2 : 0 < U.2) (hX2 : X.2 = 0)
    (hX1 : X.1 < 0) (hB2 : B.2 ≤ 0) (hB : B ≠ 0)
    (hray : ¬ ztkfc) : sideCcw U X B := by
  have hc1 : sideCross U B = -(U.2 * B.1) := by unfold sideCross; simp_all
  have hc2 : sideCross U X = -(U.2 * X.1) := by unfold sideCross; simp_all
  have hc3 : sideCross X B = X.1 * B.2 := by unfold sideCross; simp_all
  have hd1 : sideDot U B = U.2 * B.2 := by unfold sideDot; simp_all
  have hc4 : sideCross B X = -(B.2 * X.1) := by unfold sideCross; simp_all
  have hd2 : sideDot B X = B.1 * X.1 := by unfold sideDot; simp_all
  rw [hc4, hd2] at hray
  zufqe
  zuguu
  rcases lt_trichotomy B.1 0 with h | h | h
  · have hB2' : ztkzu := by
      rcases hB2.lt_or_eq with h' | h'
      · zuclh
      · exfalso; apply hray; zvmxl; exact ⟨by_ring, by_nlinarith⟩
    left; exact ztkiy
  · have hB2' : ztkzu := by
      grind
    zurx
    exact ztrav
  · zugav
omit C in
/-- A position whose open left sector contains `e'`, at the point `e`, attaches the segment
`[e, e']`. -/
theorem sideAttach_of_left {e e' : Point} (hp : p < W.n)
    (ht : 0 ≤ t) (ht1 : t < 1) (hpt : sidePt W p t = e) (hl : sideLeft W p t e') :
    SideAttach W ztnkg p t := by
  refine ⟨hp, ht, ht1, hpt ▸ Geometry.left_mem_segment _ _, 1, one_pos, ?_⟩
  intro x hx hxe _
  zufr
  unfold sideLeft sideLeftOf at hl ⊢
  zvmxe at hl hxe ⊢
  have hs : ztxx := by
    zuvl
    · zubh
    · zujpp
  have e1 : lerp e e' s - e = s • ztert := by
    zqdj
  rw [e1, sideCcw_smul hs]; exact hl

/-- Some position of the walk `W` at the point `e` has `e'` in its open left sector. -/
def SideSees (W : Polygon) (e e' : Point) : Prop :=
  ∃ p t, p < W.n ∧ 0 ≤ t ∧ t < 1 ∧ sidePt W p t = e ∧ sideLeft W p t e'

/-- Every value of the double-tour index is visited by the tour. -/
theorem sideIdx_visit (β : Bool) {j : ℕ} (hj : j < 2 * C.m) :
    ∃ i, i < 2 * C.m ∧ C.sideIdx β i = sideE C.m j ∧ C.sideIdx β ztg = sideE C.m ztl ∧
      (i = 0 → sideE C.m j = C.topIdx) ∧
      (0 < i → C.sideIdx β ztei = sideE C.m zthyh) := by
  zqes
  obtain ⟨S', hS'⟩ : ∃ S', S' = C.sideS β % (2 * C.m) := by_simp_all
  have hS := Nat.mod_lt ztdku hm2
  rw [← hS'] at hS
  have hmod : ∀ i, i < 2 * C.m → ztty % ztbb = (S' + i) % ztbb := by
    simp_all
  obtain ⟨i, hi, hij⟩ : ∃ i, i < 2 * C.m ∧ (C.sideS β + i) % (2 * C.m) = j := by
    by_cases h : S' ≤ j
    · refine ⟨j - S', by_omega, ?_⟩
      rw [hmod _ by_omega, show S' + (j - S') = j by omega, Nat.mod_eq_of_lt hj]
    · refine ⟨j + 2 * C.m - S', by_omega, ?_⟩
      rw [hmod _ by_omega, show S' + (j + 2 * C.m - S') = j + 2 * C.m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  refine ⟨i, hi, by rw [sideIdx_eq, hij], by rw [sideIdx_succ, hij], ?_, ?_⟩
  · zubww
    zubvi
    zvncl at hij
    rw [← hij]; exact C.sideE_sideS β
  · intro hi0
    zujlm
    have e := side_idx_succ hm2 ztdku ztei
    rw [Nat.sub_add_cancel hi0, hij] at e
    have hr := Nat.mod_lt ztwxx hm2
    generalize ztwxx % ztbb = r at e hr ⊢
    rcases lt_or_eq_of_le (show r + 1 ≤ 2 * C.m by omega) with h1 | h1
    · zvnnn at e; grind
    · rw [h1, Nat.mod_self] at e; grind

/-- At the top vertex: east is seen by the first position of the tour, west by the last. -/
theorem sideSees_top (hP : C.P.Simple) (β : Bool) {e' : Point} (hee : C.top ≠ e')
    (hy : C.top.2 = e'.2) (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp C.top e' s ∈ C.dom) :
    SideSees ztft C.top e' := by
  zqef
  zqfg
  have hU1 : (C.slitTop - C.top).1 = 0 := by zuotq
  have hU2 : 0 < (C.slitTop - C.top).2 := by zuotq; zuotr
  have hX2 : (e' - C.top).2 = 0 := by_simp_all
  have hX1 : (e' - C.top).1 ≠ 0 := by
    intro h; apply hee; exact point_ext (by simp at h; linarith) hy
  obtain ⟨-, -, hn1, hn2, -⟩ := C.sideTour_nbrs β
  rcases lt_or_gt_of_ne hX1 with hlt | hgt
  · -- west: the last position of the tour
    refine ⟨2 * C.m + 6, 0, by rw [sideWalk_n]; omega, le_rfl, one_pos, ?_, ?_⟩
    · rw [sidePt_zero, C.sideWalk_vtx_tour β le_rfl, sideTour_two_m]
    · rw [C.sideLeft_tour_last β]
      zucfg
      have hB2 : (C.sideTour β ztdl - C.top).2 ≤ 0 := by
        zuoci
        linarith [C.vertex_snd_le_top (C.sideIdx_le β ztdl)]
      refine sideCcw_west hU1 hU2 hX2 hlt hB2 ztykb ?_
      exact C.sideRay_free hP
        by_omega hT ztemb zthro hopen
  · -- east: the first position of the tour
    refine ⟨0 + 6, 0, by rw [sideWalk_n]; omega, le_rfl, one_pos, ?_, ?_⟩
    · rw [sidePt_zero, C.sideWalk_vtx_tour β by_omega, sideTour_zero]
    · rw [C.sideLeft_tour_first β]
      zucfg
      have hA2 : (C.sideTour β 1 - C.top).2 ≤ 0 := by
        zuoci; linarith [C.vertex_snd_le_top ztnjx]
      refine sideCcw_east hU1 hU2 hX2 hgt hA2 ztxou ?_
      exact C.sideRay_free hP
        by_omega hT ztemb zthro hopen
omit C in
/-- The full-turn sector at a spike contains every direction off the ray of the spike. -/
theorem sideCcw_spike {A X : Point} (hA : A ≠ 0)
    (hray : ¬ ztevl) : sideCcw A X A := by
  zufqe
  zubef
  refine ⟨sideCross_self A, sideDot_self_pos hA, ?_⟩
  grind

/-- At an inner chain vertex other than the top vertex: one of its two passages sees the
direction. -/
theorem sideSees_inner (hP : C.P.Simple) (β : Bool) {j : ℕ} (hj0 : 0 < j) (hjm : j < C.m)
    (hjT : j ≠ C.topIdx) {e' : Point} (hee : C.vertex j ≠ e')
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztemc e' s ∈ C.dom) :
    SideSees ztft ztemc e' := by
  zqes
  have hA := sub_ne_zero_of_ne' (C.sideVertex_succ_ne hP j).symm
  have hB := sub_ne_zero_of_ne' (C.sideVertex_pred_ne hP hj0)
  have hns := (C.sideChain_nonSpike hP hj0 hjm).1
  have hXA := C.sideRay_free hP ztp hjm.le hjm zthro hopen
  have hXB := C.sideRay_free hP (j' := j - 1) by_omega hjm.le by_omega
    zthro hopen
  rcases sideCcw_or hA hB hns hXA hXB with h | h
  · -- the forwards passage
    zqeo
    have hi0 : ztphs := by
      zqfn
      · zqfa
      omega
    zqdv
    have k2 : C.sideIdx β ztg = j + 1 := by zvmxx; unfold sideE; grind
    have k3 : C.sideIdx β ztei = j - 1 := by zuoqp; unfold sideE; grind
    zqdm
    · zqej
    · zqdw
      zubh
  · -- the backwards passage
    obtain ⟨i, hi, h1, h2, h3, h4⟩ := C.sideIdx_visit β (j := 2 * C.m - j) by_omega
    have hi0 : ztphs := by
      zqfn
      · zqfa
      omega
    zqdv
    have k2 : C.sideIdx β ztg = j - 1 := by zvmxx; unfold sideE; grind
    have k3 : C.sideIdx β ztei = j + 1 := by zuoqp; unfold sideE; grind
    zqdm
    · zqej
    · zqdw
      zubh

/-- At an endpoint of the chain other than the top vertex: the turnaround sees every direction
off the chain edge. -/
theorem sideSees_end (hP : C.P.Simple) (β : Bool) {j : ℕ} (hj : j = 0 ∨ j = C.m)
    (hjT : j ≠ C.topIdx) {e' : Point} (hee : C.vertex j ≠ e')
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztemc e' s ∈ C.dom) :
    SideSees ztft ztemc e' := by
  zqef
  zqes
  obtain ⟨j', hj', hjj, hk2, hk3⟩ : ∃ j', j' ≤ C.m ∧ (j' = j + 1 ∨ j' + 1 = j) ∧
      (∀ i, sideE C.m ztl = C.sideIdx β ztg → C.sideIdx β ztg = j') ∧
      (∀ i, sideE C.m zthyh = C.sideIdx β ztei →
        C.sideIdx β ztei = j') := by
    zudsf
    · refine ⟨1, hm, Or.inl rfl, fun i h => ?_, fun i h => ?_⟩ <;> zvmzi <;> unfold sideE <;>
        zuwd
    · refine ⟨C.m - 1, by_omega, by_omega, fun i h => ?_, fun i h => ?_⟩ <;> zvmzi <;>
        unfold sideE <;> split_ifs <;> omega
  zqeo
  have hi0 : ztphs := by
    zqfn
    · zqfa
    omega
  zqdv
  have k2 := hk2 i h2.symm
  have k3 := hk3 i by_omega
  have hA := sub_ne_zero_of_ne' (show C.vertex j' ≠ C.vertex j by
    zuklm
    · exact (C.sideVertex_succ_ne hP j).symm
    · exact C.sideVertex_succ_ne hP j')
  have hX := C.sideRay_free hP hjj by_omega hj' zthro hopen
  zqdm
  · zqej
  · zqdw
    exact sideCcw_spike hA hX

/-- A chain vertex sees every horizontal direction into the domain. -/
theorem sideSees_vertex (hP : C.P.Simple) (β : Bool) {j : ℕ} (hj : j ≤ C.m) {e' : Point}
    (hee : C.vertex j ≠ e') (hy : (C.vertex j).2 = e'.2)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztemc e' s ∈ C.dom) :
    SideSees ztft ztemc e' := by
  by_cases hjT : j = C.topIdx
  · subst hjT
    exact C.sideSees_top hP β hee hy hopen
  zqep
  · exact C.sideSees_end hP β zthrq hjT hee hopen
  rcases lt_or_eq_of_le hj with hjm | hjm
  · exact C.sideSees_inner hP β h0 hjm hjT hee hopen
  · exact C.sideSees_end hP β (Or.inr hjm) hjT hee hopen

/-- A point inside a chain edge: one of the two passages along the edge sees the direction. -/
theorem sideSees_open (hP : C.P.Simple) (β : Bool) {k : ℕ} (hk : k < C.m) {s₀ : ℝ}
    (hs : s₀ ∈ Ioo (0 : ℝ) 1) {e' : Point} (hee : lerp ztib ztwkj s₀ ≠ e')
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztbana e' s ∈ C.dom) :
    SideSees ztft ztbana e' := by
  zqes
  zukee
  have hdet : det ztib ztwkj e' ≠ 0 := by
    zubww
    have hc : sideCross ztwuh
        ztbaos = 0 := by
      have e : sideCross ztwuh
          ztbaos = det ztib ztwkj e' := by
        unfold sideCross det; zvnuo; ring
      simp_all
    obtain ⟨s, hs', t, ht0, ht1, ht⟩ := side_overlap hne hs.1.le hs.2 rfl zthro hc
      (fun h => absurd h hs.1.ne')
    have hset : lerp ztbana e' s ∈ C.set := by
      zvnup; exact C.sideLerp_mem_set ztp hk.le hk ht0 ht1
    zulww
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- the backwards passage
    obtain ⟨i, hi, h1, h2, -, -⟩ := C.sideIdx_visit β (j := 2 * C.m - 1 - k) by_omega
    have k1 : C.sideIdx β i = k + 1 := by zvmwp; unfold sideE; grind
    have k2 : C.sideIdx β ztg = k := by zvmxx; unfold sideE; grind
    have hv : (C.sideWalk β).vtx ztcy = C.vertex zts := by
      zuekw
    have hv' : (C.sideWalk β).vtx ztyt = C.vertex k := by
      zqfo
    have ht : 1 - s₀ ∈ Ioo (0 : ℝ) 1 := by_grind
    refine ⟨i + 6, 1 - s₀, by rw [sideWalk_n]; omega, ht.1.le, ht.2, ?_, ?_⟩
    · unfold sidePt; rw [hv, hv']
      zucco
    · rw [sideLeft_edge by_grind ht, hv, hv', Geometry.det_swap12]
      linarith
  · -- the forwards passage
    obtain ⟨i, hi, h1, h2, -, -⟩ := C.sideIdx_visit β (j := k) by_omega
    have k1 : C.sideIdx β i = k := by zvmwp; unfold sideE; grind
    have k2 : C.sideIdx β ztg = k + 1 := by zvmxx; unfold sideE; grind
    have hv : (C.sideWalk β).vtx ztcy = C.vertex k := by
      zuekw
    have hv' : (C.sideWalk β).vtx ztyt = C.vertex zts := by
      zqfo
    refine ⟨i + 6, s₀, by rw [sideWalk_n]; omega, hs.1.le, hs.2, ?_, ?_⟩
    · zuhbc
    · rw [sideLeft_edge by_grind hs, hv, hv']
      omega

/-- A point of an open vertical side of the box sees the horizontal direction into the box. -/
theorem sideSees_box (β : Bool) {e e' : Point}
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ C.dom) (he1 : |e.1| = C.radius)
    (he2 : |e.2| < C.radius) : SideSees ztft e e' := by
  zqfy
  have hmid := (hopen ztcn by_grind).1
  have hmid1 := abs_lt.1 hmid.1
  simp only [lerp_fst] at hmid1
  have he2' := abs_lt.1 he2
  zulkq
  rcases (abs_eq hR.le).1 he1 with h | h
  · -- the right side, going up
    have hp : ztjfq % (C.sideWalk β).n = 4 := by_rfl
    have ht : zttjm / ztekt ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · apply div_pos <;> linarith
      · zubie
    have he' : e'.1 < C.radius := by_grind
    refine ⟨3, zttjm / ztekt, by_omega, ht.1.le, ht.2, ?_, ?_⟩
    · unfold sidePt; zunxk
      zubjw
      · zufbq
      · zubzv
        grind
    · have hne : ztehh := by
        zunxk
        grind
      rw [sideLeft_edge hne ht, hp, sideWalk_vtx_three, sideWalk_vtx_four]
      zulbo

  · -- the left side, going down
    have hp : ztcse % (C.sideWalk β).n = 2 := by_rfl
    have ht : ztsvx / ztekt ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · simp_all
      · zubie
    have he' : -C.radius < e'.1 := by_grind
    refine ⟨1, ztsvx / ztekt, by_omega, ht.1.le, ht.2, ?_, ?_⟩
    · unfold sidePt; zunxl
      zubjw
      · zufbq
      · zubzv
        grind
    · have hne : ztxcw := by
        zunxl
        grind
      rw [sideLeft_edge hne ht, hp, sideWalk_vtx_one, sideWalk_vtx_two]
      zulbo

/-- **Every endpoint of a chord is seen by some position of the corrected walk**: for a
horizontal segment `[e, e']` whose open part lies in the domain and whose endpoint `e` lies on
the chain or on an open vertical side of the box, some position of `C.sideWalk β` at `e` has `e'`
in its open left sector. -/
theorem sideSees_chordEnd (hP : C.P.Simple) (β : Bool) {e e' : Point} (hee : e ≠ e')
    (hy : e.2 = e'.2) (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp e e' s ∈ C.dom)
    (he : e ∈ C.set ∨ (|e.1| = C.radius ∧ |e.2| < C.radius)) : SideSees ztft e e' := by
  rcases he with he | ⟨he1, he2⟩
  · obtain ⟨k, hk, hmem⟩ := he
    zukoo
    obtain ⟨s₀, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hmem
    zunm
    · zuji
      · exact C.sideSees_open hP β hk by_simp_all hee hopen
      · subst hs1
        rw [lerp_one] at hee hy hopen ⊢
        exact C.sideSees_vertex hP β hk hee hy hopen
    · zumqe
      rw [lerp_zero] at hee hy hopen ⊢
      exact C.sideSees_vertex hP β hk.le hee hy hopen
  · exact C.sideSees_box β hopen he1 he2

/-! ### The winding number of the corrected walk -/

/-! ### The split walks of the corrected walk at a chord -/
