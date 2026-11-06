module

public import Chazelle.MacT
public import Chazelle.Core.RestoreTPos
public import Chazelle.Core.DownPhaseMathHR1
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.SweepChainT

namespace Chazelle.Core
namespace DrvH
open Machine Machine.Stmt Programs BuildRam DrvR
@[expose] public section
structure HEnv (W n : ℕ) (N : NF) (r : ℕ) (li : Bool) (T : ℕ) (d : Config) : Prop where
  K : Kst n li d
  F : HFacts n N r
  aR : d.nreg 215030 = (N.region r).arcs.length
  kR : d.nreg 215031 = (N.region r).chords.length
  tR : d.nreg 215032 = T
  arcs : ∀ t, t < (N.region r).arcs.length →
    d.nmem (d.nreg 215027 + ztrok) = (N.region r).arcs.getD t 0 ∧
    d.nreg 215027 + ztrok < T
  chs : ∀ v, v < (N.region r).chords.length →
    d.nmem ztyen = (N.region r).chords.getD v 0 ∧
    d.nreg 215027 + zteew < T
  arcR : ∀ j, j < N.arcs.length →
    d.nmem (d.nreg 215026 + 5 * j + 1) = (N.arc j).s.edge ∧
    d.nmem (d.nreg 215026 + 5 * j + 2) = (N.arc j).s.hgt ∧
    d.nmem (d.nreg 215026 + 5 * j + 3) = (N.arc j).e.edge ∧
    d.nmem (d.nreg 215026 + 5 * j + 4) = (N.arc j).e.hgt ∧ d.nreg 215026 + 5 * j + 4 < T
  chR : ∀ i, i < N.nChords → d.nmem ztijd = (N.chord i).h ∧
    d.nmem ztgie = (N.chord i).lp ∧
    d.nmem ztgif = (N.chord i).rp ∧ d.nreg 215025 + 5 * i + 2 < T
  hT : T + 200 ≤ W
  hn : 8 * n + 32 ≤ W
  hn0 : 0 < n

/-- The environment survives the arc loop's writes. -/
theorem HEnv.keep {W n : ℕ} {N : NF} {r : ℕ} {li : Bool} {T : ℕ} {d d' : Config}
    (h : HEnv W n N r li T d) (hf : FrameM Bdyn d d') (hm : ∀ a, a < T → d'.nmem a = d.nmem a) :
    HEnv W n N r li T d' := by
  zugla
  have g25 : d'.nreg 215025 = d.nreg 215025 := g _ by_decide
  have g26 : d'.nreg 215026 = d.nreg 215026 := g _ by_decide
  have g27 : d'.nreg 215027 = d.nreg 215027 := g _ by_decide
  have g28 : d'.nreg 215028 = d.nreg 215028 := g _ by_decide
  have g29 : d'.nreg 215029 = d.nreg 215029 := g _ by_decide
  refine ⟨h.K.frame hf by_decide, h.F, by rw [g _ by_decide, h.aR],
    by rw [g _ by_decide, h.kR], by rw [g _ by_decide, h.tR], fun t ht => ?_, fun v hv => ?_,
    fun j hj => ?_, fun i hi => ?_, h.hT, h.hn, h.hn0⟩
  · obtain ⟨a1, a2⟩ := h.arcs t ht
    simp_all
  · obtain ⟨a1, a2⟩ := h.chs v hv
    simp_all
  · obtain ⟨a1, a2, a3, a4, a5⟩ := h.arcR j hj
    grind
  · obtain ⟨a1, a2, a3, a4⟩ := h.chR i hi
    grind
theorem add_1_1 (a : ℕ) : a + 1 + 1 = a + 2 := rfl
theorem add_5 (a b : ℕ) : a + ztjoc = a + 5 * b := by_ring
theorem mod_succ_of_lt {t A : ℕ} (ht : t < A) : ztbx % A = if t + 1 < A then t + 1 else 0 := by
  zus
  · zubql
  · rw [show t + 1 = A by omega, Nat.mod_self]
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
/-- **Loading the arcs of iteration `t`** and their ends. -/
theorem ldS_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {N : NF} {r : ℕ} {li : Bool} {T t : ℕ}
    (hE : HEnv W n N r li T d) (h41 : d.nreg 215041 = t) (ht : t < (N.region r).arcs.length) :
    ∃ d' k, Exec P W ldS d d' k ∧ k ≤ 30 ∧
      d'.nreg 215046 = (N.arc ztml).e.edge ∧
      d'.nreg 215047 = (N.arc ztml).e.hgt ∧
      d'.nreg 215048 = (N.arc ztwjr).s.edge ∧
      d'.nreg 215049 = (N.arc ztwjr).s.hgt ∧
      d'.nreg 215050 = (N.arc ztwjr).e.edge ∧
      d'.nreg 215051 = (N.arc ztwjr).e.hgt ∧
      d'.nmem = d.nmem ∧ FrameM Bld d d' := by
  have hmem : ztezk :=
    by simp_all
  have K := hE.K
  zuiwz
  obtain ⟨b1, b2⟩ := hE.arcs t ht
  obtain ⟨p1, p2, p3, p4, p5⟩ := hE.arcR _ (hE.F.harc _ zttoa).1
  rw [mod_succ_of_lt ht]
  by_cases hlt : t + 1 < (N.region r).arcs.length
  · zuipm
    obtain ⟨c1, c2⟩ := hE.arcs _ hlt
    obtain ⟨q1, q2, q3, q4, q5⟩ := hE.arcR _ (hE.F.harc _ (hmem _ hlt)).1
    obtain ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, hm⟩ : ∃ d' k, Exec P W ldS d d' k ∧ k ≤ 30 ∧
        d'.nreg 215046 = (N.arc ztml).e.edge ∧
        d'.nreg 215047 = (N.arc ztml).e.hgt ∧
        d'.nreg 215048 = (N.arc ztwys).s.edge ∧
        d'.nreg 215049 = (N.arc ztwys).s.hgt ∧
        d'.nreg 215050 = (N.arc ztwys).e.edge ∧
        d'.nreg 215051 = (N.arc ztwys).e.hgt ∧
        d'.nmem = d.nmem := by
      unfold ldS
      refine spec_seq ?_
      exec_block
      all_goals try (config_simp; (try simp only [h41, K.one]); omega)
      zujl
      refine spec_ifLtN_true (by config_simp; simp only [h41, K.one, hE.aR]; omega) ?_
      zurc
      exec_block
      all_goals try (config_simp; (try simp only [h41, K.one, K.three, b1, c1, add_5, add_1_1]); omega)
      refine ztdiy <;> config_simp <;>
        simp only [h41, K.one, K.three, b1, c1, add_5, add_1_1, p3, p4, q1, q2,
          q3, q4]
    exact ztedr
  · zuipm
    have h0 : ztphk := by_omega
    obtain ⟨c1, c2⟩ := hE.arcs 0 h0
    rw [Nat.add_zero] at c1 c2
    obtain ⟨q1, q2, q3, q4, q5⟩ := hE.arcR _ (hE.F.harc _ (hmem _ h0)).1
    obtain ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, hm⟩ : ∃ d' k, Exec P W ldS d d' k ∧ k ≤ 30 ∧
        d'.nreg 215046 = (N.arc ztml).e.edge ∧
        d'.nreg 215047 = (N.arc ztml).e.hgt ∧
        d'.nreg 215048 = (N.arc ztdeg).s.edge ∧
        d'.nreg 215049 = (N.arc ztdeg).s.hgt ∧
        d'.nreg 215050 = (N.arc ztdeg).e.edge ∧
        d'.nreg 215051 = (N.arc ztdeg).e.hgt ∧
        d'.nmem = d.nmem := by
      unfold ldS
      refine spec_seq ?_
      exec_block
      all_goals try (config_simp; (try simp only [h41, K.one]); omega)
      zujl
      refine spec_ifLtN_false (by config_simp; simp only [h41, K.one, hE.aR]; omega) ?_
      exec_block
      all_goals try (config_simp; (try simp only [h41, K.one, K.three, b1, c1, add_5, add_1_1,
        Nat.add_zero]); omega)
      refine ztdiy <;> config_simp <;>
        simp only [h41, K.one, K.three, b1, c1, add_5, add_1_1, p3, p4, q1, q2,
          q3, q4, Nat.add_zero]
    exact ztedr

/-- **Copy a point into the emit registers and emit it.** -/
theorem cpEm_exec (a b : ℕ) (hb : b ≠ 215064) (d : Config)
    (hw : WordsBounded W d) {li : Bool} {n e h T : ℕ}
    {xs : List HostItem} (hK : Kst n li d) (h1 : d.nreg a = e) (h2 : d.nreg b = h)
    (hB : Buf n T xs d) (hW1 : T + 3 * xs.length + 3 ≤ W) (hW2 : ptsLen n xs + 1 ≤ W)
    (hW3 : e + 1 ≤ W) :
    ∃ d' k, Exec P W (.seq ztkry emitS) d d' k ∧ k ≤ 17 ∧
      Buf n T ztkya d' ∧
      ztdbg ∧
      FrameM (fun q => Bem q || decide zttwv || decide zttww) d d' := by
  have e₁ := Exec.copyN (P := P) hw 215064 a
  have e₂ := Exec.copyN (P := P) e₁.wb_right 215065 b
  set d₁ : Config := { d with nreg := upd d.nreg 215064 (d.nreg a) } with hd₁
  set d₂ : Config := { d₁ with nreg := upd d₁.nreg 215065 _ } with hd₂
  have g : ∀ q, q ≠ 215064 → q ≠ 215065 → d₂.nreg q = d.nreg q := by_simp_all
  have K₂ : Kst n li d₂ := ⟨by rw [g _ by_decide by_decide, hK.one],
    by rw [g _ by_decide by_decide, hK.nn], by rw [g _ by_decide by_decide, hK.zero],
    by rw [g _ by_decide by_decide, hK.three], by rw [g _ by_decide by_decide, hK.two],
    by rw [g _ by_decide by_decide, hK.li]⟩
  have B₂ : Buf n T xs d₂ := ⟨hB.1, by rw [g _ by_decide by_decide, hB.2.1],
    by rw [g _ by_decide by_decide, hB.2.2.1], by rw [g _ by_decide by_decide, hB.2.2.2]⟩
  have v64 : d₂.nreg 215064 = e := by
    simp_all
  have v65 : d₂.nreg 215065 = h := by
    simp_all
  have eb : Exec P W ztkry d d₂ 2 :=
    .seq e₁ ztxug
  have fb : FrameM (fun q => decide zttwv || decide zttww) d d₂ :=
    exec_frameM eb by_rfl
  obtain ⟨d₃, k₃, e₃, hk₃, B₃, m₃, f₃⟩ := emitS_exec (P := P) d₂ e₂.wb_right K₂ v64 v65 B₂
    hW1 hW2 hW3
  refine ⟨d₃, 2 + k₃, .seq eb e₃, by_omega, B₃, by_omega, ?_⟩
  exact (fb.mono by_simp_all).trans
    (f₃.mono by_simp_all)
theorem wpos_ne {p s : WPos} (h : p ≠ s) : ¬ (p.edge = s.edge ∧ p.hgt = s.hgt) := by
  rintro ⟨h1, h2⟩; apply h; cases p; simp_all

/-- **The junction point.** -/
theorem junS_exec (d : Config) (hw : WordsBounded W d) {li : Bool} {n T : ℕ} {xs : List HostItem}
    {p s : WPos} (hK : Kst n li d) (h52 : d.nreg 215052 = p.edge) (h53 : d.nreg 215053 = p.hgt)
    (h48 : d.nreg 215048 = s.edge) (h49 : d.nreg 215049 = s.hgt) (hp : p.edge < n)
    (hph : p.hgt ≤ n) (hs : s.edge < n) (hsh : s.hgt ≤ n) (hB : Buf n T xs d)
    (hW1 : T + 3 * xs.length + 3 ≤ W) (hW2 : ptsLen n xs + 1 ≤ W) (hW3 : 2 * n + 1 ≤ W) :
    ∃ d' k, Exec P W junS d d' k ∧ k ≤ 30 ∧
      Buf n T (xs ++ (if p = s then [] else [ptI li n p false])) d' ∧
      ztdbg ∧ FrameM Bjun d d' := by
  obtain ⟨d₁, k₁, e₁, hk₁, v60, m₁⟩ : ∃ d₁ k₁, Exec P W (block [.subN 215060 215052 215048,
      .subN 215063 215048 215052, .addN 215060 215060 215063, .subN 215061 215053 215049,
      .subN 215063 215049 215053, .addN 215061 215061 215063, .addN 215060 215060 215061])
      d d₁ k₁ ∧ k₁ = 7 ∧
      d₁.nreg 215060 = p.edge - s.edge + (s.edge - p.edge) + (p.hgt - s.hgt + (s.hgt - p.hgt)) ∧
      d₁.nmem = d.nmem := by
    exec_block
    all_goals try (config_simp; (try simp only [h52, h53, h48, h49]); omega)
    refine ztrec
    config_simp; grind
  have f₁ : FrameM (fun q => decide (q = 215060) || decide (q = 215061) || decide ztofd)
    d d₁ := exec_frameM e₁ by_decide
  zujwc
  zuepl
  have F₁ : FrameM Bjun d d₁ := f₁.mono fun q hq => by
    simp only [Bjun, Bem, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega
  by_cases hps : p = s
  · have h0 : d₁.nreg 215060 = 0 := by_simp_all
    refine ⟨d₁, 7 + ztbgo, (Exec.seq e₁ (.ifLtN_true (by rw [h0, K₁.one]; omega)
      ztekc)).cast by_omega, by_omega, ?_, by_simp_all, F₁⟩
    simp_all
  · have hne := wpos_ne hps
    have h1 : 1 ≤ d₁.nreg 215060 := by_omega
    obtain ⟨d₂, k₂, e₂, hk₂, B₂, m₂, f₂⟩ := cpEm_exec 215052 215053 by_decide d₁
      e₁.wb_right K₁ (by rw [f₁.1 _ by_decide, h52]) (by rw [f₁.1 _ by_decide, h53]) B₁ hW1
      hW2 by_omega
    refine ⟨d₂, k₁ + ztoci, .seq e₁ (.ifLtN_false (by rw [K₁.one]; omega) e₂), by_omega, ?_,
      by simp_all, F₁.trans (f₂.mono fun q hq => ?_)⟩
    · simp only [hps, ↓reduceIte]; exact B₂
    · simp only [Bjun, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢
      grind
theorem partner_bounds {n : ℕ} {N : NF} {r : ℕ} (hF : HFacts n N r) {x : WPos}
    (hx : x.edge < n) (hxh : x.hgt ≤ n) :
    (partner N r x).edge < n ∧ (partner N r x).hgt ≤ n := by
  rw [partner_eq]
  cases hf : (N.region r).chords.find? _ with
  | none => exact ⟨hx, hxh⟩
  | some i =>
    have hi := List.mem_of_find?_eq_some hf
    obtain ⟨-, hl, hr, hh⟩ := hF.hch i hi
    simp only [resOf]
    split_ifs <;> simp only [CRec.lpos, CRec.rpos] <;> omega
theorem sub_Bdyn {B : ℕ → Bool} (h : ∀ q, B q = true → q = 215011 ∨ q = 215012 ∨
    ztnfs) {c c' : Config} (hf : FrameM B c c') : FrameM Bdyn c c' :=
  hf.mono fun q hq => by
    simp only [Bdyn, Bool.or_eq_true, decide_eq_true_eq]
    grind
set_option maxHeartbeats 2000000 in
/-- **One iteration of the arc loop**: appends `arcIt li n N r t`. -/
theorem arcBody_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {N : NF} {r : ℕ} {li : Bool}
    {T t : ℕ} (hE : HEnv W n N r li T d) (h41 : d.nreg 215041 = t)
    (ht : t < (N.region r).arcs.length) (hB : Buf n T ztilu d) :
    ∃ d' k, Exec P W arcBody d d' k ∧ k ≤ 300 ∧ d'.nreg 215041 = t + 1 ∧
      Buf n T (pre li n N r ztbx) d' ∧ ztiun ∧
      FrameM Bdyn d d' := by
  have hmem : ztezk :=
    by simp_all
  set jp := (N.region r).arcs.getD t 0 with hjp
  set j := (N.region r).arcs.getD (ztbx % (N.region r).arcs.length) 0 with hj
  obtain ⟨-, -, -, hxe, hxh⟩ := hE.F.harc jp zttoa
  obtain ⟨-, hse, hsh, hee, heh⟩ := hE.F.harc j (hmem _ ztcv)
  zumed
  zuiwz
  set xs := pre li n N r t with hxs
  have hxl : xs.length ≤ 4 * t := pre_length_le li n N r t
  have hxp : ptsLen n xs ≤ ztkbe * t := ptsLen_pre_le li hE.hn0 N r t
  zumbk
  have hxl' : xs.length ≤ 16 := by_omega
  have hxp' : ptsLen n xs ≤ 4 * n + 12 := by
    have : ztkbe * t ≤ ztkbe * 4 := Nat.mul_le_mul_left _ by_omega
    omega
  -- loading
  obtain ⟨d₁, k₁, e₁, hk₁, v46, v47, v48, v49, v50, v51, m₁, f₁⟩ := ldS_exec (P := P) d hw hE h41 ht
  have K₁ := hE.K.frame f₁ by_decide
  zuepl
  zuepx
  -- the partner
  obtain ⟨d₂, k₂, e₂, hk₂, v52, v53, m₂, f₂⟩ := partS_exec (P := P) d₁ e₁.wb_right K₁ hE.F v46 v47
    hxe hxh (by rw [g₁ _ by_decide, hE.kR])
    (fun v hv => by
      obtain ⟨a1, a2⟩ := hE.chs v hv
      rw [m₁, g₁ _ by_decide, g₁ _ by_decide]; omega)
    (fun i hi => by
      obtain ⟨a1, a2, a3, a4⟩ := hE.chR i hi
      rw [m₁, g₁ _ by_decide]; omega) by_omega
  zuepm

  zucgb
  obtain ⟨hpe, hph⟩ := partner_bounds hE.F hxe hxh
  -- the junction
  obtain ⟨d₃, k₃, e₃, hk₃, B₃, m₃, f₃⟩ := junS_exec (P := P) d₂ e₂.wb_right K₂ v52 v53
    (by rw [g₂ _ by_decide, v48]) (by rw [g₂ _ by_decide, v49]) hpe hph hse hsh B₂
    by_omega by_omega by_omega
  zujwd
  zuepy
  set ys := xs ++ (if partner N r (N.arc jp).e = (N.arc j).s then []
    else [ptI li n ztglf false]) with hys
  have hyl : ys.length ≤ xs.length + 1 := by rw [hys, List.length_append]; split_ifs <;> simp
  have hyp : ptsLen n ys ≤ ptsLen n xs + 1 := by
    rw [hys, ptsLen_append]; split_ifs
    · simp [ptsLen_nil]
    rfl
  -- the start point
  obtain ⟨d₄, k₄, e₄, hk₄, B₄, m₄, f₄⟩ := cpEm_exec (P := P) 215048 215049 by_decide d₃ (e := (N.arc j).s.edge) (h := (N.arc j).s.hgt)
    e₃.wb_right K₃ (by rw [g₃ _ by_decide, g₂ _ by_decide, v48])
    (by rw [g₃ _ by_decide, g₂ _ by_decide, v49]) B₃ by_omega by_omega by_omega
  zujwe
  have g₄ : ∀ q, (Bem q || decide _ || decide _) = false →
    d₄.nreg q = d₃.nreg q := f₄.1
  -- the run
  obtain ⟨d₅, k₅, e₅, hk₅, B₅, v72, m₅, f₅⟩ := runS_exec (P := P) (s := (N.arc j).s)
    (e := (N.arc j).e) d₄ e₄.wb_right K₄
    (by rw [g₄ _ by_decide, g₃ _ by_decide, g₂ _ by_decide, v48])
    (by rw [g₄ _ by_decide, g₃ _ by_decide, g₂ _ by_decide, v50])
    (by rw [g₄ _ by_decide, g₃ _ by_decide, g₂ _ by_decide, v51]) hse hee B₄
    ztkuz
    (by rw [ptsLen_append, ptE, ptsLen_pt]; omega) by_omega
  have K₅ := K₄.frame f₅ by_decide
  zuiux
  have hrl := runItems_length_le li n (N.arc j).s (N.arc j).e
  have hrp : ptsLen n (runItems li n (N.arc j).s (N.arc j).e) < n :=
    (ptsLen_runItems li hE.hn0 _ _).symm ▸ runCnt_lt li hE.hn0 _ _
  -- the end point
  obtain ⟨d₆, k₆, e₆, hk₆, B₆, m₆, f₆⟩ := cpEm_exec (P := P) 215072 215051 by_decide d₅
    (e := if atVtx li n (N.arc j).e then ztflq % n else (N.arc j).e.edge)
    (h := (N.arc j).e.hgt)
    e₅.wb_right K₅ v72
    (by rw [g₅ _ by_decide, g₄ _ by_decide, g₃ _ by_decide, g₂ _ by_decide, v51]) B₅
    ztkuz
    (by simp only [ptsLen_append, ptE, ptsLen_pt]; omega)
    (by split_ifs <;> [have := Nat.mod_lt ztflq hE.hn0; skip] <;> omega)
  have K₆ := K₅.frame f₆ by_decide
  have g₆ : ∀ q, (Bem q || decide _ || decide _) = false →
    d₆.nreg q = d₅.nreg q := f₆.1
  -- the counter
  have r41 : d₆.nreg 215041 = t := by
    rw [g₆ _ by_decide, g₅ _ by_decide, g₄ _ by_decide, g₃ _ by_decide, g₂ _ by_decide,
      g₁ _ by_decide, h41]
  have e₇ := Exec.addN (P := P) e₆.wb_right 215041 215041 215020 (by rw [r41, K₆.one]; omega)
  set d₇ : Config := { d₆ with nreg := upd d₆.nreg 215041 _ }
    with hd₇
  have f₇ : FrameM (fun q => decide (q = 215041)) d₆ d₇ :=
    exec_frameM e₇ by_decide
  have B₇ := B₆.frame f₇ by_decide rfl
  refine ⟨d₇, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + ztceh))))),
    .seq e₁ ztyoh,
    by omega, ?_, ?_, fun a ha => ?_, ?_⟩
  · simp only [hd₇, Programs.Config.nreg_mk, Machine.upd_same, r41, K₆.one]
  · have e : pre li n N r ztbx = ys ++ [ptE li n (N.arc j).s.edge (N.arc j).s.hgt] ++
        runItems li n (N.arc j).s (N.arc j).e ++
        [ptE li n (if atVtx li n (N.arc j).e then ztflq % n
          else (N.arc j).e.edge) (N.arc j).e.hgt] := by
      rw [pre_succ, hys]
      simp only [arcIt, arcItems, List.append_assoc]
      rfl
    grind
  · show d₆.nmem a = d.nmem a
    rw [m₆ a by_omega, m₅ a by_omega,
      m₄ a by_omega, m₃ a by_omega, m₂, m₁]
  · refine ((((((sub_Bdyn ?_ f₁).trans (sub_Bdyn ?_ f₂)).trans (sub_Bdyn ?_ f₃)).trans
      (sub_Bdyn ?_ f₄)).trans (sub_Bdyn ?_ f₅)).trans (sub_Bdyn ?_ f₆)).trans (sub_Bdyn ?_ f₇) <;>
      intro q hq <;>
      simp only [Bld, Bpart, Bjun, Bem, Brun, Bool.or_eq_true, decide_eq_true_eq] at hq <;> omega
end exec
end
end DrvH
end Chazelle.Core
namespace Chazelle.Core
namespace DrvH
open Machine Machine.Stmt Programs BuildRam DrvR
@[expose] public section
def Bcp (q : ℕ) : Bool := decide (215080 ≤ q ∧ q ≤ 215086)
section exec
variable {P : Polygon} {W : ℕ}
variable (d : Config)
/-- **The arc loop** writes `walkItems li n N r` into the buffer. -/
theorem arcLoop_exec (hw : WordsBounded W d) {n : ℕ} {N : NF} {r : ℕ} {li : Bool}
    {T : ℕ} (hE : HEnv W n N r li T d) (h41 : d.nreg 215041 = 0) (hB : Buf n T [] d) :
    ∃ d' k, Exec P W arcLoop d d' k ∧ k ≤ 1512 ∧ Buf n T (walkItems li n N r) d' ∧
      HEnv W n N r li T d' ∧ ztiun ∧ FrameM Bdyn d d' := by
  zumbk
  let Inv : ℕ → Config → Prop := fun t e => WordsBounded W e ∧ e.nreg 215041 = t ∧
    e.nreg 215030 = (N.region r).arcs.length ∧ HEnv W n N r li T e ∧ Buf n T ztilu e ∧
    (∀ a, a < T → e.nmem a = d.nmem a) ∧ FrameM Bdyn d e
  obtain ⟨d', k, ex, ⟨w', -, -, E', B', m', f'⟩, hk⟩ := DrvR.forLoop (P := P) (W := W)
    (ir := 215041) (nr := 215030) Inv 300 (N.region r).arcs.length
    ztfhl
    (fun t e ht ⟨hwe, e41, e30, Ee, Be, me, fe⟩ => by
      obtain ⟨e', k, ex, hk, v41, B', m', f'⟩ := arcBody_exec (P := P) e hwe Ee e41 ht Be
      exact ⟨e', k, ex, ⟨ex.wb_right, v41, by rw [f'.1 _ by_decide, e30], Ee.keep f' m', B',
        fun a ha => by_simp_all, fe.trans f'⟩, hk⟩)
    (j := 0) ⟨hw, h41, hE.aR, hE, hB, fun _ _ => rfl, FrameM.refl _ _⟩ ztbg
  exact ⟨d', k, ex, by_omega, by_tauto, E', m', f'⟩

/-- One item of the copy. -/
theorem cpyBody_exec (e : Config) (hw : WordsBounded W e) {li : Bool} {n S D u w i : ℕ}
    (hK : Kst n li e) (h81 : e.nreg 215081 = S) (h82 : e.nreg 215082 = D)
    (h83 : e.nreg 215083 = u) (h84 : e.nreg 215084 = w) (h80 : e.nreg 215080 = i)
    (hSD : S + 2 < D) (hDW : D + 3 ≤ W) (hSW : S + u ≤ W) (hiW : i + 1 ≤ W) :
    ∃ e' k, Exec P W cpyBody e e' k ∧ k = 14 ∧ e'.nreg 215080 = i + 1 ∧
      e'.nreg 215081 = S + u - w ∧ e'.nreg 215082 = D + 3 ∧
      e'.nmem = wr3 e.nmem D ztvpm ztbahr ztbahs ∧
      FrameM (fun q => decide (215080 ≤ q ∧ q ≤ 215082) || decide (215085 ≤ q ∧ q ≤ 215086)) e e' := by
  obtain ⟨e', k, ex, hk, h1, h2, h3, hm⟩ : ∃ e' k, Exec P W cpyBody e e' k ∧ k = 14 ∧
      e'.nreg 215080 = i + 1 ∧ e'.nreg 215081 = S + u - w ∧ e'.nreg 215082 = D + 3 ∧
      e'.nmem = wr3 e.nmem D ztvpm ztbahr ztbahs := by
    unfold cpyBody
    exec_block
    all_goals
      try (config_simp; (try zundo); omega)
    refine ztboc <;> config_simp <;>
      zundo
    unfold wr3
    rw [Machine.upd_other _ _ _ (show S + 1 ≠ D by omega),
      Machine.upd_other _ _ _ (show S + 2 ≠ D + 1 by omega),
      Machine.upd_other _ _ _ (show S + 2 ≠ D by omega)]
  exact ⟨e', k, ex, hk, h1, h2, h3, hm, exec_frameM ex by_decide⟩
theorem take_add_one_getD {l : List HostItem} {i : ℕ} (h : i < l.length) (x : HostItem) :
    l.take ztg = l.take i ++ [l.getD i x] := by
  simp_all
set_option maxHeartbeats 1000000 in
/-- **The copy of the items** to the host layout (reversed when `li = false`). -/
theorem cpyLoop_exec (hw : WordsBounded W d) {li : Bool} {n T : ℕ}
    {xs : List HostItem} (hK : Kst n li d) (hI : ItemsAt d.nmem T xs)
    (h11 : d.nreg 215011 = xs.length) (h80 : d.nreg 215080 = 0)
    (h82 : d.nreg 215082 = T + 3 * xs.length + 1)
    (h81 : d.nreg 215081 = if li then T else T + 3 * xs.length - 3)
    (h83 : d.nreg 215083 = if li then 3 else 0) (h84 : d.nreg 215084 = if li then 0 else 3)
    (hW : T + 6 * xs.length + 4 ≤ W) :
    ∃ d' k, Exec P W cpyLoop d d' k ∧ k ≤ 16 * xs.length + 2 ∧
      ItemsAt d'.nmem (T + 3 * xs.length + 1) (if li then xs else xs.reverse) ∧
      d'.nreg 215082 = T + 6 * xs.length + 1 ∧
      (∀ a, a < T + 3 * xs.length + 1 → d'.nmem a = d.nmem a) ∧ FrameM Bcp d d' := by
  set K := xs.length with hKdef
  set H := if li then xs else xs.reverse with hH
  have hHl : H.length = K := by_grind
  have hHget : ∀ i, i < K → H.getD i ztmn =
      xs.getD ztkwn ztmn := fun i hi => by
    grind
  let Inv : ℕ → Config → Prop := fun i e => WordsBounded W e ∧ e.nreg 215080 = i ∧
    e.nreg 215011 = K ∧ e.nreg 215082 = T + 3 * K + 1 + 3 * i ∧
    (i < K → e.nreg 215081 = T + 3 * ztkwn) ∧
    e.nreg 215083 = ztild ∧ e.nreg 215084 = ztilc ∧
    Kst n li e ∧ (∀ a, a < T + 3 * K + 1 → e.nmem a = d.nmem a) ∧
    ItemsAt e.nmem (T + 3 * K + 1) ztdbw ∧ FrameM Bcp d e
  obtain ⟨d', k, ex, ⟨w', -, -, v82, -, -, -, -, m', I', f'⟩, hk⟩ := DrvR.forLoop (P := P)
    (W := W) (ir := 215080) (nr := 215011) Inv 14 K
    ztchw
    (fun i e hi ⟨hwe, e80, e11, e82, e81, e83, e84, Ke, me, Ie, fe⟩ => by
      set si := if li then i else K - 1 - i with hsi
      have hsiK : si < K := by_grind
      obtain ⟨e', k, ex, hk, v80, v81, v82, vm, fe'⟩ := cpyBody_exec (P := P) e hwe Ke
        (e81 hi) e82 e83 e84 e80 by_omega by_omega by_grind
        by_omega
      refine ⟨e', k, ex, ⟨ex.wb_right, v80, by rw [fe'.1 _ by_decide, e11], by_omega,
        fun hi' => ?_, by rw [fe'.1 _ by_decide, e83], by rw [fe'.1 _ by_decide, e84],
        Ke.frame fe' by_decide, fun a ha => ?_, ?_, fe.trans (fe'.mono fun q hq => by
          simp only [Bcp, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega)⟩, by_omega⟩
      · rw [v81]
        cases li <;> simp only [Bool.false_eq_true, ↓reduceIte] at hsi ⊢ <;> omega
      · rw [vm, wr3_lt by_omega, me a ha]
      · rw [take_add_one_getD by_omega ztmn, vm]
        have hlen : (H.take i).length = i := by_grind
        obtain ⟨a1, a2, a3⟩ := hI si hsiK
        have s0 : e.nmem (T + 3 * si) = encK ztwzh := by
          grind
        have s1 : e.nmem (T + 3 * si + 1) = encA ztwzh := by
          grind
        have s2 : e.nmem (T + 3 * si + 2) = encB ztwzh := by
          grind
        have := Ie.snoc ztwzh
        grind)
    (j := 0) ⟨hw, h80, h11, by_omega, fun h0 => by_grind,
      h83, h84, hK, fun _ _ => rfl, by_tauto,
      FrameM.refl _ _⟩ (Nat.zero_le _)
  refine ⟨d', k, ex, by_omega, ?_, by_omega, m', f'⟩
  grind

/-- **The end of the host**: the host handle after the buffer, the count word, the copy
arguments. -/
theorem finS_exec (hw : WordsBounded W d) {li : Bool} {n T K : ℕ} (hK : Kst n li d)
    (h40 : d.nreg 215040 = T + 3 * K) (h11 : d.nreg 215011 = K) (h32 : d.nreg 215032 = T)
    (hW : T + 3 * K + 2 ≤ W) :
    ∃ d' k, Exec P W finS d d' k ∧ k ≤ 9 ∧ d'.nreg 215010 = T + 3 * K ∧
      d'.nmem = upd d.nmem ztqcv K ∧ d'.nreg 215080 = 0 ∧
      d'.nreg 215082 = T + 3 * K + 1 ∧ d'.nreg 215081 = ztita ∧
      d'.nreg 215083 = ztild ∧ d'.nreg 215084 = ztilc ∧
      FrameM (fun q => decide (q = 215010) || decide (215080 ≤ q ∧ q ≤ 215084)) d d' := by
  obtain ⟨d', k, ex, hk, v10, vm, v80, v82, v81, v83, v84⟩ : ∃ d' k, Exec P W finS d d' k ∧
      k ≤ 9 ∧ d'.nreg 215010 = T + 3 * K ∧
      d'.nmem = upd d.nmem ztqcv K ∧ d'.nreg 215080 = 0 ∧
      d'.nreg 215082 = T + 3 * K + 1 ∧ d'.nreg 215081 = ztita ∧
      d'.nreg 215083 = ztild ∧ d'.nreg 215084 = ztilc := by
    unfold finS
    refine spec_seq ?_
    exec_block
    all_goals try (config_simp; (try simp only [h40, hK.one]); omega)
    cases li with
    | true =>
      refine spec_ifLtN_true (by config_simp; rw [hK.zero, hK.li]; decide) ?_
      exec_block
      · omega
      refine ztdix <;> config_simp <;>
        simp only [h40, h11, h32, hK.one, hK.three, ↓reduceIte]
    | false =>
      refine spec_ifLtN_false (by config_simp; rw [hK.zero, hK.li]; decide) ?_
      exec_block
      · omega
      refine ztdix <;> config_simp <;>
        simp only [h40, h11, hK.one, hK.three, Bool.false_eq_true, ↓reduceIte]
  exact ⟨d', k, ex, hk, v10, vm, v80, v82, v81, v83, v84, exec_frameM ex by_decide⟩

/-- **The padding loop** runs exactly `3 (r215082 - r9999) + 2` steps. -/
theorem padLoopH_exec : ∀ (m : ℕ) (c : Config), WordsBounded W c → c.nreg 215020 = 1 →
    c.nreg 9999 ≤ c.nreg 215082 → c.nreg 215082 - c.nreg 9999 = m →
    Exec P W padLoopH c { c with nreg := upd c.nreg 9999 (c.nreg 215082) } (3 * m + 2)
  | 0, c, hw, _, hle, hd => by
    have h : c.nreg 9999 = c.nreg 215082 := by_omega
    refine ztgvg
    zuezs
  | m + 1, c, hw, h20, hle, hd => by
    have e := Exec.addN (P := P) hw 9999 9999 215020 (by zuovl; have := hw.1 215082; omega)
    have h1 : ztfcq 215020 = 1 := by
      simp_all
    have h2 : ztfcq 215082 = c.nreg 215082 :=
      upd_other _ _ _ by_decide
    have h3 : ztfcq 9999 = c.nreg 9999 + 1 := by
      simp_all
    have e' := padLoopH_exec m _ e.wb_right h1 by_grind
      by_grind
    refine ((Exec.whileLtN_true by_omega ztztl e').cast
      by_ring).cast_end ?_
    simp
end exec
end
end DrvH
end Chazelle.Core
namespace Chazelle.Core
namespace DrvH
open Machine Machine.Stmt Programs BuildRam DrvR
@[expose] public section
theorem list_ext_getD {α : Type} {l l' : List α} (x : α) (hl : l.length = l'.length)
    (h : ∀ i, i < l.length → l.getD i x = l'.getD i x) : l = l' :=
  List.ext_getElem hl fun i h1 h2 => by
    simp_all

/-- **The layout determines the records**: two normal forms readable at the same handle have the
same chord, arc and region records. -/
theorem nfAt_recs {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    N.chords = N'.chords ∧ N.arcs = N'.arcs ∧ N.regions = N'.regions := by
  obtain ⟨c0, a0, r0, -, -, hc, ha, hr, -⟩ := h
  obtain ⟨c0', a0', r0', -, -, hc', ha', hr', -⟩ := h'
  refine ⟨list_ext_getD ztrp by_omega fun i hi => ?_,
    list_ext_getD ztgp by_omega fun j hj => ?_,
    list_ext_getD zthmd by_omega fun q hq => ?_⟩
  · zucl

  · zubz

  · zuye

    have harcs : ztkyv :=
      list_ext_getD 0 by_omega fun t ht => by zunma
    have hchs : ztkyw :=
      list_ext_getD 0 by_omega fun t ht => by zunmb
    zuil

/-- `regHost` reads only the chord, arc and region records. -/
theorem regHost_congr {N N' : NF} (hc : N.chords = N'.chords) (ha : N.arcs = N'.arcs)
    (hr : N.regions = N'.regions) (li : Bool) (n r : ℕ) :
    regHost li n N r = regHost li n N' r := by
  zuded
  simp only at hc ha hr
  subst hc ha hr
  rfl
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
/-- **The setup**: constants, bases of the normal form and the record of region `r`. -/
theorem setupS_exec (c : Config) (hw : WordsBounded W c) {B r A₀ : ℕ}
    (h00 : c.nreg 215000 = B) (h01 : c.nreg 215001 = r) (hA₀ : c.nreg 9999 = A₀)
    (hB7 : B + 7 < A₀) (hR : c.nmem zter + 5 * r + 4 < A₀) (hnW : P.n ≤ W)
    (hAW : A₀ + 4 ≤ W) :
    ∃ d k, Exec P W setupS c d k ∧ k = 33 ∧ d.nreg 215020 = 1 ∧ d.nreg 215021 = P.n ∧
      d.nreg 215022 = 0 ∧ d.nreg 215023 = 3 ∧ d.nreg 215024 = 2 ∧
      d.nreg 215025 = c.nmem ztkh ∧ d.nreg 215026 = c.nmem ztow ∧
      d.nreg 215027 = c.nmem ztlw ∧
      d.nreg 215030 = c.nmem ztyvm ∧
      d.nreg 215028 = c.nmem ztwrs ∧
      d.nreg 215031 = c.nmem ztyig ∧
      d.nreg 215029 = c.nmem ztwrt ∧
      d.nreg 215032 = A₀ ∧ d.nreg 215040 = A₀ ∧ d.nreg 215011 = 0 ∧ d.nreg 215012 = 0 ∧
      d.nreg 215041 = 0 ∧ d.nreg 215002 = c.nreg 215002 ∧ d.nreg 9999 = A₀ ∧ d.nmem = c.nmem ∧
      FrameM Ball c d := by
  obtain ⟨d, k, ex, hk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
      h17, h18, h19, hm⟩ : ∃ d k, Exec P W setupS c d k ∧ k = 33 ∧ d.nreg 215020 = 1 ∧
      d.nreg 215021 = P.n ∧
      d.nreg 215022 = 0 ∧ d.nreg 215023 = 3 ∧ d.nreg 215024 = 2 ∧
      d.nreg 215025 = c.nmem ztkh ∧ d.nreg 215026 = c.nmem ztow ∧
      d.nreg 215027 = c.nmem ztlw ∧
      d.nreg 215030 = c.nmem ztyvm ∧
      d.nreg 215028 = c.nmem ztwrs ∧
      d.nreg 215031 = c.nmem ztyig ∧
      d.nreg 215029 = c.nmem ztwrt ∧
      d.nreg 215032 = A₀ ∧ d.nreg 215040 = A₀ ∧ d.nreg 215011 = 0 ∧ d.nreg 215012 = 0 ∧
      d.nreg 215041 = 0 ∧ d.nreg 215002 = c.nreg 215002 ∧ d.nreg 9999 = A₀ ∧ d.nmem = c.nmem := by
    unfold setupS
    exec_block
    all_goals try (config_simp; (try simp only [h00, h01, add_5, add_1_1]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      config_simp <;> simp only [h00, h01, add_5, add_1_1, hA₀]
  exact ⟨d, k, ex, hk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    h17, h18, h19, hm, exec_frameM ex wrM_setupS⟩
end exec
set_option maxHeartbeats 4000000 in
/-- **D3a: the host RAM.** -/
theorem hostRamSpec : DrvR.HostRamSpec := by
  refine ⟨hostS, 3000, ?_⟩
  zujar
  obtain ⟨hG, hWn, hli1, -, L, E, hLne, hL, hperm, hsort, hdeg, hNW, hr⟩ := hPre
  zuhp
  zvnek at hNW hroom
  have hroom' : c.nreg 9999 + 3000 ≤ W := hroom
  have hWn' : ztixz := hWn
  have hn3 : ztgah := hG.1.1
  zucm
  zuiag
  have hF : HFacts P.n ztbaja ztdzj :=
    hqn ▸ hfacts_of hQ hLne hL hperm hsort hdeg hr
  generalize hNdef : BuildNF.buildNF ztwiq zta L E = N at hF hNW hr
  generalize hlidef : decide ztfqe = li
  have hliv : c.nreg 215002 = if li then 1 else 0 := by
    grind
  have hN := hNW.nfAt
  obtain ⟨hb7, hbc, hba, hbr, hbra, hbrc⟩ := Restore.nf_bounds hNW
  obtain ⟨-, -, -, -, -, hNc, hNa, hNr, -⟩ := hN
  -- setup
  obtain ⟨d₁, k₁, e₁, hk₁, s20, s21, s22, s23, s24, s25, s26, s27, s30, s28, s31, s29, s32, s40,
    s11, s12, s41, s02, s99, sm, f₁⟩ := setupS_exec (P := P) c hw rfl rfl rfl hb7
    (hbr _ hr) by_omega by_omega
  have K₁ : Kst P.n li d₁ := ⟨s20, s21, s22, s23, s24, by_omega⟩
  have hE₁ : HEnv W P.n N ztdzj li zterc d₁ := by
    refine ⟨K₁, hF, by zuoua; exact (hNr _ hr).1, by rw [s31]; exact (hNr _ hr).2.1, s32,
      fun t ht => ?_, fun v hv => ?_, fun j hj => ?_, fun i hi => ?_, by_omega, by_omega,
      by omega⟩
    · rw [sm, s27, s28, ← Nat.add_assoc]
      exact ⟨(hNr _ hr).2.2.2.1 t ht, hbra _ hr t ht⟩
    · rw [sm, s27, s29, ← Nat.add_assoc]
      exact ⟨(hNr _ hr).2.2.2.2 v hv, hbrc _ hr v hv⟩
    · rw [sm, s26]
      obtain ⟨a1, a2, a3, a4, a5⟩ := hNa j hj
      exact ⟨a2, a3, a4, a5, hba j hj⟩
    · rw [sm, s25]
      obtain ⟨a1, a2, a3, a4, a5⟩ := hNc i hi
      exact ⟨a1, a2, a3, by have := hbc i hi; omega⟩
  have hB₁ : Buf P.n zterc [] d₁ := ⟨ItemsAt.nil _ _, by_omega,
    by omega, by rw [s12]; rfl⟩
  -- the arc loop
  obtain ⟨d₂, k₂, e₂, hk₂, B₂, E₂, m₂, f₂⟩ := arcLoop_exec (P := P) d₁ e₁.wb_right hE₁ s41 hB₁
  have hK20 : (walkItems li P.n N ztdzj).length ≤ 20 := by
    have := pre_length_le li P.n N ztdzj (N.region ztdzj).arcs.length
    rw [pre_full] at this
    have := hF.hA
    omega
  generalize hxs : walkItems li P.n N ztdzj = xs at B₂ hK20
  -- the host handle
  obtain ⟨d₃, k₃, e₃, hk₃, v10, vm₃, v80, v82, v81, v83, v84, f₃⟩ := finS_exec (P := P) d₂
    e₂.wb_right E₂.K B₂.2.1 B₂.2.2.1 E₂.tR by_omega
  have K₃ := E₂.K.frame f₃ by_decide
  have I₃ : ItemsAt d₃.nmem zterc xs := B₂.1.congr fun a h1 h2 => by
    rw [vm₃, Machine.upd_other _ _ _ by_omega]
  -- the copy
  obtain ⟨d₄, k₄, e₄, hk₄, I₄, w82, m₄, f₄⟩ := cpyLoop_exec (P := P) d₃ e₃.wb_right K₃ I₃
    (by rw [f₃.1 _ by_decide, B₂.2.2.1]) v80 v82 v81 v83 v84 by_omega
  -- the padding
  have p20 : d₄.nreg 215020 = 1 := by rw [f₄.1 _ by_decide, K₃.one]
  have p99 : d₄.nreg 9999 = c.nreg 9999 := by
    rw [f₄.1 _ by_decide, f₃.1 _ by_decide, f₂.1 _ by_decide, s99]
  have e₅ := padLoopH_exec (P := P) ztpuu d₄ e₄.wb_right p20 by_omega
    by_omega
  have ex : Exec P W hostS c { d₄ with nreg := upd d₄.nreg 9999 (d₄.nreg 215082) }
      (k₁ + (k₂ + (k₃ + (k₄ + (3 * ztpuu + 2))))) :=
    .seq e₁ ztbq
  have fA := exec_frameM ex wrM_hostS
  have fR := exec_frameM2 ex wrM2_hostS
  have g₄ : ∀ q, Bcp q = false → d₄.nreg q = d₃.nreg q := f₄.1
  have a99 : ztewc 9999 = c.nreg 9999 + 6 * xs.length + 1 := by
    rw [Machine.upd_same, w82]
  have a10 : ztewc 215010 = c.nreg 9999 + 3 * xs.length := by
    rw [Machine.upd_other _ _ _ by_decide, g₄ _ by_decide, v10]
  have a11 : ztewc 215011 = xs.length := by
    rw [Machine.upd_other _ _ _ by_decide, g₄ _ by_decide, f₃.1 _ by_decide, B₂.2.2.1]
  have a12 : ztewc 215012 = ptsLen P.n xs := by
    rw [Machine.upd_other _ _ _ by_decide, g₄ _ by_decide, f₃.1 _ by_decide, B₂.2.2.2]
  have hmem : ∀ a, a < c.nreg 9999 → d₄.nmem a = c.nmem a := fun a ha => by
    rw [m₄ a by_omega, vm₃, Machine.upd_other _ _ _ by_omega, m₂ a ha, sm]
  have hHB : d₄.nmem (c.nreg 9999 + 3 * xs.length) = xs.length := by
    rw [m₄ _ by_omega, vm₃, Machine.upd_same]
  refine ⟨_, _, ex, show _ ≤ 3000 by omega, ⟨fun q hq hq' => fA.1 q ?_,
    fun L' E' hLne' hL' hperm' hsort' hNA' => ?_⟩,
    ⟨fun q hq hqA => fA.1 q ?_, fun q _ => fR q rfl, hmem, fun a _ => by rw [fA.2.2.1],
      fA.2.2.2, by zuodp; omega,
      by zuodp; omega⟩⟩
  · zvmxo at hq
    zunvg; omega
  · have hrec := nfAt_recs hNA' hNW.nfAt
    have hH : regHost li (Qof P).n ztbapb
        ztdzj = if li then xs else xs.reverse := by
      rw [regHost_congr hrec.1 hrec.2.1 hrec.2.2, hqn, ← hxs]; rfl
    zubvt
    rw [hlidef, hH]
    have hl : (if li then xs else xs.reverse).length = xs.length := by split_ifs <;> simp
    simp only [hAL, a99, a10, a11, a12, hl]
    refine ⟨by_omega, by_omega, hostAt_of by_omega I₄, trivial, ?_⟩
    zuovh
    split_ifs
    · rfl
    · exact (ptsLen_reverse P.n xs).symm
  · zuggw
    zunvg
    omega
end
end DrvH
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs
@[expose] public section
def hltS : Stmt :=
  .seq (block [.readY 217160 217160, .readY 217161 217161])
    (.ifLtR 217160 217161 ztoyg
      (.ifLtR 217161 217160 ztoyf
        (.seq (block [.readX 217160 217160, .readX 217161 217161])
          (.ifLtR 217160 217161 ztoyg ztoyf))))

/-! ## Walk vertex and walk edge indices -/

/-- `dst := ivB li n src`. -/
def ivBS (src dst : ℕ) : Stmt :=
  .ifLtN 217026 217027 (block [.subN dst 217020 217027, .subN dst dst src])
    ztihw

/-- `dst := qE li n src` (scratch `217104`). -/
def qES (src dst : ℕ) : Stmt :=
  .ifLtN 217026 217027
    (.seq (block [.addN 217104 src 217027])
      (.ifLtN 217104 217020 (block [.subN dst 217020 217027, .subN dst dst 217027, .subN dst dst src])
        (block [.subN dst 217020 217027])))
    ztihw

/-- `dst := (src + 1) mod n` for `src < n`. -/
def succS (src dst : ℕ) : Stmt :=
  .seq (block [.addN dst src 217027]) (.ifLtN dst 217020 .skip ztoyi)

/-! ## Key order of interior positions -/

/-- The core of `posLtS` (equal edges, different heights). -/
def posLtCore : Stmt :=
  .seq (ivBS 217150 217160)
    (.seq (succS 217150 217155)
      (.seq (ivBS 217155 217161)
        (.seq hltS
          (.seq (block [.copyN 217156 217162, .subN 217160 217151 217027,
              .subN 217161 217153 217027])
            (.seq hltS
              (.ifLtN 217156 217162 ztdty
                ztyzy))))))

/-- `217154 := [PosLt ⟨217150, 217151⟩ ⟨217152, 217153⟩]`. -/
def posLtS : Stmt :=
  .ifLtN 217150 217152 ztihu
    (.ifLtN 217152 217150 ztdty
      (.ifLtN 217151 217153 posLtCore
        (.ifLtN 217153 217151 posLtCore ztdty)))

/-! ## Host points -/

/-- One host item of `lookS`. -/
def lookBody : Stmt :=
  .seq (block [.loadN 217094 217092, .addN 217097 217092 217027, .loadN 217095 217097,
      .addN 217097 217097 217027, .loadN 217096 217097])
    (.seq
      (.ifLtN 217094 217027
        -- a run `a = x1`, `ℓ = x2`
        (.seq
          (.ifLtN 217090 217093 .skip
            (.seq ztnsl
              (.ifLtN 217096 217097 .skip
                (.seq ztjpe
                  ztifj))))
          ztiqo)
        -- a point
        (.seq
          (.ifLtN 217090 217093 .skip
            (.ifLtN 217093 217090 .skip
              zthtb))
          ztnsd))
      (block [.addN 217092 217092 217027, .addN 217092 217092 217027, .addN 217092 217092 217027,
        .addN 217091 217091 217027]))

/-- **Host point `k = 217090`** (`217070` kind, `217071`, `217072` arguments). -/
def lookS : Stmt :=
  .seq (block [.constN 217091 0, .copyN 217092 217035, .constN 217093 0])
    (.whileLtN 217091 217034 lookBody)

/-! ## The ends of a chord -/

/-- A list of statements in sequence. -/
def seqs : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: l => .seq s (seqs l)
theorem seqs_cons₂ (s t : Stmt) (l : List Stmt) : seqs (s :: t :: l) = .seq s (seqs (t :: l)) := rfl

/-- **Classify the end at walk edge `p = 217060`** (height vertex `h = 217050`). -/
def clsS : Stmt := seqs [
  block [.subN 217061 217060 217041, .addN 217061 217025 217061],
  .ifLtN 217061 217022 .skip ztnsk,
  .ifLtN 217061 217022 .skip ztnsk,
  .ifLtN 217061 217021 (block [.constN 217063 1]) (block [.constN 217063 0]),
  .ifLtN 217021 217061 (block [.subN 217062 217022 217061]) (block [.copyN 217062 217061]),
  block [.copyN 217090 217062],
  lookS,
  .ifLtN 217070 217044 (block [.copyN 217066 217071]) (block [.copyN 217066 217072]),
  .ifLtN 217050 217066 ztiht
    (.ifLtN 217066 217050 ztiht ztoye),
  block [.constN 217064 1],
  .ifLtN 217060 217041 ztbfx .skip,
  .ifLtN 217042 217060 ztbfx .skip,
  .ifLtN 217060 217042 .skip
    (.ifLtN 217042 217060 .skip ztyzw),
  .ifLtN 217065 217027 .skip
    (.ifLtN 217062 217027 ztbfx
      ztxtz),
  .ifLtN 217063 217026 ztbfx
    (.ifLtN 217026 217063 ztbfx .skip)]

/-- **The interior walk edge of the host point** `217070 … 217072` into `217100`. -/
def peS : Stmt :=
  .ifLtN 217070 217044 (ivBS 217071 217100)
    (.seq (qES 217071 217101)
      (.seq (succS 217101 217102)
        (.seq (ivBS 217102 217103)
          (.ifLtN 217072 217103 ztoyz
            (.ifLtN 217103 217072 ztoyz
              (block [.copyN 217100 217102]))))))

/-! ## Buckets -/

/-- `dst := [a = b ∧ c = d]`. -/
def eq2S (a b c d dst : ℕ) : Stmt :=
  .seq ztoyi
    (.ifLtN a b .skip (.ifLtN b a .skip (.ifLtN c d .skip (.ifLtN d c .skip (block [.constN dst 1])))))

/-- `posLtS` on four registers, result into `dst`. -/
def posLtOn (a b c d dst : ℕ) : Stmt :=
  .seq (block [.copyN 217150 a, .copyN 217151 b, .copyN 217152 c, .copyN 217153 d])
    (.seq posLtS (block [.copyN dst 217154]))

/-- The bucket formula `bktF A j eqS eqE gtS` into `217112`. -/
def bktFS : Stmt :=
  .ifLtN 217122 217027
    (.ifLtN 217123 217027
      (.ifLtN 217125 217027 (block [.constN 217112 0])
        (block [.addN 217112 217116 217116, .addN 217112 217112 217044]))
      (.seq (block [.addN 217128 217116 217027])
        (.ifLtN 217128 217030 (block [.addN 217112 217128 217128, .addN 217112 217112 217027])
          (block [.constN 217112 1]))))
    (block [.addN 217112 217116 217116, .addN 217112 217112 217027])

/-- The arc test `eqS ∨ eqE ∨ (ltSE ? ltSX ∧ ltXE : ltSX ∨ ltXE)` into `217127`. -/
def onS : Stmt :=
  .seq (block [.constN 217127 0])
    (.ifLtN 217122 217027
      (.ifLtN 217123 217027
        (.ifLtN 217124 217027
          (.ifLtN 217125 217027 ztyzx
            ztdtx)
          (.ifLtN 217125 217027 .skip ztyzx))
        ztdtx)
      ztdtx)

/-- Read arc `j = mem 217114` of `N`: `217116 j`, `217118 … 217121` its ends. -/
def arcRdS : Stmt :=
  block [.loadN 217116 217114, .addN 217117 217116 217116, .addN 217117 217117 217117,
    .addN 217117 217117 217116, .addN 217117 217117 217031,
    .addN 217128 217117 217027, .loadN 217118 217128, .addN 217128 217128 217027,
    .loadN 217119 217128, .addN 217128 217128 217027, .loadN 217120 217128,
    .addN 217128 217128 217027, .loadN 217121 217128]

/-- One arc of the region in `bktS`. -/
def bktBody : Stmt := seqs [
  arcRdS,
  eq2S 217110 217118 217111 217119 217122,
  eq2S 217110 217120 217111 217121 217123,
  posLtOn 217118 217119 217120 217121 217124,
  posLtOn 217118 217119 217110 217111 217125,
  posLtOn 217110 217111 217120 217121 217126,
  onS,
  .ifLtN 217115 217027 ztbum .skip,
  block [.addN 217114 217114 217027, .addN 217113 217113 217027]]

/-- **The bucket of the interior position `⟨217110, 217111⟩`** into `217112`. -/
def bktS : Stmt :=
  .seq (block [.constN 217113 0, .copyN 217114 217033, .constN 217115 0, .constN 217112 0])
    (.whileLtN 217113 217032 bktBody)
open BuildRam SignK
open Classical in
/-- The value computed by `hltS`. -/
noncomputable def hltF (P : Polygon) (u v : ℕ) : ℕ :=
  if Mountain.ylexLT ztenr ztvcp then 1 else 0

/-- The registers `hltS` writes. -/
def Bhlt (r : ℕ) : Bool := decide (r = 217160 ∨ r = 217161 ∨ r = 217162)
theorem wr_hlt : wr Bhlt hltS = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
/-- **`hltS`**: the height order of the input vertices. -/
theorem hltS_exec (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W hltS d d' k ∧ k ≤ 12 ∧
      d'.nreg 217162 = hltF P ztjtq ztjtr ∧ FrameB Bhlt d d' := by
  obtain ⟨d', k, ex, hk, h1⟩ : ∃ d' k, Exec P W hltS d d' k ∧ k ≤ 12 ∧
      d'.nreg 217162 = hltF P ztjtq ztjtr := by
    unfold hltS hltF
    refine spec_seq ?_
    exec_block
    by_cases hy : (P.vtx ztjtq).2 < (P.vtx ztjtr).2
    · zucix
      exec_block
      · omega
      · zubsc
        config_simp
        rw [ite_eq_left (show Mountain.ylexLT _ _ from Or.inl hy)]
    · zupb
      by_cases hy' : (P.vtx ztjtr).2 < (P.vtx ztjtq).2
      · zucix
        exec_block
        · omega
        · zubsc
          config_simp
          rw [ite_eq_right ztohs]
          rintro (h | ⟨h, -⟩)
          · simp_all
          simp_all
      · zupb
        have heq : (P.vtx _).2 = (P.vtx _).2 :=
          le_antisymm (not_lt.1 hy') (not_lt.1 hy)
        refine spec_seq ?_
        exec_block
        by_cases hx : (P.vtx ztjtq).1 < (P.vtx ztjtr).1
        · zucix
          exec_block
          · omega
          · zubsc
            config_simp
            rw [ite_eq_left (show Mountain.ylexLT _ _ from Or.inr by_simp_all)]
        · zupb
          exec_block
          · omega
          · zubsc
            config_simp
            rw [ite_eq_right ztohs]
            rintro (h | ⟨-, h⟩)
            · simp_all
            simp_all
  exact ⟨d', k, ex, hk, h1, exec_frameB ex wr_hlt⟩

/-- The register value of the `li` bit. -/
def liV (li : Bool) : ℕ := if li then 1 else 0
theorem liV_le (li : Bool) : liV li ≤ 1 := by unfold liV; grind
set_option maxHeartbeats 1000000 in
/-- **`ivBS`**: `dst := ivB li n src`. -/
theorem ivBS_exec (d : Config) (hw : WordsBounded W d) {src dst n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hsd : src ≠ dst) (_hd20 : dst ≠ 217020) (_hd27 : dst ≠ 217027) :
    ∃ d' k, Exec P W (ivBS src dst) d d' k ∧ k ≤ 4 ∧
      d'.nreg = upd d.nreg dst (DrvR.ivB li n ztvov) ∧ d'.rreg = d.rreg ∧
      d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  unfold ivBS
  cases li
  · zumjv
    zumkc
    zujfr
    zumjz
    simp only [Machine.upd_same, Machine.upd_other _ _ _ hsd, h20, h27,
      Machine.upd_upd_same, DrvR.ivB, Bool.false_eq_true, ite_false]
  · zuiez

    refine spec_nil hw₁ ztcbo
    rfl
set_option maxHeartbeats 1000000 in
/-- **`succS`**: `dst := (src + 1) mod n` for `src < n`. -/
theorem succS_exec (d : Config) (hw : WordsBounded W d) {src dst n : ℕ}
    (h20 : d.nreg 217020 = n) (h27 : d.nreg 217027 = 1) (hs : d.nreg src < n) (hnW : n ≤ W)
    (hd20 : dst ≠ 217020) :
    ∃ d' k, Exec P W (succS src dst) d d' k ∧ k ≤ 4 ∧
      d'.nreg = upd d.nreg dst ((d.nreg src + 1) % n) ∧ d'.rreg = d.rreg ∧
      d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  unfold succS
  zujl
  zuifa

  zuhbj
  · refine spec_ifLtN_true (by simp only [Machine.upd_same,
      Machine.upd_other _ _ _ hd20.symm, h20, h27]; exact h) ?_
    refine spec_skip hw₁ ztcbo
    rw [h27, Nat.mod_eq_of_lt h]
  · refine spec_ifLtN_false (by simp only [Machine.upd_same,
      Machine.upd_other _ _ _ hd20.symm, h20, h27]; exact h) ?_
    refine spec_step (Machine.Exec.constN hw₁ _ _ by_omega) zthxf
    zumjz
    simp only [Machine.upd_upd_same, h27]
    rw [show d.nreg src + 1 = n by omega, Nat.mod_self]
set_option maxHeartbeats 1000000 in
/-- **`qES`**: `dst := qE li n src` (scratch `217104`). -/
theorem qES_exec (d : Config) (hw : WordsBounded W d) {src dst n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hs : d.nreg src < n) (hnW : n ≤ W) (hsd : src ≠ dst) (_hd20 : dst ≠ 217020)
    (hd27 : dst ≠ 217027) (_hd04 : dst ≠ 217104) (hs04 : src ≠ 217104) :
    ∃ d' k, Exec P W (qES src dst) d d' k ∧ k ≤ 8 ∧
      d'.nreg dst = DrvR.qE li n ztvov ∧
      (∀ r, r ≠ dst → r ≠ 217104 → d'.nreg r = d.nreg r) ∧ d'.rreg = d.rreg ∧
      d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  unfold qES
  cases li
  · zumjv
    zujl
    zuifa

    set f := upd d.nreg 217104 _ with hf
    have g : ∀ r, r ≠ 217104 → f r = d.nreg r := by_simp_all
    have g04 : f 217104 = d.nreg src + 1 := by_simp_all
    have g20 : f 217020 = n := by_simp_all
    have g27 : f 217027 = 1 := by_simp_all
    have gs : f src = d.nreg src := by_simp_all
    zuhbj
    · zuek
      zujfr
      refine spec_step (Machine.Exec.subN hw₂ _ _ _) (fun hw₃ => ?_)
      refine spec_step (Machine.Exec.subN hw₃ _ _ _) (fun hw₄ => ?_)
      refine spec_nil hw₄ ztfze
      · simp only [Machine.upd_same, Machine.upd_upd_same,
          Machine.upd_other _ _ _ hsd, Machine.upd_other _ _ _ hd27.symm, g20, g27, gs, DrvR.qE, Bool.false_eq_true, ite_false,
          ite_eq_left h]
        omega
      simp_all
    · zudx
      zujfr
      refine spec_nil hw₂ ztfze
      · simp only [Machine.upd_same, g20, g27, DrvR.qE, Bool.false_eq_true,
          ite_false, ite_eq_right h]
      simp_all
  · zuiez

    refine spec_nil hw₁ ⟨by_omega, ?_, fun r h1 _ => ?_, rfl, rfl, rfl, rfl⟩
    · simp [DrvR.qE]
    simp_all
open Classical in
/-- The value computed by `posLtS`. -/
noncomputable def posLtF (P : Polygon) (li : Bool) (n ae ah be bh : ℕ) : ℕ :=
  if ae < be then 1 else if be < ae then 0 else if ah = bh then 0 else
    if hltF P (DrvR.ivB li n ae) (DrvR.ivB li n ((ae + 1) % n)) = hltF P (ah - 1) (bh - 1) then 1
    else 0

/-- The registers `posLtS` writes. -/
def BposLt (r : ℕ) : Bool :=
  decide (r = 217154 ∨ r = 217155 ∨ r = 217156 ∨ r = 217160 ∨ r = 217161 ∨ r = 217162)
theorem wr_posLt : wr BposLt posLtS = true := by_decide
set_option maxHeartbeats 2000000 in
/-- The core of `posLtS`. -/
theorem posLtCore_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hae : d.nreg 217150 < n) (hnW : n ≤ W) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W posLtCore d d' k ∧ k ≤ 45 ∧
      d'.nreg 217154 = (if hltF P ztzju
        ztzjt = hltF P (d.nreg 217151 - 1) (d.nreg 217153 - 1)
        then 1 else 0) := by
  -- `u1 := ivB ae`
  obtain ⟨d1, k1, e1, hk1, n1, r1, m1, -, -⟩ := ivBS_exec (P := P) d hw (src := 217150)
    (dst := 217160) h20 h26 h27 by_decide by_decide by_decide
  have v1 : ∀ r, r ≠ 217160 → d1.nreg r = d.nreg r := by_simp_all
  -- `q1 := (ae + 1) mod n`
  obtain ⟨d2, k2, e2, hk2, n2, -, -, -, -⟩ := succS_exec (P := P) d1 e1.wb_right (src := 217150)
    (dst := 217155) by_simp_all by_simp_all
    by_simp_all hnW by_decide
  have v2 : ∀ r, r ≠ 217155 → d2.nreg r = d1.nreg r := by_simp_all
  -- `u2 := ivB q1`
  obtain ⟨d3, k3, e3, hk3, n3, -, -, -, -⟩ := ivBS_exec (P := P) d2 e2.wb_right (src := 217155)
    (dst := 217161) by_rfl
    (by rw [v2 _ by_decide, v1 _ by_decide, h26]) by_simp_all
    by_decide by_decide by_decide
  have v3 : ∀ r, r ≠ 217161 → d3.nreg r = d2.nreg r := by_simp_all
  have a160 : d3.nreg 217160 = DrvR.ivB li n ztjtp := by
    simp_all
  have a161 : d3.nreg 217161 = DrvR.ivB li n ztgbi := by
    simp_all
  -- `up`
  obtain ⟨d4, k4, e4, hk4, up4, f4⟩ := hltS_exec (P := P) d3 e3.wb_right hW
  have v4 := f4.1
  have g4 : ∀ r, Bhlt r = false → r ≠ 217155 → d4.nreg r = d.nreg r := fun r hr h55 => by
    rw [v4 r hr, v3 r ztiry,
      v2 r h55, v1 r ztiry]
  -- heights
  obtain ⟨d5, k5, e5, hk5, a56, a60, a61, g5⟩ : ∃ d5 k5, Exec P W (block [.copyN 217156 217162,
      .subN 217160 217151 217027, .subN 217161 217153 217027]) d4 d5 k5 ∧ k5 = 3 ∧
      d5.nreg 217156 = d4.nreg 217162 ∧ d5.nreg 217160 = d.nreg 217151 - 1 ∧
      d5.nreg 217161 = d.nreg 217153 - 1 ∧
      (∀ r, r ≠ 217156 → r ≠ 217160 → r ≠ 217161 → d5.nreg r = d4.nreg r) := by
    zubgi
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_⟩ <;> config_simp
    · zuelp
    · zuelp
    simp_all
  -- `hc`
  obtain ⟨d6, k6, e6, hk6, hc6, f6⟩ := hltS_exec (P := P) d5 e5.wb_right hW
  have b56 : d6.nreg 217156 = hltF P ztzju
      ztzjt := by
    rw [f6.1 _ by_decide, a56, up4, a160, a161]
  rw [a60, a61] at hc6
  -- the comparison
  obtain ⟨d7, k7, e7, hk7, h7⟩ : ∃ d7 k7, Exec P W (.ifLtN 217156 217162 (block [.constN 217154 0])
      ztyzy) d6 d7 k7 ∧
      k7 ≤ 5 ∧ d7.nreg 217154 = (if d6.nreg 217156 = d6.nreg 217162 then 1 else 0) := by
    zueso
    by_cases c1 : d6.nreg 217156 < d6.nreg 217162
    · zugsr
      exec_block
      · omega
      · refine zteh; config_simp; rw [ite_eq_right by_omega]
    · zuevv
      by_cases c2 : d6.nreg 217162 < d6.nreg 217156
      · zujfg
        exec_block
        · omega
        · refine zteh; config_simp; rw [ite_eq_right by_omega]
      · zugsp
        exec_block
        · omega
        · refine zteh; config_simp; grind
  refine ⟨d7, k1 + ztcnr,
    .seq e1 ztfmk, by_omega, ?_⟩
  rw [h7, b56, hc6]
set_option maxHeartbeats 2000000 in
/-- **`posLtS`**: the key order of two interior positions. -/
theorem posLtS_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hae : d.nreg 217150 < n) (hnW : n ≤ W) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W posLtS d d' k ∧ k ≤ 52 ∧
      d'.nreg 217154 = posLtF P li n ztjtp ztvom ztvon
        ztvoo ∧ FrameB BposLt d d' := by
  obtain ⟨d', k, ex, hk, hv⟩ : ∃ d' k, Exec P W posLtS d d' k ∧ k ≤ 52 ∧
      d'.nreg 217154 = posLtF P li n ztjtp ztvom ztvon
        ztvoo := by
    unfold posLtS posLtF
    by_cases c1 : d.nreg 217150 < d.nreg 217152
    · zugsr
      exec_block
      · omega
      simp_all
    · zuevv
      by_cases c2 : d.nreg 217152 < d.nreg 217150
      · zujfg
        exec_block
        · omega
        simp_all
      · zugsp
        by_cases c3 : d.nreg 217151 < d.nreg 217153
        · refine spec_ifLtN_true c3 ?_
          zulop

        · refine spec_ifLtN_false c3 ?_
          by_cases c4 : d.nreg 217153 < d.nreg 217151
          · refine spec_ifLtN_true c4 ?_
            zulop

          · refine spec_ifLtN_false c4 ?_
            exec_block
            · omega
            · refine zteh; config_simp; grind
  exact ⟨d', k, ex, hk, hv, exec_frameB ex wr_posLt⟩
end exec
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
@[expose] public section
def NRegs (d d' : Config) (f : ℕ → ℕ) : Prop :=
  d'.nreg = f ∧ d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output
section steps
variable {P : Polygon} {W : ℕ}
theorem x_const (d : Config) (hw : WordsBounded W d) (r v : ℕ) (hv : v ≤ W) :
    ∃ d' k, Exec P W ztoyj d d' k ∧ k ≤ 1 ∧ NRegs d d' ztluh := by
  refine spec_step (Machine.Exec.constN hw _ _ hv) ztczm
  zuitv
theorem x_copy (d : Config) (hw : WordsBounded W d) (r a : ℕ) :
    ∃ d' k, Exec P W ztozc d d' k ∧ k ≤ 1 ∧ NRegs d d' (upd d.nreg r ztvor) := by
  refine spec_step ztlfh ztczm
  zuitv
theorem x_sub (d : Config) (hw : WordsBounded W d) (r a b : ℕ) :
    ∃ d' k, Exec P W ztnsm d d' k ∧ k ≤ 1 ∧
      NRegs d d' (upd d.nreg r (d.nreg a - d.nreg b)) := by
  zumkc
  zuitv
theorem x_skipR (d : Config) (hw : WordsBounded W d) (r : ℕ) :
    ∃ d' k, Exec P W .skip d d' k ∧ k ≤ 1 ∧ NRegs d d' (upd d.nreg r ztvot) :=
  ⟨d, 0, .skip hw, by_omega, by_simp, rfl, rfl, rfl, rfl⟩
theorem x_mono {s : Stmt} {d : Config} {K K' : ℕ} {Q : Config → Prop}
    (h : ∃ d' k, Exec P W s d d' k ∧ k ≤ K ∧ Q d') (hK : K ≤ K') :
    ∃ d' k, Exec P W s d d' k ∧ k ≤ K' ∧ Q d' := by
  grind
theorem x_if {a b : ℕ} {t e : Stmt} {d : Config} {K : ℕ} {f g : ℕ → ℕ}
    (ht : d.nreg a < d.nreg b → ∃ d' k, Exec P W t d d' k ∧ k ≤ K ∧ NRegs d d' f)
    (he : ¬ d.nreg a < d.nreg b → ∃ d' k, Exec P W e d d' k ∧ k ≤ K ∧ NRegs d d' g) :
    ∃ d' k, Exec P W ztva d d' k ∧ k ≤ K + 2 ∧
      NRegs d d' (if d.nreg a < d.nreg b then f else g) := by
  by_cases h : d.nreg a < d.nreg b
  · obtain ⟨d', k, ex, hk, hn⟩ := ht h
    exact ⟨d', k + 1, .ifLtN_true h ex, by_omega, by_simp_all⟩
  · obtain ⟨d', k, ex, hk, hn⟩ := he h
    exact ⟨d', k + 2, .ifLtN_false h ex, by_omega, by_grind⟩
theorem x_ifR {a b r : ℕ} {t e : Stmt} {d : Config} {K : ℕ} {v₁ v₂ : ℕ}
    (ht : d.nreg a < d.nreg b → ∃ d' k, Exec P W t d d' k ∧ k ≤ K ∧ NRegs d d' (upd d.nreg r v₁))
    (he : ¬ d.nreg a < d.nreg b → ∃ d' k, Exec P W e d d' k ∧ k ≤ K ∧
      NRegs d d' (upd d.nreg r v₂)) :
    ∃ d' k, Exec P W ztva d d' k ∧ k ≤ K + 2 ∧
      NRegs d d' (upd d.nreg r (if d.nreg a < d.nreg b then v₁ else v₂)) := by
  obtain ⟨d', k, ex, hk, hn⟩ := x_if ht he
  grind

/-- Sequencing with an `NRegs` first part. -/
theorem x_seq {s t : Stmt} {d : Config} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop}
    (h₁ : ∃ d₁ k₁, Exec P W s d d₁ k₁ ∧ k₁ ≤ K₁ ∧ Q₁ d₁)
    (h₂ : ∀ d₁, WordsBounded W d₁ → Q₁ d₁ → ∃ d₂ k₂, Exec P W t d₁ d₂ k₂ ∧ k₂ ≤ K₂ ∧ Q₂ d₂) :
    ∃ d₂ k, Exec P W ztfmm d d₂ k ∧ k ≤ K₁ + K₂ ∧ Q₂ d₂ := by
  obtain ⟨d₁, k₁, e₁, hk₁, q₁⟩ := h₁
  obtain ⟨d₂, k₂, e₂, hk₂, q₂⟩ := h₂ d₁ e₁.wb_right q₁
  exact ⟨d₂, k₁ + k₂, .seq e₁ e₂, by_omega, q₂⟩
end steps

/-! ## Host points -/

/-- The registers `217070 … 217072` encode the symbolic point `s`. -/
def Enc (d : Config) : SymPt → Prop
  | .vtx j => d.nreg 217070 = 1 ∧ d.nreg 217071 = j
  | .onEdge e h => d.nreg 217070 = 2 ∧ d.nreg 217071 = e ∧ d.nreg 217072 = h
theorem Enc.congr {d d' : Config} {s : SymPt} (h : Enc d s) (h0 : d'.nreg 217070 = d.nreg 217070)
    (h1 : d'.nreg 217071 = d.nreg 217071) (h2 : d'.nreg 217072 = d.nreg 217072) : Enc d' s := by
  cases s <;> simp only [Enc] at h ⊢ <;> omega

/-- A host item at address `p` (three words). -/
def ItemAt (m : ℕ → ℕ) (p : ℕ) : HostItem → Prop
  | .run a ℓ => m p = 0 ∧ m ztr = a ∧ m ztcao = ℓ
  | .pt (.vtx j) => m p = 1 ∧ m ztr = j
  | .pt (.onEdge e h) => m p = 2 ∧ m ztr = e ∧ m ztcao = h

/-- A well-formed host item. -/
def ItemWF (n : ℕ) : HostItem → Prop
  | .run a ℓ => a < n ∧ ℓ < n
  | .pt x => x.Lt n
theorem itemAt_of_hostAt {m : ℕ → ℕ} {B : ℕ} {H : Host} (hH : HostAt m B H) {i : ℕ}
    (hi : i < H.length) : ItemAt m ztban ztwzh := by
  have h := hH.2 i hi
  have e1 : B + 1 + 3 * i + 1 = B + 2 + 3 * i := by_omega
  have e2 : B + 1 + 3 * i + 2 = B + 3 + 3 * i := by_omega
  rcases hx : H.getD i _ with ⟨a, ℓ⟩ | ⟨j | ⟨e, h'⟩⟩ <;> zvnly at h <;>
    simp only [ItemAt, e1, e2] at h ⊢ <;> exact h
variable {n : ℕ}
theorem itemWF_of_hostWF {H : Host} (hH : HostWF n H) {i : ℕ} (hi : i < H.length) :
    ItemWF n ztwzh := by
  have hmem : H.getD i ztmn ∈ H := by
    simp_all
  tauto
theorem pts_take_succ {H : Host} {j : ℕ} (hj : j < H.length) :
    Host.pts n ztbaec = Host.pts n ztgdy ++ (H.getD j ztmn).pts n := by
  zultt
  rw [List.take_add_one, List.flatMap_append, List.getElem?_eq_getElem hj,
    List.getD_eq_getElem _ _ hj]
  simp
theorem hpt_take {H : Host} {j k : ℕ} (hk : k < (Host.pts n ztgdy).length) :
    hpt n H k = (Host.pts n ztgdy).getD k ztga := by
  unfold hpt
  conv_lhs => rw [← List.take_append_drop j H]
  unfold Host.pts at hk ⊢
  grind
theorem run_pts_length (n a ℓ : ℕ) : ((HostItem.run a ℓ).pts n).length = ℓ + 1 := by
  zumpk
theorem run_pts_getD (n a ℓ : ℕ) {t : ℕ} (ht : t ≤ ℓ) :
    ((HostItem.run a ℓ).pts n).getD t ztga = .vtx ztxyz := by
  zulaj

/-! ## `lookS` -/

/-- The run case of `lookBody`. -/
def lookRun : Stmt :=
  .seq
    (.ifLtN 217090 217093 .skip
      (.seq ztnsl
        (.ifLtN 217096 217097 .skip
          (.seq ztjpe
            ztifj))))
    ztiqo

/-- The point case of `lookBody`. -/
def lookPt : Stmt :=
  .seq
    (.ifLtN 217090 217093 .skip
      (.ifLtN 217093 217090 .skip
        zthtb))
    ztnsd

/-- The first block of `lookBody`. -/
def lookRd : Stmt :=
  block [.loadN 217094 217092, .addN 217097 217092 217027, .loadN 217095 217097,
    .addN 217097 217097 217027, .loadN 217096 217097]

/-- The last block of `lookBody`. -/
def lookNx : Stmt :=
  block [.addN 217092 217092 217027, .addN 217092 217092 217027, .addN 217092 217092 217027,
    .addN 217091 217091 217027]
theorem lookBody_eq : lookBody = .seq lookRd (.seq ztjcz lookNx) :=
  rfl

/-- The registers `lookS` writes. -/
def Blook (r : ℕ) : Bool :=
  decide (r = 217070 ∨ r = 217071 ∨ r = 217072 ∨ (217091 ≤ r ∧ r ≤ 217097))

/-- The registers the item cases write. -/
def Bitem (r : ℕ) : Bool :=
  decide (r = 217070 ∨ r = 217071 ∨ r = 217072 ∨ r = 217093 ∨ r = 217097)
theorem wr_lookRun : wr Bitem lookRun = true := by_decide
theorem wr_lookPt : wr Bitem lookPt = true := by_decide
section look
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
theorem lookRun_exec (d : Config) (hw : WordsBounded W d) {n a ℓ cum : ℕ}
    (h20 : d.nreg 217020 = n) (h27 : d.nreg 217027 = 1) (h93 : d.nreg 217093 = cum)
    (h95 : d.nreg 217095 = a) (h96 : d.nreg 217096 = ℓ) (ha : a < n) (hℓ : ℓ < n)
    (hnW : 2 * n ≤ W) (hcW : cum + ℓ + 1 ≤ W) :
    ∃ d' k, Exec P W lookRun d d' k ∧ k ≤ 14 ∧ d'.nreg 217093 = cum + ztmv ∧
      (d.nreg 217090 < cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (cum ≤ d.nreg 217090 → d.nreg 217090 ≤ cum + ℓ →
        Enc d' ztyaj) ∧ FrameB Bitem d d' := by
  obtain ⟨d', k, ex, hk, h1, h2, h3⟩ : ∃ d' k, Exec P W lookRun d d' k ∧ k ≤ 14 ∧
      d'.nreg 217093 = cum + ztmv ∧
      (d.nreg 217090 < cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (cum ≤ d.nreg 217090 → d.nreg 217090 ≤ cum + ℓ →
        Enc d' ztyaj) := by
    unfold lookRun
    zujl
    zuhsc
    · zugsr
      refine spec_skip hw ?_
      exec_block
      · omega
      · simp_all
      · refine ⟨by_omega, by config_simp; omega, by_simp_all, by_simp_all⟩
    · zuevv
      refine spec_seq ?_
      exec_block
      by_cases c2 : ℓ < d.nreg 217090 - cum
      · zuek
        zurc
        exec_block
        · config_simp; omega
        · simp_all
        · refine ⟨by_omega, by config_simp; omega, by_simp_all,
            by grind⟩
      · zudx
        refine spec_seq ?_
        exec_block
        · omega
        · config_simp; omega
        by_cases c3 : a + ztfqx < n
        · zuek
          zurc
          exec_block
          · config_simp; omega
          · simp_all
          · refine ⟨by_omega, by config_simp; omega, by_simp_all,
              fun _ _ => ?_⟩
            simp only [Enc]
            config_simp
            rw [Nat.mod_eq_of_lt c3]; omega
        · zudx
          exec_block
          · config_simp; omega
          · config_simp; omega
          · refine ⟨by_omega, by config_simp; omega, by_grind,
              fun _ _ => ?_⟩
            simp only [Enc]
            config_simp
            zul
            omega
  exact ⟨d', k, ex, hk, h1, h2, h3, exec_frameB ex wr_lookRun⟩
set_option maxHeartbeats 1000000 in
theorem lookPt_exec (d : Config) (hw : WordsBounded W d) {cum : ℕ}
    (h27 : d.nreg 217027 = 1) (h93 : d.nreg 217093 = cum) (hcW : cum + 1 ≤ W) :
    ∃ d' k, Exec P W lookPt d d' k ∧ k ≤ 8 ∧ d'.nreg 217093 = cum + 1 ∧
      (d.nreg 217090 ≠ cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (d.nreg 217090 = cum → d'.nreg 217070 = d.nreg 217094 ∧ d'.nreg 217071 = d.nreg 217095 ∧
        d'.nreg 217072 = d.nreg 217096) ∧ FrameB Bitem d d' := by
  obtain ⟨d', k, ex, hk, h1, h2, h3⟩ : ∃ d' k, Exec P W lookPt d d' k ∧ k ≤ 8 ∧
      d'.nreg 217093 = cum + 1 ∧
      (d.nreg 217090 ≠ cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (d.nreg 217090 = cum → d'.nreg 217070 = d.nreg 217094 ∧ d'.nreg 217071 = d.nreg 217095 ∧
        d'.nreg 217072 = d.nreg 217096) := by
    unfold lookPt
    zujl
    zuhsc
    · zugsr
      refine spec_skip hw ?_
      exec_block
      · omega
      · refine ztomt
    · zuevv
      by_cases c2 : d.nreg 217093 < d.nreg 217090
      · zujfg
        refine spec_skip hw ?_
        exec_block
        · omega
        · refine ztomt
      · zugsp
        exec_block
        · simp_all
        · refine ⟨by_omega, by_simp_all, by_omega,
            by simp_all⟩
  exact ⟨d', k, ex, hk, h1, h2, h3, exec_frameB ex wr_lookPt⟩
set_option maxHeartbeats 2000000 in
/-- **One host item of `lookS`.** -/
theorem lookBody_exec (d : Config) (hw : WordsBounded W d) {n p cum : ℕ} {it : HostItem}
    (h20 : d.nreg 217020 = n) (h27 : d.nreg 217027 = 1) (h92 : d.nreg 217092 = p)
    (h93 : d.nreg 217093 = cum) (hit : ItemAt d.nmem p it) (hwf : ItemWF n it)
    (hpW : p + 3 ≤ W) (hcW : cum + (it.pts n).length ≤ W) (h91W : d.nreg 217091 + 1 ≤ W)
    (hnW : 2 * n ≤ W) :
    ∃ d' k, Exec P W lookBody d d' k ∧ k ≤ 30 ∧
      d'.nreg 217091 = d.nreg 217091 + 1 ∧ d'.nreg 217092 = p + 3 ∧
      d'.nreg 217093 = cum + (it.pts n).length ∧
      (d.nreg 217090 < cum → d'.nreg 217070 = d.nreg 217070 ∧ d'.nreg 217071 = d.nreg 217071 ∧
        d'.nreg 217072 = d.nreg 217072) ∧
      (cum ≤ d.nreg 217090 → d.nreg 217090 < cum + (it.pts n).length →
        Enc d' ztyns) ∧
      FrameB Blook d d' := by
  rw [lookBody_eq]
  -- read the item
  obtain ⟨d1, k1, e1, hk1, a94, a95, a96, f1, m1, -⟩ : ∃ d1 k1, Exec P W lookRd d d1 k1 ∧ k1 ≤ 5 ∧
      d1.nreg 217094 = d.nmem p ∧ d1.nreg 217095 = d.nmem ztr ∧
      d1.nreg 217096 = d.nmem ztcao ∧
      (∀ r, r ≠ 217094 → r ≠ 217095 → r ≠ 217096 → r ≠ 217097 → d1.nreg r = d.nreg r) ∧
      d1.nmem = d.nmem ∧ d1.rreg = d.rreg ∧ d1.rmem = d.rmem ∧ d1.output = d.output := by
    unfold lookRd
    exec_block
    · config_simp; omega
    · config_simp; omega
    simp_all
  zuqj
  -- the item
  obtain ⟨d2, k2, e2, hk2, a93, hkeep, henc, f2⟩ : ∃ d2 k2,
      Exec P W ztjcz d1 d2 k2 ∧ k2 ≤ 16 ∧
      d2.nreg 217093 = cum + (it.pts n).length ∧
      (d.nreg 217090 < cum → d2.nreg 217070 = d.nreg 217070 ∧ d2.nreg 217071 = d.nreg 217071 ∧
        d2.nreg 217072 = d.nreg 217072) ∧
      (cum ≤ d.nreg 217090 → d.nreg 217090 < cum + (it.pts n).length →
        Enc d2 ztyns) ∧ FrameB Bitem d1 d2 := by
    have b20 : d1.nreg 217020 = n := by_simp_all
    have b27 : d1.nreg 217027 = 1 := by
      simp_all
    have b93 : d1.nreg 217093 = cum := by
      simp_all
    have b90 : d1.nreg 217090 = d.nreg 217090 := by_simp_all
    have b70 : d1.nreg 217070 = d.nreg 217070 := by_simp_all
    have b71 : d1.nreg 217071 = d.nreg 217071 := by_simp_all
    have b72 : d1.nreg 217072 = d.nreg 217072 := by_simp_all
    rcases it with ⟨a, ℓ⟩ | ⟨j | ⟨e, h⟩⟩
    · zugqd
      zueaw
      rw [run_pts_length] at hcW ⊢
      obtain ⟨d2, k2, e2, hk2, r93, r1, r2, rf⟩ := lookRun_exec d1 hw1 b20 b27 b93
        by_omega by_omega ha hℓ hnW by_omega
      refine ⟨d2, k2 + 1, .ifLtN_true by_omega e2, by_omega, r93,
        fun h => ?_, fun h h' => ?_, rf⟩
      · omega
      · rw [run_pts_getD n a ℓ by_omega]
        grind
    · obtain ⟨i0, i1⟩ := hit
      obtain ⟨d2, k2, e2, hk2, r93, r1, r2, rf⟩ := lookPt_exec d1 hw1 b27 b93
        by_tauto
      refine ⟨d2, k2 + 2, .ifLtN_false by_omega e2, by_omega,
        by zuowk; rfl, fun h => ?_, fun h h' => ?_, rf⟩
      · omega
      · zueen

        obtain ⟨x, y, -⟩ := r2 by_omega
        zuduf

    · zugqd
      obtain ⟨d2, k2, e2, hk2, r93, r1, r2, rf⟩ := lookPt_exec d1 hw1 b27 b93
        by_tauto
      refine ⟨d2, k2 + 2, .ifLtN_false by_omega e2, by_omega,
        by zuowk; rfl, fun h => ?_, fun h h' => ?_, rf⟩
      · omega
      · zueen

        obtain ⟨x, y, z⟩ := r2 by_omega
        zuduf

  zump
  -- advance
  have c91 : d2.nreg 217091 = d.nreg 217091 := by
    rw [f2.1 _ by_decide, f1 _ by_decide by_decide by_decide by_decide]
  have c92 : d2.nreg 217092 = p := by
    rw [f2.1 _ by_decide, f1 _ by_decide by_decide by_decide by_decide, h92]
  have c27 : d2.nreg 217027 = 1 := by
    rw [f2.1 _ by_decide, f1 _ by_decide by_decide by_decide by_decide, h27]
  obtain ⟨d3, k3, e3, hk3, a91, a92, f3⟩ : ∃ d3 k3, Exec P W lookNx d2 d3 k3 ∧ k3 ≤ 4 ∧
      d3.nreg 217091 = d.nreg 217091 + 1 ∧ d3.nreg 217092 = p + 3 ∧
      (∀ r, r ≠ 217091 → r ≠ 217092 → d3.nreg r = d2.nreg r) := by
    unfold lookNx
    exec_block
    · omega
    · config_simp; omega
    · simp_all
    · simp_all
    simp_all
  have wr3 : wr Blook lookNx = true := by_decide
  have wr1 : wr Blook lookRd = true := by_decide
  have wr2 : wr Blook ztjcz = true := by_decide
  refine ⟨d3, k1 + ztdve, .seq e1 ztbpc, by_omega, a91, a92, ?_, fun h => ?_,
    fun h h' => ?_, (exec_frameB e1 wr1).trans ((exec_frameB e2 wr2).trans (exec_frameB e3 wr3))⟩
  · simp_all
  · simp_all
  · exact (henc h h').congr by_simp_all by_simp_all
      by_simp_all
set_option maxHeartbeats 2000000 in
/-- **`lookS`: host point `k = 217090`** of a well-formed host of at most `64` items. -/
theorem lookS_exec (d : Config) (hw : WordsBounded W d) {n HB : ℕ} {H : Host}
    (hH : HostAt d.nmem HB H) (hwf : HostWF n H) (hlen : H.length ≤ 64)
    (hHB : HB + 3 * H.length + 1 ≤ W) (hpW : 64 * n ≤ W) (hnW : 2 * n ≤ W)
    (h20 : d.nreg 217020 = n) (h27 : d.nreg 217027 = 1) (h34 : d.nreg 217034 = H.length)
    (h35 : d.nreg 217035 = HB + 1) :
    ∃ d' k, Exec P W lookS d d' k ∧ k ≤ 2100 ∧
      (d.nreg 217090 < (H.pts n).length → Enc d' (hpt n H (d.nreg 217090))) ∧
      FrameB Blook d d' := by
  have hptsW :=
    (Host.pts_length_le hwf).trans ztnnl
  -- initialisation
  obtain ⟨d0, k0, e0, hk0, a91, a92, a93, f0⟩ : ∃ d0 k0, Exec P W (block [.constN 217091 0,
      .copyN 217092 217035, .constN 217093 0]) d d0 k0 ∧ k0 ≤ 3 ∧
      d0.nreg 217091 = 0 ∧ d0.nreg 217092 = HB + 1 ∧ d0.nreg 217093 = 0 ∧ FrameB Blook d d0 := by
    obtain ⟨d0, k0, e0, hk0, a91, a92, a93⟩ : ∃ d0 k0, Exec P W (block [.constN 217091 0,
        .copyN 217092 217035, .constN 217093 0]) d d0 k0 ∧ k0 ≤ 3 ∧
        d0.nreg 217091 = 0 ∧ d0.nreg 217092 = HB + 1 ∧ d0.nreg 217093 = 0 := by
      exec_block
      · omega
      · omega
      simp_all
    exact ⟨d0, k0, e0, hk0, a91, a92, a93, exec_frameB e0 by_decide⟩
  -- the loop
  set k := d.nreg 217090 with hkdef
  let Inv : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 217091 = j ∧
    c.nreg 217034 = H.length ∧ c.nreg 217092 = HB + 1 + 3 * j ∧
    c.nreg 217093 = (Host.pts n ztgdy).length ∧
    (k < (Host.pts n ztgdy).length → Enc c (hpt n H k)) ∧ FrameB Blook d c
  have hI0 : Inv 0 d0 := ⟨e0.wb_right, a91, by rw [f0.1 _ by_decide, h34], by rw [a92],
    by tauto, fun h => by_tauto, f0⟩
  obtain ⟨d', k', e', ⟨-, -, -, -, -, henc, f'⟩, hk'⟩ := DrvR.forLoop (P := P) (W := W) (ir := 217091)
    (nr := 217034) (body := lookBody) Inv 30 H.length
    (fun j c hc => ztklj)
    (fun j c hj hc => by
      obtain ⟨hwc, c91, c34, c92, c93, cenc, cf⟩ := hc
      have hlen' : (Host.pts n ztbaec).length ≤ (H.pts n).length := by
        have := List.take_append_drop ztl H
        conv_rhs => rw [← this]
        unfold Host.pts; grind
      rw [pts_take_succ hj, List.length_append] at hlen'
      obtain ⟨c', kb, eb, hkb, b91, b92, b93, bkeep, benc, bf⟩ := lookBody_exec (P := P) c hwc
        (n := n) (p := HB + 1 + 3 * j) (cum := (Host.pts n ztgdy).length)
        (it := H.getD j ztmn) (by rw [cf.1 _ by_decide, h20])
        (by rw [cf.1 _ by_decide, h27]) c92 c93
        (by rw [cf.2.2.1]; exact itemAt_of_hostAt hH hj) (itemWF_of_hostWF hwf hj)
        by_omega by_omega by_omega hnW
      have c90 : c.nreg 217090 = k := cf.1 _ by_decide
      refine ⟨c', kb, eb, ⟨eb.wb_right, by_omega, by rw [bf.1 _ by_decide, c34],
        by omega, by rw [b93, pts_take_succ hj, List.length_append], fun hk => ?_,
        cf.trans bf⟩, hkb⟩
      rw [c90] at bkeep benc
      by_cases hk0 : k < (Host.pts n ztgdy).length
      · obtain ⟨x, y, z⟩ := bkeep hk0
        exact (cenc hk0).congr x y z
      · rw [pts_take_succ hj, List.length_append] at hk
        have := benc by_omega by_omega
        rw [hpt_take
            (by rw [pts_take_succ hj, List.length_append]; omega),
          pts_take_succ hj, List.getD_append_right _ _ _ _ by_omega]
        omega)
    hI0 ztbg
  refine ⟨d', k0 + k', .seq e0 e', by_omega, fun hk => ?_, f'⟩
  simp_all
end look
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE)
@[expose] public section
variable {d d' : Config} {r v : ℕ}
theorem NRegs.same (h : NRegs d d' ztluh) : d'.nreg r = v := by
  rw [h.1, Machine.upd_same]
theorem NRegs.other (h : NRegs d d' ztluh) {r' : ℕ}
    (hr : r' ≠ r) : d'.nreg r' = d.nreg r' := by
  rw [h.1, Machine.upd_other _ _ _ hr]
theorem seqs_one (s : Stmt) : seqs [s] = s := rfl
theorem tS_le {m T : ℕ} (β : Bool) (hT : T ≤ m) : tS m T β ≤ 2 * m := by
  unfold tS; grind
theorem red_red {x M : ℕ} (_hM : 0 < M) (hx : x < 3 * M) :
    (if ztfcf < M then ztfcf
      else ztfcf - M) = x % M := by
  by_cases h1 : x < M
  · rw [ite_eq_left h1, ite_eq_left h1, Nat.mod_eq_of_lt h1]
  · zubmd
    by_cases h2 : x - M < M
    · zucpz
    · rw [ite_eq_right h2, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_sub_mod by_omega,
        Nat.mod_eq_of_lt by_omega]

/-- The registers `clsS` writes. -/
def Bcls (r : ℕ) : Bool :=
  decide ((217061 ≤ r ∧ r ≤ 217067) ∨ r = 217070 ∨ r = 217071 ∨ r = 217072 ∨
    (217090 ≤ r ∧ r ≤ 217097))
theorem Blook_cls {r : ℕ} (h : Bcls r = false) : Blook r = false := by
  simp only [Bcls, Blook, decide_eq_false_iff_not] at h ⊢; omega
section cls
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **`clsS`: the end at walk edge `p = 217060`** of the chord at height `h = 217050`. -/
theorem clsS_exec (d : Config) (hw : WordsBounded W d) {n m T HB h p : ℕ} {β li : Bool}
    {H : Host} (hH : HostAt d.nmem HB H) (hwf : HostWF n H) (hlen : H.length ≤ 64)
    (hHB : HB + 3 * H.length + 1 ≤ W) (hW : 256 * n + 16 ≤ W)
    (hm1 : 1 ≤ m) (hmp : m + 1 = (H.pts n).length) (hT : T ≤ m) (hp : p ≤ 2 * m + 6)
    (h20 : d.nreg 217020 = n) (h21 : d.nreg 217021 = m) (h22 : d.nreg 217022 = 2 * m)
    (h25 : d.nreg 217025 = tS m T β) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h34 : d.nreg 217034 = H.length) (h35 : d.nreg 217035 = HB + 1) (h41 : d.nreg 217041 = 6)
    (h42 : d.nreg 217042 = 2 * m + 6) (h44 : d.nreg 217044 = 2) (h50 : d.nreg 217050 = h)
    (h60 : d.nreg 217060 = p) :
    ∃ d' k, Exec P W clsS d d' k ∧ k ≤ 2200 ∧
      d'.nreg 217064 = (if RegIn n H li m T β h p then 1 else 0) ∧
      Enc d' ztddc ∧ FrameB Bcls d d' := by
  have hptsW : (H.pts n).length ≤ 64 * n :=
    (Host.pts_length_le hwf).trans ztnnl
  have hmW : 4 * m + 6 ≤ W := by_omega
  have htS := tS_le β hT
  -- `u := tS + (p - 6)`
  obtain ⟨d1, k1, e1, hk1, n1⟩ : ∃ d1 k1, Exec P W (block [.subN 217061 217060 217041,
      .addN 217061 217025 217061]) d d1 k1 ∧ k1 ≤ 2 ∧
      NRegs d d1 (upd d.nreg 217061 ztkxt) := by
    exec_block
    · config_simp; omega
    · refine ztcbo
      simp_all
  zuqj
  have f1 : FrameB Bcls d d1 := exec_frameB e1 by_decide
  -- reduce twice
  obtain ⟨d2, k2, e2, hk2, n2⟩ := x_ifR (P := P) (W := W) (a := 217061) (b := 217022)
    (r := 217061) (t := .skip) (e := block [.subN 217061 217061 217022]) (d := d1) (K := 1)
    (fun _ => x_skipR d1 hw1 217061) (fun _ => x_sub d1 hw1 217061 217061 217022)
  zump
  have f2 := f1.trans (exec_frameB e2 by_decide)
  obtain ⟨d3, k3, e3, hk3, n3⟩ := x_ifR (P := P) (W := W) (a := 217061) (b := 217022)
    (r := 217061) (t := .skip) (e := block [.subN 217061 217061 217022]) (d := d2) (K := 1)
    (fun _ => x_skipR d2 hw2 217061) (fun _ => x_sub d2 hw2 217061 217061 217022)
  zubgh
  have f3 := f2.trans (exec_frameB e3 by_decide)
  have g22 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217022 = 2 * m := fun hc =>
    (hc.1 _ by_decide).trans h22
  have v3 : d3.nreg 217061 = tU m T β p := by
    rw [n3.same, n2.same, n2.other by_decide, n1.same, g22 f1]
    exact red_red by_omega by_omega
  -- side bit
  obtain ⟨d4, k4, e4, hk4, n4⟩ := x_ifR (P := P) (W := W) (a := 217061) (b := 217021)
    (r := 217063) (t := block [.constN 217063 1]) (e := block [.constN 217063 0]) (d := d3)
    (K := 1) (fun _ => x_const d3 hw3 217063 1 by_omega)
    (fun _ => x_const d3 hw3 217063 0 by_omega)
  zubgi
  have f4 := f3.trans (exec_frameB e4 by_decide)
  have g21 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217021 = m := fun hc =>
    (hc.1 _ by_decide).trans h21
  have v4 : d4.nreg 217063 = if tU m T β p < m then 1 else 0 := by
    rw [n4.same, v3, g21 f3]
  -- `kc := sideE m u`
  obtain ⟨d5, k5, e5, hk5, n5⟩ := x_ifR (P := P) (W := W) (a := 217021) (b := 217061)
    (r := 217062) (t := block [.subN 217062 217022 217061]) (e := block [.copyN 217062 217061])
    (d := d4) (K := 1) (fun _ => x_sub d4 hw4 217062 217022 217061)
    (fun _ => x_copy d4 hw4 217062 217061)
  zudpn
  have f5 := f4.trans (exec_frameB e5 by_decide)
  have u4 : d4.nreg 217061 = tU m T β p := by rw [n4.other by_decide, v3]
  have v5 : d5.nreg 217062 = tK m T β p := by
    rw [n5.same, u4, g21 f4, g22 f4]
    unfold tK Chazelle.Chain.sideE
    grind
  -- lookup
  obtain ⟨d6, k6, e6, hk6, n6⟩ := x_copy (P := P) d5 hw5 217090 217062
  zueso
  have f6 := f5.trans (exec_frameB e6 by_decide)
  have m6 := f6.2.2.1
  obtain ⟨d7, k7, e7, hk7, enc7, f7'⟩ := lookS_exec (P := P) d6 hw6 by_grind hwf hlen
    hHB by_omega by_omega ((f6.1 _ by_decide).trans h20)
    ((f6.1 _ by_decide).trans h27) ((f6.1 _ by_decide).trans h34)
    ((f6.1 _ by_decide).trans h35)
  zuizn
  have f7 := f6.trans ⟨fun r hr => f7'.1 r ztuwv,
    fun r hr => f7'.2.1 r ztuwv, f7'.2.2⟩
  have v6 : d6.nreg 217090 = tK m T β p := by rw [n6.same, v5]
  rw [v6] at enc7
  have enc7' := enc7 (by have := tK_le (T := T) β hm1 p; omega)
  -- height vertex
  obtain ⟨d8, k8, e8, hk8, n8⟩ := x_ifR (P := P) (W := W) (a := 217070) (b := 217044)
    (r := 217066) (t := block [.copyN 217066 217071]) (e := block [.copyN 217066 217072]) (d := d7)
    (K := 1) (fun _ => x_copy d7 hw7 217066 217071) (fun _ => x_copy d7 hw7 217066 217072)
  zuizo
  have f8 := f7.trans (exec_frameB e8 by_decide)
  have v8 : d8.nreg 217066 = hidx ztddc := by
    rw [n8.same, (f7.1 _ by_decide).trans h44]
    revert enc7'
    cases hpt n H _ with
    | vtx j => intro he; simp only [Enc] at he; rw [he.1, he.2, ite_eq_left by_omega]; rfl
    | onEdge e h' => intro he; simp only [Enc] at he; rw [he.1, he.2.2, ite_eq_right by_omega]; rfl
  -- `t0 := [h = hid]`
  obtain ⟨d9, k9, e9, hk9, n9⟩ := x_ifR (P := P) (W := W) (a := 217050) (b := 217066)
    (r := 217065) (t := block [.constN 217065 0])
    (e := .ifLtN 217066 217050 ztiht ztoye) (d := d8)
    (K := 3) (fun _ => x_mono (x_const d8 hw8 217065 0 by_omega) by_omega)
    (fun _ => x_ifR (fun _ => x_const d8 hw8 217065 0 by_omega)
      (fun _ => x_const d8 hw8 217065 1 by_omega))
  have hw9 := e9.wb_right
  have f9 := f8.trans (exec_frameB e9 by_decide)
  have v9 : d9.nreg 217065 =
      if tZ n H m T β h p then 1 else 0 := by
    rw [n9.same, v8, (f8.1 _ by_decide).trans h50]
    unfold tZ
    grind
  -- the regular-inner bit
  obtain ⟨d10, k10, e10, hk10, n10⟩ := x_const (P := P) d9 hw9 217064 1 by_omega
  have hw10 := e10.wb_right
  obtain ⟨d11, k11, e11, hk11, n11⟩ := x_ifR (P := P) (W := W) (a := 217060) (b := 217041)
    (r := 217064) (t := block [.constN 217064 0]) (e := .skip) (d := d10) (K := 1)
    (fun _ => x_const d10 hw10 217064 0 by_omega) (fun _ => x_skipR d10 hw10 217064)
  have hw11 := e11.wb_right
  obtain ⟨d12, k12, e12, hk12, n12⟩ := x_ifR (P := P) (W := W) (a := 217042) (b := 217060)
    (r := 217064) (t := block [.constN 217064 0]) (e := .skip) (d := d11) (K := 1)
    (fun _ => x_const d11 hw11 217064 0 by_omega) (fun _ => x_skipR d11 hw11 217064)
  have hw12 := e12.wb_right
  obtain ⟨d13, k13, e13, hk13, n13⟩ := x_ifR (P := P) (W := W) (a := 217060) (b := 217042)
    (r := 217064) (t := .skip)
    (e := .ifLtN 217042 217060 .skip
      ztyzw) (d := d12) (K := 5)
    ztjvh
    (fun _ => x_ifR ztjvh
      (fun _ => x_ifR (fun _ => x_const d12 hw12 217064 0 by_omega)
        (fun _ => x_skipR d12 hw12 217064)))
  have hw13 := e13.wb_right
  obtain ⟨d14, k14, e14, hk14, n14⟩ := x_ifR (P := P) (W := W) (a := 217065) (b := 217027)
    (r := 217064) (t := .skip)
    (e := .ifLtN 217062 217027 ztbfx
      ztxtz)
    (d := d13) (K := 7)
    ztjvi
    (fun _ => x_ifR (fun _ => x_mono (x_const d13 hw13 217064 0 by_omega) by_omega)
      (fun _ => x_ifR ztjvi
        (fun _ => x_ifR (fun _ => x_skipR d13 hw13 217064)
          (fun _ => x_const d13 hw13 217064 0 by_omega))))
  have hw14 := e14.wb_right
  obtain ⟨d15, k15, e15, hk15, n15⟩ := x_ifR (P := P) (W := W) (a := 217063) (b := 217026)
    (r := 217064) (t := block [.constN 217064 0])
    (e := .ifLtN 217026 217063 ztbfx .skip) (d := d14) (K := 3)
    (fun _ => x_mono (x_const d14 hw14 217064 0 by_omega) by_omega)
    (fun _ => x_ifR (fun _ => x_const d14 hw14 217064 0 by_omega)
      (fun _ => x_skipR d14 hw14 217064))
  -- frames of the last steps
  have f10 := f9.trans (exec_frameB e10 by_decide)
  have f11 := f10.trans (exec_frameB e11 by_decide)
  have f12 := f11.trans (exec_frameB e12 by_decide)
  have f13 := f12.trans (exec_frameB e13 by_decide)
  have f14 := f13.trans (exec_frameB e14 by_decide)
  have f15 := f14.trans (exec_frameB e15 by_decide)
  -- the inputs of the bit
  have q60 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217060 = p := fun hc =>
    (hc.1 _ by_decide).trans h60
  have q41 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217041 = 6 := fun hc =>
    (hc.1 _ by_decide).trans h41
  have q42 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217042 = 2 * m + 6 := fun hc =>
    (hc.1 _ by_decide).trans h42
  have q27 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217027 = 1 := fun hc =>
    (hc.1 _ by_decide).trans h27
  have q26 : ∀ {c : Config}, FrameB Bcls d c → c.nreg 217026 = liV li := fun hc =>
    (hc.1 _ by_decide).trans h26
  obtain ⟨zb, hzb⟩ : ∃ zb : ℕ, zb = if tZ n H m T β h p then 1 else 0 := by_grind
  have hz1 : zb ≤ 1 := by rw [hzb]; split_ifs <;> omega
  have hzt : tZ n H m T β h p ↔ zb = 1 := by
    grind
  have t65 : d12.nreg 217065 = zb := by
    rw [n12.other by_decide, n11.other by_decide, n10.other by_decide, v9, hzb]
  have t65' : d13.nreg 217065 = zb := by
    rw [n13.other by_decide, t65]
  have t62 : d13.nreg 217062 = tK m T β p := by
    rw [n13.other by_decide, n12.other by_decide, n11.other by_decide,
      n10.other by_decide, n9.other by_decide, n8.other by_decide,
      f7'.1 _ by_decide, n6.other by_decide, v5]
  have t63 : d14.nreg 217063 = if tU m T β p < m then 1 else 0 := by
    rw [n14.other by_decide, n13.other by_decide, n12.other by_decide,
      n11.other by_decide, n10.other by_decide, n9.other by_decide, n8.other by_decide,
      f7'.1 _ by_decide, n6.other by_decide, n5.other by_decide, v4]
  have w11 : d11.nreg 217064 = if 6 ≤ p then 1 else 0 := by
    rw [n11.same, q60 f10, q41 f10, n10.same]
    grind
  have w12 : d12.nreg 217064 = if 6 ≤ p then 1 else 0 := by
    rw [n12.same, q60 f11, q42 f11, w11, ite_eq_right by_grind]
  have w13 : d13.nreg 217064 = if 6 ≤ p ∧ ztcwe then 1 else 0 := by
    rw [n13.same, q60 f12, q42 f12, w12, t65, q27 f12]
    zuwd
  have w14 : d14.nreg 217064 =
      if 6 ≤ p ∧ ztcwe ∧
        ¬ ztxyk then 1 else 0 := by
    rw [n14.same, t65', q27 f13, t62, (f13.1 _ by_decide).trans h21, w13]
    zuwd
  have w15' : d15.nreg 217064 =
      if (6 ≤ p ∧ ztcwe ∧
        ¬ ztxyk) ∧
          (tU m T β p < m ↔ liV li = 1) then 1 else 0 := by
    rw [n15.same, t63, q26 f14, w14]
    have := liV_le li
    zuwd
  have hreg : ((6 ≤ p ∧ ztcwe ∧
      ¬ ztxyk) ∧ (tU m T β p < m ↔ liV li = 1)) ↔
        RegIn n H li m T β h p := by
    unfold RegIn
    have hl : liV li = 1 ↔ li = true := by cases li <;> simp [liV]
    rw [hl, ← hzt]
    constructor
    · rintro ⟨⟨h6, hlast, hirr⟩, hside⟩; exact ⟨h6, hp, hlast, hirr, hside⟩
    · rintro ⟨h6, -, hlast, hirr, hside⟩; exact ⟨by_grind, hside⟩
  have w15 : d15.nreg 217064 = if RegIn n H li m T β h p then 1 else 0 := by
    rw [w15']; exact if_congr hreg rfl rfl
  simp only [clsS, seqs_cons₂, seqs_one]
  refine ⟨d15, _, .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 (.seq e9
      (.seq e10 (.seq e11 (.seq e12 (.seq e13 (.seq e14 e15))))))))))))), by_omega, w15, ?_, f15⟩
  · have k70 : d15.nreg 217070 = d7.nreg 217070 := by
      rw [n15.other by_decide, n14.other by_decide, n13.other by_decide,
        n12.other by_decide, n11.other by_decide, n10.other by_decide,
        n9.other by_decide, n8.other by_decide]
    have k71 : d15.nreg 217071 = d7.nreg 217071 := by
      rw [n15.other by_decide, n14.other by_decide, n13.other by_decide,
        n12.other by_decide, n11.other by_decide, n10.other by_decide,
        n9.other by_decide, n8.other by_decide]
    have k72 : d15.nreg 217072 = d7.nreg 217072 := by
      rw [n15.other by_decide, n14.other by_decide, n13.other by_decide,
        n12.other by_decide, n11.other by_decide, n10.other by_decide,
        n9.other by_decide, n8.other by_decide]
    exact enc7'.congr k70 k71 k72
end cls

/-! ## The interior edge of a host point -/

/-- The registers `peS` writes. -/
def Bpe (r : ℕ) : Bool := decide (217100 ≤ r ∧ r ≤ 217104)
theorem wr_pe : wr Bpe peS = true := by_decide
section pe
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
/-- **`peS`**: `217100 := pEdge li n s` for the encoded host point `s`. -/
theorem peS_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {li : Bool} {s : SymPt}
    (hs : s.Lt n) (henc : Enc d s) (hnW : n ≤ W)
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h44 : d.nreg 217044 = 2) :
    ∃ d' k, Exec P W peS d d' k ∧ k ≤ 40 ∧ d'.nreg 217100 = pEdge li n s ∧ FrameB Bpe d d' := by
  obtain ⟨d', k, ex, hk, hv⟩ : ∃ d' k, Exec P W peS d d' k ∧ k ≤ 40 ∧
      d'.nreg 217100 = pEdge li n s := by
    unfold peS
    cases s with
    | vtx j =>
      zuenl

      zudd
      obtain ⟨d1, k1, e1, hk1, n1, -⟩ := ivBS_exec d hw (src := 217071) (dst := 217100)
        h20 h26 h27 by_decide by_decide by_decide
      exact ⟨d1, k1, e1, by_omega, by rw [n1, Machine.upd_same, henc.2]; rfl⟩
    | onEdge e h =>
      zuenl

      zubv
      obtain ⟨d1, k1, e1, hk1, a1, o1, -, m1, -⟩ := qES_exec d hw (src := 217071)
        (dst := 217101) h20 h26 h27 by_omega hnW by_decide by_decide
        by_decide by_decide by_decide
      have hq : DrvR.qE li n e < n := DownMath.qE_lt li hs.1
      rw [henc.2.1] at a1
      obtain ⟨d2, k2, e2, hk2, n2, -⟩ := succS_exec d1 e1.wb_right (src := 217101)
        (dst := 217102) by_simp_all
        by_simp_all by_omega hnW by_decide
      have b2 : d2.nreg 217102 = ztigz % n := by_simp_all
      have o2 : ∀ r, r ≠ 217102 → d2.nreg r = d1.nreg r := by_simp_all
      obtain ⟨d3, k3, e3, hk3, n3, -⟩ := ivBS_exec (P := P) d2 e2.wb_right (src := 217102)
        (dst := 217103) (n := n) (li := li)
        by_simp_all
        by_simp_all
        by_simp_all
        by_decide by_decide by_decide
      have b3 : d3.nreg 217103 = DrvR.ivB li n (ztigz % n) := by
        simp_all
      have o3 : ∀ r, r ≠ 217103 → d3.nreg r = d2.nreg r := by_simp_all
      have b72 : d3.nreg 217072 = h := by
        simp_all
      have b101 : d3.nreg 217101 = DrvR.qE li n e := by
        simp_all
      have b102 : d3.nreg 217102 = ztigz % n := by_simp_all
      zubgh
      obtain ⟨d4, k4, e4, hk4, n4⟩ := x_ifR (fun _ => x_mono (x_copy d3 hw3 217100 217101) by_omega)
        (fun _ => x_ifR (fun _ => x_copy d3 hw3 217100 217101)
          (fun _ => x_copy d3 hw3 217100 217102))
      refine ⟨d4, k1 + ztbqj, .seq e1 ztbal, by_omega, ?_⟩
      rw [n4.same, b72, b3, b101, b102]
      zufbv
      zuwd
  exact ⟨d', k, ex, hk, hv, exec_frameB ex wr_pe⟩
end pe
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE)
@[expose] public section
theorem hltF_le (P : Polygon) (u v : ℕ) : hltF P u v ≤ 1 := by
  unfold hltF; grind
theorem hltF_eq_one {P : Polygon} (hG : GoodEnv P) {u v : ℕ} (hu : u < (Qof P).n)
    (hv : v < (Qof P).n) : hltF P u v = 1 ↔ ((Qof P).vtx u).2 < ((Qof P).vtx v).2 := by
  rw [hlt_iff hG hu hv]; unfold hltF; simp
open Classical in
/-- **`posLtS` decides the key order** of two positions at vertex heights. -/
theorem posLtF_iff {P : Polygon} (hG : GoodEnv P) (li : Bool) {x y : WPos}
    (hx : x.edge < (Qof P).n) (hx1 : 1 ≤ x.hgt) (hxn : x.hgt ≤ (Qof P).n) (hy1 : 1 ≤ y.hgt)
    (hyn : y.hgt ≤ (Qof P).n) :
    posLtF P li (Qof P).n x.edge x.hgt y.edge y.hgt = if PosLt zta li x y then 1 else 0 := by
  zukdy
  have h1 := hltF_eq_one hG (DownMath.ivB_lt li hx) (DownMath.ivB_lt li ztzum)
  have h2 := hltF_eq_one hG (u := x.hgt - 1) (v := y.hgt - 1) by_omega by_omega
  have b1 := hltF_le P ztmlw ztxii
  have b2 := hltF_le P ztzs zthli
  have hiff : (EdgeUp zta li x.edge ↔
      ((Qof P).vtx ztzs).2 < ((Qof P).vtx zthli).2) ↔
      hltF P ztmlw ztxii =
        hltF P ztzs zthli := by
    unfold EdgeUp; grind
  unfold posLtF PosLt
  grind
section pieces
variable {P : Polygon} {W : ℕ}
variable (d : Config)
set_option maxHeartbeats 1000000 in
/-- `dst := [a = b ∧ c = e]`. -/
theorem eq2S_exec (hw : WordsBounded W d) {a b c e dst : ℕ} (ha : a ≠ dst)
    (hb : b ≠ dst) (hc : c ≠ dst) (he : e ≠ dst) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W (eq2S a b c e dst) d d' k ∧ k ≤ 10 ∧
      NRegs d d' (upd d.nreg dst
        (if d.nreg a = d.nreg b ∧ d.nreg c = d.nreg e then 1 else 0)) := by
  unfold eq2S
  refine x_mono (x_seq (K₂ := 9) (x_const d hw dst 0 by_omega) ztpbk) by_omega
  obtain ⟨d2, k2, e2, hk2, n2⟩ := x_ifR (P := P) (W := W) (r := dst) (d := d1) (K := 7)
    ztesd
    (fun _ => x_ifR ztesd
      (fun _ => x_ifR ztesd
        (fun _ => x_ifR (fun _ => x_skipR d1 hw1 dst)
          (fun _ => x_const d1 hw1 dst 1 by_omega))))
  refine ztlvr
  refine ⟨?_, n2.2.1.trans n1.2.1, n2.2.2.1.trans n1.2.2.1, n2.2.2.2.1.trans n1.2.2.2.1,
    n2.2.2.2.2.trans n1.2.2.2.2⟩
  zuils
  simp only [Machine.upd_other _ _ _ ha, Machine.upd_other _ _ _ hb, Machine.upd_other _ _ _ hc,
    Machine.upd_other _ _ _ he, Machine.upd_same]
  grind
set_option maxHeartbeats 2000000 in
/-- `dst := posLt (a, b) (c, e)`. -/
theorem posLtOn_exec (hw : WordsBounded W d) {a b c e dst n : ℕ} {li : Bool}
    (h20 : d.nreg 217020 = n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (hae : d.nreg a < n) (hnW : n ≤ W) (hW : 1 ≤ W) (_ha : a < 217150) (hb : b < 217150)
    (hc : c < 217150) (he : e < 217150) :
    ∃ d' k, Exec P W (posLtOn a b c e dst) d d' k ∧ k ≤ 60 ∧
      d'.nreg dst = posLtF P li n ztvor (d.nreg b) (d.nreg c) (d.nreg e) := by
  unfold posLtOn
  obtain ⟨d1, k1, e1, hk1, a50, a51, a52, a53, g1⟩ : ∃ d1 k1, Exec P W (block [.copyN 217150 a,
      .copyN 217151 b, .copyN 217152 c, .copyN 217153 e]) d d1 k1 ∧ k1 ≤ 4 ∧
      d1.nreg 217150 = d.nreg a ∧ d1.nreg 217151 = d.nreg b ∧ d1.nreg 217152 = d.nreg c ∧
      d1.nreg 217153 = d.nreg e ∧ (∀ r, r < 217150 → d1.nreg r = d.nreg r) := by
    exec_block
    refine ⟨by_omega, ?_, ?_, ?_, ?_, fun r hr => ?_⟩ <;> config_simp
    · rw [Machine.upd_other _ _ _ (show b ≠ 217150 by omega)]
    · rw [Machine.upd_other _ _ _ (show c ≠ 217151 by omega),
        Machine.upd_other _ _ _ (show c ≠ 217150 by omega)]
    · rw [Machine.upd_other _ _ _ (show e ≠ 217152 by omega),
        Machine.upd_other _ _ _ (show e ≠ 217151 by omega),
        Machine.upd_other _ _ _ (show e ≠ 217150 by omega)]
    · rw [Machine.upd_other _ _ _ (show r ≠ 217153 by omega),
        Machine.upd_other _ _ _ (show r ≠ 217152 by omega),
        Machine.upd_other _ _ _ (show r ≠ 217151 by omega),
        Machine.upd_other _ _ _ (show r ≠ 217150 by omega)]
  obtain ⟨d2, k2, e2, hk2, v2, -⟩ := posLtS_exec (P := P) d1 e1.wb_right
    by_simp_all (by rw [g1 _ by_omega, h26]) by_simp_all
    by_omega hnW hW
  obtain ⟨d3, k3, e3, hk3, n3⟩ := x_copy (P := P) d2 e2.wb_right dst 217154
  refine ⟨d3, k1 + ztdve, .seq e1 ztbpc, by_omega, ?_⟩
  rw [n3.same, v2, a50, a51, a52, a53]
set_option maxHeartbeats 2000000 in
/-- The arc test `onS` on bits. -/
theorem onS_exec (hw : WordsBounded W d) (hW : 1 ≤ W) (h27 : d.nreg 217027 = 1) :
    ∃ d' k, Exec P W onS d d' k ∧ k ≤ 16 ∧
      NRegs d d' (upd d.nreg 217127 (if d.nreg 217122 < 1 then (if d.nreg 217123 < 1 then
        (if d.nreg 217124 < 1 then (if d.nreg 217125 < 1 then (if d.nreg 217126 < 1 then 0 else 1)
          else 1) else (if d.nreg 217125 < 1 then 0 else (if d.nreg 217126 < 1 then 0 else 1)))
        else 1) else 1)) := by
  unfold onS
  refine x_mono (x_seq (K₂ := 15) (x_const d hw 217127 0 by_omega) ztpbk)
    by_omega
  have s0 := fun (K : ℕ) (hK : 1 ≤ K) => x_mono (P := P) (x_skipR d1 hw1 217127) hK
  have s1 := fun (K : ℕ) (hK : 1 ≤ K) => x_mono (P := P) (x_const d1 hw1 217127 1 by_omega) hK
  obtain ⟨d2, k2, e2, hk2, n2⟩ := x_ifR (P := P) (W := W) (r := 217127) (d := d1) (K := 13)
    (fun _ => x_ifR (fun _ => x_ifR
        (fun _ => x_ifR ztfhh
          (fun _ => s1 7 by_omega))
        (fun _ => x_ifR (fun _ => s0 7 by_omega)
          ztfhh))
      (fun _ => s1 11 by_omega))
    (fun _ => s1 13 by_omega)
  refine ztlvr
  refine ⟨?_, n2.2.1.trans n1.2.1, n2.2.2.1.trans n1.2.2.1, n2.2.2.2.1.trans n1.2.2.2.1,
    n2.2.2.2.2.trans n1.2.2.2.2⟩
  zuils
  config_simp
  grind

/-- The registers `bktFS` writes. -/
def BbktF (r : ℕ) : Bool := decide (r = 217112 ∨ r = 217128)
theorem wr_bktF : wr BbktF bktFS = true := by_decide
set_option maxHeartbeats 2000000 in
/-- **The bucket formula.** -/
theorem bktFS_exec (hw : WordsBounded W d) {A j : ℕ} (hj : j < A)
    (hAW : 2 * A + 2 ≤ W) (h27 : d.nreg 217027 = 1) (h30 : d.nreg 217030 = A)
    (h44 : d.nreg 217044 = 2) (h16 : d.nreg 217116 = j) :
    ∃ d' k, Exec P W bktFS d d' k ∧ k ≤ 12 ∧
      d'.nreg 217112 = (if d.nreg 217122 < 1 then (if d.nreg 217123 < 1 then
        ztilb else 2 * ztxek + 1) else 2 * j + 1) ∧
      FrameB BbktF d d' := by
  obtain ⟨d', k, ex, hk, hv⟩ : ∃ d' k, Exec P W bktFS d d' k ∧ k ≤ 12 ∧
      d'.nreg 217112 = (if d.nreg 217122 < 1 then (if d.nreg 217123 < 1 then
        ztilb else 2 * ztxek + 1)
          else 2 * j + 1) := by
    unfold bktFS
    by_cases c1 : d.nreg 217122 < 1
    · zudd
      by_cases c2 : d.nreg 217123 < 1
      · zudd
        by_cases c3 : d.nreg 217125 < 1
        · zudd
          exec_block
          · omega
          simp_all
        · zubv
          exec_block
          · omega
          · config_simp; omega
          · refine zteh; config_simp; grind
      · zubv
        refine spec_seq ?_
        exec_block
        · omega
        by_cases c4 : j + 1 < A
        · zuek
          exec_block
          · config_simp; omega
          · config_simp; omega
          · refine zteh; config_simp
            rw [ite_eq_left c1, ite_eq_right c2, Nat.mod_eq_of_lt c4]; omega
        · zudx
          exec_block
          · omega
          · refine zteh; config_simp
            have h0 : ztl % A = 0 := by rw [show j + 1 = A by omega, Nat.mod_self]
            simp_all
    · zubv
      exec_block
      · omega
      · config_simp; omega
      · refine zteh; config_simp; grind
  exact ⟨d', k, ex, hk, hv, exec_frameB ex wr_bktF⟩

/-- The registers `arcRdS` writes. -/
def Brd (r : ℕ) : Bool := decide ((217116 ≤ r ∧ r ≤ 217121) ∨ r = 217128)
theorem wr_arcRd : wr Brd arcRdS = true := by_decide
set_option maxHeartbeats 2000000 in
/-- **Read arc `j`** (the region list entry at `217114`). -/
theorem arcRd_exec (hw : WordsBounded W d) {AB j se sh ee eh : ℕ}
    (h14 : d.nmem ztvol = j) (h27 : d.nreg 217027 = 1) (h31 : d.nreg 217031 = AB)
    (hAW : AB + 5 * j + 4 ≤ W) (m1 : d.nmem ztbph = se)
    (m2 : d.nmem ztbpi = sh) (m3 : d.nmem ztbyb = ee)
    (m4 : d.nmem ztbyc = eh) :
    ∃ d' k, Exec P W arcRdS d d' k ∧ k ≤ 13 ∧ d'.nreg 217116 = j ∧ d'.nreg 217118 = se ∧
      d'.nreg 217119 = sh ∧ d'.nreg 217120 = ee ∧ d'.nreg 217121 = eh ∧ FrameB Brd d d' := by
  have k1 : ∀ a, a = AB + 5 * j + 1 → d.nmem a = se := fun a ha => ha ▸ m1
  have k2 : ∀ a, a = AB + 5 * j + 2 → d.nmem a = sh := fun a ha => ha ▸ m2
  have k3 : ∀ a, a = AB + 5 * j + 3 → d.nmem a = ee := fun a ha => ha ▸ m3
  have k4 : ∀ a, a = AB + 5 * j + 4 → d.nmem a = eh := fun a ha => ha ▸ m4
  obtain ⟨d', k, ex, hk, v16, v18, v19, v20, v21⟩ : ∃ d' k, Exec P W arcRdS d d' k ∧ k ≤ 13 ∧
      d'.nreg 217116 = j ∧ d'.nreg 217118 = se ∧ d'.nreg 217119 = sh ∧ d'.nreg 217120 = ee ∧
      d'.nreg 217121 = eh := by
    unfold arcRdS
    exec_block
    all_goals (try (config_simp; zunvi; omega))
    refine ztbfj <;> config_simp <;> zunvi
    · grind
    · grind
    · grind
    grind
  exact ⟨d', k, ex, hk, v16, v18, v19, v20, v21, exec_frameB ex wr_arcRd⟩
end pieces
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (ivB qE)
@[expose] public section
def Bbkt (r : ℕ) : Bool :=
  decide ((217112 ≤ r ∧ r ≤ 217128) ∨ ztgyq ∨ ztgyr)
theorem wr_bktBody : wr Bbkt bktBody = true := by_decide

/-- The registers `posLtOn … dst` writes. -/
def Bon (dst r : ℕ) : Bool :=
  decide (ztgyq ∨ ztgyr ∨ r = dst)
open Classical in
theorem onArc_bits (Q : Polygon) (li : Bool) (N : NF) (j : ℕ) (x : WPos) :
    (if (if PosEq x (N.arc j).s then 1 else 0) < 1 then
      (if (if PosEq x (N.arc j).e then 1 else 0) < 1 then
        (if (if PosLt Q li (N.arc j).s (N.arc j).e then 1 else 0) < 1 then
          (if zthye < 1 then
            ztetm else 1)
        else (if zthye < 1 then 0 else
          ztetm))
      else 1) else 1 : ℕ) = if OnArcP Q li N j x then 1 else 0 := by
  unfold OnArcP
  grind
open Classical in
theorem bktF_bits (A j : ℕ) (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :
    (if (if a then 1 else 0) < 1 then (if (if b then 1 else 0) < 1 then
        (if (if c then 1 else 0) < 1 then 0 else 2 * j + 2) else 2 * ztxek + 1)
      else 2 * j + 1 : ℕ) = bktF A j a b c := by
  unfold bktF
  simp
section body
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 8000000 in
open Classical in
/-- **One arc of the bucket loop.** -/
theorem bktBody_exec (d : Config) (hw : WordsBounded W d) (hG : GoodEnv P) {li : Bool} {N : NF}
    {x : WPos} {AB j : ℕ} (hj : j < N.arcs.length) (hx : GoodPos zta x)
    (hs : GoodPos zta (N.arc j).s) (he : GoodPos zta (N.arc j).e)
    (h14 : d.nmem ztvol = j)
    (m1 : d.nmem ztbph = (N.arc j).s.edge) (m2 : d.nmem ztbpi = (N.arc j).s.hgt)
    (m3 : d.nmem ztbyb = (N.arc j).e.edge) (m4 : d.nmem ztbyc = (N.arc j).e.hgt)
    (hAW : AB + 5 * j + 4 ≤ W) (h2A : 2 * N.arcs.length + 2 ≤ W) (hnW : (Qof P).n ≤ W)
    (h13W : d.nreg 217113 + 1 ≤ W) (h14W : d.nreg 217114 + 1 ≤ W)
    (h20 : d.nreg 217020 = (Qof P).n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h30 : d.nreg 217030 = N.arcs.length) (h31 : d.nreg 217031 = AB) (h44 : d.nreg 217044 = 2)
    (h10 : d.nreg 217110 = x.edge) (h11 : d.nreg 217111 = x.hgt) :
    ∃ d' k, Exec P W bktBody d d' k ∧ k ≤ 300 ∧
      d'.nreg 217113 = d.nreg 217113 + 1 ∧ d'.nreg 217114 = d.nreg 217114 + 1 ∧
      d'.nreg 217115 = (if d.nreg 217115 < 1 ∧ OnArcP zta li N j x then 1 else d.nreg 217115) ∧
      d'.nreg 217112 = (if d.nreg 217115 < 1 ∧ OnArcP zta li N j x then
        bktF N.arcs.length j zthca zthbz
          ztydy else d.nreg 217112) ∧
      FrameB Bbkt d d' := by
  zudk
  have hn : 1 ≤ (Qof P).n := by have := hx.2.2; omega
  -- read the arc
  obtain ⟨d1, k1, e1, hk1, a16, a18, a19, a20, a21, f1⟩ := arcRd_exec (P := P) d hw h14 h27 h31 hAW
    m1 m2 m3 m4
  zuqj
  zumas
  -- `eqS`, `eqE`
  obtain ⟨d2, k2, e2, hk2, n2⟩ := eq2S_exec (P := P) d1 hw1 (a := 217110) (b := 217118)
    (c := 217111) (e := 217119) (dst := 217122) by_decide by_decide by_decide by_decide hW1
  zump
  obtain ⟨d3, k3, e3, hk3, n3⟩ := eq2S_exec (P := P) d2 hw2 (a := 217110) (b := 217120)
    (c := 217111) (e := 217121) (dst := 217123) by_decide by_decide by_decide by_decide hW1
  zubgh
  -- values in `d3`
  have c10 : d3.nreg 217110 = x.edge := by
    rw [n3.other by_decide, n2.other by_decide, g1 _ by_decide, h10]
  have c11 : d3.nreg 217111 = x.hgt := by
    rw [n3.other by_decide, n2.other by_decide, g1 _ by_decide, h11]
  have c18 : d3.nreg 217118 = (N.arc j).s.edge := by
    rw [n3.other by_decide, n2.other by_decide, a18]
  have c19 : d3.nreg 217119 = (N.arc j).s.hgt := by
    rw [n3.other by_decide, n2.other by_decide, a19]
  have c20 : d3.nreg 217120 = (N.arc j).e.edge := by
    rw [n3.other by_decide, n2.other by_decide, a20]
  have c21 : d3.nreg 217121 = (N.arc j).e.hgt := by
    rw [n3.other by_decide, n2.other by_decide, a21]
  have q3 : ∀ r, Bbkt r = false → d3.nreg r = d.nreg r := fun r hr => by
    rw [n3.other ztecc,
      n2.other ztecc,
      g1 r (by simp only [Bbkt, Brd, decide_eq_false_iff_not] at hr ⊢; omega)]
  have b22 : d3.nreg 217122 = if PosEq x (N.arc j).s then 1 else 0 := by
    rw [n3.other by_decide, n2.same, g1 217110 by_decide, g1 217111 by_decide, h10, h11, a18,
      a19]
    rfl
  have b23 : d3.nreg 217123 = if PosEq x (N.arc j).e then 1 else 0 := by
    rw [n3.same, n2.other by_decide, n2.other by_decide, n2.other by_decide,
      n2.other by_decide, g1 217110 by_decide, g1 217111 by_decide, h10, h11, a20, a21]
    rfl
  -- the three comparisons
  have hsx := posLtF_iff hG li hs.2.2 hs.2.1 hs.1.2.2 hx.2.1 hx.1.2.2
  have hse := posLtF_iff hG li hs.2.2 hs.2.1 hs.1.2.2 he.2.1 he.1.2.2
  have hxe := posLtF_iff hG li hx.2.2 hx.2.1 hx.1.2.2 he.2.1 he.1.2.2
  obtain ⟨d4, k4, e4, hk4, v4⟩ := posLtOn_exec (P := P) d3 hw3 (a := 217118) (b := 217119)
    (c := 217120) (e := 217121) (dst := 217124) (n := (Qof P).n) (li := li)
    (by rw [q3 _ by_decide, h20]) (by rw [q3 _ by_decide, h26]) (by rw [q3 _ by_decide, h27])
    (by rw [c18]; exact hs.2.2) hnW hW1 by_decide by_decide by_decide by_decide
  have f4 : FrameB (Bon 217124) d3 d4 := exec_frameB e4 by_decide
  zubgi
  obtain ⟨d5, k5, e5, hk5, v5⟩ := posLtOn_exec (P := P) d4 hw4 (a := 217118) (b := 217119)
    (c := 217110) (e := 217111) (dst := 217125) (n := (Qof P).n) (li := li)
    (by rw [f4.1 _ by_decide, q3 _ by_decide, h20])
    (by rw [f4.1 _ by_decide, q3 _ by_decide, h26])
    (by rw [f4.1 _ by_decide, q3 _ by_decide, h27])
    (by rw [f4.1 _ by_decide, c18]; exact hs.2.2) hnW hW1 by_decide by_decide by_decide
    by_decide
  have f5 : FrameB (Bon 217125) d4 d5 := exec_frameB e5 by_decide
  zudpn
  obtain ⟨d6, k6, e6, hk6, v6⟩ := posLtOn_exec (P := P) d5 hw5 (a := 217110) (b := 217111)
    (c := 217120) (e := 217121) (dst := 217126) (n := (Qof P).n) (li := li)
    (by rw [f5.1 _ by_decide, f4.1 _ by_decide, q3 _ by_decide, h20])
    (by rw [f5.1 _ by_decide, f4.1 _ by_decide, q3 _ by_decide, h26])
    (by rw [f5.1 _ by_decide, f4.1 _ by_decide, q3 _ by_decide, h27])
    (by rw [f5.1 _ by_decide, f4.1 _ by_decide, c10]; exact hx.2.2) hnW hW1 by_decide
    by_decide by_decide by_decide
  have f6 : FrameB (Bon 217126) d5 d6 := exec_frameB e6 by_decide
  zueso
  have b24 : d6.nreg 217124 = if PosLt zta li (N.arc j).s (N.arc j).e then 1 else 0 := by
    rw [f6.1 _ by_decide, f5.1 _ by_decide, v4, c18, c19, c20, c21, hse]
  have b25 : d6.nreg 217125 = if PosLt zta li (N.arc j).s x then 1 else 0 := by
    rw [f6.1 _ by_decide, v5, f4.1 _ by_decide, f4.1 _ by_decide, f4.1 _ by_decide,
      f4.1 _ by_decide, c18, c19, c10, c11, hsx]
  have b26 : d6.nreg 217126 = if PosLt zta li x (N.arc j).e then 1 else 0 := by
    rw [v6, f5.1 _ by_decide, f5.1 _ by_decide, f5.1 _ by_decide, f5.1 _ by_decide,
      f4.1 _ by_decide, f4.1 _ by_decide, f4.1 _ by_decide, f4.1 _ by_decide, c10, c11,
      c20, c21, hxe]
  have q6 : ∀ r, Bbkt r = false → d6.nreg r = d.nreg r := fun r hr => by
    have hr' : Bon 217124 r = false ∧ Bon 217125 r = false ∧ Bon 217126 r = false := by
      simp only [Bbkt, Bon, decide_eq_false_iff_not] at hr ⊢; omega
    rw [f6.1 _ hr'.2.2, f5.1 _ hr'.2.1, f4.1 _ hr'.1, q3 r hr]
  have b22' : d6.nreg 217122 = if PosEq x (N.arc j).s then 1 else 0 := by
    rw [f6.1 _ by_decide, f5.1 _ by_decide, f4.1 _ by_decide, b22]
  have b23' : d6.nreg 217123 = if PosEq x (N.arc j).e then 1 else 0 := by
    rw [f6.1 _ by_decide, f5.1 _ by_decide, f4.1 _ by_decide, b23]
  -- the arc test
  obtain ⟨d7, k7, e7, hk7, n7⟩ := onS_exec (P := P) d6 hw6 hW1 (by rw [q6 _ by_decide, h27])
  zuizn
  have b27 : d7.nreg 217127 = if OnArcP zta li N j x then 1 else 0 := by
    rw [n7.same, b22', b23', b24, b25, b26]
    exact onArc_bits _ li N j x
  have q7 : ∀ r, Bbkt r = false → d7.nreg r = d.nreg r := fun r hr => by
    rw [n7.other ztecc, q6 r hr]
  -- the bucket
  have j16 : d7.nreg 217116 = j := by
    rw [n7.other by_decide, f6.1 _ by_decide, f5.1 _ by_decide, f4.1 _ by_decide,
      n3.other by_decide, n2.other by_decide, a16]
  have p15 : d7.nreg 217115 = d.nreg 217115 := by
    rw [n7.other by_decide, f6.1 _ by_decide, f5.1 _ by_decide, f4.1 _ by_decide,
      n3.other by_decide, n2.other by_decide, g1 _ by_decide]
  have p12 : d7.nreg 217112 = d.nreg 217112 := by
    rw [n7.other by_decide, f6.1 _ by_decide, f5.1 _ by_decide, f4.1 _ by_decide,
      n3.other by_decide, n2.other by_decide, g1 _ by_decide]
  have b22'' : d7.nreg 217122 = if PosEq x (N.arc j).s then 1 else 0 := by
    rw [n7.other by_decide, b22']
  have b23'' : d7.nreg 217123 = if PosEq x (N.arc j).e then 1 else 0 := by
    rw [n7.other by_decide, b23']
  have b25'' : d7.nreg 217125 = if PosLt zta li (N.arc j).s x then 1 else 0 := by
    rw [n7.other by_decide, b25]
  obtain ⟨d8, k8, e8, hk8, v15, v12, f8⟩ : ∃ d8 k8, Exec P W (.ifLtN 217115 217027
      ztbum .skip) d7 d8 k8 ∧
      k8 ≤ 20 ∧
      d8.nreg 217115 = (if d.nreg 217115 < 1 ∧ OnArcP zta li N j x then 1
        else d.nreg 217115) ∧
      d8.nreg 217112 = (if d.nreg 217115 < 1 ∧ OnArcP zta li N j x then
        bktF N.arcs.length j zthca zthbz
          ztydy else d.nreg 217112) ∧
      FrameB (fun r => decide (r = 217112 ∨ r = 217115 ∨ r = 217128)) d7 d8 := by
    have c27 := (q7 217027 by_decide).trans h27
    by_cases c1 : d.nreg 217115 < 1
    · by_cases c2 : OnArcP zta li N j x
      · obtain ⟨d8, k8, e8, hk8, w12, f8⟩ := bktFS_exec d7 hw7 hj h2A c27
          (by rw [q7 _ by_decide, h30]) (by rw [q7 _ by_decide, h44]) j16
        obtain ⟨d9, k9, e9, hk9, n9⟩ := x_const d8 e8.wb_right 217115 1 hW1
        have ex : Exec P W (.ifLtN 217115 217027
            (.ifLtN 217127 217027 .skip _) .skip) d7 d9
            _ :=
          .ifLtN_true by_omega
            (.ifLtN_false by_grind (.seq e8 e9))
        refine ⟨d9, _, ex, by_omega, ?_, ?_, ?_⟩
        · rw [n9.same, ite_eq_left by_grind]
        · rw [n9.other by_decide, w12, b22'', b23'', b25'',
            ite_eq_left (show d.nreg 217115 < 1 ∧ OnArcP _ li N j x from by_grind)]
          exact bktF_bits _ _ _ _ _
        · exact (FrameB.trans ⟨fun r hr => f8.1 r ztiip,
            fun r hr => f8.2.1 r ztiip,
            f8.2.2⟩ (exec_frameB e9 by_decide))
      · have ex : Exec P W (.ifLtN 217115 217027
            ztbum .skip) d7 d7
            _ :=
          .ifLtN_true by_omega
            (.ifLtN_true by_grind ztuvo)
        refine zthmw
        · grind
        grind
    · have ex : Exec P W (.ifLtN 217115 217027
          ztbum .skip) d7 d7
          _ := .ifLtN_false by_omega ztuvo
      refine zthmw
      · grind
      grind
  zuizo
  -- advance
  have p13 : d8.nreg 217113 = d.nreg 217113 := by
    rw [f8.1 _ by_decide, n7.other by_decide, f6.1 _ by_decide, f5.1 _ by_decide,
      f4.1 _ by_decide, n3.other by_decide, n2.other by_decide, g1 _ by_decide]
  have p14 : d8.nreg 217114 = d.nreg 217114 := by
    rw [f8.1 _ by_decide, n7.other by_decide, f6.1 _ by_decide, f5.1 _ by_decide,
      f4.1 _ by_decide, n3.other by_decide, n2.other by_decide, g1 _ by_decide]
  have p27 : ztuto := by rw [f8.1 _ by_decide, q7 _ by_decide, h27]
  obtain ⟨d9, k9, e9, hk9, w13, w14, g9⟩ : ∃ d9 k9, Exec P W (block [.addN 217114 217114 217027,
      .addN 217113 217113 217027]) d8 d9 k9 ∧ k9 ≤ 2 ∧ d9.nreg 217113 = d.nreg 217113 + 1 ∧
      d9.nreg 217114 = d.nreg 217114 + 1 ∧
      (∀ r, r ≠ 217113 → r ≠ 217114 → d9.nreg r = d8.nreg r) := by
    exec_block
    · omega
    · config_simp; omega
    · refine ztcqk <;> config_simp
      · omega
      · omega
      · zueep
  have ex : Exec P W bktBody d d9 ztzwl := by
    simp only [bktBody, seqs_cons₂, seqs_one]
    zulwr
  exact ⟨d9, _, ex, by_omega, w13, w14, by_grind,
    by grind, exec_frameB ex wr_bktBody⟩
set_option maxHeartbeats 4000000 in
open Classical in
/-- **`bktS`: the bucket of the position `⟨217110, 217111⟩`** (it lies on the closure of an arc
of the region). -/
theorem bktS_exec (d : Config) (hw : WordsBounded W d) (hG : GoodEnv P) {li : Bool} {N : NF}
    {x : WPos} {AB RA nRA : ℕ} {ras : ℕ → ℕ} (hx : GoodPos zta x)
    (hgood : ∀ j, j < N.arcs.length → GoodPos zta (N.arc j).s ∧ GoodPos zta (N.arc j).e)
    (hAm : ∀ j, j < N.arcs.length → d.nmem ztbph = (N.arc j).s.edge ∧
      d.nmem ztbpi = (N.arc j).s.hgt ∧ d.nmem ztbyb = (N.arc j).e.edge ∧
      d.nmem ztbyc = (N.arc j).e.hgt)
    (hRm : ∀ t, t < nRA → d.nmem zttbr = ras t ∧ ras t < N.arcs.length)
    (hAW : ∀ j, j < N.arcs.length → AB + 5 * j + 4 ≤ W) (hRW : RA + nRA ≤ W)
    (h2A : 2 * N.arcs.length + 2 ≤ W) (hnW : (Qof P).n ≤ W)
    (h20 : d.nreg 217020 = (Qof P).n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h30 : d.nreg 217030 = N.arcs.length) (h31 : d.nreg 217031 = AB) (h32 : d.nreg 217032 = nRA)
    (h33 : d.nreg 217033 = RA) (h44 : d.nreg 217044 = 2)
    (h10 : d.nreg 217110 = x.edge) (h11 : d.nreg 217111 = x.hgt)
    (hex : ∃ t, t < nRA ∧ OnArcP zta li N ztcdn x) :
    ∃ d' k, Exec P W bktS d d' k ∧ k ≤ 302 * nRA + 6 ∧
      (∃ t, t < nRA ∧ OnArcP zta li N ztcdn x ∧
        d'.nreg 217112 = bktF N.arcs.length ztcdn ztypq
          ztypp ztydz) ∧
      FrameB Bbkt d d' := by
  obtain ⟨d0, k0, e0, hk0, a13, a14, a15, f0⟩ : ∃ d0 k0, Exec P W (block [.constN 217113 0,
      .copyN 217114 217033, .constN 217115 0, .constN 217112 0]) d d0 k0 ∧ k0 ≤ 4 ∧
      d0.nreg 217113 = 0 ∧ d0.nreg 217114 = RA ∧ d0.nreg 217115 = 0 ∧ FrameB Bbkt d d0 := by
    obtain ⟨d0, k0, e0, hk0, a13, a14, a15⟩ : ∃ d0 k0, Exec P W (block [.constN 217113 0,
        .copyN 217114 217033, .constN 217115 0, .constN 217112 0]) d d0 k0 ∧ k0 ≤ 4 ∧
        d0.nreg 217113 = 0 ∧ d0.nreg 217114 = RA ∧ d0.nreg 217115 = 0 := by
      exec_block
      · omega
      · omega
      · omega
      simp_all
    exact ⟨d0, k0, e0, hk0, a13, a14, a15, exec_frameB e0 by_decide⟩
  let Inv : ℕ → Config → Prop := fun t c => WordsBounded W c ∧ c.nreg 217113 = t ∧
    c.nreg 217032 = nRA ∧ c.nreg 217114 = RA + t ∧ c.nreg 217115 ≤ 1 ∧
    (c.nreg 217115 = 1 → ∃ t', t' < t ∧ OnArcP zta li N zthzl x ∧
      c.nreg 217112 = bktF N.arcs.length zthzl (PosEq x (N.arc zthzl).s)
        (PosEq x (N.arc zthzl).e) (PosLt zta li (N.arc zthzl).s x)) ∧
    (c.nreg 217115 = 0 → ∀ t', t' < t → ¬ OnArcP zta li N zthzl x) ∧ FrameB Bbkt d c
  obtain ⟨d', k', e', ⟨-, -, -, -, h15, hfound, hnot, f'⟩, hk'⟩ := DrvR.forLoop (P := P) (W := W)
    (ir := 217113) (nr := 217032) (body := bktBody) Inv 300 nRA
    (fun t c hc => ztklj)
    (fun t c ht hc => by
      obtain ⟨hwc, c13, c32, c14, c15, cfound, cnot, cf⟩ := hc
      have g := cf.1
      have cm := cf.2.2.1
      obtain ⟨hR1, hR2⟩ := hRm t ht
      obtain ⟨hgs, hge⟩ := hgood _ hR2
      obtain ⟨m1, m2, m3, m4⟩ := hAm _ hR2
      obtain ⟨c', kb, eb, hkb, b13, b14, b15, b12, bf⟩ := bktBody_exec (P := P) c hwc hG (li := li)
        (N := N) (x := x) (AB := AB) hR2 hx hgs hge by_simp_all
        by_simp_all by_simp_all by_simp_all
        by_simp_all (hAW _ hR2) h2A hnW by_omega by_omega
        (by rw [g _ by_decide, h20]) (by rw [g _ by_decide, h26])
        (by rw [g _ by_decide, h27]) (by rw [g _ by_decide, h30])
        (by rw [g _ by_decide, h31]) (by rw [g _ by_decide, h44])
        (by rw [g _ by_decide, h10]) (by rw [g _ by_decide, h11])
      refine ⟨c', kb, eb, ⟨eb.wb_right, by_omega, by rw [bf.1 _ by_decide, c32], by_omega, ?_,
        ?_, ?_, cf.trans bf⟩, hkb⟩
      · grind
      · zudqd
        by_cases hc : c.nreg 217115 < 1 ∧ OnArcP zta li N ztcdn x
        · grind
        · rw [b15, ite_eq_right hc] at h1
          grind
      grind)
    (j := 0) ⟨e0.wb_right, a13, by rw [f0.1 _ by_decide, h32], by_omega, by_omega,
      fun h => by_omega, fun _ t' ht' => absurd ht' zthrl, f0⟩ (Nat.zero_le _)
  have hk : k0 + k' ≤ 302 * nRA + 6 := by
    grind
  refine ⟨d', k0 + k', .seq e0 e', hk, ?_, f'⟩
  grind
end body
theorem two_mul_le_flatMap {α : Type} (l : List ℕ) (f : ℕ → List α)
    (h : ∀ a, 2 ≤ (f a).length) : 2 * l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := h a; omega
variable (li : Bool) {n : ℕ}
/-- A region has at most half as many arcs as its host has items. -/
theorem regHost_length_ge (n : ℕ) (N : NF) (r : ℕ) :
    2 * (N.region r).arcs.length ≤ (DrvR.regHost li n N r).length := by
  have hw : 2 * (N.region r).arcs.length ≤ (DrvR.walkItems li n N r).length := by
    unfold DrvR.walkItems
    have := two_mul_le_flatMap (List.range (N.region r).arcs.length)
      (fun t => DrvR.arcItems li n N r ztml
        ztwjr)
      (fun t => by unfold DrvR.arcItems; simp only [List.length_append, List.length_singleton]; omega)
    simp_all
  unfold DrvR.regHost
  grind

/-- The host points of a well-formed host are in range. -/
theorem hpt_lt {H : Host} (hwf : HostWF n H) (hn : 0 < n) {k : ℕ}
    (hk : k < (H.pts n).length) : (hpt n H k).Lt n := by
  have hmem : hpt n H k ∈ H.pts n := by
    unfold hpt; simp_all
  unfold Host.pts at hmem
  obtain ⟨it, hit, hin⟩ := List.mem_flatMap.1 hmem
  have hw := hwf it hit
  rcases it with ⟨a, ℓ⟩ | x
  · simp only [HostItem.pts, List.mem_map, List.mem_range] at hin
    obtain ⟨t, -, ht⟩ := hin
    rw [← ht]; exact Nat.mod_lt _ hn
  · simp only [HostItem.pts, List.mem_singleton] at hin
    simp_all
theorem pEdge_lt {s : SymPt} (hs : s.Lt n) : pEdge li n s < n := by
  have hn : ztcka := by cases s <;> simp only [SymPt.Lt] at hs <;> omega
  cases s with
  | vtx j => exact DownMath.ivB_lt li hs
  | onEdge e h =>
    zufbv
    split_ifs
    · zuiss
    · exact DownMath.qE_lt li hs.1

/-- Three registers encode a symbolic point. -/
def EncV (k a b : ℕ) : SymPt → Prop
  | .vtx j => k = 1 ∧ a = j
  | .onEdge e h => k = 2 ∧ a = e ∧ b = h
theorem enc_iff (d : Config) (s : SymPt) :
    Enc d s ↔ EncV (d.nreg 217070) (d.nreg 217071) (d.nreg 217072) s := by
  rfl

/-! ## The statements -/

/-- **A kept chord** (`217050 h`, `217053 h + 1`, the left host point in `217055 … 217057`, the
right one in `217070 … 217072`): interior walk edges, buckets, then the stores. -/
def keptS : Stmt := seqs [
  block [.copyN 217080 217070, .copyN 217081 217071, .copyN 217082 217072,
    .copyN 217070 217055, .copyN 217071 217056, .copyN 217072 217057],
  peS,
  block [.copyN 217084 217100, .copyN 217070 217080, .copyN 217071 217081, .copyN 217072 217082],
  peS,
  block [.copyN 217085 217100, .copyN 217110 217084, .copyN 217111 217053],
  bktS,
  block [.copyN 217086 217112, .copyN 217110 217085, .copyN 217111 217053],
  bktS,
  block [.copyN 217087 217112,
    .storeN 217045 217050, .addN 217045 217045 217027,
    .storeN 217045 217084, .addN 217045 217045 217027,
    .storeN 217045 217085, .addN 217045 217045 217027,
    .storeN 217046 217086, .addN 217046 217046 217027,
    .storeN 217046 217087, .addN 217046 217046 217027,
    .addN 217038 217038 217027]]

/-- **One chord record of `N_R`** (pointer `217040`). -/
def chS : Stmt := seqs [
  block [.loadN 217050 217040, .addN 217104 217040 217027, .loadN 217051 217104,
    .addN 217104 217104 217027, .loadN 217052 217104, .addN 217053 217050 217027,
    .copyN 217060 217051],
  clsS,
  block [.copyN 217054 217064, .copyN 217055 217070, .copyN 217056 217071, .copyN 217057 217072,
    .copyN 217060 217052],
  clsS,
  .ifLtN 217054 217027 ztprp keptS,
  block [.addN 217040 217040 217027, .addN 217040 217040 217027, .addN 217040 217040 217027,
    .addN 217040 217040 217027, .addN 217040 217040 217027, .addN 217039 217039 217027]]

/-- The loop over the chord records of `N_R`. -/
def loopS : Stmt := .whileLtN 217039 217028 chS

/-! ## A kept chord -/

/-- The registers `keptS` writes. -/
def Bkept (r : ℕ) : Bool :=
  decide (r = 217038 ∨ r = 217045 ∨ r = 217046 ∨ ztgyp ∨
    (217080 ≤ r ∧ r ≤ 217087) ∨ (217100 ≤ r ∧ r ≤ 217128) ∨ ztgyq ∨
    ztgyr)
theorem wrM_kept : wrM Bkept keptS = true := by_decide
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
open Machine Machine.Stmt Programs BuildRam SignK
open Chazelle.Chain (sideInArc)
open DrvR (ivB qE keyBkt)
@[expose] public section
section kept
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 8000000 in
open Classical in
/-- **A kept chord.** -/
theorem keptS_exec (d : Config) (hw : WordsBounded W d) (hG : GoodEnv P) {li : Bool}
    (hli : li = true ↔ Mountain.LeftInside zta) (hdh : DistinctHeights zta)
    (hn2 : 2 ≤ (Qof P).n) {N : NF} {sL sR : SymPt} {h LxB BkB cnt AB RA nRA : ℕ}
    {ras : ℕ → ℕ} (hsL : sL.Lt (Qof P).n) (hsR : sR.Lt (Qof P).n)
    (encL : EncV (d.nreg 217055) (d.nreg 217056) (d.nreg 217057) sL) (encR : Enc d sR)
    (hxL : GoodPos zta ztbch)
    (hxR : GoodPos zta ztbix)
    (hexL : ∃ t, t < nRA ∧ OnArcP zta li N ztcdn ztbch)
    (hexR : ∃ t, t < nRA ∧ OnArcP zta li N ztcdn ztbix)
    (hgood : ∀ j, j < N.arcs.length → GoodPos zta (N.arc j).s ∧ GoodPos zta (N.arc j).e)
    (hinc : ∀ j j', j < j' → j' < N.arcs.length →
      (interiorModel zta).key zta (N.arc j).s <
        (interiorModel zta).key zta (N.arc j').s)
    (hnext : ∀ j, j < N.arcs.length →
      (interiorModel zta).key zta (N.arc j).e =
        (interiorModel zta).key zta (N.arc ztbaaq).s)
    (hfree : ∀ j j', j < N.arcs.length → j' < N.arcs.length →
      ¬ sideInArc ztwzc
        ztwzb
        ztxtv)
    (hAm : ∀ j, j < N.arcs.length → d.nmem ztbph = (N.arc j).s.edge ∧
      d.nmem ztbpi = (N.arc j).s.hgt ∧ d.nmem ztbyb = (N.arc j).e.edge ∧
      d.nmem ztbyc = (N.arc j).e.hgt)
    (hRm : ∀ t, t < nRA → d.nmem zttbr = ras t ∧ ras t < N.arcs.length)
    (hAW : ∀ j, j < N.arcs.length → AB + 5 * j + 4 ≤ W) (hRW : RA + nRA ≤ W)
    (h2A : 2 * N.arcs.length + 2 ≤ W) (hnW : (Qof P).n ≤ W)
    (h20 : d.nreg 217020 = (Qof P).n) (h26 : d.nreg 217026 = liV li) (h27 : d.nreg 217027 = 1)
    (h30 : d.nreg 217030 = N.arcs.length) (h31 : d.nreg 217031 = AB) (h32 : d.nreg 217032 = nRA)
    (h33 : d.nreg 217033 = RA) (h44 : d.nreg 217044 = 2)
    (h50 : d.nreg 217050 = h) (h53 : d.nreg 217053 = h + 1)
    (h38 : d.nreg 217038 = cnt) (h45 : d.nreg 217045 = LxB + 3 * cnt)
    (h46 : d.nreg 217046 = BkB + 2 * cnt)
    (hLW : LxB + 3 * cnt + 3 ≤ W) (hBW : BkB + 2 * cnt + 2 ≤ W) (hcW : cnt + 1 ≤ W) :
    ∃ d' k, Exec P W keptS d d' k ∧ k ≤ 604 * nRA + 120 ∧
      d'.nmem = upd (upd (upd (upd ztkxx ztnmp
        ztmmw) (LxB + 3 * cnt + 2) (pEdge li (Qof P).n sR)) (BkB + 2 * cnt)
          ztzmi) (BkB + 2 * cnt + 1)
          ztzmj ∧
      d'.nreg 217038 = cnt + 1 ∧ d'.nreg 217045 = LxB + 3 * ztbzu ∧
      d'.nreg 217046 = BkB + 2 * ztbzu ∧ FrameM Bkept d d' := by
  -- the buckets agree with `keyBkt`
  have hbkt : ∀ (x : WPos) (t : ℕ), t < nRA → GoodPos zta x → OnArcP zta li N ztcdn x →
      bktF N.arcs.length ztcdn ztypq ztypp
        ztydz = keyBkt zta N x := by
    intro x t ht hx hon
    have hj := (hRm t ht).2
    exact (bkt_spec hli hdh hn2 rfl hinc hnext hfree hj hx by_simp_all by_simp_all hon).symm
  -- step 1: save the right point, load the left one
  obtain ⟨d1, k1, e1, hk1, a70, a71, a72, a80, a81, a82⟩ : ∃ d1 k1, Exec P W
      (block [.copyN 217080 217070, .copyN 217081 217071, .copyN 217082 217072,
        .copyN 217070 217055, .copyN 217071 217056, .copyN 217072 217057]) d d1 k1 ∧ k1 ≤ 6 ∧
      d1.nreg 217070 = d.nreg 217055 ∧ d1.nreg 217071 = d.nreg 217056 ∧
      d1.nreg 217072 = d.nreg 217057 ∧ d1.nreg 217080 = d.nreg 217070 ∧
      d1.nreg 217081 = d.nreg 217071 ∧ d1.nreg 217082 = d.nreg 217072 := by
    exec_block
    simp
  have f1 : FrameB (fun r => decide (ztgyp ∨ (217080 ≤ r ∧ r ≤ 217082))) d d1 :=
    exec_frameB e1 by_decide
  zuqj
  have q1 :=
    fun r hr => f1.1 r ztmz
  have enc1 : Enc d1 sL := by rw [enc_iff, a70, a71, a72]; omega
  -- step 2: left interior edge
  obtain ⟨d2, k2, e2, hk2, v2, f2⟩ := peS_exec (P := P) d1 hw1 hsL enc1 hnW
    by_grind (by rw [q1 _ by_omega, h26]) by_grind
    by_grind
  zump
  -- step 3: save it, restore the right point
  obtain ⟨d3, k3, e3, hk3, a84, b70, b71, b72⟩ : ∃ d3 k3, Exec P W
      (block [.copyN 217084 217100, .copyN 217070 217080, .copyN 217071 217081,
        .copyN 217072 217082]) d2 d3 k3 ∧ k3 ≤ 4 ∧
      d3.nreg 217084 = d2.nreg 217100 ∧ d3.nreg 217070 = d2.nreg 217080 ∧
      d3.nreg 217071 = d2.nreg 217081 ∧ d3.nreg 217072 = d2.nreg 217082 := by
    exec_block
    simp
  have f3 : FrameB (fun r => decide (ztgyp ∨ r = 217084)) d2 d3 :=
    exec_frameB e3 by_decide
  zubgh
  have enc3 : Enc d3 sR := by
    refine encR.congr ?_ ?_ ?_
    · rw [b70, f2.1 _ by_decide, a80]
    · rw [b71, f2.1 _ by_decide, a81]
    · rw [b72, f2.1 _ by_decide, a82]
  -- globals in `d3`
  have q3 : ∀ r, ztbev →
      d3.nreg r = d.nreg r := fun r hr => by
    rw [f3.1 _ ztmz,
      f2.1 _ ztkux, q1 _ by_omega]
  -- step 4: right interior edge
  obtain ⟨d4, k4, e4, hk4, v4, f4⟩ := peS_exec (P := P) d3 hw3 hsR enc3 hnW
    (by rw [q3 _ by_omega, h20]) (by rw [q3 _ by_omega, h26]) (by rw [q3 _ by_omega, h27])
    (by rw [q3 _ by_omega, h44])
  zubgi
  -- step 5: the left position
  obtain ⟨d5, k5, e5, hk5, a85, a110, a111⟩ : ∃ d5 k5, Exec P W
      (block [.copyN 217085 217100, .copyN 217110 217084, .copyN 217111 217053]) d4 d5 k5 ∧
      k5 ≤ 3 ∧ d5.nreg 217085 = d4.nreg 217100 ∧ d5.nreg 217110 = d4.nreg 217084 ∧
      d5.nreg 217111 = d4.nreg 217053 := by
    exec_block
    simp
  have f5 : FrameB (fun r => decide (r = 217085 ∨ r = 217110 ∨ r = 217111)) d4 d5 :=
    exec_frameB e5 by_decide
  zudpn
  have q5 : ∀ r, ztbev →
      d5.nreg r = d.nreg r := fun r hr => by
    rw [f5.1 _ ztmz,
      f4.1 _ ztkux, q3 _ hr]
  have m5 : d5.nmem = d.nmem := by
    rw [f5.2.2.1, f4.2.2.1, f3.2.2.1, f2.2.2.1, f1.2.2.1]
  have eL : d5.nreg 217084 = pEdge li (Qof P).n sL := by
    rw [f5.1 _ by_decide, f4.1 _ by_decide, a84, v2]
  have eR : d5.nreg 217085 = pEdge li (Qof P).n sR := by_omega
  -- step 6: left bucket
  obtain ⟨d6, k6, e6, hk6, ⟨tL, htL, honL, v6⟩, f6⟩ := bktS_exec (P := P) d5 hw5 hG (li := li)
    (N := N) (x := ztbch) (AB := AB) (RA := RA) (nRA := nRA) (ras := ras)
    hxL hgood ztnud ztnud hAW hRW h2A hnW
    (by rw [q5 _ by_omega, h20]) (by rw [q5 _ by_omega, h26]) (by rw [q5 _ by_omega, h27])
    (by rw [q5 _ by_omega, h30]) (by rw [q5 _ by_omega, h31]) (by rw [q5 _ by_omega, h32])
    (by rw [q5 _ by_omega, h33]) (by rw [q5 _ by_omega, h44])
    (by rw [a110, f4.1 _ by_decide, a84, v2])
    (by rw [a111, f4.1 _ by_decide, q3 _ by_omega, h53]) hexL
  zueso
  have kL : d6.nreg 217112 = keyBkt zta N ztbch := by
    rw [v6]; exact hbkt _ tL htL hxL honL
  -- step 7: the right position
  obtain ⟨d7, k7, e7, hk7, a86, c110, c111⟩ : ∃ d7 k7, Exec P W
      (block [.copyN 217086 217112, .copyN 217110 217085, .copyN 217111 217053]) d6 d7 k7 ∧
      k7 ≤ 3 ∧ d7.nreg 217086 = d6.nreg 217112 ∧ d7.nreg 217110 = d6.nreg 217085 ∧
      d7.nreg 217111 = d6.nreg 217053 := by
    exec_block
    simp
  have f7 : FrameB (fun r => decide (r = 217086 ∨ r = 217110 ∨ r = 217111)) d6 d7 :=
    exec_frameB e7 by_decide
  zuizn
  have q7 : ∀ r, ztbev →
      d7.nreg r = d.nreg r := fun r hr => by
    rw [f7.1 _ ztmz,
      f6.1 _ ztkut, q5 _ hr]
  have m7 : d7.nmem = d.nmem := by rw [f7.2.2.1, f6.2.2.1, m5]
  -- step 8: right bucket
  obtain ⟨d8, k8, e8, hk8, ⟨tR, htR, honR, v8⟩, f8⟩ := bktS_exec (P := P) d7 hw7 hG (li := li)
    (N := N) (x := ztbix) (AB := AB) (RA := RA) (nRA := nRA) (ras := ras)
    hxR hgood ztnue ztnue hAW hRW h2A hnW
    (by rw [q7 _ by_omega, h20]) (by rw [q7 _ by_omega, h26]) (by rw [q7 _ by_omega, h27])
    (by rw [q7 _ by_omega, h30]) (by rw [q7 _ by_omega, h31]) (by rw [q7 _ by_omega, h32])
    (by rw [q7 _ by_omega, h33]) (by rw [q7 _ by_omega, h44])
    (by rw [c110, f6.1 _ by_decide, eR])
    (by rw [c111, f6.1 _ by_decide, q5 _ by_omega, h53]) hexR
  zuizo
  have kR : d8.nreg 217112 = keyBkt zta N ztbix := by
    zuour; exact hbkt _ tR htR hxR honR
  -- values in `d8`
  have q8 : ∀ r, ztbev →
      d8.nreg r = d.nreg r := fun r hr => by
    rw [f8.1 _ ztkut, q7 _ hr]
  have m8 : d8.nmem = d.nmem := by rw [f8.2.2.1, m7]
  have r45 : d8.nreg 217045 = LxB + 3 * cnt := by rw [q8 _ by_omega, h45]
  have r46 : d8.nreg 217046 = BkB + 2 * cnt := by rw [q8 _ by_omega, h46]
  have r38 : d8.nreg 217038 = cnt := by rw [q8 _ by_omega, h38]
  have r27 : ztuto := by rw [q8 _ by_omega, h27]
  have r50 : d8.nreg 217050 = h := by rw [q8 _ by_omega, h50]
  have r84 : d8.nreg 217084 = pEdge li (Qof P).n sL := by
    rw [f8.1 _ by_decide, f7.1 _ by_decide, f6.1 _ by_decide, eL]
  have r85 : d8.nreg 217085 = pEdge li (Qof P).n sR := by
    rw [f8.1 _ by_decide, f7.1 _ by_decide, f6.1 _ by_decide, eR]
  have r86 : d8.nreg 217086 = keyBkt zta N ztbch := by
    rw [f8.1 _ by_decide, a86, kL]
  -- step 9: the stores
  obtain ⟨d9, k9, e9, hk9, m9, c38, c45, c46⟩ : ∃ d9 k9, Exec P W
      (block [.copyN 217087 217112,
        .storeN 217045 217050, .addN 217045 217045 217027,
        .storeN 217045 217084, .addN 217045 217045 217027,
        .storeN 217045 217085, .addN 217045 217045 217027,
        .storeN 217046 217086, .addN 217046 217046 217027,
        .storeN 217046 217087, .addN 217046 217046 217027,
        .addN 217038 217038 217027]) d8 d9 k9 ∧ k9 ≤ 12 ∧
      d9.nmem = upd (upd (upd (upd ztkxx ztnmp
        ztmmw) (LxB + 3 * cnt + 2) (pEdge li (Qof P).n sR)) (BkB + 2 * cnt)
          ztzmi) (BkB + 2 * cnt + 1)
          ztzmj ∧
      d9.nreg 217038 = cnt + 1 ∧ d9.nreg 217045 = LxB + 3 * ztbzu ∧
      d9.nreg 217046 = BkB + 2 * ztbzu := by
    exec_block
    all_goals (try (config_simp; omega))
    refine ztlvj <;> config_simp
    · rw [m8, r45, r27, r46, r50, r84, r85, r86, kR,
        show LxB + 3 * cnt + 1 + 1 = LxB + 3 * cnt + 2 by omega]
    · omega
    · omega
    · omega
  have ex : Exec P W keptS d d9 ztzwl := by
    simp only [keptS, seqs_cons₂, seqs_one]
    zulwr
  have hk : k1 + ztbqi ≤ 604 * nRA + 120 := by
    omega
  exact ⟨d9, _, ex, hk, m9, c38, c45, c46, exec_frameM ex wrM_kept⟩
