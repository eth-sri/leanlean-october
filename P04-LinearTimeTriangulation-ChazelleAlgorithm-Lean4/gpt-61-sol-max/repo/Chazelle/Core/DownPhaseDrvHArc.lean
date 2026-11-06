module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvHPart

/-!
# Down-phase driver, host RAM (D3a), part 6: one arc

* `HEnv`: the static environment of the arc loop (constants, region data, the normal form
  readable below the buffer `T`, word bounds); it survives the loop's writes (`HEnv.keep`);
* `ldS_exec`: the arcs `arcs[t]`, `arcs[(t + 1) mod A]` and their ends;
* `junS_exec`, `cpEm_exec`: the junction point and the copied points;
* `arcBody_exec`: one iteration appends `arcIt li n N r t` to the buffer.
-/

namespace Chazelle.Core

namespace DrvH

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

/-- **The static environment of the arc loop**: constants, region data, the normal form readable
below `T`, the word bounds. -/
structure HEnv (W n : ℕ) (N : NF) (r : ℕ) (li : Bool) (T : ℕ) (d : Config) : Prop where
  K : Kst n li d
  F : HFacts n N r
  aR : d.nreg 215030 = (N.region r).arcs.length
  kR : d.nreg 215031 = (N.region r).chords.length
  tR : d.nreg 215032 = T
  arcs : ∀ t, t < (N.region r).arcs.length →
    d.nmem (d.nreg 215027 + (d.nreg 215028 + t)) = (N.region r).arcs.getD t 0 ∧
    d.nreg 215027 + (d.nreg 215028 + t) < T
  chs : ∀ v, v < (N.region r).chords.length →
    d.nmem (d.nreg 215027 + (d.nreg 215029 + v)) = (N.region r).chords.getD v 0 ∧
    d.nreg 215027 + (d.nreg 215029 + v) < T
  arcR : ∀ j, j < N.arcs.length →
    d.nmem (d.nreg 215026 + 5 * j + 1) = (N.arc j).s.edge ∧
    d.nmem (d.nreg 215026 + 5 * j + 2) = (N.arc j).s.hgt ∧
    d.nmem (d.nreg 215026 + 5 * j + 3) = (N.arc j).e.edge ∧
    d.nmem (d.nreg 215026 + 5 * j + 4) = (N.arc j).e.hgt ∧ d.nreg 215026 + 5 * j + 4 < T
  chR : ∀ i, i < N.nChords → d.nmem (d.nreg 215025 + 5 * i) = (N.chord i).h ∧
    d.nmem (d.nreg 215025 + 5 * i + 1) = (N.chord i).lp ∧
    d.nmem (d.nreg 215025 + 5 * i + 2) = (N.chord i).rp ∧ d.nreg 215025 + 5 * i + 2 < T
  hT : T + 200 ≤ W
  hn : 8 * n + 32 ≤ W
  hn0 : 0 < n

/-- The environment survives the arc loop's writes. -/
theorem HEnv.keep {W n : ℕ} {N : NF} {r : ℕ} {li : Bool} {T : ℕ} {d d' : Config}
    (h : HEnv W n N r li T d) (hf : FrameM Bdyn d d') (hm : ∀ a, a < T → d'.nmem a = d.nmem a) :
    HEnv W n N r li T d' := by
  have g : ∀ q, Bdyn q = false → d'.nreg q = d.nreg q := hf.1
  have g25 : d'.nreg 215025 = d.nreg 215025 := g _ (by decide)
  have g26 : d'.nreg 215026 = d.nreg 215026 := g _ (by decide)
  have g27 : d'.nreg 215027 = d.nreg 215027 := g _ (by decide)
  have g28 : d'.nreg 215028 = d.nreg 215028 := g _ (by decide)
  have g29 : d'.nreg 215029 = d.nreg 215029 := g _ (by decide)
  refine ⟨h.K.frame hf (by decide), h.F, by ram_grind,
    by ram_grind, by ram_grind, fun t ht => ?_, fun v hv => ?_,
    fun j hj => ?_, fun i hi => ?_, h.hT, h.hn, h.hn0⟩
  all_goals ram_grind

theorem add_1_1 (a : ℕ) : a + 1 + 1 = a + 2 := rfl
theorem add_5 (a b : ℕ) : a + (b + b + (b + b) + b) = a + 5 * b := by ring

theorem mod_succ_of_lt {t A : ℕ} (ht : t < A) : (t + 1) % A = if t + 1 < A then t + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  grind [Nat.mod_self]

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Loading the arcs of iteration `t`** and their ends. -/
theorem ldS_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {N : NF} {r : ℕ} {li : Bool} {T t : ℕ}
    (hE : HEnv W n N r li T d) (h41 : d.nreg 215041 = t) (ht : t < (N.region r).arcs.length) :
    ∃ d' k, Exec P W ldS d d' k ∧ k ≤ 30 ∧
      d'.nreg 215046 = (N.arc ((N.region r).arcs.getD t 0)).e.edge ∧
      d'.nreg 215047 = (N.arc ((N.region r).arcs.getD t 0)).e.hgt ∧
      d'.nreg 215048 = (N.arc ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)).s.edge ∧
      d'.nreg 215049 = (N.arc ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)).s.hgt ∧
      d'.nreg 215050 = (N.arc ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)).e.edge ∧
      d'.nreg 215051 = (N.arc ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)).e.hgt ∧
      d'.nmem = d.nmem ∧ FrameM Bld d d' := by
  have hmem : ∀ t', t' < (N.region r).arcs.length → (N.region r).arcs.getD t' 0 ∈ (N.region r).arcs :=
    fun t' h' => by simp_all
  have K := hE.K
  have hT := hE.hT
  obtain ⟨b1, b2⟩ := hE.arcs t ht
  obtain ⟨p1, p2, p3, p4, p5⟩ := hE.arcR _ (hE.F.harc _ (hmem t ht)).1
  rw [mod_succ_of_lt ht]
  by_cases hlt : t + 1 < (N.region r).arcs.length
  · simp only [hlt, ↓reduceIte]
    obtain ⟨c1, c2⟩ := hE.arcs (t + 1) hlt
    obtain ⟨q1, q2, q3, q4, q5⟩ := hE.arcR _ (hE.F.harc _ (hmem _ hlt)).1
    obtain ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, hm⟩ : ∃ d' k, Exec P W ldS d d' k ∧ k ≤ 30 ∧
        d'.nreg 215046 = (N.arc ((N.region r).arcs.getD t 0)).e.edge ∧
        d'.nreg 215047 = (N.arc ((N.region r).arcs.getD t 0)).e.hgt ∧
        d'.nreg 215048 = (N.arc ((N.region r).arcs.getD (t + 1) 0)).s.edge ∧
        d'.nreg 215049 = (N.arc ((N.region r).arcs.getD (t + 1) 0)).s.hgt ∧
        d'.nreg 215050 = (N.arc ((N.region r).arcs.getD (t + 1) 0)).e.edge ∧
        d'.nreg 215051 = (N.arc ((N.region r).arcs.getD (t + 1) 0)).e.hgt ∧
        d'.nmem = d.nmem := by
      unfold ldS
      refine spec_seq ?_
      exec_block
      all_goals try (config_simp; (try simp only [h41, K.one]); omega)
      refine spec_seq ?_
      refine spec_ifLtN_true (by config_simp; simp only [h41, K.one, hE.aR]; omega) ?_
      refine spec_skip ‹_› ?_
      exec_block
      all_goals try (config_simp; (try simp only [h41, K.one, K.three, b1, c1, add_5, add_1_1]); omega)
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp <;>
        simp only [h41, K.one, K.three, b1, c1, add_5, add_1_1, p3, p4, q1, q2,
          q3, q4]
    exact ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, hm, exec_frameM ex wrM_ldS⟩
  · simp only [hlt, ↓reduceIte]
    have h0 : 0 < (N.region r).arcs.length := by omega
    obtain ⟨c1, c2⟩ := hE.arcs 0 h0
    rw [Nat.add_zero] at c1 c2
    obtain ⟨q1, q2, q3, q4, q5⟩ := hE.arcR _ (hE.F.harc _ (hmem _ h0)).1
    obtain ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, hm⟩ : ∃ d' k, Exec P W ldS d d' k ∧ k ≤ 30 ∧
        d'.nreg 215046 = (N.arc ((N.region r).arcs.getD t 0)).e.edge ∧
        d'.nreg 215047 = (N.arc ((N.region r).arcs.getD t 0)).e.hgt ∧
        d'.nreg 215048 = (N.arc ((N.region r).arcs.getD 0 0)).s.edge ∧
        d'.nreg 215049 = (N.arc ((N.region r).arcs.getD 0 0)).s.hgt ∧
        d'.nreg 215050 = (N.arc ((N.region r).arcs.getD 0 0)).e.edge ∧
        d'.nreg 215051 = (N.arc ((N.region r).arcs.getD 0 0)).e.hgt ∧
        d'.nmem = d.nmem := by
      unfold ldS
      refine spec_seq ?_
      exec_block
      all_goals try (config_simp; (try simp only [h41, K.one]); omega)
      refine spec_seq ?_
      refine spec_ifLtN_false (by config_simp; simp only [h41, K.one, hE.aR]; omega) ?_
      exec_block
      all_goals try (config_simp; (try simp only [h41, K.one, K.three, b1, c1, add_5, add_1_1,
        Nat.add_zero]); omega)
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp <;>
        simp only [h41, K.one, K.three, b1, c1, add_5, add_1_1, p3, p4, q1, q2,
          q3, q4, Nat.add_zero]
    exact ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, hm, exec_frameM ex wrM_ldS⟩

/-- **Copy a point into the emit registers and emit it.** -/
theorem cpEm_exec (a b : ℕ) (hb : b ≠ 215064) (d : Config)
    (hw : WordsBounded W d) {li : Bool} {n e h T : ℕ}
    {xs : List HostItem} (hK : Kst n li d) (h1 : d.nreg a = e) (h2 : d.nreg b = h)
    (hB : Buf n T xs d) (hW1 : T + 3 * xs.length + 3 ≤ W) (hW2 : ptsLen n xs + 1 ≤ W)
    (hW3 : e + 1 ≤ W) :
    ∃ d' k, Exec P W (.seq (block [.copyN 215064 a, .copyN 215065 b]) emitS) d d' k ∧ k ≤ 17 ∧
      Buf n T (xs ++ [ptE li n e h]) d' ∧
      (∀ x, x < T + 3 * xs.length → d'.nmem x = d.nmem x) ∧
      FrameM (fun q => Bem q || decide (q = 215064) || decide (q = 215065)) d d' := by
  have e₁ := Exec.copyN (P := P) hw 215064 a
  have e₂ := Exec.copyN (P := P) e₁.wb_right 215065 b
  set d₁ : Config := { d with nreg := upd d.nreg 215064 (d.nreg a) } with hd₁
  set d₂ : Config := { d₁ with nreg := upd d₁.nreg 215065 (d₁.nreg b) } with hd₂
  have g : ∀ q, q ≠ 215064 → q ≠ 215065 → d₂.nreg q = d.nreg q := fun q h1 h2 => by
    simp_all
  have K₂ : Kst n li d₂ := ⟨by ram_grind,
    by ram_grind, by ram_grind,
    by ram_grind, by ram_grind,
    by ram_grind⟩
  have B₂ : Buf n T xs d₂ := ⟨hB.1, by ram_grind,
    by ram_grind, by ram_grind⟩
  have v64 : d₂.nreg 215064 = e := by
    simp_all
  have v65 : d₂.nreg 215065 = h := by
    simp_all
  have eb : Exec P W (block [.copyN 215064 a, .copyN 215065 b]) d d₂ 2 :=
    .seq e₁ (.seq e₂ (.skip e₂.wb_right))
  have fb : FrameM (fun q => decide (q = 215064) || decide (q = 215065)) d d₂ :=
    exec_frameM eb (by simp [wrM, block, wrOKM, SignK.wrOK])
  obtain ⟨d₃, k₃, e₃, hk₃, B₃, m₃, f₃⟩ := emitS_exec (P := P) d₂ e₂.wb_right K₂ v64 v65 B₂
    hW1 hW2 hW3
  refine ⟨d₃, 2 + k₃, .seq eb e₃, by omega, B₃, fun x hx => by rw [m₃ x hx], ?_⟩
  exact (fb.mono fun q hq => by
      grind).trans
    (f₃.mono fun q hq => by simp_all)

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
      (∀ x, x < T + 3 * xs.length → d'.nmem x = d.nmem x) ∧ FrameM Bjun d d' := by
  obtain ⟨d₁, k₁, e₁, hk₁, v60, m₁⟩ : ∃ d₁ k₁, Exec P W (block [.subN 215060 215052 215048,
      .subN 215063 215048 215052, .addN 215060 215060 215063, .subN 215061 215053 215049,
      .subN 215063 215049 215053, .addN 215061 215061 215063, .addN 215060 215060 215061])
      d d₁ k₁ ∧ k₁ = 7 ∧
      d₁.nreg 215060 = p.edge - s.edge + (s.edge - p.edge) + (p.hgt - s.hgt + (s.hgt - p.hgt)) ∧
      d₁.nmem = d.nmem := by
    exec_block
    all_goals try (config_simp; (try simp only [h52, h53, h48, h49]); omega)
    refine ⟨rfl, ?_, rfl⟩
    config_simp; simp only [h52, h53, h48, h49]
  have f₁ : FrameM (fun q => decide (q = 215060) || decide (q = 215061) || decide (q = 215063))
    d d₁ := exec_frameM e₁ (by decide)
  have K₁ := hK.frame f₁ (by decide)
  have B₁ := hB.frame f₁ (by decide) m₁
  have F₁ : FrameM Bjun d d₁ := f₁.mono fun q hq => by
    simp only [Bjun, Bem, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢; omega
  by_cases hps : p = s
  · have h0 : d₁.nreg 215060 = 0 := by rw [v60, hps]; omega
    refine ⟨d₁, 7 + (0 + 1), (Exec.seq e₁ (.ifLtN_true (by rw [h0, K₁.one]; omega)
      (.skip e₁.wb_right))).cast (by omega), by omega, ?_, fun x _ => by rw [m₁], F₁⟩
    simp only [hps, ↓reduceIte, List.append_nil]; exact B₁
  · have hne := wpos_ne hps
    have h1 : 1 ≤ d₁.nreg 215060 := by rw [v60]; omega
    obtain ⟨d₂, k₂, e₂, hk₂, B₂, m₂, f₂⟩ := cpEm_exec (P := P) 215052 215053 (by decide) d₁
      e₁.wb_right K₁ (by rw [f₁.1 _ (by decide), h52]) (by rw [f₁.1 _ (by decide), h53]) B₁ hW1
      hW2 (by omega)
    refine ⟨d₂, k₁ + (k₂ + 2), .seq e₁ (.ifLtN_false (by rw [K₁.one]; omega) e₂), by omega, ?_,
      fun x hx => by rw [m₂ x hx, m₁], F₁.trans (f₂.mono fun q hq => ?_)⟩
    · simp only [hps, ↓reduceIte]; exact B₂
    · simp only [Bjun, Bool.or_eq_true, decide_eq_true_eq] at hq ⊢
      rcases hq with (h | h) | h
      · exact Or.inl h
      · right; omega
      · right; omega

theorem partner_bounds {n : ℕ} {N : NF} {r : ℕ} (hF : HFacts n N r) {x : WPos}
    (hx : x.edge < n) (hxh : x.hgt ≤ n) :
    (partner N r x).edge < n ∧ (partner N r x).hgt ≤ n := by
  rw [partner_eq]
  cases hf : (N.region r).chords.find? (pmatch N x) with
  | none => aesop
  | some i =>
    have hi := List.mem_of_find?_eq_some hf
    obtain ⟨-, hl, hr, hh⟩ := hF.hch i hi
    grind [resOf, CRec.lpos, CRec.rpos]

theorem sub_Bdyn {B : ℕ → Bool} (h : ∀ q, B q = true → q = 215011 ∨ q = 215012 ∨
    (215040 ≤ q ∧ q < 216000)) {c c' : Config} (hf : FrameM B c c') : FrameM Bdyn c c' :=
  hf.mono fun q hq => by
    core_grind

set_option maxHeartbeats 2000000 in
/-- **One iteration of the arc loop**: appends `arcIt li n N r t`. -/
theorem arcBody_exec (d : Config) (hw : WordsBounded W d) {n : ℕ} {N : NF} {r : ℕ} {li : Bool}
    {T t : ℕ} (hE : HEnv W n N r li T d) (h41 : d.nreg 215041 = t)
    (ht : t < (N.region r).arcs.length) (hB : Buf n T (pre li n N r t) d) :
    ∃ d' k, Exec P W arcBody d d' k ∧ k ≤ 300 ∧ d'.nreg 215041 = t + 1 ∧
      Buf n T (pre li n N r (t + 1)) d' ∧ (∀ a, a < T → d'.nmem a = d.nmem a) ∧
      FrameM Bdyn d d' := by
  have hmem : ∀ t', t' < (N.region r).arcs.length → (N.region r).arcs.getD t' 0 ∈ (N.region r).arcs :=
    fun t' h' => by simp_all
  set jp := (N.region r).arcs.getD t 0 with hjp
  set j := (N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0 with hj
  obtain ⟨-, -, -, hxe, hxh⟩ := hE.F.harc jp (hmem t ht)
  obtain ⟨-, hse, hsh, hee, heh⟩ := hE.F.harc j (hmem _ (Nat.mod_lt _ (by omega)))
  have hn := hE.hn
  have hT := hE.hT
  set xs := pre li n N r t with hxs
  have hxl : xs.length ≤ 4 * t := pre_length_le li n N r t
  have hxp : ptsLen n xs ≤ (n + 3) * t := ptsLen_pre_le li hE.hn0 N r t
  have hA5 := hE.F.hA
  have hxl' : xs.length ≤ 16 := by omega
  have hxp' : ptsLen n xs ≤ 4 * n + 12 := by
    have : (n + 3) * t ≤ (n + 3) * 4 := Nat.mul_le_mul_left _ (by omega)
    omega
  -- loading
  obtain ⟨d₁, k₁, e₁, hk₁, v46, v47, v48, v49, v50, v51, m₁, f₁⟩ := ldS_exec (P := P) d hw hE h41 ht
  have K₁ := hE.K.frame f₁ (by decide)
  have B₁ := hB.frame f₁ (by decide) m₁
  have g₁ : ∀ q, Bld q = false → d₁.nreg q = d.nreg q := f₁.1
  -- the partner
  obtain ⟨d₂, k₂, e₂, hk₂, v52, v53, m₂, f₂⟩ := partS_exec (P := P) d₁ e₁.wb_right K₁ hE.F v46 v47
    hxe hxh (by rw [g₁ _ (by decide), hE.kR])
    (fun v hv => by
      obtain ⟨a1, a2⟩ := hE.chs v hv
      rw [m₁, g₁ _ (by decide), g₁ _ (by decide)]; exact ⟨a1, by omega⟩)
    (fun i hi => by
      obtain ⟨a1, a2, a3, a4⟩ := hE.chR i hi
      rw [m₁, g₁ _ (by decide)]; exact ⟨a1, a2, a3, by omega⟩) (by omega)
  have K₂ := K₁.frame f₂ (by decide)
  have B₂ := B₁.frame f₂ (by decide) m₂
  have g₂ : ∀ q, Bpart q = false → d₂.nreg q = d₁.nreg q := f₂.1
  obtain ⟨hpe, hph⟩ := partner_bounds hE.F hxe hxh
  -- the junction
  obtain ⟨d₃, k₃, e₃, hk₃, B₃, m₃, f₃⟩ := junS_exec (P := P) d₂ e₂.wb_right K₂ v52 v53
    (by rw [g₂ _ (by decide), v48]) (by rw [g₂ _ (by decide), v49]) hpe hph hse hsh B₂
    (by omega) (by omega) (by omega)
  have K₃ := K₂.frame f₃ (by decide)
  have g₃ : ∀ q, Bjun q = false → d₃.nreg q = d₂.nreg q := f₃.1
  set ys := xs ++ (if partner N r (N.arc jp).e = (N.arc j).s then []
    else [ptI li n (partner N r (N.arc jp).e) false]) with hys
  have hyl : ys.length ≤ xs.length + 1 := by rw [hys, List.length_append]; split_ifs <;> simp
  have hyp : ptsLen n ys ≤ ptsLen n xs + 1 := by
    rw [hys, ptsLen_append]; split_ifs
    · simp [ptsLen_nil]
    · rw [ptI, ptsLen_pt]
  -- the start point
  obtain ⟨d₄, k₄, e₄, hk₄, B₄, m₄, f₄⟩ := cpEm_exec (P := P) 215048 215049 (by decide) d₃ (e := (N.arc j).s.edge) (h := (N.arc j).s.hgt)
    e₃.wb_right K₃ (by rw [g₃ _ (by decide), g₂ _ (by decide), v48])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), v49]) B₃ (by omega) (by omega) (by omega)
  have K₄ := K₃.frame f₄ (by decide)
  have g₄ : ∀ q, (Bem q || decide (q = 215064) || decide (q = 215065)) = false →
    d₄.nreg q = d₃.nreg q := f₄.1
  -- the run
  obtain ⟨d₅, k₅, e₅, hk₅, B₅, v72, m₅, f₅⟩ := runS_exec (P := P) (s := (N.arc j).s)
    (e := (N.arc j).e) d₄ e₄.wb_right K₄
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), v48])
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), v50])
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), v51]) hse hee B₄
    (by simp only [List.length_append, List.length_singleton]; omega)
    (by rw [ptsLen_append, ptE, ptsLen_pt]; omega) (by omega)
  have K₅ := K₄.frame f₅ (by decide)
  have g₅ : ∀ q, Brun q = false → d₅.nreg q = d₄.nreg q := f₅.1
  have hrl := runItems_length_le li n (N.arc j).s (N.arc j).e
  have hrp : ptsLen n (runItems li n (N.arc j).s (N.arc j).e) < n :=
    (ptsLen_runItems li hE.hn0 _ _).symm ▸ runCnt_lt li hE.hn0 _ _
  -- the end point
  obtain ⟨d₆, k₆, e₆, hk₆, B₆, m₆, f₆⟩ := cpEm_exec (P := P) 215072 215051 (by decide) d₅
    (e := if atVtx li n (N.arc j).e then ((N.arc j).e.edge + n - 1) % n else (N.arc j).e.edge)
    (h := (N.arc j).e.hgt)
    e₅.wb_right K₅ v72
    (by rw [g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), v51]) B₅
    (by simp only [List.length_append, List.length_singleton]; omega)
    (by simp only [ptsLen_append, ptE, ptsLen_pt]; omega)
    (by split_ifs <;> [have := Nat.mod_lt ((N.arc j).e.edge + n - 1) hE.hn0; skip] <;> omega)
  have K₆ := K₅.frame f₆ (by decide)
  have g₆ : ∀ q, (Bem q || decide (q = 215064) || decide (q = 215065)) = false →
    d₆.nreg q = d₅.nreg q := f₆.1
  -- the counter
  have r41 : d₆.nreg 215041 = t := by
    rw [g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide),
      g₁ _ (by decide), h41]
  have e₇ := Exec.addN (P := P) e₆.wb_right 215041 215041 215020 (by rw [r41, K₆.one]; omega)
  set d₇ : Config := { d₆ with nreg := upd d₆.nreg 215041 (d₆.nreg 215041 + d₆.nreg 215020) }
    with hd₇
  have f₇ : FrameM (fun q => decide (q = 215041)) d₆ d₇ :=
    exec_frameM e₇ (s := .instr (.addN 215041 215041 215020)) (by decide)
  have B₇ := B₆.frame f₇ (by decide) rfl
  refine ⟨d₇, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (1 + 0)))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.skip e₇.wb_right))))))),
    by omega, ?_, ?_, fun a ha => ?_, ?_⟩
  · simp only [hd₇, Programs.Config.nreg_mk, Machine.upd_same, r41, K₆.one]
  · have e : pre li n N r (t + 1) = ys ++ [ptE li n (N.arc j).s.edge (N.arc j).s.hgt] ++
        runItems li n (N.arc j).s (N.arc j).e ++
        [ptE li n (if atVtx li n (N.arc j).e then ((N.arc j).e.edge + n - 1) % n
          else (N.arc j).e.edge) (N.arc j).e.hgt] := by
      rw [pre_succ, hys]
      simp only [arcIt, arcItems, List.append_assoc]
      rfl
    rw [e]; exact B₇
  · show d₆.nmem a = d.nmem a
    rw [m₆ a (by simp only [List.length_append]; omega), m₅ a (by simp only [List.length_append]; omega),
      m₄ a (by omega), m₃ a (by omega), m₂, m₁]
  · refine ((((((sub_Bdyn ?_ f₁).trans (sub_Bdyn ?_ f₂)).trans (sub_Bdyn ?_ f₃)).trans
      (sub_Bdyn ?_ f₄)).trans (sub_Bdyn ?_ f₅)).trans (sub_Bdyn ?_ f₆)).trans (sub_Bdyn ?_ f₇) <;>
      intro q hq <;>
      simp only [Bld, Bpart, Bjun, Bem, Brun, Bool.or_eq_true, decide_eq_true_eq] at hq <;> omega

end exec

end

end DrvH

end Chazelle.Core
