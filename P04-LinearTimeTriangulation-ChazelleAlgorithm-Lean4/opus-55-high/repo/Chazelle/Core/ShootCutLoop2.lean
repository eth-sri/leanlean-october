module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.ShootCutGrade

namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
variable {U₀ n c : ℕ}
theorem Uof_mod (hn : 0 < n) (hc : c < n) : Uof U₀ n c % n = c := by
  unfold Uof
  zukaw
  rw [Nat.add_mod, Nat.mod_mod]
  by_cases h : c + n - U₀ % n < n
  · rw [Nat.mod_eq_of_lt h, show U₀ % n + zthgc = c + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hc]
  · rw [Nat.mod_eq_sub_mod (show n ≤ c + n - U₀ % n by omega),
      Nat.mod_eq_of_lt (show c + n - U₀ % n - n < n by omega),
      Nat.mod_eq_of_lt by_grind]
    omega
theorem Uof_lt (hn : 0 < n) : Uof U₀ n c < U₀ + n := by
  unfold Uof; have := Nat.mod_lt zthgc hn; omega

/-- The static facts of the main loop: the first and the final unwrapped positions are less
than a lap apart, the final vertex lies on the double boundary below the top, and every stretch
of the double boundary between them is at most `γ` long. -/
structure LStat (C : Chain) (U₀ F γ : ℕ) : Prop where
  hU₀F : U₀ ≤ F
  hUF : F < U₀ + ztz
  hF6 : 6 ≤ F % ztz
  hF5 : F % ztz ≤ 2 * C.m + 5
  hΓ : ∀ v L, U₀ ≤ v → v + L ≤ F → 6 ≤ v % ztz → v % ztz + L ≤ 2 * C.m + 6 →
    L ≤ γ

/-- **The invariant of the main loop.** -/
def LoopI (P : Polygon) (C : Chain) (H : Host) (Hh MD h γ mode : ℕ) (s e : WPos)
    (m₀ : ℕ → ℕ) (A₀ W : ℕ) (I : List Pc → Config → Prop) (ps₀ : List Pc) (U₀ F μ₀ : ℕ)
    (dI d : Config) : Prop :=
  WordsBounded W d ∧ CoreRegs P C H Hh MD h γ mode s e m₀ d ∧
    ztecz ∧
    (∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → r ≠ 150042 → d.nreg r = dI.nreg r) ∧
    6 ≤ d.nreg 150040 ∧ d.nreg 150040 ≤ 2 * C.m + 6 ∧
    Uof U₀ ztz ztgid ≤ F ∧
    d.nreg 150042 = (if Uof U₀ ztz ztgid < F then 1 else 0) ∧
    ∃ ps', UPath ztz U₀ ps' ztxdr ∧
      I ztcdl d ∧ (∀ pc ∈ ps', PcOK P C m₀ h γ pc) ∧
      ps'.length + 2 * ztir *
        mu C (Qof P).n H F ztxdr ≤
        2 * ztir * μ₀
variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

/-- The flag after a step to the unwrapped position `U'`. -/
theorem flag_of {n U' F : ℕ} (hn : 0 < n) (hU' : U' ≤ F) (hF : F < U' + n) :
    (if U' % n = F % n then 0 else 1) = (if U' < F then 1 else 0) := by
  by_cases h : U' < F
  · rw [ite_eq_right (resid_gap hn h hF).1, ite_eq_left h]
  grind

/-- **One iteration of the main loop.** -/
theorem loopBody_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztbwt I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos} {U₀ F μ₀ : ℕ} (L : LStat C U₀ F γ)
    (dI : Config) (h41 : dI.nreg 150041 = F % ztz) (d : Config)
    (hL : LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI d)
    (ht : d.nreg 150090 < d.nreg 150042) :
    ∃ d' k, Exec P W ztzsd d d' k ∧
      LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI d' ∧
      k ≤ ztlu * ztir + 1700 ∧
      mu C (Qof P).n H F (Uof U₀ ztz ztvog) <
        mu C (Qof P).n H F ztxdr := by
  obtain ⟨hw, R, hm, hkI, h6, h2m, hUF', h42, ps', hpath, hI, hok, hcnt⟩ := hL
  zulz
  zucmj
  set c := d.nreg 150040 with hc
  set U := Uof U₀ n c with hUdef
  have hU0 : U₀ ≤ U := by rw [hUdef]; unfold Uof; omega
  have hUlt : U < U₀ + n := Uof_lt hn0
  have hmod : U % n = c := Uof_mod hn0 by_omega
  have hUF : U < F := by
    grind
  have hFU := L.hUF
  have hFn : F < U + n := by_omega
  obtain ⟨hne, hgap⟩ := resid_gap hn0 hUF hFn
  rw [hmod] at hne hgap
  have hf41 : d.nreg 150041 = F % n := by_grind
  have hF6 := L.hF6
  have hF5 := L.hF5
  set f := F % n with hfdef
  have hG : 1 ≤ Nat.log 2 γ + 1 := by_omega
  have hW1 : ztbla := by have := S.hW; unfold hostWords at this; omega
  by_cases hc2 : d.nreg 150040 < d.nreg 150032
  · -- a step on the double boundary
    have hc' : c < 2 * C.m + 6 := by rw [R.h32] at hc2; omega
    have hlimF : U + limOf C c f ≤ F := by
      unfold limOf; split_ifs at hgap ⊢ <;> omega
    have hlimγ := L.hΓ U _ hU0 hlimF by_grind
      (by rw [← hn, hmod]; unfold limOf; split_ifs <;> omega)
    obtain ⟨d₁, k₁, Lc, ps'', ex₁, hk₁, post⟩ := cStep_exec S (hE.mono fun pc hp => hp.1) d hw R hm hc.symm hf41 h6 hc' hF5 hne hlimγ hI
    have hLlim := post.Llim
    have hL1 := post.L1
    have hcL : c + Lc ≤ 2 * C.m + 6 := by
      have : ztknm := by unfold limOf; split_ifs <;> omega
      omega
    obtain ⟨d₂, k₂, ex₂, hk₂, o42, r₂, m₂⟩ := setFlag_exec d₁ post.wb hW1
    have a40 : d₂.nreg 150040 = c + Lc := by rw [r₂ _ by_omega, post.r40]
    have hmod' : zthcz % n = c + Lc := by
      have := mod_shift (x := c + Lc) hmod by_omega by_omega
      rwa [show U + ztqgt = U + Lc by omega] at this
    have hU₀ : Uof U₀ n ztvpi = U + Lc := by
      zufmr
    have hU' : Uof U₀ ztz _ = U + Lc := hU₀
    have hkeep : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → r ≠ 150042 →
        d₂.nreg r = d.nreg r := fun r h1 h2 h3 h4 => by
      rw [r₂ r h4, post.keep r h1 h2 h3]
    have hμ : mu C (Qof P).n H F zthcz < mu C (Qof P).n H F U := by
      refine mu_lt by_omega by_omega ?_
      rcases post.brk with hb | hb | ⟨-, hb⟩
      · zujtj
        · rw [show limOf C c f = 2 * C.m + 6 - c by unfold limOf; rw [ite_eq_left hfc]] at hb
          right; right; unfold BrkU BrkRes; grind
        · rw [show limOf C c f = f - c by unfold limOf; rw [ite_eq_right hfc]] at hb
          rw [ite_eq_left by_grind] at hgap
          omega
      · zulw
        unfold BrkU BrkRes; zupbh
        rcases (show c + Lc = 2 * C.m + 6 ∨ c + Lc < 2 * C.m + 6 by omega) with h' | h'
        · omega
        · right; refine ⟨by_omega, h', ?_⟩
          rw [show c + Lc - 6 = c - 6 + Lc by omega]; exact hb
      · left
        unfold BrkU BrkRes; rw [hmod]
        grind
    have hpath' : UPath n U₀ (ps' ++ ps'') zthcz := by
      have := chained_upath post.ch (fun pc hp => (post.pv pc hp).2) by_omega U hmod
      rw [show U + ztqgt = U + Lc by omega] at this
      exact hpath.append ps'' this
    refine ⟨d₂, k₁ + 1 + k₂, .seq (.ifLtN_true hc2 ex₁) ex₂, ⟨ex₂.wb_right,
      R.of_frame' hkeep (by zundf; exact post.k90)
        (by zundf; exact post.k91) (by zundf; exact post.k92)
        (by zundf; exact post.k93) (by zundf; exact post.k96),
      fun a ha => by zunbg; exact post.mem a ha,
      fun r h1 h2 h3 h4 => (hkeep r h1 h2 h3 h4).trans by_grind,
      by omega, by_omega, by_omega, ?_,
      ps' ++ ps'', by_grind,
      hE.stable _ _ _ (by rw [← List.append_assoc]; exact post.hI) ztnya,
      fun pc hp => by
        zutk
        · grind
        · exact (post.pv pc hp).1, ?_⟩, by_omega, by_grind⟩
    · rw [o42, hU', post.r40, post.keep _ by_omega by_omega by_omega, hf41, ← hmod']
      exact flag_of hn0 by_omega by_omega
    · zuktf
      have hlen := post.len
      have hlog : Nat.log 2 Lc ≤ Nat.log 2 γ := Nat.log_mono_right by_omega
      have e1 : 2 * ztir * mu C (Qof P).n H F zthcz + 2 * ztir ≤
          2 * ztir * mu C (Qof P).n H F U := by
        have := Nat.mul_le_mul_left ztzss (show
          mu C (Qof P).n H F zthcz + 1 ≤ mu C (Qof P).n H F U by omega)
        omega
      omega
  · -- through the uncounted block
    have hc' : c = 2 * C.m + 6 := by rw [R.h32] at hc2; omega
    obtain ⟨d₁, k₁, ex₁, hk₁, hI₁, o40, kp, mem₁⟩ := uStep_exec hE
      d hw R.h32 R.chain.h96 hI (uPc_ok P C m₀ h γ)
    obtain ⟨d₂, k₂, ex₂, hk₂, o42, r₂, m₂⟩ := setFlag_exec d₁ ex₁.wb_right hW1
    have hmod' : ztjnj % n = 6 := by
      rw [add_mod_split hn0 by_omega, hmod, ite_eq_right by_omega]; omega
    have hF7 : U + 7 ≤ F := by
      grind
    have a40 : d₂.nreg 150040 = 6 := by rw [r₂ _ by_omega, o40]
    have hU₀ : Uof U₀ n ztvpi = U + 7 := by
      zufmr
    have hU' : Uof U₀ ztz _ = U + 7 := hU₀
    have hkeep : ∀ r, 150000 ≤ r → r < 150044 → r ≠ 150040 → r ≠ 150042 →
        d₂.nreg r = d.nreg r := fun r h1 h2 h3 h4 => by
      rw [r₂ r h4, kp r ztec h3]
    have kk : ∀ r, 150089 ≤ r → r < 150100 → d₂.nreg r = d.nreg r := fun r h1 h2 => by
      rw [r₂ r by_omega, kp r ztbh by_omega]
    have hμ : mu C (Qof P).n H F ztjnj < mu C (Qof P).n H F U := by
      refine mu_lt by_omega hF7 ztenp
      unfold BrkU BrkRes; grind
    have hKc : ztxit :=
      by grind
    have hpath' : UPath n U₀ _ _ :=
      hpath.append [uPc C.m] ⟨by rw [hmod, hc']; rfl, U + 7, by_omega, by zupbh; rfl, rfl⟩
    refine ⟨d₂, k₁ + 2 + k₂, .seq (.ifLtN_false hc2 ex₁) ex₂, ⟨ex₂.wb_right,
      R.of_frame' hkeep (by zunbi; grind)
        (by zunbi; exact R.chain.h91)
        (by zunbi; exact R.h92)
        (by zunbi; exact R.chain.h93)
        (by zunbi; exact R.chain.h96),
      fun a ha => by rw [m₂, mem₁ a ha]; grind,
      fun r h1 h2 h3 h4 => (hkeep r h1 h2 h3 h4).trans by_grind,
      by rw [a40], by_omega, by_omega, ?_,
      ps' ++ [uPc C.m], by_grind,
      hE.stable _ _ _ by_grind ztnya,
      fun pc hp => by
        zutk
        · grind
        · zvnns at hp; zvohk; exact uPc_ok P C m₀ h γ, ?_⟩,
      by omega, by_grind⟩
    · rw [o42, hU', o40, kp _ ztec by_omega, hf41, ← hmod']
      exact flag_of hn0 hF7 by_omega
    · zuktf
      have e1 : 2 * ztir * mu C (Qof P).n H F ztjnj + 2 * ztir ≤
          2 * ztir * mu C (Qof P).n H F U := by
        have := Nat.mul_le_mul_left ztzss (show
          mu C (Qof P).n H F ztjnj + 1 ≤ mu C (Qof P).n H F U by omega)
        omega
      zulak

/-- **The main loop**, from the first walk vertex (unwrapped `U₀`) to the final one (`F`). -/
theorem mainLoop_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztbwt I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos} {U₀ F μ₀ : ℕ} (L : LStat C U₀ F γ)
    (dI : Config) (h41 : dI.nreg 150041 = F % ztz) (d : Config)
    (hL : LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI d) :
    ∃ d' k, Exec P W ztvyq d d' k ∧
      LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI d' ∧
      Uof U₀ ztz ztvog = F ∧
      k ≤ ztxhl *
        mu C (Qof P).n H F ztxdr + 2 := by
  obtain ⟨d', k, ex, hL', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 150090) (b := 150042)
    (body := .seq ztejm setFlag)
    (LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ps₀ U₀ F μ₀ dI)
    (fun d => mu C (Qof P).n H F ztxdr)
    (ztlu * ztir + 1700) ztoe
    (fun d hd ht => loopBody_exec S hE L dI h41 d hd ht) hL
  refine ⟨d', k, ex, hL', ?_, hk⟩
  obtain ⟨-, R', -, -, -, -, hUF, h42, -⟩ := hL'
  rw [R'.h90, h42] at hx
  grind
end
end ShootCut
@[expose] public section
open Chazelle.Chain (sideInArc)
namespace ShootCut
theorem int01 {n x : ℝ} {m : ℤ} (hn : 0 < n) (hx0 : 0 ≤ x) (hxn : x < n) (h1 : 0 < x + m * n)
    (h2 : x + m * n < 2 * n) : m = 0 ∨ m = 1 := by
  have a1 : (m : ℝ) > -1 := by
    zubdi
  have a2 : (m : ℝ) < 2 := by
    zubdi
  have b1 : m > -1 := by exact_mod_cast a1
  have b2 : m < 2 := by exact_mod_cast a2
  omega

/-- **A key between two others in unwrapped order** (within one lap) lies in their cyclic
interval. -/
theorem sideInArc_unw {n a b x A B X : ℝ} (hn : 0 < n) (ha0 : 0 ≤ a) (han : a < n) (hb0 : 0 ≤ b)
    (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) (hA : ∃ i : ℤ, A = a + i * n)
    (hX : ∃ j : ℤ, X = x + j * n) (hB : ∃ k : ℤ, B = b + k * n) (h1 : A < X) (h2 : X < B)
    (h3 : B ≤ A + n) : sideInArc a b x := by
  obtain ⟨i, rfl⟩ := hA
  obtain ⟨j, rfl⟩ := hX
  obtain ⟨k, rfl⟩ := hB
  have hj : j - i = 0 ∨ j - i = 1 := int01 hn hx0 hxn by_grind
    by_grind
  have hk : k - i = 0 ∨ k - i = 1 := int01 hn hb0 hbn by_grind
    by_grind
  have ej : (j : ℝ) = i + (j - i : ℤ) := by_simp
  have ek : (k : ℝ) = i + (k - i : ℤ) := by_simp
  zufdq
  rcases hj with hj | hj <;> rcases hk with hk | hk <;> rw [hj] at ej <;> rw [hk] at ek <;>
    push_cast at ej ek <;> rw [ej] at h1 h2 <;> rw [ek] at h2 h3
  · simp_all
  · grind
  · grind
  grind
variable (M : Model) (Q : Polygon)

/-- The pieces go through increasing unwrapped keys. -/
def KPath (n : ℝ) : ℝ → List Pc → ℝ → Prop
  | V, [], V' => V = V'
  | V, pc :: ps, V' => (∃ i : ℤ, V = M.key Q pc.s + i * n) ∧
      ∃ V₁, V < V₁ ∧ (∃ j : ℤ, V₁ = M.key Q pc.e + j * n) ∧ KPath n V₁ ps V'
variable {M Q}
variable {n : ℝ}
theorem KPath.le : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ}, KPath M Q n V ps V' → V ≤ V'
  | _, [], _, h => le_of_eq h
  | _, _ :: _, _, ⟨_, _, h1, _, h2⟩ => le_trans h1.le h2.le
theorem KPath.lt {V V' : ℝ} {ps : List Pc} (h : KPath M Q n V ps V') (hne : ps ≠ []) :
    V < V' := by
  cases ps with
  | nil => exact absurd rfl hne
  | cons pc ps => obtain ⟨_, _, h1, _, h2⟩ := h; exact lt_of_lt_of_le h1 h2.le
theorem KPath.append : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ}, KPath M Q n V ps V' →
    ∀ (qs : List Pc) {V'' : ℝ}, KPath M Q n V' qs V'' → KPath M Q n V ztlrt V''
  | _, [], _, h, _, _, hq => by simp only [KPath] at h; simp_all
  | _, _ :: _, _, ⟨h1, V₁, h2, h3, h4⟩, qs, _, hq => ⟨h1, V₁, h2, h3, KPath.append h4 qs hq⟩

/-- The last end of a path is congruent to its end value. -/
theorem KPath.last : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ} (_ : KPath M Q n V ps V')
    (hne : ps ≠ []), ∃ j : ℤ, V' = M.key Q (ps.getLast hne).e + j * n
  | _, [pc], _, ⟨_, V₁, _, h3, h4⟩, _ => by simp only [KPath] at h4; simp_all
  | _, _ :: q :: qs, _, ⟨_, _, _, _, h4⟩, _ => by
    zulpe
    exact KPath.last h4 ztjjq

/-- **The tiling conjunct**: along a path of pieces within one lap, the end of every piece but
the last lies strictly inside the cyclic interval from its start to the final end. -/
theorem e6_of_kpath (hn : 0 < n) :
    ∀ {V : ℝ} {ps : List Pc} {T : ℝ} (_ : KPath M Q n V ps T) (_ : T ≤ V + n)
      (_ : ∀ pc ∈ ps, (0 ≤ M.key Q pc.s ∧ M.key Q pc.s < n) ∧ (0 ≤ M.key Q pc.e ∧ M.key Q pc.e < n))
      (hne : ps ≠ []),
      ∀ i, (hi : i + 1 < ps.length) →
        sideInArc (M.key Q (ps[i]' by_omega).s) (M.key Q (ps.getLast hne).e)
          (M.key Q (ps[i]' by_omega).e)
  | _, [], _, _, _, _, hne, _, _ => absurd rfl hne
  | V, pc :: ps, T, ⟨hs, V₁, hV, he, hp⟩, hT, hb, hne, i, hi => by
    have hne' : ztppl := by_grind
    have hlast : (pc :: ps).getLast hne = ps.getLast hne' := List.getLast_cons hne'
    zubuk
    · zulrs
      zumnl
      have hbp := hb pc by_simp
      have hbl := hb (ps.getLast hne') by_simp
      exact sideInArc_unw hn hbp.1.1 hbp.1.2 hbl.2.1 hbl.2.2 hbp.2.1 hbp.2.2 hs he
        (KPath.last hp hne') hV (hp.lt hne') hT
    · zulrr
      zumnl
      exact e6_of_kpath hn hp by_linarith (fun q hq => hb q by_simp_all) hne' i
        by_simp_all

/-- **A path of walk vertices** is a path of unwrapped keys. -/
theorem kpath_of_upath {n : ℕ} : ∀ {u : ℕ} {ps : List Pc} {u' : ℕ}, UPath n u ps u' →
    KPath M Q n (u : ℝ) ps (u' : ℝ)
  | _, [], _, h => by_tauto
  | u, pc :: ps, u', ⟨h1, u₁, h2, h3, h4⟩ => by
    have ek : ∀ v : ℕ, ((v % n : ℕ) : ℝ) + ((v / n : ℕ) : ℝ) * (n : ℝ) = (v : ℝ) := fun v => by
      have := Nat.mod_add_div v n
      exact_mod_cast (show v % n + v / n * n = v by zuodt; exact this)
    refine ⟨ztine, u₁, by_simp_all, ⟨((u₁ / n : ℕ) : ℤ), ?_⟩,
      kpath_of_upath h4⟩
    · rw [h1, key_hgt0, Int.cast_natCast]; simp_all
    · rw [h3, key_hgt0, Int.cast_natCast]; simp_all
end ShootCut
end
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
open Chazelle.Chain (sideE)
@[expose] public section
def Bvp : ℕ → Bool := Bl [150045, 150046, 150047, 150060, 150061, 150062, 150063, 150064,
  150065, 150066, 150067, 150068, 150069, 150073, 150074, 150075, 150077, 150078, 150079]
theorem wr_vtxPt : wr Bvp vtxPt = true := by_decide
variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

/-- A chain descriptor depends only on the memory below its end. -/
theorem chainDesc_agree' {m m' : ℕ → ℕ} {B E : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (h : ChainDescAt m B Q H C) (hB : B + 5 ≤ E) (hH : m B + 3 * H.length + 4 ≤ E)
    (hm : ∀ a, a < E → m' a = m a) : ChainDescAt m' B Q H C := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, h2, by_grind, by_grind,
    by grind, by_grind⟩
  zukuy
  exact hostAt_agree' h1 hH hm

/-- **The symbolic point of a walk vertex** of the double boundary. -/
theorem vtxPt_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) (d : Config) (hw : WordsBounded W d)
    (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (R : ChainRegs C (H.pts P.n).length Hh d)
    (h27 : d.nreg 150027 = P.n) (h92 : d.nreg 150092 = 2) {v : ℕ} (h44 : d.nreg 150044 = v)
    (hv6 : 6 ≤ v) (hv : v ≤ 2 * C.m + 6) :
    ∃ d' k sp, Exec P W vtxPt d d' k ∧ k ≤ 22 * H.length + 40 ∧ FrameB Bvp d d' ∧
      SymPtIn d' 150045 sp ∧ sp.Lt P.n ∧ sp.eval zta = (chainModel C).W.vtx v := by
  zueqp
  zucgk

  zudn

  zubnw
  zucwo

  have hH' := hostAt_agree' S.hH hHA by_omega
  obtain ⟨d₁, k₁, ex₁, hk₁, fr₁, o60, o61, o62, o63, o63', o64, found⟩ :=
    locV_exec (P := P) (W := W) (v := v) d hw rfl hH' R h44 hv6 hv hsN hmN by_omega by_omega
  zubfg

  have g₁ := fun x hx =>
    fr₁.1 x ztvfb
  zukdc
  have e67 : d₁.nreg 150067 = m₀ ztcln := by_grind
  have e68 : d₁.nreg 150068 = m₀ ztbyi := by_grind
  have e69 : d₁.nreg 150069 = m₀ ztclo := by_grind
  obtain ⟨hit, hc2⟩ := NFLoc.hostAt_item S.hH hr
  zuizi
  zukgs
  -- the walk vertex is the host point
  have hwalk : ∀ sp, ztbkj[u]? = some sp → sp.eval zta = (chainModel C).W.vtx v := by
    intro sp hsp
    have := walk_vtx C ztfvc by_omega
    rw [show v - 6 + 6 = v by omega] at this
    zubk
    refine (NFLoc.chain_vertex_host C S.hP _ ?_).symm
    rw [hQn, hN, show C.s + sideE C.m (tJ C _) = C.s + sideE C.m
      ztxfp from rfl, ← o64]
    omega
  have hpts :=
    NFLoc.pts_getElem? P.n H hr hp1 by_omega
  zugnx
  have b91 : ztutr := by zuoax
  have b92 : d₁.nreg 150092 = 2 := by rw [g₁ _ by_omega, h92]
  have b27 : d₁.nreg 150027 = P.n := by rw [g₁ _ by_omega, h27]
  have fin : ∀ (d₂ : Config) (k₂ : ℕ) (sp : SymPt), Exec P W (.ifLtN 150067 150091
      (.seq ztdeq
        (.seq (.ifLtN 150075 150027 ztigg
            ztgww)
          ztift))
      (.ifLtN 150067 150092 ztfbi
        ztdlp)) d₁ d₂ k₂ →
      k₂ ≤ 8 → SymPtIn d₂ 150045 sp → sp.Lt P.n → ztbkj[u]? = some sp →
      ∃ d' k sp, Exec P W vtxPt d d' k ∧ k ≤ 22 * H.length + 40 ∧ FrameB Bvp d d' ∧
        SymPtIn d' 150045 sp ∧ sp.Lt P.n ∧ sp.eval zta = (chainModel C).W.vtx v := by
    intro d₂ k₂ sp ex₂ hk₂ hin hlt hsp
    have ex : Exec P W vtxPt d d₂ ztbct := by unfold vtxPt; exact .seq ex₁ ex₂
    exact ⟨d₂, _, sp, ex, by_omega, exec_frameB ex wr_vtxPt, hin, hlt, hwalk sp hsp⟩
  by_cases hc0 : d₁.nreg 150067 < d₁.nreg 150091
  · -- a run
    have hk0 : ztbadd := by_omega
    zugyn

    have hrun : ztoql := by rw [hit, hk0]; rfl
    rw [hrun] at hwf hsucc hpts
    zubiq
    zueaw
    set t := u - NFLoc.preLen P.n H r
    have ht : t ≤ ℓ := by_omega
    obtain ⟨d₂, k₂, ex₂, hk₂, o45, o46⟩ : ∃ d₂ k₂, Exec P W
        (.seq ztdeq
          (.seq (.ifLtN 150075 150027 ztigg
              ztgww)
            ztift)) d₁ d₂ k₂ ∧ k₂ ≤ 5 ∧
        d₂.nreg 150045 = 0 ∧ d₂.nreg 150046 = ztne % P.n := by
      refine spec_seq (spec_instr (Exec.addN w₁ _ _ _ by_omega) fun w' => ?_)
      by_cases hlt : a + t < P.n
      · refine spec_seq (spec_ifLtN_true (by config_simp; omega)
          (spec_instr ztlej fun w'' => ?_))
        refine spec_instr (Exec.constN w'' _ _ by_omega) fun _ => ⟨by_omega, by config_simp, ?_⟩
        config_simp; rw [e68, h66, Nat.mod_eq_of_lt hlt]
      · refine spec_seq (spec_ifLtN_false (by config_simp; omega)
          (spec_instr ztemo fun w'' => ?_))
        refine spec_instr (Exec.constN w'' _ _ by_omega) fun _ => ⟨by_omega, by config_simp, ?_⟩
        config_simp
        rw [e68, h66, b27, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]
    exact fin d₂ _ zteke (.ifLtN_true hc0 ex₂) by_omega ztujb
      ztcv (by rw [hpts, NFLoc.run_pts_getElem? _ _ _ ht])
  · have hk1 : 1 ≤ m₀ ztcln := by_omega
    rcases hH : H[r] with ⟨a, ℓ⟩ | x
    · exfalso; rw [hit] at hH; unfold NFLoc.itemOf at hH; zvmyd at hH
      split_ifs at hH
    rw [hH] at hwf hsucc hpts
    zubiq
    have ht0 : u - NFLoc.preLen P.n H r = 0 := by_omega
    rw [ht0] at hpts
    have hsp : ztbkj[u]? = some x := by zuowr; rfl
    by_cases hc1 : d₁.nreg 150067 < d₁.nreg 150092
    · have hx : x = .vtx ztbaik := by
        zugdx
        rw [ite_eq_right by_omega, ite_eq_left by_omega] at hH
        grind
      obtain ⟨d₂, k₂, ex₂, hk₂, o45, o46⟩ : ∃ d₂ k₂, Exec P W
          ztfbi d₁ d₂ k₂ ∧ k₂ = 2 ∧
          d₂.nreg 150045 = 0 ∧ d₂.nreg 150046 = m₀ _ := by
        exec_block
        all_goals first | omega | skip
        exact ⟨rfl, by config_simp, by config_simp; omega⟩
      zujjz
      exact fin d₂ _ zteke (.ifLtN_false hc0 (.ifLtN_true hc1 ex₂))
        by_omega ztujb hwf hsp
    · have hx : x = .onEdge ztbaik (m₀ ztclo) := by
        zugdx
        zvmyn at hH
        grind
      obtain ⟨d₂, k₂, ex₂, hk₂, o45, o46, o47⟩ : ∃ d₂ k₂, Exec P W
          ztdlp d₁ d₂ k₂ ∧
          k₂ = 3 ∧ d₂.nreg 150045 = 1 ∧ d₂.nreg 150046 = m₀ _ ∧
          d₂.nreg 150047 = m₀ _ := by
        exec_block
        all_goals first | omega | skip
        exact ⟨rfl, by config_simp, by config_simp; omega, by config_simp; omega⟩
      zujjz
      exact fin d₂ _ (.onEdge _ _)
        (.ifLtN_false hc0 (.ifLtN_false hc1 ex₂)) by_omega ⟨o45, o46, o47⟩ hwf hsp
theorem wr_posP : wr Scr posP = true := by_decide
theorem wr_keyLess : wr Scr keyLess = true := by_decide

/-- **The direction code of a walk edge** into `150059`. -/
theorem dirP_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ} (hD : ChainDescAt m₀ ztki zta H C)
    (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh) (d : Config) (hw : WordsBounded W d)
    (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (h00 : d.nreg 150000 = MD) {p : ℕ}
    (h49 : d.nreg 150049 = p) (hp : p < 2 * C.m + 7) :
    ∃ d' k, Exec P W dirP d d' k ∧ k ≤ 70 * H.length + 610 ∧
      d'.nreg 150059 = NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2 ∧
      (∀ r, (r < 150059 ∨ 150060 ≤ r) → Bdir r = false → r ≠ 50000 → r ≠ 50002 →
        d'.nreg r = d.nreg r) ∧ d'.nmem = d.nmem := by
  zudn

  zucgk

  obtain ⟨d₁, k₁, e₁, hk₁, o0, o2, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
      ztksd d d₁ k₁ ∧ k₁ = 2 ∧
      d₁.nreg 50000 = MD ∧ d₁.nreg 50002 = p ∧
      (∀ r, r ≠ 50000 → r ≠ 50002 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem := by
    exec_block
    simp_all
  have hC : ChainDescAt d₁.nmem (d₁.nreg 50000 + 1) zta H C := by
    rw [o0, m₁]
    exact chainDesc_agree' hD by_omega (by zupbc; exact le_trans S.hHA le_rfl)
      by_omega
  obtain ⟨d₂, k₂, e₂, hk₂, fr₂, o₂⟩ := NFLoc.chainDir_exec (P := P) S.hG by_omega d₁ e₁.wb_right
    hC (by zuntr; have := S.hAW; omega)
    (by rw [o0, m₁, hm _ by_omega, hHh]; have := S.hHA; have := S.hAW; omega) S.hwf S.hs
    by_omega by_omega
  have e₃ := Exec.copyN (P := P) e₂.wb_right 150059 10502
  refine ⟨_, k₁ + ztcaj, .seq e₁ ztcr, by_omega, ?_,
    fun r h1 h2 h3 h4 => ?_, ?_⟩
  · config_simp; rw [o₂, o2]; rfl
  · config_simp
    rw [upd_other _ _ _ by_omega, fr₂.1 r h2, r₁ r h3 h4]
  · config_simp; zunqi
theorem dirOf_eq_zero {a b : ℝ} : NFLoc.dirOf a b = 0 ↔ a = b := by
  unfold NFLoc.dirOf
  grind

/-- **Is the parameter of the position `⟨p, j + 1⟩` positive?** (`6 ≤ p ≤ 2m + 6`): `150089`
is `1` iff the walk edge is not horizontal and the height of `Q.vtx j` differs from the height of
the start of the edge. -/
theorem posP_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ}
    (hD : ChainDescAt m₀ ztki zta H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : ChainRegs C (H.pts P.n).length Hh d) (h00 : d.nreg 150000 = MD)
    (h27 : d.nreg 150027 = P.n) (h90 : d.nreg 150090 = 0) (h92 : d.nreg 150092 = 2) {p j : ℕ}
    (h49 : d.nreg 150049 = p) (h76 : d.nreg 150076 = j) (hp6 : 6 ≤ p) (hp : p ≤ 2 * C.m + 6)
    (hj : j < P.n) :
    ∃ d' k, Exec P W posP d d' k ∧ k ≤ 100 * H.length + 2000 ∧ FrameB Scr d d' ∧
      (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
        ((chainModel C).W.vtx p).2 ≠ ((Qof P).vtx j).2)) ∧ d'.nreg 150089 ≤ 1 := by
  zudn

  obtain ⟨d₁, k₁, ex₁, hk₁, o59, r₁, m₁⟩ := dirP_exec S hD hMD hHh d hw hm h00 h49 by_omega
  have g₁ : ztfxi :=
    fun r h1 h2 h3 => r₁ r by_omega ztqfs by_omega by_omega
  zugnx
  have hfin : ∀ (d' : Config) (k : ℕ), Exec P W posP d d' k → k ≤ 100 * H.length + 2000 →
      (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
        ((chainModel C).W.vtx p).2 ≠ ((Qof P).vtx j).2)) → d'.nreg 150089 ≤ 1 →
      ∃ d' k, Exec P W posP d d' k ∧ k ≤ 100 * H.length + 2000 ∧ FrameB Scr d d' ∧
        (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
          ((chainModel C).W.vtx p).2 ≠ ((Qof P).vtx j).2)) ∧ d'.nreg 150089 ≤ 1 :=
    fun d' k ex hk h1 h2 => ⟨d', k, ex, hk, exec_frameB ex wr_posP, h1, h2⟩
  zuhst
  · have hz : NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2 = 0 := by
      zudtx
    zueps
    refine hfin _ _ (by unfold posP; exact .seq ex₁ ztspj) by_omega ?_
      by_simp
    config_simp
    rw [dirOf_eq_zero] at hz
    grind
  · have hnz : NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2 ≠ 0 := by
      zudtx
    rw [Ne, dirOf_eq_zero] at hnz
    have e₂ := Exec.copyN (P := P) w₁ 150044 150049
    set d₂ := ({ d₁ with nreg := upd d₁.nreg 150044 _ } : Config) with hd₂
    have g₂ : ∀ r, 150000 ≤ r → r < 150100 → r ≠ 150059 → r ≠ 150044 → d₂.nreg r = d.nreg r :=
      fun r h1 h2 h3 h4 => by simp only [hd₂, upd]; grind
    have R₂ := R.of_frame fun r hr => g₂ r (by
      zvmxh at hr; omega) (by
      zvmxh at hr; omega) (by
      zvmxh at hr; omega) (by
      zvmxh at hr; omega)
    obtain ⟨d₃, k₃, sp, ex₃, hk₃, fr₃, in₃, lt₃, ev₃⟩ := vtxPt_exec S d₂ e₂.wb_right
      ztxl R₂
      by_grind
      by_grind
      (by simp [hd₂, upd]; grind) hp6 hp
    have g₃ := fr₃.1
    have b76 : d₃.nreg 150076 = j := by
      rw [g₃ _ by_decide, g₂ _ by_omega by_omega by_omega by_omega, h76]
    have b90 : d₃.nreg 150090 = 0 := by
      rw [g₃ _ by_decide, g₂ _ by_omega by_omega by_omega by_omega, h90]
    obtain ⟨d₄, k₄, ex₄, hk₄, a₄, b₄, r₄⟩ : ∃ d₄ k₄, Exec P W
        (block [.copyN 50040 150045, .copyN 50041 150046, .copyN 50042 150047, .constN 50043 0,
          .copyN 50044 150076]) d₃ d₄ k₄ ∧ k₄ = 5 ∧ SymPtIn d₄ 50040 sp ∧
        SymPtIn d₄ 50043 ztmae ∧ d₄.nreg 150090 = 0 := by
      zumfz
      exec_block
      all_goals first | omega | skip
      exact ⟨rfl, NFLoc.symPtIn_copy in₃ (by config_simp) (by config_simp) (by config_simp),
        ⟨by config_simp, by config_simp; omega⟩, by config_simp; omega⟩
    obtain ⟨d₅, k₅, ex₅, hk₅, fr₅, o₅⟩ := NFLoc.dirTail_exec S.hG by_omega d₄
      ex₄.wb_right lt₃ (show (SymPt.vtx j).Lt P.n from hj) a₄ b₄
    have e₆ := Exec.copyN (P := P) ex₅.wb_right 150089 10502
    set d₆ := ({ d₅ with nreg := upd d₅.nreg 150089 _ } : Config) with hd₆
    have o89 : d₆.nreg 150089 = NFLoc.dirOf ((chainModel C).W.vtx p).2 ((Qof P).vtx j).2 := by
      zuntq; rw [o₅, ev₃]; rfl
    have c90 : d₆.nreg 150090 = 0 := by
      zuogd; rw [ite_eq_right by_omega, fr₅.1 _ by_decide, r₄]
    zujb
    have ex_pre : ∀ (d₇ : Config) (k₇ : ℕ), Exec P W
        ztyzt d₆ d₇ k₇ →
        Exec P W posP d d₇ (k₁ + (1 + (k₃ + (ztzwt + k₇)) + 2)) := by
      intro d₇ k₇ e₇
      unfold posP hcmp
      exact .seq ex₁ (.ifLtN_false h59 (.seq e₂ (.seq ex₃ (.seq (.seq ex₄ (.seq ex₅ e₆)) e₇))))
    by_cases hy : ((chainModel C).W.vtx p).2 = ((Qof P).vtx j).2
    · have hz : d₆.nreg 150089 = 0 := by rw [o89, dirOf_eq_zero]; exact hy
      have ht : ¬ d₆.nreg 150090 < d₆.nreg 150089 := by_omega
      refine hfin d₆ _ (ex_pre d₆ 2 (.ifLtN_false ht (.skip w₆))) by_omega
        ?_ by_omega
      grind
    · have hz : d₆.nreg 150089 ≠ 0 := by rw [o89, Ne, dirOf_eq_zero]; exact hy
      have ht : d₆.nreg 150090 < d₆.nreg 150089 := by_omega
      have e₇ := Exec.constN (P := P) w₆ 150089 1 by_omega
      refine hfin _ _ (ex_pre _ 2 (.ifLtN_true ht e₇)) by_omega ?_
        by_simp
      config_simp
      grind

/-- **Is the start before the end** (both on the walk edge `p`, height codes `h₁, h₂ ≥ 1`)?
`150089` is `1` iff the edge is not horizontal and the heights of `Q.vtx (h₁ - 1)` and
`Q.vtx (h₂ - 1)` are in the order of the edge. -/
theorem keyLess_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ}
    (hD : ChainDescAt m₀ ztki zta H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (h00 : d.nreg 150000 = MD) (h91 : d.nreg 150091 = 1) {p h₁ h₂ : ℕ}
    (h49 : d.nreg 150049 = p) (h02 : d.nreg 150002 = h₁) (h04 : d.nreg 150004 = h₂)
    (hp : p < 2 * C.m + 7) (hh₁ : 1 ≤ h₁) (hh₁' : h₁ ≤ P.n) (hh₂ : 1 ≤ h₂) (hh₂' : h₂ ≤ P.n) :
    ∃ d' k, Exec P W keyLess d d' k ∧ k ≤ 100 * H.length + 2000 ∧ FrameB Scr d d' ∧
      (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
        NFLoc.dirOf ((Qof P).vtx ztjyg).2 ((Qof P).vtx ztfsn).2 =
          NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2)) ∧
      d'.nreg 150089 ≤ 1 := by
  zudn

  obtain ⟨d₁, k₁, ex₁, hk₁, o59, r₁, m₁⟩ := dirP_exec S hD hMD hHh d hw hm h00 h49 hp
  have g₁ : ztfxi :=
    fun r h1 h2 h3 => r₁ r by_omega ztqfs by_omega by_omega
  zugnx
  set D := NFLoc.dirOf ((chainModel C).wa p).2 ((chainModel C).wb p).2 with hDdef
  have hfin : ∀ (d' : Config) (k : ℕ), Exec P W keyLess d d' k → k ≤ 100 * H.length + 2000 →
      (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
        NFLoc.dirOf ((Qof P).vtx _).2 ((Qof P).vtx _).2 = D)) →
      d'.nreg 150089 ≤ 1 →
      ∃ d' k, Exec P W keyLess d d' k ∧ k ≤ 100 * H.length + 2000 ∧ FrameB Scr d d' ∧
        (d'.nreg 150089 = 1 ↔ (((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 ∧
          NFLoc.dirOf ((Qof P).vtx ztjyg).2 ((Qof P).vtx ztfsn).2 = D)) ∧
        d'.nreg 150089 ≤ 1 :=
    fun d' k ex hk h1 h2 => ⟨d', k, ex, hk, exec_frameB ex wr_keyLess, h1, h2⟩
  have b91 : ztutr := by_grind
  zuhst
  · have hz : D = 0 := by_omega
    zueps
    refine hfin _ _ (by unfold keyLess; exact .seq ex₁ ztspj) by_omega ?_
      by_simp
    config_simp
    rw [hDdef, dirOf_eq_zero] at hz
    grind
  · have hnz : D ≠ 0 := by_omega
    have hnz' := hnz
    rw [hDdef, Ne, dirOf_eq_zero] at hnz'
    obtain ⟨d₂, k₂, ex₂, hk₂, a₂, b₂, c₂⟩ : ∃ d₂ k₂, Exec P W (block [.constN 50040 0,
        .subN 50041 150002 150091, .constN 50043 0, .subN 50044 150004 150091]) d₁ d₂ k₂ ∧
        k₂ = 4 ∧ SymPtIn d₂ 50040 (.vtx ztjyg) ∧ SymPtIn d₂ 50043 ztzao ∧
        d₂.nreg 150059 = D := by
      exec_block
      all_goals first | omega | skip
      refine ⟨rfl, ⟨by config_simp, ?_⟩, ⟨by config_simp, ?_⟩, by config_simp; omega⟩
      · config_simp; grind
      · config_simp; grind
    obtain ⟨d₃, k₃, ex₃, hk₃, fr₃, o₃⟩ := NFLoc.dirTail_exec S.hG by_omega d₂
      ex₂.wb_right (show (SymPt.vtx _).Lt P.n from by show h₁ - 1 < P.n; omega)
      (show (SymPt.vtx _).Lt P.n from by show h₂ - 1 < P.n; omega) a₂ b₂
    have c59 : d₃.nreg 150059 = D := by rw [fr₃.1 _ by_decide, c₂]
    zumfz
    set E := NFLoc.dirOf ((Qof P).vtx _).2 ((Qof P).vtx _).2 with hE
    have o10 : d₃.nreg 10502 = E := o₃
    have pre : ∀ (d₄ : Config) (k₄ : ℕ), Exec P W (.ifLtN 10502 150059
        ztcym (.ifLtN 150059 10502 ztcym
          ztfeo)) d₃ d₄ k₄ →
        Exec P W keyLess d d₄ (k₁ + (zttk + 2)) := by
      intro d₄ k₄ e₄
      unfold keyLess
      exact .seq ex₁ (.ifLtN_false h59 (.seq ex₂ (.seq ex₃ e₄)))
    by_cases hlt : d₃.nreg 10502 < d₃.nreg 150059
    · zuepv
      refine hfin _ _ (pre _ _ (.ifLtN_true hlt e₄)) by_omega ?_
        by_simp
      config_simp
      grind
    · by_cases hgt : d₃.nreg 150059 < d₃.nreg 10502
      · zuepv
        refine hfin _ _ (pre _ _ (.ifLtN_false hlt (.ifLtN_true hgt e₄)))
          by_omega ?_ by_simp
        config_simp
        grind
      · have e₄ := Exec.constN (P := P) w₃ 150089 1 by_omega
        refine hfin _ _ (pre _ _ (.ifLtN_false hlt (.ifLtN_false hgt e₄)))
          by_omega ?_ by_simp
        config_simp
        grind
end
end ShootCut
@[expose] public section
namespace ShootCut
theorem param_succ (M : Model) (Q : Polygon) (p j : ℕ) :
    M.param Q ztcyf = if (M.wa p).2 = (M.wb p).2 then 0
      else ((Q.vtx j).2 - (M.wa p).2) / ztcrr := rfl

/-- **A positive parameter** (`posP`). -/
theorem param_pos_iff (M : Model) (Q : Polygon) {n p j : ℕ} (hx : ProperPos M Q n ztcyf) :
    0 < M.param Q ztcyf ↔ ((M.wa p).2 ≠ (M.wb p).2 ∧ (M.W.vtx p).2 ≠ (Q.vtx j).2) := by
  have h0 := hx.1
  rw [param_succ] at h0 ⊢
  constructor
  · zuq
    zuefh
    · simp_all
    · refine ⟨hh, fun hy => ?_⟩
      rw [ite_eq_right hh] at h
      have : (Q.vtx j).2 - (M.wa p).2 = 0 := by
        show (Q.vtx j).2 - (M.W.vtx p).2 = 0; simp_all
      simp_all
  · rintro ⟨hh, hy⟩
    rw [ite_eq_right hh] at h0 ⊢
    positivity

/-- **Two positions of one edge in key order** (`keyLess`). -/
theorem key_lt_iff (M : Model) (Q : Polygon) {p h₁ h₂ : ℕ} (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂) :
    M.key Q ztujd < M.key Q ztkmi ↔ ((M.wa p).2 ≠ (M.wb p).2 ∧
      NFLoc.dirOf (Q.vtx ztjyg).2 (Q.vtx ztfsn).2 = NFLoc.dirOf (M.wa p).2 (M.wb p).2) := by
  obtain ⟨a, rfl⟩ : ∃ a, h₁ = a + 1 := ztklx
  obtain ⟨b, rfl⟩ : ∃ b, h₂ = b + 1 := ⟨h₂ - 1, by_omega⟩
  zudli
  zuhqn
  simp only [param_succ]
  set A := (M.wa p).2
  set B := (M.wb p).2
  set y₁ := (Q.vtx a).2
  set y₂ := (Q.vtx b).2
  by_cases hh : A = B
  · simp_all
  · rw [ite_eq_right hh, ite_eq_right hh]
    unfold NFLoc.dirOf
    rcases lt_or_gt_of_ne hh with hAB | hAB
    · have hd : 0 < B - A := by_linarith
      rw [ite_eq_left hAB, add_lt_add_iff_left, div_lt_div_iff_of_pos_right hd]
      grind
    · have hd : B - A < 0 := by_linarith
      rw [ite_eq_right (not_lt.2 hAB.le), ite_eq_left hAB, add_lt_add_iff_left,
        div_lt_div_right_of_neg hd]
      grind
variable (C : Chain) (Q : Polygon)
variable {q : ℕ}
theorem walk_vtx_box (hq : q ≤ 5) :
    ((chainModel C).W.vtx q).2 = C.radius ∨ ((chainModel C).W.vtx q).2 = -C.radius := by
  show ((C.sideWalk C.sideBeta).vtx q).2 = C.radius ∨ ((C.sideWalk C.sideBeta).vtx q).2 = -C.radius
  interval_cases q
  · tauto
  · tauto
  · tauto
  · tauto
  · tauto
  tauto

/-- **All walk heights lie in `[-R, R]`.** -/
theorem walk_y_bounds (hq : q < 2 * C.m + 7) :
    -C.radius ≤ ((chainModel C).W.vtx q).2 ∧ ((chainModel C).W.vtx q).2 ≤ C.radius := by
  zubo
  zuknh
  · rcases walk_vtx_box C h with e | e <;> zvmwe <;> constructor <;> linarith
  · zubpf
    show -C.radius ≤ ((C.sideWalk C.sideBeta).vtx ztcy).2 ∧
      ((C.sideWalk C.sideBeta).vtx ztcy).2 ≤ C.radius
    zudth
    zuljn
    have := abs_lt.1 hb.2
    unfold Chazelle.Chain.sideTour
    grind

/-- The box edges `0, 2, 4` are horizontal. -/
theorem box_horizontal {p : ℕ} (hp : p = 0 ∨ p = 2 ∨ p = 4) :
    ((chainModel C).wa p).2 = ((chainModel C).wb p).2 := by
  zubgg
  zujqa
  zubdb
  show ((C.sideWalk C.sideBeta).vtx p).2 = ((C.sideWalk C.sideBeta).vtx (ztr % ztz)).2
  zuebt
  · rfl
  · rfl
  rfl

/-- **An inner position on the box edges `1, 3, 5`** has a positive parameter. -/
theorem box_param_pos {n p j : ℕ} (hp : p = 1 ∨ p = 3 ∨ p = 5)
    (hx : ProperPos ztc Q n ztcyf)
    (hin : (chainModel C).InnerPt ((chainModel C).pos Q ztcyf)) :
    0 < (chainModel C).param Q ztcyf := by
  zubo
  zubgg
  zubt
  have hwa : (chainModel C).wa p = (C.sideWalk C.sideBeta).vtx p := rfl
  have hwb : (chainModel C).wb p = (C.sideWalk C.sideBeta).vtx ztr := by
    unfold Model.wb; rw [hn, Nat.mod_eq_of_lt by_omega]; rfl
  -- the edge is not horizontal
  have hnh : ((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2 := by
    zucpy
    zuebt
    · rw [C.sideWalk_vtx_one, C.sideWalk_vtx_two]; grind
    · rw [C.sideWalk_vtx_three, C.sideWalk_vtx_four]; grind
    · rw [C.sideWalk_vtx_five, show (5 + 1 : ℕ) = 0 + 6 from rfl,
        C.sideWalk_vtx_tour _ by_omega, C.sideTour_zero]
      have := C.top_snd_lt_radius
      intro h; rw [Chazelle.Chain.slitTop_snd] at h; linarith
  -- the point of the position is at the height of `Q.vtx j`
  have hpos : ((chainModel C).pos Q ztcyf).2 = (Q.vtx j).2 := by
    zueew
    rw [Geometry.lerp_snd, param_succ, ite_eq_right hnh]
    grind
  obtain ⟨⟨q, q', hq, hq', hlo, hhi⟩, -⟩ := hin
  zvnbl at hlo hhi
  zvmxq at hq hq'
  have b1 := walk_y_bounds C hq
  have b2 := walk_y_bounds C hq'
  refine (param_pos_iff _ Q hx).2 ⟨hnh, ?_⟩
  show ((C.sideWalk C.sideBeta).vtx p).2 ≠ (Q.vtx j).2
  zuebt
  · zugbq
  · zugbr
  · rw [C.sideWalk_vtx_five, Chazelle.Chain.slitTop_snd]; grind
end ShootCut
end
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
def Bd (r : ℕ) : Bool :=
  decide (150044 ≤ r ∧ r < 150090) || decide ztdew ||
    decide ztdfc
theorem wr_decideS : wr Bd decideS = true := by_decide
theorem FrameB.mono' {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B' r = false → B r = false) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r by_simp_all, fun r hr => h.2.1 r by_simp_all, h.2.2⟩
variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

/-- **The box edges.** -/
theorem decBox_exec {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d) {p : ℕ}
    (h01 : d.nreg 150001 = p) (hp : p < 6) (h48 : d.nreg 150048 = 0) (h91 : d.nreg 150091 = 1)
    (h92 : d.nreg 150092 = 2) (h93 : d.nreg 150093 = 3) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W decBox d d' k ∧ k ≤ 12 ∧ (d'.nreg 150048 = 1 ↔ (p = 1 ∨ p = 3 ∨ p = 5)) ∧
      d'.nreg 150048 ≤ 1 ∧ (∀ x, x ≠ 150048 → x ≠ 150075 → d'.nreg x = d.nreg x) ∧
      d'.nmem = d.nmem := by
  unfold decBox
  interval_cases p
  · refine spec_ifLtN_true by_omega (spec_skip hw ⟨by_omega, ?_, by_omega,
      by omega, rfl⟩)
    omega
  · refine spec_ifLtN_false by_omega (spec_ifLtN_true by_omega
      (spec_instr ztcsz by_simp_all))
  · refine spec_ifLtN_false by_omega (spec_ifLtN_false by_omega
      (spec_ifLtN_true by_omega (spec_skip hw ⟨by_omega, ?_, by_omega,
        by omega, rfl⟩)))
    omega
  · refine spec_ifLtN_false by_omega (spec_ifLtN_false by_omega
      (spec_ifLtN_false by_omega (spec_seq (spec_instr ztbbq
        fun w₁ => spec_ifLtN_true by_simp_all (spec_instr
          ztgdo by_simp_all)))))
  · refine spec_ifLtN_false by_omega (spec_ifLtN_false by_omega
      (spec_ifLtN_false by_omega (spec_seq (spec_instr ztbbq
        fun w₁ => spec_ifLtN_false by_simp_all
          (spec_ifLtN_true by_simp_all (spec_skip w₁
            ⟨by_omega, ?_, ?_, by_simp_all, rfl⟩))))))
    · simp_all
    simp_all
  · refine spec_ifLtN_false by_omega (spec_ifLtN_false by_omega
      (spec_ifLtN_false by_omega (spec_seq (spec_instr ztbbq
        fun w₁ => spec_ifLtN_false by_simp_all
          (spec_ifLtN_false by_simp_all (spec_instr
            ztgdo by_simp_all))))))

/-- **The start at a vertex**: is the parameter of the end `⟨p, hh⟩` positive? -/
theorem decVtx_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ}
    (hD : ChainDescAt m₀ ztki zta H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : ChainRegs C (H.pts P.n).length Hh d) (h00 : d.nreg 150000 = MD)
    (h27 : d.nreg 150027 = P.n) (h48 : d.nreg 150048 = 0) (h90 : d.nreg 150090 = 0)
    (h92 : d.nreg 150092 = 2) {p hh : ℕ} (h01 : d.nreg 150001 = p) (h04 : d.nreg 150004 = hh)
    (hp : p < 2 * C.m + 7) (hh1 : 1 ≤ hh) (hhn : hh ≤ P.n)
    (hx : ProperPos ztc zta P.n ztopa)
    (hin : (chainModel C).InnerPt ((chainModel C).pos zta ztopa)) :
    ∃ d' k, Exec P W decVtx d d' k ∧ k ≤ 100 * H.length + 2050 ∧
      (d'.nreg 150048 = 1 ↔ 0 < (chainModel C).param zta ztopa) ∧ d'.nreg 150048 ≤ 1 := by
  zudn

  obtain ⟨j, rfl⟩ : ∃ j, hh = j + 1 := ⟨hh - 1, by_omega⟩
  unfold decVtx
  zufrf
  · obtain ⟨d', k, ex, hk, h1, h2, -, -⟩ := decBox_exec d hw h01 hp6 h48 R.h91 h92 R.h93
      by_omega
    refine ⟨d', _, .ifLtN_true (by zuonk; omega) ex, by_omega, ?_, h2⟩
    zuwv
    constructor
    · intro hb; exact box_param_pos C _ hb hx hin
    · zulmx
      zuldq
      have hb' : p = 0 ∨ p = 2 ∨ p = 4 := by_omega
      rw [param_succ, ite_eq_left (box_horizontal C hb')] at hpos
      simp_all
  · obtain ⟨d₁, k₁, e₁, hk₁, o49, o76, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
        ztjpi d d₁ k₁ ∧ k₁ = 2 ∧
        d₁.nreg 150049 = p ∧ d₁.nreg 150076 = j ∧
        ztgsv ∧ d₁.nmem = d.nmem := by
      exec_block
      refine ⟨rfl, by_simp_all, by config_simp; rw [h04, R.h91]; omega,
        fun x h1 h2 => ?_, rfl⟩
      simp_all
    have R₁ : ChainRegs C (H.pts P.n).length Hh d₁ := R.of_frame by_simp_all
    obtain ⟨d₂, k₂, e₂, hk₂, fr₂, i₂, l₂⟩ := posP_exec S hD hMD hHh d₁ e₁.wb_right
      by_simp_all R₁ by_simp_all
      by_simp_all by_simp_all
      by_simp_all o49 o76 by_omega by_omega by_omega
    zuffk
    refine ⟨_, _, .ifLtN_false
      (show ¬ d.nreg 150001 < d.nreg 150096 by zuonk; exact hp6)
      ztwrj, by_omega, ?_, ?_⟩
    · config_simp
      exact i₂.trans (param_pos_iff _ _ hx).symm
    simp_all

/-- **Both ends on one edge**, the end not at its start vertex: are they in key order? -/
theorem decSame_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ}
    (hD : ChainDescAt m₀ ztki zta H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : ChainRegs C (H.pts P.n).length Hh d) (h00 : d.nreg 150000 = MD)
    (h27 : d.nreg 150027 = P.n) (h48 : d.nreg 150048 = 0) (h90 : d.nreg 150090 = 0)
    (h92 : d.nreg 150092 = 2) {p h₁ h₂ : ℕ} (h01 : d.nreg 150001 = p)
    (h02 : d.nreg 150002 = h₁) (h04 : d.nreg 150004 = h₂)
    (hp : p < 2 * C.m + 7) (hh₂ : 1 ≤ h₂) (hh₁n : h₁ ≤ P.n) (hh₂n : h₂ ≤ P.n)
    (he : ProperPos ztc zta P.n ztkmi)
    (hin : (chainModel C).InnerPt ((chainModel C).pos zta ztkmi)) :
    ∃ d' k, Exec P W decSame d d' k ∧ k ≤ 100 * H.length + 2100 ∧
      (d'.nreg 150048 = 1 ↔
        (chainModel C).key zta ztujd < (chainModel C).key zta ztkmi) ∧
      d'.nreg 150048 ≤ 1 := by
  zudn

  unfold decSame
  by_cases h0 : d.nreg 150002 < d.nreg 150091
  · have hz : ztsiy := by rw [h02, R.h91] at h0; omega
    subst hz
    obtain ⟨d', k, ex, hk, h1, h2⟩ := decVtx_exec S hD hMD hHh d hw hm R h00 h27 h48 h90 h92
      h01 h04 hp hh₂ hh₂n he hin
    refine ⟨d', _, .ifLtN_true h0 ex, by_omega, ?_, h2⟩
    rw [h1, key_hgt0]
    zuhqn
    simp
  · have hh₁ : 1 ≤ h₁ := by rw [h02, R.h91] at h0; omega
    have e₁ := Exec.copyN (P := P) hw 150049 150001
    set d₁ := ({ d with nreg := upd d.nreg 150049 _ } : Config) with hd₁
    have g₁ : ∀ x, x ≠ 150049 → d₁.nreg x = d.nreg x := by_simp_all
    obtain ⟨d₂, k₂, e₂, hk₂, fr₂, i₂, l₂⟩ := keyLess_exec S hD hMD hHh d₁ e₁.wb_right
      by_omega by_simp_all (by zuoax)
      by_simp_all by_simp_all by_simp_all
      hp hh₁ hh₁n hh₂ hh₂n
    zuffk
    refine ⟨_, _, .ifLtN_false h0 ztwrj, by_omega, ?_, ?_⟩
    · config_simp
      exact i₂.trans (key_lt_iff _ _ hh₁ hh₂).symm
    simp_all

/-- **The decision `SAME`.** -/
theorem decideS_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ ztki zta H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ d)
    (hs : ProperPos ztc zta P.n s) (he : ProperPos ztc zta P.n e)
    (hs1 : s.edge < 2 * C.m + 7)
    (hin : e.hgt = 0 ∨ (chainModel C).InnerPt ztwyx) :
    ∃ d' k, Exec P W decideS d d' k ∧ k ≤ 100 * H.length + 2110 ∧ FrameB Bd d d' ∧
      (d'.nreg 150048 = 1 ↔ (s.edge = e.edge ∧
        (chainModel C).key zta s < (chainModel C).key zta e)) ∧
      d'.nreg 150048 ≤ 1 := by
  zudn

  suffices main : ∃ d' k, Exec P W decideS d d' k ∧ k ≤ 100 * H.length + 2110 ∧
      (d'.nreg 150048 = 1 ↔ (s.edge = e.edge ∧
        (chainModel C).key _ s < (chainModel C).key _ e)) ∧
      d'.nreg 150048 ≤ 1 by
    obtain ⟨d', k, ex, hk, h1, h2⟩ := main
    exact ⟨d', k, ex, hk, exec_frameB ex wr_decideS, h1, h2⟩
  have e₀ := Exec.constN (P := P) hw 150048 0 by_omega
  set d₀ := ({ d with nreg := upd d.nreg 150048 0 } : Config) with hd₀
  have g₀ : ∀ x, x ≠ 150048 → d₀.nreg x = d.nreg x := by_simp_all
  zumft
  have z₀ : d₀.nreg 150048 = 0 := by_rfl
  have r01 : d₀.nreg 150001 = s.edge := by rw [g₀ _ by_omega, R.h01]
  have r02 : d₀.nreg 150002 = s.hgt := by rw [g₀ _ by_omega, R.h02]
  have r03 : d₀.nreg 150003 = e.edge := by rw [g₀ _ by_omega, R.h03]
  have r04 : d₀.nreg 150004 = e.hgt := by rw [g₀ _ by_omega, R.h04]
  have r90 : d₀.nreg 150090 = 0 := by rw [g₀ _ by_omega, R.h90]
  have hks := key_bounds hs
  have hke := key_bounds he
  have zero : ∀ (d' : Config) (k : ℕ), Exec P W decideS d d' k → k ≤ 100 * H.length + 2110 →
      d'.nreg 150048 = 0 → ¬ (s.edge = e.edge ∧
        (chainModel C).key zta s < (chainModel C).key zta e) →
      ∃ d' k, Exec P W decideS d d' k ∧ k ≤ 100 * H.length + 2110 ∧
        (d'.nreg 150048 = 1 ↔ (s.edge = e.edge ∧
          (chainModel C).key zta s < (chainModel C).key zta e)) ∧
        d'.nreg 150048 ≤ 1 :=
    by grind
  by_cases hlt : d₀.nreg 150001 < d₀.nreg 150003
  · refine zero d₀ _ (by unfold decideS; exact .seq e₀ (.ifLtN_true hlt ztjdy)) by_omega
      z₀ ?_
    omega
  by_cases hgt : d₀.nreg 150003 < d₀.nreg 150001
  · refine zero d₀ _ (by unfold decideS; exact .seq e₀ (.ifLtN_false hlt (.ifLtN_true hgt
      ztjdy))) by_omega z₀ ?_
    omega
  have heq : s.edge = e.edge := by_omega
  by_cases h4 : d₀.nreg 150090 < d₀.nreg 150004
  · have hh₂ : 1 ≤ e.hgt := by_omega
    have hin' : (chainModel C).InnerPt ztwyx := by
      grind
    have hs' : s = ztujk := rfl
    have he' : e = ⟨s.edge, e.hgt⟩ := by zvnbk
    obtain ⟨d', k, ex, hk, h1, h2⟩ := decSame_exec S hD hMD hHh d₀ w₀ by_omega
      (R.chain.of_frame fun r hr => g₀ r (by
        zvmxh at hr; omega))
      (by rw [g₀ _ by_omega, R.h00]) (by rw [g₀ _ by_omega, R.h27]) z₀ r90
      (by rw [g₀ _ by_omega, R.h92]) r01 r02 r04 hs1 hh₂ hs.2.2 he.2.2
      by_grind by_grind
    refine ⟨d', _, by unfold decideS; exact .seq e₀ (.ifLtN_false hlt (.ifLtN_false hgt
      (.ifLtN_true h4 ex))), by_omega, ?_, h2⟩
    rw [h1, ← hs', ← he']
    grind
  · refine zero d₀ _ (by unfold decideS; exact .seq e₀ (.ifLtN_false hlt (.ifLtN_false hgt
      (.ifLtN_false h4 ztjdy)))) by_omega z₀ ?_
    rw [r90, r04] at h4
    zuhyl
    rintro ⟨-, h⟩
    have : (chainModel C).key zta e = e.edge := by
      zunkx; simp
    grind
end
end ShootCut
@[expose] public section
open Chazelle.Chain (sideInArc)
namespace ShootCut
variable (C : Chain)
/-- **A stretch of counted edges** inside the unwrapped interval of an arc weighs at least its
length. -/
theorem arcWt_ge {a b A T : ℝ}
    (ha : 0 ≤ a ∧ a < ((2 * C.m + 7 : ℕ) : ℝ)) (hb : 0 ≤ b ∧ b < ((2 * C.m + 7 : ℕ) : ℝ))
    (hA : ∃ i : ℤ, A = a + i * ((2 * C.m + 7 : ℕ) : ℝ))
    (hT : ∃ k : ℤ, T = b + k * ((2 * C.m + 7 : ℕ) : ℝ))
    (hTA : T ≤ A + ((2 * C.m + 7 : ℕ) : ℝ)) {v L : ℕ} (hv6 : 6 ≤ v % ztz)
    (hvL : v % ztz + L ≤ 2 * C.m + 6) (hAv : A ≤ v) (hvT : (v : ℝ) + L ≤ T) :
    L ≤ (chainModel C).arcWt a b := by
  zulz
  zufvt
  set c := v % n with hc
  zuiqa
  have hW := chainModel_n C
  have hsub : ((Finset.Ico c (c + L) : Finset ℕ) : Set ℕ) ⊆
      {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p ∧
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk} := by
    zuda
    simp only [Finset.coe_Ico, Set.mem_Ico] at hp
    refine ⟨by_omega, (chainModel_counted_iff C p by_omega).2 by_omega, 1 / 2, by_norm_num, by_norm_num, ?_⟩
    have ev : (v : ℝ) = (c : ℝ) + ((v / n : ℕ) : ℝ) * n := by
      have := Nat.mod_add_div v n
      zuhuk
    have hpn : ((p : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast by_grind
    refine sideInArc_unw hn0 ha.1 ha.2 hb.1 hb.2 by_positivity by_linarith hA
      (X := (v : ℝ) + ((p - c : ℕ) : ℝ) + 1 / 2) ⟨((v / n : ℕ) : ℤ), ?_⟩ hT ?_ ?_ hTA
    · rw [Int.cast_natCast, ev]
      push_cast [show c ≤ p by omega]
      ring
    · grind
    · have : ((p - c : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast by_grind
      linarith
  have hfin : {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk}.Finite :=
    (Set.finite_lt_nat _).subset fun p hp => hp.1
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Nat.card_Ico] at this
  omega

/-- **Two keys congruent modulo `n`** in `[0, n)` are equal. -/
theorem key_eq_of_unw {n x y : ℝ} (hn : 0 < n) (hx : 0 ≤ x ∧ x < n) (hy : 0 ≤ y ∧ y < n)
    {i j : ℤ} (h : x + i * n = y + j * n) : x = y := by
  have hij : ((i - j : ℤ) : ℝ) * n = y - x := by_grind
  have h1 : ((i - j : ℤ) : ℝ) > -1 := by
    zubdj
  have h2 : ((i - j : ℤ) : ℝ) < 1 := by
    zubdj
  have h3 : i - j > -1 := by exact_mod_cast h1
  have h4 : i - j < 1 := by exact_mod_cast h2
  grind

/-- The walk edge `p` is in the uncounted block. -/
def InUB (m p : ℕ) : Prop := p ≤ 5 ∨ p = 2 * m + 6
instance (m p : ℕ) : Decidable (InUB m p) := inferInstanceAs ztdta

/-- The position of a walk edge in the uncounted block (`0` for `2m + 6`, `p + 1` for `p ≤ 5`). -/
def uIx (p : ℕ) : ℕ := if p ≤ 5 then p + 1 else 0

/-- The core hands a single piece `[s, e]` from `first`. -/
def Done (m e₁ e₂ : ℕ) : Prop :=
  (InUB m e₁ ∧ InUB m e₂ ∧ uIx e₁ < uIx e₂) ∨ (¬ InUB m e₁ ∧ InUB m e₂ ∧ ¬ e₁ + 1 < 2 * m + 6)

/-- The first walk vertex of the main loop. -/
def c0Of (m e₁ : ℕ) : ℕ := if e₁ ≤ 5 ∨ e₁ = 2 * m + 6 then 6 else e₁ + 1

/-- The final walk vertex of the main loop. -/
def fOf (m e₂ : ℕ) : ℕ := if e₂ ≤ 5 ∨ e₂ = 2 * m + 6 then 2 * m + 5 else e₂

/-- **The plan of the general case.** -/
theorem plan (Q : Polygon) {N : ℕ} {s e : WPos}
    (hs : ProperPos ztc Q N s) (he : ProperPos ztc Q N e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7)
    (hsame : ¬ (s.edge = e.edge ∧ (chainModel C).key Q s < (chainModel C).key Q e))
    (hdone : ¬ Done C.m s.edge e.edge) :
    ∃ U₀ F : ℕ, U₀ % ztz = c0Of C.m s.edge ∧ (chainModel C).key Q s < U₀ ∧
      F % ztz = fOf C.m e.edge ∧ U₀ ≤ F ∧ F < U₀ + ztz ∧
      (F : ℝ) ≤ (chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ)
        ztbaj ztbai ∧
      (ztihf →
        (F : ℝ) < (chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ)
          ztbaj ztbai) ∧
      (¬ ztihf →
        (F : ℝ) = (chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ)
          ztbaj ztbai) := by
  zubzd
  set ks := M.key Q s with hks
  set ke := M.key Q e with hke
  zulz
  zubb
  have bs := key_bounds hs
  have be := key_bounds he
  have hkeq : ke = e.edge + M.param Q e := rfl
  have hp0 := he.1
  have hp1 := he.2.1
  have hT1 : ks < ke → ks + len (n : ℝ) ks ke = ke := fun h => by unfold len; simp_all
  have hT2 : ¬ ks < ke → ks + len (n : ℝ) ks ke = ke + n := fun h => by
    zuhaq
  set e₁ := s.edge with he₁
  set e₂ := e.edge with he₂
  have cn : ((n : ℕ) : ℝ) = 2 * (C.m : ℝ) + 7 := by_simp_all
  unfold c0Of fOf
  unfold Done InUB uIx at hdone
  rcases (show e₁ ≤ 5 ∨ e₁ = 2 * C.m + 6 ∨ (6 ≤ e₁ ∧ e₁ ≤ 2 * C.m + 5) by omega) with
    h1 | h1 | h1 <;>
  rcases (show e₂ ≤ 5 ∨ e₂ = 2 * C.m + 6 ∨ (6 ≤ e₂ ∧ e₂ ≤ 2 * C.m + 5) by omega) with
    h2 | h2 | h2
  -- the start in `0 … 5`
  · -- the end in `0 … 5`: `e₂ ≤ e₁`
    have hle : e₂ ≤ e₁ := by
      grind
    have hT : ztjay := by
      zuklo
      · zuhuz

      grind
    refine ztdqe
    · zueyq
    · zudxo

    · zuhmi
    · grind
    · grind
    · zulxr
  · -- the end on `2m + 6`
    have hT : ztppb := by
      zucfw

    refine ztdqe
    · zueyq
    · zudxo

    · zuhmh
    · zuzw

    · zuzw

    · zuisv
  · -- the end on the double boundary
    have hT : ztppb := by
      zucfw

    zufvy
    refine ⟨6, e₂, ?_, ?_, ?_, by_omega, by_omega, ?_, fun h => ?_, fun h => ?_⟩
    · zueyq
    · zudxo

    · zuhmp
    · grind
    · zujii
      zuy
      · tauto
      grind
    grind
  -- the start on `2m + 6`
  · exact absurd by_grind
      hdone
  · -- both on `2m + 6`
    have hT : ztjay := by_grind
    refine ⟨6 + n, 2 * C.m + 5 + n, ?_, ?_, ?_, by_omega, by_omega, ?_, fun _ => ?_, fun h => ?_⟩
    · zuhmj
    · zuhva

    · rw [ite_eq_left ztffu, Nat.add_mod_right]; exact Nat.mod_eq_of_lt by_omega
    · zulps
      have : ztfkg := by
        zuhuk
      grind
    · zulps
      have : ztfkg := by
        zuhuk
      grind
    · zuisv
  · -- the start on `2m + 6`, the end on the double boundary
    have hT : ztjay := by
      zuhuy

    zufvy
    refine ⟨6 + n, e₂ + n, ?_, ?_, ?_, by_omega, by_omega, ?_, fun h => ?_, fun h => ?_⟩
    · zuhmj
    · zuhva

    · zugev
    · grind
    · zujij
      zuy
      · tauto
      grind
    grind
  -- the start on the double boundary
  · -- the end in `0 … 5`
    have hne : ztmvp := by
      omega
    have hT : ztjay := by
      zuhuy

    refine ztdje
    · zuhmk
    · grind
    · zuhmi
    · grind
    · grind
    · zulxr
  · -- the end on `2m + 6`
    have hne : ztmvp := by
      omega
    have hT : ztppb := by
      zucfw

    refine ztdje
    · zuhmk
    · grind
    · zuhmh
    · zuzw

    · zuzw

    · zuisv
  · -- both on the double boundary
    zufvy
    have hnU1 : ¬ (e₁ ≤ 5 ∨ e₁ = 2 * C.m + 6) := by_omega
    rcases (show e₁ < e₂ ∨ e₂ ≤ e₁ by omega) with h3 | h3
    · have hT : ztppb := by
        zucfw

      refine ⟨e₁ + 1, e₂, ?_, ?_, ?_, by_omega, by_omega, ?_, fun h => ?_, fun h => ?_⟩
      · zuhmo
      · grind
      · zuhmp
      · grind
      · zujii
        zuy
        · tauto
        grind
      grind
    · have hT : ztjay := by
        rcases h3.lt_or_eq with hlt | heq
        · zuhuz

        grind
      refine ⟨e₁ + 1, e₂ + n, ?_, ?_, ?_, by_omega, by_omega, ?_, fun h => ?_, fun h => ?_⟩
      · zuhmo
      · grind
      · zugev
      · grind
      · zujij
        zuy
        · tauto
        grind
      grind
end ShootCut
end
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
theorem uFlag_exec {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d) (src dst idx : ℕ)
    (h1 : src ≠ dst) (h2 : dst ≠ idx) (h3 : dst ≠ 150091) {p m : ℕ} (hs : d.nreg src = p)
    (hp : p < 2 * m + 7) (h96 : d.nreg 150096 = 6) (h91 : d.nreg 150091 = 1)
    (h32 : d.nreg 150032 = 2 * m + 6) (hW : 7 ≤ W) :
    ∃ d' k, Exec P W (uFlag src dst idx) d d' k ∧ k ≤ 8 ∧
      d'.nreg dst = (if p ≤ 5 ∨ p = 2 * m + 6 then 1 else 0) ∧ d'.nreg idx = uIx p ∧
      (∀ x, x ≠ dst → x ≠ idx → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  unfold uFlag uIx
  zufrf
  · zudd
    zuevx
    refine spec_step (Exec.addN w₁ _ _ _ (by
      simp only [upd, h1, Ne.symm h3, ite_false]; omega))
      fun w₂ => spec_nil w₂ ztdqi
    · zucab
    · simp only [upd, ite_true, h1, Ne.symm h3, ite_false]
      grind
    simp_all
  · by_cases hpm : p < 2 * m + 6
    · refine spec_ifLtN_false by_omega
        ztoia
      zuevx
      refine spec_step ztcta
        fun w₂ => spec_nil w₂ ztdqi
      · zucab
      · zuhqd
      simp_all
    · refine spec_ifLtN_false by_omega
        (spec_ifLtN_false by_omega
          ztkfj)
      zuevx
      refine spec_step ztcta
        fun w₂ => spec_nil w₂ ztdqi
      · zucab
      · zuhqd
      simp_all

/-! ## The pieces of kind `0` -/

/-- The piece `[s, e]`. -/
def pSE (s e : WPos) : Pc := ⟨s, e, 0, 0, 0, 0, 0⟩

/-- The piece from `s` to the walk vertex `v`. -/
def pSV (s : WPos) (v : ℕ) : Pc := ⟨s, ztcfs, 0, 0, 0, 0, 0⟩

/-- The piece from the walk vertex `v` to `e`. -/
def pVE (v : ℕ) (e : WPos) : Pc := ⟨ztcfs, e, 0, 0, 0, 0, 0⟩

/-- **From the last edge of the double boundary into the uncounted block**: weight at most
`1`. -/
theorem wt_last_edge (C : Chain) (Q : Polygon) {n : ℕ} {x y : WPos}
    (hx : ProperPos ztc Q n x) (hy : ProperPos ztc Q n y)
    (hxe : x.edge = 2 * C.m + 5) (hU : InU C y.edge) :
    (chainModel C).arcWt ztlb ztov ≤ 1 := by
  zuigz
  zurs

  zubt
  unfold arcWtNat

  rw [hxe]
  zus
  · omega
  · zufzr
    · omega
    · exfalso
      zuhrs
      zulpt

      linarith [hx.2.1, hy.1]
variable {P : Polygon} {C : Chain} {m₀ : ℕ → ℕ} {h γ : ℕ}
theorem pSE_ok {s e : WPos} (hs : ProperPos ztc zta P.n s)
    (he : ProperPos ztc zta P.n e) (hs1 : s.edge < 2 * C.m + 7)
    (he1 : e.edge < 2 * C.m + 7)
    (hw : (chainModel C).arcWt ztwlj ztwli ≤ 1) :
    PcOK P C m₀ h γ zttvm :=
  ⟨hs, he, hs1, he1, Or.inl rfl, fun _ => hw, fun h1 => by_tauto⟩
theorem pSV_ok {s : WPos} {v : ℕ} (hs : ProperPos ztc zta P.n s)
    (hs1 : s.edge < 2 * C.m + 7) (hv : v < 2 * C.m + 7)
    (hw : (chainModel C).arcWt ztwlj (v : ℝ) ≤ 1) :
    PcOK P C m₀ h γ zttvn :=
  ⟨hs, proper_vtx' P C v, hs1, hv, Or.inl rfl, fun _ => by simp only [pSV, key_hgt0]; exact hw,
    fun h1 => by_tauto⟩
theorem pVE_ok {e : WPos} {v : ℕ} (he : ProperPos ztc zta P.n e)
    (he1 : e.edge < 2 * C.m + 7) (hv : v < 2 * C.m + 7)
    (hw : (chainModel C).arcWt (v : ℝ) ztwli ≤ 1) :
    PcOK P C m₀ h γ ztoeh :=
  ⟨proper_vtx' P C v, he, hv, he1, Or.inl rfl, fun _ => by simp only [pVE, key_hgt0]; exact hw,
    fun h1 => by_tauto⟩

/-- **A leaf**: a piece written by the block `B`, handed to `emit`, then one instruction `T`
(writing the register `tgt` of the core). -/
theorem leaf_exec {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop} {I : List Pc → Config → Prop}
    (hE : EmitOK P W emit A₀ Pv I K) {ps : List Pc} {pc : Pc} {B : Stmt} {T : Instr}
    {tgt : ℕ} {post : Config → Prop} (d : Config) (hI : I ps d) (hpv : Pv pc)
    (hB : ∃ d₁ k₁, Exec P W B d d₁ k₁ ∧ k₁ ≤ 5 ∧ PcRegs d₁ pc ∧ FrameB Scr d d₁ ∧
      ztbnu)
    (hT : ∀ d₂ : Config, WordsBounded W d₂ → ztkif →
      ∃ d₃, Exec P W ztuvk d₂ d₃ 1 ∧ FrameB Scr d₂ d₃ ∧ post d₃ ∧
        (∀ r, r ≠ tgt → d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem) :
    ∃ d' k, Exec P W (.seq B (.seq emit ztuvk)) d d' k ∧ k ≤ K + 6 ∧
      I ztdvs d' ∧ post d' ∧ (∀ r, Keep r → r ≠ tgt → d'.nreg r = d.nreg r) ∧
      ztno := by
  obtain ⟨d₁, k₁, e₁, hk₁, hR, fr₁, kp₁⟩ := hB
  obtain ⟨d₂, k₂, e₂, hk₂, hI₂, kp₂, mem₂⟩ := hE.run _ pc d₁ e₁.wb_right ztczr hR hpv
  obtain ⟨d₃, e₃, fr₃, hp₃, r₃, m₃⟩ := hT d₂ e₂.wb_right fun r hr => (kp₂ r hr).trans (kp₁ r hr)
  refine ⟨d₃, k₁ + ztcaj, .seq e₁ ztcr, by_omega, hE.stable _ _ _ hI₂ fr₃, hp₃,
    fun r hr h1 => by_grind, fun a ha => ?_⟩
  rw [m₃, mem₂ a ha, fr₁.2.2.1]
variable {W : ℕ}
theorem pcSE_exec (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) {s e : WPos}
    (h01 : d.nreg 150001 = s.edge) (h02 : d.nreg 150002 = s.hgt) (h03 : d.nreg 150003 = e.edge)
    (h04 : d.nreg 150004 = e.hgt) :
    ∃ d₁ k₁, Exec P W pcSE d d₁ k₁ ∧ k₁ ≤ 5 ∧ PcRegs d₁ zttvm ∧ FrameB Scr d d₁ ∧
      ztbnu := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁⟩ : ∃ d₁ k₁, Exec P W pcSE d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = s.edge ∧ d₁.nreg 150051 = s.hgt ∧ d₁.nreg 150052 = e.edge ∧
      d₁.nreg 150053 = e.hgt ∧ d₁.nreg 150054 = 0 ∧
      ztbcv := by
    unfold pcSE
    exec_block
    all_goals first | omega | skip
    refine ztbth
    all_goals first | (config_simp; first | exact h01 | exact h02 | exact h03 | exact h04; done) |
      (config_simp; done) | skip
    zubd
  exact ⟨d₁, k₁, e₁, by_omega, ztbod,
    exec_frameB e₁ by_decide, fun r hr => r₁ r ztbpy⟩
theorem pcSV_exec (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) {s : WPos} {v : ℕ}
    (h01 : d.nreg 150001 = s.edge) (h02 : d.nreg 150002 = s.hgt) (h75 : d.nreg 150075 = v) :
    ∃ d₁ k₁, Exec P W pcSV d d₁ k₁ ∧ k₁ ≤ 5 ∧ PcRegs d₁ zttvn ∧ FrameB Scr d d₁ ∧
      ztbnu := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁⟩ : ∃ d₁ k₁, Exec P W pcSV d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = s.edge ∧ d₁.nreg 150051 = s.hgt ∧ d₁.nreg 150052 = v ∧
      d₁.nreg 150053 = 0 ∧ d₁.nreg 150054 = 0 ∧
      ztbcv := by
    unfold pcSV
    exec_block
    all_goals first | omega | skip
    refine ztbth
    all_goals first | (config_simp; first | exact h01 | exact h02 | exact h75; done) |
      (config_simp; done) | skip
    zubd
  exact ⟨d₁, k₁, e₁, by_omega, ztbod,
    exec_frameB e₁ by_decide, fun r hr => r₁ r ztbpy⟩
theorem pcVE_exec (d : Config) (hw : WordsBounded W d) (hW : 1 ≤ W) {e : WPos} {v : ℕ}
    (h75 : d.nreg 150075 = v) (h03 : d.nreg 150003 = e.edge) (h04 : d.nreg 150004 = e.hgt) :
    ∃ d₁ k₁, Exec P W pcVE d d₁ k₁ ∧ k₁ ≤ 5 ∧ PcRegs d₁ ztoeh ∧ FrameB Scr d d₁ ∧
      ztbnu := by
  obtain ⟨d₁, k₁, e₁, hk₁, v50, v51, v52, v53, v54, r₁⟩ : ∃ d₁ k₁, Exec P W pcVE d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 150050 = v ∧ d₁.nreg 150051 = 0 ∧ d₁.nreg 150052 = e.edge ∧
      d₁.nreg 150053 = e.hgt ∧ d₁.nreg 150054 = 0 ∧
      ztbcv := by
    unfold pcVE
    exec_block
    all_goals first | omega | skip
    refine ztbth
    all_goals first | (config_simp; first | exact h03 | exact h04 | exact h75; done) |
      (config_simp; done) | skip
    zubd
  exact ⟨d₁, k₁, e₁, by_omega, ztbod,
    exec_frameB e₁ by_decide, fun r hr => r₁ r ztbpy⟩
variable {O : OracleIface} {H : Host} {Hh h γ : ℕ} {A₀ W : ℕ}
theorem uIx_eq {p : ℕ} (hp : InU C p) : uIx p = uIdx C p := by
  unfold uIx uIdx InU at *; grind

/-- **The first piece.** -/
theorem first_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztbwt I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos} (d : Config) (hw : WordsBounded W d)
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ d)
    (h38 : d.nreg 150038 = if s.edge ≤ 5 ∨ s.edge = 2 * C.m + 6 then 1 else 0)
    (h37 : d.nreg 150037 = uIx s.edge)
    (h39 : d.nreg 150039 = if e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6 then 1 else 0)
    (h30 : d.nreg 150030 = uIx e.edge) (hI : I ps₀ d)
    (hs : ProperPos ztc zta P.n s) (he : ProperPos ztc zta P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7) :
    ∃ d' k p₁, Exec P W zthwr d d' k ∧ k ≤ K + 20 ∧ I ztfif d' ∧
      PcOK P C m₀ h γ p₁ ∧ p₁.s = s ∧
      ztdtb ∧
      (¬ Done C.m s.edge e.edge → p₁.e = ztkka ∧
        d'.nreg 150040 = c0Of C.m s.edge ∧ d'.nreg 150043 = d.nreg 150043) ∧
      ztcoq ∧
      ztno := by
  zudn

  zuerk
  zubb
  -- the trailing instructions
  have tc43 : ∀ d₂ : Config, WordsBounded W d₂ → ztkif →
      ∃ d₃, Exec P W _ d₂ d₃ 1 ∧ FrameB Scr d₂ d₃ ∧
        d₃.nreg 150043 = 1 ∧ (∀ r, r ≠ 150043 → d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem :=
    fun d₂ w₂ _ => ⟨_, Exec.constN w₂ 150043 1 by_omega,
      exec_frameB (Exec.constN (P := P) w₂ 150043 1 by_omega) by_decide, by config_simp,
      by simp_all, rfl⟩
  have tc40 : ∀ (d₁ : Config), ztbnu →
      ∀ d₂ : Config, WordsBounded W d₂ → ztkig →
      ∃ d₃, Exec P W (.instr (.addN 150040 150001 150091)) d₂ d₃ 1 ∧ FrameB Scr d₂ d₃ ∧
        d₃.nreg 150040 = s.edge + 1 ∧ ztiva ∧
        d₃.nmem = d₂.nmem := by
    zukjf
    have a1 : d₂.nreg 150001 = s.edge := by
      rw [k₂ _ by_tauto, k₁ _ by_tauto, R.h01]
    have a91 : ztlyj := by
      rw [k₂ _ ztii, k₁ _ ztii, R.chain.h91]
    exact ⟨_, Exec.addN w₂ 150040 150001 150091 by_omega,
      exec_frameB (Exec.addN (P := P) w₂ 150040 150001 150091 by_omega)
        by_decide, by config_simp; omega, fun r hr => by zumwy, rfl⟩
  have tc40' : ∀ (d₁ : Config), ztbnu →
      ∀ d₂ : Config, WordsBounded W d₂ → ztkig →
      ∃ d₃, Exec P W ztdse d₂ d₃ 1 ∧ FrameB Scr d₂ d₃ ∧
        d₃.nreg 150040 = 6 ∧ ztiva ∧
        d₃.nmem = d₂.nmem := by
    zukjf
    have a96 : ztpoh := by
      rw [k₂ _ ztii, k₁ _ ztii, R.chain.h96]
    exact ⟨_, Exec.copyN w₂ 150040 150096, exec_frameB (Exec.copyN (P := P) w₂ 150040 150096)
      by_decide, by_tauto, fun r hr => by zumwy, rfl⟩
  unfold first
  by_cases hsU : s.edge ≤ 5 ∨ s.edge = 2 * C.m + 6
  · have t38 : d.nreg 150090 < d.nreg 150038 := by rw [R.h90, h38, ite_eq_left hsU]; omega
    -- the piece to `6` (with `75 := 6` first)
    have toSix : ¬ Done C.m s.edge e.edge →
        ∃ d' k, Exec P W (.seq ztigh (.seq pcSV (.seq emit
          ztdse))) d d' k ∧ k ≤ K + 7 ∧ I (ps₀ ++ [pSV s 6]) d' ∧
          d'.nreg 150040 = 6 ∧ ztcbk ∧
          ztno := by
      zuhge
      have e₁ := Exec.copyN (P := P) hw 150075 150096
      zudbl
      have k₁ : ztfli := fun r hr => by
        zubzt
      have hpv : PcOK P C m₀ h γ (pSV s 6) := pSV_ok hs hs1 by_omega (by
        zuoba; omega)
      obtain ⟨d', k, ex, hk, hI', h40, kp, mem⟩ := leaf_exec hE (pc := pSV s 6) (tgt := 150040)
        d₁ ztywk hpv
        (pcSV_exec d₁ e₁.wb_right by_omega ztxdt
          ztxdu (by simp [hd₁, upd, R.chain.h96]))
        (tc40' d₁ k₁)
      exact ⟨d', _, .seq e₁ ex, by_omega, hI', h40, by_grind,
        by omega⟩
    have notDone : ¬ (e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6) ∨ ¬ uIx s.edge < uIx e.edge →
        ¬ Done C.m s.edge e.edge := by
      rintro hc (⟨-, h2, h3⟩ | ⟨h1, -⟩)
      · zunk
        · tauto
        omega
      tauto
    have fin6 : ¬ Done C.m s.edge e.edge → ∀ (d' : Config) (k : ℕ),
        Exec P W zthwr d d' k → k ≤ K + 20 → I (ps₀ ++ [pSV s 6]) d' →
        d'.nreg 150040 = 6 → ztcbk →
        ztno →
        ∃ d' k p₁, Exec P W zthwr d d' k ∧ k ≤ K + 20 ∧ I ztfif d' ∧
          PcOK P C m₀ h γ p₁ ∧ p₁.s = s ∧
          ztdtb ∧
          (¬ Done C.m s.edge e.edge → p₁.e = ztkka ∧
            d'.nreg 150040 = c0Of C.m s.edge ∧ d'.nreg 150043 = d.nreg 150043) ∧
          ztcoq ∧
          ztno := by
      zugoe
      have hc0 : c0Of C.m s.edge = 6 := by unfold c0Of; grind
      refine ⟨d', k, pSV s 6, ex, hk, hI', pSV_ok hs hs1 by_omega (by
        zuoba; omega), rfl, by_grind, fun _ => ⟨by
        zunso; rfl, by_omega, kp _ ztii by_omega⟩,
        by grind, mem⟩
    zuwf
    · have t39 : ztshw := by_grind
      by_cases hlt : uIx s.edge < uIx e.edge
      · -- a single piece through the uncounted block
        have hpv : ztdjt := pSE_ok hs he hs1 he1 (by
          rw [wt_U_U C _ hs he hsU heU (by rw [← uIx_eq hsU, ← uIx_eq heU]; omega)]; omega)
        obtain ⟨d', k, ex, hk, hI', h43, kp, mem⟩ := leaf_exec hE d hI hpv (pcSE_exec d hw by_omega R.h01 R.h02 R.h03 R.h04) tc43
        refine ⟨d', _, pSE s e, .ifLtN_true t38 (.ifLtN_true t39 (.ifLtN_true
          by_omega ex)), by_omega, hI', hpv, rfl, fun _ => ⟨rfl, h43⟩,
          (absurd (Or.inl ⟨hsU, heU, hlt⟩)), by_grind, mem⟩
      · zucnt
        exact fin6 by_grind d' _ (.ifLtN_true t38 (.ifLtN_true t39
          ztdrw)) by_omega hI' h40 kp mem
    · have t39 : ztrho := by_grind
      zucnt
      exact fin6 by_grind d' _ (.ifLtN_true t38 ztspc) by_omega
        hI' h40 kp mem
  · have t38 : ¬ d.nreg 150090 < d.nreg 150038 := by_grind
    have hc0 : c0Of C.m s.edge = s.edge + 1 := by unfold c0Of; grind
    -- `75 := e₁ + 1`
    have e₁ := Exec.addN (P := P) hw 150075 150001 150091 (by rw [R.h01, R.chain.h91]; omega)
    set d₁ := ({ d with nreg := upd d.nreg 150075 _ } : Config)
      with hd₁
    have k₁ : ztfli := fun r hr => by
      zubzt
    have o75 : d₁.nreg 150075 = s.edge + 1 := by simp [hd₁, upd, R.h01, R.chain.h91]
    zud
    have hI₁ := hE.stable _ _ _ hI ztduj
    have a39 : d₁.nreg 150039 = d.nreg 150039 := k₁ _ ztii
    have a90 : d₁.nreg 150090 = 0 := by rw [k₁ _ ztii, R.h90]
    have a32 : ztorb := by rw [k₁ _ ztii, R.h32]
    -- the piece to `e₁ + 1`
    have toNext : ¬ Done C.m s.edge e.edge →
        ∃ d' k, Exec P W ztdet d₁ d' k ∧
          k ≤ K + 6 ∧ I ztite d' ∧ d'.nreg 150040 = s.edge + 1 ∧
          zthlv ∧
          ztiug := by
      zuhge
      have hpv : ztdjt := pSV_ok hs hs1 by_omega
        ztryk
      exact leaf_exec hE d₁ hI₁ hpv
        (pcSV_exec d₁ w₁ by_omega ztxdt
          ztxdu o75)
        (tc40 d₁ k₁)
    have finN : ¬ Done C.m s.edge e.edge → ∀ (d' : Config) (k : ℕ),
        Exec P W zthwr d d' k → k ≤ K + 20 → I ztite d' →
        d'.nreg 150040 = s.edge + 1 → zthlv →
        ztiug →
        ∃ d' k p₁, Exec P W zthwr d d' k ∧ k ≤ K + 20 ∧ I ztfif d' ∧
          PcOK P C m₀ h γ p₁ ∧ p₁.s = s ∧
          ztdtb ∧
          (¬ Done C.m s.edge e.edge → p₁.e = ztkka ∧
            d'.nreg 150040 = c0Of C.m s.edge ∧ d'.nreg 150043 = d.nreg 150043) ∧
          ztcoq ∧
          ztno := by
      zugoe
      refine ⟨d', k, pSV s _, ex, hk, hI', pSV_ok hs hs1 by_omega
        ztryk, rfl, by_grind, fun _ => ⟨by zunso; rfl,
        by omega, (kp _ ztii by_omega).trans
          (k₁ _ ztii)⟩,
        by grind, by_omega⟩
    zuwf
    · have t39 : d₁.nreg 150090 < d₁.nreg 150039 := by
        grind
      by_cases hnx : s.edge + 1 < 2 * C.m + 6
      · have hnd : ztmxj := by
          rintro (⟨h1, -⟩ | ⟨-, -, h3⟩)
          · tauto
          omega
        zucns
        exact finN hnd d' _ (.ifLtN_false t38 (.seq e₁ (.ifLtN_true t39 (.ifLtN_true
          by_omega ex)))) by_omega hI' h40 kp mem
      · -- a single piece from the last edge into the uncounted block
        have hpv : ztdjt := pSE_ok hs he hs1 he1
          (wt_last_edge C _ hs he by_omega heU)
        obtain ⟨d', k, ex, hk, hI', h43, kp, mem⟩ := leaf_exec hE
          (tgt := 150043) (post := fun d₃ => d₃.nreg 150043 = 1) d₁ hI₁ hpv
          (pcSE_exec d₁ w₁ by_omega
            ztxdt
            ztxdu
            ztyee
            ztyef)
          (fun d₂ w₂ _ => ⟨_, Exec.constN w₂ 150043 1 by_omega,
            exec_frameB (Exec.constN (P := P) w₂ 150043 1 by_omega) by_decide,
            by config_simp, fun r hr => by zumwy, rfl⟩)
        refine ⟨d', _, pSE s e, .ifLtN_false t38 (.seq e₁ (.ifLtN_true t39 (.ifLtN_false
          by_omega ex))), by_omega, hI', hpv, rfl, fun _ => ⟨rfl, h43⟩,
          (absurd (Or.inr ⟨hsU, heU, hnx⟩)),
          by grind, by_omega⟩
    · have t39 : ¬ d₁.nreg 150090 < d₁.nreg 150039 := by
        grind
      have hnd : ztmxj := by
        rintro (⟨h1, -⟩ | ⟨-, h2, -⟩)
        · tauto
        tauto
      zucns
      exact finN hnd d' _ (.ifLtN_false t38 (.seq e₁ ztspc)) by_omega hI' h40
        kp mem

/-- A piece to the end `e` from the walk vertex in `75`, handed to `emit`. -/
theorem leafVE_exec {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop} {I : List Pc → Config → Prop}
    (hE : EmitOK P W emit A₀ Pv I K) {ps : List Pc} {e : WPos} {v : ℕ} (d : Config)
    (hw : WordsBounded W d) (hW : 1 ≤ W) (h75 : d.nreg 150075 = v)
    (h03 : d.nreg 150003 = e.edge) (h04 : d.nreg 150004 = e.hgt) (hI : I ps d)
    (hpv : Pv ztoeh) :
    ∃ d' k, Exec P W ztncu d d' k ∧ k ≤ K + 5 ∧ I (ps ++ [pVE v e]) d' ∧
      (∀ r, Keep r → d'.nreg r = d.nreg r) ∧ ztno := by
  obtain ⟨d₁, k₁, e₁, hk₁, hR, fr₁, kp₁⟩ := pcVE_exec (P := P) d hw hW h75 h03 h04
  obtain ⟨d₂, k₂, e₂, hk₂, hI₂, kp₂, mem₂⟩ := hE.run _ _ d₁ e₁.wb_right ztczr hR hpv
  exact ⟨d₂, k₁ + k₂, .seq e₁ e₂, by_omega, hI₂, by_simp_all,
    fun a ha => by rw [mem₂ a ha, fr₁.2.2.1]⟩

/-- **The last piece**: from the walk vertex `2m + 5` into the uncounted block, or from the start
vertex of the edge of the end when its parameter is positive, or none. -/
theorem final_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztbwt I K)
    {ps : List Pc} {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ ztki zta H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ d)
    (h39 : d.nreg 150039 = if e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6 then 1 else 0) (hI : I ps d)
    (he : ProperPos ztc zta P.n e) (he1 : e.edge < 2 * C.m + 7) :
    ∃ d' k fin, Exec P W ztvql d d' k ∧ k ≤ K + 100 * H.length + 2200 ∧
      I (ps ++ fin) d' ∧ (∀ pc ∈ fin, PcOK P C m₀ h γ pc) ∧
      (ztxqr →
        fin = [pVE (fOf C.m e.edge) e]) ∧
      (¬ ztxqr → fin = []) ∧
      ztno := by
  zudn

  zuerk
  zubb
  unfold final
  zuwf
  · have t39 : ztshw := by rw [R.h90, h39, ite_eq_left heU]; omega
    have hf : fOf C.m e.edge = 2 * C.m + 5 := by unfold fOf; simp_all
    have e₁ := Exec.copyN (P := P) hw 150075 150031
    zudbl
    have k₁ : ztfli := fun r hr => by
      zubzt
    have hpv : ztdjt := pVE_ok he he1 by_omega
      (wt_last_to_U C _ he heU)
    obtain ⟨d', k, ex, hk, hI', -, mem⟩ := leafVE_exec hE d₁ e₁.wb_right by_omega
      (by simp [hd₁, upd, R.h31]) ztyee
      ztyef
      ztywk hpv
    refine ⟨d', _, [pVE _ e], .ifLtN_true t39 ztncm, by_omega, hI', ?_,
      by simp_all, (absurd (Or.inl heU)), by_omega⟩
    simp_all
  · have t39 : ztrho := by_simp_all
    have hf : fOf C.m e.edge = e.edge := by unfold fOf; simp_all
    by_cases h4 : d.nreg 150090 < d.nreg 150004
    · have hh : 1 ≤ e.hgt := by rw [R.h90, R.h04] at h4; omega
      obtain ⟨j, hj⟩ : ∃ j, e.hgt = j + 1 := ⟨e.hgt - 1, by_omega⟩
      have hex : e = ztrcf := by zuorx
      obtain ⟨d₁, k₁, e₁, hk₁, o49, o76, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
          ztjpj d d₁ k₁ ∧ k₁ = 2 ∧
          d₁.nreg 150049 = e.edge ∧ d₁.nreg 150076 = j ∧
          ztgsv ∧ d₁.nmem = d.nmem := by
        exec_block
        refine ⟨rfl, by config_simp; exact R.h03, by config_simp; rw [R.h04, R.chain.h91]; omega,
          fun x h1 h2 => ?_, rfl⟩
        zubd
      have R₁ := R.chain.of_frame fun r hr => r₁ r (by
        zvmxh at hr; omega) (by
        zvmxh at hr; omega)
      have hpe : ProperPos ztc zta P.n ztrcf := by_grind
      obtain ⟨d₂, k₂, e₂, hk₂, fr₂, i₂, l₂⟩ := posP_exec S hD hMD hHh d₁ e₁.wb_right
        ztxl R₁ (by rw [r₁ _ by_omega by_omega, R.h00])
        (by rw [r₁ _ by_omega by_omega, R.h27]) (by rw [r₁ _ by_omega by_omega, R.h90])
        (by rw [r₁ _ by_omega by_omega, R.h92]) o49 o76 by_omega by_omega
        (by have := he.2.2; omega)
      have ip : d₂.nreg 150089 = 1 ↔ 0 < (chainModel C).param zta e := by
        zupat; exact i₂.trans (param_pos_iff _ _ hpe).symm
      have c90 : ztpog := by
        rw [(exec_frameB e₂ (B := Bd) by_decide).1 _ by_decide, r₁ _ by_omega by_omega,
          R.h90]
      have hI₂ := hE.stable _ _ _ hI ((exec_frameB e₁ by_decide).trans fr₂)
      zue
      by_cases hp : d₂.nreg 150090 < d₂.nreg 150089
      · have hpos : 0 < (chainModel C).param _ e := ip.1 by_omega
        have e₃ := Exec.copyN (P := P) w₂ 150075 150003
        set d₃ := ({ d₂ with nreg := upd d₂.nreg 150075 _ } : Config) with hd₃
        have a3 : ztutv := by
          rw [fr₂.1 _ by_decide, r₁ _ by_omega by_omega, R.h03]
        have a4 : d₂.nreg 150004 = e.hgt := by
          rw [fr₂.1 _ by_decide, r₁ _ by_omega by_omega, R.h04]
        have hpv : ztdjt := pVE_ok he he1 by_omega
          (wt_from_start _ _ he hpos)
        obtain ⟨d', k, ex, hk, hI', -, mem⟩ := leafVE_exec hE d₃ e₃.wb_right by_omega
          ztljs ztljs (by simp [hd₃, upd, a4])
          (hE.stable _ _ _ hI₂ ztduk) hpv
        refine ⟨d', _, [pVE e.edge e], .ifLtN_false t39 (.ifLtN_true h4 (.seq e₁ (.seq e₂
          (.ifLtN_true hp ztncp)))), by_omega, hI', ?_, by_grind,
          by grind, fun a ha => ?_⟩
        · grind
        · rw [mem a ha]; show d₂.nmem a = d.nmem a; zunqi
      · have hpos : ztygv := by_grind
        refine ⟨d₂, _, [], .ifLtN_false t39 (.ifLtN_true h4 (.seq e₁ (.seq e₂
          (.ifLtN_false hp ztbun)))), by_omega, by_grind,
          by simp, fun h => h.elim ztpbn by_grind,
          by grind, fun a ha => by zunqi⟩
    · have hpos : ztygv := by
        rw [R.h90, R.h04] at h4
        zuhyl
        zunkx
        simp
      refine ⟨d, _, [], .ifLtN_false t39 (.ifLtN_false h4 ztjd), by_omega,
        by simp_all, by_simp, fun h => h.elim ztpbn by_simp_all, by_simp_all,
        by omega⟩
end
end ShootCut
@[expose] public section
open Chazelle.Chain (sideInArc)
namespace ShootCut
theorem Chained.get {x y : WPos} {ps : List Pc} (h : Chained x ps y) :
    ∀ i (hi : i + 1 < ps.length), (ps[i]' by_omega).e = (ps[i + 1]'hi).s := by
  induction ps generalizing x with
  | nil => intro i hi; simp at hi
  | cons p ps ih =>
    zug
    obtain ⟨_, h2⟩ := h
    cases i with
    | zero =>
      cases ps with
      | nil => simp at hi
      | cons q qs =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        exact h2.1.symm
    | succ i =>
      zulrr
      exact ih h2 i by_simp_all
theorem Chained.append' : ∀ {x y z : WPos} {ps qs : List Pc}, Chained x ps y → Chained y qs z →
    Chained x ztlrt z
  | _, _, _, [], _, h, hq => by simp only [Chained] at h; simp_all
  | _, _, _, _ :: _, _, ⟨h1, h2⟩, hq => ⟨h1, Chained.append' h2 hq⟩
theorem Chained.last : ∀ {x y : WPos} {ps : List Pc}, Chained x ps y → (hne : ps ≠ []) →
    (ps.getLast hne).e = y
  | _, _, [], _, hne => absurd rfl hne
  | _, _, [_], ⟨_, h2⟩, _ => h2
  | _, _, _ :: q :: qs, ⟨_, h2⟩, _ => by
      zulpe
      exact Chained.last h2 ztjjq
variable {n : ℕ} {N : ℕ} {P : Polygon} {m₀ : ℕ → ℕ} {h γ : ℕ}
theorem upath_chained : ∀ {u : ℕ} {ps : List Pc} {u' : ℕ}, UPath n u ps u' →
    Chained ztret ps ⟨u' % n, 0⟩
  | _, [], _, h => by_tauto
  | _, _ :: _, _, ⟨h1, _, _, h3, h4⟩ => ⟨h1, by zvncq; exact upath_chained h4⟩
variable (C : Chain) (Q : Polygon)

/-- **The pieces tile the subarc** from `s` to `e`. -/
structure ArcOK (s e : WPos) (ps : List Pc) : Prop where
  ne : ps ≠ []
  hs : (ps.head ne).s = s
  he : (chainModel C).key Q (ps.getLast ne).e = (chainModel C).key Q e
  ch : ∀ i (hi : i + 1 < ps.length), (ps[i]' by_omega).e = (ps[i + 1]'hi).s
  e6 : ∀ i (hi : i + 1 < ps.length), sideInArc ztgvt
    ztbai ztgvs
  kp : KPath ztc Q ((2 * C.m + 7 : ℕ) : ℝ) ztbaj ps
    ((chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ) ztbaj
      ztbai)
  ends : ∀ pc ∈ ps, (pc.s = s ∨ pc.s.hgt = 0) ∧ (pc.e = e ∨ pc.e.hgt = 0)
variable {C Q}
theorem key_range {x : WPos} (hx : ProperPos ztc Q N x)
    (h1 : x.edge < 2 * C.m + 7) :
    0 ≤ (chainModel C).key Q x ∧ (chainModel C).key Q x < ((2 * C.m + 7 : ℕ) : ℝ) := by
  have := key_bounds hx
  have e : (x.edge : ℝ) + 1 ≤ ((2 * C.m + 7 : ℕ) : ℝ) := by exact_mod_cast h1
  grind
theorem T_unw (k k' : ℝ) (n : ℝ) : ∃ j : ℤ, k + len n k k' = k' + j * n := by
  unfold len
  split_ifs
  · simp
  · exact ⟨1, by_grind⟩

/-- **A single piece** `[s, e]`. -/
theorem arcOK_single {s e : WPos} (hs : ProperPos ztc Q N s)
    (he : ProperPos ztc Q N e) (hs1 : s.edge < 2 * C.m + 7)
    (he1 : e.edge < 2 * C.m + 7) {p : Pc} (hps : p.s = s) (hpe : p.e = e) :
    ArcOK C Q s e [p] := by
  have ks := key_range hs hs1
  have ke := key_range he he1
  refine ⟨by_simp, hps, by_simp_all, fun i hi => by_grind, fun i hi => by_grind, ?_,
    fun pc hpc => ?_⟩
  swap
  · simp_all
  have hl := len_pos ((2 * C.m + 7 : ℕ) : ℝ) ztbaj ztbai
    ks.2 ke.1
  refine ⟨⟨0, by_simp_all⟩, (chainModel C).key Q s + len ((2 * C.m + 7 : ℕ) : ℝ)
    ztbaj ztbai, by_linarith, by zungd; exact T_unw _ _ _,
    rfl⟩

/-- The keys of a valid piece are keys of the walk. -/
theorem pcOK_keys {pc : Pc} (hp : PcOK P C m₀ h γ pc) :
    (0 ≤ (chainModel C).key zta pc.s ∧
      (chainModel C).key zta pc.s < ((2 * C.m + 7 : ℕ) : ℝ)) ∧
    (0 ≤ (chainModel C).key zta pc.e ∧
      (chainModel C).key zta pc.e < ((2 * C.m + 7 : ℕ) : ℝ)) :=
  ⟨key_range hp.1 hp.2.2.1, key_range hp.2.1 hp.2.2.2.1⟩

/-- The pieces of a path of walk vertices start and end at walk vertices. -/
theorem UPath.ends : ∀ {u : ℕ} {ps : List Pc} {u' : ℕ}, UPath n u ps u' →
    ∀ pc ∈ ps, pc.s.hgt = 0 ∧ pc.e.hgt = 0
  | _, [], _, _, _, h => by_simp_all
  | _, _ :: _, _, ⟨h1, _, _, h2, h3⟩, pc, hpc => by
    zucyl
    · simp_all
    · exact UPath.ends h3 pc hpc

/-- **The general case**: the first piece to the walk vertex of `U₀`, the main loop from `U₀`
to `F`, and the last piece from the vertex of `F` to `e` (if `F < T`). -/
theorem arcOK_general {s e : WPos}
    (hs : ProperPos ztc zta P.n s) (he : ProperPos ztc zta P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7) {U₀ F : ℕ} {p₁ : Pc}
    {loop fin : List Pc} (hp₁s : p₁.s = s) (hp₁e : p₁.e = ⟨U₀ % ztz, 0⟩)
    (hks : (chainModel C).key zta s < U₀) (hloop : UPath ztz U₀ loop F)
    (hfin : (fin = [pVE (F % ztz) e] ∧ (F : ℝ) < (chainModel C).key zta s +
        len ((2 * C.m + 7 : ℕ) : ℝ) ztwlj ztwli) ∨
      (fin = [] ∧ (F : ℝ) = (chainModel C).key zta s +
        len ((2 * C.m + 7 : ℕ) : ℝ) ztwlj ztwli))
    (hok : ∀ pc ∈ p₁ :: ztcdj, PcOK P C m₀ h γ pc) :
    ArcOK C zta s e (p₁ :: ztcdj) := by
  zulz
  zubzd
  zubep
  zukzq
  set ke := M.key Q e
  set T := ks + len (n : ℝ) ks ke with hT
  zufvt
  zufhn

  have hTle : T ≤ ks + n := by
    have := len_le (n : ℝ) ks ke kS.1 kE.2; linarith
  have hTu := T_unw ks ke (n : ℝ)
  -- the whole path of keys
  have hkU : ∀ u : ℕ, ∃ j : ℤ, (u : ℝ) = M.key Q ztret + j * n := fun u => by
    refine ztine
    rw [key_hgt0, Int.cast_natCast]
    have := Nat.mod_add_div u n
    have e : ((u % n : ℕ) : ℝ) + ((u / n : ℕ) : ℝ) * (n : ℝ) = (u : ℝ) := by
      exact_mod_cast (show u % n + u / n * n = u by zuodt; omega)
    linarith
  have hfinP : KPath M Q (n : ℝ) (F : ℝ) fin T := by
    rcases hfin with ⟨rfl, hlt⟩ | ⟨rfl, heq⟩
    · exact ⟨hkU F, T, hlt, hTu, rfl⟩
    tauto
  have hkp : KPath M Q (n : ℝ) ks (p₁ :: ztcdj) T :=
    ⟨⟨0, by_grind⟩, U₀, hks, by zupba; tauto,
      (kpath_of_upath hloop).append fin hfinP⟩
  have hne : p₁ :: ztcdj ≠ [] := List.cons_ne_nil _ _
  -- the last key is the key of `e`
  have hlast : M.key Q ((p₁ :: ztcdj).getLast hne).e = ke := by
    obtain ⟨j, hj⟩ := KPath.last hkp hne
    obtain ⟨j', hj'⟩ := hTu
    have hb := (pcOK_keys (hok _ (List.getLast_mem hne))).2
    exact key_eq_of_unw hn0 hb kE (i := j) (j := j') by_grind
  -- consecutive
  have hch : Chained s (p₁ :: ztcdj) ((p₁ :: ztcdj).getLast hne).e := by
    have hc : ∃ y, Chained s (p₁ :: ztcdj) y := by
      have hl := upath_chained hloop
      zuejw
      · exact ⟨e, hp₁s, by zupba; exact Chained.append' hl ztrh⟩
      · exact ⟨_, hp₁s, by rw [hp₁e, List.append_nil]; exact hl⟩
    obtain ⟨y, hy⟩ := hc
    rw [Chained.last hy hne]; exact hy
  refine ⟨hne, hp₁s, hlast, fun i hi => Chained.get hch i hi, fun i hi => ?_, hkp, ?_⟩
  swap
  · zujbk
    zucyl
    · grind
    zujcl
    · have := UPath.ends hloop pc hpc; omega
    · zuejw
      · zvojs at hpc; subst hpc; exact ⟨Or.inr rfl, Or.inl rfl⟩
      tauto
  have := e6_of_kpath hn0 hkp by_linarith (fun pc hpc => pcOK_keys (hok pc hpc)) hne i hi
  grind
end ShootCut
open Set
open Chazelle.Geometry (lerp)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Sweep (FirstHitOpt omin firstHitOpt_union firstHit_unique)
namespace ShootCut
theorem eq_of_unw_pos {n a b : ℝ} (hn : 0 < n) (ha : 0 < a ∧ a ≤ n) (hb : 0 < b ∧ b ≤ n)
    {i j : ℤ} (h : a + i * n = b + j * n) : a = b := by
  have := key_eq_of_unw hn (x := n - a) (y := n - b) ztbcx
    ⟨by_linarith, by_linarith⟩ (i := j) (j := i) by_linarith
  linarith

/-- **A path of pieces through unwrapped keys** covers the unwrapped interval. -/
theorem kpath_wset {M : Model} {Q : Polygon} (hn : 0 < M.W.n) :
    ∀ {V : ℝ} {ps : List Pc} {V' : ℝ}, KPath M Q (M.W.n : ℝ) V ps V' → ps ≠ [] →
      V' ≤ V + M.W.n →
      (∀ pc ∈ ps, (0 ≤ M.key Q pc.s ∧ M.key Q pc.s < M.W.n) ∧
        (0 ≤ M.key Q pc.e ∧ M.key Q pc.e < M.W.n)) →
      wset M V V' = ⋃ pc ∈ ps, M.arcSet ztene ztend
  | _, [], _, _, hne, _, _ => absurd rfl hne
  | V, pc :: ps, V', ⟨⟨i, hi⟩, V₁, hV₁, ⟨j, hj⟩, hrest⟩, _, hle, hk => by
    zufvr
    have hk₀ := hk pc (List.mem_cons_self ..)
    have hV₁' := hrest.le
    -- the first piece ends at `V + len`
    obtain ⟨j', hj'⟩ := T_unw ztene ztend (M.W.n : ℝ)
    have hL := len_pos (M.W.n : ℝ) ztene ztend hk₀.1.2 hk₀.2.1
    have hL' := len_le (M.W.n : ℝ) ztene ztend hk₀.1.1 hk₀.2.2
    have hstep : V₁ - V = len (M.W.n : ℝ) ztene ztend :=
      eq_of_unw_pos hn' ztbcx ⟨hL, hL'⟩ (i := j' + i) (j := j)
        by_grind
    have hpc : M.arcSet ztene ztend = wset M V V₁ := by
      rw [arcSet_step M hk₀.1.1 hk₀.1.2 hk₀.2.1 hk₀.2.2 i, ← hi]
      grind
    have e : (⋃ q ∈ pc :: ps, M.arcSet ztszx ztszw) =
        M.arcSet ztene ztend ∪
          ⋃ q ∈ ps, M.arcSet ztszx ztszw := by
      simp
    rw [e, hpc]
    by_cases hne' : ps = []
    · subst hne'
      have : V₁ = V' := hrest
      simp_all
    · rw [← kpath_wset hn hrest hne' by_linarith (fun pc' hpc' => hk pc'
        (List.mem_cons_of_mem _ hpc')), wset_union M hV₁.le hV₁']
variable {C : Chain} {Q : Polygon}

/-- **The subarc is the union of its pieces.** -/
theorem arcSet_pieces {s e : WPos} {ps : List Pc} (hA : ArcOK C Q s e ps)
    (hs : 0 ≤ (chainModel C).key Q s ∧ (chainModel C).key Q s < ((2 * C.m + 7 : ℕ) : ℝ))
    (he : 0 ≤ (chainModel C).key Q e ∧ (chainModel C).key Q e < ((2 * C.m + 7 : ℕ) : ℝ))
    (hk : ∀ pc ∈ ps, (0 ≤ (chainModel C).key Q pc.s ∧
        (chainModel C).key Q pc.s < ((2 * C.m + 7 : ℕ) : ℝ)) ∧
      (0 ≤ (chainModel C).key Q pc.e ∧ (chainModel C).key Q pc.e < ((2 * C.m + 7 : ℕ) : ℝ))) :
    (chainModel C).arcSet ztbaj ztbai =
      ⋃ pc ∈ ps, (chainModel C).arcSet ztmyp
        ztmyo := by
  zubzd
  zuerv
  zuiy
  have hkp := hA.kp
  rw [← hnW] at hkp hs he hk
  have hL' := len_le (M.W.n : ℝ) ztenf ztfoc hs.1 he.2
  rw [← kpath_wset hn hkp hA.ne by_linarith hk, arcSet_eq_wset M hs.1 hs.2 he.1 he.2]
  zucr
  zuhaq

/-! ## Candidates -/
theorem sigma_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 := by
  grind

/-- **A candidate answer** on `S`: flag `1` and the first hit at abscissa `x`, or no hit. -/
def Cand (S : Set Point) (z : Point) (σ : ℝ) (f : ℕ) (x : ℝ) : Prop :=
  (f = 1 → FirstHit S z σ ztewx) ∧ (f ≠ 1 → NoHit S z σ)

/-- The option of a candidate. -/
noncomputable def candOpt (z : Point) (σ : ℝ) (f : ℕ) (x : ℝ) : Option ℝ :=
  if f = 1 then some ztewx else none
theorem cand_iff {S : Set Point} {z : Point} {σ : ℝ} {f : ℕ} {x : ℝ} :
    Cand S z σ f x ↔ FirstHitOpt S z σ (candOpt z σ f x) := by
  unfold Cand candOpt
  by_cases hf : f = 1
  · rw [ite_eq_left hf]; tauto
  · rw [ite_eq_right hf]; tauto

/-- **The nearer of two candidates** is a candidate on the union. -/
theorem cand_union {S₁ S₂ : Set Point} {z : Point} {σ : ℝ} (_hσ : σ = 1 ∨ σ = -1) {f₁ f₂ : ℕ}
    {x₁ x₂ : ℝ} (h₁ : Cand S₁ z σ f₁ x₁) (h₂ : Cand S₂ z σ f₂ x₂) :
    Cand ztbzc z σ (if f₂ = 1 ∧ ztjws then 1 else f₁)
      (if f₂ = 1 ∧ ztjws then x₂ else x₁) := by
  have hu := firstHitOpt_union (cand_iff.1 h₁) (cand_iff.1 h₂)
  rw [cand_iff]
  convert hu using 1
  unfold candOpt omin
  grind
end ShootCut
open Chazelle.Geometry (lerp_fst lerp_snd)
namespace ShootCut
def seg (U V : Point) : Set Point := {x | ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ x = lerp U V u}
theorem lerp_lerp (a b : Point) (α β u : ℝ) :
    lerp (lerp a b α) (lerp a b β) u = lerp a b (α + u * ztokt) := by
  ext <;> simp only [lerp_fst, lerp_snd] <;> ring

/-- **A sub-segment of a walk edge is the segment between its ends.** -/
theorem subSeg_eq_seg (M : Model) (p : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    subSeg M p α β = seg ztzmp ztzmq := by
  zumx
  constructor
  · rintro ⟨s, h0, h1, rfl⟩
    rcases hαβ.lt_or_eq with hlt | heq
    · refine ⟨(s - α) / ztokt, div_nonneg by_linarith by_linarith,
        (div_le_one by_linarith).2 by_linarith, ?_⟩
      zunts; grind
    · zufpx
      exact ⟨0, le_rfl, zero_le_one, by zunts; grind⟩
  · rintro ⟨u, h0, h1, rfl⟩
    refine ⟨α + u * ztokt, by_nlinarith, by_nlinarith, by zunts⟩
theorem U_mem_seg (U V : Point) : U ∈ seg U V :=
  ⟨0, le_rfl, zero_le_one, by_simp⟩
theorem V_mem_seg (U V : Point) : V ∈ seg U V :=
  ⟨1, zero_le_one, le_rfl, by_simp⟩

/-- A point of the segment at the height of `U`, when the heights of the ends are equal. -/
theorem seg_snd_of_eq {U V : Point} (h : U.2 = V.2) {x : Point} (hx : x ∈ seg U V) :
    x.2 = U.2 := by
  zufkx
  simp_all
variable {U V z : Point} {σ : ℝ}

/-- **No hit**: the segment is at another height. -/
theorem seg_off (h : U.2 = V.2) (hz : z.2 ≠ U.2) (x : ℝ) : Cand ztevj z σ 0 x :=
  ⟨fun h' => absurd h' by_norm_num, fun _ t _ hS => hz (by
    rw [← seg_snd_of_eq h hS]; rfl)⟩

/-- The ray point at the abscissa of a point at the height of `z`. -/
theorem rayPt_of_x (hσ : σ = 1 ∨ σ = -1) {X : Point} (hX : X.2 = z.2) :
    rayPt z σ ztbabg = X := by
  have := sigma_sq hσ
  ext
  · zudch
  simp_all

/-- **A set meeting the line of the ray in at most one point `X`.** -/
theorem cand_single {S : Set Point} (hσ : σ = 1 ∨ σ = -1) {X : Point} (hXS : X ∈ S)
    (hX : X.2 = z.2) (huniq : ∀ x ∈ S, x.2 = z.2 → x = X) :
    Cand S z σ ztyaz X.1 := by
  zuhfy
  have key : ∀ t, rayPt z σ t ∈ S → t = σ * ztdtq := fun t ht => by
    have := huniq _ ht rfl
    have hx := congrArg Prod.fst this
    zufbx
    grind
  by_cases hpos : 0 < σ * ztdtq
  · zulpz
    refine ⟨fun _ => ⟨hpos, by rw [rayPt_of_x hσ hX]; omega, fun t' h1 h2 hS => ?_⟩,
      fun h => absurd rfl h⟩
    grind
  · zulqi
    refine zticl
    grind

/-- **Ends at different heights**: the segment meets the line of `z` at most once. -/
theorem seg_unique (h : U.2 ≠ V.2) {x x' : Point} (hx : x ∈ seg U V) (hx' : x' ∈ seg U V)
    (hy : x.2 = x'.2) : x = x' := by
  zufkx
  obtain ⟨u', -, -, rfl⟩ := hx'
  simp only [lerp_snd] at hy
  grind

/-- **The hit at a point `X` of a segment with ends at different heights.** -/
theorem seg_at (hσ : σ = 1 ∨ σ = -1) (h : U.2 ≠ V.2) {X : Point} (hXS : X ∈ seg U V)
    (hX : X.2 = z.2) :
    Cand ztevj z σ ztyaz X.1 :=
  cand_single hσ hXS hX fun x hx hxz => seg_unique h hx hXS by_simp_all

/-- **No hit**: the height of `z` is outside the heights of the ends. -/
theorem seg_out (hout : ¬ (min U.2 V.2 ≤ z.2 ∧ z.2 ≤ max U.2 V.2)) (x : ℝ) :
    Cand ztevj z σ 0 x := by
  refine ⟨fun h' => absurd h' by_norm_num, fun _ t _ hS => hout ?_⟩
  obtain ⟨u, h0, h1, he⟩ := hS
  zukhf
  simp only [rayPt_snd, lerp_snd] at hy
  zujka
  constructor
  · zuiej
    · rw [min_eq_left hh]; nlinarith
    · rw [min_eq_right hh]; nlinarith
  · zuiej
    · rw [max_eq_right hh]; nlinarith
    · rw [max_eq_left hh]; nlinarith

/-- **Ends and `z` at one height**: the nearer end if `U` is ahead, no hit otherwise. -/
theorem seg_on (hσ : σ = 1 ∨ σ = -1) (h : U.2 = V.2) (hz : z.2 = U.2) (hzS : z ∉ seg U V) :
    Cand ztevj z σ (if 0 < σ * ztdgg then 1 else 0)
      (if σ * U.1 ≤ σ * V.1 then U.1 else V.1) := by
  zuhfy
  -- the points of the segment on the ray line
  have hmem : ∀ t, rayPt z σ t ∈ seg U V ↔ ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧
      z.1 + σ * t = U.1 + u * ztdgh := fun t => by
    constructor
    · zugtk
      exact ⟨u, h0, h1, by have := congrArg Prod.fst he; tauto⟩
    · zugtk
      refine ⟨u, h0, h1, ?_⟩
      ext
      · simp_all
      simp_all
  -- `z` is not between `U` and `V`
  have hzn : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → z.1 ≠ U.1 + u * ztdgh := fun u h0 h1 he =>
    hzS ⟨u, h0, h1, Prod.ext by_simp_all by_simp_all⟩
  have hzU : z.1 ≠ U.1 := fun he => hzn 0 le_rfl zero_le_one by_simp_all
  have hzV : z.1 ≠ V.1 := fun he => hzn 1 zero_le_one le_rfl by_simp_all
  -- both ends on the same side of `z`
  have hside : ztzaq ↔ ztzar := by
    constructor
    · zulmt
      by_contra hV
      push Not at hV
      have hV' : σ * zteok < 0 := lt_of_le_of_ne hV (fun h0 => by
        grind)
      -- a point between `U` and `V` is `z`
      zukzz
      have hne : ztscx := fun h0 => by
        grind
      zukgi
      zur
      · zudne

        exact hzn u zttjd
          ztosr hu
      · zudnd

        exact hzn u zttjb
          ztosp hu
    · intro hV
      by_contra hU
      push Not at hU
      have hU' : σ * ztdgg < 0 := lt_of_le_of_ne hU (fun h0 => by
        grind)
      zukzz
      have hne : ztscx := fun h0 => by
        grind
      zukgi
      zur
      · zudnd

        exact hzn u zttjb
          ztosp hu
      · zudne

        exact hzn u zttjd
          ztosr hu
  by_cases hU : 0 < σ * ztdgg
  · rw [ite_eq_left hU]
    have hV := hside.1 hU
    -- the nearer end
    set X := if σ * U.1 ≤ σ * V.1 then U.1 else V.1 with hXd
    have hXU : X = U.1 ∨ X = V.1 := by_grind
    have hXle : σ * X ≤ σ * U.1 ∧ σ * X ≤ σ * V.1 := by
      grind
    have hXpos : 0 < σ * (X - z.1) := by_grind
    refine ⟨fun _ => ⟨hXpos, ?_, fun t' h1 h2 hS => ?_⟩, fun h => absurd rfl h⟩
    · rcases hXU with e | e
      · rw [e, rayPt_of_x hσ (by rw [hz])]; exact U_mem_seg U V
      · rw [e, rayPt_of_x hσ by_grind]; exact V_mem_seg U V
    · obtain ⟨u, h0, h1', he⟩ := (hmem t').1 hS
      -- `σ x` of a point of the segment is at least `σ X`
      have hx : σ * ztxvy ≥ σ * X := by
        have : σ * ztxvy = ztgxi * (σ * U.1) + u * (σ * V.1) := by_ring
        zvmwk; nlinarith [hXle.1, hXle.2]
      have : σ * (z.1 + σ * t') = σ * z.1 + t' := by
        grind
      rw [← he, this] at hx
      linarith
  · rw [ite_eq_right hU]
    have hV : ¬ 0 < σ * zteok := fun h' => hU (hside.2 h')
    refine zticl
    obtain ⟨u, h0, h1, he⟩ := (hmem t).1 hS
    push Not at hU hV
    have e0 : σ * ztkhn = σ * z.1 + t := by_grind
    have e1 : σ * ztkhn = σ * ztxvy := by zvmxm
    have e2 : t = ztgxi * ztbabf + u * ztbabh := by
      grind
    have p1 : ztgxi * ztbabf ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos by_linarith hU
    have p2 : u * ztbabh ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 hV
    linarith
def pcEdge (n sE d : ℕ) : ℕ := (sE + d) % n

/-- The start parameter on the `d`-th edge. -/
noncomputable def pcA (a : ℝ) (d : ℕ) : ℝ := if d = 0 then a else 0

/-- The end parameter on the `d`-th edge. -/
noncomputable def pcB (D : ℕ) (b : ℝ) (d : ℕ) : ℝ := if d = D then b else 1

/-- The union of the sub-segments of the edges `0 … j` of a piece. -/
def pcSet (M : Model) (sE : ℕ) (a : ℝ) (D : ℕ) (b : ℝ) (j : ℕ) : Set Point :=
  ⋃ d ∈ List.range ztl, subSeg M (pcEdge M.W.n sE d) (pcA a d) (pcB D b d)
variable (M : Model) (sE : ℕ) (a : ℝ) (D : ℕ) (b : ℝ) {n : ℕ} {x y : WPos}
theorem pcSet_succ (j : ℕ) :
    pcSet M sE a D b ztl = pcSet M sE a D b j ∪
      subSeg M (pcEdge M.W.n sE ztl) (pcA a ztl) (pcB D b ztl) := by
  unfold pcSet
  zumlp
  ext x; simp
theorem pcSet_zero :
    pcSet M sE a D b 0 = subSeg M (pcEdge M.W.n sE 0) (pcA a 0) (pcB D b 0) := by
  unfold pcSet; simp

/-- The sub-segments up to `j < D` do not depend on the end parameter. -/
theorem pcSet_congr {D D' : ℕ} {b b' : ℝ} {j : ℕ}
    (h : ∀ d, d ≤ j → pcB D b d = pcB D' b' d) : pcSet M sE a D b j = pcSet M sE a D' b' j := by
  unfold pcSet
  simp_all
theorem nat_split (k n : ℕ) : (k : ℝ) = ((k % n : ℕ) : ℝ) + ((k / n : ℕ) : ℤ) * (n : ℝ) := by
  rw [Int.cast_natCast]; exact_mod_cast (Nat.mod_add_div' k n).symm

/-- **An unwrapped key range from `sE + a` over `D` more edges to `+ b`** is the union of the
sub-segments of its edges. -/
theorem wset_decomp (M : Model) {sE : ℕ} (hn : 0 < M.W.n) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ (D : ℕ) {b : ℝ}, 0 ≤ b → b ≤ 1 → (D = 0 → a ≤ b) →
      wset M ((sE : ℝ) + a) ((sE : ℝ) + D + b) = pcSet M sE a D b D
  | 0, b, hb0, hb1, hab => by
    rw [pcSet_zero]
    zumtw
    simp only [ite_true, Nat.cast_zero, add_zero]
    have hsE := nat_split sE M.W.n
    rw [hsE, show ((sE % M.W.n : ℕ) : ℝ) + ((sE / M.W.n : ℕ) : ℤ) * M.W.n + a =
        ((sE % M.W.n : ℕ) : ℝ) + a + ((sE / M.W.n : ℕ) : ℤ) * M.W.n by ring,
      show ((sE % M.W.n : ℕ) : ℝ) + ((sE / M.W.n : ℕ) : ℤ) * M.W.n + b =
        ((sE % M.W.n : ℕ) : ℝ) + b + ((sE / M.W.n : ℕ) : ℤ) * M.W.n by ring]
    exact wset_edge M zthp ha0 (hab rfl) hb1 _
  | D + 1, b, hb0, hb1, _ => by
    have ih := wset_decomp M (sE := sE) hn ha0 ha1 D (b := 1) zero_le_one le_rfl (fun _ => ha1)
    rw [pcSet_succ, ← pcSet_congr M sE a (D := D) (b := 1) (fun d hd => by
      unfold pcB; grind), ← ih]
    have hlast : wset M ((sE : ℝ) + D + 1) ((sE : ℝ) + ↑ztef + b) =
        subSeg M (pcEdge M.W.n sE ztef) (pcA a ztef) (pcB ztef b ztef) := by
      zumtw
      simp only [Nat.add_one_ne_zero, ite_false, ite_true]
      set q := sE + ztef
      have hq := nat_split q M.W.n
      have e1 : (sE : ℝ) + D + 1 = ((q % M.W.n : ℕ) : ℝ) + 0 + ((q / M.W.n : ℕ) : ℤ) * M.W.n := by
        grind
      have e2 : (sE : ℝ) + ↑ztef + b =
          ((q % M.W.n : ℕ) : ℝ) + b + ((q / M.W.n : ℕ) : ℤ) * M.W.n := by
        grind
      zuea
      exact wset_edge M zthp le_rfl hb0 hb1 _
    rw [← hlast, wset_union M by_linarith by_grind]

/-! ## The number of edges -/
variable {C : Chain} {Q : Polygon}

/-- **A kind-0 piece within one edge does not wrap around.** -/
theorem piece0_nowrap (hx : ProperPos ztc Q n x)
    (hy : ProperPos ztc Q n y) (hxy : x.edge = y.edge) (hxn : x.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ztlb ztov ≤ 1) :
    (chainModel C).param Q x < (chainModel C).param Q y := by
  zuguc
  zuks

  zubt
  zurs

  zumrq
  grind

/-- The count of a kind-0 piece. -/
def pcD (n sE eE : ℕ) : ℕ := ztqmi % n

/-- **At most ten edges.** -/
theorem piece0_D_le (hx : ProperPos ztc Q n x)
    (hy : ProperPos ztc Q n y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ztlb ztov ≤ 1) :
    pcD ztz x.edge y.edge ≤ 9 := by
  zukeh
  zuguc
  zubt
  zurs

  zubgj

  unfold pcD
  zumrq
  split_ifs at hwt with hlt
  · -- no wrap in keys: `x.edge ≤ y.edge`
    have hle : x.edge ≤ y.edge := by
      zubq

      zuhux

    rw [show y.edge + ztz - x.edge = ztfvl + ztz by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    omega
  · -- wrap in keys: `y.edge ≤ x.edge`
    have hle : y.edge ≤ x.edge := by
      omega
    zuklp
    · zuey
      omega
    omega

/-- **The unwrapped end** of a kind-0 piece. -/
theorem piece0_end (hx : ProperPos ztc Q n x)
    (hy : ProperPos ztc Q n y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ztlb ztov ≤ 1) :
    (chainModel C).key Q x + len ((2 * C.m + 7 : ℕ) : ℝ) ztlb
        ztov =
      (x.edge : ℝ) + (pcD ztz x.edge y.edge : ℕ) + (chainModel C).param Q y := by
  zukeh
  zubgj

  unfold len pcD Model.key
  split_ifs with hlt
  · have hle : x.edge ≤ y.edge := by
      zubq

      zuhux

    rw [show y.edge + ztz - x.edge = ztfvl + ztz by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt by_omega, Nat.cast_sub hle]
    ring
  · have hle : y.edge ≤ x.edge := by
      zubq

      zuepg
      grind
    zuklp
    · zuey
      push_cast [show x.edge ≤ y.edge + ztz by omega]
      ring
    simp_all

/-- **A kind-0 piece is the union of its edge segments.** -/
theorem piece0_union (hx : ProperPos ztc Q n x)
    (hy : ProperPos ztc Q n y) (hxn : x.edge < 2 * C.m + 7)
    (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ztlb ztov ≤ 1) :
    (chainModel C).arcSet ztlb ztov =
      pcSet ztc x.edge ztuy ztwqs
        ztqq ztwqs := by
  zubzd
  zuerv
  zuiy
  have kx := key_range hx hxn
  have ky := key_range hy hyn
  rw [← hnW] at kx ky
  have hL := len_le (M.W.n : ℝ) ztbys ztfof kx.1 ky.2
  have hend := piece0_end hx hy hxn hyn hwt
  have hstep := arcSet_step M kx.1 kx.2 ky.1 ky.2 0
  simp only [Int.cast_zero, zero_mul, add_zero] at hstep
  rw [hnW] at hstep
  rw [hstep, hend, show M.key Q x = (x.edge : ℝ) + M.param Q x from rfl]
  refine wset_decomp M (sE := x.edge) hn hx.1 hx.2.1.le ztwqs hy.1
    hy.2.1.le (fun hD => ?_)
  -- one edge: the start comes first
  have hxy : ztsnc := by
    unfold pcD at hD
    rcases Nat.lt_or_ge y.edge x.edge with h | h
    · zvmyc at hD; omega
    · rw [show y.edge + ztz - x.edge = ztfvl + ztz by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt by_omega] at hD
      omega
  exact (piece0_nowrap hx hy hxy hxn hwt).le
end ShootCut
end
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
open Chazelle.Chain (sideInArc)
@[expose] public section
variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}
theorem CoreRegs.of_low {MD mode : ℕ} {s e : WPos} {c c' : Config}
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ c)
    (hk : ∀ r, 150000 ≤ r → r < 150037 → r ≠ 150030 → c'.nreg r = c.nreg r)
    (h90 : c'.nreg 150090 = 0) (h91 : c'.nreg 150091 = 1) (h92 : c'.nreg 150092 = 2)
    (h93 : c'.nreg 150093 = 3) (h96 : c'.nreg 150096 = 6) :
    CoreRegs P C H Hh MD h γ mode s e m₀ c' := by
  have k : ∀ r, 150000 ≤ r → r < 150030 ∨ (150030 < r ∧ r < 150037) →
      c'.nreg r = c.nreg r := by_grind
  exact ⟨⟨(k _ by_norm_num by_norm_num).trans R.chain.h21,
      (k _ by_norm_num by_norm_num).trans R.chain.h22,
      (k _ by_norm_num by_norm_num).trans R.chain.h23,
      (k _ by_norm_num by_norm_num).trans R.chain.h26,
      (k _ by_norm_num by_norm_num).trans R.chain.h28,
      (k _ by_norm_num by_norm_num).trans R.chain.h29, h91, h93, h96⟩,
    (k _ by_norm_num by_norm_num).trans R.h00, (k _ by_norm_num by_norm_num).trans R.h01,
    (k _ by_norm_num by_norm_num).trans R.h02, (k _ by_norm_num by_norm_num).trans R.h03,
    (k _ by_norm_num by_norm_num).trans R.h04, (k _ by_norm_num by_norm_num).trans R.h09,
    (k _ by_norm_num by_norm_num).trans R.h13, (k _ by_norm_num by_norm_num).trans R.h20,
    (k _ by_norm_num by_norm_num).trans R.h27, (k _ by_norm_num by_norm_num).trans R.h31,
    (k _ by_norm_num by_norm_num).trans R.h32, (k _ by_norm_num by_norm_num).trans R.h33,
    (k _ by_norm_num by_norm_num).trans R.h34, (k _ by_norm_num by_norm_num).trans R.h35,
    (k _ by_norm_num by_norm_num).trans R.h36, h90, h92⟩

/-- The cost bound of the general case. -/
def genCost (K γ : ℕ) : ℕ := 1100 * ztxhl + 2 * K + 20000

/-- **The general case.** -/
theorem general_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztbwt I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ ztki zta H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh)
    (d : Config) (hw : WordsBounded W d) (R : CoreRegs P C H Hh MD h γ mode s e m₀ d)
    (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (hI : I ps₀ d)
    (hs : ProperPos ztc zta P.n s) (he : ProperPos ztc zta P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7)
    (hsame : ¬ (s.edge = e.edge ∧ (chainModel C).key zta s < (chainModel C).key zta e))
    (hwt : (chainModel C).arcWt ztwlj ztwli ≤ γ) :
    ∃ d' k ps, Exec P W ztqor d d' k ∧ k ≤ genCost K γ ∧ I ztrup d' ∧
      ArcOK C zta s e ps ∧ ztiuq ∧
      ps.length ≤ 2100 * ztir ∧ ztcqe := by
  zudn

  zuerk
  zubb
  zulz
  -- the flags of the uncounted block
  obtain ⟨d₁, k₁, e₁, hk₁, o38, o37, r₁, m₁⟩ := uFlag_exec (P := P) d hw 150001 150038 150037
    by_omega by_omega by_omega R.h01 hs1 R.chain.h96 R.chain.h91 R.h32 by_omega
  obtain ⟨d₂, k₂, e₂, hk₂, o39, o30, r₂, m₂⟩ := uFlag_exec (P := P) d₁ e₁.wb_right 150003 150039
    150030 by_omega by_omega by_omega (by rw [r₁ _ by_omega by_omega, R.h03]) he1
    (by rw [r₁ _ by_omega by_omega, R.chain.h96])
    (by rw [r₁ _ by_omega by_omega, R.chain.h91])
    (by rw [r₁ _ by_omega by_omega, R.h32]) by_omega
  have g₂ : ∀ x, x ≠ 150037 → x ≠ 150038 → x ≠ 150039 → x ≠ 150030 → d₂.nreg x = d.nreg x :=
    by simp_all
  zue
  -- `41 := f`
  obtain ⟨d₃, k₃, e₃, hk₃, o41, r₃, m₃⟩ : ∃ d₃ k₃, Exec P W (.ifLtN 150090 150039
      ztovc ztovb) d₂ d₃ k₃ ∧ k₃ ≤ 3 ∧
      d₃.nreg 150041 = fOf C.m e.edge ∧ (∀ x, x ≠ 150041 → d₃.nreg x = d₂.nreg x) ∧
      d₃.nmem = d₂.nmem := by
    unfold fOf
    have a90 : ztpog := by
      rw [g₂ 150090 by_omega by_omega by_omega by_omega, R.h90]
    have a31 : d₂.nreg 150031 = 2 * C.m + 5 := by
      rw [g₂ 150031 by_omega by_omega by_omega by_omega, R.h31]
    have a03 : ztutv := by
      rw [g₂ 150003 by_omega by_omega by_omega by_omega, R.h03]
    zuwf
    · have c39 : d₂.nreg 150090 < d₂.nreg 150039 := by_simp_all
      refine spec_ifLtN_true c39 (spec_instr ztrjh fun _ => ⟨by_omega, ?_,
          by simp_all, rfl⟩)
      simp_all
    · have c39 : ¬ d₂.nreg 150090 < d₂.nreg 150039 := by_simp_all
      refine spec_ifLtN_false c39 (spec_instr ztrjh fun _ => ⟨by_omega, ?_,
          by simp_all, rfl⟩)
      config_simp; grind
  -- `43 := 0`
  have e₄ := Exec.constN (P := P) e₃.wb_right 150043 0 by_omega
  set d₄ := ({ d₃ with nreg := upd d₃.nreg 150043 0 } : Config) with hd₄
  have g₄ : ∀ x, x ≠ 150037 → x ≠ 150038 → x ≠ 150039 → x ≠ 150030 → x ≠ 150041 →
      x ≠ 150043 → d₄.nreg x = d.nreg x := by_simp_all
  zucc
  have R₄ : CoreRegs P C H Hh MD h γ mode s e m₀ d₄ := R.of_low
    by_grind
    (by rw [g₄ _ by_omega by_omega by_omega by_omega by_omega by_omega, R.h90])
    (by rw [g₄ _ by_omega by_omega by_omega by_omega by_omega by_omega, R.chain.h91])
    (by rw [g₄ _ by_omega by_omega by_omega by_omega by_omega by_omega, R.h92])
    (by rw [g₄ _ by_omega by_omega by_omega by_omega by_omega by_omega, R.chain.h93])
    (by rw [g₄ _ by_omega by_omega by_omega by_omega by_omega by_omega, R.chain.h96])
  have hm₄ : ∀ a, a < A₀ → d₄.nmem a = m₀ a := by_simp_all
  have fr₄ : FrameB Scr d d₄ := ((exec_frameB e₁ by_decide).trans
    (exec_frameB e₂ by_decide)).trans ((exec_frameB e₃ by_decide).trans
      ztjuw)
  have hI₄ := hE.stable _ _ _ hI fr₄
  have b38 : d₄.nreg 150038 = if s.edge ≤ 5 ∨ s.edge = 2 * C.m + 6 then 1 else 0 := by
    zuber
  have b37 : d₄.nreg 150037 = uIx s.edge := by
    zuber
  have b39 : d₄.nreg 150039 = if e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6 then 1 else 0 := by
    zuber
  have b30 : d₄.nreg 150030 = uIx e.edge := by
    zuber
  have b41 : d₄.nreg 150041 = fOf C.m e.edge := by
    zuber
  have b43 : d₄.nreg 150043 = 0 := by_rfl
  -- the first piece
  obtain ⟨d₅, k₅, p₁, ex₅, hk₅, hI₅, hp₁, hp₁s, hdone, hndone, kp₅, mem₅⟩ :=
    first_exec S hE (ps₀ := ps₀) d₄ w₄ R₄ b38 b37 b39 b30 hI₄ hs he hs1 he1
  have w₅ := ex₅.wb_right
  have R₅ := R₄.of_low
    (fun r h1 h2 h3 => kp₅ r ztec by_omega by_omega)
    (by rw [kp₅ _ ztii by_omega by_omega, R₄.h90])
    (by rw [kp₅ _ ztii by_omega by_omega, R₄.chain.h91])
    (by rw [kp₅ _ ztii by_omega by_omega, R₄.h92])
    (by rw [kp₅ _ ztii by_omega by_omega, R₄.chain.h93])
    (by rw [kp₅ _ ztii by_omega by_omega, R₄.chain.h96])
  have hm₅ : ∀ a, a < A₀ → d₅.nmem a = m₀ a := fun a ha => by_grind
  have c91 := R₅.chain.h91
  have hpre : ∀ {d' : Config} {k : ℕ}, Exec P W _ d₅ d' k →
      Exec P W ztqor d d' _ := fun ex => by
    unfold general; exact .seq ztyv (.seq e₃ (.seq e₄ (.seq ex₅ ex)))
  have hGc : ztxit := by_grind
  by_cases hd43 : d₅.nreg 150043 < d₅.nreg 150091
  · -- the main loop and the last piece
    have hnd : ztmxj := by_grind
    obtain ⟨hp₁e, h40, h43⟩ := hndone hnd
    obtain ⟨U₀, F, hU₀, hksU, hF, hUF, hFU, hFT, hfin1, hfin2⟩ :=
      plan C _ hs he hs1 he1 hsame hnd
    set ks := (chainModel C).key _ s
    set ke := (chainModel C).key _ e
    zufhn

    have hTle : ks + len ((2 * C.m + 7 : ℕ) : ℝ) ks ke ≤ ks + ((2 * C.m + 7 : ℕ) : ℝ) := by
      have := len_le ((2 * C.m + 7 : ℕ) : ℝ) ks ke kS.1 kE.2; linarith
    -- the flag
    obtain ⟨d₆, k₆, e₆, hk₆, o42, r₆, m₆⟩ := setFlag_exec (P := P) d₅ w₅ by_omega
    zujb
    have a40 : d₆.nreg 150040 = U₀ % n := by rw [r₆ _ by_omega, h40, hU₀]
    have a41 : d₆.nreg 150041 = F % n := by
      rw [r₆ _ by_omega, kp₅ _ ztii by_omega by_omega, b41, hF]
    have hc0 : 6 ≤ U₀ % n ∧ U₀ % n ≤ 2 * C.m + 6 := by
      rw [hU₀]; unfold c0Of; split_ifs <;> omega
    have hf : 6 ≤ F % n ∧ F % n ≤ 2 * C.m + 5 := by
      zvoij; unfold fOf; split_ifs <;> omega
    have hUof : Uof U₀ n _ = U₀ := Uof_eq by_omega le_rfl by_omega
    have L : LStat C U₀ F γ := ⟨hUF, hFU, hf.1, hf.2, fun v L hv hvF h6 hL => le_trans
      (arcWt_ge C kS kE ⟨0, by_ring⟩ (T_unw ks ke _) hTle h6 hL
        (by have : (U₀ : ℝ) ≤ v := by exact_mod_cast hv
            linarith)
        (by have : ((v + L : ℕ) : ℝ) ≤ F := by exact_mod_cast hvF
            grind)) hwt⟩
    have hI₆ := hE.stable _ _ _ hI₅ ztnyb
    have hL0 : LoopI P C H Hh MD h γ mode s e m₀ A₀ W I ztfif U₀ F
        (mu C (Qof P).n H F U₀) d₆ d₆ := by
      refine ⟨w₆, R₅.of_frame' (fun r h1 h2 h3 h4 => r₆ r h4) (by zunde; exact R₅.h90)
        (by zunde; omega) (by zunde; exact R₅.h92)
        (by zunde; exact R₅.chain.h93) (by zunde; exact R₅.chain.h96),
        fun a ha => by_grind, by_omega, by_omega,
        by omega, by_grind, ?_, [], ?_, by_grind,
        by simp, by rw [a40, hUof]; simp⟩
      · rw [o42, a40, hUof, show d₅.nreg 150040 = U₀ % n by rw [h40, hU₀],
          show d₅.nreg 150041 = F % n by rw [← a41, r₆ _ by_omega]]
        exact flag_of by_omega hUF by_omega
      · rw [a40, hUof]; rfl
    obtain ⟨d₇, k₇, e₇, hL₇, hU₇, hk₇⟩ := mainLoop_exec S hE L d₆ a41 d₆ hL0
    obtain ⟨w₇, R₇, hm₇, hk₇', -, -, -, -, loop, hpath, hI₇, hok₇, hcnt⟩ := hL₇
    rw [hU₇] at hpath hcnt
    -- the last piece
    obtain ⟨d₈, k₈, fin, e₈, hk₈, hI₈, hok₈, hfinY, hfinN, mem₈⟩ := final_exec S hE hD hMD hHh d₇ w₇ hm₇ R₇
      (by rw [hk₇' _ by_omega by_omega by_omega by_omega, r₆ _ by_omega,
        kp₅ _ ztii by_omega by_omega, b39]) hI₇ he he1
    -- the pieces
    have hfin : (fin = [pVE (F % n) e] ∧ (F : ℝ) < ks + len ((2 * C.m + 7 : ℕ) : ℝ) ks ke) ∨
        (fin = [] ∧ (F : ℝ) = ks + len ((2 * C.m + 7 : ℕ) : ℝ) ks ke) := by
      by_cases hc : InUB C.m e.edge ∨ 0 < (chainModel C).param zta e
      · grind
      grind
    have hok : ∀ pc ∈ p₁ :: ztcdj, PcOK P C m₀ h γ pc := by
      zujbk
      zucyl
      · omega
      · zujcl
        · exact hok₇ pc hpc
        · exact hok₈ pc hpc
    have arc := arcOK_general hs he hs1 he1 hp₁s by_grind by_omega
      hpath hfin hok
    -- the count
    have hμ : mu C (Qof P).n H F U₀ ≤ 1031 := by
      have h1 := mu_le (C := C) (nQ := (Qof P).n) (H := H) F U₀
      have h2 := card_brkU_le (C := C) (nQ := (Qof P).n)
        (by zupbg; omega) (by zupbg; exact S.hwf) (U := U₀) (F := F) by_omega
      have := S.hlen
      omega
    have hfinL : fin.length ≤ 1 := by rcases hfin with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    refine ⟨d₈, _, p₁ :: ztcdj, hpre (.ifLtN_true hd43 (.seq e₆ ztjdu)), ?_,
      by simpa using hI₈, arc, hok, ?_, fun a ha => by rw [mem₈ a ha]; exact hm₇ a ha⟩
    · have hcl : ztxhl * mu C (Qof P).n H F U₀ ≤
          ztxhl * 1031 := Nat.mul_le_mul_left _ hμ
      rw [a40, hUof] at hk₇
      unfold genCost
      have := S.hlen
      omega
    · simp only [List.length_cons, List.length_append]
      have e1 : 2 * ztir * mu C (Qof P).n H F U₀ ≤ 2 * ztir * 1031 :=
        Nat.mul_le_mul_left _ hμ
      grind
  · -- a single piece
    have hd : Done C.m s.edge e.edge := by
      grind
    obtain ⟨hp₁e, -⟩ := hdone hd
    refine ⟨d₅, _, [p₁], hpre (.ifLtN_false hd43 (.skip w₅)), ?_, hI₅,
      arcOK_single hs he hs1 he1 hp₁s hp₁e, by_grind, ?_, hm₅⟩
    · unfold genCost; omega
    grind
