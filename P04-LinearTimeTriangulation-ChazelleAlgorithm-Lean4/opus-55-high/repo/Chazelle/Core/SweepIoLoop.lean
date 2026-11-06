module

public import Chazelle.MacT
public import Chazelle.Core.SweepIoBruteLoop
public import Chazelle.Core.SweepIoLHit3
public import Chazelle.Core.SweepIoGather
public import Chazelle.Core.SweepEvEnv
public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.SweepIoHoles

namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
@[expose] public section
def allocB : Stmt :=
  block [.addN ALLOC ALLOC K4, .addN pJ pJ K1, .constN (sw 5003) 0, .constN (sw 5004) 0]

/-- The step of the query loop. -/
def incB : Stmt := block [.addN pJ pJ K1, .addN pA pA K3, .addN pR pR K4]

/-- **The query loop.** -/
def loopS (qry : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .seq (block [.constN pJ 0]) (.seq (.whileLtN pJ ztgml allocB)
    (.seq (block [.constN pJ 0, .copyN pA ztfiw, .copyN pR ztbor])
      (.whileLtN pJ ztgml (.seq ztwcd incB))))

/-! ## Lemmas -/
variable {α : Type} {R : List α} {r d : α}
theorem getD_snoc_lt {k : ℕ} (hk : k < R.length) :
    (R ++ [r]).getD k d = R.getD k d := by
  grind
theorem getD_snoc_eq : (R ++ [r]).getD R.length d = r := by
  simp
theorem loop_cost_le {n A₁ Fg T κ S : ℕ}
    (hS : S ≤ n * (κ * ztbbs) + 5 * (κ * ztjgo * ztclk) + 5 * n) :
    1 + (6 * n + 2 + (3 + ztenx)) ≤
      ztpum * ztkk * ztbbs + ztpum * ztjgo * ztclk := by
  grind
section exec
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem allocB_irs (hI : IInv W c₀ c) (hK : Consts c) (hroom : c.nreg ALLOC + 4 ≤ W)
    (hj : c.nreg pJ + 1 ≤ W) :
    IRS P W c₀ allocB c 4 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 4 ∧
      c'.nreg pJ = c.nreg pJ + 1 ∧
      (∀ r, r ≠ ALLOC → r ≠ pJ → r ≠ sw 5003 → r ≠ sw 5004 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  zubgn
  zukia
  zubod
  zukfi
  have hj' : ztrgc := hj
  have ex : ∃ c' k, Exec P W (block [.addN 9999 9999 240613, .addN 245000 245000 240611,
      .constN 245003 0, .constN 245004 0]) c c' k ∧ k = 4 ∧ c'.nreg 9999 = c.nreg 9999 + 4 ∧
      c'.nreg 245000 = c.nreg 245000 + 1 ∧
      (∀ r, r ≠ 9999 → r ≠ 245000 → r ≠ 245003 → r ≠ 245004 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    simp_all
  zubtw
  refine IRS.ofExec hI ex by_omega (fun r hr hra => h3 r hra ?_ ?_ ?_) h5
    by_simp_all h6 h7 ztljk
    ztjqi ⟨h1, h2, h3, h4⟩
  · zujc
  · zujc
  · zujc
theorem incB_irs (hI : IInv W c₀ c) (hK : Consts c) (h1 : c.nreg pJ + 1 ≤ W)
    (h2 : c.nreg pA + 3 ≤ W) (h3 : c.nreg pR + 4 ≤ W) :
    IRS P W c₀ incB c 3 (fun c' => c'.nreg pJ = c.nreg pJ + 1 ∧ c'.nreg pA = c.nreg pA + 3 ∧
      c'.nreg pR = c.nreg pR + 4 ∧
      (∀ r, r ≠ pJ → r ≠ pA → r ≠ pR → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  zubgn
  have k3 : ztunx := hK.2.2.2.2.2.2
  zukia
  zubod
  have h1' : ztrgc := h1
  have h2' : c.nreg 245001 + 3 ≤ W := h2
  have h3' : c.nreg 245002 + 4 ≤ W := h3
  have ex : ∃ c' k, Exec P W (block [.addN 245000 245000 240611, .addN 245001 245001 240616,
      .addN 245002 245002 240613]) c c' k ∧ k = 3 ∧ c'.nreg 245000 = c.nreg 245000 + 1 ∧
      c'.nreg 245001 = c.nreg 245001 + 3 ∧ c'.nreg 245002 = c.nreg 245002 + 4 ∧
      (∀ r, r ≠ 245000 → r ≠ 245001 → r ≠ 245002 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    simp_all
  obtain ⟨c', k, ex, hk, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ex
  refine IRS.ofExec hI ex by_omega (fun r hr hra => e4 r ?_ ?_ ?_) e6
    by_simp_all e7 e8 by_grind
    (by rw [e4 _ by_decide by_decide by_decide]; omega)
    ⟨e1, e2, e3, e4, e5⟩
  · zujc
  · zujc
  · zujc
end exec

/-! ## The loop -/
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
open Classical in
/-- **The query loop** from the per-query procedure (piece H). -/
theorem loopSpec_of {Aux : Polygon → Merge.Junction → NF → Config → Prop} (hq : QrySpec Aux)
    (hT : TopCountSpec) : LoopSpec Aux := by
  obtain ⟨qry, κq, hqry⟩ := hq
  refine ⟨loopS qry, fun D => 5 * κq D + 21, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ J H N₁ N₂ E L i hB hroom
  have hI₀ : ztulc := ⟨hB.hw, by_omega, le_rfl, by_omega, fun _ _ => rfl⟩
  set n := L.length with hn
  set f : ℕ → ℕ := fun j => qCost κq F c₀ J P N₁ N₂ L i j with hf
  have hsum := qCost_sum (κ := κq) (F := F) (c₀ := c₀) (N₁ := N₁) hT hB.hA.hG hB.hA.hP
    hB.hA.hNF₂ hB.hend
  have hS : ∑ j ∈ Finset.range n, ztlns ≤
      n * (κq zto * ztwit) +
        5 * (κq zto * ztyz * ztwju) + 5 * n := by
    have hsum' : ∑ j ∈ Finset.range n, f j ≤
        n * (κq _ * (F _ + c₀.nreg TLR + 1)) +
          5 * (κq _ * ztyz * (F _ + 1)) := hsum
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  have hcost := loop_cost_le hS
  unfold loopCost at hroom ⊢
  zubmr
  zuinn
  have hK₀ := hB.hA.hK
  have hn9 : c₀.nreg _ = n := hB.hLn
  have hnW : ztskn := by_omega
  have hAW : c₀.nreg ALLOC ≤ W := hB.hw.1 _
  zumby
  have h11 := hB.hres
  -- the cost of the whole loop
  refine (IRS.seq (K₁ := 1)
    ((IRS.block [.constN pJ 0] hI₀ ⟨⟨iscr_sw by_decide by_decide,
      Nat.zero_le _⟩, trivial⟩).mono le_rfl (fun _ h => h)) ?_).mono hcost (fun _ h => h)
  zubun
  have j1 : c₁.nreg pJ = 0 := by zvmxj; rfl
  -- 1. the allocation
  let Ia : Config → Prop := fun c => c.nreg pJ ≤ n ∧ c.nreg ALLOC = c₀.nreg ALLOC + 4 * c.nreg pJ
  have hA1e : c₁.nreg ALLOC = c₀.nreg ALLOC := by
    zvmxj; rfl
  refine IRS.seq
    ((IRS.whileP Ia (fun c => 6 * (n - c.nreg pJ))
      (fun c hI hc hlt hrm => ⟨4, (allocB_irs hI (hK₀.fix hI)
        by_omega
        by_omega).mono le_rfl
        (fun c' h => by
          obtain ⟨a1, a2, -, -⟩ := h
          rw [hI.hin ztgml by_trivial, hn9] at hlt
          omega)⟩)
      hI₁ by_omega by_omega).mono by_omega
      ztb)
    ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨⟨ja, ha⟩, hex⟩
  rw [hI₂.hin ztgml by_trivial, hn9] at hex
  have hj2 : c₂.nreg pJ = n := by_omega
  have hA2e : c₂.nreg ALLOC = c₀.nreg ALLOC + 4 * n := by_omega
  -- 2. the loop registers
  zuheh
  refine IRS.seq
    ((IRS.block [.constN pJ 0, .copyN pA _, .copyN pR _] hI₂
      ⟨⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩,
        iscr_sw by_decide by_decide,
        iscr_sw by_decide by_decide, trivial⟩).mono le_rfl
      ztb) ?_
  rintro c₃ hI₃ hA₃ hA₃' hc₃
  have v3 : c₃.nreg pJ = 0 ∧ c₃.nreg pA = c₀.nreg ztfiw ∧ c₃.nreg pR = c₀.nreg ztbor ∧
      c₃.nreg ALLOC = c₂.nreg ALLOC ∧ c₃.nmem = c₂.nmem := by
    zumnd
    simp only [regB, regI, upd, pJ, pA, pR, sw,
      ALLOC]
    refine ⟨by_simp, by simp; exact hI₂.hin _ by_trivial,
      by simp; exact hI₂.hin _ by_trivial, by_simp, trivial⟩
  obtain ⟨j3, p3, r3, a3, m3⟩ := v3
  -- 3. the queries
  let Iq : Config → Prop := fun c => ∃ j, c.nreg pJ = j ∧ j ≤ n ∧ c.nreg ztgml = n ∧
    c.nreg pA = c₀.nreg ztfiw + 3 * j ∧ c.nreg pR = c₀.nreg ztbor + 4 * j ∧
    c₀.nreg ztbor + 4 * n ≤ c.nreg ALLOC ∧
    ∃ R : List _, R.length = j ∧ ResultListAt c.nmem ztbahc R ∧
      ∀ j', j' < j → SeesInWhole J zta i (L.getD j' ztt) (R.getD j' ztlt)
  have hIq₃ : Iq c₃ := ⟨0, j3, Nat.zero_le _, by rw [hI₃.hin _ by_trivial, hn9],
    by omega, by_omega,
    by omega, [], rfl, fun k hk => by_tauto, fun k hk => by_omega⟩
  have hΦ₃ : ∑ k ∈ Finset.Ico (c₃.nreg pJ) n, zthwo = ∑ j ∈ Finset.range n, ztlns := by
    rw [j3, Finset.range_eq_Ico]
  refine (IRS.whileP Iq
    (fun c => ∑ k ∈ Finset.Ico ztvjv n, zthwo) ?_ hI₃ hIq₃
    by_omega).mono (by rw [hΦ₃]) ?_
  · -- one query
    rintro c hI ⟨j, hj, hjn, h9, hpA, hpR, hAl, R, hRl, hRat, hRs⟩ hlt hrm
    rw [h9, hj] at hlt
    have hsplit : ∑ k ∈ Finset.Ico ztvjv n, zthwo =
        ztlns + ∑ k ∈ Finset.Ico ztl n, zthwo := by
      rw [hj, Finset.sum_eq_sum_Ico_succ_bot hlt]
    have hrq : c.nreg ALLOC + qCost κq F c₀ J P N₁ N₂ L i j ≤ W := by
      rw [hsplit] at hrm
      have : f j = qCost κq F c₀ J P N₁ N₂ L i j := rfl
      omega
    refine ⟨f j + 3, (IRS.seq (hqry sh Bs F X Ok hsh hBs hXl P W c₀ c J H
      N₁ N₂ E L i j hB hI hj hlt hpA hpR by_omega hrq) ?_).mono le_rfl
      ztb⟩
    rintro c' hI' hA' hA'' ⟨⟨r, q0, q1, q2, q3, hsee⟩, hmem, hreg, hAm⟩
    have kreg := hreg
    have cJ := (kreg pJ by_rfl by_decide).trans hj
    have cA : c'.nreg pA = c₀.nreg _ + 3 * j :=
      (kreg pA by_decide by_decide).trans hpA
    have cR : c'.nreg pR = c₀.nreg _ + 4 * j :=
      (kreg pR by_decide by_decide).trans hpR
    have hW' : c'.nreg ALLOC ≤ W := hI'.hw.1 _
    refine (incB_irs hI' (hK₀.fix hI') by_omega by_omega
      by_omega).mono le_rfl ?_
    rintro c'' ⟨e1, e2, e3, e4, e5⟩
    have hAc : ztsdz :=
      e4 _ by_decide by_decide
        by_decide
    have c9 : c''.nreg ztgml = n := by
      rw [e4 _ by_decide by_decide by_decide,
        hI'.hin _ by_trivial, hn9]
    refine ⟨⟨j + 1, by_omega, by_omega, c9, by_omega, by_omega,
      by rw [hAc]; omega, R ++ [r], by simp [hRl], fun k hk => ?_, fun k hk => ?_⟩, ?_⟩
    · zujhx
      zuhpg
      rcases (show k < R.length ∨ k = R.length by omega) with hk' | hk'
      · rw [getD_snoc_lt hk']
        obtain ⟨b0, b1, b2, b3⟩ := hRat k hk'
        have hb : c₀.nreg ztbor + 4 * k + 3 < c.nreg pR := by_omega
        have hb' : c₀.nreg ztbor + 4 * k + 3 < c.nreg ALLOC := by_omega
        zudfi
        · zunef; exact b0
        · zunef; exact b1
        · zunef; exact b2
        · zunef; exact b3
      · zujpq
        rw [getD_snoc_eq]
        have hpos : c₀.nreg ztbor + 4 * R.length = c.nreg pR := by_omega
        zudul
        omega
    · rcases (show k < j ∨ k = j by omega) with hk' | hk'
      · rw [getD_snoc_lt by_omega]; exact hRs k hk'
      · zujpq
        rw [← hRl, getD_snoc_eq]; zuovi; omega
    · rw [e1, cJ, hsplit]; omega
  · -- the end
    rintro c' ⟨⟨j, hj, hjn, h9, -, -, hAl, R, hRl, hRat, hRs⟩, hex⟩
    rw [h9, hj] at hex
    have hjn' : j = n := by_omega
    subst hjn'
    exact ⟨R, hRl, hAl, hRat, hRs⟩
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Set
open Chazelle.Chain (IsHChordIn)
open Sweep
@[expose] public section
variable {D : Set Point}
/-- A horizontal chord of a domain is determined by its height and its left end. -/
theorem hchord_right_eq {y a b b' : ℝ} (h : IsHChordIn D y a b)
    (h' : IsHChordIn D y a b') : b = b' := by
  zuct
  zujek
  · exact h.right_not (h'.open_mem b h.lt hlt)
  · exact h'.right_not (h.open_mem b' h'.lt hlt)

/-- A horizontal chord of a domain is determined by its height and its right end. -/
theorem hchord_left_eq {y a a' b : ℝ} (h : IsHChordIn D y a b)
    (h' : IsHChordIn D y a' b) : a = a' := by
  zuct
  zujek
  · exact h'.left_not (h.open_mem a' hlt h'.lt)
  · exact h.left_not (h'.open_mem a hlt h.lt)

/-- The chord records of a normal form of a chain model are augmented chords. -/
theorem chord_aug {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF ztc Q N) {k : ℕ}
    (hk : k < N.nChords) :
    ∃ y a b : ℝ, IsHChordIn C.dom y a b ∧ (N.chord k).toSet ztc Q = Visibility.hseg y a b ∧
      Merge.lend ztymk = ztdv ∧
      Merge.rend ztymk = ztdy := by
  have hmem : ztxcx := by
    zuno

  obtain ⟨y, a, b, hH, -, heq, hl, hr⟩ :=
    Merge.augChords_spec ztglw
  simp_all

/-- Two endpoint queries of the same parity with the same origin are equal. -/
theorem endOrigin_inj {J : Merge.Junction} {Q : Polygon} {N : NF}
    (hN : IsNF ztj Q N) {j j' : ℕ} (hj : j < 2 * N.nChords)
    (hj' : j' < 2 * N.nChords) (hp : j % 2 = j' % 2)
    (h : endOrigin J Q N j = endOrigin J Q N j') : j = j' := by
  obtain ⟨y, a, b, hH, heq, hl, hr⟩ := chord_aug hN (k := j / 2) by_omega
  obtain ⟨y', a', b', hH', heq', hl', hr'⟩ := chord_aug hN (k := j' / 2) by_omega
  have hset : (N.chord ztwm).toSet ztj Q =
      (N.chord (j' / 2)).toSet ztj Q := by
    rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
    · simp only [endOrigin, h0, show j' % 2 = 0 by omega, ↓reduceIte, hl, hl'] at h
      zueii

      rw [heq, heq', hchord_right_eq hH hH']
    · simp only [endOrigin, h1, show j' % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte, hr,
        hr'] at h
      zueii

      rw [heq, heq', hchord_left_eq hH hH']
  have := hN.2.1 _ _ by_omega by_omega hset
  omega

/-- **At most two endpoint queries start at the top of `C₂`.** -/
theorem topCount : TopCountSpec := by
  intro P J N₂ _ _ hN
  classical
  set l := (List.range ztbxu).filter
    ztxqw with hl
  have hnd : l.Nodup := (List.nodup_range).filter _
  zukzf
  have hmem : ∀ j ∈ l.toFinset, j < 2 * N₂.nChords ∧ endOrigin J zta N₂ j = J.right.top := by
    simp_all
  calc l.toFinset.card ≤ (Finset.range 2).card :=
        Finset.card_le_card_of_injOn (fun j => j % 2)
          (fun j _ => by_grind)
          (fun j hj j' hj' h => by
            zuxm

            exact endOrigin_inj hN h1 h1' h ztqpb)
    _ = 2 := Finset.card_range 2
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
open Sweep WalkEmbed
@[expose] public section
theorem origin_ray (C : Chain) {o z : Point} {d : ℝ} (_hd : d = 1 ∨ d = -1)
    (hz : z ∈ Merge.shoot C o d) (hzd : z ∉ C.dom) (hne : z ≠ o) :
    0 < C.hitParam o d ∧ z = rayPt o d (C.hitParam o d) := by
  set h := C.hitParam o d with hh
  have h0 : 0 ≤ h := Merge.hitParam_nonneg C o d
  obtain ⟨s, hs0, hs1, hzs⟩ := hz
  simp only [rayPt_fst, rayPt_snd, sub_self, mul_zero, add_zero] at hzs
  have hzs' : z = rayPt o d (s * h) := by
    rw [hzs]; ext <;> simp only [rayPt_fst, rayPt_snd]; ring
  have hsh : 0 < s * h := by
    rcases (mul_nonneg hs0 h0).lt_or_eq with h1 | h1
    · zubvv
    grind
  have hle : h ≤ s * h := Chain.hitParam_le_of_not_mem_dom C o d hsh by_simp_all
  have hpos : 0 < h := by
    rcases h0.lt_or_eq with h1 | h1
    · zubvv
    grind
  have hs : s = 1 := by
    have : 1 * h ≤ s * h := by_linarith
    have := le_of_mul_le_mul_right this hpos
    linarith
  simp_all

/-- The origin as a point of the ray from `z` in the opposite direction. -/
theorem origin_back {o : Point} {d τ : ℝ} {z : Point} (hz : z = rayPt o d τ) :
    o = rayPt z (-d) τ := by
  zvncr; ext <;> simp [rayPt_fst, rayPt_snd]

/-- **A candidate origin** for the walk point `w` and the direction `d`. -/
def CandAt (J : Merge.Junction) (o : Point) (d : ℝ) (w : Point) : Prop :=
  o ∉ J.whole.dom ∧ o ∉ J.right.dom ∧ w ∈ Merge.shoot J.whole o d
variable {J : Merge.Junction}
/-- **The ray to a candidate origin.**  For a point `z` of the domain of `C₂` off the domain of
`C`, a candidate origin is `rayPt z (-d) τ` with `τ = C.hitParam o d > 0`. -/
theorem cand_ray {o z : Point} {d : ℝ} (hd : d = 1 ∨ d = -1)
    (h : CandAt J o d z) (hz : z ∈ J.right.dom) (hzw : z ∉ J.whole.dom) :
    0 < J.whole.hitParam o d ∧ o = rayPt z (-d) ztemx := by
  have hne : z ≠ o := fun he => h.2.1 ztjxs
  obtain ⟨hp, hr⟩ := origin_ray J.whole hd h.2.2 hzw hne
  exact ⟨hp, origin_back hr⟩

/-- **Uniqueness of the candidate origin.** -/
theorem cand_unique {o₁ o₂ z : Point} {d : ℝ} (hd : d = 1 ∨ d = -1)
    (h₁ : CandAt J o₁ d z) (h₂ : CandAt J o₂ d z) (hz : z ∈ J.right.dom)
    (hzw : z ∉ J.whole.dom) : o₁ = o₂ := by
  obtain ⟨p₁, e₁⟩ := origin_ray J.whole hd h₁.2.2 hzw (fun he => h₁.2.1 ztjxs)
  obtain ⟨p₂, e₂⟩ := origin_ray J.whole hd h₂.2.2 hzw (fun he => h₂.2.1 ztjxs)
  set t₁ := J.whole.hitParam o₁ d
  set t₂ := J.whole.hitParam o₂ d
  have hy : o₁.2 = o₂.2 := by
    have a := congrArg Prod.snd e₁; have b := congrArg Prod.snd e₂
    simp only [rayPt_snd] at a b; simp_all
  have hx : o₁.1 + d * t₁ = o₂.1 + d * t₂ := by
    have a := congrArg Prod.fst e₁; have b := congrArg Prod.fst e₂
    zvogc at a b; simp_all
  have hdd : d * d = 1 := by_grind
  -- the nearer origin blocks the chord of the farther one
  have key : ∀ (a b : Point) (ta tb : ℝ), a.2 = b.2 → a.1 + d * ta = b.1 + d * tb →
      0 < ta → ta < tb → tb = J.whole.hitParam b d → a ∉ J.whole.dom → False := by
    intro a b ta tb hab hxab h0 hlt htb ha
    have hpt : a = rayPt b d (tb - ta) := by
      ext
      · zudch
      simp_all
    have := Chain.hitParam_le_of_not_mem_dom J.whole b d (t := tb - ta) by_linarith
      by_simp_all
    linarith
  rcases lt_trichotomy t₁ t₂ with hl | he | hl
  · exact (key o₁ o₂ t₁ t₂ hy hx p₁ hl rfl h₁.1).elim
  · grind
  · exact (key o₂ o₁ t₂ t₁ hy.symm hx.symm p₂ hl rfl h₂.1).elim

/-! ## The query point -/

/-- A point of `C₁` other than the shared vertex, not above the top of `C₂`, is in the domain
of `C₂`. -/
theorem z_mem_right_dom {J : Merge.Junction} (hP : J.P.Simple) {z : Point} (hz : z ∈ J.left.set)
    (hzs : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2) : z ∈ J.right.dom := by
  zumv
  rcases (Merge.not_mem_dom_iff J.right hz2).1 h with h1 | h1
  · exact h1 (J.left.set_subset_box hz)
  · have : ztmxf := ⟨hz, h1⟩
    zuigq
    simp_all

/-- A point of `C₁` is off the domain of `C`. -/
theorem z_not_mem_whole_dom {J : Merge.Junction} {z : Point} (hz : z ∈ J.left.set) :
    z ∉ J.whole.dom :=
  J.whole.set_subset_dom_compl (J.left_set_subset hz)

/-! ## The origins -/

/-- The chord sets of a normal form of the model of `C₂` are augmented chords. -/
theorem chord_mem_F {M : Model} {Q : Polygon} {N : NF} {k : ℕ} (hk : k < N.nChords) :
    (N.chord k).toSet M Q ∈ N.F M Q := by
  zuno

/-- **The ends of the chords of `N₂` are off the domains** of `C₂` and of `C`. -/
theorem endOrigin_not_dom (J : Merge.Junction) {Q : Polygon} {N : NF}
    (hN : IsNF ztj Q N) {j : ℕ} (hj : j < 2 * N.nChords) :
    endOrigin J Q N j ∉ J.right.dom ∧ endOrigin J Q N j ∉ J.whole.dom := by
  zufux
  have hmem := chord_mem_F (M := chainModel J.right) (Q := Q) hk
  have haug : (N.chord ztwm).toSet ztj Q ∈ Merge.augChords J.right :=
    hN.1.2.1 hmem
  obtain ⟨y, a, b, hH, -, -, hl, hr⟩ := Merge.augChords_spec haug
  have hw := end_not_mem_dom J (S₂ := N.F ztj Q) (fun c hc => hN.1.2.1 hc) hmem
  zulbr
  split_ifs
  · zvnen; exact ⟨hH.left_not, hl ▸ hw.1⟩
  · zvnel; exact ⟨hH.right_not, hr ▸ hw.2⟩

/-- A point of `C₂` is off both domains. -/
theorem right_not_dom (J : Merge.Junction) {a : Point} (ha : a ∈ J.right.set) :
    a ∉ J.right.dom ∧ a ∉ J.whole.dom :=
  ⟨J.right.set_subset_dom_compl ha, J.whole.set_subset_dom_compl ztuzf⟩

/-- **The origins of the stop records are off both domains.** -/
theorem stopOrig_not_dom (J : Merge.Junction) {Q : Polygon} {N : NF}
    (hN : IsNF ztj Q N) {kind k b : ℕ} (_hkind : kind ≤ 2)
    (hk : kind = 1 → k < N.nChords) :
    stopOrig J Q N kind k b ∉ J.right.dom ∧ stopOrig J Q N kind k b ∉ J.whole.dom := by
  unfold stopOrig
  zufqu
  · rw [ite_eq_left h0]; exact right_not_dom J J.shared_mem_right
  · zucqa
    zubsx
    · zubel
      have := hk h1
      exact endOrigin_not_dom J hN by_grind
    · rw [ite_eq_right h1]; exact right_not_dom J J.right.top_mem_set

/-- The chord of a stop record is the chord seen from its origin. -/
theorem stopSet_eq (J : Merge.Junction) (Q : Polygon) (N : NF) (kind k b : ℕ) :
    stopSet J Q N kind k b = Merge.shoot J.whole (stopOrig J Q N kind k b) ztkz := by
  unfold stopSet stopOrig
  grind

/-! ## Offsets and keys -/

/-- **Offsets are injective** on the keys of a cycle. -/
theorem off_inj {n g x y : ℝ} (_hg0 : 0 ≤ g) (_hgn : g < n) (hx0 : 0 ≤ x) (hxn : x < n)
    (hy0 : 0 ≤ y) (hyn : y < n) (h : off n g x = off n g y) : x = y := by
  zuhqx

/-- A key with parameters in `[0, 1)` determines its edge and parameter. -/
theorem key_split {e e' : ℕ} {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (ht0' : 0 ≤ t')
    (ht1' : t' < 1) (h : (e : ℝ) + t = e' + t') : e = e' ∧ t = t' := by
  have hee : e = e' := by
    have h1 : (e : ℝ) < e' + 1 := by_linarith
    have h2 : (e' : ℝ) < e + 1 := by_linarith
    have h1' : e < e' + 1 := by exact_mod_cast h1
    have h2' : e' < e + 1 := by exact_mod_cast h2
    omega
  simp_all

/-- The parameter of a point on a horizontal ray. -/
theorem rayPt_param {z : Point} {σ τ τ' : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : rayPt z σ τ = rayPt z σ τ') : τ = τ' := by
  have := congrArg Prod.fst h
  zudv
  grind
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
open Sweep WalkEmbed
@[expose] public section
variable (J : Merge.Junction) {Q : Polygon} {N : NF}
theorem gW_lt : (gW J : ℝ) < (chainModel J.whole).W.n := by
  zvokr
  have := tpos_lt J.whole J.m₁
  unfold gW
  exact_mod_cast (by omega : 6 + tpos J.whole J.m₁ < 2 * J.whole.m + 7)

/-- **An attachment of a chord of `F₂⁺` on the `C₁` part is a key of the event log.** -/
theorem cut_key {S₂ : Set ztf} {es : List ztwws}
    (hL : LogOK J S₂ es) {e : Set Point} (he : e ∈ F₂plus J S₂) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hst : (Lst J : ℝ) ≤ oW J ztk) :
    ∃ i, i < es.length ∧ (es.getD i ztfj).1 = p ∧ (es.getD i ztfj).2.1 = t := by
  obtain ⟨hne, hmem, hhead, hsort, hgap, hlast, -⟩ := hL
  zudbn
  set x : ℝ := p + t with hx
  have hpn := hA.1
  zudzr

  zukgw
  have hxn : x < n := by
    have : ztcjz := by exact_mod_cast hpn
    linarith
  have hcut : (chainModel J.whole).IsCut ztbi x := zteyg
  have hlen : 0 < es.length := List.length_pos_iff.2 hne
  -- keys of the log
  let K : ℕ → ℝ := fun i => (es.getD i ztfj).1 + (es.getD i ztfj).2.1
  have hget : ∀ i (hi : i < es.length), es.getD i ztfj = es[i] := fun i hi => by
    zuews
  have hmemi : ∀ i, i < es.length → es.getD i ztfj ∈ es := fun i hi => by
    grind
  have hK0 : oW J (K 0) ≤ oW J x := by
    have h := hhead (es.getD 0 ztfj) (by
      rw [hget 0 hlen, List.head?_eq_getElem?, List.getElem?_eq_getElem hlen]; rfl)
    grind
  -- the last key not after `x`
  set i := Nat.findGreatest (fun i => oW J ztjjf ≤ oW J x) (es.length - 1) with hi
  have hiP : oW J ztjjf ≤ oW J x := Nat.findGreatest_spec (P := fun i => oW J ztjjf ≤ oW J x)
    ztbg hK0
  have hil : i < es.length := by
    have : i ≤ es.length - 1 := Nat.findGreatest_le _
    omega
  have hKi := hmem _ (hmemi i hil)
  have hKi0 : 0 ≤ K i := by_grind
  have hKin : K i < n := by
    have h1 := hKi.1; have h2 := hKi.2.2.1
    have : ((es.getD i ztfj).1 : ℝ) + 1 ≤ n := by exact_mod_cast h1
    grind
  have hgW0 : (0 : ℝ) ≤ gW J := by_positivity
  have heq : oW J ztjjf = oW J x := by
    rcases hiP.lt_or_eq with hlt | h
    · exfalso
      by_cases hnext : i + 1 < es.length
      · have hnot : ¬ oW J (K ztg) ≤ oW J x :=
          Nat.findGreatest_is_greatest (P := fun i => oW J ztjjf ≤ oW J x)
            (n := es.length - 1) (k := i + 1) by_omega by_omega
        exact hgap i hnext x hcut hx0 hxn ⟨hlt, not_le.1 hnot⟩
      · have hlast' : es.getLast? = some (es.getD i ztfj) := by
          rw [List.getLast?_eq_getElem?, hget i hil]
          rw [show es.length - 1 = i by omega, List.getElem?_eq_getElem hil]
        have := hlast _ by_omega x hcut hx0 hxn
        exact this ⟨hlt, off_lt hxn hgW0⟩
    omega
  have hkx : K i = x := off_inj hgW0 ztvrg hKi0 hKin hx0 hxn heq
  obtain ⟨h1, h2⟩ := key_split hKi.2.1 hKi.2.2.1 ht0 ht1 hkx
  grind

/-! ## Records in memory -/
theorem stopRecs_unique {m : ℕ → ℕ} {A : ℕ} {rs rs' : List ztcf}
    (h : StopRecsAt m A rs) (h' : StopRecsAt m A rs') (hl : rs.length = rs'.length) : rs = rs' := by
  zuiqu
  zugoh
  zudqs
  obtain ⟨b1, b2, b3, b4, b5⟩ := h' i hi'
  grind

/-- The key of a log record in the event log. -/
theorem logOf_getD (Q : Polygon) (N : NF)
    {ls : List ztck} {i : ℕ} (hi : i < ls.length) :
    ((logOf J Q N ls).getD i ztfj).1 = (ls.getD i ztem).1 ∧
      ((logOf J Q N ls).getD i ztfj).2.1 = (chainModel J.whole).param Q
        ⟨(ls.getD i ztem).1, (ls.getD i ztem).2.1⟩ := by
  unfold logOf
  simp_all

/-! ## The candidates of the stops and the table -/

/-- **A stop record gives a candidate origin** at its position, attached at a log key. -/
theorem stop_cand
    (hN : IsNF ztj Q N) {rs : List ztcf}
    (hS : StopsOK J ztwzl (stopsOf J Q N rs))
    {r : ℕ × ℕ × ℕ × ℕ × ℕ} (hr : r ∈ rs) (hkind : r.2.2.1 ≤ 2)
    (hk : r.2.2.1 = 1 → r.2.2.2.1 < N.nChords) :
    CandAt J (stopOrig J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2) ztqmb
        (sidePt (chainModel J.whole).W r.1 ztynj) ∧
      stopSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∈ F₂plus J ztwzl ∧
      SideAttach (chainModel J.whole).W (stopSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2) r.1
        ztynj ∧
      (Lst J : ℝ) ≤ oW J (r.1 + (chainModel J.whole).param Q ztbhg) := by
  have hs : (r.1, (chainModel J.whole).param Q ztbhg,
      stopSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2) ∈ stopsOf J Q N rs := by
    unfold stopsOf; grind
  obtain ⟨hF, -, hA, hL⟩ := hS.1 _ hs
  obtain ⟨n1, n2⟩ := stopOrig_not_dom J hN (b := r.2.2.2.2) hkind hk
  refine ⟨ztrdv, hF, hA, hL⟩
  rw [← stopSet_eq]; exact hA.2.2.2.1

/-- **A regular table entry gives a candidate origin** at its position, attached at a log key. -/
theorem tab_cand {T : ℕ → Option zthlt}
    (hT : TabOK J Q N T) {j : ℕ} (hj : j < 2 * N.nChords) (hon : endOrigin J Q N j ∈ J.right.set)
    (hsh : endOrigin J Q N j ≠ J.shared) (htop : endOrigin J Q N j ≠ J.right.top) {p : ℕ}
    {t : ℝ} (hTj : T j = some (p, t)) :
    CandAt J zttr ztri (sidePt (chainModel J.whole).W p t) ∧
      Merge.shoot J.whole zttr ztri ∈ F₂plus J ztwzl ∧
      SideAttach (chainModel J.whole).W ztxmy p t ∧
      (Lst J : ℝ) ≤ oW J ztk := by
  obtain ⟨hfree, hm⟩ := hT j hj hon hsh htop
  zugdm
  obtain ⟨hA, hpt, hL⟩ := hm
  obtain ⟨n1, n2⟩ := right_not_dom J hon
  refine ⟨ztrdv, ?_, hA, hL⟩
  · zubil
    exact ⟨1, zero_le_one, le_rfl, by_grind⟩
  · left
    zufux
    have hc := chord_mem_F (M := chainModel J.right) (Q := Q) hk
    unfold endOrigin endDir at hfree ⊢
    zudww
    · simp only [h, ite_true] at hfree ⊢
      zujby
    · simp only [h, ite_false] at hfree ⊢
      zujby

/-! ## Regular origins by their positions -/

/-- **The regular origins**: on `C₂`, neither the shared vertex nor the top, by a normalised walk
position of the model of `C₂`. -/
theorem valid_iff (J : Merge.Junction) (hP : J.right.P.Simple) (Q : Polygon) {x : WPos}
    (hx : x.edge < (chainModel J.right).W.n) (h0 : 0 ≤ (chainModel J.right).param Q x)
    (h1 : (chainModel J.right).param Q x < 1)
    (hnorm : x.hgt = 0 ↔ (chainModel J.right).param Q x = 0) :
    ((chainModel J.right).pos Q x ∈ J.right.set ∧ (chainModel J.right).pos Q x ≠ J.shared ∧
        (chainModel J.right).pos Q x ≠ J.right.top) ↔
      (6 ≤ x.edge ∧ x.edge ≤ 2 * J.right.m + 5 ∧
        (x.hgt ≠ 0 ∨ (x.edge ≠ 6 ∧ x.edge ≠ 6 + tpos J.right 0 ∧
          x.edge ≠ 6 + midT J.right))) := by
  have hmem := pos_mem_set_iff J.right hP (Q := Q) hx h0 h1 hnorm
  have hsh := atEnd_iff J.right hP (k := 0) ztp Q hx h0 h1
  have htop := atTop_iff J.right hP Q hx h0 h1
  rw [Merge.Junction.right_vertex_zero] at hsh
  grind
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
@[expose] public section
def lsI : ℕ := sw 4000
/-- The target position. -/
def lsxE : ℕ := sw 4020
def lsxH : ℕ := sw 4021

/-- The registers the search may write (outside the oracle bands, besides the allocator). -/
def LSet (r : ℕ) : Prop := sw 4000 ≤ r ∧ r ≤ sw 4019

/-- **The predicate of the search**: the key of log record `j` (in memory `m` at base `AL`) has
a smaller offset from `G` than the target `x`. -/
def lsPr (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (AL G : ℕ) (x : WPos) (j : ℕ) : Prop :=
  off (chainModel J.whole).W.n G
      ((chainModel J.whole).key zta ztzim) <
    off (chainModel J.whole).W.n G ztwqc

/-- **The contract of the binary search in the log.** -/
def LSearchSpec : Prop :=
  ∃ (lsearch : Stmt) (κ : ℕ), ∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (c₀ c : Config),
    IInv W c₀ c → Consts c₀ → ChainCtx P W c ztjl J.whole →
    ztug →
    c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC →
    c.nreg ztex < 2 ^ c.nreg TLR →
    c.nreg ztfx + 7 * c.nreg ztex ≤ c.nreg ALLOC →
    c.nreg ztfg < (chainModel J.whole).W.n →
    (∀ j, j < c.nreg ztex → SweepEv.PosW P J ztwun
      ztwrr) →
    SweepEv.PosW P J ztmgx ztmgy →
    (∀ i j, i ≤ j → j < c.nreg ztex →
      lsPr P J c.nmem ztwml ztwmp ztbih j →
      lsPr P J c.nmem ztwml ztwmp ztbih i) →
    c.nreg ALLOC + κ * ztuc ≤ W →
    IRS P W c₀ lsearch c ztxzd (fun c' =>
      c'.nreg lsI ≤ c.nreg ztex ∧
      (∀ j, j < c'.nreg lsI →
        lsPr P J c.nmem ztwml ztwmp ztbih j) ∧
      (∀ j, c'.nreg lsI ≤ j → j < c.nreg ztex →
        ¬ lsPr P J c.nmem ztwml ztwmp ztbih j) ∧
      ztrn ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth)
open Chazelle.Chain (sidePt)
def sB : ℕ := sw 620

/-- The slot of a stop record with direction code `b` (`0` for east). -/
def sOf (b : ℕ) : ℕ := if b = 1 then 0 else 1

/-- The direction of slot `s`. -/
noncomputable def dS (s : ℕ) : ℝ := if s = 0 then 1 else -1

/-- The address of slot `(i, s)`. -/
def slotA (B i s : ℕ) : ℕ := B + 6 * i + 3 * s

/-- The walk position of log record `i` (memory `m`, base `AL`). -/
def logPos (m : ℕ → ℕ) (AL i : ℕ) : WPos := ⟨m ztbdu, m (AL + 7 * i + 1)⟩

/-- The point of the walk of `C` at log record `i`. -/
noncomputable def logPt (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (AL i : ℕ) : Point :=
  sidePt (chainModel J.whole).W (logPos m AL i).edge
    ((chainModel J.whole).param zta ztbwa)

/-- **A good slot**: flag `≤ 1`; flag `1`: a proper position of the model of `C₂` whose point is a
candidate origin for the point of log record `i` in the direction of the slot. -/
def SlotOK (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (B AL i s : ℕ) : Prop :=
  m ztege ≤ 1 ∧
    (m ztege = 1 →
      m (slotA B i s + 1) < (chainModel J.right).W.n ∧
      ProperPos ztj zta P.n ztcoz ∧
      S0C.CandAt J ((chainModel J.right).pos zta ztcoz)
        ztmiq (logPt P J m AL i))

/-- A regular endpoint query: its origin is a point of `C₂`, neither the shared vertex nor the
top. -/
def ValidO (J : Merge.Junction) (Q : Polygon) (N : NF) (j : ℕ) : Prop :=
  endOrigin J Q N j ∈ J.right.set ∧ endOrigin J Q N j ≠ J.shared ∧
    endOrigin J Q N j ≠ J.right.top

/-- **The slot table** in the configuration `c`. -/
def AuxCore (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c : Config) : Prop :=
  c.nreg sB + 6 * rd c bSweep 301 ≤ c.nreg ALLOC ∧
  rd c bSweep 300 + 7 * rd c bSweep 301 ≤ c.nreg ALLOC ∧
  rd c bSweep 200 + 5 * rd c bSweep 201 ≤ c.nreg ALLOC ∧
  rd c bSweep 302 + 3 * ztbxu ≤ c.nreg ALLOC ∧
  (∀ i, i < rd c bSweep 301 → ∀ s, s ≤ 1 →
    SlotOK P J c.nmem zthvm ztiad i s) ∧
  (∀ x, x < rd c bSweep 201 → ∃ i, i < rd c bSweep 301 ∧
    c.nmem ztmnh = c.nmem ztmng ∧
    (chainModel J.whole).param zta ztzmv =
      (chainModel J.whole).param zta
        ⟨c.nmem ztmng, c.nmem (rd c bSweep 200 + 5 * x + 1)⟩ ∧
    c.nmem (slotA zthvm i (sOf (c.nmem (rd c bSweep 200 + 5 * x + 4)))) = 1) ∧
  (∀ j, j < 2 * N₂.nChords → ValidO J zta N₂ j → c.nmem (rd c bSweep 302 + 3 * j) = 1 →
    ∃ i, i < rd c bSweep 301 ∧
    c.nmem ztmnh = c.nmem ztkww ∧
    (chainModel J.whole).param zta ztzmv =
      (chainModel J.whole).param zta
        ⟨c.nmem ztkww, c.nmem (rd c bSweep 302 + 3 * j + 2)⟩ ∧
    c.nmem (slotA zthvm i ztfsu) = 1)

/-- **The auxiliary fact of the side-0 initialisation**: the slot table, for every configuration
agreeing on the fixed registers (except `sw 11`) and on the memory below a bound `A₀`. -/
def Aux (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c : Config) : Prop :=
  ∃ A₀, A₀ ≤ c.nreg ALLOC ∧ ∀ c' : Config, (∀ q, IFix q → q ≠ sw 11 → c'.nreg q = c.nreg q) →
    ztpt → A₀ ≤ c'.nreg ALLOC → AuxCore P J N₂ c'
variable {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c : Config}
/-- `Aux` is robust along `IInv`. -/
theorem aux_iinv {W : ℕ} {J : Merge.Junction} {N₂ : NF} {c₀ c : Config}
    (h : Aux P J N₂ c₀) (hI : IInv W c₀ c) : Aux P J N₂ c := by
  zucxi
  refine ⟨A₀, le_trans hA₀ hI.hA, fun c' hr hm hA => h c' ztpbt
    ztts hA⟩
  · rw [hr q hq hq11, hI.hin q hq]
  · rw [hm a ha, hI.hm a by_omega]

/-- `Aux` survives a write of `sw 11`. -/
theorem aux_sw11 {v : ℕ}
    (h : Aux P J N₂ c) : Aux P J N₂ { c with nreg := upd c.nreg (sw 11) v } := by
  zucxi
  have hAl : upd c.nreg ztbor v ALLOC = c.nreg ALLOC := upd_other _ _ _ by_decide
  refine ⟨A₀, by_grind,
    fun c' hr hm hA => h c' ztpbt hm hA⟩
  rw [hr q hq hq11]
  exact upd_other _ _ _ hq11
theorem rd_sw (c : Config) (k : ℕ) : rd c bSweep k = c.nreg ztcbe := rfl

/-- **`AuxCore` is local**: it depends only on the fixed registers other than `sw 11` and on the
memory below the allocator. -/
theorem auxCore_transport {c c' : Config}
    (h : AuxCore P J N₂ c) (hr : ∀ q, IFix q → q ≠ sw 11 → c'.nreg q = c.nreg q)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    AuxCore P J N₂ c' := by
  have fx : ∀ k, k < 700 → k ≠ 11 → c'.nreg ztcbe = c.nreg ztcbe := fun k hk h11 =>
    hr _ ztze ztce
  obtain ⟨b1, b2, b3, b4, hsl, hst, htb⟩ := h
  simp only [AuxCore, rd_sw] at *
  have eB : ztiyz := fx 620 by_norm_num by_norm_num
  have e200 := fx 200 by_norm_num by_norm_num
  have e201 := fx 201 by_norm_num by_norm_num
  have e300 := fx 300 by_norm_num by_norm_num
  have e301 := fx 301 by_norm_num by_norm_num
  have e302 := fx 302 by_norm_num by_norm_num
  rw [eB, e200, e201, e300, e301, e302]
  set B := c.nreg sB
  set AL := c.nreg ztfx
  set E := c.nreg ztex
  set AS := c.nreg ztcwm
  set S := c.nreg ztsn
  set AT := c.nreg ztps
  have mL : ∀ i, i < E → ∀ d, d < 7 → c'.nmem ztniw = c.nmem ztniw :=
    fun i hi d hd => hm _ by_nlinarith
  have mL0 : ∀ i, i < E → c'.nmem ztbdu = c.nmem ztbdu := fun i hi => by
    grind
  have mS : ∀ x, x < S → ∀ d, d < 5 → c'.nmem ztniy = c.nmem ztniy :=
    fun x hx d hd => hm _ by_nlinarith
  have mS0 : ∀ x, x < S → c'.nmem ztbbm = c.nmem ztbbm := fun x hx => by
    grind
  have mT : ∀ j, j < 2 * N₂.nChords → ∀ d, d < 3 → c'.nmem ztniz = c.nmem ztniz :=
    fun j hj d hd => hm _ by_nlinarith
  have mT0 : ∀ j, j < 2 * N₂.nChords → c'.nmem ztcsu = c.nmem ztcsu := fun j hj => by
    grind
  have mB : ∀ i, i < E → ∀ s, s ≤ 1 → ∀ d, d < 3 →
      c'.nmem ztimf = c.nmem ztimf :=
    fun i hi s hs d hd => hm _ (by unfold slotA; nlinarith)
  have mB0 : ∀ i, i < E → ∀ s, s ≤ 1 → c'.nmem ztege = c.nmem ztege :=
    fun i hi s hs => by simpa using mB i hi s hs 0 by_norm_num
  have hlogPos : ∀ i, i < E → logPos c'.nmem AL i = logPos c.nmem AL i := fun i hi => by
    zuhar
  have hlogPt : ∀ i, i < E → logPt P J c'.nmem AL i = logPt P J c.nmem AL i := fun i hi => by
    unfold logPt; grind
  refine ⟨by_omega, by_omega, by_omega, by_omega, fun i hi s hs => ?_, fun x hx => ?_,
    fun j hj hv hf => ?_⟩
  · obtain ⟨f1, f2⟩ := hsl i hi s hs
    zumrl
    rw [mB0 i hi s hs, mB i hi s hs 1 by_norm_num, mB i hi s hs 2 by_norm_num,
      hlogPt i hi]
    grind
  · obtain ⟨i, hi, e1, e2, e3⟩ := hst x hx
    zumkj
    · grind
    · rw [hlogPos i hi, mS0 x hx, mS x hx 1 by_norm_num, e2]
    · rw [mS x hx 4 by_norm_num, mB0 i hi _ (by unfold sOf; grind), e3]
  · obtain ⟨i, hi, e1, e2, e3⟩ := htb j hj hv by_grind
    zumkj
    · rw [mL0 i hi, mT j hj 1 by_norm_num, e1]
    · rw [hlogPos i hi, mT j hj 1 by_norm_num, mT j hj 2 by_norm_num, e2]
    grind

/-- **`AuxCore` gives `Aux`.** -/
theorem aux_of_core
    (h : AuxCore P J N₂ c) : Aux P J N₂ c :=
  ⟨c.nreg ALLOC, le_rfl, fun _c' hr hm hA => auxCore_transport h hr hm hA⟩

/-- **`Aux` at a configuration gives `AuxCore` there.** -/
theorem core_of_aux
    (h : Aux P J N₂ c) : AuxCore P J N₂ c := by
  zucxi
  grind

/-- **The contract of the initialisation** of the side-0 stop and table candidates. -/
def InitPartSpec : Prop := ∃ (initC : Stmt) (κ : ℕ → ℕ), InitSpec initC Aux κ
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ : Config}

/-! ## Small facts -/
theorem dS_eq (s : ℕ) : dS s = 1 ∨ dS s = -1 := by unfold dS; grind
theorem dS_inj {s s' : ℕ} (hs : s ≤ 1) (hs' : s' ≤ 1) (h : dS s = dS s') : s = s' := by
  unfold dS at h; grind
variable (b : ℕ) (d : ℕ)
theorem dS_sOf : dS ztmnm = dirOf b := by
  unfold dS sOf dirOf; simp
theorem sOf_le : sOf b ≤ 1 := by unfold sOf; grind
theorem dS_mod (j : ℕ) : dS ztfsu = endDir j := by
  rfl

/-- The slot of the query direction code `d`: the candidates point in direction `-dirOf d`. -/
def qS (d : ℕ) : ℕ := if d = 1 then 1 else 0
theorem dS_qS : dS zthzj = -dirOf d := by
  unfold dS qS dirOf; grind
theorem qS_le : qS d ≤ 1 := by unfold qS; grind

/-! ## The query position -/

/-- **A query position with height code `0` is on a tour edge.** -/
theorem query_h6 {z : Point} {σ : ℝ} (hz : z ∈ J.left.set) {e h : ℕ}
    (harr : Arrival (chainModel J.whole).W z σ e ztxjs)
    (h0 : h = 0) : 6 ≤ e := by
  zubvi
  zulwd
  have hbox := J.left.set_subset_box hz
  have hpt := harr.2.2.2.1
  have hp0 : (chainModel J.whole).param zta ztjy = 0 := rfl
  rw [hp0] at hpt
  have hW : (chainModel J.whole).W = J.whole.sideWalk J.whole.sideBeta := rfl
  rw [hW] at hpt
  obtain ⟨b0, b1, b2, b3, b4, b5, -⟩ := J.whole.sidePt_box J.whole.sideBeta 0
  have hR : J.left.radius = J.whole.radius := rfl
  have hRp := J.whole.radius_pos
  obtain ⟨hx, hy⟩ := hbox
  rw [hR] at hx hy
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5) with he | he | he | he | he | he <;>
    zulsz
  · grind
  · grind
  · grind
  · grind
  · grind
  grind

/-! ## The log in memory -/

/-- `AEnv` gives the base of the offsets at `sw 40`. -/
theorem aenv_gW (hA : AEnv P W X Ok J H N₁ N₂ E c₀) : c₀.nreg ztfg = gW J := by
  zubfc
  have := h40 0 by_norm_num
  tauto

/-- **The log keys increase strictly in offset.** -/
theorem log_sorted (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {i j : ℕ} (hij : i < j)
    (hj : j < rd c₀ bSweep 301) :
    off (chainModel J.whole).W.n ztwnj
        ((chainModel J.whole).key zta ztwye) <
      off (chainModel J.whole).W.n ztwnj
        ((chainModel J.whole).key zta (logPos c₀.nmem ztjt j)) := by
  obtain ⟨rs, ls, -, -, -, -, hlsl, hls, hL, -, -, -⟩ := hA.hout
  have hi : i < ls.length := by_omega
  have hj' : j < ls.length := by_omega
  have hsort := hL.2.2.2.1
  have hlen : ztygf := by unfold logOf; simp
  have hp := List.pairwise_iff_getElem.1 hsort i j by_omega by_omega hij
  rw [← List.getD_eq_getElem _ ztfj, ← List.getD_eq_getElem _ ztfj] at hp
  obtain ⟨a1, a2⟩ := logOf_getD J zta N₂ hi
  obtain ⟨b1, b2⟩ := logOf_getD J zta N₂ hj'
  rw [a1, a2, b1, b2] at hp
  zufkj
  obtain ⟨n1, n2, -⟩ := hls j hj'
  rw [aenv_gW hA]
  unfold logPos Model.key
  zubi
  rw [m1, m2, n1, n2]
  zuitn

/-- The PosW facts of the log records. -/
theorem log_posW (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {i : ℕ} (hi : i < rd c₀ bSweep 301) :
    SweepEv.PosW P J (c₀.nmem ztglr)
      (c₀.nmem (rd c₀ bSweep 300 + 7 * i + 1)) := by
  zubph
  have hi' : i < ls.length := by_omega
  obtain ⟨m1, m2, -⟩ := hls i hi'
  grind

/-! ## The binary search -/

/-- **The result of the search is the log record at the target**, if there is one. -/
theorem search_eq (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {x : WPos} {t i : ℕ}
    (ht1 : ∀ j, j < t → lsPr P J c₀.nmem ztjt ztwnj x j)
    (ht2 : ∀ j, t ≤ j → j < rd c₀ bSweep 301 →
      ¬ lsPr P J c₀.nmem ztjt ztwnj x j)
    (hi : i < rd c₀ bSweep 301)
    (hkey : (chainModel J.whole).key zta ztwye =
      (chainModel J.whole).key zta x) : t = i := by
  have hnot : ¬ lsPr P J c₀.nmem ztjt ztwnj x i := by
    unfold lsPr; rw [show (⟨c₀.nmem _, c₀.nmem _⟩ :
      WPos) = logPos c₀.nmem _ i from rfl, hkey]; simp
  have h1 : t ≤ i := by
    grind
  zuct
  have hlt : t < i := by_omega
  zuldh
  zumtl
  rw [← hkey]
  exact log_sorted hA hlt hi

/-- The predicate of the search is downward closed. -/
theorem log_mono (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (x : WPos) {i j : ℕ} (hij : i ≤ j)
    (hj : j < rd c₀ bSweep 301)
    (h : lsPr P J c₀.nmem ztjt ztwnj x j) :
    lsPr P J c₀.nmem ztjt ztwnj x i := by
  rcases hij.lt_or_eq with hlt | rfl
  · exact lt_trans (log_sorted hA hlt hj) h
  omega

/-- **Equal offsets give equal positions** (proper positions of the walk of `C`). -/
theorem bits_eq (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {x y : WPos}
    (hx : x.edge < (chainModel J.whole).W.n) (hy : y.edge < (chainModel J.whole).W.n)
    (hpx : ProperPos ztbm zta P.n x)
    (hpy : ProperPos ztbm zta P.n y)
    (h1 : ¬ off (chainModel J.whole).W.n ztwnj ztwqc <
      off (chainModel J.whole).W.n ztwnj ztyni)
    (h2 : ¬ off (chainModel J.whole).W.n ztwnj ztyni <
      off (chainModel J.whole).W.n ztwnj ztwqc) :
    x.edge = y.edge ∧ (chainModel J.whole).param zta x =
      (chainModel J.whole).param zta y := by
  have heq := le_antisymm ztkbn ztmmr
  rw [aenv_gW hA] at heq
  have kx0 : 0 ≤ (chainModel J.whole).key zta x := by
    unfold Model.key; have := hpx.1; positivity
  have ky0 : 0 ≤ (chainModel J.whole).key zta y := by
    unfold Model.key; have := hpy.1; positivity
  have kxn : (chainModel J.whole).key zta x < (chainModel J.whole).W.n := by
    unfold Model.key; have := hpx.2.1
    have : (x.edge : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hx
    linarith
  have kyn : (chainModel J.whole).key zta y < (chainModel J.whole).W.n := by
    unfold Model.key; have := hpy.2.1
    have : (y.edge : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hy
    linarith
  have hk := off_inj by_positivity ztvrg kx0 kxn ky0 kyn heq
  zuckv
  exact key_split hpx.1 hpx.2.1 hpy.1 hpy.2.1 hk

/-! ## Matches -/

/-- **The origin in a flagged slot** at a log record with the point `z` is the candidate origin
of `z` in the direction of the slot. -/
theorem slot_eq (hP : J.P.Simple) {m : ℕ → ℕ} {B AL i s : ℕ} {z o : Point}
    (hslot : SlotOK P J m B AL i s) (hf : m ztege = 1) (hpt : logPt P J m AL i = z)
    (hz : z ∈ J.left.set) (hzs : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2)
    (ho : CandAt J o ztmiq z) :
    (chainModel J.right).pos zta ztcoz = o := by
  obtain ⟨-, -, hc⟩ := hslot.2 hf
  zukvt
  exact cand_unique ztvox hc ho (z_mem_right_dom hP hz hzs hz2) ztwic

/-- **A stop record at the query position** is attached at a log record with that position,
whose slot (of its direction) is flagged, and its origin is a candidate origin of `z`. -/
theorem stop_match (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hX : AuxCore P J N₂ c₀) {z : Point}
    {σ : ℝ} {zp zh : ℕ}
    (harr : Arrival (chainModel J.whole).W z σ zp ztwyz)
    {rs : List ztcf} (hrsl : rs.length = rd c₀ bSweep 201)
    (hrs : StopRecsAt c₀.nmem ztdpi rs) {r : ℕ × ℕ × ℕ × ℕ × ℕ} (hr : r ∈ rs)
    (hr1 : r.1 = zp)
    (hr2 : (chainModel J.whole).param zta ztbhg =
      (chainModel J.whole).param zta ztyf) :
    ∃ i, i < rd c₀ bSweep 301 ∧
      logPos c₀.nmem ztjt i = ztyge ∧
      (chainModel J.whole).param zta ztwye =
        (chainModel J.whole).param zta ztyf ∧
      c₀.nmem (slotA ztghy i (sOf r.2.2.2.2)) = 1 ∧
      CandAt J (stopOrig J zta N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2) ztqmb z := by
  obtain ⟨rs₀, ls₀, hl0, hrs0, hS, hW0, -⟩ := hA.hout
  have heq := stopRecs_unique hrs hrs0 by_omega
  zufpx
  obtain ⟨x, hx, hxr⟩ := List.getElem_of_mem hr
  have hfx := hrs x hx
  rw [List.getD_eq_getElem _ _ hx, hxr] at hfx
  obtain ⟨f1, f2, -, -, f5⟩ := hfx
  obtain ⟨-, -, -, -, -, hst, -⟩ := hX
  obtain ⟨i, hi, e1, e2, e3⟩ := hst x by_omega
  rw [f1, f2] at e2
  rw [f1, hr1] at e1
  rw [f5] at e3
  obtain ⟨-, hk, -, hk1⟩ := hW0 r hr
  obtain ⟨hc, -⟩ := stop_cand J hA.hNF₂ hS hr hk hk1
  refine ⟨i, hi, ?_, e2.trans hr2, e3, ?_⟩
  · zuhar
  · rw [hr2, hr1, harr.2.2.2.1] at hc; exact hc

/-- **A regular table entry at the query position** is attached at a log record with that
position, whose slot (of its direction) is flagged; its origin is a candidate origin of `z`. -/
theorem tab_match (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hX : AuxCore P J N₂ c₀) {z : Point}
    {σ : ℝ} {zp zh : ℕ}
    (harr : Arrival (chainModel J.whole).W z σ zp ztwyz)
    {j : ℕ} (hj : j < 2 * N₂.nChords)
    (hT : tabOf J zta c₀.nmem ztdaf j =
      some ztyfx)
    (hv : ValidO J zta N₂ j) :
    ∃ i, i < rd c₀ bSweep 301 ∧
      logPos c₀.nmem ztjt i = ztyge ∧
      (chainModel J.whole).param zta ztwye =
        (chainModel J.whole).param zta ztyf ∧
      c₀.nmem (slotA ztghy i ztfsu) = 1 ∧
      CandAt J ztwka ztri z := by
  obtain ⟨rs₀, ls₀, -, -, -, -, -, -, -, -, hTab, -⟩ := hA.hout
  have hflag : ztbacn := by
    unfold tabOf at hT; simp_all
  have hT' := hT
  unfold tabOf at hT'
  rw [ite_eq_left hflag] at hT'
  simp only [Option.some.injEq, Prod.mk.injEq] at hT'
  obtain ⟨g1, g2⟩ := hT'
  obtain ⟨-, -, -, -, -, -, htb⟩ := hX
  obtain ⟨i, hi, e1, e2, e3⟩ := htb j hj hv hflag
  rw [g1] at e1
  rw [g2] at e2
  obtain ⟨hc, -⟩ := tab_cand J hTab hj hv.1 hv.2.1 hv.2.2 hT
  refine ⟨i, hi, ?_, e2, e3, ?_⟩
  · unfold logPos; simp_all
  · rw [harr.2.2.2.1] at hc; exact hc
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ : Config}

/-- **The completeness clauses** from the completeness of the slot read. -/
theorem compl_of (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hX : AuxCore P J N₂ c₀) {z : Point}
    {zp zh d : ℕ} {L' : Set ℝ}
    (harr : Arrival (chainModel J.whole).W z (-dirOf d) zp
      ztwyz)
    (H : ∀ i, i < rd c₀ bSweep 301 → c₀.nmem ztglr = zp →
      (chainModel J.whole).param zta ztwye =
        (chainModel J.whole).param zta ztyf →
      c₀.nmem ztznw = 1 →
      ∀ (o : Point) (τ : ℝ), CandAt J o ztbahh z → 0 < τ → o = rayPt z ztwf τ →
        τ ∈ L') :
    (∀ (rs : List ztcf), rs.length = rd c₀ bSweep 201 →
      StopRecsAt c₀.nmem ztdpi rs →
      ∀ r ∈ rs, r.1 = zp →
        (chainModel J.whole).param zta ztbhg =
          (chainModel J.whole).param zta ztyf →
        dirOf r.2.2.2.2 = -dirOf d →
        ∀ τ, 0 < τ → stopOrig J zta N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
          rayPt z ztwf τ → τ ∈ L') ∧
    (∀ j, j < 2 * N₂.nChords →
      tabOf J zta c₀.nmem ztdaf j =
        some ztyfx →
      endDir j = -dirOf d → endOrigin J zta N₂ j ∈ J.right.set →
      endOrigin J zta N₂ j ≠ J.shared → endOrigin J zta N₂ j ≠ J.right.top →
      ∀ τ, 0 < τ → endOrigin J zta N₂ j = rayPt z ztwf τ → τ ∈ L') := by
  refine ⟨fun rs hrsl hrs r hr hr1 hr2 hdir τ hτ ho => ?_,
    fun j hj hT hdir hv1 hv2 hv3 τ hτ ho => ?_⟩
  · obtain ⟨i, hi, e1, e2, e3, hc⟩ := stop_match hA hX harr hrsl hrs hr hr1 hr2
    have hs : sOf r.2.2.2.2 = qS d := by
      apply dS_inj (sOf_le _) ztwcb
      rw [dS_sOf, dS_qS, hdir]
    zukvz
    rw [← dS_sOf, hs] at hc
    zufen
  · obtain ⟨i, hi, e1, e2, e3, hc⟩ := tab_match hA hX harr hj hT ⟨hv1, hv2, hv3⟩
    have hs : j % 2 = qS d := by
      apply dS_inj by_omega ztwcb
      rw [dS_mod, dS_qS, hdir]
    zukvz
    rw [← dS_mod, hs] at hc
    zufen

/-! ## Registers and program -/
def kA : ℕ := sw 4100
def kE : ℕ := sw 4101
def kH : ℕ := sw 4102
def kO : ℕ := sw 4104
def kS : ℕ := sw 4106
def kF : ℕ := sw 4107
def kPe : ℕ := sw 4108
def kPh : ℕ := sw 4109
def kPo : ℕ := sw 4110

/-- Copy the query position to the target registers of the search. -/
def cIn : List Instr := [.copyN lsxE zP, .copyN lsxH zPh]

/-- The key of the log record found. -/
def cAddr : List Instr :=
  [.copyN kA ztfx, .addN kA kA lsI, .addN kA kA lsI, .addN kA kA lsI, .addN kA kA lsI,
    .addN kA kA lsI, .addN kA kA lsI, .addN kA kA lsI, .loadN kE kA, .addN kA kA K1, .loadN kH kA]

/-- The address of the slot of the log record found (east). -/
def cSlot : List Instr :=
  [.copyN kS sB, .addN kS kS lsI, .addN kS kS lsI, .addN kS kS lsI, .addN kS kS lsI,
    .addN kS kS lsI, .addN kS kS lsI]

/-- The slot of the query direction: west (`+ 3`) for the direction code `1`. -/
def cDir : Stmt := .ifLtN qD K1 .skip (.ifLtN K1 qD .skip (.instr (.addN kS kS K3)))

/-- Read the slot. -/
def cRead : List Instr :=
  [.loadN kF kS, .addN kS kS K1, .loadN kPe kS, .addN kS kS K1, .loadN kPh kS]

/-- Offer the origin of a flagged slot. -/
def cOffer : Stmt := .ifLtN K0 kF (offerF accA zted kPe kPh K1 qD zthy kPo) .skip

/-- The slot part. -/
def cHit : Stmt := .seq (block cSlot) (.seq cDir (.seq (block cRead) cOffer))

/-- The check of the record found and the slot part. -/
def cCheck : Stmt :=
  .seq (block cAddr) (.seq (callOff ztjl kE kH lsxE lsxH ztfg kO)
    (.ifLtN K0 kO .skip (.ifLtN K0 zttqp .skip cHit)))

/-- **The per-query procedure** (with the binary search `ls`). -/
def candQ (ls : Stmt) : Stmt :=
  .seq (block cIn) (.seq ls (.ifLtN lsI ztex cCheck .skip))
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The registers written by the per-query procedure (outside the oracle bands, besides the
allocator). -/
def QSet (r : ℕ) : Prop := (sw 2000 ≤ r ∧ r ≤ sw 2012) ∨ (sw 4000 ≤ r ∧ r ≤ sw 4111)

/-- The frame of the per-query procedure and of its parts. -/
def FrQ (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ QSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth
theorem FrQ.trans {c₁ c₂ c₃ : Config} (h₁ : FrQ c₁ c₂) (h₂ : FrQ c₂ c₃) : FrQ c₁ c₃ :=
  ⟨fun r a b d => (h₂.1 r a b d).trans ztjyh, h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a (by have := h₁.2.1; omega)).trans ztdux⟩
theorem nob {r : ℕ} (h1 : 240000 ≤ r) (h2 : r < 250000) : bandOf r ∉ oracleBands :=
  not_oracle_sw h1 h2

/-! ## The blocks -/
variable (m f : ℕ → ℕ)
theorem cIn_val :
    regB m cIn f lsxE = f zP ∧ regB m cIn f lsxH = f zPh ∧
      ∀ q, q ≠ lsxE → q ≠ lsxH → regB m cIn f q = f q := by
  refine ztfcz
  · rfl
  · rfl
  · simp only [cIn, regB, regI]
    simp_all
theorem cIn_ok : okB W m cIn f := by
  simp only [cIn, okB, okI]
  tauto
theorem cAddr_val (hk1 : f K1 = 1) :
    regB m cAddr f kE = m (f ztfx + 7 * f lsI) ∧
      regB m cAddr f kH = m (f ztfx + 7 * f lsI + 1) ∧
      ∀ q, q ≠ kA → q ≠ kE → q ≠ kH → regB m cAddr f q = f q := by
  zubx
  refine ztkio
  · zucci

  · zucci

  · refine regB_other m cAddr f ztdp
    simp only [cAddr, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zubzr
theorem cAddr_ok (hk1 : f K1 = 1) (hb : f ztfx + 7 * f lsI + 1 ≤ W) :
    okB W m cAddr f := by
  zubx
  have s : IScr kA := iscr_sw by_decide by_decide
  have sE : IScr kE := iscr_sw by_decide by_decide
  have sH : IScr kH := iscr_sw by_decide by_decide
  simp only [kA, kE, kH, sw] at s sE sH
  have hb' : f 240300 + 7 * f 244000 + 1 ≤ W := hb
  simp only [cAddr, okB, okI, regI, upd, kA, kE, kH, lsI, K1, sw]
  grind
theorem cSlot_val :
    regB m cSlot f kS = f sB + 6 * f lsI ∧ ∀ q, q ≠ kS → regB m cSlot f q = f q := by
  refine ⟨?_, fun q h1 => ?_⟩
  · simp only [cSlot, regB, regI, upd, kS, sB, lsI, sw]
    grind
  · refine regB_other m cSlot f ztdp
    simp only [cSlot, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zubzr
theorem cSlot_ok (hb : f sB + 6 * f lsI ≤ W) : okB W m cSlot f := by
  zuhgc
  simp only [kS, sw] at s
  have hb' : f 240620 + 6 * f 244000 ≤ W := hb
  simp only [cSlot, okB, okI, regI, upd, kS, sB, lsI, sw]
  grind
theorem cRead_val (hk1 : f K1 = 1) :
    regB m cRead f kF = m (f kS) ∧ regB m cRead f kPe = m (f kS + 1) ∧
      regB m cRead f kPh = m (f kS + 2) ∧
      ∀ q, q ≠ kS → q ≠ kF → q ≠ kPe → q ≠ kPh → regB m cRead f q = f q := by
  zubx
  refine ⟨?_, ?_, ?_, fun q h1 h2 h3 h4 => ?_⟩
  · rfl
  · zuccj

  · zuccj

  · refine regB_other m cRead f ztdp
    simp only [cRead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      zubzr
theorem cRead_ok (hk1 : f K1 = 1) (hb : f kS + 2 ≤ W) : okB W m cRead f := by
  zubx
  zuhgc
  have sF : IScr kF := iscr_sw by_decide by_decide
  have sE : IScr kPe := iscr_sw by_decide by_decide
  have sH : IScr kPh := iscr_sw by_decide by_decide
  simp only [kS, kF, kPe, kPh, sw] at s sF sE sH
  have hb' : f 244106 + 2 ≤ W := hb
  simp only [cRead, okB, okI, regI, upd, kS, kF, kPe, kPh, K1, sw]
  grind

/-! ## The direction -/
theorem cDir_irs (hI : IInv W c₀ c) (hK : Consts c) (hb : c.nreg kS + 3 ≤ W) :
    IRS P W c₀ cDir c 5 (fun c' => c'.nreg kS = c.nreg kS + 3 * qS ztql ∧
      (∀ q, q ≠ kS → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  zucnb
  have k3 : c.nreg K3 = 3 := hK.2.2.2.2.2.2
  unfold cDir
  by_cases h0 : c.nreg qD < c.nreg K1
  · refine (IRS.ifT h0 (IRS.skip (K := 0) hI ztcos)).mono by_norm_num
      ztb
    rw [k1] at h0; unfold qS; simp_all
  · refine (IRS.ifF h0 ?_).mono (K := 3 + 2) by_norm_num ztb
    by_cases h1 : c.nreg K1 < c.nreg qD
    · refine (IRS.ifT h1 (IRS.skip (K := 0) hI ztcos)).mono by_norm_num
        ztb
      rw [k1] at h1; unfold qS; grind
    · refine (IRS.ifF h1 (IRS.instr1 (i := .addN kS kS K3) hI
        ⟨iscr_sw by_decide by_decide, by_omega⟩)).mono
        by_norm_num ?_
      zuu
      rw [k1] at h0 h1
      refine ztlvc
      · simp only [regI, upd_same, k3]
        unfold qS; grind
      · zuua
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Machine Machine.Stmt Programs SweepRam SweepPrim
@[expose] public section
def lsInit : Stmt := block [.constN 244000 0, .copyN 244001 240601]

/-- `k := k - 1`, `p := 2^k`, `E - i`. -/
def lsB1 : Stmt := block [.subN 244001 244001 240611, .addN 244002 240600 244001,
  .loadN 244003 244002, .subN 244016 240301 244000]

/-- The candidate and the key of its record. -/
def lsB2 : Stmt := block [.addN 244004 244000 244003, .subN 244005 244004 240611,
  .addN 244006 244005 244005, .addN 244007 244006 244006, .addN 244008 244007 244006,
  .addN 244009 244008 244005, .addN 244011 240300 244009, .loadN 244012 244011,
  .addN 244011 244011 240611, .loadN 244013 244011]

/-- Accept the candidate. -/
def lsB3 : Stmt := block [.copyN 244000 244004]

/-- The test of a candidate. -/
def lsTest : Stmt :=
  .seq lsB2 (.seq (callOff 240002 244012 244013 244020 244021 240040 244014)
    (.ifLtN 240610 244014 lsB3 .skip))

/-- One step of the search. -/
def lsBody : Stmt := .seq lsB1 (.ifLtN 244016 244003 .skip lsTest)

/-- **The binary search in the log.** -/
def lsearchS : Stmt := .seq lsInit (.whileLtN 240610 244001 lsBody)

/-- The registers of the search. -/
def LB (r : ℕ) : Bool := decide (244000 ≤ r ∧ r ≤ 244019)
section exec
variable {P : Polygon} {W : ℕ}
variable (d : Config)
set_option maxHeartbeats 1000000 in
theorem lsInit_exec (hw : WordsBounded W d) :
    ∃ d' k, Exec P W lsInit d d' k ∧ k = 2 ∧ d'.nreg 244000 = 0 ∧
      d'.nreg 244001 = d.nreg 240601 ∧ ztcjj ∧
      d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨d', k, ex, hk, q1, q2⟩ : ∃ d' k, Exec P W lsInit d d' k ∧ k = 2 ∧
      d'.nreg 244000 = 0 ∧ d'.nreg 244001 = d.nreg 240601 := by
    unfold lsInit
    exec_block
    all_goals try (config_simp; omega)
    simp
  zubgb
  exact ⟨d', k, ex, hk, q1, q2, hf.1, funext fun r => WalkKey.exec_rframe ex
    (B := fun _ => false) by_decide r rfl, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
set_option maxHeartbeats 1000000 in
theorem lsB1_exec (hw : WordsBounded W d) {I KK TB E : ℕ}
    (h00 : d.nreg 244000 = I) (h01 : d.nreg 244001 = KK) (hTB : d.nreg 240600 = TB)
    (hE : d.nreg 240301 = E) (hK1 : d.nreg 240611 = 1) (hW : TB + KK ≤ W) :
    ∃ d' k, Exec P W lsB1 d d' k ∧ k = 4 ∧ d'.nreg 244001 = KK - 1 ∧
      d'.nreg 244003 = d.nmem ztnpw ∧ d'.nreg 244016 = E - I ∧ d'.nreg 244000 = I ∧
      ztcjj ∧
      d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨d', k, ex, hk, q1, q2, q3, q4⟩ : ∃ d' k, Exec P W lsB1 d d' k ∧ k = 4 ∧
      d'.nreg 244001 = KK - 1 ∧ d'.nreg 244003 = d.nmem ztnpw ∧
      d'.nreg 244016 = E - I ∧ d'.nreg 244000 = I := by
    unfold lsB1
    exec_block
    all_goals try (config_simp; (try simp only [h00, h01, hTB, hE, hK1]); omega)
    simp_all
  zubgb
  exact ⟨d', k, ex, hk, q1, q2, q3, q4, hf.1, funext fun r => WalkKey.exec_rframe ex
    (B := fun _ => false) by_decide r rfl, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
set_option maxHeartbeats 2000000 in
theorem lsB2_exec (hw : WordsBounded W d) {I Pv E AL : ℕ}
    (h00 : d.nreg 244000 = I) (h03 : d.nreg 244003 = Pv) (hAL : d.nreg 240300 = AL)
    (hK1 : d.nreg 240611 = 1) (hle : I + Pv ≤ E) (hpos : 1 ≤ I + Pv) (hW : AL + 7 * E ≤ W) :
    ∃ d' k, Exec P W lsB2 d d' k ∧ k = 10 ∧ d'.nreg 244004 = I + Pv ∧
      d'.nreg 244012 = d.nmem ztzbj ∧
      d'.nreg 244013 = d.nmem ztyol ∧ d'.nreg 244000 = I ∧
      d'.nreg 244001 = d.nreg 244001 ∧ ztcjj ∧
      d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨d', k, ex, hk, q1, q2, q3, q4, q5⟩ : ∃ d' k, Exec P W lsB2 d d' k ∧ k = 10 ∧
      d'.nreg 244004 = I + Pv ∧ d'.nreg 244012 = d.nmem ztzbj ∧
      d'.nreg 244013 = d.nmem ztyol ∧ d'.nreg 244000 = I ∧
      d'.nreg 244001 = d.nreg 244001 := by
    unfold lsB2
    exec_block
    all_goals try (config_simp; (try simp only [h00, h03, hAL, hK1]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h00, h03, hAL, hK1])
    · grind
    grind
  zubgb
  exact ⟨d', k, ex, hk, q1, q2, q3, q4, q5, hf.1, funext fun r => WalkKey.exec_rframe ex
    (B := fun _ => false) by_decide r rfl, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
theorem lsB3_exec (hw : WordsBounded W d) :
    ∃ d' k, Exec P W lsB3 d d' k ∧ k = 1 ∧ d'.nreg 244000 = d.nreg 244004 ∧
      d'.nreg 244001 = d.nreg 244001 ∧ ztcjj ∧
      d'.rreg = d.rreg ∧ d'.nmem = d.nmem ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨d', k, ex, hk, q1, q2⟩ : ∃ d' k, Exec P W lsB3 d d' k ∧ k = 1 ∧
      d'.nreg 244000 = d.nreg 244004 ∧ d'.nreg 244001 = d.nreg 244001 := by
    unfold lsB3
    exec_block
    simp
  zubgb
  exact ⟨d', k, ex, hk, q1, q2, hf.1, funext fun r => WalkKey.exec_rframe ex
    (B := fun _ => false) by_decide r rfl, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2⟩
end exec
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace S0C
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
@[expose] public section
def lsP (P : Polygon) (J : Merge.Junction) (c : Config) (j : ℕ) : Prop :=
  lsPr P J c.nmem (c.nreg 240300) (c.nreg 240040) ⟨c.nreg 244020, c.nreg 244021⟩ j

/-- **The invariant of the search loop.** -/
structure LInv (P : Polygon) (J : Merge.Junction) (c d : Config) : Prop where
  fr : ∀ r, bandOf r ∉ oracleBands → ¬ LSet r → r ≠ ALLOC → d.nreg r = c.nreg r
  hA : c.nreg ALLOC ≤ d.nreg ALLOC
  hm : ∀ a, a < c.nreg ALLOC → d.nmem a = c.nmem a
  hk : d.nreg 244001 ≤ c.nreg 240601
  hi : d.nreg 244000 ≤ c.nreg 240301
  hlo : ∀ j, j < d.nreg 244000 → lsP P J c j
  hhi : ∀ j, d.nreg 244000 + 2 ^ d.nreg 244001 ≤ j + 1 → j < c.nreg 240301 → ¬ lsP P J c j
variable {r : ℕ}
theorem lb_false_of_lset (h : ¬ LSet r) : LB r = false := by
  unfold LSet sw at h
  zuhpe
theorem lb_false_of_scr (h : ¬ IScr r) : LB r = false := by
  unfold IScr at h
  zuhpe
theorem fix_keep {P : Polygon} {J : Merge.Junction} {c d : Config} (h : LInv P J c d) {r : ℕ}
    (h1 : 240000 ≤ r) (h2 : r < 244000 ∨ (244019 < r ∧ r < 250000)) : d.nreg r = c.nreg r :=
  h.fr r (by rw [band_sw h1 by_omega]; decide) ztbpz
    ztu
section
variable {P : Polygon} {W : ℕ} {J : Merge.Junction} {c₀ c : Config}

/-- A straight-line block of the search as a run step. -/
theorem irs_blk {s : Stmt} {d d' : Config} {k : ℕ} (hI : IInv W c₀ d) (ex : Exec P W s d d' k)
    (f : ∀ r, LB r = false → d'.nreg r = d.nreg r) (rr : d'.rreg = d.rreg) (m : d'.nmem = d.nmem)
    (rm : d'.rmem = d.rmem) (o : d'.output = d.output) : IRS P W c₀ s d k (fun x => x = d') :=
  IRS.ofExec hI ex le_rfl (fun r hr _ => f r (lb_false_of_scr hr)) rr by_simp_all rm o
    (by zuope) (by zuope; omega) rfl
set_option maxHeartbeats 16000000 in
/-- **One step of the search.** -/
theorem lsBody_irs (hctx : ChainCtx P W c 240002 J.whole)
    (htab : ∀ j, j < c.nreg 240601 → c.nmem ztrma = 2 ^ j)
    (hTB : c.nreg 240600 + c.nreg 240601 ≤ c.nreg ALLOC)
    (hAL : c.nreg 240300 + 7 * c.nreg 240301 ≤ c.nreg ALLOC)
    (hG : c.nreg 240040 < (chainModel J.whole).W.n)
    (hrec : ∀ j, j < c.nreg 240301 → SweepEv.PosW P J ztlkj
      ztjrp)
    (hx : SweepEv.PosW P J ztvic ztvid)
    (hdc : ∀ i j, i ≤ j → j < c.nreg 240301 → lsP P J c j → lsP P J c i)
    (k0 : c.nreg 240610 = 0) (k1 : c.nreg 240611 = 1) {d : Config} (hI : IInv W c₀ d)
    (hL : LInv P J c d) (hpos : d.nreg 240610 < d.nreg 244001)
    (hroom : d.nreg ALLOC + 11100 ≤ W) :
    IRS P W c₀ lsBody d 11100 (fun d' => LInv P J c d' ∧ d'.nreg 244001 < d.nreg 244001) := by
  have d0 := (fix_keep hL by_norm_num by_norm_num).trans k0
  have dK1 := (fix_keep hL by_norm_num by_norm_num).trans k1
  have dTB : d.nreg 240600 = c.nreg 240600 := fix_keep hL by_norm_num by_norm_num
  have dE : d.nreg 240301 = c.nreg 240301 := fix_keep hL by_norm_num by_norm_num
  have dAL : d.nreg 240300 = c.nreg 240300 := fix_keep hL by_norm_num by_norm_num
  have dD : d.nreg 240002 = c.nreg 240002 := fix_keep hL by_norm_num by_norm_num
  have dG : d.nreg 240040 = c.nreg 240040 := fix_keep hL by_norm_num by_norm_num
  have dxE : d.nreg 244020 = c.nreg 244020 := fix_keep hL by_norm_num by_norm_num
  have dxH : d.nreg 244021 = c.nreg 244021 := fix_keep hL by_norm_num by_norm_num
  have hKK : 0 < d.nreg 244001 := by_omega
  have hWA := hI.hw.1 ALLOC
  have hAd := hL.hA
  have hkTL := hL.hk
  -- 1. `k := k - 1`, the power, the room
  obtain ⟨d1, k₁, e1, hk1, a01, a03, a16, a00, f1, rr1, m1, rm1, o1⟩ := lsB1_exec (P := P) d hI.hw
    (I := d.nreg 244000) (KK := d.nreg 244001) rfl rfl dTB dE dK1 by_omega
  have hpw : d.nmem (c.nreg 240600 + ztcmx) = 2 ^ ztcmx := by
    rw [hL.hm _ by_omega]; grind
  rw [hpw] at a03
  have h2 : 2 ^ d.nreg 244001 = 2 * 2 ^ ztcmx := by
    grind
  have hb1 := irs_blk hI e1 f1 rr1 m1 rm1 o1
  -- the frame facts of the step, from `d1` on
  zugks
  refine (IRS.seq hb1 (K₂ := 11021 + 2) (fun d1' hI1 _ _ h1 => ?_)).mono by_omega
    ztb
  subst d1'
  zujwa
  have e101 := a01
  by_cases hlt : d1.nreg 244016 < d1.nreg 244003
  · -- no room: no record `j < E` above
    refine IRS.ifT hlt (IRS.skip hI1 ⟨⟨fun r hr1 hr2 hr3 => (F1 r hr2).trans ztjxk,
      by omega, fun a ha => by zvnmf; exact hL.hm a ha, by_omega, by zuodl; exact hL.hi,
      by zuodl; exact hL.hlo, fun j hj hjE => ?_⟩, by_omega⟩)
    exfalso
    zuigv
    rw [a00, a01] at hj
    omega
  refine IRS.ifF hlt ?_
  -- 2. the test
  zuigv
  have hge := hlt
  have hle : d.nreg 244000 + 2 ^ ztcmx ≤ c.nreg 240301 := by
    have := hL.hi; omega
  have hp1 : 1 ≤ 2 ^ ztcmx := Nat.one_le_two_pow
  obtain ⟨d2, k₂, e2, hk2, b04, b12, b13, b00, b01, f2, rr2, m2, rm2, o2⟩ := lsB2_exec (P := P) d1
    hI1.hw (I := d.nreg 244000) (Pv := 2 ^ ztcmx) (E := c.nreg 240301)
    (AL := c.nreg 240300) a00 a03 (by rw [F1 _ ztbpz, dAL])
    (by rw [F1 _ ztbpz, dK1]) hle by_omega by_omega
  have hb2 := irs_blk hI1 e2 f2 rr2 m2 rm2 o2
  have F2 : ∀ r, ¬ LSet r → d2.nreg r = d.nreg r := fun r hr =>
    (f2 r ztmmd).trans by_grind
  refine (IRS.seq hb2 (K₂ := 11008 + ztgxh) (fun d2' hI2 _ _ h2' => ?_)).mono by_omega
    ztb
  subst d2'
  have A2 : d2.nreg ALLOC = d.nreg ALLOC := by rw [f2 ALLOC by_decide, A1]
  -- the record and its key
  set j0 := d.nreg 244000 + 2 ^ ztcmx - 1 with hj0
  have hj0E : j0 < c.nreg 240301 := by_omega
  have hmem : ∀ a, a < c.nreg ALLOC → d1.nmem a = c.nmem a := fun a ha => by
    zvnmf; exact hL.hm a ha
  rw [hmem _ by_omega] at b12
  rw [hmem _ by_omega] at b13
  obtain ⟨hpe, hpp, hp6⟩ := hrec j0 hj0E
  obtain ⟨hxe, hxp, hx6⟩ := hx
  have g12 : d2.nreg 244012 = c.nmem _ := b12
  have g13 : d2.nreg 244013 = c.nmem _ := b13
  have g20 : d2.nreg 244020 = c.nreg 244020 := by rw [F2 _ ztbpz, dxE]
  have g21 : d2.nreg 244021 = c.nreg 244021 := by rw [F2 _ ztbpz, dxH]
  have g40 : d2.nreg 240040 = c.nreg 240040 := by rw [F2 _ ztbpz, dG]
  have g02 : d2.nreg 240002 = c.nreg 240002 := by rw [F2 _ ztbpz, dD]
  have hmem2 : ∀ a, a < c.nreg ALLOC → d2.nmem a = c.nmem a := fun a ha => by
    grind
  have hctx2 :=
    hctx.transport g02 hmem2 by_omega
  have hcall := callOff_irs (ex := 244012) (hx := 244013)
    (ey := 244020) (hy := 244021) (g := 240040) (o := 244014) hI2 hctx2 by_norm_num
    by_norm_num by_omega by_omega by_omega
    by_grind by_grind by_omega
    by_omega by_omega
  refine IRS.seq hcall (fun d3 hI3 _ _ h3 => ?_)
  obtain ⟨bit, -, fr3, A3, m3⟩ := h3
  have F3 :=
    fun r hr1 hr2 hr3 => (fr3 r hr1 ztmem
      ztmem hr3).trans (F2 r hr2)
  have hbit : d3.nreg 244014 = 1 ↔ lsP P J c j0 := by
    rw [bit.2, g12, g13, g20, g21, g40]; rfl
  have hb1' := bit.1
  have e10 : d3.nreg 240610 = 0 := by
    rw [F3 _ by_decide ztbpz by_decide, d0]
  have e01 : d3.nreg 244001 = d.nreg 244001 - 1 := by
    rw [fr3 _ by_decide by_norm_num by_norm_num by_decide,
      b01, a01]
  have e00 : d3.nreg 244000 = d.nreg 244000 := by
    rw [fr3 _ by_decide by_norm_num by_norm_num by_decide, b00]
  have e04 : d3.nreg 244004 = d.nreg 244000 + 2 ^ ztcmx := by
    rw [fr3 _ by_decide by_norm_num by_norm_num by_decide, b04]
  have hmem3 : ∀ a, a < c.nreg ALLOC → d3.nmem a = c.nmem a := fun a ha => by
    zuooj; exact hmem2 a ha
  have hA3 : c.nreg ALLOC ≤ d3.nreg ALLOC := by_omega
  by_cases hlt3 : d3.nreg 240610 < d3.nreg 244014
  · -- accept
    refine IRS.ifT hlt3 ?_
    have hlt := hlt3
    rw [e10] at hlt
    have hpr : lsP P J c j0 := by_grind
    obtain ⟨d4, k₄, e4, hk4, c00, c01, f4, rr4, m4, rm4, o4⟩ := lsB3_exec d3 hI3.hw
    refine (irs_blk hI3 e4 f4 rr4 m4 rm4 o4).mono by_omega (fun x hx' => ?_)
    subst x
    have F4 := fun r hr => f4 r ztmmd
    have e41 : d4.nreg 244001 = d.nreg 244001 - 1 := by
      omega
    have e40 : d4.nreg 244000 = d.nreg 244000 + 2 ^ ztcmx := by_omega
    refine ⟨⟨fun r hr1 hr2 hr3 => ((F4 r hr2).trans (F3 r hr1 hr2 hr3)).trans ztjxk,
      by rw [f4 ALLOC by_decide]; omega, fun a ha => by rw [m4]; exact hmem3 a ha,
      by omega, by_omega, fun j hj => ?_, fun j hj hjE => ?_⟩, by_omega⟩
    · rw [e40] at hj
      by_cases hji : j < d.nreg 244000
      · exact hL.hlo j hji
      · exact hdc j j0 by_omega hj0E hpr
    · rw [e40, e41] at hj
      exact hL.hhi j by_omega hjE
  · -- reject
    refine IRS.ifF hlt3 ?_
    have hge' := hlt3
    rw [e10] at hge'
    have hnpr : ¬ lsP P J c j0 := by_grind
    refine IRS.skip hI3 ⟨⟨fun r hr1 hr2 hr3 => (F3 r hr1 hr2 hr3).trans ztjxk,
      hA3, hmem3, by_omega, by_omega, by rw [e00]; exact hL.hlo, fun j hj hjE hpr => ?_⟩, by_omega⟩
    rw [e00, e01] at hj
    exact hnpr (hdc j0 j by_omega hjE hpr)
end
set_option maxHeartbeats 16000000 in
/-- **The binary search in the log meets its contract.** -/
theorem lsearchSpec : LSearchSpec := by
  refine ⟨lsearchS, 11106, ?_⟩
  intro P W J c₀ c hI hC hctx htab hTB hET hAL hG hrec hx hdc hroom
  obtain ⟨k0, k1, -⟩ := hC.fix hI
  replace k0 : c.nreg 240610 = 0 := k0
  replace k1 : c.nreg 240611 = 1 := k1
  replace hctx : ChainCtx P W c 240002 J.whole := hctx
  replace htab : ∀ j, j < c.nreg 240601 → c.nmem ztrma = 2 ^ j := htab
  replace hTB : c.nreg 240600 + c.nreg 240601 ≤ c.nreg ALLOC := hTB
  replace hET : c.nreg 240301 < 2 ^ c.nreg 240601 := hET
  replace hAL : c.nreg 240300 + 7 * c.nreg 240301 ≤ c.nreg ALLOC := hAL
  replace hG : c.nreg 240040 < (chainModel J.whole).W.n := hG
  replace hrec : ∀ j, j < c.nreg 240301 → SweepEv.PosW P J ztlkj
      ztjrp := hrec
  replace hx : SweepEv.PosW P J ztvic ztvid := hx
  replace hdc : ∀ i j, i ≤ j → j < c.nreg 240301 → lsP P J c j → lsP P J c i := hdc
  replace hroom : c.nreg ALLOC + 11106 * ztrmb ≤ W := hroom
  show IRS P W c₀ lsearchS c (11106 * ztrmb) (fun c' =>
    c'.nreg 244000 ≤ c.nreg 240301 ∧ (∀ j, j < c'.nreg 244000 → lsP P J c j) ∧
      (∀ j, c'.nreg 244000 ≤ j → j < c.nreg 240301 → ¬ lsP P J c j) ∧
      ztrn ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth)
  obtain ⟨c1, k₁, e1, hk1, i00, i01, f1, rr1, m1, rm1, o1⟩ := lsInit_exec (P := P) c hI.hw
  have hb := irs_blk hI e1 f1 rr1 m1 rm1 o1
  refine (IRS.seq hb (K₂ := (11100 + 2) * c.nreg 240601 + 2) (fun c1' hI1 _ _ h1 => ?_)).mono
    by_omega ztb
  subst c1'
  zugks
  zujwa
  have hL1 : LInv P J c c1 := ⟨by_simp_all, by_omega, by_simp_all,
    by omega, by_omega, by_simp_all, by_grind⟩
  have hw := IRS.while
    _ (fun d => d.nreg 244001) 11100
    by_grind
    (fun d hId hd hlt hr => lsBody_irs hctx htab hTB hAL hG hrec hx hdc k0 k1 hId hd hlt hr)
    hI1 hL1 by_omega
  rw [i01] at hw
  refine hw.mono le_rfl (fun d ⟨hd, hn⟩ => ?_)
  have h10 := (fix_keep hd by_norm_num by_norm_num).trans k0
  have hk0 : d.nreg 244001 = 0 := by_omega
  refine ⟨hd.hi, hd.hlo, fun j hj hjE => hd.hhi j by_simp_all hjE, hd.fr, hd.hA,
    hd.hm⟩
end
end S0C
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace Lab0
open Set Filter Topology
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideInArc)
open Chazelle.Merge (FreeAt)
open OracleQ (sj sk ek)
@[expose] public section
theorem sideInArc_eventually_sub {a b x : ℝ} (h : sideInArc a b x) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc a b ztfvh := by
  zusg
  zudwd
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT zthkj]
      with s hs hs'
    grind
  · zuy
    · zuhdc

    · zusq
      grind

/-- An interval of `𝓝[>] 0`. -/
theorem exists_Ioo_of_eventually {p : ℝ → Prop} (h : ∀ᶠ s in 𝓝[>] (0 : ℝ), p s) :
    ∃ u > (0 : ℝ), ∀ s, 0 < s → s < u → p s := by
  zuvg
  exact ⟨u, hu, fun s h0 h1 => hsub zteyi⟩

/-- **The regions faced at a walk vertex** `p` (parameter `0`) are among the three regions of an
answer of double identification for its key. -/
theorem gap_reg {C : Chain} (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF ztc Q N) {p : ℕ} (hp : p < (chainModel C).W.n) (hp1 : 1 ≤ p)
    {j : ℕ} (hj : j < N.arcs.length)
    (hloc1 : ¬ (chainModel C).IsCut ztwjh (p : ℝ) →
      N.F ztc Q = ∅ ∨
        sideInArc ztwvb ztwus (p : ℝ))
    (hloc2 : (chainModel C).IsCut ztwjh (p : ℝ) →
      sk ztc Q N j = (p : ℝ) ∨ ek ztc Q N j = (p : ℝ))
    {V : Set Point} (hV : V ∈ (chainModel C).regions ztwjh)
    (hW : AfterFaces ztc p 0 V ∨ BeforeFaces ztc p 0 V) :
    ∃ r ∈ nbrRegs N j, regOf ztc Q N r = V := by
  zudbh
  zuinu
  zubqs

  zuhwt
  have hF : F ⊆ M.Adm := hFam.2.1
  zukbz
  zuzj
  have hp' : ztmm = p := add_zero _
  by_cases hcut : M.IsCut F (p : ℝ)
  · obtain ⟨c, hc, -⟩ := id hcut
    zubar
    obtain ⟨hfa, hfb⟩ := faced_arcs hM hF hfin hp (le_refl (0 : ℝ)) zero_lt_one (fun _ => hp1)
      by_simp_all hV
    obtain ⟨r, hr, rfl⟩ := regOf_surj hN hV
    refine ⟨r, ?_, rfl⟩
    zufzs
    · obtain ⟨b, harc⟩ := hfa hW
      zukvk
      exact region_of_arc_at hN hGM hne hj ztmlj hr harc ztp
    · obtain ⟨a, harc⟩ := hfb hW
      zukvk
      exact region_of_arc_at hN hGM hne hj ztmlj hr harc ztbt
  · have hjA : sj N j < N.arcs.length := NFLoc.seq_lt hN hj
    zugps
    have hin : sideInArc ztevn zteru (p : ℝ) := by
      rcases hloc1 hcut with hF0 | hin
      · zucir
        · grind
        · have hk0 : ztfzn := by_positivity
          show sideInArc ztypa ztyoz (p : ℝ)
          zucpu
          zuxb
      omega
    set U₀ := regOf M Q N (N.arc ztbhb).reg with hU₀
    have hU₀m : U₀ ∈ M.regions F := hRC.1 _ hr0
    have hmem : (N.arc ztbhb).reg ∈ nbrRegs N j := by zupdi
    refine ⟨_, hmem, ?_⟩
    rw [← hU₀]
    zufzs
    · obtain ⟨u, hu, hsub⟩ := exists_Ioo_of_eventually ztkfe
      have hA0 : AfterFaces M p 0 U₀ := by
        refine ⟨u, hu, fun s hs0 hsu hs1 => ?_⟩
        refine harc0.2.2.2.2.2.2 p ztsqm hp by_linarith hs1 ?_
        have := hsub s hs0 hsu
        rw [zero_add]; tauto
      exact after_unique zero_lt_one hU₀m hV hA0 hW
    · obtain ⟨u, hu, hsub⟩ := exists_Ioo_of_eventually ztwdy
      have hB0 : BeforeFaces M p 0 U₀ := by
        refine ⟨min u 1, lt_min hu one_pos, fun h => absurd h ztkal, fun _ s hs0 hsu => ?_⟩
        have hsu' : s < u := lt_of_lt_of_le hsu ztff
        have hs1 : ztdrm := lt_of_lt_of_le hsu ztgh
        have hpm : ztxfk := by
          rw [show p + M.W.n - 1 = ztoq + M.W.n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt by_omega]
        rw [hpm]
        refine harc0.2.2.2.2.2.2 ztoq zteb by_omega by_linarith by_linarith ?_
        have e : ((p - 1 : ℕ) : ℝ) + zteb = (p : ℝ) - s := by
          simp_all
        zvmwe; exact hsub s hs0 hsu'
      exact before_unique ztbhw hU₀m hV hB0 hW

/-! ## The gap labels -/

/-- **The gap labels** are faced just after the walk vertex `2 m₂ + 6` or just before the walk
vertex `6` of the walk of `C₂`. -/
theorem gap_pos (J : Merge.Junction) {S₂ : Set ztf} {V : Set Point}
    (h : GapLab J S₂ V) :
    V ∈ (chainModel J.right).regions S₂ ∧
      (AfterFaces ztj ztekv 0 V ∨
        BeforeFaces ztj 6 0 V) := by
  obtain ⟨hδ, hV, hW⟩ := h
  refine ⟨hV, ?_⟩
  zuiym
  zukgc
  zunc
  have key : rL1 J = 2 * J.right.m - tpos J.right 0 ∧ rδ J = 7 := by
    unfold rδ at hδ
    unfold rL1 rδ
    grind
  obtain ⟨k1, k2⟩ := key
  have e1 : ztuk % (chainModel J.right).W.n = 2 * J.right.m + 6 := by
    rw [hn, k1, Nat.mod_eq_of_lt by_omega]; omega
  have e2 : ztymc := by
    rw [hn, k1, k2, show 6 + tpos J.right 0 + ztbxt + 7 =
      6 + ztqf by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
  grind

/-! ## The log entry of the query key -/
section Log
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ : Config}

/-- The key of a log entry is the key of its record in memory. -/
theorem logKey_eq {ls : List ztck} {m : ℕ → ℕ} {AL : ℕ}
    (hls : LogRecsAt m AL ls) {i : ℕ} (hi : i < ls.length) :
    logKey J zta N₂ ls i = (chainModel J.whole).key zta (S0C.logPos m AL i) := by
  obtain ⟨a1, a2⟩ := S0C.logOf_getD J zta N₂ hi
  zufkj
  unfold logKey Model.key S0C.logPos
  simp_all

/-- **The log entry of the key of `x`** is the result `t` of the binary search or `t - 1`. -/
theorem logIdx_cases (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {x : WPos} {t i : ℕ}
    (ht0 : t ≤ rd c₀ bSweep 301)
    (ht1 : ∀ j, j < t → S0C.lsPr P J c₀.nmem ztjt ztwnj x j)
    (ht2 : ∀ j, t ≤ j → j < rd c₀ bSweep 301 →
      ¬ S0C.lsPr P J c₀.nmem ztjt ztwnj x j)
    {ls : List ztck} (hlsl : ls.length = rd c₀ bSweep 301)
    (hls : LogRecsAt c₀.nmem ztjt ls)
    (hi : LogIdx J zta N₂ ls ztwqc i) : i = t ∨ i + 1 = t := by
  obtain ⟨hil, hle, hlt⟩ := hi
  have hg := S0C.aenv_gW hA
  have hoW : ∀ y, oW J y = off (chainModel J.whole).W.n ztwnj y := fun y => by
    unfold oW; rw [hg]
  zuct
  rcases (show i + 1 < t ∨ t < i by omega) with h | h
  · have h1 := ht1 ztg h
    have h2 := hlt by_omega
    unfold S0C.lsPr at h1
    rw [logKey_eq hls by_omega, hoW, hoW] at h2
    exact absurd (lt_trans h1 h2) ztkal
  · zuldh
    unfold S0C.lsPr
    have h3 := S0C.log_sorted hA h by_omega
    rw [logKey_eq hls hil, hoW, hoW] at hle
    exact lt_of_lt_of_le h3 hle
end Log

/-! ## The exit point on the gathered arcs -/

/-- **A ray starting in a listed region exits on the gathered arcs**, and its direction is free. -/
theorem exit_mem_gather {P : Polygon} {C : Chain} (hP : C.P.Simple) {N : NF}
    (hN : IsNF ztc zta N) {rs : List ℕ} {m : ℕ → ℕ} {A : ℕ}
    (harcs : ∀ k, k < (regArcs N rs).length →
      ShotList.arcAt m A k = nArc ztc zta N ztdxx)
    {r : ℕ} (hr : r < N.nRegions) (hrs : r ∈ rs) {z : Point} (hzt : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hray : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ regOf ztc zta N r) :
    FreeAt C z σ ∧ rayPt z σ ztbtm ∈
      ShotList.loSet ztc zta m A (regArcs N rs).length [] := by
  zudbh
  set F := N.F M zta with hFdef
  have hFam : M.ChordFamily zta F := hN.1
  zuzj
  have hU : regOf M zta N r ∈ M.regions F := hRC.1 r hr
  have hfree : FreeAt C z σ :=
    hray.mono fun t ht => (Chazelle.Chain.regionsIn_subset (show regOf M zta N r ∈
      Chazelle.Chain.regionsIn C.dom F from hU) ht).1
  zuknu
  set K := (regArcs N rs).length with hK
  set L := (List.range K).map (fun i => (M.key zta (ShotList.arcAt m A i).1,
    M.key zta (ShotList.arcAt m A i).2)) with hLdef
  have hL : ∀ a b, M.IsArc F (regOf M zta N r) a b → ztvk ∈ L := by
    zucdj

    have hmem : i₀ ∈ (N.region r).arcs := (hArcs.2.2.2 r hr i₀).2 ⟨hi₀, hir⟩
    have hmem' : i₀ ∈ regArcs N rs := List.mem_flatMap.2 ⟨r, hrs, hmem⟩
    obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1 hmem'
    refine List.mem_map.2 ⟨k, List.mem_range.2 hk, ?_⟩
    have hg : (regArcs N rs).getD k 0 = i₀ := by_simp_all
    rw [harcs k hk, hg]
    obtain ⟨⟨hps, -, -⟩, ⟨hpe, -, -⟩⟩ := arc_end_facts hP hN hi₀
    zujqr
    zubi
    rw [(Restore.normOf_facts hps).2.2.2.1, (Restore.normOf_facts hpe).2.2.2.1, his, hie]
  zuga

  exact ⟨p', t', hp', ht0', ht1', ⟨i, List.mem_range.1 hi, hk'⟩,
    fun g hg => absurd hg List.not_mem_nil, hpt'⟩
end
end Lab0
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace Lab0
open Machine Machine.Stmt Programs SweepRam SweepPrim
@[expose] public section
def eR0 : ℕ := sw 4030
def eR1 : ℕ := sw 4031
def eR2 : ℕ := sw 4032
def sV : ℕ := sw 4033
def sA : ℕ := sw 4034
def sX : ℕ := sw 4035
def sN : ℕ := sw 4036
def sE : ℕ := sw 4037

/-! ## A slot -/

/-- The address of the labels of the log record `e` (`sA`) and its label count (`sN`). -/
def addrL (e : ℕ) : List Instr :=
  [.copyN sE e, .addN sA sE sE, .addN sA sA sA, .addN sA sA sE, .addN sA sA sE, .addN sA sA sE,
    .addN sA sA ztfx, .addN sX sA K2, .loadN sN sX, .addN sA sA K3]

/-- The label at place `k`. -/
def labL (k : ℕ) : List Instr := [.addN sA sA k, .loadN sV sA]

/-- Store `sV` at the allocator. -/
def put1 : Stmt := block [.storeN ALLOC sV, .addN ALLOC ALLOC K1]

/-- **One slot.** -/
def slotS (e k : ℕ) : Stmt :=
  .seq (block [.loadN sV gL])
    (.seq (.ifLtN e ztex (.seq (block zthsc) (.ifLtN k sN (block ztjzz) .skip)) .skip)
      put1)

/-- The value of a slot. -/
def slotVal (m : ℕ → ℕ) (AL E g e k : ℕ) : ℕ :=
  if e < E ∧ k < m (AL + 7 * e + 2) then m (AL + 7 * e + 3 + k) else g

/-- The cost of a slot. -/
def slotK : ℕ := 19
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem put1_irs (hI : IInv W c₀ c) (hK : Consts c) (hroom : c.nreg ALLOC + 1 ≤ W) :
    IRS P W c₀ put1 c 2 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 1 ∧
      ztjn ∧
      c'.nmem = upd c.nmem ztm (c.nreg sV)) := by
  zubgn
  zubod
  zukfh
  have ex : ∃ c' k, Exec P W (block [.storeN 9999 244033, .addN 9999 9999 240611]) c c' k ∧
      k = 2 ∧ c'.nreg 9999 = c.nreg 9999 + 1 ∧
      ztedh ∧
      c'.nmem = upd c.nmem zterc (c.nreg 244033) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    simp_all
  zupp
  refine IRS.ofExec hI ex by_omega ztgjo h4 ztts h5 h6
    by_grind by_grind
    ⟨h1, h2, h3⟩
  zugul
  zubcl

  zuby
  grind

/-- The registers of a slot. -/
def SlotW (r : ℕ) : Prop := r = sV ∨ r = sA ∨ r = sX ∨ r = sN ∨ r = sE
variable (m f : ℕ → ℕ) (e : ℕ) (k : ℕ)
theorem addrL_val (hk2 : f K2 = 2) (hk3 : f K3 = 3) :
    regB m zthsc f sA = f ztfx + 7 * f e + 3 ∧
    regB m zthsc f sN = m (f ztfx + 7 * f e + 2) := by
  zufgt

  simp only [addrL, regB, regI, upd, sA, sX, sN, sE, K2, K3, sw]
  grind
theorem addrL_other {q : ℕ} (hq : ¬ SlotW q) : regB m zthsc f q = f q :=
  regB_other m zthsc f (fun i hi => by
    zufbh
    zumrm
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;>
      intro h <;> subst h <;> simp at hq)
theorem addrL_ok (hk2 : f K2 = 2) (hk3 : f K3 = 3)
    (hb : f ztfx + 7 * f e + 3 ≤ W) : okB W m zthsc f := by
  zufgt

  have hb' : f 240300 + 7 * f e + 3 ≤ W := hb
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [addrL, okB, okI, regI, upd, sA, sX, sN, sE, K2, K3, sw]
  grind
theorem labL_val :
    regB m ztjzz f sV = m (f sA + f k) := by
  rfl
theorem labL_other {q : ℕ} (hq : ¬ SlotW q) : regB m ztjzz f q = f q :=
  regB_other m ztjzz f (fun i hi => by
    simp only [labL, List.mem_cons, List.not_mem_nil, or_false] at hi
    zumrm
    rcases hi with rfl | rfl <;> zvmwd <;> intro h <;> subst h <;> simp at hq)
theorem labL_ok (hb : f sA + f k ≤ W) : okB W m ztjzz f := by
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [labL, okB, okI, sA, sV, sw] at hb ⊢
  grind
set_option maxHeartbeats 1000000 in
/-- **One slot**: its value is stored at the allocator. -/
theorem slot_irs (hI : IInv W c₀ c) (hK : Consts c₀) {e k : ℕ} (he : ¬ SlotW e) (hk : ¬ SlotW k)
    (hk3 : c.nreg k ≤ 3) (hAL : c.nreg ztfx + 7 * c.nreg ztex ≤ W)
    (hroom : c.nreg ALLOC + slotK ≤ W) :
    IRS P W c₀ (slotS e k) c slotK (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 1 ∧
      ztgsu ∧
      c'.nmem = upd c.nmem ztm (slotVal c.nmem ztwml ztxcl
        ztqhh ztvjk (c.nreg k))) := by
  have nW : ∀ q, (q = ALLOC ∨ q = gL ∨ q = sw 300 ∨ q = sw 301 ∨ q = K1 ∨ q = K2 ∨ q = K3) →
      ¬ SlotW q := by
    zuiby

    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases h with h | h | h | h | h <;> simp [ALLOC, gL, K1, K2, K3, sV, sA, sX, sN, sE, sw] at h
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  set v := slotVal c.nmem _ _ _ _
    _ with hv
  unfold slotS slotK
  unfold slotK at hroom
  refine IRS.seq (K₂ := 16 + 2)
    (IRS.block [.loadN sV gL] hI ⟨s 4033 by_norm_num by_norm_num, trivial⟩) ?_
  zufg
  set c₁ : Config := { c with nreg := regB c.nmem [.loadN sV gL] c.nreg } with hc₁
  have v1 : c₁.nreg sV = c.nmem (c.nreg gL) := by
    rfl
  have o1 : ∀ q, ¬ SlotW q → c₁.nreg q = c.nreg q := fun q hq =>
    regB_other _ _ _ (fun i hi => by
      zuvx
      subst hi; zvmwd; intro h; subst h; exact hq (Or.inl rfl))
  zulij
  refine IRS.seq (Q₁ := fun c₂ => c₂.nreg sV = v ∧
      (∀ q, ¬ SlotW q → c₂.nreg q = c.nreg q) ∧ c₂.nmem = c.nmem) ?_ ?_
  · zugsk
    · zufoc
      have hb : c₁.nreg ztfx + 7 * c₁.nreg e + 3 ≤ W := by
        grind
      refine IRS.seq (K₂ := 4)
        (IRS.block _ hI₁ (addrL_ok _ _ e hK₁.2.2.2.2.2.1
          hK₁.2.2.2.2.2.2 hb)) ?_
      zubup
      set c₃ : Config := { c₁ with nreg := regB c₁.nmem _ c₁.nreg } with hc₃
      obtain ⟨a1, a2⟩ := addrL_val c₁.nmem c₁.nreg e hK₁.2.2.2.2.2.1
        hK₁.2.2.2.2.2.2
      have o3 : ∀ q, ¬ SlotW q → c₃.nreg q = c.nreg q := fun q hq => by
        show regB c₁.nmem _ c₁.nreg q = c.nreg q
        rw [addrL_other _ _ e hq, o1 q hq]
      have m3 : ztckd := rfl
      have eA : c₃.nreg sA = c.nreg ztfx + 7 * c.nreg e + 3 := by
        simp_all
      have eN : c₃.nreg sN = c.nmem (c.nreg ztfx + 7 * c.nreg e + 2) := by
        simp_all
      refine IRS.ite ztrqg ztrqg
      · zugws
        refine (IRS.block _ hI₃ (labL_ok _ _ k by_grind)).mono
          by_rfl ?_
        rintro _ rfl
        refine ztlvc
        · show regB c₃.nmem _ c₃.nreg sV = v
          rw [labL_val, eA, o3 k hk, hv]
          zulcg
          simp_all
        · show regB c₃.nmem _ c₃.nreg q = c.nreg q
          rw [labL_other _ _ k hq, o3 q hq]
      · zugws
        refine IRS.skip hI₃ ⟨?_, o3, m3⟩
        show regB c₁.nmem _ c₁.nreg sV = v
        rw [regB_other _ _ _ (fun i hi => by
          zufbh
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [dstI, sV, sA, sX, sN, sE, sw]), v1, hv]
        zulcg
        simp_all
    · zufoc
      refine IRS.skip hI₁ ⟨?_, o1, rfl⟩
      rw [v1, hv]
      zulcg
      simp_all
  · rintro c₂ hI₂ hA₂ hA₂' ⟨v2, o2, m2⟩
    have hK₂ := hK.fix hI₂
    have eA2 : ztbae := by_simp_all
    refine (put1_irs hI₂ hK₂ by_omega).mono le_rfl ?_
    simp_all

/-! ## The twelve slots -/

/-- A list of slots. -/
def slotsOf : List ztw → Stmt
  | [] => .skip
  | p :: l => .seq (slotS p.1 p.2) ztwel

/-- The slots of the label shot: the entries `eR0, eR1, eR2`, the places `0 … 3`. -/
def slotPairs : List ztw :=
  [(eR0, K0), (eR0, K1), (eR0, K2), (eR0, K3), (eR1, K0), (eR1, K1), (eR1, K2), (eR1, K3),
    (eR2, K0), (eR2, K1), (eR2, K2), (eR2, K3)]
theorem slotVal_congr {m m' : ℕ → ℕ} {AL E g e k : ℕ} (hk : k ≤ 3)
    (h : ∀ a, a < AL + 7 * E → m' a = m a) :
    slotVal m' AL E g e k = slotVal m AL E g e k := by
  zulcg
  grind
set_option maxHeartbeats 1000000 in
/-- **A list of slots**: the values in order at the allocator. -/
theorem slots_irs : ∀ (l : List ztw) {c : Config}, IInv W c₀ c → Consts c₀ →
    (∀ p ∈ l, ¬ SlotW p.1 ∧ ¬ SlotW p.2 ∧ p.1 ≠ ALLOC ∧ p.2 ≠ ALLOC ∧ c.nreg p.2 ≤ 3) →
    c.nreg ztfx + 7 * c.nreg ztex ≤ c.nreg ALLOC → c.nreg gL < c.nreg ALLOC →
    c.nreg ALLOC + slotK * l.length ≤ W →
    IRS P W c₀ ztwel c (slotK * l.length) (fun c' =>
      c'.nreg ALLOC = c.nreg ALLOC + l.length ∧
      ztgsu ∧
      zth ∧
      ∀ i, i < l.length → c'.nmem ztfqi =
        slotVal c.nmem ztwml ztxcl ztqhh
          (c.nreg (l.getD i ztdr).1) (c.nreg (l.getD i ztdr).2))
  | [], c, hI, _, _, _, _, _ => IRS.skip hI by_simp_all
  | p :: l, c, hI, hK, hl, hAL, hgL, hroom => by
    obtain ⟨he, hk, -, -, hk3⟩ := hl p List.mem_cons_self
    zubwc
    simp only [List.length_cons] at hroom ⊢
    refine (IRS.seq (K₂ := slotK * l.length)
      (slot_irs hI hK he hk hk3 by_omega by_nlinarith) ?_).mono by_grind
      ztb
    rintro c₁ hI₁ hA₁ hA₁' ⟨e1, o1, m1⟩
    have nW : ∀ q, (q = ALLOC ∨ q = gL ∨ q = sw 300 ∨ q = sw 301) → ¬ SlotW q := by
      zuiby

      rcases hq with rfl | rfl | rfl | rfl <;>
        rcases h with h | h | h | h | h <;> simp [ALLOC, gL, sV, sA, sX, sN, sE, sw] at h
    have r300 : c₁.nreg _ = c.nreg ztfx :=
      o1 _ by_grind by_decide
    have r301 : c₁.nreg _ = c.nreg ztex :=
      o1 _ by_grind by_decide
    have rgL : c₁.nreg gL = c.nreg gL := by_grind
    have hmlow : ztjbb := fun a ha => by
      zvnmf; zvmwf; grind
    have hl' : ∀ q ∈ l, ¬ SlotW q.1 ∧ ¬ SlotW q.2 ∧ q.1 ≠ ALLOC ∧ q.2 ≠ ALLOC ∧
        c₁.nreg q.2 ≤ 3 := fun q hq => by
      grind
    refine (slots_irs l hI₁ hK hl' by_omega by_omega
      by_grind).mono le_rfl ?_
    zucph
    refine ⟨by_omega, by_grind,
      fun a ha => by_grind, fun i hi => ?_⟩
    zubuk
    · rw [f3 _ by_omega, m1]
      simp
    · have hi' : i < l.length := by_omega
      rw [show c.nreg ALLOC + ztg = c₁.nreg ALLOC + i by zvmxy; ring, f4 i hi',
        r300, r301, rgL, hmlow _ hgL]
      zufax
      have hmem : l.getD i ztdr ∈ l := by
        grind
      obtain ⟨a, b, d, f, g⟩ := hl _ (List.mem_cons_of_mem _ hmem)
      rw [o1 _ a d, o1 _ b f]
      exact slotVal_congr g by_grind
end
end Lab0
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace Lab0
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Chain (sideInArc)
open OracleQ (sk ek)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The setup of the gap part. -/
def gS0 : List Instr :=
  [.copyN gL ALLOC, .copyN lMD ztqm, .addN lCD lMD K1, .copyN lNF ztbz,
    .subN lE zthy K1, .constN lH 0]

/-- **The gap regions.** -/
def gapS : Stmt := .seq (block gS0) (.seq lh1 (.seq (block [.constN lE 6]) lh1))

/-- The cost of the gap part. -/
def gapK (T : ℕ) : ℕ := 6 + (lh1K T + (1 + lh1K T))

/-- **An answer of double identification** for the key `p` (parameter `0`). -/
def LocAt (C : Chain) (Q : Polygon) (N : NF) (p j : ℕ) : Prop :=
  j < N.arcs.length ∧
    (¬ (chainModel C).IsCut ztwjh (p : ℝ) →
      N.F ztc Q = ∅ ∨
        sideInArc ztwvb ztwus (p : ℝ)) ∧
    ((chainModel C).IsCut ztwjh (p : ℝ) →
      sk ztc Q N j = (p : ℝ) ∨ ek ztc Q N j = (p : ℝ))
theorem key_zero (M : Model) (Q : Polygon) (p : ℕ) : M.key Q ztcye = (p : ℝ) := by
  simp
theorem pp_zero (M : Model) (Q : Polygon) (n p : ℕ) : ProperPos M Q n ztcye := by
  have : M.param Q ztcye = 0 := rfl
  exact ztpfc
variable (m f : ℕ → ℕ)
theorem gS0_val :
    regB m gS0 f gL = f ALLOC ∧ regB m gS0 f lMD = f ztqm ∧
    regB m gS0 f lCD = f ztqm + f K1 ∧ regB m gS0 f lNF = f ztbz ∧
    regB m gS0 f lE = f zthy - f K1 ∧ regB m gS0 f lH = 0 ∧
    ∀ q, q ≠ gL → ¬ (sw 1100 ≤ q ∧ q ≤ sw 1119) → regB m gS0 f q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q h1 h2 => regB_other _ _ _ ztdp⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [gS0, List.mem_cons, List.not_mem_nil, or_false] at hi
    unfold gL lMD lCD lNF lE lH sw at *
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;> omega
theorem gS0_ok (hb : f ztqm + f K1 ≤ W) : okB W m gS0 f := by
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  have hb' : f 240031 + f 240611 ≤ W := hb
  simp only [gS0, okB, okI, regI, upd, gL, lMD, lCD, lNF, lE, lH, K1, ALLOC, sw]
  grind
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The gap regions**: the three regions at each of the walk vertices `2 m₂ + 6` and `6` of
`C₂`, as six words at the list address `gL`. -/
theorem gap_irs {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} {E : ℕ} (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c)
    (hroom : c.nreg ALLOC + gapK ztdg ≤ W) :
    IRS P W c₀ gapS c (gapK ztdg) (fun c' =>
      c'.nreg gL = c.nreg ALLOC ∧ c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      zth ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ gL → ¬ (sw 1100 ≤ r ∧ r ≤ sw 1119) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      ∃ j₁ j₂, LocAt J.right zta N₂ ztekv j₁ ∧
        LocAt J.right zta N₂ 6 j₂ ∧
        ∀ i, i < 3 → c'.nmem ztfqi = (Sweep.nbrRegs N₂ j₁).getD i 0 ∧
          c'.nmem (c.nreg ALLOC + 3 + i) = (Sweep.nbrRegs N₂ j₂).getD i 0) := by
  zulje
  zudnn
  have hfix : ∀ q, IFix q → c.nreg q = c₀.nreg q := fun q hq => hI.hin q hq
  have e31 : c.nreg ztqm = c₀.nreg ztqm := hfix _ by_trivial
  have e4 : c.nreg ztbz = c₀.nreg ztbz := hfix _ by_trivial
  have e34 : ztyug := (hfix _ by_trivial).trans hS.hnr
  have k1 : ztfdp := (hK.fix hI).2.1
  have hmdW : c.nreg ztqm + c.nreg K1 ≤ W := by
    rw [e31, k1]; have := hS.hmwf.1; have := hI.hA; grind
  unfold gapS gapK
  unfold gapK at hroom
  refine IRS.seq (K₁ := 6) (K₂ := lh1K ztdg + (1 + lh1K ztdg))
    ((IRS.block gS0 hI (gS0_ok _ _ hmdW)).mono by_rfl ztb) ?_
  zufg
  obtain ⟨v1, v2, v3, v4, v5, v6, vo⟩ := gS0_val c.nmem c.nreg
  set c₁ : Config := { c with nreg := regB c.nmem gS0 c.nreg } with hc₁
  have eA1 : ztdc :=
    vo ALLOC by_decide by_decide
  have eT1 : ztguk := hI₁.hin _ by_trivial
  have hL₁ : LCtx P W J.right N₂ E c₁ := lctx_of hS hI₁ hA.htab hA.hTB hA.hTW
    by_simp_all
    by_simp_all
    by_simp_all
  have hE1 : c₁.nreg lE = 2 * J.right.m + 6 := by
    simp_all
  have hH1 : c₁.nreg lH = 0 := v6
  zuery
  refine IRS.seq (K₁ := lh1K ztdg) (K₂ := 1 + lh1K ztdg)
    ((lh1_irs hI₁ hK hL₁ by_omega (by zupcx; exact pp_zero _ _ _ _)
      by_grind).mono (by rw [eT1]) (fun _ h => h)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hj1, hl1, hl2, hLL2, hAl2, hlist2, hm2, fr2, -, -, -⟩
  have fr2' : ∀ q, bandOf q ∉ oracleBands → ¬ ztltq → q ≠ ALLOC →
      c₂.nreg q = c₁.nreg q := fun q h1 h2 h3 => fr2 q h1 h2 h3
  refine IRS.seq (K₁ := 1) (K₂ := lh1K ztdg)
    (IRS.block [.constN lE 6] hI₂ ⟨⟨iscr_sw by_decide by_decide,
      by omega⟩, trivial⟩) ?_
  zubup
  set c₃ : Config := { c₂ with nreg := regB c₂.nmem [.constN lE 6] c₂.nreg } with hc₃
  have o3 : ∀ q, q ≠ lE → c₃.nreg q = c₂.nreg q := fun q hq => by
    simp only [hc₃, regB, regI]; exact upd_other _ _ _ hq
  have hE3 : c₃.nreg lE = 6 := by_rfl
  have nO : ztcge := fun q h1 h2 =>
    not_oracle_sw h1 h2
  have k32 : ∀ q, (q = lMD ∨ q = lCD ∨ q = lNF ∨ q = lH ∨ q = gL) → c₃.nreg q = c₁.nreg q := by
    zuco
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      (rw [o3 _ by_decide]
       exact fr2' _ ztdoy by_decide by_decide)
  have hL₃ : LCtx P W J.right N₂ E c₃ := lctx_of hS hI₃ hA.htab hA.hTB hA.hTW
    by_grind
    by_grind
    by_grind
  have hH3 : c₃.nreg lH = 0 := by_grind
  have eT3 : ztshp := hI₃.hin _ by_trivial
  have eA3 : c₃.nreg ALLOC = c.nreg ALLOC + 3 := by
    grind
  refine ((lh1_irs hI₃ hK hL₃ by_omega (by rw [hH3]; exact pp_zero _ _ _ _)
      by_grind).mono (by rw [eT3]) ?_)
  rintro c₄ ⟨hj4, hl4, hl4', hLL4, hAl4, hlist4, hm4, fr4, -, -, -⟩
  have fr4' : ∀ q, bandOf q ∉ oracleBands → ¬ ztltq → q ≠ ALLOC →
      c₄.nreg q = c₃.nreg q := fun q h1 h2 h3 => fr4 q h1 h2 h3
  have hm3 : ztdrk := rfl
  refine ⟨?_, by_omega, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_, c₂.nreg lJ, c₄.nreg lJ,
    ⟨hj1, ?_, ?_⟩, ⟨hj4, ?_, ?_⟩, fun i hi => ⟨?_, ?_⟩⟩
  · rw [fr4' gL ztdoy by_decide by_decide,
      k32 _ ztbakw]
    omega
  · grind
  · have h3' : ¬ (sw 1108 ≤ r ∧ r ≤ sw 1119) :=
      fun h => h3 ⟨le_trans (show sw 1100 ≤ sw 1108 by decide) h.1, h.2⟩
    have h3e : r ≠ lE := by rintro rfl; exact h3 by_decide
    rw [fr4' r h1 h3' h4, o3 r h3e, fr2' r h1 h3' h4]
    grind
  · intro hc; rw [hE1, hH1, key_zero] at hl1; grind
  · intro hc; rw [hE1, hH1, key_zero] at hl2; grind
  · intro hc; rw [hE3, hH3, key_zero] at hl4; grind
  · intro hc; rw [hE3, hH3, key_zero] at hl4'; grind
  · grind
  · rw [show c.nreg ALLOC + 3 + i = c₃.nreg ALLOC + i by rw [eA3], hlist4 i hi]
end
end Lab0
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace Lab0
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The body of the contract of the binary search.** -/
def LSBody (lsearch : Stmt) (κ : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (c₀ c : Config),
    IInv W c₀ c → Consts c₀ → ChainCtx P W c ztjl J.whole →
    ztug →
    c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC →
    c.nreg ztex < 2 ^ c.nreg TLR →
    c.nreg ztfx + 7 * c.nreg ztex ≤ c.nreg ALLOC →
    c.nreg ztfg < (chainModel J.whole).W.n →
    (∀ j, j < c.nreg ztex → SweepEv.PosW P J ztwun
      ztwrr) →
    SweepEv.PosW P J (c.nreg S0C.lsxE) (c.nreg S0C.lsxH) →
    (∀ i j, i ≤ j → j < c.nreg ztex →
      S0C.lsPr P J c.nmem ztwml ztwmp ztrbm j →
      S0C.lsPr P J c.nmem ztwml ztwmp ztrbm i) →
    c.nreg ALLOC + κ * ztuc ≤ W →
    IRS P W c₀ lsearch c ztxzd (fun c' =>
      c'.nreg S0C.lsI ≤ c.nreg ztex ∧
      (∀ j, j < c'.nreg S0C.lsI →
        S0C.lsPr P J c.nmem ztwml ztwmp
          ⟨c.nreg S0C.lsxE, c.nreg S0C.lsxH⟩ j) ∧
      (∀ j, c'.nreg S0C.lsI ≤ j → j < c.nreg ztex →
        ¬ S0C.lsPr P J c.nmem ztwml ztwmp
          ⟨c.nreg S0C.lsxE, c.nreg S0C.lsxH⟩ j) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ S0C.LSet r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth)
theorem lsBody_of (h : S0C.LSearchSpec) : ∃ ls κ, LSBody ls κ := h
section Env
variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}

/-- The chain descriptor of `C` at `sw 2`. -/
theorem ctxW (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) :
    ChainCtx P W c ztjl J.whole := by
  zubbs
  have h0 : ztziz :=
    ⟨hA.hG, hA.hWh, hJWF.2.2.1, ⟨H, hJ.2.2, hA.hostReg⟩, hA.hP, hA.hWm⟩
  zuhcs

/-- The predicate of the search reads only the two words of the record. -/
theorem lsPr_congr {m m' : ℕ → ℕ} {AL G : ℕ} {x : WPos} {j : ℕ}
    (h0 : m' ztcst = m ztcst) (h1 : m' ztbyd = m ztbyd) :
    S0C.lsPr P J m' AL G x j ↔ S0C.lsPr P J m AL G x j := by
  unfold S0C.lsPr; simp_all

/-- The block setting the target of the search. -/
def lsIn : List Instr := [.copyN S0C.lsxE zP, .copyN S0C.lsxH zPh]
set_option maxHeartbeats 4000000 in
/-- **The binary search at the arrival position of the query point.** -/
theorem search_irs {ls : Stmt} {κL : ℕ} (hls : LSBody ls κL)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) {z : Point} (hz : z ∈ J.left.set)
    {σ : ℝ} (hzP : c.nreg zP < (chainModel J.whole).W.n)
    (hpp : ProperPos ztbm zta P.n ztlo)
    (harr : Arrival (chainModel J.whole).W z σ ztdmx
      ztwmc)
    (hroom : c.nreg ALLOC + ztzaz ≤ W) :
    IRS P W c₀ ztowf c ztzaz (fun c' =>
      c'.nreg S0C.lsI ≤ rd c₀ bSweep 301 ∧
      (∀ j, j < c'.nreg S0C.lsI → S0C.lsPr P J c₀.nmem ztjt ztwnj
        ⟨c.nreg zP, c.nreg zPh⟩ j) ∧
      (∀ j, c'.nreg S0C.lsI ≤ j → j < rd c₀ bSweep 301 →
        ¬ S0C.lsPr P J c₀.nmem ztjt ztwnj ztlo j) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ (sw 4000 ≤ r ∧ r ≤ sw 4021) → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      zth) := by
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  refine IRS.seq (K₁ := 2) (K₂ := κL * ztgf)
    (IRS.block lsIn hI ⟨s 4020 by_norm_num by_norm_num, s 4021 by_norm_num by_norm_num,
      trivial⟩) ?_
  zufg
  set c₁ : Config := { c with nreg := regB c.nmem lsIn c.nreg } with hc₁
  have v1 : c₁.nreg S0C.lsxE = c.nreg zP := by
    rfl
  have v2 : c₁.nreg S0C.lsxH = c.nreg zPh := by
    rfl
  have vo : ∀ q, q ≠ S0C.lsxE → q ≠ S0C.lsxH → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    regB_other _ _ _ (fun i hi => by
      simp only [lsIn, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> zvmwd <;> intro h <;> subst h <;> simp at h1 h2)
  have hfix : ∀ q, IFix q → c₁.nreg q = c₀.nreg q := fun q hq => hI₁.hin q hq
  have eTB : ztsgk := hfix _ by_trivial
  have eTL : ztguk := hfix _ by_trivial
  have e300 : c₁.nreg ztfx = rd c₀ bSweep 300 := hfix _ by_trivial
  have e301 : c₁.nreg ztex = rd c₀ bSweep 301 := hfix _ by_trivial
  have e40 : c₁.nreg ztfg = c₀.nreg ztfg := hfix _ by_trivial
  zuerf
  have hm : ∀ a, a < c₀.nreg ALLOC → c₁.nmem a = c₀.nmem a := fun a ha => hI₁.hm a ha
  have hlsP : ∀ j, j < rd c₀ bSweep 301 →
      (S0C.lsPr P J c₁.nmem ztzeh ztyjc
        ⟨c₁.nreg S0C.lsxE, c₁.nreg S0C.lsxH⟩ j ↔
      S0C.lsPr P J c₀.nmem ztjt ztwnj ztlo j) := by
    zun
    rw [e300, e40, v1, v2]
    exact lsPr_congr zttnx zttnx
  have hG : c₁.nreg ztfg < (chainModel J.whole).W.n := by
    rw [e40, S0C.aenv_gW hA]; exact_mod_cast S0C.gW_lt J
  have hrec : ∀ j, j < c₁.nreg ztex → SweepEv.PosW P J
      (c₁.nmem (c₁.nreg ztfx + 7 * j)) (c₁.nmem (c₁.nreg ztfx + 7 * j + 1)) := by
    zun
    zukqw
    rw [e300, hm _ by_omega, hm _ by_omega]
    exact S0C.log_posW hA hj
  have hx : SweepEv.PosW P J (c₁.nreg S0C.lsxE) (c₁.nreg S0C.lsxH) := by
    zunqo
    exact ⟨hzP, hpp, fun h0 => S0C.query_h6 hz harr h0⟩
  have hdc : ∀ i j, i ≤ j → j < c₁.nreg ztex →
      S0C.lsPr P J c₁.nmem ztzeh ztyjc
        ⟨c₁.nreg S0C.lsxE, c₁.nreg S0C.lsxH⟩ j →
      S0C.lsPr P J c₁.nmem ztzeh ztyjc
        ⟨c₁.nreg S0C.lsxE, c₁.nreg S0C.lsxH⟩ i := by
    intro i j hij hj h
    zukqw
    rw [hlsP i by_omega]
    rw [hlsP j hj] at h
    exact S0C.log_mono hA _ hij hj h
  have hA1 : ztdc := vo _ by_decide by_decide
  have h := hls P W J c₀ c₁ hI₁ hA.hK (ctxW hA hI₁)
    (fun j hj => by
      zukra
      rw [eTB, hm _ (by have := hA.hTW; omega)]
      exact hA.htab j hj)
    (by zunqt; have := hA.hTW; have := hI₁.hA; omega)
    (by rw [e301, eTL]; have := hA.hbigE; omega)
    (by rw [e300, e301]; have := hI₁.hA; omega) hG hrec hx hdc
    by_grind
  rw [eTL] at h
  zuevu
  rintro c' ⟨r1, r2, r3, r4, r5, r6⟩
  rw [e301] at r1
  refine ⟨r1, fun j hj => (hlsP j by_omega).1 (r2 j hj),
    fun j hj hjE => fun h' => r3 j hj by_omega ((hlsP j hjE).2 h'),
    fun r h1 h2 h3 => ?_, fun a ha => by_grind⟩
  rw [r4 r h1 (fun h => h2 (by unfold S0C.LSet at h; unfold sw at *; omega)) h3]
  exact vo r (by rintro rfl; trivial) (by rintro rfl; trivial)
end Env
end
end Lab0
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace Lab0
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
@[expose] public section
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ : Config}

/-- The label words of a log record. -/
theorem logRec_labels {m : ℕ → ℕ} {AL : ℕ} {ls : List ztck}
    (hls : LogRecsAt m AL ls) {i : ℕ} (hi : i < ls.length) :
    m ztniv = (ls.getD i ztem).2.2.1 ∧
    ∀ k, k ≤ 3 → m ztldv =
      [(ls.getD i ztem).2.2.2.1, (ls.getD i ztem).2.2.2.2.1,
        (ls.getD i ztem).2.2.2.2.2.1,
        (ls.getD i ztem).2.2.2.2.2.2].getD k 0 := by
  obtain ⟨-, -, a2, a3, a4, a5, a6⟩ := hls i hi
  refine ⟨a2, fun k hk => ?_⟩
  interval_cases k
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-- **A label of a log record** (place below its count) is a region index of `N₂`. -/
theorem label_valid (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {e k : ℕ} (he : e < rd c₀ bSweep 301)
    (hk : k < c₀.nmem (rd c₀ bSweep 300 + 7 * e + 2)) (hk3 : k ≤ 3) :
    c₀.nmem (rd c₀ bSweep 300 + 7 * e + 3 + k) < N₂.nRegions := by
  zubph
  have he' : e < ls.length := by_omega
  obtain ⟨n2, hlab⟩ := logRec_labels hls he'
  rw [hlab k hk3]
  rw [n2] at hk
  have hmem : ls.getD e ztem ∈ ls := by
    rw [List.getD_eq_getElem _ _ he']; simp
  obtain ⟨-, -, b0, b1, b2, b3⟩ := hlsW _ hmem
  interval_cases k
  · exact b0 by_omega
  · exact b1 by_omega
  · exact b2 by_omega
  · exact b3 by_omega

/-- The label set of a log entry. -/
theorem logLab_eq {Q : Polygon} {N : NF} {ls : List ztck} {i : ℕ}
    (hi : i < ls.length) :
    logLab J Q N ls i = labSet J Q N (ls.getD i ztem).2.2.1
      (ls.getD i ztem).2.2.2.1 (ls.getD i ztem).2.2.2.2.1
      (ls.getD i ztem).2.2.2.2.2.1
      (ls.getD i ztem).2.2.2.2.2.2 := by
  unfold logLab logOf
  simp_all

/-- **A region of the label set of a log entry** is the region of a label in memory. -/
theorem label_mem {ls : List ztck} {m : ℕ → ℕ} {AL : ℕ}
    (hls : LogRecsAt m AL ls) {i : ℕ} (hi : i < ls.length) {V : Set Point}
    (hV : V ∈ logLab J zta N₂ ls i) :
    ∃ k, k ≤ 3 ∧ k < m ztniv ∧
      regOf ztj zta N₂ (m ztldv) = V := by
  rw [logLab_eq hi] at hV
  obtain ⟨n2, hlab⟩ := logRec_labels hls hi
  obtain ⟨l, hl, rfl⟩ := hV
  rcases hl with ⟨h0, rfl⟩ | ⟨h1, rfl⟩ | ⟨h2, rfl⟩ | ⟨h3, rfl⟩
  · exact ⟨0, by_norm_num, by_omega, by rw [hlab 0 by_norm_num]; rfl⟩
  · exact ⟨1, by_norm_num, by_omega, by_simp_all⟩
  · exact ⟨2, by_norm_num, by_omega, by_simp_all⟩
  · exact ⟨3, le_rfl, by_omega, by_simp_all⟩

/-- **Every entry register and label place has a slot.** -/
theorem slotPairs_cover {e k : ℕ} (he : e = eR0 ∨ e = eR1 ∨ e = eR2) (hk : k ≤ 3) :
    ∃ idx, idx < 12 ∧ (slotPairs.getD idx ztdr).1 = e ∧
      ∀ c : Config, Consts c → c.nreg (slotPairs.getD idx ztdr).2 = k := by
  rcases he with rfl | rfl | rfl <;> interval_cases k
  · exact ⟨0, by_norm_num, rfl, fun c h => h.1⟩
  · exact ⟨1, by_norm_num, rfl, fun c h => h.2.1⟩
  · exact ⟨2, by_norm_num, rfl, fun c h => h.2.2.2.2.2.1⟩
  · exact ⟨3, by_norm_num, rfl, fun c h => h.2.2.2.2.2.2⟩
  · exact ⟨4, by_norm_num, rfl, fun c h => h.1⟩
  · exact ⟨5, by_norm_num, rfl, fun c h => h.2.1⟩
  · exact ⟨6, by_norm_num, rfl, fun c h => h.2.2.2.2.2.1⟩
  · exact ⟨7, by_norm_num, rfl, fun c h => h.2.2.2.2.2.2⟩
  · exact ⟨8, by_norm_num, rfl, fun c h => h.1⟩
  · exact ⟨9, by_norm_num, rfl, fun c h => h.2.1⟩
  · exact ⟨10, by_norm_num, rfl, fun c h => h.2.2.2.2.2.1⟩
  · exact ⟨11, by_norm_num, rfl, fun c h => h.2.2.2.2.2.2⟩

/-- The slot pairs: entry registers and constant registers. -/
theorem slotPairs_facts : ∀ p ∈ slotPairs,
    (p.1 = eR0 ∨ p.1 = eR1 ∨ p.1 = eR2) ∧
      (p.2 = K0 ∨ p.2 = K1 ∨ p.2 = K2 ∨ p.2 = K3) := by
  decide
end
end Lab0
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
namespace Lab0
open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def eIn : List Instr := [.copyN eR2 S0C.lsI, .subN eR1 eR2 K1, .subN eR0 eR1 K1]

/-- The inputs of the gather: the normal form of `C₂`, eighteen regions. -/
def gIn : List Instr := [.copyN gNF ztbz, .constN gC 18]

/-- **The label candidates of a side-0 query.** -/
def lab0S (ls sh : Stmt) : Stmt :=
  .seq ztowf (.seq gapS (.seq (block eIn) (.seq (slotsOf slotPairs)
    (.seq (block gIn) (.seq (gather zted) (symShot sh ztqm gBase gK zted K1))))))

/-- The bound on the gather. -/
def gB (D : ℕ) : ℕ := 11 + 18 * (regK ztef + 2)

/-- The total budget. -/
def lab0Kt (κL T Fg D : ℕ) : ℕ :=
  (2 + κL * ztxz) + (gapK T + (3 + (slotK * 12 + (2 + (gB D + symShotK Fg (18 * ztef))))))
theorem lab0_cost (κL T Fg D : ℕ) :
    lab0Kt κL T Fg D ≤ ztuff * ztmo * ztbbs := by
  unfold lab0Kt gapK lh1K slotK gB regK arcK symShotK ShotList.shotCost offerK
  grind
theorem symShotK_mono {Fg K K' : ℕ} (h : K ≤ K') : symShotK Fg K ≤ symShotK Fg K' := by
  unfold symShotK ShotList.shotCost
  simp_all
section Run
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable (m f : ℕ → ℕ)
theorem eIn_val (hk : f K1 = 1) :
    regB m eIn f eR2 = f S0C.lsI ∧ regB m eIn f eR1 = f S0C.lsI - 1 ∧
    regB m eIn f eR0 = f S0C.lsI - 1 - 1 ∧
    ∀ q, q ≠ eR0 → q ≠ eR1 → q ≠ eR2 → regB m eIn f q = f q := by
  zufvb
  refine ⟨?_, ?_, ?_, fun q h0 h1 h2 => regB_other _ _ _ ztdp⟩
  · rfl
  · zucck

  · zucck

  · simp only [eIn, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> zvmwd <;> intro h <;> subst h <;> simp_all
theorem gIn_val :
    regB m gIn f gNF = f ztbz ∧ regB m gIn f gC = 18 ∧
    ∀ q, q ≠ gNF → q ≠ gC → regB m gIn f q = f q := by
  refine ⟨?_, ?_, fun q h0 h1 => regB_other _ _ _ ztdp⟩
  · rfl
  · rfl
  · simp only [gIn, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> zvmwd <;> intro h <;> subst h <;> simp_all
end Run

/-! ## The contract -/
theorem acc_regs {j : ℕ} (hj : j ≤ 12) : 240000 ≤ accA + j ∧ accA + j < 250000 ∧
    ¬ (sw 1000 ≤ accA + j ∧ accA + j ≤ sw 1119) ∧ ¬ (sw 4000 ≤ accA + j ∧ accA + j ≤ sw 4037) ∧
    accA + j ≠ ALLOC := by
  unfold accA sw ALLOC; omega
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 40000 in
/-- **The label candidates of a side-0 query** from the binary search in the log. -/
theorem lab0_of (hLS : S0C.LSearchSpec) : Lab0Spec := by
  obtain ⟨ls, κL, hls⟩ := lsBody_of hLS
  refine ⟨lab0S ls, fun D => ztuff * ztmo, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E L s z hA hI hz hzs hzt hfree hzPn hpp
    harr hs hsl hseval hbR hacc hroom
  zubmr
  have hcost := lab0_cost κL ztdg ztwiu zto
  have hroom' : c.nreg ALLOC + lab0Kt κL _ _ _ ≤ W :=
    le_trans (Nat.add_le_add_left hcost _) hroom
  unfold lab0Kt at hroom'
  zudnn
  zuiwt
  have hN := hA.hNF₂
  have nO : ztcge := fun q h1 h2 =>
    not_oracle_sw h1 h2
  unfold lab0S
  -- 1. the binary search
  refine (IRS.seq
    (search_irs hls hA hI hz hzPn hpp harr by_omega) ?_).mono
    (le_trans (le_of_eq rfl) hcost) ztb
  rintro c₂ hI₂ hA₂ hA₂' ⟨t_le, t_lt, t_ge, fr2, m2⟩
  set t := c₂.nreg S0C.lsI with ht
  set G := c₂.nreg ALLOC with hG
  -- 2. the gap regions
  refine IRS.seq
    (gap_irs hA hI₂ by_omega) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨g1, g2, g3, g4, j₁, j₂, hj₁, hj₂, g5⟩
  -- 3. the entries
  have k3 := hK.fix hI₃
  refine IRS.seq
    ((IRS.block eIn hI₃ ⟨iscr_sw by_decide by_decide, iscr_sw by_decide by_decide,
      iscr_sw by_decide by_decide, trivial⟩).mono by_rfl (fun _ h => h)) ?_
  rintro c₄ hI₄ hA₄ hA₄' rfl
  obtain ⟨e2v, e1v, e0v, eo⟩ := eIn_val c₃.nmem c₃.nreg k3.2.1
  set c₄ : Config := { c₃ with nreg := regB c₃.nmem eIn c₃.nreg } with hc₄
  have tl3 : c₃.nreg S0C.lsI = t :=
    g4 _ ztdoy by_decide by_decide by_decide
  have eA4 : c₄.nreg ALLOC = G + 6 := by
    show regB _ _ _ _ = _; rw [eo _ by_decide by_decide by_decide, g2]
  have egL4 : c₄.nreg gL = G := by
    show regB _ _ _ _ = _; rw [eo _ by_decide by_decide by_decide, g1]
  have em4 : ztmvj := rfl
  -- 4. the slots
  have hK₄ := hK.fix hI₄
  have f300 : ∀ c', IInv W c₀ c' → c'.nreg ztfx = rd c₀ bSweep 300 := fun c' h =>
    h.hin _ by_trivial
  have f301 : ∀ c', IInv W c₀ c' → c'.nreg ztex = rd c₀ bSweep 301 := fun c' h =>
    h.hin _ by_trivial
  zuerf
  have hitems : ∀ p ∈ slotPairs, ¬ SlotW p.1 ∧ ¬ SlotW p.2 ∧ p.1 ≠ ALLOC ∧ p.2 ≠ ALLOC ∧
      c₄.nreg p.2 ≤ 3 := by
    zuda
    obtain ⟨h1, h2⟩ := slotPairs_facts p hp
    zuflw
    · rcases h1 with h | h | h <;> zvmwc <;> unfold SlotW <;> decide
    · rcases h2 with h | h | h | h <;> zvmwc <;> unfold SlotW <;> decide
    · rcases h1 with h | h | h <;> zvmwc <;> decide
    · rcases h2 with h | h | h | h <;> zvmwc <;> decide
    · rcases h2 with h | h | h | h <;> zvmwc
      · rw [hK₄.1]; omega
      · rw [hK₄.2.1]; omega
      · rw [hK₄.2.2.2.2.2.1]; omega
      · rw [hK₄.2.2.2.2.2.2]
  refine IRS.seq
    (slots_irs slotPairs hI₄ hK hitems
      (by rw [f300 _ hI₄, f301 _ hI₄]; have := hI₄.hA; omega) by_omega
      (by zupdh; simp [slotPairs]; omega)) ?_
  rintro c₅ hI₅ hA₅ hA₅' ⟨s1, s2, s3, s4⟩
  simp only [show slotPairs.length = 12 from rfl] at s1 s4
  -- 5. the inputs of the gather
  refine IRS.seq
    ((IRS.block gIn hI₅ ⟨iscr_sw by_decide by_decide,
      ⟨iscr_sw by_decide by_decide, by_omega⟩, trivial⟩).mono
      by_rfl ztb) ?_
  rintro c₆ hI₆ hA₆ hA₆' rfl
  obtain ⟨n6, c6v, go⟩ := gIn_val c₅.nmem c₅.nreg
  set c₆ : Config := { c₅ with nreg := regB c₅.nmem gIn c₅.nreg } with hc₆
  have egL6 : c₆.nreg gL = G := by
    show regB _ _ _ _ = _
    rw [go _ by_decide by_decide, s2 _ (by unfold SlotW gL sV sA sX sN sE sw; omega)
      by_decide, egL4]
  have eA6 : c₆.nreg ALLOC = G + 18 := by
    show regB _ _ _ _ = _
    rw [go _ by_decide by_decide, s1, eA4]
  have em6 : ztlar := rfl
  -- the words of the list
  have hI4m := hI₄.hm
  have gap1 : ∀ i, i < 3 → c₆.nmem ztnle = (Sweep.nbrRegs N₂ j₁).getD i 0 := fun i hi => by
    zunug; exact (g5 i hi).1
  have gap2 : ∀ i, i < 3 → c₆.nmem (G + 3 + i) = (Sweep.nbrRegs N₂ j₂).getD i 0 := fun i hi => by
    zunug; exact (g5 i hi).2
  have slotw : ∀ idx, idx < 12 → c₆.nmem (G + 6 + idx) =
      slotVal c₄.nmem ztjt ztiah ztvnn
        (c₄.nreg (slotPairs.getD idx ztdr).1) (c₄.nreg (slotPairs.getD idx ztdr).2) := by
    intro idx hidx
    rw [em6, show G + 6 + idx = c₄.nreg ALLOC + idx by zupdh, s4 idx hidx, f300 _ hI₄,
      f301 _ hI₄, egL4]
  have nbr_lt : ∀ j, j < N₂.arcs.length → ∀ i, i < 3 → (Sweep.nbrRegs N₂ j).getD i 0 < N₂.nRegions :=
    fun j hj i hi => nbrRegs_lt hN hj _ (by
      rw [List.getD_eq_getElem _ _ (by simp [Sweep.nbrRegs]; omega)]; simp)
  have hg0 : c₄.nmem G < N₂.nRegions := by
    have := (g5 0 by_norm_num).1
    zukqd
    rw [em4, this]; exact nbr_lt j₁ hj₁.1 0 by_norm_num
  have slot_lt : ∀ v w, w ≤ 3 →
      slotVal c₄.nmem ztjt ztiah ztvnn v w < N₂.nRegions := by
    intro v w hw
    zulcg
    zugif
    · obtain ⟨hv, hwn⟩ := hc
      rw [hI4m _ by_omega] at hwn ⊢
      exact label_valid hA hv hwn hw
    omega
  have valid : ∀ i, i < 18 → c₆.nmem ztnle < N₂.nRegions := by
    zug
    rcases (show i < 3 ∨ (3 ≤ i ∧ i < 6) ∨ 6 ≤ i by omega) with h | ⟨h1, h2⟩ | h
    · rw [gap1 i h]; exact nbr_lt j₁ hj₁.1 i h
    · rw [show G + i = G + 3 + (i - 3) by omega, gap2 _ by_omega]
      exact nbr_lt j₂ hj₂.1 _ by_omega
    · rw [show G + i = G + 6 + ztjyn by omega, slotw _ by_omega]
      have hmem : slotPairs.getD ztjyn ztdr ∈ slotPairs := by
        rw [List.getD_eq_getElem _ _ (by simp [slotPairs]; omega)]; simp
      exact slot_lt _ _ (hitems _ hmem).2.2.2.2
  -- 6. the gather
  set rs : List ℕ := (List.range 18).map (fun i => c₆.nmem ztnle) with hrs_def
  have hrs_len : rs.length = 18 := by_rfl
  have hrs_get : ∀ j, j < 18 → rs.getD j 0 = c₆.nmem (G + j) := fun j hj => by
    simp [rs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  have mem_rs : ∀ i, i < 18 → c₆.nmem _ ∈ rs := fun i hi =>
    List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  have hrs : ∀ r ∈ rs, r < N₂.nRegions := by
    zuz
    zufyl
    exact valid i ztuzp
  obtain ⟨hAr, -⟩ := region_bounds' hP hN hA.hdeg₂
  have hArs : ∀ r ∈ rs, (N₂.region r).arcs.length ≤ c₀.nreg _ + 1 := fun r hr =>
    hAr r zttoi
  have hgK : gatherK N₂ rs ≤ gB zto := by
    have := gatherK_le hArs
    rw [hrs_len] at this
    unfold gB; omega
  have n6' : c₆.nreg gNF = c₀.nreg ztbz := by
    show regB _ _ _ _ = _; rw [n6]; exact hI₅.hin _ by_trivial
  refine IRS.seq
    ((gather_irs hI₆ hK
      (hA.ctxR hI₆) ⟨by_decide, by_decide, by unfold GSet sw; omega⟩ hP hN
      (hA.hN₂.transport (fun a ha => hI₆.hm a (by have := hA.hE; omega))) n6'
      (hA.hE.trans hI₆.hA) hrs (fun j hj => by rw [egL6, hrs_get j by_omega])
      by_omega by_rfl
      by_omega).mono hgK (fun _ h => h)) ?_
  rintro c₇ hI₇ hA₇ hA₇' ⟨⟨w1, w2, w3, w4, w5, w6, -, -, -⟩, hctx7⟩
  -- 7. the shot
  have hlen : (regArcs N₂ rs).length ≤ 18 * ztyem := by
    have := regArcs_length_le hArs
    rw [hrs_len] at this; omega
  have keep7 : ∀ r, bandOf r ∉ oracleBands → ¬ (sw 1000 ≤ r ∧ r ≤ sw 1119) →
      ¬ (sw 4000 ≤ r ∧ r ≤ sw 4037) → r ≠ ALLOC → c₇.nreg r = c.nreg r := by
    zufxp
    unfold sw at h2 h3
    rw [w6 r h1 (by unfold GSet sw; omega) h4]
    show regB _ _ _ _ = _
    rw [go r (by unfold gNF sw; omega) (by unfold gC sw; omega),
      s2 r (by unfold SlotW sV sA sX sN sE sw; omega) h4]
    show regB _ _ _ _ = _
    rw [eo r (by unfold eR0 sw; omega) (by unfold eR1 sw; omega) (by unfold eR2 sw; omega),
      g4 r h1 (by unfold gL sw; omega) ztce h4,
      fr2 r h1 ztce h4]
  have qD7 : c₇.nreg qD = c.nreg qD :=
    keep7 _ ztdoy by_decide by_decide by_decide
  have hs7 := symPtIn_copy hs
    ztxra
    ztxra
    ztxra
  have hacc7 : AccOK P accA ztdm J.whole.radius z
      (dirOf (c₇.nreg qD)) L c₇ := by
    rw [qD7]
    refine hacc.transport ztjvz
    obtain ⟨hj1, hj2, hj3, hj4, hj5⟩ := acc_regs hj
    exact keep7 _ (nO _ hj1 hj2) hj3 hj4 hj5
  have hK₇ := hK.fix hI₇
  have hzD := S0C.z_mem_right_dom hA.hP hz hzs hzt
  have hbox := J.right.dom_subset_box hzD
  have hMod : ModB J ztcpq ztcpr (c₇.nreg K1) = J.right := by
    rw [hK₇.2.1, hbR]; rfl
  have harcs : ∀ j, j < c₇.nreg gK →
      ShotList.PieceOK ztj zta P.n
        (ShotList.arcAt c₇.nmem ztqku j) ∧
      (chainModel J.right).arcWt
        ((chainModel J.right).key zta (ShotList.arcAt c₇.nmem ztqku j).1)
        ((chainModel J.right).key zta (ShotList.arcAt c₇.nmem ztqku j).2) ≤
        c₀.nreg ztbcb := by
    zun
    rw [w2] at hj
    rw [w1, w4 j hj]
    exact nArc_piece hP hN hA.hsg₂ (regArcs_lt hN hrs _ (by
      zuofp; simp))
  refine (symShot_irs hsh hBs hXl hI₇ hK hA.hG hA.hWh hA.hX hA.hcap hA.hOk₂
    (hA.mdR hI₇) hA.hostReg hctx7 harcs by_omega hs7 hsl hseval hzD hbox.1 hbox.2
    hzt hacc7 (by rw [hK₇.2.1]; omega) hMod rfl
    ⟨by_trivial, by_trivial, by_trivial,
      by trivial, by_trivial⟩
    (by rw [w2]; have := symShotK_mono (Fg := F ztq) hlen; omega)).mono
    (by rw [w2]; exact symShotK_mono hlen) ?_
  rintro c' ⟨L', hacc', hL', hcomp, k8, hA8, hm8⟩
  rw [qD7] at hacc' hL' hcomp
  refine ⟨⟨L', hacc', ?_, fun τ hτ => ?_, ?_⟩, fun r h1 h2 h3 h4 h5 => ?_, ?_, fun a ha => ?_⟩
  · zuflj
    · simp
    simp
  · zuejr
    · exact Or.inl hτ
    · rcases hτ with rfl | hτ
      · exact Or.inr ⟨hτ0, hon⟩
      · exact Or.inl hτ
  · intro ls' hlsl hlsrec i hidx V hV hcase hray
    have hσ : dirOf _ = 1 ∨ dirOf ztql = -1 := SweepPrim.dirOf_cases _
    have eR2v : c₄.nreg eR2 = t := by show regB _ _ _ _ = _; omega
    have eR1v : c₄.nreg eR1 = t - 1 := by show regB _ _ _ _ = _; rw [e1v, tl3]
    have eR0v : c₄.nreg eR0 = t - 1 - 1 := by show regB _ _ _ _ = _; omega
    have lab : ∀ e eR, (eR = eR0 ∨ eR = eR1 ∨ eR = eR2) → c₄.nreg eR = e → e < ls'.length →
        V ∈ logLab J zta N₂ ls' e →
        ∃ q, q < 18 ∧ regOf ztj zta N₂ ztpam = V := by
      intro e eR heR hev he hVe
      obtain ⟨k, hk3, hkn, hkV⟩ := label_mem hlsrec he hVe
      obtain ⟨idx, hidx', h1, h2⟩ := slotPairs_cover heR hk3
      refine ⟨6 + idx, by_omega, ?_⟩
      rw [← add_assoc, slotw idx hidx', h1, hev, h2 c₄ hK₄]
      zulcg
      rw [hI4m _ by_omega,
        ite_eq_left by_omega, hI4m _ by_omega]
      omega
    have hti := logIdx_cases hA t_le t_lt t_ge hlsl hlsrec hidx
    obtain ⟨q, hq18, hqV⟩ : ∃ q, q < 18 ∧
        regOf _ _ N₂ ztpam = V := by
      rcases hcase with h | ⟨hi0, h⟩ | h
      · zugmj

        · exact lab i eR2 by_omega by_omega hi h
        · exact lab i eR1 by_omega by_omega hi h
      · zugmj

        · exact lab _ eR1 by_omega by_omega by_omega h
        · exact lab _ eR0 ztp by_omega by_omega h
      · obtain ⟨hV', hW⟩ := gap_pos J h
        have hn2 := cm_n J.right
        zufzs
        · obtain ⟨r, hr, hrV⟩ := gap_reg hP hN by_omega by_omega
            hj₁.1 hj₁.2.1 hj₁.2.2 hV' (Or.inl hW)
          zubxt

          refine ⟨ii, by_omega, ?_⟩
          rw [gap1 ii hii3, List.getD_eq_getElem _ _ hii, hir, hrV]
        · obtain ⟨r, hr, hrV⟩ := gap_reg hP hN by_omega by_omega
            hj₂.1 hj₂.2.1 hj₂.2.2 hV' (Or.inr hW)
          zubxt

          refine ⟨3 + ii, by_omega, ?_⟩
          rw [← add_assoc, gap2 ii hii3, List.getD_eq_getElem _ _ hii, hir, hrV]
    obtain ⟨hfreeR, hexit⟩ := exit_mem_gather hP hN w4 (valid q hq18) (mem_rs q hq18) hzt hσ (by rw [hqV]; omega)
    exact hcomp hfreeR (by rw [w1, w2]; omega)
  · unfold sw at h2 h3 h4
    rw [k8 r h1 zteqn zthk h5]
    exact keep7 r h1 ztce ztce h5
  · omega
  · rw [hm8 a by_omega, w5 a by_omega, em6, s3 a by_omega, em4, g3 a by_omega, m2 a ha]
end
end Lab0
@[expose] public section

/-- **The label candidates of a side-0 query** (piece E). -/
theorem lab0 : Lab0Spec := Lab0.lab0_of S0C.lsearchSpec
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt rayPt_fst)
open Chazelle.Chain (sidePt sideLeft)
@[expose] public section
theorem rayPt_rev (a : Point) (σ τ u : ℝ) : rayPt ztiu (-σ) u = rayPt a σ (τ - u) := by
  refine Prod.ext ?_ rfl
  zujou
variable {C : Chain} {a : Point} {σ τ : ℝ} {Q : Polygon}
/-- Points of the chain or of the boundary of its box are off its domain. -/
theorem not_dom_of_onCB {p : Point} (h : OnCB C p) : p ∉ C.dom := by
  zudqe
  have hb := C.dom_subset_box hd
  rw [Chazelle.Chain.mem_box_iff] at hb
  zude
  · zulwx
  · simp_all
  simp_all

/-- **Genuineness by the reverse ray**: for `a` in the domain and `w = rayPt a σ τ` off it, the
hit is genuine iff the reverse ray from `w` leaves the domain beyond `a`. -/
theorem genuine_iff_rev (hσ : σ = 1 ∨ σ = -1)
    (ha : a ∈ C.dom) (hw : rayPt a σ τ ∉ C.dom) (h0 : 0 < τ) (htop : a.2 ≤ C.top.2)
    (hfree : Merge.FreeAt C ztiu (-σ)) :
    Genuine C a σ τ ↔ τ < C.hitParam ztiu (-σ) := by
  zudpr
  obtain ⟨hT, hTD, hin⟩ := Merge.hit_of_freeAt C (p := rayPt a σ τ) by_simp_all hσ' hfree
  set T := C.hitParam ztiu (-σ) with hTd
  constructor
  · rintro ⟨-, hin', -⟩
    zuks

    zuklo
    · apply hTD
      rw [rayPt_rev]
      simp_all
    · apply hTD
      rw [heq, rayPt_rev, sub_self]
      simpa using ha
  · zufia
    refine ⟨h0, fun s hs1 hs2 => ?_, hw⟩
    have := hin ztold by_linarith by_linarith
    rwa [rayPt_rev, show τ - ztold = s by ring] at this

/-- **Genuineness by abscissas**: the hit `h` of the reverse ray lies beyond `a`. -/
theorem genuine_iff_abs (hσ : σ = 1 ∨ σ = -1)
    (ha : a ∈ C.dom) (hw : rayPt a σ τ ∉ C.dom) (h0 : 0 < τ) (htop : a.2 ≤ C.top.2)
    (hfree : Merge.FreeAt C ztiu (-σ)) :
    (σ = 1 → (Genuine C a σ τ ↔
      (rayPt ztiu (-σ) ztyvd).1 < a.1)) ∧
    (σ = -1 → (Genuine C a σ τ ↔
      a.1 < (rayPt ztiu (-σ) ztyvd).1)) := by
  rw [genuine_iff_rev hσ ha hw h0 htop hfree]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩ <;> subst h1 <;> zvogc <;>
    zufry

/-- **The least candidate of the local hit is the hit**: candidates are positive parameters of
points of the chain or of the box boundary, and the hit is a candidate. -/
theorem lh_min {z : Point} {σ : ℝ} {L : Set ℝ} {τm : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hz : z.2 ≤ C.top.2) (hL : ∀ τ ∈ L, 0 < τ ∧ OnCB C ztdpf)
    (hfree : Merge.FreeAt C z σ) (hmem : C.hitParam z σ ∈ L) (hτm : τm ∈ L)
    (hmin : ∀ τ' ∈ L, τm ≤ τ') : τm = C.hitParam z σ := by
  obtain ⟨-, -, hin⟩ := Merge.hit_of_freeAt C hz hσ hfree
  refine le_antisymm (hmin _ hmem) ?_
  zube

  obtain ⟨hpos, hon⟩ := hL τm hτm
  exact not_dom_of_onCB hon (hin τm hpos hlt)

/-! ## The arrival position -/

/-- **The arrival position of a hit** below the top: its point is the hit, it is of the class of
the local hit (a vertical side of the box, or a point of the chain on a walk edge `≥ 6`), and the
hit is off the domain. -/
theorem arr_facts {N : ℕ} {x : WPos} {w : Point} {σ : ℝ}
    (he : x.edge < (chainModel C).W.n) (hpp : ProperPos ztc Q N x)
    (harr : Arrival (chainModel C).W w σ x.edge ztuy)
    (hy : |w.2| < C.radius) (htop : w.2 ≤ C.top.2) :
    (chainModel C).pos Q x = w ∧ PosClass C Q x ∧
      (ztdiq ∨ ztigw) ∧
      w ∉ C.dom := by
  have hpos : (chainModel C).pos Q x = w := by
    rw [pos_eq_sidePt']; exact harr.2.2.2.1
  have hcl : PosClass C Q x := posClass_of he hpp.1 hpp.2.1 by_simp_all
    ztmbv
  zucn
  have hloc : ztdiq ∨ ztigw := by
    rcases hcl with h | ⟨h6, hlt⟩ | ⟨hend, hz⟩
    · omega
    · refine Or.inr ⟨h6, ?_⟩
      rw [pos_eq_sidePt', hW]
      have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6)
        (t := (chainModel C).param Q x) by_omega ztczk hpp.1 hpp.2.1
      simp_all
    · refine Or.inr zteh
      rw [pos_eq_sidePt', hW, hend, hz]
      exact C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) (t := 0) le_rfl ztdnl
        le_rfl one_pos
  refine ⟨hpos, hcl, hloc, ?_⟩
  zulre
  rcases posClass_pt hcl hpp.1 hpp.2.1 by_simp_all with h | ⟨h, -⟩
  · exact not_dom_of_onCB zteg
  · exact not_dom_of_onCB ztwkb

/-- A positive normalised height code names the height of the point. -/
theorem hgt_of_pos {M : Model} {Q : Polygon} {x : WPos} {h : ℕ} (hx : x.hgt = h + 1)
    (hpar : M.param Q x ≠ 0) : (Q.vtx h).2 = (M.pos Q x).2 := by
  have hne : ztkyu := fun he => hpar (Model.param_horizontal he)
  zulpg
  unfold Model.hgtY
  zucjv

/-- **The vertex fix**: a vertex position gets a positive height code naming its height; the
parameter (`0`) and the point are kept. -/
theorem vtx_fix {M : Model} {Q : Polygon} {e h' : ℕ} (hht : (Q.vtx h').2 = (M.pos Q ztjy).2) :
    M.param Q ztcju = 0 ∧ M.pos Q ztcju = M.pos Q ztjy := by
  have hp0 : M.param Q ztjy = 0 := rfl
  have hwa : M.pos Q ztjy = M.wa e := by
    unfold Model.pos; simp
  have hpar : M.param Q ztcju = 0 :=
    (param_eq_zero_iff M Q ztcju).2 (Or.inr (Or.inr (by
      simp_all)))
  refine ⟨hpar, ?_⟩
  zueew
  simp_all

/-- The two copies `6` and `2m + 6` of the top of a chain have the same point. -/
theorem pos_top_copies (C : Chain) (Q : Polygon) :
    (chainModel C).pos Q zthlx = (chainModel C).pos Q ztbcw := by
  rw [pos_eq_sidePt', pos_eq_sidePt']
  have h0 : (chainModel C).param Q zthlx = 0 := rfl
  have h0' : (chainModel C).param Q ztbcw = 0 := rfl
  zucn
  simp only [h0, h0', Chazelle.Chain.sidePt_zero, hW]
  have e1 := C.sideWalk_vtx_tour C.sideBeta (i := 2 * C.m) le_rfl
  have e2 := C.sideWalk_vtx_tour C.sideBeta (i := 0) by_omega
  rw [show 0 + 6 = 6 by rfl] at e2
  rw [e1, e2, C.sideTour_two_m, C.sideTour_zero]

/-- The height code of a symbolic point (`i` for a vertex, `h` for a point of an edge at the
height of vertex `h`). -/
theorem symHgt {P : Polygon} {c : Config} {o : ℕ} {s : SymPt} (hs : SymPtIn c o s)
    (hl : s.Lt P.n) :
    ztxxj < P.n ∧
      ((Qof P).vtx ztxxj).2 =
        (s.eval zta).2 := by
  cases s with
  | vtx i =>
    zuici
    rw [ite_eq_left h0, h1]
    exact ⟨hl, rfl⟩
  | onEdge e h =>
    obtain ⟨h0, -, h2⟩ := hs
    rw [ite_eq_right by_omega, h2]
    exact ⟨hl.2, rfl⟩

/-! ## Region bounds -/

/-- **Arcs and exit chords of the regions** of a normal form of degree `≤ D`. -/
theorem region_bounds {N : NF} {D : ℕ} (hP : C.P.Simple)
    (hNF : IsNF ztc Q N) (hdeg : (chainModel C).DegLe ztwjh D) :
    ztgsg ∧
      ztibz := by
  zubtj

  have hregs : Restore.NFRegs ztc Q N reg := zteyk
  zuoj
  refine ztkld
  · have := Restore.arcs_le_deg hGM hNF hregs hr
    have := hdeg ztcz ztdhm
    omega
  · have := Restore.chords_le_deg hNF hregs hr
    have := hdeg ztcz ztdhm
    omega
