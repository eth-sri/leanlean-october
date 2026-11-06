module

public import Chazelle.Core.SweepIoCand0L
public import Chazelle.Core.SweepIoBruteShot
public import Chazelle.Core.SweepIoS0CandBsSpec
public import Chazelle.Core.SweepIoS0CandQMath
public import Chazelle.Core.SweepIoLHit5

/-!
# The sweep RAM (WP-D), answers: the label candidates of a side-0 query, the mathematics

* `gap_reg`: a region faced just after or just before a walk vertex `p` (parameter `0`) is one of
  the three regions `nbrRegs N j` at an answer `j` of double identification for the key `p`;
* `gap_pos`: the gap labels (`GapLab`) are faced just after the walk vertex `2 m₂ + 6` or just
  before the walk vertex `6` of the walk of `C₂` (the two copies of the top at the slit);
* `logIdx_cases`: the log entry of the key of a position is the result `t` of the binary search
  (number of log keys before it) or `t - 1`;
* `exit_mem_gather`: a ray starting in a listed region exits on the gathered arcs.
-/

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

/-! ## Regions faced at a walk vertex -/

/-- Keys just before a key inside an open cyclic interval are inside it. -/
theorem sideInArc_eventually_sub {a b x : ℝ} (h : sideInArc a b x) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideInArc a b (x - s) := by
  unfold sideInArc at h ⊢
  split_ifs at h ⊢ with hab
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < x - a by linarith [h.1])]
      with s hs hs'
    have : (0 : ℝ) < s := hs
    exact ⟨by linarith [hs'.2], by linarith [h.2]⟩
  · rcases h with h | h
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x - a by linarith)] with s hs
      left; linarith [hs.2]
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have : (0 : ℝ) < s := hs
      right; linarith

/-- An interval of `𝓝[>] 0`. -/
theorem exists_Ioo_of_eventually {p : ℝ → Prop} (h : ∀ᶠ s in 𝓝[>] (0 : ℝ), p s) :
    ∃ u > (0 : ℝ), ∀ s, 0 < s → s < u → p s := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun s h0 h1 => hsub ⟨h0, h1⟩⟩

/-- **The regions faced at a walk vertex** `p` (parameter `0`) are among the three regions of an
answer of double identification for its key. -/
theorem gap_reg {C : Chain} (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel C) Q N) {p : ℕ} (hp : p < (chainModel C).W.n) (hp1 : 1 ≤ p)
    {j : ℕ} (hj : j < N.arcs.length)
    (hloc1 : ¬ (chainModel C).IsCut (N.F (chainModel C) Q) (p : ℝ) →
      N.F (chainModel C) Q = ∅ ∨
        sideInArc (sk (chainModel C) Q N j) (ek (chainModel C) Q N j) (p : ℝ))
    (hloc2 : (chainModel C).IsCut (N.F (chainModel C) Q) (p : ℝ) →
      sk (chainModel C) Q N j = (p : ℝ) ∨ ek (chainModel C) Q N j = (p : ℝ))
    {V : Set Point} (hV : V ∈ (chainModel C).regions (N.F (chainModel C) Q))
    (hW : AfterFaces (chainModel C) p 0 V ∨ BeforeFaces (chainModel C) p 0 V) :
    ∃ r ∈ nbrRegs N j, regOf (chainModel C) Q N r = V := by
  set M := chainModel C
  set F := N.F M Q with hFdef
  have hGM : GoodModel M := Or.inl ⟨C, hP, rfl⟩
  have hM : WalkAx M := walkAx_of_goodModel hGM
  have hFam : M.ChordFamily Q F := hN.1
  have hF : F ⊆ M.Adm := hFam.2.1
  have hfin : F.Finite := hFam.1
  obtain ⟨hRC, -, hArcs, -⟩ := regOf_spec hN
  have hp' : ((p : ℝ) + 0) = p := add_zero _
  by_cases hcut : M.IsCut F (p : ℝ)
  · obtain ⟨c, hc, -⟩ := id hcut
    have hne : F.Nonempty := ⟨c, hc⟩
    obtain ⟨hfa, hfb⟩ := faced_arcs hM hF hfin hp (le_refl (0 : ℝ)) zero_lt_one (fun _ => hp1)
      (by rwa [hp']) hV
    obtain ⟨r, hr, rfl⟩ := regOf_surj hN hV
    refine ⟨r, ?_, rfl⟩
    rcases hW with hW | hW
    · obtain ⟨b, harc⟩ := hfa hW
      rw [hp'] at harc
      exact region_of_arc_at hN hGM hne hj (hloc2 hcut) hr harc (Or.inl rfl)
    · obtain ⟨a, harc⟩ := hfb hW
      rw [hp'] at harc
      exact region_of_arc_at hN hGM hne hj (hloc2 hcut) hr harc (Or.inr rfl)
  · have hjA : sj N j < N.arcs.length := NFLoc.seq_lt hN hj
    obtain ⟨hr0, harc0⟩ := hArcs.1 (sj N j) hjA
    have hin : sideInArc (sk M Q N j) (ek M Q N j) (p : ℝ) := by
      rcases hloc1 hcut with hF0 | hin
      · rcases harc0.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, ha, hb⟩
        · rw [← hFdef, hF0] at hc; exact absurd hc (Set.notMem_empty c)
        · have hk0 : (0 : ℝ) < p := by exact_mod_cast hp1
          show sideInArc (M.key Q (N.arc (sj N j)).s) (M.key Q (N.arc (sj N j)).e) (p : ℝ)
          rw [ha, hb]
          unfold sideInArc; rw [ite_eq_right (lt_irrefl _)]; exact Or.inl hk0
      · exact hin
    set U₀ := regOf M Q N (N.arc (sj N j)).reg with hU₀
    have hU₀m : U₀ ∈ M.regions F := hRC.1 _ hr0
    have hmem : (N.arc (sj N j)).reg ∈ nbrRegs N j := by simp [nbrRegs]
    refine ⟨_, hmem, ?_⟩
    rw [← hU₀]
    rcases hW with hW | hW
    · obtain ⟨u, hu, hsub⟩ := exists_Ioo_of_eventually (sideInArc_eventually_add hin)
      have hA0 : AfterFaces M p 0 U₀ := by
        refine ⟨u, hu, fun s hs0 hsu hs1 => ?_⟩
        refine harc0.2.2.2.2.2.2 p (0 + s) hp (by linarith) hs1 ?_
        have := hsub s hs0 hsu
        rw [zero_add]; exact this
      exact after_unique zero_lt_one hU₀m hV hA0 hW
    · obtain ⟨u, hu, hsub⟩ := exists_Ioo_of_eventually (sideInArc_eventually_sub hin)
      have hB0 : BeforeFaces M p 0 U₀ := by
        refine ⟨min u 1, lt_min hu one_pos, fun h => absurd h (lt_irrefl _), fun _ s hs0 hsu => ?_⟩
        have hsu' : s < u := lt_of_lt_of_le hsu (min_le_left _ _)
        have hs1 : s < 1 := lt_of_lt_of_le hsu (min_le_right _ _)
        have hpm : (p + M.W.n - 1) % M.W.n = p - 1 := by
          rw [show p + M.W.n - 1 = (p - 1) + M.W.n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
        rw [hpm]
        refine harc0.2.2.2.2.2.2 (p - 1) (1 - s) (by omega) (by linarith) (by linarith) ?_
        have e : ((p - 1 : ℕ) : ℝ) + (1 - s) = (p : ℝ) - s := by
          rw [Nat.cast_sub hp1]; push_cast; ring
        rw [e]; exact hsub s hs0 hsu'
      exact before_unique (le_refl _) hU₀m hV hB0 hW

/-! ## The gap labels -/

/-- **The gap labels** are faced just after the walk vertex `2 m₂ + 6` or just before the walk
vertex `6` of the walk of `C₂`. -/
theorem gap_pos (J : Merge.Junction) {S₂ : Set (Set Point)} {V : Set Point}
    (h : GapLab J S₂ V) :
    V ∈ (chainModel J.right).regions S₂ ∧
      (AfterFaces (chainModel J.right) (2 * J.right.m + 6) 0 V ∨
        BeforeFaces (chainModel J.right) 6 0 V) := by
  obtain ⟨hδ, hV, hW⟩ := h
  refine ⟨hV, ?_⟩
  have hn : (chainModel J.right).W.n = 2 * J.right.m + 7 := cm_n J.right
  have ht := tpos_lt J.right 0
  have hm2 : J.right.m = J.m₂ := rfl
  have key : rL1 J = 2 * J.right.m - tpos J.right 0 ∧ rδ J = 7 := by
    unfold rδ at hδ
    unfold rL1 rδ
    split_ifs at hδ ⊢ with h1 h2 <;> first | omega
  obtain ⟨k1, k2⟩ := key
  have e1 : (6 + tpos J.right 0 + rL1 J) % (chainModel J.right).W.n = 2 * J.right.m + 6 := by
    rw [hn, k1, Nat.mod_eq_of_lt (by omega)]; omega
  have e2 : (6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n = 6 := by
    rw [hn, k1, k2, show 6 + tpos J.right 0 + (2 * J.right.m - tpos J.right 0) + 7 =
      6 + (2 * J.right.m + 7) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rwa [e1, e2] at hW

/-! ## The log entry of the query key -/

section Log

variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ : Config}

/-- The key of a log entry is the key of its record in memory. -/
theorem logKey_eq {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} {m : ℕ → ℕ} {AL : ℕ}
    (hls : LogRecsAt m AL ls) {i : ℕ} (hi : i < ls.length) :
    logKey J (Qof P) N₂ ls i = (chainModel J.whole).key (Qof P) (S0C.logPos m AL i) := by
  obtain ⟨a1, a2⟩ := S0C.logOf_getD J (Qof P) N₂ hi
  obtain ⟨m1, m2, -⟩ := hls i hi
  unfold logKey Model.key S0C.logPos
  rw [a1, a2, m1, m2]

/-- **The log entry of the key of `x`** is the result `t` of the binary search or `t - 1`. -/
theorem logIdx_cases (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {x : WPos} {t i : ℕ}
    (ht0 : t ≤ rd c₀ bSweep 301)
    (ht1 : ∀ j, j < t → S0C.lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) x j)
    (ht2 : ∀ j, t ≤ j → j < rd c₀ bSweep 301 →
      ¬ S0C.lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) x j)
    {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} (hlsl : ls.length = rd c₀ bSweep 301)
    (hls : LogRecsAt c₀.nmem (rd c₀ bSweep 300) ls)
    (hi : LogIdx J (Qof P) N₂ ls ((chainModel J.whole).key (Qof P) x) i) : i = t ∨ i + 1 = t := by
  obtain ⟨hil, hle, hlt⟩ := hi
  have hg := S0C.aenv_gW hA
  have hoW : ∀ y, oW J y = off (chainModel J.whole).W.n (c₀.nreg (sw 40)) y := fun y => by
    unfold oW; rw [hg]
  by_contra hne
  rcases (show i + 1 < t ∨ t < i by omega) with h | h
  · have h1 := ht1 (i + 1) h
    have h2 := hlt (by omega)
    unfold S0C.lsPr at h1
    rw [logKey_eq hls (by omega), hoW, hoW] at h2
    exact absurd (lt_trans h1 h2) (lt_irrefl _)
  · apply ht2 t le_rfl (by omega)
    unfold S0C.lsPr
    have h3 := S0C.log_sorted hA h (by omega)
    rw [logKey_eq hls hil, hoW, hoW] at hle
    exact lt_of_lt_of_le h3 hle

end Log

/-! ## The exit point on the gathered arcs -/

/-- **A ray starting in a listed region exits on the gathered arcs**, and its direction is free. -/
theorem exit_mem_gather {P : Polygon} {C : Chain} (hP : C.P.Simple) {N : NF}
    (hN : IsNF (chainModel C) (Qof P) N) {rs : List ℕ} {m : ℕ → ℕ} {A : ℕ}
    (harcs : ∀ k, k < (regArcs N rs).length →
      ShotList.arcAt m A k = nArc (chainModel C) (Qof P) N ((regArcs N rs).getD k 0))
    {r : ℕ} (hr : r < N.nRegions) (hrs : r ∈ rs) {z : Point} (hzt : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hray : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ regOf (chainModel C) (Qof P) N r) :
    FreeAt C z σ ∧ rayPt z σ (C.hitParam z σ) ∈
      ShotList.loSet (chainModel C) (Qof P) m A (regArcs N rs).length [] := by
  set M := chainModel C
  set F := N.F M (Qof P)
  have hFam : M.ChordFamily (Qof P) F := hN.1
  obtain ⟨hRC, -, hArcs, -⟩ := regOf_spec hN
  have hU : regOf M (Qof P) N r ∈ M.regions F := hRC.1 r hr
  have hfree : FreeAt C z σ :=
    hray.mono fun t ht => (Chazelle.Chain.regionsIn_subset (show regOf M (Qof P) N r ∈
      Chazelle.Chain.regionsIn C.dom F from hU) ht).1
  refine ⟨hfree, ?_⟩
  set K := (regArcs N rs).length
  set L := (List.range K).map (fun i => (M.key (Qof P) (ShotList.arcAt m A i).1,
    M.key (Qof P) (ShotList.arcAt m A i).2))
  have hL : ∀ a b, M.IsArc F (regOf M (Qof P) N r) a b → (a, b) ∈ L := by
    intro a b harc
    obtain ⟨i₀, hi₀, hir, his, hie⟩ := hArcs.2.2.1 r hr a b harc
    have hmem : i₀ ∈ (N.region r).arcs := (hArcs.2.2.2 r hr i₀).2 ⟨hi₀, hir⟩
    have hmem' : i₀ ∈ regArcs N rs := List.mem_flatMap.2 ⟨r, hrs, hmem⟩
    obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1 hmem'
    refine List.mem_map.2 ⟨k, List.mem_range.2 hk, ?_⟩
    have hg : (regArcs N rs).getD k 0 = i₀ := by rw [List.getD_eq_getElem _ _ hk, hki]
    rw [harcs k hk, hg]
    obtain ⟨⟨hps, -, -⟩, ⟨hpe, -, -⟩⟩ := arc_end_facts hP hN hi₀
    unfold nArc
    simp only
    rw [(Restore.normOf_facts hps).2.2.2.1, (Restore.normOf_facts hpe).2.2.2.1, his, hie]
  have hFh := firstHit_arcs C hP hFam hU hzt hσ hray L hL
  have hw := hFh.2.1
  simp only [mem_iUnion] at hw
  obtain ⟨ab, hab, hwab⟩ := hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hab
  obtain ⟨p', t', hp', ht0', ht1', hk', hpt'⟩ := (ShotList.arcSet_iff M _ _ _).1 hwab
  exact ⟨p', t', hp', ht0', ht1', ⟨i, List.mem_range.1 hi, hk'⟩,
    fun g hg => absurd hg List.not_mem_nil, hpt'⟩

end

end Lab0

end SweepIo

end Chazelle.Core
