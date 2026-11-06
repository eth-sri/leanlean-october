module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoS0CandAux

/-!
# The sweep RAM (WP-D), answers: the side-0 stop and table candidates of a query (mathematics)

For a query point `z` of `C₁` (not the shared vertex, not above the top of `C₂`) with its
arrival position `x = (zP, zPh)` in the walk of `C`:

* `query_h6`: a height code `0` of `x` is on a tour edge (`callOff` accepts `x`);
* `log_sorted`, `log_mono`: the log keys increase strictly in offset (the predicate of the binary
  search is downward closed);
* `search_eq`: the result of the binary search is a log record with the position `x`, if any;
* `bits_eq`: two positions with equal offsets are equal;
* `stop_match`, `tab_match`: a stop record or a regular table entry at `x` gives a log record
  with the position `x` whose slot is flagged, and a candidate origin for `z`;
* `slot_eq`: the origin in the slot is that candidate origin.
-/

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

theorem dS_eq (s : ℕ) : dS s = 1 ∨ dS s = -1 := by core_grind

theorem dS_inj {s s' : ℕ} (hs : s ≤ 1) (hs' : s' ≤ 1) (h : dS s = dS s') : s = s' := by
  core_grind

theorem dS_sOf (b : ℕ) : dS (sOf b) = dirOf b := by
  unfold dS sOf dirOf; split_ifs <;> simp_all

theorem sOf_le (b : ℕ) : sOf b ≤ 1 := by core_grind

theorem dS_mod (j : ℕ) : dS (j % 2) = endDir j := by
  core_grind

section
variable (d : ℕ)
include d
/-- The slot of the query direction code `d`: the candidates point in direction `-dirOf d`. -/
def qS : ℕ := if d = 1 then 1 else 0

theorem dS_qS : dS (qS d) = -dirOf d := by
  unfold dS qS dirOf; split_ifs <;> simp_all

theorem qS_le : qS d ≤ 1 := by core_grind

/-! ## The query position -/


end

/-- **A query position with height code `0` is on a tour edge.** -/
theorem query_h6 {z : Point} {σ : ℝ} (hz : z ∈ J.left.set) {e h : ℕ}
    (harr : Arrival (chainModel J.whole).W z σ e ((chainModel J.whole).param (Qof P) ⟨e, h⟩))
    (h0 : h = 0) : 6 ≤ e := by
  subst h0
  by_contra h6
  have hbox := J.left.set_subset_box hz
  have hpt := harr.2.2.2.1
  have hp0 : (chainModel J.whole).param (Qof P) ⟨e, 0⟩ = 0 := rfl
  rw [hp0] at hpt
  have hW : (chainModel J.whole).W = J.whole.sideWalk J.whole.sideBeta := rfl
  rw [hW] at hpt
  obtain ⟨b0, b1, b2, b3, b4, b5, -⟩ := J.whole.sidePt_box J.whole.sideBeta 0
  have hR : J.left.radius = J.whole.radius := rfl
  have hRp := J.whole.radius_pos
  obtain ⟨hx, hy⟩ := hbox
  rw [hR] at hx hy
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5) with he | he | he | he | he | he <;>
    subst he
  · ram_grind
  · ram_grind
  · ram_grind
  all_goals grind

/-! ## The log in memory -/

section
variable (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
include hA
/-- `AEnv` gives the base of the offsets at `sw 40`. -/
theorem aenv_gW : c₀.nreg (sw 40) = gW J := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -⟩ := hA.hst
  grind [cstR, gW]

/-- **The log keys increase strictly in offset.** -/
theorem log_sorted {i j : ℕ} (hij : i < j)
    (hj : j < rd c₀ bSweep 301) :
    off (chainModel J.whole).W.n (c₀.nreg (sw 40))
        ((chainModel J.whole).key (Qof P) (logPos c₀.nmem (rd c₀ bSweep 300) i)) <
      off (chainModel J.whole).W.n (c₀.nreg (sw 40))
        ((chainModel J.whole).key (Qof P) (logPos c₀.nmem (rd c₀ bSweep 300) j)) := by
  obtain ⟨rs, ls, -, -, -, -, hlsl, hls, hL, -, -, -⟩ := hA.hout
  have hi : i < ls.length := by omega
  have hj' : j < ls.length := by omega
  have hsort := hL.2.2.2.1
  have hlen : (logOf J (Qof P) N₂ ls).length = ls.length := by unfold logOf; simp
  have hp := List.pairwise_iff_getElem.1 hsort i j (by omega) (by omega) hij
  rw [← List.getD_eq_getElem _ (0, 0, ∅), ← List.getD_eq_getElem _ (0, 0, ∅)] at hp
  obtain ⟨a1, a2⟩ := logOf_getD J (Qof P) N₂ hi
  obtain ⟨b1, b2⟩ := logOf_getD J (Qof P) N₂ hj'
  rw [a1, a2, b1, b2] at hp
  obtain ⟨m1, m2, -⟩ := hls i hi
  obtain ⟨n1, n2, -⟩ := hls j hj'
  rw [aenv_gW hA]
  unfold logPos Model.key
  simp only
  rw [m1, m2, n1, n2]
  exact hp

/-- The PosW facts of the log records. -/
theorem log_posW {i : ℕ} (hi : i < rd c₀ bSweep 301) :
    SweepEv.PosW P J (c₀.nmem (rd c₀ bSweep 300 + 7 * i))
      (c₀.nmem (rd c₀ bSweep 300 + 7 * i + 1)) := by
  obtain ⟨rs, ls, -, -, -, -, hlsl, hls, -, hlsW, -, -⟩ := hA.hout
  have hi' : i < ls.length := by omega
  obtain ⟨m1, m2, -⟩ := hls i hi'
  rw [m1, m2]
  exact (hlsW _ (by rw [List.getD_eq_getElem _ _ hi']; ram_grind)).1

/-! ## The binary search -/

/-- **The result of the search is the log record at the target**, if there is one. -/
theorem search_eq {x : WPos} {t i : ℕ}
    (ht1 : ∀ j, j < t → lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) x j)
    (ht2 : ∀ j, t ≤ j → j < rd c₀ bSweep 301 →
      ¬ lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) x j)
    (hi : i < rd c₀ bSweep 301)
    (hkey : (chainModel J.whole).key (Qof P) (logPos c₀.nmem (rd c₀ bSweep 300) i) =
      (chainModel J.whole).key (Qof P) x) : t = i := by
  have hnot : ¬ lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) x i := by
    unfold lsPr; rw [show (⟨c₀.nmem (rd c₀ bSweep 300 + 7 * i), c₀.nmem (rd c₀ bSweep 300 + 7 * i + 1)⟩ :
      WPos) = logPos c₀.nmem (rd c₀ bSweep 300) i from rfl, hkey]; simp_all
  have h1 : t ≤ i := by
    ram_grind
  by_contra hne
  have hlt : t < i := by omega
  apply ht2 t le_rfl (by omega)
  unfold lsPr
  rw [← hkey]
  exact log_sorted hA hlt hi

/-- The predicate of the search is downward closed. -/
theorem log_mono (x : WPos) {i j : ℕ} (hij : i ≤ j)
    (hj : j < rd c₀ bSweep 301)
    (h : lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) x j) :
    lsPr P J c₀.nmem (rd c₀ bSweep 300) (c₀.nreg (sw 40)) x i := by
  rcases hij.lt_or_eq with hlt | rfl
  · exact lt_trans (log_sorted hA hlt hj) h
  · exact h

/-- **Equal offsets give equal positions** (proper positions of the walk of `C`). -/
theorem bits_eq {x y : WPos}
    (hx : x.edge < (chainModel J.whole).W.n) (hy : y.edge < (chainModel J.whole).W.n)
    (hpx : ProperPos (chainModel J.whole) (Qof P) P.n x)
    (hpy : ProperPos (chainModel J.whole) (Qof P) P.n y)
    (h1 : ¬ off (chainModel J.whole).W.n (c₀.nreg (sw 40)) ((chainModel J.whole).key (Qof P) x) <
      off (chainModel J.whole).W.n (c₀.nreg (sw 40)) ((chainModel J.whole).key (Qof P) y))
    (h2 : ¬ off (chainModel J.whole).W.n (c₀.nreg (sw 40)) ((chainModel J.whole).key (Qof P) y) <
      off (chainModel J.whole).W.n (c₀.nreg (sw 40)) ((chainModel J.whole).key (Qof P) x)) :
    x.edge = y.edge ∧ (chainModel J.whole).param (Qof P) x =
      (chainModel J.whole).param (Qof P) y := by
  have heq := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
  rw [aenv_gW hA] at heq
  have kx0 : 0 ≤ (chainModel J.whole).key (Qof P) x := by
    unfold Model.key; ram_grind
  have ky0 : 0 ≤ (chainModel J.whole).key (Qof P) y := by
    unfold Model.key; ram_grind
  have kxn : (chainModel J.whole).key (Qof P) x < (chainModel J.whole).W.n := by
    unfold Model.key; have := hpx.2.1
    have : (x.edge : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hx
    linarith
  have kyn : (chainModel J.whole).key (Qof P) y < (chainModel J.whole).W.n := by
    unfold Model.key; have := hpy.2.1
    have : (y.edge : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hy
    linarith
  have hk := off_inj (by positivity) (gW_lt J) kx0 kxn ky0 kyn heq
  unfold Model.key at hk
  exact key_split hpx.1 hpx.2.1 hpy.1 hpy.2.1 hk

/-! ## Matches -/


end

/-- **The origin in a flagged slot** at a log record with the point `z` is the candidate origin
of `z` in the direction of the slot. -/
theorem slot_eq (hP : J.P.Simple) {m : ℕ → ℕ} {B AL i s : ℕ} {z o : Point}
    (hslot : SlotOK P J m B AL i s) (hf : m (slotA B i s) = 1) (hpt : logPt P J m AL i = z)
    (hz : z ∈ J.left.set) (hzs : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2)
    (ho : CandAt J o (dS s) z) :
    (chainModel J.right).pos (Qof P) ⟨m (slotA B i s + 1), m (slotA B i s + 2)⟩ = o := by
  obtain ⟨-, -, hc⟩ := hslot.2 hf
  rw [hpt] at hc
  exact cand_unique (dS_eq s) hc ho (z_mem_right_dom hP hz hzs hz2) (z_not_mem_whole_dom hz)

section
variable (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hX : AuxCore P J N₂ c₀) {z : Point} {σ : ℝ} {zp zh : ℕ} (harr : Arrival (chainModel J.whole).W z σ zp ((chainModel J.whole).param (Qof P) ⟨zp, zh⟩))
include hA hX σ harr
/-- **A stop record at the query position** is attached at a log record with that position,
whose slot (of its direction) is flagged, and its origin is a candidate origin of `z`. -/
theorem stop_match
    {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (hrsl : rs.length = rd c₀ bSweep 201)
    (hrs : StopRecsAt c₀.nmem (rd c₀ bSweep 200) rs) {r : ℕ × ℕ × ℕ × ℕ × ℕ} (hr : r ∈ rs)
    (hr1 : r.1 = zp)
    (hr2 : (chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩ =
      (chainModel J.whole).param (Qof P) ⟨zp, zh⟩) :
    ∃ i, i < rd c₀ bSweep 301 ∧
      logPos c₀.nmem (rd c₀ bSweep 300) i = ⟨zp, (logPos c₀.nmem (rd c₀ bSweep 300) i).hgt⟩ ∧
      (chainModel J.whole).param (Qof P) (logPos c₀.nmem (rd c₀ bSweep 300) i) =
        (chainModel J.whole).param (Qof P) ⟨zp, zh⟩ ∧
      c₀.nmem (slotA (c₀.nreg sB) i (sOf r.2.2.2.2)) = 1 ∧
      CandAt J (stopOrig J (Qof P) N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2) (dirOf r.2.2.2.2) z := by
  obtain ⟨rs₀, ls₀, hl0, hrs0, hS, hW0, -⟩ := hA.hout
  have heq : rs = rs₀ := stopRecs_unique hrs hrs0 (by omega)
  subst heq
  obtain ⟨x, hx, hxr⟩ := List.getElem_of_mem hr
  have hfx := hrs x hx
  rw [List.getD_eq_getElem _ _ hx, hxr] at hfx
  obtain ⟨f1, f2, -, -, f5⟩ := hfx
  obtain ⟨-, -, -, -, -, hst, -⟩ := hX
  obtain ⟨i, hi, e1, e2, e3⟩ := hst x (by omega)
  rw [f1, f2] at e2
  rw [f1, hr1] at e1
  rw [f5] at e3
  obtain ⟨-, hk, -, hk1⟩ := hW0 r hr
  obtain ⟨hc, -⟩ := stop_cand J hA.hNF₂ hS hr hk hk1
  refine ⟨i, hi, ?_, e2.trans hr2, e3, ?_⟩
  · grind [logPos]
  ram_grind

/-- **A regular table entry at the query position** is attached at a log record with that
position, whose slot (of its direction) is flagged; its origin is a candidate origin of `z`. -/
theorem tab_match
    {j : ℕ} (hj : j < 2 * N₂.nChords)
    (hT : tabOf J (Qof P) c₀.nmem (rd c₀ bSweep 302) j =
      some (zp, (chainModel J.whole).param (Qof P) ⟨zp, zh⟩))
    (hv : ValidO J (Qof P) N₂ j) :
    ∃ i, i < rd c₀ bSweep 301 ∧
      logPos c₀.nmem (rd c₀ bSweep 300) i = ⟨zp, (logPos c₀.nmem (rd c₀ bSweep 300) i).hgt⟩ ∧
      (chainModel J.whole).param (Qof P) (logPos c₀.nmem (rd c₀ bSweep 300) i) =
        (chainModel J.whole).param (Qof P) ⟨zp, zh⟩ ∧
      c₀.nmem (slotA (c₀.nreg sB) i (j % 2)) = 1 ∧
      CandAt J (endOrigin J (Qof P) N₂ j) (endDir j) z := by
  obtain ⟨rs₀, ls₀, -, -, -, -, -, -, -, -, hTab, -⟩ := hA.hout
  have hflag : c₀.nmem (rd c₀ bSweep 302 + 3 * j) = 1 := by
    simp_all [tabOf] 
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
  · grind [logPos]
  ram_grind


end

end

end S0C

end SweepIo

end Chazelle.Core
