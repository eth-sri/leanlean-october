module

public import Chazelle.Core.FuseAsmSide
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000

/-!
# WP-F fusion assembly, part 22: the query lists of the two sides (driver pieces)

`sideQ₀` writes `endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)` (base in `70150`) and
computes the cap data; `sideQ₁` writes `endQL N₂.chords ++ (t'₁ ++ t'₀ ++ k₁)` (base in
`70151`), using the cap data.
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK SweepPrim MergeAsm

@[expose] public section

/-- The query list of side `0`. -/
def sideQ₀ : Stmt :=
  .seq (endPart 70150 70003) (.seq (vtxPts 70000 2) (.seq (vtxPts 70000 3) (.seq capS capQ₀)))

/-- The query list of side `1`. -/
def sideQ₁ : Stmt := .seq (endPart 70151 70004) (.seq (vtxPts 70001 3) capQ₁)

/-- The registers written by the side stages. -/
def Bside (S r : ℕ) : Bool := Bend S r || Bpt r || Bcs r

/-- The cost bound of `sideQ₀`. -/
def sq0Cost (K : ℕ) : ℕ := 22 * K + 200000

/-- The cost bound of `sideQ₁`. -/
def sq1Cost (K : ℕ) : ℕ := 22 * K + 120000

theorem bend_of {S r : ℕ} (h : Bside S r = false) : Bend S r = false := by
  simp [Bside, Bool.or_eq_false_iff] at h; exact h.1.1

theorem bcs_of {S r : ℕ} (h : Bside S r = false) : Bcs r = false := by
  simp [Bside, Bool.or_eq_false_iff] at h; exact h.2

theorem bpt_of_side {S r : ℕ} (h : Bside S r = false) : Bpt r = false := by
  simp [Bside, Bool.or_eq_false_iff] at h; exact h.1.2

theorem bpt_lo {r : ℕ} (h1 : 70000 ≤ r) (h2 : r < 70120) : Bpt r = false := by
  simp [Bpt, Bprim, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega

theorem bcs_lo {r : ℕ} (h1 : 70000 ≤ r) (h2 : r < 70120) : Bcs r = false := by
  simp [Bcs, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega

theorem bend_lo {S r : ℕ} (h1 : 70000 ≤ r) (h2 : r < 70100) (hS : r ≠ S) : Bend S r = false := by
  simp [Bend, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega

theorem bpt_cap {r : ℕ} (h : r = 70126 ∨ (70140 ≤ r ∧ r < 70144)) : Bpt r = false := by
  simp [Bpt, Bprim, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega

theorem sideQ₀_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {A : ℕ} (hF : FCtx P W J H N₁ N₂ A c)
    (hroom : c.nreg ALLOC + sq0Cost N₁.nChords ≤ W) :
    ∃ c' k v₁ v₀ t₁ t₀ k₀, Exec P W sideQ₀ c c' k ∧ k ≤ sq0Cost N₁.nChords ∧
      3 * (endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)).length ≤ k ∧
      v₁.length ≤ 1 ∧ v₀.length ≤ 1 ∧ t₁.length ≤ 1 ∧ t₀.length ≤ 1 ∧ k₀.length ≤ 1 ∧
      c'.nreg 70150 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)).length ∧
      c'.nreg 70128 = (endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)).length ∧
      ChordListAt c'.nmem (c.nreg ALLOC) (endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bside 70150 r = false → c'.nreg r = c.nreg r) ∧
      (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 70105 = 1 ∧ c'.nreg 70108 = 0 ∧ CapRegs P J c' ∧
      PtAns J (Qof P) 0 (J.whole.vertex J.m₁) 1 v₁ ∧
      PtAns J (Qof P) 0 (J.whole.vertex J.m₁) (-1) v₀ ∧
      PtAns J (Qof P) 0 (J.whole.vertex J.left.topIdx) 1 t₁ ∧
      PtAns J (Qof P) 0 (J.whole.vertex J.left.topIdx) (-1) t₀ ∧
      (SharedExtremum J → ¬ NearU J → PtAns J (Qof P) 0 (capOrigin J) (capDir J) k₀) ∧
      (¬ (SharedExtremum J ∧ ¬ NearU J) → k₀ = []) := by
  have hG := hF.good
  have hHW := hF.hw
  unfold sq0Cost at hroom
  rw [← Nat.add_assoc] at hroom
  have hnW : P.n ≤ W := by ufo hostWords at hHW
  obtain ⟨A₀, hA₀⟩ : ∃ x, c.nreg ALLOC = x := ⟨_, rfl⟩
  -- the chord-end queries
  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', s₁, a₁, n₁, o05, o08, L₁, m₁, r₁, rr₁, rm₁, ou₁⟩ :=
    endPart_exec (P := P) c hw (S := 70150) (G := 70003) (Or.inl rfl) (Or.inl rfl) hF.nf₁ hF.le
      hF.is₁ hnW (by omega)
  have w₁ := e₁.wb_right
  have hF₁ : FCtx P W J H N₁ N₂ A c₁ := hF.keep (fun r h1 h2 => r₁ r (bend_lo h1 (by omega)
      (by omega))) (fun a ha => m₁ a (by have := hF.le; omega)) (by rwo [a₁])
  obtain ⟨sd0, sw0, -, -, sdw, sww⟩ := hF₁.side
  obtain ⟨pre, hpre⟩ : ∃ l, l = endQL N₁.chords := ⟨_, rfl⟩
  have hlenpre : pre.length = 2 * N₁.nChords := by rw [hpre]; exact endQL_length _
  rw [← hpre] at a₁ n₁ L₁ ⊢
  -- the shared vertex
  obtain ⟨c₂, k₂, v₁, v₀, e₂, hk₂, hk₂', hv₁, hv₀, a₂, n₂, L₂, m₂, r₂, rr₂, rm₂, ou₂, pv₁, pv₀⟩ :=
    vtxPts_exec (P := P) c₁ w₁ hG hHW (D := 70000) (off := 2) (by norm_num) (by norm_num) sw0 J 0
      sd0 hF.simple (kk := J.m₁) sd0.2.2.2.1 (by show J.m₁ ≤ J.m₁; exact le_rfl) o05 o08
      (LB := A₀) (pre := pre) (by rw [a₁, hA₀]) n₁ (by rw [← hA₀]; exact L₁)
      (by rw [a₁, show vtxCost = 74000 from rfl]; clear * - hroom hlenpre; omega)
      (by clear * - hroom hlenpre hnW hHW; ufo hostWords at hHW)
  have w₂ := e₂.wb_right
  have hF₂ : FCtx P W J H N₁ N₂ A c₂ := hF₁.keep (fun r h1 h2 => r₂ r (bpt_lo h1 (by omega))) (fun a ha => m₂ a (by have := hF₁.le; omega))
      (by rsio [a₂, a₁, hA₀] only [List.length_append])
  obtain ⟨sd0', sw0', -, -, -, -⟩ := hF₂.side
  -- the top of `C₁`
  obtain ⟨c₃, k₃, t₁, t₀, e₃, hk₃, hk₃', ht₁, ht₀, a₃, n₃, L₃, m₃, r₃, rr₃, rm₃, ou₃, pt₁, pt₀⟩ :=
    vtxPts_exec (P := P) c₂ w₂ hG hHW (D := 70000) (off := 3) (by norm_num) (by norm_num) sw0' J 0
      sd0' hF.simple (kk := J.left.topIdx) sd0'.2.2.2.2.1 J.left.topIdx_le
      (by rw [r₂ _ (by decide), o05]) (by rw [r₂ _ (by decide), o08])
      (LB := A₀) (pre := pre ++ v₁ ++ v₀) a₂ n₂ L₂
      (by rw [a₂, show vtxCost = 74000 from rfl]; simp [List.length_append]
          clear * - hroom hlenpre hv₁ hv₀ hA₀; omega)
      (by simp [List.length_append]; clear * - hroom hlenpre hv₁ hv₀ hHW
          ufo hostWords at hHW)
  have w₃ := e₃.wb_right
  have hF₃ : FCtx P W J H N₁ N₂ A c₃ := hF₂.keep (fun r h1 h2 => r₃ r (bpt_lo h1 (by omega))) (fun a ha => m₃ a (by have := hF₂.le; omega))
      (by rsio [a₃, a₂] only [List.length_append])
  obtain ⟨sd0'', sw0'', -, -, sdw'', sww''⟩ := hF₃.side
  -- the cap data
  obtain ⟨c₄, k₄, e₄, hk₄, R₄, m₄, r₄, rr₄, rm₄, ou₄⟩ := capS_exec (P := P) c₃ w₃ hG hHW J hF.gen
    sww'' sdw'' sd0''
    (by have h5 := sw0''.1; rw [a₃] at h5; simp [List.length_append] at h5
        clear * - h5 hroom hlenpre hv₁ hv₀ ht₁ ht₀ hA₀; omega)
    (by rw [a₃]; simp [List.length_append]
        clear * - hroom hlenpre hv₁ hv₀ ht₁ ht₀ hA₀; omega)
  have w₄ := e₄.wb_right
  have a₄ : c₄.nreg ALLOC = c₃.nreg ALLOC := r₄ _ (by decide)
  have hF₄ : FCtx P W J H N₁ N₂ A c₄ := hF₃.keep (fun r h1 h2 => r₄ r (bcs_lo h1 (by omega))) (fun a _ => by rw [m₄]) (by rw [a₄])
  obtain ⟨sd0₄, sw0₄, -, -, -, -⟩ := hF₄.side
  -- the cap query
  obtain ⟨c₅, k₅, k₀, e₅, hk₅, hk₅', hk₀, a₅, n₅, L₅, m₅, r₅, rr₅, rm₅, ou₅, pk₀, nk₀⟩ :=
    capQ₀_exec (P := P) c₄ w₄ hG hHW J hF.simple hF.gen sw0₄ sd0₄ R₄
      (by rw [r₄ _ (by decide), r₃ _ (by decide), r₂ _ (by decide), o05])
      (by rw [r₄ _ (by decide), r₃ _ (by decide), r₂ _ (by decide), o08])
      (LB := A₀) (pre := pre ++ v₁ ++ v₀ ++ t₁ ++ t₀) (by rw [a₄, a₃])
      (by rw [r₄ _ (by decide), n₃]) (by rw [m₄]; exact L₃)
      (by rw [a₄, a₃, show capBCost = 35100 from rfl]; simp [List.length_append]
          clear * - hroom hlenpre hv₁ hv₀ ht₁ ht₀ hA₀; omega)
      (by simp [List.length_append]; clear * - hroom hlenpre hv₁ hv₀ ht₁ ht₀ hHW
          ufo hostWords at hHW)
  have hL : pre ++ v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀ = pre ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀) := by
    simp [List.append_assoc]
  have ex : Exec P W sideQ₀ c c₅ (k₁ + (k₂ + (k₃ + (k₄ + k₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  have hlen : (pre ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)).length =
      2 * N₁.nChords + v₁.length + v₀.length + t₁.length + t₀.length + k₀.length := by
    sir only [List.length_append, hlenpre]
  refine ⟨c₅, _, v₁, v₀, t₁, t₀, k₀, ex, ?_, ?_, hv₁, hv₀, ht₁, ht₀, hk₀, ?_, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, pv₁, pv₀, pt₁, pt₀,
    pk₀, nk₀⟩
  · unfold sq0Cost; unfold vtxCost at hk₂ hk₃; ufo capBCost at hk₅
  · rwo [hlen]
  · rw [r₅ _ (by decide), r₄ _ (by decide), r₃ _ (by decide), r₂ _ (by decide), s₁]
  · rw [a₅, ← hL, hA₀]
  · rw [n₅, hL]
  · rw [← hL, hA₀]; exact L₅
  · rw [m₅ a (by rsio [a₄, a₃] only [List.length_append]), m₄,
      m₃ a (by rsio [a₂] only [List.length_append]),
      m₂ a (by rwo [a₁]), m₁ a ha]
  · rw [r₅ r (bpt_of_side hr), r₄ r (bcs_of hr), r₃ r (bpt_of_side hr), r₂ r (bpt_of_side hr),
      r₁ r (bend_of hr)]
  · rw [rr₅ r hr, rr₄ r hr, rr₃ r hr, rr₂ r hr, rr₁]
  · rw [rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [ou₅, ou₄, ou₃, ou₂, ou₁]
  · rw [r₅ _ (by decide), r₄ _ (by decide), r₃ _ (by decide), r₂ _ (by decide), o05]
  · rw [r₅ _ (by decide), r₄ _ (by decide), r₃ _ (by decide), r₂ _ (by decide), o08]
  · exact R₄.keep fun r h1 => r₅ r (bpt_cap h1)

theorem sideQ₁_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {A : ℕ} (hF : FCtx P W J H N₁ N₂ A c)
    (hR : CapRegs P J c) (hroom : c.nreg ALLOC + sq1Cost N₂.nChords ≤ W) :
    ∃ c' k t₁ t₀ k₁, Exec P W sideQ₁ c c' k ∧ k ≤ sq1Cost N₂.nChords ∧
      3 * (endQL N₂.chords ++ (t₁ ++ t₀ ++ k₁)).length ≤ k ∧
      t₁.length ≤ 1 ∧ t₀.length ≤ 1 ∧ k₁.length ≤ 1 ∧
      c'.nreg 70151 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (endQL N₂.chords ++ (t₁ ++ t₀ ++ k₁)).length ∧
      c'.nreg 70128 = (endQL N₂.chords ++ (t₁ ++ t₀ ++ k₁)).length ∧
      ChordListAt c'.nmem (c.nreg ALLOC) (endQL N₂.chords ++ (t₁ ++ t₀ ++ k₁)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bside 70151 r = false → c'.nreg r = c.nreg r) ∧
      (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.nreg 70105 = 1 ∧ c'.nreg 70108 = 0 ∧
      PtAns J (Qof P) 1 (J.whole.vertex (J.m₁ + J.right.topIdx)) 1 t₁ ∧
      PtAns J (Qof P) 1 (J.whole.vertex (J.m₁ + J.right.topIdx)) (-1) t₀ ∧
      (SharedExtremum J → NearU J → PtAns J (Qof P) 1 (capOrigin J) (capDir J) k₁) ∧
      (¬ (SharedExtremum J ∧ NearU J) → k₁ = []) := by
  have hG := hF.good
  have hHW := hF.hw
  unfold sq1Cost at hroom
  rw [← Nat.add_assoc] at hroom
  have hnW : P.n ≤ W := by ufo hostWords at hHW
  obtain ⟨A₀, hA₀⟩ : ∃ x, c.nreg ALLOC = x := ⟨_, rfl⟩
  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', s₁, a₁, n₁, o05, o08, L₁, m₁, r₁, rr₁, rm₁, ou₁⟩ :=
    endPart_exec (P := P) c hw (S := 70151) (G := 70004) (Or.inr rfl) (Or.inr rfl) hF.nf₂ hF.le
      hF.is₂ hnW (by omega)
  have w₁ := e₁.wb_right
  have hF₁ : FCtx P W J H N₁ N₂ A c₁ := hF.keep (fun r h1 h2 => r₁ r (bend_lo h1 (by omega)
      (by omega))) (fun a ha => m₁ a (by have := hF.le; omega)) (by rwo [a₁])
  have hR₁ : CapRegs P J c₁ := hR.keep fun r h => r₁ r (by
    simp [Bend, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    omega)
  obtain ⟨-, -, sd1, sw1, -, -⟩ := hF₁.side
  obtain ⟨pre, hpre⟩ : ∃ l, l = endQL N₂.chords := ⟨_, rfl⟩
  have hlenpre : pre.length = 2 * N₂.nChords := by rw [hpre]; exact endQL_length _
  rw [← hpre] at a₁ n₁ L₁ ⊢
  -- the top of `C₂`
  obtain ⟨c₂, k₂, t₁, t₀, e₂, hk₂, hk₂', ht₁, ht₀, a₂, n₂, L₂, m₂, r₂, rr₂, rm₂, ou₂, pt₁, pt₀⟩ :=
    vtxPts_exec (P := P) c₁ w₁ hG hHW (D := 70001) (off := 3) (by norm_num) (by norm_num) sw1 J 1
      sd1 hF.simple (kk := J.right.topIdx) sd1.2.2.2.2.1 J.right.topIdx_le o05 o08
      (LB := A₀) (pre := pre) (by rw [a₁, hA₀]) n₁ (by rw [← hA₀]; exact L₁)
      (by rw [a₁, show vtxCost = 74000 from rfl]; clear * - hroom hlenpre; omega)
      (by clear * - hroom hlenpre hnW hHW; ufo hostWords at hHW)
  have w₂ := e₂.wb_right
  have hF₂ : FCtx P W J H N₁ N₂ A c₂ := hF₁.keep (fun r h1 h2 => r₂ r (bpt_lo h1 (by omega)))
      (fun a ha => m₂ a (by have := hF₁.le; omega))
      (by rsio [a₂, a₁, hA₀] only [List.length_append])
  have hR₂ : CapRegs P J c₂ := hR₁.keep fun r h => r₂ r (bpt_cap h)
  obtain ⟨-, -, sd1', sw1', -, -⟩ := hF₂.side
  -- the cap query
  obtain ⟨c₃, k₃, k₁', e₃, hk₃, hk₃', hk₀, a₃, n₃, L₃, m₃, r₃, rr₃, rm₃, ou₃, pk₁, nk₁⟩ :=
    capQ₁_exec (P := P) c₂ w₂ hG hHW J hF.simple hF.gen sw1' sd1' hR₂
      (by rw [r₂ _ (by decide), o05]) (by rw [r₂ _ (by decide), o08])
      (LB := A₀) (pre := pre ++ t₁ ++ t₀) a₂ n₂ L₂
      (by rw [a₂, show capBCost = 35100 from rfl]; simp [List.length_append]
          clear * - hroom hlenpre ht₁ ht₀ hA₀; omega)
      (by simp [List.length_append]; clear * - hroom hlenpre ht₁ ht₀ hHW
          ufo hostWords at hHW)
  have hL : pre ++ t₁ ++ t₀ ++ k₁' = pre ++ (t₁ ++ t₀ ++ k₁') := by
    simp [List.append_assoc]
  have ex : Exec P W sideQ₁ c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  have hlen : (pre ++ (t₁ ++ t₀ ++ k₁')).length =
      2 * N₂.nChords + t₁.length + t₀.length + k₁'.length := by
    sir only [List.length_append, hlenpre]
  have hv : J.whole.vertex (J.m₁ + J.right.topIdx) = (sideChain J 1).vertex J.right.topIdx :=
    Merge.Junction.whole_vertex_add J _
  refine ⟨c₃, _, t₁, t₀, k₁', ex, ?_, ?_, ht₁, ht₀, hk₀, ?_, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, by rw [hv]; exact pt₁,
    by rw [hv]; exact pt₀, pk₁, nk₁⟩
  · unfold sq1Cost; unfold vtxCost at hk₂; ufo capBCost at hk₃
  · rwo [hlen]
  · rw [r₃ _ (by decide), r₂ _ (by decide), s₁]
  · rw [a₃, ← hL, hA₀]
  · rw [n₃, hL]
  · rw [← hL, hA₀]; exact L₃
  · rw [m₃ a (by rsio [a₂] only [List.length_append]),
      m₂ a (by rwo [a₁]), m₁ a ha]
  · rw [r₃ r (bpt_of_side hr), r₂ r (bpt_of_side hr), r₁ r (bend_of hr)]
  · rw [rr₃ r hr, rr₂ r hr, rr₁]
  · rw [rm₃, rm₂, rm₁]
  · rw [ou₃, ou₂, ou₁]
  · rw [r₃ _ (by decide), r₂ _ (by decide), o05]
  · rw [r₃ _ (by decide), r₂ _ (by decide), o08]

end

end FuseAsm

end Chazelle.Core
