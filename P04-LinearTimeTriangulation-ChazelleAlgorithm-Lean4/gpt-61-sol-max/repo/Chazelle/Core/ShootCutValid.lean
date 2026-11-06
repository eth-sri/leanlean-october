module

public import Chazelle.Core.ShootCutWalk
public import Chazelle.Core.ShootCutGrade

/-!
# WP-G, part 12: valid pieces

A piece handed from the core of the arc-cutter to its `emit` statement (`Pc`): two walk
positions, a kind, and for kind `1` the grade-table entry of its chain of `Q`, the first edge of
that chain, the direction in which the walk traverses it and its length `2^g`.

* `PcOK`: the validity the core guarantees; for kind `1`, the walk from the piece start visits
  the vertices of the chain upward or downward;
* `kind1_facts`: from `PcOK` and the grade table, the facts `CutterOK` asks of a kind-1 piece
  (chain descriptor, normal form, granularity, point set, weight, `PieceWalk`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideE sideInArc)

namespace ShootCut

/-- A piece. -/
structure Pc where
  /-- The start. -/
  s : WPos
  /-- The end. -/
  e : WPos
  /-- The kind (`0` at most one counted edge, `1` a grade chain). -/
  kind : ℕ
  /-- The grade-table entry (kind `1`). -/
  entry : ℕ
  /-- The first edge of the chain of `Q` (kind `1`). -/
  x0 : ℕ
  /-- The direction (`1` upward). -/
  dir : ℕ
  /-- The number of edges `2^g` (kind `1`). -/
  pw : ℕ

/-- The walk of a kind-1 piece visits the chain `[x₀, x₀ + w]` of `Q` upward or downward. -/
def BlockWalk (W Q : Polygon) (p x0 w dir : ℕ) : Prop :=
  ∀ d, d ≤ w → W.vtx (p + d) = Q.vtx (if dir = 1 then x0 + d else x0 + w - d)

/-- **A valid piece** of the chain model of `C`, for the grade table at `h` in the memory `m`
and the weight bound `γ`. -/
def PcOK (P : Polygon) (C : Chain) (m : ℕ → ℕ) (h γ : ℕ) (pc : Pc) : Prop :=
  ProperPos (chainModel C) (Qof P) P.n pc.s ∧ ProperPos (chainModel C) (Qof P) P.n pc.e ∧
    pc.s.edge < 2 * C.m + 7 ∧ pc.e.edge < 2 * C.m + 7 ∧ (pc.kind = 0 ∨ pc.kind = 1) ∧
    (pc.kind = 0 → (chainModel C).arcWt ((chainModel C).key (Qof P) pc.s)
      ((chainModel C).key (Qof P) pc.e) ≤ 1) ∧
    (pc.kind = 1 → ∃ g b, 1 ≤ g ∧ g < m h ∧ b < gradeCount P.n g ∧
      pc.entry = entryAddr m h g b ∧ pc.pw = 2 ^ g ∧ pc.x0 = b * 2 ^ g ∧
      b * 2 ^ g + 2 ^ g < P.n ∧ gradeGran g ≤ cutGran γ ∧
      pc.s.hgt = 0 ∧ pc.e.hgt = 0 ∧ 6 ≤ pc.s.edge ∧ pc.e.edge = pc.s.edge + 2 ^ g ∧
      pc.e.edge ≤ 2 * C.m + 6 ∧ (pc.dir = 1 ∨ pc.dir = 0) ∧
      BlockWalk (chainModel C).W (Qof P) pc.s.edge (b * 2 ^ g) (2 ^ g) pc.dir)

theorem gradeLen_full {n g b : ℕ} (h : b * 2 ^ g + 2 ^ g < n) : gradeLen n g b = 2 ^ g := by
  unfold gradeLen; omega

/-- **The facts of a kind-1 piece** (`CutterOK`), read from the grade table in any memory `m'`
where it holds. -/
theorem kind1_facts {O : OracleIface} {P : Polygon} {C : Chain} {m m' : ℕ → ℕ} {h γ A : ℕ}
    {pc : Pc} (hok : PcOK P C m h γ pc) (hk : pc.kind = 1)
    (hR : Robust A m fun m'' => GradeRaw O P m'' h A) (hm' : ∀ a, a < A → m' a = m a)
    {A' : ℕ} (hA' : A ≤ A') :
    ChainWF P A' m' (m' pc.entry) ∧
      ∃ Hs Cα N, ChainDescAt m' (m' pc.entry) (Qof P) Hs Cα ∧
        NFWithin m' (m' (pc.entry + 1)) A' N ∧
        (∃ γ', γ' ≤ cutGran γ ∧ IsCanonicalNF (chainModel Cα) (Qof P) N γ' 4) ∧
        (chainModel C).arcSet ((chainModel C).key (Qof P) pc.s)
          ((chainModel C).key (Qof P) pc.e) = Cα.set ∧
        (chainModel C).arcWt ((chainModel C).key (Qof P) pc.s)
          ((chainModel C).key (Qof P) pc.e) = Cα.m ∧
        PieceWalk (chainModel C) Cα pc.s pc.e ∧ Cα.P = Qof P ∧
        ((∀ d, d ≤ Cα.m → (chainModel C).W.vtx ((pc.s.edge + d) % (chainModel C).W.n) =
            Cα.vertex d) ∨
          (∀ d, d ≤ Cα.m → (chainModel C).W.vtx ((pc.s.edge + d) % (chainModel C).W.n) =
            Cα.vertex (Cα.m - d))) := by
  obtain ⟨hs, he, hsn, hen, -, -, h1⟩ := hok
  obtain ⟨g, b, hg1, hgΛ, hb, hE, hpw, hx0, hbn, hgran, hs0, he0, h6, hee, hem, hdir, hW⟩ := h1 hk
  have hR' : Robust A m' fun m'' => GradeRaw O P m'' h A := hR.transport hm'
  have hΛ : g < m' h := by
    have := (grade_low hR).1
    grind
  obtain ⟨Hs, Cα, N, hC, hwf, hP, -, -, hsC, hmC, hN, hcan, -⟩ := hR'.holds.2.2.2 g b hΛ hb
  have hPQ : Cα.P = Qof P := hP
  have hent : m' (m' (h + 2) + g) + 3 * b = pc.entry := by
    obtain ⟨h2, hr, -⟩ := grade_entry hR hgΛ hb
    have e1 : m' (h + 2) = m (h + 2) := hm' _ h2
    have e2 : m' (m (h + 2) + g) = m (m (h + 2) + g) := hm' _ hr
    rw [e1, e2, hE]; rfl
  rw [hent] at hC hwf hN
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hlen : Cα.m = 2 ^ g := by rw [hmC]; exact gradeLen_full hbn
  have hsα : Cα.s = b * 2 ^ g := by rw [hsC]; rfl
  have hx : Cα.s + Cα.m < (Qof P).n := by omega
  -- the walk agrees with the tour of `Cα`
  have hV : ∀ d, d ≤ Cα.m → (chainModel C).W.vtx (pc.s.edge + d) =
      WalkEmbed.tourV Cα (if pc.dir = 1 then 0 else Cα.m) d := by
    intro d hd
    rw [hW d (by omega)]
    split_ifs with hd1
    · rw [tourV_up Cα hd, grade_vertex hP hx hd, hsα]
    · rw [tourV_down Cα hd, grade_vertex hP hx (by omega), hsα, hlen]
      grind
  have hn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  have hsP : pc.s = ⟨pc.s.edge, 0⟩ := by rw [← hs0]
  have heP : pc.e = ⟨pc.s.edge + Cα.m, 0⟩ := by rw [hlen, ← hee, ← he0]
  refine ⟨hwf.mono hA', Hs, Cα, N, hC, hN.mono hA', ⟨gradeGran g, hgran, hcan⟩, ?_, ?_, ?_⟩
  · rw [hsP, heP, key_hgt0, key_hgt0]
    refine arcSet_tour (J := if pc.dir = 1 then 0 else Cα.m) (by grind) (by omega)
      hV
  · rw [hsP, heP, key_hgt0, key_hgt0]
    exact arcWt_chain_nat C (by grind) h6 (by omega)
  · rw [hsP, heP]
    have hmod : (pc.s.edge + Cα.m) % (chainModel C).W.n = pc.s.edge + Cα.m :=
      Nat.mod_eq_of_lt (by omega)
    have := pieceWalk_tour (M := chainModel C) (Cα := Cα) (p₀ := pc.s.edge)
      (J := if pc.dir = 1 then 0 else Cα.m) (by omega) (fun d hd => by
        rw [Nat.mod_eq_of_lt (by omega)]; grind)
    rw [hmod] at this
    refine ⟨this, hPQ, ?_⟩
    dsimp only
    rcases hdir with hd1 | hd0
    · left
      intro d hd
      rw [Nat.mod_eq_of_lt (by omega), hV d hd, ite_eq_left hd1, tourV_up Cα hd]
    · right
      intro d hd
      rw [Nat.mod_eq_of_lt (by omega), hV d hd, ite_eq_right (by omega), tourV_down Cα hd]

end ShootCut

end

end Chazelle.Core
