module

public import Chazelle.Core.RestoreFComplete

/-!
# WP-E, the search: completeness (part 2)

The region faced just after a walk vertex (`faced_after`), and walk offsets inside a piece
(`unwrap_off`, `off_sideInArc`, `closed_offset`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideInArc SideAttach sidePt)
open DownHost ArcT

/-- **The region faced just after a walk vertex.** -/
theorem faced_after {M : Model} (hGM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hF : M.ChordFamily Q F) {p : ℕ} (hp : p < M.W.n) :
    ∃ U ∈ M.regions F, ∀ᶠ ε in 𝓝[>] (0 : ℝ), M.Faces p ε U := by
  have hM := walkAx_of_goodModel hGM
  obtain ⟨t', ⟨ht0, ht1⟩, hfree⟩ := hM.exists_after hF.2.1 hF.1 hp le_rfl one_pos
  simp only [add_zero] at hfree
  set x : ℝ := p + t' / 2 with hx
  have hxc : ¬ M.IsCut F x := fun h => hfree x h ⟨by linarith, by linarith⟩
  have hx0 : 0 < x := by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith
  obtain ⟨U, hU, l, r, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hF hx0 hxc
  refine ⟨U, hU, ?_⟩
  -- the ends of the arc are not in `(p, p + t']`
  have hlr : (l ≤ p ∨ (p : ℝ) + t' < l) ∧ (r ≤ p ∨ (p : ℝ) + t' < r) := by
    obtain ⟨-, -, -, -, hc, -⟩ := harc
    rcases hc with ⟨hl, hr, -⟩ | ⟨-, rfl, rfl⟩
    · constructor
      · by_contra h; push Not at h; exact hfree l hl ⟨h.1, h.2⟩
      · by_contra h; push Not at h; exact hfree r hr ⟨h.1, h.2⟩
    · have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      exact ⟨Or.inl this, Or.inl this⟩
  have hconst : ∀ z : ℝ, (p : ℝ) < z → z ≤ p + t' → sideInArc l r z := by
    intro z hz1 hz2
    have e1 : l < z ↔ l < x := by
      rcases hlr.1 with h | h
      · exact ⟨fun _ => by linarith, fun _ => by linarith⟩
      · exact ⟨fun h' => by linarith, fun h' => by linarith⟩
    have e2 : z < r ↔ x < r := by
      rcases hlr.2 with h | h
      · exact ⟨fun h' => by linarith, fun h' => by linarith⟩
      · exact ⟨fun _ => by linarith, fun _ => by linarith⟩
    unfold sideInArc at hin ⊢
    split_ifs at hin ⊢
    · exact ⟨e1.2 hin.1, e2.2 hin.2⟩
    · rcases hin with h | h
      · exact Or.inl (e1.2 h)
      · exact Or.inr (e2.2 h)
  filter_upwards [Ioo_mem_nhdsGT ht0] with ε hε
  exact harc.2.2.2.2.2.2 p ε hp hε.1 (by linarith [hε.2]) (hconst _ (by linarith [hε.1])
    (by linarith [hε.2]))

/-- **Unwrapped offsets**: from the walk vertex `s`, the key `k` steps and `t` further on. -/
theorem unwrap_off {n s k : ℕ} {t : ℝ} (hs : s < n) (ht0 : 0 ≤ t) (hkn : (k : ℝ) + t < n) :
    unwrapK n s ((((s + k) % n : ℕ) : ℝ) + t) = s + k + t := by
  have hk : k < n := by
    have : (k : ℝ) < n := by linarith
    exact_mod_cast this
  unfold unwrapK
  by_cases h : s + k < n
  · rw [Nat.mod_eq_of_lt h, ite_eq_left (by push_cast; linarith)]; push_cast; ring
  · have e : (s + k) % n = s + k - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e, ite_eq_right (by
      have : ((s + k - n : ℕ) : ℝ) = (s : ℝ) + k - n := by rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; linarith)]
    rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- **A key strictly inside a piece's walk.** -/
theorem off_sideInArc {n s m k : ℕ} {t : ℝ} (hs : s < n) (hmn : m < n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h0 : 0 < (k : ℝ) + t) (hm : (k : ℝ) + t < m) :
    sideInArc (s : ℝ) (((s + m) % n : ℕ) : ℝ) ((((s + k) % n : ℕ) : ℝ) + t) := by
  have hnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hsR : (s : ℝ) < n := by exact_mod_cast hs
  have hs0 : 0 ≤ (s : ℝ) ∧ (s : ℝ) < n := ⟨Nat.cast_nonneg s, hsR⟩
  have he := unwrap_off (k := m) (t := 0) hs le_rfl (by linarith)
  have hy := unwrap_off (k := k) (t := t) hs ht0 (by linarith)
  simp only [add_zero] at he
  have hb : 0 ≤ (((s + m) % n : ℕ) : ℝ) ∧ (((s + m) % n : ℕ) : ℝ) < n :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.mod_lt _ (by omega)⟩
  have hyb : 0 ≤ (((s + k) % n : ℕ) : ℝ) + t ∧ (((s + k) % n : ℕ) : ℝ) + t < n := by
    have h1 : ((s + k) % n : ℕ) + 1 ≤ n := Nat.mod_lt _ (by omega)
    have h1' : (((s + k) % n : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast h1
    exact ⟨by positivity, by linarith⟩
  exact (cyc_unwrap hs0 hs0 hb hyb (by rw [unwrapK_self, he]; linarith)).2
    ⟨by rw [unwrapK_self, hy]; linarith, by rw [hy, he]; linarith⟩

/-- **A walk vertex in the closed key interval of a piece** is `d ≤ m` steps from its start. -/
theorem closed_offset {n s m p : ℕ} (hs : s < n) (hmn : m < n) (hm : 0 < m) (hp : p < n)
    (h : ClosedArc (s : ℝ) (((s + m) % n : ℕ) : ℝ) (p : ℝ)) :
    ∃ d, d ≤ m ∧ (s + d) % n = p := by
  have hsR : (s : ℝ) < n := by exact_mod_cast hs
  have hs0 : 0 ≤ (s : ℝ) ∧ (s : ℝ) < n := ⟨Nat.cast_nonneg s, hsR⟩
  have he := unwrap_off (k := m) (t := 0) hs le_rfl (by simp only [add_zero]; exact_mod_cast hmn)
  simp only [add_zero] at he
  have hb : 0 ≤ (((s + m) % n : ℕ) : ℝ) ∧ (((s + m) % n : ℕ) : ℝ) < n :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.mod_lt _ (by omega)⟩
  have hpb : 0 ≤ (p : ℝ) ∧ (p : ℝ) < n := ⟨Nat.cast_nonneg p, by exact_mod_cast hp⟩
  have hne : (s : ℝ) ≠ (((s + m) % n : ℕ) : ℝ) := by
    intro h'
    have h'' : s = (s + m) % n := by exact_mod_cast h'
    by_cases hw : s + m < n
    · rw [Nat.mod_eq_of_lt hw] at h''; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h''; omega
  obtain ⟨h1, h2⟩ := (closedArc_unwrap hs0 hb hpb hne).1 h
  rw [he] at h2
  -- the unwrapped vertex is `p` or `p + n`
  obtain ⟨Pn, hPn, hPm⟩ : ∃ Pn : ℕ, (Pn : ℝ) = unwrapK n s p ∧ Pn % n = p := by
    unfold unwrapK
    split_ifs
    · exact ⟨p, rfl, Nat.mod_eq_of_lt hp⟩
    · exact ⟨p + n, by push_cast; ring, by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hp]⟩
  rw [← hPn] at h1 h2
  have h1' : s ≤ Pn := by exact_mod_cast h1
  have h2' : Pn ≤ s + m := by exact_mod_cast (by push_cast; linarith : (Pn : ℝ) ≤ ((s + m : ℕ) : ℝ))
  exact ⟨Pn - s, by omega, by rw [show s + (Pn - s) = Pn by omega, hPm]⟩


/-! ## The descent's facts for a stretch of a kind-1 piece -/

variable {E : FEnv} {c₀ : Config}

/-- **The facts of a stretch holding the good vertex.** -/
theorem descGood_mk (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M (Qof E.P) E.N reg) (hch : (E.N.region E.r).chords ≠ [])
    {ai bi aj bj : ℝ} (hAi : E.M.IsArc (E.N.F E.M (Qof E.P)) (reg E.r) ai bi)
    (hAj : E.M.IsArc (E.N.F E.M (Qof E.P)) (reg E.r) aj bj) (hij : ai ≠ aj)
    {PR : ℕ} {Hs : Host} {Cα : Chain} {N : NF} {γ' : ℕ} (hK : K1Hyp E c₀ PR Hs Cα N γ')
    {s : ℕ} (hcnt : ∀ d, d < Cα.m → E.M.counted ((s + d) % E.M.W.n))
    (hsetD : ∀ x ∈ Cα.set, x ∉ E.M.D) (hinB : ∀ C : Chain, E.M = chainModel C → Cα.set ⊆ C.set)
    (hin : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → t < 1 → 0 < (k : ℝ) + t → (k : ℝ) + t < Cα.m →
      sideInArc ai bi ((((s + k) % E.M.W.n : ℕ) : ℝ) + t))
    {d0 g g' L dX : ℕ} (hg : g = (s + d0) % E.M.W.n) (hd0L : d0 + L ≤ Cα.m)
    (hg' : g' + dX < 2 * Cα.m + 7) (hX0 : 0 < dX) (hXL : dX < L)
    {σ T : ℝ} {σb : ℕ} (hσb : σb ≤ 1) (hdσ : dirOf σb = σ) {po : ℕ} {tq : ℝ}
    (hgc : GoodCand E.M (Qof E.P) (E.N.F E.M (Qof E.P)) (reg E.r)
      ⟨(g + dX) % E.M.W.n, 0⟩ σ T)
    (hXA : SideAttach E.M.W (chordOf (E.M.pos (Qof E.P) ⟨(g + dX) % E.M.W.n, 0⟩) σ T)
      ((g + dX) % E.M.W.n) 0)
    (hOA : SideAttach E.M.W (chordOf (E.M.pos (Qof E.P) ⟨(g + dX) % E.M.W.n, 0⟩) σ T) po tq)
    (hne : sidePt E.M.W ((g + dX) % E.M.W.n) 0 ≠ sidePt E.M.W po tq)
    (hXi : ClosedArc ai bi ((((g + dX) % E.M.W.n : ℕ) : ℝ) + 0))
    (hXj : ClosedArc aj bj ((po : ℝ) + tq))
    (hcount : CountOK E.M (E.N.F E.M (Qof E.P)) (reg E.r)
      ((((g + dX) % E.M.W.n : ℕ) : ℝ) + 0) ((po : ℝ) + tq)) :
    ∃ regα Tα, DescGood E c₀ Cα N g g' L reg ai bi aj bj dX regα Tα := by
  have hcan := hK.hcan
  obtain ⟨-, -, -, regα, hRC, hCS, hArcs, hRg, -⟩ := hcan.1
  have hGα : GoodModel (chainModel Cα) :=
    Or.inl ⟨Cα, by rw [hK.hQ]; exact qof_simple hE, rfl⟩
  have hn7 : (chainModel Cα).W.n = 2 * Cα.m + 7 := chainModel_n Cα
  obtain ⟨U, hU, hfU⟩ := faced_after hGα hcan.1.1 (p := g' + dX) (by rwa [hn7])
  obtain ⟨Tα, hTα, hTU⟩ := hRC.2.2 U hU
  have hsn : ∀ d', (g + d') % E.M.W.n = (s + (d0 + d')) % E.M.W.n := fun d' => by
    rw [hg, Nat.mod_add_mod, Nat.add_assoc]
  refine ⟨regα, Tα, ⟨hregs, hch, hAi, hAj, hij, fun d' hd' t ht0 ht1 hpos => ?_,
    fun d' hd' => ?_, hsetD, hinB, hX0, hXL, ⟨σb, hσb, T, by rwa [hdσ]⟩,
    ⟨_, po, tq, hgc.2.2.2.2.2.2.2.1, hXA, hOA, hne, hXi, hXj, hcount⟩,
    ⟨hRC, hCS, hArcs, hRg⟩, ⟨4, Dec.recTree_of hGα hcan.1 hcan.2.1⟩, hTα,
    by rwa [hTU]⟩⟩
  · rw [hsn]
    exact hin _ t ht0 ht1 (by push_cast; linarith [(Nat.cast_nonneg d0 : (0 : ℝ) ≤ d0)])
      (by have : ((d0 + d' : ℕ) : ℝ) + 1 ≤ Cα.m := by exact_mod_cast (by omega)
          push_cast at this ⊢; linarith)
  · rw [hsn]
    exact hE.ehc _ (Nat.mod_lt _ (by have := hK.hs; omega)) (hcnt _ (by omega))

end

end Restore

end Chazelle.Core
