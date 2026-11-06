module

public import Chazelle.Golf

public import Chazelle.Core.OracleFree

/-!
# Lemma 3.6 (WP-H), part 22: the answer of the main phase

`main_answer`: in the main phase of the query (the origin below the top and not on the chord at
its height next to it), the best edge found by the scans of `D*` and of the clusters of the
candidates of the stopping point answers the query: its parameter is the first hit of the chain,
on that edge; no edge means no hit.  The proof applies `OracleQ.query_main` to the ray from the
effective origin (the entry point into the box) up to the stopping point.
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ OracleBook
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)

@[expose] public section

/-- **The context of the main phase**: the structure in memory, as the proof reads it. -/
structure MainCtx (P : Polygon) (C : Chain) (V : QV) (N : NF) (B : BookData) (m : ℕ → ℕ) :
    Prop where
  ch : ChordRecOK P C V m N
  hP : C.P.Simple
  mem : NodeMemOK m V N
  gOK : GraphOK C (Qof P) N B
  μ : B.N = V.μ
  hlab : ∀ u v (w : (bookGraph B).Walk u v), (∀ x ∈ w.support, m (V.FL + x) ≠ 1) →
    m (V.LAB + u) = m (V.LAB + v)
  dl : ∀ i, i < V.nD → m (V.DL + i) < V.μ ∧ m (V.FL + m (V.DL + i)) = 1
  dl_all : ∀ v, v < V.μ → m (V.FL + v) = 1 → ∃ i, i < V.nD ∧ m (V.DL + i) = v

variable {P : Polygon} {C : Chain} {V : QV} {N : NF} {B : BookData} {m : ℕ → ℕ}

theorem nodePts_sub (X : MainCtx P C V N B m) (u : ℕ) : nodePts m V C u ⊆ C.set := by
  rw [nodePts_eq X.ch.hN X.hP X.mem X.ch.hT.hv.m]; exact nodeScan_subset u

theorem dstarPts_sub (X : MainCtx P C V N B m) (k : ℕ) : dstarPts m V C k ⊆ C.set := by
  rintro x ⟨i, -, hx⟩; exact nodePts_sub X _ hx

theorem clusPts_sub (X : MainCtx P C V N B m) (l : ℕ) : clusPts m V C l ⊆ C.set := by
  rintro x ⟨u, -, -, hx⟩; exact nodePts_sub X _ hx

theorem clusPts3_sub (X : MainCtx P C V N B m) (p : ℕ) : clusPts3 m V C p ⊆ C.set := by
  unfold clusPts3
  exact Set.union_subset (Set.union_subset (clusPts_sub X _) (clusPts_sub X _)) (clusPts_sub X _)

/-- **The entry point**: the ray from the origin reaches the effective origin `(ζ, y)` after
`d ≥ 0`, outside the box before. -/
theorem entry_facts {z : Point} (_hs : SemOK P C V z) (hnp : NotPast C V z) :
    0 ≤ sgnOf V.σb * (ζOf C V z - z.1) ∧
    rayPt z (sgnOf V.σb) (sgnOf V.σb * (ζOf C V z - z.1)) = ((ζOf C V z, z.2) : Point) ∧
    (∀ s, 0 < s → s ≤ sgnOf V.σb * (ζOf C V z - z.1) →
      rayPt z (sgnOf V.σb) s ∉ Chain.box C.radius) ∧
    |ζOf C V z| ≤ C.radius := by
  have hR := C.radius_pos
  unfold ζOf
  by_cases hσ : V.σb = 1
  · Ξ ite_eq_left hσ, sgnOf_one hσ
    have hzR := hnp.1 hσ
    refine ⟨by simp only [one_mul]; linarith [le_max_left z.1 (-C.radius)], ?_, ?_, ?_⟩
    · rw [rayPt_right]; ext <;> simp
    · intro s hs0 hsd hb
      have := (abs_lt.1 hb.1)
      ϴ' rayPt_right at this
      ϴ' one_mul at hsd
      rcases le_total z.1 (-C.radius) with h' | h'
      · Ξ' max_eq_right h' at hsd; linarith [this.1]
      · Ξ' max_eq_left h' at hsd; linarith
    · rw [abs_le]; constructor
      · exact le_max_right _ _
      · exact max_le hzR.le (⟡)
  · Ξ ite_eq_right hσ, sgnOf_ne hσ
    have hzR := hnp.2 hσ
    refine ⟨by linarith [min_le_left z.1 C.radius], ?_, ?_, ?_⟩
    · Ξ show (-1 : ℝ) * (min z.1 C.radius - z.1) = z.1 - min z.1 C.radius by ring, rayPt_left
      ext <;> simp
    · intro s hs0 hsd hb
      have := (abs_lt.1 hb.1)
      ϴ' rayPt_left at this
      rcases le_total z.1 C.radius with h' | h'
      · Ξ' min_eq_left h' at hsd; linarith
      · Ξ' min_eq_right h' at hsd; linarith [this.2]
    · rw [abs_le]; constructor
      · exact le_min hzR.le (⟡)
      · exact min_le_right _ _

/-- **The answer of the main phase.** -/
theorem main_answer (X : MainCtx P C V N B m) {z : Point} (hs : SemOK P C V z)
    (hab : ¬ ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2) {t : ℕ} (hpart : PartC P C V m t)
    (hnd : ¬ (FoundC V m t ∧ DegC P C V m t)) {bD : Option ℕ}
    (hD : Sweep.FirstHitOpt (dstarPts m V C V.nD) z (sgnOf V.σb)
      (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z bD))
    (hbD : ∀ cb, bD = some cb → cb < V.m) {pk : ℕ → ℕ}
    (hloc : ∀ k, k < 4 → pk k < V.A ∧
      LocFacts P (chainModel C) N V.hz (posK (mainPos P C V m t bD) k) (pk k))
    {best : Option ℕ}
    (hbest : Sweep.FirstHitOpt (dstarPts m V C V.nD ∪ clusPts3 m V C (pk 0) ∪
        clusPts3 m V C (pk 1) ∪ clusPts3 m V C (pk 2) ∪ clusPts3 m V C (pk 3))
      z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z best)) :
    (∀ ci, best = some ci → FirstHit C.set z (sgnOf V.σb) (vOf (Qof P) V.s V.hz (sgnOf V.σb) z ci)) ∧
      (best = none → NoHit C.set z (sgnOf V.σb)) := by
  have hT := X.ch.hT
  have hv := hT.hv
  have hN := X.ch.hN
  have hR := C.radius_pos
  have hσ := hs.σ
  set σ := sgnOf V.σb with hσdef
  set y := ((Qof P).vtx V.hz).2 with hydef
  set S := dstarPts m V C V.nD ∪ clusPts3 m V C (pk 0) ∪ clusPts3 m V C (pk 1) ∪
    clusPts3 m V C (pk 2) ∪ clusPts3 m V C (pk 3) with hSdef
  have hSC : S ⊆ C.set := by
    Ξ hSdef
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (dstarPts_sub X _) (clusPts3_sub X _)) (clusPts3_sub X _)) (clusPts3_sub X _))
      (clusPts3_sub X _)
  have hSB : S ⊆ Chain.box C.radius := hSC.trans C.set_subset_box
  have hDB : dstarPts m V C V.nD ⊆ Chain.box C.radius := (dstarPts_sub X _).trans C.set_subset_box
  -- an origin past the box
  by_cases hnp : NotPast C V z
  swap
  · have hpast : C.radius ≤ σ * z.1 := by
      unfold NotPast at hnp
      Ξ hσdef
      by_cases h1 : V.σb = 1
      · Ξ sgnOf_one h1, one_mul
        by_contra hc; push Not at hc; exact hnp ⟨fun _ => hc, fun h' => absurd h1 h'⟩
      · Ξ sgnOf_ne h1
        by_contra hc; push Not at hc
        exact hnp ⟨fun h' => absurd h' h1, fun _ => ⟡⟩
    have hnh := noHit_past (C.set_subset_box) hσ hpast (z := z)
    have hbn : best = none := by
      cases best with
      | none => rfl
      | some ci =>
        exfalso
        have := (show FirstHit S z σ _ from hbest)
        exact noHit_past hSB hσ hpast _ this.1 this.2.1
    exact ⟨fun ci h => by rw [hbn] at h; exact absurd h (✓), fun _ => hnh⟩
  -- the effective origin
  obtain ⟨hd0, hzd, hout, hζ⟩ := entry_facts hs hnp
  set d := σ * (ζOf C V z - z.1) with hddef
  set ζ := ζOf C V z with hζdef
  set z' : Point := (ζ, y) with hz'def
  have hz'e : rayPt z σ d = z' := Ρ hzd, hs.zy
  -- the stopping point
  obtain ⟨Xp, hSel⟩ := sel_facts X.ch hs X.hP hpart hnd hD hbD
  set T := σ * (Xp.1 - ζ) with hTdef
  have hT0 : 0 < T := hSel.ahead hnp
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hXpt : rayPt z' σ T = Xp := by
    ϴ rayPt, hz'def, hTdef
    ext
    · simp only; rw [← mul_assoc, hσ2, one_mul]; ring
    · simp only; Ξ hSel.y
  have hyR := vtx_snd_lt_radius hv.CQ hv.hz_lt
  have hyt : z'.2 ≤ C.top.2 := by
    rw [hz'def]; simp only; rw [← hT.top]; exact not_lt.1 hab
  -- the shifted scans
  have hD' := firstHitOpt_shift hDB hd0 hout hD
  have hbest' := firstHitOpt_shift hSB hd0 hout hbest
  Ξ' hz'e at hD' hbest'
  obtain ⟨reg, hRc, hAc, -⟩ := NFLoc.isNF_arcs hN
  have hArc := X.mem.A
  -- the query
  have hQ := query_main (Q := Qof P) (B := B) X.hP (by rw [hv.CQ]; exact hs.hD) hN hRc hAc X.gOK
    (fun i => m (V.FL + i) = 1) (fun i => m (V.LAB + i)) (fun u v w hw => X.hlab u v w hw)
    (z := z') hyt hσ hT0
    (fun s hs0 hsT => by
      refine rayPt_mem_box C (by rw [hz'def]; exact hζ) (by rw [hz'def]; exact hyR) hσ hs0 ?_
      rw [hz'def]; simp only
      have := hSel.le
      have : σ * Xp.1 ≤ C.radius := by
        rcases hσ with h | h <;> rw [h] <;> [linarith [le_abs_self Xp.1]; linarith [neg_abs_le Xp.1]]
      linarith)
    (fun s hs0 hsT => by
      have hpt : rayPt z' σ s = ((ζ + σ * s, y) : Point) := by
        ϴ rayPt, hz'def
      Ξ hpt
      refine chord_free X.ch hs hnp hpart ?_ ?_
      · Ξ ← hσdef, ← hζdef
        have : σ * (ζ + σ * s - ζ) = s := Ρ show ζ + σ * s - ζ = σ * s by ring, ← mul_assoc, hσ2, one_mul
        linarith
      · intro hf
        have hn := hSel.near hf
        Ξ' ← hσdef at hn ⊢
        have : σ * (ζ + σ * s) = σ * ζ + s := Ρ mul_add, ← mul_assoc, hσ2, one_mul
        nlinarith)
    (fun i hi s hs0 hsT hmem => by
      -- `D*` is not hit before the stopping point
      have hiμ : i.1 < V.μ := by rw [← X.μ]; exact i.2
      obtain ⟨k, hk, hki⟩ := X.dl_all i.1 hiμ hi
      have hin : rayPt z' σ s ∈ dstarPts m V C V.nD := by
        refine ⟨k, hk, ?_⟩
        rw [hki, nodePts_eq hN X.hP X.mem hv.m]; exact hmem
      refine avoid_of_firstHitOpt hD' (T := T) ?_ s hs0 hsT hin
      intro v hv'
      cases bD with
      | none => exact absurd hv' (⊚ bestVal)
      | some cD =>
        ϴ' bestVal, Option.map_some, Option.some.injEq at hv'
        Ξ ← hv'
        have hdh := hSel.dhit cD rfl
        have hpos : 0 < vOf (Qof P) V.s V.hz σ z cD := (show FirstHit _ _ _ _ from hD).1
        Ξ vOf_of_spans (spans_of_vOf_pos hpos), show (Qof P).n = P.n from shear_n _ _
        Ξ hTdef, hddef
        linarith)
    (by
      Ξ hXpt
      rcases hSel.on with h | h
      · exact fun hd => hd.2 (Or.inl h)
      · exact fun hd => by have := hd.1.1; Ξ' h at this; exact lt_irrefl _ this)
    (fun v => ∃ k, k < 4 ∧ (v.1 = pk k ∨ v.1 = succP V.A (pk k) ∨ v.1 = predP V.A (pk k)))
    (fun v hv hmem => by
      Ξ' hXpt at hmem
      Ξ hArc
      exact cand_of_stop hN X.hP hSel.stop (fun k hk => by rw [← hArc]; exact hloc k hk) hv hmem)
    (fun i => m (V.FL + i) = 1 ∨ ∃ c : Fin B.N, (∃ k, k < 4 ∧ (c.1 = pk k ∨
      c.1 = succP V.A (pk k) ∨ c.1 = predP V.A (pk k))) ∧ m (V.LAB + i) = m (V.LAB + c))
    (fun i h => h)
    (S := S)
    (fun i hi => by
      have hiμ : i.1 < V.μ := by rw [← X.μ]; exact i.2
      Ξ ← nodePts_eq hN X.hP X.mem hv.m
      intro x hx
      rcases hi with hd | ⟨c, ⟨k, hk, hc⟩, hl⟩
      · obtain ⟨j, hj, hji⟩ := X.dl_all i.1 hiμ hd
        exact Or.inl (Or.inl (Or.inl (Or.inl ⟨j, hj, by rw [hji]; exact hx⟩)))
      · have hcl : x ∈ clusPts m V C (lab m V c) := ⟨i.1, hiμ, hl, hx⟩
        have h3 : x ∈ clusPts3 m V C (pk k) := by
          unfold clusPts3
          rcases hc with e | e | e <;> Ξ' e at hcl
          · exact Or.inl (Or.inl hcl)
          · exact Or.inl (Or.inr hcl)
          · exact Or.inr hcl
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inl (Or.inl (Or.inr h3)))
        · exact Or.inl (Or.inl (Or.inr h3))
        · exact Or.inl (Or.inr h3)
        · exact Or.inr h3)
    hSC hbest'
  obtain ⟨q1, q2⟩ := hQ
  refine ⟨fun ci hci => ?_, fun hbn => ?_⟩
  · subst hci
    have := q1 _ rfl
    have h' := firstHit_unshift (C.set_subset_box) hd0 hout (by rw [hz'e]; exact this)
    simpa using h'
  · subst hbn
    exact noHit_unshift (C.set_subset_box) hd0 hout (by rw [hz'e]; exact q2 rfl)

end

end OracleR

end Chazelle.Core
