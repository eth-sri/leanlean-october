module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseOracleCuM
public import Chazelle.Core.ShootCutKey
public import Chazelle.Core.ShootCutGen

/-!
# WP-M (E7-B, part 14): the pieces of the chain cutter along a stretch

The chain cutter answers a chain arc `[sa, ea]` with pieces whose ends go through increasing keys
from `sa` to `ea` (`chain_mono`, from the tiling conjunct of `CutterOK`).  Translated along the
stretch (`trPc`), the pieces form a path of unwrapped keys of the interior walk (`KPath`,
`slot_kpath`), from `e₁ + off - g₀ + key sa` to `e₁ + off - g₀ + key ea` when the stretch starts at
the interior vertex `u₀ = (e₁ + off) mod n`.

* `kpath_of_idx`: a path of unwrapped keys from facts indexed by the pieces.
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)
open ShootCut (Pc KPath)

/-! ## Paths of unwrapped keys from indexed facts -/

/-- **A path of unwrapped keys** from facts indexed by the pieces. -/
theorem kpath_of_idx {M : Model} {Q : Polygon} {n : ℝ} :
    ∀ (ps : List Pc) (Vs Ve : ℕ → ℝ), ps ≠ [] →
      (∀ i (hi : i < ps.length), (∃ k : ℤ, Vs i = M.key Q (ps[i]'hi).s + k * n) ∧
        (∃ k : ℤ, Ve i = M.key Q (ps[i]'hi).e + k * n) ∧ Vs i < Ve i) →
      (∀ i, i + 1 < ps.length → Vs (i + 1) = Ve i) →
      KPath M Q n (Vs 0) ps (Ve (ps.length - 1))
  | [], _, _, hne, _, _ => absurd rfl hne
  | [pc], Vs, Ve, _, h, _ => by
    obtain ⟨h1, h2, h3⟩ := h 0 (✓)
    exact ⟨h1, Ve 0, h3, h2, rfl⟩
  | pc :: q :: qs, Vs, Ve, _, h, hc => by
    obtain ⟨h1, h2, h3⟩ := h 0 (✓)
    refine ⟨h1, Ve 0, h3, h2, ?_⟩
    have ih := kpath_of_idx (q :: qs) (fun i => Vs (i + 1)) (fun i => Ve (i + 1))
      (List.cons_ne_nil q qs) (fun i hi => h (i + 1) (by simp at hi ⊢; omega))
      (fun i hi => hc (i + 1) (by simp at hi ⊢; omega))
    rw [hc 0 (✓)] at ih
    simpa using ih

/-! ## The chain pieces go through increasing keys -/

/-- **The keys of the chain pieces increase** from the start of the arc to its end. -/
theorem chain_mono {K : WPos → ℝ} {ps : List Pc} {sa ea : WPos} (hne : ps ≠ [])
    (hlt : K sa < K ea) (h0 : K (ps[0]'(List.length_pos_iff.2 hne)).s = K sa)
    (hl : K (ps[ps.length - 1]'(by have := List.length_pos_iff.2 hne; omega)).e = K ea)
    (hc : ∀ i (hi : i + 1 < ps.length), K (ps[i]'(⋄)).e = K (ps[i + 1]'hi).s)
    (ht : ∀ i (hi : i + 1 < ps.length), sideInArc (K (ps[i]'(⋄)).s) (K ea)
      (K (ps[i]'(⋄)).e)) :
    ∀ i (hi : i < ps.length), K sa ≤ K (ps[i]'hi).s ∧ K (ps[i]'hi).s < K (ps[i]'hi).e ∧
      K (ps[i]'hi).e ≤ K ea := by
  have hlen := List.length_pos_iff.2 hne
  -- the starts lie in `[K sa, K ea)`
  have hs : ∀ i (hi : i < ps.length), K sa ≤ K (ps[i]'hi).s ∧ K (ps[i]'hi).s < K ea := by
    intro i
    induction i with
    | zero => intro hi; rw [h0]; exact ⟨le_rfl, hlt⟩
    | succ i ih =>
      intro hi
      obtain ⟨a1, a2⟩ := ih (⋄)
      have hti := ht i hi
      unfold sideInArc at hti
      rw [ite_eq_left a2] at hti
      Ξ ← hc i hi
      exact ⟨by linarith [hti.1], hti.2⟩
  intro i hi
  obtain ⟨a1, a2⟩ := hs i hi
  by_cases hlast : i + 1 < ps.length
  · have hti := ht i hlast
    unfold sideInArc at hti
    rw [ite_eq_left a2] at hti
    exact ⟨a1, hti.1, hti.2.le⟩
  · have : i = ps.length - 1 := ⋄
    subst this
    Ξ hl
    exact ⟨a1, a2, le_rfl⟩

/-! ## Pieces in memory -/

/-- **The piece `i` of the list at `L`** in the memory `m` (the descriptor and normal-form
handles in the fields `entry` and `x0`). -/
def rdPc (m : ℕ → ℕ) (L i : ℕ) : Pc :=
  ⟨⟨m (L + 1 + 7 * i), m (L + 1 + 7 * i + 1)⟩, ⟨m (L + 1 + 7 * i + 2), m (L + 1 + 7 * i + 3)⟩,
    m (L + 1 + 7 * i + 4), m (L + 1 + 7 * i + 5), m (L + 1 + 7 * i + 6), 0, 0⟩

/-- **The translation of a piece** along a stretch. -/
def trPc (n u₀ g₀ : ℕ) (pc : Pc) : Pc :=
  { pc with s := trP n u₀ g₀ pc.s, e := trP n u₀ g₀ pc.e }

/-- **The facts `CutterOK` asks of one piece** in the model `M` (memory `m`, bound `E`,
granularity bound `Hγ`). -/
def PcV (P : Polygon) (M : Model) (m : ℕ → ℕ) (E Hγ : ℕ) (pc : Pc) : Prop :=
  ProperPos M (Qof P) P.n pc.s ∧ ProperPos M (Qof P) P.n pc.e ∧ pc.s.edge < M.W.n ∧
    pc.e.edge < M.W.n ∧ pc.kind ≤ 1 ∧
    (pc.kind = 0 → M.arcWt (M.key (Qof P) pc.s) (M.key (Qof P) pc.e) ≤ 1) ∧
    (pc.kind = 1 → ChainWF P E m pc.entry ∧ ∃ Hs Cα N, ChainDescAt m pc.entry (Qof P) Hs Cα ∧
      NFWithin m pc.x0 E N ∧ (∃ γ', γ' ≤ Hγ ∧ IsCanonicalNF (chainModel Cα) (Qof P) N γ' 4) ∧
      M.arcSet (M.key (Qof P) pc.s) (M.key (Qof P) pc.e) = Cα.set ∧
      M.arcWt (M.key (Qof P) pc.s) (M.key (Qof P) pc.e) = Cα.m ∧
      PieceWalk M Cα pc.s pc.e ∧ Cα.P = Qof P ∧
      ((∀ d, d ≤ Cα.m → M.W.vtx ((pc.s.edge + d) % M.W.n) = Cα.vertex d) ∨
        (∀ d, d ≤ Cα.m → M.W.vtx ((pc.s.edge + d) % M.W.n) = Cα.vertex (Cα.m - d))))

/-- **A chain descriptor determines the chain.** -/
theorem chainDesc_uniq {m : ℕ → ℕ} {B : ℕ} {Q : Polygon} {H : Host} {C C' : Chain}
    (h : ChainDescAt m B Q H C) (h' : ChainDescAt m B Q H C') : C = C' := by
  obtain ⟨-, h2, h3, h4, -⟩ := h
  obtain ⟨-, h2', h3', h4', -⟩ := h'
  obtain ⟨P, s, m, a, b⟩ := C
  obtain ⟨P', s', m', a', b'⟩ := C'
  simp only at h2 h2' h3 h3' h4 h4'
  subst h2 h2'
  have e1 : s = s' := h3.symm.trans h3'
  have e2 : m = m' := h4.symm.trans h4'
  subst e1 e2
  rfl

/-- **The facts of a piece survive** memory changes at or above their bound. -/
theorem PcV.keep {P : Polygon} {M : Model} {m m' : ℕ → ℕ} {E E' Hγ : ℕ} {pc : Pc}
    (h : PcV P M m E Hγ pc) (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    PcV P M m' E' Hγ pc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun hk => ?_⟩
  obtain ⟨hwf, Hs, Cα, N, hCD, hNF, hrest⟩ := h7 hk
  obtain ⟨hlen, hHwf, hEb, hs⟩ := hwf.2 Hs Cα hCD
  have hb5 := hwf.1
  have hCD' : ChainDescAt m' pc.entry (Qof P) Hs Cα :=
    ShotList.chainDescAt_copy hCD hEb he (fun j hj => he _ (⋄))
  refine ⟨?_, Hs, Cα, N, hCD', (hNF.transport he).mono hE, hrest⟩
  refine ⟨⋄, fun H' C' hC' => ?_⟩
  have hb : m' pc.entry = m pc.entry := he _ (⋄)
  have hH : H' = Hs := NFLoc.hostAt_unique hC'.1 hCD'.1
  subst hH
  have hC : C' = Cα := chainDesc_uniq hC' hCD'
  subst hC
  exact ⟨hlen, hHwf, by rw [hb]; omega, hs⟩

/-- **A chain piece inside the stretch, translated, is a piece of the interior walk.** -/
theorem pcV_tr {P : Polygon} {C : Chain} {u₀ g₀ ℓ : ℕ} (S : Stretch (Qof P) C u₀ g₀ ℓ)
    {m : ℕ → ℕ} {E Hγ : ℕ} {pc : Pc} (hv : PcV P (chainModel C) m E Hγ pc)
    (hs0 : (g₀ : ℝ) ≤ (chainModel C).key (Qof P) pc.s)
    (he1 : (chainModel C).key (Qof P) pc.e ≤ g₀ + ℓ)
    (hse : (chainModel C).key (Qof P) pc.s < (chainModel C).key (Qof P) pc.e) :
    PcV P (interiorModel (Qof P)) m E Hγ (trPc (Qof P).n u₀ g₀ pc) := by
  have hQ : (Qof P).n = P.n := qn'
  obtain ⟨sP, eP, sE, eE, hk, h0, h1⟩ := hv
  have sP' : ProperPos (chainModel C) (Qof P) (Qof P).n pc.s := by rw [hQ]; exact sP
  have eP' : ProperPos (chainModel C) (Qof P) (Qof P).n pc.e := by rw [hQ]; exact eP
  have hs1 : (chainModel C).key (Qof P) pc.s ≤ g₀ + ℓ := hse.le.trans he1
  have he0 : (g₀ : ℝ) ≤ (chainModel C).key (Qof P) pc.e := hs0.trans hse.le
  obtain ⟨-, sPI, sEI, -⟩ := trP_spec S sP' hs0 hs1
  obtain ⟨-, ePI, eEI, -⟩ := trP_spec S eP' he0 he1
  obtain ⟨hset, hwt⟩ := trP_arc S sP' eP' hs0 he1 hse
  have hmi : (interiorModel (Qof P)).W.n = (Qof P).n := mi_n
  refine ⟨by rw [← hQ]; exact sPI, by rw [← hQ]; exact ePI, by rw [hmi]; exact sEI,
    by rw [hmi]; exact eEI, hk, fun hk0 => ?_, fun hk1 => ?_⟩
  · show (interiorModel (Qof P)).arcWt _ _ ≤ 1
    rw [show (trPc (Qof P).n u₀ g₀ pc).s = trP (Qof P).n u₀ g₀ pc.s from rfl,
      show (trPc (Qof P).n u₀ g₀ pc).e = trP (Qof P).n u₀ g₀ pc.e from rfl, hwt]
    exact h0 hk0
  · obtain ⟨hwf, Hs, Cα, N, hCD, hNF, hcan, hcs, hcw, hpw, hCαP, hvl⟩ := h1 hk1
    obtain ⟨hpw', hvl'⟩ := trP_pieceWalk S hpw hcw hse hs0 he1 hvl
    refine ⟨hwf, Hs, Cα, N, hCD, hNF, hcan, ?_, ?_, hpw', hCαP, hvl'⟩
    · show (interiorModel (Qof P)).arcSet _ _ = _
      rw [show (trPc (Qof P).n u₀ g₀ pc).s = trP (Qof P).n u₀ g₀ pc.s from rfl,
        show (trPc (Qof P).n u₀ g₀ pc).e = trP (Qof P).n u₀ g₀ pc.e from rfl, hset, hcs]
    · show (interiorModel (Qof P)).arcWt _ _ = _
      rw [show (trPc (Qof P).n u₀ g₀ pc).s = trP (Qof P).n u₀ g₀ pc.s from rfl,
        show (trPc (Qof P).n u₀ g₀ pc).e = trP (Qof P).n u₀ g₀ pc.e from rfl, hwt, hcw]

/-- **The unwrapped interior key** of a translated position. -/
theorem trP_cong {Q : Polygon} {C : Chain} {u₀ g₀ ℓ : ℕ} (S : Stretch Q C u₀ g₀ ℓ) {e₁ off : ℕ}
    (hu₀ : u₀ = (e₁ + off) % Q.n) {x : WPos} (hx : ProperPos (chainModel C) Q Q.n x)
    (hk0 : (g₀ : ℝ) ≤ (chainModel C).key Q x) (hk1 : (chainModel C).key Q x ≤ g₀ + ℓ) :
    ∃ k : ℤ, (e₁ : ℝ) + off - g₀ + (chainModel C).key Q x =
      (interiorModel Q).key Q (trP Q.n u₀ g₀ x) + k * Q.n := by
  obtain ⟨hg1, -, -⟩ := str_edge S hx hk0 hk1
  Ξ trP_key S hx hk0 hk1, key_eq, hu₀, Nat.mod_add_mod
  set a := e₁ + off + (x.edge - g₀) with ha
  refine ⟨((a / Q.n : ℕ) : ℤ), ?_⟩
  have e1 := Nat.mod_add_div a Q.n
  have e2 : ((a % Q.n : ℕ) : ℝ) + Q.n * ((a / Q.n : ℕ) : ℝ) = a := by exact_mod_cast e1
  have e3 : (a : ℝ) = e₁ + off + x.edge - g₀ := by
    rw [ha]; push_cast [Nat.cast_sub hg1]; ring
  ϴ Int.cast_natCast
  linarith

/-- A default piece. -/
def pc0 : Pc := ⟨⟨0, 0⟩, ⟨0, 0⟩, 0, 0, 0, 0, 0⟩

/-- **The translated pieces of one chain arc** form a path of unwrapped interior keys. -/
theorem slot_kpath {Q : Polygon} {C : Chain} {u₀ g₀ ℓ : ℕ} (S : Stretch Q C u₀ g₀ ℓ)
    {e₁ off : ℕ} (hu₀ : u₀ = (e₁ + off) % Q.n) {ps : List Pc} (hne : ps ≠ []) {sa ea : WPos}
    (hlt : (chainModel C).key Q sa < (chainModel C).key Q ea)
    (h0 : (chainModel C).key Q (ps[0]'(List.length_pos_iff.2 hne)).s = (chainModel C).key Q sa)
    (hl : (chainModel C).key Q (ps[ps.length - 1]'(by
      have := List.length_pos_iff.2 hne; omega)).e = (chainModel C).key Q ea)
    (hc : ∀ i (hi : i + 1 < ps.length), (chainModel C).key Q (ps[i]'(⋄)).e =
      (chainModel C).key Q (ps[i + 1]'hi).s)
    (ht : ∀ i (hi : i + 1 < ps.length), sideInArc ((chainModel C).key Q (ps[i]'(⋄)).s)
      ((chainModel C).key Q ea) ((chainModel C).key Q (ps[i]'(⋄)).e))
    (hpp : ∀ pc ∈ ps, ProperPos (chainModel C) Q Q.n pc.s ∧ ProperPos (chainModel C) Q Q.n pc.e)
    (hsa : (g₀ : ℝ) ≤ (chainModel C).key Q sa) (hea : (chainModel C).key Q ea ≤ g₀ + ℓ) :
    KPath (interiorModel Q) Q Q.n ((e₁ : ℝ) + off - g₀ + (chainModel C).key Q sa)
      (ps.map (trPc Q.n u₀ g₀)) ((e₁ : ℝ) + off - g₀ + (chainModel C).key Q ea) := by
  have hmono := chain_mono hne hlt h0 hl hc ht
  have hne' : ps.map (trPc Q.n u₀ g₀) ≠ [] := by simpa using hne
  have hlen : (ps.map (trPc Q.n u₀ g₀)).length = ps.length := List.length_map _
  have key := kpath_of_idx (M := interiorModel Q) (Q := Q) (n := (Q.n : ℝ))
    (ps.map (trPc Q.n u₀ g₀))
    (fun i => (e₁ : ℝ) + off - g₀ + (chainModel C).key Q (ps.getD i pc0).s)
    (fun i => (e₁ : ℝ) + off - g₀ + (chainModel C).key Q (ps.getD i pc0).e) hne'
    (fun i hi => by
      rw [hlen] at hi
      have hgi : ps.getD i pc0 = ps[i]'hi := ⊚ List.getD, hi
      ϴ List.getElem_map, hgi
      obtain ⟨m1, m2, m3⟩ := hmono i hi
      have hp := hpp _ (List.getElem_mem hi)
      exact ⟨trP_cong S hu₀ hp.1 (hsa.trans m1) ((m2.le.trans m3).trans hea),
        trP_cong S hu₀ hp.2 (hsa.trans (m1.trans m2.le)) (m3.trans hea), ⟡⟩)
    (fun i hi => by
      rw [hlen] at hi
      have hgi : ps.getD i pc0 = ps[i]'(⋄) := by simp [List.getD, show i < ps.length by omega]
      have hgi' : ps.getD (i + 1) pc0 = ps[i + 1]'hi := ⊚ List.getD, hi
      simp only [hgi, hgi', hc i hi])
  have hg0 : ps.getD 0 pc0 = ps[0]'(List.length_pos_iff.2 hne) := by
    Θ List.getD, List.length_pos_iff.2 hne
  have hgl : ps.getD (ps.length - 1) pc0 = ps[ps.length - 1]'(by
      have := List.length_pos_iff.2 hne; omega) := by
    Θ List.getD, show ps.length - 1 < ps.length by have := List.length_pos_iff.2 hne; omega
  simp only [hlen, hg0, hgl, h0, hl] at key
  exact key

end

end IOrc

end Chazelle.Core
