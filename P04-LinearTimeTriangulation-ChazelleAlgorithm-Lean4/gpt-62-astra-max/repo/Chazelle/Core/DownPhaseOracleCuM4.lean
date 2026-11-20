module

public import Chazelle.Core.DownPhaseOracleCuM3

/-!
# WP-M (E7-B, part 16): the answer of the interior cutter, and the slot registers

* `cut_out`: a path of unwrapped interior keys from the key of the start of the query to a value
  congruent to the key of its end, within one lap, gives the order facts `CutterOK` asks for (the
  first and last keys, consecutive keys, the tiling conjunct).
* `slotOK_edges`: the edges of the pieces of a valid slot lie in its stretch (the RAM's
  translation stays below `2 n`).
* `slotsOf c k`: the slots recorded in the registers `170200 + 5 j …` (`j < k`, flag `1`), in
  order; `SlotSt`: the invariant of the slot registers while the interior cutter calls the chain
  cutter (`SlotSt.keep`, `SlotSt.add`).
* `ee_bound`: a normalized query spans at most one lap.
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)
open ShootCut (Pc KPath)
open Machine

/-! ## Indexed facts of a path of unwrapped keys -/

/-- Consecutive ends of a path of unwrapped keys are congruent. -/
theorem kpath_idx {M : Model} {Q : Polygon} {n : ℝ} : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ},
    KPath M Q n V ps V' → ∀ i (hi : i + 1 < ps.length), ∃ (j j' : ℤ),
      M.key Q (ps[i]'(by omega)).e + j * n = M.key Q (ps[i + 1]'hi).s + j' * n
  | _, [], _, _, i, hi => by simp at hi
  | _, [_], _, _, i, hi => by simp at hi
  | _, pc :: q :: qs, _, ⟨_, V₁, _, ⟨j, hj⟩, hp⟩, i, hi => by
    rcases i with _ | i
    · obtain ⟨⟨j', hj'⟩, -⟩ := hp
      exact ⟨j, j', by simp only [List.getElem_cons_zero, List.getElem_cons_succ]; linarith⟩
    · have := kpath_idx hp i (by simp at hi ⊢; omega)
      simpa using this

/-- Keys of proper positions on the walk lie in `[0, n)`. -/
theorem pkey_bd {M : Model} {Q : Polygon} {N : ℕ} {x : WPos} (hx : ProperPos M Q N x)
    (he : x.edge < M.W.n) : 0 ≤ M.key Q x ∧ M.key Q x < M.W.n := by
  have hk : M.key Q x = x.edge + M.param Q x := rfl
  have : (x.edge : ℝ) + 1 ≤ M.W.n := by exact_mod_cast he
  rw [hk]; constructor <;> linarith [hx.1, hx.2.1, (Nat.cast_nonneg x.edge : (0 : ℝ) ≤ x.edge)]

/-- **The answer of the interior cutter**: the order facts of `CutterOK` from a path of unwrapped
interior keys within one lap. -/
theorem cut_out {P : Polygon} {ps : List Pc} {V0 V1 : ℝ} {m : ℕ → ℕ} {E Hγ : ℕ} {s e : WPos}
    (hk : KPath (interiorModel (Qof P)) (Qof P) (Qof P).n V0 ps V1)
    (hv : ∀ pc ∈ ps, PcV P (interiorModel (Qof P)) m E Hγ pc) (hne : ps ≠ [])
    (hs : V0 = (interiorModel (Qof P)).key (Qof P) s)
    (he : ∃ j : ℤ, V1 = (interiorModel (Qof P)).key (Qof P) e + j * (Qof P).n)
    (hsb : 0 ≤ (interiorModel (Qof P)).key (Qof P) s ∧
      (interiorModel (Qof P)).key (Qof P) s < (Qof P).n)
    (heb : 0 ≤ (interiorModel (Qof P)).key (Qof P) e ∧
      (interiorModel (Qof P)).key (Qof P) e < (Qof P).n)
    (hle : V1 ≤ V0 + (Qof P).n) :
    (interiorModel (Qof P)).key (Qof P) (ps[0]'(List.length_pos_iff.2 hne)).s =
        (interiorModel (Qof P)).key (Qof P) s ∧
      (interiorModel (Qof P)).key (Qof P) (ps[ps.length - 1]'(by
        have := List.length_pos_iff.2 hne; omega)).e = (interiorModel (Qof P)).key (Qof P) e ∧
      (∀ i (hi : i + 1 < ps.length), (interiorModel (Qof P)).key (Qof P) (ps[i]'(by omega)).e =
        (interiorModel (Qof P)).key (Qof P) (ps[i + 1]'hi).s) ∧
      (∀ i (hi : i + 1 < ps.length), sideInArc ((interiorModel (Qof P)).key (Qof P) (ps[i]'(by omega)).s)
        ((interiorModel (Qof P)).key (Qof P) e) ((interiorModel (Qof P)).key (Qof P) (ps[i]'(by omega)).e)) := by
  set M := interiorModel (Qof P) with hM
  set Q := Qof P with hQd
  have hmi : M.W.n = Q.n := mi_n
  have hQ : Q.n = P.n := qn'
  have hlen := List.length_pos_iff.2 hne
  have hn0 : (0 : ℝ) < Q.n := lt_of_le_of_lt hsb.1 hsb.2
  have hb : ∀ pc ∈ ps, (0 ≤ M.key Q pc.s ∧ M.key Q pc.s < Q.n) ∧
      (0 ≤ M.key Q pc.e ∧ M.key Q pc.e < Q.n) := by
    intro pc hpc
    obtain ⟨h1, h2, h3, h4, -⟩ := hv pc hpc
    have a := pkey_bd h1 h3
    have b := pkey_bd h2 h4
    rw [hmi] at a b
    exact ⟨a, b⟩
  have hget : ∀ i (hi : i < ps.length), ps[i]'hi ∈ ps := fun i hi => List.getElem_mem hi
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · -- the first key
    obtain ⟨pc, qs, rfl⟩ : ∃ pc qs, ps = pc :: qs := List.exists_cons_of_ne_nil hne
    obtain ⟨⟨i, hi⟩, -⟩ := hk
    simp only [List.getElem_cons_zero]
    exact (ShootCut.key_eq_of_unw hn0 (hb pc (by simp)).1 hsb (i := i) (j := 0)
      (by rw [← hi, hs]; simp)).symm.symm
  · -- the last key
    obtain ⟨j, hj⟩ := KPath.last hk hne
    obtain ⟨j', hj'⟩ := he
    rw [← List.getLast_eq_getElem hne]
    exact ShootCut.key_eq_of_unw hn0 (hb _ (List.getLast_mem hne)).2 heb (i := j) (j := j')
      (by rw [← hj, ← hj'])
  · obtain ⟨j, j', h⟩ := kpath_idx hk i hi
    exact ShootCut.key_eq_of_unw hn0 (hb _ (hget i (by omega))).2 (hb _ (hget (i + 1) hi)).1 h
  · have := ShootCut.e6_of_kpath hn0 hk hle hb hne i hi
    have hl : M.key Q (ps.getLast hne).e = M.key Q e := by
      obtain ⟨j, hj⟩ := KPath.last hk hne
      obtain ⟨j', hj'⟩ := he
      exact ShootCut.key_eq_of_unw hn0 (hb _ (List.getLast_mem hne)).2 heb (i := j) (j := j')
        (by rw [← hj, ← hj'])
    rw [hl] at this
    exact this

/-! ## The edges of the pieces of a slot -/

/-- **The pieces of a valid slot lie in its stretch**: their edges are at most `ℓ < n` beyond
`g₀`, and the stretch starts at an interior vertex. -/
theorem slotOK_edges {P : Polygon} {m : ℕ → ℕ} {E Hγ e₁ : ℕ} {Va Vb : ℝ} {sl : Slot}
    (h : SlotOK P m E Hγ e₁ Va Vb sl) :
    sl.u₀ < (Qof P).n ∧ sl.L + 1 + 7 * sl.q ≤ E ∧ m sl.L = sl.q ∧ 1 ≤ sl.q ∧
      ∀ i, i < sl.q → (rdPc m sl.L i).s.edge - sl.g₀ < (Qof P).n ∧
        (rdPc m sl.L i).e.edge - sl.g₀ < (Qof P).n := by
  obtain ⟨C, ℓ, off, sa, ea, S, hu, hq, hq1, hLE, h0, hl, hc, ht, hv, r1, r2, r3, r4, r5⟩ := h
  have hQ : (Qof P).n = P.n := qn'
  refine ⟨S.hu, hLE, hq, hq1, fun i hi => ?_⟩
  set ps := (List.range sl.q).map (rdPc m sl.L) with hps
  have hlen : ps.length = sl.q := by simp [hps]
  have hne : ps ≠ [] := by
    intro h; have := congrArg List.length h; rw [hlen] at this; simp at this; omega
  have hget : ∀ i (hi : i < ps.length), ps[i]'hi = rdPc m sl.L i := fun i hi => by
    simp [hps]
  have h0' : (chainModel C).key (Qof P) (ps[0]'(List.length_pos_iff.2 hne)).s =
      (chainModel C).key (Qof P) sa := by rw [hget]; exact h0
  have hl' : (chainModel C).key (Qof P) (ps[ps.length - 1]'(by
      have := List.length_pos_iff.2 hne; omega)).e = (chainModel C).key (Qof P) ea := by
    rw [hget, hlen]; exact hl
  have hc' : ∀ i (hi : i + 1 < ps.length), (chainModel C).key (Qof P) (ps[i]'(by omega)).e =
      (chainModel C).key (Qof P) (ps[i + 1]'hi).s := fun i hi => by
    rw [hget, hget]; exact hc i (by omega)
  have ht' : ∀ i (hi : i + 1 < ps.length), sideInArc ((chainModel C).key (Qof P) (ps[i]'(by omega)).s)
      ((chainModel C).key (Qof P) ea) ((chainModel C).key (Qof P) (ps[i]'(by omega)).e) :=
    fun i hi => by rw [hget]; exact ht i (by omega)
  obtain ⟨m1, m2, m3⟩ := chain_mono hne r3 h0' hl' hc' ht' i (by omega)
  rw [hget] at m1 m2 m3
  have hp := hv i hi
  have hsP : ProperPos (chainModel C) (Qof P) (Qof P).n (rdPc m sl.L i).s := by rw [hQ]; exact hp.1
  have heP : ProperPos (chainModel C) (Qof P) (Qof P).n (rdPc m sl.L i).e := by rw [hQ]; exact hp.2.1
  obtain ⟨a1, a2, -⟩ := str_edge S hsP (r1.trans m1) ((m2.le.trans m3).trans r2)
  obtain ⟨b1, b2, -⟩ := str_edge S heP (r1.trans (m1.trans m2.le)) (m3.trans r2)
  have hℓ := S.hℓ
  exact ⟨by omega, by omega⟩

/-! ## The slot registers -/

/-- **Slot `k`** in the registers `170201 + 5 k … 170204 + 5 k` (its flag at `170200 + 5 k`). -/
def slotAt (c : Config) (k : ℕ) : Slot :=
  ⟨c.nreg (170201 + 5 * k), c.nreg (170202 + 5 * k), c.nreg (170203 + 5 * k),
    c.nreg (170204 + 5 * k)⟩

/-- **The recorded slots** among the first `k`, in order. -/
def slotsOf (c : Config) : ℕ → List Slot
  | 0 => []
  | k + 1 => slotsOf c k ++ (if c.nreg (170200 + 5 * k) = 1 then [slotAt c k] else [])

theorem slotsOf_congr {c c' : Config} :
    ∀ {k : ℕ}, (∀ j f, j < k → f < 5 → c'.nreg (170200 + 5 * j + f) = c.nreg (170200 + 5 * j + f)) →
      slotsOf c' k = slotsOf c k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := slotsOf_congr (k := k) (fun j f hj hf => h j f (by omega) hf)
    have h0 := h k 0 (by omega) (by omega)
    have h1 := h k 1 (by omega) (by omega)
    have h2 := h k 2 (by omega) (by omega)
    have h3 := h k 3 (by omega) (by omega)
    have h4 := h k 4 (by omega) (by omega)
    simp only [Nat.add_zero] at h0
    have e : slotAt c' k = slotAt c k := by
      unfold slotAt
      rw [show 170201 + 5 * k = 170200 + 5 * k + 1 by ring,
        show 170202 + 5 * k = 170200 + 5 * k + 2 by ring,
        show 170203 + 5 * k = 170200 + 5 * k + 3 by ring,
        show 170204 + 5 * k = 170200 + 5 * k + 4 by ring, h1, h2, h3, h4]
    simp only [slotsOf, ih, h0, e]

theorem slotsOf_free {c : Config} {k : ℕ} :
    ∀ {K : ℕ}, k ≤ K → (∀ j, k ≤ j → j < K → c.nreg (170200 + 5 * j) = 0) →
      slotsOf c K = slotsOf c k
  | 0, hk, _ => by rw [show k = 0 by omega]
  | K + 1, hk, h => by
    rcases hk.lt_or_eq with hk | hk
    · have ih := slotsOf_free (K := K) (by omega) (fun j h1 h2 => h j h1 (by omega))
      simp only [slotsOf, ih, h K (by omega) (by omega)]
      simp
    · rw [hk]

/-- Recording slot `k`. -/
theorem slotsOf_rec {c c' : Config} {k : ℕ} (hk : k < 4)
    (hfree : ∀ j, k ≤ j → j < 4 → c.nreg (170200 + 5 * j) = 0)
    (hfree' : ∀ j, k + 1 ≤ j → j < 4 → c'.nreg (170200 + 5 * j) = 0)
    (hr : ∀ r, r < 170200 + 5 * k → c'.nreg r = c.nreg r)
    (hf : c'.nreg (170200 + 5 * k) = 1) :
    slotsOf c' 4 = slotsOf c 4 ++ [slotAt c' k] := by
  rw [slotsOf_free (k := k + 1) (by omega) hfree', slotsOf_free (k := k) (by omega) hfree]
  simp only [slotsOf, hf, ite_true]
  rw [slotsOf_congr (fun j f hj hf => hr _ (by omega))]

/-- **The slot state**: the recorded slots form a chain of valid slots from `V0` to `V`, the
slots from `k` on are free, the flags are bits, each slot has at most `Gγ` pieces. -/
structure SlotSt (P : Polygon) (Hγ Gγ e₁ : ℕ) (V0 V : ℝ) (k : ℕ) (c : Config) : Prop where
  ok : SlotsOK P c.nmem (c.nreg ALLOC) Hγ e₁ V0 (slotsOf c 4) V
  free : ∀ j, k ≤ j → j < 4 → c.nreg (170200 + 5 * j) = 0
  bit : ∀ j, j < 4 → c.nreg (170200 + 5 * j) ≤ 1
  qG : ∀ sl ∈ slotsOf c 4, sl.q ≤ Gγ

/-- **The slot state survives** steps keeping the slot registers and the memory below the
allocator, not lowering the allocator. -/
theorem SlotSt.keep {P : Polygon} {Hγ Gγ e₁ : ℕ} {V0 V : ℝ} {k : ℕ} {c c' : Config}
    (h : SlotSt P Hγ Gγ e₁ V0 V k c) (hr : ∀ r, 170200 ≤ r → r < 170220 → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    SlotSt P Hγ Gγ e₁ V0 V k c' := by
  have hs : slotsOf c' 4 = slotsOf c 4 := slotsOf_congr (fun j f hj hf => hr _ (by omega)
    (by omega))
  refine ⟨?_, fun j h1 h2 => ?_, fun j hj => ?_, fun sl hsl => h.qG sl (by rw [← hs]; exact hsl)⟩
  · rw [hs]; exact h.ok.keep hm ha
  · rw [hr _ (by omega) (by omega)]; exact h.free j h1 h2
  · rw [hr _ (by omega) (by omega)]; exact h.bit j hj

/-- **Recording slot `k`**: a valid slot from `V` to `V'` with at most `Gγ` pieces. -/
theorem SlotSt.add {P : Polygon} {Hγ Gγ e₁ : ℕ} {V0 V V' : ℝ} {k : ℕ} {c c' : Config}
    (h : SlotSt P Hγ Gγ e₁ V0 V k c) (hk : k < 4)
    (hr : ∀ r, (r < 170200 + 5 * k ∨ 170205 + 5 * k ≤ r) → c'.nreg r = c.nreg r)
    (hf : c'.nreg (170200 + 5 * k) = 1) (hm : c'.nmem = c.nmem)
    (hs : SlotOK P c.nmem (c.nreg ALLOC) Hγ e₁ V V' (slotAt c' k)) (hq : (slotAt c' k).q ≤ Gγ) :
    SlotSt P Hγ Gγ e₁ V0 V' (k + 1) c' := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr _ (Or.inl (by unfold ALLOC; omega))
  have hfree' : ∀ j, k + 1 ≤ j → j < 4 → c'.nreg (170200 + 5 * j) = 0 := fun j h1 h2 => by
    rw [hr _ (Or.inr (by omega))]; exact h.free j (by omega) h2
  have he := slotsOf_rec hk h.free hfree' (fun r hr' => hr r (Or.inl hr')) hf
  refine ⟨?_, hfree', fun j hj => ?_, fun sl hsl => ?_⟩
  · rw [he, hm, hA]; exact h.ok.snoc hs
  · rcases (show j < k ∨ j = k ∨ k < j by omega) with h1 | h1 | h1
    · rw [hr _ (Or.inl (by omega))]; exact h.bit j hj
    · subst h1; rw [hf]
    · rw [hfree' j (by omega) hj]; omega
  · rw [he, List.mem_append, List.mem_singleton] at hsl
    rcases hsl with hsl | rfl
    · exact h.qG sl hsl
    · exact hq

/-- The number of recorded slots is at most `k`. -/
theorem slotsOf_length {c : Config} : ∀ {k : ℕ}, (slotsOf c k).length ≤ k
  | 0 => le_rfl
  | k + 1 => by
    have := slotsOf_length (c := c) (k := k)
    simp only [slotsOf, List.length_append]
    split_ifs <;> simp <;> omega

/-! ## One lap -/

/-- **A normalized query spans at most one lap.** -/
theorem ee_bound {Q : Polygon} {e₁ h₁ e₂ h₂ : ℕ} (hn : 1 ≤ Q.n)
    (hx : 0 ≤ (interiorModel Q).param Q ⟨e₁, h₁⟩)
    (hy : (interiorModel Q).param Q ⟨e₂, h₂⟩ < 1) :
    (eeOf Q e₁ h₁ e₂ h₂ : ℝ) + (interiorModel Q).param Q ⟨e₂, h₂⟩ ≤
      Q.n + (interiorModel Q).param Q ⟨e₁, h₁⟩ := by
  unfold eeOf
  split_ifs with h0 h1
  · push_cast; have : (1 : ℝ) ≤ Q.n := by exact_mod_cast hn
    linarith
  · push Not at h1; linarith
  · have hd : WalkEmbed.dOf Q.n e₁ e₂ < Q.n := by
      unfold WalkEmbed.dOf; exact Nat.mod_lt _ (by omega)
    have : ((WalkEmbed.dOf Q.n e₁ e₂ : ℕ) : ℝ) + 1 ≤ Q.n := by exact_mod_cast hd
    linarith

end

end IOrc

end Chazelle.Core
