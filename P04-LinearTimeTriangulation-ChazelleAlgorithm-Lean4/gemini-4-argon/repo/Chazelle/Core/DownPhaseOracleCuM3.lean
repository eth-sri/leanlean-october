module

public import Chazelle.Core.DownPhaseOracleCuM2

/-!
# WP-M (E7-B, part 15): the slots of the interior cutter

Each call of the chain cutter is recorded as a **slot** `(L, q, g₀, u₀)`: the list address, the
number of pieces, and the stretch of the call (`SlotOK`: a chain arc in a stretch, its pieces
valid and in increasing key order, with unwrapped interior keys from `Va` to `Vb`).  The interior
cutter copies the pieces of its slots, oldest first, translating their ends on the RAM (`trE`,
`trPcR`, `slotPcs`).

* `slotOK_out`: the translated pieces of a slot form a path of unwrapped interior keys from `Va`
  to `Vb` and are valid pieces of the interior walk (`PcV`);
* `slotsOK_out`: the same for a chain of slots (`SlotsOK`).
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)
open ShootCut (Pc KPath)

/-! ## The translation on the RAM -/

/-- The translated edge as the RAM computes it. -/
def trE (n u₀ g₀ e : ℕ) : ℕ := if u₀ + (e - g₀) < n then u₀ + (e - g₀) else u₀ + (e - g₀) - n

theorem trE_eq {n u₀ g₀ e : ℕ} (hu : u₀ < n) (he : e - g₀ < n) :
    trE n u₀ g₀ e = (u₀ + (e - g₀)) % n := by
  unfold trE
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The translated piece as the RAM computes it. -/
def trPcR (n u₀ g₀ : ℕ) (pc : Pc) : Pc :=
  { pc with s := ⟨trE n u₀ g₀ pc.s.edge, pc.s.hgt⟩, e := ⟨trE n u₀ g₀ pc.e.edge, pc.e.hgt⟩ }

theorem trPcR_eq {n u₀ g₀ : ℕ} {pc : Pc} (hu : u₀ < n) (hs : pc.s.edge - g₀ < n)
    (he : pc.e.edge - g₀ < n) : trPcR n u₀ g₀ pc = trPc n u₀ g₀ pc := by
  unfold trPcR trPc trP
  rw [trE_eq hu hs, trE_eq hu he]

/-- The words of a piece record. -/
def pcW (pc : Pc) : ℕ → ℕ
  | 0 => pc.s.edge
  | 1 => pc.s.hgt
  | 2 => pc.e.edge
  | 3 => pc.e.hgt
  | 4 => pc.kind
  | 5 => pc.entry
  | _ => pc.x0

/-! ## Slots -/

/-- **A slot**: the list address, the number of pieces, the stretch start in the chain walk and
in the interior walk. -/
structure Slot where
  L : ℕ
  q : ℕ
  g₀ : ℕ
  u₀ : ℕ

/-- The translated pieces of a slot. -/
def slotPcs (m : ℕ → ℕ) (n : ℕ) (sl : Slot) : List Pc :=
  (List.range sl.q).map fun i => trPcR n sl.u₀ sl.g₀ (rdPc m sl.L i)

/-- **A valid slot**: the pieces of a chain arc `[sa, ea]` of the chain `C`, inside a stretch,
valid and in increasing key order, with unwrapped interior keys from `Va` to `Vb`. -/
def SlotOK (P : Polygon) (m : ℕ → ℕ) (E Hγ e₁ : ℕ) (Va Vb : ℝ) (sl : Slot) : Prop :=
  ∃ (C : Chain) (ℓ off : ℕ) (sa ea : WPos), Stretch (Qof P) C sl.u₀ sl.g₀ ℓ ∧
    sl.u₀ = (e₁ + off) % (Qof P).n ∧ m sl.L = sl.q ∧ 1 ≤ sl.q ∧ sl.L + 1 + 7 * sl.q ≤ E ∧
    (chainModel C).key (Qof P) (rdPc m sl.L 0).s = (chainModel C).key (Qof P) sa ∧
    (chainModel C).key (Qof P) (rdPc m sl.L (sl.q - 1)).e = (chainModel C).key (Qof P) ea ∧
    (∀ i, i + 1 < sl.q → (chainModel C).key (Qof P) (rdPc m sl.L i).e =
      (chainModel C).key (Qof P) (rdPc m sl.L (i + 1)).s) ∧
    (∀ i, i + 1 < sl.q → sideInArc ((chainModel C).key (Qof P) (rdPc m sl.L i).s)
      ((chainModel C).key (Qof P) ea) ((chainModel C).key (Qof P) (rdPc m sl.L i).e)) ∧
    (∀ i, i < sl.q → PcV P (chainModel C) m E Hγ (rdPc m sl.L i)) ∧
    (sl.g₀ : ℝ) ≤ (chainModel C).key (Qof P) sa ∧
    (chainModel C).key (Qof P) ea ≤ sl.g₀ + ℓ ∧
    (chainModel C).key (Qof P) sa < (chainModel C).key (Qof P) ea ∧
    Va = (e₁ : ℝ) + off - sl.g₀ + (chainModel C).key (Qof P) sa ∧
    Vb = (e₁ : ℝ) + off - sl.g₀ + (chainModel C).key (Qof P) ea

theorem rdPc_congr {m m' : ℕ → ℕ} {L i E : ℕ} (he : ∀ a, a < E → m' a = m a)
    (hi : L + 1 + 7 * i + 7 ≤ E) : rdPc m' L i = rdPc m L i := by
  unfold rdPc
  rw [he _ (by omega), he _ (by omega), he _ (by omega), he _ (by omega), he _ (by omega),
    he _ (by omega), he _ (by omega)]

/-- **A valid slot survives** memory changes at or above its bound. -/
theorem SlotOK.keep {P : Polygon} {m m' : ℕ → ℕ} {E E' Hγ e₁ : ℕ} {Va Vb : ℝ} {sl : Slot}
    (h : SlotOK P m E Hγ e₁ Va Vb sl) (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    SlotOK P m' E' Hγ e₁ Va Vb sl := by
  obtain ⟨C, ℓ, off, sa, ea, S, hu, hq, hq1, hLE, h0, hl, hc, ht, hv, r1, r2, r3, r4, r5⟩ := h
  have hr : ∀ i, i < sl.q → rdPc m' sl.L i = rdPc m sl.L i := fun i hi =>
    rdPc_congr he (by have : 7 * i + 7 ≤ 7 * sl.q := by omega
                      omega)
  refine ⟨C, ℓ, off, sa, ea, S, hu, by rwa [he _ (by omega)], hq1, by omega,
    by rwa [hr 0 (by omega)], by rwa [hr _ (by omega)],
    fun i hi => by rw [hr i (by omega), hr (i + 1) hi]; exact hc i hi,
    fun i hi => by rw [hr i (by omega)]; exact ht i hi,
    fun i hi => by rw [hr i hi]; exact (hv i hi).keep he hE, r1, r2, r3, r4, r5⟩

/-- **The translated pieces of a valid slot** form a path of unwrapped interior keys and are
valid pieces of the interior walk. -/
theorem slotOK_out {P : Polygon} {m : ℕ → ℕ} {E Hγ e₁ : ℕ} {Va Vb : ℝ} {sl : Slot}
    (h : SlotOK P m E Hγ e₁ Va Vb sl) :
    KPath (interiorModel (Qof P)) (Qof P) (Qof P).n Va (slotPcs m (Qof P).n sl) Vb ∧
      (∀ pc ∈ slotPcs m (Qof P).n sl, PcV P (interiorModel (Qof P)) m E Hγ pc) ∧
      slotPcs m (Qof P).n sl ≠ [] := by
  obtain ⟨C, ℓ, off, sa, ea, S, hu, hq, hq1, hLE, h0, hl, hc, ht, hv, r1, r2, r3, r4, r5⟩ := h
  have hQ : (Qof P).n = P.n := qn'
  set ps := (List.range sl.q).map (rdPc m sl.L) with hps
  have hlen : ps.length = sl.q := by simp [hps]
  have hne : ps ≠ [] := by
    intro h; have := congrArg List.length h; rw [hlen] at this; simp at this; omega
  have hget : ∀ i (hi : i < ps.length), ps[i]'hi = rdPc m sl.L i := fun i hi => by
    simp [hps]
  -- the order facts in list form
  have h0' : (chainModel C).key (Qof P) (ps[0]'(List.length_pos_iff.2 hne)).s =
      (chainModel C).key (Qof P) sa := by rwa [hget]
  have hl' : (chainModel C).key (Qof P) (ps[ps.length - 1]'(by
      have := List.length_pos_iff.2 hne; omega)).e = (chainModel C).key (Qof P) ea := by
    rwa [hget, hlen]
  have hc' : ∀ i (hi : i + 1 < ps.length), (chainModel C).key (Qof P) (ps[i]'(by omega)).e =
      (chainModel C).key (Qof P) (ps[i + 1]'hi).s := fun i hi => by
    rw [hget, hget]; exact hc i (by omega)
  have ht' : ∀ i (hi : i + 1 < ps.length), sideInArc ((chainModel C).key (Qof P) (ps[i]'(by omega)).s)
      ((chainModel C).key (Qof P) ea) ((chainModel C).key (Qof P) (ps[i]'(by omega)).e) :=
    fun i hi => by rw [hget]; exact ht i (by omega)
  have hpp : ∀ pc ∈ ps, ProperPos (chainModel C) (Qof P) (Qof P).n pc.s ∧
      ProperPos (chainModel C) (Qof P) (Qof P).n pc.e := by
    intro pc hpc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpc
    rw [hget]
    have := hv i (by omega)
    rw [hQ]; exact ⟨this.1, this.2.1⟩
  have hmono := chain_mono hne r3 h0' hl' hc' ht'
  -- the RAM translation is the translation
  have hslot : slotPcs m (Qof P).n sl = ps.map (trPc (Qof P).n sl.u₀ sl.g₀) := by
    unfold slotPcs
    rw [hps, List.map_map]
    refine List.map_congr_left (fun i hi => ?_)
    have hi' : i < sl.q := List.mem_range.1 hi
    obtain ⟨m1, m2, m3⟩ := hmono i (by omega)
    rw [hget] at m1 m2 m3
    have hp := hv i hi'
    have hsP : ProperPos (chainModel C) (Qof P) (Qof P).n (rdPc m sl.L i).s := by rw [hQ]; exact hp.1
    have heP : ProperPos (chainModel C) (Qof P) (Qof P).n (rdPc m sl.L i).e := by rw [hQ]; exact hp.2.1
    obtain ⟨a1, a2, -⟩ := str_edge S hsP (r1.trans m1) ((m2.le.trans m3).trans r2)
    obtain ⟨b1, b2, -⟩ := str_edge S heP (r1.trans (m1.trans m2.le)) (m3.trans r2)
    have hℓ := S.hℓ
    exact trPcR_eq S.hu (by omega) (by omega)
  refine ⟨?_, fun pc hpc => ?_, ?_⟩
  · rw [hslot, r4, r5]
    exact slot_kpath S hu hne r3 h0' hl' hc' ht' hpp r1 r2
  · rw [hslot] at hpc
    obtain ⟨pc', hpc', rfl⟩ := List.mem_map.1 hpc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpc'
    obtain ⟨m1, m2, m3⟩ := hmono i hi
    rw [hget] at m1 m2 m3 ⊢
    exact pcV_tr S (hv i (by omega)) (r1.trans m1) (m3.trans r2) m2
  · rw [hslot]; simpa using hne

/-! ## Chains of slots -/

/-- **A chain of valid slots** (oldest first), with unwrapped keys from `V` to `V'`. -/
def SlotsOK (P : Polygon) (m : ℕ → ℕ) (E Hγ e₁ : ℕ) : ℝ → List Slot → ℝ → Prop
  | V, [], V' => V = V'
  | V, sl :: sls, V' => ∃ V₁, SlotOK P m E Hγ e₁ V V₁ sl ∧ SlotsOK P m E Hγ e₁ V₁ sls V'

theorem SlotsOK.keep {P : Polygon} {m m' : ℕ → ℕ} {E E' Hγ e₁ : ℕ} (he : ∀ a, a < E → m' a = m a)
    (hE : E ≤ E') : ∀ {V : ℝ} {sls : List Slot} {V' : ℝ}, SlotsOK P m E Hγ e₁ V sls V' →
      SlotsOK P m' E' Hγ e₁ V sls V'
  | _, [], _, h => h
  | _, _ :: _, _, ⟨V₁, h1, h2⟩ => ⟨V₁, h1.keep he hE, SlotsOK.keep he hE h2⟩

theorem SlotsOK.snoc {P : Polygon} {m : ℕ → ℕ} {E Hγ e₁ : ℕ} :
    ∀ {V : ℝ} {sls : List Slot} {V₁ : ℝ}, SlotsOK P m E Hγ e₁ V sls V₁ →
      ∀ {sl : Slot} {V₂ : ℝ}, SlotOK P m E Hγ e₁ V₁ V₂ sl → SlotsOK P m E Hγ e₁ V (sls ++ [sl]) V₂
  | _, [], _, h, _, _, hs => by simp only [SlotsOK] at h; subst h; exact ⟨_, hs, rfl⟩
  | _, _ :: _, _, ⟨W₁, h1, h2⟩, _, _, hs => ⟨W₁, h1, SlotsOK.snoc h2 hs⟩

/-- **The translated pieces of a chain of valid slots.** -/
theorem slotsOK_out {P : Polygon} {m : ℕ → ℕ} {E Hγ e₁ : ℕ} :
    ∀ {V : ℝ} {sls : List Slot} {V' : ℝ}, SlotsOK P m E Hγ e₁ V sls V' →
      KPath (interiorModel (Qof P)) (Qof P) (Qof P).n V (sls.flatMap (slotPcs m (Qof P).n)) V' ∧
        (∀ pc ∈ sls.flatMap (slotPcs m (Qof P).n), PcV P (interiorModel (Qof P)) m E Hγ pc) ∧
        (sls ≠ [] → sls.flatMap (slotPcs m (Qof P).n) ≠ [])
  | _, [], _, h => by simp only [SlotsOK] at h; subst h; exact ⟨rfl, by simp, fun h => absurd rfl h⟩
  | _, sl :: sls, _, ⟨V₁, h1, h2⟩ => by
    obtain ⟨k1, v1, n1⟩ := slotOK_out h1
    obtain ⟨k2, v2, -⟩ := slotsOK_out h2
    refine ⟨?_, fun pc hpc => ?_, fun _ => ?_⟩
    · rw [List.flatMap_cons]; exact k1.append _ k2
    · rw [List.flatMap_cons, List.mem_append] at hpc
      rcases hpc with h | h
      · exact v1 pc h
      · exact v2 pc h
    · rw [List.flatMap_cons]; simp [n1]

end

end IOrc

end Chazelle.Core
