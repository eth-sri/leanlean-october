module

public import Chazelle.Core.OraclePrepPlanar

/-!
# Lemma 3.6 (WP-H), preprocessing part 20: the darts of the book

For a book `⟨N, I, O⟩` with its chords `L = I ++ O` in two arrays, the edge `e` has ends
`eU e`, `eV e` and kind `eKind e` (`0` spine, `1` inner, `2` outer); its darts `2 e` and
`2 e + 1` have the tails `eU e`, `eV e` and the keys `dKey0`, `dKey1` (`view_even`,
`view_odd`).  `edgeS`: the ends and the kind of the edge in `60030` (`edgeS_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleBook OracleBook.BookData

@[expose] public section

/-- The first end of edge `e`. -/
def eU (N : ℕ) (L : List (ℕ × ℕ)) (e : ℕ) : ℕ := if e < N then e else (L.getD (e - N) (0, 0)).1

/-- The second end of edge `e`. -/
def eV (N : ℕ) (L : List (ℕ × ℕ)) (e : ℕ) : ℕ :=
  if e < N then (if e + 1 < N then e + 1 else 0) else (L.getD (e - N) (0, 0)).2

/-- The kind of edge `e`. -/
def eKind (N nI e : ℕ) : ℕ := if e < N then 0 else if e - N < nI then 1 else 2

/-- The key of the dart `2 e`. -/
def dKey0 (N k u v : ℕ) : ℕ := if k = 0 then 0 else if k = 1 then v - u else 2 * N - 2 - (v - u)

/-- The key of the dart `2 e + 1`. -/
def dKey1 (N k u v : ℕ) : ℕ :=
  if k = 0 then N - 1 else if k = 1 then N - v + u else N - 2 + (v - u)

theorem getD_I {B : BookData} {j : ℕ} (hj : j < B.I.length) :
    B.I.getD j (0, 0) = (B.I ++ B.O).getD j (0, 0) := (List.getD_append _ _ _ _ hj).symm

theorem getD_O {B : BookData} {j : ℕ} (hj : B.I.length ≤ j) :
    B.O.getD (j - B.I.length) (0, 0) = (B.I ++ B.O).getD j (0, 0) :=
  (List.getD_append_right _ _ _ _ hj).symm

/-- **The even dart of an edge.** -/
theorem view_even (B : BookData) (_hV : B.Valid) {e : ℕ} (_he : e < B.E) :
    View.tail B.N (B.view (2 * e)) = eU B.N (B.I ++ B.O) e ∧
      View.key B.N (B.view (2 * e)) =
        dKey0 B.N (eKind B.N B.I.length e) (eU B.N (B.I ++ B.O) e) (eV B.N (B.I ++ B.O) e) := by
  have h2 : 2 * e / 2 = e := by omega
  have h3 : 2 * e % 2 = 0 := by omega
  unfold view
  rw [h2]
  by_cases a : e < B.N
  · rw [ite_eq_left a, ite_eq_left h3]; simp [View.tail, View.key, eU, eKind, dKey0, a]
  · rw [ite_eq_right a]
    by_cases b : e < B.N + B.I.length
    · rw [ite_eq_left b, ite_eq_left h3, getD_I (by omega)]
      simp [View.tail, View.key, eU, eV, eKind, dKey0, a, show e - B.N < B.I.length by omega]
    · rw [ite_eq_right b, ite_eq_left h3, show e - B.N - B.I.length = (e - B.N) - B.I.length by omega,
        getD_O (by omega)]
      simp [View.tail, View.key, eU, eV, eKind, dKey0, a, show ¬ e - B.N < B.I.length by omega]

/-- **The odd dart of an edge.** -/
theorem view_odd (B : BookData) (hV : B.Valid) {e : ℕ} (he : e < B.E) :
    View.tail B.N (B.view (2 * e + 1)) = eV B.N (B.I ++ B.O) e ∧
      View.key B.N (B.view (2 * e + 1)) =
        dKey1 B.N (eKind B.N B.I.length e) (eU B.N (B.I ++ B.O) e) (eV B.N (B.I ++ B.O) e) := by
  have h2 : (2 * e + 1) / 2 = e := by omega
  have h3 : ¬ (2 * e + 1) % 2 = 0 := by omega
  unfold view
  rw [h2]
  by_cases a : e < B.N
  · rw [ite_eq_left a, ite_eq_right h3]
    refine ⟨?_, ?_⟩
    · simp only [View.tail, eV, ite_eq_left a]
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · rw [show e + 1 = B.N by omega, Nat.mod_self]
    · simp [View.key, eKind, dKey1, a]
  · rw [ite_eq_right a]
    by_cases b : e < B.N + B.I.length
    · rw [ite_eq_left b, ite_eq_right h3, getD_I (by omega)]
      simp only [View.tail, View.key, eU, eV, eKind, dKey1, ite_eq_right a,
        ite_eq_left (show e - B.N < B.I.length by omega)]
      refine ⟨trivial, ?_⟩
      simp
    · rw [ite_eq_right b, ite_eq_right h3, show e - B.N - B.I.length = (e - B.N) - B.I.length by omega,
        getD_O (by omega)]
      simp only [View.tail, View.key, eU, eV, eKind, dKey1, ite_eq_right a,
        ite_eq_right (show ¬ e - B.N < B.I.length by omega)]
      refine ⟨trivial, ?_⟩
      -- the outer chords have increasing ends
      have hmem : (B.I ++ B.O).getD (e - B.N) (0, 0) ∈ B.O := by
        rw [← getD_O (by omega)]
        exact getD_mem (by unfold E at he; omega)
      obtain ⟨h1, -, -⟩ := hV.2.2.2.2.1 _ hmem
      simp only [show (2 = 0) = False from by decide, show (2 = 1) = False from by decide, ite_false]
      omega

/-! ## The ends of an edge on the RAM -/

/-- The ends (`60031`, `60032`) and the kind (`60033`) of the edge in `60030`. -/
def edgeS : Stmt :=
  .ifLtN 60030 60034
    (.seq (block [.copyN 60031 60030, .addN 60032 60030 120011])
      (.seq (.ifLtN 60032 60034 .skip (.instr (.constN 60032 0))) (.instr (.constN 60033 0))))
    (.seq (block [.subN 60035 60030 60034, .addN 60036 60001 60035, .loadN 60031 60036,
        .addN 60036 60002 60035, .loadN 60032 60036])
      (.ifLtN 60035 60008 (.instr (.constN 60033 1)) (.instr (.constN 60033 2))))

/-- The registers written by `edgeS`. -/
def BEd (r : ℕ) : Bool := decide ((60031 ≤ r ∧ r ≤ 60033) ∨ r = 60035 ∨ r = 60036)

theorem edgeS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {N nI CH1 CH2 e : ℕ}
    {L : List (ℕ × ℕ)} (hN : c.nreg 60034 = N) (hI : c.nreg 60008 = nI) (h1 : c.nreg 60001 = CH1)
    (h2 : c.nreg 60002 = CH2) (hone : c.nreg 120011 = 1) (he : c.nreg 60030 = e)
    (heL : e < N + L.length) (hP : PairsAt c.nmem CH1 CH2 L) (hW1 : CH1 + L.length ≤ W)
    (hW2 : CH2 + L.length ≤ W) (hNW : N + 2 ≤ W) :
    ∃ c' k, Exec P W edgeS c c' k ∧ k ≤ 12 ∧ FrameB BEd c c' ∧ c'.nreg 60031 = eU N L e ∧
      c'.nreg 60032 = eV N L e ∧ c'.nreg 60033 = eKind N nI e := by
  have hwr : wr BEd edgeS = true := by decide
  suffices H : ∃ c' k, Exec P W edgeS c c' k ∧ k ≤ 12 ∧ c'.nreg 60031 = eU N L e ∧
      c'.nreg 60032 = eV N L e ∧ c'.nreg 60033 = eKind N nI e by
    obtain ⟨c', k, ex, hk, a, b, d⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, a, b, d⟩
  unfold edgeS eU eV eKind
  by_cases hs : e < N
  · refine spec_ifLtN_true (by rwa [he, hN]) ?_
    refine spec_seq ?_
    exec_block
    · config_simp; rw [he, hone]; omega
    · refine spec_seq ?_
      by_cases h' : e + 1 < N
      · refine spec_ifLtN_true (by config_simp; rwa [he, hone, hN]) (spec_skip ‹_› ?_)
        refine spec_instr (Exec.constN ‹_› _ _ (by omega)) fun _ => ⟨by omega, ?_, ?_, ?_⟩ <;>
          config_simp <;> simp [hs, h', he, hone]
      · refine spec_ifLtN_false (by config_simp; rwa [he, hone, hN])
          (spec_instr (Exec.constN ‹_› _ 0 (Nat.zero_le _)) fun _ => ?_)
        refine spec_instr (Exec.constN ‹_› _ _ (by omega)) fun _ => ⟨by omega, ?_, ?_, ?_⟩ <;>
          config_simp <;> simp [hs, h', he]
  · refine spec_ifLtN_false (by rwa [he, hN]) ?_
    have hj : e - N < L.length := by omega
    obtain ⟨p1, p2⟩ := hP (e - N) hj
    refine spec_seq ?_
    exec_block
    · config_simp; rw [he, hN, h1]; omega
    · config_simp; rw [he, hN, h2]; omega
    · by_cases h' : e - N < nI
      · refine spec_ifLtN_true (by config_simp; rwa [he, hN, hI])
          (spec_instr (Exec.constN ‹_› _ _ (by omega)) fun _ => ⟨by omega, ?_, ?_, ?_⟩) <;>
          config_simp <;> simp only [he, hN, h1, h2, p1, p2, ite_eq_right hs, ite_eq_left h']
      · refine spec_ifLtN_false (by config_simp; rwa [he, hN, hI])
          (spec_instr (Exec.constN ‹_› _ _ (by omega)) fun _ => ⟨by omega, ?_, ?_, ?_⟩) <;>
          config_simp <;> simp only [he, hN, h1, h2, p1, p2, ite_eq_right hs, ite_eq_right h']

/-! ## The values of the darts -/

/-- The address and the value of the dart array `k` (`0, 1`: vertices, `2, 3`: keys, `4, 5`:
opposite darts; even `k`: dart `2 e`, odd `k`: dart `2 e + 1`). -/
def dvS : ℕ → Stmt
  | 0 => block [.addN 60040 60030 60030, .addN 60040 60040 60050, .copyN 60041 60031]
  | 1 => block [.addN 60040 60030 60030, .addN 60040 60040 60050, .addN 60040 60040 120011,
      .copyN 60041 60032]
  | 2 => .seq (block [.addN 60040 60030 60030, .addN 60040 60040 60051, .subN 60042 60032 60031])
      (.ifLtN 60033 120011 (.instr (.constN 60041 0))
        (.ifLtN 60033 120048 (.instr (.copyN 60041 60042))
          (block [.addN 60041 60034 60034, .subN 60041 60041 120048, .subN 60041 60041 60042])))
  | 3 => .seq (block [.addN 60040 60030 60030, .addN 60040 60040 60051, .addN 60040 60040 120011,
        .subN 60042 60032 60031])
      (.ifLtN 60033 120011 (.instr (.subN 60041 60034 120011))
        (.ifLtN 60033 120048 (block [.subN 60041 60034 60032, .addN 60041 60041 60031])
          (block [.subN 60041 60034 120048, .addN 60041 60041 60042])))
  | 4 => block [.addN 60040 60030 60030, .addN 60040 60040 60052, .addN 60041 60030 60030,
      .addN 60041 60041 120011]
  | _ => block [.addN 60040 60030 60030, .addN 60040 60040 60052, .addN 60040 60040 120011,
      .addN 60041 60030 60030]

/-- The base register of the dart array `k`. -/
def dBase (k : ℕ) : ℕ := if k < 2 then 60050 else if k < 4 then 60051 else 60052

/-- The value of the dart array `k`. -/
def dVal (k N e u v kd : ℕ) : ℕ :=
  if k = 0 then u else if k = 1 then v else if k = 2 then dKey0 N kd u v
  else if k = 3 then dKey1 N kd u v else if k = 4 then 2 * e + 1 else 2 * e

/-- The registers written by `dvS`. -/
def BDV (r : ℕ) : Bool := decide (60040 ≤ r ∧ r ≤ 60042)

theorem dvS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {k : ℕ} (hk : k < 6)
    {N e u v kd base : ℕ} (hb : c.nreg (dBase k) = base) (he : c.nreg 60030 = e)
    (hu : c.nreg 60031 = u) (hv : c.nreg 60032 = v) (hkd : c.nreg 60033 = kd) (hkd2 : kd ≤ 2)
    (hN : c.nreg 60034 = N) (h1 : c.nreg 120011 = 1) (h2 : c.nreg 120048 = 2) (huN : u ≤ N)
    (hvN : v ≤ N) (hNW : 2 * N + 2 ≤ W) (hbW : base + 2 * e + 2 ≤ W) :
    ∃ c' kk, Exec P W (dvS k) c c' kk ∧ kk ≤ 12 ∧ FrameB BDV c c' ∧
      c'.nreg 60040 = base + 2 * e + k % 2 ∧ c'.nreg 60041 = dVal k N e u v kd := by
  have hwr : wr BDV (dvS k) = true := by interval_cases k <;> decide
  suffices H : ∃ c' kk, Exec P W (dvS k) c c' kk ∧ kk ≤ 12 ∧
      c'.nreg 60040 = base + 2 * e + k % 2 ∧ c'.nreg 60041 = dVal k N e u v kd by
    obtain ⟨c', kk, ex, hkk, a, b⟩ := H
    exact ⟨c', kk, ex, hkk, exec_frameB ex hwr, a, b⟩
  interval_cases k <;> simp only [dBase] at hb <;> norm_num at hb <;> unfold dvS dVal
  · exec_block
    · rw [he]; omega
    · config_simp; rw [he, hb]; omega
    · exact ⟨by omega, by config_simp; rw [he, hb]; ring, by config_simp; exact hu⟩
  · exec_block
    · rw [he]; omega
    · config_simp; rw [he, hb]; omega
    · config_simp; rw [he, hb, h1]; omega
    · exact ⟨by omega, by config_simp; rw [he, hb, h1]; ring, by config_simp; exact hv⟩
  · refine spec_seq ?_
    exec_block
    · rw [he]; omega
    · config_simp; rw [he, hb]; omega
    · simp only [dKey0]
      by_cases a0 : kd = 0
      · refine spec_ifLtN_true (by config_simp; rw [hkd, h1]; omega)
          (spec_instr (Exec.constN ‹_› _ _ (Nat.zero_le _)) fun _ => ⟨by omega, ?_, ?_⟩)
        · config_simp; rw [he, hb]; ring
        · config_simp; simp [a0]
      · refine spec_ifLtN_false (by config_simp; rw [hkd, h1]; omega) ?_
        by_cases a1 : kd = 1
        · refine spec_ifLtN_true (by config_simp; rw [hkd, h2]; omega)
            (spec_instr (Exec.copyN ‹_› _ _) fun _ => ⟨by omega, ?_, ?_⟩)
          · config_simp; rw [he, hb]; ring
          · config_simp; rw [hu, hv]; simp [a1]
        · refine spec_ifLtN_false (by config_simp; rw [hkd, h2]; omega) ?_
          exec_block
          · config_simp; rw [hN]; omega
          · refine ⟨by omega, ?_, ?_⟩
            · config_simp; rw [he, hb]; ring
            · config_simp; rw [hN, h2, hu, hv]; simp [a0, a1]; omega
  · refine spec_seq ?_
    exec_block
    · rw [he]; omega
    · config_simp; rw [he, hb]; omega
    · config_simp; rw [he, hb, h1]; omega
    · simp only [dKey1]
      by_cases a0 : kd = 0
      · refine spec_ifLtN_true (by config_simp; rw [hkd, h1]; omega)
          (spec_instr (Exec.subN ‹_› _ _ _) fun _ => ⟨by omega, ?_, ?_⟩)
        · config_simp; rw [he, hb, h1]; ring
        · config_simp; rw [hN, h1]; simp [a0]
      · refine spec_ifLtN_false (by config_simp; rw [hkd, h1]; omega) ?_
        by_cases a1 : kd = 1
        · refine spec_ifLtN_true (by config_simp; rw [hkd, h2]; omega) ?_
          exec_block
          · config_simp; rw [hN, hv, hu]; omega
          · refine ⟨by omega, ?_, ?_⟩
            · config_simp; rw [he, hb, h1]; ring
            · config_simp; rw [hN, hu, hv]; simp [a1]
        · refine spec_ifLtN_false (by config_simp; rw [hkd, h2]; omega) ?_
          exec_block
          · config_simp; rw [hN, h2, hu, hv]; omega
          · refine ⟨by omega, ?_, ?_⟩
            · config_simp; rw [he, hb, h1]; ring
            · config_simp; rw [hN, h2, hu, hv]; simp [a0, a1]
  · exec_block
    · rw [he]; omega
    · config_simp; rw [he, hb]; omega
    · config_simp; rw [he]; omega
    · config_simp; rw [he, h1]; omega
    · exact ⟨by omega, by config_simp; rw [he, hb]; ring, by config_simp; rw [he, h1]; simp; omega⟩
  · exec_block
    · rw [he]; omega
    · config_simp; rw [he, hb]; omega
    · config_simp; rw [he, hb, h1]; omega
    · config_simp; rw [he]; omega
    · exact ⟨by omega, by config_simp; rw [he, hb, h1]; ring, by config_simp; rw [he]; simp; omega⟩

/-! ## One pass over the edges -/

/-- The environment of the passes. -/
structure DartEnv (N nI CH1 CH2 VT E lo : ℕ) (L : List (ℕ × ℕ)) (c : Config) : Prop where
  rN : c.nreg 60034 = N
  rI : c.nreg 60008 = nI
  r1 : c.nreg 60001 = CH1
  r2 : c.nreg 60002 = CH2
  one : c.nreg 120011 = 1
  two : c.nreg 120048 = 2
  rV : c.nreg 60050 = VT
  rK : c.nreg 60051 = VT + 2 * E
  rO : c.nreg 60052 = VT + 4 * E
  rE : c.nreg 60037 = E
  pairs : PairsAt c.nmem CH1 CH2 L
  hE : E = N + L.length
  hC1 : CH1 + L.length ≤ lo
  hC2 : CH2 + L.length ≤ lo
  hlo : lo ≤ VT
  ends : ∀ t, t < L.length → (L.getD t (0, 0)).1 ≤ N ∧ (L.getD t (0, 0)).2 ≤ N
  hI : nI ≤ L.length

/-- The registers the passes keep. -/
def DKeep (r : ℕ) : Bool :=
  decide (r = 60034) || decide (r = 60008) || decide (r = 60001) || decide (r = 60002) ||
    decide (r = 120011) || decide (r = 120048) || decide (60050 ≤ r ∧ r ≤ 60052) ||
    decide (r = 60037)

theorem DartEnv.stable {N nI CH1 CH2 VT E lo : ℕ} {L : List (ℕ × ℕ)} {c c' : Config}
    (h : DartEnv N nI CH1 CH2 VT E lo L c) (hr : ∀ r, DKeep r = true → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < lo → c'.nmem a = c.nmem a) : DartEnv N nI CH1 CH2 VT E lo L c' where
  rN := by rw [hr _ (by decide)]; exact h.rN
  rI := by rw [hr _ (by decide)]; exact h.rI
  r1 := by rw [hr _ (by decide)]; exact h.r1
  r2 := by rw [hr _ (by decide)]; exact h.r2
  one := by rw [hr _ (by decide)]; exact h.one
  two := by rw [hr _ (by decide)]; exact h.two
  rV := by rw [hr _ (by decide)]; exact h.rV
  rK := by rw [hr _ (by decide)]; exact h.rK
  rO := by rw [hr _ (by decide)]; exact h.rO
  rE := by rw [hr _ (by decide)]; exact h.rE
  pairs := PairsAt.congr h.pairs fun t ht => ⟨hm _ (by have := h.hC1; omega),
    hm _ (by have := h.hC2; omega)⟩
  hE := h.hE
  hC1 := h.hC1
  hC2 := h.hC2
  hlo := h.hlo
  ends := h.ends
  hI := h.hI

theorem DKeep_B {r : ℕ} (h : DKeep r = true) : (BEd r || BDV r) = false ∧ r ≠ 60030 := by
  unfold DKeep at h; unfold BEd BDV
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h ⊢
  omega

/-- One pass: the dart array `k` over the edges. -/
def passS (k : ℕ) : Stmt := scatS 60030 60037 120011 60040 60041 (.seq edgeS (dvS k))

/-- The base of the dart array `k`. -/
def dBaseV (VT E k : ℕ) : ℕ := if k < 2 then VT else if k < 4 then VT + 2 * E else VT + 4 * E

theorem passS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {k : ℕ} (hk : k < 6)
    {N nI CH1 CH2 VT E lo : ℕ} {L : List (ℕ × ℕ)} (h : DartEnv N nI CH1 CH2 VT E lo L c)
    (hNW : 2 * N + 2 ≤ W) (hVW : VT + 6 * E + 2 ≤ W) :
    ∃ c' kk, Exec P W (passS k) c c' kk ∧ kk ≤ E * 40 + 3 ∧
      (∀ r, BEd r = false → BDV r = false → r ≠ 60030 → c'.nreg r = c.nreg r) ∧
      (∀ r, BEd r = false → BDV r = false → c'.rreg r = c.rreg r) ∧
      c'.nmem = scat c.nmem (fun e => dBaseV VT E k + 2 * e + k % 2)
        (fun e => dVal k N e (eU N L e) (eV N L e) (eKind N nI e)) E ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ DartEnv N nI CH1 CH2 VT E lo L c' := by
  obtain ⟨c', kk, ex, hkk, r', rr', mm, rm, o, J'⟩ := scatS_exec (P := P) (W := W)
    (ri := 60030) (rn := 60037) (r1 := 120011) (ra := 60040) (rv := 60041)
    (body := .seq edgeS (dvS k)) (B := fun r => BEd r || BDV r) (by decide) (by decide)
    (by decide) (by decide) (by decide) (DartEnv N nI CH1 CH2 VT E lo L) lo
    (fun d d' hJ hr hm => hJ.stable (fun r hr' => hr r (DKeep_B hr').1 (DKeep_B hr').2) hm)
    (n := E) (κ := 36) (fun e => dBaseV VT E k + 2 * e + k % 2)
    (fun e => dVal k N e (eU N L e) (eV N L e) (eKind N nI e))
    (fun i _ => by
      show lo ≤ dBaseV VT E k + 2 * i + k % 2
      have := h.hlo; unfold dBaseV; split_ifs <;> omega)
    (fun i d hi hJ hwd hri => by
      obtain ⟨d₁, k₁, e₁, hk₁, f₁, v1, v2, v3⟩ := edgeS_exec (P := P) hwd hJ.rN hJ.rI hJ.r1 hJ.r2 hJ.one hri
        (by rwa [← hJ.hE]) hJ.pairs (by have := hJ.hC1; have := hJ.hlo; omega)
        (by have := hJ.hC2; have := hJ.hlo; omega) (by omega)
      have K : ∀ r, DKeep r = true → d₁.nreg r = d.nreg r := fun r hr => f₁.1 r (by
        have := (DKeep_B hr).1; simp only [Bool.or_eq_false_iff] at this; exact this.1)
      have hJ₁ := hJ.stable K (fun a _ => by rw [f₁.2.2.1])
      have hkd : eKind N nI i ≤ 2 := by unfold eKind; split_ifs <;> omega
      have huN : eU N L i ≤ N := by
        unfold eU; split_ifs with a
        · omega
        · exact (hJ.ends _ (by rw [hJ.hE] at hi; omega)).1
      have hvN : eV N L i ≤ N := by
        unfold eV; split_ifs with a b
        · omega
        · omega
        · exact (hJ.ends _ (by rw [hJ.hE] at hi; omega)).2
      have hb : d₁.nreg (dBase k) = dBaseV VT E k := by
        unfold dBase dBaseV
        split_ifs
        · exact hJ₁.rV
        · exact hJ₁.rK
        · exact hJ₁.rO
      obtain ⟨d₂, k₂, e₂, hk₂, f₂, a2, b2⟩ := dvS_exec (P := P) (e := i) e₁.wb_right hk hb
        (by rwa [f₁.1 _ (by decide)]) v1 v2 v3 hkd hJ₁.rN hJ₁.one hJ₁.two huN hvN hNW
        (by unfold dBaseV; split_ifs <;> omega)
      have ex : Exec P W (.seq edgeS (dvS k)) d d₂ _ := .seq e₁ e₂
      refine ⟨d₂, _, ex, by omega, (FrameB.mono f₁ fun r hr => by simp [hr]).trans
        (FrameB.mono f₂ fun r hr => by simp [hr]), a2, b2⟩)
    hw h h.rE h.one (by omega)
  exact ⟨c', kk, ex, by nlinarith, fun r a b c'' => r' r (by simp [a, b]) c'',
    fun r a b => rr' r (by simp [a, b]), mm, rm, o, J'⟩

/-! ## The six passes -/

/-- The first `j` passes. -/
def passesS : ℕ → Stmt
  | 0 => .skip
  | j + 1 => .seq (passesS j) (passS j)

/-- The dart arrays `k < j` are written. -/
def DArr (N nI VT E : ℕ) (L : List (ℕ × ℕ)) (j : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ k, k < j → ∀ e, e < E →
    m (dBaseV VT E k + 2 * e + k % 2) = dVal k N e (eU N L e) (eV N L e) (eKind N nI e)

theorem dAddr_ne {VT E k k' e e' : ℕ} (hk : k < 6) (hk' : k' < 6) (he : e < E) (he' : e' < E)
    (hne : k ≠ k' ∨ e ≠ e') :
    dBaseV VT E k + 2 * e + k % 2 ≠ dBaseV VT E k' + 2 * e' + k' % 2 := by
  unfold dBaseV
  interval_cases k <;> interval_cases k' <;> simp <;> omega

theorem dAddr_range {VT E k e : ℕ} (_hk : k < 6) (he : e < E) :
    VT ≤ dBaseV VT E k + 2 * e + k % 2 ∧ dBaseV VT E k + 2 * e + k % 2 < VT + 6 * E := by
  unfold dBaseV; split_ifs <;> omega

/-- **The passes.** -/
theorem passesS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {j : ℕ}
    (hj : j ≤ 6) {N nI CH1 CH2 VT E lo : ℕ} {L : List (ℕ × ℕ)}
    (h : DartEnv N nI CH1 CH2 VT E lo L c) (hNW : 2 * N + 2 ≤ W) (hVW : VT + 6 * E + 2 ≤ W) :
    ∃ c' kk, Exec P W (passesS j) c c' kk ∧ kk ≤ j * (E * 40 + 3) ∧
      (∀ r, BEd r = false → BDV r = false → r ≠ 60030 → c'.nreg r = c.nreg r) ∧
      (∀ r, BEd r = false → BDV r = false → c'.rreg r = c.rreg r) ∧
      DArr N nI VT E L j c'.nmem ∧ (∀ a, (a < VT ∨ VT + 6 * E ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ DartEnv N nI CH1 CH2 VT E lo L c' := by
  induction j with
  | zero =>
    exact ⟨c, 0, .skip hw, by omega, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
      fun k hk => by omega, fun _ _ => rfl, rfl, rfl, h⟩
  | succ j ih =>
    obtain ⟨c₁, k₁, e₁, hk₁, r₁, rr₁, D₁, m₁, rm₁, o₁, J₁⟩ := ih (by omega)
    obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, m₂, rm₂, o₂, J₂⟩ :=
      passS_exec (P := P) e₁.wb_right (k := j) (by omega) J₁ hNW hVW
    refine ⟨c₂, _, .seq e₁ e₂, by rw [Nat.succ_mul]; omega,
      fun r a b c'' => (r₂ r a b c'').trans (r₁ r a b c''),
      fun r a b => (rr₂ r a b).trans (rr₁ r a b), ?_, ?_, rm₂.trans rm₁, o₂.trans o₁, J₂⟩
    · intro k hk e he
      rw [m₂]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [scat_other fun i hi => dAddr_ne (by omega) (by omega) hi he (Or.inl (by omega))]
        exact D₁ k hk e he
      · exact scat_at (g := fun e => dBaseV VT E k + 2 * e + k % 2) he
          fun i hi hei => dAddr_ne (by omega) (by omega) hi he (Or.inr (by omega))
    · intro a ha
      rw [m₂, scat_other fun i hi e => by
        have := dAddr_range (VT := VT) (k := j) (by omega) hi; omega]
      exact m₁ a ha

/-- **The dart arrays**: the tails at `VT`, the keys at `VT + 2 E`, the opposite darts at
`VT + 4 E`. -/
theorem darts_of (B : BookData) (hV : B.Valid) {VT : ℕ} {m : ℕ → ℕ}
    (h : DArr B.N B.I.length VT B.E (B.I ++ B.O) 6 m) {d : ℕ} (hd : d < 2 * B.E) :
    m (VT + d) = View.tail B.N (B.view d) ∧ m (VT + 2 * B.E + d) = View.key B.N (B.view d) ∧
      m (VT + 4 * B.E + d) = oppN d := by
  have he : d / 2 < B.E := by omega
  rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
  · have hd' : d = 2 * (d / 2) := by omega
    obtain ⟨a, b⟩ := view_even B hV he
    have x0 := h 0 (by omega) _ he
    have x2 := h 2 (by omega) _ he
    have x4 := h 4 (by omega) _ he
    simp only [dBaseV, dVal] at x0 x2 x4
    norm_num at x0 x2 x4
    refine ⟨?_, ?_, ?_⟩
    · rw [hd', a, ← x0]
    · rw [hd', b, ← x2]
    · rw [show VT + 4 * B.E + d = VT + 4 * B.E + 2 * (d / 2) by omega, x4]
      unfold oppN; rw [ite_eq_left h2]; omega
  · have hd' : d = 2 * (d / 2) + 1 := by omega
    obtain ⟨a, b⟩ := view_odd B hV he
    have x1 := h 1 (by omega) _ he
    have x3 := h 3 (by omega) _ he
    have x5 := h 5 (by omega) _ he
    simp only [dBaseV, dVal] at x1 x3 x5
    norm_num at x1 x3 x5
    refine ⟨?_, ?_, ?_⟩
    · rw [hd', a, ← x1]; congr 1
    · rw [hd', b, ← x3]; congr 1
    · rw [show VT + 4 * B.E + d = VT + 4 * B.E + 2 * (d / 2) + 1 by omega, x5]
      unfold oppN; rw [ite_eq_right (by omega)]; omega

end

end OracleR

end Chazelle.Core
