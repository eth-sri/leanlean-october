module

public import Chazelle.Core.OraclePrepRotSort
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Lemma 3.6 (WP-H), preprocessing part 22: the rotation array on the RAM

With the darts sorted (`s t` at `Sb + t`) by their vertices (`G d` at `VT + d`) and keys, `fpS`
writes the first position of each vertex into the array at `FPb` (a scatter over the positions in
decreasing order), and `rotS` writes `rotN` of every position `t` at `ROTb + s t`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-- The registers written by the rotation bodies. -/
def BR (r : ℕ) : Bool := decide (60064 ≤ r ∧ r ≤ 60070)

/-! ## The first positions -/

/-- The body of `fpS`: address `FPb + G (s (M - 1 - i))`, value `M - 1 - i`. -/
def fpBody : Stmt :=
  block [.subN 60065 60060 60063, .subN 60065 60065 120011, .addN 60067 60007 60065,
    .loadN 60067 60067, .addN 60067 60050 60067, .loadN 60067 60067, .addN 60064 60061 60067]

theorem fpBody_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {Sb VT M FPb i : ℕ} (h7 : c.nreg 60007 = Sb) (h50 : c.nreg 60050 = VT)
    (h60 : c.nreg 60060 = M) (h61 : c.nreg 60061 = FPb) (h1 : c.nreg 120011 = 1)
    (hi : c.nreg 60063 = i) (hiM : i < M) (hSW : Sb + M ≤ W) (hVW : VT + M ≤ W)
    (hs : c.nmem (Sb + (M - 1 - i)) < M)
    (hFW : FPb + c.nmem (VT + c.nmem (Sb + (M - 1 - i))) ≤ W) :
    ∃ c' k, Exec P W fpBody c c' k ∧ k ≤ 7 ∧ FrameB BR c c' ∧
      c'.nreg 60064 = FPb + c.nmem (VT + c.nmem (Sb + (M - 1 - i))) ∧
      c'.nreg 60065 = M - 1 - i := by
  have hwr : wr BR fpBody = true := by decide
  suffices H : ∃ c' k, Exec P W fpBody c c' k ∧ k ≤ 7 ∧
      c'.nreg 60064 = FPb + c.nmem (VT + c.nmem (Sb + (M - 1 - i))) ∧
      c'.nreg 60065 = M - 1 - i by
    obtain ⟨c', k, ex, hk, a, b⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, a, b⟩
  unfold fpBody
  exec_block
  · config_simp; rwo [h7, h60, hi, h1]
  · config_simp; rwo [h7, h60, hi, h1, h50, show M - i - 1 = M - 1 - i by omega]
  · config_simp; rwx [h7, h60, hi, h1, h50, h61, show M - i - 1 = M - 1 - i by omega]
  · exact ⟨by omega, by config_simp; rw [h7, h60, hi, h1, h50, h61,
      show M - i - 1 = M - 1 - i by omega], by config_simp; rwo [h60, hi, h1]⟩

/-- The environment of `fpS`. -/
def FPJ (Sb VT M FPb : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop :=
  c.nreg 60007 = Sb ∧ c.nreg 60050 = VT ∧ c.nreg 60060 = M ∧ c.nreg 60061 = FPb ∧
    c.nreg 120011 = 1 ∧ ∀ a, a < FPb → c.nmem a = m₀ a

/-- **The first positions**: a scatter over `i < M`. -/
def fpS : Stmt := scatS 60063 60060 120011 60064 60065 fpBody

theorem fpS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {Sb VT M FPb N : ℕ} (hJ : FPJ Sb VT M FPb c.nmem c) (hSF : Sb + M ≤ FPb) (hVF : VT + M ≤ FPb)
    (hs : ∀ t, t < M → c.nmem (Sb + t) < M) (hG : ∀ d, d < M → c.nmem (VT + d) < N)
    (hFW : FPb + N ≤ W) :
    ∃ c' k, Exec P W fpS c c' k ∧ k ≤ M * 11 + 3 ∧
      (∀ r, BR r = false → r ≠ 60063 → c'.nreg r = c.nreg r) ∧
      (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.nmem = scat c.nmem (fun i => FPb + c.nmem (VT + c.nmem (Sb + (M - 1 - i))))
        (fun i => M - 1 - i) M ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ FPJ Sb VT M FPb c.nmem c' := by
  obtain ⟨c', k, ex, hk, r', rr', mm, rm, o, J', -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60063) (rn := 60060) (r1 := 120011) (ra := 60064) (rv := 60065) (body := fpBody)
    (B := BR) (by decide) (by decide) (by decide) (by decide) (by decide)
    (FPJ Sb VT M FPb c.nmem) FPb
    (fun d d' hJ hr hm => ⟨by rw [hr _ (by decide) (by decide)]; exact hJ.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.2.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.2.2.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.2.2.2.1,
      fun a ha => by rw [hm a ha]; exact hJ.2.2.2.2.2 a ha⟩)
    (n := M) (κ := 7) (fun i => FPb + c.nmem (VT + c.nmem (Sb + (M - 1 - i))))
    (fun i => M - 1 - i) (fun i _ => by omega)
    (fun i d hi hJd hwd hri => by
      obtain ⟨a7, a50, a60, a61, a1, am⟩ := hJd
      have e1 : d.nmem (Sb + (M - 1 - i)) = c.nmem (Sb + (M - 1 - i)) := am _ (by omega)
      have hs' := hs (M - 1 - i) (by omega)
      have e2 : d.nmem (VT + d.nmem (Sb + (M - 1 - i))) =
          c.nmem (VT + c.nmem (Sb + (M - 1 - i))) := by rw [e1]; exact am _ (by omega)
      have hg' := hG _ hs'
      obtain ⟨d', k, ex, hk, F, v1, v2⟩ := fpBody_exec hwd a7 a50 a60 a61 a1 hri hi
        (by omega) (by omega) (by rwx [e1]) (by rwo [e2])
      exact ⟨d', k, ex, hk, F, by rw [v1, e2], v2⟩)
    hw hJ hJ.2.2.1 hJ.2.2.2.2.1 (by omega)
  exact ⟨c', k, ex, by nlinarith, r', rr', mm, rm, o, J'⟩

theorem fpN_spec' {M : ℕ} {G s : ℕ → ℕ} {t : ℕ} (ht : t < M) :
    fpN M G s (G (s t)) < M ∧ G (s (fpN M G s (G (s t)))) = G (s t) ∧
      ∀ t', t' < M → G (s t') = G (s t) → fpN M G s (G (s t)) ≤ t' := by
  classical
  have hex : ∃ t', t' < M ∧ G (s t') = G (s t) := ⟨t, ht, rfl⟩
  unfold fpN
  rw [dite_eq_left hex]
  obtain ⟨a, b⟩ := Nat.find_spec hex
  exact ⟨a, b, fun t' ht' e => Nat.find_min' hex ⟨ht', e⟩⟩

theorem fpN_congr {M : ℕ} {G s G' s' : ℕ → ℕ} (h : ∀ t, t < M → G (s t) = G' (s' t)) (v : ℕ) :
    fpN M G s v = fpN M G' s' v := by
  classical
  by_cases hex : ∃ t, t < M ∧ G (s t) = v
  · obtain ⟨t, ht, rfl⟩ := hex
    have e := h t ht
    obtain ⟨a1, a2, a3⟩ := fpN_spec' (G := G) (s := s) ht
    obtain ⟨b1, b2, b3⟩ := fpN_spec' (G := G') (s := s') ht
    conv_rhs => rw [e]
    exact le_antisymm (a3 _ b1 (by rw [h _ b1, b2, e]))
      (b3 _ a1 (by rw [← h _ a1, a2, e]))
  · have hex' : ¬ ∃ t, t < M ∧ G' (s' t) = v := fun ⟨t, ht, e⟩ => hex ⟨t, ht, by rw [h t ht]; exact e⟩
    unfold fpN; rw [dite_eq_right hex, dite_eq_right hex']

/-- **The first-position array** holds `fpN`. -/
theorem fp_scat {M FPb : ℕ} {G s g : ℕ → ℕ} (hg : ∀ i, i < M → g i = FPb + G (s (M - 1 - i)))
    (m : ℕ → ℕ) {t : ℕ} (ht : t < M) :
    scat m g (fun i => M - 1 - i) M (FPb + G (s t)) = fpN M G s (G (s t)) := by
  obtain ⟨f1, f2, f3⟩ := fpN_spec' (G := G) (s := s) ht
  set t₀ := fpN M G s (G (s t))
  have ha : FPb + G (s t) = g (M - 1 - t₀) := by
    rw [hg _ (by omega), show M - 1 - (M - 1 - t₀) = t₀ by omega, f2]
  rw [ha, scat_at (by omega) fun j hj hij e => by
    rw [hg _ hj, hg _ (by omega), show M - 1 - (M - 1 - t₀) = t₀ by omega, f2] at e
    have := f3 (M - 1 - j) (by omega) (by omega)
    omega]
  omega

theorem rotN_congr {M : ℕ} {G s G' s' : ℕ → ℕ} (hs : ∀ t, t < M → s t = s' t)
    (h : ∀ t, t < M → G (s t) = G' (s' t)) {t : ℕ} (ht : t < M) :
    rotN M G s t = rotN M G' s' t := by
  unfold rotN
  have e1 := fpN_congr h (G (s t))
  have hf := (fpN_spec' (G := G) (s := s) ht).1
  by_cases hc : t + 1 < M ∧ G (s (t + 1)) = G (s t)
  · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by rw [← h _ hc.1, ← h _ ht]; exact hc.2⟩, hs _ hc.1]
  · rw [ite_eq_right hc, ite_eq_right (fun hc' => hc ⟨hc'.1, by rw [h _ hc'.1, h _ ht]; exact hc'.2⟩),
      ← h _ ht, ← e1, hs _ hf]

theorem SortedSeq.congr {pr pr' s : ℕ → ℕ} {n : ℕ} (h : SortedSeq (fun i => (pr i, pr' i)) s n)
    {q q' : ℕ → ℕ} (hq : ∀ t, t < n → pr (s t) = q (s t) ∧ pr' (s t) = q' (s t)) :
    SortedSeq (fun i => (q i, q' i)) s n := fun t t' htt ht' => by
  have := h t t' htt ht'
  simp at this ⊢
  rw [(hq t (by omega)).1, (hq t (by omega)).2, (hq t' ht').1, (hq t' ht').2] at this
  exact this

/-! ## The rotation -/

/-- `s t`, `ROTb + s t`, `G (s t)`, `t + 1`. -/
def rPre : Stmt :=
  block [.addN 60066 60007 60063, .loadN 60068 60066, .addN 60064 60062 60068,
    .addN 60067 60050 60068, .loadN 60067 60067, .addN 60069 60063 120011]

/-- `s (t + 1)` in `60065`, `G (s (t + 1))` in `60070`. -/
def rNext : Stmt :=
  block [.addN 60066 60066 120011, .loadN 60065 60066, .addN 60070 60050 60065,
    .loadN 60070 60070]

/-- `s (FP (G (s t)))` in `60065`. -/
def rFb : Stmt :=
  block [.addN 60070 60061 60067, .loadN 60070 60070, .addN 60070 60007 60070,
    .loadN 60065 60070]

/-- The body of `rotS`. -/
def rotBody : Stmt :=
  .seq rPre (.ifLtN 60069 60060
    (.seq rNext (.ifLtN 60070 60067 rFb (.ifLtN 60067 60070 rFb .skip))) rFb)

/-- The environment of `rotS` (memory `m₁` below `ROTb`). -/
def RotJ (Sb VT M FPb ROTb : ℕ) (m₁ : ℕ → ℕ) (c : Config) : Prop :=
  c.nreg 60007 = Sb ∧ c.nreg 60050 = VT ∧ c.nreg 60060 = M ∧ c.nreg 60061 = FPb ∧
    c.nreg 60062 = ROTb ∧ c.nreg 120011 = 1 ∧ ∀ a, a < ROTb → c.nmem a = m₁ a

theorem rPre_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {Sb VT ROTb t : ℕ} (h7 : c.nreg 60007 = Sb) (h50 : c.nreg 60050 = VT)
    (h62 : c.nreg 60062 = ROTb) (h1 : c.nreg 120011 = 1) (hi : c.nreg 60063 = t)
    (hb1 : Sb + t + 1 ≤ W) (hb2 : ROTb + c.nmem (Sb + t) ≤ W) (hb3 : VT + c.nmem (Sb + t) ≤ W) :
    ∃ c' k, Exec P W rPre c c' k ∧ k = 6 ∧
      FrameB (fun r => decide (r = 60064 ∨ r = 60066 ∨ r = 60067 ∨ r = 60068 ∨ r = 60069)) c c' ∧
      c'.nreg 60066 = Sb + t ∧ c'.nreg 60064 = ROTb + c.nmem (Sb + t) ∧
      c'.nreg 60067 = c.nmem (VT + c.nmem (Sb + t)) ∧ c'.nreg 60069 = t + 1 := by
  have hwr : wr (fun r => decide (r = 60064 ∨ r = 60066 ∨ r = 60067 ∨ r = 60068 ∨ r = 60069))
    rPre = true := by decide
  suffices H : ∃ c' k, Exec P W rPre c c' k ∧ k = 6 ∧
      c'.nreg 60066 = Sb + t ∧ c'.nreg 60064 = ROTb + c.nmem (Sb + t) ∧
      c'.nreg 60067 = c.nmem (VT + c.nmem (Sb + t)) ∧ c'.nreg 60069 = t + 1 by
    obtain ⟨c', k, ex, hk, a, b, d, e⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, a, b, d, e⟩
  unfold rPre
  exec_block
  · rwo [h7, hi]
  · config_simp; rwo [h7, hi, h62]
  · config_simp; rwo [h7, hi, h50]
  · config_simp; rwo [hi, h1]
  · exact ⟨rfl, by config_simp; rw [h7, hi], by config_simp; rw [h7, hi, h62],
      by config_simp; rw [h7, hi, h50], by config_simp; rw [hi, h1]⟩

theorem rNext_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {VT a : ℕ} (h50 : c.nreg 60050 = VT) (h1 : c.nreg 120011 = 1) (h66 : c.nreg 60066 = a)
    (hb1 : a + 1 ≤ W) (hb2 : VT + c.nmem (a + 1) ≤ W) :
    ∃ c' k, Exec P W rNext c c' k ∧ k = 4 ∧
      FrameB (fun r => decide (r = 60065 ∨ r = 60066 ∨ r = 60070)) c c' ∧
      c'.nreg 60065 = c.nmem (a + 1) ∧ c'.nreg 60070 = c.nmem (VT + c.nmem (a + 1)) := by
  have hwr : wr (fun r => decide (r = 60065 ∨ r = 60066 ∨ r = 60070)) rNext = true := by decide
  suffices H : ∃ c' k, Exec P W rNext c c' k ∧ k = 4 ∧
      c'.nreg 60065 = c.nmem (a + 1) ∧ c'.nreg 60070 = c.nmem (VT + c.nmem (a + 1)) by
    obtain ⟨c', k, ex, hk, x, y⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, x, y⟩
  unfold rNext
  exec_block
  · rwo [h66, h1]
  · config_simp; rwo [h66, h1, h50]
  · exact ⟨rfl, by config_simp; rw [h66, h1], by config_simp; rw [h66, h1, h50]⟩

theorem rFb_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {Sb FPb g : ℕ} (h7 : c.nreg 60007 = Sb) (h61 : c.nreg 60061 = FPb) (h67 : c.nreg 60067 = g)
    (hb1 : FPb + g ≤ W) (hb2 : Sb + c.nmem (FPb + g) ≤ W) :
    ∃ c' k, Exec P W rFb c c' k ∧ k = 4 ∧
      FrameB (fun r => decide (r = 60065 ∨ r = 60070)) c c' ∧
      c'.nreg 60065 = c.nmem (Sb + c.nmem (FPb + g)) := by
  have hwr : wr (fun r => decide (r = 60065 ∨ r = 60070)) rFb = true := by decide
  suffices H : ∃ c' k, Exec P W rFb c c' k ∧ k = 4 ∧
      c'.nreg 60065 = c.nmem (Sb + c.nmem (FPb + g)) by
    obtain ⟨c', k, ex, hk, x⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, x⟩
  unfold rFb
  exec_block
  · rwo [h61, h67]
  · config_simp; rwo [h61, h67, h7]
  · exact ⟨rfl, by config_simp; rw [h61, h67, h7]⟩

theorem rotBody_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {Sb VT M FPb ROTb N t : ℕ} {m₁ : ℕ → ℕ} (hJ : RotJ Sb VT M FPb ROTb m₁ c)
    (hi : c.nreg 60063 = t) (ht : t < M) (hSR : Sb + M ≤ ROTb) (hVR : VT + M ≤ ROTb)
    (hFR : FPb + N ≤ ROTb) (hRW : ROTb + M ≤ W)
    (hs : ∀ t, t < M → m₁ (Sb + t) < M) (hG : ∀ d, d < M → m₁ (VT + d) < N)
    (hfp : ∀ t, t < M → m₁ (FPb + m₁ (VT + m₁ (Sb + t))) =
      fpN M (fun d => m₁ (VT + d)) (fun t => m₁ (Sb + t)) (m₁ (VT + m₁ (Sb + t))))
    (hfpl : ∀ t, t < M → fpN M (fun d => m₁ (VT + d)) (fun t => m₁ (Sb + t))
      (m₁ (VT + m₁ (Sb + t))) < M) :
    ∃ c' k, Exec P W rotBody c c' k ∧ k ≤ 24 ∧ FrameB BR c c' ∧
      c'.nreg 60064 = ROTb + m₁ (Sb + t) ∧
      c'.nreg 60065 = rotN M (fun d => m₁ (VT + d)) (fun t => m₁ (Sb + t)) t := by
  obtain ⟨a7, a50, a60, a61, a62, a1, am⟩ := hJ
  have hwr : wr BR rotBody = true := by decide
  suffices H : ∃ c' k, Exec P W rotBody c c' k ∧ k ≤ 24 ∧
      c'.nreg 60064 = ROTb + m₁ (Sb + t) ∧
      c'.nreg 60065 = rotN M (fun d => m₁ (VT + d)) (fun t => m₁ (Sb + t)) t by
    obtain ⟨c', k, ex, hk, a, b⟩ := H
    exact ⟨c', k, ex, hk, exec_frameB ex hwr, a, b⟩
  have mS : ∀ u, u < M → c.nmem (Sb + u) = m₁ (Sb + u) := fun u hu => am _ (by omega)
  have mV : ∀ d, d < M → c.nmem (VT + d) = m₁ (VT + d) := fun d hd => am _ (by omega)
  have mF : ∀ v, v < N → c.nmem (FPb + v) = m₁ (FPb + v) := fun v hv => am _ (by omega)
  have hst := hs t ht
  have hGt := hG _ hst
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, p66, p64, p67, p69⟩ := rPre_exec (P := P) hw a7 a50 a62 a1 hi
    (by omega) (by rwo [mS t ht]) (by rwo [mS t ht])
  rw [mS t ht] at p64 p67
  rw [mV _ hst] at p67
  have K₁ : ∀ r, r = 60007 ∨ r = 60050 ∨ r = 60060 ∨ r = 60061 ∨ r = 120011 →
      c₁.nreg r = c.nreg r := fun r hr => F₁.1 r (by sio only [decide_eq_false_iff_not])
  have m₁e  := F₁.2.2.1
  -- the fallback: `s (fpN (G (s t)))`
  have fb : ∀ d, WordsBounded W d → d.nmem = c.nmem → d.nreg 60007 = Sb → d.nreg 60061 = FPb →
      d.nreg 60067 = m₁ (VT + m₁ (Sb + t)) → d.nreg 60064 = ROTb + m₁ (Sb + t) →
      ∃ d' k, Exec P W rFb d d' k ∧ k = 4 ∧ d'.nreg 60064 = ROTb + m₁ (Sb + t) ∧
        d'.nreg 60065 = m₁ (Sb + fpN M (fun d => m₁ (VT + d)) (fun t => m₁ (Sb + t))
          (m₁ (VT + m₁ (Sb + t)))) := by
    intro d hwd hm h7 h61 h67 h64
    have q1 : d.nmem (FPb + m₁ (VT + m₁ (Sb + t))) =
        fpN M (fun d => m₁ (VT + d)) (fun t => m₁ (Sb + t)) (m₁ (VT + m₁ (Sb + t))) := by
      rw [hm, mF _ hGt, hfp t ht]
    obtain ⟨d', k, ex, hk, F, v⟩ := rFb_exec (P := P) hwd h7 h61 h67 (by omega)
      (by rw [q1]; have := hfpl t ht; omega)
    refine ⟨d', k, ex, hk, by rw [F.1 _ (by decide), h64], ?_⟩
    rw [v, q1, hm, mS _ (hfpl t ht)]
  unfold rotBody
  by_cases hn : t + 1 < M
  · have hs1 := hs (t + 1) hn
    have hG1 := hG _ hs1
    obtain ⟨c₂, k₂, e₂, hk₂, F₂, x65, x70⟩ := rNext_exec (P := P) e₁.wb_right
      (by rw [K₁ _ (by omega), a50]) (by rw [K₁ _ (by omega), a1]) p66 (by omega)
      (by rwo [m₁e, show Sb + t + 1 = Sb + (t + 1) by omega, mS _ hn])
    rw [m₁e, show Sb + t + 1 = Sb + (t + 1) by omega, mS _ hn] at x65 x70
    rw [mV _ hs1] at x70
    have K₂ : ∀ r, r = 60007 ∨ r = 60061 ∨ r = 60064 ∨ r = 60067 →
        c₂.nreg r = c₁.nreg r := fun r hr => F₂.1 r (by sio only [decide_eq_false_iff_not])
    have hm₂  := F₂.2.2.1.trans m₁e
    have b7 : c₂.nreg 60007 = Sb := by rw [K₂ _ (by omega), K₁ _ (by omega), a7]
    have b61 : c₂.nreg 60061 = FPb := by rw [K₂ _ (by omega), K₁ _ (by omega), a61]
    have b67 : c₂.nreg 60067 = m₁ (VT + m₁ (Sb + t)) := by rw [K₂ _ (by omega), p67]
    have b64 : c₂.nreg 60064 = ROTb + m₁ (Sb + t) := by rw [K₂ _ (by omega), p64]
    have hrot : rotN M (fun d => m₁ (VT + d)) (fun t => m₁ (Sb + t)) t =
        if m₁ (VT + m₁ (Sb + (t + 1))) = m₁ (VT + m₁ (Sb + t)) then m₁ (Sb + (t + 1)) else
          m₁ (Sb + fpN M (fun d => m₁ (VT + d)) (fun t => m₁ (Sb + t))
            (m₁ (VT + m₁ (Sb + t)))) := by
      unfold rotN; simp [hn, true_and]
    have hc1 : c₁.nreg 60069 < c₁.nreg 60060 := by rwx [p69, K₁ _ (by omega), a60]
    rcases lt_trichotomy (m₁ (VT + m₁ (Sb + (t + 1)))) (m₁ (VT + m₁ (Sb + t))) with h | h | h
    · obtain ⟨c₃, k₃, e₃, hk₃, v64, v65⟩ := fb c₂ e₂.wb_right hm₂ b7 b61 b67 b64
      refine ⟨c₃, _, .seq e₁ (.ifLtN_true hc1 (.seq e₂ (.ifLtN_true (by rwx [x70, b67])
        e₃))), by omega, v64, by rw [v65, hrot, ite_eq_right (by omega)]⟩
    · refine ⟨c₂, _, .seq e₁ (.ifLtN_true hc1 (.seq e₂ (.ifLtN_false (by rwo [x70, b67])
        (.ifLtN_false (by rwo [x70, b67]) (.skip e₂.wb_right))))), by omega, b64,
        by rw [x65, hrot, ite_eq_left h]⟩
    · obtain ⟨c₃, k₃, e₃, hk₃, v64, v65⟩ := fb c₂ e₂.wb_right hm₂ b7 b61 b67 b64
      refine ⟨c₃, _, .seq e₁ (.ifLtN_true hc1 (.seq e₂ (.ifLtN_false (by rwo [x70, b67])
        (.ifLtN_true (by rwx [x70, b67]) e₃)))), by omega, v64,
        by rw [v65, hrot, ite_eq_right (by omega)]⟩
  · have hc1 : ¬ c₁.nreg 60069 < c₁.nreg 60060 := by rwx [p69, K₁ _ (by omega), a60]
    obtain ⟨c₃, k₃, e₃, hk₃, v64, v65⟩ := fb c₁ e₁.wb_right m₁e
      (by rw [K₁ _ (by omega), a7]) (by rw [K₁ _ (by omega), a61]) p67 p64
    refine ⟨c₃, _, .seq e₁ (.ifLtN_false hc1 e₃), by omega, v64, ?_⟩
    rw [v65]; unfold rotN; rw [ite_eq_right (by omega)]

/-- **The rotation**: a scatter over the positions. -/
def rotS : Stmt := scatS 60063 60060 120011 60064 60065 rotBody

theorem rotS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {Sb VT M FPb ROTb N : ℕ} (hJ : RotJ Sb VT M FPb ROTb c.nmem c)
    (hSR : Sb + M ≤ ROTb) (hVR : VT + M ≤ ROTb)
    (hFR : FPb + N ≤ ROTb) (hRW : ROTb + M ≤ W)
    (hs : ∀ t, t < M → c.nmem (Sb + t) < M) (hG : ∀ d, d < M → c.nmem (VT + d) < N)
    (hfp : ∀ t, t < M → c.nmem (FPb + c.nmem (VT + c.nmem (Sb + t))) =
      fpN M (fun d => c.nmem (VT + d)) (fun t => c.nmem (Sb + t)) (c.nmem (VT + c.nmem (Sb + t))))
    (hfpl : ∀ t, t < M → fpN M (fun d => c.nmem (VT + d)) (fun t => c.nmem (Sb + t))
      (c.nmem (VT + c.nmem (Sb + t))) < M) :
    ∃ c' k, Exec P W rotS c c' k ∧ k ≤ M * 28 + 3 ∧
      (∀ r, BR r = false → r ≠ 60063 → c'.nreg r = c.nreg r) ∧
      (∀ r, BR r = false → c'.rreg r = c.rreg r) ∧
      c'.nmem = scat c.nmem (fun t => ROTb + c.nmem (Sb + t))
        (fun t => rotN M (fun d => c.nmem (VT + d)) (fun t => c.nmem (Sb + t)) t) M ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ RotJ Sb VT M FPb ROTb c.nmem c' := by
  obtain ⟨c', k, ex, hk, r', rr', mm, rm, o, J', -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60063) (rn := 60060) (r1 := 120011) (ra := 60064) (rv := 60065) (body := rotBody)
    (B := BR) (by decide) (by decide) (by decide) (by decide) (by decide)
    (RotJ Sb VT M FPb ROTb c.nmem) ROTb
    (fun d d' hJ hr hm => ⟨by rw [hr _ (by decide) (by decide)]; exact hJ.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.2.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.2.2.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.2.2.2.1,
      by rw [hr _ (by decide) (by decide)]; exact hJ.2.2.2.2.2.1,
      fun a ha => by rw [hm a ha]; exact hJ.2.2.2.2.2.2 a ha⟩)
    (n := M) (κ := 24) (fun t => ROTb + c.nmem (Sb + t))
    (fun t => rotN M (fun d => c.nmem (VT + d)) (fun t => c.nmem (Sb + t)) t) (fun i _ => by omega)
    (fun i d hi hJd hwd hri => by
      obtain ⟨d', k, ex, hk, F, v1, v2⟩ := rotBody_exec hwd hJd hri hi hSR hVR hFR hRW hs hG hfp hfpl
      exact ⟨d', k, ex, hk, F, v1, v2⟩)
    hw hJ hJ.2.2.1 hJ.2.2.2.2.2.1 (by omega)
  exact ⟨c', k, ex, by nlinarith, r', rr', mm, rm, o, J'⟩

end

end OracleR

end Chazelle.Core
