module

public import Chazelle.Core.SweepEvKey2Lab

/-!
# The sweep (WP-D), stage 3: the next key (task K), skipping the stops at the key

`skipS next`: if the stop `sP` is at the offset of the key `(kE, kH)` (compared by `callOff`),
its labels are appended (`stopLab`), `sP` is incremented and `next` runs.  Since there are at most
two stops at one offset, `skipS (skipS skip)` skips all of them: `skip2_irs` (`SkDone`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-- **Skip the stop `sP` if it is at the key**, then run `next`. -/
def skipS (next : Stmt) : Stmt :=
  .ifLtN sP sC
    (.seq (block ldStopL) (.seq (callOff (sw 2) kE kH kqSE kqSH cGW kqO)
      (.ifLtN K0 kqO .skip (.seq stopLab (.seq (block [.addN sP sP K1]) next)))))
    .skip

/-- The registers the skipping writes. -/
def SkR (r : ℕ) : Prop := r = sP ∨ r = kqSE ∨ r = kqSH ∨ r = kqO ∨ r = kqO + 1 ∨ KStR r

/-- **The context of the skipping**: `c` is the configuration at the start of the next-key step,
`d₀` the one at the start of the skipping. -/
structure SkCtx (P : Polygon) (J : Merge.Junction) (c d₀ : Config) : Prop where
  hsP : d₀.nreg sP = c.nreg sP
  hsC : d₀.nreg sC = c.nreg sC
  hsB : d₀.nreg sB = c.nreg sB
  haB : d₀.nreg aB = c.nreg aB
  hA : c.nreg ALLOC ≤ d₀.nreg ALLOC
  hm : ∀ x, x < c.nreg ALLOC → d₀.nmem x = c.nmem x
  hpk : PosW P J (d₀.nreg kE) (d₀.nreg kH)
  hmin : c.nreg sP < c.nreg sC → offK P J (d₀.nreg kE) (d₀.nreg kH) ≤
    offK P J (stopE c (c.nreg sP)) (stopH c (c.nreg sP))
  hps : ∀ i, i < c.nreg sC → PosW P J (stopE c i) (stopH c i)
  hsort : ∀ i i', i ≤ i' → i' < c.nreg sC →
    offK P J (stopE c i) (stopH c i) ≤ offK P J (stopE c i') (stopH c i')
  htwo : ∀ i, i + 2 < c.nreg sC →
    offK P J (stopE c i) (stopH c i) < offK P J (stopE c (i + 2)) (stopH c (i + 2))
  hsBA : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC
  haBA : c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC

/-- **The invariant of the skipping** after `j` skipped stops. -/
def SkInv (P : Polygon) (J : Merge.Junction) (c d₀ d : Config) (j : ℕ) : Prop :=
  EFr SkR d₀ d ∧ d.nreg sP = c.nreg sP + j ∧ c.nreg sP + j ≤ c.nreg sC ∧ j ≤ 2 ∧
  (∀ i, c.nreg sP ≤ i → i < c.nreg sP + j →
    offK P J (stopE c i) (stopH c i) = offK P J (d₀.nreg kE) (d₀.nreg kH)) ∧
  d.nreg kqN ≤ 4 ∧
  lblOf d kqN kqL = addLs (lblOf d₀ kqN kqL)
    ((List.range' (c.nreg sP) j).flatMap (stopLabs c.nmem (c.nreg aB))) ∧
  d.nreg kqA ≤ 1 ∧
  (d.nreg kqA = 1 ↔ ∃ i, c.nreg sP ≤ i ∧ i < c.nreg sP + j ∧ c.nmem (c.nreg aB + 5 * i) = 1)

/-- **The end of the skipping**: the next stop is not at the key. -/
def SkDone (P : Polygon) (J : Merge.Junction) (c d₀ d : Config) : Prop :=
  ∃ j, SkInv P J c d₀ d j ∧ (d.nreg sP < c.nreg sC →
    offK P J (stopE c (d.nreg sP)) (stopH c (d.nreg sP)) ≠ offK P J (d₀.nreg kE) (d₀.nreg kH))

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c d₀ d : Config} {J : Merge.Junction} {N₁ N₂ : NF}

theorem kqGW_lt (J : Merge.Junction) : gW J < (chainModel J.whole).W.n := by
  unfold gW; rw [cm_n]; have := tpos_lt J.whole J.m₁; omega

theorem stopLabs_congr {m m' : ℕ → ℕ} {A i : ℕ} (h : ∀ t, t < 4 → m' (A + 5 * i + t) = m (A + 5 * i + t)) :
    stopLabs m' A i = stopLabs m A i := by
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num)
  simp only [Nat.add_zero] at h0
  unfold stopLabs
  rw [h0, h1]
  split_ifs
  · apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    have := h (2 + t) (by omega)
    rw [← Nat.add_assoc] at this
    exact this
  · rfl

theorem skInv_zero (hS : SkCtx P J c d₀) (hsC : c.nreg sP ≤ c.nreg sC) (hN : d₀.nreg kqN ≤ 4)
    (hA : d₀.nreg kqA = 0) : SkInv P J c d₀ d₀ 0 :=
  ⟨EFr.refl _ _, by rw [hS.hsP]; rfl, by omega, by norm_num, fun i h1 h2 => by omega, hN,
    by simp [addLs], by omega, ⟨fun h => by omega, fun ⟨i, h1, h2, _⟩ => by omega⟩⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **One skip.** -/
theorem skipS_irs {next : Stmt} {K : ℕ} {Q : Config → Prop} {j : ℕ}
    (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hS : SkCtx P J c d₀) (hId : IInv W c₀ d)
    (hj1 : j ≤ 1) (hj : SkInv P J c d₀ d j) (hroom : d.nreg ALLOC + 11200 ≤ W)
    (hnext : ∀ d', IInv W c₀ d' → d'.nreg ALLOC ≤ d.nreg ALLOC + 11200 →
      SkInv P J c d₀ d' (j + 1) → IRS P W c₀ next d' K Q)
    (hstop : ∀ d', SkDone P J c d₀ d' → Q d') :
    IRS P W c₀ (skipS next) d (11200 + K) Q := by
  obtain ⟨fr, hsP, hjC, hj2, hoff, hN, hlb, hA1, hAiff⟩ := hj
  have nSk : ∀ r, (r = sC ∨ r = sB ∨ r = aB ∨ r = kE ∨ r = kH) → ¬ SkR r ∧ 240000 ≤ r ∧ r < 250000 :=
    fun r hr => by
      simp only [sC, sB, aB, kE, kH, sw] at hr
      exact ⟨by simp only [SkR, KStR, LblR]; kqr, by kqr, by kqr⟩
  have kp : ∀ r, (r = sC ∨ r = sB ∨ r = aB ∨ r = kE ∨ r = kH) → d.nreg r = d₀.nreg r :=
    fun r hr => fr.kkeep (nSk r hr).1 (nSk r hr).2
  have eSC : d.nreg sC = c.nreg sC := (kp _ (Or.inl rfl)).trans hS.hsC
  have eSB : d.nreg sB = c.nreg sB := (kp _ (Or.inr (Or.inl rfl))).trans hS.hsB
  have eAB : d.nreg aB = c.nreg aB := (kp _ (Or.inr (Or.inr (Or.inl rfl)))).trans hS.haB
  have eKE : d.nreg kE = d₀.nreg kE := kp _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have eKH : d.nreg kH = d₀.nreg kH := kp _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hAd : c.nreg ALLOC ≤ d.nreg ALLOC := hS.hA.trans fr.2.1
  have hmem : ∀ x, x < c.nreg ALLOC → d.nmem x = c.nmem x := fun x hx =>
    (fr.2.2 x (lt_of_lt_of_le hx hS.hA)).trans (hS.hm x hx)
  have hKd := E.hK.fix hId
  have hW4 : 4 ≤ W := by omega
  set o' := offK P J (d₀.nreg kE) (d₀.nreg kH) with ho'
  unfold skipS
  by_cases hsd : d.nreg sP < d.nreg sC
  · have hs : c.nreg sP + j < c.nreg sC := by rw [hsP, eSC] at hsd; exact hsd
    set i := c.nreg sP + j with hi
    refine IRS.mono (K := 11102 + K + 2) (IRS.ifT hsd ?_) (by omega) (fun _ h => h)
    have hsBA := hS.hsBA
    have haBA := hS.haBA
    have h5 : 5 * i + 5 ≤ 5 * c.nreg sC := by omega
    refine (IRS.seq (K₁ := 7) (K₂ := 11095 + K) (ldStop_irs hId hKd.2.1 (by rw [eSB, hsP]; omega))
      ?_).mono (by omega) (fun _ h => h)
    rintro d₁ hI₁ hA₁ hA₁' ⟨s1, s2, s3, s4⟩
    rw [eSB, hsP, hmem _ (by omega)] at s1
    rw [eSB, hsP, hmem _ (by omega)] at s2
    change d₁.nreg kqSE = stopE c i at s1
    change d₁.nreg kqSH = stopH c i at s2
    have fr1 : EFr SkR d d₁ := ⟨fun r _ hr _ => s3 r (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h))))))))
      (fun h => hr (Or.inr (Or.inl h))) (fun h => hr (Or.inr (Or.inr (Or.inl h)))),
      (s3 ALLOC (by kqr) (by kqr) (by kqr)).ge, fun a _ => by rw [s4]⟩
    have eKE1 : d₁.nreg kE = d₀.nreg kE := (s3 _ (by kqr) (by kqr) (by kqr)).trans eKE
    have eKH1 : d₁.nreg kH = d₀.nreg kH := (s3 _ (by kqr) (by kqr) (by kqr)).trans eKH
    have hgw₁ : d₁.nreg cGW = gW J := E.gw' hI₁
    have hgw₁' : ((d₁.nreg cGW : ℕ) : ℝ) = (gW J : ℝ) := by rw [hgw₁]
    have hpk := hS.hpk
    have hpi := hS.hps i hs
    refine IRS.seq (K₁ := 11008) (K₂ := 87 + K) (callOff_irs (dsc := sw 2) (ex := kE) (hx := kH)
      (ey := kqSE) (hy := kqSH) (g := cGW) (o := kqO) hI₁ (E.ctxW' hI₁)
      ⟨by norm_num [sw], by norm_num [sw], by unfold kE sw; norm_num, by unfold kE sw; norm_num,
        by unfold kH sw; norm_num, by unfold kH sw; norm_num, by unfold kqSE sw; norm_num,
        by unfold kqSE sw; norm_num, by unfold kqSH sw; norm_num, by unfold kqSH sw; norm_num,
        by unfold cGW sw; norm_num, by unfold cGW sw; norm_num⟩
      ⟨by unfold kqO sw; norm_num, by unfold kqO sw; norm_num⟩ (by rw [eKE1]; exact hpk.1)
      (by rw [s1]; exact hpi.1) (by rw [hgw₁]; exact kqGW_lt J) (by rw [eKE1, eKH1]; exact hpk.2.1)
      (by rw [s1, s2]; exact hpi.2.1) (by rw [eKE1, eKH1]; exact hpk.2.2)
      (by rw [s1, s2]; exact hpi.2.2) (by omega)) ?_ |>.mono (by omega) (fun _ h => h)
    rintro d₂ hI₂ hA₂ hA₂' ⟨b1, -, k₂, ha₂, hm₂⟩
    rw [hgw₁', eKE1, eKH1, s1, s2] at b1
    change BitIs d₂ kqO (o' < offK P J (stopE c i) (stopH c i)) at b1
    have fr2 : EFr SkR d₁ d₂ := ⟨fun r hr hX hra => k₂ r hr
      (fun h => hX (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      (fun h => hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hra, ha₂, hm₂⟩
    have same : ∀ r, r = sP ∨ r = kqA ∨ LblR kqN kqL r → d₂.nreg r = d.nreg r := by
      intro r hr
      have hr' : r = sP ∨ r = kqA ∨ (kqN ≤ r ∧ r < kqL + 4) := by
        rcases hr with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨by rw [h], by rw [h]; unfold kqN kqL sw; omega⟩)
        · exact Or.inr (Or.inr ⟨by unfold kqN kqL sw at *; omega, h.2⟩)
      have hr'' : r = 242450 ∨ (242488 ≤ r ∧ r < 242494) := by
        simp only [sP, kqA, kqN, kqL, sw] at hr'; omega
      rw [k₂ r (not_oracle_sw (by omega) (by omega)) (by unfold kqO sw; omega)
        (by unfold kqO sw; omega) (by unfold ALLOC; omega)]
      exact s3 r (by unfold kqX sw; omega) (by unfold kqSE sw; omega) (by unfold kqSH sw; omega)
    have eSP2 : d₂.nreg sP = i := (same _ (Or.inl rfl)).trans hsP
    have eN2 : d₂.nreg kqN = d.nreg kqN := same _ (Or.inr (Or.inr (Or.inl rfl)))
    have eA2 : d₂.nreg kqA = d.nreg kqA := same _ (Or.inr (Or.inl rfl))
    have lb2 : lblOf d₂ kqN kqL = lblOf d kqN kqL := kqLblOf_eq fun q hq =>
      same q (Or.inr (Or.inr hq))
    have fr02 : EFr SkR d₀ d₂ := fr.trans (fr1.trans fr2)
    have k02 : d₂.nreg K0 = 0 := (E.hK.fix hI₂).1
    by_cases h2 : d₂.nreg K0 < d₂.nreg kqO
    · rw [k02] at h2
      have hlt : o' < offK P J (stopE c i) (stopH c i) := b1.2.1 (by have := b1.1; omega)
      refine IRS.mono (K := 0 + 2) (IRS.ifT (by rw [k02]; exact h2) (IRS.skip hI₂ rfl)) (by omega) ?_
      rintro d' rfl
      refine hstop d₂ ⟨j, ⟨fr02, by rw [eSP2], hjC, hj2, hoff, by rw [eN2]; exact hN,
        by rw [lb2]; exact hlb, by rw [eA2]; exact hA1, by rw [eA2]; exact hAiff⟩, fun _ => ?_⟩
      rw [eSP2]
      exact ne_of_gt hlt
    · rw [k02] at h2
      have hnlt : ¬ o' < offK P J (stopE c i) (stopH c i) := fun h => by have := b1.2.2 h; omega
      have hle : o' ≤ offK P J (stopE c i) (stopH c i) := by
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · have := hS.hmin (by omega)
          rw [hi, hj0, Nat.add_zero]; exact this
        · rw [← hoff (c.nreg sP) le_rfl (by omega)]
          exact hS.hsort _ _ (by omega) hs
      have heq : offK P J (stopE c i) (stopH c i) = o' := le_antisymm (not_lt.1 hnlt) hle
      refine IRS.mono (K := 85 + K + 2) (IRS.ifF (by rw [k02]; exact h2) ?_) (by omega)
        (fun _ h => h)
      have eAB2 : d₂.nreg aB = c.nreg aB := by
        rw [fr02.kkeep (nSk aB (Or.inr (Or.inr (Or.inl rfl)))).1 (nSk aB (Or.inr (Or.inr (Or.inl rfl)))).2]
        exact hS.haB
      have hAd2 : c.nreg ALLOC ≤ d₂.nreg ALLOC := hAd.trans (hA₁.trans hA₂)
      have hmem2 : ∀ x, x < c.nreg ALLOC → d₂.nmem x = c.nmem x := fun x hx => by
        rw [hm₂ x (lt_of_lt_of_le hx (hAd.trans hA₁)), s4, hmem x hx]
      refine IRS.seq (K₁ := 84) (K₂ := 1 + K) (stopLab_irs hI₂ E.hK (by rw [eN2]; exact hN)
        (by rw [eAB2, eSP2]; omega) hW4) ?_ |>.mono (by omega) (fun _ h => h)
      rintro d₃ hI₃ hA₃ hA₃' ⟨t1, t2, t3, t4, t5, t6⟩
      rw [eAB2, eSP2, stopLabs_congr (m := c.nmem) (fun t ht => hmem2 _ (by omega))] at t4
      rw [eAB2, eSP2, hmem2 _ (by omega)] at t5 t6
      have hK₃ := E.hK.fix hI₃
      have eSP3 : d₃.nreg sP = i := by
        rw [t1 _ (by unfold KStR LblR; kqr)]; exact eSP2
      refine IRS.seq (K₁ := 1) (K₂ := K) (IRS.block [.addN sP sP K1] hI₃
        ⟨⟨iscr_sw' (by norm_num) (by norm_num), by rw [eSP3, hK₃.2.1]; omega⟩, trivial⟩) ?_
      rintro d₄ hI₄ hA₄ hA₄' hd₄
      have v1 : d₄.nreg sP = i + 1 := by
        rw [hd₄]; simp [regB, regI, eSP3, hK₃.2.1]
      have v2 : ∀ r, r ≠ sP → d₄.nreg r = d₃.nreg r := fun r hr => by
        rw [hd₄]; simp [regB, regI, upd, hr]
      have mem4 : d₄.nmem = d₃.nmem := by rw [hd₄]
      have fr34 : EFr SkR d₂ d₄ := ⟨fun r _ hr _ => by
          rw [v2 r (fun h => hr (Or.inl h))]
          exact t1 r (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))),
        by rw [v2 ALLOC (by kqr), t1 ALLOC (by unfold KStR LblR; kqr)], fun a _ => by rw [mem4, t2]⟩
      refine hnext d₄ hI₄ (by
        have := v2 ALLOC (by kqr); have := t1 ALLOC (by unfold KStR LblR; kqr); omega) ?_
      have eN4 : d₄.nreg kqN = d₃.nreg kqN := v2 _ (by kqr)
      have eA4 : d₄.nreg kqA = d₃.nreg kqA := v2 _ (by kqr)
      have lb4 : lblOf d₄ kqN kqL = lblOf d₃ kqN kqL := kqLblOf_eq fun q hq =>
        v2 q (by simp only [LblR, kqN, kqL, sw] at hq; kqr)
      refine ⟨fr02.trans fr34, by rw [v1, hi]; ring, by omega, by omega, fun i' h1 h2 => ?_, by omega,
        ?_, ?_, ?_⟩
      · rcases Nat.lt_or_ge i' i with h | h
        · exact hoff i' h1 h
        · rw [show i' = i by omega]; exact heq
      · rw [lb4, t4, lb2, hlb, ← kqAddLs_append, ← List.flatMap_singleton (f := stopLabs c.nmem
          (c.nreg aB)) (x := i), ← List.flatMap_append, List.range'_1_concat]
      · by_cases hf : c.nmem (c.nreg aB + 5 * i) = 1
        · rw [eA4, t5 hf]
        · rw [eA4, t6 hf, eA2]; exact hA1
      · by_cases hf : c.nmem (c.nreg aB + 5 * i) = 1
        · rw [eA4, t5 hf]
          exact ⟨fun _ => ⟨i, by omega, by omega, hf⟩, fun _ => rfl⟩
        · rw [eA4, t6 hf, eA2, hAiff]
          constructor
          · rintro ⟨i', h1, h2, h3⟩; exact ⟨i', h1, by omega, h3⟩
          · rintro ⟨i', h1, h2, h3⟩
            refine ⟨i', h1, ?_, h3⟩
            rcases Nat.lt_or_ge i' i with h | h
            · exact h
            · exact absurd (show i' = i by omega ▸ h3) hf
  · have hs : ¬ c.nreg sP + j < c.nreg sC := by rw [hsP, eSC] at hsd; exact hsd
    refine IRS.mono (K := 0 + 2) (IRS.ifF hsd (IRS.skip hId rfl)) (by omega) ?_
    rintro d' rfl
    exact hstop d ⟨j, ⟨fr, hsP, hjC, hj2, hoff, hN, hlb, hA1, hAiff⟩, fun h => by omega⟩

/-- **The two skips.** -/
theorem skip2_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hS : SkCtx P J c d₀)
    (hId₀ : IInv W c₀ d₀) (h0 : SkInv P J c d₀ d₀ 0) (hroom : d₀.nreg ALLOC + 22400 ≤ W) :
    IRS P W c₀ (skipS (skipS .skip)) d₀ 22400 (SkDone P J c d₀) := by
  refine (skipS_irs (K := 11200) E hS hId₀ (by norm_num) h0 (by omega) (fun d' hI' hA' h1 => ?_)
    (fun _ h => h)).mono le_rfl (fun _ h => h)
  refine (skipS_irs (K := 0) E hS hI' le_rfl h1 (by omega) (fun d'' hI'' _ h2 => IRS.skip hI'' ?_)
    (fun _ h => h)).mono le_rfl (fun _ h => h)
  refine ⟨2, h2, fun hlt => ?_⟩
  obtain ⟨-, hsP, -, -, hoff, -⟩ := h2
  rw [hsP]
  rw [← hoff (c.nreg sP) le_rfl (by omega)]
  exact ne_of_gt (hS.htwo _ (by omega))

end

end SweepEv

end Chazelle.Core
