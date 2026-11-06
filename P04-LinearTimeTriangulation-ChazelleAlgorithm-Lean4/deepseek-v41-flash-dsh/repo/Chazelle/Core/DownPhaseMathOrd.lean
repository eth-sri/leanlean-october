module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseMathCyc

/-!
# Down phase, math (H-R1): the arcs of a region in cyclic order

Let the arcs of the region `R` be listed as `(a t, b t)`, `t < k`, in increasing order of their
start keys (as the region records of `buildNF` list them).  Going around the walk from `a 0`, the
host keys are: the start `a t`, the inner walk vertices, the end `b t`, possibly one junction point
(a walk vertex between two chord gaps), then the start `a (t + 1)` of the next arc (`arcs_cycle`).
With `O t = Σ_{s < t} (d s + 1 + J s)` (`d s` the gaps of arc `s`, `J s ∈ {0, 1}` the junction
after it) the start of arc `t` is the host key of index `i 0 + O t` (mod `N`), and `O k = N`.

* `cyc_start`: a key outside an arc whose next gap lies in the arc is the start of the arc;
* `start_of_arcGap`: an arc gap at a cut starts an arc of `R`;
* `arcGap_of_start`: the start of an arc starts an arc gap.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- **The start of a cyclic interval**: if `x` is not in `(a, b)` but the gap `(x, y)` is, then
`x = a`. -/
theorem cyc_start {n : ℝ} {a b x y : ℝ} (hxy : x ≠ y) (hx0 : 0 ≤ x) (hxn : x < n)
    (hy0 : 0 ≤ y) (hyn : y < n) (_ha0 : 0 ≤ a) (_han : a < n)
    (hsub : ∀ z, 0 ≤ z → z < n → sideInArc x y z → sideInArc a b z)
    (hnot : ¬ sideInArc a b x) : x = a := by
  -- a point of the gap just after `x`, below any given bound `u > x`
  have hpt : ∀ u, x < u → ∃ z, x < z ∧ z < u ∧ 0 ≤ z ∧ z < n ∧ sideInArc a b z := by
    intro u hu
    rcases lt_or_gt_of_ne hxy with h | h
    · refine ⟨(x + min u y) / 2, ?_, ?_, ?_, ?_, ?_⟩
      · have := lt_min hu h; linarith
      · have := min_le_left u y; linarith
      · have := lt_min hu h; linarith
      · have := min_le_right u y; linarith
      · apply hsub _ (by have := lt_min hu h; linarith) (by have := min_le_right u y; linarith)
        unfold sideInArc; rw [ite_eq_left h]
        constructor
        · have := lt_min hu h; linarith
        · have := min_le_right u y; have := lt_min hu h; linarith
    · refine ⟨(x + min u n) / 2, ?_, ?_, ?_, ?_, ?_⟩
      · have := lt_min hu hxn; linarith
      · have := min_le_left u n; linarith
      · have := lt_min hu hxn; linarith
      · have := min_le_right u n; have := lt_min hu hxn; linarith
      · apply hsub _ (by have := lt_min hu hxn; linarith)
          (by have := min_le_right u n; have := lt_min hu hxn; linarith)
        unfold sideInArc; rw [ite_eq_right (not_lt.2 h.le)]
        left; have := lt_min hu hxn; linarith
  unfold sideInArc at hnot hpt
  by_cases hab : a < b
  · simp only [ite_eq_left hab] at hnot hpt
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨z, h1, h2, -, -, h3, -⟩ := hpt a h
      linarith
    · -- `a < x`, so `b ≤ x`, and points just after `x` are not below `b`
      have hb : b ≤ x := by
        by_contra hb; push Not at hb; exact hnot ⟨h, hb⟩
      obtain ⟨z, h1, -, -, -, -, h3⟩ := hpt (x + 1) (⟡)
      linarith
  · simp only [ite_eq_right hab] at hnot hpt
    push Not at hnot
    by_contra hne
    have hxa : x < a := lt_of_le_of_ne hnot.1 hne
    obtain ⟨z, h1, h2, -, -, h3⟩ := hpt a hxa
    rcases h3 with h3 | h3
    · linarith
    · linarith [hnot.2]

/-- The length of the group of host keys of arc `t`: its `d t + 1` keys from the start to the
key before the next group, plus the junction. -/
def grpLen (d J : ℕ → ℕ) (t : ℕ) : ℕ := d t + 1 + J t

/-- The offset of group `t`: the sum of the lengths of the groups before it. -/
def grpOff (d J : ℕ → ℕ) (t : ℕ) : ℕ := ∑ s ∈ Finset.range t, grpLen d J s

theorem grpOff_succ (d J : ℕ → ℕ) (t : ℕ) : grpOff d J (t + 1) = grpOff d J t + grpLen d J t := by
  unfold grpOff; rw [Finset.sum_range_succ]

section

variable (hQ : Q.Simple) (hFam : (interiorModel Q).ChordFamily Q S) (hne : S.Nonempty)
  (hR : R ∈ (interiorModel Q).regions S)
include hQ hFam hne hR

/-- **An arc gap at a cut starts an arc of `R`.** -/
theorem start_of_arcGap {j : ℕ} (hj : j < nk (interiorModel Q) S R)
    (hA : ArcGap (interiorModel Q) S R j)
    (hcut : (interiorModel Q).IsCut S (hk (interiorModel Q) S R j)) :
    ∃ b, (interiorModel Q).IsArc S R (hk (interiorModel Q) S R j) b := by
  set I := interiorModel Q
  set N := nk I S R
  have hM : WalkAx I := walkAx_interiorModel hQ
  have h3 : 3 ≤ N := three_le_nk hQ hFam hne hR
  obtain ⟨a', b', harc, hsub⟩ := hA
  have hsj : (j + 1) % N < N := Nat.mod_lt _ (⋄)
  have hbx := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hj)
  have hby := hostKeys_bounds (hk_mem hM hFam.2.1 hFam.1 hsj)
  have e := cyc_start (hk_succ_ne hM hFam.2.1 hFam.1 (⋄) hj) hbx.1 hbx.2 hby.1 hby.2
    harc.1 harc.2.1 hsub (fun h => harc.2.2.2.2.2.1 _ h hcut)
  exact ⟨b', e ▸ harc⟩

/-- **The start of an arc starts an arc gap.** -/
theorem arcGap_of_start {j : ℕ} (hj : j < nk (interiorModel Q) S R) {b : ℝ}
    (harc : (interiorModel Q).IsArc S R (hk (interiorModel Q) S R j) b) :
    ArcGap (interiorModel Q) S R j := by
  have hM : WalkAx (interiorModel Q) := walkAx_interiorModel hQ
  obtain ⟨i_l, d, hD⟩ := arc_keys hM hFam.2.1 hFam.1 hne hR harc
  have := hk_inj hM hFam.2.1 hFam.1 hD.hil hj hD.hl
  subst this
  have h := arcData_gap hQ hFam hne hR harc hD hD.hd0
  rwa [add_zero, Nat.mod_eq_of_lt hD.hil] at h

/-- **The arcs of `R` in cyclic order** (see the module doc). -/
theorem arcs_cycle (hdh : DistinctHeights Q) {k : ℕ} (hk1 : 0 < k) (a b : ℕ → ℝ)
    (harc : ∀ t, t < k → (interiorModel Q).IsArc S R (a t) (b t))
    (hsort : ∀ t t', t < t' → t' < k → a t < a t')
    (hcomp : ∀ a' b', (interiorModel Q).IsArc S R a' b' → ∃ t, t < k ∧ a t = a' ∧ b t = b') :
    ∃ i d J : ℕ → ℕ,
      (∀ t, t < k → ArcData (interiorModel Q) S R (a t) (b t) (i t) (d t)) ∧
      (∀ t, t < k → (J t = 0 ↔
        ArcGap (interiorModel Q) S R ((i t + d t + 1) % nk (interiorModel Q) S R))) ∧
      (∀ t, t < k → J t ≤ 1) ∧
      (∀ t, t < k → i t = i 0 + grpOff d J t) ∧
      grpOff d J k = nk (interiorModel Q) S R := by
  classical
  set I := interiorModel Q with hI
  set N := nk I S R with hN
  have hM : WalkAx I := walkAx_interiorModel hQ
  have hF := hFam.2.1
  have hfin := hFam.1
  have h3 : 3 ≤ N := three_le_nk hQ hFam hne hR
  have hAD : ∀ t, t < k → ∃ i d, ArcData I S R (a t) (b t) i d :=
    fun t ht => arc_keys hM hF hfin hne hR (harc t ht)
  choose! i d hD using hAD
  set J : ℕ → ℕ := fun t => if ArcGap I S R ((i t + d t + 1) % N) then 0 else 1 with hJ
  have hJ0 : ∀ t, (J t = 0 ↔ ArcGap I S R ((i t + d t + 1) % N)) := by
    intro t; simp only [hJ]; split_ifs with h <;> simp [h]
  have hJ1 : ∀ t, J t ≤ 1 := by intro t; simp only [hJ]; split_ifs <;> omega
  -- the start indices increase
  have hil : ∀ t, t < k → i t < N := fun t ht => (hD t ht).hil
  have hmono : ∀ t t', t < t' → t' < k → i t < i t' := by
    intro t t' htt ht'
    by_contra h; push Not at h
    rcases h.lt_or_eq with h | h
    · have := hk_strictMono hM hF hfin h (hil t (by omega))
      rw [(hD t' ht').hl, (hD t (by omega)).hl] at this
      linarith [hsort t t' htt ht']
    · have := hsort t t' htt ht'
      rw [← (hD t' ht').hl, ← (hD t (by omega)).hl, h] at this
      exact lt_irrefl _ this
  have hi0 : ∀ t, t < k → i 0 ≤ i t := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | h
    · exact le_rfl
    · exact (hmono 0 t h ht).le
  -- an arc start is an arc gap
  have hstartA : ∀ s, s < k → ArcGap I S R (i s) := by
    intro s hs
    exact arcGap_of_start hQ hFam hne hR (hil s hs) (by rw [(hD s hs).hl]; exact harc s hs)
  -- the facts after the end of arc `t`
  have hafter : ∀ t, t < k →
      ChordGap I S R ((i t + d t) % N) ∧
      (∃ s, s < k ∧ i s = (i t + grpLen d J t) % N) ∧
      (∀ j, 0 < j → j < grpLen d J t → ∀ s, s < k → i s ≠ (i t + j) % N) := by
    intro t ht
    have hDt := hD t ht
    set m := (i t + d t) % N with hm
    have hmN : m < N := Nat.mod_lt _ (by omega)
    have hbm := hDt.hr
    obtain ⟨c, ⟨hc, htc⟩, pc, tc, hAc, hec⟩ := hM.exists_exit_at_end hF hfin hne hR (harc t ht)
    have hx : hk I S R m ∈ exitKeys I S R := ⟨c, hc, htc, pc, tc, hAc, by rw [hbm]; exact hec⟩
    have hprev : prevIdx N m = (i t + (d t - 1)) % N := by
      have e : m = ((i t + (d t - 1)) % N + 1) % N := by
        rw [hm, Nat.mod_add_mod, show i t + (d t - 1) + 1 = i t + d t by have := hDt.hd0; omega]
      rw [e]; exact prevIdx_succ (Nat.mod_lt _ (by omega))
    have hAp : ArcGap I S R (prevIdx N m) := by
      rw [hprev]; exact arcData_gap hQ hFam hne hR (harc t ht) hDt (by have := hDt.hd0; omega)
    obtain ⟨hCm, hnext⟩ := end_chord hQ hFam hne hR hmN hx hAp
    set q₁ := (m + 1) % N with hq₁
    have hq₁N : q₁ < N := Nat.mod_lt _ (by omega)
    have hq₁e : q₁ = (i t + d t + 1) % N := by rw [hq₁, hm, Nat.mod_add_mod]
    obtain ⟨pz, tz, hAz, hez⟩ := hnext c hc htc pc tc hAc (by rw [hbm]; exact hec)
    have hcut₁ : I.IsCut S (hk I S R q₁) := ⟨c, hc, pz, tz, hAz, hez⟩
    -- no arc start at the end
    have hnot_m : ∀ s, s < k → i s ≠ m := by
      intro s hs he
      exact not_arc_and_chord hM hF hfin (by omega) hmN (he ▸ hstartA s hs) hCm
    -- no arc start inside the arc
    have hnot_in : ∀ j, 0 < j → j < d t → ∀ s, s < k → i s ≠ (i t + j) % N := by
      intro j hj0 hjd s hs he
      have hin := (hDt.inner j hj0 hjd).2
      rw [← he, (hD s hs).hl] at hin
      exact (harc t ht).2.2.2.2.2.1 _ hin (WalkAx.arc_cuts hne (harc s hs)).1
    by_cases hA₁ : ArcGap I S R q₁
    · -- the next key starts the next arc
      have hJt : J t = 0 := (hJ0 t).2 (hq₁e ▸ hA₁)
      obtain ⟨b', hb'⟩ := start_of_arcGap hQ hFam hne hR hq₁N hA₁ hcut₁
      obtain ⟨s, hs, has, -⟩ := hcomp _ _ hb'
      refine ⟨hCm, ⟨s, hs, ?_⟩, ?_⟩
      · have := hk_inj hM hF hfin (hil s hs) hq₁N (by rw [(hD s hs).hl, has])
        rw [this, hq₁e]; unfold grpLen; rw [hJt]; congr 1
      · intro j hj0 hj s' hs'
        unfold grpLen at hj; rw [hJt] at hj
        rcases Nat.lt_or_ge j (d t) with hjd | hjd
        · exact hnot_in j hj0 hjd s' hs'
        · rw [show j = d t by omega]; exact hnot_m s' hs'
    · -- a junction
      have hJt : J t = 1 := by
        have := hJ1 t
        by_contra h
        exact hA₁ (hq₁e ▸ (hJ0 t).1 (by omega))
      have hCp : ChordGap I S R (prevIdx N q₁) := by rw [hq₁, prevIdx_succ hmN]; exact hCm
      obtain ⟨-, hA₂⟩ := junction hQ hFam hne hR hdh hq₁N hCp hA₁
      have hC₁ : ChordGap I S R q₁ :=
        (gap_cases hM hF hfin hne hR (by omega) hq₁N).resolve_left hA₁
      obtain ⟨c'', hc'', -, p₂, -, t₂, -, hA₂', -, he₂, -⟩ := hC₁
      have hq₂N : (q₁ + 1) % N < N := Nat.mod_lt _ (by omega)
      have hcut₂ : I.IsCut S (hk I S R ((q₁ + 1) % N)) := ⟨c'', hc'', p₂, t₂, hA₂', he₂⟩
      obtain ⟨b', hb'⟩ := start_of_arcGap hQ hFam hne hR hq₂N hA₂ hcut₂
      obtain ⟨s, hs, has, -⟩ := hcomp _ _ hb'
      refine ⟨hCm, ⟨s, hs, ?_⟩, ?_⟩
      · have := hk_inj hM hF hfin (hil s hs) hq₂N (by rw [(hD s hs).hl, has])
        rw [this, hq₁e, Nat.mod_add_mod]; unfold grpLen; rw [hJt]; congr 1
      · intro j hj0 hj s' hs'
        unfold grpLen at hj; rw [hJt] at hj
        rcases Nat.lt_or_ge j (d t) with hjd | hjd
        · exact hnot_in j hj0 hjd s' hs'
        · rcases (show j = d t ∨ j = d t + 1 by omega) with rfl | rfl
          · exact hnot_m s' hs'
          · intro he
            rw [← Nat.add_assoc, ← hq₁e] at he
            exact hA₁ (he ▸ hstartA s' hs')
  -- the offsets
  have hstep : ∀ t, t < k → (t + 1 < k → i t + grpLen d J t = i (t + 1)) ∧
      (t + 1 = k → i t + grpLen d J t = i 0 + N) := by
    intro t ht
    obtain ⟨-, ⟨s, hs, his⟩, hnone⟩ := hafter t ht
    have hdN := (hD t ht).hdN
    have hG : grpLen d J t ≤ N + 1 := by unfold grpLen; have := hJ1 t; omega
    -- the next start is not `i 0` strictly inside the group
    have hle : i t + grpLen d J t ≤ i 0 + N := by
      by_contra h; push Not at h
      have hj0 : 0 < i 0 + N - i t := by have := hil t ht; omega
      apply hnone (i 0 + N - i t) hj0 (by omega) 0 hk1
      rw [show i t + (i 0 + N - i t) = i 0 + N by have := hil t ht; omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (hil 0 hk1)]
    constructor
    · intro ht1
      -- the next start is `i (t + 1)`
      have hlt : i t + grpLen d J t < i 0 + N := by
        rcases hle.lt_or_eq with h | h
        · exact h
        · exfalso
          have h1 := hmono t (t + 1) (by omega) ht1
          have h2 := hil (t + 1) ht1
          apply hnone (i (t + 1) - i t) (by omega) (by omega) (t + 1) ht1
          rw [show i t + (i (t + 1) - i t) = i (t + 1) by omega, Nat.mod_eq_of_lt h2]
      have hgN : i t + grpLen d J t < N ∨ N ≤ i t + grpLen d J t := Nat.lt_or_ge _ _
      rcases hgN with hgN | hgN
      · rw [Nat.mod_eq_of_lt hgN] at his
        -- `s` is after `t`, and no start lies in between
        have hst : t < s := by
          by_contra h; push Not at h
          rcases h.lt_or_eq with h | h
          · have := hmono s t h ht; unfold grpLen at his; omega
          · subst h; unfold grpLen at his; omega
        rcases (show s = t + 1 ∨ t + 1 < s by omega) with rfl | hs1
        · exact his.symm
        · exfalso
          have h1 := hmono t (t + 1) (by omega) ht1
          have h2 := hmono (t + 1) s hs1 hs
          apply hnone (i (t + 1) - i t) (by omega) (by omega) (t + 1) ht1
          rw [show i t + (i (t + 1) - i t) = i (t + 1) by omega,
            Nat.mod_eq_of_lt (hil (t + 1) ht1)]
      · exfalso
        have h0N := hil 0 hk1
        rw [show i t + grpLen d J t = (i t + grpLen d J t - N) + N by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)] at his
        have := hi0 s hs
        omega
    · intro ht1
      rcases hle.lt_or_eq with h | h
      · exfalso
        -- the next start would come after the last one
        rcases Nat.lt_or_ge (i t + grpLen d J t) N with hgN | hgN
        · rw [Nat.mod_eq_of_lt hgN] at his
          have hst : t < s := by
            by_contra h'; push Not at h'
            rcases h'.lt_or_eq with h' | h'
            · have := hmono s t h' ht; unfold grpLen at his; omega
            · subst h'; unfold grpLen at his; omega
          omega
        · have h0N := hil 0 hk1
          rw [show i t + grpLen d J t = (i t + grpLen d J t - N) + N by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)] at his
          have := hi0 s hs
          omega
      · exact h
  have hoff : ∀ t, t < k → i t = i 0 + grpOff d J t := by
    intro t ht
    induction t with
    | zero => simp [grpOff]
    | succ t ih =>
      rw [grpOff_succ, ← Nat.add_assoc, ← ih (by omega)]
      exact ((hstep t (by omega)).1 ht).symm
  refine ⟨i, d, J, hD, fun t _ => hJ0 t, fun t _ => hJ1 t, hoff, ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 := (hstep k' (by omega)).2 rfl
  rw [hoff k' (by omega)] at h1
  rw [grpOff_succ]
  omega

end

end

end DownMath

end Chazelle.Core
