module

public import Chazelle.Golf

public import Chazelle.Core.NFDecompRooted

/-!
# Tree decomposition (WP-C), part 2: the size and top passes

The two array passes of one round of the decomposition, as functions mirroring the RAM loops,
with their characterisations:

* `p1` (reverse search order): accumulates subtree sizes into parents; after all `R` steps from
  the all-ones array, entry `u` is `sz rem u` (`p1_full`).
* `p2` (search order): the top of every region, and for every top the best cut candidate: a
  region `c` of its component maximising `min (sz c) (sz t - sz c)` (`p2_full`).
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset

/-! ## Pass 1: sizes -/

/-- Step `j` of the size pass: region `r = ord (R - 1 - j)`, if it is not a top, adds its size
into its parent's. -/
def p1 (R : ℕ) (ord prg pch rem : ℕ → ℕ) (s : ℕ → ℕ) (j : ℕ) : ℕ → ℕ :=
  if ord (R - 1 - j) ≠ 0 ∧ rem (pch (ord (R - 1 - j))) ≠ 1 then
    Function.update s (prg (ord (R - 1 - j))) (s (prg (ord (R - 1 - j))) + s (ord (R - 1 - j)))
  else s

/-- The all-ones array. -/
def ones : ℕ → ℕ := fun _ => 1

section p1

variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h

variable {rem : ℕ → ℕ}

open Classical in
/-- Splitting the children sum at one position of the search order. -/
theorem sum_kids_split {v p r : ℕ} (hr : r < R) (hpr : pos r = p) :
    ∑ c ∈ (kids R prg pch rem v).filter (fun c => p ≤ pos c), sz R prg pch rem c =
      (if ChX R prg pch rem v r then sz R prg pch rem r else 0) +
        ∑ c ∈ (kids R prg pch rem v).filter (fun c => p + 1 ≤ pos c), sz R prg pch rem c := by
  classical
  Ξ Finset.sum_filter, Finset.sum_filter
  have hpt : ∀ c ∈ kids R prg pch rem v,
      (if p ≤ pos c then sz R prg pch rem c else 0) =
        (if c = r then sz R prg pch rem c else 0) +
          (if p + 1 ≤ pos c then sz R prg pch rem c else 0) := by
    intro c hc
    rw [mem_kids] at hc
    by_cases hcr : c = r
    · subst hcr
      Θ hpr
    · have hne : pos c ≠ p := fun e => hcr (h.pos_inj hc.1 hr (e.trans hpr.symm))
      by_cases h1 : p ≤ pos c
      · rw [ite_eq_left h1, ite_eq_right hcr, ite_eq_left (⋄)]; simp
      · rw [ite_eq_right h1, ite_eq_right hcr, ite_eq_right (⋄)]
  Ξ Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq'
  congr 1
  by_cases hk : ChX R prg pch rem v r
  · Ξ ite_eq_left ((mem_kids).2 hk), ite_eq_left hk
  · Ξ ite_eq_right (fun hh => hk ((mem_kids).1 hh)), ite_eq_right hk

/-- **The size pass**, partial: after `j` steps, entry `u` is `1` plus the sizes of its children
at search positions `≥ R - j`. -/
theorem p1_fold {j : ℕ} (hj : j ≤ R) {u : ℕ} (hu : u < R) :
    ((List.range j).foldl (p1 R ord prg pch rem) ones) u =
      1 + ∑ c ∈ (kids R prg pch rem u).filter (fun c => R - j ≤ pos c), sz R prg pch rem c := by
  classical
  induction j generalizing u with
  | zero =>
    ϴ List.range_zero, List.foldl_nil, ones, Nat.sub_zero
    have : (kids R prg pch rem u).filter (fun c => R ≤ pos c) = ∅ := by
      ext c
      ϴ Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_le
      intro hc
      exact h.pos_lt c ((mem_kids).1 hc).1
    Ξ this, Finset.sum_empty
    rfl
  | succ j ih =>
    Ξ List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil
    have hjR : j < R := ⋄
    have hp : R - 1 - j < R := ⋄
    have hr : ord (R - 1 - j) < R := h.ord_lt _ hp
    have hpr : pos (ord (R - 1 - j)) = R - (j + 1) := by rw [h.pos_ord _ hp]; omega
    have ih' : ∀ v, v < R → ((List.range j).foldl (p1 R ord prg pch rem) ones) v =
        1 + ∑ c ∈ (kids R prg pch rem v).filter (fun c => R - j ≤ pos c), sz R prg pch rem c :=
      fun v hv => ih (⋄) hv
    generalize (List.range j).foldl (p1 R ord prg pch rem) ones = s at ih' ⊢
    unfold p1
    generalize ord (R - 1 - j) = r at hr hpr ⊢
    have hsplit := fun v => sum_kids_split h (rem := rem) (v := v) hr hpr
    have hth : R - (j + 1) + 1 = R - j := ⋄
    -- the size of `r` is final
    have hsr : s r = sz R prg pch rem r := by
      Ξ ih' r hr, sz_rec h hr
      congr 1
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext c
      ϴ Finset.mem_filter, and_iff_left_iff_imp
      intro hc
      rw [mem_kids] at hc
      have := h.pos_prg c hc.1 hc.2.1
      rw [hc.2.2.1, hpr] at this
      omega
    by_cases hc : r ≠ 0 ∧ rem (pch r) ≠ 1
    · Ξ ite_eq_left hc
      have hk : ChX R prg pch rem (prg r) r := ⟨hr, hc.1, rfl, hc.2⟩
      by_cases hu' : u = prg r
      · subst hu'
        Ξ Function.update_self, hsr, ih' _ hu, hsplit, ite_eq_left hk, hth
        ring
      · rw [Function.update_of_ne hu', ih' u hu, hsplit,
          ite_eq_right (fun hh : ChX R prg pch rem u r => hu' hh.2.2.1.symm), hth, zero_add]
    · rw [ite_eq_right hc, ih' u hu, hsplit,
        ite_eq_right (fun hh : ChX R prg pch rem u r => hc ⟨hh.2.1, hh.2.2.2⟩), hth, zero_add]

/-- **The size pass**: after all `R` steps, entry `u` is `sz rem u`. -/
theorem p1_full {u : ℕ} (hu : u < R) :
    ((List.range R).foldl (p1 R ord prg pch rem) ones) u = sz R prg pch rem u := by
  Ξ p1_fold h le_rfl hu, sz_rec h hu, Nat.sub_self
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext c
  simp

end p1

/-! ## Pass 2: tops and cut candidates -/

/-- The state of the top pass: tops, best candidates and their values. -/
structure T3 where
  /-- The top of each region. -/
  top : ℕ → ℕ
  /-- The best cut candidate of each top (the top itself if none). -/
  best : ℕ → ℕ
  /-- The value of the best candidate. -/
  bestv : ℕ → ℕ

/-- Step `i` of the top pass (region `r = ord i`, sizes `S`). -/
def p2 (ord prg pch rem S : ℕ → ℕ) (st : T3) (i : ℕ) : T3 :=
  if ord i = 0 ∨ rem (pch (ord i)) = 1 then
    ⟨Function.update st.top (ord i) (ord i), Function.update st.best (ord i) (ord i),
      Function.update st.bestv (ord i) 0⟩
  else if st.bestv (st.top (prg (ord i))) <
      min (S (ord i)) (S (st.top (prg (ord i))) - S (ord i)) then
    ⟨Function.update st.top (ord i) (st.top (prg (ord i))),
      Function.update st.best (st.top (prg (ord i))) (ord i),
      Function.update st.bestv (st.top (prg (ord i)))
        (min (S (ord i)) (S (st.top (prg (ord i))) - S (ord i)))⟩
  else ⟨Function.update st.top (ord i) (st.top (prg (ord i))), st.best, st.bestv⟩

/-- The value of a cut candidate `c` of the component of `t`. -/
noncomputable def cval (R : ℕ) (prg pch rem : ℕ → ℕ) (t c : ℕ) : ℕ :=
  min (sz R prg pch rem c) (sz R prg pch rem t - sz R prg pch rem c)

/-- The invariant of the top pass after `i` steps. -/
def P2Inv (R : ℕ) (pos prg pch rem : ℕ → ℕ) (i : ℕ) (st : T3) : Prop :=
  (∀ u, u < R → pos u < i → st.top u < R ∧ IsTop pch rem (st.top u) ∧
      AncX R prg pch rem (st.top u) u) ∧
  (∀ t, t < R → IsTop pch rem t → pos t < i →
    (∀ c, c < R → AncX R prg pch rem t c → c ≠ t → pos c < i →
        cval R prg pch rem t c ≤ st.bestv t) ∧
    ((st.best t = t ∧ st.bestv t = 0 ∧ ∀ c, c < R → AncX R prg pch rem t c → c ≠ t → i ≤ pos c) ∨
      (st.best t < R ∧ AncX R prg pch rem t (st.best t) ∧ st.best t ≠ t ∧ pos (st.best t) < i ∧
        st.bestv t = cval R prg pch rem t (st.best t))))

section p2

variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h

variable {rem S : ℕ → ℕ}

/-- A proper member of a component has a positive value. -/
theorem cval_pos {t c : ℕ} (hc : c < R) (htc : AncX R prg pch rem t c) (hne : c ≠ t) :
    1 ≤ cval R prg pch rem t c := by
  unfold cval
  have h1 := sz_pos h (rem := rem) hc
  have h2 := sz_lt h htc (Ne.symm hne) hc
  omega

theorem p2_step {i : ℕ} (hi : i < R) (hS : ∀ u, u < R → S u = sz R prg pch rem u) {st : T3}
    (hI : P2Inv R pos prg pch rem i st) : P2Inv R pos prg pch rem (i + 1) (p2 ord prg pch rem S st i) := by
  obtain ⟨hA, hB⟩ := hI
  have hr : ord i < R := h.ord_lt i hi
  have hpr : pos (ord i) = i := h.pos_ord i hi
  unfold p2
  generalize ord i = r at hr hpr ⊢
  -- positions `< i + 1` are positions `< i` or `r`
  have hlt : ∀ u, u < R → pos u < i + 1 → pos u < i ∨ u = r := by
    intro u hu hpu
    by_cases e : pos u = i
    · exact Or.inr (h.pos_inj hu hr (e.trans hpr.symm))
    · exact Or.inl (⋄)
  by_cases htop : r = 0 ∨ rem (pch r) = 1
  · Ξ ite_eq_left htop
    refine ⟨fun u hu hpu => ?_, fun t ht htt hpt => ?_⟩
    · rcases hlt u hu hpu with h1 | e
      · have hne : u ≠ r := by rintro rfl; omega
        dsimp only
        Ξ Function.update_of_ne hne
        exact hA u hu h1
      · subst e
        dsimp only
        Ξ Function.update_self
        exact ⟨hr, htop, ReflTransGen.refl⟩
    · rcases hlt t ht hpt with h1 | e
      · have hne : t ≠ r := by rintro rfl; omega
        dsimp only
        ϴ Function.update_of_ne hne
        obtain ⟨hB1, hB2⟩ := hB t ht htt h1
        -- `r` is a top, so it is no proper member of the component of `t`
        have hnm : ∀ c, AncX R prg pch rem t c → c ≠ t → c ≠ r := by
          intro c hc hct e
          rw [e] at hc hct
          exact AncX.not_top hc (Ne.symm hct) htop
        refine ⟨fun c hc htc hct hpc => ?_, ?_⟩
        · rcases hlt c hc hpc with h2 | h2
          · exact hB1 c hc htc hct h2
          · exact absurd h2 (hnm c htc hct)
        · rcases hB2 with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4, b5⟩
          · refine Or.inl ⟨b1, b2, fun c hc htc hct => ?_⟩
            have := b3 c hc htc hct
            have hcr := hnm c htc hct
            by_contra hh
            exact hcr (h.pos_inj hc hr (⋄))
          · exact Or.inr ⟨b1, b2, b3, ⋄, b5⟩
      · subst e
        dsimp only
        Ξ Function.update_self, Function.update_self
        refine ⟨fun c hc htc hct hpc => ?_, Or.inl ⟨rfl, rfl, fun c hc htc hct => ?_⟩⟩
        · have := (AncX.pos_le h htc hc).2.2 (Ne.symm hct)
          omega
        · have := (AncX.pos_le h htc hc).2.2 (Ne.symm hct)
          omega
  · Ξ ite_eq_right htop
    have hrnt := htop
    simp only [not_or] at htop
    have hr0 := htop.1
    have hprR : prg r < R := h.prg_lt r hr hr0
    have hppr : pos (prg r) < i := by rw [← hpr]; exact h.pos_prg r hr hr0
    obtain ⟨htR, httop, htanc⟩ := hA (prg r) hprR hppr
    generalize st.top (prg r) = t at htR httop htanc ⊢
    have htr : AncX R prg pch rem t r := htanc.tail ⟨hr, hr0, rfl, htop.2⟩
    have htne : t ≠ r := by
      intro e
      rw [e] at httop
      exact hrnt httop
    have hpt : pos t < i := by
      have := (AncX.pos_le h htr hr).2.2 htne
      omega
    have hval : min (S r) (S t - S r) = cval R prg pch rem t r := by
      rw [hS r hr, hS t htR]; rfl
    Ξ hval
    -- the top of `r`
    have hA' : ∀ u, u < R → pos u < i + 1 → Function.update st.top r t u < R ∧
        IsTop pch rem (Function.update st.top r t u) ∧
          AncX R prg pch rem (Function.update st.top r t u) u := by
      intro u hu hpu
      rcases hlt u hu hpu with h1 | e
      · have hne : u ≠ r := by rintro rfl; omega
        Ξ Function.update_of_ne hne
        exact hA u hu h1
      · subst e
        Ξ Function.update_self
        exact ⟨htR, httop, htr⟩
    -- members of other components are unaffected
    have hother : ∀ t', t' < R → IsTop pch rem t' → t' ≠ t → ¬ AncX R prg pch rem t' r := by
      intro t' ht' htt' hne hanc
      exact hne (top_unique h htt' httop hanc htr)
    have hvpos := cval_pos h hr htr (Ne.symm htne)
    by_cases hbig : st.bestv t < cval R prg pch rem t r
    · Ξ ite_eq_left hbig
      refine ⟨hA', fun t' ht' htt' hpt' => ?_⟩
      rcases hlt t' ht' hpt' with h1 | e2
      · obtain ⟨hB1, hB2⟩ := hB t' ht' htt' h1
        by_cases e : t' = t
        · subst e
          dsimp only
          Ξ Function.update_self, Function.update_self
          refine ⟨fun c hc htc hct hpc => ?_, Or.inr ⟨hr, htr, Ne.symm htne, ⋄, rfl⟩⟩
          rcases hlt c hc hpc with h2 | h2
          · exact (hB1 c hc htc hct h2).trans hbig.le
          · Ξ h2
        · dsimp only
          ϴ Function.update_of_ne e
          refine ⟨fun c hc htc hct hpc => ?_, ?_⟩
          · rcases hlt c hc hpc with h2 | h2
            · exact hB1 c hc htc hct h2
            · rw [h2] at htc; exact absurd htc (hother t' ht' htt' e)
          · rcases hB2 with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4, b5⟩
            · refine Or.inl ⟨b1, b2, fun c hc htc hct => ?_⟩
              have := b3 c hc htc hct
              by_contra hh
              have hcr : c = r := h.pos_inj hc hr (⋄)
              rw [hcr] at htc
              exact hother t' ht' htt' e htc
            · exact Or.inr ⟨b1, b2, b3, ⋄, b5⟩
      · exact absurd (e2 ▸ htt') hrnt
    · Ξ ite_eq_right hbig
      unfold P2Inv
      dsimp only
      refine ⟨hA', fun t' ht' htt' hpt' => ?_⟩
      rcases hlt t' ht' hpt' with h1 | e2
      · obtain ⟨hB1, hB2⟩ := hB t' ht' htt' h1
        by_cases e : t' = t
        · subst e
          refine ⟨fun c hc htc hct hpc => ?_, ?_⟩
          · rcases hlt c hc hpc with h2 | h2
            · exact hB1 c hc htc hct h2
            · rw [h2]; omega
          · rcases hB2 with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4, b5⟩
            · omega
            · exact Or.inr ⟨b1, b2, b3, ⋄, b5⟩
        · refine ⟨fun c hc htc hct hpc => ?_, ?_⟩
          · rcases hlt c hc hpc with h2 | h2
            · exact hB1 c hc htc hct h2
            · rw [h2] at htc; exact absurd htc (hother t' ht' htt' e)
          · rcases hB2 with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4, b5⟩
            · refine Or.inl ⟨b1, b2, fun c hc htc hct => ?_⟩
              have := b3 c hc htc hct
              by_contra hh
              have hcr : c = r := h.pos_inj hc hr (⋄)
              rw [hcr] at htc
              exact hother t' ht' htt' e htc
            · exact Or.inr ⟨b1, b2, b3, ⋄, b5⟩
      · exact absurd (e2 ▸ htt') hrnt

theorem p2_fold {i : ℕ} (hi : i ≤ R) (hS : ∀ u, u < R → S u = sz R prg pch rem u) (st : T3) :
    P2Inv R pos prg pch rem i ((List.range i).foldl (p2 ord prg pch rem S) st) := by
  induction i with
  | zero =>
    refine ⟨fun u _ hu => absurd hu (Nat.not_lt_zero _), fun t _ _ ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ i ih =>
    Ξ List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil
    exact p2_step h (⋄) hS (ih (by omega))

/-- **The top pass**: after all `R` steps, `top u` is the top of `u`, and for every top `t`,
either its component is `{t}` and `best t = t`, or `best t` is a proper member of the component
of maximal value. -/
theorem p2_full (hS : ∀ u, u < R → S u = sz R prg pch rem u) (st : T3) :
    let st' := (List.range R).foldl (p2 ord prg pch rem S) st
    (∀ u, u < R → st'.top u < R ∧ IsTop pch rem (st'.top u) ∧ AncX R prg pch rem (st'.top u) u) ∧
    (∀ t, t < R → IsTop pch rem t →
      (∀ c, c < R → AncX R prg pch rem t c → c ≠ t → cval R prg pch rem t c ≤ st'.bestv t) ∧
      ((st'.best t = t ∧ ∀ c, c < R → AncX R prg pch rem t c → c = t) ∨
        (st'.best t < R ∧ AncX R prg pch rem t (st'.best t) ∧ st'.best t ≠ t ∧
          st'.bestv t = cval R prg pch rem t (st'.best t)))) := by
  intro st'
  obtain ⟨hA, hB⟩ := p2_fold h le_rfl hS st
  refine ⟨fun u hu => hA u hu (h.pos_lt u hu), fun t ht htt => ?_⟩
  obtain ⟨hB1, hB2⟩ := hB t ht htt (h.pos_lt t ht)
  refine ⟨fun c hc htc hct => hB1 c hc htc hct (h.pos_lt c hc), ?_⟩
  rcases hB2 with ⟨b1, -, b3⟩ | ⟨b1, b2, b3, -, b5⟩
  · refine Or.inl ⟨b1, fun c hc htc => ?_⟩
    by_contra hct
    have := b3 c hc htc hct
    have := h.pos_lt c hc
    omega
  · exact Or.inr ⟨b1, b2, b3, b5⟩

end p2

end

end Chazelle.Core.Dec
