module

public import Chazelle.Core.NFDecompStep3
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# Tree decomposition (WP-C), part 8: start, loop test and the final decomposition

* `rinv_init`: the round invariant holds for the initial state `rs0`;
* `fin_lt_iff`: the loop test `fin < R` holds iff an active component remains, and then
  `j ≤ rounds D K` (`le_rounds_of_active`);
* `lowSide_iff`: the low side of a chord in the normal form's record tree, in terms of the rooted
  tree;
* `isDecomp_final`: when no active component remains, the arrays of the state form a valid tree
  decomposition of depth `decDepth D K`.
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset


section init

variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ}
variable (h : Rooted R K up dn ord pos prg pch)
include h

end init

section loop

variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ}
variable (h : Rooted R K up dn ord pos prg pch)
variable {j : ℕ} {σ : RS} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
variable (hI : RInv R K D prg pch isdn chOf j σ gc cr)
include h hI

/-- **The loop test**: fewer than `R` finished leaves iff an active component remains. -/
theorem fin_lt_iff : σ.fin < R ↔ ∃ t, t < R ∧ IsTop pch σ.rem t ∧ σ.act t = 1 := by
  classical
  rw [hI.i9]
  constructor
  · intro hlt
    have hne : ¬ (range R ⊆ (range R).filter (fun t => IsTop pch σ.rem t ∧ σ.act t ≠ 1)) := by
      intro hsub
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      omega
    rw [Finset.not_subset] at hne
    obtain ⟨u, hu, hnu⟩ := hne
    rw [Finset.mem_range] at hu
    simp only [Finset.mem_filter, Finset.mem_range, not_and, not_not] at hnu
    obtain ⟨t, htop, htu⟩ := exists_top h (rem := σ.rem) hu
    have ht := (AncX.pos_le h htu hu).1
    by_cases htu' : t = u
    · subst htu'
      exact ⟨t, ht, htop, hnu hu htop⟩
    · refine ⟨t, ht, htop, ?_⟩
      by_contra hact
      have := (hI.i5 t ht htop hact).1
      have hmem  := (mem_sub).2 ⟨hu, htu⟩
      rw [this, Finset.mem_singleton] at hmem
      exact htu' hmem.symm
  · rintro ⟨t, ht, htop, hact⟩
    have hsub : (range R).filter (fun t => IsTop pch σ.rem t ∧ σ.act t ≠ 1) ⊂ range R := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun e => ?_⟩
      have : t ∈ (range R).filter (fun t => IsTop pch σ.rem t ∧ σ.act t ≠ 1) := by
        rw [e]; exact Finset.mem_range.2 ht
      rw [Finset.mem_filter] at this
      exact this.2.2 hact
    have := Finset.card_lt_card hsub
    rwa [Finset.card_range] at this

/-- While a component is active, the round index is at most `rounds D K`. -/
theorem le_rounds_of_active {t : ℕ} (ht : t < R) (htop : IsTop pch σ.rem t) (hact : σ.act t = 1) :
    j ≤ rounds D K := by
  rcases (hI.i6 t ht htop hact).2 with hj | hj
  · omega
  · have := lt_rounds hj
    omega

end loop

/-! ## The low and high sides of a chord in the record tree -/

section sides

variable {R K : ℕ} {up dn ord pos prg pch chOf : ℕ → ℕ}
variable (h : Rooted R K up dn ord pos prg pch)
variable (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch (chOf e) = e)
include h hch

/-- Adjacent in the record tree through a chord other than `k`. -/
def AdjAv (K : ℕ) (up dn : ℕ → ℕ) (k r r' : ℕ) : Prop :=
  ∃ i, i < K ∧ i ≠ k ∧ (up i = r ∧ dn i = r' ∨ up i = r' ∧ dn i = r)

theorem adjAv_symm {k r r' : ℕ} (hh : AdjAv K up dn k r r') : AdjAv K up dn k r' r := by
  obtain ⟨i, hi, hik, hh⟩ := hh
  exact ⟨i, hi, hik, hh.symm⟩

theorem rtg_adjAv_symm {k r r' : ℕ} (hh : ReflTransGen (AdjAv K up dn k) r r') :
    ReflTransGen (AdjAv K up dn k) r' r := by
  induction hh with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (adjAv_symm h hch hbc) ih

theorem chOf_pch' {s : ℕ} (hs : s < R) (h0 : s ≠ 0) : chOf (pch s) = s := by
  obtain ⟨h1, h2, h3⟩ := hch (pch s) (h.pch_lt s hs h0)
  exact h.pch_inj h1 hs h2 h0 h3

/-- A tree edge other than the parent chord of `c`. -/
theorem adjAv_of_child {k y s : ℕ} (_hk : k < K) (hs : s < R) (hs0 : s ≠ 0) (hy : prg s = y)
    (hne : s ≠ chOf k) : AdjAv K up dn k y s := by
  refine ⟨pch s, h.pch_lt s hs hs0, fun e => hne ?_, ?_⟩
  · rw [← e]; exact (chOf_pch' h hch hs hs0).symm
  · rcases h.ends s hs hs0 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨by rw [a1, hy], a2⟩
    · exact Or.inr ⟨a1, by rw [a2, hy]⟩

/-- Below `a`, the tree path to `r` avoids chord `k` if it does not pass through `chOf k`. -/
theorem rtg_of_anc {k a r : ℕ} (hk : k < K) (har : AncX R prg pch rem0 a r)
    (hav : ∀ w, AncX R prg pch rem0 a w → AncX R prg pch rem0 w r → w ≠ a → w ≠ chOf k) :
    ReflTransGen (AdjAv K up dn k) a r := by
  induction har with
  | refl => exact ReflTransGen.refl
  | tail hay hyr ih =>
    rename_i y s
    obtain ⟨hs, hs0, hps, -⟩ := hyr
    have has : AncX R prg pch rem0 a s := hay.tail ⟨hs, hs0, hps, by simp [rem0]⟩
    refine (ih fun w h1 h2 h3 => hav w h1 (h2.tail ⟨hs, hs0, hps, by simp [rem0]⟩) h3).tail ?_
    refine adjAv_of_child h hch hk hs hs0 hps (hav s has ReflTransGen.refl ?_)
    intro e
    rw [← e] at hay
    have := (AncX.pos_le h hay (hps ▸ h.prg_lt s hs hs0)).2.1
    have := h.pos_prg s hs hs0
    rw [hps] at this
    omega

/-- **Reachability avoiding a chord**: from `x`, the regions reachable without chord `k` are
those on the same side of `k` (inside or outside the subtree of its child endpoint). -/
theorem rtg_adjAv_iff {k x r : ℕ} (hk : k < K) (hx : x < R) :
    ReflTransGen (AdjAv K up dn k) x r ↔
      r < R ∧ (AncX R prg pch rem0 (chOf k) r ↔ AncX R prg pch rem0 (chOf k) x) := by
  obtain ⟨c1, c2, c3⟩ := hch k hk
  constructor
  · intro hh
    induction hh with
    | refl => exact ⟨hx, Iff.rfl⟩
    | tail hxy hbc ih =>
      rename_i y r'
      obtain ⟨i, hi, hik, hends⟩ := hbc
      obtain ⟨s, hs, hs0, hsi⟩ := h.pch_surj i hi
      have hsc : s ≠ chOf k := fun e => hik (by rw [← hsi, e, c3])
      obtain ⟨hyR, hy⟩ := ih
      -- the edge joins `prg s` and `s`
      have hpair : (y = prg s ∧ r' = s) ∨ (y = s ∧ r' = prg s) := by
        rcases h.ends s hs hs0 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rw [hsi] at a1 a2 <;>
          rcases hends with ⟨b1, b2⟩ | ⟨b1, b2⟩
        · exact Or.inl ⟨b1.symm.trans a1, b2.symm.trans a2⟩
        · exact Or.inr ⟨b2.symm.trans a2, b1.symm.trans a1⟩
        · exact Or.inr ⟨b1.symm.trans a1, b2.symm.trans a2⟩
        · exact Or.inl ⟨b2.symm.trans a2, b1.symm.trans a1⟩
      have hstep : AncX R prg pch rem0 (chOf k) s ↔ AncX R prg pch rem0 (chOf k) (prg s) := by
        rw [AncX.back_iff h]
        constructor
        · rintro (e | ⟨-, -, -, hh⟩)
          · exact absurd e.symm hsc
          · exact hh
        · intro hh
          exact Or.inr ⟨hs, hs0, by simp [rem0], hh⟩
      have hpR := h.prg_lt s hs hs0
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hs, hstep.trans hy⟩
      · exact ⟨hpR, hstep.symm.trans hy⟩
  · rintro ⟨hr, hiff⟩
    -- both on the subtree side, or both outside
    by_cases hcx : AncX R prg pch rem0 (chOf k) x
    · have hcr := hiff.2 hcx
      have hav : ∀ v, AncX R prg pch rem0 (chOf k) v → ReflTransGen (AdjAv K up dn k) (chOf k) v :=
        fun v hv => rtg_of_anc h hch hk hv fun w _ _ hw => hw
      exact (rtg_adjAv_symm h hch (hav x hcx)).trans (hav r hcr)
    · have hcr : ¬ AncX R prg pch rem0 (chOf k) r := fun hh => hcx (hiff.1 hh)
      have hav : ∀ v, v < R → ¬ AncX R prg pch rem0 (chOf k) v →
          ReflTransGen (AdjAv K up dn k) 0 v := fun v hv hnv =>
        rtg_of_anc h hch hk (anc_root h hv) fun w _ hwv _ e => by
          rw [e] at hwv; exact hnv hwv
      exact (rtg_adjAv_symm h hch (hav x hx hcx)).trans (hav r hr hcr)

end sides

/-! ## The final decomposition -/

section final

variable {R K D : ℕ} {ord pos prg pch isdn chOf : ℕ → ℕ}

/-- The normal form with the decomposition of the state `σ`. -/
def withDec (N : NF) (K R : ℕ) (σ : RS) : NF :=
  NF.mk N.chords N.arcs N.regions N.seq
    ((List.range K).map (fun k => (⟨σ.dpar k, σ.dlo k, σ.dhi k⟩ : DNode))) σ.root
    ((List.range R).map σ.lpar)

variable {N : NF} (hK : N.nChords = K) (hRR : N.nRegions = R)
variable (h : Rooted R K (fun i => (N.chord i).up) (fun i => (N.chord i).dn) ord pos prg pch)
variable (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch (chOf e) = e)
variable (hisdn : ∀ s, s < R → s ≠ 0 → (isdn s = 1 ↔ (N.chord (pch s)).dn = s))
variable {j : ℕ} {σ : RS} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
variable (hI : RInv R K D prg pch isdn chOf j σ gc cr)
variable (hna : ∀ t, t < R → IsTop pch σ.rem t → σ.act t ≠ 1)
include hK hRR h hch hisdn hI hna

theorem withDec_dnode {k : ℕ} (hk : k < K) :
    (withDec N K R σ).dnode k = ⟨σ.dpar k, σ.dlo k, σ.dhi k⟩ := by
  simp [withDec, NF.dnode, List.getD_eq_getElem?_getD, hk]

theorem withDec_lpar {r : ℕ} (hr : r < R) : (withDec N K R σ).lpar.getD r (withDec N K R σ).root =
    σ.lpar r := by
  simp [withDec, List.getD_eq_getElem?_getD, hr]

theorem withDec_lpar_out {r : ℕ} (hr : R ≤ r) :
    (withDec N K R σ).lpar.getD r (withDec N K R σ).root = σ.root := by
  simp [withDec, List.getD_eq_getElem?_getD, hr]

/-- All chords are removed and nothing is pending. -/
theorem final_cut {e : ℕ} (he : e < K) : σ.rem e = 1 ∧ σ.pend e ≠ 1 := by
  obtain ⟨c1, c2, c3⟩ := hch e he
  obtain ⟨t, htop, htc⟩ := exists_top h (rem := σ.rem) c1
  have ht := (AncX.pos_le h htc c1).1
  have hsing := (hI.i5 t ht htop (hna t ht htop)).1
  have hmem  := (mem_sub).2 ⟨c1, htc⟩
  rw [hsing, Finset.mem_singleton] at hmem
  rw [← hmem] at htop
  have hr : σ.rem e = 1 := by
    rcases htop with h0 | h1
    · exact absurd h0 c2
    · rwa [c3] at h1
  refine ⟨hr, fun hp => ?_⟩
  obtain ⟨t', ht', htop', hact', -⟩ := (hI.i3 e he hp).2 0 (by norm_num)
  exact hna t' ht' htop' hact'

theorem final_j : 1 ≤ j := by
  by_contra hj
  have := (hI.i7 (by omega)).2.1
  exact hna 0 h.R_pos (Or.inl rfl) this

/-- A placed code is in range. -/
theorem valid_range {x : ℕ} (hx : ValidC R K pch σ x) :
    (x % 2 = 0 ∧ x / 2 < K) ∨ (x % 2 = 1 ∧ x / 2 < R) := by
  rcases hx with ⟨a, b, -⟩ | ⟨a, b, -⟩
  · exact Or.inl ⟨a, b⟩
  · exact Or.inr ⟨a, b⟩

theorem valid_of_range {x : ℕ} (hx : (x % 2 = 0 ∧ x / 2 < K) ∨ (x % 2 = 1 ∧ x / 2 < R)) :
    ValidC R K pch σ x := by
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a, b, (final_cut hK hRR h hch hisdn hI hna b).1⟩
  · have htop : IsTop pch σ.rem (x / 2) := by
      by_cases h0 : x / 2 = 0
      · exact Or.inl h0
      · right
        exact (final_cut hK hRR h hch hisdn hI hna (h.pch_lt _ b h0)).1
    exact Or.inr ⟨a, b, htop, hna _ b htop⟩

/-- The parent code of the decomposition is `pcode` on placed codes. -/
theorem parentCode_eq {x : ℕ} (hx : ValidC R K pch σ x) :
    (withDec N K R σ).parentCode x = pcode σ x := by
  unfold NF.parentCode pcode
  rcases valid_range hK hRR h hch hisdn hI hna hx with ⟨a, b⟩ | ⟨a, b⟩
  · rw [ite_eq_left a, ite_eq_left a, withDec_dnode hK hRR h hch hisdn hI hna b]
  · have a' : x % 2 ≠ 0 := by omega
    rw [ite_eq_right a', ite_eq_right a', withDec_lpar hK hRR h hch hisdn hI hna b]

/-- Parents of placed codes are placed codes containing them. -/
theorem up_step {x : ℕ} (hx : ValidC R K pch σ x) :
    ValidC R K pch σ (pcode σ x) ∧ compOf gc x ⊆ compOf gc (pcode σ x) := by
  rcases hx with ⟨a, b, c⟩ | ⟨a, b, c, d⟩
  · obtain ⟨-, -, -, -, -, h6⟩ := hI.i1 _ b c
    have hp : pcode σ x = σ.dpar (x / 2) := by unfold pcode; rw [ite_eq_left a]
    rcases h6 with ⟨e1, -, -, -⟩ | ⟨p, hp', hrp, e1, -, e3⟩
    · have : pcode σ x = x := by rwo [hp, e1]
      rw [this]; exact ⟨Or.inl ⟨a, b, c⟩, le_rfl⟩
    · rw [hp, e1]
      have h2 : 2 * p % 2 = 0 := by omega
      have h3 : 2 * p / 2 = p := by omega
      refine ⟨Or.inl ⟨h2, by rwx [h3], by rwx [h3]⟩, ?_⟩
      simp only [compOf, ite_eq_left a, ite_eq_left h2, h3]
      exact e3
  · obtain ⟨-, h2⟩ := hI.i5 _ b c d
    have a' : x % 2 ≠ 0 := by omega
    have hp : pcode σ x = σ.lpar (x / 2) := by unfold pcode; rw [ite_eq_right a']
    rcases h2 with ⟨e1, -, -⟩ | ⟨p, hp', hrp, e1, -, e3⟩
    · have : pcode σ x = x := by rwo [hp, e1]
      rw [this]; exact ⟨Or.inr ⟨a, b, c, d⟩, le_rfl⟩
    · rw [hp, e1]
      have h2 : 2 * p % 2 = 0 := by omega
      have h3 : 2 * p / 2 = p := by omega
      refine ⟨Or.inl ⟨h2, by rwx [h3], by rwx [h3]⟩, ?_⟩
      simp only [compOf, ite_eq_right a', ite_eq_left h2, h3]
      intro v hv
      rw [Finset.mem_singleton] at hv
      rwx [hv]

/-- The chain of parents from a leaf stays among placed codes containing the leaf. -/
theorem chain_mem {r : ℕ} (hr : r < R) (i : ℕ) :
    ValidC R K pch σ ((withDec N K R σ).parentCode^[i] (2 * r + 1)) ∧
      r ∈ compOf gc ((withDec N K R σ).parentCode^[i] (2 * r + 1)) := by
  induction i with
  | zero =>
    simp only [Function.iterate_zero, id]
    have a : (2 * r + 1) % 2 = 1 := by omega
    have b : (2 * r + 1) / 2 = r := by omega
    refine ⟨valid_of_range hK hRR h hch hisdn hI hna (Or.inr ⟨a, by rwx [b]⟩), ?_⟩
    simp only [compOf, ite_eq_right (show (2 * r + 1) % 2 ≠ 0 by omega), b,
      Finset.mem_singleton]
  | succ i ih =>
    rw [Function.iterate_succ_apply', parentCode_eq hK hRR h hch hisdn hI hna ih.1]
    obtain ⟨u1, u2⟩ := up_step hK hRR h hch hisdn hI hna ih.1
    exact ⟨u1, u2 ih.2⟩

/-- The slots of a chord split its component. -/
theorem slot_facts {k s : ℕ} (hk : k < K) (hs : s ≤ 1) :
    ValidC R K pch σ (if s = 0 then σ.dlo k else σ.dhi k) ∧
    compOf gc (if s = 0 then σ.dlo k else σ.dhi k) = gc k ∩ sideSet R prg pch isdn chOf s k ∧
    pcode σ (if s = 0 then σ.dlo k else σ.dhi k) = 2 * k := by
  obtain ⟨hr, hp⟩ := final_cut hK hRR h hch hisdn hI hna hk
  exact hI.i2 k hk hr hp s hs

end final

end

end Chazelle.Core.Dec
