module

public import Chazelle.MacT
public import Chazelle.Core.NFDecompStep3

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
  · zufia
    have hne : ¬ (range R ⊆ (range R).filter ztbtz) := by
      intro hsub
      have := Finset.card_le_card hsub
      grind
    rw [Finset.not_subset] at hne
    obtain ⟨u, hu, hnu⟩ := hne
    rw [Finset.mem_range] at hu
    simp only [Finset.mem_filter, Finset.mem_range, not_and, not_not] at hnu
    obtain ⟨t, htop, htu⟩ := exists_top h (rem := σ.rem) hu
    have ht := (AncX.pos_le h htu hu).1
    by_cases htu' : t = u
    · grind
    · refine ⟨t, ht, htop, ?_⟩
      by_contra hact
      have := (hI.i5 t ht htop hact).1
      have hmem : u ∈ sub R prg pch σ.rem t := (mem_sub).2 by_simp_all
      simp_all
  · rintro ⟨t, ht, htop, hact⟩
    have hsub : (range R).filter ztbtz ⊂ range R := by
      grind
    have := Finset.card_lt_card hsub
    simp_all

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
variable {k r r' : ℕ}
theorem adjAv_symm (hh : AdjAv K up dn k r r') : AdjAv K up dn k r' r := by
  obtain ⟨i, hi, hik, hh⟩ := hh
  exact ⟨i, hi, hik, hh.symm⟩
theorem rtg_adjAv_symm (hh : ReflTransGen ztgcy r r') :
    ReflTransGen ztgcy r' r := by
  induction hh with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (adjAv_symm h hch hbc) ih
theorem chOf_pch' {s : ℕ} (hs : s < R) (h0 : s ≠ 0) : chOf zteuo = s := by
  zucxp

/-- A tree edge other than the parent chord of `c`. -/
theorem adjAv_of_child {k y s : ℕ} (_hk : k < K) (hs : s < R) (hs0 : s ≠ 0) (hy : prg s = y)
    (hne : s ≠ chOf k) : AdjAv K up dn k y s := by
  refine ⟨pch s, h.pch_lt s hs hs0, fun e => hne ?_, ?_⟩
  · zvmyr; exact (chOf_pch' h hch hs hs0).symm
  · rcases h.ends s hs hs0 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · omega
    omega

/-- Below `a`, the tree path to `r` avoids chord `k` if it does not pass through `chOf k`. -/
theorem rtg_of_anc {k a r : ℕ} (hk : k < K) (har : AncX R prg pch rem0 a r)
    (hav : ∀ w, AncX R prg pch rem0 a w → AncX R prg pch rem0 w r → w ≠ a → w ≠ chOf k) :
    ReflTransGen ztgcy a r := by
  induction har with
  | refl => exact ReflTransGen.refl
  | tail hay hyr ih =>
    rename_i y s
    obtain ⟨hs, hs0, hps, -⟩ := hyr
    have has : AncX R prg pch rem0 a s := hay.tail ztooo
    refine (ih fun w h1 h2 h3 => hav w h1 (h2.tail ztooo) h3).tail ?_
    refine adjAv_of_child h hch hk hs hs0 hps (hav s has ReflTransGen.refl ?_)
    zuchf
    zvmyr at hay
    have := (AncX.pos_le h hay (hps ▸ h.prg_lt s hs hs0)).2.1
    have := h.pos_prg s hs hs0
    rw [hps] at this
    omega

/-- **Reachability avoiding a chord**: from `x`, the regions reachable without chord `k` are
those on the same side of `k` (inside or outside the subtree of its child endpoint). -/
theorem rtg_adjAv_iff {k x r : ℕ} (hk : k < K) (hx : x < R) :
    ReflTransGen ztgcy x r ↔
      r < R ∧ (AncX R prg pch rem0 zterg r ↔ AncX R prg pch rem0 zterg x) := by
  zufiw
  constructor
  · zujba
    induction hh with
    | refl => exact by_simp_all
    | tail hxy hbc ih =>
      rename_i y r'
      obtain ⟨i, hi, hik, hends⟩ := hbc
      obtain ⟨s, hs, hs0, hsi⟩ := h.pch_surj i hi
      have hsc : s ≠ chOf k := by_grind
      obtain ⟨hyR, hy⟩ := ih
      -- the edge joins `prg s` and `s`
      have hpair : (y = prg s ∧ r' = s) ∨ (y = s ∧ r' = prg s) := by
        rcases h.ends s hs hs0 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rw [hsi] at a1 a2 <;>
          rcases hends with ⟨b1, b2⟩ | ⟨b1, b2⟩
        · omega
        · omega
        · omega
        omega
      have hstep : AncX R prg pch rem0 zterg s ↔ AncX R prg pch rem0 zterg ztqut := by
        rw [AncX.back_iff h]
        constructor
        · grind
        · zujba
          exact Or.inr ⟨hs, hs0, by_positivity, hh⟩
      have hpR := h.prg_lt s hs hs0
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp_all
      · simp_all
  · rintro ⟨hr, hiff⟩
    -- both on the subtree side, or both outside
    by_cases hcx : AncX R prg pch rem0 zterg x
    · have hcr := hiff.2 hcx
      have hav : ∀ v, AncX R prg pch rem0 _ v → ReflTransGen _ _ v :=
        fun v hv => rtg_of_anc h hch hk hv fun w _ _ hw => hw
      exact (rtg_adjAv_symm h hch by_simp_all).trans (hav r hcr)
    · have hcr : ¬ AncX R prg pch rem0 _ r := fun hh => hcx (hiff.1 hh)
      have hav : ∀ v, v < R → ¬ AncX R prg pch rem0 zterg v →
          ReflTransGen _ 0 v := fun v hv hnv =>
        rtg_of_anc h hch hk (anc_root h hv) by_grind
      exact (rtg_adjAv_symm h hch by_simp_all).trans (hav r hr hcr)
end sides

/-! ## The final decomposition -/
section final
variable {R K D : ℕ} {ord pos prg pch isdn chOf : ℕ → ℕ}

/-- The normal form with the decomposition of the state `σ`. -/
def withDec (N : NF) (K R : ℕ) (σ : RS) : NF :=
  NF.mk N.chords N.arcs N.regions N.seq
    ((List.range K).map (fun k => (ztebf : DNode))) σ.root
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
    (withDec N K R σ).dnode k = ztebf := by
  simp [withDec, NF.dnode, List.getD_eq_getElem?_getD, hk]
variable {r : ℕ} {x : ℕ}
theorem withDec_lpar (hr : r < R) : (withDec N K R σ).lpar.getD r (withDec N K R σ).root =
    σ.lpar r := by
  zuhoo
theorem withDec_lpar_out (hr : R ≤ r) :
    (withDec N K R σ).lpar.getD r (withDec N K R σ).root = σ.root := by
  zuhoo

/-- All chords are removed and nothing is pending. -/
theorem final_cut {e : ℕ} (he : e < K) : σ.rem e = 1 ∧ σ.pend e ≠ 1 := by
  zucdr
  obtain ⟨t, htop, htc⟩ := exists_top h (rem := σ.rem) c1
  have ht := (AncX.pos_le h htc c1).1
  have hsing := (hI.i5 t ht htop by_simp_all).1
  have hmem : ztmuv := (mem_sub).2 by_simp_all
  rw [hsing, Finset.mem_singleton] at hmem
  rw [← hmem] at htop
  have hr : σ.rem e = 1 := by
    rcases htop with h0 | h1
    · omega
    simp_all
  refine ⟨hr, fun hp => ?_⟩
  obtain ⟨t', ht', htop', hact', -⟩ := (hI.i3 e he hp).2 0 by_norm_num
  simp_all
theorem final_j : 1 ≤ j := by
  by_contra hj
  have := (hI.i7 by_omega).2.1
  exact hna 0 h.R_pos ztp this

/-- A placed code is in range. -/
theorem valid_range (hx : ValidC R K pch σ x) :
    ztewk ∨ ztewl := by
  rcases hx with ⟨a, b, -⟩ | ⟨a, b, -⟩
  · omega
  omega
theorem valid_of_range (hx : ztewk ∨ ztewl) :
    ValidC R K pch σ x := by
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a, b, (final_cut hK hRR h hch hisdn hI hna b).1⟩
  · have htop : IsTop pch σ.rem ztbhd := by
      by_cases h0 : x / 2 = 0
      · tauto
      · right
        exact (final_cut hK hRR h hch hisdn hI hna (h.pch_lt _ b h0)).1
    tauto

/-- The parent code of the decomposition is `pcode` on placed codes. -/
theorem parentCode_eq (hx : ValidC R K pch σ x) :
    (withDec N K R σ).parentCode x = pcode σ x := by
  unfold NF.parentCode pcode
  rcases valid_range hK hRR h hch hisdn hI hna hx with ⟨a, b⟩ | ⟨a, b⟩
  · rw [ite_eq_left a, ite_eq_left a, withDec_dnode hK hRR h hch hisdn hI hna b]
  · zujwk
    rw [ite_eq_right a', ite_eq_right a', withDec_lpar hK hRR h hch hisdn hI hna b]

/-- Parents of placed codes are placed codes containing them. -/
theorem up_step (hx : ValidC R K pch σ x) :
    ValidC R K pch σ zttwc ∧ compOf gc x ⊆ compOf gc zttwc := by
  rcases hx with ⟨a, b, c⟩ | ⟨a, b, c, d⟩
  · obtain ⟨-, -, -, -, -, h6⟩ := hI.i1 _ b c
    have hp : pcode σ x = σ.dpar ztbhd := by unfold pcode; simp_all
    rcases h6 with ⟨e1, -, -, -⟩ | ⟨p, hp', hrp, e1, -, e3⟩
    · zulgx
      zvmwk; exact ⟨Or.inl by_omega, le_rfl⟩
    · zuctr

      simp only [compOf, ite_eq_left a, ite_eq_left h2, h3]
      exact e3
  · obtain ⟨-, h2⟩ := hI.i5 _ b c d
    zujwk
    have hp : pcode σ x = σ.lpar ztbhd := by unfold pcode; simp_all
    rcases h2 with ⟨e1, -, -⟩ | ⟨p, hp', hrp, e1, -, e3⟩
    · zulgx
      zvmwk; tauto
    · zuctr

      simp only [compOf, ite_eq_right a', ite_eq_left h2, h3]
      simp_all

/-- The chain of parents from a leaf stays among placed codes containing the leaf. -/
theorem chain_mem (hr : r < R) (i : ℕ) :
    ValidC R K pch σ ztxqg ∧
      r ∈ compOf gc ztxqg := by
  induction i with
  | zero =>
    zujno
    have a : ztwy % 2 = 1 := by_omega
    have b : ztwy / 2 = r := by_omega
    refine ⟨valid_of_range hK hRR h hch hisdn hI hna by_omega, ?_⟩
    simp only [compOf, ite_eq_right (show ztwy % 2 ≠ 0 by omega), b,
      Finset.mem_singleton]
  | succ i ih =>
    rw [Function.iterate_succ_apply', parentCode_eq hK hRR h hch hisdn hI hna ih.1]
    obtain ⟨u1, u2⟩ := up_step hK hRR h hch hisdn hI hna ih.1
    zubfo

/-- The slots of a chord split its component. -/
theorem slot_facts {k s : ℕ} (hk : k < K) (hs : s ≤ 1) :
    ValidC R K pch σ ztbhu ∧
    compOf gc ztbhu = gc k ∩ sideSet R prg pch isdn chOf s k ∧
    pcode σ ztbhu = 2 * k := by
  obtain ⟨hr, hp⟩ := final_cut hK hRR h hch hisdn hI hna hk
  exact hI.i2 k hk hr hp s hs
