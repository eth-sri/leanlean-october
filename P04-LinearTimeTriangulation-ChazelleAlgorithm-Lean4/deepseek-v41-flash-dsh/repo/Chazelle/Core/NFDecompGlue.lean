module

public import Chazelle.Golf

public import Chazelle.Core.NFDecompRamLoop

/-!
# Tree decomposition (WP-C), part 21: glue for the specification

* `kids_deg`: the children of a region and its parent chord are among its chords;
* `Rooted.congr`: `Rooted` only reads its functions below `R`;
* `rb_addr`, `rb_addr2`: a robust memory fact reads below its bound;
* `inEnv_of`: a normal form readable below `A` gives the search environment;
* `nfAt_*_eq'`: the layout determines the chords, arcs, regions and sequence table.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec Relation

@[expose] public section

section kids

variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ}

/-- **Degrees**: the children of `v` and its parent chord are distinct chords of `v`. -/
theorem kids_deg (h : Rooted R K up dn ord pos prg pch) {lst : ℕ → List ℕ}
    (hlists : ∀ r, r < R → ∀ i, i ∈ lst r ↔ i < K ∧ (up i = r ∨ dn i = r))
    (hnd : ∀ r, r < R → (lst r).Nodup) {v : ℕ} (hv : v < R) :
    (kids R prg pch rem0 v).card + (if v = 0 then 0 else 1) ≤ (lst v).length := by
  classical
  have hinj : Set.InjOn pch (kids R prg pch rem0 v : Set ℕ) := by
    intro a ha b hb he
    rw [Finset.mem_coe, mem_kids] at ha hb
    exact h.pch_inj ha.1 hb.1 ha.2.1 hb.2.1 he
  have himg : (kids R prg pch rem0 v).image pch ⊆ (lst v).toFinset := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨c, hc, rfl⟩ := hi
    rw [mem_kids] at hc
    obtain ⟨c1, c2, c3, -⟩ := hc
    Ξ List.mem_toFinset, hlists v hv
    refine ⟨h.pch_lt c c1 c2, ?_⟩
    rcases h.ends c c1 c2 with ⟨a1, -⟩ | ⟨-, a2⟩
    · left; rw [a1, c3]
    · right; rw [a2, c3]
  have hcard1 : ((kids R prg pch rem0 v).image pch).card = (kids R prg pch rem0 v).card :=
    Finset.card_image_of_injOn hinj
  have hlen : (lst v).toFinset.card = (lst v).length := List.toFinset_card_of_nodup (hnd v hv)
  by_cases hv0 : v = 0
  · Ξ ite_eq_left hv0, Nat.add_zero, ← hcard1, ← hlen
    exact Finset.card_le_card himg
  · Ξ ite_eq_right hv0
    have hpv : pch v ∈ (lst v).toFinset := by
      Ξ List.mem_toFinset, hlists v hv
      refine ⟨h.pch_lt v hv hv0, ?_⟩
      rcases h.ends v hv hv0 with ⟨-, a2⟩ | ⟨a1, -⟩
      · right; exact a2
      · left; exact a1
    have hnot : pch v ∉ (kids R prg pch rem0 v).image pch := by
      intro hi
      rw [Finset.mem_image] at hi
      obtain ⟨c, hc, he⟩ := hi
      rw [mem_kids] at hc
      obtain ⟨c1, c2, c3, -⟩ := hc
      have := h.pch_inj c1 hv c2 hv0 he
      subst this
      have := h.pos_prg c c1 c2
      rw [c3] at this
      omega
    have hsub : insert (pch v) ((kids R prg pch rem0 v).image pch) ⊆ (lst v).toFinset :=
      Finset.insert_subset hpv himg
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot, hcard1, hlen] at this
    exact this

/-- `Rooted` only reads its functions below `R`. -/
theorem Rooted.congr (h : Rooted R K up dn ord pos prg pch) {ord' prg' pch' : ℕ → ℕ}
    (ho : ∀ j, j < R → ord' j = ord j) (hp : ∀ j, j < R → prg' j = prg j)
    (hc : ∀ j, j < R → pch' j = pch j) : Rooted R K up dn ord' pos prg' pch' where
  hR := h.hR
  ord_lt i hi := by rw [ho i hi]; exact h.ord_lt i hi
  pos_lt := h.pos_lt
  ord_pos r hr := by rw [ho _ (h.pos_lt r hr)]; exact h.ord_pos r hr
  pos_ord i hi := by rw [ho i hi]; exact h.pos_ord i hi
  root := by rw [ho 0 (by have := h.hR; omega)]; exact h.root
  prg_lt s hs hs0 := by rw [hp s hs]; exact h.prg_lt s hs hs0
  pos_prg s hs hs0 := by rw [hp s hs]; exact h.pos_prg s hs hs0
  pch_lt s hs hs0 := by rw [hc s hs]; exact h.pch_lt s hs hs0
  ends s hs hs0 := by rw [hc s hs, hp s hs]; exact h.ends s hs hs0
  pch_surj i hi := by
    obtain ⟨s, s1, s2, s3⟩ := h.pch_surj i hi
    exact ⟨s, s1, s2, by rw [hc s s1]; exact s3⟩
  ends_lt := h.ends_lt

end kids

section robust

/-- A robust fact at a fixed address reads below the bound. -/
theorem rb_addr {E : ℕ} {m : ℕ → ℕ} {a v : ℕ} (h : Robust E m fun m' => m' a = v) : a < E := by
  by_contra hge
  have := h (Function.update m a (v + 1)) (fun b hb => by
    rw [Function.update_of_ne (⋄)])
  simp at this

/-- A word reached through a pointer: the pointer and the word lie below the bound. -/
theorem rb_addr2 {E : ℕ} {m : ℕ → ℕ} {b o v : ℕ}
    (h : Robust E m fun m' => m' (m' b + o) = v) : b < E ∧ m b + o < E := by
  have hb : b < E := by
    by_contra hge
    have hX : b ≠ E + b + 1 + o := by omega
    have := h (Function.update (Function.update m b (E + b + 1)) (E + b + 1 + o) (v + 1))
      (fun a ha => by
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
    simp only at this
    rw [Function.update_of_ne hX, Function.update_self, Function.update_self] at this
    omega
  refine ⟨hb, ?_⟩
  by_contra hge
  have := h (Function.update m (m b + o) (v + 1)) (fun a ha => by
    rw [Function.update_of_ne (by omega)])
  simp only at this
  rw [Function.update_of_ne (show b ≠ m b + o by omega), Function.update_self] at this
  omega

/-- A robust fact with an inner offset read at a fixed address below the bound. -/
theorem rb_fix {E : ℕ} {m : ℕ → ℕ} {c : ℕ} (hc : c < E) {Φ : ℕ → (ℕ → ℕ) → Prop}
    (h : Robust E m fun m' => Φ (m' c) m') : Robust E m fun m' => Φ (m c) m' :=
  fun m' hm' => by
    have := h m' hm'
    simp only at this ⊢
    rwa [hm' c hc] at this

end robust

section env

/-- **The search environment** from a normal form readable below `A`. -/
theorem inEnv_of {m : ℕ → ℕ} {B A : ℕ} {N : NF} (h : NFWithin m B A N) :
    InEnv m A N.nRegions N.nChords (m (B + 3)) (m (B + 5)) (m (B + 7))
      (fun i => (N.chord i).up) (fun i => (N.chord i).dn) (fun r => (N.region r).chords) := by
  have hN := h.nfAt
  refine ⟨fun i hi => ?_, fun r hr => ?_, fun r hr t ht => ?_⟩
  · obtain ⟨-, -, -, a1, a2⟩ := hN.2.2.2.2.2.1 i hi
    have r4 : Robust A m fun m' => m' (m' (B + 3) + (5 * i + 4)) = (N.chord i).dn :=
      fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.1 i hi).2.2.2.2
        simpa only [Nat.add_assoc] using this
    have := (rb_addr2 r4).2
    exact ⟨a1, a2, ⋄⟩
  · obtain ⟨-, a2, -, -, -⟩ := hN.2.2.2.2.2.2.2.1 r hr
    have r4 : Robust A m fun m' => m' (m' (B + 5) + (5 * r + 4)) = (N.region r).wt :=
      fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
        simpa only [Nat.add_assoc] using this
    have := (rb_addr2 r4).2
    exact ⟨a2, ⋄⟩
  · obtain ⟨-, -, -, -, a5⟩ := hN.2.2.2.2.2.2.2.1 r hr
    have r4 : Robust A m fun m' => m' (m' (B + 5) + (5 * r + 4)) = (N.region r).wt :=
      fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
        simpa only [Nat.add_assoc] using this
    obtain ⟨hB5, hw⟩ := rb_addr2 r4
    have hc : m (B + 5) + 5 * r + 3 < A := ⋄
    have r5 : Robust A m fun m' => m' (m' (B + 7) + m' (m (B + 5) + 5 * r + 3) + t) =
        (N.region r).chords.getD t 0 := fun m' hm' => by
      have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht
      rwa [hm' (B + 5) hB5] at this
    have r6 := rb_fix (Φ := fun x m' => m' (m' (B + 7) + x + t) = (N.region r).chords.getD t 0)
      hc r5
    have r7 : Robust A m fun m' => m' (m' (B + 7) + (m (m (B + 5) + 5 * r + 3) + t)) =
        (N.region r).chords.getD t 0 := fun m' hm' => by
      have := r6 m' hm'
      simpa only [Nat.add_assoc] using this
    have := (rb_addr2 r7).2
    exact ⟨a5 t ht, ⋄⟩

/-- Region records are determined by their fields. -/
theorem rRec_ext' {a b : RRec} (h1 : a.arcs = b.arcs) (h2 : a.chords = b.chords)
    (h3 : a.wt = b.wt) : a = b := by
  obtain ⟨_, _, _⟩ := a
  obtain ⟨_, _, _⟩ := b
  simp_all

/-- Chord records are determined by their fields. -/
theorem cRec_ext' {a b : CRec} (h1 : a.h = b.h) (h2 : a.lp = b.lp) (h3 : a.rp = b.rp)
    (h4 : a.up = b.up) (h5 : a.dn = b.dn) : a = b := by
  obtain ⟨_, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _⟩ := b
  simp_all

/-- Arc records are determined by their fields. -/
theorem aRec_ext' {a b : ARec} (h1 : a.reg = b.reg) (h2 : a.s.edge = b.s.edge)
    (h3 : a.s.hgt = b.s.hgt) (h4 : a.e.edge = b.e.edge) (h5 : a.e.hgt = b.e.hgt) : a = b := by
  obtain ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ := a
  obtain ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ := b
  simp_all

/-- Lists of naturals with equal lengths and entries are equal. -/
theorem list_ext_getD {l l' : List ℕ} (hl : l'.length = l.length)
    (h : ∀ t, t < l.length → l'.getD t 0 = l.getD t 0) : l' = l := by
  apply List.ext_getElem hl
  intro t h1 h2
  have := h t h2
  rwa [getD_of_lt h1, getD_of_lt h2] at this

/-- The layout determines the chord records. -/
theorem nfAt_chords_eq' {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    N'.chords = N.chords := by
  have hl : N'.chords.length = N.chords.length := h'.1.symm.trans h.1
  apply List.ext_getElem hl
  intro j hj hj'
  have e := h.2.2.2.2.2.1 j hj'
  have e' := h'.2.2.2.2.2.1 j hj
  have a1 : N.chord j = N.chords[j] := getD_of_lt hj' _
  have a2 : N'.chord j = N'.chords[j] := getD_of_lt hj _
  Ξ ← a1, ← a2
  exact cRec_ext' (e'.1.symm.trans e.1) (e'.2.1.symm.trans e.2.1) (e'.2.2.1.symm.trans e.2.2.1)
    (e'.2.2.2.1.symm.trans e.2.2.2.1) (e'.2.2.2.2.symm.trans e.2.2.2.2)

/-- The layout determines the arc records. -/
theorem nfAt_arcs_eq' {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    N'.arcs = N.arcs := by
  have hl : N'.arcs.length = N.arcs.length := h'.2.1.symm.trans h.2.1
  apply List.ext_getElem hl
  intro j hj hj'
  have e := h.2.2.2.2.2.2.1 j hj'
  have e' := h'.2.2.2.2.2.2.1 j hj
  have a1 : N.arc j = N.arcs[j] := getD_of_lt hj' _
  have a2 : N'.arc j = N'.arcs[j] := getD_of_lt hj _
  Ξ ← a1, ← a2
  exact aRec_ext' (e'.1.symm.trans e.1) (e'.2.1.symm.trans e.2.1) (e'.2.2.1.symm.trans e.2.2.1)
    (e'.2.2.2.1.symm.trans e.2.2.2.1) (e'.2.2.2.2.symm.trans e.2.2.2.2)

/-- The layout determines the region records. -/
theorem nfAt_regions_eq' {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    N'.regions = N.regions := by
  have hl : N'.regions.length = N.regions.length := h'.2.2.1.symm.trans h.2.2.1
  apply List.ext_getElem hl
  intro j hj hj'
  have e := h.2.2.2.2.2.2.2.1 j hj'
  have e' := h'.2.2.2.2.2.2.2.1 j hj
  have a1 : N.region j = N.regions[j] := getD_of_lt hj' _
  have a2 : N'.region j = N'.regions[j] := getD_of_lt hj _
  Ξ ← a1, ← a2
  refine rRec_ext' ?_ ?_ (e'.2.2.1.symm.trans e.2.2.1)
  · exact list_ext_getD (e'.1.symm.trans e.1) fun t ht => by
      Ξ ← e.2.2.2.1 t ht, ← e'.2.2.2.1 t (by rw [← e'.1, e.1]; exact ht)
  · exact list_ext_getD (e'.2.1.symm.trans e.2.1) fun t ht => by
      Ξ ← e.2.2.2.2 t ht, ← e'.2.2.2.2 t (by rw [← e'.2.1, e.2.1]; exact ht)

end env

end

end Chazelle.Core.DecR
