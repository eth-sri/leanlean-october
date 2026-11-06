module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvOrgDo
public import Chazelle.Core.SweepEvTasks3

/-!
# The sweep (WP-D), stage 3: a batch of origins (the invariant)

`BatchInv P J N₂ cs lo O c`: after the endpoint queries `O` of one iteration (started at `cs`, with
the best candidate cleared, gathered arcs `lo`), there is a set `A` of accepted triples
`(j, e, h)` (`CandOK`) such that

* the table slots are those of `cs` or hold an accepted triple, the rest of the memory below the
  allocator of `cs` is unchanged;
* every valid query of `O` whose chord ends on the `C₁` part beyond the start with its hit on `lo`
  is accepted at its attachment (`comp`);
* the best candidate is an accepted triple of least offset beyond the key, and its label list
  (without repetitions) holds the labels of the accepted triples at its offset (up to four).

`batch_step`: one origin (`orgDo_irs`'s post) keeps the invariant.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-- A valid origin: a point of `C₂` other than the shared vertex and the top of `C₂`. -/
def ValidJ (J : Merge.Junction) (Q : Polygon) (N : NF) (j : ℕ) : Prop :=
  endOrigin J Q N j ∈ J.right.set ∧ endOrigin J Q N j ≠ J.shared ∧ endOrigin J Q N j ≠ J.right.top

/-- The offset of an accepted triple. -/
noncomputable def offT (P : Polygon) (J : Merge.Junction) (t : ℕ × ℕ × ℕ) : ℝ :=
  offK P J t.2.1 t.2.2

section
variable (N : NF) (j : ℕ)
include N j
/-- The labels of the chord of query `j`. -/
def upOf : ℕ := (N.chord (j / 2)).up
def dnOf : ℕ := (N.chord (j / 2)).dn


end

/-- **The facts of a batch** for the accepted triples `A`. -/
structure BatchA (P : Polygon) (J : Merge.Junction) (N₂ : NF) (cs : Config) (lo : Set Point)
    (O : Set ℕ) (c : Config) (A : Set (ℕ × ℕ × ℕ)) : Prop where
  acc : ∀ t ∈ A, t.1 ∈ O ∧ t.1 < 2 * N₂.nChords ∧
    CandOK P J (N₂.F (chainModel J.right) (Qof P)) (endOrigin J (Qof P) N₂ t.1) (endDir t.1)
      t.2.1 t.2.2
  memT : ∀ x, x < cs.nreg ALLOC → (x < cs.nreg cTB ∨ cs.nreg cTB + 6 * N₂.nChords ≤ x) →
    c.nmem x = cs.nmem x
  slot : ∀ j, j < 2 * N₂.nChords →
    (c.nmem (cs.nreg cTB + 3 * j) = cs.nmem (cs.nreg cTB + 3 * j) ∧
      c.nmem (cs.nreg cTB + 3 * j + 1) = cs.nmem (cs.nreg cTB + 3 * j + 1) ∧
      c.nmem (cs.nreg cTB + 3 * j + 2) = cs.nmem (cs.nreg cTB + 3 * j + 2)) ∨
    ∃ e h, (j, e, h) ∈ A ∧ c.nmem (cs.nreg cTB + 3 * j) = 1 ∧
      c.nmem (cs.nreg cTB + 3 * j + 1) = e ∧ c.nmem (cs.nreg cTB + 3 * j + 2) = h
  flag : ∀ t ∈ A, c.nmem (cs.nreg cTB + 3 * t.1) = 1
  comp : ∀ j ∈ O, j < 2 * N₂.nChords → ValidJ J (Qof P) N₂ j → ∀ (p : ℕ) (t : ℝ),
    SideAttach (chainModel J.whole).W
      (Merge.shoot J.whole (endOrigin J (Qof P) N₂ j) (endDir j)) p t →
    sidePt (chainModel J.whole).W p t = rayPt (endOrigin J (Qof P) N₂ j) (endDir j)
      (J.whole.hitParam (endOrigin J (Qof P) N₂ j) (endDir j)) →
    (Lst J : ℝ) < oW J (p + t) → sidePt (chainModel J.whole).W p t ≠ J.shared →
    J.whole.hitParam (endOrigin J (Qof P) N₂ j) (endDir j) <
      J.right.hitParam (endOrigin J (Qof P) N₂ j) (endDir j) →
    rayPt (endOrigin J (Qof P) N₂ j) (endDir j)
      (J.whole.hitParam (endOrigin J (Qof P) N₂ j) (endDir j)) ∈ lo →
    ∃ h, (chainModel J.whole).param (Qof P) ⟨p, h⟩ = t ∧ (j, p, h) ∈ A
  fF : c.nreg bF ≤ 1
  fN : c.nreg bN ≤ 4
  bAcc : c.nreg bF = 1 → (∃ j, (j, c.nreg bE, c.nreg bH) ∈ A) ∧
    offK P J (cs.nreg kE) (cs.nreg kH) < offK P J (c.nreg bE) (c.nreg bH)
  bMin : ∀ t ∈ A, offK P J (cs.nreg kE) (cs.nreg kH) < offT P J t →
    c.nreg bF = 1 ∧ offK P J (c.nreg bE) (c.nreg bH) ≤ offT P J t
  lNd : c.nreg bF = 1 → (lblOf c bN bL).Nodup
  lSrc : c.nreg bF = 1 → ∀ x ∈ lblOf c bN bL, ∃ t ∈ A,
    offT P J t = offK P J (c.nreg bE) (c.nreg bH) ∧ (x = upOf N₂ t.1 ∨ x = dnOf N₂ t.1)
  lCov : c.nreg bF = 1 → ∀ t ∈ A, offT P J t = offK P J (c.nreg bE) (c.nreg bH) →
    (upOf N₂ t.1 ∈ lblOf c bN bL ∨ (lblOf c bN bL).length = 4) ∧
      (dnOf N₂ t.1 ∈ lblOf c bN bL ∨ (lblOf c bN bL).length = 4)
  val : ∀ t ∈ A, ValidJ J (Qof P) N₂ t.1

/-- **The invariant of a batch of origins** (started at `cs`). -/
def BatchInv (P : Polygon) (J : Merge.Junction) (N₂ : NF) (cs : Config) (lo : Set Point)
    (O : Set ℕ) (c : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → ¬ LR r → r ≠ ALLOC → c.nreg r = cs.nreg r) ∧
    cs.nreg ALLOC ≤ c.nreg ALLOC ∧ ∃ A, BatchA P J N₂ cs lo O c A

/-! ## Label lists -/

section
variable {l : List ℕ}
theorem addL_nodup (h : l.Nodup) (v : ℕ) : (addL l v).Nodup := by
  grind [addL]

theorem mem_addL_of_mem {v x : ℕ} (h : x ∈ l) : x ∈ addL l v := by
  unfold addL; split_ifs
  · exact h
  · exact List.mem_append_left _ h

theorem addL_len4 (h : l.length = 4) (v : ℕ) : (addL l v).length = 4 := by
  simp_all [addL] 

theorem addL_self (h : l.length ≤ 4) (v : ℕ) :
    v ∈ addL l v ∨ (addL l v).length = 4 := by
  aesop (add simp [addL]) (add safe (by omega))


end

theorem lblOf_len (c : Config) : (lblOf c bN bL).length ≤ 4 := by
  core_grind

section
variable {l : List ℕ}
/-- Membership or fullness survives `addL`. -/
theorem memOrFull_addL {x : ℕ} (h : x ∈ l ∨ l.length = 4) (v : ℕ) :
    x ∈ addL l v ∨ (addL l v).length = 4 := by
  rcases h with h | h
  · exact Or.inl (mem_addL_of_mem h)
  · exact Or.inr (addL_len4 h v)

theorem addL_len_le (h : l.length ≤ 4) (v : ℕ) : (addL l v).length ≤ 4 :=
  addL_length_le h v

/-! ## The table -/


end

section
variable (m : ℕ → ℕ) (T j e h : ℕ)
theorem tabUpd_0 : tabUpd m T j e h (T + 3 * j) = 1 := by
  simp_all [tabUpd, upd_same] <;> omega_nf

theorem tabUpd_1 : tabUpd m T j e h (T + 3 * j + 1) = e := by
  simp_all [tabUpd, upd_same] <;> omega_nf

theorem tabUpd_2 : tabUpd m T j e h (T + 3 * j + 2) = h := by
  unfold tabUpd; simp_all


end

theorem tabUpd_o (m : ℕ → ℕ) {T j e h x : ℕ} (h0 : x ≠ T + 3 * j) (h1 : x ≠ T + 3 * j + 1)
    (h2 : x ≠ T + 3 * j + 2) : tabUpd m T j e h x = m x := by
  simp_all [tabUpd] 

variable {P : Polygon} {J : Merge.Junction} {N₂ : NF}

/-- **The start of a batch.** -/
theorem batch_base {cs : Config} {lo : Set Point} (hbF : cs.nreg bF = 0) (hbN : cs.nreg bN ≤ 4) :
    BatchInv P J N₂ cs lo ∅ cs := by
  refine ⟨fun _ _ _ _ _ => rfl, le_rfl, ∅, ⟨fun t ht => absurd ht (Set.notMem_empty t),
    fun _ _ _ => rfl, fun j _ => Or.inl ⟨rfl, rfl, rfl⟩, fun t ht => absurd ht (Set.notMem_empty t),
    fun j hj => absurd hj (Set.notMem_empty j),
    by omega, hbN, fun h => by omega, fun t ht => absurd ht (Set.notMem_empty t),
    fun h => by omega, fun h => by omega, fun h => by omega,
    fun t ht => absurd ht (Set.notMem_empty t)⟩⟩

/-- **The invariant ignores the loop registers.** -/
theorem batch_stable {cs c c' : Config} {lo : Set Point} {O : Set ℕ}
    (h : BatchInv P J N₂ cs lo O c) (hr : ∀ r, ¬ LR r → c'.nreg r = c.nreg r)
    (hm : c'.nmem = c.nmem) : BatchInv P J N₂ cs lo O c' := by
  obtain ⟨hreg, hA, A, hB⟩ := h
  have nLR : ∀ q, LblR bN bL q ∨ q = bF ∨ q = bE ∨ q = bH → ¬ LR q := fun q hq => by
    unfold LR LblR oK oS bN bL bF bE bH sw at *; omega
  have eF := hr bF (nLR _ (Or.inr (Or.inl rfl)))
  have eE := hr bE (nLR _ (Or.inr (Or.inr (Or.inl rfl))))
  have eH := hr bH (nLR _ (Or.inr (Or.inr (Or.inr rfl))))
  have eN := hr bN (nLR _ (Or.inl (Or.inl rfl)))
  have eL : lblOf c' bN bL = lblOf c bN bL := lblOf_congr fun q hq => hr q (nLR q (Or.inl hq))
  have eA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC (by omega_nf)
  refine ⟨fun r h1 h2 h3 h4 => (hr r h3).trans (hreg r h1 h2 h3 h4), by omega, A,
    ⟨hB.acc, fun x h1 h2 => by rw [hm]; exact hB.memT x h1 h2,
    fun j hj => by rw [hm]; exact hB.slot j hj, fun t ht => by rw [hm]; exact hB.flag t ht, hB.comp, by rw [eF]; exact hB.fF,
    by rw [eN]; exact hB.fN, ?_, ?_, ?_, ?_, ?_, hB.val⟩⟩
  · intro h; rw [eE, eH]; rw [eF] at h; exact hB.bAcc h
  · intro t ht h1; rw [eF, eE, eH]; exact hB.bMin t ht h1
  · intro h; rw [eL]; rw [eF] at h; exact hB.lNd h
  · intro h; rw [eL, eE, eH]; rw [eF] at h; exact hB.lSrc h
  · intro h; rw [eL, eE, eH]; rw [eF] at h; exact hB.lCov h

set_option maxHeartbeats 4000000 in
/-- **One origin keeps the invariant of the batch.** -/
theorem batch_step {cs c c' : Config} {lo : Set Point} {O : Set ℕ} {k s : ℕ}
    (hInv : BatchInv P J N₂ cs lo O c) (hj : 2 * k + s < 2 * N₂.nChords) (hs : s ≤ 1)
    (hud : (N₂.chord k).up ≠ (N₂.chord k).dn)
    (hT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg ALLOC)
    (hres : CandRes P J (N₂.F (chainModel J.right) (Qof P)) (c.nreg cTB) (2 * k + s)
      (N₂.chord k).up (N₂.chord k).dn (endOrigin J (Qof P) N₂ (2 * k + s)) (endDir (2 * k + s))
      c c')
    (hcomp : ValidJ J (Qof P) N₂ (2 * k + s) →
      CandComp P J (N₂.F (chainModel J.right) (Qof P)) (c.nreg cTB) (2 * k + s)
        (N₂.chord k).up (N₂.chord k).dn (endOrigin J (Qof P) N₂ (2 * k + s)) (endDir (2 * k + s))
        lo c c')
    (hval : ¬ ValidJ J (Qof P) N₂ (2 * k + s) → RejAt c c')
    (hfr : ∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    BatchInv P J N₂ cs lo (insert (2 * k + s) O) c' := by
  obtain ⟨hreg, hAc, A, hB⟩ := hInv
  have hk2 : (2 * k + s) / 2 = k := by omega
  have hup : upOf N₂ (2 * k + s) = (N₂.chord k).up := by grind [upOf]
  have hdn : dnOf N₂ (2 * k + s) = (N₂.chord k).dn := by grind [dnOf]
  have keepS : ∀ r, 240000 ≤ r → r < 250000 → ¬ OrgR r → ¬ LR r → c.nreg r = cs.nreg r :=
    fun r h1 h2 h3 h4 => hreg r (band_sw_not ⟨h1, h2⟩) h3 h4 (by omega_nf)
  have hTc : c.nreg cTB = cs.nreg cTB :=
    keepS _ (by omega_nf) (by omega_nf)
      (by omega_nf)
      (by omega_nf)
  have hkE : c.nreg kE = cs.nreg kE :=
    keepS _ (by omega_nf) (by omega_nf)
      (by omega_nf)
      (by omega_nf)
  have hkH : c.nreg kH = cs.nreg kH :=
    keepS _ (by omega_nf) (by omega_nf)
      (by omega_nf)
      (by omega_nf)
  rw [hTc] at hres hcomp
  set j := 2 * k + s with hjd
  set a := endOrigin J (Qof P) N₂ j
  set σ := endDir j
  set S₂ := N₂.F (chainModel J.right) (Qof P)
  set oL := offK P J (cs.nreg kE) (cs.nreg kH) with hoL
  have hTA : (cs.nreg cTB) + 6 * N₂.nChords ≤ c.nreg ALLOC := by omega
  -- the new set of accepted triples
  set A' : Set (ℕ × ℕ × ℕ) := A ∪ {t | t.1 = j ∧ ValidJ J (Qof P) N₂ j ∧
    AccAt P J S₂ (cs.nreg cTB) j (N₂.chord k).up (N₂.chord k).dn a σ c c' t.2.1 t.2.2} with hA'd
  have hsub : A ⊆ A' := Set.subset_union_left
  have hreg' : ∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → ¬ LR r → r ≠ ALLOC →
      c'.nreg r = cs.nreg r := fun r h1 h2 h3 h4 => (hfr r h1 h2 h4).trans (hreg r h1 h2 h3 h4)
  refine ⟨hreg', by omega, A', ?_⟩
  -- common fields
  have acc' : ∀ t ∈ A', t.1 ∈ insert j O ∧ t.1 < 2 * N₂.nChords ∧
      CandOK P J S₂ (endOrigin J (Qof P) N₂ t.1) (endDir t.1) t.2.1 t.2.2 := by
    rintro t (ht | ⟨ht1, -, ht2⟩)
    · obtain ⟨h1, h2, h3⟩ := hB.acc t ht
      grind
    · rw [ht1]; exact ⟨Set.mem_insert _ _, hj, ht2.1⟩
  have comp' : ∀ j' ∈ insert j O, j' < 2 * N₂.nChords → ValidJ J (Qof P) N₂ j' →
      ∀ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W
        (Merge.shoot J.whole (endOrigin J (Qof P) N₂ j') (endDir j')) p t →
      sidePt (chainModel J.whole).W p t = rayPt (endOrigin J (Qof P) N₂ j') (endDir j')
        (J.whole.hitParam (endOrigin J (Qof P) N₂ j') (endDir j')) →
      (Lst J : ℝ) < oW J (p + t) → sidePt (chainModel J.whole).W p t ≠ J.shared →
      J.whole.hitParam (endOrigin J (Qof P) N₂ j') (endDir j') <
        J.right.hitParam (endOrigin J (Qof P) N₂ j') (endDir j') →
      rayPt (endOrigin J (Qof P) N₂ j') (endDir j')
        (J.whole.hitParam (endOrigin J (Qof P) N₂ j') (endDir j')) ∈ lo →
      ∃ h, (chainModel J.whole).param (Qof P) ⟨p, h⟩ = t ∧ (j', p, h) ∈ A' := by
    intro j' hj' hj'n hv p t h1 h2 h3 h4 h5 h6
    rcases Set.mem_insert_iff.1 hj' with rfl | hj'
    · obtain ⟨h, hh, hacc⟩ := hcomp hv p t h1 h2 h3 h4 h5 h6
      grind
    · obtain ⟨h, hh, hm⟩ := hB.comp j' hj' hj'n hv p t h1 h2 h3 h4 h5 h6
      grind
  have val' : ∀ t ∈ A', ValidJ J (Qof P) N₂ t.1 := by
    rintro t (ht | ⟨ht1, hv, -⟩)
    · exact hB.val t ht
    grind
  by_cases hacc : ∃ e h, ValidJ J (Qof P) N₂ j ∧
    AccAt P J S₂ (cs.nreg cTB) j (N₂.chord k).up (N₂.chord k).dn a σ c c' e h
  · obtain ⟨e, h, hvj, hAcc⟩ := hacc
    obtain ⟨hok, hmem, hoff⟩ := hAcc
    -- uniqueness of the new triple
    have huq : ∀ t ∈ A', t ∉ A → t = (j, e, h) := by
      rintro ⟨j₁, e₁, h₁⟩ (ht | ⟨ht1, -, -, hmem₁, -⟩) hn
      · grind
      · simp only at ht1 hmem₁
        subst ht1
        have w1 := hmem₁ ((cs.nreg cTB) + 3 * j + 1) (by omega)
        have w2 := hmem₁ ((cs.nreg cTB) + 3 * j + 2) (by omega)
        rw [hmem ((cs.nreg cTB) + 3 * j + 1) (by omega), tabUpd_1, tabUpd_1] at w1
        rw [hmem ((cs.nreg cTB) + 3 * j + 2) (by omega), tabUpd_2, tabUpd_2] at w2
        rw [w1, w2]
    have hnew : (j, e, h) ∈ A' := Or.inr ⟨rfl, hvj, hok, hmem, hoff⟩
    have hmA : ∀ t ∈ A', t ∈ A ∨ t = (j, e, h) := fun t ht => by
      grind
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hoff
    rw [hkE, hkH] at o3 o4 o5 o6
    have hoffN : offT P J (j, e, h) = offK P J e h := rfl
    refine ⟨acc', fun x h1 h2 => ?_, fun j' hj' => ?_, fun t ht => ?_, comp', o1, o2, ?_, ?_, ?_, ?_, ?_, val'⟩
    · rw [hmem x (by omega), tabUpd_o _ (by omega) (by omega) (by omega)]
      exact hB.memT x h1 h2
    · by_cases hjj : j' = j
      · subst hjj
        refine Or.inr ⟨e, h, hnew, ?_, ?_, ?_⟩
        · rw [hmem _ (by omega), tabUpd_0]
        · rw [hmem _ (by omega), tabUpd_1]
        · rw [hmem _ (by omega), tabUpd_2]
      · have e0 : c'.nmem ((cs.nreg cTB) + 3 * j') = c.nmem ((cs.nreg cTB) + 3 * j') := by
          rw [hmem _ (by omega), tabUpd_o _ (by omega) (by omega) (by omega)]
        have e1 : c'.nmem ((cs.nreg cTB) + 3 * j' + 1) = c.nmem ((cs.nreg cTB) + 3 * j' + 1) := by
          rw [hmem _ (by omega), tabUpd_o _ (by omega) (by omega) (by omega)]
        have e2 : c'.nmem ((cs.nreg cTB) + 3 * j' + 2) = c.nmem ((cs.nreg cTB) + 3 * j' + 2) := by
          rw [hmem _ (by omega), tabUpd_o _ (by omega) (by omega) (by omega)]
        rw [e0, e1, e2]
        rcases hB.slot j' hj' with h' | ⟨e', h'', hm, w⟩
        · omega
        · exact Or.inr ⟨e', h'', hsub hm, w⟩
    · rcases hmA t ht with ht | rfl
      · have htj := (hB.acc t ht).2.1
        by_cases hjj : t.1 = j
        · rw [hjj, hmem _ (by omega), tabUpd_0]
        · rw [hmem _ (by omega), tabUpd_o _ (by omega) (by omega) (by omega)]
          exact hB.flag t ht
      · rw [hmem _ (by omega), tabUpd_0]
    -- the best candidate: four cases of the offer
    · intro hF'
      by_cases hlt : oL < offK P J e h
      · by_cases hnb : c.nreg bF ≠ 1 ∨ offK P J e h < offK P J (c.nreg bE) (c.nreg bH)
        · obtain ⟨-, w2, w3, -, -⟩ := o4 hlt hnb
          rw [w2, w3]; exact ⟨⟨j, hnew⟩, hlt⟩
        · push Not at hnb
          rcases hnb.2.lt_or_eq with hlt2 | heq
          · have hs' := o6 hlt hnb.1 hlt2
            rw [hs'.2.1, hs'.2.2.1]; rw [hs'.1] at hF'
            obtain ⟨⟨j₁, hj₁⟩, hh⟩ := hB.bAcc hF'
            exact ⟨⟨j₁, hsub hj₁⟩, hh⟩
          · obtain ⟨w1, w2, w3, -⟩ := o5 hlt hnb.1 heq.symm
            rw [w2, w3]
            obtain ⟨⟨j₁, hj₁⟩, hh⟩ := hB.bAcc hnb.1
            exact ⟨⟨j₁, hsub hj₁⟩, hh⟩
      · have hs' := o3 hlt
        rw [hs'.2.1, hs'.2.2.1]; rw [hs'.1] at hF'
        obtain ⟨⟨j₁, hj₁⟩, hh⟩ := hB.bAcc hF'
        exact ⟨⟨j₁, hsub hj₁⟩, hh⟩
    · intro t ht hlt
      rcases hmA t ht with ht | rfl
      · obtain ⟨hF, hle⟩ := hB.bMin t ht hlt
        have hlt' : oL < offK P J e h ∨ ¬ oL < offK P J e h := em _
        rcases hlt' with hl | hl
        · by_cases hnb : c.nreg bF ≠ 1 ∨ offK P J e h < offK P J (c.nreg bE) (c.nreg bH)
          · grind
          · push Not at hnb
            rcases hnb.2.lt_or_eq with hlt2 | heq
            · have hs' := o6 hl hnb.1 hlt2
              rw [hs'.1, hs'.2.1, hs'.2.2.1]; grind
            grind
        · have hs' := o3 hl
          rw [hs'.1, hs'.2.1, hs'.2.2.1]; grind
      · rw [hoffN] at hlt ⊢
        by_cases hnb : c.nreg bF ≠ 1 ∨ offK P J e h < offK P J (c.nreg bE) (c.nreg bH)
        · grind
        · push Not at hnb
          rcases hnb.2.lt_or_eq with hlt2 | heq
          · have hs' := o6 hlt hnb.1 hlt2
            rw [hs'.1, hs'.2.1, hs'.2.2.1]; omega
          grind
    · -- no repetitions
      intro hF'
      by_cases hlt : oL < offK P J e h
      · by_cases hnb : c.nreg bF ≠ 1 ∨ offK P J e h < offK P J (c.nreg bE) (c.nreg bH)
        · obtain ⟨-, -, -, w4, -⟩ := o4 hlt hnb
          rw [w4]; simpa using hud
        · push Not at hnb
          rcases hnb.2.lt_or_eq with hlt2 | heq
          · have hs' := o6 hlt hnb.1 hlt2
            rw [hs'.2.2.2.1]; exact hB.lNd hnb.1
          · obtain ⟨-, -, -, w4⟩ := o5 hlt hnb.1 heq.symm
            rw [w4]; exact addL_nodup (addL_nodup (hB.lNd hnb.1) _) _
      · have hs' := o3 hlt
        rw [hs'.2.2.2.1]; rw [hs'.1] at hF'; exact hB.lNd hF'
    · -- the sources of the labels
      intro hF' x hx
      by_cases hlt : oL < offK P J e h
      · by_cases hnb : c.nreg bF ≠ 1 ∨ offK P J e h < offK P J (c.nreg bE) (c.nreg bH)
        · obtain ⟨-, w2, w3, w4, -⟩ := o4 hlt hnb
          rw [w4] at hx; rw [w2, w3]
          refine ⟨(j, e, h), hnew, rfl, ?_⟩
          rw [hup, hdn]; simpa using hx
        · push Not at hnb
          rcases hnb.2.lt_or_eq with hlt2 | heq
          · have hs' := o6 hlt hnb.1 hlt2
            rw [hs'.2.2.2.1] at hx; rw [hs'.2.1, hs'.2.2.1]
            obtain ⟨t, ht, h1, h2⟩ := hB.lSrc hnb.1 x hx
            exact ⟨t, hsub ht, h1, h2⟩
          · obtain ⟨-, w2, w3, w4⟩ := o5 hlt hnb.1 heq.symm
            rw [w4] at hx; rw [w2, w3]
            rcases mem_addL hx with hx | hx
            · rcases mem_addL hx with hx | hx
              · obtain ⟨t, ht, h1, h2⟩ := hB.lSrc hnb.1 x hx
                exact ⟨t, hsub ht, h1, h2⟩
              · exact ⟨(j, e, h), hnew, heq.symm, Or.inl (by grind)⟩
            · exact ⟨(j, e, h), hnew, heq.symm, Or.inr (by grind)⟩
      · have hs' := o3 hlt
        rw [hs'.2.2.2.1] at hx; rw [hs'.2.1, hs'.2.2.1]; rw [hs'.1] at hF'
        obtain ⟨t, ht, h1, h2⟩ := hB.lSrc hF' x hx
        exact ⟨t, hsub ht, h1, h2⟩
    · -- the coverage of the labels
      intro hF' t ht hto
      by_cases hlt : oL < offK P J e h
      · by_cases hnb : c.nreg bF ≠ 1 ∨ offK P J e h < offK P J (c.nreg bE) (c.nreg bH)
        · obtain ⟨-, w2, w3, w4, -⟩ := o4 hlt hnb
          rw [w4]; rw [w2, w3] at hto
          rcases hmA t ht with ht | rfl
          · obtain ⟨hF, hle⟩ := hB.bMin t ht (by grind)
            grind
          · rw [hup, hdn]; simp
        · push Not at hnb
          rcases hnb.2.lt_or_eq with hlt2 | heq
          · have hs' := o6 hlt hnb.1 hlt2
            rw [hs'.2.2.2.1]; rw [hs'.2.1, hs'.2.2.1] at hto
            rcases hmA t ht with ht | rfl
            · exact hB.lCov hnb.1 t ht hto
            grind
          · obtain ⟨-, w2, w3, w4⟩ := o5 hlt hnb.1 heq.symm
            rw [w4]; rw [w2, w3] at hto
            have hl := lblOf_len c
            rcases hmA t ht with ht | rfl
            · obtain ⟨h1, h2⟩ := hB.lCov hnb.1 t ht hto
              exact ⟨memOrFull_addL (memOrFull_addL h1 _) _, memOrFull_addL (memOrFull_addL h2 _) _⟩
            · rw [hup, hdn]
              exact ⟨memOrFull_addL (addL_self hl _) _, addL_self (addL_len_le hl _) _⟩
      · have hs' := o3 hlt
        rw [hs'.2.2.2.1]; rw [hs'.2.1, hs'.2.2.1] at hto; rw [hs'.1] at hF'
        rcases hmA t ht with ht | rfl
        · exact hB.lCov hF' t ht hto
        · obtain ⟨-, hb⟩ := hB.bAcc hF'
          grind
  · -- no acceptance: the rejection
    have hrej : RejAt c c' := by
      by_cases hv : ValidJ J (Qof P) N₂ j
      · rcases hres with h | ⟨e, h, hh⟩
        · exact h
        grind
      grind
    obtain ⟨hmem, hbs⟩ := hrej
    have hA'A : ∀ t ∈ A', t ∈ A := by
      rintro t (ht | ⟨-, hv, ht⟩)
      · exact ht
      grind
    obtain ⟨eF, eE, eH, eL, eN⟩ := hbs
    refine ⟨acc', fun x h1 h2 => by rw [hmem x (by omega)]; exact hB.memT x h1 h2,
      fun j' hj' => ?_, fun t ht => ?_, comp', by rw [eF]; exact hB.fF, by rw [eN]; exact hB.fN, fun h => ?_,
      fun t ht h1 => by rw [eF, eE, eH]; exact hB.bMin t (hA'A t ht) h1,
      fun h => by rw [eL]; rw [eF] at h; exact hB.lNd h, fun h x hx => ?_, fun h t ht h1 => ?_, val'⟩
    · rw [hmem _ (by omega), hmem _ (by omega), hmem _ (by omega)]
      rcases hB.slot j' hj' with h' | ⟨e', h'', hm, w⟩
      · omega
      · exact Or.inr ⟨e', h'', hsub hm, w⟩
    · have ht' := hA'A t ht
      rw [hmem _ (by have := (hB.acc t ht').2.1; omega)]
      exact hB.flag t ht'
    · rw [eF] at h; rw [eE, eH]
      obtain ⟨⟨j₁, hj₁⟩, hh⟩ := hB.bAcc h
      exact ⟨⟨j₁, hsub hj₁⟩, hh⟩
    · rw [eF] at h; rw [eL] at hx; rw [eE, eH]
      obtain ⟨t, ht, h1, h2⟩ := hB.lSrc h x hx
      exact ⟨t, hsub ht, h1, h2⟩
    · rw [eF] at h; rw [eL]; rw [eE, eH] at h1
      exact hB.lCov h t (hA'A t ht) h1

end

end SweepEv

end Chazelle.Core
