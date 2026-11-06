module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvEnv
public import Chazelle.Core.SweepEvOrg
public import Chazelle.Core.OracleQuery
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.SweepChainT

namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def ValidJ (J : Merge.Junction) (Q : Polygon) (N : NF) (j : ℕ) : Prop :=
  endOrigin J Q N j ∈ J.right.set ∧ endOrigin J Q N j ≠ J.shared ∧ endOrigin J Q N j ≠ J.right.top

/-- The offset of an accepted triple. -/
noncomputable def offT (P : Polygon) (J : Merge.Junction) (t : ℕ × ℕ × ℕ) : ℝ :=
  offK P J t.2.1 t.2.2

/-- The labels of the chord of query `j`. -/
def upOf (N : NF) (j : ℕ) : ℕ := (N.chord ztwm).up
def dnOf (N : NF) (j : ℕ) : ℕ := (N.chord ztwm).dn

/-- **The facts of a batch** for the accepted triples `A`. -/
structure BatchA (P : Polygon) (J : Merge.Junction) (N₂ : NF) (cs : Config) (lo : Set Point)
    (O : Set ℕ) (c : Config) (A : Set zte) : Prop where
  acc : ∀ t ∈ A, t.1 ∈ O ∧ t.1 < 2 * N₂.nChords ∧
    CandOK P J ztwis ztwnl ztdzu
      t.2.1 t.2.2
  memT : ∀ x, x < cs.nreg ALLOC → (x < cs.nreg cTB ∨ cs.nreg cTB + 6 * N₂.nChords ≤ x) →
    c.nmem x = cs.nmem x
  slot : ∀ j, j < 2 * N₂.nChords →
    (c.nmem ztijc = cs.nmem ztijc ∧
      c.nmem ztghw = cs.nmem ztghw ∧
      c.nmem ztghx = cs.nmem ztghx) ∨
    ∃ e h, ztcip ∈ A ∧ c.nmem ztijc = 1 ∧
      c.nmem ztghw = e ∧ c.nmem ztghx = h
  flag : ∀ t ∈ A, c.nmem (cs.nreg cTB + 3 * t.1) = 1
  comp : ∀ j ∈ O, j < 2 * N₂.nChords → ValidJ J zta N₂ j → ∀ (p : ℕ) (t : ℝ),
    SideAttach (chainModel J.whole).W
      ztbams p t →
    sidePt (chainModel J.whole).W p t = rayPt ztwka ztri
      ztbanq →
    (Lst J : ℝ) < oW J ztk → sidePt (chainModel J.whole).W p t ≠ J.shared →
    J.whole.hitParam ztwka ztri <
      J.right.hitParam ztwka ztri →
    rayPt ztwka ztri
      ztbanq ∈ lo →
    ∃ h, (chainModel J.whole).param zta ztnk = t ∧ ztjzc ∈ A
  fF : c.nreg bF ≤ 1
  fN : c.nreg bN ≤ 4
  bAcc : c.nreg bF = 1 → (∃ j, (j, c.nreg bE, c.nreg bH) ∈ A) ∧
    offK P J ztmhs ztmht < offK P J ztvo ztvp
  bMin : ∀ t ∈ A, offK P J ztmhs ztmht < offT P J t →
    c.nreg bF = 1 ∧ offK P J ztvo ztvp ≤ offT P J t
  lNd : c.nreg bF = 1 → (lblOf c bN bL).Nodup
  lSrc : c.nreg bF = 1 → ∀ x ∈ lblOf c bN bL, ∃ t ∈ A,
    offT P J t = offK P J ztvo ztvp ∧ ztcxa
  lCov : c.nreg bF = 1 → ∀ t ∈ A, offT P J t = offK P J ztvo ztvp →
    (upOf N₂ t.1 ∈ lblOf c bN bL ∨ (lblOf c bN bL).length = 4) ∧
      (dnOf N₂ t.1 ∈ lblOf c bN bL ∨ (lblOf c bN bL).length = 4)
  val : ∀ t ∈ A, ValidJ J zta N₂ t.1

/-- **The invariant of a batch of origins** (started at `cs`). -/
def BatchInv (P : Polygon) (J : Merge.Junction) (N₂ : NF) (cs : Config) (lo : Set Point)
    (O : Set ℕ) (c : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → ¬ LR r → r ≠ ALLOC → c.nreg r = cs.nreg r) ∧
    cs.nreg ALLOC ≤ c.nreg ALLOC ∧ ∃ A, BatchA P J N₂ cs lo O c A

/-! ## Label lists -/
variable {l : List ℕ} (m : ℕ → ℕ) (T j e h : ℕ) {cs c c' : Config}
theorem addL_nodup (h : l.Nodup) (v : ℕ) : (addL l v).Nodup := by
  zuckx
theorem mem_addL_of_mem {v x : ℕ} (h : x ∈ l) : x ∈ addL l v := by
  zuckx
theorem addL_len4 (h : l.length = 4) (v : ℕ) : (addL l v).length = 4 := by
  unfold addL; simp_all
theorem addL_self (h : l.length ≤ 4) (v : ℕ) :
    v ∈ addL l v ∨ (addL l v).length = 4 := by
  zuckx
theorem lblOf_len (c : Config) : (lblOf c bN bL).length ≤ 4 := by
  rw [lblOf_length]; omega

/-- Membership or fullness survives `addL`. -/
theorem memOrFull_addL {x : ℕ} (h : x ∈ l ∨ l.length = 4) (v : ℕ) :
    x ∈ addL l v ∨ (addL l v).length = 4 := by
  zuy
  · exact Or.inl ztvys
  · exact Or.inr (addL_len4 h v)
theorem addL_len_le (h : l.length ≤ 4) (v : ℕ) : (addL l v).length ≤ 4 :=
  addL_length_le h v

/-! ## The table -/
theorem tabUpd_0 : tabUpd m T j e h ztctp = 1 := by
  zujrf
theorem tabUpd_1 : tabUpd m T j e h zteog = e := by
  zujrf
theorem tabUpd_2 : tabUpd m T j e h zteoh = h := by
  zujrf
theorem tabUpd_o {T j e h x : ℕ} (h0 : x ≠ T + 3 * j) (h1 : x ≠ T + 3 * j + 1)
    (h2 : x ≠ T + 3 * j + 2) : tabUpd m T j e h x = m x := by
  unfold tabUpd; simp_all
variable {P : Polygon} {J : Merge.Junction} {N₂ : NF}

/-- **The start of a batch.** -/
theorem batch_base {cs : Config} {lo : Set Point} (hbF : cs.nreg bF = 0) (hbN : cs.nreg bN ≤ 4) :
    BatchInv P J N₂ cs lo ∅ cs := by
  refine ⟨by_omega, le_rfl, ∅, ⟨by_simp_all,
    by omega, by_omega, by_simp_all,
    by simp_all,
    by omega, hbN, by_simp_all, by_simp_all,
    by simp_all, by_simp_all, by_simp_all,
    by simp_all⟩⟩

/-- **The invariant ignores the loop registers.** -/
theorem batch_stable {lo : Set Point} {O : Set ℕ}
    (h : BatchInv P J N₂ cs lo O c) (hr : ∀ r, ¬ LR r → c'.nreg r = c.nreg r)
    (hm : c'.nmem = c.nmem) : BatchInv P J N₂ cs lo O c' := by
  obtain ⟨hreg, hA, A, hB⟩ := h
  have nLR : ∀ q, LblR bN bL q ∨ q = bF ∨ q = bE ∨ q = bH → ¬ LR q := fun q hq => by
    unfold LR LblR oK oS bN bL bF bE bH sw at *; omega
  have eF := hr bF by_simp_all
  have eE := hr bE by_simp_all
  have eH := hr bH by_simp_all
  have eN := hr bN (nLR _ ztxvr)
  have eL : lblOf c' bN bL = lblOf c bN bL := lblOf_congr by_simp_all
  have eA := hr ALLOC (by unfold LR ALLOC oK oS sw; omega)
  refine ⟨by_simp_all, by_omega, A,
    ⟨hB.acc, fun x h1 h2 => by zvmwi; exact hB.memT x h1 h2,
    fun j hj => by zvmwi; exact hB.slot j hj, fun t ht => by zvmwi; exact hB.flag t ht, hB.comp, by zvnnc; exact hB.fF,
    by zupbx; exact hB.fN, ?_, ?_, ?_, ?_, ?_, hB.val⟩⟩
  · intro h; zvpby; zvnnc at h; exact hB.bAcc h
  · intro t ht h1; zuobm; exact hB.bMin t ht h1
  · intro h; rw [eL]; zvnnc at h; exact hB.lNd h
  · intro h; zuobn; zvnnc at h; exact hB.lSrc h
  · intro h; zuobn; zvnnc at h; exact hB.lCov h
set_option maxHeartbeats 4000000 in
/-- **One origin keeps the invariant of the batch.** -/
theorem batch_step {lo : Set Point} {O : Set ℕ} {k s : ℕ}
    (hInv : BatchInv P J N₂ cs lo O c) (hj : 2 * k + s < 2 * N₂.nChords) (hs : s ≤ 1)
    (hud : (N₂.chord k).up ≠ (N₂.chord k).dn)
    (hT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg ALLOC)
    (hres : CandRes P J ztwis ztdmu ztci
      (N₂.chord k).up (N₂.chord k).dn ztwut ztxnz
      c c')
    (hcomp : ValidJ J zta N₂ ztci →
      CandComp P J ztwis ztdmu ztci
        (N₂.chord k).up (N₂.chord k).dn ztwut ztxnz
        lo c c')
    (hval : ¬ ValidJ J zta N₂ ztci → RejAt c c')
    (hfr : ∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    BatchInv P J N₂ cs lo (insert ztci O) c' := by
  zufjz
  have hk2 : ztzra := by_omega
  have hup : upOf N₂ ztci = (N₂.chord k).up := by unfold upOf; zupbz
  have hdn : dnOf N₂ ztci = (N₂.chord k).dn := by unfold dnOf; zupbz
  have keepS :=
    fun r h1 h2 h3 h4 => hreg r zthse h3 h4 ztu
  have hTc : ztsfa :=
    keepS _ by_decide by_decide
      ztdgz
      ztlju
  have hkE : ztsfc :=
    keepS _ by_decide by_decide
      zthfq
      ztljv
  have hkH : ztsfd :=
    keepS _ by_decide by_decide
      zthfr
      ztljw
  rw [hTc] at hres hcomp
  zugyq
  set a := endOrigin J zta N₂ j
  set σ := endDir j
  set S₂ := N₂.F ztj zta
  set oL := offK P J ztmhs ztmht with hoL
  have hTA : ztdne + 6 * N₂.nChords ≤ c.nreg ALLOC := by_omega
  -- the new set of accepted triples
  set A' : Set _ := A ∪ {t | t.1 = j ∧ ValidJ J zta N₂ j ∧
    AccAt P J S₂ ztdne j (N₂.chord k).up (N₂.chord k).dn a σ c c' t.2.1 t.2.2} with hA'd
  have hsub : A ⊆ A' := Set.subset_union_left
  have hreg' : ∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → ¬ LR r → r ≠ ALLOC →
      c'.nreg r = cs.nreg r := by_grind
  refine ⟨hreg', by_omega, A', ?_⟩
  -- common fields
  have acc' : ∀ t ∈ A', t.1 ∈ insert j O ∧ t.1 < 2 * N₂.nChords ∧
      CandOK P J S₂ ztwnl ztdzu t.2.1 t.2.2 := by
    rintro t (ht | ⟨ht1, -, ht2⟩)
    · obtain ⟨h1, h2, h3⟩ := hB.acc t ht
      grind
    · rw [ht1]; exact ⟨by_grind, hj, ht2.1⟩
  have comp' : ∀ j' ∈ insert j O, j' < 2 * N₂.nChords → ValidJ J zta N₂ j' →
      ∀ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W
        (Merge.shoot J.whole ztwry ztdzt) p t →
      sidePt (chainModel J.whole).W p t = rayPt ztwry ztdzt
        ztbarg →
      (Lst J : ℝ) < oW J ztk → sidePt (chainModel J.whole).W p t ≠ J.shared →
      J.whole.hitParam ztwry ztdzt <
        J.right.hitParam ztwry ztdzt →
      rayPt ztwry ztdzt
        ztbarg ∈ lo →
      ∃ h, (chainModel J.whole).param zta ztnk = t ∧ (j', p, h) ∈ A' := by
    intro j' hj' hj'n hv p t h1 h2 h3 h4 h5 h6
    rcases Set.mem_insert_iff.1 hj' with rfl | hj'
    · obtain ⟨h, hh, hacc⟩ := hcomp hv p t h1 h2 h3 h4 h5 h6
      grind
    · obtain ⟨h, hh, hm⟩ := hB.comp j' hj' hj'n hv p t h1 h2 h3 h4 h5 h6
      grind
  have val' : ∀ t ∈ A', ValidJ J zta N₂ t.1 := by
    rintro t (ht | ⟨ht1, hv, -⟩)
    · exact hB.val t ht
    grind
  by_cases hacc : ∃ e h, ValidJ J zta N₂ j ∧
    AccAt P J S₂ ztdne j (N₂.chord k).up (N₂.chord k).dn a σ c c' e h
  · obtain ⟨e, h, hvj, hAcc⟩ := hacc
    obtain ⟨hok, hmem, hoff⟩ := hAcc
    -- uniqueness of the new triple
    have huq : ∀ t ∈ A', t ∉ A → t = ztcip := by
      rintro ⟨j₁, e₁, h₁⟩ (ht | ⟨ht1, -, -, hmem₁, -⟩) hn
      · grind
      · simp only at ht1 hmem₁
        subst ht1
        have w1 := hmem₁ (ztdne + 3 * j + 1) by_omega
        have w2 := hmem₁ (ztdne + 3 * j + 2) by_omega
        rw [hmem _ by_omega, tabUpd_1, tabUpd_1] at w1
        rw [hmem _ by_omega, tabUpd_2, tabUpd_2] at w2
        grind
    have hnew : ztcip ∈ A' := Or.inr ⟨rfl, hvj, hok, hmem, hoff⟩
    have hmA : ∀ t ∈ A', t ∈ A ∨ t = ztcip := fun t ht => by
      grind
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hoff
    rw [hkE, hkH] at o3 o4 o5 o6
    have hoffN : offT P J ztcip = offK P J e h := rfl
    refine ⟨acc', fun x h1 h2 => ?_, fun j' hj' => ?_, fun t ht => ?_, comp', o1, o2, ?_, ?_, ?_, ?_, ?_, val'⟩
    · rw [hmem x by_omega, tabUpd_o _ by_omega by_omega by_omega]
      exact hB.memT x h1 h2
    · by_cases hjj : j' = j
      · subst hjj
        refine Or.inr ⟨e, h, hnew, ?_, ?_, ?_⟩
        · zuikd
        · rw [hmem _ by_omega, tabUpd_1]
        · rw [hmem _ by_omega, tabUpd_2]
      · have e0 : c'.nmem ztzhp = c.nmem ztzhp := by
          zubda
        have e1 : c'.nmem ztyss = c.nmem ztyss := by
          zubda
        have e2 : c'.nmem ztyst = c.nmem ztyst := by
          zubda
        rw [e0, e1, e2]
        zudry
        · omega
        · exact Or.inr ztmqk
    · zubbb
      · have htj := (hB.acc t ht).2.1
        by_cases hjj : t.1 = j
        · rw [hjj, hmem _ by_omega, tabUpd_0]
        · zubda
          exact hB.flag t ht
      · zuikd
    -- the best candidate: four cases of the offer
    · intro hF'
      zubms
      · zudp
        · obtain ⟨-, w2, w3, -, -⟩ := o4 hlt hnb
          zuoof; exact ⟨⟨j, hnew⟩, hlt⟩
        · zuqw

          · zubwo
            zubqa

          · obtain ⟨w1, w2, w3, -⟩ := o5 hlt hnb.1 heq.symm
            zuoof
            obtain ⟨⟨j₁, hj₁⟩, hh⟩ := hB.bAcc hnb.1
            exact ztebg
      · zuesf
        zubqa

    · intro t ht hlt
      zubbb
      · obtain ⟨hF, hle⟩ := hB.bMin t ht hlt
        have hlt' : oL < offK P J e h ∨ ¬ oL < offK P J e h := em _
        rcases hlt' with hl | hl
        · zudp
          · grind
          · zuqw

            · have hs' := o6 hl hnb.1 hlt2
              zugvm
            grind
        · have hs' := o3 hl
          zugvm
      · rw [hoffN] at hlt ⊢
        zudp
        · grind
        · zuqw

          · zubwo
            rw [hs'.1, hs'.2.1, hs'.2.2.1]; omega
          grind
    · -- no repetitions
      intro hF'
      zubms
      · zudp
        · obtain ⟨-, -, -, w4, -⟩ := o4 hlt hnb
          zunsh; simpa using hud
        · zuqw

          · zubwo
            rw [hs'.2.2.2.1]; exact hB.lNd hnb.1
          · obtain ⟨-, -, -, w4⟩ := o5 hlt hnb.1 heq.symm
            zunsh; exact addL_nodup (addL_nodup (hB.lNd hnb.1) _) _
      · zuesf
        rw [hs'.2.2.2.1]; rw [hs'.1] at hF'; exact hB.lNd hF'
    · -- the sources of the labels
      intro hF' x hx
      zubms
      · zudp
        · zudqr
          zuezo
          refine ⟨ztcip, hnew, rfl, ?_⟩
          zunqn; simpa using hx
        · zuqw

          · zubwo
            rw [hs'.2.2.2.1] at hx; rw [hs'.2.1, hs'.2.2.1]
            zudjc

          · zueai
            zuezo
            zujep
            · zujep
              · zudjc

              · exact ztytl
            · exact ztytl
      · zuesf
        rw [hs'.2.2.2.1] at hx; rw [hs'.2.1, hs'.2.2.1]; rw [hs'.1] at hF'
        obtain ⟨t, ht, h1, h2⟩ := hB.lSrc hF' x hx
        exact ztebe
    · -- the coverage of the labels
      intro hF' t ht hto
      zubms
      · zudp
        · zudqr
          zuezp
          zubbb
          · obtain ⟨hF, hle⟩ := hB.bMin t ht by_grind
            grind
          · zunqn; simp
        · zuqw

          · zubwo
            rw [hs'.2.2.2.1]; rw [hs'.2.1, hs'.2.2.1] at hto
            zubbb
            · exact hB.lCov hnb.1 t ht hto
            grind
          · zueai
            zuezp
            have hl := lblOf_len c
            zubbb
            · obtain ⟨h1, h2⟩ := hB.lCov hnb.1 t ht hto
              exact ⟨memOrFull_addL (memOrFull_addL h1 _) _, memOrFull_addL (memOrFull_addL h2 _) _⟩
            · zunqn
              exact ⟨memOrFull_addL (addL_self hl _) _, addL_self (addL_len_le hl _) _⟩
      · zuesf
        rw [hs'.2.2.2.1]; rw [hs'.2.1, hs'.2.2.1] at hto; rw [hs'.1] at hF'
        zubbb
        · exact hB.lCov hF' t ht hto
        · obtain ⟨-, hb⟩ := hB.bAcc hF'
          grind
  · -- no acceptance: the rejection
    have hrej : RejAt c c' := by
      by_cases hv : ValidJ J zta N₂ j
      · rcases hres with h | ⟨e, h, hh⟩
        · zubh
        grind
      grind
    obtain ⟨hmem, hbs⟩ := hrej
    have hA'A : ∀ t ∈ A', t ∈ A := by
      grind
    obtain ⟨eF, eE, eH, eL, eN⟩ := hbs
    refine ⟨acc', fun x h1 h2 => by rw [hmem x by_omega]; exact hB.memT x h1 h2,
      fun j' hj' => ?_, fun t ht => ?_, comp', by zvnnc; exact hB.fF, by zupbx; exact hB.fN, fun h => ?_,
      fun t ht h1 => by zuobm; exact hB.bMin t zttly h1,
      fun h => by rw [eL]; zvnnc at h; exact hB.lNd h, fun h x hx => ?_, fun h t ht h1 => ?_, val'⟩
    · rw [hmem _ by_omega, hmem _ by_omega, hmem _ by_omega]
      zudry
      · omega
      · exact Or.inr ztmqk
    · have ht' := hA'A t ht
      rw [hmem _ (by have := (hB.acc t ht').2.1; omega)]
      exact hB.flag t ht'
    · zvnnc at h; zvpby
      obtain ⟨⟨j₁, hj₁⟩, hh⟩ := hB.bAcc h
      exact ztebg
    · zvnnc at h; rw [eL] at hx; zvpby
      obtain ⟨t, ht, h1, h2⟩ := hB.lSrc h x hx
      exact ztebe
    · zvnnc at h; rw [eL]; zvpby at h1
      exact hB.lCov h t zttly h1
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
@[expose] public section
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- The regions of a chord record differ. -/
theorem up_ne_dn (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {k : ℕ} (hk : k < N₂.nChords) :
    (N₂.chord k).up ≠ (N₂.chord k).dn := by
  have hPr : J.right.P.Simple := E.ctx2.2.2.2.2.1
  obtain ⟨hRC, hCS, -⟩ := regOf_spec E.hNF₂
  exact (Gran.touch_iff_side E.hNF₂ (FactsChain.walkAx J.right hPr) hRC hCS hk).1
theorem not_orgR {r : ℕ} (h : ztbcj ∨ ER r) : ¬ OrgR r := by
  unfold OrgR CandR BestR LblR bF bE bH bN bL
  rcases h with ⟨h, h1, h2⟩ | h
  · simp only [LR, oK, oS, sw] at h h1 h2; unfold sw; omega
  · unfold ER kN kL gN gR sP sC aB sw at h; unfold sw; omega
set_option maxHeartbeats 4000000 in
/-- **One origin as a step of a batch.** -/
theorem orgDo_batch (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {g : Stmt} {KG : ℕ}
    (hgen : GenOK P W c₀ J g KG) {cs : Config} {L : List ℕ}
    (hL : ∀ a ∈ L, a < N₁.arcs.length) (hgK : cs.nreg wGK = L.length)
    (hAB : cs.nreg wGB + 4 * L.length ≤ cs.nreg ALLOC)
    (harcs : ∀ k, k < L.length → ShotList.arcAt cs.nmem ztcpv k =
      nArc ztbw zta N₁ zthbf)
    (hT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg ALLOC)
    (hWT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg wGB)
    (hauxT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg aB)
    (haux : cs.nreg aB + 5 * cs.nreg sC ≤ cs.nreg ALLOC)
    (hkey : PosW P J ztmhs ztmht)
    (O : Set ℕ) (c : Config) (hI : IInv W c₀ c)
    (hInv : BatchInv P J N₂ cs
      ztyhz O c)
    (hk : c.nreg oK < N₂.nChords) (hs : c.nreg oS ≤ 1)
    (hroom : c.nreg ALLOC + orgDoK ztwiu L.length KG ≤ W) :
    IRS P W c₀ ztkbr c ztbaqh (fun c' =>
      BatchInv P J N₂ cs
        ztyhz
        ztxxm c' ∧
      ztwpx ∧
      ztvw) := by
  have hInv' := hInv
  zufjz
  have keepS : ∀ r, 240000 ≤ r → r < 250000 → ¬ OrgR r → ¬ LR r → c.nreg r = cs.nreg r :=
    fun r h1 h2 h3 h4 => hreg r ztyid h3 h4 ztu
  have eGK : c.nreg wGK = cs.nreg wGK := keepS _ by_decide
    by_decide (by unfold OrgR CandR BestR LblR wGK bF bE bH bN bL sw; omega)
    (by unfold LR wGK oK oS sw; omega)
  have eGB : c.nreg wGB = cs.nreg wGB := keepS _ by_decide
    by_decide (by unfold OrgR CandR BestR LblR wGB bF bE bH bN bL sw; omega)
    (by unfold LR wGB oK oS sw; omega)
  have eKE : ztsfc := keepS _ by_decide
    by_decide zthfq
    ztljv
  have eKH : ztsfd := keepS _ by_decide
    by_decide zthfr
    ztljw
  have eTB : ztsfa := keepS _ by_decide
    by_decide ztdgz
    ztlju
  have hmc : ∀ x, cs.nreg cTB + 6 * N₂.nChords ≤ x → x < cs.nreg ALLOC → c.nmem x = cs.nmem x :=
    fun x h1 h2 => hB.memT x h2 ztjku
  have harcs' : ∀ k, k < L.length → ShotList.arcAt c.nmem ztdcv k =
      nArc ztbw zta N₁ zthbf := fun k hk' => by
    rw [eGB, ← harcs k hk']
    unfold ShotList.arcAt
    grind
  have hlo : ShotList.loSet ztbw zta c.nmem ztdcv L.length [] =
      ShotList.loSet ztbw zta cs.nmem ztcpv L.length [] := by
    zupca; exact loSet_congr (fun x h1 h2 => hmc x by_omega by_omega)
  have hb : c.nreg bF = 1 → PosW P J ztvo ztvp := fun h => by
    obtain ⟨⟨j, hj⟩, -⟩ := hB.bAcc h
    exact (hB.acc _ hj).2.2.2.2.2.2.2.1
  refine (orgDo_irs E hI hgen hL by_omega by_omega harcs' rfl rfl hk hs
    by_grind hb hB.fF hB.fN hroom).mono le_rfl ?_
  rintro c' ⟨hres, hcomp, hrej, hfr, hA'⟩
  refine ⟨batch_step hInv' by_omega hs (up_ne_dn E hk) hT hres
    (fun hv => hlo ▸ hcomp hv.1 hv.2.1 hv.2.2) hrej hfr hA', fun r hr => ?_, fun x h1 h2 => ?_⟩
  · refine hfr r (band_sw_not ?_) (not_orgR hr) (by
      zuflo
      · unfold LR oK oS sw at h; unfold ALLOC; omega
      · unfold ER kN kL gN gR sP sC aB sw at h; unfold ALLOC; omega)
    zuflo
    · unfold LR oK oS sw at h; omega
    · unfold ER kN kL gN gR sP sC aB sw at h; omega
  · have eaB : c.nreg aB = cs.nreg aB := keepS _ by_decide
      by_decide (by unfold OrgR CandR BestR LblR aB bF bE bH bN bL sw; omega)
      (by unfold LR aB oK oS sw; omega)
    have eC : c.nreg sC = cs.nreg sC := keepS _ by_decide
      by_decide zthfs
      (by unfold LR sC oK oS sw; omega)
    rw [eaB] at h1; rw [eaB, eC] at h2
    rcases hres with ⟨hm, -⟩ | ⟨e, h, -, hm, -⟩
    · grind
    · rw [hm x by_omega, tabUpd_o _ by_omega by_omega
        by_omega]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed Sweep
@[expose] public section
theorem finite_ncard_le_of_rel {α β : Type*} {A : Set α} {B : Set β} (hB : B.Finite)
    (R : α → β → Prop) (hcov : ∀ a ∈ A, ∃ b ∈ B, R a b)
    (huniq : ∀ a a' b, R a b → R a' b → a = a') : A.Finite ∧ A.ncard ≤ B.ncard := by
  classical
  rcases A.eq_empty_or_nonempty with hA | ⟨a₀, ha₀⟩
  · simp_all
  obtain ⟨b₀, -, -⟩ := hcov a₀ ha₀
  have : Nonempty β := ⟨b₀⟩
  choose! f hfB hfR using hcov
  have hinj : InjOn f A := fun a ha a' ha' h =>
    huniq a a' ztbaa (hfR a ha) by_simp_all
  refine ⟨Finite.of_finite_image (hB.subset ?_) hinj, ncard_le_ncard_of_injOn f hfB hinj hB⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hfB a ha

/-! ## Cut keys -/
variable {M : Model} (J : Merge.Junction)
/-- **An admissible chord is attached at at most two keys.** -/
theorem attach_keys (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ x y : ℝ, ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t → (p : ℝ) + t = x ∨ (p : ℝ) + t = y := by
  obtain ⟨a, b, -, rfl, -, hopen, ⟨⟨pa, ta, hAa, hpa⟩, -⟩, ⟨⟨pb, tb, hAb, hpb⟩, -⟩⟩ :=
    hM.ends _ hc
  refine ⟨pa + ta, pb + tb, fun p t hA => ?_⟩
  zuebs
  · obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hA hAa (h.trans hpa.symm)
    simp
  · obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hA hAb (h.trans hpb.symm)
    simp

/-- **The cut keys of a finite admissible family** are finitely many, at most twice its size. -/
theorem cut_keys_ncard (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) :
    {x : ℝ | M.IsCut F x}.Finite ∧ {x : ℝ | M.IsCut F x}.ncard ≤ 2 * F.ncard := by
  classical
  choose! fx fy hxy using fun c (hc : c ∈ F) => attach_keys hM (hF hc)
  have hsub : {x : ℝ | M.IsCut F x} ⊆ fx '' F ∪ fy '' F := by
    zuecj
    grind
  have hfu : (fx '' F ∪ fy '' F).Finite := (hfin.image _).union ztjxu
  refine ⟨hfu.subset hsub, ?_⟩
  calc {x : ℝ | M.IsCut F x}.ncard ≤ (fx '' F ∪ fy '' F).ncard := ncard_le_ncard hsub hfu
    _ ≤ (fx '' F).ncard + (fy '' F).ncard := ncard_union_le _ _
    _ ≤ F.ncard + F.ncard := Nat.add_le_add ztvzo ztvzo
    _ = 2 * F.ncard := by_ring

/-! ## The size of `F₂⁺` -/

/-- There are at most two top chords at the top of `C₂`. -/
theorem topChords₂_ncard_le : (topChords₂ J).ncard ≤ 2 := by
  have hsub : topChords₂ J ⊆
      ztywi '' ({1, -1} : Set ℝ) := by
    zucej

  calc (topChords₂ J).ncard
      ≤ (ztywi '' ({1, -1} : Set ℝ)).ncard :=
        ncard_le_ncard hsub ((toFinite _).image _)
    _ ≤ ({1, -1} : Set ℝ).ncard := ncard_image_le ztcwq
    _ = 2 := ncard_pair by_norm_num

/-- **`|F₂⁺| ≤ 2 |S₂| + 4`.** -/
theorem F₂plus_ncard_le {S₂ : Set ztf} (hS₂f : S₂.Finite) :
    (F₂plus J S₂).ncard ≤ 2 * S₂.ncard + 4 := by
  have h1 := J.ncard_fusion_le finite_empty hS₂f
  rw [ncard_empty, zero_add] at h1
  have h2 := topChords₂_ncard_le J
  calc (F₂plus J S₂).ncard ≤ (J.fusion ∅ S₂).ncard + (topChords₂ J).ncard := ncard_union_le _ _
    _ ≤ 2 * S₂.ncard + 4 := by_omega

/-- **The offsets of the cut keys of `F₂⁺`**: finitely many, at most `4 |S₂| + 8`. -/
theorem cutOffs_ncard (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    (cutOffs J S₂).Finite ∧ (cutOffs J S₂).ncard ≤ 4 * S₂.ncard + 8 := by
  zugb
  obtain ⟨hfin, hle⟩ := cut_keys_ncard hM ztsxq ztnld
  have hsub : cutOffs J S₂ ⊆ oW J '' {x : ℝ | (chainModel J.whole).IsCut ztbi x} := by
    rintro o ⟨x, hx, -, -, rfl⟩
    grind
  refine ⟨(hfin.image _).subset hsub, ?_⟩
  have := F₂plus_ncard_le J hS₂f
  calc (cutOffs J S₂).ncard
      ≤ (oW J '' {x : ℝ | (chainModel J.whole).IsCut ztbi x}).ncard :=
        ncard_le_ncard hsub ztjxu
    _ ≤ {x : ℝ | (chainModel J.whole).IsCut ztbi x}.ncard := ncard_image_le hfin
    _ ≤ 4 * S₂.ncard + 8 := by_omega

/-! ## The window offsets -/

/-- The point of the walk of `C₁` at `b₁` is the shared vertex. -/
theorem b₁_pt :
    sidePt (chainModel J.left).W ((b₁ J + 0) % (chainModel J.left).W.n) 0 = J.shared := by
  rw [add_zero, Nat.mod_eq_of_lt (b₁_lt (J := J))]
  unfold b₁
  zus
  · rw [(sidePt_top_copies J.left).2]
    exact left_top_eq J (caseB_facts J h).1
  · rw [Chazelle.Chain.sidePt_zero, vtx_tpos' J.left (k := J.m₁) ztbhw]
    rfl

/-- The predecessor of a nonzero residue. -/
theorem pred_mod' {b d n e : ℕ} (hb : b < n) (hd : d < n) (h1 : 1 ≤ d)
    (he : zthdo % n = e) (he0 : e ≠ 0) : ztzvc % n + 1 = e := by
  zuhsh
  · zujhf
    zupd
  · zugty
    zuzu

/-- The two readings `(d, 1)` and `(d + 1, 0)` of a vertex key give the same offset. -/
theorem win_uniq_step (hP : J.P.Simple) {d d' : ℕ}
    (hv : MValid J d 1) (hv' : MValid J d' 0)
    (hk : ztljy % (chainModel J.left).W.n = zthm % (chainModel J.left).W.n + 1) :
    ψ J d + 1 = ψ J d' := by
  zuheq
  zugln
  have hd : d < (chainModel J.left).W.n := lt_of_lt_of_le hv.1 hE
  have hd' : d' < (chainModel J.left).W.n := lt_of_lt_of_le hv'.1 hE
  have hd'1 : 1 ≤ d' := by
    rcases Nat.eq_zero_or_pos d' with h0 | h0
    · subst h0; exact absurd (b₁_pt J) (hv'.2.2.2 rfl)
    omega
  have hpm := pred_mod' hb hd' hd'1 hk by_omega
  have hdd : d = d' - 1 := add_mod_inj (g := b₁ J) hd by_omega by_omega
  subst hdd
  obtain ⟨-, hg, hl, -⟩ := hv
  obtain ⟨-, hg', -, -⟩ := hv'
  have hl' : ¬ (0 < lδ J ∧ d' - 1 = lL1 J) := fun h => hl ⟨h.1, h.2, one_ne_zero⟩
  unfold ψ
  grind

/-- **A cut key of `N₁` gives at most one window offset.** -/
theorem win_uniq (hP : J.P.Simple) {d d' : ℕ} {t t' : ℝ}
    (hv : MValid J d t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv' : MValid J d' t') (ht0' : 0 ≤ t')
    (ht1' : t' ≤ 1)
    (hx : ((zthm % (chainModel J.left).W.n : ℕ) : ℝ) + t =
      ((ztljy % (chainModel J.left).W.n : ℕ) : ℝ) + t') :
    (ψ J d : ℝ) + t = ψ J d' + t' := by
  zubae
  zugln
  have hd : d < n₁ := lt_of_lt_of_le hv.1 hE
  have hd' : d' < n₁ := lt_of_lt_of_le hv'.1 hE
  set k := zthm % n₁ with hkdef
  set k' := ztljy % n₁ with hk'def
  have hlo : (k : ℝ) < k' + 2 := by_linarith
  have hhi : (k' : ℝ) < k + 2 := by_linarith
  have hlo' : k < k' + 2 := by exact_mod_cast hlo
  have hhi' : k' < k + 2 := by exact_mod_cast hhi
  rcases (show k = k' ∨ k' = k + 1 ∨ k = k' + 1 by omega) with h | h | h
  · have htt : t = t' := by_simp_all
    have hdd : d = d' := add_mod_inj hd hd' h
    simp_all
  · have e : (k' : ℝ) = k + 1 := by exact_mod_cast h
    zucmr
    have ht' : ztmwy := by_linarith
    subst ht ht'
    have := win_uniq_step J hP hv hv' h
    have e2 : ((ψ J d + 1 : ℕ) : ℝ) = ψ J d' := by_simp_all
    grind
  · have e : (k : ℝ) = k' + 1 := by exact_mod_cast h
    have ht' : t' = 1 := by_linarith
    zufwk
    subst ht ht'
    have := win_uniq_step J hP hv' hv h
    have e2 : ((ψ J d' + 1 : ℕ) : ℝ) = ψ J d := by_simp_all
    grind

/-- **The window offsets**: finitely many, at most `2 K₁ + 1`. -/
theorem winOffs_ncard (P : Polygon) (J : Merge.Junction) (hP : J.P.Simple) (N₁ : NF)
    (hN₁ : IsNF ztbw zta N₁) :
    (winOffs P J N₁).Finite ∧ (winOffs P J N₁).ncard ≤ 2 * N₁.nChords + 1 := by
  have hP₁ : J.left.P.Simple := hP
  have hM : WalkAx ztbw := FactsChain.walkAx J.left hP₁
  obtain ⟨hfin, hle⟩ := cut_keys_ncard hM hN₁.1.2.1 hN₁.1.1
  rw [Gran.ncard_F hN₁] at hle
  obtain ⟨hf2, hl2⟩ := finite_ncard_le_of_rel hfin
    (A := {o | ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (chainModel J.left).IsCut ztwjx
        ztwms ∧ o = (Lst J : ℝ) + ψ J d + t})
    (fun o x => ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
      x = ((zthm % (chainModel J.left).W.n : ℕ) : ℝ) + t ∧ o = (Lst J : ℝ) + ψ J d + t)
    (by
      grind)
    (by
      rintro o o' x ⟨d, t, hv, h0, h1, rfl, rfl⟩ ⟨d', t', hv', h0', h1', hx, rfl⟩
      have := win_uniq J hP hv h0 h1 hv' h0' h1' hx
      linarith)
  refine ⟨(finite_singleton _).union hf2, ?_⟩
  calc (winOffs P J N₁).ncard ≤ ({(Lst J : ℝ) + lL1 J} : Set ℝ).ncard + _ := ncard_union_le _ _
    _ ≤ 2 * N₁.nChords + 1 := by rw [ncard_singleton]; omega

/-- **Task C (mathematics): the number of keys.** -/
theorem countTask : CountTask := by
  intro P J N₁ N₂ hP hN₁ hN₂
  obtain ⟨hc, hcl⟩ := cutOffs_ncard J hP hN₂.1.2.1 hN₂.1.1
  rw [Gran.ncard_F hN₂] at hcl
  obtain ⟨hw, hwl⟩ := winOffs_ncard P J hP N₁ hN₁
  refine ⟨hc.union hw, ?_⟩
  have := ncard_union_le (cutOffs J ztwis) (winOffs P J N₁)
  omega
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def kqF : ℕ := sw 2480
def kqE : ℕ := sw 2481
def kqH : ℕ := sw 2482
/-- The position offered (a stop or the window end). -/
def kqSE : ℕ := sw 2483
def kqSH : ℕ := sw 2484
/-- The comparison bits (`kqO`, `kqO + 1`). -/
def kqO : ℕ := sw 2485
/-- The flags "the best candidate is at the key" and "an anchored stop was skipped". -/
def kqB : ℕ := sw 2487
def kqA : ℕ := sw 2488
/-- The label list under construction: count `kqN`, labels `kqL … kqL + 3`. -/
def kqN : ℕ := sw 2489
def kqL : ℕ := sw 2490
/-- An address and two values. -/
def kqX : ℕ := sw 2494
def kqV : ℕ := sw 2495
def kqY : ℕ := sw 2496

/-! ## `kqIsOne` -/

/-- Run `s` iff the register `r` holds `1`. -/
def kqIsOne (r : ℕ) (s : Stmt) : Stmt := .ifLtN K0 r (.ifLtN r K2 s .skip) .skip
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {r : ℕ}
theorem kqIsOne_irs {s : Stmt} {K : ℕ} {Q : Config → Prop} (hI : IInv W c₀ c)
    (hK : Consts c) (hs : c.nreg r = 1 → IRS P W c₀ s c K Q) (hq : c.nreg r ≠ 1 → Q c) :
    IRS P W c₀ (kqIsOne r s) c ztfns Q := by
  obtain ⟨k0, -, -, -, -, k2, -⟩ := hK
  unfold kqIsOne
  by_cases h1 : c.nreg K0 < c.nreg r
  · by_cases h2 : c.nreg r < c.nreg K2
    · exact (IRS.ifT h1 ztoxc).mono by_omega by_simp_all
    · exact (IRS.ifT h1 (IRS.ifF h2 (IRS.skip (K := 0) hI by_grind))).mono by_omega
        ztb
  · exact (IRS.ifF h1 (IRS.skip (K := 0) hI by_simp_all)).mono by_omega ztb

/-! ## Offer to the running minimum -/

/-- Take the offered position. -/
def kqTake : List Instr := [.constN kqF 1, .copyN kqE kqSE, .copyN kqH kqSH]

/-- **Offer `(kqSE, kqSH)` to the running minimum** (taken if there is none, or if its offset is
smaller). -/
def offerQ : Stmt :=
  .ifLtN K0 kqF
    (.seq (callOff ztjl kqSE kqSH kqE kqH cGW kqO) (.ifLtN K0 kqO ztqef .skip))
    ztqef

/-- The registers the offer writes. -/
def OffR (r : ℕ) : Prop := r = kqF ∨ r = kqE ∨ r = kqH ∨ r = kqO ∨ r = kqO + 1

/-- The outputs of the offer. -/
def OfferQOut (P : Polygon) (J : Merge.Junction) (c c' : Config) : Prop :=
  c'.nreg kqF = 1 ∧
  ((c.nreg kqF = 1 ∧ c'.nreg kqE = c.nreg kqE ∧ c'.nreg kqH = c.nreg kqH) ∨
    (c'.nreg kqE = c.nreg kqSE ∧ c'.nreg kqH = c.nreg kqSH)) ∧
  offK P J ztvgt ztvgu ≤ offK P J ztvjr ztvjs ∧
  (c.nreg kqF = 1 →
    offK P J ztvgt ztvgu ≤ offK P J ztvjp ztvjq) ∧
  EFr OffR c c'
theorem kqTake_irs (hI : IInv W c₀ c) (hW : 1 ≤ W) :
    IRS P W c₀ ztqef c 3 (fun c' => c'.nreg kqF = 1 ∧ c'.nreg kqE = c.nreg kqSE ∧
      c'.nreg kqH = c.nreg kqSH ∧ EFr OffR c c') := by
  refine (IRS.block kqTake hI ?_).mono le_rfl ?_
  · simp only [kqTake, okB, okI]
    tauto
  · zuu
    refine ⟨?_, ?_, ?_, ⟨fun r _ hr hra => ?_, ?_, by_simp_all⟩⟩
    · rfl
    · rfl
    · rfl
    · unfold OffR at hr
      simp only [kqTake, regB, regI]
      simp_all
    rfl
set_option maxHeartbeats 4000000 in
/-- **The offer.** -/
theorem offerQ_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c)
    (hctx : ChainCtx P W c ztjl J.whole) (hgw : c.nreg cGW = gW J)
    (hgn : gW J < (chainModel J.whole).W.n) (hF : c.nreg kqF ≤ 1)
    (ht : c.nreg kqF = 1 → PosW P J ztvjp ztvjq)
    (hq : PosW P J ztvjr ztvjs) (hroom : c.nreg ALLOC + 11008 ≤ W) :
    IRS P W c₀ offerQ c 11020 (OfferQOut P J c) := by
  obtain ⟨k0, -, -, -, -, -, -⟩ := hK
  zudk
  zugmg
  unfold offerQ
  by_cases h1 : c.nreg K0 < c.nreg kqF
  · have hF1 : c.nreg kqF = 1 := by_omega
    have htP := ht hF1
    refine IRS.mono (K := 11015 + 2) (IRS.ifT h1 ?_) by_norm_num ztb
    refine IRS.seq (K₂ := 7) (callOff_irs hI hctx
      ⟨by_decide, by_decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide⟩
      ⟨by_decide, by_decide⟩ hq.1 htP.1 by_omega
      hq.2.1 htP.2.1 hq.2.2 htP.2.2 hroom) ?_
    rintro c₁ hI₁ hA₁ hA₁' ⟨b1, -, k₁, ha₁, hm₁⟩
    rw [hgw'] at b1
    change BitIs c₁ kqO (offK P J _ _ <
      offK P J _ _) at b1
    have fr1 : EFr OffR c c₁ := ⟨fun r hr hX hra => k₁ r hr ztwuv ztwuv hra, ha₁, hm₁⟩
    have keep : ∀ r, r = kqF ∨ r = kqE ∨ r = kqH ∨ r = kqSE ∨ r = kqSH → c₁.nreg r = c.nreg r := by
      zuz
      have hr' : 242480 ≤ r ∧ r ≤ 242484 := by
        unfold kqF kqE kqH kqSE kqSH sw at hr; omega
      exact k₁ r ztbet ztcyx
        ztcyx ztu
    have k01 : zteib := by
      rw [k₁ K0 ztmr
        by_decide by_decide by_decide]
      exact k0
    by_cases h2 : c₁.nreg K0 < c₁.nreg kqO
    · zudus
      zufgx
      refine IRS.mono (IRS.ifT by_omega (kqTake_irs hI₁ hW1))
        by_norm_num ?_
      zugay
      rw [keep _ by_omega] at e2
      rw [keep _ by_omega] at e3
      exact ⟨e1, by_omega, by_simp_all, by_grind,
        fr1.trans fr2⟩
    · zudus
      have hnlt : ztknr :=
        fun h => by have := b1.2.2 h; omega
      refine IRS.mono (K := 0 + 2) ztclp
        by_norm_num ?_
      zuu
      have eF := keep _ ztp
      have eE := keep _ ztwiz
      have eH := keep _ ztbajm
      exact ⟨by_omega, by_omega, by_grind,
        by grind, fr1⟩
  · have hF0 : c.nreg kqF ≠ 1 := by_omega
    refine IRS.mono (IRS.ifF h1 (kqTake_irs hI hW1)) by_norm_num ?_
    zugay
    exact ⟨e1, by_omega, by_simp_all, by_omega, fr2⟩

/-! ## Stores -/

/-- Store the registers `vs` at `x, x + 1, …` (raising `x`). -/
def storeL (x : ℕ) : List ℕ → Stmt
  | [] => .skip
  | v :: vs => .seq ztowe (.seq (.instr (.addN x x K1)) ztubd)

/-- **The stores.** -/
theorem storeL_irs {x : ℕ} (hx : IScr x) (hx1 : x ≠ K1) :
    ∀ (vs : List ℕ) {c : Config}, IInv W c₀ c → c.nreg K1 = 1 → ztmps →
      c₀.nreg ALLOC ≤ c.nreg x → c.nreg x + vs.length ≤ W →
      IRS P W c₀ ztubd c ztsso (fun c' =>
        (∀ i (h : i < vs.length), c'.nmem ztrmo = c.nreg (vs[i])) ∧
        (∀ y, (y < c.nreg x ∨ c.nreg x + vs.length ≤ y) → c'.nmem y = c.nmem y) ∧
        ztivl)
  | [], c, hI, _, _, _, _ => IRS.skip hI by_simp_all
  | v :: vs, c, hI, hK1, hv, hA, hW => by
    have hvx : v ≠ x := by_simp_all
    zuiox
    have e : 2 * (vs.length + 1) = 1 + ztpsk := by_ring
    zui
    refine IRS.seq ztnlr ?_
    zuer
    refine IRS.seq (IRS.instr1 hI₁ ⟨hx, by_grind⟩) ?_
    zubuo
    have hx2 : (upd c.nreg x (c.nreg x + c.nreg K1)) x = c.nreg x + 1 := by
      simp_all
    refine (storeL_irs hx hx1 vs hI₂ (by simp only [regI]; rw [upd_other _ _ _ (Ne.symm hx1)]; omega)
      by_simp_all
      ztmei
      ztmei).mono le_rfl ?_
    rintro c' ⟨s1, s2, s3⟩
    simp only [regI, hx2] at s1 s2 s3
    refine ⟨fun i hi => ?_, fun y hy => ?_, fun r hr => ?_⟩
    · zubuk
      · simp_all
      · have := s1 i by_omega
        rw [show c.nreg x + ztg = c.nreg x + 1 + i by ring, this]
        simp_all
    · rw [s2 _ by_omega]
      zuby
      grind
    simp_all

/-! ## Loads -/

/-- Load the position of stop `sP`: `kqX = sB + 5 sP + 1`. -/
def ldStopL : List Instr :=
  [.addN kqX sP sP, .addN kqX kqX kqX, .addN kqX kqX sP, .addN kqX kqX sB, .loadN kqSE kqX,
    .addN kqX kqX K1, .loadN kqSH kqX]
theorem ldStop_irs (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1)
    (hW : c.nreg sB + 5 * c.nreg sP + 1 ≤ W) :
    IRS P W c₀ ztqeg c 7 (fun c' =>
      c'.nreg kqSE = c.nmem (c.nreg sB + 5 * c.nreg sP) ∧
      c'.nreg kqSH = c.nmem (c.nreg sB + 5 * c.nreg sP + 1) ∧
      (∀ q, q ≠ kqX → q ≠ kqSE → q ≠ kqSH → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  simp only [sw, K1, sB, sP, Nat.reduceAdd] at hK1 hW
  refine (IRS.block ldStopL hI ?_).mono le_rfl ?_
  · simp [ldStopL, okB, okI, regI, upd, kqX, kqSE, kqSH, sP, sB, K1, sw, IScr, hK1]
    omega
  · zuu
    simp [ldStopL, regB, regI, upd, kqX, kqSE, kqSH, sP, sB, K1, sw, hK1]
    grind

/-- Load the flag of the auxiliary record `sP`: `kqX = aB + 5 sP`. -/
def ldAuxL : List Instr :=
  [.addN kqX sP sP, .addN kqX kqX kqX, .addN kqX kqX sP, .addN kqX kqX aB, .loadN kqV kqX]
theorem ldAux_irs (hI : IInv W c₀ c) (hW : c.nreg aB + 5 * c.nreg sP ≤ W) :
    IRS P W c₀ ztvfe c 5 (fun c' =>
      c'.nreg kqX = c.nreg aB + 5 * c.nreg sP ∧
      c'.nreg kqV = c.nmem zthgf ∧
      (∀ q, q ≠ kqX → q ≠ kqV → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  simp only [sw, aB, sP, Nat.reduceAdd] at hW
  refine (IRS.block ldAuxL hI ?_).mono le_rfl ?_
  · simp [ldAuxL, okB, okI, regI, upd, kqX, kqV, sP, aB, sw, IScr]
    omega
  · zuu
    simp [ldAuxL, regB, regI, upd, kqX, kqV, sP, aB, sw]
    grind

/-- Advance `kqX` and load `kqV` (resp. `kqY`) from it. -/
theorem ldNext_irs (hr : r = kqV ∨ r = kqY) (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1)
    (hW : c.nreg kqX + 1 ≤ W) :
    IRS P W c₀ (block [.addN kqX kqX K1, .loadN r kqX]) c 2 (fun c' =>
      c'.nreg kqX = c.nreg kqX + 1 ∧ c'.nreg r = c.nmem ztllp ∧
      (∀ q, q ≠ kqX → q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  zuccm

  · rcases hr with rfl | rfl <;>
    simp [okB, okI, kqX, kqV, kqY, K1, sw, IScr, hK1] <;> omega
  · zuu
    rcases hr with rfl | rfl <;>
    · simp [regB, regI, upd, kqX, kqV, kqY, K1, sw, hK1]
      simp_all
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
macro "kqr" : tactic => `(tactic| ((try simp only [kqF, kqE, kqH, kqSE, kqSH, kqO, kqB, kqA, kqN, kqL,
  kqX, kqV, kqY, kE, kH, kN, kL, bF, bE, bH, bN, bL, sP, sC, sB, aB, dF, lB, lC, wX, wE, wH, cGW,
  K0, K1, K2, K3, K4, ALLOC, OffR, LblR, KR, sw, ne_eq, not_or]) <;> omega))

/-! ## The program -/

/-- The best candidate. -/
def kqSelB : Stmt :=
  .seq (block [.constN kqF 0]) (kqIsOne bF (block [.constN kqF 1, .copyN kqE bE, .copyN kqH bH]))

/-- The next stop. -/
def selS : Stmt := .ifLtN sP sC (.seq ztqeg offerQ) .skip

/-- The window end. -/
def selW : Stmt := .ifLtN K0 wX .skip (.seq (block [.copyN kqSE wE, .copyN kqSH wH]) offerQ)

/-- **The selection of the least candidate.** -/
def kqSel : Stmt := .seq kqSelB (.seq selS selW)

/-- The registers the selection writes. -/
def SelR (r : ℕ) : Prop := OffR r ∨ r = kqSE ∨ r = kqSH ∨ r = kqX

/-- A candidate position. -/
def CandK (_P : Polygon) (_J : Merge.Junction) (c : Config) (e h : ℕ) : Prop :=
  (c.nreg bF = 1 ∧ e = c.nreg bE ∧ h = c.nreg bH) ∨
  (c.nreg sP < c.nreg sC ∧ e = stopE c ztccy ∧ h = stopH c ztccy) ∨
  (c.nreg wX = 0 ∧ e = c.nreg wE ∧ h = c.nreg wH)

/-- **The invariant of the selection** (stops considered iff `ps`, window end iff `pw`). -/
def SelInv (P : Polygon) (J : Merge.Junction) (c d : Config) (ps pw : Prop) : Prop :=
  EFr SelR c d ∧ d.nreg kqF ≤ 1 ∧
  (d.nreg kqF = 1 ↔ (c.nreg bF = 1 ∨ (ps ∧ c.nreg sP < c.nreg sC) ∨ (pw ∧ c.nreg wX = 0))) ∧
  (d.nreg kqF = 1 → CandK P J c ztdzr ztdzs ∧
    (c.nreg bF = 1 →
      offK P J ztdzr ztdzs ≤ offK P J ztvo ztvp) ∧
    (ps → c.nreg sP < c.nreg sC → offK P J ztdzr ztdzs ≤
      offK P J ztyrv ztyrw) ∧
    (pw → c.nreg wX = 0 →
      offK P J ztdzr ztdzs ≤ offK P J ztmhd ztmhe))

/-- The hypotheses on the candidates. -/
def CandHyp (P : Polygon) (J : Merge.Junction) (c : Config) : Prop :=
  ztxbh ∧
  ztdav ∧
  ztwwt ∧
  c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC
variable {P : Polygon} {W : ℕ} {c₀ c d : Config} {J : Merge.Junction}
theorem candK_posW {e h : ℕ} (hH : CandHyp P J c) (hc : CandK P J c e h) : PosW P J e h := by
  rcases hc with ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩
  · exact hH.1 h1
  · exact hH.2.2.1 _ h1
  · exact hH.2.1 h1
variable {X : ℕ → Prop}
theorem EFr.kkeep {c d : Config} (h : EFr X c d) {r : ℕ} (hr : ¬ X r)
    (h1 : 240000 ≤ r ∧ r < 250000) : d.nreg r = c.nreg r :=
  h.1 r (not_oracle_sw h1.1 h1.2) hr ztu

/-- The frame of a block. -/
theorem kqEfr_block (l : List Instr) (hX : ∀ i ∈ l, X ztcpw) (hA : ¬ X ALLOC) :
    EFr X c { c with nreg := regB c.nmem l c.nreg } :=
  ⟨fun r _ hr _ => regB_other _ _ _ by_grind,
    (regB_other _ _ _ by_grind).ge, by_simp_all⟩

/-- The stop records below the allocator are kept. -/
theorem kqStop_keep {c d : Config} (h : EFr X c d) (hsB : ¬ X sB)
    (hH : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC) {i : ℕ} (hi : i < c.nreg sC) :
    d.nmem (d.nreg sB + 5 * i) = stopE c i ∧ d.nmem (d.nreg sB + 5 * i + 1) = stopH c i := by
  rw [h.kkeep hsB by_decide]
  exact ⟨h.2.2 _ by_omega, h.2.2 _ by_omega⟩

/-! ## The steps -/
set_option maxHeartbeats 4000000 in
theorem selB_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hW : 1 ≤ W) :
    IRS P W c₀ kqSelB c 8 (fun d => SelInv P J c d False False) := by
  unfold kqSelB
  refine IRS.seq (K₂ := 7) (IRS.block [.constN kqF 0] hI
    ⟨⟨iscr_sw' by_norm_num by_norm_num, by_omega⟩, trivial⟩) ?_
  zukny
  have fr1 : EFr SelR c c₁ := by
    rw [hc₁]; exact kqEfr_block _ (by simp [dstI, SelR, OffR]) (by unfold SelR; kqr)
  have e0 : c₁.nreg kqF = 0 := by zvmxj; rfl
  have eF : c₁.nreg bF = c.nreg bF := fr1.kkeep (by unfold SelR; kqr) (by kqr)
  have eE : c₁.nreg bE = c.nreg bE := fr1.kkeep (by unfold SelR; kqr) (by kqr)
  have eH : c₁.nreg bH = c.nreg bH := fr1.kkeep (by unfold SelR; kqr) (by kqr)
  zueqk
  zuknm
  · refine (IRS.block _ hI₁ (by
      zudu
      tauto)).mono
      le_rfl ?_
    rintro d hd
    have fr2 : EFr SelR c₁ d := by
      rw [hd]; exact kqEfr_block _ (by simp [dstI, SelR, OffR]) (by unfold SelR; kqr)
    have v1 : d.nreg kqF = 1 := by zvnej; rfl
    have v2 : d.nreg kqE = c₁.nreg bE := by zvnej; rfl
    have v3 : d.nreg kqH = c₁.nreg bH := by
      zvnej; rfl
    rw [eE] at v2; rw [eH] at v3; zvnnc at h1
    refine ⟨fr1.trans fr2, by_omega, by_omega, fun _ => ⟨Or.inl by_omega,
      by simp_all, by_simp_all, by_simp_all⟩⟩
  · zvnnc at h1
    refine ⟨fr1, by_omega, ⟨by_simp_all, fun h => ?_⟩,
      by simp_all⟩
    simp_all
set_option maxHeartbeats 8000000 in
theorem selS_irs (hK₀ : Consts c₀) (hH : CandHyp P J c)
    (hctx : ChainCtx P W d ztjl J.whole) (hgw : d.nreg cGW = gW J)
    (hgn : gW J < (chainModel J.whole).W.n) (hId : IInv W c₀ d)
    (hS : SelInv P J c d False False) (hroom : d.nreg ALLOC + 11030 ≤ W) :
    IRS P W c₀ selS d 11029 (fun d' => SelInv P J c d' True False) := by
  zufiz
  have eSP : d.nreg sP = c.nreg sP := fr.kkeep (by unfold SelR; kqr) (by kqr)
  have eSC : d.nreg sC = c.nreg sC := fr.kkeep (by unfold SelR; kqr) (by kqr)
  have eBF : d.nreg bF = c.nreg bF := fr.kkeep (by unfold SelR; kqr) (by kqr)
  have eSB : d.nreg sB = c.nreg sB := fr.kkeep (by unfold SelR; kqr) (by kqr)
  zulie
  unfold selS
  by_cases hs : d.nreg sP < d.nreg sC
  · zuihu
    obtain ⟨l1, l2⟩ := kqStop_keep fr (by unfold SelR; kqr) hH.2.2.2 hs
    zulnz
    refine IRS.seq (K₂ := 11020) (ldStop_irs hId hKd.2.1 (by
      rw [eSP, eSB]
      have := hH.2.2.2; have := fr.2.1; omega)) ?_
    zuekp
    rw [eSP, l1] at s1; rw [eSP, l2] at s2
    have fr1 : ztuko := ⟨fun r _ hr _ => s3 r ztwkw
      ztbake ztwkw,
      by omega, by_simp_all⟩
    have k1 : ztfxk := fun r hr => by
      rcases hr with rfl | rfl | rfl <;> exact s3 _ (by kqr) (by kqr) (by kqr)
    zujzf
    refine (offerQ_irs hI₁ (hK₀.fix hI₁) (hctx.transport (fr1.kkeep (by unfold SelR; kqr) (by kqr))
      by_simp_all fr1.2.1) (by rw [fr1.kkeep (by unfold SelR; kqr) (by kqr)]; omega)
      hgn hF1 ztep (by zumzh; exact hH.2.2.1 _ hs) by_omega).mono le_rfl ?_
    · zucjx

    zuxu

    refine ⟨fr.trans ztkvw, by_omega,
      by simp_all, fun _ => ?_⟩
    zudsn
    · simp_all
    · zuea
      refine ⟨Or.inr by_omega, fun hb => ?_, by_simp_all, by_simp_all⟩
      grind
  · zuihu
    refine IRS.mono (K := 0 + 2) (IRS.ifF by_omega ztnlq)
      by_norm_num ?_
    zugbf
    refine ztkyk
    · simp_all
    simp_all
set_option maxHeartbeats 8000000 in
theorem selW_irs (hK₀ : Consts c₀) (hH : CandHyp P J c)
    (hctx : ChainCtx P W d ztjl J.whole) (hgw : d.nreg cGW = gW J)
    (hgn : gW J < (chainModel J.whole).W.n) (hId : IInv W c₀ d)
    (hS : SelInv P J c d True False) (hroom : d.nreg ALLOC + 11030 ≤ W) :
    IRS P W c₀ selW d 11024 (fun d' => SelInv P J c d' True True) := by
  zufiz
  have eWX : d.nreg wX = c.nreg wX := fr.kkeep (by unfold SelR; kqr) (by kqr)
  have eWE : d.nreg wE = c.nreg wE := fr.kkeep (by unfold SelR; kqr) (by kqr)
  have eWH : d.nreg wH = c.nreg wH := fr.kkeep (by unfold SelR; kqr) (by kqr)
  zulie
  unfold selW
  by_cases hs : d.nreg K0 < d.nreg wX
  · have hw : c.nreg wX ≠ 0 := by_omega
    refine IRS.mono (K := 0 + 2) (IRS.ifT hs ztnlq) by_norm_num ?_
    zugbf
    refine ztkyk
    · simp_all
    simp_all
  · have hw : c.nreg wX = 0 := by rw [hKd.1] at hs; omega
    refine IRS.mono (IRS.ifF hs ?_) le_rfl ztb
    refine IRS.seq (K₂ := 11020) (IRS.block [.copyN kqSE wE, .copyN kqSH wH] hId
      ⟨iscr_sw' by_norm_num by_norm_num, iscr_sw' by_norm_num by_norm_num, trivial⟩) ?_
    zukoe
    have fr1 : ztuko := by
      rw [hd₁]; exact kqEfr_block _ (by simp [dstI, SelR]) (by unfold SelR; kqr)
    have s1 : d₁.nreg kqSE = d.nreg wE := by zvnes; rfl
    have s2 : d₁.nreg kqSH = d.nreg wH := by zvnes; rfl
    rw [eWE] at s1; rw [eWH] at s2
    have k1 : ztfxk := fun r hr => by
      zvnes
      rcases hr with rfl | rfl | rfl <;> simp [regB, regI, upd, kqF, kqE, kqH, kqSE, kqSH, sw]
    zujzf
    refine (offerQ_irs hI₁ (hK₀.fix hI₁) (hctx.transport (fr1.kkeep (by unfold SelR; kqr) (by kqr))
      by_simp_all fr1.2.1) (by rw [fr1.kkeep (by unfold SelR; kqr) (by kqr)]; omega)
      hgn hF1 ztep (by zumzh; exact hH.2.1 hw) by_omega).mono le_rfl ?_
    · zucjx

    zuxu

    refine ⟨fr.trans ztkvw, by_omega,
      by simp_all, fun _ => ?_⟩
    zudsn
    · simp_all
    · zuea
      have hle : ∀ x : ℝ, d.nreg kqF = 1 → offK P J ztdzr ztdzs ≤ x →
          offK P J ztmhd ztmhe ≤ x := fun x hF' hx => by
        grind
      refine ⟨Or.inr by_omega, fun hb => ?_, fun _ hs' => ?_, by_simp_all⟩
      · simp_all
      simp_all
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def anchL : Stmt :=
  .seq zthdz
    (.ifLtN K0 kqY
      (.seq ztjpa (.seq ztlfw
        (.ifLtN K1 kqY (.seq ztjpa ztlfw)
          .skip)))
      .skip)

/-- **The labels of the stop `sP`** (if its auxiliary record is anchored). -/
def stopLab : Stmt := .seq ztvfe (kqIsOne kqV anchL)

/-- The registers of the label step. -/
def KStR (q : ℕ) : Prop := q = kqA ∨ q = kqX ∨ q = kqV ∨ q = kqY ∨ LblR kqN kqL q
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem kqLblOf_eq {c c' : Config} {N L : ℕ} (h : ∀ q, LblR N L q → c'.nreg q = c.nreg q) :
    lblOf c' N L = lblOf c N L := by
  zujqo
  rw [h N ztp]
  zucfh
  zug
  zucpm
  exact h _ ztxgk
theorem kqAddLs_nil (l : List ℕ) : addLs l [] = l := rfl
theorem kqAddLs_append (l a b : List ℕ) : addLs l ztrkm = addLs zttez b := by
  zumro
theorem addLabK_irs (hI : IInv W c₀ c) (hK : Consts c) (hN : c.nreg kqN ≤ 4) (hW : 4 ≤ W) :
    IRS P W c₀ ztlfw c 30 (fun c' => c'.nreg kqN ≤ 4 ∧
      lblOf c' kqN kqL = addL ztlqq (c.nreg kqV) ∧
      (∀ q, ¬ LblR kqN kqL q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) :=
  addLab_irs hI hK zttpq
    (fun i hi => iscr_sw ztozo ztozo)
    (fun i hi => by unfold kqN kqL sw; omega) (by kqr) (fun i hi => by unfold kqV kqL sw; omega)
    (by rintro k (rfl | rfl | rfl | rfl) <;> unfold LblR <;> kqr) hN hW
theorem anchHead_irs (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1) (hW : c.nreg kqX + 1 ≤ W) :
    IRS P W c₀ zthdz c 3 (fun c' =>
      c'.nreg kqA = 1 ∧ c'.nreg kqX = c.nreg kqX + 1 ∧ c'.nreg kqY = c.nmem ztllp ∧
      (∀ q, q ≠ kqA → q ≠ kqX → q ≠ kqY → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  zuccm

  · simp [okB, okI, regI, upd, kqX, kqA, kqY, K1, sw, IScr, hK1]
    omega
  · zuu
    simp [regB, regI, upd, kqX, kqA, kqY, K1, sw, hK1]
    simp_all
set_option maxHeartbeats 8000000 in
/-- **The labels of an anchored record.** -/
theorem anchL_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hN : c.nreg kqN ≤ 4)
    (hW : c.nreg kqX + 3 ≤ W) (hW4 : 4 ≤ W) :
    IRS P W c₀ anchL c 75 (fun c' =>
      c'.nreg kqA = 1 ∧ c'.nreg kqN ≤ 4 ∧
      lblOf c' kqN kqL = addLs ztlqq
        ((List.range (min (c.nmem ztllp) 2)).map fun t => c.nmem (c.nreg kqX + 2 + t)) ∧
      ztiut ∧ c'.nmem = c.nmem) := by
  zuyr
  unfold anchL
  refine IRS.seq (K₁ := 3) (K₂ := 72) (anchHead_irs hI hK.2.1 by_omega) ?_
  rintro c₁ hI₁ - - ⟨a1, a2, a3, a4, a5⟩
  zueqk
  have nA : ∀ q, ¬ KStR q → q ≠ kqA ∧ q ≠ kqX ∧ q ≠ kqY := fun q hq =>
    ⟨fun h => hq zteg, fun h => hq ztwkb, fun h => hq (Or.inr (Or.inr (Or.inr
      zteg)))⟩
  have nL : ∀ q, LblR kqN kqL q → q ≠ kqA ∧ q ≠ kqX ∧ q ≠ kqY ∧ q ≠ kqV := fun q hq => by
    simp only [LblR, kqN, kqL, sw] at hq; refine ztfh <;> kqr
  have lb1 : ztmwg := kqLblOf_eq fun q hq =>
    a4 q (nL q hq).1 (nL q hq).2.1 (nL q hq).2.2.1
  have eN1 : c₁.nreg kqN = c.nreg kqN := a4 _ (by kqr) (by kqr) (by kqr)
  set m := c.nmem with hm
  set x := c.nreg kqX with hx
  by_cases h0 : c₁.nreg K0 < c₁.nreg kqY
  · zuiiu
    refine IRS.mono (K := 66 + 2) (IRS.ifT (by rw [hK₁.1, a3]; exact h0) ?_) by_norm_num
      ztb
    refine IRS.seq (K₁ := 2) (K₂ := 64) (ldNext_irs ztp hI₁ hK₁.2.1 by_omega) ?_
    rintro c₂ hI₂ - - ⟨b1, b2, b3, b4⟩
    zuheh
    have eN2 : c₂.nreg kqN = c.nreg kqN := (b3 _ (by kqr) (by kqr)).trans eN1
    have lb2 : lblOf c₂ kqN kqL = lblOf c kqN kqL := (kqLblOf_eq fun q hq =>
      b3 q (nL q hq).2.1 (nL q hq).2.2.2).trans lb1
    rw [a5, a2] at b2
    refine IRS.seq (K₁ := 30) (K₂ := 34) (addLabK_irs hI₂ hK₂ by_omega hW4) ?_
    rintro c₃ hI₃ - - ⟨d1, d2, d3, d4⟩
    rw [lb2, b2] at d2
    zulim
    have eY3 : c₃.nreg kqY = m zthf := by
      rw [d3 _ by_grind, b3 _ (by kqr) (by kqr), a3]
    have eX3 : c₃.nreg kqX = x + 2 := by_grind
    have eA3 : c₃.nreg kqA = 1 := by
      rw [d3 _ by_grind, b3 _ (by kqr) (by kqr), a1]
    have fr3 : ∀ q, ¬ KStR q → c₃.nreg q = c.nreg q := fun q hq => by
      rw [d3 q ztbamb,
        b3 q (nA q hq).2.1 ztbaky,
        a4 q (nA q hq).1 (nA q hq).2.1 (nA q hq).2.2]
    have mem3 : c₃.nmem = m := by_simp_all
    by_cases h1 : c₃.nreg K1 < c₃.nreg kqY
    · zuiiz
      refine IRS.mono (K := 32 + 2) (IRS.ifT ztkta ?_) le_rfl
        ztb
      refine IRS.seq (K₁ := 2) (K₂ := 30) (ldNext_irs ztp hI₃ hK₃.2.1 by_omega) ?_
      rintro c₄ hI₄ - - ⟨e1, e2, e3, e4⟩
      have lb4 : lblOf c₄ kqN kqL = lblOf c₃ kqN kqL := kqLblOf_eq fun q hq =>
        e3 q (nL q hq).2.1 (nL q hq).2.2.2
      have eN4 : c₄.nreg kqN = c₃.nreg kqN := e3 _ (by kqr) (by kqr)
      rw [mem3, eX3] at e2
      refine (addLabK_irs hI₄ ztqpk by_omega hW4).mono le_rfl ?_
      zucph
      refine ⟨by rw [f3 _ by_grind, e3 _ (by kqr) (by kqr), eA3], f1, ?_,
        fun q hq => ?_, by_grind⟩
      · rw [f2, lb4, d2, e2, show min ztyjn 2 = 2 by omega]
        rfl
      · rw [f3 q ztbamb,
          e3 q (nA q hq).2.1 ztbaky, fr3 q hq]
    · zuiiz
      refine IRS.mono (K := 0 + 2) (IRS.ifF ztkta zthau)
        by_norm_num ?_
      zuu
      refine ⟨eA3, d1, ?_, fr3, mem3⟩
      rw [d2, show min ztyjn 2 = 1 by omega]
      rfl
  · zuiiu
    refine IRS.mono (K := 0 + 2) ztclp
      by_norm_num ?_
    zuu
    refine ⟨a1, by_omega, ?_, fun q hq => a4 q (nA q hq).1 (nA q hq).2.1 (nA q hq).2.2,
      a5⟩
    rw [lb1, show min ztyjn 2 = 0 by omega]
    rfl
set_option maxHeartbeats 8000000 in
/-- **The labels of the stop `sP`.** -/
theorem stopLab_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hN : c.nreg kqN ≤ 4)
    (hW : c.nreg aB + 5 * c.nreg sP + 3 ≤ W) (hW4 : 4 ≤ W) :
    IRS P W c₀ stopLab c 84 (fun c' =>
      ztiut ∧ c'.nmem = c.nmem ∧ c'.nreg kqN ≤ 4 ∧
      lblOf c' kqN kqL = addLs ztlqq (stopLabs c.nmem ztmgu ztccy) ∧
      (c.nmem zthgf = 1 → c'.nreg kqA = 1) ∧
      (c.nmem zthgf ≠ 1 → c'.nreg kqA = c.nreg kqA)) := by
  unfold stopLab
  refine IRS.seq (K₁ := 5) (K₂ := 79) (ldAux_irs hI by_omega) ?_
  rintro c₁ hI₁ - - ⟨a1, a2, a3, a4⟩
  zueqk
  have nL : ∀ q, LblR kqN kqL q → q ≠ kqX ∧ q ≠ kqV := fun q hq => by
    simp only [LblR, kqN, kqL, sw] at hq; refine ztcp <;> kqr
  have lb1 : ztmwg := kqLblOf_eq fun q hq =>
    a3 q (nL q hq).1 (nL q hq).2
  have fr1 : ∀ q, ¬ KStR q → c₁.nreg q = c.nreg q := fun q hq =>
    a3 q ztbakd ztbaky
  have eN1 : c₁.nreg kqN = c.nreg kqN := a3 _ (by kqr) (by kqr)
  have eA1 : c₁.nreg kqA = c.nreg kqA := a3 _ (by kqr) (by kqr)
  refine kqIsOne_irs (K := 75) hI₁ hK₁ ztyq ztyq
  · zukqc
    refine (anchL_irs hI₁ hK₀ by_omega by_omega hW4).mono le_rfl ?_
    rintro c' ⟨b1, b2, b3, b4, b5⟩
    refine ⟨fun q hq => (b4 q hq).trans (fr1 q hq), by_simp_all, b2, ?_, fun _ => b1,
      fun h => absurd h1 h⟩
    rw [b3, lb1, a1, a4]
    zumvb
    simp_all
  · zukqc
    refine ⟨fr1, a4, by_omega, ?_, fun h => absurd h h1, fun _ => eA1⟩
    rw [lb1]
    zumvb
    rw [ite_eq_right h1, kqAddLs_nil]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def skipS (next : Stmt) : Stmt :=
  .ifLtN sP sC
    (.seq ztqeg (.seq (callOff ztjl kE kH kqSE kqSH cGW kqO)
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
  hpk : PosW P J ztmiu ztmiv
  hmin : c.nreg sP < c.nreg sC → offK P J ztmiu ztmiv ≤
    offK P J ztyrv ztyrw
  hps : ∀ i, i < c.nreg sC → PosW P J ztbjv ztbjw
  hsort : ∀ i i', i ≤ i' → i' < c.nreg sC →
    offK P J ztbjv ztbjw ≤ offK P J ztkfo ztkfp
  htwo : ∀ i, i + 2 < c.nreg sC →
    offK P J ztbjv ztbjw < offK P J ztxyb ztxyc
  hsBA : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC
  haBA : c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC

/-- **The invariant of the skipping** after `j` skipped stops. -/
def SkInv (P : Polygon) (J : Merge.Junction) (c d₀ d : Config) (j : ℕ) : Prop :=
  EFr SkR d₀ d ∧ d.nreg sP = c.nreg sP + j ∧ c.nreg sP + j ≤ c.nreg sC ∧ j ≤ 2 ∧
  (∀ i, c.nreg sP ≤ i → i < c.nreg sP + j →
    offK P J ztbjv ztbjw = offK P J ztmiu ztmiv) ∧
  d.nreg kqN ≤ 4 ∧
  lblOf d kqN kqL = addLs (lblOf d₀ kqN kqL)
    ((List.range' ztccy j).flatMap ztzxz) ∧
  d.nreg kqA ≤ 1 ∧
  (d.nreg kqA = 1 ↔ ∃ i, c.nreg sP ≤ i ∧ i < c.nreg sP + j ∧ c.nmem ztduc = 1)

/-- **The end of the skipping**: the next stop is not at the key. -/
def SkDone (P : Polygon) (J : Merge.Junction) (c d₀ d : Config) : Prop :=
  ∃ j, SkInv P J c d₀ d j ∧ (d.nreg sP < c.nreg sC →
    offK P J (stopE c ztvou) (stopH c ztvou) ≠ offK P J ztmiu ztmiv)
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c d₀ d : Config} {J : Merge.Junction} {N₁ N₂ : NF}
theorem kqGW_lt (J : Merge.Junction) : gW J < (chainModel J.whole).W.n := by
  zugq
theorem stopLabs_congr {m m' : ℕ → ℕ} {A i : ℕ} (h : ∀ t, t < 4 → m' ztnip = m ztnip) :
    stopLabs m' A i = stopLabs m A i := by
  have h0 := h 0 by_norm_num; have h1 := h 1 by_norm_num
  zudca
  zumvb
  rw [h0, h1]
  split_ifs
  · zucfh
    zucj
    zudtp
    have := h (2 + t) by_omega
    grind
  · rfl
theorem skInv_zero (hS : SkCtx P J c d₀) (hsC : c.nreg sP ≤ c.nreg sC) (hN : d₀.nreg kqN ≤ 4)
    (hA : d₀.nreg kqA = 0) : SkInv P J c d₀ d₀ 0 :=
  ⟨EFr.refl _ _, by rw [hS.hsP]; rfl, by_omega, by_norm_num, by_simp_all, hN,
    by rfl, by_omega, by_omega⟩
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **One skip.** -/
theorem skipS_irs {next : Stmt} {K : ℕ} {Q : Config → Prop} {j : ℕ}
    (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hS : SkCtx P J c d₀) (hId : IInv W c₀ d)
    (hj1 : j ≤ 1) (hj : SkInv P J c d₀ d j) (hroom : d.nreg ALLOC + 11200 ≤ W)
    (hnext : ∀ d', IInv W c₀ d' → d'.nreg ALLOC ≤ d.nreg ALLOC + 11200 →
      SkInv P J c d₀ d' ztl → IRS P W c₀ next d' K Q)
    (hstop : ∀ d', SkDone P J c d₀ d' → Q d') :
    IRS P W c₀ (skipS next) d (11200 + K) Q := by
  obtain ⟨fr, hsP, hjC, hj2, hoff, hN, hlb, hA1, hAiff⟩ := hj
  have nSk : ∀ r, (r = sC ∨ r = sB ∨ r = aB ∨ r = kE ∨ r = kH) → ¬ SkR r ∧ 240000 ≤ r ∧ r < 250000 :=
    fun r hr => by
      simp only [sC, sB, aB, kE, kH, sw] at hr
      exact ⟨by simp only [SkR, KStR, LblR]; kqr, by kqr, by kqr⟩
  have kp :=
    fun r hr => fr.kkeep by_grind (nSk r hr).2
  have eSC := (kp _ ztp).trans hS.hsC
  have eSB := (kp _ by_omega).trans hS.hsB
  have eAB := (kp _ by_omega).trans hS.haB
  have eKE : d.nreg kE = d₀.nreg kE := by_grind
  have eKH : d.nreg kH = d₀.nreg kH := by_grind
  have hAd := hS.hA.trans fr.2.1
  have hmem := fun x hx =>
    (fr.2.2 x (lt_of_lt_of_le hx hS.hA)).trans (hS.hm x hx)
  zulid
  zukar
  set o' := offK P J _ _ with ho'
  unfold skipS
  by_cases hsd : d.nreg sP < d.nreg sC
  · have hs : c.nreg sP + j < c.nreg sC := by_omega
    set i := c.nreg sP + j with hi
    refine IRS.mono (K := 11102 + K + 2) (IRS.ifT hsd ?_) by_omega ztb
    have hsBA := hS.hsBA
    have haBA := hS.haBA
    have h5 : 5 * i + 5 ≤ 5 * c.nreg sC := by_omega
    refine (IRS.seq (K₂ := 11095 + K) (ldStop_irs hId hKd.2.1 by_omega)
      ?_).mono by_omega (fun _ h => h)
    zuekp
    rw [eSB, hsP, hmem _ by_omega] at s1
    rw [eSB, hsP, hmem _ by_omega] at s2
    change d₁.nreg kqSE = stopE c i at s1
    change d₁.nreg kqSH = stopH c i at s2
    have fr1 : EFr SkR d d₁ := ⟨fun r _ hr _ => s3 r (fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr
      ztbase)))))
      ztbake ztwkw,
      by omega, by_grind⟩
    have eKE1 := (s3 _ (by kqr) (by kqr) (by kqr)).trans eKE
    have eKH1 := (s3 _ (by kqr) (by kqr) (by kqr)).trans eKH
    zulkc
    have hgw₁' : ztgtg := by_grind
    have hpk := hS.hpk
    have hpi := hS.hps i hs
    refine IRS.seq (K₂ := 87 + K) (callOff_irs hI₁ ztpxi
      ⟨by_decide, by_decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide⟩
      ⟨by_decide, by_decide⟩ (by rw [eKE1]; exact hpk.1)
      (by zunsu; exact hpi.1) ztlhu (by zuooi; exact hpk.2.1)
      (by zumzh; exact hpi.2.1) (by zuooi; exact hpk.2.2)
      (by zumzh; exact hpi.2.2) by_omega) ?_ |>.mono by_omega (fun _ h => h)
    zudsx
    rw [hgw₁', eKE1, eKH1, s1, s2] at b1
    change BitIs d₂ kqO _ at b1
    have fr2 : EFr SkR d₁ d₂ := ⟨fun r hr hX hra => k₂ r hr
      ztwuv
      ztwuv hra, ha₂, hm₂⟩
    have same : ∀ r, r = sP ∨ r = kqA ∨ LblR kqN kqL r → d₂.nreg r = d.nreg r := by
      zuz
      have hr' : r = sP ∨ r = kqA ∨ (kqN ≤ r ∧ r < kqL + 4) := by
        rcases hr with h | h | h | h
        · omega
        · omega
        · exact Or.inr ztgqp
        · exact Or.inr (Or.inr ⟨by unfold kqN kqL sw at *; omega, h.2⟩)
      have hr'' : r = 242450 ∨ (242488 ≤ r ∧ r < 242494) := by
        simp only [sP, kqA, kqN, kqL, sw] at hr'; omega
      rw [k₂ r ztbet ztcyx
        ztcyx ztu]
      exact s3 r (by unfold kqX sw; omega) (by unfold kqSE sw; omega) (by unfold kqSH sw; omega)
    have eSP2 : d₂.nreg sP = i := by_grind
    have eN2 := same _ ztbajm
    have eA2 : d₂.nreg kqA = d.nreg kqA := by_grind
    have lb2 : lblOf d₂ kqN kqL = lblOf d kqN kqL := kqLblOf_eq by_grind
    have fr02 := fr.trans (fr1.trans fr2)
    zudpy

    · zudut
      have hlt : o' < offK P J _ _ := b1.2.1 (by have := b1.1; omega)
      refine IRS.mono (K := 0 + 2) zthat by_omega ?_
      zugbf
      refine hstop d₂ ⟨j, ⟨fr02, by_omega, hjC, hj2, hoff, by_omega,
        by grind, by_omega, by rw [eA2]; omega⟩, fun _ => ?_⟩
      grind
    · zudut
      have hnlt : ¬ o' < offK P J _ _ := fun h => by have := b1.2.2 h; omega
      have hle : o' ≤ offK P J ztbjv ztbjw := by
        rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · have := hS.hmin by_omega
          rw [hi, hj0, Nat.add_zero]; omega
        · zuino
          exact hS.hsort _ _ by_omega hs
      have heq : offK P J _ _ = o' := le_antisymm ztwai hle
      refine IRS.mono (K := 85 + K + 2) ztbyj by_omega
        ztb
      have eAB2 : d₂.nreg aB = c.nreg aB := by
        rw [fr02.kkeep by_grind (nSk aB by_omega).2]
        grind
      have hAd2 := by_omega
      have hmem2 : ∀ x, x < c.nreg ALLOC → d₂.nmem x = c.nmem x := fun x hx => by
        grind
      refine IRS.seq (K₂ := 1 + K) (stopLab_irs hI₂ E.hK by_omega
        by_omega hW4) ?_ |>.mono by_omega (fun _ h => h)
      rintro d₃ hI₃ hA₃ hA₃' ⟨t1, t2, t3, t4, t5, t6⟩
      rw [eAB2, eSP2, stopLabs_congr (fun t ht => hmem2 _ by_omega)] at t4
      rw [eAB2, eSP2, hmem2 _ by_omega] at t5 t6
      zuhei
      have eSP3 : d₃.nreg sP = i := by
        rw [t1 _ (by unfold KStR LblR; kqr)]; omega
      refine IRS.seq (IRS.block [.addN sP sP K1] hI₃
        ⟨⟨iscr_sw' by_norm_num by_norm_num, by rw [eSP3, hK₃.2.1]; omega⟩, trivial⟩) ?_
      rintro d₄ hI₄ hA₄ hA₄' hd₄
      have v1 : d₄.nreg sP = i + 1 := by
        zungl; simp [regB, regI, eSP3, hK₃.2.1]
      have v2 : ∀ r, r ≠ sP → d₄.nreg r = d₃.nreg r := fun r hr => by
        zuedd
      have mem4 : d₄.nmem = d₃.nmem := by zungl
      have fr34 : EFr SkR d₂ d₄ := ⟨fun r _ hr _ => by
          rw [v2 r ztwnm]
          exact t1 r ztzfc,
        by omega, by_grind⟩
      refine hnext d₄ hI₄ (by
        omega) ?_
      have eN4 : d₄.nreg kqN = d₃.nreg kqN := v2 _ (by kqr)
      have eA4 : d₄.nreg kqA = d₃.nreg kqA := v2 _ (by kqr)
      have lb4 : lblOf d₄ kqN kqL = lblOf d₃ kqN kqL := kqLblOf_eq fun q hq =>
        v2 q (by simp only [LblR, kqN, kqL, sw] at hq; kqr)
      refine ⟨fr02.trans fr34, by_omega, by_omega, by_omega, fun i' h1 h2 => ?_, by_omega,
        ?_, ?_, ?_⟩
      · grind
      · rw [lb4, t4, lb2, hlb, ← kqAddLs_append, ← List.flatMap_singleton (f := stopLabs c.nmem
          _), ← List.flatMap_append, List.range'_1_concat]
      · omega
      · by_cases hf : c.nmem ztduc = 1
        · rw [eA4, t5 hf]
          exact ⟨fun _ => ⟨i, by_omega, by_omega, hf⟩, by_omega⟩
        · rw [eA4, t6 hf, eA2, hAiff]
          constructor
          · rintro ⟨i', h1, h2, h3⟩; exact ⟨i', h1, by_omega, h3⟩
          · rintro ⟨i', h1, h2, h3⟩
            refine ⟨i', h1, ?_, h3⟩
            rcases Nat.lt_or_ge i' i with h | h
            · zubh
            · exact absurd (show i' = i by omega ▸ h3) hf
  · have hs : ¬ c.nreg sP + j < c.nreg sC := by_omega
    refine IRS.mono (K := 0 + 2) (IRS.ifF hsd ztnlq) by_omega ?_
    zugbf
    exact hstop d ⟨j, ⟨fr, hsP, hjC, hj2, hoff, hN, hlb, hA1, hAiff⟩, by_grind⟩

/-- **The two skips.** -/
theorem skip2_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hS : SkCtx P J c d₀)
    (hId₀ : IInv W c₀ d₀) (h0 : SkInv P J c d₀ d₀ 0) (hroom : d₀.nreg ALLOC + 22400 ≤ W) :
    IRS P W c₀ ztqwn d₀ 22400 (SkDone P J c d₀) := by
  refine (skipS_irs (K := 11200) E hS hId₀ by_norm_num h0 by_omega (fun d' hI' hA' h1 => ?_)
    by_simp_all).mono le_rfl (fun _ h => h)
  refine (skipS_irs (K := 0) E hS hI' le_rfl h1 by_omega (fun d'' hI'' _ h2 => IRS.skip hI'' ?_)
    ztb).mono le_rfl (fun _ h => h)
  refine ⟨2, h2, fun hlt => ?_⟩
  obtain ⟨-, hsP, -, -, hoff, -⟩ := h2
  rw [hsP]
  zuino
  exact ne_of_gt (hS.htwo _ by_omega)
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def setKL : List Instr :=
  [.copyN kE kqE, .copyN kH kqH, .constN dF 0, .constN kqB 0, .constN kqA 0]

/-- The flag "the best candidate is at the key". -/
def bestAt : Stmt :=
  kqIsOne bF (.seq (callOff ztjl kE kH bE bH cGW kqO) (.ifLtN K0 kqO .skip (block [.constN kqB 1])))

/-- Copy the best's labels. -/
def cpBestL : List Instr :=
  [.copyN kqN bN, .copyN kqL bL, .copyN zttqz ztbzi, .copyN zttra ztfpc,
    .copyN zttrb ztnru]

/-- The initial label list under construction. -/
def initLab : Stmt := .ifLtN K0 kqB (block cpBestL) (block [.constN kqN 0])

/-- The steps before the skipping. -/
def kqPre : Stmt := .seq (block setKL) (.seq bestAt initLab)

/-- Copy the label list under construction to `(kN, kL)`. -/
def cpLabL : List Instr :=
  [.copyN kN kqN, .copyN kL kqL, .copyN ztdvf zttqz, .copyN ztdvg zttra,
    .copyN ztdvh zttrb]

/-- **The new label list** (iff `kqB = 1 ∨ kqA = 1`). -/
def finLab : Stmt := .ifLtN K0 kqB ztqed (.ifLtN K0 kqA ztqed .skip)

/-- The address of the log record: `kqX = lB + 7 lC`. -/
def logAddrL : List Instr :=
  [.addN kqY lC lC, .addN kqX kqY kqY, .addN kqX kqX kqY, .addN kqX kqX lC, .addN kqX kqX lB]

/-- The registers of the log record. -/
def logRegs : List ℕ := [kE, kH, kN, kL, kL + 1, kL + 2, kL + 3]

/-- **The log record.** -/
def writeLog : Stmt :=
  .seq (block logAddrL) (.seq (storeL kqX logRegs) (block [.addN lC lC K1]))

/-- The registers `pre` writes. -/
def PreR (r : ℕ) : Prop :=
  r = kE ∨ r = kH ∨ r = dF ∨ r = kqB ∨ r = kqA ∨ r = kqO ∨ r = kqO + 1 ∨ LblR kqN kqL r
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c d : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- A copy of a label list. -/
theorem kqLblOf_copy {c c' : Config} {N L N' L' : ℕ} (hN : c'.nreg N' = c.nreg N)
    (hL : ∀ i, i < 4 → c'.nreg (L' + i) = c.nreg ztsyy) : lblOf c' N' L' = lblOf c N L := by
  zujqo
  simp_all
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **The steps before the skipping.** -/
theorem pre_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hId : IInv W c₀ d)
    (hpk : PosW P J ztdzr ztdzs)
    (hbP : d.nreg bF = 1 → PosW P J ztjts ztjtt)
    (hmin : d.nreg bF = 1 →
      offK P J ztdzr ztdzs ≤ offK P J ztjts ztjtt)
    (hroom : d.nreg ALLOC + 11030 ≤ W) :
    IRS P W c₀ kqPre d 11030 (fun d' =>
      EFr PreR d d' ∧ d'.nreg kE = d.nreg kqE ∧ d'.nreg kH = d.nreg kqH ∧ d'.nreg dF = 0 ∧
      d'.nreg kqA = 0 ∧ d'.nreg kqB ≤ 1 ∧
      (d'.nreg kqB = 1 ↔ (d.nreg bF = 1 ∧
        offK P J ztjts ztjtt = offK P J ztdzr ztdzs)) ∧
      (d'.nreg kqB = 1 → d'.nreg kqN = d.nreg bN ∧ lblOf d' kqN kqL = lblOf d bN bL) ∧
      (d'.nreg kqB ≠ 1 → lblOf d' kqN kqL = [] ∧ d'.nreg kqN = 0)) := by
  have hW : ztbla := by_omega
  unfold kqPre
  refine (IRS.seq (K₁ := 5) (K₂ := 11025) (IRS.block setKL hId (by
    simp only [setKL, okB, okI]
    exact ⟨iscr_sw' by_norm_num by_norm_num, iscr_sw' by_norm_num by_norm_num,
      ⟨iscr_sw' by_norm_num by_norm_num, by_omega⟩, ⟨iscr_sw' by_norm_num by_norm_num,
        by omega⟩, ⟨iscr_sw' by_norm_num by_norm_num, by_omega⟩, trivial⟩)) ?_).mono le_rfl
    ztb
  zukoe
  have v1 : d₁.nreg kE = d.nreg kqE := by zvnes; rfl
  have v2 : d₁.nreg kH = d.nreg kqH := by zvnes; rfl
  have v3 : d₁.nreg dF = 0 := by zvnes; rfl
  have v4 : d₁.nreg kqB = 0 := by zvnes; rfl
  have v5 : d₁.nreg kqA = 0 := by zvnes; rfl
  have fr1 : EFr PreR d d₁ := by
    rw [hd₁]; exact kqEfr_block _ (by simp [setKL, dstI, PreR]) (by unfold PreR; kqr)
  have kp1 : ∀ r, ¬ PreR r → 240000 ≤ r ∧ r < 250000 → d₁.nreg r = d.nreg r := fun r h1 h2 =>
    fr1.kkeep h1 h2
  have eBF : d₁.nreg bF = d.nreg bF := kp1 _ (by unfold PreR; kqr) (by kqr)
  have eBE : d₁.nreg bE = d.nreg bE := kp1 _ (by unfold PreR; kqr) (by kqr)
  have eBH : d₁.nreg bH = d.nreg bH := kp1 _ (by unfold PreR; kqr) (by kqr)
  zubke
  -- the flag
  have hB : IRS P W c₀ bestAt d₁ 11015 (fun d₂ => EFr PreR d₁ d₂ ∧ d₂.nreg kqB ≤ 1 ∧
      (d₂.nreg kqB = 1 ↔ (d.nreg bF = 1 ∧
        offK P J ztjts ztjtt = offK P J ztdzr ztdzs)) ∧
      (∀ r, r = kE ∨ r = kH ∨ r = dF ∨ r = kqA → d₂.nreg r = d₁.nreg r)) := by
    unfold bestAt
    zuknm
    · zukqz
      have hbp := hbP h1
      zulkc
      have hgw₁' : ztgtg := by_simp_all
      refine IRS.seq (K₂ := 3) (callOff_irs hI₁ ztpxi
        ⟨by_decide, by_decide, by_decide, by_decide,
          by decide, by_decide, by_decide,
          by decide, by_decide, by_decide,
          by decide, by_decide⟩
        ⟨by_decide, by_decide⟩ (by rw [v1]; exact hpk.1)
        (by zupcf; exact hbp.1) ztlhu (by zunqo; exact hpk.2.1)
        (by zungw; exact hbp.2.1) (by zunqo; exact hpk.2.2)
        (by zungw; exact hbp.2.2) by_omega) ?_
      zudsx
      rw [hgw₁', v1, v2, eBE, eBH] at b1
      change BitIs d₂ kqO (offK P J _ _ <
        offK P J _ _) at b1
      have fr2 : EFr PreR d₁ d₂ := ⟨fun r hr hX hra => k₂ r hr
        ztwuv
        ztwuv hra, ha₂, hm₂⟩
      have kp2 : ∀ r, r = kE ∨ r = kH ∨ r = dF ∨ r = kqA ∨ r = kqB → d₂.nreg r = d₁.nreg r := by
        zuz
        have hr' : r = 242400 ∨ r = 242401 ∨ r = 242451 ∨ r = 242488 ∨ r = 242487 := by
          tauto
        exact k₂ r ztbet ztcyx
          ztcyx ztu
      zudpy

      · zudut
        zufgx
        refine IRS.mono (K := 0 + 2) zthat
          by_norm_num ?_
        grind
      · zudut
        have hnlt : ztknr :=
          fun h => by have := b1.2.2 h; omega
        have heq : offK P J _ _ = offK P J _ _ :=
          le_antisymm ztwai (hmin h1)
        refine IRS.mono (IRS.ifF by_omega (IRS.block _ hI₂
          ⟨⟨iscr_sw' by_norm_num by_norm_num, hW⟩, trivial⟩)) by_norm_num ?_
        zugbe
        have w1 : d'.nreg kqB = 1 := by zumzk; rfl
        have w2 : ∀ r, r ≠ kqB → d'.nreg r = d₂.nreg r := fun r hr => by
          zutu
        refine ⟨fr2.trans ⟨fun r _ hr _ => w2 r ztwkw,
          by grind, fun a _ => by zumzk⟩, by_omega,
          by grind, fun r hr => ?_⟩
        rw [w2 r (by rcases hr with rfl | rfl | rfl | rfl <;> kqr)]
        grind
    · zukqz
      exact ⟨EFr.refl _ _, by_omega, by_omega,
        by omega⟩
  refine IRS.seq (K₂ := 10) hB ?_
  rintro d₂ hI₂ hA₂ hA₂' ⟨fr2, hb1, hbiff, kp2⟩
  zudhh
  have eBN : d₂.nreg bN = d.nreg bN := (fr2.kkeep (by unfold PreR; kqr) (by kqr)).trans
    (kp1 _ (by unfold PreR; kqr) (by kqr))
  have eBL : ∀ i, i < 4 → d₂.nreg _ = d.nreg ztctw := fun i hi =>
    (fr2.kkeep (by unfold PreR; kqr) (by kqr)).trans (kp1 _ (by unfold PreR; kqr) (by kqr))
  have common : ∀ d' : Config, EFr PreR d₂ d' → d'.nreg kqB = d₂.nreg kqB →
      (∀ r, r = kE ∨ r = kH ∨ r = dF ∨ r = kqA → d'.nreg r = d₂.nreg r) →
      EFr PreR d d' ∧ d'.nreg kE = d.nreg kqE ∧ d'.nreg kH = d.nreg kqH ∧ d'.nreg dF = 0 ∧
      d'.nreg kqA = 0 ∧ d'.nreg kqB ≤ 1 ∧
      (d'.nreg kqB = 1 ↔ (d.nreg bF = 1 ∧
        offK P J ztjts ztjtt = offK P J ztdzr ztdzs)) := by
    intro d' fr hB' hk
    refine ⟨fr1.trans (fr2.trans fr), ?_, ?_, ?_, ?_, by_omega, by_grind⟩
    · grind
    · grind
    · grind
    grind
  unfold initLab
  by_cases h3 : d₂.nreg K0 < d₂.nreg kqB
  · zuksu
    have hB1 : d₂.nreg kqB = 1 := by_omega
    refine IRS.mono (K := 5 + 2) (IRS.ifT (by zuogj; exact h3) (IRS.block cpBestL hI₂ (by
      simp only [cpBestL, okB, okI]
      exact ⟨iscr_sw' by_norm_num by_norm_num, iscr_sw' by_norm_num by_norm_num,
        iscr_sw by_decide by_decide,
        iscr_sw by_decide by_decide,
        iscr_sw by_decide by_decide, trivial⟩)))
      by_norm_num ?_
    zugbe
    have fr3 : ztukn := by
      rw [hd']; exact kqEfr_block _ (by simp [cpBestL, dstI, PreR, LblR, kqN, kqL, sw]) (by unfold PreR; kqr)
    have w0 : ∀ r, r = kE ∨ r = kH ∨ r = dF ∨ r = kqA ∨ r = kqB → d'.nreg r = d₂.nreg r := by
      zuz
      zujit
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp [cpBestL, regB, regI, upd, kE, kH, dF, kqA, kqB, kqN, kqL, sw]
    have wN : d'.nreg kqN = d.nreg bN := by
      rw [hd', ← eBN]; rfl
    have wL : ∀ i, i < 4 → d'.nreg (kqL + i) = d.nreg ztctw := by
      zug
      rw [← eBL i hi, hd']
      interval_cases i <;> simp [cpBestL, regB, regI, upd, kqN, kqL, bN, bL, sw]
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := common d' fr3 by_grind (fun r hr => w0 r by_tauto)
    refine ⟨c1, c2, c3, c4, c5, c6, c7, fun _ => ⟨wN, kqLblOf_copy wN wL⟩, fun h => ?_⟩
    grind
  · zuksu
    have hB0 : d₂.nreg kqB ≠ 1 := by_omega
    refine IRS.mono (IRS.ifF by_omega (IRS.block _ hI₂
      ⟨⟨iscr_sw' by_norm_num by_norm_num, by_omega⟩, trivial⟩)) by_norm_num ?_
    zugbe
    have fr3 : ztukn := by
      rw [hd']; exact kqEfr_block _ (by simp [dstI, PreR, LblR]) (by unfold PreR; kqr)
    have wN : d'.nreg kqN = 0 := by zumzk; rfl
    have w0 : ∀ r, r ≠ kqN → d'.nreg r = d₂.nreg r := fun r hr => by
      zutu
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := common d' fr3 by_grind
      (fun r hr => w0 r (by rcases hr with rfl | rfl | rfl | rfl <;> kqr))
    refine ⟨c1, c2, c3, c4, c5, c6, c7, fun h => ?_, fun _ => ⟨?_, wN⟩⟩
    · grind
    · unfold lblOf; grind
set_option maxHeartbeats 4000000 in
/-- **The new label list.** -/
theorem fin_irs (hId : IInv W c₀ d) (hK₀ : Consts c₀) (hB : d.nreg kqB ≤ 1)
    (hA : d.nreg kqA ≤ 1) :
    IRS P W c₀ finLab d 9 (fun d' =>
      ztica ∧ d'.nmem = d.nmem ∧
      (ztfqz →
        lblOf d' kN kL = lblOf d kqN kqL ∧ d'.nreg kN = d.nreg kqN) ∧
      (¬ ztfqz → ∀ r, d'.nreg r = d.nreg r)) := by
  zulia
  have cp : IRS P W c₀ ztqed d 5 (fun d' =>
      ztica ∧ d'.nmem = d.nmem ∧
      (ztfqz →
        lblOf d' kN kL = lblOf d kqN kqL ∧ d'.nreg kN = d.nreg kqN)) := by
    refine (IRS.block cpLabL hId (by
      simp only [cpLabL, okB, okI]
      tauto)).mono le_rfl ?_
    zugbe
    have wN : d'.nreg kN = d.nreg kqN := by
      zumzk; rfl
    refine ⟨fun r hr => ?_, by zumzk, fun _ => ⟨kqLblOf_copy wN fun i hi => ?_, wN⟩⟩
    · have h0 := fun h => hr zteg
      have h1 : r ≠ kL := fun h => hr ztbh
      have h2 : r ≠ kL + 1 := fun h => hr ztbh
      have h3 : r ≠ kL + 2 := fun h => hr ztbh
      have h4 : r ≠ kL + 3 := fun h => hr ztbh
      zujit
      simp only [cpLabL, regB, regI]
      simp_all
    · zujit
      interval_cases i <;> simp [cpLabL, regB, regI, upd, kN, kL, kqN, kqL, sw]
  unfold finLab
  by_cases h1 : d.nreg K0 < d.nreg kqB
  · refine (IRS.ifT h1 cp).mono by_norm_num ztezt
    omega
  · refine (IRS.ifF (K := 5 + 2) h1 ?_).mono by_norm_num ztb
    by_cases h2 : d.nreg K0 < d.nreg kqA
    · refine (IRS.ifT h2 cp).mono le_rfl ztezt
      omega
    · refine IRS.ifF h2 (IRS.skip hId ⟨by_omega, rfl, fun h => ?_, by_omega⟩)
      rw [hK.1] at h1 h2; omega
set_option maxHeartbeats 4000000 in
/-- **The log record.** -/
theorem writeLog_irs (hId : IInv W c₀ d) (hK₀ : Consts c₀) (hA : c₀.nreg ALLOC ≤ d.nreg lB)
    (hW : d.nreg lB + 7 * d.nreg lC + 7 ≤ W) :
    IRS P W c₀ writeLog d 20 (fun d' =>
      d'.nreg lC = d.nreg lC + 1 ∧ (∀ r, r ≠ kqX → r ≠ kqY → r ≠ lC → d'.nreg r = d.nreg r) ∧
      d'.nmem (d.nreg lB + 7 * d.nreg lC) = d.nreg kE ∧
      d'.nmem (d.nreg lB + 7 * d.nreg lC + 1) = d.nreg kH ∧
      d'.nmem (d.nreg lB + 7 * d.nreg lC + 2) = d.nreg kN ∧
      (∀ i, i < 4 → d'.nmem (d.nreg lB + 7 * d.nreg lC + 3 + i) = d.nreg ztbuc) ∧
      (∀ y, (y < d.nreg lB + 7 * d.nreg lC ∨ d.nreg lB + 7 * d.nreg lC + 7 ≤ y) →
        d'.nmem y = d.nmem y)) := by
  zulia
  have hK1 := hK.2.1
  unfold writeLog
  refine IRS.seq (K₂ := 15) (IRS.block logAddrL hId (by
    simp only [lC, lB, sw, Nat.reduceAdd] at hW
    simp [logAddrL, okB, okI, regI, upd, kqX, kqY, lC, lB, sw, IScr]
    omega)) ?_
  rintro d₁ hI₁ - - hd₁
  have a1 : d₁.nreg kqX = d.nreg lB + 7 * d.nreg lC := by
    zvnes; simp [logAddrL, regB, regI, upd, kqX, kqY, lC, lB, sw]; ring
  have a2 : ∀ r, r ≠ kqX → r ≠ kqY → d₁.nreg r = d.nreg r := fun r h1 h2 => by
    zvnes; simp [logAddrL, regB, regI, upd, h1, h2]
  have m1 : ztpod := by zvnes
  zueqk
  refine IRS.seq (K₂ := 1) (storeL_irs (x := kqX) zttpq
    (by kqr) logRegs hI₁ hK₁.2.1 by_decide
    by_omega ztntb) ?_
  rintro d₂ hI₂ - - ⟨s1, s2, s3⟩
  zuheh
  have eLC : d₂.nreg lC = d.nreg lC := (s3 _ (by kqr)).trans (a2 _ (by kqr) (by kqr))
  refine (IRS.block [.addN lC lC K1] hI₂ ⟨⟨iscr_sw' by_norm_num by_norm_num,
    by rw [eLC, hK₂.2.1]; omega⟩, trivial⟩).mono le_rfl ?_
  zugbe
  have w2 : ∀ r, r ≠ lC → d'.nreg r = d₂.nreg r := fun r hr => by
    zutu
  have wm : d'.nmem = d₂.nmem := by zumzk
  have kr : ∀ r, r ≠ kqX → r ≠ kqY → d₂.nreg r = d.nreg r := by_simp_all
  have st : ∀ i (h : i < logRegs.length),
      d'.nmem (d.nreg lB + 7 * d.nreg lC + i) = d.nreg (logRegs[i]) := by
    intro i h
    have h7 : i < 7 := by_tauto
    rw [wm, ← a1, s1 i h, a2]
    · interval_cases i <;> simp [logRegs, kE, kH, kN, kL, kqX, sw]
    · interval_cases i <;> simp [logRegs, kE, kH, kN, kL, kqY, sw]
  refine ⟨by zumzk; simp [regB, regI, hK₂.2.1, eLC], by_grind,
    by simpa [logRegs] using st 0 by_decide, by simpa [logRegs] using st 1 by_decide,
    by simpa [logRegs] using st 2 by_decide, fun i hi => ?_,
    fun y hy => by rw [wm, s2 y ztntb, m1]⟩
  have := st ztssx (by zupcg; omega)
  zujlw
  zubk
  interval_cases i <;> zupcg
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def keyMain : Stmt := .seq kqPre (.seq ztqwn (.seq finLab writeLog))

/-- **The next key.** -/
def keyProg : Stmt := .seq kqSel (.ifLtN K0 kqF keyMain (block [.constN dF 1]))
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-! ## Register sets -/
variable {r : ℕ}
theorem selR_KR (h : SelR r) : KR r := by
  zvnbu at h
  zusc
theorem preR_KR (h : PreR r) : KR r := by
  simp only [PreR, LblR, kE, kH, dF, kqB, kqA, kqO, kqN, kqL, sw] at h
  zusc
theorem skR_KR (h : SkR r) : KR r := by
  zvnwz at h
  zusc
theorem lbl_KR (h : LblR kN kL r) : KR r := by
  zufaw
  tauto
theorem lbl_not (h : LblR kN kL r) :
    ¬ SelR r ∧ ¬ PreR r ∧ ¬ SkR r ∧ r ≠ kqX ∧ r ≠ kqY ∧ r ≠ lC ∧ 240000 ≤ r ∧ r < 250000 := by
  zufaw
  simp only [SelR, OffR, PreR, SkR, KStR, LblR, kqF, kqE, kqH, kqO, kqSE, kqSH, kqX, kqV, kqY,
    kE, kH, dF, kqB, kqA, kqN, kqL, sP, lC, sw]
  omega

/-! ## The selection -/
theorem sel_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hH : CandHyp P J c) (hroom : c.nreg ALLOC + 22100 ≤ W) :
    IRS P W c₀ kqSel c 22061 (fun d => SelInv P J c d True True) := by
  unfold kqSel
  refine IRS.seq (K₂ := 22053) (selB_irs (J := J) hI E.hK by_omega) ?_
  rintro d hId - hA hS
  refine IRS.seq (K₂ := 11024) (selS_irs E.hK hH (E.ctxW' hId) (E.gw' hId)
    ztvxt hId hS by_omega) ?_
  rintro d' hId' - hA' hS'
  exact selW_irs E.hK hH (E.ctxW' hId') (E.gw' hId') ztvxt hId' hS' by_omega

/-! ## The next key -/
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 100000 in
/-- **The next key.** -/
theorem key_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hb : c.nreg bF = 1 → PosW P J ztvo ztvp)
    (hw : c.nreg wX = 0 → PosW P J ztmhd ztmhe)
    (hst : ∀ i, i < c.nreg sC → PosW P J ztbjv ztbjw)
    (hsort : ∀ i i', i ≤ i' → i' < c.nreg sC →
      offK P J ztbjv ztbjw ≤ offK P J ztkfo ztkfp)
    (htwo : ∀ i, i + 2 < c.nreg sC →
      offK P J ztbjv ztbjw < offK P J ztxyb ztxyc)
    (hsPC : c.nreg sP ≤ c.nreg sC) (hkN : c.nreg kN ≤ 4) (hbN : c.nreg bN ≤ 4)
    (hsB : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC) (haB : c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC)
    (hlB : c₀.nreg ALLOC ≤ c.nreg lB) (hlC : c.nreg lB + 7 * ztllq ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + 56000 ≤ W) :
    IRS P W c₀ keyProg c 56000 ztlew := by
  have hH : CandHyp P J c := ⟨hb, hw, hst, hsB⟩
  unfold keyProg
  refine (IRS.seq (K₂ := 33461) (sel_irs E hI hH by_omega) ?_).mono by_norm_num
    ztb
  rintro d₁ hI₁ hA₁ hA₁' ⟨frS, hF, hFiff, hFmin⟩
  zubke
  have kS : ∀ r, ¬ SelR r → 240000 ≤ r ∧ r < 250000 → d₁.nreg r = c.nreg r :=
    fun r h1 h2 => frS.kkeep h1 h2
  have nS : ∀ r, (r = bF ∨ r = bE ∨ r = bH ∨ r = bN ∨ r = sP ∨ r = sC ∨ r = sB ∨ r = aB ∨
      r = lB ∨ r = lC ∨ r = kN ∨ r = dF) → ¬ SelR r ∧ 240000 ≤ r ∧ r < 250000 := by
    zuz
    simp only [bF, bE, bH, bN, sP, sC, sB, aB, lB, lC, kN, dF, sw] at hr
    zvnbu
    omega
  have e1 :=
    fun r hr => kS r by_grind (nS r hr).2
  by_cases hc : d₁.nreg K0 < d₁.nreg kqF
  · -- a candidate exists
    have hF1 : d₁.nreg kqF = 1 := by_omega
    have hcand := hFiff.1 hF1
    obtain ⟨hCK, hm1, hm2, hm3⟩ := hFmin hF1
    have hpk := candK_posW hH hCK
    refine IRS.mono (K := 33459 + 2) (IRS.ifT hc ?_) by_norm_num ztb
    unfold keyMain
    refine IRS.seq (K₂ := 22429) (pre_irs E hI₁ hpk
      by_grind
      by_grind by_omega) ?_
    rintro d₀ hI₀ hA₀ hA₀' ⟨frP, eKE, eKH, eDF, eKA, hB1, hBiff, hBlab, hBlab0⟩
    have nP : ∀ r, (r = bF ∨ r = bE ∨ r = bH ∨ r = bN ∨ r = sP ∨ r = sC ∨ r = sB ∨ r = aB ∨
        r = lB ∨ r = lC ∨ r = kN) → ¬ PreR r := by
      zuz
      simp only [bF, bE, bH, bN, sP, sC, sB, aB, lB, lC, kN, sw] at hr
      simp only [PreR, LblR, kE, kH, dF, kqB, kqA, kqO, kqN, kqL, sw]
      omega
    have e0 : ∀ r, (r = bF ∨ r = bE ∨ r = bH ∨ r = bN ∨ r = sP ∨ r = sC ∨ r = sB ∨ r = aB ∨
        r = lB ∨ r = lC ∨ r = kN) → d₀.nreg r = c.nreg r := fun r hr =>
      (frP.kkeep by_grind (nS r by_grind).2).trans
        by_grind
    have hN0 : d₀.nreg kqN ≤ 4 := by
      by_cases h : d₀.nreg kqB = 1
      · grind
      omega
    have hS : SkCtx P J c d₀ :=
      { hsP := e0 sP by_simp, hsC := e0 sC by_simp, hsB := e0 sB by_simp,
        haB := e0 aB by_simp, hA := frS.2.1.trans frP.2.1,
        hm := fun x hx => (frP.2.2 x by_omega).trans (frS.2.2 x hx),
        hpk := by_grind,
        hmin := fun h => by_grind,
        hps := hst, hsort := hsort, htwo := htwo, hsBA := hsB, haBA := haB }
    refine IRS.seq (K₂ := 29) (skip2_irs E hS hI₀ (skInv_zero hS hsPC hN0 eKA)
      by_omega) ?_
    rintro d₅ hI₅ hA₅ hA₅' ⟨j, ⟨frK, hsP5, hjC, hj2, hoff, hN5, hlb5, hA5, hAiff5⟩, hnext⟩
    have nK : ∀ r, (r = kE ∨ r = kH ∨ r = dF ∨ r = kqB ∨ r = lB ∨ r = lC ∨ r = kN) →
        ¬ SkR r ∧ 240000 ≤ r ∧ r < 250000 := by
      zuz
      simp only [kE, kH, dF, kqB, lB, lC, kN, sw] at hr
      zvnwz
      omega
    have e5 := fun r hr => frK.kkeep (nK r hr).1 (nK r hr).2
    have hB5 : d₅.nreg kqB ≤ 1 := by rw [e5 kqB by_simp]; omega
    refine IRS.seq (K₂ := 20) (fin_irs hI₅ E.hK hB5 hA5) ?_
    rintro d₆ hI₆ hA₆ hA₆' ⟨f1, f2, f3, f4⟩
    have e6 := f1
    have eLB6 : d₆.nreg lB = c.nreg lB := by
      rw [e6 lB (by simp only [LblR, lB, kN, kL, sw]; omega), e5 lB by_simp, e0 lB by_simp]
    have eLC6 : d₆.nreg lC = c.nreg lC := by
      rw [e6 lC (by simp only [LblR, lC, kN, kL, sw]; omega), e5 lC by_simp, e0 lC by_simp]
    have hc'A : c.nreg ALLOC ≤ d₆.nreg ALLOC := by
      omega
    refine (writeLog_irs hI₆ E.hK by_omega by_omega).mono
      le_rfl ?_
    rintro c' ⟨w1, w2, w3, w4, w5, w6, w7⟩
    rw [eLB6, eLC6] at w3 w4 w5 w6 w7
    -- registers of `c'`
    have g6 :=
      fun r h1 h2 h3 h4 => (w2 r h1 h2 h3).trans (e6 r h4)
    have nW : ∀ r, (r = kE ∨ r = kH ∨ r = dF ∨ r = kqB ∨ r = sP) →
        r ≠ kqX ∧ r ≠ kqY ∧ r ≠ lC ∧ ¬ LblR kN kL r := by
      zuz
      simp only [kE, kH, dF, kqB, sP, sw] at hr
      simp only [LblR, kqX, kqY, lC, kN, kL, sw]
      omega
    have g :=
      fun r hr => g6 r (nW r hr).1 by_grind by_grind (nW r hr).2.2.2
    have cKE := (g kE by_simp).trans (e5 kE by_simp)
    have cKH := (g kH by_simp).trans (e5 kH by_simp)
    have cDF := ((g dF by_simp).trans (e5 dF by_simp)).trans eDF
    have cSP := (g sP by_simp).trans hsP5
    have cKB := e5 kqB by_simp
    have ok : offK P J ztccp ztdco = offK P J (d₁.nreg kqE) (d₁.nreg kqH) := by
      zuntx
    have lblC : ∀ (d d' : Config) (X : ℕ → Prop), EFr X d d' → (∀ r, LblR bN bL r → ¬ X r) →
        lblOf d' bN bL = lblOf d bN bL := fun d d' X h hX => kqLblOf_eq fun q hq =>
      h.kkeep (hX q hq) (by simp only [LblR, bN, bL, sw] at hq ⊢; omega)
    -- the label condition
    have hCb : (d₅.nreg kqB = 1) ↔ (c.nreg bF = 1 ∧
        offK P J ztvo ztvp = offK P J ztccp ztdco) := by
      rw [cKB, hBiff, ok, e1 bF by_simp, e1 bE by_simp, e1 bH by_simp]
    have hCa : (d₅.nreg kqA = 1) ↔ ∃ i, c.nreg sP ≤ i ∧ i < c'.nreg sP ∧
        c.nmem ztduc = 1 := by rw [cSP]; omega
    have lab0 : lblOf d₀ kqN kqL = if c.nreg bF = 1 ∧
        offK P J ztvo ztvp = offK P J ztccp ztdco
        then lblOf c bN bL else [] := by
      zus
      · rw [(hBlab (cKB ▸ hCb.2 h)).2, lblC c d₁ SelR frS (fun r hr => by
          simp only [LblR, bN, bL, sw] at hr
          zvnbu; omega)]
      · exact (hBlab0 (fun h' => h (hCb.1 by_omega))).1
    have nKR : ∀ r, ¬ KR r → r ≠ kqX ∧ r ≠ kqY ∧ r ≠ lC ∧ ¬ LblR kN kL r ∧ ¬ SkR r ∧
        ¬ PreR r ∧ ¬ SelR r := by
      zuz
      refine ⟨fun h => hr ?_, fun h => hr ?_, fun h => hr ?_, fun h => hr (lbl_KR h),
        fun h => hr (skR_KR h), fun h => hr (preR_KR h), fun h => hr ztwdl⟩ <;>
        subst h <;> simp only [KR, kqX, kqY, lC, kE, kH, kN, kL, sP, dF, sw] <;> norm_num
    refine ⟨fun r hb hr hra => ?_, ?_, fun h => by
      rcases hcand with h1 | ⟨-, h1⟩ | ⟨-, h1⟩
      · omega
      · omega
      omega, fun _ => ?_⟩
    · obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := nKR r hr
      rw [g6 r n1 n2 n3 n4, frK.1 r hb n5 hra, frP.1 r hb n6 hra, frS.1 r hb n7 hra]
    · rw [w2 ALLOC (by kqr) (by kqr) (by kqr)]; omega
    -- the candidate case
    have hlbK : ∀ r, LblR kN kL r → d₅.nreg r = c.nreg r := fun r hr => by
      obtain ⟨n1, n2, n3, -, -, -, n7, n8⟩ := lbl_not hr
      rw [frK.kkeep n3 by_omega, frP.kkeep n2 by_omega, frS.kkeep n1 by_omega]
    have hlbC := fun r hr => by
      obtain ⟨-, -, -, n4, n5, n6, -⟩ := lbl_not hr
      exact w2 r n4 n5 n6
    have hmemC : ∀ x, x < c.nreg ALLOC → d₆.nmem x = c.nmem x := fun x hx => by
      rw [f2, frK.2.2 x by_omega,
        frP.2.2 x by_omega, frS.2.2 x hx]
    have hkN' : c'.nreg kN ≤ 4 := by
      rw [hlbC kN ztp]
      by_cases hC : d₅.nreg kqB = 1 ∨ d₅.nreg kqA = 1
      · rw [(f3 hC).2]; omega
      · rw [f4 hC kN, hlbK kN ztp]; omega
    refine ⟨cDF, by zuntx; tauto, fun h => by zuogk; exact hm1 h,
      fun h => by zuogk; exact hm2 trivial h, fun h => by zuogk; exact hm3 trivial h,
      by omega, by_omega, fun i h1 h2 => ?_, fun h => ?_, hkN',
      fun hC => ?_, fun hC => ?_, by_omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cSP] at h2; rw [hoff i h1 h2, cKE, cKH]
    · rw [g sP by_simp] at h ⊢; rw [cKE, cKH]; exact hnext h
    · have hC' : d₅.nreg kqB = 1 ∨ d₅.nreg kqA = 1 := by
        rcases hC with h | h
        · exact Or.inl (hCb.2 h)
        · exact Or.inr (hCa.2 h)
      rw [kqLblOf_eq hlbC, (f3 hC').1, hlb5, lab0, cSP, Nat.add_sub_cancel_left]
    · have hC' : ¬ (d₅.nreg kqB = 1 ∨ d₅.nreg kqA = 1) := by
        zunp
        · exact hC (Or.inl (hCb.1 h))
        · exact hC (Or.inr (hCa.1 h))
      zujx
      · rw [kqLblOf_eq hlbC, kqLblOf_eq (fun r _ => f4 hC' r), kqLblOf_eq hlbK]
      · rw [hlbC kN ztp, f4 hC' kN, hlbK kN ztp]
    · rw [w3, w2 kE (by kqr) (by kqr) (by kqr)]
    · rw [w4, w2 kH (by kqr) (by kqr) (by kqr)]
    · rw [w5, w2 kN (by kqr) (by kqr) (by kqr)]
    · zug
      rw [w6 i hi, w2 _ (by unfold kL kqX sw; omega) (by unfold kL kqY sw; omega)
        ztnvu]
    · zueth
      rw [w7 x hx', hmemC x hx]
  · -- no candidate
    have hF0 : d₁.nreg kqF ≠ 1 := by rw [hK₁.1] at hc; omega
    refine IRS.mono (IRS.ifF hc (IRS.block [.constN dF 1] hI₁
      ⟨⟨iscr_sw' by_norm_num by_norm_num, by_omega⟩, trivial⟩)) by_norm_num ?_
    zujgc
    have v1 : ztunh := by zumyg; rfl
    have v2 : ∀ r, r ≠ dF → c'.nreg r = d₁.nreg r := fun r hr => by
      zumyg; simp [regB, regI, upd, hr]
    have vm : c'.nmem = d₁.nmem := by zumyg
    refine ⟨fun r hb hr hra => ?_, by rw [v2 ALLOC (by kqr)]; omega,
      fun _ => ⟨v1, by rw [v2 lC (by kqr)]; grind,
        fun x hx => by rw [vm]; exact frS.2.2 x hx⟩, by_grind⟩
    rw [v2 r (fun h => hr (by subst h; simp [KR]))]
    exact frS.1 r hb (fun h => hr ztwdl) hra

/-- **Task K: the next key.** -/
theorem keyTask : KeyTask :=
  ⟨keyProg, 56000, fun _ _ _ _ _ _ _ _ _ _ _ _ E hI _ hb hw hst hsort htwo hsPC hkN hbN hsB haB hlB hlC
    hroom => key_irs E hI hb hw hst hsort htwo hsPC hkN hbN hsB haB hlB hlC hroom⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def uK : ℕ := sw 2460
def uR : ℕ := sw 2461
def uA : ℕ := sw 2462
def uI : ℕ := sw 2463
def uLen : ℕ := sw 2464
def uOff : ℕ := sw 2465
def uR7 : ℕ := sw 2466
def uT : ℕ := sw 2467
def uY : ℕ := sw 2468

/-! ## The abstract per-origin statement -/

/-- The contract of the per-origin statement (as in `OrgsTask`). -/
def OdOK (P : Polygon) (W : ℕ) (c₀ : Config) (N₂ : NF) (od : Stmt) (Kod : ℕ)
    (Inv : Set ℕ → Config → Prop) : Prop :=
  ∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c → c.nreg oK < N₂.nChords →
    c.nreg oS ≤ 1 → c.nreg ALLOC + Kod ≤ W →
    IRS P W c₀ od c Kod (fun c' => Inv ztxxm c' ∧
      ztwpx ∧
      ztvw)

/-- The stability of the invariant under changes of the loop registers (as in `OrgsTask`). -/
def InvStab (Inv : Set ℕ → Config → Prop) : Prop :=
  ∀ (O : Set ℕ) (c c' : Config), Inv O c → ztedk →
    c'.nmem = c.nmem → c'.rmem = c.rmem → c'.rreg = c.rreg → c'.output = c.output → Inv O c'

/-- The auxiliary array of `c` is unchanged in `c'`. -/
def AuxKeep (c c' : Config) : Prop :=
  ∀ x, c.nreg aB ≤ x → x < c.nreg aB + 5 * c.nreg sC → c'.nmem x = c.nmem x

/-- The two endpoint queries of chord `k`. -/
def pairS (k : ℕ) : Set ℕ := {j | ∃ s, s ≤ 1 ∧ j = 2 * k + s}
theorem er_not_lr {r : ℕ} (h : ER r) : ¬ LR r := by
  unfold ER at h; unfold LR
  unfold kN kL gN gR sP sC aB oK oS sw at *
  omega

/-- A block writing only loop registers keeps the invariant. -/
theorem inv_blk {Inv : Set ℕ → Config → Prop} (hst : InvStab Inv) {l : List Instr}
    (hl : ∀ i ∈ l, LR ztcpw) {O : Set ℕ} {c : Config} (h : Inv O c) :
    Inv O { c with nreg := regB c.nmem l c.nreg } :=
  hst O c _ h (fun _r hr => regB_other _ _ _ by_grind) rfl rfl rfl rfl

/-- A block writing only loop registers keeps the read registers. -/
theorem er_blk {l : List Instr} (hl : ∀ i ∈ l, LR ztcpw) {m f : ℕ → ℕ} {r : ℕ} (hr : ER r) :
    regB m l f r = f r :=
  regB_other _ _ _ (fun i hi he => er_not_lr hr by_grind)
theorem auxKeep_trans {c c₁ c₂ : Config} (h₁ : AuxKeep c c₁) (hr : ∀ r, ER r → c₁.nreg r = c.nreg r)
    (h₂ : AuxKeep c₁ c₂) : AuxKeep c c₂ := fun x hx1 hx2 => by
  have ea : c₁.nreg aB = c.nreg aB := hr _ by_tauto
  have es : c₁.nreg sC = c.nreg sC := hr _ by_tauto
  rw [h₂ x by_omega by_omega, h₁ x hx1 hx2]

/-! ## Both ends of one chord -/
def uPre0 : List Instr := [.copyN oK uK, .copyN oS K0]
def uPre1 : List Instr := [.copyN oK uK, .copyN oS K1]

/-- **Both ends of the chord `uK`.** -/
def odPair (od : Stmt) : Stmt := .seq (block uPre0) (.seq od (.seq (block uPre1) od))
theorem uPre0_lr : ∀ i ∈ uPre0, LR ztcpw := by
  simp [uPre0, dstI, LR]
theorem uPre1_lr : ∀ i ∈ uPre1, LR ztcpw := by
  simp [uPre1, dstI, LR]
theorem pair_union (O : Set ℕ) (k : ℕ) :
    insert ztekz ztlqh = O ∪ pairS k := by
  zumag
  simp only [mem_insert_iff, mem_union, pairS, mem_ofPred_eq]
  constructor
  · zuciz
    · simp_all
    · simp_all
    simp_all
  grind
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- **Both ends of one chord.** -/
theorem odPair_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    (hI : IInv W c₀ c) {O : Set ℕ} (hinv : Inv O c) {k : ℕ} (hk : c.nreg uK = k)
    (hkn : k < N₂.nChords) (hroom : c.nreg ALLOC + ztjez ≤ W) :
    IRS P W c₀ ztquh c ztjez (fun c' => Inv (O ∪ pairS k) c' ∧
      (∀ r, ER r ∨ ztbcj → c'.nreg r = c.nreg r) ∧ AuxKeep c c') := by
  zuiw
  zudpx
  zubof
  refine IRS.mono (K := 2 + (Kod + (2 + Kod))) (IRS.seq (IRS.block uPre0 hI ?_) ?_) by_omega
    ztb
  · simp [uPre0, okB, okI, IScr, oK, oS, sw]
  zuknz
  have r1 : c₁.nreg = regB c.nmem uPre0 c.nreg := by zvmwl
  zufp
  have v1k : ztuqu := by
    zugfe
  have v1s : c₁.nreg oS = 0 := by
    zugfe
  have o1 : zthpp := fun r h1 h2 => by
    zumov
    exact regB_other _ _ _ (fun i hi he => by
      simp only [uPre0, List.mem_cons, List.not_mem_nil, or_false] at hi
      zufzx
      · tauto
      tauto)
  have inv1 : ztlaa := by zvmwl; exact inv_blk hst uPre0_lr hinv
  have nAk : ALLOC ≠ oK := by_decide
  have nAs : ALLOC ≠ oS := by_decide
  have eA1 : ztdc := by_simp_all
  refine IRS.seq (hod O _ hI₁ inv1 by_omega by_omega
    by_omega) ?_
  rw [v1k, v1s]
  rintro c₂ hI₂ hA2 hA2' ⟨inv2, keep2, aux2⟩
  have hk2 : c₂.nreg uK = k := by
    rw [keep2 _ (Or.inl ⟨by unfold LR uK; decide, by_decide,
      by decide⟩)]
    rw [o1 _ by_decide by_decide, hk]
  zuhef
  refine IRS.seq (IRS.block uPre1 hI₂ ?_) ?_
  · simp [uPre1, okB, okI, IScr, oK, oS, sw]
  zukoa
  have r3 : c₃.nreg = regB c₂.nmem uPre1 c₂.nreg := by zvnar
  zucwz
  have v3k : ztusq := by
    zukyl
  have v3s : c₃.nreg oS = 1 := by
    have := hK2.2.1
    zukyl
  have o3 : ∀ r, r ≠ oK → r ≠ oS → c₃.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [r3]
    exact regB_other _ _ _ (fun i hi he => by
      simp only [uPre1, List.mem_cons, List.not_mem_nil, or_false] at hi
      zufzx
      · tauto
      tauto)
  have inv3 : Inv ztlqh c₃ := by zvnar; exact inv_blk hst uPre1_lr inv2
  zujxo
  refine (hod _ _ hI₃ inv3 by_omega (by rw [v3s])
    by_omega).mono le_rfl ?_
  rintro c' ⟨inv', keep', aux'⟩
  rw [v3k, v3s] at inv'
  have ER_ne : ∀ r, ER r → r ≠ oK ∧ r ≠ oS := fun r h =>
    ⟨fun e => er_not_lr h (e ▸ Or.inl rfl), fun e => er_not_lr h (e ▸ Or.inr ztp)⟩
  have keepAll : ∀ r, ER r ∨ ztbcj → c'.nreg r = c.nreg r := by_grind
  refine ⟨by rw [← pair_union]; omega, keepAll, ?_⟩
  have e3 : ∀ r, ER r → c₃.nreg r = c.nreg r := fun r h => by
    grind
  have e1 : ∀ r, ER r → c₁.nreg r = c.nreg r := by_grind
  have hEa : ER aB := by unfold ER; simp
  have hEs : ER sC := by unfold ER; simp
  zuetl
  grind

/-! ## The chords of one region -/

/-- The head of a region: its chord count `uLen`, list offset `uOff`, list area `uR7`; `uT = 0`. -/
def regHead : List Instr :=
  [.addN uA ztbz K5, .loadN uA uA, .addN uA uA uR, .addN uA uA uR, .addN uA uA uR,
    .addN uA uA uR, .addN uA uA uR, .addN uY uA K2, .loadN uLen uY, .addN uY uA K3,
    .loadN uOff uY, .addN uY ztbz K6, .addN uY uY K1, .loadN uR7 uY, .constN uT 0]

/-- Read the chord at place `uT` of the list. -/
def regBody0 : List Instr := [.addN uA uR7 uOff, .addN uA uA uT, .loadN uK uA]
def uInc : List Instr := [.addN uT uT K1]

/-- One chord of the region. -/
def regBody (od : Stmt) : Stmt := .seq (block regBody0) (.seq ztquh (block uInc))

/-- **Both ends of every chord of the region `uR`** of `N₂`. -/
def regDo (od : Stmt) : Stmt := .seq (block regHead) (.whileLtN uT uLen (regBody od))

/-- The cost of a region. -/
def regK (Kod D : ℕ) : ℕ := ztjey * D + 17
theorem regHead_lr : ∀ i ∈ regHead, LR ztcpw := by
  simp [regHead, dstI, LR, uA, uY, uLen, uOff, uR7, uT, oK, oS, sw]
theorem regBody0_lr : ∀ i ∈ regBody0, LR ztcpw := by
  simp [regBody0, dstI, LR, uA, uK, oK, oS, sw]
theorem uInc_lr : ∀ i ∈ uInc, LR ztcpw := by
  simp [uInc, dstI, LR, uT, oK, oS, sw]
variable (m f : ℕ → ℕ)
theorem regHead_val (k5 : f K5 = 5) (k2 : f K2 = 2) (k3 : f K3 = 3)
    (k6 : f K6 = 6) (k1 : f K1 = 1) :
    regB m regHead f uLen = m (m ztyes + 5 * f uR + 2) ∧
    regB m regHead f uOff = m (m ztyes + 5 * f uR + 3) ∧
    regB m regHead f uR7 = m (f ztbz + 7) ∧ regB m regHead f uT = 0 := by
  simp only [K5, K2, K3, K6, K1, sw] at k5 k2 k3 k6 k1
  refine ztfh <;>
    simp [regHead, regB, regI, upd, uA, uY, uLen, uOff, uR7, uT, uR, K5, K2, K3, K6, K1, sw,
      k5, k2, k3, k6, k1] <;> ring_nf
theorem regHead_ok (k5 : f K5 = 5) (k2 : f K2 = 2) (k3 : f K3 = 3)
    (k6 : f K6 = 6) (k1 : f K1 = 1) (hb1 : f ztbz + 7 ≤ W)
    (hb2 : m ztyes + 5 * f uR + 3 ≤ W) : okB W m regHead f := by
  simp only [K5, K2, K3, K6, K1, sw, uR, Nat.reduceAdd] at k5 k2 k3 k6 k1 hb1 hb2
  simp [regHead, okB, okI, regI, upd, uA, uY, uLen, uOff, uR7, uT, uR, K5, K2, K3, K6, K1, sw,
    k5, k2, k3, k6, k1, IScr]
  omega
theorem regBody0_val :
    regB m regBody0 f uK = m (f uR7 + f uOff + f uT) := by
  rfl
theorem regBody0_ok (hb : f uR7 + f uOff + f uT ≤ W) : okB W m regBody0 f := by
  simp only [uR7, uOff, uT, sw, Nat.reduceAdd] at hb
  simp [regBody0, okB, okI, regI, upd, uA, uK, uR7, uOff, uT, sw, IScr]
  omega

/-- The chords of a region as positions of its list. -/
theorem regO_eq (N : NF) (r : ℕ) : regO N r =
    {j | ∃ t, t < (N.region r).chords.length ∧ j ∈ pairS ((N.region r).chords.getD t 0)} := by
  zumag
  simp only [regO, pairS, mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, s, hs, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hk
    exact ⟨t, ht, s, hs, by_simp_all⟩
  · rintro ⟨t, ht, s, hs, rfl⟩
    exact ⟨_, by_simp_all, s, hs, rfl⟩
theorem pre_succ (l : List ℕ) (t : ℕ) :
    {j | ∃ t', t' < t + 1 ∧ j ∈ pairS zttrp} =
      {j | ∃ t', t' < t ∧ j ∈ pairS zttrp} ∪ pairS ztocn := by
  zumag
  grind
set_option maxHeartbeats 4000000 in
/-- **Both ends of every chord of a region.** -/
theorem regDo_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    (hI : IInv W c₀ c) {O : Set ℕ} (hinv : Inv O c) {r : ℕ} (hr : c.nreg uR = r)
    (hrn : r < N₂.nRegions) (hroom : c.nreg ALLOC + regK Kod zto ≤ W) :
    IRS P W c₀ ztwco c (regK Kod zto) (fun c' => Inv (O ∪ regO N₂ r) c' ∧
      ztkie ∧ AuxKeep c c') := by
  zuiw
  zuch
  zujmm
  set B := c₀.nreg ztbz with hBd
  have hB : c.nreg _ = B := hI.hin _ by_trivial
  have hNW := E.hNW₂
  zuiwq
  obtain ⟨b1, -, -, b4, -, b6⟩ := Restore.nf_bounds hNW
  obtain ⟨-, -, -, reg, hRC, -, -, hRO, -⟩ := E.hNF₂
  have hlenD := Gran.chords_le E.hNF₂ hRC hRO E.hdeg₂ hrn
  set R5 := c₀.nmem zter with hR5
  set R7 := c₀.nmem ztlw with hR7
  set off := c₀.nmem (R5 + 5 * r + 3) with hoff
  set len := (N₂.region r).chords.length with hlen
  have hreg := hNA.2.2.2.2.2.2.2.1 r hrn
  have hlen0 := hreg.2.1
  have hch : ∀ t, t < len → c₀.nmem (R7 + off + t) = (N₂.region r).chords.getD t 0 :=
    by grind
  have hb4 := b4 r hrn
  have hb6 : ∀ t, t < len → R7 + off + t < c₀.nreg ALLOC := by_grind
  zubnp
  zuki
  have hm5 : c.nmem _ = R5 := hI.hm _ by_omega
  -- the head
  have hok : okB W c.nmem regHead c.nreg := regHead_ok _ _ k5 k2 k3 k6 k1
    by_omega by_grind
  obtain ⟨vLen, vOff, vR7, vT⟩ := regHead_val c.nmem c.nreg k5 k2 k3 k6 k1
  rw [hB, hm5, hr, hI.hm _ by_omega] at vLen vOff
  rw [hB, hI.hm _ by_omega] at vR7
  rw [hlen0] at vLen
  refine IRS.mono (K := regHead.length + (ztekw * len + 2))
    (IRS.seq (IRS.block regHead hI hok) ?_) ?_ ztb
  rotate_left
  · zuiun
    simp only [regHead, List.length_cons, List.length_nil, regK]; omega
  zuknz
  have r1 : c₁.nreg = regB c.nmem regHead c.nreg := by zvmwl
  zufp
  have inv1 : ztlaa := by zvmwl; exact inv_blk hst regHead_lr hinv
  have e1 : ztfle := fun q h => by zvnal; exact er_blk regHead_lr h
  have eA1 : ztdc := by
    zvnal; rfl
  -- the loop
  let S : ℕ → Set ℕ := fun t => {j | ∃ t', t' < t ∧ j ∈ pairS ((N₂.region r).chords.getD t' 0)}
  let I : Config → Prop := fun c' => Inv (O ∪ S (c'.nreg uT)) c' ∧ c'.nreg uT ≤ len ∧
    c'.nreg uLen = len ∧ c'.nreg uOff = off ∧ c'.nreg uR7 = R7 ∧
    ztkie ∧ AuxKeep c c'
  have S0 : S 0 = ∅ := by
    grind
  have hI1 : ztkzz := by
    refine ⟨?_, ?_, ?_, ?_, ?_, e1, fun x _ _ => by zvnmf⟩
    · rw [r1, vT, S0, Set.union_empty]; omega
    · rw [r1, vT]; omega
    · rw [r1, vLen]
    · rw [r1, vOff]
    · rw [r1, vR7]
  have hroomL : c₁.nreg ALLOC + ztekw * (len - c₁.nreg uT) ≤ W := by
    zuiun
    rw [eA1, r1, vT, Nat.sub_zero]; unfold regK at hroom; omega
  have hw := IRS.while (P := P) (a := uT) (b := uLen) (body := regBody od) I
    (fun c' => len - c'.nreg uT) _
    by_grind ?_ hI₁ hI1 hroomL
  · refine (hw.mono by_simp ?_)
    rintro c' ⟨⟨hinv', hle, hlen', -, -, he', hax'⟩, hnlt⟩
    rw [hlen'] at hnlt
    have ht : c'.nreg uT = len := by_omega
    refine ⟨?_, he', hax'⟩
    rw [regO_eq]
    zvnup at hinv'
    omega
  -- the body
  intro c₂ hI₂ hc2 hlt hroom2
  obtain ⟨inv2, hle2, hlen2, hoff2, hR72, he2, hax2⟩ := hc2
  rw [hlen2] at hlt
  set t := c₂.nreg uT with ht
  have hbt := hb6 t hlt
  have hok0 : okB W c₂.nmem regBody0 c₂.nreg := regBody0_ok _ _ (by
    omega)
  unfold regBody
  refine IRS.mono (K := regBody0.length + (2 * Kod + 4 + uInc.length)) ?_
    (by simp [regBody0, uInc]; omega) ztb
  refine IRS.seq
    (IRS.block regBody0 hI₂ hok0) ?_
  zukoa
  have r3 : c₃.nreg = regB c₂.nmem regBody0 c₂.nreg := by zvnar
  zucwz
  have inv3 : Inv (O ∪ S t) c₃ := by zvnar; exact inv_blk hst regBody0_lr inv2
  have o3 : ∀ q, ¬ LR q → c₃.nreg q = c₂.nreg q := fun q hq => by
    rw [r3]; exact regB_other _ _ _ (fun i hi he => hq (he ▸ regBody0_lr i hi))
  have keepL3 : ∀ q, q ≠ uA → q ≠ uK → c₃.nreg q = c₂.nreg q := fun q h1 h2 => by
    rw [r3]; exact regB_other _ _ _ (fun i hi he => by
      simp only [regBody0, List.mem_cons, List.not_mem_nil, or_false] at hi
      zuiec
      · exact h1 he.symm
      · exact h1 he.symm
      · exact h2 he.symm)
  have vK : c₃.nreg uK = (N₂.region r).chords.getD t 0 := by
    rw [r3, regBody0_val, hR72, hoff2, hI₂.hm _ hbt, hch t hlt]
  have hkn : (N₂.region r).chords.getD t 0 < N₂.nChords := by
    have hmem : (N₂.region r).chords.getD t 0 ∈ (N₂.region r).chords := by
      rw [List.getD_eq_getElem _ _ hlt]; simp
    exact (((hRO r hrn).1 _).1 hmem).1
  zukil
  zujxo
  have hl0 : regBody0.length = 3 := rfl
  have hl1 : uInc.length = 1 := rfl
  rw [hl0] at hA3'
  refine IRS.seq
    (odPair_irs E hod hst hI₃ inv3 vK hkn by_omega) ?_
  rintro c₄ hI₄ hA4 hA4' ⟨inv4, keep4, aux4⟩
  have lr4 : ∀ q, q = uT ∨ q = uLen ∨ q = uOff ∨ q = uR7 → c₄.nreg q = c₂.nreg q := by
    zuco
    have hq' : LR q ∧ q ≠ oK ∧ q ≠ oS := by
      rcases hq with rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;>
        simp [LR, uT, uLen, uOff, uR7, oK, oS, sw]
    rw [keep4 q (Or.inr hq'), keepL3 q (by rcases hq with rfl | rfl | rfl | rfl <;>
      simp [uT, uLen, uOff, uR7, uA, sw]) (by rcases hq with rfl | rfl | rfl | rfl <;>
      simp [uT, uLen, uOff, uR7, uK, sw])]
  have k14 := (E.hK.fix hI₄).2.1
  have hT4 := lr4 _ ztp
  refine (IRS.block uInc hI₄ ?_).mono le_rfl ?_
  · simp only [uInc, okB, okI]
    exact ⟨⟨iscr_sw by_decide by_decide,
      by omega⟩, trivial⟩
  zujgc
  have r' : c'.nreg = regB c₄.nmem uInc c₄.nreg := by zumyg
  have vT' : c'.nreg uT = t + 1 := by
    zupcl; simp [uInc, regB, regI, upd_same]; omega
  have o' : ∀ q, q ≠ uT → c'.nreg q = c₄.nreg q := fun q hq => by
    zupcl; simp only [uInc, regB, regI]; exact upd_other _ _ _ hq
  have e3 : ∀ q, ER q → c₃.nreg q = c.nreg q := fun q h => (o3 q (er_not_lr h)).trans by_grind
  have eER : ∀ q, ER q → c'.nreg q = c.nreg q := fun q h => by
    rw [o' q (fun e => er_not_lr h (e ▸ Or.inr ztxcg)),
      keep4 q zteg, e3 q h]
  refine ⟨⟨?_, by_omega, ?_, ?_, ?_, eER, ?_⟩, by_grind⟩
  · have hS : S _ = S t ∪ pairS _ := pre_succ _ t
    rw [vT', hS, ← Set.union_assoc]
    zumyg; exact inv_blk hst uInc_lr inv4
  · rw [o' _ by_decide, lr4 _ by_omega, hlen2]
  · rw [o' _ by_decide, lr4 _ by_omega, hoff2]
  · rw [o' _ by_decide, lr4 _ by_omega, hR72]
  · have m' : c'.nmem = c₄.nmem := by zumyg
    have hax3 : AuxKeep c c₃ := fun x h1 h2 => by rw [m3]; exact hax2 x h1 h2
    have := auxKeep_trans hax3 e3 aux4
    intro x h1 h2; rw [m']; exact this x h1 h2
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-! ## Steps -/

/-- **A step of the enumeration** relative to the entry `ci`: it adds the queries `S` to the
invariant and keeps the read registers and the auxiliary array of `ci`. -/
def StepOK (P : Polygon) (W : ℕ) (c₀ ci : Config) (Inv : Set ℕ → Config → Prop) (s : Stmt)
    (S : Set ℕ) (K : ℕ) : Prop :=
  ∀ (O : Set ℕ) (c : Config), IInv W c₀ c → (∀ q, ER q → c.nreg q = ci.nreg q) → AuxKeep ci c →
    Inv O c → c.nreg ALLOC + K ≤ W →
    IRS P W c₀ s c K (fun c' => Inv (O ∪ S) c' ∧ ztexb ∧
      AuxKeep ci c')
theorem StepOK.seq {ci : Config} {Inv : Set ℕ → Config → Prop} {s t : Stmt} {S T : Set ℕ}
    {K K' : ℕ} (h₁ : StepOK P W c₀ ci Inv s S K) (h₂ : StepOK P W c₀ ci Inv t T K') :
    StepOK P W c₀ ci Inv ztfmm (S ∪ T) (K + K') := by
  zuche
  refine IRS.seq (h₁ O c hI he ha hinv by_omega) ?_
  rintro c₁ hI₁ - hA1 ⟨inv1, he1, ha1⟩
  refine (h₂ _ c₁ hI₁ he1 ha1 inv1 by_omega).mono le_rfl ?_
  grind

/-- Chaining the read registers and the auxiliary array. -/
theorem keep_chain {ci c c' : Config} (he : ∀ q, ER q → c.nreg q = ci.nreg q) (ha : AuxKeep ci c)
    (he' : ∀ q, ER q → c'.nreg q = c.nreg q) (ha' : AuxKeep c c') :
    ztexb ∧ AuxKeep ci c' := by
  zulos
  have he2 := he
  zuchi
  have ea : ztsez := he2 _ by_tauto
  have es : ztmur := he2 _ by_tauto
  rw [ha' x by_omega by_omega, ha x h1 h2]

/-! ## A region step -/

/-- **A region step**: if `i < cnt` (`ka` holds `i`), the region in register `src`. -/
def rStep (ka cnt src : ℕ) (od : Stmt) : Stmt :=
  .ifLtN ka cnt (.seq (block [.copyN uR src]) ztwco) .skip
theorem copyR_lr (src : ℕ) : ∀ i ∈ [Instr.copyN uR src], LR ztcpw := by
  simp [dstI, LR, uR, oK, oS, sw]
theorem rStep_ok (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    {ci : Config} {ka cnt src i : ℕ} (hka : ∀ c, IInv W c₀ c → c.nreg ka = i) (hcnt : ER cnt)
    (hsrc : ER src) (hval : i < ci.nreg cnt → ci.nreg src < N₂.nRegions) :
    StepOK P W c₀ ci Inv (rStep ka cnt src od)
      {j | i < ci.nreg cnt ∧ j ∈ regO N₂ ztmhj} (regK Kod zto + 3) := by
  zuche
  have hk := hka c hI
  refine IRS.mono (K := 1 + regK Kod zto + 2) ztsye by_omega
    ztb
  · zufia
    zuguy
    refine IRS.seq (IRS.block [.copyN uR src] hI ⟨iscr_sw by_decide
      by_decide, trivial⟩) ?_
    zudsu
    have r1 : c₁.nreg = regB c.nmem [.copyN uR src] c.nreg := by zvmwl
    zufp
    have vR : c₁.nreg uR = ci.nreg src := by
      zugfe
    have inv1 : ztlaa := by zvmwl; exact inv_blk hst ztvls hinv
    have he1 : ztfle := fun q h => by
      zvnal; exact er_blk ztvls h
    refine (regDo_irs E hod hst hI₁ inv1 vR (hval hlt) by_omega).mono le_rfl ?_
    zuhjo
    have hS : {j | i < ci.nreg cnt ∧ j ∈ regO N₂ ztmhj} = regO N₂ ztmhj := by
      simp_all
    refine ⟨by_simp_all, keep_chain he ha by_simp_all
      (fun x h1 h2 => by rw [ha' x (by rw [he1 _ ztcuk]; exact h1)
        (by rw [he1 _ ztcuk, he1 _ ztcuk]; exact h2), m1])⟩
  · zufia
    zuguy
    have hS : {j | i < ci.nreg cnt ∧ j ∈ regO N₂ ztmhj} = ∅ := by
      grind
    zugkc

/-! ## A parent step -/

/-- The parent of the stop `uI`: its auxiliary word `aB + 5 uI + 4`. -/
def parBody : List Instr :=
  [.copyN uA aB, .addN uA uA uI, .addN uA uA uI, .addN uA uA uI, .addN uA uA uI, .addN uA uA uI,
    .addN uA uA K4, .loadN uK uA]
def uDec : List Instr := [.subN uK uK K1]

/-- **The parent of the stop `uI`** (if `uI < sC` and it has one). -/
def parDo (od : Stmt) : Stmt :=
  .ifLtN uI sC (.seq (block parBody) (.ifLtN K0 uK (.seq (block uDec) ztquh) .skip)) .skip

/-- The queries of the parent of stop `i`. -/
def parS (ci : Config) (i : ℕ) : Set ℕ :=
  {j | i < ci.nreg sC ∧ 0 < parOf ci i ∧ ∃ s, s ≤ 1 ∧ j = 2 * ztquo + s}
theorem parBody_lr : ∀ i ∈ parBody, LR ztcpw := by
  simp [parBody, dstI, LR, uA, uK, oK, oS, sw]
theorem uDec_lr : ∀ i ∈ uDec, LR ztcpw := by
  simp [uDec, dstI, LR, uK, oK, oS, sw]
variable (m f : ℕ → ℕ)
theorem parBody_val (k4 : f K4 = 4) :
    regB m parBody f uK = m (f aB + 5 * f uI + 4) := by
  simp only [K4, sw] at k4
  simp [parBody, regB, regI, upd, uA, uK, uI, aB, K4, sw, k4]
  ring_nf
theorem parBody_other {q : ℕ} (h1 : q ≠ uA) (h2 : q ≠ uK) :
    regB m parBody f q = f q :=
  regB_other _ _ _ (fun i hi he => by
    simp only [parBody, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact h1 he.symm | exact h2 he.symm)
theorem parBody_ok (k4 : f K4 = 4) (hb : f aB + 5 * f uI + 4 ≤ W) :
    okB W m parBody f := by
  simp only [K4, aB, uI, sw, Nat.reduceAdd] at k4 hb
  simp [parBody, okB, okI, regI, upd, uA, uK, uI, aB, K4, sw, k4, IScr]
  omega
set_option maxHeartbeats 2000000 in
theorem parDo_ok (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    {ci : Config} (hpar : ∀ i, i < ci.nreg sC → parOf ci i ≤ N₂.nChords)
    (haux : ci.nreg aB + 5 * ci.nreg sC ≤ ci.nreg ALLOC) (hA : ci.nreg ALLOC ≤ W)
    {O : Set ℕ} (hI : IInv W c₀ c) (he : ∀ q, ER q → c.nreg q = ci.nreg q) (ha : AuxKeep ci c)
    (hinv : Inv O c) {i : ℕ} (hi : c.nreg uI = i) (hroom : c.nreg ALLOC + ztgcd ≤ W) :
    IRS P W c₀ ztqun c ztgcd (fun c' => Inv (O ∪ parS ci i) c' ∧
      ztexb ∧ AuxKeep ci c') := by
  zuiw
  have esC : ztmur := he _ ztcuk
  have eaB : ztsez := he _ ztcuk
  refine IRS.mono (K := 8 + (1 + ztjez + 2) + 2) ztsye by_omega
    ztb
  swap
  · zufia
    zuijw
    zudyo
    zugkc
  zufia
  zuijw
  have hadr : ci.nreg aB + 5 * i + 4 < ci.nreg aB + 5 * ci.nreg sC := by_omega
  refine IRS.seq (K₁ := parBody.length) (IRS.block parBody hI
    (parBody_ok _ _ hK.2.2.2.1 by_omega)) ?_
  zudsu
  have r1 : c₁.nreg = regB c.nmem parBody c.nreg := by zvmwl
  zufp
  have vK : c₁.nreg uK = parOf ci i := by
    rw [r1, parBody_val _ _ hK.2.2.2.1, eaB, hi, ha _ by_omega hadr]; rfl
  have inv1 : ztlaa := by zvmwl; exact inv_blk hst parBody_lr hinv
  have he1 : ztfle := fun q h => by
    zvnal; exact er_blk parBody_lr h
  have ha1 : AuxKeep c c₁ := fun x _ _ => by zvnmf
  zukil
  have eA1 : ztdc := by zvnal; rfl
  zulib
  have hl : parBody.length = 8 := rfl
  zulny

  · intro hn
    rw [hK1.1, vK] at hn
    zudyo
    obtain ⟨he', ha'⟩ := keep_chain he ha he1 ha1
    exact IRS.skip hI₁ by_simp_all
  zulmw
  rw [hK1.1, vK] at hp
  refine IRS.seq (IRS.block uDec hI₁ ⟨iscr_sw by_decide
    by_decide, trivial⟩) ?_
  rintro c₂ hI₂ - hA2 hc2
  have r2 : c₂.nreg = regB c₁.nmem uDec c₁.nreg := by zumyw
  have m2 : ztpna := by zumyw
  have vK2 : c₂.nreg uK = parOf ci i - 1 := by
    rw [r2]; simp [uDec, regB, regI, upd_same]; rw [vK, hK1.2.1]
  have inv2 : Inv O c₂ := by zumyw; exact inv_blk hst uDec_lr inv1
  have he2 : ∀ q, ER q → c₂.nreg q = c₁.nreg q := fun q h => by
    rw [r2]; exact er_blk uDec_lr h
  have eA2 : zteic := by
    zukyk
  have hkn : parOf ci i - 1 < N₂.nChords := by_grind
  refine (odPair_irs E hod hst hI₂ inv2 vK2 hkn by_omega).mono le_rfl ?_
  zuhjo
  have hS : parS ci i = pairS ztquo := by
    ext j; simp only [parS, pairS, mem_ofPred_eq]
    simp_all
  obtain ⟨k1e, k1a⟩ := keep_chain he ha he1 ha1
  obtain ⟨k2e, k2a⟩ := keep_chain k1e k1a he2 (fun x _ _ => by rw [m2])
  obtain ⟨k3e, k3a⟩ := keep_chain k2e k2a by_simp_all ha'
  grind

/-- The parent of the stop `sP`. -/
def pStep0 (od : Stmt) : Stmt := .seq (block [.copyN uI sP]) ztqun

/-- The parent of the stop `sP + 1` (if `sP < sC`). -/
def pStep1 (od : Stmt) : Stmt :=
  .ifLtN sP sC (.seq (block [.addN uI sP K1]) ztqun) .skip
theorem pStep0_ok (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    {ci : Config} (hpar : ∀ i, i < ci.nreg sC → parOf ci i ≤ N₂.nChords)
    (haux : ci.nreg aB + 5 * ci.nreg sC ≤ ci.nreg ALLOC) (hA : ci.nreg ALLOC ≤ W) :
    StepOK P W c₀ ci Inv ztwbh (parS ci (ci.nreg sP)) (1 + ztgcd) := by
  zuche
  have hlr : ∀ i ∈ [Instr.copyN uI sP], LR ztcpw := by zuniz
  refine IRS.seq (IRS.block [.copyN uI sP] hI ⟨iscr_sw by_decide
    by_decide, trivial⟩) ?_
  zudsu
  have r1 : c₁.nreg = regB c.nmem [.copyN uI sP] c.nreg := by zvmwl
  zufp
  have vI : c₁.nreg uI = ci.nreg sP := by
    zvnal; zuobt; exact he _ ztcuk
  zudpv
  obtain ⟨he1, ha1⟩ := keep_chain he ha zthxg
    ztkwg
  zuefq
theorem pStep1_ok (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {od : Stmt} {Kod : ℕ}
    {Inv : Set ℕ → Config → Prop} (hod : OdOK P W c₀ N₂ od Kod Inv) (hst : InvStab Inv)
    {ci : Config} (hpar : ∀ i, i < ci.nreg sC → parOf ci i ≤ N₂.nChords)
    (haux : ci.nreg aB + 5 * ci.nreg sC ≤ ci.nreg ALLOC) (hA : ci.nreg ALLOC ≤ W) :
    StepOK P W c₀ ci Inv ztwbi (parS ci ztrnk) (1 + ztgcd + 2) := by
  zuche
  have eP : c.nreg sP = ci.nreg sP := he _ by_tauto
  have eC : ztmur := he _ ztcuk
  zulny

  · intro hn
    rw [eP, eC] at hn
    have hS : parS ci ztrnk = ∅ := by ext j; simp [parS]; omega
    zugkc
  zufia
  zuiw
  have hlr : ∀ i ∈ [Instr.addN uI sP K1], LR ztcpw := by zuniz
  refine IRS.seq (IRS.block [.addN uI sP K1] hI ⟨⟨iscr_sw by_decide
    by_decide, by rw [hK.2.1]; omega⟩, trivial⟩) ?_
  zudsu
  have r1 : c₁.nreg = regB c.nmem [.addN uI sP K1] c.nreg := by zvmwl
  zufp
  have vI : c₁.nreg uI = ci.nreg sP + 1 := by
    zvnal; zuobt; rw [eP, hK.2.1]
  zudpv
  obtain ⟨he1, ha1⟩ := keep_chain he ha zthxg
    ztkwg
  zuefq

/-! ## The enumeration -/

/-- **The origin enumeration of one iteration.** -/
def orgs (od : Stmt) : Stmt :=
  .seq (rStep K0 kN kL od) (.seq (rStep K1 kN ztdvf od) (.seq (rStep K2 kN ztdvg od)
    (.seq (rStep K3 kN ztdvh od) (.seq (rStep K0 gN gR od) (.seq (rStep K1 gN ztduu od)
      (.seq ztwbh ztwbi))))))

/-- The queries of the steps are those of `iterO`. -/
theorem iter_eq (N : NF) (c : Config) :
    {j | 0 < c.nreg kN ∧ j ∈ regO N ztvjo} ∪
      ({j | 1 < c.nreg kN ∧ j ∈ regO N ztbagn} ∪
      ({j | 2 < c.nreg kN ∧ j ∈ regO N ztbago} ∪
      ({j | 3 < c.nreg kN ∧ j ∈ regO N ztbagp} ∪
      ({j | 0 < c.nreg gN ∧ j ∈ regO N (c.nreg gR)} ∪
      ({j | 1 < c.nreg gN ∧ j ∈ regO N (c.nreg ztduu)} ∪
      (parS c ztccy ∪ parS c (c.nreg sP + 1))))))) = iterO N c := by
  zumag
  simp only [iterO, parO, parS, mem_union, mem_ofPred_eq]
  constructor
  · rintro (⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h, hj⟩ | ⟨h1, h2, hj⟩ |
      ⟨h1, h2, hj⟩)
    · exact Or.inl (Or.inl ztkij)
    · exact Or.inl (Or.inl ztqzw)
    · exact Or.inl (Or.inl ⟨2, by_omega, hj⟩)
    · exact Or.inl (Or.inl ⟨3, by_omega, hj⟩)
    · exact Or.inl (Or.inr ztkij)
    · exact Or.inl (Or.inr ztqzw)
    · simp_all
    simp_all
  · rintro ((⟨i, hi, hj⟩ | ⟨i, hi, hj⟩) | ⟨i, hi | hi, h1, h2, hj⟩)
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
      · simp_all
      · simp_all
      · simp_all
      simp_all
    · grind
    · simp_all
    simp_all
theorem er_of {r : ℕ} (h : r = kN ∨ ztdot ∨ r = gN ∨ r = gR ∨ r = gR + 1) :
    ER r := by
  tauto
set_option maxHeartbeats 2000000 in
/-- **Task E: the origin enumeration.** -/
theorem orgsTask : OrgsTask := by
  refine ⟨orgs, 200, ?_⟩
  intro sh Bs F X Ok P W c₀ J N₁ N₂ E od Kod Inv hod hst O c hI hinv hkL hgR hpar haux hroom
  have hod' := hod
  zuizh
  have hA := hI.hw.1 ALLOC
  have kv : ∀ c', IInv W c₀ c' → c'.nreg K0 = 0 ∧ c'.nreg K1 = 1 ∧ c'.nreg K2 = 2 ∧
      c'.nreg K3 = 3 := fun c' h => by
    obtain ⟨a, b, -, -, -, f, g⟩ := E.hK.fix h; omega
  have h := (rStep_ok E hod' hst'
      ztkvy ztyjf (er_of (Or.inr (Or.inl ⟨le_rfl, by
        omega⟩))) (fun h => by simpa using hkL 0 by_omega)).seq
    ((rStep_ok E hod' hst'
      ztkvz ztyjf ztmjc (fun h => hkL 1 by_omega)).seq
    ((rStep_ok E hod' hst'
      (fun c' h => (kv c' h).2.2.1) ztyjf ztmjc (fun h => hkL 2 by_omega)).seq
    ((rStep_ok E hod' hst'
      (fun c' h => (kv c' h).2.2.2) ztyjf ztmjc (fun h => hkL 3 by_omega)).seq
    ((rStep_ok E hod' hst'
      ztkvy (er_of ztbajm)
      (er_of ztbaje) (fun h => by simpa using hgR 0 by_omega)).seq
    ((rStep_ok E hod' hst'
      ztkvz (er_of ztbajm)
      ztmjc (fun h => hgR 1 by_omega)).seq
    ((pStep0_ok E hod' hst' hpar haux hA).seq (pStep1_ok E hod' hst' hpar haux hA)))))))
  rw [iter_eq] at h
  zujmn
  have e1 : zteki * (Kod + 200) + 200 = 12 * ztswi + 2400 * D + 8 * Kod + 1800 := by
    ring
  have e2 : regK Kod D = 2 * ztswi + 10 * D + 17 := by unfold regK; ring
  refine (h O c hI by_omega ztczj hinv ?_).mono ?_ by_grind
  · grind
  grind
