module

public import Chazelle.MacT
public import Chazelle.Core.GranRamBody
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.FactsAttach
public import Chazelle.Core.ClusterLabelStage

namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set
open Chazelle.Chain (ChordSystem regionsIn TouchesIn freeIn freeIn_anti regionsIn_subset
  regionsIn_isPreconnected regionsIn_nonempty mem_regionsIn regionsIn_eq_component)
open Chazelle.Merge (exitsIn IsSplit)
variable {M : Model}

/-- **A region of `S` inside the free set of `T ⊇ S` is a region of `T`.** -/
theorem region_of_subset_free {S T : Set ztf} (hST : S ⊆ T) {R : Set Point}
    (hR : R ∈ regionsIn M.D S) (hfree : R ⊆ freeIn M.D T) : R ∈ regionsIn M.D T := by
  obtain ⟨z, hz⟩ := regionsIn_nonempty hR
  have hzT := hfree hz
  refine ⟨z, hzT, Subset.antisymm ?_ ?_⟩
  · exact (regionsIn_isPreconnected hR).subset_connectedComponentIn hz hfree
  · rw [regionsIn_eq_component hR hz]
    exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn
      (mem_connectedComponentIn hzT)
      ((connectedComponentIn_subset _ _).trans (freeIn_anti M.D hST))

/-- **The halves do not depend on the chords outside the region**: a region of `insert e T`
inside `R` is a region of `insert e S`, for `S ⊆ T` finite admissible families of which `R` is a
common region, and `e` a new admissible chord inside `R`. -/
theorem half_old (hM : WalkAx M) {S T : Set ztf} (hST : S ⊆ T) (hT : T ⊆ M.Adm)
    (hTfin : T.Finite) {R : Set Point} (hRS : R ∈ regionsIn M.D S) (hRT : R ∈ regionsIn M.D T)
    {e : Set Point} (he : e ∈ M.Adm) (heT : e ∉ T) (heR : e ∩ M.D ⊆ R) {P : Set Point}
    (hP : P ∈ regionsIn M.D zthhy) (hPR : P ⊆ R) : P ∈ regionsIn M.D ztrc := by
  zuivz
  have heS : ztsii := fun h => heT (hST h)
  have hSF : insert e S ⊆ insert e T := insert_subset_insert hST
  obtain ⟨R₁, R₂, hs⟩ := Merge.exists_split hFT ztkfs ztodj heT hRT heR
  obtain ⟨R₁', R₂', hs'⟩ := Merge.exists_split hFT (hST.trans ztkfs)
    ztodj heS hRS heR
  -- the halves in `S` are open and disjoint, and cover `R \ e`
  have ho₁ := hFT.regionsIn_open hSF hs'.mem₁
  have ho₂ := hFT.regionsIn_open hSF hs'.mem₂
  have hd : Disjoint R₁' R₂' :=
    Chazelle.Chain.regionsIn_disjoint_of_ne hs'.mem₁ hs'.mem₂ hs'.ne
  have hPsub : P ⊆ R \ e := fun z hz => ⟨hPR hz, fun hze => (regionsIn_subset hP hz).2
    ⟨e, mem_insert e T, hze⟩⟩
  rw [← hs'.union] at hPsub
  rcases (regionsIn_isPreconnected hP).subset_or_subset ho₁ ho₂ hd hPsub with h | h
  · -- `P ⊆ R₁'`, and conversely `R₁'` lies in a region of `insert e T`, which must be `P`
    have hR₁ : R₁' ⊆ freeIn M.D zthhy := by
      zugh
      refine ⟨(regionsIn_subset hs'.mem₁ hz).1, ?_⟩
      zueck
      zukkz
      · exact (regionsIn_subset hs'.mem₁ hz).2 ztonc
      · have hzR : z ∈ R := hs'.sub₁ hz
        have := regionsIn_subset hRT hzR
        exact this.2 ztrbh
    zuhic
    have hPe : ztylh :=
      regionsIn_eq_component hP hz
    have : R₁' ⊆ P := by
      zummr
      exact (regionsIn_isPreconnected hs'.mem₁).subset_connectedComponentIn ztvrn hR₁
    zuonc; exact hs'.mem₁
  · have hR₂ : R₂' ⊆ freeIn M.D zthhy := by
      zugh
      refine ⟨(regionsIn_subset hs'.mem₂ hz).1, ?_⟩
      zueck
      zukkz
      · exact (regionsIn_subset hs'.mem₂ hz).2 ztonc
      · have hzR : z ∈ R := hs'.sub₂ hz
        have := regionsIn_subset hRT hzR
        exact this.2 ztrbh
    zuhic
    have hPe : ztylh :=
      regionsIn_eq_component hP hz
    have : R₂' ⊆ P := by
      zummr
      exact (regionsIn_isPreconnected hs'.mem₂).subset_connectedComponentIn ztvrn hR₂
    zuonc; exact hs'.mem₂

/-- **Good splits survive more chords outside the region.** -/
theorem splitsWell_mono (hM : WalkAx M) {S T : Set ztf} (hST : S ⊆ T) (hT : T ⊆ M.Adm)
    (hTfin : T.Finite) {R : Set Point} (hRS : R ∈ regionsIn M.D S) (hRT : R ∈ regionsIn M.D T)
    {e : Set Point} (he : e ∈ M.Adm) (heT : e ∉ T) (hw : SplitsWell M S R e) :
    SplitsWell M T R e := by
  refine ⟨heT, hw.2.1, fun P hP hPR => ?_⟩
  have h1 := hw.2.2 P (half_old hM hST hT hTfin hRS hRT he heT hw.2.1 hP hPR) hPR
  exact h1.trans (ncard_le_ncard (Merge.exitsIn_mono hST P)
    (hTfin.subset (Merge.exitsIn_subset T P)))

/-- The data of a round: new admissible chords, each splitting a region of `S` well, at most one
per region. -/
structure RoundData (M : Model) (S E : Set ztf) : Prop where
  adm : E ⊆ M.Adm
  fin : E.Finite
  split : ∀ e ∈ E, ∃ R ∈ regionsIn M.D S, SplitsWell M S R e
  uniq : ∀ e ∈ E, ∀ e' ∈ E, ∀ R ∈ regionsIn M.D S, SplitsWell M S R e →
    SplitsWell M S R e' → e = e'

/-- The classification of the regions after a round (see the module docstring). -/
def Classified (M : Model) (S E : Set ztf) (U : Set Point) : Prop :=
  (U ∈ regionsIn M.D S ∧ exitsIn M.D zteny U = exitsIn M.D S U ∧
      ∀ e ∈ E, ¬ (e ∩ M.D ⊆ U)) ∨
    (∃ R ∈ regionsIn M.D S, ∃ e ∈ E, SplitsWell M S R e ∧ U ⊆ R ∧
      3 ≤ (exitsIn M.D zteny U).ncard ∧
      (exitsIn M.D zteny U).ncard < (exitsIn M.D S R).ncard)
theorem inter_nonempty_of_adm (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) :
    (e ∩ M.D).Nonempty :=
  ((hM.sys {e} ztqwm (finite_singleton e)).chord_inter_nonempty_isPreconnected
    ztkau).1

/-- **The regions after a round.** -/
theorem round_classify (hM : WalkAx M) {S E : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) (hE : RoundData M S E) :
    ∀ U ∈ regionsIn M.D zteny, Classified M S E U := by
  suffices key : ∀ E₀ : Set ztf, E₀.Finite → E₀ ⊆ E →
      ∀ U ∈ regionsIn M.D (S ∪ E₀), Classified M S E₀ U from key E hE.fin subset_rfl
  intro E₀ hE₀
  induction E₀, hE₀ using Set.Finite.induction_on with
  | empty =>
    intro _ U hU
    rw [union_empty] at hU
    left
    exact ⟨hU, by_simp, fun e he => absurd he (notMem_empty e)⟩
  | @insert e E₀ heE₀ hE₀fin ih =>
    intro hsub U hU
    have hE₀sub : E₀ ⊆ E := (subset_insert e E₀).trans hsub
    have heE : e ∈ E := hsub (mem_insert e E₀)
    set T := S ∪ E₀ with hTd
    have hT : T ⊆ M.Adm := union_subset hS (hE₀sub.trans hE.adm)
    have hTfin : T.Finite := hfin.union hE₀fin
    have hTe : S ∪ insert e E₀ = insert e T := by
      simp_all
    obtain ⟨R, hR, hw⟩ := hE.split e heE
    have he := hE.adm heE
    have heS : ztsii := hw.1
    have heT : e ∉ T := by
      simp_all
    -- the chords of `E₀` avoid `R`
    have hE₀R : ∀ e₀ ∈ E₀, ∀ z ∈ e₀, z ∉ closure R ∨ z ∉ M.D := by
      intro e₀ he₀ z hz
      zuho

      obtain ⟨hzR, hzD⟩ := hcon
      obtain ⟨R₀, hR₀, hw₀⟩ := hE.split e₀ ztvsw
      have hzR₀ : z ∈ R₀ := hw₀.2.1 ztuit
      have hopen : IsOpen R₀ := (hM.sys S hS hfin).regionsIn_open subset_rfl hR₀
      obtain ⟨y, hyR₀, hyR⟩ := mem_closure_iff.1 hzR R₀ hopen hzR₀
      have hRR₀ : R = R₀ := by
        rw [regionsIn_eq_component hR hyR, regionsIn_eq_component hR₀ hyR₀]
      subst hRR₀
      exact heE₀ (hE.uniq e heE e₀ ztvsw R hR hw hw₀ ▸ he₀)
    have hRfree : R ⊆ freeIn M.D T := by
      zugh
      refine ⟨(regionsIn_subset hR hz).1, ?_⟩
      zueck
      rcases hc with hcS | hcE
      · exact (regionsIn_subset hR hz).2 ⟨c, hcS, hzc⟩
      · rcases hE₀R c hcE z hzc with h | h
        · exact h (subset_closure hz)
        · exact h (regionsIn_subset hR hz).1
    have hRT : R ∈ regionsIn M.D T := region_of_subset_free subset_union_left hR hRfree
    have hexR : exitsIn M.D T R = exitsIn M.D S R := by
      zubcj
      refine ⟨fun ⟨hcT, hcR⟩ => ⟨?_, hcR⟩, fun ⟨hcS, hcR⟩ => ⟨Or.inl hcS, hcR⟩⟩
      rcases hcT with hcS | hcE
      · omega
      · exfalso
        obtain ⟨z, ⟨hz, hzD⟩, hzR⟩ := hcR
        grind
    have hwT : SplitsWell M T R e :=
      splitsWell_mono hM subset_union_left hT hTfin hR hRT he heT hw
    zuivz
    obtain ⟨R₁, R₂, hs⟩ := Merge.exists_split hFT ztkfs ztodj heT hRT
      hw.2.1
    rw [hTe] at hU
    unfold Classified
    rw [hTe]
    rcases hs.mem_cases hU with ⟨hUT, hUR⟩ | hU12
    · -- an old region of `T` other than `R`
      have hex := hs.exits_other hFT ztkfs hUT hUR
      rcases ih hE₀sub U hUT with ⟨hUS, hexS, hno⟩ | ⟨R', hR', e', he', hw', hUR', h3, hlt⟩
      · left
        refine ⟨hUS, by_simp_all, fun e'' he'' => ?_⟩
        rcases he'' with rfl | he''
        · intro hsub'
          obtain ⟨z, hz⟩ := inter_nonempty_of_adm hM he
          have hzU := hsub' hz
          have hzR := hw.2.1 hz
          have : ztmtw := by
            rw [regionsIn_eq_component hUS hzU, regionsIn_eq_component hR hzR]
          simp_all
        simp_all
      grind
    · -- a half of `R`
      right
      have hUsub : U ⊆ R := by rcases hU12 with rfl | rfl; exacts [hs.sub₁, hs.sub₂]
      obtain ⟨h3, hlt⟩ := splitsWell_degrees hM hT hTfin hRT he hwT U hU hUsub
      grind

/-- **The degree after a round.**  If `S` has degree `≤ d` and every region of `S` with more
than `D` exit chords received a chord of `E`, then `S ∪ E` has degree `≤ max D (d - 1)`. -/
theorem round_degLe (hM : WalkAx M) {S E : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) (hE : RoundData M S E) {d D : ℕ} (hd : M.DegLe S d)
    (hall : ∀ R ∈ regionsIn M.D S, D < (exitsIn M.D S R).ncard → ∃ e ∈ E, SplitsWell M S R e) :
    M.DegLe zteny ztzxa := by
  zucne
  rcases round_classify hM hS hfin hE U hU with ⟨hUS, hex, hno⟩ | ⟨R, hR, e, he, hw, -, -, hlt⟩
  · show (exitsIn M.D zteny U).ncard ≤ _
    zupat
    zuho

    obtain ⟨e, he, hw⟩ := hall U hUS (lt_of_le_of_lt (le_max_left _ _) hcon)
    exact hno e he hw.2.1
  · show (exitsIn M.D zteny U).ncard ≤ _
    have := hd R hR
    change (exitsIn M.D S R).ncard ≤ d at this
    omega
open Chazelle.Chain (SideAttach sideInArc sidePt SideSectorIn)
theorem same_side (hM : WalkAx M) {e s : Set Point} (he : e ∈ M.Adm) (hs : s ∈ M.Adm)
    (hes : s ≠ e) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W e pa ta)
    (hB : SideAttach M.W e pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    {pv pw : ℕ} {tv tw : ℝ} (hv : SideAttach M.W s pv tv) (hw : SideAttach M.W s pw tw)
    (hvin : sideInArc ztbf ztbd (pv + tv)) :
    ¬ sideInArc ztbd ztbf ztbjs := by
  intro hwin
  zubjh
  have hF : ChordSystem M.D {e, s} :=
    hM.sys _ (insert_subset he (singleton_subset_iff.2 hs)) ztcwq
  obtain ⟨hvp, hv0, hv1, -⟩ := id hv
  obtain ⟨hwp, hw0, hw1, -⟩ := id hw
  obtain ⟨x₁, hx₁, hxK₁⟩ := exists_near_attach hM hs hv (hsec₁ pv hvp tv hv0 hv1 hvin)
  obtain ⟨x₂, hx₂, hxK₂⟩ := exists_near_attach hM hs hw (hsec₂ pw hwp tw hw0 hw1 hwin)
  have hsD : s ∩ M.D ⊆ M.D \ e := fun z hz =>
    ⟨hz.2, fun hze => hF.inter_subset_compl ztbt ztp hes ⟨hz.1, hze⟩ hz.2⟩
  have hsub := (hF.chord_inter_nonempty_isPreconnected (Or.inr rfl : s ∈ ({e, s} : Set _))).2
    |>.subset_connectedComponentIn hx₁ hsD
  have e1 := connectedComponentIn_eq hxK₁
  have e2 := connectedComponentIn_eq hxK₂
  exact hK (e1.trans ((connectedComponentIn_eq (hsub hx₂)).trans e2.symm))

/-- **An admissible chord has one attachment per endpoint**: two attachments of `e` with the
same point are the same position. -/
theorem attach_unique (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {p p' : ℕ} {t t' : ℝ}
    (hA : SideAttach M.W e p t) (hA' : SideAttach M.W e p' t')
    (hpt : sidePt M.W p t = sidePt M.W p' t') : p = p' ∧ t = t' := by
  obtain ⟨a, b, hab, rfl, -, hopen, hEa, hEb⟩ := hM.ends e he
  zuct
  have hne' : ztppi := fun h1 h2 => hne ztwo
  obtain ⟨hp, ht0, ht1, hmem, r, hr, hsec⟩ := hA
  obtain ⟨hp', ht0', ht1', -, r', hr', hsec'⟩ := hA'
  have key : ∀ u v : Point, u ≠ v → (∀ s ∈ Set.Ioo (0 : ℝ) 1, Geometry.lerp u v s ∈ M.D) →
      Chazelle.segment u v = Chazelle.segment a b → WalkEnd M.W ztemf u →
      sidePt M.W p t = u → False := by
    intro u v huv hop hseg hE hu
    obtain ⟨ρ, hρ, hdisj⟩ := hE.2 p p' t t' hp ht0 ht1 hp' ht0' ht1' hne' hu (hpt ▸ hu)
    obtain ⟨s, hs0, hs1, hsne, hsd⟩ := exists_lerp_near huv (lt_min hρ zttsr)
    have hx : Geometry.lerp u v s ∈ Chazelle.segment a b := by
      zufow
    have h1 := hsec _ hx by_grind
      by_grind
    have h2 := hsec' _ hx by_grind
      by_grind
    exact hdisj _ (by rw [Metric.mem_ball]; grind) h1 h2
  rcases hM.attach_endpoint hopen ⟨hp, ht0, ht1, hmem, r, hr, hsec⟩ with h | h
  · grind
  · exact key b a hab.symm ztjnr ztfnp hEb h
variable (a b : ℝ)
theorem not_sideInArc_left : ¬ sideInArc a b a := by
  zudcn
theorem not_sideInArc_right : ¬ sideInArc a b b := by
  zudcn

/-- An admissible chord is attached strictly inside a side of itself at no position. -/
theorem not_attach_strict (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {pa pb : ℕ}
    {ta tb : ℝ} (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {p : ℕ} {t : ℝ} (hat : SideAttach M.W e p t)
    (hin : sideInArc ztbf ztbd ztk ∨ sideInArc ztbd ztbf ztk) :
    False := by
  obtain ⟨hseg, -, hopen, -, -⟩ := hM.attach_seg he hA hB hAB
  have hat' := hat
  rw [hseg] at hat'
  rcases hM.attach_endpoint hopen hat' with h | h
  · obtain ⟨rfl, rfl⟩ := attach_unique hM he hat hA h
    zuklk
    · zulfr
    · zulfs
  · obtain ⟨rfl, rfl⟩ := attach_unique hM he hat hB h
    zuklk
    · zulfs
    · zulfr

/-- **Counting decides a good split.**  An admissible chord `e`, attached at two positions with
distinct points, with at least two exit chords of the region `R` attached strictly on each side,
is not a chord of `S`, lies in `R`, and splits `R` well. -/
theorem splitsWell_of_counts (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ Chazelle.Chain.regionsIn M.D S) {e : Set Point}
    (he : e ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (h1 : 2 ≤ (sideExits M S R ztbf ztbd).ncard)
    (h2 : 2 ≤ (sideExits M S R ztbd ztbf).ncard) : SplitsWell M S R e := by
  obtain ⟨K₁, K₂, hK, ⟨c₁', rfl⟩, ⟨c₂', rfl⟩, hsec₁, hsec₂⟩ := hM.split he hA hB hAB
  obtain ⟨d₁, hd₁⟩ := Set.nonempty_of_ncard_ne_zero
    (show (sideExits M S R ztbf ztbd).ncard ≠ 0 by omega)
  obtain ⟨d₂, hd₂⟩ := Set.nonempty_of_ncard_ne_zero
    (show (sideExits M S R ztbd ztbf).ncard ≠ 0 by omega)
  -- a side exit touches `R` and has points of the domain in the component of its side
  have side : ∀ (c₀ : Point) (k₁ k₂ : ℝ), (k₁ = pa + ta ∧ k₂ = pb + tb ∨ k₁ = pb + tb ∧ k₂ = pa + ta) →
      (∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc k₁ k₂ ztk →
        SideSectorIn M.W ztyqg p t) →
      ∀ d ∈ sideExits M S R k₁ k₂, d ≠ e ∧ ∃ x ∈ d ∩ M.D, x ∈ connectedComponentIn ztbto c₀ := by
    rintro c₀ k₁ k₂ hk hsec d ⟨⟨hdS, -⟩, p, t, hat, hin⟩
    have hdne : d ≠ e := by
      zunq
      refine not_attach_strict hM he hA hB hAB hat ?_
      grind
    obtain ⟨hp, ht0, ht1, -⟩ := id hat
    exact ⟨hdne, exists_near_attach hM ztqpo hat ztobf⟩
  obtain ⟨hne1, x₁, hx₁, hxK₁⟩ := side c₁' _ _ ztwzn hsec₁ d₁ hd₁
  obtain ⟨hne2, x₂, hx₂, hxK₂⟩ := side c₂' _ _ ztxch hsec₂ d₂ hd₂
  zuljy
  -- `e ∉ S` and `e ∩ D ⊆ R`: otherwise `R` avoids `e` and lies in both components
  have key : e ∉ S ∧ e ∩ M.D ⊆ R := by
    zubqk
    have hRe : R ⊆ M.D \ e := by
      zugh
      refine ⟨(Chazelle.Chain.regionsIn_subset hR hz).1, fun hze => ?_⟩
      by_cases heS : e ∈ S
      · exact (Chazelle.Chain.regionsIn_subset hR hz).2 ⟨e, heS, hze⟩
      · zuivy
        obtain ⟨R', hR', heR'⟩ := Merge.exists_region_of_chord hF ztoiq
          zttte heS
        have hRR : R = R' := by
          rw [Chazelle.Chain.regionsIn_eq_component hR hz,
            Chazelle.Chain.regionsIn_eq_component hR' (heR' ⟨hze, (Chazelle.Chain.regionsIn_subset hR hz).1⟩)]
        grind
    have hF₁ := hM.sys {d₁, e} (insert_subset (hS hd₁.1.1) ztqwm) ztcwq
    have hF₂ := hM.sys {d₂, e} (insert_subset (hS hd₂.1.1) ztqwm) ztcwq
    have hR1 := subset_component_of_touches hM.isOpen hF₁ ztp ztbt hne1 hx₁ hxK₁
      hRe ztpwu hd₁.1.2
    have hR2 := subset_component_of_touches hM.isOpen hF₂ ztp ztbt hne2 hx₂ hxK₂
      hRe ztpwu hd₂.1.2
    zuhib
    exact hdisj.notMem_of_mem_left (hR1 hz) (hR2 hz)
  exact splitsWell_of_sideExits hM hS hfin hR he key.1 key.2 hA hB hAB h1 h2
open Filter Topology Metric
open Chazelle.Chain (sideKey_inj)
open Merge (exitsIn)
theorem cyc_cases {a b x : ℝ} (hab : a ≠ b) :
    x = a ∨ x = b ∨ sideInArc a b x ∨ sideInArc b a x := by
  zudmi
  · simp_all
  zujud
  · simp_all
  zulw
  zuiq

/-- Two attachment positions with distinct points have distinct keys. -/
theorem key_ne_of_attach {W : Polygon} {c c' : Set Point} {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach W c pa ta) (hB : SideAttach W c' pb tb)
    (hAB : sidePt W pa ta ≠ sidePt W pb tb) : (pa : ℝ) + ta ≠ pb + tb := by
  zuq
  obtain ⟨h1, h2⟩ := sideKey_inj hA.2.1 hA.2.2.1 hB.2.1 hB.2.2.1 h
  simp_all

/-- **An admissible chord other than `e` has an attachment off the two attachment keys of
`e`.** -/
theorem exists_attach_off (hM : WalkAx M) {e c : Set Point} (he : e ∈ M.Adm) (hc : c ∈ M.Adm)
    (hce : c ≠ e) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W e pa ta)
    (hB : SideAttach M.W e pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) :
    ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧
      (sideInArc ztbf ztbd ztk ∨ sideInArc ztbd ztbf ztk) := by
  have hne := key_ne_of_attach hA hB hAB
  obtain ⟨a, b, hab, hcab, -, hopen, ⟨⟨p₁, t₁, hA₁, h₁⟩, -⟩, ⟨⟨p₂, t₂, hA₂, h₂⟩, -⟩⟩ :=
    hM.ends c hc
  zuchu
  -- the attachment points of `e` are its ends
  have hAe : sidePt M.W pa ta = ea ∨ sidePt M.W pa ta = eb := by
    zvnbk at hA; exact hM.attach_endpoint heopen hA
  have hBe : sidePt M.W pb tb = ea ∨ sidePt M.W pb tb = eb := by
    zvnbk at hB; exact hM.attach_endpoint heopen hB
  -- if both attachments of `c` sit at keys of `e`, then `c = e`
  have pos_of : ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
      (p : ℝ) + t = pa + ta ∨ (p : ℝ) + t = pb + tb →
      sidePt M.W p t = sidePt M.W pa ta ∨ sidePt M.W p t = sidePt M.W pb tb := by
    intro p t hat hk
    zucot
    · obtain ⟨h1, h2⟩ := sideKey_inj hat.2.1 hat.2.2.1 hA.2.1 hA.2.2.1 hk
      simp_all
    · obtain ⟨h1, h2⟩ := sideKey_inj hat.2.1 hat.2.2.1 hB.2.1 hB.2.2.1 hk
      simp_all
  zubaj

  have off : ∀ (p : ℕ) (t : ℝ), SideAttach M.W c p t →
      (p : ℝ) + t = pa + ta ∨ (p : ℝ) + t = pb + tb := by
    intro p t hat
    rcases cyc_cases (x := (p : ℝ) + t) hne with h | h | h | h
    · grind
    · grind
    · grind
    grind
  have ha := pos_of p₁ t₁ hA₁ by_grind
  have hb := pos_of p₂ t₂ hA₂ by_grind
  zvnbm at ha
  rw [h₂] at hb
  apply hce
  rw [hcab, heq]
  -- `{a, b} = {ea, eb}`
  have hpts : (a = ea ∧ b = eb) ∨ (a = eb ∧ b = ea) := by
    grind
  rcases hpts with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · zulxb

/-- **A good split is seen by the count test.**  If the admissible chord `e`, attached at two
positions with distinct points, splits the region `R` of `S` well, then at least two exit chords
of `R` are attached strictly inside each of the two key intervals cut by `e`. -/
theorem counts_of_splitsWell (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ regionsIn M.D S) {e : Set Point}
    (he : e ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W e pa ta)
    (hB : SideAttach M.W e pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    (hsw : SplitsWell M S R e) :
    2 ≤ (sideExits M S R ztbf ztbd).ncard ∧
      2 ≤ (sideExits M S R ztbd ztbf).ncard := by
  obtain ⟨heS, heR, hP⟩ := hsw
  zusa

  obtain ⟨K₁, K₂, hK, ⟨c₁, hK₁⟩, ⟨c₂, hK₂⟩, hsec₁, hsec₂⟩ := hM.split he hA hB hAB
  have hdisj : Disjoint K₁ K₂ := by
    zuczz
  have hsub : ztkns := fun Q hQ z hz =>
    ⟨(regionsIn_subset hQ hz).1, fun hze => (regionsIn_subset hQ hz).2 by_grind⟩
  -- every exit chord of a half lies on one side, with the half in that side's component
  have hside : ∀ Q ∈ regionsIn M.D F, ∀ c ∈ exitsIn M.D S Q,
      (Q ⊆ K₁ ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ sideInArc ztbf ztbd ztk) ∨
      (Q ⊆ K₂ ∧ ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ sideInArc ztbd ztbf ztk) := by
    intro Q hQ c ⟨hcS, hcQ⟩
    zukbk
    obtain ⟨p, t, hat, hin⟩ := exists_attach_off hM he ztmkv hce hA hB hAB
    obtain ⟨hp, ht0, ht1, -⟩ := id hat
    zukll
    · left
      obtain ⟨x, hx, hxK⟩ := exists_near_attach hM ztmkv hat (hsec₁ p hp t ht0 ht1 hin)
      rw [hK₁] at hxK ⊢
      exact ⟨subset_component_of_touches hM.isOpen hF ztqpp heF hce hx hxK by_grind
        ztqvp hcQ, p, t, hat, hin⟩
    · right
      obtain ⟨x, hx, hxK⟩ := exists_near_attach hM ztmkv hat (hsec₂ p hp t ht0 ht1 hin)
      rw [hK₂] at hxK ⊢
      exact ⟨subset_component_of_touches hM.isOpen hF ztqpp heF hce hx hxK by_grind
        ztqvp hcQ, p, t, hat, hin⟩
  have hR₁R : ztiyp := fun z hz => by
    zuege

  have hR₂R : ztiyq := fun z hz => by
    zuege

  have hc₁ := hP R₁ hs.mem₁ hR₁R
  have hc₂ := hP R₂ hs.mem₂ hR₂R
  have hfinS : ztjba := fun Q =>
    hfin.subset zttag
  have hfinE := fun k₁ k₂ =>
    (hfinS R).subset (sideExits_subset S R k₁ k₂)
  -- a half lies in one component
  have hin : ∀ Q ∈ regionsIn M.D F, Q ⊆ R → 2 ≤ (exitsIn M.D S Q).ncard → Q ⊆ K₁ ∨ Q ⊆ K₂ := by
    intro Q hQ _ h2
    obtain ⟨c, hc⟩ := nonempty_of_ncard_ne_zero (s := exitsIn M.D S Q) by_omega
    grind
  -- the exits of a half in `K₁` are on the first side, and so on
  have hcount : ∀ Q ∈ regionsIn M.D F, Q ⊆ R → 2 ≤ (exitsIn M.D S Q).ncard →
      (Q ⊆ K₁ → 2 ≤ (sideExits M S R ztbf ztbd).ncard) ∧
      (Q ⊆ K₂ → 2 ≤ (sideExits M S R ztbd ztbf).ncard) := by
    intro Q hQ hQR h2
    zuhid
    have htouch : ∀ c, TouchesIn M.D c Q → TouchesIn M.D c R := by
      rintro c ⟨w, hw, hwc⟩
      exact ⟨w, hw, closure_mono hQR hwc⟩
    constructor
    · zudzy

      · exact ztlwt
      · exact absurd (h.1 hz) by_grind
    · zudzy

      · exact absurd ztvto by_grind
      · exact ztlwt
  -- the two halves are in different components
  have hdiff : ¬ ((R₁ ⊆ K₁ ∧ R₂ ⊆ K₁) ∨ (R₁ ⊆ K₂ ∧ R₂ ⊆ K₂)) := by
    zuchu
    set z := Geometry.lerp ea eb ztcn with hz
    have hzD : ztmxg := heopen _ ztfm
    have hze : ztpqq := by
      zugdv
    have hRo := hF.regionsIn_open hSF hR
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hRo z (heR ⟨hze, hzD⟩)
    have hsys : ({e} : Set _) ⊆ F := singleton_subset_iff.2 heF
    obtain ⟨ε₀, hε₀, hsep⟩ := hF.chord_separates_in hsys ztkau hze hzD
    set ε := min ztcop ztkia with hε
    zusv
    obtain ⟨hu, hd, hne⟩ := hsep ε hε0 ztyrj
    have hfe : freeIn M.D {e} = M.D \ e := by
      ext w; zunjh
    rw [hfe] at hu hd hne
    have hmemR : ∀ w : Point, dist w z < ρ → w ∈ M.D \ e → w ∈ R₁ ∪ R₂ := by
      intro w hw hwe
      rw [hs.union]
      exact ⟨hball hw, hwe.2⟩
    have hdu : dist (ztgd : Point) z < ρ := by
      zutq
      zufpu
      zugey

    have hdd : dist (ztfr : Point) z < ρ := by
      zutq
      zuens
      zugey

    have hU12 := hmemR _ hdu hu
    have hD12 := hmemR _ hdd hd
    have same : ∀ K : Set Point, (∃ c₀, K = connectedComponentIn ztbto c₀) →
        (ztgd : Point) ∈ K → (ztfr : Point) ∈ K → False := by
      rintro K ⟨c₀, rfl⟩ h1 h2
      exact hne ((connectedComponentIn_eq h1).symm.trans (connectedComponentIn_eq h2))
    zuwt
    · zufhe

      exact same K₁ ⟨c₁, hK₁⟩ hu' hd'
    · zufhe

      exact same K₂ ⟨c₂, hK₂⟩ hu' hd'
  have i1 := hin R₁ hs.mem₁ hR₁R hc₁
  have i2 := hin R₂ hs.mem₂ hR₂R hc₂
  have k1 := hcount R₁ hs.mem₁ hR₁R hc₁
  have k2 := hcount R₂ hs.mem₂ hR₂R hc₂
  rcases i1 with h1 | h1 <;> rcases i2 with h2 | h2
  · grind
  · grind
  · grind
  grind
open Chazelle.Chain (sideInArc_swap)
open WalkEmbed (off)
variable {n g a b x : ℝ} {S : Set (Set Point)}
/-- Cyclic betweenness is invariant under rotation. -/
theorem sideInArc_rot (_hg0 : 0 ≤ g) (_hgn : g < n) (ha0 : 0 ≤ a) (han : a < n)
    (hb0 : 0 ≤ b) (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) :
    sideInArc a b x ↔ sideInArc ztlrl ztlrm zthzb := by
  unfold off sideInArc
  split_ifs <;> constructor <;> intro h <;> cyc_close

/-- The closed cyclic interval `[a, b]`. -/
def ClosedArc (a b x : ℝ) : Prop := sideInArc a b x ∨ x = a ∨ x = b

/-- Facts about an interval `(A, B)` (keys in `[0, n)`) containing the key `0`. -/
theorem cyc_zero {A B : ℝ} (hA0 : 0 ≤ A) (hAB : A ≠ B) (hi : sideInArc A B 0) : 0 < B ∧ B < A := by
  unfold sideInArc at hi
  grind

/-- Outside an interval `(A, B)` containing `0`. -/
theorem cyc_zero_out {A B u : ℝ} (hBA : B < A) (h : ¬ sideInArc A B u) : B ≤ u ∧ u ≤ A := by
  zujqy
  grind

/-- On the closed interval `[A, B]` containing `0` inside. -/
theorem cyc_zero_closed {A B x : ℝ} (hBA : B < A) (h : ClosedArc A B x) : A ≤ x ∨ x ≤ B := by
  unfold ClosedArc sideInArc at h
  grind

/-- **Domination when `a'` is strictly inside `Aⱼ`** (keys rotated so that `a` is at `0`). -/
theorem cyc_dom_open {A B A' B' x x' a' u : ℝ} (hA0 : 0 ≤ A) (_hB'0 : 0 ≤ B') (_hx0 : 0 ≤ x)
    (hAB : A ≠ B) (hi : sideInArc A B 0) (hjA : ¬ sideInArc A B A')
    (hjB : ¬ sideInArc A B B') (hj0 : ¬ sideInArc A' B' 0)
    (ha' : sideInArc A' B' a') (hx : ClosedArc A B x) (hx' : ClosedArc A' B' x') (hxx : x ≠ x')
    (hui : ¬ sideInArc A B u) (huj : ¬ sideInArc A' B' u) :
    (sideInArc x x' u → sideInArc 0 a' u) ∧ (sideInArc x' x u → sideInArc a' 0 u) := by
  zufya
  obtain ⟨h1, h2⟩ := cyc_zero_out hBA hjA
  obtain ⟨h3, h4⟩ := cyc_zero_out hBA hjB
  zudre

  have hA'B' : A' < B' := by
    zuks

    unfold sideInArc at hj0
    grind
  have ha'' : A' < a' ∧ a' < B' := by unfold sideInArc at ha'; simp_all
  have hx'' : A' ≤ x' ∧ x' ≤ B' := by
    unfold ClosedArc sideInArc at hx'
    grind
  have huj' : u ≤ A' ∨ B' ≤ u := by
    unfold sideInArc at huj
    grind
  have ha'0 : 0 < a' := by_grind
  constructor
  · zuq
    zusg
    grind
  · zuq
    zusg
    grind

/-- **Domination when `a' = x'`** (keys rotated so that `a` is at `0`). -/
theorem cyc_dom_same {A B x k u : ℝ} (hA0 : 0 ≤ A) (hAB : A ≠ B) (hi : sideInArc A B 0)
    (hx : ClosedArc A B x) (hxk : x ≠ k) (hk : ¬ sideInArc A B k) (hui : ¬ sideInArc A B u) :
    (sideInArc x k u → sideInArc 0 k u) ∧ (sideInArc k x u → sideInArc k 0 u) := by
  zufya
  obtain ⟨h1, h2⟩ := cyc_zero_out hBA hk
  zudre

  have hk0 : ztkzl := by_linarith
  constructor
  · zuq
    zusg
    grind
  · zuq
    zusg
    grind

/-- A start or an end version of `cyc_nosep`: the start of an interval is on the side of its
interior points (with respect to two keys outside the interval). -/
theorem cyc_nosep_start {a x y A B : ℝ} (hy : sideInArc a x y) (hA : ¬ sideInArc a x A)
    (hB : ¬ sideInArc a x B) (haA : a ≠ A) (haB : a ≠ B) (hAB : A ≠ B) :
    sideInArc A B y ↔ sideInArc A B a := by
  rcases lt_or_gt_of_ne haA with h1 | h1 <;> rcases lt_or_gt_of_ne haB with h2 | h2 <;>
    rcases lt_or_gt_of_ne hAB with h3 | h3 <;>
    · unfold sideInArc at *
      grind

/-- A more thorough closing tactic for cyclic case analyses (nested disjunctions). -/
macro "cyc_close2" : tactic => `(tactic| (
  (try simp only [not_and_or, not_or, not_lt] at *) <;>
  (casesm* _ ∧ _, _ ∨ _) <;>
  first
  | linarith
  | (constructor! <;> linarith)
  | (left; constructor! <;> linarith) | (right; constructor! <;> linarith)
  | (left; linarith) | (right; linarith)
  | (right; left; linarith) | (right; right; linarith)
  | (left; left; linarith) | (left; right; linarith)
  | (right; left; constructor! <;> linarith) | (right; right; constructor! <;> linarith)
  | (left; left; constructor! <;> linarith) | (left; right; constructor! <;> linarith)))

/-- The part of an interval before one of its interior points is inside the interval. -/
theorem cyc_sub_arc {a b w z : ℝ} (hw : sideInArc a b w) (hz : sideInArc a w z) :
    sideInArc a b z := by
  unfold sideInArc at *
  grind

/-- Of two distinct interior points of an interval, one is before the other. -/
theorem cyc_split {a b y w : ℝ} (hy : sideInArc a b y) (hw : sideInArc a b w) (hyw : y ≠ w) :
    sideInArc a w y ∨ sideInArc a y w := by
  rcases lt_or_gt_of_ne hyw with h | h <;>
  · unfold sideInArc at *
    grind

/-- Two interior points of an interval: one is inside the part of the interval before the other. -/
theorem cyc_order {a b y w : ℝ} (hy : sideInArc a b y) (hw : sideInArc a b w) (hyw : y ≠ w) :
    (sideInArc a w y ∧ ∀ z, sideInArc a w z → sideInArc a b z) ∨
      (sideInArc a y w ∧ ∀ z, sideInArc a y z → sideInArc a b z) := by
  rcases cyc_split hy hw hyw with h | h
  · exact Or.inl ⟨h, fun z hz => cyc_sub_arc hw hz⟩
  · exact Or.inr ⟨h, fun z hz => cyc_sub_arc hy hz⟩

/-- A closed interval avoiding two keys lies on one side of them. -/
theorem cyc_closed_side {a b y w k k' : ℝ} (hy : sideInArc a b y)
    (hw : ClosedArc a b w) (hk : ¬ sideInArc a b k) (hk' : ¬ sideInArc a b k') (hkk : k ≠ k')
    (hwk : w ≠ k) (hwk' : w ≠ k') :
    sideInArc k k' w ↔ sideInArc k k' y := by
  have hyk : y ≠ k := by_grind
  have hyk' : y ≠ k' := by_grind
  rcases hw with hw | rfl | rfl
  · by_cases hyw : y = w
    · rw [hyw]
    rcases cyc_order hy hw hyw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (cyc_nosep h1 by_grind by_grind hwk hwk' hkk).symm
    · exact cyc_nosep h1 by_grind by_grind hyk hyk' hkk
  · exact (cyc_nosep_start hy hk hk' hwk hwk' hkk).symm
  · exact (cyc_nosep hy hk hk' hwk hwk' hkk).symm

/-- Two cyclic intervals with a common interior key and distinct starts: the start of one is
inside the other. -/
theorem cyc_overlap {a b a' b' y : ℝ} (hab : a ≠ b) (hab' : a' ≠ b') (haa : a ≠ a')
    (hy : sideInArc a b y) (hy' : sideInArc a' b' y) : sideInArc a b a' ∨ sideInArc a' b' a := by
  rcases lt_or_gt_of_ne haa with h1 | h1 <;> rcases lt_or_gt_of_ne hab with h2 | h2 <;>
    rcases lt_or_gt_of_ne hab' with h3 | h3 <;>
    · unfold sideInArc at *
      grind

/-- A key is strictly on one side when it avoids both ends. -/
theorem cyc_two {k k' x : ℝ} (hkk : k ≠ k') (hx : x ≠ k) (hx' : x ≠ k') :
    sideInArc k k' x ∨ sideInArc k' k x := by
  rcases cyc_cases (x := x) hkk with h | h | h | h
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-! ## Side counts -/

/-- The count test of a candidate chord: at least two exit chords of `R` attached strictly on each
side. -/
def CountOK (M : Model) (S : Set ztf) (R : Set Point) (k₁ k₂ : ℝ) : Prop :=
  2 ≤ (sideExits M S R k₁ k₂).ncard ∧ 2 ≤ (sideExits M S R k₂ k₁).ncard

/-- The side counts only depend on the cut keys inside the key interval. -/
theorem sideExits_mono {R : Set Point} {k₁ k₂ l₁ l₂ : ℝ}
    (h : ∀ u, M.IsCut S u → sideInArc k₁ k₂ u → sideInArc l₁ l₂ u) :
    sideExits M S R k₁ k₂ ⊆ sideExits M S R l₁ l₂ := by
  rintro c ⟨hc, p, t, hat, hin⟩
  exact ⟨hc, p, t, hat, h _ ztkjs hin⟩

/-- Domination of the count test. -/
theorem countOK_mono (hfin : S.Finite) {R : Set Point} {k₁ k₂ l₁ l₂ : ℝ}
    (h₁ : ∀ u, M.IsCut S u → sideInArc k₁ k₂ u → sideInArc l₁ l₂ u)
    (h₂ : ∀ u, M.IsCut S u → sideInArc k₂ k₁ u → sideInArc l₂ l₁ u)
    (hc : CountOK M S R k₁ k₂) : CountOK M S R l₁ l₂ := by
  have hf : ∀ a b : ℝ, (sideExits M S R a b).Finite := fun a b =>
    (hfin.subset (Merge.exitsIn_subset S R)).subset (sideExits_subset S R a b)
  exact ⟨hc.1.trans (ncard_le_ncard (sideExits_mono h₁) by_simp_all),
    hc.2.trans (ncard_le_ncard (sideExits_mono h₂) by_simp_all)⟩

/-! ## The pruning lemma -/

/-- The key of an attachment is in `[0, n)`. -/
theorem key_range {W : Polygon} {c : Set Point} {p : ℕ} {t : ℝ} (hA : SideAttach W c p t) :
    0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < W.n := by
  have hp : ztmrl := by exact_mod_cast hA.1
  zubkc

/-- Offsets are injective on `[0, n)`. -/
theorem off_inj {n g x y : ℝ} (_hg0 : 0 ≤ g) (_hgn : g < n) (hx0 : 0 ≤ x) (hxn : x < n)
    (hy0 : 0 ≤ y) (hyn : y < n) (h : off n g x = off n g y) : x = y := by
  zuhqx

/-- Rotation of a closed interval. -/
theorem closedArc_rot (hg0 : 0 ≤ g) (hgn : g < n) (ha0 : 0 ≤ a) (han : a < n)
    (hb0 : 0 ≤ b) (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) :
    ClosedArc a b x ↔ ClosedArc ztlrl ztlrm zthzb := by
  unfold ClosedArc
  zufoi
  constructor
  · grind
  · zuciz
    · simp_all
    · exact Or.inr (Or.inl (off_inj hg0 hgn hx0 hxn ha0 han h))
    · exact Or.inr (Or.inr (off_inj hg0 hgn hx0 hxn hb0 hbn h))

/-- An attachment of an admissible chord `e` attached at `A` and `A'` is `A` or `A'` (by key). -/
theorem attach_key_cases (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {pa pb p : ℕ}
    {ta tb t : ℝ} (hA : SideAttach M.W e pa ta) (hB : SideAttach M.W e pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) (h : SideAttach M.W e p t) :
    (p : ℝ) + t = pa + ta ∨ (p : ℝ) + t = pb + tb := by
  obtain ⟨a, b, hab, heq, -, hopen, -, -⟩ := hM.ends e he
  zvnbk at hA hB h
  have ha := hM.attach_endpoint hopen hA
  have hb := hM.attach_endpoint hopen hB
  have hx := hM.attach_endpoint hopen h
  zvnbo at hA hB h
  have key : ∀ (q : ℕ) (s : ℝ), SideAttach M.W e q s → sidePt M.W p t = sidePt M.W q s →
      (p : ℝ) + t = q + s := by
    intro q s hq hpt
    obtain ⟨h1, h2⟩ := attach_unique hM he h hq hpt
    simp_all
  grind

/-- **The pruning lemma.**  Let `Aᵢ = (aᵢ, bᵢ)` and `Aⱼ = (aⱼ, bⱼ)` be two distinct arcs of the
region `R` of the nonempty family `S`.  Let the admissible chord `e_a` be attached at `A`, with key
strictly inside `Aᵢ`, and at `A'`, and fail the count test; let the admissible chord `e_x` be
attached at `X`, with key in the closed arc `Aᵢ`, and at `X'`, with key in the closed arc `Aⱼ`, and
pass the count test.  If the key of `X` is neither that of `A` nor that of `A'`, then `A'` is not
inside `Aⱼ`, and the key of `X` is strictly on the side of `e_a` that contains the open arc
`Aⱼ`. -/
theorem prune (hM : WalkAx M) {S : Set ztf} (_hS : S ⊆ M.Adm) (hfin : S.Finite)
    (hne : S.Nonempty) {R : Set Point} {ai bi aj bj : ℝ} (hAi : M.IsArc S R ai bi)
    (hAj : M.IsArc S R aj bj) (hij : ai ≠ aj)
    {ea : Set Point} (hea : ea ∈ M.Adm) {pa pa' : ℕ} {ta ta' : ℝ}
    (hA : SideAttach M.W ea pa ta) (hA' : SideAttach M.W ea pa' ta')
    (hAA' : sidePt M.W pa ta ≠ sidePt M.W pa' ta') (hka : sideInArc ai bi ztbf)
    {ex : Set Point} (hex : ex ∈ M.Adm) {px px' : ℕ} {tx tx' : ℝ}
    (hX : SideAttach M.W ex px tx) (hX' : SideAttach M.W ex px' tx')
    (hXX' : sidePt M.W px tx ≠ sidePt M.W px' tx') (hkx : ClosedArc ai bi ztcat)
    (hkx' : ClosedArc aj bj ztdvt)
    (hgood : CountOK M S R ztcat ztdvt) (hbad : ¬ CountOK M S R ztbf ztdhw)
    (hxa : (px : ℝ) + tx ≠ pa + ta) (hxa' : (px : ℝ) + tx ≠ pa' + ta') :
    ¬ sideInArc aj bj ztdhw ∧ ∀ y, sideInArc aj bj y →
      (sideInArc ztbf ztdhw ztcat ↔ sideInArc ztbf ztdhw y) := by
  set n : ℝ := (M.W.n : ℝ) with hn
  set ka : ℝ := (pa : ℝ) + ta with hkad
  set ka' : ℝ := (pa' : ℝ) + ta' with hka'd
  set kx : ℝ := (px : ℝ) + tx with hkxd
  set kx' : ℝ := (px' : ℝ) + tx' with hkx'd
  obtain ⟨hka0, hkan⟩ := key_range hA
  obtain ⟨hka'0, hka'n⟩ := key_range hA'
  obtain ⟨hkx0, hkxn⟩ := key_range hX
  obtain ⟨hkx'0, hkx'n⟩ := key_range hX'
  obtain ⟨hcai, hcbi, hab⟩ := WalkAx.arc_cuts hne hAi
  obtain ⟨hcaj, hcbj, hab'⟩ := WalkAx.arc_cuts hne hAj
  obtain ⟨hai0, hain, hbi0, hbin, -, hnoi, -⟩ := hAi
  obtain ⟨haj0, hajn, hbj0, hbjn, -, hnoj, -⟩ := hAj
  have hkk := key_ne_of_attach hA hA' hAA'
  have hxx := key_ne_of_attach hX hX' hXX'
  -- the two open arcs are disjoint
  have hF1 : ¬ sideInArc ai bi aj := by_grind
  have hF1' : ¬ sideInArc ai bi bj := by_grind
  have hF1'' : ¬ sideInArc aj bj ai := by_grind
  have disj : ∀ z, sideInArc ai bi z → ¬ sideInArc aj bj z := by
    zumhs
    rcases cyc_overlap hab hab' hij h1 h2 with h | h
    · simp_all
    simp_all
  have hF2 : ¬ sideInArc aj bj ka := by_simp_all
  have hF4 : ¬ sideInArc ai bi kx' := by
    zuq
    rcases hkx' with h' | h' | h'
    · simp_all
    · simp_all
    simp_all
  -- rotation by `ka`
  have rot := fun {a b x : ℝ} (ha0 : 0 ≤ a) (han : a < n) (hb0 : 0 ≤ b) (hbn : b < n)
      (hx0 : 0 ≤ x) (hxn : x < n) =>
    sideInArc_rot (n := n) (g := ka) hka0 hkan ha0 han hb0 hbn hx0 hxn
  have crot := fun {a b x : ℝ} (ha0 : 0 ≤ a) (han : a < n) (hb0 : 0 ≤ b) (hbn : b < n)
      (hx0 : 0 ≤ x) (hxn : x < n) =>
    closedArc_rot (n := n) (g := ka) hka0 hkan ha0 han hb0 hbn hx0 hxn
  have o0 := WalkEmbed.off_self n ka
  have on0 : ∀ {x}, 0 ≤ x → 0 ≤ off n ka x := fun h => WalkEmbed.off_nonneg h hkan
  have onn : ∀ {x}, x < n → off n ka x < n := fun h => WalkEmbed.off_lt h hka0
  have oinj : ∀ {x y}, 0 ≤ x → x < n → 0 ≤ y → y < n → off n ka x = off n ka y → x = y :=
    (off_inj hka0 hkan)
  have hi' : sideInArc (off n ka ai) (off n ka bi) 0 := by
    rw [← o0]; exact (rot hai0 hain hbi0 hbin hka0 hkan).1 hka
  have habo := fun h => hab (oinj hai0 hain hbi0 hbin h)
  -- (a) `a'` is not inside `Aⱼ`
  have ha'j : ¬ sideInArc aj bj ka' := by
    intro ha'
    zuhrt

    · zubxr
      have hdom := cyc_dom_open ztmmu ztway ztwaz habo hi'
        zthts
        zthtt
        ztggc
        ztjco ztcru
        ztjch
        ztisq
        ztbhq
        ztfbr
      have := hdom.1 ((rot hkx0 hkxn hkx'0 hkx'n hu0 hun).1 h)
      zudbc
      zufem
    · zubxr
      have hdom := cyc_dom_open ztmmu ztway ztwaz habo hi'
        zthts
        zthtt
        ztggc
        ztjco ztcru
        ztjch
        ztisq
        ztbhq
        ztfbr
      have := hdom.2 ((rot hkx'0 hkx'n hkx0 hkxn hu0 hun).1 h)
      zudbc
      zufel
  -- (b) `x'` is not `a'`
  have hx'a' : kx' ≠ ka' := by
    zudii
    have hF4' : ¬ sideInArc ai bi ka' := by_grind
    zuhrt

    · zubxr
      have hdom := cyc_dom_same ztmmu habo hi'
        ztcru
        ztisp
        zthtu
        ztbhq
      zukue
      have := hdom.1 ((rot hkx0 hkxn hka'0 hka'n hu0 hun).1 h)
      zudbc
      zufem
    · zubxr
      have hdom := cyc_dom_same ztmmu habo hi'
        ztcru
        ztisp
        zthtu
        ztbhq
      zukue
      have := hdom.2 ((rot hka'0 hka'n hkx0 hkxn hu0 hun).1 h)
      zudbc
      zufel
  refine ⟨ha'j, fun y hy => ?_⟩
  -- (c) `x'`, hence `x`, is on the side of the open arc `Aⱼ`
  have hx'ka : kx' ≠ ka := by_grind
  have hside := cyc_closed_side hy hkx' hF2 ha'j hkk hx'ka hx'a'
  have hne' : ex ≠ ea := by
    zuq
    zvmwc at hX
    rcases attach_key_cases hM hea hA hA' hAA' hX with h | h
    · grind
    grind
  rcases cyc_two hkk hx'ka hx'a' with h | h
  · have h1 := same_side hM hea hex hne' hA hA' hAA' hX' hX h
    zuhih
    · grind
    grind
  · have h1 := same_side hM hea hex hne' hA' hA hAA'.symm hX' hX h
    zuhih
    · grind
    · constructor
      · grind
      · intro h3
        exfalso
        exact (sideInArc_swap hkk hx'ka hx'a').1 (hside.2 h3) h
open Relation
variable {Q : Polygon} {N : NF} {reg : ℕ → Set Point}
theorem cover {D : ℕ} (hT : Dec.RecTree N D) {k : ℕ} (hk : k < N.nChords) {r : ℕ}
    (hr : r < N.nRegions) : r ∈ N.lowSide k ∨ r ∈ N.highSide k := by
  have hdn := (hT.ends_lt k hk).2
  have hreach := hT.conn _ _ hdn hr
  clear hr
  induction hreach with
  | refl => exact Or.inl ReflTransGen.refl
  | @tail s s' _ hadj ih =>
    obtain ⟨i, hi, hh⟩ := hadj
    by_cases hik : i = k
    · subst hik
      rcases hh with ⟨-, h⟩ | ⟨h, -⟩
      · zvmzi; exact Or.inl ReflTransGen.refl
      · zvmzi; tauto
    · have hav : N.AdjAvoid k s s' := ⟨i, hi, hik, hh⟩
      rcases ih with h | h
      · exact Or.inl ztvsb
      · exact Or.inr ztvsb

/-- A point of the open part of a chord record. -/
theorem exists_chord_pt (hM : WalkAx M) (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) :
    ∃ z, z ∈ (N.chord i).toSet M Q ∧ z ∈ M.D := by
  have hc := hN.1.2.1 ztomc
  obtain ⟨a, b, -, heq, -, hopen, -, -⟩ := hM.ends _ hc
  refine ⟨Geometry.lerp a b ztcn, ?_, by_grind⟩
  zugdv

/-- A preconnected subset of `D \ c` meeting a component of `D \ c` lies in it. -/
theorem sub_comp {A : Set Point} {X : Set Point} (hX : IsPreconnected X) (hXA : X ⊆ A)
    {z w : Point} (hz : z ∈ X) (hzw : z ∈ connectedComponentIn A w) :
    X ⊆ connectedComponentIn A w := by
  rw [connectedComponentIn_eq hzw]
  exact hX.subset_connectedComponentIn hz hXA

/-- **Neighbours through another chord are in the same component.** -/
theorem adj_same_comp (hM : WalkAx M) (hN : IsNF M Q N) (hS : ChordSidesOK M Q N reg)
    (hR : ∀ r, r < N.nRegions → reg r ∈ M.regions ztdu) {k i : ℕ} (hk : k < N.nChords)
    (hi : i < N.nChords) (_hik : i ≠ k) (hne : (N.chord i).toSet M Q ≠ (N.chord k).toSet M Q)
    {w : Point} :
    reg (N.chord i).up ⊆ connectedComponentIn ztbfv w ↔
      reg (N.chord i).dn ⊆ connectedComponentIn ztbfv w := by
  zucev
  zuizl
  have hci : ztdjo := ztomc
  zufum
  obtain ⟨z, hzc, hzD⟩ := exists_chord_pt hM hN hi
  have hzc' : z ∉ c := fun h => hsys.inter_subset_compl hci hck hne by_simp_all hzD
  have hcl := hsys.isClosed_chord hck
  have hopen : ztsbs := hM.isOpen.sdiff hcl
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen z ⟨hzD, hzc'⟩
  obtain ⟨hup, hdn, hside⟩ := hS i hi
  zubxw
  set ε := min ztcop ztkia with hεdef
  zudpq
  obtain ⟨hu, hd⟩ := hε ε hε0 by_grind
  have hbu : (ztgd : Point) ∈ ball z ρ := by
    zufv
    zufpu
    grind
  have hbd : (ztfr : Point) ∈ ball z ρ := by
    zufv
    zuens
    grind
  have hregsub : zteil := fun r hr x hx =>
    ⟨(regionsIn_subset ztdhl hx).1, fun hxc => (regionsIn_subset ztdhl hx).2 by_grind⟩
  have hballP := (convex_ball z ρ).isPreconnected
  constructor
  · zuq
    have hb : ztplp := sub_comp hballP hball hbu (h hu)
    exact sub_comp (regionsIn_isPreconnected zttmo) by_grind hd (hb hbd)
  · zuq
    have hb : ztplp := sub_comp hballP hball hbd (h hd)
    exact sub_comp (regionsIn_isPreconnected zttmp) by_grind hu (hb hbu)

/-- The components of `D \ c` of the regions below and above a chord `c`. -/
theorem comps_of (hM : WalkAx M) (hN : IsNF M Q N) (hS : ChordSidesOK M Q N reg)
    (hR : ∀ r, r < N.nRegions → reg r ∈ M.regions ztdu) {k : ℕ} (hk : k < N.nChords) :
    ∃ zd zu : Point,
      reg (N.chord k).dn ⊆ connectedComponentIn ztbfv zd ∧
      reg (N.chord k).up ⊆ connectedComponentIn ztbfv zu ∧
      Disjoint (connectedComponentIn ztbfv zd)
        (connectedComponentIn ztbfv zu) := by
  zucev
  zuizl
  zufum
  obtain ⟨z, hzc, hzD⟩ := exists_chord_pt hM hN hk
  obtain ⟨hup, hdn, hside⟩ := hS k hk
  zubxw
  have hsub : ({c} : Set _) ⊆ N.F M Q := singleton_subset_iff.2 hck
  obtain ⟨ε₁, hε₁, hsep⟩ := hsys.chord_separates_in hsub ztmmn hzc hzD
  set ε := min ztcop (ε₁ / 2) with hεdef
  zusv
  obtain ⟨hu, hd⟩ := hε ε hε0 ztyrj
  obtain ⟨hu', hd', hne⟩ := hsep ε hε0 (lt_of_le_of_lt ztgh by_linarith)
  have hfe : freeIn M.D {c} = M.D \ c := by ext w; zunjh
  rw [hfe] at hu' hd' hne
  have hregsub : zteil := fun r hr x hx =>
    ⟨(regionsIn_subset ztdhl hx).1, fun hxc => (regionsIn_subset ztdhl hx).2 by_grind⟩
  refine ⟨ztfr, ztgd,
    (regionsIn_isPreconnected zttmo).subset_connectedComponentIn hd by_grind,
    (regionsIn_isPreconnected zttmp).subset_connectedComponentIn hu by_grind,
    components_disjoint ztnr⟩

/-- **The regions of the low side lie in the component of the region below the chord** (and
those of the high side in the component of the region above). -/
theorem side_sub (hM : WalkAx M) (hN : IsNF M Q N) (hS : ChordSidesOK M Q N reg)
    (hR : ∀ r, r < N.nRegions → reg r ∈ M.regions ztdu)
    (hinj : ∀ i i', i < N.nChords → i' < N.nChords →
      (N.chord i).toSet M Q = (N.chord i').toSet M Q → i = i')
    {k : ℕ} (hk : k < N.nChords) {w : Point} {r₀ : ℕ}
    (h₀ : reg r₀ ⊆ connectedComponentIn ztbfv w) {r : ℕ}
    (hr : ReflTransGen ztqai r₀ r) :
    reg r ⊆ connectedComponentIn ztbfv w := by
  induction hr with
  | refl => exact h₀
  | @tail s s' _ hadj ih =>
    obtain ⟨i, hi, hik, hh⟩ := hadj
    have hne : (N.chord i).toSet M Q ≠ (N.chord k).toSet M Q := by_grind
    have key := adj_same_comp hM hN hS hR hk hi hik hne (w := w)
    rcases hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp_all
    · simp_all

/-- **Deciding the side of a region.**  Let the walk position `(p, t)` inside an edge face the
region `reg r`, and the position `(p₀, t₀)` inside an edge face the region below the chord `k`.
If their keys are strictly inside the same one of the two key intervals cut by the attachments
of the chord, `r` is on the low side of `k`; if they are strictly inside different ones, `r` is on
the high side. -/
theorem decide_side (hGM : GoodModel M) (hN : IsNF M Q N) {D : ℕ} (hT : Dec.RecTree N D)
    (hcorr : RegionCorr M Q N reg) (hS : ChordSidesOK M Q N reg)
    {k : ℕ} (hk : k < N.nChords) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W ztbpa pa ta)
    (hB : SideAttach M.W ztbpa pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb)
    {r : ℕ} (hr : r < N.nRegions) {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht : 0 < t) (ht1 : t < 1)
    (hf : M.Faces p t ztcz) {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < M.W.n) (ht₀ : 0 < t₀)
    (ht₀1 : t₀ < 1) (hf₀ : M.Faces p₀ t₀ ztpdm) :
    ((sideInArc ztbf ztbd ztk ∧ sideInArc ztbf ztbd zthw) ∨
        (sideInArc ztbd ztbf ztk ∧ sideInArc ztbd ztbf zthw) →
      r ∈ N.lowSide k) ∧
    ((sideInArc ztbf ztbd ztk ∧ sideInArc ztbd ztbf zthw) ∨
        (sideInArc ztbd ztbf ztk ∧ sideInArc ztbf ztbd zthw) →
      r ∈ N.highSide k) := by
  zubm
  have hR := hcorr.1
  zucev
  zufum
  have hcA := hN.1.2.1 hck
  obtain ⟨K₁, K₂, hK, ⟨c₁, hK₁⟩, ⟨c₂, hK₂⟩, hsec₁, hsec₂⟩ := hM.split hcA hA hB hAB
  obtain ⟨zd, zu, hdK, huK, hdisj⟩ := comps_of hM hN hS hR hk
  have hregsub : zteil := fun r hr x hx =>
    ⟨(regionsIn_subset ztdhl hx).1, fun hxc => (regionsIn_subset ztdhl hx).2 by_grind⟩
  obtain ⟨hup, hdn, -⟩ := hS k hk
  -- a region faced at a key strictly inside a side lies in that side's component
  have inK : ∀ r', r' < N.nRegions → ∀ (q : ℕ) (s : ℝ), q < M.W.n → 0 < s → s < 1 →
      M.Faces q s (reg r') → ∀ (K : Set Point) (w : Point), K = connectedComponentIn ztjq w →
      SideSectorIn M.W K q s → reg r' ⊆ K := by
    intro r' hr' q s hq hs hs1 hfq K w hKw hsec
    obtain ⟨x, hx1, hx2⟩ := hM.faces_meets hq ⟨hs, hs1⟩ hsec hfq
    rw [hKw] at hx2 ⊢
    exact sub_comp (regionsIn_isPreconnected zttmr) by_grind hx1 hx2
  have hlow := fun r' (h : r' ∈ N.lowSide k) =>
    side_sub hM hN hS hR hN.2.1 hk hdK h
  have hhigh := fun r' (h : r' ∈ N.highSide k) =>
    side_sub hM hN hS hR hN.2.1 hk huK h
  have hne := fun r' hr' =>
    regionsIn_nonempty zttmr
  -- two regions in a common component `K`: if one is on the low side, so is the other, etc.
  have ceq : ∀ {x w w' : Point}, x ∈ connectedComponentIn _ w →
      x ∈ connectedComponentIn _ w' →
      connectedComponentIn _ w = connectedComponentIn ztjq w' := fun h h' =>
    (connectedComponentIn_eq h).trans (connectedComponentIn_eq h').symm
  have same : ∀ K : Set Point, ∀ w, K = connectedComponentIn ztjq w →
      reg r ⊆ K → reg (N.chord k).dn ⊆ K → r ∈ N.lowSide k := by
    intro K w hKw hrK hdK'
    zuhig
    · zubh
    · exfalso
      have h1 := hhigh r h
      zuctc

      -- `K` is the component of `zu` (through `x`) and of `zd` (through `y`)
      have e1 : connectedComponentIn _ zu = K :=
        (ceq ztvsg ztrro).trans hKw.symm
      have e2 : ztsfp :=
        (ceq ztqpx (hKw ▸ hdK' hy)).trans hKw.symm
      exact hdisj.notMem_of_mem_left ztqpx (by rw [e1, ← e2]; exact hdK hy)
  have diff : ∀ K K' : Set Point, ∀ w w', K = connectedComponentIn ztjq w →
      K' = connectedComponentIn ztjq w' → Disjoint K K' →
      reg r ⊆ K → reg (N.chord k).dn ⊆ K' → r ∈ N.highSide k := by
    intro K K' w w' hKw hKw' hKK hrK hdK'
    zuhig
    · exfalso
      have h1 := hlow r h
      zuctc

      have e1 : ztsfp :=
        (ceq ztvsg ztrro).trans hKw.symm
      have e2 : connectedComponentIn _ zd = K' :=
        (ceq ztqpx (hKw' ▸ hdK' hy)).trans hKw'.symm
      exact hKK.notMem_of_mem_left (e1 ▸ hdK hy) (e2 ▸ hdK hy)
    omega
  have hdisj12 : Disjoint K₁ K₂ := by
    zuczz
  constructor
  · zuwt
    · exact same K₁ c₁ hK₁ (inK r hr p t hp ht ht1 hf K₁ c₁ hK₁ (hsec₁ p hp t ht.le ht1 h1))
        ztilh
    · exact same K₂ c₂ hK₂ ztfcg
        (inK _ hdn p₀ t₀ hp₀ ht₀ ht₀1 hf₀ K₂ c₂ hK₂ by_grind)
  · zuwt
    · exact diff K₁ K₂ c₁ c₂ hK₁ hK₂ hdisj12
        (inK r hr p t hp ht ht1 hf K₁ c₁ hK₁ by_grind)
        (inK _ hdn p₀ t₀ hp₀ ht₀ ht₀1 hf₀ K₂ c₂ hK₂ (hsec₂ p₀ hp₀ t₀ ht₀.le ht₀1 h2))
    · exact diff K₂ K₁ c₂ c₁ hK₂ hK₁ hdisj12.symm
        ztfcg
        ztilh
end
end Restore
namespace ShotList
@[expose] public section
open Chazelle.Chain (sideInArc)

/-- `k` lies in the closed cyclic interval `[a, b]` (the whole circle when `a = b`). -/
def CIn (a b k : ℝ) : Prop := sideInArc a b k ∨ k = a ∨ k = b

/-- **The pieces of the arc `[a, b]` outside the open hole `(x, y)`**, from the keys
`ka kb kx ky` of the four ends. -/
noncomputable def cutK {α : Type} (ka kb kx ky : ℝ) (a b x y : α) : List zthln := by
  classical
  exact
    if sideInArc kx ky ka then
      (if sideInArc ka kb ky then
        (if sideInArc ky kb kx then [ztuen] else [ztokh])
      else [])
    else if sideInArc ka kb kx then
      (a, x) :: (if sideInArc kx kb ky then [ztokh] else [])
    else if kx = ka then
      (if sideInArc ka kb ky then [ztokh] else [])
    else [ztvk]

/-- **The pieces of the arc `[a, b]` outside the open hole `(x, y)`.** -/
noncomputable def cut1 {α : Type} (key : α → ℝ) (a b x y : α) : List zthln :=
  cutK ztbom ztcah ztbhv ztbnb a b x y

/-- The pieces of `cut1`, as key pairs. -/
theorem cut1_cases {α : Type} (key : α → ℝ) (a b x y : α) {u v : α}
    (h : ztnz ∈ cut1 key a b x y) :
    (sideInArc ztbhv ztbnb ztbom ∧ sideInArc ztbom ztcah ztbnb ∧
        sideInArc ztbnb ztcah ztbhv ∧ u = y ∧ v = x) ∨
      (sideInArc ztbhv ztbnb ztbom ∧ sideInArc ztbom ztcah ztbnb ∧
        ¬ sideInArc ztbnb ztcah ztbhv ∧ u = y ∧ v = b) ∨
      (¬ sideInArc ztbhv ztbnb ztbom ∧ sideInArc ztbom ztcah ztbhv ∧ u = a ∧ v = x) ∨
      (¬ sideInArc ztbhv ztbnb ztbom ∧ sideInArc ztbom ztcah ztbhv ∧
        sideInArc ztbhv ztcah ztbnb ∧ u = y ∧ v = b) ∨
      (¬ sideInArc ztbhv ztbnb ztbom ∧ ¬ sideInArc ztbom ztcah ztbhv ∧
        key x = key a ∧ sideInArc ztbom ztcah ztbnb ∧ u = y ∧ v = b) ∨
      (¬ sideInArc ztbhv ztbnb ztbom ∧ ¬ sideInArc ztbom ztcah ztbhv ∧
        key x ≠ key a ∧ u = a ∧ v = b) := by
  unfold cut1 cutK at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;>
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-! ## Transfer to ranks

A statement built from order comparisons of five reals holds as soon as it holds for their ranks
(naturals below `5`), where it is decided. -/

/-- The cyclic interval test on naturals. -/
def siaN (a b k : ℕ) : Bool := if a < b then a < k && k < b else a < k || k < b

/-- The closed cyclic interval test on naturals. -/
def CInN (a b k : ℕ) : Bool := siaN a b k || k == a || k == b

/-- The rank of `v` among the elements of `L`. -/
noncomputable def rank (L : List ℝ) (v : ℝ) : ℕ := (L.filter (fun w => decide (w < v))).length
variable {L : List ℝ} {v w : ℝ} {a b k : ℝ}
theorem rank_lt_of_lt (hv : v ∈ L) (h : v < w) : rank L v < rank L w := by
  unfold rank
  induction L with
  | nil => simp at hv
  | cons z L ih =>
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hv with rfl | hv'
    · simp only [lt_irrefl, decide_false, h, decide_true]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have : (L.filter (fun u => decide (u < v))).length ≤
          (L.filter (fun u => decide ztoiz)).length :=
        List.Sublist.length_le (List.monotone_filter_right L (fun u hu => by
          grind))
      omega
    · grind
theorem rank_lt_iff (hv : v ∈ L) (hw : w ∈ L) :
    v < w ↔ rank L v < rank L w := by
  constructor
  · exact rank_lt_of_lt hv
  · zuq
    zudxc
    rcases (not_lt.1 h').lt_or_eq with h'' | h''
    · exact absurd (rank_lt_of_lt hw h'') by_omega
    simp_all
theorem rank_eq_iff (hv : v ∈ L) (hw : w ∈ L) :
    v = w ↔ rank L v = rank L w := by
  constructor
  · simp_all
  · zuq
    rcases lt_trichotomy v w with h' | h' | h'
    · exact absurd h ((rank_lt_of_lt hv h').ne)
    · zuclh
    · exact absurd h ((rank_lt_of_lt hw h').ne')
theorem rank_lt_length (L : List ℝ) (v : ℝ) : rank L v ≤ L.length :=
  List.length_filter_le _ _
theorem sideInArc_rank (ha : a ∈ L) (hb : b ∈ L) (hk : k ∈ L) :
    sideInArc a b k ↔ siaN ztogt ztogu ztogv = true := by
  unfold sideInArc siaN
  have e1 := rank_lt_iff ha hb
  have e2 := rank_lt_iff ha hk
  have e3 := rank_lt_iff hk hb
  simp_all
theorem cIn_rank (ha : a ∈ L) (hb : b ∈ L) (hk : k ∈ L) :
    CIn a b k ↔ CInN ztogt ztogu ztogv = true := by
  unfold CIn CInN
  rw [sideInArc_rank ha hb hk, rank_eq_iff hk ha, rank_eq_iff hk hb]
  grind

/-! ## The order facts, decided on ranks -/

/-- Boolean implication. -/
def imp (p q : Bool) : Bool := !p || q

/-- P1 on ranks: each piece lies in the arc and outside the open hole. -/
def P1N (A B X Y K : ℕ) : Bool :=
  imp zttea (
    imp (siaN X Y A && siaN A B Y && siaN Y B X && CInN Y X K) ztcek &&
    imp (siaN X Y A && siaN A B Y && !siaN Y B X && CInN Y B K) ztcek &&
    imp (!siaN X Y A && siaN A B X && CInN A X K) ztcek &&
    imp (!siaN X Y A && siaN A B X && siaN X B Y && CInN Y B K) ztcek &&
    imp (!siaN X Y A && !siaN A B X && X == A && siaN A B Y && CInN Y B K)
      ztcek &&
    imp (!siaN X Y A && !siaN A B X && X != A && CInN A B K) (!siaN X Y K))

/-- P2 on ranks: a key of the arc outside the closed hole lies in a piece. -/
def P2N (A B X Y K : ℕ) : Bool :=
  imp (X != Y && CInN A B K && !CInN X Y K) (
    imp (siaN X Y A) (siaN A B Y && imp (siaN Y B X) (CInN Y X K) &&
      imp (!siaN Y B X) (CInN Y B K)) &&
    imp (!siaN X Y A && siaN A B X) (CInN A X K || (siaN X B Y && CInN Y B K)) &&
    imp (!siaN X Y A && !siaN A B X && X == A) (siaN A B Y && CInN Y B K))
theorem p1N_all : ∀ A, A < 6 → ∀ B, B < 6 → ∀ X, X < 6 → ∀ Y, Y < 6 → ∀ K, K < 6 →
    P1N A B X Y K = true := by_decide

/-- P0 on ranks: the open interval of a piece lies in the open interval of the arc. -/
def P0N (A B X Y K : ℕ) : Bool :=
  imp zttea (
    imp (siaN X Y A && siaN A B Y && siaN Y B X && siaN Y X K) ztfun &&
    imp (siaN X Y A && siaN A B Y && siaN Y B K) ztfun &&
    imp (!siaN X Y A && siaN A B X && siaN A X K) ztfun &&
    imp (!siaN X Y A && siaN A B X && siaN X B Y && siaN Y B K) ztfun &&
    imp (!siaN X Y A && !siaN A B X && siaN A B Y && siaN Y B K) ztfun)
theorem p0N_all : ∀ A, A < 6 → ∀ B, B < 6 → ∀ X, X < 6 → ∀ Y, Y < 6 → ∀ K, K < 6 →
    P0N A B X Y K = true := by_decide
theorem p2N_all : ∀ A, A < 6 → ∀ B, B < 6 → ∀ X, X < 6 → ∀ Y, Y < 6 → ∀ K, K < 6 →
    P2N A B X Y K = true := by_decide

/-! ## The order facts on reals -/
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- P1 on reals. -/
theorem p1R (a b x y k : ℝ) (hxy : x ≠ y) :
    (sideInArc x y a → sideInArc a b y → sideInArc y b x → CIn y x k →
        CIn a b k ∧ ¬ sideInArc x y k) ∧
    (sideInArc x y a → sideInArc a b y → ¬ sideInArc y b x → CIn y b k →
        CIn a b k ∧ ¬ sideInArc x y k) ∧
    (¬ sideInArc x y a → sideInArc a b x → CIn a x k → CIn a b k ∧ ¬ sideInArc x y k) ∧
    (¬ sideInArc x y a → sideInArc a b x → sideInArc x b y → CIn y b k →
        CIn a b k ∧ ¬ sideInArc x y k) ∧
    (¬ sideInArc x y a → ¬ sideInArc a b x → x = a → sideInArc a b y → CIn y b k →
        CIn a b k ∧ ¬ sideInArc x y k) ∧
    (¬ sideInArc x y a → ¬ sideInArc a b x → x ≠ a → CIn a b k → ¬ sideInArc x y k) := by
  set L : List ℝ := [a, b, x, y, k] with hL
  have ma : a ∈ L := by zunlc
  have mb : b ∈ L := by zunlc
  have mx : x ∈ L := by zunlc
  have my : y ∈ L := by zunlc
  have mk : k ∈ L := by zunlc
  have hlen : L.length = 5 := rfl
  have hP := p1N_all ztogt (by have := rank_lt_length L a; omega)
    ztogu (by have := rank_lt_length L b; omega) (rank L x)
    (by have := rank_lt_length L x; omega) (rank L y) (by have := rank_lt_length L y; omega)
    ztogv (by have := rank_lt_length L k; omega)
  simp only [ne_eq] at hxy ⊢
  zuedt
  rw [sideInArc_rank mx my ma, sideInArc_rank ma mb my, sideInArc_rank my mb mx,
    cIn_rank my mx mk, cIn_rank ma mb mk, sideInArc_rank mx my mk, cIn_rank my mb mk,
    sideInArc_rank ma mb mx, cIn_rank ma mx mk, sideInArc_rank mx mb my, rank_eq_iff mx ma]
  generalize rank L a = A at *
  generalize rank L b = B at *
  generalize rank L x = X at *
  generalize rank L y = Y at *
  generalize rank L k = K at *
  rw [show ztted = ztmyi from propext beq_iff_eq.symm] at *
  zuceq
  simp only [P1N, imp, bne] at hP
  generalize siaN X Y A = s1 at *
  generalize siaN A B Y = s2 at *
  generalize siaN Y B X = s3 at *
  generalize CInN Y X K = s4 at *
  generalize CInN A B K = s5 at *
  generalize siaN X Y K = s6 at *
  generalize CInN Y B K = s7 at *
  generalize siaN A B X = s8 at *
  generalize CInN A X K = s9 at *
  generalize siaN X B Y = s10 at *
  generalize (X == A) = e1 at *
  generalize (X == Y) = e2 at *
  have he2 : e2 = false := by_simp_all
  subst he2
  revert hP
  revert s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 e1
  decide

/-- The ranks of five reals, as a transfer package. -/
theorem ranks5 (a b x y k : ℝ) : ∃ L : List ℝ, a ∈ L ∧ b ∈ L ∧ x ∈ L ∧ y ∈ L ∧ k ∈ L ∧
    rank L a < 6 ∧ rank L b < 6 ∧ rank L x < 6 ∧ rank L y < 6 ∧ rank L k < 6 := by
  refine ⟨[a, b, x, y, k], by_simp, by_simp, by_simp, by_simp, by_simp, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · have := rank_lt_length [a, b, x, y, k]; simp only [List.length_cons, List.length_nil] at this
    grind
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- P0 on reals. -/
theorem p0R (a b x y k : ℝ) (hxy : x ≠ y) :
    (sideInArc x y a → sideInArc a b y → sideInArc y b x → sideInArc y x k → sideInArc a b k) ∧
    (sideInArc x y a → sideInArc a b y → sideInArc y b k → sideInArc a b k) ∧
    (¬ sideInArc x y a → sideInArc a b x → sideInArc a x k → sideInArc a b k) ∧
    (¬ sideInArc x y a → sideInArc a b x → sideInArc x b y → sideInArc y b k →
      sideInArc a b k) ∧
    (¬ sideInArc x y a → ¬ sideInArc a b x → sideInArc a b y → sideInArc y b k →
      sideInArc a b k) := by
  zubgw
  have hP := p0N_all _ ra _ rb _ rx _ ry _ rk
  zujoq
  zuedt
  rw [sideInArc_rank mx my ma, sideInArc_rank ma mb my, sideInArc_rank my mb mx,
    sideInArc_rank my mx mk, sideInArc_rank ma mb mk, sideInArc_rank my mb mk,
    sideInArc_rank ma mb mx, sideInArc_rank ma mx mk, sideInArc_rank mx mb my]
  generalize rank L a = A at *
  generalize rank L b = B at *
  generalize rank L x = X at *
  generalize rank L y = Y at *
  generalize rank L k = K at *
  zuceq
  simp only [P0N, imp, bne] at hP
  grind
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- P2 on reals. -/
theorem p2R (a b x y k : ℝ) (hxy : x ≠ y) (hk : CIn a b k) (hk' : ¬ CIn x y k) :
    (sideInArc x y a → sideInArc a b y ∧ (sideInArc y b x → CIn y x k) ∧
      (¬ sideInArc y b x → CIn y b k)) ∧
    (¬ sideInArc x y a → sideInArc a b x → CIn a x k ∨ (sideInArc x b y ∧ CIn y b k)) ∧
    (¬ sideInArc x y a → ¬ sideInArc a b x → x = a → sideInArc a b y ∧ CIn y b k) := by
  zubgw
  have hP := p2N_all _ ra _ rb _ rx _ ry _ rk
  zujoq
  zuedt
  rw [cIn_rank ma mb mk] at hk
  rw [cIn_rank mx my mk] at hk'
  rw [sideInArc_rank mx my ma, sideInArc_rank ma mb my, sideInArc_rank my mb mx,
    cIn_rank my mx mk, cIn_rank my mb mk, sideInArc_rank ma mb mx, cIn_rank ma mx mk,
    sideInArc_rank mx mb my, rank_eq_iff mx ma]
  generalize rank L a = A at *
  generalize rank L b = B at *
  generalize rank L x = X at *
  generalize rank L y = Y at *
  generalize rank L k = K at *
  rw [show ztted = ztmyi from propext beq_iff_eq.symm] at *
  zuceq
  simp only [P2N, imp, bne] at hP
  grind

/-! ## The pieces of one hole -/
section Generic
variable {α : Type} (key : α → ℝ)
variable {a b x y : α} {hs : List (α × α)}
/-- **P0**: the open interval of a piece lies in the open interval of the arc. -/
theorem cut1_open (hxy : key x ≠ key y) {u v : α}
    (h : ztnz ∈ cut1 key a b x y) {k : ℝ} (hk : sideInArc ztvxp ztjzk k) :
    sideInArc ztbom ztcah k := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := p0R ztbom ztcah ztbhv ztbnb k hxy
  rcases cut1_cases key a b x y h with
    ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ |
    ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, h3, h4, rfl, rfl⟩ | ⟨h1, h2, h3, rfl, rfl⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  omega

/-- **P1**: a piece lies in the arc and outside the open hole. -/
theorem cut1_sub (hxy : key x ≠ key y) {u v : α}
    (h : ztnz ∈ cut1 key a b x y) {k : ℝ} (hk : CIn ztvxp ztjzk k) :
    CIn ztbom ztcah k ∧ ¬ sideInArc ztbhv ztbnb k := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := p1R ztbom ztcah ztbhv ztbnb k hxy
  rcases cut1_cases key a b x y h with
    ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ |
    ⟨h1, h2, h3, rfl, rfl⟩ | ⟨h1, h2, h3, h4, rfl, rfl⟩ | ⟨h1, h2, h3, rfl, rfl⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-- **P2**: a key of the arc outside the closed hole lies in a piece. -/
theorem cut1_cover (hxy : key x ≠ key y) {k : ℝ} (hk : CIn ztbom ztcah k)
    (hk' : ¬ CIn ztbhv ztbnb k) :
    ∃ uv ∈ cut1 key a b x y, CIn ztmlx ztmly k := by
  obtain ⟨q1, q2, q3⟩ := p2R ztbom ztcah ztbhv ztbnb k hxy hk hk'
  unfold cut1 cutK
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-! ## Several holes -/

/-- **The pieces of an arc after a list of holes**, cut one after the other. -/
noncomputable def leaves : List zthln → α × α → List zthln
  | [], p => [p]
  | h :: hs, p => (cut1 key p.1 p.2 h.1 h.2).flatMap (fun q => leaves hs q)

/-- The holes are proper (distinct end keys). -/
def HolesOK (hs : List zthln) : Prop := ∀ h ∈ hs, key h.1 ≠ key h.2

/-- **P0 for several holes.** -/
theorem leaves_open (hh : HolesOK key hs) {p uv : α × α}
    (h : uv ∈ leaves key hs p) {k : ℝ} (hk : sideInArc ztmlx ztmly k) :
    sideInArc ztqsi ztqsj k := by
  induction hs generalizing p with
  | nil => simp only [leaves, List.mem_singleton] at h; subst h; exact hk
  | cons g hs ih =>
    zudce

    exact cut1_open key ztoat hq
      (ih (fun h' hm => hh h' by_simp_all) hq')

/-- **P1 for several holes.** -/
theorem leaves_sub (hh : HolesOK key hs) {p uv : α × α}
    (h : uv ∈ leaves key hs p) {k : ℝ} (hk : CIn ztmlx ztmly k) :
    CIn ztqsi ztqsj k ∧ ∀ g ∈ hs, ¬ sideInArc ztvxn ztvxo k := by
  induction hs generalizing p with
  | nil =>
    simp only [leaves, List.mem_singleton] at h; subst h
    zufeo
  | cons g hs ih =>
    zudce

    obtain ⟨h1, h2⟩ := ih ztnyw hq'
    obtain ⟨h3, h4⟩ := cut1_sub key ztoat hq h1
    refine ⟨h3, fun g' hg' => ?_⟩
    rcases List.mem_cons.1 hg' with rfl | hg'
    · zulyj
    · grind

/-- **P2 for several holes.** -/
theorem leaves_cover (hh : HolesOK key hs) {p : α × α} {k : ℝ}
    (hk : CIn ztqsi ztqsj k) (hk' : ∀ g ∈ hs, ¬ CIn ztvxn ztvxo k) :
    ∃ uv ∈ leaves key hs p, CIn ztmlx ztmly k := by
  induction hs generalizing p with
  | nil => exact ⟨p, by_tauto, hk⟩
  | cons g hs ih =>
    obtain ⟨q, hq, hq'⟩ := cut1_cover key ztoat hk by_grind
    obtain ⟨uv, huv, huv'⟩ := ih ztnyw hq'
      by_grind
    exact ⟨uv, by simp only [leaves, List.mem_flatMap]; grind, huv'⟩
end Generic
end
end ShotList
end Chazelle.Core
section
set_option hygiene false
local macro "zqpj" : tactic => `(tactic| (set v := M.W.vtx p with hv; have hwa : M.wa p = v := rfl; set B : Point := M.wb p - v with hB; set a := M.W.vtx ((p + M.W.n - 1) % M.W.n) with ha; set A : Point := a - v with hA))
local macro "zqpk" : tactic => `(tactic| (obtain ⟨e, hev, hey, hce, hopen, heD, -⟩ := hM.attach_other_end ztlz hA; obtain ⟨e', hev', hey', hce', hopen', heD', -⟩ := hM.attach_other_end ztesy hA'; set v := sidePt M.W p t))
local macro "zqpl" : tactic => `(tactic| (intro pe pw te tw hBe hBe' hBw hBw'; have hpe := hothe pe te hBe hBe'; have hpw := hothw pw tw hBw hBw'; obtain ⟨py, ty, hpy, hty0, hty1, hRf⟩ := hM.exists_faces hF hfin hR))
local macro "zqpm" : tactic => `(tactic| (rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_lt, abs_lt, hx1, hx2]; refine ⟨⟨by_linarith, by_linarith⟩, ⟨by_linarith, by_linarith⟩⟩))
local macro "zqpn" : tactic => `(tactic| simp only [mem_ofPred_eq, one_mul])
local macro "zqpo" : tactic => `(tactic| (zvmxy; exact hopen' _ ⟨div_pos by_linarith by_linarith, (div_lt_one by_linarith).2 by_linarith⟩))
local macro "zqpp" : tactic => `(tactic| (zvmxy; exact hopen _ ⟨div_pos by_linarith by_linarith, (div_lt_one by_linarith).2 by_linarith⟩))
local macro "zqpq" : tactic => `(tactic| (refine ⟨rfl, ?_⟩; have hp := hAe.1; have hv0 := Chazelle.Chain.sidePt_zero M.W p; obtain ⟨r, hr, hfree⟩ := hM.local_free hF hfin hp))
local macro "zqps" : tactic => `(tactic| (have q1 := mul_le_mul_of_nonneg_left a1 hδ0.le; have q2 := mul_le_mul_of_nonneg_left a2 hδ0.le; have q3 := mul_le_mul_of_nonneg_left a3 hδ0.le; have q4 := mul_le_mul_of_nonneg_left a4 hδ0.le))
local macro "zqpt" : tactic => `(tactic| (simp only [mem_ofPred_eq, one_mul]; zunvn; rw [hwbq, hwaq] at h1; exact h1))
local macro "zqpu" : tactic => `(tactic| (intro h; have := (sideKey_inj hty0.le hty1 le_rfl zero_lt_one (by zvncl; exact h)).2; linarith))
local macro "zqpv" : tactic => `(tactic| (zuoru; simp only [sideCross, Prod.fst_sub, Prod.snd_sub, hzey, sub_self, mul_zero, zero_sub]))
local macro "zqpw" : tactic => `(tactic| (zunvn; simp only [sideCross, Prod.fst_sub, Prod.snd_sub, hzwy, sub_self, zero_mul, sub_zero]))
local macro "zqpx" : tactic => `(tactic| (zvnme; rintro z ⟨s, hs0, hs1, rfl⟩; simp only; nlinarith))
local macro "zqpy" : tactic => `(tactic| refine Tie.cyc_cover hab hac hbc hya ztrqf ztrqf)
local macro "zqpz" : tactic => `(tactic| (simp only [Geometry.lerp_snd]; grind))
set_option hygiene true

/-!
# WP-C (BuildNF): two chords attached at one walk position (the tie fact)

`BuildNF` sorts the `2K` attachment positions of the chords along the walk and runs a stack over
them (parenthesis structure).  Two chords of one family can be attached at the **same** walk
position (review finding B2): a walk vertex `v` whose left sector contains both horizontal
directions, with one chord leaving `v` eastward and one westward.  Their keys tie, and
`AttachFaceSpec`/`UpSideSpec` do not apply.  This file settles the tie.

## Results (for every walk-axiom model, hence every good model)

* `WalkAx.no_cross`: two distinct chords of an admissible family never cross on the walk (the
  attachment keys of one chord lie in one closed arc of the other), which makes the sorted
  attachment sequence a parenthesis word.
* `WalkAx.tie_pair`, `WalkAx.tie_shape`, `WalkAx.attach_east_unique`, `WalkAx.attach_west_unique`:
  if two distinct chords of `F` are attached at the same position `(p, t)`, they leave its point
  `v` in opposite horizontal directions, `t = 0` (a walk vertex), the walk edge `p` leaving it is
  not horizontal, and every chord of `F` attached there is one of the two (two chords attached at
  one position with the same direction are equal).  Hence at most two chords are attached at one
  position.
* `WalkAx.tie_down` / `WalkAx.tie_up`: the **nesting order and the facing regions** at a tie.
  Let `ce` (east) and `cw` (west) be attached at the walk vertex `v = W p`, with other ends at the
  keys `ke`, `kw`, and `k = p`.
  - If the walk edge `p` goes **down** from `v`: going along the walk from `k`, the key `ke` comes
    before `kw` (`sideInArc k kw ke`); the walk faces the region **below `ce`** just after `v` and
    the region **below `cw`** just before `v`, and one region lies **above both** chords.
  - If it goes **up**: `kw` comes before `ke` (`sideInArc k ke kw`); just after `v` the walk
    faces the region **above `cw`**, just before `v` the region **above `ce`**, and one region lies
    **below both**.
* `TieSpec` and `tieFact : TieSpec`, `NoCrossSpec` and `noCross : NoCrossSpec`: the good-model
  forms of the above.

**Use in `BuildNF`** (secondary sort key).  At a tie at key `k`, the event of the chord whose other
end comes *later* along the walk after `k` must come first in the sorted sequence (it is the outer
parenthesis).  So at a walk vertex whose leaving edge goes down (direction code `2`), the event of
the west chord (the chord whose *right* endpoint is `v`, i.e. its `rpos` event) comes first; when
the edge goes up (code `1`), the event of the east chord (its `lpos` event) comes first.  One
height test of the leaving edge (`WalkKey.dirCode`) decides it.  In the region assignment, the
zero-length gap between the two events is the region above both chords (down) or below both (up);
for each of the two chords the `up`/`dn` assignment is the one of `UpSideSpec` (the region faced
just before a left endpoint and just after a right endpoint is `up`).
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideLeftOf sideCcw sideCross sideDot
  SideClean ChordSystem freeIn regionsIn TouchesIn sideKey_inj)
open Chazelle.Jordan (offset nrm)
open Chazelle.Geometry (lerp point_ext lerp_mem_segment)
namespace Tie
theorem sideCcw_neg (B X A : Point) : sideCcw (-B) (-X) (-A) ↔ sideCcw B X A := by
  have h1 : ∀ u v : Point, sideCross (-u) (-v) = sideCross u v := by
    intro u v; simp only [sideCross, Prod.fst_neg, Prod.snd_neg]; ring
  have h2 : ∀ u v : Point, sideDot (-u) (-v) = sideDot u v := by
    intro u v; simp only [sideDot, Prod.fst_neg, Prod.snd_neg]; ring
  zufqe
  rw [h1, h1, h1, h2, h2]
variable {B A : Point} {s : ℝ}
/-- Both horizontal directions in the left sector of a corner: the leaving direction `B` is not
horizontal, and the corner is not a straight angle. -/
theorem ccw_ew {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (hE : sideCcw B ztdwb A) (hW : sideCcw B (-s', 0) A) :
    B.2 ≠ 0 ∧ ¬ (sideCross B A = 0 ∧ sideDot B A < 0) := by
  unfold sideCcw at hE hW
  simp only [sideCross, sideDot] at hE hW ⊢
  constructor
  · intro hB
    rw [hB] at hE hW
    rcases hE with ⟨-, h, -⟩ | ⟨h1, h | h⟩ | ⟨-, -, h⟩ | ⟨h1, -, h | h⟩ <;>
      rcases hW with ⟨-, h', -⟩ | ⟨h1', h' | h'⟩ | ⟨-, -, h'⟩ | ⟨h1', -, h' | h'⟩ <;>
      first
        | (simp at h; done)
        | (simp at h'; done)
        | nlinarith
  · zubf
    rcases hE with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ <;>
      rcases hW with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, -, h'⟩ | ⟨-, h', -⟩ <;> nlinarith

/-- **Leaving edge going down** (`B.2 < 0`) with the west direction in the sector: the arriving
direction `A` also points down, and the sector contains every direction `X` that is strictly left
of `B`, or points up, or is strictly right of `A`. -/
theorem ccw_down (hs : 0 < s) (hB : B.2 < 0) (hW : sideCcw B ztldd A) :
    A.2 < 0 ∧ ∀ X : Point, (0 < sideCross B X ∨ 0 < X.2 ∨ 0 < sideCross X A) → sideCcw B X A := by
  unfold sideCcw at hW
  simp only [sideCross, sideDot] at hW
  rcases hW with ⟨-, h, -⟩ | ⟨h1, h | h⟩ | ⟨-, -, h⟩ | ⟨h1, h2, -⟩
  · nlinarith
  · nlinarith
  · -- reflex corner, `A` points down
    have hA : ztmsv := by_nlinarith
    refine ⟨hA, fun X hX => Or.inr (Or.inl ⟨by_tauto, ?_⟩)⟩
    simp only [sideCross]
    zuidz
    · tauto
    · zubaj

      nlinarith [mul_pos hX (neg_pos.2 hA), mul_pos hX (neg_pos.2 hB),
        mul_nonneg (neg_nonneg.2 hA.le) (sub_nonneg.2 hno.1),
        mul_nonneg (neg_nonneg.2 hB.le) (sub_nonneg.2 hno.2)]
    tauto
  · nlinarith
  · -- full turn: `A` has the direction of `B`
    have hA : ztmsv := by
      zuhbt
      zubhq
      have e : B.2 * ztely = ztdfh * A.2 := by
        grind
      have := mul_neg_of_neg_of_pos hB h2
      nlinarith [mul_nonneg (add_nonneg (sq_nonneg B.1) (sq_nonneg B.2)) hA]
    refine ⟨hA, fun X hX => Or.inr (Or.inr (Or.inr ⟨by_tauto,
      by positivity, ?_⟩))⟩
    simp only [sideCross, sideDot]
    zuidz
    · left; positivity
    · by_cases hc : B.1 * X.2 - B.2 * X.1 = 0
      · right
        have e : B.2 * ztgzv = ztdfh * X.2 := by
          grind
        have h3 : 0 < ztdfh * X.2 :=
          mul_pos (by nlinarith [sq_nonneg B.1, sq_pos_of_neg hB]) hX
        by_contra h4
        push Not at h4
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hB.le h4]
      simp_all
    · left
      zuchg
      simp only [sideCross] at hX
      have e : B.2 * (X.1 * A.2 - X.2 * A.1) = 0 := by
        grind
      have := mul_neg_of_neg_of_pos hB hX
      linarith

/-- **Leaving edge going up** (`0 < B.2`) with the east direction in the sector (mirror of
`ccw_down` by the half-turn). -/
theorem ccw_up (hs : 0 < s) (hB : 0 < B.2) (hE : sideCcw B ztdwb A) :
    0 < A.2 ∧ ∀ X : Point, (0 < sideCross B X ∨ X.2 < 0 ∨ 0 < sideCross X A) → sideCcw B X A := by
  have hE' : sideCcw (-B) ztldd (-A) := by
    have : (ztldd : Point) = -(ztdwb : Point) := by_simp
    rw [this, sideCcw_neg]; exact hE
  obtain ⟨hA, hX⟩ := ccw_down hs by_simp_all hE'
  refine ⟨by_simp_all, fun X h => ?_⟩
  rw [← sideCcw_neg]
  apply hX
  have e1 : sideCross (-B) (-X) = sideCross B X := by simp only [sideCross]; simp
  have e2 : sideCross (-X) (-A) = sideCross X A := by simp only [sideCross]; simp
  simp_all

/-! ## A cyclic fact -/

/-- If `y ≠ a` is neither strictly between `a` and `b` nor strictly between `c` and `a` (all
cyclically, three distinct keys), then `b` is strictly between `a` and `c`. -/
theorem cyc_cover {a b c y : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hya : y ≠ a)
    (h1 : ¬ sideInArc a b y) (h2 : ¬ sideInArc c a y) : sideInArc a c b := by
  unfold sideInArc at *
  grind
end Tie

/-! ## The conclusions at a tie -/

/-- **The tie at a vertex whose leaving edge goes down.**  For the east chord `ce` and the west
chord `cw` attached at the walk vertex `v = W p` (position `(p, 0)`): the walk faces the region
below `ce` just after `v` (on edge `p`) and the region below `cw` just before `v` (on the arriving
edge `(p + n - 1) mod n`, near its end), one region lies above both chords, and going along the
walk from the key `p` the other end of `ce` comes before the other end of `cw`. -/
def Model.TieDown (M : Model) (F : Set ztf) (ce cw : Set Point) (p : ℕ) : Prop :=
  ∃ U V R, U ∈ M.regions F ∧ V ∈ M.regions F ∧ R ∈ M.regions F ∧
    M.BelowOf ce U ∧ M.BelowOf cw V ∧ M.AboveOf ce R ∧ M.AboveOf cw R ∧
    ztegu ∧
    ztwxk ∧
    ∀ (pe pw : ℕ) (te tw : ℝ), SideAttach M.W ce pe te → sidePt M.W pe te ≠ M.W.vtx p →
      SideAttach M.W cw pw tw → sidePt M.W pw tw ≠ M.W.vtx p →
        sideInArc (p : ℝ) ztbjs zteuq

/-- **The tie at a vertex whose leaving edge goes up** (the mirror of `Model.TieDown`): the walk
faces the region above `cw` just after `v` and the region above `ce` just before `v`, one region
lies below both chords, and going along the walk from the key `p` the other end of `cw` comes
before the other end of `ce`. -/
def Model.TieUp (M : Model) (F : Set ztf) (ce cw : Set Point) (p : ℕ) : Prop :=
  ∃ U V R, U ∈ M.regions F ∧ V ∈ M.regions F ∧ R ∈ M.regions F ∧
    M.AboveOf cw U ∧ M.AboveOf ce V ∧ M.BelowOf ce R ∧ M.BelowOf cw R ∧
    ztegu ∧
    ztwxk ∧
    ∀ (pe pw : ℕ) (te tw : ℝ), SideAttach M.W ce pe te → sidePt M.W pe te ≠ M.W.vtx p →
      SideAttach M.W cw pw tw → sidePt M.W pw tw ≠ M.W.vtx p →
        sideInArc (p : ℝ) zteuq ztbjs

/-! ## Chords at a walk position -/
namespace WalkAx
variable {M : Model}

/-- **The other end of an attached admissible chord**: the chord is the segment from the point
`v` of the attachment to a point `e ≠ v` at the same height, off the domain, whose open part is in
the domain; every attachment of the chord at a point other than `v` is at `e`. -/
theorem attach_other_end (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) :
    ∃ e : Point, e ≠ sidePt M.W p t ∧ e.2 = (sidePt M.W p t).2 ∧
      c = Chazelle.segment ztbp e ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp ztbp e s ∈ M.D) ∧ e ∉ M.D ∧
      ∀ (p' : ℕ) (t' : ℝ), SideAttach M.W c p' t' → sidePt M.W p' t' ≠ sidePt M.W p t →
        sidePt M.W p' t' = e := by
  zuchn
  have hnotD : ∀ q, WalkEnd M.W c q → q ∉ M.D := by
    rintro q ⟨⟨p', t', h', rfl⟩, -⟩
    exact hM.trace p' h'.1 t' h'.2.1 h'.2.2.1.le
  zucgh
  zugdq
  have hother : ∀ e, (sidePt M.W p t = a ∧ e = b ∨ sidePt M.W p t = b ∧ e = a) →
      ∀ (p' : ℕ) (t' : ℝ), SideAttach M.W c p' t' → sidePt M.W p' t' ≠ sidePt M.W p t →
        sidePt M.W p' t' = e := by
    intro e he p' t' hA2 hne
    zumbj
    zvmyh at hA2'
    rcases he with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
      rcases hM.attach_endpoint hopen hA2' with h2 | h2
    · simp_all
    · zucvi
    · zucvi
    simp_all
  zucio
  · refine ⟨b, by_grind, by_simp_all, by_simp_all,
      by simp_all, by_simp_all, hother b by_simp_all⟩
  · refine ⟨a, by_simp_all, by_simp_all, (by zunow; omega), by zvmwc; exact open_rev hopen, by_grind, hother a by_simp_all⟩

/-- Distance from the start of a segment to a point of it. -/
theorem dist_lerp_left (v e : Point) {s : ℝ} (hs : 0 ≤ s) : dist ztrtn v = s * dist v e := by
  zuecv
  have : v - lerp v e s = s • (v - e) := by
    zubvl
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]

/-- Points of an attached chord close to its attachment are in the left sector there. -/
theorem exists_left_on_chord {c : Set Point} {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    {e : Point} (hce : c = Chazelle.segment ztbp e) (he : e ≠ sidePt M.W p t)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ dist ztzmn ztbp < ρ ∧
      sideLeft M.W p t ztzmn := by
  obtain ⟨-, -, -, -, r₀, hr₀, hatt⟩ := hA
  set v := sidePt M.W p t
  set r := min r₀ ρ with hr
  zufwe
  have hn : 0 < dist v e + 1 := by_positivity
  set s := min (r / zterp) ztcn with hs
  zucmo
  zuiai
  have hd : dist ztrtn v < r := by
    rw [dist_lerp_left v e hs0.le]
    have h1 : s ≤ r / zterp := by_grind
    calc s * dist v e < s * zterp := by_nlinarith
      _ ≤ r / zterp * zterp := mul_le_mul_of_nonneg_right h1 hn.le
      _ = r := div_mul_cancel₀ _ hn.ne'
  refine ⟨s, hs0, hs1, by_grind,
    hatt _ (by zvnme; exact lerp_mem_segment _ _ hs0.le hs1.le)
    (Chazelle.Jordan.lerp_ne_left ztvbb hs0) by_grind⟩

/-- **Every chord attached at a position leaves it horizontally, east or west.** -/
theorem attach_dir (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) :
    ztdqa ∨ ztdqb := by
  obtain ⟨e, -, -, hce, -⟩ := hM.attach_other_end hc hA
  rcases le_total (sidePt M.W p t).1 e.1 with h | h
  · left
    zqpx
  · right
    zqpx

/-- **Two chords of `F` attached at one position in the same direction are equal** (east). -/
theorem attach_east_unique (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) (hE : ∀ z ∈ c, (sidePt M.W p t).1 ≤ z.1)
    (hE' : ∀ z ∈ c', (sidePt M.W p t).1 ≤ z.1) : c = c' := by
  zqpk
  have h1 := lt_of_le_of_ne (hE e ztktj)
    by_grind
  have h1' := lt_of_le_of_ne
    (hE' e' ztkti)
    by_grind
  zugsc
  · zulgd

    have e1 : e = lerp v e' (ztnxs / zttjk) := by
      zubjw
      · zufau
      · zqpz
    zqpo
  · grind
  · exfalso
    apply heD'
    have e1 : e' = lerp v e (zttjk / ztnxs) := by
      zubjw
      · zufau
      · zqpz
    zqpp

/-- **Two chords of `F` attached at one position in the same direction are equal** (west). -/
theorem attach_west_unique (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {c c' : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) (hW : ∀ z ∈ c, z.1 ≤ (sidePt M.W p t).1)
    (hW' : ∀ z ∈ c', z.1 ≤ (sidePt M.W p t).1) : c = c' := by
  zqpk
  have h1 := lt_of_le_of_ne (hW e ztktj)
    by_grind
  have h1' := lt_of_le_of_ne
    (hW' e' ztkti)
    by_grind
  zugsc
  · exfalso
    apply heD'
    have e1 : e' = lerp v e (ztucr / ztucs) := by
      zubjw
      · zudlh
        grind
      · zqpz
    zqpp
  · grind
  · zulgd

    have e1 : e = lerp v e' (ztucs / ztucr) := by
      zubjw
      · zudlh
        grind
      · zqpz
    zqpo

/-! ## Non-crossing -/

/-- **Two distinct chords of an admissible family do not cross on the walk**: if an attachment
key of `d` is strictly inside the arc from `A` to `B` of `c`, no attachment key of `d` is strictly
inside the arc from `B` to `A`. -/
theorem no_cross (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c d : Set Point} (hc : c ∈ F) (hd : d ∈ F) (hcd : c ≠ d) {pa pb pc pd : ℕ}
    {ta tb tc td : ℝ} (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) (hC : SideAttach M.W d pc tc)
    (hD : SideAttach M.W d pd td) :
    ¬ (sideInArc ztbf ztbd zttvv ∧ sideInArc ztbd ztbf zttwd) := by
  zubf
  zudr
  obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split ztlz hA hB hAB
  -- a point of `d ∩ D` in a component, near an attachment of `d`
  have hpt : ∀ {q : ℕ} {τ : ℝ} {k : Point}, SideAttach M.W d q τ →
      Chazelle.Chain.SideSectorIn M.W ztyqh q τ →
      ∃ x ∈ d ∩ M.D, x ∈ connectedComponentIn ztjq k := by
    intro q τ k hQ hsec
    obtain ⟨r, hr, hsecr⟩ := hsec
    obtain ⟨e, hev, -, hde, hopen, -⟩ := hM.attach_other_end ztvsy hQ
    obtain ⟨s, hs0, hs1, hdist, hleft⟩ := exists_left_on_chord hQ hde hev hr
    refine ⟨_, ⟨by rw [hde]; exact lerp_mem_segment _ _ hs0.le hs1.le, by_simp_all⟩,
      hsecr _ by_simp_all hleft⟩
  obtain ⟨x₁, hx₁d, hx₁K⟩ := hpt hC (hK₁ pc hC.1 tc hC.2.1 hC.2.2.1 h1)
  obtain ⟨x₂, hx₂d, hx₂K⟩ := hpt hD (hK₂ pd hD.1 td hD.2.1 hD.2.2.1 h2)
  have hsub : d ∩ M.D ⊆ M.D \ c := fun x hx =>
    ⟨hx.2, fun hxc => hsys.inter_subset_compl hd hc (Ne.symm hcd) by_grind hx.2⟩
  have hcon := (hsys.chord_inter_nonempty_isPreconnected hd).2.subset_connectedComponentIn
    hx₁d hsub
  zufqo
  rw [connectedComponentIn_eq hx₁K, connectedComponentIn_eq hx₂K,
    connectedComponentIn_eq (hcon hx₂d)]

/-! ## The setup of a tie -/

/-- **At a tie the position is a walk vertex, and both horizontal directions lie in its left
sector.**  For chords `ce` (east) and `cw` (west) of the admissible set attached at the same
position `(p, t)`: `t = 0`, and with `B` the direction of the leaving walk edge and `A` that of the
arriving one, both `(s₁, 0)` and `(-s₂, 0)` (for some `s₁, s₂ > 0`) are strictly inside the
counterclockwise sector from `B` to `A`. -/
theorem tie_setup (hM : WalkAx M) {ce cw : Set Point} (hce : ce ∈ M.Adm) (hcw : cw ∈ M.Adm)
    {p : ℕ} {t : ℝ} (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1) :
    t = 0 ∧ ∃ s₁ s₂ : ℝ, 0 < s₁ ∧ 0 < s₂ ∧
      sideCcw ztjkb (s₁, 0) ztzcb ∧
      sideCcw ztjkb (-s₂, 0) ztzcb := by
  obtain ⟨we, hwev, hwey, hceq, -⟩ := hM.attach_other_end hce hAe
  obtain ⟨uw, huwv, huwy, hcwq, -⟩ := hM.attach_other_end hcw hAw
  set v := sidePt M.W p t with hv
  have hlte := lt_of_le_of_ne
    zthxs
    by_grind
  have hltw := lt_of_le_of_ne
    zthxw
    by_grind
  obtain ⟨s, hs0, hs1, -, hL⟩ := exists_left_on_chord hAe hceq hwev one_pos
  obtain ⟨s', hs0', hs1', -, hL'⟩ := exists_left_on_chord hAw hcwq huwv one_pos
  have hsnd : ∀ (e : Point) (σ : ℝ), e.2 = v.2 → (lerp v e σ).2 = v.2 := by
    simp_all
  have ht0 : ztbhh := by
    by_contra ht
    have ht' : ztbxd := ⟨lt_of_le_of_ne hAe.2.1 (Ne.symm ht), hAe.2.2.1⟩
    rw [Chazelle.Chain.sideLeft_edge (hM.nd p hAe.1) ht'] at hL hL'
    zuhog
    set b := M.W.vtx ztwjk
    have hva : v = lerp a b t := rfl
    have key : ∀ (e : Point) (σ : ℝ), e.2 = v.2 →
        det a b (lerp v e σ) = -(σ * ztnxs) * ztti := by
      intro e σ he
      have h2 := hsnd e σ he
      zulbn
      zuczw
      simp only [Geometry.lerp_fst, hva, Geometry.lerp_snd]
      ring
    rw [key we s hwey] at hL
    rw [key uw s' huwy] at hL'
    have h1 : 0 < s * ztoju := mul_pos hs0 by_linarith
    have h2 : 0 < s' * ztojk := mul_pos hs0' by_linarith
    nlinarith
  zudlw
  have hv0 : v = M.W.vtx p := Chazelle.Chain.sidePt_zero M.W p
  refine ⟨rfl, s * ztoju, s' * ztojk, by_simp_all,
    by simp_all, ?_, ?_⟩
  · rw [Chazelle.Chain.sideLeft_zero] at hL
    unfold sideLeftOf at hL
    have e1 : lerp v we s - M.W.vtx p = (s * ztoju, 0) := by
      zulrf
      zubjw
      · simp
      simp_all
    zvmxy at hL
    exact hL
  · rw [Chazelle.Chain.sideLeft_zero] at hL'
    unfold sideLeftOf at hL'
    have e1 : lerp v uw s' - M.W.vtx p = (-(s' * ztojk), 0) := by
      zulrf
      zubjw
      · simp [Geometry.lerp_fst]; ring
      simp_all
    zvmxy at hL'
    tauto

/-! ## Local regions at a walk vertex -/

/-- **Near a walk vertex, the left sector off the vertex height is free**: there is `r > 0` such
that every point of the ball of radius `r` around the vertex `W p` that lies in the left sector
of the position `(p, 0)` and not at the height of the vertex is in the free set of `F`. -/
theorem local_free (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) :
    ∃ r > 0, ∀ x ∈ ball ztoy r, sideLeft M.W p 0 x → x.2 ≠ (M.W.vtx p).2 →
      x ∈ freeIn M.D F := by
  zudr
  obtain ⟨r₁, hr₁, hcl⟩ := hM.clean p hp 0 le_rfl zero_lt_one
  rw [Chazelle.Chain.sidePt_zero] at hcl
  set G := {c ∈ F | M.W.vtx p ∉ c} with hG
  have hGF : G ⊆ F := by_simp_all
  have hGc : IsClosed _ := hsys.isClosed_sUnion hGF
  have hvG : M.W.vtx p ∉ ⋃₀ G := by_simp_all
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.1 hGc.isOpen_compl _ hvG
  refine ⟨min r₁ r₂, by_simp_all, fun x hx hL hy => ztcp⟩
  · zujuk
    simp_all
  · zuifl
    by_cases hvc : M.W.vtx p ∈ c
    · exact hy (hsys.snd_eq hc hxc hvc)
    · exact hb₂ by_simp_all ⟨c, by_simp_all, hxc⟩
variable {F : Set (Set Point)} {p : ℕ}
/-- A nonempty preconnected subset of the free set lies in one region. -/
theorem exists_region_of_free {S : Set Point} (hS : IsPreconnected S)
    (hne : S.Nonempty) (hSF : S ⊆ freeIn M.D F) : ∃ U ∈ M.regions F, S ⊆ U := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨_, ⟨x, hSF hx, rfl⟩, hS.subset_connectedComponentIn hx hSF⟩

/-- A region containing the points just below one point of a chord is the region below it. -/
theorem below_of_meets (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} (hz : z ∈ c)
    (hzD : z ∈ M.D) (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztcxf : Point) ∈ U) : M.BelowOf c U := by
  obtain ⟨Up, Dn, -, hDn, -, hside, -⟩ := chordSides_of_system ztbip hc
  obtain ⟨δ, h1, -, h2⟩ := (h.and ztrsd).exists
  have hUD : U = Dn := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU hDn with h' | h'
    · zuclh
    grind
  zugdn

/-- A region containing the points just above one point of a chord is the region above it. -/
theorem above_of_meets (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {U : Set Point} (hU : U ∈ M.regions F) {z : Point} (hz : z ∈ c)
    (hzD : z ∈ M.D) (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztcxe : Point) ∈ U) : M.AboveOf c U := by
  obtain ⟨Up, Dn, hUp, -, -, hside, -⟩ := chordSides_of_system ztbip hc
  obtain ⟨δ, h1, h2, -⟩ := (h.and ztrsd).exists
  have hUD : U = Up := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU hUp with h' | h'
    · zuclh
    grind
  zugdn

/-- Vertical displacements of a point of an open set stay in it for small displacements. -/
theorem eventually_vert {O : Set Point} (hO : IsOpen O) {z : Point} (hz : z ∈ O) (σ : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztewt : Point) ∈ O := by
  have hc : Continuous fun δ : ℝ => (ztewt : Point) := by fun_prop
  have h0 : ((z.1, z.2 + σ * 0) : Point) = z := by_simp
  have := hc.tendsto 0
  zubuv
  exact (this.eventually (hO.mem_nhds hz)).filter_mono nhdsWithin_le_nhds

/-- **A local region piece at a walk vertex.**  Let `O` be an open convex set inside the free
radius `r` of the vertex `v = W p` (`local_free`), such that the points of `O` strictly on the
`σ`-side of the height of `v` (`σ = ±1`) are in the left sector of `(p, 0)`.  Then those points
lie in one region `U`, which contains the vertical displacements `(z.1, z.2 + σ δ)` (small
`δ > 0`) of every point `z ∈ O` at the height of `v`. -/
theorem region_of_piece {r : ℝ}
    (hfree : ∀ x ∈ ball ztoy r, sideLeft M.W p 0 x → x.2 ≠ (M.W.vtx p).2 →
      x ∈ freeIn M.D F)
    {O : Set Point} (hOo : IsOpen O) (hOc : Convex ℝ O) (hOb : O ⊆ ball ztoy r)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : ∀ x ∈ O, 0 < σ * ztewq → sideLeft M.W p 0 x)
    {z : Point} (hz : z ∈ O) (hzv : z.2 = (M.W.vtx p).2) :
    ∃ U ∈ M.regions F, (∀ x ∈ O, 0 < σ * ztewq → x ∈ U) ∧
      ∀ z' ∈ O, z'.2 = (M.W.vtx p).2 → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztokk : Point) ∈ U := by
  zulrl
  zubgl
  set S := O ∩ {x : Point | 0 < σ * det v ztqye x} with hS
  have hdet : ∀ x : Point, det v ztqye x = x.2 - v.2 := by
    intro x; zuorv; ring
  have hSc : Convex ℝ S := hOc.inter (Chazelle.Jordan.convex_det_pos _ _ σ)
  have hSF : S ⊆ freeIn M.D F := by
    grind
  have hev : ∀ z' ∈ O, z'.2 = v.2 → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztokk : Point) ∈ S := by
    intro z' hz' hz'v
    filter_upwards [eventually_vert hOo hz' σ, self_mem_nhdsWithin] with δ h1 h2
    zujfv
    simp only [mem_ofPred_eq, hdet, hz'v]
    have : σ * (v.2 + σ * δ - v.2) = δ := by_grind
    grind
  obtain ⟨δ₀, hδ₀⟩ := (hev z hz hzv).exists
  obtain ⟨U, hU, hSU⟩ := exists_region_of_free hSc.isPreconnected ⟨_, hδ₀⟩ hSF
  refine ⟨U, hU, fun x hx h => hSU zthne, fun z' hz' hz'v => (hev z' hz' hz'v).mono
    by_grind⟩
  grind

/-- **The walk just after a vertex** faces the region containing the points of the ball around
the vertex that are left of the leaving edge and strictly on its side (`σ = ±1`) of the vertex
height. -/
theorem faces_after_of {U : Set Point} {r σ : ℝ} (hr : 0 < r) (hσ : σ = 1 ∨ σ = -1)
    (hB : 0 < σ * ztcrr)
    (hU : ∀ x ∈ ball ztpr r, 0 < sideCross ztjkb (x - M.wa p) →
      0 < σ * (x.2 - (M.wa p).2) → x ∈ U) :
    ∃ δ₁ > (0 : ℝ), ∀ t', 0 < t' → t' < δ₁ → M.Faces p t' U := by
  set v := M.wa p
  set B : Point := M.wb p - v with hBdef
  have hB1 : B.1 = (M.wb p).1 - v.1 := rfl
  have hB2 : B.2 = (M.wb p).2 - v.2 := rfl
  rw [← hB2] at hB
  have hσB : -|B.1| ≤ σ * B.1 := by
    zur
    · grind
    grind
  have hB2ne : ztsan := by_grind
  set K := |B.1| + |B.2| + 1 with hK
  zudno
  refine ztxsr
  have hpos : 0 < min t' (t' * ztufh / K) := lt_min ht0 by_positivity
  zuenu

  have hδ1 : δ < t' := by_grind
  have hδ2 : δ * K < t' * ztufh := by
    have := hδ.2.trans_le ztgh
    zudbe
  zuion
  have hx1 : x.1 - v.1 = t' * B.1 - δ * B.2 := by
    simp only [x, offset, nrm, Geometry.add_fst, Geometry.smul_fst, Geometry.lerp_fst, hB1, hB2]
    ring
  have hx2 : x.2 - v.2 = t' * B.2 + δ * B.1 := by
    simp only [x, offset, nrm, Geometry.add_snd, Geometry.smul_snd, Geometry.lerp_snd, hB1, hB2]
    ring
  have hK2 : ztoit * K < r := by
    have h1 := ht1
    rw [lt_div_iff₀ by_positivity] at h1
    nlinarith
  have a1 := le_abs_self B.1
  have a2 := neg_abs_le B.1
  have a3 := le_abs_self B.2
  have a4 := neg_abs_le B.2
  have p1 := mul_le_mul_of_nonneg_left a1 ht0.le
  have p2 := mul_le_mul_of_nonneg_left a2 ht0.le
  have p3 := mul_le_mul_of_nonneg_left a3 ht0.le
  have p4 := mul_le_mul_of_nonneg_left a4 ht0.le
  zqps
  have hKe : ztoit * K = t' * |B.1| + t' * |B.2| + δ * |B.1| + δ * |B.2| + ztoit := by
    grind
  apply hU
  · zqpm
  · have : sideCross B ztsq = δ * ztdfh := by
      zuees
    zubk
    positivity
  · zumoj
    have : δ * |B.1| ≤ δ * K := by_grind
    have h3 : -(δ * |B.1|) ≤ δ * (σ * B.1) := by_nlinarith
    nlinarith

/-- **The walk just before a vertex** (on the arriving edge `q`, near its end) faces the region
containing the points of the ball around the vertex that are right of the arriving direction and
strictly on its side (`σ = ±1`) of the vertex height. -/
theorem faces_before_of {q : ℕ} {V : Set Point} {r σ : ℝ} (hr : 0 < r) (hσ : σ = 1 ∨ σ = -1)
    (hA : 0 < σ * zteip)
    (hV : ∀ x ∈ ball (M.wb q) r, 0 < sideCross (x - M.wb q) (M.wa q - M.wb q) →
      0 < σ * (x.2 - (M.wb q).2) → x ∈ V) :
    ∃ δ₁ > (0 : ℝ), ∀ t', 1 - δ₁ < t' → t' < 1 → M.Faces q t' V := by
  set v := M.wb q
  set A : Point := M.wa q - v with hAdef
  have hA1 : A.1 = (M.wa q).1 - v.1 := rfl
  have hA2 : A.2 = (M.wa q).2 - v.2 := rfl
  rw [← hA2] at hA
  have hσA : σ * A.1 ≤ |A.1| := by
    zur
    · grind
    grind
  have hA2ne : ztsak := by_grind
  set K := |A.1| + |A.2| + 1 with hK
  zudno
  refine ztxsr
  set u := 1 - t' with hu
  have hu0 : 0 < u := by_grind
  have hu1 : u < r / ztbds := by_grind
  have hpos : 0 < min u (u * ztokz / K) := lt_min hu0 by_positivity
  zuenu

  have hδ1 := hδ.2.trans_le ztff
  have hδ2 : δ * K < u * ztokz := by
    have := hδ.2.trans_le ztgh
    zudbe
  zuion
  have hx1 : x.1 - v.1 = u * A.1 + δ * A.2 := by
    simp only [x, offset, nrm, Geometry.add_fst, Geometry.smul_fst, Geometry.lerp_fst, hA1, hA2, hu]
    ring
  have hx2 : x.2 - v.2 = u * A.2 - δ * A.1 := by
    simp only [x, offset, nrm, Geometry.add_snd, Geometry.smul_snd, Geometry.lerp_snd, hA1, hA2, hu]
    ring
  have hK2 : ztoix * K < r := by
    rw [lt_div_iff₀ by_positivity] at hu1
    nlinarith
  have a1 := le_abs_self A.1
  have a2 := neg_abs_le A.1
  have a3 := le_abs_self A.2
  have a4 := neg_abs_le A.2
  have p1 := mul_le_mul_of_nonneg_left a1 hu0.le
  have p2 := mul_le_mul_of_nonneg_left a2 hu0.le
  have p3 := mul_le_mul_of_nonneg_left a3 hu0.le
  have p4 := mul_le_mul_of_nonneg_left a4 hu0.le
  zqps
  have hKe : ztoix * K = u * |A.1| + u * |A.2| + δ * |A.1| + δ * |A.2| + ztoix := by
    grind
  apply hV
  · zqpm
  · have : sideCross ztsq A = δ * ztnit := by
      zuees
    zubk
    positivity
  · zumoj
    have : δ * |A.1| ≤ δ * K := by_grind
    have h3 := mul_le_mul_of_nonneg_left hσA hδ0.le
    grind

/-- The arriving edge of a walk vertex ends at it. -/
theorem prev_succ {p n : ℕ} (hp : p < n) : ztxhn % n = p := by
  rcases p with _ | k
  · have hn : n - 1 < n := by_omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hn, Nat.sub_add_cancel by_omega, Nat.mod_self]
  · have e : k + 1 + n - 1 = k + n := by_omega
    have h1 : (k + 1 + n - 1) % n = k := by
      rw [e, Nat.add_mod_right]; exact Nat.mod_eq_of_lt by_omega
    zvmwp; exact Nat.mod_eq_of_lt hp

/-- Common data of a tie at a vertex: the other ends of the two chords and points of the chords
near the vertex, in the domain, within a given distance. -/
theorem tie_ends (hM : WalkAx M) {ce cw : Set Point} (hce : ce ∈ M.Adm) (hcw : cw ∈ M.Adm)
    {p : ℕ} (hAe : SideAttach M.W ce p 0) (hAw : SideAttach M.W cw p 0)
    (hE : ∀ z ∈ ce, (sidePt M.W p 0).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p 0).1)
    {r : ℝ} (hr : 0 < r) :
    ∃ we uw ze zw : Point, we.2 = (M.W.vtx p).2 ∧ uw.2 = (M.W.vtx p).2 ∧
      (M.W.vtx p).1 < we.1 ∧ uw.1 < (M.W.vtx p).1 ∧
      ce = Chazelle.segment ztoy we ∧ cw = Chazelle.segment ztoy uw ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp ztoy we s ∈ M.D) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp ztoy uw s ∈ M.D) ∧
      (∀ (p' : ℕ) (t' : ℝ), SideAttach M.W ce p' t' → sidePt M.W p' t' ≠ M.W.vtx p →
        sidePt M.W p' t' = we) ∧
      (∀ (p' : ℕ) (t' : ℝ), SideAttach M.W cw p' t' → sidePt M.W p' t' ≠ M.W.vtx p →
        sidePt M.W p' t' = uw) ∧
      ze ∈ ce ∧ ze ∈ M.D ∧ ze.2 = (M.W.vtx p).2 ∧ (M.W.vtx p).1 < ze.1 ∧
        dist ze ztoy < r ∧
      zw ∈ cw ∧ zw ∈ M.D ∧ zw.2 = (M.W.vtx p).2 ∧ zw.1 < (M.W.vtx p).1 ∧
        dist zw ztoy < r := by
  have hv0 := Chazelle.Chain.sidePt_zero M.W p
  obtain ⟨we, hwev, hwey, hceq, hopene, -, hothe⟩ := hM.attach_other_end hce hAe
  obtain ⟨uw, huwv, huwy, hcwq, hopenw, -, hothw⟩ := hM.attach_other_end hcw hAw
  obtain ⟨se, hse0, hse1, hsed, -⟩ := exists_left_on_chord hAe hceq hwev hr
  obtain ⟨sw, hsw0, hsw1, hswd, -⟩ := exists_left_on_chord hAw hcwq huwv hr
  rw [hv0] at hE hW hwev hwey hceq hopene hothe huwv huwy hcwq hopenw hothw hsed hswd
  zulrl
  have hlte := lt_of_le_of_ne
    zthxs
    by_grind
  have hltw := lt_of_le_of_ne
    zthxw
    by_grind
  refine ⟨we, uw, lerp v we se, lerp v uw sw, hwey, huwy, hlte, hltw, hceq, hcwq, hopene, hopenw,
    hothe, hothw, by rw [hceq]; exact lerp_mem_segment _ _ hse0.le hse1.le,
    by grind, by simp only [Geometry.lerp_snd, hwey]; ring,
    by simp only [Geometry.lerp_fst]; nlinarith, hsed,
    by zuoxs; exact lerp_mem_segment _ _ hsw0.le hsw1.le,
    by grind, by simp only [Geometry.lerp_snd, huwy]; ring,
    by simp only [Geometry.lerp_fst]; nlinarith, hswd⟩

/-- An open half-plane `{0 < det a b x}` is open. -/
theorem isOpen_det_pos (a b : Point) : IsOpen {x : Point | 0 < 1 * det a b x} :=
  isOpen_lt continuous_const (by unfold det; fun_prop)

/-- **The tie, leaving edge down.** -/
theorem tie_down (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ}
    (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
    (hdown : (M.wb p).2 < (M.wa p).2) :
    t = 0 ∧ M.TieDown F ce cw p := by
  obtain ⟨rfl, s₁, s₂, hs₁, hs₂, -, hsW⟩ := hM.tie_setup ztgka ztgkb hAe hAw hE hW
  zqpq
  obtain ⟨we, uw, ze, zw, hwey, huwy, hlte, hltw, hceq, hcwq, hopene, hopenw, hothe, hothw,
    hzec, hzeD, hzey, hzex, hzed, hzwc, hzwD, hzwy, hzwx, hzwd⟩ :=
    hM.tie_ends ztgka ztgkb hAe hAw hE hW hr
  zqpj
  have hB2 : ztkzu := by zuoex; grind
  obtain ⟨hA2, hsec⟩ := Tie.ccw_down hs₂ hB2 hsW
  have hA2' : ztmsv := hA2
  have hleft : ∀ x : Point, (0 < sideCross B ztsq ∨ 0 < (x - v).2 ∨ 0 < sideCross ztsq A) →
      sideLeft M.W p 0 x := by
    zuh
    zugtq
    zulyz
  have hcrossB : ztjbm :=
    ztztd
  have hcrossA : ztjbn :=
    ztswg
  -- the region below `ce` (after `v`)
  obtain ⟨U, hU, hUin, hUev⟩ := region_of_piece (σ := -1) hfree
    ztydg
    ztcph inter_subset_left
    ztbt (fun x hx hy => hleft x (Or.inl (by
      zuoxt; have := hx.2; simp only [mem_ofPred_eq, one_mul] at this; omega)))
    (z := ze) ⟨by_tauto, by
      zqpn
      zqpv
      nlinarith⟩ hzey
  have hUbelow := hM.below_of_meets hF hfin hce hU hzec hzeD
    ((hUev ze ⟨by_tauto, by
      zqpn
      zqpv
      nlinarith⟩ hzey).mono by_grind)
  -- the region below `cw` (before `v`)
  obtain ⟨V, hV, hVin, hVev⟩ := region_of_piece (σ := -1) hfree
    ztlcs
    ztcph inter_subset_left
    ztbt (fun x hx hy => hleft x (Or.inr (Or.inr (by
      zuoxu; have := hx.2; simp only [mem_ofPred_eq, one_mul] at this; omega))))
    (z := zw) ⟨by_tauto, by
      zqpn
      zqpw
      exact mul_pos_of_neg_of_neg by_linarith hA2'⟩ hzwy
  have hVbelow := hM.below_of_meets hF hfin hcw hV hzwc hzwD
    ((hVev zw ⟨by_tauto, by
      zqpn
      zqpw
      exact mul_pos_of_neg_of_neg by_linarith hA2'⟩ hzwy).mono by_grind)
  -- the region above both
  obtain ⟨R, hR, -, hRev⟩ := region_of_piece (σ := 1) hfree isOpen_ball zttih
    subset_rfl ztp (fun x hx hy => hleft x (Or.inr (Or.inl (by
      simp only [Prod.snd_sub]; linarith))))
    (z := ze) by_tauto hzey
  have hRe := hM.above_of_meets hF hfin hce hR hzec hzeD
    ((hRev ze by_tauto hzey).mono by_grind)
  have hRw := hM.above_of_meets hF hfin hcw hR hzwc hzwD
    ((hRev zw by_tauto hzwy).mono by_grind)
  refine ⟨U, V, R, hU, hV, hR, hUbelow, hVbelow, hRe, hRw, ?_, ?_, ?_⟩
  · -- just after `v`
    refine faces_after_of hr ztbt by_linarith (fun x hx h1 h2 => hUin x
      ⟨hx, ?_⟩ h2)
    zudwb
  · -- just before `v`
    zukzx
    have hwbq : ztuls := by
      show M.W.vtx _ = M.W.vtx p
      zulqp
    zukgr
    have hA2'' : 0 < -1 * zteip := by
      rw [hwbq, hwaq]; have : A.2 = a.2 - v.2 := rfl; linarith
    refine faces_before_of hr ztbt hA2'' (fun x hx h1 h2 => hVin x ztiwd ztktv)
    zqpt
  · -- the nesting order
    zqpl
    have hne1 : sidePt M.W p 0 ≠ sidePt M.W pe te := by rw [hv0]; exact Ne.symm hBe'
    have hne2 : sidePt M.W pw tw ≠ sidePt M.W p 0 := by rw [hv0]; omega
    have hab : ztmrr := by
      have := key_ne_of_pt_ne hAe hBe hne1; rwa [add_zero] at this
    have hac : ztmrs := by
      have := key_ne_of_pt_ne hAw hBw ztvbl; rwa [add_zero] at this
    have hbc := key_ne_of_pt_ne hBe hBw (by
      zuokm; intro h; zvmwc at hlte; linarith)
    have hya : ztmrw := by
      zqpu
    zqpy
    · refine hM.not_left_of_after hF hce hAe hBe hne1 hR hpy ztklt
        ztcmb hRf ?_
      zukwj
      have hm : lerp v we ztcn ∈ ce := by
        rw [hceq]; exact lerp_mem_segment _ _ by_norm_num by_norm_num
      refine (eventually_mul_pos (hRe _ hm (hopene _ ztfm))
        ztwfw).mono fun δ h => ?_
      rw [Chazelle.Core.offset_mid_ab hwey.symm]; exact h
    · refine hM.not_left_of_after hF hcw hBw hAw hne2 hR hpy ztklt
        ztcmb hRf ?_
      zukwk
      have hm : lerp uw v ztcn ∈ cw := by
        rw [hcwq, Geometry.segment_comm]; exact lerp_mem_segment _ _ by_norm_num by_norm_num
      refine (eventually_mul_pos (hRw _ hm (open_rev hopenw _ ztfm))
        ztwfx).mono fun δ h => ?_
      rw [Chazelle.Core.offset_mid_ab huwy]; exact h

/-- **The tie, leaving edge up.** -/
theorem tie_up (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ}
    (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
    (hup : (M.wa p).2 < (M.wb p).2) :
    t = 0 ∧ M.TieUp F ce cw p := by
  obtain ⟨rfl, s₁, s₂, hs₁, hs₂, hsE, -⟩ := hM.tie_setup ztgka ztgkb hAe hAw hE hW
  zqpq
  obtain ⟨we, uw, ze, zw, hwey, huwy, hlte, hltw, hceq, hcwq, hopene, hopenw, hothe, hothw,
    hzec, hzeD, hzey, hzex, hzed, hzwc, hzwD, hzwy, hzwx, hzwd⟩ :=
    hM.tie_ends ztgka ztgkb hAe hAw hE hW hr
  zqpj
  have hB2 : ztpho := by zuoex; grind
  obtain ⟨hA2, hsec⟩ := Tie.ccw_up hs₁ hB2 hsE
  zumbj
  have hleft : ∀ x : Point, (0 < sideCross B ztsq ∨ (x - v).2 < 0 ∨ 0 < sideCross ztsq A) →
      sideLeft M.W p 0 x := by
    zuh
    zugtq
    zulyz
  have hcrossB : ztjbm :=
    ztztd
  have hcrossA : ztjbn :=
    ztswg
  have hzwB : zw ∈ ball v r ∩ {x | 0 < 1 * det v _ x} := ⟨by_tauto, by
      zqpn
      zuoru
      simp only [sideCross, Prod.fst_sub, Prod.snd_sub, hzwy, sub_self, mul_zero, zero_sub]
      nlinarith⟩
  have hzeA : ze ∈ ball v r ∩ {x | 0 < 1 * det a v x} := ⟨by_tauto, by
      zqpn
      zunvn
      simp only [sideCross, Prod.fst_sub, Prod.snd_sub, hzey, sub_self, zero_mul, sub_zero]
      positivity⟩
  -- the region above `cw` (after `v`)
  obtain ⟨U, hU, hUin, hUev⟩ := region_of_piece (σ := 1) hfree
    ztydg
    ztcph inter_subset_left
    ztp (fun x hx hy => hleft x (Or.inl (by
      zuoxt; have := hx.2; simp only [mem_ofPred_eq, one_mul] at this; omega)))
    hzwB hzwy
  have hUabove := hM.above_of_meets hF hfin hcw hU hzwc hzwD
    ((hUev zw hzwB hzwy).mono by_grind)
  -- the region above `ce` (before `v`)
  obtain ⟨V, hV, hVin, hVev⟩ := region_of_piece (σ := 1) hfree
    ztlcs
    ztcph inter_subset_left
    ztp (fun x hx hy => hleft x (Or.inr (Or.inr (by
      zuoxu; have := hx.2; simp only [mem_ofPred_eq, one_mul] at this; omega))))
    hzeA hzey
  have hVabove := hM.above_of_meets hF hfin hce hV hzec hzeD
    ((hVev ze hzeA hzey).mono by_grind)
  -- the region below both
  obtain ⟨R, hR, -, hRev⟩ := region_of_piece (σ := -1) hfree isOpen_ball zttih
    subset_rfl ztbt (fun x hx hy => hleft x (Or.inr (Or.inl (by
      simp only [Prod.snd_sub]; linarith))))
    (z := ze) by_tauto hzey
  have hRe := hM.below_of_meets hF hfin hce hR hzec hzeD
    ((hRev ze by_tauto hzey).mono fun δ h => by
      rwa [neg_one_mul, ← sub_eq_add_neg] at h)
  have hRw := hM.below_of_meets hF hfin hcw hR hzwc hzwD
    ((hRev zw by_tauto hzwy).mono fun δ h => by
      rwa [neg_one_mul, ← sub_eq_add_neg] at h)
  refine ⟨U, V, R, hU, hV, hR, hUabove, hVabove, hRe, hRw, ?_, ?_, ?_⟩
  · -- just after `v`
    refine faces_after_of hr ztp by_linarith (fun x hx h1 h2 => hUin x
      ⟨hx, ?_⟩ h2)
    zudwb
  · -- just before `v`
    zukzx
    have hwbq : ztuls := by
      show M.W.vtx _ = M.W.vtx p
      zulqp
    zukgr
    have hA2'' : 0 < 1 * zteip := by
      rw [hwbq, hwaq]; positivity
    refine faces_before_of hr ztp hA2'' (fun x hx h1 h2 =>
      hVin x ztiwd ztktv)
    zqpt
  · -- the nesting order
    zqpl
    have hne1 : sidePt M.W p 0 ≠ sidePt M.W pw tw := by rw [hv0]; exact Ne.symm hBw'
    have hne2 : sidePt M.W pe te ≠ sidePt M.W p 0 := by rw [hv0]; omega
    have hab : ztmrs := by
      have := key_ne_of_pt_ne hAw hBw hne1; rwa [add_zero] at this
    have hac : ztmrr := by
      have := key_ne_of_pt_ne hAe hBe ztvbl; rwa [add_zero] at this
    have hbc := key_ne_of_pt_ne hBw hBe (by
      zuokm; intro h; zvmzi at hlte; linarith)
    have hya : ztmrw := by
      zqpu
    zqpy
    · refine hM.not_left_of_after hF hcw hAw hBw hne1 hR hpy ztklt
        ztcmb hRf ?_
      zukwk
      have hm : lerp v uw ztcn ∈ cw := by
        zuoxs; exact lerp_mem_segment _ _ by_norm_num by_norm_num
      refine (eventually_mul_pos (hRw _ hm (hopenw _ ztfm))
        ztwfx).mono fun δ h => ?_
      rw [Chazelle.Core.offset_mid_ab huwy.symm]
      convert h using 2; ring
    · refine hM.not_left_of_after hF hce hBe hAe hne2 hR hpy ztklt
        ztcmb hRf ?_
      zukwj
      have hm : lerp we v ztcn ∈ ce := by
        rw [hceq, Geometry.segment_comm]; exact lerp_mem_segment _ _ by_norm_num by_norm_num
      refine (eventually_mul_pos (hRe _ hm (open_rev hopene _ ztfm))
        ztwfw).mono fun δ h => ?_
      rw [Chazelle.Core.offset_mid_ab hwey]
      convert h using 2; ring

/-- **Two distinct chords of `F` at one position go opposite ways.** -/
theorem tie_pair (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) {c c' : Set Point}
    (hc : c ∈ F) (hc' : c' ∈ F) (hne : c ≠ c') {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) :
    (ztdqa ∧ (∀ z ∈ c', z.1 ≤ (sidePt M.W p t).1)) ∨
      (ztdqb ∧ (∀ z ∈ c', (sidePt M.W p t).1 ≤ z.1)) := by
  rcases hM.attach_dir ztlz hA with h | h <;> rcases hM.attach_dir (hF hc') hA' with h' | h'
  · exact absurd (hM.attach_east_unique hF hc hc' hA hA' h h') hne
  · grind
  · grind
  · exact absurd (hM.attach_west_unique hF hc hc' hA hA' h h') hne

/-- **The shape of a tie**: for an east chord `ce` and a west chord `cw` of `F` attached at the
same position `(p, t)`, `t = 0`, the leaving walk edge is not horizontal, and every chord of `F`
attached at that position is `ce` or `cw` (so at most two chords are attached at one
position). -/
theorem tie_shape (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) {ce cw : Set Point}
    (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ} (hAe : SideAttach M.W ce p t)
    (hAw : SideAttach M.W cw p t) (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1)
    (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1) :
    t = 0 ∧ (M.wb p).2 ≠ (M.wa p).2 ∧ ∀ c ∈ F, SideAttach M.W c p t → c = ce ∨ c = cw := by
  obtain ⟨ht, s₁, s₂, hs₁, hs₂, hsE, hsW⟩ := hM.tie_setup ztgka ztgkb hAe hAw hE hW
  refine ⟨ht, fun h => (Tie.ccw_ew hs₁ hs₂ hsE hsW).1 by_simp_all,
    fun c hc hA => ?_⟩
  rcases hM.attach_dir ztlz hA with h | h
  · exact Or.inl (hM.attach_east_unique hF hc hce hA hAe h hE)
  · exact Or.inr (hM.attach_west_unique hF hc hcw hA hAw h hW)
end WalkAx
end
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbmn" : tactic => `(tactic| (have hxA : x ≠ A := by_grind
                                           have hxB : x ≠ B := by_grind
                                           have hyA : y ≠ A := by_grind
                                           have hyB : y ≠ B := by_grind))
local macro "zqbmo" : tactic => `(tactic| obtain ⟨-, V₀, l, -, -, hV₀, -, -, harc, -⟩ := hM.attach_face hF hfin hc hA)
local macro "zqbmp" : tactic => `(tactic| obtain ⟨s, h1, h2⟩ := (h₀.and hf).exists)
local macro "zqbmq" : tactic => `(tactic| have hne := fun h => hAB (off_inj hg hgn hA hAn hB hBn h))
set_option hygiene true

/-!
# The degree of the revised fusion, part 2: keys, offsets and faced regions (general models)

* `sideInArc_compl`, `off_same_side`, `off_sep`: cyclic intervals of keys read through offsets
  from a base key.
* `ncard_biUnion_le_mul`, `ncard_attKeys_le`: counting keys of attachments.
* `arc_start_of_faced`, `arc_end_of_faced`, `arc_end_of_faced_zero`, `faced_before_zero`: a region
  faced just after (before) a cut position has an arc starting (ending) there.
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft TouchesIn)
open Chazelle.Geometry (lerp)
open WalkEmbed
namespace FuseDeg
variable {M : Model}

/-! ## Cyclic intervals and offsets -/

/-- Away from its ends, a key is in exactly one of the two cyclic intervals between them. -/
theorem sideInArc_compl {a b x : ℝ} (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    sideInArc a b x ↔ ¬ sideInArc b a x := by
  zuiq
variable {n g A B x y : ℝ}
/-- **Two keys with no end of `(A, B)` between them are on the same side.** -/
theorem off_same_side (hg : 0 ≤ g) (hgn : g < n) (hA : 0 ≤ A) (hAn : A < n)
    (hB : 0 ≤ B) (hBn : B < n) (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y) (hyn : y < n)
    (hAB : A ≠ B) (hxy : off n g x ≤ off n g y)
    (hA' : off n g A < off n g x ∨ off n g y < off n g A)
    (hB' : off n g B < off n g x ∨ off n g y < off n g B) :
    sideInArc A B x ↔ sideInArc A B y := by
  zqbmq
  zqbmn
  zuto
  · rw [sideInArc_iff_off hg hgn hA hAn hB hBn hx hxn h,
      sideInArc_iff_off hg hgn hA hAn hB hBn hy hyn h]
    grind
  · rw [sideInArc_compl hAB hxA hxB, sideInArc_compl hAB hyA hyB,
      sideInArc_iff_off hg hgn hB hBn hA hAn hx hxn h,
      sideInArc_iff_off hg hgn hB hBn hA hAn hy hyn h]
    grind

/-- **Two keys with both ends of `(A, B)` between them are on the same side.** -/
theorem off_same_side_in (hg : 0 ≤ g) (hgn : g < n) (hA : 0 ≤ A) (hAn : A < n)
    (hB : 0 ≤ B) (hBn : B < n) (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y) (hyn : y < n)
    (hAB : A ≠ B) (hA' : off n g x < off n g A ∧ off n g A < off n g y)
    (hB' : off n g x < off n g B ∧ off n g B < off n g y) :
    sideInArc A B x ↔ sideInArc A B y := by
  zqbmq
  zqbmn
  obtain ⟨h1, h2⟩ := hA'
  obtain ⟨h3, h4⟩ := hB'
  zuto
  · rw [sideInArc_iff_off hg hgn hA hAn hB hBn hx hxn h,
      sideInArc_iff_off hg hgn hA hAn hB hBn hy hyn h]
    grind
  · rw [sideInArc_compl hAB hxA hxB, sideInArc_compl hAB hyA hyB,
      sideInArc_iff_off hg hgn hB hBn hA hAn hx hxn h,
      sideInArc_iff_off hg hgn hB hBn hA hAn hy hyn h]
    grind

/-- **A chord with one end between two keys and the other outside separates them.** -/
theorem off_sep (hg : 0 ≤ g) (hgn : g < n) (hA : 0 ≤ A) (hAn : A < n)
    (hB : 0 ≤ B) (hBn : B < n) (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y) (hyn : y < n)
    (hA' : off n g x < off n g A ∧ off n g A < off n g y)
    (hB' : off n g B < off n g x ∨ off n g y < off n g B) :
    sideInArc A B x ↔ ¬ sideInArc A B y := by
  have hAB : A ≠ B := by_grind
  have hne : off n g A ≠ off n g B := by_grind
  zqbmn
  obtain ⟨h1, h2⟩ := hA'
  zuto
  · rw [sideInArc_iff_off hg hgn hA hAn hB hBn hx hxn h,
      sideInArc_iff_off hg hgn hA hAn hB hBn hy hyn h]
    grind
  · rw [sideInArc_compl hAB hxA hxB, sideInArc_compl hAB hyA hyB,
      sideInArc_iff_off hg hgn hB hBn hA hAn hx hxn h,
      sideInArc_iff_off hg hgn hB hBn hA hAn hy hyn h]
    grind

/-! ## Counting keys -/

/-- A finite union of sets of at most `k` elements has at most `k` times as many elements as
there are sets. -/
theorem ncard_biUnion_le_mul {ι α : Type*} {T : Set ι} (hT : T.Finite) (s : ι → Set α) {k : ℕ}
    (hs : ∀ i ∈ T, (s i).ncard ≤ k) : (⋃ i ∈ T, s i).ncard ≤ k * T.ncard := by
  classical
  have e : (⋃ i ∈ T, s i) = ⋃ i ∈ hT.toFinset, s i := by
    simp
  rw [e, Set.ncard_eq_toFinset_card T hT]
  refine (Chazelle.Chain.ncard_biUnion_finset_le _ _).trans ?_
  calc ∑ i ∈ hT.toFinset, (s i).ncard ≤ ∑ _i ∈ hT.toFinset, k :=
        Finset.sum_le_sum by_simp_all
    _ = k * hT.toFinset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The keys at which a set is attached. -/
def attKeys (M : Model) (c : Set Point) : Set ℝ :=
  {x | ∃ (p : ℕ) (t : ℝ), SideAttach M.W c p t ∧ x = p + t}

/-- **An admissible chord is attached at at most two keys** (one at each endpoint). -/
theorem ncard_attKeys_le (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    (attKeys M c).ncard ≤ 2 := by
  classical
  obtain ⟨a, b, hab, hce, -, hop, -, -⟩ := hM.ends c hc
  let f : ℝ → Point := fun x => sidePt M.W ⌊x⌋₊ ztpep
  have hkey : ∀ (p : ℕ) (t : ℝ), 0 ≤ t → t < 1 → f ztk = sidePt M.W p t := by
    intro p t ht ht1
    have hfl : ⌊(p : ℝ) + t⌋₊ = p := by
      zuorn; simp_all
    grind
  have hmaps : MapsTo f zttfe {a, b} := by
    zugbg
    rw [hkey p t hA.2.1 hA.2.2.1]
    have hq := hA.2.2.2.1
    zvnme at hq
    obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hq
    have hnD := hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
    zunl
    · zuqy
      · simp_all
      simp_all
    · left; zunvo
  have hinj : InjOn f zttfe := by
    rintro x ⟨p, t, hA, rfl⟩ y ⟨p', t', hA', rfl⟩ hxy
    rw [hkey p t hA.2.1 hA.2.2.1, hkey p' t' hA'.2.1 hA'.2.2.1] at hxy
    obtain ⟨rfl, rfl⟩ := hM.attach_unique hc hA hA' hxy
    rfl
  calc (attKeys M c).ncard ≤ ({a, b} : Set Point).ncard :=
        Set.ncard_le_ncard_of_injOn f hmaps hinj
    _ ≤ 2 := by_simp_all

/-- The keys at which the chords of a finite admissible set `T` are attached: at most `2 |T|`. -/
theorem ncard_attKeys_union_le (hM : WalkAx M) {T : Set ztf} (hT : T ⊆ M.Adm)
    (hfin : T.Finite) : (⋃ c ∈ T, attKeys M c).ncard ≤ 2 * T.ncard :=
  ncard_biUnion_le_mul hfin _ fun _c hc => ncard_attKeys_le hM (hT hc)

/-! ## Arcs at cut positions -/

/-- The positions just before a walk vertex face the region of an arc ending there. -/
theorem faced_before_zero {F : Set ztf} {V : Set Point} {l : ℝ} {p : ℕ}
    (hp : p < M.W.n) (harcV : M.IsArc F V l ztcfa) (hVne : l ≠ (p : ℝ) + 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ztcm zteb V := by
  zuevd
  · zuhyz

    have hl0' := lt_of_le_of_ne hl0 ztrpx
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 ztszs from
      by_simp_all)] with s hs hs'
    zufwh
    zukfp
    have hs2 : s < M.W.n - l := by_simp_all
    have e : ztcrd := by
      simp
    zuelq

    have hc : zticr := by_simp_all
    zuktq
    zuiq

  · zufes
    have e : ztxfk := by
      rw [show p + M.W.n - 1 = p - 1 + M.W.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt by_omega]
    zui
    refine harcV.2.2.2.2.2.2 _ _ by_omega by_simp_all by_simp_all ?_
    simp_all

/-- **A region faced just after a cut position has an arc starting there.** -/
theorem arc_start_of_faced (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    {U : Set Point} (hU : U ∈ M.regions F) (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p ztuf U) :
    ∃ r, M.IsArc F U ztk r := by
  obtain ⟨U₀, -, -, r, hU₀, -, -, harc, -, -⟩ := hM.attach_face hF hfin hc hA
  have h₀ := faced_after hA.1 hA.2.1 hA.2.2.1 harc (WalkAx.arc_cuts ztzx harc).2.2
  zqbmp
  exact ⟨r, (WalkAx.faces_unique hU₀ hU h1 h2) ▸ harc⟩

/-- **A region faced just before a cut position inside a walk edge has an arc ending there.** -/
theorem arc_end_of_faced (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t)
    (ht : 0 < t) {U : Set Point} (hU : U ∈ M.regions F)
    (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p ztfuw U) : ∃ l, M.IsArc F U l ztk := by
  zqbmo
  have h₀ := faced_before hA.1 ht hA.2.2.1 harc (WalkAx.arc_cuts ztzx harc).2.2
  zqbmp
  exact ztkmf

/-- **A region faced just before a cut walk vertex has an arc ending there.** -/
theorem arc_end_of_faced_zero (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {p : ℕ} (hA : SideAttach M.W c p 0)
    {U : Set Point} (hU : U ∈ M.regions F)
    (hf : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ztcm zteb U) :
    ∃ l, M.IsArc F U l ztcfa := by
  zqbmo
  have h₀ := faced_before_zero hA.1 harc (WalkAx.arc_cuts ztzx harc).2.2
  zqbmp
  exact ztkmf

/-! ## Non-cut keys near a key -/

/-- The keys just after a key are not cuts. -/
theorem eventually_not_cut_after (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (x : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), ¬ M.IsCut F ztkgy := by
  zubap
  have h := (Filter.eventually_all_finite hK (l := 𝓝[>] (0 : ℝ))
    (p := fun y s => x + s ≠ y)).2 fun y _ => by
      zuiei
      · zusq
        grind
      · zuhde

  grind

/-- The keys just before a key are not cuts. -/
theorem eventually_not_cut_before (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (x : ℝ) : ∀ᶠ s in 𝓝[>] (0 : ℝ), ¬ M.IsCut F ztfvh := by
  zubap
  have h := (Filter.eventually_all_finite hK (l := 𝓝[>] (0 : ℝ))
    (p := fun y s => x - s ≠ y)).2 fun y _ => by
      zuieh
      · zusq
        grind
      · zuhdd

  grind

/-- **Faced positions next to an adjacency**: if a region has an arc starting (ending) at the
position of offset `d + t` from the walk vertex `g`, then non-cut positions faced by it exist at
offsets just above (below) `d + t`. -/
theorem adj_near (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (hne : F.Nonempty) {g : ℕ} {R : Set Point} {d : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hdt : 0 < (d : ℝ) + t) (hadj : Adj M F R ztwje t) :
    (∀ b : ℝ, (d : ℝ) + t < b → ∃ (d₁ : ℕ) (t₁ : ℝ), d₁ ≤ d ∧ t₁ ∈ Ioo (0 : ℝ) 1 ∧
      (d : ℝ) + t < d₁ + t₁ ∧ (d₁ : ℝ) + t₁ < b ∧
      ¬ M.IsCut F ztxdh ∧ M.Faces ztxyu t₁ R) ∨
    (∀ a : ℝ, a < (d : ℝ) + t → ∃ (d₁ : ℕ) (t₁ : ℝ), d₁ ≤ d ∧ t₁ ∈ Ioo (0 : ℝ) 1 ∧
      a < d₁ + t₁ ∧ (d₁ : ℝ) + t₁ < d + t ∧
      ¬ M.IsCut F ztxdh ∧ M.Faces ztxyu t₁ R) := by
  have hn : ztbiy := by
    rcases hadj with ⟨r, h⟩ | ⟨l, h⟩
    · have := h.2.1; exact_mod_cast (h.1.trans_lt this)
    · have := h.2.2.2.1; exact_mod_cast (h.2.2.1.trans_lt this)
  zuioh
  zuejs
  · left
    intro b hb
    zuegk
    obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩ := (((h1.and (eventually_not_cut_after hM hF hfin
      ztdj)).and self_mem_nhdsWithin).and (Ioo_mem_nhdsGT (show (0 : ℝ) <
        min ztca (b - ztbcr) from by_simp_all))).exists
    zuizg
    have hs5 : s < 1 - t := by_simp_all
    have hs6 : s < b - ztbcr := by_simp_all
    grind
  · right
    zuge
    zucox
    · zuegl
      obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩ := (((h1.and (eventually_not_cut_before hM hF hfin
        ztdj)).and self_mem_nhdsWithin).and (Ioo_mem_nhdsGT (show (0 : ℝ) <
          min t (ztbcr - a) from by_simp_all))).exists
      zuizg
      have hs5 : ztslv := by_simp_all
      grind
    · zultg
      have hd1 : 1 ≤ d := by
        zulgr
        zufc
      zucvo

      zukvn
      obtain ⟨s, ⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩ := (((h1.and (eventually_not_cut_before hM hF hfin
        ztxfo)).and self_mem_nhdsWithin).and
        (Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (zttir - a) from
          by_simp_all))).exists
      zuizg
      have hs5 : ztdrm := by_simp_all
      have hs6 : s < zttir - a := by_simp_all
      have hc : ((d - 1 : ℕ) : ℝ) = d - 1 := by_simp_all
      refine ⟨d - 1, 1 - s, by_omega, by_simp_all, by_grind,
        by grind, ?_, hs1⟩
      grind

/-- The exit chords of `R` attached at an offset in `(0, L)` from `g` next to which `R` is faced,
and whose other attachment is outside the stretch (the *crossing* chords of a piece). -/
def CrossX (M : Model) (F : Set ztf) (R : Set Point) (g L : ℕ) : Set ztf :=
  {f | f ∈ exits M F R ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ 0 < (d : ℝ) + t ∧
    SideAttach M.W f ztwje t ∧ Adj M F R ztwje t ∧
    ∃ (pb : ℕ) (tb : ℝ), SideAttach M.W f pb tb ∧
      sidePt M.W pb tb ≠ sidePt M.W ztwje t ∧
      (off M.W.n g ztbd = 0 ∨ (L : ℝ) ≤ off M.W.n g ztbd)}

/-- The chords attached at the position of offset `o` from `g` (with vertex offset `< L`): at most
two. -/
theorem ncard_at_off_le (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (g L : ℕ) (o : ℝ) :
    {f | f ∈ F ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ o = d + t ∧
      SideAttach M.W f ztwje t}.ncard ≤ 2 := by
  by_cases h : ∃ (d : ℕ) (t : ℝ), 0 ≤ t ∧ t < 1 ∧ o = d + t
  · obtain ⟨d₀, t₀, ht₀, ht₀1, ho⟩ := h
    refine le_trans (Set.ncard_le_ncard ?_ ztvvg)
      (ncard_at_le hM hF hfin ztxyw t₀)
    rintro f ⟨hf, d, t, -, ht, ht1, ho', hA⟩
    obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj ht ht1 ht₀ ht₀1 (ho'.symm.trans ho)
    simp_all
  · have : {f | f ∈ F ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ o = d + t ∧
        SideAttach M.W f ztwje t} = ∅ := by
      grind
    zuedz

/-- **At most four crossing chords per piece**: the positions of crossing chords next to which
`R` is faced are at most two (the first and the last of `R`'s positions in the stretch), by the
separation of the walk by a chord. -/
theorem crossX_ncard_le (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {g L : ℕ} (hg : g < M.W.n) (hLn : L < M.W.n) {R : Set Point} (hR : R ∈ M.regions F) :
    (CrossX M F R g L).ncard ≤ 4 := by
  zucqo
  zuqi
  have hgR : ztcrg := by_simp_all
  set O : Set ℝ := {o | ∃ f ∈ exits M F R, ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧
    0 < (d : ℝ) + t ∧ SideAttach M.W f ztxym t ∧ Adj M F R ztxym t ∧
    (∃ (pb : ℕ) (tb : ℝ), SideAttach M.W f pb tb ∧
      sidePt M.W pb tb ≠ sidePt M.W ztxym t ∧
      (off n g ztbd = 0 ∨ (L : ℝ) ≤ off n g ztbd)) ∧ o = d + t} with hO
  have hkey : ∀ {p : ℕ}, p < n → ∀ {t : ℝ}, 0 ≤ t → t < 1 →
      0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < n := by
    intro p hp t ht ht1
    zuhuw

  have hLR : ztdrn := fun {d t} hd ht => by
    zuhve

  -- no three positions
  have hno3 : ∀ x ∈ O, ∀ y ∈ O, ∀ z ∈ O, x < y → y < z → False := by
    rintro _ ⟨f₁, hf₁, d₁, t₁, hd₁, ht₁, ht₁1, hdt₁, hA₁, hadj₁, -, rfl⟩
      _ ⟨f₂, hf₂, d₂, t₂, hd₂, ht₂, ht₂1, hdt₂, hA₂, hadj₂, ⟨pb, tb, hB, hBne, hBo⟩, rfl⟩
      _ ⟨f₃, hf₃, d₃, t₃, hd₃, ht₃, ht₃1, hdt₃, hA₃, hadj₃, -, rfl⟩ h12 h23
    have hne : F.Nonempty := ⟨f₁, hf₁.1⟩
    -- the separation by `f₂` of two faced positions on its two sides
    have hsep : ∀ {dx dy : ℕ} {tx ty : ℝ}, dx < n → dy < n → tx ∈ Ioo (0 : ℝ) 1 →
        ty ∈ Ioo (0 : ℝ) 1 → 0 < (dx : ℝ) + tx → (dx : ℝ) + tx < d₂ + t₂ →
        (d₂ : ℝ) + t₂ < dy + ty → (dy : ℝ) + ty < L →
        ¬ M.IsCut F ztdrq → M.Faces ztmyv tx R →
        ¬ M.IsCut F ztiet → M.Faces (zttko % n) ty R → False := by
      intro dx dy tx ty hdx hdy htx hty h0 h1 h2 h3 hcx hfx hcy hfy
      have hox : off n g _ = dx + tx := off_key hg hdx htx.1.le htx.2
      have hoy : off n g _ = dy + ty := off_key hg hdy hty.1.le hty.2
      have hoA : off n g _ = d₂ + t₂ :=
        off_key hg by_omega ht₂ ht₂1
      have hKx := hkey (Nat.mod_lt (g + dx) hn) htx.1.le htx.2
      have hKy := hkey (Nat.mod_lt zttko hn) hty.1.le hty.2
      have hKA := hkey ztzun ht₂ ht₂1
      have hKB := hkey hB.1 hB.2.1 hB.2.2.1
      have hs : M.Separates f₂ ztdrq ztiet := by
        refine ⟨ztdur % n, pb, t₂, tb, hA₂, hB, Ne.symm hBne, ?_⟩
        refine off_sep ztdys hgR hKA.1 hKA.2 hKB.1 hKB.2 hKx.1 hKx.2 hKy.1 hKy.2
          by_grind ?_
        grind
      exact ((hM.eq_iff_not_separates hF hfin hR hR zthp zthp htx hty
        hcx hcy hfx hfy).1 rfl) f₂ hf₂.1 hs
    -- a faced position of `R` near the first position, below the second
    obtain ⟨dx, tx, hdx, htx, hx0, hx1, hcx, hfx⟩ : ∃ (dx : ℕ) (tx : ℝ), dx ≤ d₁ ∧
        tx ∈ Ioo (0 : ℝ) 1 ∧ 0 < (dx : ℝ) + tx ∧ (dx : ℝ) + tx < d₂ + t₂ ∧
        ¬ M.IsCut F ztdrq ∧ M.Faces ztmyv tx R := by
      rcases adj_near hM hF hfin hne ht₁ ht₁1 hdt₁ hadj₁ with h | h
      · obtain ⟨dx, tx, hdx, htx, h1, h2, h3, h4⟩ := h _ h12
        exact ⟨dx, tx, hdx, htx, by_linarith, h2, h3, h4⟩
      · obtain ⟨dx, tx, hdx, htx, h1, h2, h3, h4⟩ := h 0 hdt₁
        exact ⟨dx, tx, hdx, htx, h1, by_linarith, h3, h4⟩
    -- a faced position of `R` near the third position, above the second
    obtain ⟨dz, tz, hdz, htz, hz0, hz1, hcz, hfz⟩ : ∃ (dz : ℕ) (tz : ℝ), dz ≤ d₃ ∧
        tz ∈ Ioo (0 : ℝ) 1 ∧ (d₂ : ℝ) + t₂ < dz + tz ∧ (dz : ℝ) + tz < L ∧
        ¬ M.IsCut F ((zttkp % n : ℕ) + tz) ∧ M.Faces (zttkp % n) tz R := by
      rcases adj_near hM hF hfin hne ht₃ ht₃1 hdt₃ hadj₃ with h | h
      · obtain ⟨dz, tz, hdz, htz, h1, h2, h3, h4⟩ := h _ (hLR hd₃ ht₃1)
        exact ⟨dz, tz, hdz, htz, by_linarith, h2, h3, h4⟩
      · obtain ⟨dz, tz, hdz, htz, h1, h2, h3, h4⟩ := h _ h23
        exact ⟨dz, tz, hdz, htz, h1, by zuoky, h3, h4⟩
    rcases adj_near hM hF hfin hne ht₂ ht₂1 hdt₂ hadj₂ with h | h
    · obtain ⟨dy, ty, hdy, hty, h1, h2, h3, h4⟩ := h _ h23
      exact hsep by_omega by_omega htx hty hx0 hx1 h1 (by zuoky)
        hcx hfx h3 h4
    · obtain ⟨dy, ty, hdy, hty, h1, h2, h3, h4⟩ := h _ h12
      exact hsep by_omega by_omega hty htz by_linarith h2 hz0 hz1 h3 h4 hcz hfz
  have hOfin : O.Finite := by
    refine ((hM.finite_cuts hF hfin).image zttut).subset ?_
    rintro _ ⟨f, hf, d, t, hd, ht, ht1, -, hA, -, -, rfl⟩
    exact ⟨_, ⟨f, hf.1, _, _, hA, rfl⟩, off_key hg by_omega ht ht1⟩
  have hO2 := ncard_le_two_of_no_three hno3
  have hsub : CrossX M F R g L ⊆ ⋃ o ∈ O, {f | f ∈ F ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧
      t < 1 ∧ o = d + t ∧ SideAttach M.W f ztwje t} := by
    rintro f ⟨hf, d, t, hd, ht, ht1, hdt, hA, hadj, hX⟩
    zucqw
    exact ⟨d + t, ⟨f, hf, d, t, hd, ht, ht1, hdt, hA, hadj, hX, rfl⟩,
      hf.1, d, t, hd, ht, ht1, rfl, hA⟩
  calc (CrossX M F R g L).ncard
      ≤ (⋃ o ∈ O, {f | f ∈ F ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ o = d + t ∧
          SideAttach M.W f _ t}).ncard :=
        Set.ncard_le_ncard hsub (hfin.subset (by
          simp))
    _ ≤ 2 * O.ncard := ncard_biUnion_le_mul hOfin _ fun o _ => ncard_at_off_le hM hF hfin g L o
    _ ≤ 4 := by_omega
