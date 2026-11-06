module

public import Chazelle.Core.FuseDegPos
public import Chazelle.Core.FuseMath

/-!
# The degree of the revised fusion, part 3: pieces and the one-region-per-piece argument

Let `J` be a junction, `C = J.whole`, `S' = J.fusion S₁ S₂ ∪ glueChords J`, and let a *piece* be a
stretch of the walk `W` of `C` agreeing with the walk `W'` of a side chain `C'` (`PieceAt`).

* `chord_transfer`: a chord of `Sᵢ` attached at a position of a piece gives a chord of `S'`
  attached at the same offset and contained in it (the fused chord at its endpoint, or a shared
  chord).
* `one_piece`: **the positions of one region `R` of `S'` inside a piece all face one region of
  `Sᵢ`** — a chord of `Sᵢ` separating two of them would give a chord of `S'` separating them.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft TouchesIn)
open Chazelle.Visibility (rayPt)
open Chazelle.Geometry (lerp)
open WalkEmbed FuseMath

namespace FuseDeg

variable (J : Merge.Junction)

/-- **A piece**: the walk of `C` from vertex `g` and the walk of the side chain `C'` from vertex
`g'` agree along `L` edges, and counted edges of the first are counted edges of the second. -/
def PieceAt (C' : Chain) (g g' L : ℕ) : Prop :=
  g < (chainModel J.whole).W.n ∧ g' < (chainModel C').W.n ∧ L < (chainModel J.whole).W.n ∧
    L ≤ (chainModel C').W.n ∧ Agree (chainModel J.whole).W (chainModel C').W g g' L ∧
    ∀ d, d < L → (chainModel J.whole).counted ((g + d) % (chainModel J.whole).W.n) →
      (chainModel C').counted ((g' + d) % (chainModel C').W.n)

/-- **Chord transfer along an agreement**: a chord of `Sᵢ` attached at an offset of an agreeing
stretch gives a chord of `S'` attached at the same offset of the walk of `C` and contained in
it. -/
theorem chord_transfer (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple)
    {Si S' : Set (Set Point)} (hsub : Si ⊆ Merge.augChords C')
    (hend : ∀ c ∈ Si, (Merge.lend c ≠ J.shared → ∃ e ∈ S', Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared → ∃ e ∈ S', Merge.rend c ∈ e ∧ e ⊆ c))
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hA : Agree (chainModel J.whole).W (chainModel C').W g g' L)
    {d : ℕ} (hd : d < L) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hdt : 0 < (d : ℝ) + t)
    {c : Set Point} (hcS : c ∈ Si)
    (hc : SideAttach (chainModel C').W c ((g' + d) % (chainModel C').W.n) t) :
    ∃ f ∈ S', SideAttach (chainModel J.whole).W f ((g + d) % (chainModel J.whole).W.n) t ∧
      f ⊆ c := by
  set W := (chainModel J.whole).W with hW
  set W' := (chainModel C').W with hW'
  have hn : 0 < W.n := by rw [hW, WalkEmbed.cm_n]; omega
  have hn' : 0 < W'.n := by rw [hW', WalkEmbed.cm_n]; omega
  have hdt' : t = 0 → 1 ≤ d := fun h => by
    rw [h, add_zero] at hdt; exact_mod_cast hdt
  set p' := (g' + d) % W'.n
  set q := sidePt W' p' t
  have hq : q ∈ c := hc.2.2.2.1
  have hqd : q ∉ C'.dom := (walkAx_chainModel hP').trace _ hc.1 t ht ht1.le
  obtain ⟨y, a, b, hH, hy, hceq, hl, hr⟩ := Merge.augChords_spec (hsub hcS)
  have hqe : q = (a, y) ∨ q = (b, y) := by
    have hq' := hq
    rw [hceq] at hq'
    obtain ⟨hq2, hqa, hqb⟩ := hq'
    rcases hqa.lt_or_eq with h1 | h1
    · rcases hqb.lt_or_eq with h2 | h2
      · exact absurd (by rw [show q = (q.1, y) from Prod.ext rfl hq2]; exact hH.open_mem q.1 h1 h2)
          hqd
      · right; exact Prod.ext h2 hq2
    · left; exact Prod.ext h1.symm hq2
  have hpt : sidePt W ((g + d) % W.n) t = q := hA.sidePt_eq hd t
  have hleft := hA.sideLeft_eq hn hn' hd hdt'
  by_cases hv : q = J.shared
  · obtain ⟨r, hr0, hsec⟩ := hc.2.2.2.2
    have hab := hH.lt
    obtain ⟨σ, hσ, hdir, hsubc⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        sideLeft W' p' t (rayPt q σ 1) ∧ Merge.shoot J.whole q σ ⊆ c := by
      set ε := min (r / 2) ((b - a) / 2)
      have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
      have hεr : ε < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hεb : ε ≤ (b - a) / 2 := min_le_right _ _
      rcases hqe with hqa | hqb
      · refine ⟨1, Or.inl rfl, (sideLeft_rayPt hε0).1 (hsec _ ?_ ?_ ?_), ?_⟩
        · show rayPt q 1 ε ∈ c
          rw [hceq, hqa]; refine ⟨rfl, ?_, ?_⟩ <;> simp only [rayPt] <;> linarith
        · intro e; have := congrArg Prod.fst e; simp only [rayPt] at this; linarith
        · rwa [dist_rayPt _ (Or.inl rfl) hε0.le]
        · rw [hqa, hceq]
          exact Merge.shoot_subset_pos J.whole hab (by rw [← hr]; exact (hends c hcS).2)
      · refine ⟨-1, Or.inr rfl, (sideLeft_rayPt hε0).1 (hsec _ ?_ ?_ ?_), ?_⟩
        · show rayPt q (-1) ε ∈ c
          rw [hceq, hqb]; refine ⟨rfl, ?_, ?_⟩ <;> simp only [rayPt] <;> linarith
        · intro e; have := congrArg Prod.fst e; simp only [rayPt] at this; linarith
        · rwa [dist_rayPt _ (Or.inr rfl) hε0.le]
        · rw [hqb, hceq]
          exact Merge.shoot_subset_neg J.whole hab (by rw [← hl]; exact (hends c hcS).1)
    have hl2 : sideLeft W ((g + d) % W.n) t (rayPt (sidePt W ((g + d) % W.n) t) σ 1) := by
      rwa [hleft, hpt]
    have hm₁ : J.m₁ ≤ J.whole.m := by rw [Merge.Junction.whole_m]; omega
    have hvq : sidePt W ((g + d) % W.n) t = J.whole.vertex J.m₁ := hpt.trans hv
    obtain ⟨hfree, hAt⟩ := sideAttach_shoot hP (Nat.mod_lt _ hn) ht ht1 hσ
      (by rw [hvq]; exact J.whole.vertex_snd_le_top hm₁) hl2
    rw [hvq] at hfree hAt
    refine ⟨_, hshared ⟨σ, hσ, hfree, rfl⟩, hAt, ?_⟩
    have e : J.whole.vertex J.m₁ = q := hv.symm
    show Merge.shoot J.whole (J.whole.vertex J.m₁) σ ⊆ c
    rwa [e]
  · obtain ⟨hL, hR⟩ := hend _ hcS
    rcases hqe with hqa | hqb
    · obtain ⟨e, he, hqe, hec⟩ := hL (by rwa [hl, ← hqa])
      rw [hl, ← hqa] at hqe
      exact ⟨e, he, hA.sideAttach_subset hn hn' hd hdt' hc hec hqe, hec⟩
    · obtain ⟨e, he, hqe, hec⟩ := hR (by rwa [hr, ← hqb])
      rw [hr, ← hqb] at hqe
      exact ⟨e, he, hA.sideAttach_subset hn hn' hd hdt' hc hec hqe, hec⟩


/-- The endpoints of an admissible chord are its only points off the domain. -/
theorem seg_end {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ u w : Point, c = Chazelle.segment u w ∧ ∀ z ∈ c, z ∉ M.D → z = u ∨ z = w := by
  obtain ⟨u, w, -, hcuw, -, hopc, -, -⟩ := hM.ends c hc
  refine ⟨u, w, hcuw, fun z hz hzD => ?_⟩
  rw [hcuw] at hz
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
  rcases hs0.lt_or_eq with h0 | h0
  · rcases hs1.lt_or_eq with h1 | h1
    · exact absurd (hopc s ⟨h0, h1⟩) hzD
    · right; rw [h1, Geometry.lerp_one]
  · left; rw [← h0, Geometry.lerp_zero]

/-- An admissible chord contained in another and containing both of its endpoints is equal to
it. -/
theorem eq_of_ends {M : Model} (hM : WalkAx M) {f c : Set Point} (hf : f ∈ M.Adm)
    (hfc : f ⊆ c) {u w : Point} (hcuw : c = Chazelle.segment u w) (hu : u ∈ f) (hw : w ∈ f) :
    f = c := by
  obtain ⟨a, b, -, hfab, -⟩ := hM.ends f hf
  refine le_antisymm hfc ?_
  rw [hcuw]
  exact Geometry.segment_subset_of_convex (hfab ▸ Geometry.segment_convex a b) hu hw

/-- **The core of `one_piece`**: no chord of `Sᵢ` separates the side positions of two non-cut
positions of a piece faced by one region of `S'`. -/
theorem one_piece_core (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple) {Q : Polygon}
    {Si S' : Set (Set Point)} (hSi : (chainModel C').ChordFamily Q Si)
    (hS'A : S' ⊆ (chainModel J.whole).Adm) (hS' : S'.Finite)
    (hend : ∀ c ∈ Si, (Merge.lend c ≠ J.shared → ∃ e ∈ S', Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared → ∃ e ∈ S', Merge.rend c ∈ e ∧ e ⊆ c))
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S')
    {d₁ d₂ : ℕ} {t₁ t₂ : ℝ} (hd₁ : d₁ < L) (hd₂ : d₂ < L) (ht₁ : t₁ ∈ Ioo (0 : ℝ) 1)
    (ht₂ : t₂ ∈ Ioo (0 : ℝ) 1) (hlt : (d₁ : ℝ) + t₁ < d₂ + t₂)
    (hc₁ : ¬ (chainModel J.whole).IsCut S' (((g + d₁) % (chainModel J.whole).W.n : ℕ) + t₁))
    (hc₂ : ¬ (chainModel J.whole).IsCut S' (((g + d₂) % (chainModel J.whole).W.n : ℕ) + t₂))
    (hf₁ : (chainModel J.whole).Faces ((g + d₁) % (chainModel J.whole).W.n) t₁ R)
    (hf₂ : (chainModel J.whole).Faces ((g + d₂) % (chainModel J.whole).W.n) t₂ R)
    {c : Set Point} (hc : c ∈ Si)
    (hsep : (chainModel C').Separates c (((g' + d₁) % (chainModel C').W.n : ℕ) + t₁)
      (((g' + d₂) % (chainModel C').W.n : ℕ) + t₂)) : False := by
  obtain ⟨hg, hg', hLn, hLn', hA, -⟩ := hpc
  set M := chainModel J.whole
  set M' := chainModel C'
  have hM : WalkAx M := walkAx_chainModel hP
  have hM' : WalkAx M' := walkAx_chainModel hP'
  set n := M.W.n
  set n' := M'.W.n
  have hn : 0 < n := by omega
  have hn' : 0 < n' := by omega
  have hgR : (g : ℝ) < n := by exact_mod_cast hg
  have hg'R : (g' : ℝ) < n' := by exact_mod_cast hg'
  have hkey : ∀ {N p : ℕ}, p < N → ∀ {t : ℝ}, 0 ≤ t → t < 1 →
      0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < N := by
    intro N p hp t ht ht1
    have : (p : ℝ) + 1 ≤ N := by exact_mod_cast hp
    exact ⟨by positivity, by linarith⟩
  have hLR : ∀ {d : ℕ} {t : ℝ}, d < L → t < 1 → (d : ℝ) + t < L := fun {d t} hd ht => by
    have : (d : ℝ) + 1 ≤ L := by exact_mod_cast hd
    linarith
  have hdL : ∀ {d : ℕ} {t : ℝ}, 0 ≤ t → (d : ℝ) + t < d₂ + t₂ → d < L := fun {d t} ht h => by
    have h' := hLR hd₂ ht₂.2
    have : (d : ℝ) < L := by linarith
    exact_mod_cast this
  set k₁ : ℝ := ((g + d₁) % n : ℕ) + t₁
  set k₂ : ℝ := ((g + d₂) % n : ℕ) + t₂
  set k₁' : ℝ := ((g' + d₁) % n' : ℕ) + t₁
  set k₂' : ℝ := ((g' + d₂) % n' : ℕ) + t₂
  have ho₁ : off n g k₁ = d₁ + t₁ := off_key hg (by omega) ht₁.1.le ht₁.2
  have ho₂ : off n g k₂ = d₂ + t₂ := off_key hg (by omega) ht₂.1.le ht₂.2
  have ho₁' : off n' g' k₁' = d₁ + t₁ := off_key hg' (by omega) ht₁.1.le ht₁.2
  have ho₂' : off n' g' k₂' = d₂ + t₂ := off_key hg' (by omega) ht₂.1.le ht₂.2
  have hK₁ := hkey (Nat.mod_lt (g + d₁) hn) ht₁.1.le ht₁.2
  have hK₂ := hkey (Nat.mod_lt (g + d₂) hn) ht₂.1.le ht₂.2
  have hK₁' := hkey (Nat.mod_lt (g' + d₁) hn') ht₁.1.le ht₁.2
  have hK₂' := hkey (Nat.mod_lt (g' + d₂) hn') ht₂.1.le ht₂.2
  -- the side positions are not cuts of `Sᵢ`
  have hnc : ∀ {d : ℕ} {t : ℝ}, d < L → t ∈ Ioo (0 : ℝ) 1 →
      ¬ M.IsCut S' (((g + d) % n : ℕ) + t) → ¬ M'.IsCut Si (((g' + d) % n' : ℕ) + t) := by
    rintro d t hd ht hnc ⟨c₀, hc₀, p₀, t₀, hA₀, hk₀⟩
    obtain ⟨hp, htt⟩ := Chazelle.Chain.sideKey_inj ht.1.le ht.2 hA₀.2.1 hA₀.2.2.1 hk₀
    rw [← hp, ← htt] at hA₀
    obtain ⟨f, hf, hAf, -⟩ := chord_transfer J hP hP' hSi.2.1 hend hends hshared hA hd ht.1.le
      ht.2 (by have := ht.1; positivity) hc₀ hA₀
    exact hnc ⟨f, hf, _, t, hAf, rfl⟩
  have hnc₁ := hnc hd₁ ht₁ hc₁
  have hnc₂ := hnc hd₂ ht₂ hc₂
  -- the case of a chord of `Sᵢ` with an end strictly between the two positions
  have inside : ∀ {pa pb : ℕ} {ta tb : ℝ}, SideAttach M'.W c pa ta → SideAttach M'.W c pb tb →
      sidePt M'.W pa ta ≠ sidePt M'.W pb tb →
      (sideInArc (pa + ta) (pb + tb) k₁' ↔ ¬ sideInArc (pa + ta) (pb + tb) k₂') →
      (d₁ : ℝ) + t₁ < off n' g' (pa + ta) → off n' g' (pa + ta) < d₂ + t₂ → False := by
    intro pa pb ta tb hA' hB' hne hiff h1 h2
    set dA := dOf n' g' pa
    have hpa : (g' + dA) % n' = pa := add_dOf hg' hA'.1
    have hoA : off n' g' (pa + ta) = dA + ta := off_key' hg' hA'.1 hA'.2.1 hA'.2.2.1
    rw [hoA] at h1 h2
    have hdAL : dA < L := hdL hA'.2.1 h2
    have hA'' : SideAttach M'.W c ((g' + dA) % n') ta := by rwa [hpa]
    have hdA0 : (0 : ℝ) < dA + ta := by linarith [ht₁.1, (Nat.cast_nonneg d₁ : (0 : ℝ) ≤ d₁)]
    obtain ⟨f, hf, hAf, hfc⟩ := chord_transfer J hP hP' hSi.2.1 hend hends hshared hA hdAL
      hA'.2.1 hA'.2.2.1 hdA0 hc hA''
    obtain ⟨pf, tf, hBf, hBfne⟩ := hM.other_attach (hS'A hf) hAf
    have hoA_W : off n g (((g + dA) % n : ℕ) + ta) = dA + ta :=
      off_key hg (by omega) hA'.2.1 hA'.2.2.1
    have hKA := hkey (Nat.mod_lt (g + dA) hn) hA'.2.1 hA'.2.2.1
    have hKF := hkey hBf.1 hBf.2.1 hBf.2.2.1
    have hofk : off n g (pf + tf) = dOf n g pf + tf := off_key' hg hBf.1 hBf.2.1 hBf.2.2.1
    -- the other end of `f` is outside the interval of the two positions
    have hof : off n g (pf + tf) < d₁ + t₁ ∨ d₂ + t₂ < off n g (pf + tf) := by
      by_contra hno
      push Not at hno
      obtain ⟨hlo, hhi⟩ := hno
      have hf1 : (pf : ℝ) + tf ≠ k₁ := fun h => hc₁ ⟨f, hf, pf, tf, hBf, h.symm⟩
      have hf2 : (pf : ℝ) + tf ≠ k₂ := fun h => hc₂ ⟨f, hf, pf, tf, hBf, h.symm⟩
      have hlo' : d₁ + t₁ < off n g (pf + tf) := lt_of_le_of_ne hlo fun h =>
        hf1 (off_inj (Nat.cast_nonneg g) hgR hKF.1 hKF.2 hK₁.1 hK₁.2 (by rw [ho₁]; exact h.symm))
      have hhi' : off n g (pf + tf) < d₂ + t₂ := lt_of_le_of_ne hhi fun h =>
        hf2 (off_inj (Nat.cast_nonneg g) hgR hKF.1 hKF.2 hK₂.1 hK₂.2 (by rwa [ho₂]))
      set dF := dOf n g pf
      have hpf : (g + dF) % n = pf := add_dOf hg hBf.1
      rw [hofk] at hlo' hhi'
      have hdFL : dF < L := hdL hBf.2.1 hhi'
      have hBf' : SideAttach M.W f ((g + dF) % n) tf := by rwa [hpf]
      have hdF1 : tf = 0 → 1 ≤ dF := by
        intro h0
        rw [h0, add_zero] at hlo'
        have : (0 : ℝ) < dF := by linarith [ht₁.1, (Nat.cast_nonneg d₁ : (0 : ℝ) ≤ d₁)]
        exact_mod_cast this
      have hBi : SideAttach M'.W f ((g' + dF) % n') tf :=
        (hA.sideAttach_iff hn hn' hdFL hdF1 f).1 hBf'
      have hptF : sidePt M.W ((g + dF) % n) tf = sidePt M'.W ((g' + dF) % n') tf :=
        hA.sidePt_eq hdFL tf
      have hptA : sidePt M.W ((g + dA) % n) ta = sidePt M'.W ((g' + dA) % n') ta :=
        hA.sidePt_eq hdAL ta
      obtain ⟨u, w, hcuw, hends2⟩ := seg_end hM' (hSi.2.1 hc)
      have hzA := hends2 _ hA'.2.2.2.1 (hM'.trace pa hA'.1 ta hA'.2.1 hA'.2.2.1.le)
      have hzB := hends2 _ hB'.2.2.2.1 (hM'.trace pb hB'.1 tb hB'.2.1 hB'.2.2.1.le)
      have hzF := hends2 _ (hfc hBi.2.2.2.1)
        (hM'.trace _ hBi.1 tf hBi.2.1 hBi.2.2.1.le)
      have hAF : sidePt M'.W pa ta ≠ sidePt M'.W ((g' + dF) % n') tf := by
        rw [← hptF, hpf, ← hpa, ← hptA]; exact Ne.symm hBfne
      have hBF : sidePt M'.W pb tb = sidePt M'.W ((g' + dF) % n') tf := by
        rcases hzA with h | h <;> rcases hzB with h' | h' <;> rcases hzF with h'' | h''
        all_goals first | exact h'.trans h''.symm | (exfalso; exact hne (h.trans h'.symm)) |
          (exfalso; exact hAF (h.trans h''.symm))
      -- `f` contains both ends of `c`, so `f = c`
      have hAf' : sidePt M'.W pa ta ∈ f := by
        rw [← hpa, ← hptA]; exact hAf.2.2.2.1
      have hFf : sidePt M'.W ((g' + dF) % n') tf ∈ f := hBi.2.2.2.1
      have hfeq : f = c := by
        rcases hzA with h | h <;> rcases hzF with h'' | h''
        · exact absurd (h.trans h''.symm) hAF
        · exact eq_of_ends hM (hS'A hf) hfc hcuw (h ▸ hAf') (h'' ▸ hFf)
        · exact eq_of_ends hM (hS'A hf) hfc hcuw (h'' ▸ hFf) (h ▸ hAf')
        · exact absurd (h.trans h''.symm) hAF
      rw [hfeq] at hBi
      obtain ⟨hpb, htb⟩ := hM'.attach_unique (hSi.2.1 hc) hB' hBi hBF
      have hoB : off n' g' (pb + tb) = dF + tf := by
        rw [hpb, htb]; exact off_key hg' (by omega) hBi.2.1 hBi.2.2.1
      have hKA' := hkey hA'.1 hA'.2.1 hA'.2.2.1
      have hKB' := hkey hB'.1 hB'.2.1 hB'.2.2.1
      have hsame := off_same_side_in (Nat.cast_nonneg g') hg'R hKA'.1 hKA'.2 hKB'.1 hKB'.2
        hK₁'.1 hK₁'.2 hK₂'.1 hK₂'.2 (Chazelle.Core.WalkAx.key_ne_of_pt_ne hA' hB' hne)
        ⟨by rwa [ho₁', hoA], by rwa [ho₂', hoA]⟩
        ⟨by rwa [ho₁', hoB], by rwa [ho₂', hoB]⟩
      exact iff_not_self (hsame.symm.trans hiff)
    -- so `f` separates the two positions in the walk of `C`
    have hsepf : M.Separates f k₁ k₂ := by
      refine ⟨(g + dA) % n, pf, ta, tf, hAf, hBf, Ne.symm hBfne, ?_⟩
      exact off_sep (Nat.cast_nonneg g) hgR hKA.1 hKA.2 hKF.1 hKF.2 hK₁.1 hK₁.2 hK₂.1 hK₂.2
        ⟨by rwa [ho₁, hoA_W], by rwa [ho₂, hoA_W]⟩
        (by rwa [ho₁, ho₂])
    exact ((hM.eq_iff_not_separates hS'A hS' hR hR (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) ht₁ ht₂
      hc₁ hc₂ hf₁ hf₂).1 rfl) f hf hsepf
  obtain ⟨pa, pb, ta, tb, hA', hB', hne, hiff⟩ := hsep
  have hKA' := hkey hA'.1 hA'.2.1 hA'.2.2.1
  have hKB' := hkey hB'.1 hB'.2.1 hB'.2.2.1
  have hAB := Chazelle.Core.WalkAx.key_ne_of_pt_ne hA' hB' hne
  have hA1 : (pa : ℝ) + ta ≠ k₁' := fun h => hnc₁ ⟨c, hc, pa, ta, hA', h.symm⟩
  have hA2 : (pa : ℝ) + ta ≠ k₂' := fun h => hnc₂ ⟨c, hc, pa, ta, hA', h.symm⟩
  have hB1 : (pb : ℝ) + tb ≠ k₁' := fun h => hnc₁ ⟨c, hc, pb, tb, hB', h.symm⟩
  have hB2 : (pb : ℝ) + tb ≠ k₂' := fun h => hnc₂ ⟨c, hc, pb, tb, hB', h.symm⟩
  have hoffne : ∀ {x y : ℝ}, 0 ≤ x → x < n' → 0 ≤ y → y < n' → x ≠ y →
      off n' g' x ≠ off n' g' y := fun hx hxn hy hyn hxy h =>
    hxy (off_inj (Nat.cast_nonneg g') hg'R hx hxn hy hyn h)
  by_cases hin : (d₁ : ℝ) + t₁ < off n' g' (pa + ta) ∧ off n' g' (pa + ta) < d₂ + t₂
  · exact inside hA' hB' hne hiff hin.1 hin.2
  by_cases hin' : (d₁ : ℝ) + t₁ < off n' g' (pb + tb) ∧ off n' g' (pb + tb) < d₂ + t₂
  · refine inside hB' hA' (Ne.symm hne) ?_ hin'.1 hin'.2
    rw [sideInArc_compl (Ne.symm hAB) (Ne.symm hB1) (Ne.symm hA1),
      sideInArc_compl (Ne.symm hAB) (Ne.symm hB2) (Ne.symm hA2)]
    exact not_congr hiff
  have hA1' := hoffne hKA'.1 hKA'.2 hK₁'.1 hK₁'.2 hA1
  have hA2' := hoffne hKA'.1 hKA'.2 hK₂'.1 hK₂'.2 hA2
  have hB1' := hoffne hKB'.1 hKB'.2 hK₁'.1 hK₁'.2 hB1
  have hB2' := hoffne hKB'.1 hKB'.2 hK₂'.1 hK₂'.2 hB2
  rw [ho₁'] at hA1' hB1'
  rw [ho₂'] at hA2' hB2'
  have hsame := off_same_side (Nat.cast_nonneg g') hg'R hKA'.1 hKA'.2 hKB'.1 hKB'.2
    hK₁'.1 hK₁'.2 hK₂'.1 hK₂'.2 hAB (by rw [ho₁', ho₂']; exact hlt.le)
    (by
      rw [ho₁', ho₂']
      by_contra h; push Not at h
      exact hin ⟨lt_of_le_of_ne h.1 (Ne.symm hA1'), lt_of_le_of_ne h.2 hA2'⟩)
    (by
      rw [ho₁', ho₂']
      by_contra h; push Not at h
      exact hin' ⟨lt_of_le_of_ne h.1 (Ne.symm hB1'), lt_of_le_of_ne h.2 hB2'⟩)
  exact iff_not_self (hsame.symm.trans hiff)


/-- A non-cut position of a piece has a non-cut side position. -/
theorem side_not_cut (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple)
    {Si S' : Set (Set Point)} (hsub : Si ⊆ Merge.augChords C')
    (hend : ∀ c ∈ Si, (Merge.lend c ≠ J.shared → ∃ e ∈ S', Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared → ∃ e ∈ S', Merge.rend c ∈ e ∧ e ⊆ c))
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hA : Agree (chainModel J.whole).W (chainModel C').W g g' L)
    {d : ℕ} (hd : d < L) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut S' (((g + d) % (chainModel J.whole).W.n : ℕ) + t)) :
    ¬ (chainModel C').IsCut Si (((g' + d) % (chainModel C').W.n : ℕ) + t) := by
  rintro ⟨c₀, hc₀, p₀, t₀, hA₀, hk₀⟩
  obtain ⟨hp, htt⟩ := Chazelle.Chain.sideKey_inj ht.1.le ht.2 hA₀.2.1 hA₀.2.2.1 hk₀
  rw [← hp, ← htt] at hA₀
  obtain ⟨f, hf, hAf, -⟩ := chord_transfer J hP hP' hsub hend hends hshared hA hd ht.1.le
    ht.2 (by have := ht.1; positivity) hc₀ hA₀
  exact hnc ⟨f, hf, _, t, hAf, rfl⟩

theorem separates_symm {M : Model} {c : Set Point} {x y : ℝ} (h : M.Separates c x y) :
    M.Separates c y x := by
  obtain ⟨pa, pb, ta, tb, hA, hB, hne, hiff⟩ := h
  refine ⟨pa, pb, ta, tb, hA, hB, hne, ?_⟩
  constructor
  · intro hy hx; exact (hiff.1 hx) hy
  · intro hx; by_contra hy; exact hx (hiff.2 hy)

/-- **One region of `Sᵢ` per piece**: two non-cut positions of a piece faced by one region of
`S'` have side positions facing one region of `Sᵢ`. -/
theorem one_piece (hP : J.P.Simple) {C' : Chain} (hP' : C'.P.Simple) {Q : Polygon}
    {Si S' : Set (Set Point)} (hSi : (chainModel C').ChordFamily Q Si)
    (hS'A : S' ⊆ (chainModel J.whole).Adm) (hS' : S'.Finite)
    (hend : ∀ c ∈ Si, (Merge.lend c ≠ J.shared → ∃ e ∈ S', Merge.lend c ∈ e ∧ e ⊆ c) ∧
      (Merge.rend c ≠ J.shared → ∃ e ∈ S', Merge.rend c ∈ e ∧ e ⊆ c))
    (hends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom)
    (hshared : J.sharedChords ⊆ S')
    {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S')
    {d₁ d₂ : ℕ} {t₁ t₂ : ℝ} (hd₁ : d₁ < L) (hd₂ : d₂ < L) (ht₁ : t₁ ∈ Ioo (0 : ℝ) 1)
    (ht₂ : t₂ ∈ Ioo (0 : ℝ) 1)
    (hc₁ : ¬ (chainModel J.whole).IsCut S' (((g + d₁) % (chainModel J.whole).W.n : ℕ) + t₁))
    (hc₂ : ¬ (chainModel J.whole).IsCut S' (((g + d₂) % (chainModel J.whole).W.n : ℕ) + t₂))
    (hf₁ : (chainModel J.whole).Faces ((g + d₁) % (chainModel J.whole).W.n) t₁ R)
    (hf₂ : (chainModel J.whole).Faces ((g + d₂) % (chainModel J.whole).W.n) t₂ R)
    {U₁ U₂ : Set Point} (hU₁ : U₁ ∈ (chainModel C').regions Si)
    (hU₂ : U₂ ∈ (chainModel C').regions Si)
    (hg₁ : (chainModel C').Faces ((g' + d₁) % (chainModel C').W.n) t₁ U₁)
    (hg₂ : (chainModel C').Faces ((g' + d₂) % (chainModel C').W.n) t₂ U₂) : U₁ = U₂ := by
  have hA := hpc.2.2.2.2.1
  have hn' : 0 < (chainModel C').W.n := by rw [WalkEmbed.cm_n]; omega
  have hnc₁ := side_not_cut J hP hP' hSi.2.1 hend hends hshared hA hd₁ ht₁ hc₁
  have hnc₂ := side_not_cut J hP hP' hSi.2.1 hend hends hshared hA hd₂ ht₂ hc₂
  refine ((walkAx_chainModel hP').eq_iff_not_separates hSi.2.1 hSi.1 hU₁ hU₂ (Nat.mod_lt _ hn')
    (Nat.mod_lt _ hn') ht₁ ht₂ hnc₁ hnc₂ hg₁ hg₂).2 fun c hc hsep => ?_
  rcases lt_trichotomy ((d₁ : ℝ) + t₁) (d₂ + t₂) with h | h | h
  · exact one_piece_core J hP hP' hSi hS'A hS' hend hends hshared hpc hR hd₁ hd₂ ht₁ ht₂ h
      hc₁ hc₂ hf₁ hf₂ hc hsep
  · obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj ht₁.1.le ht₁.2 ht₂.1.le ht₂.2 h
    obtain ⟨pa, pb, ta, tb, hA0, hB0, hne0, hiff0⟩ := hsep
    exact iff_not_self hiff0
  · exact one_piece_core J hP hP' hSi hS'A hS' hend hends hshared hpc hR hd₂ hd₁ ht₂ ht₁ h
      hc₂ hc₁ hf₂ hf₁ hc (separates_symm hsep)


/-- The data of one side of the junction used by the piece arguments. -/
structure SideOK (C' : Chain) (Q : Polygon) (Si S' : Set (Set Point)) : Prop where
  simple : C'.P.Simple
  fam : (chainModel C').ChordFamily Q Si
  endm : ∀ c ∈ Si, (Merge.lend c ≠ J.shared → ∃ e ∈ S', Merge.lend c ∈ e ∧ e ⊆ c) ∧
    (Merge.rend c ≠ J.shared → ∃ e ∈ S', Merge.rend c ∈ e ∧ e ⊆ c)
  ends : ∀ c ∈ Si, Merge.lend c ∉ J.whole.dom ∧ Merge.rend c ∉ J.whole.dom
  shared : J.sharedChords ⊆ S'
  adm : S' ⊆ (chainModel J.whole).Adm
  fin : S'.Finite

/-- A faced non-cut position of a piece has its side position facing the region `U` of `Sᵢ`
faced at one reference position. -/
theorem faces_ref (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si S' : Set (Set Point)}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S') {d₀ : ℕ} {t₀ : ℝ} (hd₀ : d₀ < L)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut S' (((g + d₀) % (chainModel J.whole).W.n : ℕ) + t₀))
    (hf₀ : (chainModel J.whole).Faces ((g + d₀) % (chainModel J.whole).W.n) t₀ R)
    {U : Set Point} (hU : U ∈ (chainModel C').regions Si)
    (hg₀ : (chainModel C').Faces ((g' + d₀) % (chainModel C').W.n) t₀ U)
    {d : ℕ} {t : ℝ} (hd : d < L) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut S' (((g + d) % (chainModel J.whole).W.n : ℕ) + t))
    (hf : (chainModel J.whole).Faces ((g + d) % (chainModel J.whole).W.n) t R) :
    (chainModel C').Faces ((g' + d) % (chainModel C').W.n) t U := by
  have hn' : 0 < (chainModel C').W.n := by rw [WalkEmbed.cm_n]; omega
  have hnc' := side_not_cut J hP hS.simple hS.fam.2.1 hS.endm hS.ends hS.shared hpc.2.2.2.2.1 hd ht
    hnc
  obtain ⟨U₁, hU₁, hg₁⟩ := (walkAx_chainModel hS.simple).exists_faces_of_not_cut hS.fam.2.1
    hS.fam.1 (Nat.mod_lt _ hn') ht hnc'
  rwa [one_piece J hP hS.simple hS.fam hS.adm hS.fin hS.endm hS.ends hS.shared hpc hR hd hd₀ ht ht₀
    hnc hnc₀ hf hf₀ hU₁ hU hg₁ hg₀] at hg₁

/-- **The positions of type (I)**: at a position of a piece next to which `R` is faced and at
whose side position a chord of `Sᵢ` is attached, some exit chord of the region `U` of `Sᵢ` faced
by `R`'s positions in the piece is attached. -/
theorem piece_I (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si S' : Set (Set Point)}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S') {d₀ : ℕ} {t₀ : ℝ} (hd₀ : d₀ < L)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut S' (((g + d₀) % (chainModel J.whole).W.n : ℕ) + t₀))
    (hf₀ : (chainModel J.whole).Faces ((g + d₀) % (chainModel J.whole).W.n) t₀ R)
    {U : Set Point} (hU : U ∈ (chainModel C').regions Si)
    (hg₀ : (chainModel C').Faces ((g' + d₀) % (chainModel C').W.n) t₀ U)
    {d : ℕ} {t : ℝ} (hd : d < L) (ht0 : 0 ≤ t) (ht1 : t < 1) (hdt : 0 < (d : ℝ) + t)
    (hne : S'.Nonempty)
    (hadj : Adj (chainModel J.whole) S' R ((g + d) % (chainModel J.whole).W.n) t)
    {c : Set Point} (hc : c ∈ Si)
    (hcA : SideAttach (chainModel C').W c ((g' + d) % (chainModel C').W.n) t) :
    ∃ c' ∈ exits (chainModel C') Si U,
      SideAttach (chainModel C').W c' ((g' + d) % (chainModel C').W.n) t := by
  set M := chainModel J.whole with hMdef
  set M' := chainModel C' with hM'def
  have hM : WalkAx M := walkAx_chainModel hP
  have hM' : WalkAx M' := walkAx_chainModel hS.simple
  have hn : 0 < M.W.n := by rw [hMdef, WalkEmbed.cm_n]; omega
  have hn' : 0 < M'.W.n := by rw [hM'def, WalkEmbed.cm_n]; omega
  set p := (g + d) % M.W.n
  set p' := (g' + d) % M'.W.n
  have hfaced : ∀ {d₁ : ℕ} {t₁ : ℝ}, d₁ < L → t₁ ∈ Ioo (0 : ℝ) 1 →
      ¬ M.IsCut S' (((g + d₁) % M.W.n : ℕ) + t₁) → M.Faces ((g + d₁) % M.W.n) t₁ R →
      M'.Faces ((g' + d₁) % M'.W.n) t₁ U :=
    fun hd₁ ht₁ hnc hf => faces_ref J hP hS hpc hR hd₀ ht₀ hnc₀ hf₀ hU hg₀ hd₁ ht₁ hnc hf
  rcases hadj with ⟨r, harc⟩ | ⟨l, harc⟩
  · have h1 := faced_after (Nat.mod_lt _ hn) ht0 ht1 harc (WalkAx.arc_cuts hne harc).2.2
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), M'.Faces p' (t + s) U := by
      filter_upwards [h1, eventually_not_cut_after hM hS.adm hS.fin ((p : ℝ) + t),
        self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 - t by linarith)]
        with s hs1 hs2 hs3 hs4
      have hs0 : (0 : ℝ) < s := hs3
      refine hfaced hd ⟨by linarith, by linarith [hs4.2]⟩ ?_ hs1
      rw [← add_assoc]; exact hs2
    obtain ⟨r', harc'⟩ := arc_start_of_faced hM' hS.fam.2.1 hS.fam.1 hc hcA hU h2
    obtain ⟨c', hc', p₁, t₁, hA₁, hk⟩ :=
      hM'.exists_exit_at_start hS.fam.2.1 hS.fam.1 ⟨c, hc⟩ hU harc'
    obtain ⟨hp₁, ht₁⟩ := Chazelle.Chain.sideKey_inj ht0 ht1 hA₁.2.1 hA₁.2.2.1 hk
    rw [← hp₁, ← ht₁] at hA₁
    exact ⟨c', hc', hA₁⟩
  · rcases ht0.lt_or_eq with ht0' | ht0'
    · have h1 := faced_before (Nat.mod_lt _ hn) ht0' ht1 harc (WalkAx.arc_cuts hne harc).2.2
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), M'.Faces p' (t - s) U := by
        filter_upwards [h1, eventually_not_cut_before hM hS.adm hS.fin ((p : ℝ) + t),
          self_mem_nhdsWithin, Ioo_mem_nhdsGT ht0'] with s hs1 hs2 hs3 hs4
        have hs0 : (0 : ℝ) < s := hs3
        refine hfaced hd ⟨by linarith [hs4.2], by linarith⟩ ?_ hs1
        rw [show (p : ℝ) + (t - s) = p + t - s by ring]; exact hs2
      obtain ⟨l', harc'⟩ := arc_end_of_faced hM' hS.fam.2.1 hS.fam.1 hc hcA ht0' hU h2
      obtain ⟨c', hc', p₁, t₁, hA₁, hk⟩ :=
        hM'.exists_exit_at_end hS.fam.2.1 hS.fam.1 ⟨c, hc⟩ hU harc'
      obtain ⟨hp₁, ht₁⟩ := Chazelle.Chain.sideKey_inj ht0 ht1 hA₁.2.1 hA₁.2.2.1 hk
      rw [← hp₁, ← ht₁] at hA₁
      exact ⟨c', hc', hA₁⟩
    · subst ht0'
      have hd1 : 1 ≤ d := by
        have : (0 : ℝ) < d := by linarith
        exact_mod_cast this
      have h1 := faced_before_zero (Nat.mod_lt _ hn) harc (WalkAx.arc_cuts hne harc).2.2
      have hpm : (p + M.W.n - 1) % M.W.n = (g + (d - 1)) % M.W.n := mod_pred_mod hn g hd1
      have hpm' : (p' + M'.W.n - 1) % M'.W.n = (g' + (d - 1)) % M'.W.n :=
        mod_pred_mod hn' g' hd1
      rw [hpm] at h1
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), M'.Faces ((p' + M'.W.n - 1) % M'.W.n) (1 - s) U := by
        rw [hpm']
        filter_upwards [h1, eventually_not_cut_before hM hS.adm hS.fin
          ((((g + (d - 1)) % M.W.n : ℕ) : ℝ) + 1), self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos]
          with s hs1 hs2 hs3 hs4
        have hs0 : (0 : ℝ) < s := hs3
        refine hfaced (by omega) ⟨by linarith [hs4.2], by linarith⟩ ?_ hs1
        rw [show (((g + (d - 1)) % M.W.n : ℕ) : ℝ) + (1 - s) =
          (((g + (d - 1)) % M.W.n : ℕ) : ℝ) + 1 - s by ring]
        exact hs2
      obtain ⟨l', harc'⟩ := arc_end_of_faced_zero hM' hS.fam.2.1 hS.fam.1 hc hcA hU h2
      obtain ⟨c', hc', p₁, t₁, hA₁, hk⟩ :=
        hM'.exists_exit_at_end hS.fam.2.1 hS.fam.1 ⟨c, hc⟩ hU harc'
      obtain ⟨hp₁, ht₁⟩ := Chazelle.Chain.sideKey_inj le_rfl one_pos hA₁.2.1 hA₁.2.2.1 hk
      rw [← hp₁, ← ht₁] at hA₁
      exact ⟨c', hc', hA₁⟩


/-- The chords of `S'` of type (I) in a piece: attached at an offset in `(0, L)` next to which `R`
is faced, where a chord of `Sᵢ` is attached at the side position. -/
def TypeI (C' : Chain) (Si S' : Set (Set Point)) (R : Set Point) (g g' L : ℕ) :
    Set (Set Point) :=
  {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ 0 < (d : ℝ) + t ∧
    SideAttach (chainModel J.whole).W f ((g + d) % (chainModel J.whole).W.n) t ∧
    Adj (chainModel J.whole) S' R ((g + d) % (chainModel J.whole).W.n) t ∧
    ∃ c ∈ Si, SideAttach (chainModel C').W c ((g' + d) % (chainModel C').W.n) t}

/-- **At most `4 D` chords of type (I) per piece**: their side positions carry exit chords of the
one region of `Sᵢ` faced there (`piece_I`), which has at most `D` exit chords, each attached at
at most two keys. -/
theorem typeI_ncard_le (hP : J.P.Simple) {C' : Chain} {Q : Polygon} {Si S' : Set (Set Point)}
    (hS : SideOK J C' Q Si S') {g g' L : ℕ} (hpc : PieceAt J C' g g' L) {R : Set Point}
    (hR : R ∈ (chainModel J.whole).regions S') {D : ℕ}
    (hdeg : (chainModel C').DegLe Si D) : (TypeI J C' Si S' R g g' L).ncard ≤ 4 * D := by
  have hpc' := hpc
  obtain ⟨hg, hg', hLn, hLn', hA, -⟩ := hpc
  set M := chainModel J.whole
  set M' := chainModel C'
  have hM : WalkAx M := walkAx_chainModel hP
  have hM' : WalkAx M' := walkAx_chainModel hS.simple
  have hn' : 0 < M'.W.n := by omega
  rcases (TypeI J C' Si S' R g g' L).eq_empty_or_nonempty with h0 | ⟨f₀, hf₀, d₀', t₀', hd₀',
    ht₀', ht₀'1, hdt₀', -, hadj₀, -⟩
  · rw [h0, Set.ncard_empty]; omega
  have hne : S'.Nonempty := ⟨f₀, hf₀⟩
  -- a reference position and the region of `Sᵢ` it faces
  obtain ⟨d₀, t₀, hd₀, ht₀, hc₀, hf₀'⟩ : ∃ (d₀ : ℕ) (t₀ : ℝ), d₀ < L ∧ t₀ ∈ Ioo (0 : ℝ) 1 ∧
      ¬ M.IsCut S' (((g + d₀) % M.W.n : ℕ) + t₀) ∧ M.Faces ((g + d₀) % M.W.n) t₀ R := by
    rcases adj_near hM hS.adm hS.fin hne ht₀' ht₀'1 hdt₀' hadj₀ with h | h
    · obtain ⟨d, t, hd, ht, -, -, h3, h4⟩ := h _ (lt_add_one _)
      exact ⟨d, t, by omega, ht, h3, h4⟩
    · obtain ⟨d, t, hd, ht, -, -, h3, h4⟩ := h _ (sub_one_lt _)
      exact ⟨d, t, by omega, ht, h3, h4⟩
  have hnc₀' := side_not_cut J hP hS.simple hS.fam.2.1 hS.endm hS.ends hS.shared hA hd₀ ht₀ hc₀
  obtain ⟨U, hU, hg₀⟩ := hM'.exists_faces_of_not_cut hS.fam.2.1 hS.fam.1 (Nat.mod_lt _ hn') ht₀
    hnc₀'
  -- the side keys
  set K' : Set ℝ := {k | ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ 0 < (d : ℝ) + t ∧
    Adj M S' R ((g + d) % M.W.n) t ∧
    (∃ c ∈ Si, SideAttach M'.W c ((g' + d) % M'.W.n) t) ∧ k = ((g' + d) % M'.W.n : ℕ) + t}
  have hcutsfin := hM'.finite_cuts hS.fam.2.1 hS.fam.1
  have hUnion : (⋃ c ∈ exits M' Si U, attKeys M' c) ⊆ {x | M'.IsCut Si x} := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨c, ⟨hc, -⟩, p, t, hAc, rfl⟩ := hx
    exact ⟨c, hc, p, t, hAc, rfl⟩
  have hK'sub : K' ⊆ ⋃ c ∈ exits M' Si U, attKeys M' c := by
    rintro k ⟨d, t, hd, ht, ht1, hdt, hadj, ⟨c, hc, hcA⟩, rfl⟩
    obtain ⟨c', hc', hA'⟩ := piece_I J hP hS hpc' hR hd₀ ht₀ hc₀ hf₀' hU hg₀ hd ht ht1 hdt hne
      hadj hc hcA
    simp only [Set.mem_iUnion]
    exact ⟨c', hc', _, t, hA', rfl⟩
  have hK'fin : K'.Finite := hcutsfin.subset (hK'sub.trans hUnion)
  have hexits : (exits M' Si U).ncard ≤ D := hdeg U hU
  have hK'le : K'.ncard ≤ 2 * D := by
    refine (Set.ncard_le_ncard hK'sub (hcutsfin.subset hUnion)).trans ?_
    refine (ncard_attKeys_union_le hM' (fun c hc => hS.fam.2.1 hc.1)
      (hS.fam.1.subset fun c hc => hc.1)).trans ?_
    omega
  -- the chords at one side key
  have hat : ∀ k : ℝ, {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧
      k = ((g' + d) % M'.W.n : ℕ) + t ∧ SideAttach M.W f ((g + d) % M.W.n) t}.ncard ≤ 2 := by
    intro k
    by_cases h : ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧ k = ((g' + d) % M'.W.n : ℕ) + t
    · obtain ⟨d₁, t₁, hd₁, ht₁, ht₁1, hk₁⟩ := h
      refine le_trans (Set.ncard_le_ncard ?_ (hS.fin.subset fun f hf => hf.1))
        (ncard_at_le hM hS.adm hS.fin ((g + d₁) % M.W.n) t₁)
      rintro f ⟨hf, d, t, hd, ht, ht1, hk, hAf⟩
      obtain ⟨hp, rfl⟩ := Chazelle.Chain.sideKey_inj ht ht1 ht₁ ht₁1 (hk.symm.trans hk₁)
      have := add_mod_inj (show d < M'.W.n by omega) (show d₁ < M'.W.n by omega) hp
      subst this
      exact ⟨hf, hAf⟩
    · have : {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧
          k = ((g' + d) % M'.W.n : ℕ) + t ∧ SideAttach M.W f ((g + d) % M.W.n) t} = ∅ := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
        intro _ d t hd ht ht1 hk _
        exact h ⟨d, t, hd, ht, ht1, hk⟩
      rw [this, Set.ncard_empty]; omega
  have hsub : TypeI J C' Si S' R g g' L ⊆ ⋃ k ∈ K', {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧
      0 ≤ t ∧ t < 1 ∧ k = ((g' + d) % M'.W.n : ℕ) + t ∧
      SideAttach M.W f ((g + d) % M.W.n) t} := by
    rintro f ⟨hf, d, t, hd, ht, ht1, hdt, hAf, hadj, hc⟩
    simp only [Set.mem_iUnion]
    exact ⟨_, ⟨d, t, hd, ht, ht1, hdt, hadj, hc, rfl⟩, hf, d, t, hd, ht, ht1, rfl, hAf⟩
  calc (TypeI J C' Si S' R g g' L).ncard
      ≤ (⋃ k ∈ K', {f | f ∈ S' ∧ ∃ (d : ℕ) (t : ℝ), d < L ∧ 0 ≤ t ∧ t < 1 ∧
          k = ((g' + d) % M'.W.n : ℕ) + t ∧ SideAttach M.W f ((g + d) % M.W.n) t}).ncard :=
        Set.ncard_le_ncard hsub (hS.fin.subset (by
          intro f hf; simp only [Set.mem_iUnion] at hf; obtain ⟨k, -, hf, -⟩ := hf; exact hf))
    _ ≤ 2 * K'.ncard := ncard_biUnion_le_mul hK'fin _ fun k _ => hat k
    _ ≤ 4 * D := by omega

end FuseDeg

end

end Chazelle.Core
