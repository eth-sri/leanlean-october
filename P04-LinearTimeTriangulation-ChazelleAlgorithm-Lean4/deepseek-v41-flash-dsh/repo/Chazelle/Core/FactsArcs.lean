module

public import Chazelle.Golf

public import Chazelle.Core.FactsCut

/-!
# WP-B: arcs and exit chords alternate (`ArcsPerRegionSpec`)

For a model satisfying the walk axioms (every good model), a region `U` of a finite admissible
family `F` has finitely many arcs, and at most `deg F U + 1` of them (`WalkAx.arcs_bound`):

* `F = ∅`: the only arc is the pinned `(0, 0)`;
* `F ≠ ∅`: every arc `(a, b)` ends at a cut `b` where some **exit chord** of `U` (a chord of `F`
  touching `U`) is attached (`WalkAx.exists_exit_at_end`), and an exit chord is attached at the
  end of at most one arc (`WalkAx.arcEnd_injective`), so the number of arcs is at most the number
  of exit chords.

The key facts are the side-aware Lemma 2.1 (`WalkAx.split`) and the parenthesis structure of the
exit chords: `U` is also a region of the family of its exit chords (`region_of_exits`), so two
non-cut positions not separated by an exit chord face regions of `F` in the same region of the
exits, hence the same region of `F`.  Cyclic order facts on keys (`sideInArc`) are proved by case
analysis (`cyc_*`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft ChordSystem freeIn regionsIn TouchesIn
  sideKey_inj sideInArc_swap)
open Chazelle.Geometry (lerp point_ext lerp_mem_segment)

/-! ## Cyclic order of keys -/

/-- Closing tactic for the case analyses of cyclic betweenness. -/
macro "cyc_close" : tactic => `(tactic| (
  (try simp only [not_and_or, not_or, not_lt] at *) <;>
  (casesm* _ ∧ _, _ ∨ _) <;>
  first
  | linarith
  | (constructor! <;> linarith)
  | (left; constructor! <;> linarith) | (right; constructor! <;> linarith)
  | (left; linarith) | (right; linarith)))

/-- If `y` is strictly between `a` and `b` and `k ≠ b` is not, then `y` is strictly between `k`
and `b`. -/
theorem cyc_sub {a b y k : ℝ} (hy : sideInArc a b y) (hk : ¬ sideInArc a b k) (hkb : k ≠ b) :
    sideInArc k b y := by
  have := lt_or_gt_of_ne hkb
  unfold sideInArc at *
  split_ifs at * <;> cyc_close

/-- Rotation: for distinct `a, b, c`, `c` is between `a` and `b` iff `b` is not between `a`
and `c`. -/
theorem cyc_rot {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    sideInArc a b c ↔ ¬ sideInArc a c b := by
  have := lt_or_gt_of_ne hab
  have := lt_or_gt_of_ne hac
  have := lt_or_gt_of_ne hbc
  unfold sideInArc
  split_ifs <;> constructor <;> intro h <;> cyc_close

/-- Two keys in an interval free of `A` and `B` are on the same side of `A, B`. -/
theorem cyc_nosep {a x y A B : ℝ} (hy : sideInArc a x y) (hA : ¬ sideInArc a x A)
    (hB : ¬ sideInArc a x B) (hxA : x ≠ A) (hxB : x ≠ B) (hAB : A ≠ B) :
    sideInArc A B y ↔ sideInArc A B x := by
  have := lt_or_gt_of_ne hxA
  have := lt_or_gt_of_ne hxB
  have := lt_or_gt_of_ne hAB
  unfold sideInArc at *
  split_ifs at * <;> constructor <;> intro h <;> cyc_close

/-- Extending an arc `(a, b)` a little past its end `b` (to `x`, with no `a` in `(b, x]`). -/
theorem cyc_ext {a b x y k : ℝ} (hab : a ≠ b) (hy : sideInArc a b y) (hbx : b < x)
    (ha : ¬ (b < a ∧ a ≤ x)) (hk : ¬ sideInArc a b k) (hkb : k ≠ b) (hkx : ¬ (b < k ∧ k ≤ x)) :
    sideInArc a x y ∧ ¬ sideInArc a x k ∧ x ≠ k := by
  have := lt_or_gt_of_ne hab
  have := lt_or_gt_of_ne hkb
  refine ⟨?_, ?_, ?_⟩
  · unfold sideInArc at *
    split_ifs at * <;> cyc_close
  · unfold sideInArc at *
    split_ifs at * <;> intro h <;> cyc_close
  · rintro rfl; exact hkx ⟨hbx, le_rfl⟩

/-- Past the end `b` of an interval free of `k`, a key `x` is between `b` and `k`. -/
theorem cyc_after {b x k : ℝ} (hbx : b < x) (hkb : k ≠ b) (hkx : ¬ (b < k ∧ k ≤ x)) :
    sideInArc b k x := by
  have := lt_or_gt_of_ne hkb
  unfold sideInArc at *
  split_ifs at * <;> cyc_close

/-- Two intervals ending at `b` and free of each other's starts have the same start. -/
theorem cyc_start_eq {a a' b : ℝ} (ha : a ≠ b) (ha' : a' ≠ b) (h1 : ¬ sideInArc a b a')
    (h2 : ¬ sideInArc a' b a) : a = a' := by
  by_contra hne
  have := lt_or_gt_of_ne ha
  have := lt_or_gt_of_ne ha'
  have := lt_or_gt_of_ne hne
  unfold sideInArc at *
  split_ifs at * <;> cyc_close

namespace WalkAx

variable {M : Model}

/-! ## Cuts -/

/-- The chord points off the domain are finitely many. -/
theorem finite_chord_ends (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) : (⋃ c ∈ F, c \ M.D).Finite := by
  refine hfin.biUnion fun c hc => ?_
  obtain ⟨a, b, -, rfl, -, hopen, -, -⟩ := hM.ends c (hF hc)
  refine (Set.toFinite {a, b}).subset ?_
  rintro x ⟨hx, hxD⟩
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  rcases hs0.lt_or_eq with h0 | h0
  · rcases hs1.lt_or_eq with h1 | h1
    · exact absurd (hopen s ⟨h0, h1⟩) hxD
    · right; rw [h1, Geometry.lerp_one]; rfl
  · left; rw [← h0, Geometry.lerp_zero]

/-- **The cut keys are finitely many.** -/
theorem finite_cuts (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite) :
    {x : ℝ | M.IsCut F x}.Finite := by
  set E := ⋃ c ∈ F, c \ M.D with hE
  have hEf := hM.finite_chord_ends hF hfin
  have hsub : {x : ℝ | M.IsCut F x} ⊆
      ⋃ p ∈ Iio M.W.n, ⋃ e ∈ E, (fun t : ℝ => (p : ℝ) + t) ''
        {t : ℝ | sidePt M.W p t = e} := by
    rintro x ⟨c, hc, p, t, hA, rfl⟩
    ϴ mem_iUnion, mem_Iio, mem_image, mem_ofPred_eq
    refine ⟨p, hA.1, sidePt M.W p t, ?_, t, rfl, rfl⟩
    Ξ hE, mem_iUnion₂
    exact ⟨c, hc, hA.2.2.2.1, hM.trace p hA.1 t hA.2.1 hA.2.2.1.le⟩
  refine Set.Finite.subset ((finite_Iio _).biUnion fun p hp => hEf.biUnion fun e _ => ?_) hsub
  refine Set.Finite.image _ (Set.Subsingleton.finite ?_)
  intro t ht t' ht'
  exact lerp_injective_aux (hM.nd p hp) (ht.trans ht'.symm)
where
  lerp_injective_aux {u v : Point} (huv : u ≠ v) {t t' : ℝ} (h : lerp u v t = lerp u v t') :
      t = t' := Geometry.lerp_injective huv h

/-- **Uniqueness of the attachment at a point**: an admissible chord is attached at most once at
each of its points. -/
theorem attach_unique (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p p' : ℕ} {t t' : ℝ}
    (hA : SideAttach M.W c p t) (hA' : SideAttach M.W c p' t')
    (heq : sidePt M.W p t = sidePt M.W p' t') : p = p' ∧ t = t' := by
  by_contra hne
  obtain ⟨a, b, hab, rfl, -, hopen, ha, hb⟩ := hM.ends c hc
  -- the other endpoint
  obtain ⟨e', hend, hseq, he'⟩ : ∃ e', WalkEnd M.W (Chazelle.segment a b) (sidePt M.W p t) ∧
      Chazelle.segment a b = Chazelle.segment (sidePt M.W p t) e' ∧ e' ≠ sidePt M.W p t := by
    rcases hM.attach_endpoint hopen hA with h | h
    · exact ⟨b, h ▸ ha, by rw [h], by rw [h]; exact hab.symm⟩
    · exact ⟨a, h ▸ hb, by rw [h, Geometry.segment_comm], by rw [h]; exact hab⟩
  obtain ⟨-, hdisj⟩ := hend
  obtain ⟨r, hr, hsep⟩ := hdisj p p' t t' hA.1 hA.2.1 hA.2.2.1 hA'.1 hA'.2.1 hA'.2.2.1
    (fun h1 h2 => hne ⟨h1, h2⟩) rfl heq.symm
  obtain ⟨-, -, -, -, r₁, hr₁, h₁⟩ := hA
  obtain ⟨-, -, -, -, r₂, hr₂, h₂⟩ := hA'
  set q := sidePt M.W p t with hq
  set ρ := min r (min r₁ r₂) with hρ
  have hρ0 : 0 < ρ := lt_min hr (lt_min hr₁ hr₂)
  have hn : 0 < dist q e' + 1 := by positivity
  set s := min (ρ / (dist q e' + 1)) (1 / 2) with hs
  have hs0 : 0 < s := lt_min (div_pos hρ0 hn) (by norm_num)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  set x := lerp q e' s with hx
  have hxc : x ∈ Chazelle.segment q e' := lerp_mem_segment _ _ hs0.le hs1.le
  have hxq : x ≠ q := Chazelle.Jordan.lerp_ne_left (Ne.symm he') hs0
  have hdist : dist x q < ρ := by
    have e : dist x q = s * dist q e' := by
      rw [hx, dist_comm, dist_eq_norm, dist_eq_norm]
      have : q - lerp q e' s = s • (q - e') := by
        apply point_ext <;> simp [lerp] <;> ring
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    rw [e]
    have h1 : s ≤ ρ / (dist q e' + 1) := min_le_left _ _
    calc s * dist q e' < s * (dist q e' + 1) := by nlinarith
      _ ≤ ρ / (dist q e' + 1) * (dist q e' + 1) := mul_le_mul_of_nonneg_right h1 hn.le
      _ = ρ := div_mul_cancel₀ _ hn.ne'
  rw [hseq] at h₁ h₂
  have hl₁ := h₁ x hxc hxq (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hl₂ := h₂ x hxc (by rw [← heq]; exact hxq) (by
    rw [← heq]; exact hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  exact hsep x (by rw [mem_ball]; exact hdist.trans_le (min_le_left _ _)) hl₁ hl₂

/-- **The other attachment** of an attached admissible chord, at its other endpoint. -/
theorem other_attach (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) :
    ∃ p' t', SideAttach M.W c p' t' ∧ sidePt M.W p' t' ≠ sidePt M.W p t := by
  obtain ⟨a, b, hab, hcab, -, hopen, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ :=
    hM.ends c hc
  have hA' := hA
  rw [hcab] at hA'
  rcases hM.attach_endpoint hopen hA' with h | h
  · exact ⟨pb, tb, hBb, by rw [hBb', h]; exact hab.symm⟩
  · exact ⟨pa, ta, hAa, by rw [hAa', h]; exact hab⟩

/-! ## The region of the exit chords -/

/-- **A region is a region of its exit chords**: if `U` is a region of `F`, it is the component
of `u ∈ U` in the free set of the chords of `F` touching `U`. -/
theorem region_of_exits {F : Set (Set Point)} (hsys : ChordSystem M.D F) {U : Set Point}
    (hU : U ∈ regionsIn M.D F) {u : Point} (hu : u ∈ U) :
    U = connectedComponentIn (freeIn M.D {c | c ∈ F ∧ TouchesIn M.D c U}) u := by
  set T := {c | c ∈ F ∧ TouchesIn M.D c U} with hT
  have hTF : T ⊆ F := fun c hc => hc.1
  have hUF : U ⊆ freeIn M.D F := Chazelle.Chain.regionsIn_subset hU
  have hUT : U ⊆ freeIn M.D T := hUF.trans (Chazelle.Chain.freeIn_anti M.D hTF)
  have hUc := Chazelle.Chain.regionsIn_isPreconnected hU
  have hUo : IsOpen U := hsys.regionsIn_open subset_rfl hU
  apply Subset.antisymm (hUc.subset_connectedComponentIn hu hUT)
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hUo
    ⟨u, mem_connectedComponentIn (hUT hu), hu⟩ ?_
  rintro x ⟨hxc, hxK⟩
  have hxT : x ∈ freeIn M.D T := connectedComponentIn_subset _ _ hxK
  have hxF : x ∈ freeIn M.D F := by
    refine ⟨hxT.1, ?_⟩
    rintro ⟨c, hc, hxc'⟩
    exact hxT.2 ⟨c, ⟨hc, x, ⟨hxc', hxT.1⟩, hxc⟩, hxc'⟩
  have hpre : IsPreconnected (closure U ∩ freeIn M.D F) :=
    hUc.subset_closure (subset_inter subset_closure hUF) inter_subset_left
  have := hpre.subset_connectedComponentIn ⟨subset_closure hu, hUF hu⟩ inter_subset_right
  rw [← Chazelle.Chain.regionsIn_eq_component hU hu] at this
  exact this ⟨hxc, hxF⟩

/-! ## The arcs of a region -/

/-- A position just after a cut key, inside a walk edge, with no cut in between. -/
theorem exists_after (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} {t : ℝ} (_hp : p < M.W.n) (_ht : 0 ≤ t) (ht1 : t < 1) :
    ∃ t' ∈ Ioo t 1, ∀ k, M.IsCut F k → ¬ ((p : ℝ) + t < k ∧ k ≤ p + t') := by
  have hcf := hM.finite_cuts hF hfin
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k ∈ {x : ℝ | M.IsCut F x},
      ¬ ((p : ℝ) + t < k ∧ k ≤ p + (t + ε)) := by
    refine (hcf.eventually_all (p := fun k ε => ¬ ((p : ℝ) + t < k ∧ k ≤ p + (t + ε)))).2 ?_
    intro k _
    by_cases hk : (p : ℝ) + t < k
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < k - (p + t) by linarith)] with ε hε
      rintro ⟨-, h2⟩; linarith [hε.2]
    · exact Eventually.of_forall fun ε h => hk h.1
  obtain ⟨ε, h1, h2⟩ := (hall.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 - t by linarith))).exists
  exact ⟨t + ε, ⟨by linarith [h2.1], by linarith [h2.2]⟩, fun k hk => h1 k hk⟩

/-- A position inside an arc, just after its start. -/
theorem exists_in_arc {F : Set (Set Point)} {U : Set Point} {a b : ℝ}
    {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht : 0 ≤ t) (ht1 : t < 1) (ha : a = p + t)
    (harc : ∀ x, sideInArc a b x → ¬ M.IsCut F x)
    (hfac : ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 < t → t < 1 → sideInArc a b (p + t) →
      M.Faces p t U) :
    ∃ t' ∈ Ioo (0 : ℝ) 1, sideInArc a b (p + t') ∧ ¬ M.IsCut F (p + t') ∧ M.Faces p t' U := by
  set ε := if a < b then min (1 - t) (b - a) / 2 else (1 - t) / 2 with hε
  have hε0 : 0 < ε := by
    rw [hε]; split_ifs with h
    · have := lt_min (show 0 < 1 - t by linarith) (show 0 < b - a by linarith); linarith
    · linarith
  have hε1 : ε < 1 - t := by
    rw [hε]; split_ifs with h
    · have := min_le_left (1 - t) (b - a); linarith
    · linarith
  have hin : sideInArc a b (p + (t + ε)) := by
    unfold sideInArc
    split_ifs with h
    · have : ε < b - a := by
        have e : ε = min (1 - t) (b - a) / 2 := by simp [hε, h]
        rw [e]; have := min_le_right (1 - t) (b - a)
        have := lt_min (show 0 < 1 - t by linarith) (show 0 < b - a by linarith); linarith
      constructor <;> linarith
    · left; linarith
  exact ⟨t + ε, ⟨by linarith, by linarith⟩, hin, harc _ hin,
    hfac p (t + ε) hp (by linarith) (by linarith) hin⟩

/-- Unpacking an arc of a nonempty family. -/
theorem arc_cuts {F : Set (Set Point)} (hne : F.Nonempty) {U : Set Point} {a b : ℝ}
    (h : M.IsArc F U a b) : M.IsCut F a ∧ M.IsCut F b ∧ a ≠ b := by
  rcases h.2.2.2.2.1 with h' | ⟨h', -⟩
  · exact h'
  · exact absurd h' hne.ne_empty

/-- **The end of an arc carries an exit chord**: some chord of `F` touching `U` is attached at
the end key of every arc of `U`. -/
theorem exists_exit_at_end (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (hne : F.Nonempty) {U : Set Point} (hU : U ∈ M.regions F) {a b : ℝ}
    (harc : M.IsArc F U a b) :
    ∃ c ∈ {c | c ∈ F ∧ TouchesIn M.D c U}, ∃ p t, SideAttach M.W c p t ∧ b = p + t := by
  set T := {c | c ∈ F ∧ TouchesIn M.D c U} with hT
  have hTF : T ⊆ F := fun c hc => hc.1
  have hTfin : T.Finite := hfin.subset hTF
  have hsys := hM.sys F hF hfin
  obtain ⟨hcuta, hcutb, hab⟩ := arc_cuts hne harc
  obtain ⟨-, -, -, -, -, hfree, hfac⟩ := harc
  by_contra hno
  -- a position `y` inside the arc
  obtain ⟨c₁, hc₁, p₁, t₁, hA₁, ha₁⟩ := hcuta
  obtain ⟨ty, hty, hyin, hycut, hyf⟩ :=
    exists_in_arc (M := M) hA₁.1 hA₁.2.1 hA₁.2.2.1 ha₁ hfree hfac
  -- a position `x` just after the end
  obtain ⟨c₀, hc₀, pb, tb, hB₀, hb⟩ := hcutb
  obtain ⟨tx, htx, hxfree⟩ := hM.exists_after hF hfin hB₀.1 hB₀.2.1 hB₀.2.2.1
  have htx' : tx ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hB₀.2.1, htx.1], htx.2⟩
  have hbx : b < pb + tx := by rw [hb]; linarith [htx.1]
  have hxcut : ¬ M.IsCut F (pb + tx) := fun h => hxfree _ h ⟨⟡, le_rfl⟩
  rw [← hb] at hxfree
  -- the region of `F` faced at `x` is `U`
  obtain ⟨V, hV, hxV⟩ := hM.exists_faces_of_not_cut hF hfin hB₀.1 htx' hxcut
  obtain ⟨v, hv⟩ := Chazelle.Chain.regionsIn_nonempty hV
  obtain ⟨u, hu⟩ := Chazelle.Chain.regionsIn_nonempty hU
  have hVfree : V ⊆ freeIn M.D T :=
    (Chazelle.Chain.regionsIn_subset hV).trans (Chazelle.Chain.freeIn_anti M.D hTF)
  set VT := connectedComponentIn (freeIn M.D T) v with hVT
  have hVVT : V ⊆ VT :=
    (Chazelle.Chain.regionsIn_isPreconnected hV).subset_connectedComponentIn hv hVfree
  have hVTr : VT ∈ M.regions T := ⟨v, hVfree hv, rfl⟩
  have hUT : U = connectedComponentIn (freeIn M.D T) u := region_of_exits hsys hU hu
  have hUTr : U ∈ M.regions T := by
    Ξ hUT
    exact ⟨u, ((Chazelle.Chain.regionsIn_subset hU).trans
      (Chazelle.Chain.freeIn_anti M.D hTF)) hu, rfl⟩
  have hxVT : M.Faces pb tx VT := hxV.mono fun δ h => hVVT h
  have hTcut : ∀ k, M.IsCut T k → M.IsCut F k := fun k ⟨c, hc, h⟩ => ⟨c, hc.1, h⟩
  have hkeys : ∀ k, M.IsCut T k → ¬ sideInArc a b k ∧ k ≠ b ∧ ¬ (b < k ∧ k ≤ pb + tx) := by
    intro k hk
    refine ⟨fun h => hfree k h (hTcut k hk), ?_, fun h => hxfree k (hTcut k hk) h⟩
    rintro rfl
    obtain ⟨c, hc, p, t, h1, h2⟩ := hk
    exact hno ⟨c, hc, p, t, h1, h2⟩
  have ha_after : ¬ (b < a ∧ a ≤ pb + tx) := fun h => hxfree a ⟨c₁, hc₁, p₁, t₁, hA₁, ha₁⟩ h
  have hsame : VT = U := by
    refine (hM.eq_iff_not_separates (fun c hc => hF hc.1) hTfin hVTr hUTr hB₀.1 hA₁.1 htx'
      hty (fun h => hxcut (hTcut _ h)) (fun h => hycut (hTcut _ h)) hxVT hyf).2 ?_
    rintro c hc ⟨pa', pb', ta', tb', hA, hB, hAB, hiff⟩
    have hkA := hkeys _ ⟨c, hc, pa', ta', hA, rfl⟩
    have hkB := hkeys _ ⟨c, hc, pb', tb', hB, rfl⟩
    obtain ⟨hy', hA', hxA⟩ := cyc_ext hab hyin hbx ha_after hkA.1 hkA.2.1 hkA.2.2
    obtain ⟨-, hB', hxB⟩ := cyc_ext hab hyin hbx ha_after hkB.1 hkB.2.1 hkB.2.2
    have h := cyc_nosep hy' hA' hB' hxA hxB (key_ne_of_pt_ne hA hB hAB)
    exact (iff_not_self (hiff.trans (not_congr h))).elim
  have hVU : V ⊆ U := hsame ▸ hVVT
  have hVeq : V = U := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hV hU with h | h
    · exact h
    · exact absurd (h.le_bot ⟨hv, hVU hv⟩) (fun h => h)
  rw [hVeq] at hxV
  -- the chord `c₀` at `b` separates `y` from `x`
  obtain ⟨pa₀, ta₀, hA₀, hA₀ne⟩ := hM.other_attach (hF hc₀) hB₀
  obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split (hF hc₀) hA₀ hB₀ hA₀ne
  have hkA₀ : M.IsCut F (pa₀ + ta₀) := ⟨c₀, hc₀, pa₀, ta₀, hA₀, rfl⟩
  have hkne : (pa₀ : ℝ) + ta₀ ≠ b := by rw [hb]; exact key_ne_of_pt_ne hA₀ hB₀ hA₀ne
  have hyA : sideInArc (pa₀ + ta₀) (pb + tb) (p₁ + ty) := by
    rw [← hb]; exact cyc_sub hyin (fun h => hfree _ h hkA₀) hkne
  have hxA : sideInArc (pb + tb) (pa₀ + ta₀) (pb + tx) := by
    rw [← hb]; exact cyc_after hbx hkne (hxfree _ hkA₀)
  have hU1 := hM.region_subset_of_sector hc₀ hU hA₁.1 hty hyf
    (hK₁ p₁ hA₁.1 ty hty.1.le hty.2 hyA)
  have hU2 := hM.region_subset_of_sector hc₀ hU hB₀.1 htx' hxV
    (hK₂ pb hB₀.1 tx htx'.1.le htx'.2 hxA)
  exact hne ((connectedComponentIn_eq (hU1 hu)).trans (connectedComponentIn_eq (hU2 hu)).symm)

/-- A position inside an arc of a nonempty family, facing the region, off the cuts. -/
theorem exists_pos_in_arc {F : Set (Set Point)} (hne : F.Nonempty) {U : Set Point} {a b : ℝ}
    (harc : M.IsArc F U a b) :
    ∃ p < M.W.n, ∃ t ∈ Ioo (0 : ℝ) 1, sideInArc a b (p + t) ∧ ¬ M.IsCut F (p + t) ∧
      M.Faces p t U := by
  obtain ⟨hcuta, -, -⟩ := arc_cuts hne harc
  obtain ⟨-, -, -, -, -, hfree, hfac⟩ := harc
  obtain ⟨c₁, -, p₁, t₁, hA₁, ha₁⟩ := hcuta
  obtain ⟨t, ht, h1, h2, h3⟩ := exists_in_arc (M := M) hA₁.1 hA₁.2.1 hA₁.2.2.1 ha₁ hfree hfac
  exact ⟨p₁, hA₁.1, t, ht, h1, h2, h3⟩

/-- **Arcs and exit chords alternate**: a region of a finite admissible family has finitely many
arcs, and at most `deg + 1` of them (at most `deg` when the family is nonempty). -/
theorem arcs_bound (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) :
    {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2}.Finite ∧
      {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2}.ncard ≤ M.deg F U + 1 := by
  classical
  set S := {ab : ℝ × ℝ | M.IsArc F U ab.1 ab.2} with hS
  rcases F.eq_empty_or_nonempty with rfl | hne
  · have hsub : S ⊆ {((0 : ℝ), (0 : ℝ))} := by
      rintro ⟨a, b⟩ h
      rcases h.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, rfl, rfl⟩
      · exact absurd hc (notMem_empty c)
      · rfl
    refine ⟨(finite_singleton _).subset hsub, ?_⟩
    calc S.ncard ≤ ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)).ncard :=
          ncard_le_ncard hsub (finite_singleton _)
      _ = 1 := ncard_singleton _
      _ ≤ M.deg ∅ U + 1 := Nat.le_add_left _ _
  · set T := {c | c ∈ F ∧ TouchesIn M.D c U} with hT
    have hcf := hM.finite_cuts hF hfin
    have hSsub : S ⊆ {x | M.IsCut F x} ×ˢ {x | M.IsCut F x} := fun ab h =>
      ⟨(arc_cuts hne h).1, (arc_cuts hne h).2.1⟩
    have hSfin : S.Finite := (hcf.prod hcf).subset hSsub
    refine ⟨hSfin, ?_⟩
    let f : ℝ × ℝ → Set Point := fun ab =>
      if h : ∃ c ∈ T, ∃ p t, SideAttach M.W c p t ∧ ab.2 = p + t then h.choose else ∅
    have hf : ∀ ab ∈ S, f ab ∈ T ∧ ∃ p t, SideAttach M.W (f ab) p t ∧ ab.2 = p + t := by
      intro ab hab
      have h := hM.exists_exit_at_end hF hfin hne hU hab
      have e : f ab = h.choose := dite_eq_left h
      Ξ e
      exact h.choose_spec
    have hinj : InjOn f S := by
      rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
      obtain ⟨hcT, p, t, hA, hb⟩ := hf _ hab
      obtain ⟨-, p', t', hA', hb'⟩ := hf _ hab'
      rw [← heq] at hA'
      simp only at hb hb'
      set c := f (a, b)
      have hc := hcT.1
      obtain ⟨-, hcutb, hab0⟩ := arc_cuts hne hab
      obtain ⟨-, hcutb', hab0'⟩ := arc_cuts hne hab'
      have hfree := hab.2.2.2.2.2.1
      have hfree' := hab'.2.2.2.2.2.1
      by_cases hbb : b = b'
      · subst hbb
        have hcuta := (arc_cuts hne hab).1
        have hcuta' := (arc_cuts hne hab').1
        exact Prod.ext (cyc_start_eq hab0 hab0' (fun h => hfree _ h hcuta')
            (fun h => hfree' _ h hcuta)) rfl
      · exfalso
        have hAB : sidePt M.W p' t' ≠ sidePt M.W p t := by
          intro h
          obtain ⟨rfl, rfl⟩ := hM.attach_unique (hF hc) hA' hA h
          exact hbb (hb.trans hb'.symm)
        obtain ⟨K₁, K₂, hne', ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split (hF hc) hA' hA hAB
        obtain ⟨py, hpy, ty, hty, hyin, -, hyf⟩ := exists_pos_in_arc hne hab
        obtain ⟨py', hpy', ty', hty', hyin', -, hyf'⟩ := exists_pos_in_arc hne hab'
        have h1 : sideInArc (p' + t') (p + t) (py + ty) := by
          Ξ ← hb, ← hb'
          exact cyc_sub hyin (fun h => hfree _ h hcutb') (Ne.symm hbb)
        have h2 : sideInArc (p + t) (p' + t') (py' + ty') := by
          Ξ ← hb, ← hb'
          exact cyc_sub hyin' (fun h => hfree' _ h hcutb) hbb
        have hU1 := hM.region_subset_of_sector hc hU hpy hty hyf (hK₁ py hpy ty hty.1.le hty.2 h1)
        have hU2 := hM.region_subset_of_sector hc hU hpy' hty' hyf'
          (hK₂ py' hpy' ty' hty'.1.le hty'.2 h2)
        obtain ⟨u, hu⟩ := Chazelle.Chain.regionsIn_nonempty hU
        exact hne' ((connectedComponentIn_eq (hU1 hu)).trans
          (connectedComponentIn_eq (hU2 hu)).symm)
    calc S.ncard ≤ T.ncard :=
          ncard_le_ncard_of_injOn f (fun ab h => (hf ab h).1) hinj (hfin.subset fun c hc => hc.1)
      _ ≤ M.deg F U + 1 := Nat.le_succ _

end WalkAx

end

end Chazelle.Core

namespace Chazelle.Core

@[expose] public section

/-- **WP-B: arcs and exit chords alternate** (`ArcsPerRegionSpec`). -/
theorem arcsPerRegion : ArcsPerRegionSpec := by
  intro M Q F hM hF U hU
  exact (walkAx_of_goodModel hM).arcs_bound hF.2.1 hF.1 hU

end

end Chazelle.Core
