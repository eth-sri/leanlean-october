module

public import Chazelle.Core.DownPhaseHostRegion

/-!
# WP-M (H1, part 3): consecutive host keys

For a region `U` of a finite nonempty admissible family `F` (walk axioms), two host keys `a ≠ b`
with no host key strictly between them (cyclically) are joined either

* **(A)** inside an arc of `U` (the whole open interval `(a, b)` lies in one arc of `U`), or
* **(B)** by one chord of `F`: `a` and `b` are the keys of its two attachments.

This is `DownHost.WalkAx.gap`.  The proof: if `a` is not a cut, it is a walk vertex inside an
arc of `U`, case (A).  Otherwise let `X` and `Y` be the regions faced just after and just before
`a` (`attach_face`).  If `X = U`, case (A).  Otherwise an exit chord `c` of `U` attached at `a`,
with other end key `f`, has `U` off the side `K₁` of `c` containing the positions of `(a, f)`:
* if `U = Y`, `U` lies on the other side `K₂`;
* if `c` is the only chord at `a`, the regions touching `c` are `X` and `Y`, so `U ∈ {X, Y}`;
* at a tie (two chords at the vertex `a`), `U` is the region between both chords
  (`Model.TieDown`/`TieUp`), and the chord `c` touched by both `X` and `U` works, because two
  distinct regions touching a chord lie on different sides of it (`touch_sep`).
Then no host key lies in `(a, f)` (`host_side`) and `f` is a host key, so `b = f`.
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideSectorIn ChordSystem freeIn
  regionsIn TouchesIn)
open Chazelle.Geometry (lerp lerp_mem_segment point_ext)
open Chazelle.Jordan (offset nrm)

variable {M : Model} {F : Set (Set Point)} {U : Set Point}

/-! ## Cyclic facts -/

theorem cyc_first {a b f : ℝ} (hab : a ≠ b) (haf : a ≠ f) (h1 : ¬ sideInArc a f b)
    (h2 : ¬ sideInArc a b f) : b = f := by
  by_contra hbf
  have := lt_or_gt_of_ne hab
  have := lt_or_gt_of_ne haf
  have := lt_or_gt_of_ne hbf
  unfold sideInArc at *
  split_ifs at * <;> cyc_close

theorem cyc_sub_in {a b a' b' x : ℝ} (ha : sideInArc a' b' a) (h1 : ¬ sideInArc a b a')
    (h2 : ¬ sideInArc a b b') (hx : sideInArc a b x) : sideInArc a' b' x := by
  unfold sideInArc at *
  split_ifs at * <;> cyc_close

/-! ## Regions next to an attachment -/

/-- A region with an arc inside the side `(pa + ta, pb + tb)` of a chord `c` lies in the
component of that side. -/
theorem arc_in_side (hM : WalkAx M) (hne : F.Nonempty) {X : Set Point}
    (hX : X ∈ M.regions F) {u v : ℝ} (harc : M.IsArc F X u v) {c : Set Point} (hc : c ∈ F)
    {pa pb : ℕ} {ta tb : ℝ} (hsub : ∀ x, sideInArc u v x → sideInArc (pa + ta) (pb + tb) x)
    {k₁ : Point}
    (hK : ∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc (pa + ta) (pb + tb) (p + t) →
      SideSectorIn M.W (connectedComponentIn (M.D \ c) k₁) p t) :
    X ⊆ connectedComponentIn (M.D \ c) k₁ := by
  obtain ⟨p, hp, t, ht, hin, -, hfac⟩ := WalkAx.exists_pos_in_arc hne harc
  exact hM.region_subset_of_sector hc hX hp ht hfac (hK p hp t ht.1.le ht.2 (hsub _ hin))

/-- **Two distinct regions touching a chord lie in different components of the domain minus
the chord.** -/
theorem touch_sep (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) {c : Set Point}
    (hc : c ∈ F) {X Z : Set Point} (hX : X ∈ M.regions F) (hZ : Z ∈ M.regions F) (hXZ : X ≠ Z)
    (htX : TouchesIn M.D c X) (htZ : TouchesIn M.D c Z) {k : Point}
    (hXk : X ⊆ connectedComponentIn (M.D \ c) k) (hZk : Z ⊆ connectedComponentIn (M.D \ c) k) :
    False := by
  obtain ⟨Up, Dn, hUp, hDn, -, hside, htouch⟩ := chordSides_of_system (hM.sys F hF hfin) hc
  have hUDk : Up ⊆ connectedComponentIn (M.D \ c) k ∧ Dn ⊆ connectedComponentIn (M.D \ c) k := by
    rcases (htouch X hX).1 htX with rfl | rfl <;> rcases (htouch Z hZ).1 htZ with rfl | rfl
    · exact absurd rfl hXZ
    · exact ⟨hXk, hZk⟩
    · exact ⟨hZk, hXk⟩
    · exact absurd rfl hXZ
  obtain ⟨a, b, hab, hcab, hy, hopen, -, -⟩ := hM.ends c (hF hc)
  have hs := hM.hsep (hF hc) hcab hab hy hopen
  rw [← hcab] at hs
  set z := lerp a b (1 / 2) with hz
  have hzc : z ∈ c := by rw [hcab]; exact lerp_mem_segment _ _ (by norm_num) (by norm_num)
  have hzD : z ∈ M.D := hopen (1 / 2) ⟨by norm_num, by norm_num⟩
  set d := b.1 - a.1 with hd
  have hd0 : d ≠ 0 := by
    intro h; apply hab; exact point_ext (by rw [hd] at h; linarith) hy
  have hdpos : 0 < |d| := abs_pos.2 hd0
  obtain ⟨ε₀, hε₀, hs'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hs
  obtain ⟨ε₁, hε₁, hside'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hside z hzc hzD)
  rw [mem_Ioi] at hε₀ hε₁
  set δ := min ε₀ (ε₁ / |d|) / 2 with hδ
  have hδ0 : 0 < δ := by have := lt_min hε₀ (div_pos hε₁ hdpos); rw [hδ]; linarith
  have hδ1 : δ < ε₀ := by have := min_le_left ε₀ (ε₁ / |d|); rw [hδ]; linarith
  have hδ2 : δ * |d| < ε₁ := by
    have h1 : δ < ε₁ / |d| := by
      have := min_le_right ε₀ (ε₁ / |d|)
      rw [hδ]; linarith
    rwa [lt_div_iff₀ hdpos] at h1
  have hneq := hs' ⟨hδ0, hδ1⟩
  have e1 : offset a b (1 / 2) δ = (z.1, z.2 + δ * d) := by
    apply point_ext <;> simp [offset, nrm, lerp, hy, hz, hd]
  have e2 : offset b a (1 / 2) δ = (z.1, z.2 - δ * d) := by
    apply point_ext <;> simp [offset, nrm, lerp, hy, hz, hd] <;> ring
  have hmem : ∀ w, w ∈ Up ∨ w ∈ Dn →
      connectedComponentIn (M.D \ c) w = connectedComponentIn (M.D \ c) k := by
    rintro w (hw | hw)
    · exact (connectedComponentIn_eq (hUDk.1 hw)).symm
    · exact (connectedComponentIn_eq (hUDk.2 hw)).symm
  have hpt := hside' ⟨mul_pos hδ0 hdpos, hδ2⟩
  simp only [mem_ofPred_eq] at hpt
  apply hneq
  rw [e1, e2]
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · rw [abs_of_neg hneg] at hpt
    have e3 : z.2 + δ * d = z.2 - δ * -d := by ring
    have e4 : z.2 - δ * d = z.2 + δ * -d := by ring
    rw [e3, e4, hmem _ (Or.inr hpt.2), hmem _ (Or.inl hpt.1)]
  · rw [abs_of_pos hpos] at hpt
    rw [hmem _ (Or.inl hpt.1), hmem _ (Or.inr hpt.2)]

/-- The region with a given side relation to a chord (`AboveOf`) is the upper side region. -/
theorem eq_up_of_above (hM : WalkAx M) (hF : F ⊆ M.Adm) (_hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {Up Dn X : Set Point} (hUp : Up ∈ M.regions F)
    (hside : ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + δ) : Point) ∈ Up ∧
      ((z.1, z.2 - δ) : Point) ∈ Dn)
    (hX : X ∈ M.regions F) (hA : M.AboveOf c X) : X = Up := by
  obtain ⟨a, b, hab, hcab, -, hopen, -, -⟩ := hM.ends c (hF hc)
  have hzc : lerp a b (1 / 2) ∈ c := by
    rw [hcab]; exact lerp_mem_segment _ _ (by norm_num) (by norm_num)
  have hzD := hopen (1 / 2) ⟨by norm_num, by norm_num⟩
  obtain ⟨δ, h1, h2⟩ := ((hA _ hzc hzD).and (hside _ hzc hzD)).exists
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hUp with h | h
  · exact h
  · exact absurd (h.le_bot ⟨h1, h2.1⟩) (fun h => h)

/-- The region below a chord (`BelowOf`) is the lower side region. -/
theorem eq_dn_of_below (hM : WalkAx M) (hF : F ⊆ M.Adm) (_hfin : F.Finite)
    {c : Set Point} (hc : c ∈ F) {Up Dn X : Set Point} (hDn : Dn ∈ M.regions F)
    (hside : ∀ z ∈ c, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + δ) : Point) ∈ Up ∧
      ((z.1, z.2 - δ) : Point) ∈ Dn)
    (hX : X ∈ M.regions F) (hB : M.BelowOf c X) : X = Dn := by
  obtain ⟨a, b, hab, hcab, -, hopen, -, -⟩ := hM.ends c (hF hc)
  have hzc : lerp a b (1 / 2) ∈ c := by
    rw [hcab]; exact lerp_mem_segment _ _ (by norm_num) (by norm_num)
  have hzD := hopen (1 / 2) ⟨by norm_num, by norm_num⟩
  obtain ⟨δ, h1, h2⟩ := ((hB _ hzc hzD).and (hside _ hzc hzD)).exists
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hDn with h | h
  · exact h
  · exact absurd (h.le_bot ⟨h1, h2.2⟩) (fun h => h)

/-- Keys just before a walk vertex `p`: the position `((p + n - 1) mod n, t')` for `t'` close to
`1` lies in every open interval `(l, p)`. -/
theorem eventually_before_vertex {n p : ℕ} (hp : p < n) {l : ℝ} (hl0 : 0 ≤ l)
    (hln : l < n) (hlp : l ≠ p) :
    ∀ᶠ t' in 𝓝[<] (1 : ℝ), sideInArc l p (((p + n - 1) % n : ℕ) + t') := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · have e : (0 + n - 1) % n = n - 1 := by rw [zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have hn1 : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
    filter_upwards [Ioo_mem_nhdsLT (show l - (n - 1) < (1 : ℝ) by linarith)] with t ht
    unfold sideInArc
    rw [hn1]
    split_ifs with h
    · simp at h; linarith
    · left; linarith [ht.1]
  · have e : (p + n - 1) % n = p - 1 := by
      rw [show p + n - 1 = (p - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have hp1 : ((p - 1 : ℕ) : ℝ) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hp1]
    unfold sideInArc
    split_ifs with h
    · filter_upwards [Ioo_mem_nhdsLT (show l - (p - 1) < (1 : ℝ) by linarith),
        self_mem_nhdsWithin] with t ht ht1
      have : t < 1 := ht1
      exact ⟨by linarith [ht.1], by linarith⟩
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have : t < 1 := ht
      right; linarith

/-! ## The dichotomy -/

/-- **Consecutive host keys** `a ≠ b` of `U` (no host key strictly between them) are joined
inside an arc of `U` (A), or by one chord of `F` attached at `a` and at `b` (B). -/
theorem gap (hM : WalkAx M) (hF : F ⊆ M.Adm) (hfin : F.Finite) (hne : F.Nonempty)
    (hU : U ∈ M.regions F) {a b : ℝ} (ha : a ∈ hostKeys M F U) (hb : b ∈ hostKeys M F U)
    (hab : a ≠ b) (hgap : ∀ x ∈ hostKeys M F U, ¬ sideInArc a b x) :
    (∃ a' b' : ℝ, M.IsArc F U a' b' ∧ ∀ x, sideInArc a b x → sideInArc a' b' x) ∨
    (∃ c ∈ F, ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧ SideAttach M.W c p' t' ∧
      a = p + t ∧ b = p' + t' ∧ sidePt M.W p t ≠ sidePt M.W p' t') := by
  have hstart : ∀ {a' b' : ℝ}, M.IsArc F U a' b' → a' ∈ hostKeys M F U := fun harc => by
    obtain ⟨c, ⟨hc, ht⟩, p, t, hA, h⟩ := hM.exists_exit_at_start hF hfin hne hU harc
    exact Or.inl ⟨c, hc, ht, p, t, hA, h⟩
  have hend : ∀ {a' b' : ℝ}, M.IsArc F U a' b' → b' ∈ hostKeys M F U := fun harc => by
    obtain ⟨c, ⟨hc, ht⟩, p, t, hA, h⟩ := hM.exists_exit_at_end hF hfin hne hU harc
    exact Or.inl ⟨c, hc, ht, p, t, hA, h⟩
  by_cases hacut : M.IsCut F a
  swap
  · rcases ha with hx | ⟨k, hk, rfl, a', b', harc, hkin⟩
    · exact absurd (exitKeys_subset_cuts hx) hacut
    · exact Or.inl ⟨a', b', harc, fun x hx =>
        cyc_sub_in hkin (hgap _ (hstart harc)) (hgap _ (hend harc)) hx⟩
  obtain ⟨c₁, hc₁, p₀, t₀, hA₁, hak⟩ := hacut
  subst hak
  obtain ⟨X, Y, l, r, hX, hY, hXY, harcX, harcY, hsoleT⟩ := hM.attach_face hF hfin hc₁ hA₁
  by_cases hXU : X = U
  · subst hXU
    exact Or.inl ⟨_, r, harcX, fun x hx =>
      cyc_sub_start hx (hgap _ (hend harcX)) (WalkAx.arc_cuts hne harcX).2.2.symm⟩
  right
  have haex : (p₀ : ℝ) + t₀ ∈ exitKeys M F U := by
    rcases ha with hx | ⟨k, hk, hkeq, a', b', harc, hkin⟩
    · exact hx
    · rw [← hkeq] at hkin
      exact absurd ⟨c₁, hc₁, p₀, t₀, hA₁, rfl⟩ (harc.2.2.2.2.2.1 _ hkin)
  obtain ⟨c₀, hc₀, ht₀, p₁, t₁, hA₀, ha₀⟩ := haex
  obtain ⟨rfl, rfl⟩ := key_inj hA₁.2.1 hA₁.2.2.1 hA₀.2.1 hA₀.2.2.1 ha₀
  have hUne : U.Nonempty := Chazelle.Chain.regionsIn_nonempty hU
  -- the finishing argument, for a suitable exit chord `c` at `a`
  have finish : ∀ c ∈ F, TouchesIn M.D c U → SideAttach M.W c p₀ t₀ →
      (∀ k₁ k₂ : Point, X ⊆ connectedComponentIn (M.D \ c) k₁ →
        Y ⊆ connectedComponentIn (M.D \ c) k₂ →
        connectedComponentIn (M.D \ c) k₁ ≠ connectedComponentIn (M.D \ c) k₂ →
        ¬ U ⊆ connectedComponentIn (M.D \ c) k₁) →
      ∃ c ∈ F, ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧ SideAttach M.W c p' t' ∧
        (p₀ : ℝ) + t₀ = p + t ∧ b = p' + t' ∧ sidePt M.W p t ≠ sidePt M.W p' t' := by
    intro c hc htc hA hoff
    obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hF hc) hA
    have hAB : sidePt M.W p₀ t₀ ≠ sidePt M.W pb tb := fun h => hBne h.symm
    obtain ⟨K₁, K₂, hK12, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split (hF hc) hA hB hAB
    have hfa : (pb : ℝ) + tb ≠ p₀ + t₀ := fun h => WalkAx.key_ne_of_pt_ne hA hB hAB h.symm
    have hfcut : M.IsCut F ((pb : ℝ) + tb) := ⟨c, hc, pb, tb, hB, rfl⟩
    have hXs : X ⊆ connectedComponentIn (M.D \ c) k₁ :=
      arc_in_side hM hne hX harcX hc (fun x hx =>
        cyc_sub_start hx (fun h => harcX.2.2.2.2.2.1 _ h hfcut) hfa) hK₁
    have hYs : Y ⊆ connectedComponentIn (M.D \ c) k₂ :=
      arc_in_side hM hne hY harcY hc (fun x hx =>
        cyc_sub hx (fun h => harcY.2.2.2.2.2.1 _ h hfcut) hfa) hK₂
    have hnot := hoff k₁ k₂ hXs hYs hK12
    have hfh : (pb : ℝ) + tb ∈ hostKeys M F U := Or.inl ⟨c, hc, htc, pb, tb, hB, rfl⟩
    have hnone : ∀ x ∈ hostKeys M F U, ¬ sideInArc ((p₀ : ℝ) + t₀) (pb + tb) x :=
      fun x hx hin => hnot (host_side hM hF hfin hU hc hA hB hAB hK₁ hx hin)
    have hbf : b = pb + tb := cyc_first hab (Ne.symm hfa) (hnone b hb) (hgap _ hfh)
    exact ⟨c, hc, p₀, pb, t₀, tb, hA, hB, rfl, hbf, hAB⟩
  -- components met by a nonempty region are equal
  have hcomp : ∀ (c : Set Point) (k₁ k₂ : Point), U ⊆ connectedComponentIn (M.D \ c) k₁ →
      U ⊆ connectedComponentIn (M.D \ c) k₂ →
      connectedComponentIn (M.D \ c) k₁ = connectedComponentIn (M.D \ c) k₂ := by
    intro c k₁ k₂ h₁ h₂
    obtain ⟨u, hu⟩ := hUne
    rw [connectedComponentIn_eq (h₁ hu), connectedComponentIn_eq (h₂ hu)]
  by_cases hUY : U = Y
  · subst hUY
    exact finish c₀ hc₀ ht₀ hA₀ fun k₁ k₂ _ hYs hne' hU₁ => hne' (hcomp c₀ k₁ k₂ hU₁ hYs)
  by_cases hsole : ∀ c' ∈ F, SideAttach M.W c' p₀ t₀ → c' = c₀
  · exfalso
    obtain rfl := hsole c₁ hc₁ hA₁
    obtain ⟨htX, htY⟩ := hsoleT hsole
    obtain ⟨Up, Dn, -, -, -, -, htouch⟩ := chordSides_of_system (hM.sys F hF hfin) hc₁
    rcases (htouch X hX).1 htX with rfl | rfl <;> rcases (htouch Y hY).1 htY with rfl | rfl <;>
      rcases (htouch U hU).1 ht₀ with rfl | rfl <;> simp_all
  push Not at hsole
  obtain ⟨c', hc', hA', hc'0⟩ := hsole
  -- the tie at the vertex `a`
  have tie : ∀ ce cw : Set Point, ce ∈ F → cw ∈ F → SideAttach M.W ce p₀ t₀ →
      SideAttach M.W cw p₀ t₀ → (∀ z ∈ ce, (sidePt M.W p₀ t₀).1 ≤ z.1) →
      (∀ z ∈ cw, z.1 ≤ (sidePt M.W p₀ t₀).1) → (c₀ = ce ∨ c₀ = cw) →
      ∃ c ∈ F, ∃ (p p' : ℕ) (t t' : ℝ), SideAttach M.W c p t ∧ SideAttach M.W c p' t' ∧
        (p₀ : ℝ) + t₀ = p + t ∧ b = p' + t' ∧ sidePt M.W p t ≠ sidePt M.W p' t' := by
    intro ce cw hce hcw hAe hAw hE hW hc0
    obtain ⟨ht0, hhor, -⟩ := hM.tie_shape hF hce hcw hAe hAw hE hW
    subst ht0
    have hp₀ : p₀ < M.W.n := hAe.1
    have hl0 : 0 ≤ l := harcY.1
    have hln : l < M.W.n := harcY.2.1
    have hlp : l ≠ (p₀ : ℝ) + 0 := (WalkAx.arc_cuts hne harcY).2.2
    -- the region faced just after `a` is `X`, just before is `Y`
    have hafter : ∀ Z ∈ M.regions F, (∃ δ > (0 : ℝ), ∀ t', 0 < t' → t' < δ → M.Faces p₀ t' Z) →
        Z = X := by
      rintro Z hZ ⟨δ, hδ, hf⟩
      have hra : (p₀ : ℝ) + 0 ≠ r := (WalkAx.arc_cuts hne harcX).2.2
      obtain ⟨ε, ⟨hε0, hε1⟩, hin⟩ := ((ev_Ioo (lt_min hδ one_pos)).and
        (WalkAx.eventually_after_start hra)).exists
      have hin' : sideInArc ((p₀ : ℝ) + 0) r (p₀ + ε) := by simpa using hin
      exact WalkAx.faces_unique hZ hX (hf ε hε0 (lt_of_lt_of_le hε1 (min_le_left _ _)))
        (harcX.2.2.2.2.2.2 p₀ ε hp₀ hε0 (lt_of_lt_of_le hε1 (min_le_right _ _)) hin')
    have hbefore : ∀ Z ∈ M.regions F, (∃ δ > (0 : ℝ), ∀ t', 1 - δ < t' → t' < 1 →
        M.Faces ((p₀ + M.W.n - 1) % M.W.n) t' Z) → Z = Y := by
      rintro Z hZ ⟨δ, hδ, hf⟩
      have hlp' : l ≠ (p₀ : ℝ) := by rwa [add_zero] at hlp
      obtain ⟨t', ⟨ht'1, ht'2⟩, ht'3, hin⟩ := ((ev_Ioo_lt (show 1 - min δ 1 < (1 : ℝ) by
        linarith [lt_min hδ one_pos])).and ((ev_Ioo_lt (show (0 : ℝ) < 1 by norm_num)).and
        (eventually_before_vertex hp₀ hl0 hln hlp'))).exists
      have hq : (p₀ + M.W.n - 1) % M.W.n < M.W.n := Nat.mod_lt _ (by omega)
      have hin' : sideInArc l ((p₀ : ℝ) + 0) (((p₀ + M.W.n - 1) % M.W.n : ℕ) + t') := by
        rwa [add_zero]
      exact WalkAx.faces_unique hZ hY
        (hf t' (by linarith [min_le_left δ 1]) ht'2)
        (harcY.2.2.2.2.2.2 _ t' hq ht'3.1 ht'3.2 hin')
    obtain ⟨Upe, Dne, hUpe, hDne, hUDe, hsidee, htouche⟩ := chordSides_of_system (hM.sys F hF hfin) hce
    obtain ⟨Upw, Dnw, hUpw, hDnw, hUDw, hsidew, htouchw⟩ := chordSides_of_system (hM.sys F hF hfin) hcw
    rcases lt_or_gt_of_ne hhor with hdown | hup
    · obtain ⟨-, Ua, Vb, R, hUa, hVb, hR, hBe, hBw, hAe', hAw', hfa, hfb, -⟩ :=
        hM.tie_down hF hfin hce hcw hAe hAw hE hW hdown
      have hUaX := hafter Ua hUa hfa
      have hVbY := hbefore Vb hVb hfb
      have e1 := eq_dn_of_below hM hF hfin hce hDne hsidee hUa hBe
      have e2 := eq_up_of_above hM hF hfin hce hUpe hsidee hR hAe'
      have e3 := eq_dn_of_below hM hF hfin hcw hDnw hsidew hVb hBw
      have e4 := eq_up_of_above hM hF hfin hcw hUpw hsidew hR hAw'
      subst hUaX hVbY
      have hUR : U = R := by
        rcases hc0 with rfl | rfl
        · rcases (htouche U hU).1 ht₀ with h | h
          · exact h.trans e2.symm
          · exact absurd (h.trans e1.symm) (fun h' => hXU h'.symm)
        · rcases (htouchw U hU).1 ht₀ with h | h
          · exact h.trans e4.symm
          · exact absurd (h.trans e3.symm) hUY
      have htU : TouchesIn M.D ce U := (htouche U hU).2 (Or.inl (hUR.trans e2))
      have htX : TouchesIn M.D ce Ua := (htouche Ua hUa).2 (Or.inr e1)
      exact finish ce hce htU hAe fun k₁ k₂ hXs _ _ hU₁ =>
        touch_sep hM hF hfin hce hUa hU hXU htX htU hXs hU₁
    · obtain ⟨-, Ua, Vb, R, hUa, hVb, hR, hAw', hAe', hBe, hBw, hfa, hfb, -⟩ :=
        hM.tie_up hF hfin hce hcw hAe hAw hE hW hup
      have hUaX := hafter Ua hUa hfa
      have hVbY := hbefore Vb hVb hfb
      have e1 := eq_up_of_above hM hF hfin hcw hUpw hsidew hUa hAw'
      have e2 := eq_dn_of_below hM hF hfin hcw hDnw hsidew hR hBw
      have e3 := eq_up_of_above hM hF hfin hce hUpe hsidee hVb hAe'
      have e4 := eq_dn_of_below hM hF hfin hce hDne hsidee hR hBe
      subst hUaX hVbY
      have hUR : U = R := by
        rcases hc0 with rfl | rfl
        · rcases (htouche U hU).1 ht₀ with h | h
          · exact absurd (h.trans e3.symm) hUY
          · exact h.trans e4.symm
        · rcases (htouchw U hU).1 ht₀ with h | h
          · exact absurd (h.trans e1.symm) (fun h' => hXU h'.symm)
          · exact h.trans e2.symm
      have htU : TouchesIn M.D cw U := (htouchw U hU).2 (Or.inr (hUR.trans e2))
      have htX : TouchesIn M.D cw Ua := (htouchw Ua hUa).2 (Or.inl e1)
      exact finish cw hcw htU hAw fun k₁ k₂ hXs _ _ hU₁ =>
        touch_sep hM hF hfin hcw hUa hU hXU htX htU hXs hU₁
  rcases hM.tie_pair hF hc₀ hc' (Ne.symm hc'0) hA₀ hA' with ⟨hE, hW⟩ | ⟨hW, hE⟩
  · exact tie c₀ c' hc₀ hc' hA₀ hA' hE hW (Or.inl rfl)
  · exact tie c' c₀ hc' hc₀ hA' hA₀ hE hW (Or.inr rfl)

end

end DownHost

end Chazelle.Core
