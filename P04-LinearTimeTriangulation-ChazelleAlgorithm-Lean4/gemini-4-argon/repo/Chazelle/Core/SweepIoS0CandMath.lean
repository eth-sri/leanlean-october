module

public import Chazelle.Core.SweepIoSpec
public import Chazelle.Core.SweepEvOrgM
public import Chazelle.Core.SweepIoClass

/-!
# The sweep RAM (WP-D), answers: stop and table candidates of a side-0 query (mathematics)

A *candidate origin* `o` for a point `w` of the walk of `C` and a direction `d` is a point off
the domains of `C` and `C₂` whose chord `shoot C o d` passes through `w` (`CandAt`).  For a query
point `z` of `C₁` other than the shared vertex (not above the top of `C₂`), `z` is in the domain
of `C₂`, so `z ≠ o`, and then `z` is the far end of the chord: `o = rayPt z (-d) τ` with
`τ = C.hitParam o d > 0` (`cand_ray`).  Two candidate origins for the same `z` and `d` are equal
(`cand_unique`: the nearer one would block the chord of the farther one).

* `z_mem_right_dom`, `z_not_mem_whole_dom`: the query point;
* `endOrigin_not_dom`, `stopOrig_not_dom`, `stopSet_eq`: the origins of stops and table entries;
* `off_inj`, `key_split`: offsets and keys of walk positions.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Set
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
open Sweep WalkEmbed

@[expose] public section

/-! ## The chord through the query point -/

/-- **The far end of a chord.**  If a point `z` off the domain lies on the chord seen from `o` in
direction `d`, and `z ≠ o`, then `z` is the first hit from `o`, at a positive parameter. -/
theorem origin_ray (C : Chain) {o z : Point} {d : ℝ} (_hd : d = 1 ∨ d = -1)
    (hz : z ∈ Merge.shoot C o d) (hzd : z ∉ C.dom) (hne : z ≠ o) :
    0 < C.hitParam o d ∧ z = rayPt o d (C.hitParam o d) := by
  set h := C.hitParam o d
  have h0 : 0 ≤ h := Merge.hitParam_nonneg C o d
  obtain ⟨s, hs0, hs1, hzs⟩ := hz
  simp only [rayPt_fst, rayPt_snd, sub_self, mul_zero, add_zero] at hzs
  have hzs' : z = rayPt o d (s * h) := by
    rw [hzs]; ext <;> simp only [rayPt_fst, rayPt_snd]; ring
  have hsh : 0 < s * h := by
    rcases (mul_nonneg hs0 h0).lt_or_eq with h1 | h1
    · exact h1
    · exfalso; apply hne; rw [hzs', ← h1]; ext <;> simp
  have hle : h ≤ s * h := Chain.hitParam_le_of_not_mem_dom C o d hsh (by rwa [← hzs'])
  have hpos : 0 < h := by
    rcases h0.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, mul_zero] at hsh; exact absurd hsh (lt_irrefl _)
  have hs : s = 1 := by
    have : 1 * h ≤ s * h := by linarith
    have := le_of_mul_le_mul_right this hpos
    linarith
  refine ⟨hpos, ?_⟩
  rw [hzs', hs, one_mul]

/-- The origin as a point of the ray from `z` in the opposite direction. -/
theorem origin_back {o : Point} {d τ : ℝ} {z : Point} (hz : z = rayPt o d τ) :
    o = rayPt z (-d) τ := by
  rw [hz]; ext <;> simp [rayPt_fst, rayPt_snd]

/-- **A candidate origin** for the walk point `w` and the direction `d`. -/
def CandAt (J : Merge.Junction) (o : Point) (d : ℝ) (w : Point) : Prop :=
  o ∉ J.whole.dom ∧ o ∉ J.right.dom ∧ w ∈ Merge.shoot J.whole o d

/-- **The ray to a candidate origin.**  For a point `z` of the domain of `C₂` off the domain of
`C`, a candidate origin is `rayPt z (-d) τ` with `τ = C.hitParam o d > 0`. -/
theorem cand_ray {J : Merge.Junction} {o z : Point} {d : ℝ} (hd : d = 1 ∨ d = -1)
    (h : CandAt J o d z) (hz : z ∈ J.right.dom) (hzw : z ∉ J.whole.dom) :
    0 < J.whole.hitParam o d ∧ o = rayPt z (-d) (J.whole.hitParam o d) := by
  have hne : z ≠ o := fun he => h.2.1 (he ▸ hz)
  obtain ⟨hp, hr⟩ := origin_ray J.whole hd h.2.2 hzw hne
  exact ⟨hp, origin_back hr⟩

/-- **Uniqueness of the candidate origin.** -/
theorem cand_unique {J : Merge.Junction} {o₁ o₂ z : Point} {d : ℝ} (hd : d = 1 ∨ d = -1)
    (h₁ : CandAt J o₁ d z) (h₂ : CandAt J o₂ d z) (hz : z ∈ J.right.dom)
    (hzw : z ∉ J.whole.dom) : o₁ = o₂ := by
  obtain ⟨p₁, e₁⟩ := origin_ray J.whole hd h₁.2.2 hzw (fun he => h₁.2.1 (he ▸ hz))
  obtain ⟨p₂, e₂⟩ := origin_ray J.whole hd h₂.2.2 hzw (fun he => h₂.2.1 (he ▸ hz))
  set t₁ := J.whole.hitParam o₁ d
  set t₂ := J.whole.hitParam o₂ d
  have hy : o₁.2 = o₂.2 := by
    have a := congrArg Prod.snd e₁; have b := congrArg Prod.snd e₂
    simp only [rayPt_snd] at a b; rw [← a, ← b]
  have hx : o₁.1 + d * t₁ = o₂.1 + d * t₂ := by
    have a := congrArg Prod.fst e₁; have b := congrArg Prod.fst e₂
    simp only [rayPt_fst] at a b; rw [← a, ← b]
  -- the nearer origin blocks the chord of the farther one
  have key : ∀ (a b : Point) (ta tb : ℝ), a.2 = b.2 → a.1 + d * ta = b.1 + d * tb →
      0 < ta → ta < tb → tb = J.whole.hitParam b d → a ∉ J.whole.dom → False := by
    intro a b ta tb hab hxab h0 hlt htb ha
    have hpt : a = rayPt b d (tb - ta) := by
      ext
      · simp only [rayPt_fst]; linear_combination hxab
      · simp only [rayPt_snd]; exact hab
    have := Chain.hitParam_le_of_not_mem_dom J.whole b d (t := tb - ta) (by linarith)
      (by rwa [← hpt])
    linarith
  rcases lt_trichotomy t₁ t₂ with hl | he | hl
  · exact (key o₁ o₂ t₁ t₂ hy hx p₁ hl rfl h₁.1).elim
  · ext
    · rw [he] at hx; linarith
    · exact hy
  · exact (key o₂ o₁ t₂ t₁ hy.symm hx.symm p₂ hl rfl h₂.1).elim

/-! ## The query point -/

/-- A point of `C₁` other than the shared vertex, not above the top of `C₂`, is in the domain
of `C₂`. -/
theorem z_mem_right_dom {J : Merge.Junction} (hP : J.P.Simple) {z : Point} (hz : z ∈ J.left.set)
    (hzs : z ≠ J.shared) (hz2 : z.2 ≤ J.right.top.2) : z ∈ J.right.dom := by
  by_contra h
  rcases (Merge.not_mem_dom_iff J.right hz2).1 h with h1 | h1
  · exact h1 (J.left.set_subset_box hz)
  · have : z ∈ J.left.set ∩ J.right.set := ⟨hz, h1⟩
    rw [Merge.Junction.left_inter_right J hP] at this
    exact hzs this

/-- A point of `C₁` is off the domain of `C`. -/
theorem z_not_mem_whole_dom {J : Merge.Junction} {z : Point} (hz : z ∈ J.left.set) :
    z ∉ J.whole.dom :=
  J.whole.set_subset_dom_compl (J.left_set_subset hz)

/-! ## The origins -/

/-- The chord sets of a normal form of the model of `C₂` are augmented chords. -/
theorem chord_mem_F {M : Model} {Q : Polygon} {N : NF} {k : ℕ} (hk : k < N.nChords) :
    (N.chord k).toSet M Q ∈ N.F M Q := by
  refine ⟨N.chord k, ?_, rfl⟩
  unfold NF.chord
  rw [NFLoc.getD_of_lt _ hk]
  exact List.getElem_mem _

/-- **The ends of the chords of `N₂` are off the domains** of `C₂` and of `C`. -/
theorem endOrigin_not_dom (J : Merge.Junction) {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) Q N) {j : ℕ} (hj : j < 2 * N.nChords) :
    endOrigin J Q N j ∉ J.right.dom ∧ endOrigin J Q N j ∉ J.whole.dom := by
  have hk : j / 2 < N.nChords := by omega
  have hmem := chord_mem_F (M := chainModel J.right) (Q := Q) hk
  have haug : (N.chord (j / 2)).toSet (chainModel J.right) Q ∈ Merge.augChords J.right :=
    hN.1.2.1 hmem
  obtain ⟨y, a, b, hH, -, -, hl, hr⟩ := Merge.augChords_spec haug
  have hw := end_not_mem_dom J (S₂ := N.F (chainModel J.right) Q) (fun c hc => hN.1.2.1 hc) hmem
  unfold endOrigin
  split_ifs
  · rw [hl]; exact ⟨hH.left_not, hl ▸ hw.1⟩
  · rw [hr]; exact ⟨hH.right_not, hr ▸ hw.2⟩

/-- A point of `C₂` is off both domains. -/
theorem right_not_dom (J : Merge.Junction) {a : Point} (ha : a ∈ J.right.set) :
    a ∉ J.right.dom ∧ a ∉ J.whole.dom :=
  ⟨J.right.set_subset_dom_compl ha, J.whole.set_subset_dom_compl (J.right_set_subset ha)⟩

/-- **The origins of the stop records are off both domains.** -/
theorem stopOrig_not_dom (J : Merge.Junction) {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) Q N) {kind k b : ℕ} (_hkind : kind ≤ 2)
    (hk : kind = 1 → k < N.nChords) :
    stopOrig J Q N kind k b ∉ J.right.dom ∧ stopOrig J Q N kind k b ∉ J.whole.dom := by
  unfold stopOrig
  by_cases h0 : kind = 0
  · rw [ite_eq_left h0]; exact right_not_dom J J.shared_mem_right
  · rw [ite_eq_right h0]
    by_cases h1 : kind = 1
    · rw [ite_eq_left h1]
      have := hk h1
      exact endOrigin_not_dom J hN (by split_ifs <;> omega)
    · rw [ite_eq_right h1]; exact right_not_dom J J.right.top_mem_set

/-- The chord of a stop record is the chord seen from its origin. -/
theorem stopSet_eq (J : Merge.Junction) (Q : Polygon) (N : NF) (kind k b : ℕ) :
    stopSet J Q N kind k b = Merge.shoot J.whole (stopOrig J Q N kind k b) (dirOf b) := by
  unfold stopSet stopOrig
  split_ifs <;> rfl

/-! ## Offsets and keys -/

/-- **Offsets are injective** on the keys of a cycle. -/
theorem off_inj {n g x y : ℝ} (_hg0 : 0 ≤ g) (_hgn : g < n) (hx0 : 0 ≤ x) (hxn : x < n)
    (hy0 : 0 ≤ y) (hyn : y < n) (h : off n g x = off n g y) : x = y := by
  unfold off at h
  split_ifs at h <;> linarith

/-- A key with parameters in `[0, 1)` determines its edge and parameter. -/
theorem key_split {e e' : ℕ} {t t' : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (ht0' : 0 ≤ t')
    (ht1' : t' < 1) (h : (e : ℝ) + t = e' + t') : e = e' ∧ t = t' := by
  have hee : e = e' := by
    have h1 : (e : ℝ) < e' + 1 := by linarith
    have h2 : (e' : ℝ) < e + 1 := by linarith
    have h1' : e < e' + 1 := by exact_mod_cast h1
    have h2' : e' < e + 1 := by exact_mod_cast h2
    omega
  subst hee
  exact ⟨rfl, by linarith⟩

/-- The parameter of a point on a horizontal ray. -/
theorem rayPt_param {z : Point} {σ τ τ' : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : rayPt z σ τ = rayPt z σ τ') : τ = τ' := by
  have := congrArg Prod.fst h
  simp only [rayPt_fst] at this
  rcases hσ with rfl | rfl <;> linarith

end

end S0C

end SweepIo

end Chazelle.Core
