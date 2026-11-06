module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseMirrorWalk
public import Chazelle.Core.SpecBase

/-!
# Mirror symmetry (F-D7), part 4: mirrored disk models

`ModelMir M M' c`: the model `M'` is the mirror image of `M` (domain, admissible chords and full
map reflected by `mir`), its walk is the mirror image of the walk of `M` traversed backwards
(`WalkMir`, shift `c`), and the counted edges correspond.  Then, for the mirrored family
`mirF F` of a family `F`:

* the regions are the mirrored regions (`regions`), with the same degrees (`deg`, `degLe`);
* the cut keys are the reflected cut keys (`isCut`), the facing relation reverses the walk edge
  (`faces`), an arc `(a', b')` is the reflected arc `(rk b', rk a')` (`isArc`) with the same
  number of counted edges (`arcWt`), hence the weights agree (`weight`, `semigranular`);
* chord families correspond (`chordFamily`, for the mirrored height polygon).
-/

namespace Chazelle.Core

namespace Mir

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (freeIn regionsIn TouchesIn SideAttach sideInArc IsHChordIn)
open Chazelle.Visibility (hseg rayPt)

/-! ## Points, rays, horizontal segments -/

theorem mir_pt (x y : ℝ) : mir ((x, y) : Point) = (-x, y) := rfl

theorem mir_rayPt (p : Point) (σ t : ℝ) : mir (rayPt p σ t) = rayPt (mir p) (-σ) t := by
  apply Prod.ext <;> simp [mir, rayPt]; ring

theorem hseg_mir (y a b : ℝ) : mir '' hseg y a b = hseg y (-b) (-a) := by
  ext x
  Ξ mem_image_mir
  ϴ hseg, mem_ofPred_eq, mir_fst, mir_snd
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, ⟡, ⟡⟩

/-- **Horizontal chords of the mirrored domain.** -/
theorem isHChordIn_mir {D : Set Point} {y a b : ℝ} :
    IsHChordIn (mir '' D) y (-b) (-a) ↔ IsHChordIn D y a b := by
  constructor
  · intro h
    refine ⟨by linarith [h.lt], fun hm => h.right_not ?_, fun hm => h.left_not ?_,
      fun x h1 h2 => ?_⟩
    · rw [mem_image_mir, mir_pt, neg_neg]; exact hm
    · rw [mem_image_mir, mir_pt, neg_neg]; exact hm
    · have := h.open_mem (-x) (⟡) (⟡)
      rwa [mem_image_mir, mir_pt, neg_neg] at this
  · intro h
    refine ⟨by linarith [h.lt], fun hm => h.right_not ?_, fun hm => h.left_not ?_,
      fun x h1 h2 => ?_⟩
    · rwa [mem_image_mir, mir_pt, neg_neg] at hm
    · rwa [mem_image_mir, mir_pt, neg_neg] at hm
    · rw [mem_image_mir, mir_pt]; exact h.open_mem (-x) (⟡) (⟡)

theorem closure_mir (U : Set Point) : closure (mir '' U) = mir '' closure U :=
  (mirHomeo.image_closure U).symm

/-! ## Mirrored families -/

/-- The mirror image of a family of sets. -/
def mirF (F : Set (Set Point)) : Set (Set Point) := (fun c => mir '' c) '' F

theorem mem_mirF {F : Set (Set Point)} {c : Set Point} : c ∈ mirF F ↔ mir '' c ∈ F := by
  constructor
  · rintro ⟨e, he, rfl⟩; rwa [image_mir_image_mir]
  · intro h; exact ⟨mir '' c, h, image_mir_image_mir c⟩

theorem image_mem_mirF {F : Set (Set Point)} {e : Set Point} : mir '' e ∈ mirF F ↔ e ∈ F := by
  Ξ mem_mirF, image_mir_image_mir

theorem mirF_mirF (F : Set (Set Point)) : mirF (mirF F) = F := by
  ext c; rw [mem_mirF, mem_mirF, image_mir_image_mir]

theorem mirF_injective : Function.Injective (fun c : Set Point => mir '' c) := fun a b hab => by
  have := congrArg (fun c : Set Point => mir '' c) hab
  simpa only [image_mir_image_mir] using this

theorem mirF_finite {F : Set (Set Point)} : (mirF F).Finite ↔ F.Finite :=
  ⟨fun h => by rw [← mirF_mirF F]; exact h.image _, fun h => h.image _⟩

@[simp] theorem mirF_empty : mirF ∅ = ∅ := image_empty _

theorem mirF_nonempty {F : Set (Set Point)} : (mirF F).Nonempty ↔ F.Nonempty := image_nonempty

theorem mirF_subset {F G : Set (Set Point)} : mirF F ⊆ mirF G ↔ F ⊆ G :=
  image_subset_image_iff mirF_injective

theorem mirF_union (F G : Set (Set Point)) : mirF (F ∪ G) = mirF F ∪ mirF G := image_union _ _ _

theorem sUnion_mirF (F : Set (Set Point)) : ⋃₀ mirF F = mir '' ⋃₀ F := by
  ext x
  Ξ mem_image_mir, mem_sUnion, mem_sUnion
  constructor
  · rintro ⟨c, hc, hx⟩
    exact ⟨mir '' c, mem_mirF.1 hc, mem_image_of_mem mir hx⟩
  · rintro ⟨e, he, hx⟩
    exact ⟨mir '' e, image_mem_mirF.2 he, mem_image_mir.2 hx⟩

theorem freeIn_mir (D : Set Point) (F : Set (Set Point)) :
    freeIn (mir '' D) (mirF F) = mir '' freeIn D F := by
  unfold freeIn; rw [sUnion_mirF, image_sdiff mir_injective]

/-- **The regions of the mirrored family are the mirrored regions.** -/
theorem regionsIn_mir (D : Set Point) (F : Set (Set Point)) :
    regionsIn (mir '' D) (mirF F) = mirF (regionsIn D F) := by
  ext U
  Ξ mem_mirF
  unfold regionsIn
  Ξ freeIn_mir
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨mir z, mem_image_mir.1 hz, ?_⟩
    Ξ image_connectedComponentIn_mir, image_mir_image_mir
  · rintro ⟨z, hz, hU⟩
    refine ⟨mir z, mem_image_mir.2 (by rwa [mir_mir]), ?_⟩
    Ξ ← image_mir_image_mir U, hU, image_connectedComponentIn_mir

theorem touchesIn_mir {D c U : Set Point} :
    TouchesIn (mir '' D) (mir '' c) (mir '' U) ↔ TouchesIn D c U := by
  unfold TouchesIn
  Ξ ← image_inter mir_injective, closure_mir
  constructor
  · rintro ⟨z, hz, hzU⟩
    exact ⟨mir z, mem_image_mir.1 hz, mem_image_mir.1 hzU⟩
  · rintro ⟨z, hz, hzU⟩
    exact ⟨mir z, mem_image_mir.2 (by rwa [mir_mir]), mem_image_mir.2 (by rwa [mir_mir])⟩

/-! ## Mirrored models -/

/-- **`M'` is the mirror image of the model `M`**, its walk traversed backwards (shift `c`). -/
structure ModelMir (M M' : Model) (c : ℕ) : Prop where
  D : M'.D = mir '' M.D
  walk : WalkMir M.W M'.W c
  counted : ∀ p, p < M.W.n → (M'.counted p ↔ M.counted ((c + 2 * M.W.n - 1 - p) % M.W.n))
  Adm : M'.Adm = mirF M.Adm
  Full : M'.Full = mirF M.Full

/-- Cut keys lie in `[0, n)`. -/
theorem isCut_bounds {M : Model} {F : Set (Set Point)} {x : ℝ} (hx : M.IsCut F x) :
    0 ≤ x ∧ x < M.W.n := by
  obtain ⟨e, -, p, t, hA, rfl⟩ := hx
  have hp : (p : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hA.1
  exact ⟨by linarith [hA.2.1, (Nat.cast_nonneg p : (0 : ℝ) ≤ p)], by linarith [hA.2.2.1]⟩

/-- For the empty family, the only arc is the pinned whole walk. -/
theorem isArc_empty {M : Model} {U : Set Point} {a b : ℝ} :
    M.IsArc ∅ U a b ↔ a = 0 ∧ b = 0 ∧ 0 < M.W.n ∧
      ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 < t → t < 1 → M.Faces p t U := by
  have hnc : ∀ x, ¬ M.IsCut ∅ x := fun x ⟨_, he, _⟩ => he
  constructor
  · rintro ⟨-, han, -, -, hc, -, hf⟩
    obtain ⟨ha, hb⟩ : a = 0 ∧ b = 0 := by
      rcases hc with ⟨h, -⟩ | ⟨-, ha, hb⟩
      · exact absurd h (hnc a)
      · exact ⟨ha, hb⟩
    subst ha hb
    refine ⟨rfl, rfl, by exact_mod_cast han, fun p t hp ht0 ht1 => hf p t hp ht0 ht1 ?_⟩
    unfold sideInArc; rw [ite_eq_right (lt_irrefl _)]
    left; positivity
  · rintro ⟨rfl, rfl, hn, hf⟩
    have hn' : (0 : ℝ) < M.W.n := by exact_mod_cast hn
    exact ⟨le_rfl, hn', le_rfl, hn', Or.inr ⟨rfl, rfl, rfl⟩, fun x _ => hnc x,
      fun p t hp ht0 ht1 _ => hf p t hp ht0 ht1⟩

/-- The arc weight of a degenerate interval `(a, a)`: every counted edge. -/
theorem arcWt_self (M : Model) (a : ℝ) :
    M.arcWt a a = {p : ℕ | p < M.W.n ∧ M.counted p}.ncard := by
  unfold Model.arcWt
  congr 1
  ext p
  ϴ mem_ofPred_eq
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    unfold sideInArc
    ϴ lt_irrefl, ite_false
    by_cases h : (p : ℝ) + 1 / 2 = a
    · exact ⟨1 / 4, ⊛, ⊛, Or.inr (⟡)⟩
    · rcases lt_or_gt_of_ne h with h | h
      · exact ⟨1 / 2, ⊛, ⊛, Or.inr h⟩
      · exact ⟨1 / 2, ⊛, ⊛, Or.inl h⟩

namespace ModelMir

variable {M M' : Model} {c : ℕ} (h : ModelMir M M' c)
include h

theorem n_eq : M'.W.n = M.W.n := h.walk.n_eq

/-- **Regions correspond.** -/
theorem regions (F : Set (Set Point)) : M'.regions (mirF F) = mirF (M.regions F) := by
  unfold Model.regions; rw [h.D, regionsIn_mir]

/-- **Degrees correspond.** -/
theorem deg (F : Set (Set Point)) (U : Set Point) : M'.deg (mirF F) (mir '' U) = M.deg F U := by
  unfold Model.deg
  have e : {e' | e' ∈ mirF F ∧ TouchesIn M'.D e' (mir '' U)} =
      (fun e => mir '' e) '' {e | e ∈ F ∧ TouchesIn M.D e U} := by
    ext e'
    constructor
    · rintro ⟨he, ht⟩
      refine ⟨mir '' e', ⟨mem_mirF.1 he, ?_⟩, image_mir_image_mir e'⟩
      rw [h.D] at ht
      rw [← touchesIn_mir, image_mir_image_mir]; exact ht
    · rintro ⟨e, ⟨he, ht⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, by rw [h.D]; exact touchesIn_mir.2 ht⟩
  Ξ e, Set.ncard_image_of_injective _ mirF_injective

theorem deg' (F : Set (Set Point)) (U' : Set Point) :
    M'.deg (mirF F) U' = M.deg F (mir '' U') := by
  Ξ ← h.deg, image_mir_image_mir

/-- **Cut keys correspond** (reflected keys). -/
theorem isCut (F : Set (Set Point)) {x' : ℝ} (hx0 : 0 ≤ x') (hxn : x' < M.W.n) :
    M'.IsCut (mirF F) x' ↔ M.IsCut F (rk M.W.n c x') := by
  constructor
  · rintro ⟨e', he', p', t', hA, rfl⟩
    have hp : p' < M.W.n := h.n_eq ▸ hA.1
    have hA' : SideAttach M'.W (mir '' (mir '' e')) p' t' := by rwa [image_mir_image_mir]
    rw [h.walk.sideAttach_mir hp hA.2.1 hA.2.2.1] at hA'
    exact ⟨_, mem_mirF.1 he', _, _, hA', (posMir_key h.walk.c_lt hp hA.2.1 hA.2.2.1).symm⟩
  · rintro ⟨e, he, p, t, hA, hx⟩
    have hp : p < M'.W.n := h.n_eq.symm ▸ hA.1
    have hA' : SideAttach M.W (mir '' (mir '' e)) p t := by rwa [image_mir_image_mir]
    rw [h.walk.symm.sideAttach_mir hp hA.2.1 hA.2.2.1] at hA'
    refine ⟨_, ⟨e, he, rfl⟩, _, _, hA', ?_⟩
    rw [posMir_key h.walk.symm.c_lt hp hA.2.1 hA.2.2.1, h.n_eq, ← hx,
      rk_rk h.walk.c_lt hx0 hxn]

/-- **Facing reverses the walk edge.** -/
theorem faces {p' : ℕ} (hp : p' < M.W.n) (t' : ℝ) (U : Set Point) :
    M'.Faces p' t' (mir '' U) ↔ M.Faces ((c + 2 * M.W.n - 1 - p') % M.W.n) (1 - t') U := by
  unfold Model.Faces Model.wa Model.wb
  rw [h.n_eq, h.walk.vtx p' hp, h.walk.vtx _ (Nat.mod_lt _ h.walk.n_pos),
    idx_next h.walk.n_pos hp, idx_succ h.walk.n_pos hp]
  ϴ mem_image_mir, mir_offset, mir_mir, offset_rev

/-- Facing at all interior edge positions. -/
theorem faces_all (U : Set Point) :
    (∀ p' : ℕ, ∀ t' : ℝ, p' < M'.W.n → 0 < t' → t' < 1 → M'.Faces p' t' (mir '' U)) ↔
      ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 < t → t < 1 → M.Faces p t U := by
  have hn := h.walk.n_pos
  have hc := h.walk.c_lt
  Ξ h.n_eq
  constructor
  · intro H p t hp ht0 ht1
    have := H _ (1 - t) (Nat.mod_lt (c + 2 * M.W.n - 1 - p) hn) (⟡) (⟡)
    rwa [h.faces (Nat.mod_lt _ hn), idx_q_invol hc hp, sub_sub_cancel] at this
  · intro H p' t' hp ht0 ht1
    Ξ h.faces hp
    exact H _ _ (Nat.mod_lt _ hn) (⟡) (⟡)

theorem rk_lt {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < M.W.n) :
    0 ≤ rk M.W.n c x ∧ rk M.W.n c x < M.W.n := rk_bounds h.walk.c_lt hx0 hxn

/-- **Arcs correspond** (nonempty families): the arc `(a', b')` is the reflected arc
`(rk b', rk a')`. -/
theorem isArc {F : Set (Set Point)} (hF : F.Nonempty) (U : Set Point) {a' b' : ℝ} (ha0 : 0 ≤ a')
    (han : a' < M.W.n) (hb0 : 0 ≤ b') (hbn : b' < M.W.n) :
    M'.IsArc (mirF F) (mir '' U) a' b' ↔
      M.IsArc F U (rk M.W.n c b') (rk M.W.n c a') := by
  have hn := h.walk.n_pos
  have hc := h.walk.c_lt
  set n := M.W.n with hn_def
  obtain ⟨ra0, ran⟩ := h.rk_lt ha0 han
  obtain ⟨rb0, rbn⟩ := h.rk_lt hb0 hbn
  have hF' : mirF F ≠ ∅ := (mirF_nonempty.2 hF).ne_empty
  have hF0 : F ≠ ∅ := hF.ne_empty
  have hcut : ((M'.IsCut (mirF F) a' ∧ M'.IsCut (mirF F) b' ∧ a' ≠ b') ∨
      (mirF F = ∅ ∧ a' = 0 ∧ b' = 0)) ↔
      ((M.IsCut F (rk n c b') ∧ M.IsCut F (rk n c a') ∧ rk n c b' ≠ rk n c a') ∨
        (F = ∅ ∧ rk n c b' = 0 ∧ rk n c a' = 0)) := by
    Ξ h.isCut F ha0 han, h.isCut F hb0 hbn
    have hne : a' ≠ b' ↔ rk n c b' ≠ rk n c a' := by
      constructor
      · intro hab e
        apply hab
        Ξ ← rk_rk hc ha0 han, ← rk_rk hc hb0 hbn, e
      · rintro hab rfl; exact hab rfl
    Ξ hne
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, -⟩)
      · exact Or.inl ⟨h2, h1, h3⟩
      · exact absurd h1 hF'
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, -⟩)
      · exact Or.inl ⟨h2, h1, h3⟩
      · exact absurd h1 hF0
  have hnocut : (∀ x, sideInArc a' b' x → ¬ M'.IsCut (mirF F) x) ↔
      (∀ x, sideInArc (rk n c b') (rk n c a') x → ¬ M.IsCut F x) := by
    constructor
    · intro H x hx hcx
      obtain ⟨hx0, hxn⟩ := isCut_bounds hcx
      obtain ⟨r0, rn⟩ := h.rk_lt hx0 hxn
      apply H (rk n c x)
      · rw [sideInArc_rk hc ha0 han hb0 hbn r0 rn, rk_rk hc hx0 hxn]; exact hx
      · rw [h.isCut F r0 rn, rk_rk hc hx0 hxn]; exact hcx
    · intro H x' hx' hcx'
      obtain ⟨hx0, hxn⟩ := isCut_bounds hcx'
      rw [h.n_eq] at hxn
      exact H _ ((sideInArc_rk hc ha0 han hb0 hbn hx0 hxn).1 hx') ((h.isCut F hx0 hxn).1 hcx')
  have hfaces : (∀ p' : ℕ, ∀ t' : ℝ, p' < M'.W.n → 0 < t' → t' < 1 → sideInArc a' b' (p' + t') →
      M'.Faces p' t' (mir '' U)) ↔
      (∀ p : ℕ, ∀ t : ℝ, p < n → 0 < t → t < 1 → sideInArc (rk n c b') (rk n c a') (p + t) →
        M.Faces p t U) := by
    Ξ h.n_eq
    constructor
    · intro H p t hp ht0 ht1 hin
      have hq := Nat.mod_lt (c + 2 * n - 1 - p) hn
      have hq' : ((c + 2 * n - 1 - p) % n : ℕ) < (n : ℝ) := by exact_mod_cast hq
      have hql : (((c + 2 * n - 1 - p) % n : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hq
      have := H _ (1 - t) hq (⟡) (⟡) ?_
      · rwa [h.faces hq, idx_q_invol hc hp, sub_sub_cancel] at this
      · rw [sideInArc_rk hc ha0 han hb0 hbn (⟢) (⟡),
          rk_edge hc hq (⟡) (⟡), idx_q_invol hc hp, sub_sub_cancel]
        exact hin
    · intro H p' t' hp ht0 ht1 hin
      have hpl : (p' : ℝ) + 1 ≤ n := by exact_mod_cast hp
      Ξ h.faces hp
      apply H _ _ (Nat.mod_lt _ hn) (⟡) (⟡)
      Ξ ← rk_edge hc hp ht0 ht1
      exact (sideInArc_rk hc ha0 han hb0 hbn (⟢) (⟡)).1 hin
  unfold Model.IsArc
  constructor
  · rintro ⟨-, -, -, -, h1, h2, h3⟩
    exact ⟨rb0, rbn, ra0, ran, hcut.1 h1, hnocut.1 h2, hfaces.1 h3⟩
  · rintro ⟨-, -, -, -, h1, h2, h3⟩
    exact ⟨ha0, by rw [h.n_eq]; exact han, hb0, by rw [h.n_eq]; exact hbn, hcut.2 h1, hnocut.2 h2,
      hfaces.2 h3⟩

/-- **Arc weights correspond.** -/
theorem arcWt {a' b' : ℝ} (ha0 : 0 ≤ a') (han : a' < M.W.n) (hb0 : 0 ≤ b') (hbn : b' < M.W.n) :
    M'.arcWt a' b' = M.arcWt (rk M.W.n c b') (rk M.W.n c a') := by
  have hn := h.walk.n_pos
  have hc := h.walk.c_lt
  set n := M.W.n with hn_def
  unfold Model.arcWt
  Ξ h.n_eq
  refine Set.ncard_congr (fun p' _ => (c + 2 * n - 1 - p') % n) ?_ ?_ ?_
  · rintro p' ⟨hp, hcnt, t', ht0, ht1, hin⟩
    have hpl : (p' : ℝ) + 1 ≤ n := by exact_mod_cast hp
    refine ⟨Nat.mod_lt _ hn, (h.counted p' hp).1 hcnt, 1 - t', ⟡, ⟡, ?_⟩
    Ξ ← rk_edge hc hp ht0 ht1
    exact (sideInArc_rk hc ha0 han hb0 hbn (⟢) (⟡)).1 hin
  · rintro p₁ p₂ ⟨hp₁, -⟩ ⟨hp₂, -⟩ e
    Ξ ← idx_q_invol hc hp₁, ← idx_q_invol hc hp₂
    exact congrArg (fun q => (c + 2 * n - 1 - q) % n) e
  · rintro p ⟨hp, hcnt, t, ht0, ht1, hin⟩
    have hq := Nat.mod_lt (c + 2 * n - 1 - p) hn
    have hql : (((c + 2 * n - 1 - p) % n : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hq
    refine ⟨(c + 2 * n - 1 - p) % n, ⟨hq, ?_, 1 - t, ⟡, ⟡, ?_⟩,
      idx_q_invol hc hp⟩
    · rw [h.counted _ hq, idx_q_invol hc hp]; exact hcnt
    · rw [sideInArc_rk hc ha0 han hb0 hbn (⟢) (⟡),
        rk_edge hc hq (⟡) (⟡), idx_q_invol hc hp, sub_sub_cancel]
      exact hin

/-- **Weights correspond.** -/
theorem weight (F : Set (Set Point)) (U : Set Point) :
    M'.weight (mirF F) (mir '' U) = M.weight F U := by
  have hn := h.walk.n_pos
  have hc := h.walk.c_lt
  unfold Model.weight
  congr 1
  rcases F.eq_empty_or_nonempty with rfl | hF
  · Ξ mirF_empty
    have e0 : M'.arcWt 0 0 = M.arcWt 0 0 := by
      have hn' : (0 : ℝ) < M.W.n := by exact_mod_cast hn
      Ξ h.arcWt le_rfl hn' le_rfl hn', arcWt_self, arcWt_self
    ext w
    ϴ mem_image, mem_ofPred_eq, Prod.exists
    constructor
    · rintro ⟨a, b, hab, rfl⟩
      obtain ⟨rfl, rfl, hn', hf⟩ := isArc_empty.1 hab
      exact ⟨0, 0, isArc_empty.2 ⟨rfl, rfl, hn, (h.faces_all U).1 hf⟩, e0.symm⟩
    · rintro ⟨a, b, hab, rfl⟩
      obtain ⟨rfl, rfl, -, hf⟩ := isArc_empty.1 hab
      exact ⟨0, 0, isArc_empty.2 ⟨rfl, rfl, h.n_eq ▸ hn, (h.faces_all U).2 hf⟩, e0⟩
  · ext w
    ϴ mem_image, mem_ofPred_eq, Prod.exists
    constructor
    · rintro ⟨a', b', hab, rfl⟩
      have ha := hab.2.1; have hb := hab.2.2.2.1
      rw [h.n_eq] at ha hb
      refine ⟨_, _, (h.isArc hF U hab.1 ha hab.2.2.1 hb).1 hab, ?_⟩
      exact (h.arcWt hab.1 ha hab.2.2.1 hb).symm
    · rintro ⟨a, b, hab, rfl⟩
      obtain ⟨ra0, ran⟩ := h.rk_lt hab.1 hab.2.1
      obtain ⟨rb0, rbn⟩ := h.rk_lt hab.2.2.1 hab.2.2.2.1
      refine ⟨rk M.W.n c b, rk M.W.n c a, ?_, ?_⟩
      · rw [h.isArc hF U rb0 rbn ra0 ran, rk_rk hc hab.1 hab.2.1,
          rk_rk hc hab.2.2.1 hab.2.2.2.1]
        exact hab
      · Ξ h.arcWt rb0 rbn ra0 ran, rk_rk hc hab.1 hab.2.1, rk_rk hc hab.2.2.1 hab.2.2.2.1

/-- **Chord families correspond** (for the mirrored height polygon). -/
theorem chordFamily (Q : Polygon) (F : Set (Set Point)) :
    M'.ChordFamily Q.mir (mirF F) ↔ M.ChordFamily Q F := by
  unfold Model.ChordFamily
  Ξ mirF_finite, h.Adm, mirF_subset, mir_n
  have hy : ∀ k, (Q.mir.vtx k).2 = (Q.vtx k).2 := fun k => Ρ mir_vtx, mir_snd
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun e he => ?_⟩
    obtain ⟨k, hk, a, b, hab⟩ := h3 _ (image_mem_mirF.2 he)
    refine ⟨k, hk, -b, -a, ?_⟩
    Ξ ← image_mir_image_mir e, hab, hseg_mir, hy
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun e' he' => ?_⟩
    obtain ⟨k, hk, a, b, hab⟩ := h3 _ (mem_mirF.1 he')
    refine ⟨k, hk, -b, -a, ?_⟩
    Ξ ← image_mir_image_mir e', hab, hseg_mir, hy

end ModelMir

end

end Mir

end Chazelle.Core
