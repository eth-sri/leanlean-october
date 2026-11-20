module

public import PottsDiscontinuity.TorusCrossing.BaseConn
public import PottsDiscontinuity.TorusCrossing.BdEven
public import PottsDiscontinuity.TorusCrossing.Cochain
public import PottsDiscontinuity.TorusCrossing.Explore

/-!
# The boundary of the exploration is connected

The boundary edges of the explored region separate the class `U` (joined to the row `p₂`) from
the class `X` (the rest).  Suppose they split into two vertex-disjoint parts.  The indicator of one
part is a closed cochain, hence has a primitive `g`; `g` is constant on `U` and on `X` (it is
constant on the two port rows and does not change across non-boundary edges), so it changes by the
same amount across every boundary edge, contradicting that it changes across one part only.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

namespace Rect

variable (R : Rect)

theorem mem_expBd_iff {p₁ p₂ : ℤ} {A : Finset Cell} {m : Cell} :
    m ∈ R.expBd p₁ p₂ A ↔
      m ∈ R.inner ∧ IsSep (fun z => z ∈ R.expU p₁ p₂ A) m := by
  unfold expBd IsSep
  grind

theorem faceRow_nonempty (hw : 0 < R.w) (r : ℤ) (h1 : R.y0 ≤ r) (h2 : r ≤ R.y0 + R.h) :
    ∃ z ∈ R.faceRow r, True := by
  refine ⟨(if IsPrimal (R.x0, r) then R.x0 + 1 else R.x0, r), ?_, trivial⟩
  simp only [faceRow, Finset.mem_filter, mem_dcells, mem_cells, IsPrimal, and_true]
  split_ifs <;> omega

theorem cdeg_ind_eq (S : Finset Cell) (c : Cell) :
    cdeg (ind S) c = (((corners c).filter (fun m => m ∈ S)).card : ZMod 2) := by
  rw [card_filter_corners]
  unfold cdeg ind
  push_cast
  simp

theorem mem_expD_of_faceRow {p₁ : ℤ} {A : Finset Cell} {z : Cell} (hz : z ∈ R.faceRow p₁) :
    z ∈ R.expD p₁ A := by
  unfold expD
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, z, hz, Relation.ReflTransGen.refl⟩

section

variable {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell}

theorem not_mem_expU_of_faceRow
    (hz : z ∈ R.faceRow p₁) : z ∉ R.expU p₁ p₂ A := fun h =>
  expU_subset_not_expD h (R.mem_expD_of_faceRow hz)

theorem mem_expU_of_faceRow
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) (hz : z ∈ R.faceRow p₂) :
    z ∈ R.expU p₁ p₂ A := by
  unfold expU
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, hb z hz, z, hz, hb z hz,
    Relation.ReflTransGen.refl⟩

end

theorem faceRow_mem {r : ℤ} {z : Cell} : z ∈ R.faceRow r ↔ z ∈ R.dcells ∧ z.2 = r := by
  unfold faceRow; exact Finset.mem_filter

/-- The faces of one boundary row all have the same label. -/
theorem label_row {p₁ p₂ : ℤ} {A : Finset Cell} (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨
      (p₁ = R.y0 + R.h ∧ p₂ = R.y0)) (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    {z z' : Cell} (hz : z ∈ R.dcells) (hz' : z' ∈ R.dcells) (r : ℤ)
    (hr : r = R.y0 ∨ r = R.y0 + R.h) (hzr : z.2 = r) (hz'r : z'.2 = r) :
    (z ∈ R.expU p₁ p₂ A ↔ z' ∈ R.expU p₁ p₂ A) := by
  have h1 := R.faceRow_mem.2 ⟨hz, hzr⟩
  have h2 := R.faceRow_mem.2 ⟨hz', hz'r⟩
  rcases (show r = p₁ ∨ r = p₂ by omega) with rfl | rfl
  · exact iff_of_false (R.not_mem_expU_of_faceRow h1) (R.not_mem_expU_of_faceRow h2)
  · exact iff_of_true (R.mem_expU_of_faceRow hb h1) (R.mem_expU_of_faceRow hb h2)

/-- Even number of boundary edges at primal cells strictly between the side columns. -/
theorem expBd_cdeg_zero (hh : 0 < R.h) {p₁ p₂ : ℤ} {A : Finset Cell}
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) {c : Cell} (hc : c ∈ R.pcells)
    (hx1 : R.x0 < c.1) (hx2 : c.1 < R.x0 + R.w) :
    cdeg (ind (R.expBd p₁ p₂ A)) c = 0 := by
  have hcc := mem_cells.1 (mem_pcells.1 hc).1
  have hcp := (mem_pcells.1 hc).2
  simp only [cdeg_ind_eq, R.mem_expBd_iff]
  have hd (d : ℤ) (hd : d = -1 ∨ d = 1) : ((c.1 + d, c.2) : Cell) ∈ R.dcells := by
    simp only [mem_dcells, mem_cells, IsPrimal] at *
    omega
  have hlabel (r : ℤ) (hr : r = R.y0 ∨ r = R.y0 + R.h) (hy : c.2 = r) :
      ((c.1 - 1, c.2) : Cell) ∈ R.expU p₁ p₂ A ↔ ((c.1 + 1, c.2) : Cell) ∈ R.expU p₁ p₂ A := by
    exact R.label_row hp hb (by simpa [sub_eq_add_neg] using hd (-1) (Or.inl rfl))
      (hd 1 (Or.inr rfl)) r hr hy hy
  have hev := sep_deg_even R hh (fun z => z ∈ R.expU p₁ p₂ A) c hcp hx1 hx2 hcc.2.2.1 hcc.2.2.2
    (hlabel _ (Or.inl rfl)) (hlabel _ (Or.inr rfl))
  obtain ⟨k, hk⟩ := hev
  rw [hk]
  push_cast
  exact zmod2_two _

section Potential

variable {R}
variable (f g : Cell → ZMod 2)

/-- A primitive on the whole strip is constant along the ports: consecutive
port cells are joined by two edges lying just outside the board. -/
private theorem g_two (hfin : ∀ m, f m ≠ 0 → m ∈ R.inner)
    (hg : ∀ m : Cell, R.x0 < m.1 → m.1 ≤ R.x0 + R.w → g (dualEnds m).1 + g (dualEnds m).2 = f m)
    {i r : ℤ} (hr : r = R.y0 ∨ r = R.y0 + R.h) (hz : ((i, r) : Cell) ∈ R.dcells)
    (hz' : ((i + 2, r) : Cell) ∈ R.dcells) : g (i, r) = g (i + 2, r) := by
  have hzc := mem_cells.1 (mem_dcells.1 hz).1
  have hzc' := mem_cells.1 (mem_dcells.1 hz').1
  have hzp := (mem_dcells.1 hz).2
  unfold IsPrimal at hzp
  dsimp only at hzc hzc' hzp
  have h0 (z : Cell) (hz : z.2 ≤ R.y0 ∨ R.y0 + R.h < z.2) : f z = 0 := by
    by_contra hn
    have := mem_inner.1 (hfin _ hn)
    omega
  rcases hr with hr | hr
  · have h₁ := hg (i + 1, r) (by dsimp; omega) (by dsimp; omega)
    have h₂ := hg (i + 2, r) (by dsimp; omega) (by dsimp; omega)
    have e₁ : (i + 1 + r) % 2 = 0 := by omega
    have e₂ : (i + 2 + r) % 2 ≠ 0 := by omega
    simp only [dualEnds, e₁, e₂, ite_true, ite_false, add_sub_cancel_right, show i + 2 - 1 = i + 1 by omega,
      h0 (i + 1, r) (Or.inl hr.le), h0 (i + 2, r) (Or.inl hr.le)] at h₁ h₂
    exact add_right_cancel (h₁.trans h₂.symm)
  · have h₁ := hg (i + 1, r + 1) (by dsimp; omega) (by dsimp; omega)
    have h₂ := hg (i + 2, r + 1) (by dsimp; omega) (by dsimp; omega)
    have e₁ : (i + 1 + (r + 1)) % 2 ≠ 0 := by omega
    have e₂ : (i + 2 + (r + 1)) % 2 = 0 := by omega
    have hh : R.y0 + R.h < r + 1 := by omega
    simp only [dualEnds, e₁, e₂, ite_true, ite_false, add_sub_cancel_right, show i + 2 - 1 = i + 1 by omega,
      h0 (i + 1, r + 1) (Or.inr hh), h0 (i + 2, r + 1) (Or.inr hh)] at h₁ h₂
    exact add_left_cancel (h₁.trans h₂.symm)

private theorem g_row (hfin : ∀ m, f m ≠ 0 → m ∈ R.inner)
    (hg : ∀ m : Cell, R.x0 < m.1 → m.1 ≤ R.x0 + R.w → g (dualEnds m).1 + g (dualEnds m).2 = f m)
    {r : ℤ} (hr : r = R.y0 ∨ r = R.y0 + R.h) {z z' : Cell}
    (hz : z ∈ R.faceRow r) (hz' : z' ∈ R.faceRow r) : g z = g z' := by
  exact R.rel_of_same_dual_row (rel := fun a b => g a = g b) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    (fun ⟨i, y⟩ hy hy' hy'' => by
      change y = r at hy'
      subst y
      exact g_two f g hfin hg hr hy hy'')
    (R.faceRow_mem.1 hz).1 (R.faceRow_mem.1 hz').1 (R.faceRow_mem.1 hz).2 (R.faceRow_mem.1 hz').2

end Potential

/-- **The exploration boundary is connected.** -/
theorem bd_connected (hh : 0 < R.h) (hw' : 0 < R.w) {p₁ p₂ : ℤ} {A : Finset Cell}
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    {m m' : Cell} (hm : m ∈ R.expBd p₁ p₂ A) (hm' : m' ∈ R.expBd p₁ p₂ A) :
    Relation.ReflTransGen (StepRel primalEnds (R.expBd p₁ p₂ A))
      (primalEnds m).1 (primalEnds m').1 := by
  let bd := R.expBd p₁ p₂ A
  let K := Relation.ReflTransGen (StepRel primalEnds bd) (primalEnds m).1
  by_contra hcon
  have hbdinner : ∀ e ∈ bd, e ∈ R.inner := fun e he => (R.mem_expBd_iff.1 he).1
  have hKedge : ∀ e ∈ bd, K (primalEnds e).1 ↔ K (primalEnds e).2 := by
    intro e he
    exact ⟨fun h => h.tail ⟨e, he, Or.inl rfl⟩, fun h => h.tail ⟨e, he, Or.inr rfl⟩⟩
  set bd₁ := bd.filter (fun e => K (primalEnds e).1) with hbd₁
  have hmbd₁ : m ∈ bd₁ := Finset.mem_filter.2 ⟨hm, Relation.ReflTransGen.refl⟩
  have hm'bd₁ : m' ∉ bd₁ := fun h => hcon (Finset.mem_filter.1 h).2
  set f : Cell → ZMod 2 := ind bd₁ with hf
  have hfm : f m = 1 := ind_apply_of_mem hmbd₁
  have hfm' : f m' = 0 := ind_apply_of_not_mem hm'bd₁
  have hfin (e : Cell) (he : f e ≠ 0) : e ∈ R.inner :=
    hbdinner e (Finset.mem_filter.1 (mem_of_ind_ne_zero he)).1
  have hx0 : ∀ e : Cell, e.1 ≤ R.x0 → f e = 0 := fun e h => by_contra fun hn =>
    (not_lt_of_ge h) (mem_inner.1 (hfin e hn)).1
  have hy0 : ∀ e : Cell, e.2 ≤ R.y0 → f e = 0 := fun e h => by_contra fun hn =>
    (not_lt_of_ge h) (mem_inner.1 (hfin e hn)).2.2.1
  -- closedness at primal cells strictly between the side columns
  have hclosed : ∀ c : Cell, IsPrimal c → R.x0 < c.1 → c.1 < R.x0 + R.w → cdeg f c = 0 := by
    intro c hcp hx1 hx2
    rw [hf, cdeg_ind_eq]
    have heq : (corners c).filter (· ∈ bd₁) = (corners c).filter (fun e => e ∈ bd ∧ K c ∧ c ∈ R.pcells) := by
      apply Finset.filter_congr
      intro e he
      rw [hbd₁, Finset.mem_filter]
      refine and_congr_right fun hE => ?_
      rcases (mem_primalEnds_iff c e hcp).2 he with h | h
      · simp [h, (R.pData.mem e (hbdinner e hE)).1]
      · simp [h, (R.pData.mem e (hbdinner e hE)).2, hKedge e hE]
    rw [heq]
    by_cases h : K c ∧ c ∈ R.pcells
    · simpa [h.1, h.2, cdeg_ind_eq] using R.expBd_cdeg_zero hh hp hb h.2 hx1 hx2
    · simp [h]
  let g := leftPotential R.x0 R.y0 f
  have hg := leftPotential_primitive R.x0 R.y0 R.w f hx0 hy0 hclosed
  have hg' (e : Cell) (he : e ∈ R.inner) : g (dualEnds e).1 + g (dualEnds e).2 = f e :=
    hg e (mem_inner.1 he).1 (mem_inner.1 he).2.1
  -- constants on the two port rows
  have hp1 : p₁ = R.y0 ∨ p₁ = R.y0 + R.h := by omega
  have hp2 : p₂ = R.y0 ∨ p₂ = R.y0 + R.h := by omega
  obtain ⟨q₁, hq₁, -⟩ := R.faceRow_nonempty hw' p₁ (by omega) (by omega)
  obtain ⟨q₂, hq₂, -⟩ := R.faceRow_nonempty hw' p₂ (by omega) (by omega)
  have hrow := fun {r} hr {z z'} hz hz' => g_row f g hfin hg (r := r) hr (z := z) (z' := z') hz hz'
  let U := R.expU p₁ p₂ A
  let D := R.expD p₁ A
  have heq {x y : Cell} (h : StepRel dualEnds R.inner x y) (hU : x ∈ U ↔ y ∈ U) : g x = g y := by
    obtain ⟨e, he, hec⟩ := h
    have hiff : (dualEnds e).1 ∈ U ↔ (dualEnds e).2 ∈ U := by
      rcases hec with h | h
      · rwa [h]
      · simpa [h] using hU.symm
    have hn : e ∉ bd := fun hh => (Finset.mem_filter.mp hh).2 (propext hiff)
    have hf0 : f e = 0 := ind_apply_of_not_mem (fun h => hn (Finset.mem_filter.1 h).1)
    exact potential_eq_of_ends ((hg' e he).trans hf0) hec
  have hU : ∀ z ∈ U, g z = g q₂ := by
    intro z hz
    obtain ⟨hzc, hzD, t, ht, htD, hr⟩ := R.mem_expU.1 hz
    clear hz hzc hzD
    have hc : z ∈ U ∧ g z = g t := by
      have htU := R.mem_expU.2 ⟨(R.faceRow_mem.mp ht).1, htD, t, ht, htD, .refl⟩
      induction hr with
      | refl => exact ⟨htU, rfl⟩
      | @tail x y _ hs ih =>
        obtain ⟨hxU, he⟩ := ih
        exact ⟨R.expU_step hxU hs, (heq hs.2.2 (iff_of_true hxU (R.expU_step hxU hs))).symm.trans he⟩
    exact hc.2.trans (hrow hp2 ht hq₂)
  have hD (z : Cell) (hz : z ∈ D) : g z = g q₁ := by
    obtain ⟨hzc, p, hp', hr⟩ := R.mem_expD.1 hz
    clear hz hzc
    have hc : g z = g p := by
      induction hr with
      | refl => rfl
      | @tail x y hpre hs ih =>
        have hx : x ∈ D := R.mem_expD.2
          ⟨R.rtg_mem_dcells (R.faceRow_mem.mp hp').1 hpre, p, hp', hpre⟩
        have hy := R.expD_step hx hs
        exact (heq (stepRel_mono Finset.sdiff_subset hs) (iff_of_false
          (fun hxU => expU_subset_not_expD hxU hx) (fun hyU => expU_subset_not_expD hyU hy))).symm.trans ih
    exact hc.trans (hrow hp1 hp' hq₁)
  have hq₁c := (Finset.mem_filter.1 hq₁).1
  have hX : ∀ w, Relation.ReflTransGen (StepRel dualEnds R.inner) w q₁ → w ∉ U → g w = g q₁ := by
    intro w hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => intros; rfl
    | @head w y hstep hrest ih =>
      intro hwU
      by_cases hwD : w ∈ D
      · exact hD w hwD
      · have hyU : y ∉ U := fun hyU => hwU
          (R.expU_step hyU ⟨expU_subset_not_expD hyU, hwD, stepRel_symm hstep⟩)
        exact (heq hstep (iff_of_false hwU hyU)).trans (ih hyU)
  have hXall := fun w hw hwU =>
    hX w (R.dual_connected hw' hh hw hq₁c) hwU
  -- every boundary edge carries the same value
  have hbdval : ∀ e ∈ bd, f e = g q₁ + g q₂ := by
    intro e he
    have hei := hbdinner e he
    have hmem := R.dData.mem e hei
    have hsep := (R.mem_expBd_iff.1 he).2
    unfold IsSep at hsep
    rw [← hg' e hei]
    by_cases h1 : (dualEnds e).1 ∈ U
    · rw [hU _ h1, hXall _ hmem.2 (hsep.1 h1), add_comm]
    · rw [hU _ (not_not.mp (h1 ∘ hsep.2)), hXall _ hmem.1 h1]
  have he := (hbdval m hm).trans (hbdval m' hm').symm
  rw [hfm, hfm'] at he
  exact one_ne_zero he

end Rect

end PottsDiscontinuity.TorusCrossing
