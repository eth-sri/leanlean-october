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

public section

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
  by_cases hp : IsPrimal (R.x0, r)
  · refine ⟨(R.x0 + 1, r), ?_, trivial⟩
    unfold faceRow
    rw [Finset.mem_filter, mem_dcells, mem_cells]
    unfold IsPrimal at *
    omega
  · refine ⟨(R.x0, r), ?_, trivial⟩
    unfold faceRow
    rw [Finset.mem_filter, mem_dcells, mem_cells]
    simp_all

theorem cdeg_ind_eq (S : Finset Cell) (c : Cell) :
    cdeg (ind S) c = (((corners c).filter (fun m => m ∈ S)).card : ZMod 2) := by
  rw [card_filter_corners]
  aesop

theorem mem_expD_of_faceRow {p₁ : ℤ} {A : Finset Cell} {z : Cell} (hz : z ∈ R.faceRow p₁) :
    z ∈ R.expD p₁ A :=
  Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, z, hz, Relation.ReflTransGen.refl⟩

section
variable {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell}
theorem not_mem_expU_of_faceRow (hz : z ∈ R.faceRow p₁) : z ∉ R.expU p₁ p₂ A := fun h =>
  expU_subset_not_expD h (R.mem_expD_of_faceRow hz)

theorem mem_expU_of_faceRow (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) (hz : z ∈ R.faceRow p₂) :
    z ∈ R.expU p₁ p₂ A :=
  Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, hb z hz, z, hz, hb z hz,
    Relation.ReflTransGen.refl⟩
end

theorem faceRow_mem {r : ℤ} {z : Cell} : z ∈ R.faceRow r ↔ z ∈ R.dcells ∧ z.2 = r := by
  simp [faceRow]

/-- The faces of one boundary row all have the same label. -/
theorem label_row {p₁ p₂ : ℤ} {A : Finset Cell} (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨
      (p₁ = R.y0 + R.h ∧ p₂ = R.y0)) (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    {z z' : Cell} (hz : z ∈ R.dcells) (hz' : z' ∈ R.dcells) (r : ℤ)
    (hr : r = R.y0 ∨ r = R.y0 + R.h) (hzr : z.2 = r) (hz'r : z'.2 = r) :
    (z ∈ R.expU p₁ p₂ A ↔ z' ∈ R.expU p₁ p₂ A) := by
  have hrow : r = p₁ ∨ r = p₂ := by omega
  rcases hrow with h | h
  · subst h
    exact ⟨fun h => absurd h (R.not_mem_expU_of_faceRow (R.faceRow_mem.2 ⟨hz, hzr⟩)), fun h => absurd h (R.not_mem_expU_of_faceRow (R.faceRow_mem.2 ⟨hz', hz'r⟩))⟩
  · subst h
    exact ⟨fun _ => R.mem_expU_of_faceRow hb (R.faceRow_mem.2 ⟨hz', hz'r⟩), fun _ => R.mem_expU_of_faceRow hb (R.faceRow_mem.2 ⟨hz, hzr⟩)⟩

/-- Even number of boundary edges at primal cells strictly between the side columns. -/
theorem expBd_cdeg_zero (hh : 0 < R.h) {p₁ p₂ : ℤ} {A : Finset Cell}
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) {c : Cell} (hc : c ∈ R.pcells)
    (hx1 : R.x0 < c.1) (hx2 : c.1 < R.x0 + R.w) :
    cdeg (ind (R.expBd p₁ p₂ A)) c = 0 := by
  have hcc := mem_cells.1 (mem_pcells.1 hc).1
  have hcp := (mem_pcells.1 hc).2
  rw [cdeg_ind_eq]
  have hfilt : (corners c).filter (fun m => m ∈ R.expBd p₁ p₂ A) =
      (corners c).filter (fun m => m ∈ R.inner ∧ IsSep (fun z => z ∈ R.expU p₁ p₂ A) m) := by
    apply Finset.filter_congr
    intro m _
    exact R.mem_expBd_iff
  rw [hfilt]
  have hev := sep_deg_even R hh (fun z => z ∈ R.expU p₁ p₂ A) c hcp hx1 hx2 hcc.2.2.1 hcc.2.2.2
    (by
      intro hy
      have hW : ((c.1 - 1, c.2) : Cell) ∈ R.dcells := by
        rw [mem_dcells, mem_cells]; grind [IsPrimal]
      have hE : ((c.1 + 1, c.2) : Cell) ∈ R.dcells := by
        rw [mem_dcells, mem_cells]; grind [IsPrimal]
      exact R.label_row hp hb hW hE R.y0 (Or.inl rfl) hy hy)
    (by
      intro hy
      have hW : ((c.1 - 1, c.2) : Cell) ∈ R.dcells := by
        rw [mem_dcells, mem_cells]; grind [IsPrimal]
      have hE : ((c.1 + 1, c.2) : Cell) ∈ R.dcells := by
        rw [mem_dcells, mem_cells]; grind [IsPrimal]
      exact R.label_row hp hb hW hE (R.y0 + R.h) (Or.inr rfl) hy hy)
  obtain ⟨k, hk⟩ := hev
  rw [hk]
  grind

section Potential

variable {R}
variable (f g : Cell → ZMod 2)

section
variable (hh : 0 < R.h) (hfin : ∀ m, f m ≠ 0 → m ∈ R.inner) (hg : ∀ m ∈ R.inner, g (dualEnds m).1 + g (dualEnds m).2 = f m) (hclosed : ∀ c : Cell, IsPrimal c → R.x0 < c.1 → c.1 < R.x0 + R.w → cdeg f c = 0)
include hh hfin hg hclosed
/-- Consecutive faces of a boundary row have equal potential, for a closed cochain `f` supported
on inner medial vertices with primitive `g`. -/
theorem g_two {i r : ℤ} (hr : r = R.y0 ∨ r = R.y0 + R.h) (hz : ((i, r) : Cell) ∈ R.dcells)
    (hz' : ((i + 2, r) : Cell) ∈ R.dcells) : g (i, r) = g (i + 2, r) := by
  have hzc := mem_cells.1 (mem_dcells.1 hz).1
  have hzc' := mem_cells.1 (mem_dcells.1 hz').1
  have hzp := (mem_dcells.1 hz).2
  unfold IsPrimal at hzp
  have hcp : IsPrimal ((i + 1, r) : Cell) := by grind [IsPrimal]
  have hzero : ∀ m : Cell, m.2 ≤ R.y0 ∨ R.y0 + R.h < m.2 → f m = 0 := by
    intro m hm; by_contra hne
    have := hfin m hne; rw [mem_inner] at this; omega
  rcases hr with hr | hr
  · have hm3 : ((i + 1, r + 1) : Cell) ∈ R.inner := by
      rw [mem_inner]; omega
    have hm4 : ((i + 2, r + 1) : Cell) ∈ R.inner := by
      rw [mem_inner]; omega
    have d3 : dualEnds ((i + 1, r + 1) : Cell) = ((i + 1, r + 1), (i, r)) := by
      unfold dualEnds; rw [ite_eq_right (by omega)]; simp
    have d4 : dualEnds ((i + 2, r + 1) : Cell) = ((i + 1, r + 1), (i + 2, r)) := by
      unfold dualEnds; rw [ite_eq_left (by omega)]; ring
    grind [cdeg, decide]
  · have hm1 : ((i + 1, r) : Cell) ∈ R.inner := by
      rw [mem_inner]; omega
    have hm2 : ((i + 2, r) : Cell) ∈ R.inner := by
      rw [mem_inner]; omega
    have d1 : dualEnds ((i + 1, r) : Cell) = ((i, r), (i + 1, r - 1)) := by
      unfold dualEnds; rw [ite_eq_left (by omega)]; simp
    have d2 : dualEnds ((i + 2, r) : Cell) = ((i + 2, r), (i + 1, r - 1)) := by
      unfold dualEnds; rw [ite_eq_right (by omega)]; ring
    grind [cdeg, decide]

theorem g_row {r : ℤ} (hr : r = R.y0 ∨ r = R.y0 + R.h) :
    ∀ n : ℕ, ∀ z z' : Cell, z ∈ R.dcells → z' ∈ R.dcells → z.2 = r → z'.2 = r →
      (z'.1 - z.1).natAbs = 2 * n → g z = g z' := by
  intro n
  induction n with
  | zero =>
    grind
  | succ n ih =>
    intro z z' hz hz' hzr hz'r hn
    have hzc := mem_cells.1 (mem_dcells.1 hz).1
    have hzc' := mem_cells.1 (mem_dcells.1 hz').1
    have hzp := (mem_dcells.1 hz).2
    by_cases hlt : z.1 < z'.1
    · have hmid : ((z.1 + 2, z.2) : Cell) ∈ R.dcells := by
        rw [mem_dcells, mem_cells]; grind [IsPrimal]
      have h1 : g (z.1, r) = g (z.1 + 2, r) :=
        g_two f g hh hfin hg hclosed hr (by grind) (by grind)
      grind
    · have hmid : ((z'.1 + 2, z'.2) : Cell) ∈ R.dcells := by
        rw [mem_dcells, mem_cells]; grind [IsPrimal]
      have h1 : g (z'.1, r) = g (z'.1 + 2, r) :=
        g_two f g hh hfin hg hclosed hr (by grind) (by grind)
      grind
end

end Potential

theorem mem_expU {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell} :
    z ∈ R.expU p₁ p₂ A ↔ z ∈ R.dcells ∧ z ∉ R.expD p₁ A ∧ ∃ t ∈ R.faceRow p₂,
      t ∉ R.expD p₁ A ∧ Relation.ReflTransGen (R.AvoidStep (R.expD p₁ A)) t z := by
  simp [expU]

theorem avoid_mem_dcells {E : Finset Cell} {t z : Cell} (ht : t ∈ R.dcells)
    (hr : Relation.ReflTransGen (R.AvoidStep E) t z) : z ∈ R.dcells := by
  induction hr with
  | refl => omega
  | @tail b c _ hstep _ =>
    obtain ⟨_, _, e, he, hec⟩ := hstep
    have hmem := R.dData.mem e he
    grind

theorem stepRel_mem_dcells {y w : Cell} (h : StepRel dualEnds R.inner w y) : y ∈ R.dcells := by
  obtain ⟨e, he, hec⟩ := h
  have hmem := R.dData.mem e he
  grind

/-- **The exploration boundary is connected.** -/
theorem bd_connected (hh : 0 < R.h) (hw' : 0 < R.w) {p₁ p₂ : ℤ} {A : Finset Cell}
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    {m m' : Cell} (hm : m ∈ R.expBd p₁ p₂ A) (hm' : m' ∈ R.expBd p₁ p₂ A) :
    Relation.ReflTransGen (StepRel primalEnds (R.expBd p₁ p₂ A))
      (primalEnds m).1 (primalEnds m').1 := by
  set bd := R.expBd p₁ p₂ A with hbd
  set K : Cell → Prop :=
    fun x => Relation.ReflTransGen (StepRel primalEnds bd) (primalEnds m).1 x with hK
  by_contra hcon
  have hbdinner : ∀ e ∈ bd, e ∈ R.inner := fun e he => (R.mem_expBd_iff.1 he).1
  have hKedge : ∀ e ∈ bd, K (primalEnds e).1 ↔ K (primalEnds e).2 := fun e he =>
    ⟨fun h => h.tail ⟨e, he, Or.inl rfl⟩, fun h => h.tail ⟨e, he, Or.inr rfl⟩⟩
  set bd₁ := bd.filter (fun e => K (primalEnds e).1) with hbd₁
  have hmbd₁ : m ∈ bd₁ := by grind
  have hm'bd₁ : m' ∉ bd₁ := by simp_all
  set f : Cell → ZMod 2 := ind bd₁ with hf
  have hfm := ind_apply_of_mem hmbd₁
  have hfm' := ind_apply_of_not_mem hm'bd₁
  have hfin : ∀ e, f e ≠ 0 → e ∈ R.inner := fun e he => by_contra fun hne =>
    he (ind_apply_of_not_mem fun h => hne (hbdinner e (Finset.mem_filter.1 h).1))
  have hx0 : ∀ e : Cell, e.1 ≤ R.x0 → f e = 0 := by
    intro e he; by_contra hne
    have := mem_inner.1 (hfin e hne); omega
  have hy0 : ∀ e : Cell, e.2 ≤ R.y0 → f e = 0 := by
    intro e he; by_contra hne
    have := mem_inner.1 (hfin e hne); omega
  -- closedness at primal cells strictly between the side columns
  have hclosed : ∀ c : Cell, IsPrimal c → R.x0 < c.1 → c.1 < R.x0 + R.w → cdeg f c = 0 := by
    intro c hcp hx1 hx2
    rw [hf, cdeg_ind_eq]
    by_cases hcc : c ∈ R.pcells
    · by_cases hKc : K c
      · have : (corners c).filter (fun e => e ∈ bd₁) = (corners c).filter (fun e => e ∈ bd) := by
          apply Finset.filter_congr
          intro e he
          constructor
          · grind
          · rcases ((mem_primalEnds_iff c e hcp).2 he) with h1 | h1
            · grind
            grind
        rw [this]
        have h0 := R.expBd_cdeg_zero hh hp hb hcc hx1 hx2
        rw [cdeg_ind_eq] at h0
        omega
      · have : (corners c).filter (fun e => e ∈ bd₁) = ∅ := by
          apply Finset.filter_eq_empty_iff.2
          intro e he hmem
          rcases ((mem_primalEnds_iff c e hcp).2 he) with h1 | h1 <;> grind
        rw [this]; simp
    · have : (corners c).filter (fun e => e ∈ bd₁) = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        intro e he hmem
        have hei := hbdinner e (Finset.mem_filter.1 hmem).1
        rw [mem_inner] at hei
        apply hcc
        rw [mem_pcells, mem_cells]
        refine ⟨⟨?_, ?_, ?_, ?_⟩, hcp⟩
        all_goals
          unfold corners at he
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at he
          omega
      rw [this]; simp
  set g : Cell → ZMod 2 := leftPotential R.x0 R.y0 f with hgdef
  have hg : ∀ e ∈ R.inner, g (dualEnds e).1 + g (dualEnds e).2 = f e := by
    intro e he
    have := mem_inner.1 he
    exact leftPotential_primitive R.x0 R.y0 R.w f hx0 hy0 hclosed e (by omega) (by omega)
  -- constants on the two port rows
  have hp1 : p₁ = R.y0 ∨ p₁ = R.y0 + R.h := by omega
  have hp2 : p₂ = R.y0 ∨ p₂ = R.y0 + R.h := by omega
  obtain ⟨q₁, hq₁, -⟩ := R.faceRow_nonempty hw' p₁ (by omega) (by omega)
  obtain ⟨q₂, hq₂, -⟩ := R.faceRow_nonempty hw' p₂ (by omega) (by omega)
  have hrow : ∀ r, (r = R.y0 ∨ r = R.y0 + R.h) → ∀ z ∈ R.faceRow r, ∀ z' ∈ R.faceRow r, g z = g z' := by
    intro r hr z hz z' hz'
    have hz1 := R.faceRow_mem.1 hz
    have hz1' := R.faceRow_mem.1 hz'
    have hzp := (mem_dcells.1 hz1.1).2
    have hzp' := (mem_dcells.1 hz1'.1).2
    unfold IsPrimal at hzp hzp'
    exact g_row f g hh hfin hg hclosed hr ((z'.1 - z.1).natAbs / 2) z z' hz1.1 hz1'.1 hz1.2 hz1'.2
      (by omega)
  have hzeq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  -- g is constant along an edge not in the boundary
  have hnb : ∀ e ∈ R.inner, e ∉ bd → g (dualEnds e).1 = g (dualEnds e).2 := by
    intro e he hebd
    have hfe : f e = 0 := ind_apply_of_not_mem (fun h => hebd (Finset.mem_filter.1 h).1)
    grind
  have hchain : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A →
      ∀ z, Relation.ReflTransGen (R.AvoidStep (R.expD p₁ A)) t z →
        z ∉ R.expD p₁ A ∧ g z = g t := by
    intro t ht htD z hr
    induction hr with
    | refl => grind
    | @tail b c hbr hstep ih =>
      obtain ⟨ihD, ihg⟩ := ih
      have hbU :=
        R.mem_expU.2 ⟨R.avoid_mem_dcells (Finset.mem_filter.1 ht).1 hbr, ihD, t, ht, htD, hbr⟩
      have hcU :=
        R.mem_expU.2 ⟨R.avoid_mem_dcells (Finset.mem_filter.1 ht).1 (hbr.tail hstep), hstep.2.1,
          t, ht, htD, hbr.tail hstep⟩
      obtain ⟨_, hcD, e, he, hec⟩ := hstep
      have hesep : e ∉ bd := by
        intro hebd
        have hsep := (R.mem_expBd_iff.1 hebd).2
        unfold IsSep at hsep
        rcases hec with h | h <;> grind
      rcases hec with h | h <;> grind
  have hU : ∀ z ∈ R.expU p₁ p₂ A, g z = g q₂ := by
    intro z hz
    obtain ⟨hzc, hzD, t, ht, htD, hr⟩ := R.mem_expU.1 hz
    grind
  have hD1 : ∀ z ∈ R.expD p₁ A, g z = g q₁ := by
    intro z hz
    obtain ⟨hzc, p, hp', hr⟩ := R.mem_expD.1 hz
    have key : ∀ y, Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p y → g y = g p := by
      intro y hr
      induction hr with
      | refl => rfl
      | @tail b c hbr hstep ih =>
        obtain ⟨e, he, hec⟩ := hstep
        have hcD :=
          R.mem_expD.2 ⟨R.rtg_mem_dcells (Finset.mem_filter.1 hp').1 (hbr.tail ⟨e, he, hec⟩), p, hp',
            hbr.tail ⟨e, he, hec⟩⟩
        have hesep : e ∉ bd := by
          intro hebd
          have hsep := (R.mem_expBd_iff.1 hebd).2
          unfold IsSep at hsep
          have hbU := fun h => (Finset.mem_sdiff.1 (expD_subset_expX p₁ p₂ A (R.mem_expD.2 ⟨R.rtg_mem_dcells (Finset.mem_filter.1 hp').1 hbr, p, hp', hbr⟩))).2 h
          have hcU := fun h => (Finset.mem_sdiff.1 (expD_subset_expX p₁ p₂ A hcD)).2 h
          rcases hec with h | h <;> grind
        rcases hec with h | h <;> grind
    grind
  have hX : ∀ w, Relation.ReflTransGen (StepRel dualEnds R.inner) w q₁ → w ∈ R.dcells →
      w ∉ R.expU p₁ p₂ A → g w = g q₁ := by
    intro w hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => simp
    | @head w y hstep hrest ih =>
      intro hwc hwU
      by_cases hwD : w ∈ R.expD p₁ A
      · exact hD1 w hwD
      · have hyc := R.stepRel_mem_dcells hstep
        have hyU : y ∉ R.expU p₁ p₂ A := by
          intro hyU
          apply hwU
          obtain ⟨_, hyD, t, ht, htD, hr'⟩ := R.mem_expU.1 hyU
          exact R.mem_expU.2 ⟨hwc, hwD, t, ht, htD, hr'.tail ⟨hyD, hwD, stepRel_symm hstep⟩⟩
        obtain ⟨e, he, hec⟩ := hstep
        have hesep : e ∉ bd := by
          intro hebd
          have hsep := (R.mem_expBd_iff.1 hebd).2
          unfold IsSep at hsep
          rcases hec with h | h <;> grind
        rcases hec with h | h <;> grind
  have hXall := fun w hw hwU =>
    hX w (R.dual_connected hw' hh hw ((Finset.mem_filter.1 hq₁).1)) hw hwU
  -- every boundary edge carries the same value
  have hbdval : ∀ e ∈ bd, f e = g q₁ + g q₂ := by
    intro e he
    have hei := hbdinner e he
    have hmem := R.dData.mem e hei
    have hsep := (R.mem_expBd_iff.1 he).2
    unfold IsSep at hsep
    rw [← (hg e hei)]
    by_cases h1 : (dualEnds e).1 ∈ R.expU p₁ p₂ A
    · rw [hU _ h1, hXall _ hmem.2 (hsep.1 h1)]; ring
    · have h2 : (dualEnds e).2 ∈ R.expU p₁ p₂ A := by
        grind
      rw [hU _ h2, hXall _ hmem.1 h1]
  grind

end Rect

end PottsDiscontinuity.TorusCrossing
