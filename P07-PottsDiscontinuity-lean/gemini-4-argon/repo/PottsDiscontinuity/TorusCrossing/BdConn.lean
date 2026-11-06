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

theorem prop_ne_iff (P Q : Prop) : (P ≠ Q) ↔ (P ↔ ¬ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem mem_expBd_iff {p₁ p₂ : ℤ} {A : Finset Cell} {m : Cell} :
    m ∈ R.expBd p₁ p₂ A ↔
      m ∈ R.inner ∧ IsSep (fun z => z ∈ R.expU p₁ p₂ A) m := by
  unfold expBd IsSep
  rw [Finset.mem_filter, prop_ne_iff]

theorem faceRow_nonempty (hw : 0 < R.w) (r : ℤ) (h1 : R.y0 ≤ r) (h2 : r ≤ R.y0 + R.h) :
    ∃ z ∈ R.faceRow r, True := by
  have hw' : (0 : ℤ) < R.w := by exact_mod_cast hw
  by_cases hp : IsPrimal (R.x0, r)
  · refine ⟨(R.x0 + 1, r), ?_, trivial⟩
    rw [faceRow, Finset.mem_filter, mem_dcells, mem_cells]
    unfold IsPrimal at *
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, rfl⟩ <;> dsimp only <;> omega
  · refine ⟨(R.x0, r), ?_, trivial⟩
    rw [faceRow, Finset.mem_filter, mem_dcells, mem_cells]
    unfold IsPrimal at *
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, rfl⟩ <;> dsimp only <;> omega

theorem cdeg_ind_eq (S : Finset Cell) (c : Cell) :
    cdeg (ind S) c = (((corners c).filter (fun m => m ∈ S)).card : ZMod 2) := by
  rw [card_filter_corners]; unfold cdeg ind; push_cast; simp

theorem mem_expD_of_faceRow {p₁ : ℤ} {A : Finset Cell} {z : Cell} (hz : z ∈ R.faceRow p₁) :
    z ∈ R.expD p₁ A :=
  Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, z, hz, Relation.ReflTransGen.refl⟩

theorem not_mem_expU_of_faceRow {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell}
    (hz : z ∈ R.faceRow p₁) : z ∉ R.expU p₁ p₂ A := fun h =>
  expU_subset_not_expD h (R.mem_expD_of_faceRow hz)

theorem mem_expU_of_faceRow {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell}
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) (hz : z ∈ R.faceRow p₂) :
    z ∈ R.expU p₁ p₂ A :=
  Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, hb z hz, z, hz, hb z hz,
    Relation.ReflTransGen.refl⟩

theorem faceRow_mem {r : ℤ} {z : Cell} : z ∈ R.faceRow r ↔ z ∈ R.dcells ∧ z.2 = r :=
  Finset.mem_filter

theorem label_row {p₁ p₂ : ℤ} {A : Finset Cell} (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨
      (p₁ = R.y0 + R.h ∧ p₂ = R.y0)) (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    {z z' : Cell} (hz : z ∈ R.dcells) (hz' : z' ∈ R.dcells) (r : ℤ)
    (hr : r = R.y0 ∨ r = R.y0 + R.h) (hzr : z.2 = r) (hz'r : z'.2 = r) :
    (z ∈ R.expU p₁ p₂ A ↔ z' ∈ R.expU p₁ p₂ A) := by
  have h1 : z ∈ R.faceRow r := R.faceRow_mem.2 ⟨hz, hzr⟩
  have h2 : z' ∈ R.faceRow r := R.faceRow_mem.2 ⟨hz', hz'r⟩
  rcases (show r = p₁ ∨ r = p₂ by omega) with rfl | rfl
  · exact iff_of_false (R.not_mem_expU_of_faceRow h1) (R.not_mem_expU_of_faceRow h2)
  · exact iff_of_true (R.mem_expU_of_faceRow hb h1) (R.mem_expU_of_faceRow hb h2)

theorem expBd_cdeg_zero (hh : 0 < R.h) {p₁ p₂ : ℤ} {A : Finset Cell}
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A) {c : Cell} (hc : c ∈ R.pcells)
    (hx1 : R.x0 < c.1) (hx2 : c.1 < R.x0 + R.w) :
    cdeg (ind (R.expBd p₁ p₂ A)) c = 0 := by
  have hcc := mem_cells.1 (mem_pcells.1 hc).1
  have hcp := (mem_pcells.1 hc).2
  have hWE : ((c.1 - 1, c.2) : Cell) ∈ R.dcells ∧ ((c.1 + 1, c.2) : Cell) ∈ R.dcells := by
    rw [mem_dcells, mem_dcells, mem_cells, mem_cells]; unfold IsPrimal at *
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩⟩ <;> dsimp only <;> omega
  rw [cdeg_ind_eq, Finset.filter_congr fun _ _ => R.mem_expBd_iff]
  obtain ⟨k, hk⟩ := sep_deg_even R hh (fun z => z ∈ R.expU p₁ p₂ A) c hcp hx1 hx2 hcc.2.2.1 hcc.2.2.2
    (fun hy => R.label_row hp hb hWE.1 hWE.2 R.y0 (Or.inl rfl) hy hy)
    (fun hy => R.label_row hp hb hWE.1 hWE.2 (R.y0 + R.h) (Or.inr rfl) hy hy)
  rw [hk]; push_cast; exact zmod2_two _

section Potential

variable {R}
variable (f g : Cell → ZMod 2)

theorem g_two (hh : 0 < R.h) (hfin : ∀ m, f m ≠ 0 → m ∈ R.inner)
    (hg : ∀ m ∈ R.inner, g (dualEnds m).1 + g (dualEnds m).2 = f m)
    (hclosed : ∀ c : Cell, IsPrimal c → R.x0 < c.1 → c.1 < R.x0 + R.w → cdeg f c = 0)
    {i r : ℤ} (hr : r = R.y0 ∨ r = R.y0 + R.h) (hz : ((i, r) : Cell) ∈ R.dcells)
    (hz' : ((i + 2, r) : Cell) ∈ R.dcells) : g (i, r) = g (i + 2, r) := by
  have hzc := mem_cells.1 (mem_dcells.1 hz).1
  have hzc' := mem_cells.1 (mem_dcells.1 hz').1
  have hzp := (mem_dcells.1 hz).2
  unfold IsPrimal at hzp
  have hh' : (0 : ℤ) < R.h := by exact_mod_cast hh
  have hcd := hclosed (i + 1, r) (by unfold IsPrimal; dsimp; omega) (by dsimp; omega) (by dsimp; omega)
  have hzero (m : Cell) (hm : m.2 ≤ R.y0 ∨ R.y0 + R.h < m.2) : f m = 0 := by
    by_contra hne; have := mem_inner.1 (hfin m hne); omega
  rcases hr with hr | hr
  · have e3 := hg (i + 1, r + 1) (by rw [mem_inner]; dsimp; omega)
    have e4 := hg (i + 2, r + 1) (by rw [mem_inner]; dsimp; omega)
    rw [show dualEnds ((i + 1, r + 1) : Cell) = ((i + 1, r + 1), (i, r)) by
      unfold dualEnds; rw [ite_eq_right (by dsimp; omega)]; ext <;> simp] at e3
    rw [show dualEnds ((i + 2, r + 1) : Cell) = ((i + 1, r + 1), (i + 2, r)) by
      unfold dualEnds; rw [ite_eq_left (by dsimp; omega)]; ext <;> simp; ring] at e4
    unfold cdeg at hcd; dsimp only at e3 e4 hcd
    rw [hzero (i + 1, r) (Or.inl (by dsimp; omega)),
      hzero (i + 1 + 1, r) (Or.inl (by dsimp; omega)),
      show i + 1 + 1 = i + 2 by ring] at hcd
    generalize g (i + 1, r + 1) = N at *
    generalize g (i, r) = W at *
    generalize g (i + 2, r) = E at *
    generalize f (i + 1, r + 1) = F3 at *
    generalize f (i + 2, r + 1) = F4 at *
    revert N W E F3 F4; decide
  · have e1 := hg (i + 1, r) (by rw [mem_inner]; dsimp; omega)
    have e2 := hg (i + 2, r) (by rw [mem_inner]; dsimp; omega)
    rw [show dualEnds ((i + 1, r) : Cell) = ((i, r), (i + 1, r - 1)) by
      unfold dualEnds; rw [ite_eq_left (by dsimp; omega)]; ext <;> simp] at e1
    rw [show dualEnds ((i + 2, r) : Cell) = ((i + 2, r), (i + 1, r - 1)) by
      unfold dualEnds; rw [ite_eq_right (by dsimp; omega)]; ext <;> simp; ring] at e2
    unfold cdeg at hcd; dsimp only at e1 e2 hcd
    rw [hzero (i + 1, r + 1) (Or.inr (by dsimp; omega)),
      hzero (i + 1 + 1, r + 1) (Or.inr (by dsimp; omega)),
      show i + 1 + 1 = i + 2 by ring] at hcd
    generalize g (i + 1, r - 1) = S at *
    generalize g (i, r) = W at *
    generalize g (i + 2, r) = E at *
    generalize f (i + 1, r) = F1 at *
    generalize f (i + 2, r) = F2 at *
    revert S W E F1 F2; decide

theorem g_row_le (hh : 0 < R.h) (hfin : ∀ m, f m ≠ 0 → m ∈ R.inner)
    (hg : ∀ m ∈ R.inner, g (dualEnds m).1 + g (dualEnds m).2 = f m)
    (hclosed : ∀ c : Cell, IsPrimal c → R.x0 < c.1 → c.1 < R.x0 + R.w → cdeg f c = 0)
    {r : ℤ} (hr : r = R.y0 ∨ r = R.y0 + R.h) :
    ∀ n : ℕ, ∀ z z' : Cell, z ∈ R.dcells → z' ∈ R.dcells → z.2 = r → z'.2 = r →
      z'.1 - z.1 = 2 * n → g z = g z' := by
  intro n
  induction n with
  | zero =>
    intro z z' _ _ hzr hz'r hn
    exact congrArg g (Prod.ext (by omega) (by omega))
  | succ n ih =>
    intro z z' hz hz' hzr hz'r hn
    have hzc := mem_cells.1 (mem_dcells.1 hz).1
    have hzc' := mem_cells.1 (mem_dcells.1 hz').1
    have hzp := (mem_dcells.1 hz).2
    unfold IsPrimal at hzp
    have hmid : ((z.1 + 2, z.2) : Cell) ∈ R.dcells := by
      rw [mem_dcells, mem_cells]; unfold IsPrimal
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> dsimp only <;> omega
    have h1 : g (z.1, r) = g (z.1 + 2, r) :=
      g_two f g hh hfin hg hclosed hr (by rwa [← hzr]) (by rwa [← hzr])
    have h2 := ih (z.1 + 2, z.2) z' hmid hz' (by dsimp only; omega) hz'r (by dsimp only; omega)
    rw [hzr] at h2
    have heq : g z = g (z.1, r) := by rw [← hzr]
    rw [heq, h1]; exact h2

end Potential

theorem mem_expU {p₁ p₂ : ℤ} {A : Finset Cell} {z : Cell} :
    z ∈ R.expU p₁ p₂ A ↔ z ∈ R.dcells ∧ z ∉ R.expD p₁ A ∧ ∃ t ∈ R.faceRow p₂,
      t ∉ R.expD p₁ A ∧ Relation.ReflTransGen (R.AvoidStep (R.expD p₁ A)) t z :=
  Finset.mem_filter

theorem stepRel_mem_dcells {S : Finset Cell} (hS : S ⊆ R.inner) {y w : Cell}
    (h : StepRel dualEnds S w y) : y ∈ R.dcells := by
  obtain ⟨e, he, h | h⟩ := h <;> have hmem := R.dData.mem e (hS he)
  · simpa [h] using hmem.2
  · simpa [h] using hmem.1

theorem avoid_mem_dcells {E : Finset Cell} {t z : Cell} (ht : t ∈ R.dcells)
    (hr : Relation.ReflTransGen (R.AvoidStep E) t z) : z ∈ R.dcells := by
  induction hr with
  | refl => exact ht
  | @tail b c _ hstep _ => exact R.stepRel_mem_dcells subset_rfl hstep.2.2

theorem bd_connected (hh : 0 < R.h) (hw' : 0 < R.w) {p₁ p₂ : ℤ} {A : Finset Cell}
    (hp : (p₁ = R.y0 ∧ p₂ = R.y0 + R.h) ∨ (p₁ = R.y0 + R.h ∧ p₂ = R.y0))
    (hb : ∀ t ∈ R.faceRow p₂, t ∉ R.expD p₁ A)
    {m m' : Cell} (hm : m ∈ R.expBd p₁ p₂ A) (hm' : m' ∈ R.expBd p₁ p₂ A) :
    Relation.ReflTransGen (StepRel primalEnds (R.expBd p₁ p₂ A))
      (primalEnds m).1 (primalEnds m').1 := by
  set bd := R.expBd p₁ p₂ A
  set K : Cell → Prop := fun x => Relation.ReflTransGen (StepRel primalEnds bd) (primalEnds m).1 x
  by_contra hcon
  have hbdinner : ∀ e ∈ bd, e ∈ R.inner := fun e he => (R.mem_expBd_iff.1 he).1
  have hKedge (e : Cell) (he : e ∈ bd) : K (primalEnds e).1 ↔ K (primalEnds e).2 :=
    ⟨fun h => h.tail ⟨e, he, Or.inl rfl⟩, fun h => h.tail ⟨e, he, Or.inr rfl⟩⟩
  set bd₁ := bd.filter (fun e => K (primalEnds e).1)
  set f : Cell → ZMod 2 := ind bd₁ with hf
  have hfm : f m = 1 := ind_apply_of_mem (Finset.mem_filter.2 ⟨hm, Relation.ReflTransGen.refl⟩)
  have hfm' : f m' = 0 := ind_apply_of_not_mem fun h => hcon (Finset.mem_filter.1 h).2
  have hfin (e : Cell) (he : f e ≠ 0) : e ∈ R.inner := by
    by_contra hne
    exact he (ind_apply_of_not_mem fun h => hne (hbdinner e (Finset.mem_filter.1 h).1))
  have hx0 (e : Cell) (he : e.1 ≤ R.x0) : f e = 0 := by
    by_contra hne; have := mem_inner.1 (hfin e hne); omega
  have hy0 (e : Cell) (he : e.2 ≤ R.y0) : f e = 0 := by
    by_contra hne; have := mem_inner.1 (hfin e hne); omega
  have hclosed (c : Cell) (hcp : IsPrimal c) (hx1 : R.x0 < c.1) (hx2 : c.1 < R.x0 + R.w) :
      cdeg f c = 0 := by
    rw [hf, cdeg_ind_eq]
    by_cases hcc : c ∈ R.pcells
    · by_cases hKc : K c
      · have : (corners c).filter (fun e => e ∈ bd₁) = (corners c).filter (fun e => e ∈ bd) :=
          Finset.filter_congr fun e he => ⟨fun h => (Finset.mem_filter.1 h).1, fun h =>
            Finset.mem_filter.2 ⟨h, by
              rcases (mem_primalEnds_iff c e hcp).2 he with h1 | h1
              · rwa [← h1]
              · exact (hKedge e h).2 (h1 ▸ hKc)⟩⟩
        have h0 := R.expBd_cdeg_zero hh hp hb hcc hx1 hx2
        rwa [this, ← cdeg_ind_eq]
      · rw [Finset.filter_eq_empty_iff.2 fun e he hmem => by
          obtain ⟨hebd, hKe⟩ := Finset.mem_filter.1 hmem
          rcases (mem_primalEnds_iff c e hcp).2 he with rfl | rfl
          · exact hKc hKe
          · exact hKc ((hKedge e hebd).1 hKe)]; simp
    · rw [Finset.filter_eq_empty_iff.2 fun e he hmem => hcc <| by
        have hei := mem_inner.1 (hbdinner e (Finset.mem_filter.1 hmem).1)
        rw [mem_pcells, mem_cells]
        unfold corners at he
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at he
        exact ⟨⟨by omega, by omega, by omega, by omega⟩, hcp⟩]; simp
  set g : Cell → ZMod 2 := leftPotential R.x0 R.y0 f
  have hg (e : Cell) (he : e ∈ R.inner) : g (dualEnds e).1 + g (dualEnds e).2 = f e := by
    have := mem_inner.1 he
    exact leftPotential_primitive R.x0 R.y0 R.w f hx0 hy0 hclosed e (by omega) (by omega)
  have hp1 : p₁ = R.y0 ∨ p₁ = R.y0 + R.h := by omega
  have hp2 : p₂ = R.y0 ∨ p₂ = R.y0 + R.h := by omega
  obtain ⟨q₁, hq₁, -⟩ := R.faceRow_nonempty hw' p₁ (by omega) (by omega)
  obtain ⟨q₂, hq₂, -⟩ := R.faceRow_nonempty hw' p₂ (by omega) (by omega)
  have hrow (r : ℤ) (hr : r = R.y0 ∨ r = R.y0 + R.h) {z z' : Cell}
      (hz : z ∈ R.faceRow r) (hz' : z' ∈ R.faceRow r) : g z = g z' := by
    have hz1 := R.faceRow_mem.1 hz
    have hz1' := R.faceRow_mem.1 hz'
    have hzp := (mem_dcells.1 hz1.1).2
    have hzp' := (mem_dcells.1 hz1'.1).2
    unfold IsPrimal at hzp hzp'
    rcases le_total z.1 z'.1 with hle | hle
    · exact g_row_le f g hh hfin hg hclosed hr ((z'.1 - z.1).toNat / 2) z z'
        hz1.1 hz1'.1 hz1.2 hz1'.2 (by omega)
    · exact (g_row_le f g hh hfin hg hclosed hr ((z.1 - z'.1).toNat / 2) z' z
        hz1'.1 hz1.1 hz1'.2 hz1.2 (by omega)).symm
  have hzeq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  have hnot_sep {P : Cell → Prop} {b c e : Cell}
      (hec : dualEnds e = (b, c) ∨ dualEnds e = (c, b)) (hsame : P b ↔ P c) : ¬ IsSep P e := by
    unfold IsSep
    rcases hec with h | h <;> rw [h] <;> dsimp only <;> tauto
  have hstep_eq {b c e : Cell} (he : e ∈ R.inner)
      (hec : dualEnds e = (b, c) ∨ dualEnds e = (c, b))
      (hsame : b ∈ R.expU p₁ p₂ A ↔ c ∈ R.expU p₁ p₂ A) : g b = g c := by
    have hebd : e ∉ bd := fun hebd => hnot_sep hec hsame (R.mem_expBd_iff.1 hebd).2
    have hnb := hzeq _ _ ((hg e he).trans
      (ind_apply_of_not_mem fun h => hebd (Finset.mem_filter.1 h).1))
    rcases hec with h | h <;> rw [h] at hnb
    · exact hnb
    · exact hnb.symm
  have hchain (t : Cell) (ht : t ∈ R.faceRow p₂) (htD : t ∉ R.expD p₁ A) :
      ∀ z, Relation.ReflTransGen (R.AvoidStep (R.expD p₁ A)) t z →
        z ∉ R.expD p₁ A ∧ g z = g t := by
    intro z hr
    induction hr with
    | refl => exact ⟨htD, rfl⟩
    | @tail b c hbr hstep ih =>
      have hbU : b ∈ R.expU p₁ p₂ A :=
        R.mem_expU.2 ⟨R.avoid_mem_dcells (Finset.mem_filter.1 ht).1 hbr, ih.1, t, ht, htD, hbr⟩
      have hcU : c ∈ R.expU p₁ p₂ A :=
        R.mem_expU.2 ⟨R.avoid_mem_dcells (Finset.mem_filter.1 ht).1 (hbr.tail hstep), hstep.2.1,
          t, ht, htD, hbr.tail hstep⟩
      obtain ⟨_, hcD, e, he, hec⟩ := hstep
      exact ⟨hcD, (hstep_eq he hec (iff_of_true hbU hcU)).symm.trans ih.2⟩
  have hU (z : Cell) (hz : z ∈ R.expU p₁ p₂ A) : g z = g q₂ := by
    obtain ⟨_, _, t, ht, htD, hr⟩ := R.mem_expU.1 hz
    exact (hchain t ht htD z hr).2.trans (hrow p₂ hp2 ht hq₂)
  have hD1 (z : Cell) (hz : z ∈ R.expD p₁ A) : g z = g q₁ := by
    obtain ⟨_, p, hp', hr⟩ := R.mem_expD.1 hz
    have key : ∀ y, Relation.ReflTransGen (StepRel dualEnds (R.inner \ A)) p y → g y = g p := by
      intro y hr
      induction hr with
      | refl => rfl
      | @tail b c hbr hstep ih =>
        obtain ⟨e, he, hec⟩ := hstep
        have hbD : b ∈ R.expD p₁ A :=
          R.mem_expD.2 ⟨R.rtg_mem_dcells (Finset.mem_filter.1 hp').1 hbr, p, hp', hbr⟩
        have hcD : c ∈ R.expD p₁ A :=
          R.mem_expD.2 ⟨R.rtg_mem_dcells (Finset.mem_filter.1 hp').1 (hbr.tail ⟨e, he, hec⟩),
            p, hp', hbr.tail ⟨e, he, hec⟩⟩
        exact (hstep_eq (Finset.mem_sdiff.1 he).1 hec
          (iff_of_false (fun h => expU_subset_not_expD h hbD)
            (fun h => expU_subset_not_expD h hcD))).symm.trans ih
    exact (key z hr).trans (hrow p₁ hp1 hp' hq₁)
  have hX : ∀ w, Relation.ReflTransGen (StepRel dualEnds R.inner) w q₁ → w ∈ R.dcells →
      w ∉ R.expU p₁ p₂ A → g w = g q₁ := by
    intro w hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => intro _ _; rfl
    | @head w y hstep hrest ih =>
      intro hwc hwU
      by_cases hwD : w ∈ R.expD p₁ A
      · exact hD1 w hwD
      · have hyU : y ∉ R.expU p₁ p₂ A := fun hyU => by
          obtain ⟨_, hyD, t, ht, htD, hr'⟩ := R.mem_expU.1 hyU
          exact hwU (R.mem_expU.2 ⟨hwc, hwD, t, ht, htD, hr'.tail ⟨hyD, hwD, stepRel_symm hstep⟩⟩)
        obtain ⟨e, he, hec⟩ := hstep
        exact (hstep_eq he hec (iff_of_false hwU hyU)).trans
          (ih (R.stepRel_mem_dcells subset_rfl ⟨e, he, hec⟩) hyU)
  have hXall (w : Cell) (hw : w ∈ R.dcells) (hwU : w ∉ R.expU p₁ p₂ A) : g w = g q₁ :=
    hX w (R.dual_connected hw' hh hw (Finset.mem_filter.1 hq₁).1) hw hwU
  have hbdval (e : Cell) (he : e ∈ bd) : f e = g q₁ + g q₂ := by
    have hei := hbdinner e he
    have hmem := R.dData.mem e hei
    have hsep := (R.mem_expBd_iff.1 he).2
    unfold IsSep at hsep
    rw [← hg e hei]
    by_cases h1 : (dualEnds e).1 ∈ R.expU p₁ p₂ A
    · rw [hU _ h1, hXall _ hmem.2 (hsep.1 h1), add_comm]
    · rw [hU (dualEnds e).2 (by by_contra h2; exact h1 (hsep.2 h2)), hXall _ hmem.1 h1]
  have e1 := hbdval m hm
  have e2 := hbdval m' hm'
  rw [hfm] at e1
  rw [hfm', ← e1] at e2
  exact absurd e2 (by decide)

end Rect

end PottsDiscontinuity.TorusCrossing
