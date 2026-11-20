module
public import GS.Spectral.Chart
public import GS.Spectral.Model
@[expose] public section

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.Isometric Set
open scoped ComplexOrder Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace GS.Spectral
variable {𝕜 : Type} [RCLike 𝕜] {q : ℕ} (Q : U 𝕜 q) (o : Fin q)
private def positive : Set (U 𝕜 q) := {A | (∀ i, 0 < RCLike.re (A.val i o / Q.val i o)) ∧ ∀ j, 0 < RCLike.re (A.val o j / Q.val o j)}
private lemma positive_open : IsOpen (positive Q o) := by
  have h (i j : Fin q) : IsOpen {A : U 𝕜 q | 0 < RCLike.re (A.val i j / Q.val i j)} :=
    isOpen_lt continuous_const (RCLike.continuous_re.comp ((continuous_entry i j).div_const _))
  simp only [positive,Set.ofPred_and,Set.ofPred_forall]
  exact (isOpen_iInter_of_finite fun i => h i o).inter (isOpen_iInter_of_finite fun j => h o j)

private lemma positive_iff (A : U 𝕜 q) (ha : A ∈ positive Q o) : Anchored Q o A ↔ constraint Q o A.val = 0 := by
  change _ ↔ ((fun i => skewAdjointPart ℝ (A.val i o / Q.val i o)),(fun j : {j : Fin q // j ≠ o} => skewAdjointPart ℝ (A.val o j.val / Q.val o j.val))) = 0
  simp only [Anchored,RCLike.pos_iff (K := 𝕜),Prod.ext_iff,funext_iff,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,im_zero]
  obtain ⟨hc,hr⟩ := ha
  constructor
  · simp_all
  · exact fun ⟨a,b⟩ => ⟨fun i => ⟨hc i,a i⟩,fun j => ⟨hr j,by by_cases hj : j=o; exact hj ▸ a o; simp_all⟩⟩

abbrev Width := Module.finrank ℝ (derivLevel Q o).ker
variable (hne : ∀ i j, Q.val i j ≠ 0)
include hne in
lemma slice_patch : Nonempty (Patch (V (Width Q o)) (Slice Q o) (ref Q o hne)) := by
  let d := derivLevel Q o
  let v := (level_strict Q o).implicitToOpenPartialHomeomorph (levels Q o) d (level_onto Q o hne)
  let w := ((groupChart Q).trans v).restrOpen _ (positive_open Q o)
  have hQ : Q ∈ positive Q o := ⟨fun i => by simp [hne],fun j => by simp [hne]⟩
  have hs : Q ∈ w.source := ⟨⟨groupChart_source Q,by change groupChart Q Q ∈ v.source; rw [groupChart_base]; exact (level_strict Q o).mem_implicitToOpenPartialHomeomorph_source (level_onto Q o hne)⟩,hQ⟩
  have h₀ : w Q = (0,0) := by
    change v (groupChart Q Q) = _; rw [groupChart_base]; simp only [v,HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self]
    exact Prod.ext (by simpa [levels] using! (positive_iff Q o Q hQ).mp (ref_anchored Q o hne)) rfl
  have hz (A : U 𝕜 q) (ha : A ∈ w.source) : Anchored Q o A ↔ (w A).1 = 0 := by
    change _ ↔ (v (groupChart Q A)).1 = 0
    simp only [v,HasStrictFDerivAt.implicitToOpenPartialHomeomorph_fst,levels,Function.comp_apply]
    have h : ((groupChart Q).symm (groupChart Q A)).val = A.val := congrArg Subtype.val ((groupChart Q).left_inv ha.1.1)
    rw [h]; exact positive_iff Q o A ha.2
  let k : d.ker ≃L[ℝ] V (Width Q o) := ContinuousLinearEquiv.ofFinrankEq (E := ↥d.ker) (F := V (Width Q o)) (by simp [V,Width,d])
  exact level_patch w (ref Q o hne) hs k.toHomeomorph (by change k (w Q).2 = 0; simp [h₀]) hz

include hne in
lemma width_add : Width Q o + (q + (q-1)) * Module.finrank ℝ (Im 𝕜) = Module.finrank ℝ (G 𝕜 q) := by
  have h := LinearMap.finrank_range_add_finrank_ker (derivLevel Q o).toLinearMap
  rw [level_onto Q o hne,finrank_top] at h
  simpa [Anchors,Width,Module.finrank_pi_fintype,add_mul,Nat.add_comm] using h
end GS.Spectral
