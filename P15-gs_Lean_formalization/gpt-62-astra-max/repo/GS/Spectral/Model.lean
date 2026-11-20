module
public import GS.Spectral.Base
public import GS.Spectral.Cone
public import GS.Spectral.Patch
@[expose] public section

/-! A chart of the dephased slice changes the middle spectral variables into
scalar coordinates and a rank-one cone. Use the *same* compact parameter
space on both sides; the diagonal intertwiner test identifies the fibres. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open GS.Isometric Matrix Filter Set
open scoped Topology
namespace GS.Spectral
variable {𝕜 : Type} [RCLike 𝕜] {q r d : ℕ} (Q : U 𝕜 q) (o : Fin q) (hne : ∀ i j, Q.val i j ≠ 0)
def ref : Slice Q o := ⟨Q,ref_anchored Q o hne⟩
def marked : range (@eval 𝕜 _ q) := ⟨base Q, build_base Q o 1 ▸ build_mem (1 : Outer 𝕜 o) 1 (fun _ => Q)⟩
variable (C : Patch (V d) (Slice Q o) (ref Q o hne)) (e : (ℝ × 𝕜) ≃L[ℝ] V r)
local notation "ψ" => (Subtype.val ∘ Patch.map C)

lemma spectral_fibres {s t : U 𝕜 2} (x y : Fin 2 → C.K) :
    middle s (ψ ∘ x) = middle t (ψ ∘ y) ↔ spectrum e s (Subtype.val ∘ x) = spectrum e t (Subtype.val ∘ y) := by
  let f (a : C.K) (ij : Fin q × Fin q) := (ψ a).val ij.1 ij.2
  let g (a : C.K) (j : Fin d) : 𝕜 := (a.val j : 𝕜)
  have hf : Function.Injective f := fun a b h => C.inj (Subtype.ext (Subtype.ext (Matrix.ext (fun i j => congrFun h (i,j)))))
  have hg : Function.Injective g := fun a b h => Subtype.ext (funext fun j => RCLike.ofReal_injective (congrFun h j))
  have eq := mix_fibres (x := x) (y := y) (s := s) (t := t) f g (fun a b => hf.eq_iff.trans hg.eq_iff.symm)
  conv_rhs => rw [← (realize_inj e).eq_iff, funext_iff]; simp only [realize_spectrum]
  refine Iff.trans ?_ eq
  exact ⟨fun h ij => congrFun (congrFun h ij.1) ij.2, fun h => funext fun i => funext fun j => h (i,j)⟩

lemma near_patch {A : U 𝕜 q} (hg : Good Q o A) (hc : clean Q o A = Q) :
    ∀ᶠ B in 𝓝 A, clean Q o B ∈ range ψ := by
  let f (b : {B // Good Q o B}) : Slice Q o := ⟨clean Q o b.val,clean_anchored Q o b.property⟩
  have hf : Continuous f := (continuous_iff_continuousAt.mpr (fun b => (clean_continuousAt Q o b.property).comp continuous_subtype_val.continuousAt)).subtype_mk _
  have he : f ⟨A,hg⟩ = ref Q o hne := Subtype.ext hc
  have hs := hf.continuousAt.preimage_mem_nhds (show range C.map ∈ 𝓝 (f ⟨A,hg⟩) by rw [he]; exact C.covers)
  filter_upwards [(good_open Q o).isOpenMap_subtype_val.image_mem_nhds hs] with B hb
  obtain ⟨a,⟨v,hv⟩,e⟩ := hb; subst B
  exact ⟨v,congrArg Subtype.val hv⟩

include C e in
theorem local_model : Local.Model (marked Q o) ((1 : Outer 𝕜 o),(vertex : Target r d)) := by
  letI : CompactSpace C.K := isCompact_iff_compactSpace.mp C.compact
  let D := Outer 𝕜 o × U 𝕜 2 × (Fin 2 → C.K)
  let F (p : D) : range (@eval 𝕜 _ q) := ⟨build p.1 p.2.1 (ψ ∘ p.2.2),build_mem ..⟩
  let G (p : D) := (p.1,spectrum e p.2.1 (Subtype.val ∘ p.2.2))
  have hψ : Continuous ψ := continuous_subtype_val.comp C.cont
  have comp {Y : Type} [TopologicalSpace Y] {f : C.K → Y} (h : Continuous f) : Continuous (fun p : D => f ∘ p.2.2) := continuous_pi fun k => h.comp ((continuous_apply k).comp continuous_snd.snd)
  have hf : Continuous F := ((build_cont (o := o)).comp (continuous_fst.prodMk (continuous_snd.fst.prodMk (comp hψ)))).subtype_mk _
  have hg : Continuous G := continuous_fst.prodMk ((continuous_spectrum e).comp (continuous_snd.fst.prodMk (comp continuous_subtype_val)))
  have eq (a b : D) : F a = F b ↔ G a = G b := by
    rw [Subtype.ext_iff,Prod.ext_iff]; apply (build_fibres Q o (fun k => (C.map (a.2.2 k)).property) (fun k => (C.map (b.2.2 k)).property)).trans
    exact and_congr_right' (spectral_fibres Q o hne C e ..)
  obtain ⟨chart,hchart⟩ := GS.exists_homeomorph_ranges_of_same_fibres F G hf hg eq
  let z : C.K := ⟨0,mem_of_mem_nhds C.around⟩
  let p₀ : D := (1,1,fun _ => z)
  have f₀ : F p₀ = marked Q o := by
    apply Subtype.ext; change build 1 1 (fun _ => (C.map z).val) = base Q
    rw [show C.map z = ref Q o hne from C.point]; exact build_base Q o 1
  have g₀ : G p₀ = (1,vertex) := by
    refine Prod.ext rfl ?_; ext <;> simp [G,spectrum,delta,center,RankLocus.outer,RankLocus.tip,vecMulVec,p₀,z,vertex]
  let a : range F := ⟨F p₀,mem_range_self _⟩
  have hv : (chart a).val = (1,vertex) := (congrArg Subtype.val (hchart p₀)).trans g₀
  rw [← (show a.val = marked Q o from f₀),← hv]; apply Local.around
  · change range F ∈ 𝓝 (F p₀); rw [f₀]
    have h := (continuous_eval.subtype_mk (Set.mem_range_self (f := @eval 𝕜 _ q))).isClosedMap.eventually_nhds_fiber
      (p := fun p => ∀ k, clean Q o (p.2.1 k) ∈ range ψ) (marked Q o) (fun p hp => ?_)
    · filter_upwards [h] with b hb
      obtain ⟨p,hp⟩ := rangeFactorization_surjective b
      choose v hv using hb p hp
      refine ⟨(frames Q o p,p.2.2 o,v),Subtype.ext ?_⟩
      change build _ _ (ψ ∘ v) = b.val
      rw [show ψ ∘ v = clean Q o ∘ p.2.1 from funext hv,build_clean]; exact congrArg Subtype.val hp
    · apply Filter.eventually_all.mpr; intro k
      have he : eval p = base Q := congrArg Subtype.val hp
      exact (((continuous_apply k).comp (continuous_fst.comp continuous_snd)).continuousAt : ContinuousAt (fun p : Raw 𝕜 q => p.2.1 k) p) (near_patch Q o hne C (good_base Q o p he hne k) (clean_base Q o p he hne k))
  · rw [hv]
    have h := (isClosedMap_snd_of_compactSpace (X := U 𝕜 2)).eventually_nhds_fiber
      (p := fun p => ∀ k, recover e p.1 p.2 k ∈ C.K) vertex (fun ⟨s,p⟩ hp => ?_)
    · filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds h] with p hp
      obtain ⟨s,a,ea⟩ := spectrum_onto e p.2
      have hrec : recover e s p.2 = a := ea ▸ recover_spec e s a
      have hk : ∀ k, a k ∈ C.K := hrec ▸ hp (s,p.2) rfl
      exact ⟨(p.1,s,fun k => ⟨a k,hk k⟩),Prod.ext rfl ea⟩
    · change p = vertex at hp; subst p
      apply Filter.eventually_all.mpr; intro k
      exact ((continuous_apply k).comp (continuous_recover e)).continuousAt.preimage_mem_nhds (by simpa [recover_vertex] using C.around)
end GS.Spectral
