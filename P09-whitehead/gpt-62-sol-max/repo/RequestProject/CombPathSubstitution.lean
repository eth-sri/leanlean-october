module

public import RequestProject.CombCoveringLift

@[expose] public section

namespace FiniteChains.Comb
universe u
variable {X Y : Complex2.{u}}

/-- A map realized by paths on edges. Reversed edges trace the reversed path, and the
attaching paths of faces must become null-homotopic. -/
structure PathSubstitution (X Y : Complex2.{u}) where
  onV : X.V → Y.V
  onGerm : X.E × Bool → List (Y.E × Bool)
  valid : ∀ e, IsPath Y.src Y.tgt (onGerm e)
    (onV (germSrc X.src X.tgt e)) (onV (germTgt X.src X.tgt e))
  reverse : ∀ e, onGerm (revGerm e) = revPath (onGerm e)
  faces : ∀ f, Htpy Y (onV (X.base f)) (onV (X.base f)) ((X.att f).flatMap onGerm) []

namespace PathSubstitution

variable (F : PathSubstitution X Y)

theorem isPath {a b : X.V} {p : List (X.E × Bool)} (hp : IsPath X.src X.tgt p a b) :
    IsPath Y.src Y.tgt (p.flatMap F.onGerm) (F.onV a) (F.onV b) := by
  induction p generalizing a with
  | nil => exact congrArg F.onV hp
  | cons e p ih =>
    obtain ⟨rfl, hp⟩ := hp
    exact (F.valid e).append (ih hp)

private theorem step {a b : X.V} {p q : List (X.E × Bool)} (h : Step X a b p q) :
    Htpy Y (F.onV a) (F.onV b) (p.flatMap F.onGerm) (q.flatMap F.onGerm) := by
  obtain ⟨hp, -, hc⟩ := h
  rcases hc with ⟨l, r, e, rfl, rfl⟩ | ⟨l, r, f, rfl, rfl⟩
  · obtain ⟨_, hl, ⟨rfl, _, hr⟩⟩ := isPath_append_iff.mp hp
    rw [germTgt_revGerm] at hr
    simpa [F.reverse, List.flatMap_append, List.append_assoc] using
      (htpy_append_revPath (F.valid e)).congr_append (F.isPath hl) (F.isPath hr)
  · rcases eq_or_ne (X.att f) [] with hz | hz
    · simp [hz, Htpy.refl]
    obtain ⟨w, h₁, hr⟩ := isPath_append_iff.mp hp
    obtain ⟨v, hl, hm⟩ := isPath_append_iff.mp h₁
    have hf := X.att_isLoop f
    have hv := isPath_start_eq hm hf hz
    subst v
    have hw := isPath_endpoint_eq hm hf
    subst w
    simpa [List.flatMap_append] using (F.faces f).congr_append (F.isPath hl) (F.isPath hr)

theorem htpy {a b : X.V} {p q : List (X.E × Bool)} (h : Htpy X a b p q) :
    Htpy Y (F.onV a) (F.onV b) (p.flatMap F.onGerm) (q.flatMap F.onGerm) :=
  h.map_of_step (fun l => l.flatMap F.onGerm) (fun _ _ => F.step)

end PathSubstitution

/-- A path whose closure by two root paths is null is homotopic to the path through the root. -/
theorem htpy_of_rooted_null {o a b : Y.V} {r p s : List (Y.E × Bool)}
    (hr : IsPath Y.src Y.tgt r o a) (hp : IsPath Y.src Y.tgt p a b)
    (hs : IsPath Y.src Y.tgt s o b) (h : Htpy Y o o (r ++ p ++ revPath s) []) :
    Htpy Y a b p (revPath r ++ s) := by
  have h₁ := (htpy_revPath_append hr).congr_append
    (show IsPath Y.src Y.tgt [] a a from rfl) (hp.append ((isPath_revPath hs).append hs))
  have h₂ := (htpy_revPath_append hs).congr_append hp (show IsPath Y.src Y.tgt [] b b from rfl)
  exact ((by simpa [List.append_assoc] using h₁.trans (by simpa using h₂)) :
    Htpy Y a b (revPath r ++ (r ++ p ++ revPath s) ++ s) p).symm.trans
    (by simpa using h.congr_append (isPath_revPath hr) hs)

/-- Paths made of root-path differences telescope. -/
theorem htpy_telescope {S : X.V → Prop} {f : X.V → Y.V} {o : Y.V}
    {γ : X.V → List (Y.E × Bool)} {g : X.E × Bool → List (Y.E × Bool)}
    (hγ : ∀ v, S v → IsPath Y.src Y.tgt (γ v) o (f v))
    (hg : ∀ e, S (germSrc X.src X.tgt e) → S (germTgt X.src X.tgt e) →
      Htpy Y (f (germSrc X.src X.tgt e)) (f (germTgt X.src X.tgt e)) (g e)
        (revPath (γ (germSrc X.src X.tgt e)) ++ γ (germTgt X.src X.tgt e)))
    {p : List (X.E × Bool)} {a b : X.V} (hp : IsPath X.src X.tgt p a b)
    (ha : S a) (hb : S b)
    (hS : ∀ e ∈ p, S (germSrc X.src X.tgt e) ∧ S (germTgt X.src X.tgt e)) :
    Htpy Y (f a) (f b) (p.flatMap g) (revPath (γ a) ++ γ b) := by
  induction p generalizing a with
  | nil =>
    have he : a = b := hp
    subst b
    exact (htpy_revPath_append (hγ a ha)).symm
  | cons e p ih =>
    obtain ⟨rfl, hp⟩ := hp
    have hm := (hS e (List.mem_cons_self ..)).2
    have h₁ := hg e ha hm
    have h₂ := ih hp hm (fun e he => hS e (List.mem_cons_of_mem _ he))
    have hγa := isPath_revPath (hγ _ ha)
    have hγb := hγ _ hb
    have hγm := hγ _ hm
    have h := Htpy.append_congr (h₁.symm.isPath (hγa.append hγm))
      (h₂.symm.isPath ((isPath_revPath hγm).append hγb)) h₁ h₂
    refine h.trans ?_
    simpa [List.append_assoc] using (htpy_append_revPath hγm).congr_append hγa hγb

end FiniteChains.Comb
