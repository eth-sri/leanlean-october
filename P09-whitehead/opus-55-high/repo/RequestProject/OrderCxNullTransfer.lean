import RequestProject.OrderCxNatHtpy
import RequestProject.OrderCxConeNull
import RequestProject.Tac


/-! Null homotopies transfer through an actual order homotopy, including changing bases. -/
bwd

namespace FiniteChains.Comb

theorem htpy_nil_of_conjugate {a b}
    {e p} (he : IsPathX X e a b)
    (hp : IsPathX X p a a)
    (h : Htpy X b b (revPath e ++ p ++ e) []) : Htpy X a a p [] := by
  have hc := htpy_append_revPath he
  have hA := hc.congr_append (show IsPathX X [] a a from rfl)
    (hp.append (he.append (isPath_revPath he)))
  have hB := hc.congr_append hp (show IsPathX X [] a a from rfl)
  have hstrip : Htpy X a a (e ++ (revPath e ++ p ++ e) ++ revPath e) p := by
    simpa using hA.trans (by simpa using hB)
  have hstep := h.congr_append he (isPath_revPath he)
  have hkill :=
    hstep.trans (by simpa using hc)
  exact hstrip.symm.trans hkill

variable {P Q : Type} [Preorder P] [Preorder Q]

/-- Pointwise comparable monotone maps preserve and reflect null homotopy of their images.
The proof uses the connecting edge at the base and cancels it, so fixed bases are unnecessary. -/
theorem htpy_nil_mapPath_le_iff hf hg
    (hfg : ∀ x, f x ≤ g x) {a : P} {p}
    (hp : IsPathX (orderCx P) p a a) :
    Htpy (orderCx Q) (f a) (f a) (mapPath (orderCxMap f hf) p) [] ↔
      Htpy (orderCx Q) (g a) (g a) (mapPath (orderCxMap g hg) p) [] := by
  have hnat := htpy_loop_mapPath_le hf hg hfg hp
  constructor
  · intro h
    have hh := h.congr_append (isPath_ordNeg (hfg a)) (isPath_ordPos (hfg a))
    exact hnat.trans (hh.trans (by simpa using htpy_ordNeg_ordPos _))
  · intro h
    apply htpy_nil_of_conjugate (isPath_ordPos (hfg a))
      (isPath_mapPath _ hp)
    simpa using hnat.symm.trans h

/-- An explicit three-step order contraction gives simple connectedness. -/
theorem simplyConnected_orderCx_of_zigzag
    (hf : Monotone f) (hg : Monotone g) (hig : ∀ x, x ≤ g x)
    (hfg : ∀ x, f x ≤ g x) (d : P) (hfd : ∀ x, f x ≤ d) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hc := htpy_nil_mapPath_const d hp
  have hfnil := (htpy_nil_mapPath_le_iff hf monotone_const hfd hp).mpr hc
  have hgnil := (htpy_nil_mapPath_le_iff hf hg hfg hp).mp hfnil
  have hinil := (htpy_nil_mapPath_le_iff monotone_id hg hig hp).mpr hgnil
  simpa [mapPath, orderCxMap] using hinil

/-- The same contraction supplies paths to the common point, hence connectedness. -/
theorem isConnected_orderCx_of_zigzag {f g : P → P}
    (hig : ∀ x, x ≤ g x) (hfg : ∀ x, f x ≤ g x)
    d (hfd : ∀ x, f x ≤ d) : IsConnected (orderCx P) := by
  let p (a : P) :=
    [ordPos (hig a), ordNeg (hfg a), ordPos (hfd a)]
  have hp (a : P) : IsPathX (orderCx P) (p a) a d :=
    by aesop
  intro a b
  exact ⟨p a ++ revPath (p b), (hp a).append (isPath_revPath (hp b))⟩
