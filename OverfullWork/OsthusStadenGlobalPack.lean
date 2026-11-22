module

public import OverfullWork.OsthusStadenLayerMerge
public import OverfullWork.OsthusStadenCycleCount

@[expose] public section


/-! The physical coordinates of different layers may differ. Transport
their Hamilton packs to the host and count all of the cycles. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

private theorem spanning_cycle_equiv {X V : Type*} (e : X ≃ V) (f : Equiv.Perm X)
    (h : HasSpanningCycle (fun x y => f x = y)) :
    HasSpanningCycle (fun x y => (e.permCongr f) x = y) := by
  obtain ⟨T,z,hN,hAll,hHead,hCh⟩ := h
  refine ⟨T.map e,e z,hN.map e.injective,?_,?_,?_⟩
  · intro v
    exact List.mem_map.mpr ⟨e.symm v,hAll _,e.apply_symm_apply v⟩
  · rw [List.head?_map,hHead]
    rfl
  · rw [←List.map_singleton,←List.map_append]
    apply List.isChain_map_of_isChain e _ hCh
    intro a b h
    rw [Equiv.permCongr_apply,e.symm_apply_apply,h]

/-- Each layer pack is spanning on the host through its own coordinates.
Distinct host layers are arc-disjoint, giving all `rκ` cycles. -/
theorem combine_physical_layer_packs {V : Type*} {r κ : ℕ}
    (X : Fin r → Type*) (coord : ∀ i, X i ≃ V)
    (D : Digraph V) (H : Fin r → Digraph V)
    (F : ∀ i, Fin κ → Equiv.Perm (X i))
    (hLe : ∀ i, H i ≤ D)
    (hLayer : ∀ i j, i ≠ j → Disjoint (H i) (H j))
    (hCycle : ∀ i f, HasSpanningCycle (fun x y => F i f x = y))
    (hAdj : ∀ i f x, (H i).Adj (coord i x) (coord i (F i f x)))
    (hDis : ∀ i f g, f ≠ g → ∀ x, F i f x ≠ F i g x) :
    ∃ G : Fin (r*κ) → Equiv.Perm V,
      (∀ f, HasSpanningCycle (fun x y => G f x = y)) ∧
      (∀ f x, D.Adj x (G f x)) ∧
      ∀ f g, f ≠ g → ∀ x, G f x ≠ G g x := by
  let e : Fin (r*κ) ≃ Fin r × Fin κ := finProdFinEquiv.symm
  let G (f : Fin (r*κ)) := (coord (e f).1).permCongr (F (e f).1 (e f).2)
  have hH (f : Fin (r*κ)) (x : V) : (H (e f).1).Adj x (G f x) := by
    have h := hAdj (e f).1 (e f).2 ((coord (e f).1).symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h
  refine ⟨G,fun f => spanning_cycle_equiv _ _ (hCycle _ _),fun f x => hLe _ (hH f x),?_⟩
  intro f g hfg x he
  by_cases hi : (e f).1 = (e g).1
  · have hEq : ∀ (i j : Fin r) (a b : Fin κ), i = j →
        (coord i).permCongr (F i a) x = (coord j).permCongr (F j b) x → a = b := by
      intro i j a b h h'
      subst j
      by_contra! hab
      exact hDis i a b hab ((coord i).symm x) ((coord i).injective h')
    exact hfg (e.injective (Prod.ext hi (hEq _ _ _ _ hi he)))
  · exact disjoint_iff_inf_le.mp (hLayer _ _ hi) ⟨hH f x,he.symm ▸ hH g x⟩

end OverfullWork.DirectedRobustExpansion
