module

public import OverfullWork.SaturatedCentreColouring
public import OverfullWork.MultigraphActiveSupport

@[expose] public section


/-! # Saturated centres with arbitrary isolated vertices

The remaining obstruction has an ordinary vertex of positive degree,
with every incident bundle bounded by mu. This is precisely the row
where CMS Lemma 3.10 applies its multifan argument.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem colourable_of_active_saturated_centre (M : MultiGraph V) (a : V) (μ : ℕ)
    (hoff : ∀ u v, u ≠ a → v ≠ a → M.mult s(u,v) ≤ μ)
    (hsat : ∀ v, v ≠ a → 0 < M.degree v → μ ≤ M.mult s(a,v)) :
    Nonempty (M.EdgeColoring (M.degree a+μ)) := by
  let S := M.activeWith a
  let x : S := ⟨a,(M.mem_activeWith a a).mpr (Or.inl rfl)⟩
  have hcol := (M.onVertices S).colourable_of_saturated_centre x μ (by
    intro u v hu hv
    exact hoff u.val v.val (fun he => hu (Subtype.ext he)) (fun he => hv (Subtype.ext he))) (by
    intro v hv
    have hva : v.val ≠ a := fun he => hv (Subtype.ext he)
    have hpos := (M.mem_activeWith a v.val).mp v.property
    exact hsat v.val hva (hpos.resolve_left hva))
  have hd : (M.onVertices S).degree x = M.degree a := M.onVertices_active_degree a x
  rw [hd] at hcol
  exact M.colourable_of_activeWith a _ hcol

theorem exists_bounded_row_of_not_colourable (M : MultiGraph V) (a : V) (d μ : ℕ)
    (hoff : ∀ u v, u ≠ a → v ≠ a → M.mult s(u,v) ≤ μ) (ha : M.degree a ≤ d)
    (hNo : ¬Nonempty (M.EdgeColoring (d+μ))) :
    ∃ v, v ≠ a ∧ 0 < M.degree v ∧ M.mult s(a,v) < μ ∧ ∀ w, M.mult s(v,w) ≤ μ := by
  have hbad : ¬∀ v, v ≠ a → 0 < M.degree v → μ ≤ M.mult s(a,v) := by
    intro hsat
    obtain ⟨C⟩ := M.colourable_of_active_saturated_centre a μ hoff hsat
    exact hNo (C.enlarge (by omega))
  push Not at hbad
  obtain ⟨v,hva,hpos,hsmall⟩ := hbad
  refine ⟨v,hva,hpos,hsmall,?_⟩
  intro w
  by_cases hw : w=a
  · subst w
    rw [show s(v,a) = s(a,v) from Sym2.eq_swap]
    exact hsmall.le
  · exact hoff v w hva hw

end SimpleGraph.MultiGraph
