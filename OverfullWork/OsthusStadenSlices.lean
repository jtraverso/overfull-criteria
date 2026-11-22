module

public import OverfullWork.OsthusStadenLayerUnwinding
public import OverfullWork.DirectedRegularPairs

@[expose] public section


/-! The actual slices in Osthus–Staden §5.3. Each arc retains its base
copy, and the two refined labels identify its slice uniquely. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset DirectedRegularPairs
open scoped Classical
variable {V U : Type*}

abbrev RefinedVertex (U : Type*) (s p : ℕ) := (U × ZMod s) × ZMod p

def unwoundSlice {r s p : ℕ}
    (copy : Fin r → U → Digraph V) (label : Fin r → V → Option (RefinedVertex U s p))
    (F : RefinedFactorIndex r s p → Equiv.Perm (RefinedVertex U s p))
    (j : RefinedFactorIndex r s p) : Digraph V :=
  ⟨fun x y => ∃ a, label j.1 x = some a ∧ label j.1 y = some (F j a) ∧ (copy j.1 a.1.1).Adj x y⟩

theorem unwoundSlice_pair {r s p : ℕ}
    (copy : Fin r → U → Digraph V) (label : Fin r → V → Option (RefinedVertex U s p))
    (F : RefinedFactorIndex r s p → Equiv.Perm (RefinedVertex U s p))
    (j : RefinedFactorIndex r s p) (a : RefinedVertex U s p) {x y : V}
    (hx : label j.1 x = some a) (hy : label j.1 y = some (F j a)) :
    (unwoundSlice copy label F j).Adj x y ↔ (copy j.1 a.1.1).Adj x y := by
  constructor
  · rintro ⟨b,hb,_,h⟩
    have he := Option.some.inj (hb.symm.trans hx)
    subst b
    exact h
  · intro h
    exact ⟨a,hx,hy,h⟩

theorem unwoundSlice_le {r s p : ℕ} (D : Digraph V)
    (copy : Fin r → U → Digraph V) (label : Fin r → V → Option (RefinedVertex U s p))
    (F : RefinedFactorIndex r s p → Equiv.Perm (RefinedVertex U s p))
    (hLe : ∀ i u, copy i u ≤ D) (j : RefinedFactorIndex r s p) :
    unwoundSlice copy label F j ≤ D := by
  rintro x y ⟨a,_,_,ha⟩
  exact hLe _ _ ha

theorem disjoint_unwoundSlices {r s p : ℕ}
    (copy : Fin r → U → Digraph V) (label : Fin r → V → Option (RefinedVertex U s p))
    (F : RefinedFactorIndex r s p → Equiv.Perm (RefinedVertex U s p))
    (hCopy : ∀ i j, i ≠ j → ∀ u v, Disjoint (copy i u) (copy j v))
    (hSect : ∀ i a a' b b', (a,b) ≠ (a',b') → ∀ x, F (i,a,b) x ≠ F (i,a',b') x) :
    ∀ i j, i ≠ j → Disjoint (unwoundSlice copy label F i) (unwoundSlice copy label F j) := by
  rintro ⟨i,a,b⟩ ⟨j,c,d⟩ h
  rw [disjoint_iff_inf_le]
  rintro x y ⟨⟨u,hx,hy,hu⟩,⟨v,hx',hy',hv⟩⟩
  by_cases he : i = j
  · subst j
    have hEq := Option.some.inj (hx.symm.trans hx')
    subst v
    exact hSect i a c b d (fun h' => h (Prod.ext rfl h')) u (Option.some.inj (hy.symm.trans hy'))
  · exact (disjoint_iff_inf_le.mp (hCopy i j he u.1.1 v.1.1)) ⟨hu,hv⟩

/-- Against a fixed pair of selected cells, the slice and its original
copy have the same incidence counts and hence the same regularity. -/
theorem uniform_unwoundSlice_pair [Fintype V] {r s p : ℕ}
    (copy : Fin r → U → Digraph V) (label : Fin r → V → Option (RefinedVertex U s p))
    (F : RefinedFactorIndex r s p → Equiv.Perm (RefinedVertex U s p))
    (j : RefinedFactorIndex r s p) (a : RefinedVertex U s p) (A B : Finset V) (ε : ℝ)
    (hA : ∀ v ∈ A, label j.1 v = some a)
    (hB : ∀ v ∈ B, label j.1 v = some (F j a))
    (hR : IsUniform (copy j.1 a.1.1) ε A B) :
    IsUniform (unwoundSlice copy label F j) ε A B ∧
      density (unwoundSlice copy label F j) A B = density (copy j.1 a.1.1) A B := by
  have he (X Y : Finset V) (hX : X ⊆ A) (hY : Y ⊆ B) :
      density (unwoundSlice copy label F j) X Y = density (copy j.1 a.1.1) X Y := by
    unfold density
    simp only [incidences_eq_sum]
    congr 1
    apply sum_congr rfl
    intro v hv
    apply sum_congr rfl
    intro u hu
    exact if_congr (unwoundSlice_pair copy label F j a (hA _ (hX hu)) (hB _ (hY hv))) rfl rfl
  refine ⟨?_,he A B (subset_refl _) (subset_refl _)⟩
  intro X hX Y hY hX' hY'
  rw [he X Y hX hY,he A B (subset_refl _) (subset_refl _)]
  exact hR X hX Y hY hX' hY'

end OverfullWork.DirectedRobustExpansion
