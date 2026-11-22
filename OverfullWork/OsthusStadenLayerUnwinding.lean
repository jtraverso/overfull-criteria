module

public import OverfullWork.FactorUnwinding
public import OverfullWork.DirectedMultigraphFactors

@[expose] public section


/-! The two levels of reduced 1-factor refinement in Osthus–Staden §5.3.
Parallel base arcs are counted with their actual multiplicities. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

abbrev RefinedFactorIndex (r s p : ℕ) := Fin r × UnwindingLabel s × UnwindingLabel p

theorem card_refined_factor_index (r s p : ℕ) [NeZero s] [NeZero p] :
    Fintype.card (RefinedFactorIndex r s p) = r*((s-1)*(p-1)) := by
  simp only [RefinedFactorIndex,UnwindingLabel,Fintype.card_prod,Fintype.card_fin,count_unwinding_increments]

/-- Refine each original factor twice and retain the separation property
in every second-stage cycle. -/
theorem exists_two_level_factor_unwinding {r : ℕ} (σ : Fin r → Equiv.Perm V)
    (hFixed : ∀ i v, σ i v ≠ v)
    (m p : ℕ) [NeZero p] (hm : 0 < m) (hp : p.Prime) (hp2 : 2 < p) :
    ∃ F₁ : Fin r → UnwindingLabel (2*m) → Equiv.Perm (V × ZMod (2*m)),
    ∃ C₂ : ∀ i a, FactorCycleCoordinates (F₁ i a),
    ∃ F₂ : RefinedFactorIndex r (2*m) p → Equiv.Perm ((V × ZMod (2*m)) × ZMod p),
      (∀ i a x, (F₁ i a x).1 = σ i x.1) ∧
      (∀ i a b x, (F₂ (i,a,b) x).1 = F₁ i a x.1) ∧
      (∀ i a a' b b', (a,b) ≠ (a',b') → ∀ x, F₂ (i,a,b) x ≠ F₂ (i,a',b') x) ∧
      (∀ i a b x y, (F₂ (i,a,b)).SameCycle x y ↔ (σ i).SameCycle x.1.1 y.1.1) ∧
      ∀ i a b j (x y : Fin ((C₂ i a).length j) × ZMod p) k, 0 < k →
        x.1.val < (C₂ i a).length j-2 → y.1.val < (C₂ i a).length j-2 → x.2 = y.2 →
        ((F₂ (i,a,b))^k) ((C₂ i a).order ⟨j,x.1⟩,x.2) = ((C₂ i a).order ⟨j,y.1⟩,y.2) →
        p ≤ k := by
  let C₁ := fun i => factorCycleCoordinates (σ i) (hFixed i)
  letI : NeZero (2*m) := ⟨by omega⟩
  choose F₁ hProj hDis hOrbit using fun i => exists_even_factor_unwinding (σ i) (C₁ i) m hm
  have hFixed₁ (i : Fin r) (a : UnwindingLabel (2*m)) (v : V × ZMod (2*m)) : F₁ i a v ≠ v := by
    intro h
    exact hFixed i v.1 ((hProj i a v).symm.trans (congrArg Prod.fst h))
  let C₂ := fun i a => factorCycleCoordinates (F₁ i a) (hFixed₁ i a)
  choose F hF hFDis hFOrbit hDist using fun (i : Fin r) (a : UnwindingLabel (2*m)) =>
    exists_factor_unwinding (F₁ i a) (C₂ i a) p hp hp2
  refine ⟨F₁,C₂,fun ⟨i,a,b⟩ => F i a b,hProj,hF,?_,?_,hDist⟩
  · intro i a a' b b' he x hx
    have ha : a = a' := by
      by_contra h
      exact hDis i a a' h x.1 ((hF i a b x).symm.trans ((congrArg Prod.fst hx).trans (hF i a' b' x)))
    subst a'
    exact hFDis i a b b' (fun h => he (Prod.ext rfl h)) x hx
  · intro i a b x y
    exact (hFOrbit i a b x y).trans (hOrbit i a x.1 y.1)

omit [Fintype V] in
/-- At most one of the refined factors of a given original type can
use the same refined arc. The retained base multiplicity therefore
bounds the refined multiplicity at every pair of refined vertices. -/
theorem refined_multiplicity_le {r s p : ℕ} [NeZero s] [NeZero p]
    (M : V → V → ℕ) (σ : Fin r → Equiv.Perm V)
    (P : RefinedFactorIndex r s p → Equiv.Perm ((V × ZMod s) × ZMod p))
    (hBase : ∀ x y, ((univ : Finset (Fin r)).filter (fun i => σ i x = y)).card ≤ M x y)
    (hProj : ∀ i x, (P i x).1.1 = σ i.1 x.1.1)
    (hSect : ∀ i a a' b b', (a,b) ≠ (a',b') → ∀ x, P (i,a,b) x ≠ P (i,a',b') x)
    (x y : (V × ZMod s) × ZMod p) :
    ((univ : Finset (RefinedFactorIndex r s p)).filter (fun j => P j x = y)).card ≤ M x.1.1 y.1.1 := by
  let A := (univ : Finset (RefinedFactorIndex r s p)).filter (fun j => P j x = y)
  let B := (univ : Finset (Fin r)).filter (fun i => σ i x.1.1 = y.1.1)
  refine (card_le_card_of_injOn Prod.fst ?_ ?_).trans (hBase x.1.1 y.1.1)
  · intro j hj
    exact mem_filter.mpr ⟨mem_univ _,(hProj j x).symm.trans (congrArg (fun w => w.1.1) (mem_filter.mp hj).2)⟩
  · rintro ⟨i,a,b⟩ hi ⟨j,c,d⟩ hj he
    change i = j at he
    subst j
    have h : (a,b) = (c,d) := by
      by_contra hn
      exact hSect i a c b d hn x ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
    exact Prod.ext rfl h

end OverfullWork.DirectedRobustExpansion
