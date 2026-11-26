module

public import OverfullWork.ChenShanAbsorberCatalogue
public import OverfullWork.ChenShanEmbeddedAbsorber

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

/-- The statement of Chen–Shan's universal tripartite absorber lemma. -/
theorem exists_universal_tripartite_absorber
    (AB : A → B → Prop) (AW : A → W → Prop) (BW : B → W → Prop)
    (U Z : Finset (TripartiteVertex A B W)) (h : ℕ) (m η γ ε : ℝ)
    (hm : 0 < m) (hη : 0 < η) (hγ : 0 < γ)
    (hSizeA : (Fintype.card A : ℝ) = m)
    (hSizeW : γ*m ≤ (Fintype.card W : ℝ))
    (hDegreeA : ∀ a, (1/2+η)*m ≤ ((univ.filter (AB a) : Finset B).card : ℝ))
    (hDegreeB : ∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => AB a b) : Finset A).card : ℝ))
    (hAW : ∀ a, ((univ.filter (fun z => ¬ AW a z) : Finset W).card : ℝ) ≤ ε*m)
    (hBW : ∀ b, ((univ.filter (fun z => ¬ BW b z) : Finset W).card : ℝ) ≤ ε*m)
    (hWA : ∀ z, ((univ.filter (fun a => ¬ AW a z) : Finset A).card : ℝ) ≤ ε*m)
    (hWB : ∀ z, ((univ.filter (fun b => ¬ BW b z) : Finset B).card : ℝ) ≤ ε*m)
    (hε : 0 ≤ ε) (hEps : ε ≤ η/32) (hEpsCycles : (h : ℝ)*ε ≤ γ/16)
    (hUZ : U ⊆ Z) (hU : U.card ≤ h) (hZ : (Z.card : ℝ) ≤ min η γ*m/16)
    (hRoom : ((4*(h*h)*2^(h*h) : ℕ) : ℝ) ≤ min η γ*m/16) :
    ∃ (Q : Finset (TripartiteVertex A B W))
      (E : A → B → Prop) (l : A → W → Prop) (r : B → W → Prop),
      Disjoint Q Z ∧
      tripartiteArcs E l r ⊆ tripartiteArcs AB AW BW ∧
      (∀ e ∈ tripartiteArcs E l r, FootprintEdge Q U e.1 e.2) ∧
      (tripartiteArcs E l r).card + Q.card ≤ 4*(h*h)*2^(h*h) ∧
      Nonempty (TripartiteTriangleDecomposition E l r) ∧
      ∀ (L : A → B → Prop) (lL : A → W → Prop) (rL : B → W → Prop),
        tripartiteArcs L lL rL ⊆ tripartiteArcs AB AW BW →
        tripartiteArcs L lL rL ⊆ U ×ˢ U → TripartiteLocallyBalanced L lL rL →
        Nonempty (TripartiteTriangleDecomposition
          (fun a b => E a b ∨ L a b) (fun a w => l a w ∨ lL a w)
          (fun b w => r b w ∨ rL b w)) := by
  sorry

end OverfullWork.ChenShan
