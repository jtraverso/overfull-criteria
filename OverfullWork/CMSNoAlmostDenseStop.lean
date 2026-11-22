module

public import OverfullWork.CMSEvenDenseStoppingGraph
public import OverfullWork.CMSOddDenseStoppingGraph

@[expose] public section


/-! Stage II's no-almost-overfull branch. Case 1.1 and the odd
Case 1.2 endpoints have at most one exceptional old degree. The
even Case 1.2 endpoint may have two. The final cleanup supplies
the local degree condition in both cases. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion
open scoped Classical
universe u

theorem cms_colourable_of_cleaned_dense_stop (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ,0 < τ ∧ ∀ ν : ℝ,0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ v,0 < G.degree v) →
          (∀ u v,G.degree u ≤ 2 → G.Adj u v → d+2 ≤ G.degree u+G.degree v) →
          ((∃ z : V,∀ v,v ≠ z → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) ∨
            (Even n ∧ ∃ x y : V,∀ v,v ≠ x → v ≠ y → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ))) →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν τ → G.EdgeColorable d := by
  obtain ⟨τ₁,hτ₁,hEven⟩ := cms_colourable_of_even_dense_stop_with_two_exceptions.{u} α hα hα₁
  obtain ⟨τ₂,hτ₂,hOdd⟩ := cms_colourable_of_odd_dense_simple_stop.{u} α hα hα₁
  let τ := min τ₁ τ₂
  have ht₁ : τ ≤ τ₁ := min_le_left _ _
  have ht₂ : τ ≤ τ₂ := min_le_right _ _
  refine ⟨τ,by dsimp only [τ]; positivity,?_⟩
  intro ν hν hντ
  obtain ⟨η₁,hη₁,hEven⟩ := hEven ν hν (hντ.trans ht₁)
  obtain ⟨η₂,hη₂,hOdd⟩ := hOdd ν hν (hντ.trans ht₂)
  let ηMax := min η₁ η₂
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  obtain ⟨N₁,hEven⟩ := hEven η hη (hηMax.trans (min_le_left _ _))
  obtain ⟨N₂,hOdd⟩ := hOdd η hη (hηMax.trans (min_le_right _ _))
  refine ⟨max N₁ N₂,?_⟩
  intro V _ _ G _ n d hn hDensity hPos hWeak hProfiles hNo hRob
  have hLarger (σ : ℝ) (hσ : τ ≤ σ) : IsRealRobust G ν σ := by
    intro S hL hU
    have hN : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    apply hRob S
    · exact (mul_le_mul_of_nonneg_right hσ hN).trans hL
    · exact hU.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left hσ 1) hN)
  rcases hProfiles with ⟨z,hz⟩ | ⟨he,hPair⟩
  · by_cases he : Even n
    · exact hEven G ((le_max_left _ _).trans hn) he hDensity hPos hWeak
        ⟨z,z,fun v hv _ => hz v hv⟩ hNo (hLarger τ₁ ht₁)
    · exact hOdd G ((le_max_right _ _).trans hn) (Nat.not_even_iff_odd.mp he)
        hDensity hPos hWeak ⟨z,hz⟩ hNo (hLarger τ₂ ht₂)
  · exact hEven G ((le_max_left _ _).trans hn) he hDensity hPos hWeak hPair hNo (hLarger τ₁ ht₁)

theorem cms_colourable_of_no_almost_dense_stop (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ n → α*(n:ℝ) ≤ (d:ℝ) →
          ((∀ v,0 < G.degree v) ∧
            (∀ u v,G.degree u ≤ 2 → G.Adj u v → d+2 ≤ G.degree u+G.degree v) ∧
            (∃ z : V,∀ v,v ≠ z → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ))) ∨
          (Even n ∧ (∀ v,3 ≤ G.degree v) ∧
            ∃ x y : V,∀ v,v ≠ x → v ≠ y → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν τ → G.EdgeColorable d := by
  obtain ⟨τ,hτ,hUse⟩ := cms_colourable_of_cleaned_dense_stop.{u} α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse ν hν hντ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hUse⟩ := hUse η hη hηMax
  refine ⟨N,?_⟩
  intro V _ _ G _ n d hn hDensity hStop hNo hRob
  rcases hStop with ⟨hPos,hWeak,hOrd⟩ | ⟨he,hMin,hOrd⟩
  · exact hUse G hn hDensity hPos hWeak (Or.inl hOrd) hNo hRob
  · exact hUse G hn hDensity (fun v => Nat.pos_of_ne_zero (by have h := hMin v; omega))
      (fun u v hLow _ => by have h := hMin u; omega) (Or.inr ⟨he,hOrd⟩) hNo hRob

end OverfullWork.CanonicalRegularization
