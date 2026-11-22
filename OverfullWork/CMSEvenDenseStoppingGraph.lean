module

public import OverfullWork.CMSSimpleStoppingProfiles

@[expose] public section


/-! The even-order simple endpoint of CMS Case 1.1. The local
triangle condition follows from the weak VAL cleaning of degree-one
and degree-two vertices. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion OddCutDeficit
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- If the least-degree vertex has only one neighbour apart from the
second least-degree vertex, weak VAL forces degree two at the first
and maximum degree at every other vertex. -/
theorem even_simple_stop_local_of_cleaned_low_degrees (G : SimpleGraph V) [DecidableRel G.Adj]
    (hD : 4 ≤ G.maxDegree) (hPos : ∀ v,0 < G.degree v)
    (hWeak : ∀ u v,G.degree u ≤ 2 → G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v)
    (p q : V) (hpq : p ≠ q) (hSecond : ∀ v,v ≠ p → G.degree q ≤ G.degree v)
    (hFew : ((G.neighborFinset p).erase q).card ≤ 1) :
    ∀ v,v ≠ p → v ≠ q → G.maxDegree ≤ cutEdges G {p,q,v} := by
  have hDegN : (G.neighborFinset p).card = G.degree p := card_neighborFinset_eq_degree ..
  have hSmall : G.degree p ≤ 2 := by
    by_cases hq : q ∈ G.neighborFinset p
    · have hh := card_erase_add_one hq
      omega
    · rw [erase_eq_of_notMem hq] at hFew
      omega
  have hTwo : G.degree p = 2 := by
    obtain ⟨v,hpv⟩ := (G.degree_pos_iff_exists_adj p).mp (hPos p)
    have h := hWeak p v hSmall hpv
    have hh := G.degree_le_maxDegree v
    omega
  have hq : q ∈ G.neighborFinset p := by
    by_contra h
    rw [erase_eq_of_notMem h] at hFew
    omega
  have hMaxQ : G.degree q = G.maxDegree := by
    have h := hWeak p q hSmall ((mem_neighborFinset _ _ _).mp hq)
    have hh := G.degree_le_maxDegree q
    omega
  intro v hvp hvq
  have hMaxV : G.degree v = G.maxDegree := by
    have h := hSecond v hvp
    have hh := G.degree_le_maxDegree v
    omega
  let M := MultiGraph.ofSimpleGraph G
  have hSimple (s : Sym2 V) : M.mult s ≤ 1 := by
    change (if s ∈ G.edgeSet then 1 else 0) ≤ 1
    split_ifs <;> omega
  rw [cutEdges_eq_multigraph]
  change G.maxDegree ≤ M.cutSize {p,q,v}
  have hh := CriticalCentreTriples.triple_cut_identity M p q v hpq hvp.symm hvq.symm
  have hDegree (w : V) : M.degree w = G.degree w := MultiGraph.degree_ofSimpleGraph G w
  rw [hDegree,hDegree,hDegree] at hh
  have h₁ := hSimple s(p,q)
  have h₂ := hSimple s(p,v)
  have h₃ := hSimple s(q,v)
  omega

set_option maxHeartbeats 2400000 in
theorem cms_colourable_of_even_dense_stop_with_two_exceptions (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ n → Even n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ v,0 < G.degree v) →
          (∀ u v,G.degree u ≤ 2 → G.Adj u v → d+2 ≤ G.degree u+G.degree v) →
          (∃ x y : V,∀ v,v ≠ x → v ≠ y → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν τ → G.EdgeColorable d := by
  obtain ⟨τ,hτ,hUse⟩ := cms_colourable_of_even_simple_with_two_exceptions α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse ν hν hντ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N₀,hUse⟩ := hUse η hη hηMax
  obtain ⟨Q,hQ⟩ := exists_nat_ge (4/α)
  refine ⟨max N₀ Q,?_⟩
  intro V _ _ G _ n d hn hEven hDens hPos hWeak hDef hNo hRob
  have hLarge : (Q:ℝ) ≤ (n:ℝ) := by exact_mod_cast (le_max_right _ _).trans hn
  have hDegree : 4 ≤ G.maxDegree := by
    have hx := (div_le_iff₀ hα).mp (hQ.trans hLarge)
    exact_mod_cast (show (4:ℝ) ≤ (G.maxDegree:ℝ) by linarith only [hx,hDens])
  refine hUse G ((le_max_left _ _).trans hn) hEven hDens hDef ?_ hNo hRob
  intro p q hpq _ hSecond hFew
  exact Or.inr (even_simple_stop_local_of_cleaned_low_degrees G hDegree hPos hWeak p q hpq hSecond hFew)

set_option maxHeartbeats 2400000 in
theorem cms_colourable_of_even_dense_simple_stop (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ n → Even n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ v,0 < G.degree v) →
          (∀ u v,G.degree u ≤ 2 → G.Adj u v → d+2 ≤ G.degree u+G.degree v) →
          (∃ z : V,∀ v,v ≠ z → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν τ → G.EdgeColorable d := by
  obtain ⟨τ,hτ,hUse⟩ := cms_colourable_of_even_dense_stop_with_two_exceptions.{u} α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse ν hν hντ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hUse⟩ := hUse η hη hηMax
  refine ⟨N,?_⟩
  intro V _ _ G _ n d hn hEven hDens hPos hWeak hDef hNo hRob
  obtain ⟨z,hz⟩ := hDef
  exact hUse G hn hEven hDens hPos hWeak ⟨z,z,fun v hv _ => hz v hv⟩ hNo hRob

end OverfullWork.CanonicalRegularization
