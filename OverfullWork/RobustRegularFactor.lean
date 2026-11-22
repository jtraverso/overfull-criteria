module

public import OverfullWork.DirectedDemandHall

@[expose] public section


/-! Exact regular completion of a sparse robust subdigraph in a
disjoint reserve, following Kühn–Osthus, Applications Lemma 3.4. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

theorem exists_subdigraph_of_robust_degree_demands (D : Digraph V) (r t L U : ℕ)
    (p q : V → ℕ) (hR : IsRobustAt D r t) (hLU : L ≤ U) (hTwo : U ≤ 2*L)
    (hGap : 2*(U-L)*Fintype.card V ≤ L*r)
    (hSquare : 2*U*Fintype.card V ≤ r*r)
    (hIn : ∀ v, t+U ≤ inDegree D v) (hOut : ∀ v, 2*t+U ≤ outDegree D v)
    (hp : ∀ v, L ≤ p v ∧ p v ≤ U) (hq : ∀ v, L ≤ q v ∧ q v ≤ U)
    (hBalance : (∑ v,p v) = ∑ v,q v) :
    ∃ H : Digraph V, H ≤ D ∧ (∀ v, outDegree H v = p v) ∧ (∀ v, inDegree H v = q v) :=
  DirectedDemandHall.exists_subdigraph_of_capacity_cuts D p q hBalance
    (degree_demand_cut_bound D r t L U p q hR hLU hTwo hGap hSquare hIn hOut hp hq hBalance)

private theorem degree_totals (D : Digraph V) :
    (∑ v, outDegree D v) = ∑ v, inDegree D v := by
  simp only [outDegree,inDegree,inNeighbours,card_filter]
  exact sum_comm

theorem robust_mono {A H : Digraph V} (h : A ≤ H) {r t : ℕ}
    (hA : IsRobustAt A r t) : IsRobustAt H r t := by
  intro S hSt hSn
  apply (hA S hSt hSn).trans
  apply card_le_card
  intro v hv
  refine mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2.trans ?_⟩
  apply card_le_card
  intro u hu
  exact mem_filter.mpr ⟨(mem_filter.mp hu).1,h (mem_filter.mp hu).2⟩

theorem degrees_sup_of_disjoint (A C : Digraph V)
    (hDis : ∀ v w, ¬(A.Adj v w ∧ C.Adj v w)) (v : V) :
    outDegree (A ⊔ C) v = outDegree A v + outDegree C v ∧
      inDegree (A ⊔ C) v = inDegree A v + inDegree C v := by
  have hO : outDegree (A ⊔ C) v = outDegree A v + outDegree C v := by
    simp only [outDegree,card_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro w _
    by_cases ha : A.Adj v w
    · have hc : ¬ C.Adj v w := fun h => hDis v w ⟨ha,h⟩
      simp [Digraph.sup_adj,ha,hc]
    · simp [Digraph.sup_adj,ha]
  have hI : inDegree (A ⊔ C) v = inDegree A v + inDegree C v := by
    simp only [inDegree,inNeighbours,card_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro w _
    by_cases ha : A.Adj w v
    · have hc : ¬ C.Adj w v := fun h => hDis w v ⟨ha,h⟩
      simp [Digraph.sup_adj,ha,hc]
    · simp [Digraph.sup_adj,ha]
  exact ⟨hO,hI⟩

/-- Top up a sparse robust seed from an arc-disjoint robust reserve.
The integer bounds are the quantitative inputs to the degree-demand lemma. -/
theorem exists_robust_regular_completion (A B : Digraph V) (k rA rB t L : ℕ)
    (hA : IsRobustAt A rA t) (hB : IsRobustAt B rB t)
    (hDis : ∀ v w, ¬(A.Adj v w ∧ B.Adj v w))
    (hL : L ≤ k) (hTwo : k ≤ 2*L)
    (hGap : 2*(k-L)*Fintype.card V ≤ L*rB)
    (hSquare : 2*k*Fintype.card V ≤ rB*rB)
    (hIn : ∀ v, t+k ≤ inDegree B v) (hOut : ∀ v, 2*t+k ≤ outDegree B v)
    (hSmall : ∀ v, inDegree A v ≤ k-L ∧ outDegree A v ≤ k-L) :
    ∃ H : Digraph V, A ≤ H ∧ H ≤ A ⊔ B ∧ IsRobustAt H rA t ∧
      ∀ v, outDegree H v = k ∧ inDegree H v = k := by
  let p := fun v => k - outDegree A v
  let q := fun v => k - inDegree A v
  have hp (v : V) : L ≤ p v ∧ p v ≤ k := by
    have h := (hSmall v).2
    dsimp [p]
    omega
  have hq (v : V) : L ≤ q v ∧ q v ≤ k := by
    have h := (hSmall v).1
    dsimp [q]
    omega
  have hP : (∑ v,p v) + (∑ v,outDegree A v) = ∑ _ : V,k := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun v _ => Nat.sub_add_cancel ((hSmall v).2.trans (Nat.sub_le _ _))
  have hQ : (∑ v,q v) + (∑ v,inDegree A v) = ∑ _ : V,k := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun v _ => Nat.sub_add_cancel ((hSmall v).1.trans (Nat.sub_le _ _))
  have hBal : (∑ v,p v) = ∑ v,q v := by
    rw [degree_totals A] at hP
    omega
  obtain ⟨C,hCB,hCO,hCI⟩ := exists_subdigraph_of_robust_degree_demands B rB t L k p q hB
    hL hTwo hGap hSquare hIn hOut hp hq hBal
  refine ⟨A ⊔ C,le_sup_left,sup_le_sup_left hCB A,robust_mono le_sup_left hA,?_⟩
  intro v
  obtain ⟨hO,hI⟩ := degrees_sup_of_disjoint A C (fun v w h => hDis v w ⟨h.1,hCB h.2⟩) v
  rw [hO,hI,hCO,hCI]
  change outDegree A v + (k - outDegree A v) = k ∧
    inDegree A v + (k - inDegree A v) = k
  have := hSmall v
  omega

end OverfullWork.DirectedRobustExpansion
