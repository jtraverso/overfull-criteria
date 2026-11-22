module

public import OverfullWork.CriticalSpectrum

@[expose] public section


/-! # Colouring-free CCJS restrictions for every degree pair

The anchor need not have minimum degree. Its missing-edge colouring and
maximum-degree neighbour are obtained from criticality. These are joint
degree restrictions, not a classification of all critical obstructions.
-/
namespace OverfullWork.Gate8J2C
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem critical_exists_maximum_edge_from (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀v,0<G.degree v) (a : V) :
    ∃ b,G.Adj a b ∧ G.degree b=G.maxDegree := by
  obtain ⟨z,haz⟩ := (G.degree_pos_iff_exists_adj a).mp (hactive a)
  obtain ⟨b,hab,_,hb⟩ := Overfull.exists_maxdeg_nbr hcrit haz
  exact ⟨b,hab,hb⟩

/-- CCJS's forbidden interval holds at every active anchor. -/
theorem critical_degree_dichotomy (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀v,0<G.degree v)
    {a v : V} (hva : v≠a) (hlo : G.degree v+G.degree a≤G.maxDegree) :
    G.degree v+G.maxDegree+5<Fintype.card V+2*G.degree a := by
  obtain ⟨b,hab,hb⟩ := critical_exists_maximum_edge_from G hcrit hactive a
  obtain ⟨c,hcm⟩ := Overfull.exists_colMinus_of_colorable hab
    (hcrit.2.2 s(a,b) ((mem_edgeSet G).mpr hab))
  have ha2 := Overfull.two_le_degree hcrit hab.symm
  by_contra hn
  exact Overfull.degree_dichotomy hcrit hcm hb ha2 hva (by omega) hlo

/-- Low degree pairs must satisfy the CCJS inequalities in both
orientations, even when neither endpoint has minimum degree. -/
theorem critical_low_degree_pair_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀v,0<G.degree v)
    {a v : V} (hne : a≠v) (hlo : G.degree a+G.degree v≤G.maxDegree) :
    G.degree v+G.maxDegree+5<Fintype.card V+2*G.degree a ∧
    G.degree a+G.maxDegree+5<Fintype.card V+2*G.degree v := by
  exact ⟨critical_degree_dichotomy G hcrit hactive hne.symm (by omega),
    critical_degree_dichotomy G hcrit hactive hne hlo⟩

theorem critical_degree_pair_disjunction (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀v,0<G.degree v)
    {a v : V} (hne : a≠v) :
    G.maxDegree<G.degree a+G.degree v ∨
      (G.degree v+G.maxDegree+5<Fintype.card V+2*G.degree a ∧
       G.degree a+G.maxDegree+5<Fintype.card V+2*G.degree v) := by
  by_cases hlo : G.degree a+G.degree v≤G.maxDegree
  · exact Or.inr (critical_low_degree_pair_bounds G hcrit hactive hne hlo)
  · exact Or.inl (by omega)

end OverfullWork.Gate8J2C
