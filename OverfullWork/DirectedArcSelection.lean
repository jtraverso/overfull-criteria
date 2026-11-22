module

public import OverfullWork.DirectedRobustExpansion
public import OverfullWork.BiasedDegreeCutSelection

@[expose] public section


/-! Exact ordered-arc weights, cut counts and actual biased subdigraphs.
Every coordinate denotes one possible ordered arc, with zero coefficient
on absent arcs. All counting functions avoid decidability parameters. -/
namespace OverfullWork.DirectedArcSelection
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

def selected (D : Digraph V) (s : V × V → Bool) : Digraph V where
  Adj u v := D.Adj u v ∧ s (u,v)=true

theorem selected_le (D : Digraph V) (s : V × V → Bool) : selected D s ≤ D :=
  fun _ _ h => h.1

noncomputable def weight (D : Digraph V) (S T : Finset V) (e : V × V) : ℝ :=
  if e.1 ∈ S ∧ e.2 ∈ T ∧ D.Adj e.1 e.2 then 1 else 0

theorem sum_weight (D : Digraph V) (S T : Finset V) :
    (∑ e : V × V,weight D S T e)=(incidences D S T:ℝ) := by
  rw [Fintype.sum_prod_type,sum_comm,incidences_eq_sum]
  unfold weight
  have hInner : ∀ v : V,
      (∑ u : V,if u ∈ S ∧ v ∈ T ∧ D.Adj u v then (1:ℝ) else 0)=
        if v ∈ T then ∑ u ∈ S,if D.Adj u v then 1 else 0 else 0 := by
    intro v
    by_cases hv : v ∈ T
    · simp only [hv,true_and,ite_true,ite_and]
      rw [←sum_filter]
      simp only [filter_mem_eq_inter,univ_inter]
    · simp only [hv,false_and,and_false,ite_false,sum_const_zero]
  simp_rw [hInner]
  rw [←sum_filter]
  simp only [filter_mem_eq_inter,univ_inter]

theorem incidences_outDegree (D : Digraph V) (v : V) :
    incidences D {v} univ=outDegree D v := by
  simp only [incidences,inNeighbours,card_filter,sum_singleton]
  simp only [outDegree,card_filter]

theorem incidences_le (D : Digraph V) (S T : Finset V) :
    incidences D S T ≤ S.card*T.card := by
  unfold incidences inNeighbours
  calc
    _ ≤ ∑ _v ∈ T,S.card := sum_le_sum fun v _ => card_le_card (filter_subset _ _)
    _ = _ := by simp [Nat.mul_comm]

theorem inDegree_le (D : Digraph V) (v : V) : inDegree D v ≤ Fintype.card V :=
  (card_le_card (filter_subset _ _)).trans_eq (card_univ)

theorem outDegree_le (D : Digraph V) (v : V) : outDegree D v ≤ Fintype.card V :=
  (card_le_card (filter_subset _ _)).trans_eq (card_univ)

theorem sum_squared_weight (D : Digraph V) (S T : Finset V) :
    (∑ e : V × V,(weight D S T e)^2)=(incidences D S T:ℝ) := by
  rw [←sum_weight]
  apply sum_congr rfl
  intro e _
  unfold weight
  split_ifs <;> norm_num

theorem cut_variance_bound (D : Digraph V) (S T : Finset V) :
    (∑ e : V × V,(weight D S T e)^2) ≤ 2*(Fintype.card V:ℝ)^2 := by
  rw [sum_squared_weight]
  have hh := (incidences_le D S T).trans (Nat.mul_le_mul (card_le_univ S) (card_le_univ T))
  have hhR : (incidences D S T:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
    exact_mod_cast (by simpa only [pow_two] using hh : incidences D S T ≤ (Fintype.card V)^2)
  nlinarith only [hhR,sq_nonneg (Fintype.card V:ℝ)]

theorem in_variance_bound (D : Digraph V) (v : V) :
    (∑ e : V × V,(weight D univ {v} e)^2) ≤ (Fintype.card V:ℝ) := by
  rw [sum_squared_weight,incidences_degree]
  exact_mod_cast inDegree_le D v

theorem out_variance_bound (D : Digraph V) (v : V) :
    (∑ e : V × V,(weight D {v} univ e)^2) ≤ (Fintype.card V:ℝ) := by
  rw [sum_squared_weight,incidences_outDegree]
  exact_mod_cast outDegree_le D v

theorem selected_weight (D : Digraph V) (s : V × V → Bool)
    (S T : Finset V) (e : V × V) :
    weight (selected D s) S T e=if s e then weight D S T e else 0 := by
  rcases e with ⟨u,v⟩
  cases hs : s (u,v) <;> simp [weight,selected,hs]

theorem biased_cut_identity (D : Digraph V) (p : ℝ) (s : V × V → Bool)
    (S T : Finset V) :
    BiasedDegreeCutSelection.value p (weight D S T) s=
      (incidences (selected D s) S T:ℝ)-p*(incidences D S T:ℝ) := by
  rw [←sum_weight (selected D s),←sum_weight D,mul_sum,←sum_sub_distrib]
  unfold BiasedDegreeCutSelection.value
  apply sum_congr rfl
  intro e _
  rw [selected_weight]
  cases hs : s e <;> simp [hs] <;> ring

theorem incidence_partition (D H : Digraph V) (hLe : H ≤ D) (S T : Finset V) :
    incidences (D\H) S T+incidences H S T=incidences D S T := by
  letI : DecidableRel (D\H).Adj := fun u v => Classical.propDecidable _
  have hPoint : ∀ u v : V,
      (if (D\H).Adj u v then (1:ℝ) else 0)+(if H.Adj u v then 1 else 0)=
        if D.Adj u v then 1 else 0 := by
    intro u v
    by_cases hH : H.Adj u v
    · have hD := hLe hH
      simp [Digraph.sdiff_adj,hH,hD]
    · by_cases hD : D.Adj u v <;> simp [Digraph.sdiff_adj,hH,hD]
  have hReal : (incidences (D\H) S T:ℝ)+(incidences H S T:ℝ)=(incidences D S T:ℝ) := by
    simp only [incidences_eq_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro v _
    apply sum_congr rfl
    intro u _
    exact hPoint u v
  exact_mod_cast hReal

theorem complementary_cut_error (D H : Digraph V) (hLe : H ≤ D) (p : ℝ)
    (S T : Finset V) :
    (incidences (D\H) S T:ℝ)-(1-p)*(incidences D S T:ℝ)=
      -((incidences H S T:ℝ)-p*(incidences D S T:ℝ)) := by
  have hPay : (incidences (D\H) S T:ℝ)+(incidences H S T:ℝ)=(incidences D S T:ℝ) := by
    exact_mod_cast incidence_partition D H hLe S T
  linarith only [hPay]

theorem exact_partition (D H : Digraph V) (hLe : H ≤ D) :
    H ⊔ (D\H)=D ∧ Disjoint H (D\H) := by
  constructor
  · ext u v
    simp only [Digraph.sup_adj,Digraph.sdiff_adj]
    constructor
    · rintro (hH|hRest)
      · exact hLe hH
      · exact hRest.1
    · intro hD
      by_cases hH : H.Adj u v
      · exact Or.inl hH
      · exact Or.inr ⟨hD,hH⟩
  · rw [disjoint_iff_inf_le]
    intro u v h
    exact False.elim (h.2.2 h.1)

end OverfullWork.DirectedArcSelection
