module

public import OverfullWork.RobustExpansionFinite

@[expose] public section


/-! Exact edge-coordinate weights for degree and directed cut counts.
An unordered edge contributes at most twice to a directed cut, and at
most once to a degree row. Nonedges and loops contribute zero.
-/
namespace OverfullWork.EdgeSigningWeights
open SimpleGraph Finset PrunedCore RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

noncomputable def incidences (G : SimpleGraph V) (S T : Finset V) : ℕ := by
  classical
  exact ∑ x ∈ T,neighboursIn G S x

theorem incidences_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    incidences G S T=∑ x ∈ T,neighboursIn G S x := by
  unfold incidences
  apply sum_congr rfl
  intro x _
  simp only [neighboursIn_eq_filter_card]
  congr 1
  ext y
  simp only [mem_filter]

noncomputable def weight (G : SimpleGraph V) (S T : Finset V) (e : Sym2 V) : ℝ :=
  ∑ x ∈ T,∑ y ∈ S,if G.Adj x y ∧ e=s(x,y) then 1 else 0

theorem weight_pair (G : SimpleGraph V) (S T : Finset V) (a b : V) :
    weight G S T s(a,b)=if G.Adj a b then
      (if a ∈ T ∧ b ∈ S then 1 else 0)+(if b ∈ T ∧ a ∈ S then 1 else 0) else 0 := by
  by_cases hab : G.Adj a b
  · have hne : a ≠ b := hab.ne
    have hAtom : ∀ x y : V,
        (if G.Adj x y ∧ s(a,b)=s(x,y) then (1:ℝ) else 0)=
          (if x=a ∧ y=b then 1 else 0)+(if x=b ∧ y=a then 1 else 0) := by
      intro x y
      by_cases hxa : x=a <;> by_cases hxb : x=b <;>
        by_cases hya : y=a <;> by_cases hyb : y=b <;>
        simp_all [Sym2.eq_iff,G.adj_comm] <;> grind
    unfold weight
    simp_rw [hAtom,sum_add_distrib]
    have hDelta : ∀ c d : V,
        (∑ x ∈ T,∑ y ∈ S,if x=c ∧ y=d then (1:ℝ) else 0)=
          if c ∈ T ∧ d ∈ S then 1 else 0 := by
      intro c d
      simp only [ite_and,sum_ite_irrel,sum_const_zero,sum_ite_eq']
    rw [hDelta,hDelta,if_pos hab]
  · have hAtom : ∀ x y : V,¬(G.Adj x y ∧ s(a,b)=s(x,y)) := by
      intro x y ⟨hxy,he⟩
      rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩|⟨hb,ha⟩
      · exact hab (by simpa only [ha,hb] using hxy)
      · exact hab (by simpa only [ha,hb] using hxy.symm)
    unfold weight
    simp_rw [if_neg (hAtom _ _)]
    simp only [sum_const_zero,if_neg hab]

theorem weight_nonneg (G : SimpleGraph V) (S T : Finset V) (e : Sym2 V) :
    0 ≤ weight G S T e := by
  unfold weight
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem weight_le_two (G : SimpleGraph V) (S T : Finset V) (e : Sym2 V) :
    weight G S T e ≤ 2 := by
  induction e using Sym2.inductionOn with
  | hf a b => rw [weight_pair];split_ifs <;> norm_num

theorem degree_weight_le_one (G : SimpleGraph V) (v : V) (e : Sym2 V) :
    weight G univ {v} e ≤ 1 := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [weight_pair]
    by_cases hab : G.Adj a b
    · have hne := hab.ne
      by_cases ha : a=v <;> by_cases hb : b=v <;> simp_all
    · simp [hab]

theorem sum_weight (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    (∑ e : Sym2 V,weight G S T e)=(incidences G S T:ℝ) := by
  unfold weight
  rw [sum_comm]
  calc
    _ = ∑ x ∈ T,∑ y ∈ S,(if G.Adj x y then (1:ℝ) else 0) := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      by_cases hxy : G.Adj x y <;> simp [hxy]
    _ = _ := by
      rw [incidences_eq_sum]
      simp only [Nat.cast_sum,neighboursIn_eq_filter_card,card_filter,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem incidences_le (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    incidences G S T ≤ S.card*T.card := by
  rw [incidences_eq_sum]
  calc
    _ ≤ ∑ _x ∈ T,S.card := sum_le_sum (fun x _ => neighboursIn_le_card G S x)
    _ = _ := by simp [Nat.mul_comm]

theorem incidences_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    incidences G univ {v}=G.degree v := by
  rw [incidences_eq_sum]
  simp only [sum_singleton,neighboursIn_eq_filter_card]
  have hN : univ.filter (G.Adj v)=G.neighborFinset v := by
    ext w
    simp only [mem_filter,mem_univ,true_and,mem_neighborFinset]
  rw [hN,card_neighborFinset_eq_degree]

theorem cut_squared_weight_bound (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    (∑ e : Sym2 V,(weight G S T e)^2) ≤ 2*(Fintype.card V:ℝ)^2 := by
  have hPoint : ∀ e : Sym2 V,(weight G S T e)^2 ≤ 2*weight G S T e := by
    intro e
    nlinarith only [weight_nonneg G S T e,weight_le_two G S T e]
  have hSum := sum_le_sum (s:=univ) (fun e _ => hPoint e)
  rw [←mul_sum,sum_weight] at hSum
  have hI : incidences G S T ≤ Fintype.card V*Fintype.card V :=
    (incidences_le G S T).trans (Nat.mul_le_mul (card_le_univ _) (card_le_univ _))
  have hIR : (incidences G S T:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
    exact_mod_cast (by simpa only [pow_two] using hI : incidences G S T ≤ Fintype.card V^2)
  linarith only [hSum,hIR]

theorem degree_squared_weight_bound (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (∑ e : Sym2 V,(weight G univ {v} e)^2) ≤ (Fintype.card V:ℝ) := by
  have hPoint : ∀ e : Sym2 V,(weight G univ {v} e)^2 ≤ weight G univ {v} e := by
    intro e
    nlinarith only [weight_nonneg G univ {v} e,degree_weight_le_one G v e]
  have hSum := sum_le_sum (s:=univ) (fun e _ => hPoint e)
  rw [sum_weight,incidences_degree] at hSum
  have hDegree : (G.degree v:ℝ) ≤ Fintype.card V := by exact_mod_cast (G.degree_lt_card_verts v).le
  exact hSum.trans hDegree

end OverfullWork.EdgeSigningWeights
