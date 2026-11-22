module

public import OverfullWork.RobustExpansionFinite
public import OverfullWork.EdgeSigningWeights
public import Mathlib.Combinatorics.Digraph.Basic

@[expose] public section


/-! Finite robust out-expansion on actual Mathlib digraphs.
Counts are independent of decidability instances. In-neighbours from a
source set define the robust out-neighbourhood, as in Gao--Shan §2.3.
No Hamiltonian or spanning-path statement is assumed.
-/
namespace OverfullWork.DirectedRobustExpansion
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def inNeighbours (D : Digraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter fun u => D.Adj u v).card

noncomputable def inDegree (D : Digraph V) (v : V) : ℕ := inNeighbours D univ v

noncomputable def outDegree (D : Digraph V) (v : V) : ℕ :=
  (univ.filter fun w => D.Adj v w).card

noncomputable def incidences (D : Digraph V) (S T : Finset V) : ℕ :=
  ∑ v ∈ T,inNeighbours D S v

noncomputable def neighbourhood (D : Digraph V) (r : ℕ) (S : Finset V) : Finset V :=
  univ.filter fun v => r ≤ inNeighbours D S v

def IsRobustAt (D : Digraph V) (r t : ℕ) : Prop :=
  ∀ S : Finset V,t ≤ S.card → S.card+t ≤ Fintype.card V →
    S.card+r ≤ (neighbourhood D r S).card

def IsOrientationOf (D : Digraph V) (G : SimpleGraph V) : Prop :=
  (∀ u v,D.Adj u v → G.Adj u v) ∧
  (∀ u v,G.Adj u v → D.Adj u v ∨ D.Adj v u) ∧
  ∀ u v,¬(D.Adj u v ∧ D.Adj v u)

theorem incidences_eq_sum (D : Digraph V) (S T : Finset V) :
    (incidences D S T:ℝ)=∑ v ∈ T,∑ u ∈ S,if D.Adj u v then (1:ℝ) else 0 := by
  simp only [incidences,inNeighbours,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]

theorem incidences_degree (D : Digraph V) (v : V) :
    incidences D univ {v}=inDegree D v := by simp only [incidences,sum_singleton,inDegree]

theorem degree_partition (D : Digraph V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hD : IsOrientationOf D G) (v : V) : inDegree D v+outDegree D v=G.degree v := by
  have hPoint : ∀ w : V,
      (if D.Adj w v then (1:ℕ) else 0)+(if D.Adj v w then 1 else 0)=
        if G.Adj v w then 1 else 0 := by
    intro w
    by_cases hG : G.Adj v w
    · rcases hD.2.1 v w hG with hOut|hIn
      · have hNot : ¬D.Adj w v := fun h => hD.2.2 v w ⟨hOut,h⟩
        simp only [if_neg hNot,if_pos hOut,if_pos hG,Nat.zero_add]
      · have hNot : ¬D.Adj v w := fun h => hD.2.2 v w ⟨h,hIn⟩
        simp only [if_neg hNot,if_pos hIn,if_pos hG,Nat.add_zero]
    · have hOut : ¬D.Adj v w := fun h => hG (hD.1 v w h)
      have hIn : ¬D.Adj w v := fun h => hG (hD.1 w v h).symm
      simp only [if_neg hOut,if_neg hIn,if_neg hG,Nat.add_zero]
  have hSum := sum_congr (s₁:=univ) rfl (fun w _ => hPoint w)
  rw [sum_add_distrib,←card_filter] at hSum
  have hN : univ.filter (G.Adj v)=G.neighborFinset v := by
    ext w
    simp only [mem_filter,mem_univ,true_and,mem_neighborFinset]
  simp only [inDegree,outDegree,inNeighbours,card_filter]
  calc
    _ = ∑ w,if G.Adj v w then 1 else 0 := by simpa only [card_filter] using hSum
    _ = G.degree v := by rw [←card_filter,hN,card_neighborFinset_eq_degree]

end OverfullWork.DirectedRobustExpansion
