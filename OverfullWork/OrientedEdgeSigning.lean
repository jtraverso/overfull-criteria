module

public import OverfullWork.DirectedRobustExpansion
public import OverfullWork.DegreeCutSigning

@[expose] public section


/-! Orient unordered edges by actual Boolean signs. Antisymmetric cut
coefficients have variance bounded by the undirected incidence weights.
The construction supplies all arcs; no orientation witness is assumed. -/
namespace OverfullWork.OrientedEdgeSigning
open SimpleGraph Finset SignedEdgeSplit
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

def oriented (G : SimpleGraph V) (code : V → ℕ) (s : Sym2 V → Bool) : Digraph V where
  Adj u v := G.Adj u v ∧ (s s(u,v)=true ↔ code u < code v)

theorem isOrientationOf (G : SimpleGraph V) (code : V → ℕ)
    (hCode : Function.Injective code) (s : Sym2 V → Bool) :
    DirectedRobustExpansion.IsOrientationOf (oriented G code s) G := by
  refine ⟨fun _ _ h => h.1,?_,?_⟩
  · intro u v huv
    have hne : code u ≠ code v := fun h => huv.ne (hCode h)
    change (G.Adj u v ∧ _) ∨ (G.Adj v u ∧ _)
    rw [Sym2.eq_swap]
    cases hs : s s(v,u) <;> simp only [hs,Bool.false_eq_true,false_iff,true_iff]
    · by_cases h : code u < code v
      · exact Or.inr ⟨huv.symm,by omega⟩
      · exact Or.inl ⟨huv,h⟩
    · by_cases h : code u < code v
      · exact Or.inl ⟨huv,h⟩
      · exact Or.inr ⟨huv.symm,by omega⟩
  · intro u v ⟨h₁,h₂⟩
    change G.Adj u v ∧ _ at h₁
    change G.Adj v u ∧ _ at h₂
    have hne : code u ≠ code v := fun h => h₁.1.ne (hCode h)
    have hs : s s(u,v)=s s(v,u) := congrArg s Sym2.eq_swap
    rcases h₁ with ⟨_,h₁⟩
    rcases h₂ with ⟨_,h₂⟩
    rw [←hs] at h₂
    cases h : s s(u,v) <;> simp only [h,Bool.false_eq_true,false_iff,true_iff] at h₁ h₂ <;> omega

noncomputable def cutWeight (G : SimpleGraph V) (code : V → ℕ)
    (S T : Finset V) (e : Sym2 V) : ℝ :=
  ∑ x ∈ T,∑ y ∈ S,if G.Adj x y ∧ e=s(x,y) then
    (if code y < code x then 1 else -1) else 0

theorem abs_cutWeight_le (G : SimpleGraph V) (code : V → ℕ)
    (S T : Finset V) (e : Sym2 V) :
    |cutWeight G code S T e| ≤ EdgeSigningWeights.weight G S T e := by
  unfold cutWeight EdgeSigningWeights.weight
  calc
    _ ≤ ∑ x ∈ T,|∑ y ∈ S,if G.Adj x y ∧ e=s(x,y) then
        (if code y < code x then (1:ℝ) else -1) else 0| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro x _
      calc
        _ ≤ ∑ y ∈ S,|if G.Adj x y ∧ e=s(x,y) then
            (if code y < code x then (1:ℝ) else -1) else 0| := abs_sum_le_sum_abs _ _
        _ = _ := by apply sum_congr rfl;intro y _;split_ifs <;> norm_num

theorem squared_cutWeight_le (G : SimpleGraph V) (code : V → ℕ)
    (S T : Finset V) (e : Sym2 V) :
    (cutWeight G code S T e)^2 ≤ (EdgeSigningWeights.weight G S T e)^2 := by
  have h := abs_cutWeight_le G code S T e
  have hNonneg := EdgeSigningWeights.weight_nonneg G S T e
  nlinarith only [sq_abs (cutWeight G code S T e),sq_nonneg
    (EdgeSigningWeights.weight G S T e-|cutWeight G code S T e|),
    mul_nonneg (abs_nonneg (cutWeight G code S T e)) (sub_nonneg.mpr h)]

theorem cut_variance_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (code : V → ℕ) (S T : Finset V) :
    (∑ e : Sym2 V,(cutWeight G code S T e)^2) ≤ 2*(Fintype.card V:ℝ)^2 :=
  (sum_le_sum fun e _ => squared_cutWeight_le G code S T e).trans
    (EdgeSigningWeights.cut_squared_weight_bound G S T)

theorem degree_variance_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (code : V → ℕ) (v : V) :
    (∑ e : Sym2 V,(cutWeight G code univ {v} e)^2) ≤ (Fintype.card V:ℝ) :=
  (sum_le_sum fun e _ => squared_cutWeight_le G code univ {v} e).trans
    (EdgeSigningWeights.degree_squared_weight_bound G v)

theorem signed_cut_identity (G : SimpleGraph V)
    (code : V → ℕ) (hCode : Function.Injective code) (s : Sym2 V → Bool)
    (S T : Finset V) :
    signedValue (cutWeight G code S T) s =
      2*(DirectedRobustExpansion.incidences (oriented G code s) S T:ℝ)-
        (EdgeSigningWeights.incidences G S T:ℝ) := by
  have hAtom : ∀ x y : V,
      (∑ e : Sym2 V,if s e then
          (if G.Adj x y ∧ e=s(x,y) then (if code y < code x then (1:ℝ) else -1) else 0)
        else -(if G.Adj x y ∧ e=s(x,y) then (if code y < code x then 1 else -1) else 0)) =
      2*(if (oriented G code s).Adj y x then 1 else 0)-(if G.Adj x y then 1 else 0) := by
    intro x y
    by_cases hxy : G.Adj x y
    · have hne : code x ≠ code y := fun h => hxy.ne (hCode h)
      rw [sum_eq_single s(x,y)]
      · simp only [oriented]
        simp only [Sym2.eq_swap (a:=y) (b:=x)]
        cases hs : s s(x,y) <;> by_cases hlt : code y < code x <;>
          simp [oriented,hxy,hxy.symm,hs,hlt] <;> norm_num
      · intro e _ he
        simp [he]
      · simp
    · have hyx : ¬G.Adj y x := fun h => hxy h.symm
      simp [hxy,hyx,oriented]
  unfold signedValue cutWeight
  have hSwap : ∀ e : Sym2 V,
      (if s e then ∑ x ∈ T,∑ y ∈ S,if G.Adj x y ∧ e=s(x,y) then
          (if code y < code x then (1:ℝ) else -1) else 0
        else -(∑ x ∈ T,∑ y ∈ S,if G.Adj x y ∧ e=s(x,y) then
          (if code y < code x then (1:ℝ) else -1) else 0)) =
      ∑ x ∈ T,∑ y ∈ S,if s e then
          (if G.Adj x y ∧ e=s(x,y) then (if code y < code x then (1:ℝ) else -1) else 0)
        else -(if G.Adj x y ∧ e=s(x,y) then (if code y < code x then 1 else -1) else 0) := by
    intro e
    cases hs : s e <;> simp [hs,sum_neg_distrib]
  simp_rw [hSwap]
  rw [sum_comm]
  simp_rw [sum_comm (s:=univ) (t:=S),hAtom,sum_sub_distrib,←mul_sum]
  rw [DirectedRobustExpansion.incidences_eq_sum,EdgeSigningWeights.incidences_eq_sum]
  simp only [RobustExpansion.neighboursIn_eq_filter_card,card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

end OverfullWork.OrientedEdgeSigning
