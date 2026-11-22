module

public import OverfullWork.EdgeSigningWeights

@[expose] public section


/-! An actual partition of the edge set selected by unordered-edge signs.
Signed row sums equal twice the selected incidences minus the source
incidences. Complementary edges carry the opposite discrepancy.
-/
namespace OverfullWork.SignedEdgeSplit
open SimpleGraph Finset EdgeSigningWeights
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 14000000

def selected (G : SimpleGraph V) (s : Sym2 V → Bool) : SimpleGraph V :=
  G ⊓ SimpleGraph.fromEdgeSet {e | s e=true}

theorem selected_adj (G : SimpleGraph V) (s : Sym2 V → Bool) (x y : V) :
    (selected G s).Adj x y ↔ G.Adj x y ∧ s s(x,y)=true := by
  simp only [selected,inf_adj,fromEdgeSet_adj,Set.mem_setOf_eq]
  constructor
  · exact fun h => ⟨h.1,h.2.1⟩
  · exact fun h => ⟨h.1,h.2,h.1.ne⟩

theorem selected_le (G : SimpleGraph V) (s : Sym2 V → Bool) : selected G s ≤ G := inf_le_left

theorem complementary (G : SimpleGraph V) (s : Sym2 V → Bool) :
    selected G (fun e => !(s e))=G\selected G s := by
  ext x y
  simp only [selected_adj,sdiff_adj,Bool.not_eq_true]
  cases h : s s(x,y) <;> simp [h]

theorem selected_weight (G : SimpleGraph V) (s : Sym2 V → Bool) (S T : Finset V) (e : Sym2 V) :
    weight (selected G s) S T e=if s e then weight G S T e else 0 := by
  unfold weight
  have hAtom : ∀ x y : V,
      (if (selected G s).Adj x y ∧ e=s(x,y) then (1:ℝ) else 0)=
        if s e then (if G.Adj x y ∧ e=s(x,y) then 1 else 0) else 0 := by
    intro x y
    by_cases he : e=s(x,y)
    · subst e
      cases hs : s s(x,y) <;> simp [selected_adj,hs]
    · simp [he]
  simp_rw [hAtom]
  cases hs : s e <;> simp [hs]

def signedValue {E : Type*} [Fintype E] (a : E → ℝ) (s : E → Bool) : ℝ :=
  ∑ e,if s e then a e else -a e

theorem signed_incidence_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Sym2 V → Bool) (S T : Finset V) :
    signedValue (weight G S T) s=
      2*(incidences (selected G s) S T:ℝ)-(incidences G S T:ℝ) := by
  classical
  rw [←sum_weight (selected G s) S T,←sum_weight G S T]
  rw [mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  rw [selected_weight]
  cases hs : s e <;> simp [hs] <;> ring

theorem incidence_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Sym2 V → Bool) (S T : Finset V) :
    incidences (selected G s) S T+incidences (G\selected G s) S T=incidences G S T := by
  classical
  have hValue : signedValue (weight G S T) s+
      signedValue (weight G S T) (fun e => !(s e))=0 := by
    rw [signedValue,signedValue,←sum_add_distrib]
    apply sum_eq_zero
    intro e _
    cases hs : s e <;> simp [hs]
  rw [signed_incidence_identity,signed_incidence_identity,complementary] at hValue
  exact_mod_cast (show (incidences (selected G s) S T:ℝ)+
    (incidences (G\selected G s) S T:ℝ)=(incidences G S T:ℝ) by linarith only [hValue])

end OverfullWork.SignedEdgeSplit
