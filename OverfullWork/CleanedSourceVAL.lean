module

public import OverfullWork.PaperContinuationAboveHalf

@[expose] public section


/-! # The local VAL data supplied by maximum-neighbour cleanup

No criticality is required. The full maximum-neighbour inequality is
kept explicit, since weak degree sums alone do not imply it.
-/
namespace OverfullWork.CleanedSourceVAL
open SimpleGraph Finset PrunedCore MaximumNeighbourCleanup
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

def IsReady (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) : Prop :=
  (∀w∈Y,G.degree w<G.maxDegree) ∧
  ∀w∈Y,∀v,G.Adj w v → G.maxDegree+1≤G.degree w+neighboursIn G (maximumVertices G) v

theorem weak_VAL (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) (h : IsReady G Y) :
    ∀w∈Y,∀v,G.Adj w v → G.maxDegree+2≤G.degree w+G.degree v :=
  degree_sum_of_final_inequality G Y h.1 h.2

theorem active_degree_at_least_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (h : IsReady G Y) (w : V) (hw : w∈Y) (hPos : 0<G.degree w) :
    2≤G.degree w := by
  obtain ⟨v,hAdj⟩:=(G.degree_pos_iff_exists_adj w).mp hPos
  have hVal:=weak_VAL G Y h w hw v hAdj
  have hV:=G.degree_le_maxDegree v
  omega

/-- A degree-two Y vertex already uses the only available nonmaximum
neighbour slot at its neighbour. An additional nonmaximum neighbour is
impossible. This replaces the critical-source guard in the old proof. -/
theorem degree_two_forbids_nonmaximum_common_neighbour (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (h : IsReady G Y) (w x v : V) (hw : w∈Y)
    (hwTwo : G.degree w=2) (hxD : G.degree x<G.maxDegree) (hxw : x≠w)
    (hwv : G.Adj w v) (hxv : G.Adj x v) : False := by
  have hPairNonmax:∀a∈({x,w}:Finset V),G.degree a<G.maxDegree:=by
    intro a ha
    rcases mem_insert.mp ha with he|ha
    · exact he ▸ hxD
    · exact mem_singleton.mp ha ▸ h.1 w hw
  have hCount:=neighbours_set_add_maximum_le G {x,w} hPairNonmax v
  have hPair:2≤neighboursIn G {x,w} v:=by
    rw [RobustExpansion.neighboursIn_eq_filter_card]
    have hEq:({x,w}:Finset V).filter (G.Adj v)={x,w}:=by
      apply filter_eq_self.mpr
      intro a ha
      rcases mem_insert.mp ha with he|ha
      · exact he ▸ hxv.symm
      · exact mem_singleton.mp ha ▸ hwv.symm
    rw [hEq,card_pair hxw]
  have hFinal:=h.2 w hw v hwv
  have hMax:=G.degree_le_maxDegree v
  omega

theorem selected_anchor_degree_at_least_two (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : NormalizedAlmostStoppingRun.Certificate G B K)
    {x y z : V} (h : IsReady G c.setᶜ) (r : ClassTwoMatchingRound.CoreRound G c.set x y z)
    (hx : x∈c.set) (hy : y∈c.setᶜ) : 2≤G.degree x := by
  have hF:r.matching.degree y=1:=by rw [r.complementary_degrees y hy,if_pos (Or.inl rfl)]
  have hLe:=r.matching.degree_le_of_le r.le_original (v:=y)
  have hyPos:0<G.degree y:=by
    simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hF hLe ⊢
    omega
  have hTwo:=active_degree_at_least_two G c.setᶜ h y hy hyPos
  exact hTwo.trans (c.ordered y hy x hx)

end OverfullWork.CleanedSourceVAL
