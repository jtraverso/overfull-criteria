module

public import OverfullWork.GoodRouteRuns

@[expose] public section


/-! # Crossing copy counts and a matching cover

Count cut copies with their multiplicity. If every crossing edge meets
E, the cut is bounded by the total degree on E; for a matching by |E|.
-/
namespace SimpleGraph.MultiGraph
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

theorem cutSize_le_edgeCount (M : MultiGraph V) (A : Finset V) : M.cutSize A ≤ M.edgeCount := by
  have hA := M.sum_degree_eq_internal_add_cut A
  have hB := M.sum_degree_eq_internal_add_cut Aᶜ
  rw [M.cutSize_compl] at hB
  have hTotal : (∑ v ∈ A, M.degree v)+(∑ v ∈ Aᶜ, M.degree v)=2*M.edgeCount := by
    rw [sum_add_sum_compl,M.sum_degrees_eq_twice_edgeCount]
  omega

theorem cutSize_le_cover_degrees (M : MultiGraph V) (A E : Finset V)
    (hCover : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → 0 < M.mult s(x,y) → x ∈ E ∨ y ∈ E) :
    M.cutSize A ≤ ∑ v ∈ E, M.degree v := by
  have hEq : M.cutSize A=(M.incidentOn E).cutSize A := by
    unfold cutSize
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro y hy
    change M.mult s(x,y)=(if ∃ v ∈ E, v ∈ s(x,y) then M.mult s(x,y) else 0)
    by_cases hp : 0 < M.mult s(x,y)
    · have hCross : ¬(x ∈ A ↔ y ∈ A) := by
        have hn := mem_compl.mp hy
        tauto
      have hExists : ∃ v ∈ E, v ∈ s(x,y) := by
        rcases hCover x y hCross hp with he|he
        · exact ⟨x,he,by simp⟩
        · exact ⟨y,he,by simp⟩
      rw [if_pos hExists]
    · have hz : M.mult s(x,y)=0 := by omega
      simp only [hz,ite_self]
  calc
    M.cutSize A = (M.incidentOn E).cutSize A := hEq
    _ ≤ (M.incidentOn E).edgeCount := (M.incidentOn E).cutSize_le_edgeCount A
    _ ≤ ∑ v ∈ E, M.degree v := M.incidentOn_edgeCount_le E

theorem matching_cut_le_cover (M : MultiGraph V) (hM : ∀ v, M.degree v ≤ 1) (A E : Finset V)
    (hCover : ∀ x y, ¬(x ∈ A ↔ y ∈ A) → 0 < M.mult s(x,y) → x ∈ E ∨ y ∈ E) :
    M.cutSize A ≤ E.card := by
  calc
    M.cutSize A ≤ ∑ v ∈ E, M.degree v := M.cutSize_le_cover_degrees A E hCover
    _ ≤ ∑ _v ∈ E, 1 := sum_le_sum (fun v _ => hM v)
    _ = E.card := by simp

end SimpleGraph.MultiGraph
