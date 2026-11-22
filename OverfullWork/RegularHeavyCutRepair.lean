module

public import OverfullWork.RegularSupportRobustCut
public import OverfullWork.CanonicalGlobalRobust

@[expose] public section


/-! # Preserve robust crossing while putting heavy centre bundles across

This is the actual partition modification in CMS Case 2, Step 1.
Multiplicity weights and the exceptional heavy set are computed from
the input regular multigraph, and the returned crossing remains robust.
-/
namespace OverfullWork.RegularHeavyCutRepair
open SimpleGraph Finset PrunedCore RobustExpansion BipartiteRobustMargin BalancedCutPerturbation
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

def heavySet (M : MultiGraph V) (a b : V) (L : ℕ) : Finset V :=
  (CanonicalGlobalRobust.heavyNeighbours M a L).erase b

theorem heavySet_mem (M : MultiGraph V) (a b x : V) (L : ℕ) :
    x ∈ heavySet M a b L ↔ x ≠ b ∧ L < M.mult s(a,x) := by
  simp [heavySet, CanonicalGlobalRobust.heavyNeighbours]

theorem heavySet_card (M : MultiGraph V) (a b : V) (d L : ℕ) (hreg : M.IsRegularOfDegree d) :
    (heavySet M a b L).card ≤ d/(L+1) :=
  card_erase_le.trans (CanonicalGlobalRobust.heavyNeighbours_card M a L d (hreg a))

theorem heavySet_card_at_scale (M : MultiGraph V) (a b : V) (d m T : ℕ)
    (hreg : M.IsRegularOfDegree d) (hD : d ≤ 3*m) (hT : 1 ≤ T) :
    (heavySet M a b (m/T)).card ≤ 3*T := by
  have hm := Nat.lt_mul_div_succ m (show 0 < T by omega)
  have hDiv : d/(m/T+1) < 3*T := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < m/T+1)).mpr
    nlinarith only [hm,hD]
  exact (heavySet_card M a b d (m/T) hreg).trans (by omega)

theorem exists_adjusted_cut (M : MultiGraph V) (d m L h r t : ℕ)
    (hreg : M.IsRegularOfDegree d) (a b : V) (A : Finset V)
    (hA : A.card = m) (hAc : Aᶜ.card = m) (ha : a ∈ A) (hb : b ∉ A)
    (hCount : (heavySet M a b L).card+1 ≤ h) (hRoom : h ≤ m) (hr : 2*h ≤ r)
    (ξ : ℝ) (hDis : ∀ v, |(neighboursIn M.supportGraph A v:ℝ)-
      (neighboursIn M.supportGraph Aᶜ v:ℝ)| < ξ)
    (hRobust : IsBipartiteRobustAt M.supportGraph A r t) :
    ∃ B : Finset V, B.card = m ∧ Bᶜ.card = m ∧ a ∈ B ∧ b ∉ B ∧
      (∀ v, v ≠ b → L < M.mult s(a,v) → v ∉ B) ∧
      2*M.degreeInto B a ≤ d ∧
      IsBipartiteRobustAt M.supportGraph B (r-2*h) (t+h) ∧
      ∀ v, |(neighboursIn M.supportGraph B v:ℝ)-
        (neighboursIn M.supportGraph Bᶜ v:ℝ)| < ξ+2*(h:ℝ) := by
  let Z := heavySet M a b L
  have haZ : a ∉ Z := by
    intro hz
    have hh := (heavySet_mem M a b a L).mp hz
    have hl := M.loopless s(a,a) (by simp)
    omega
  have hbZ : b ∉ Z := by simp [Z,heavySet]
  have hwa : M.mult s(a,a) = 0 := M.loopless _ (by simp)
  obtain ⟨B,hB,hBc,haB,hbB,hBZ,hWeight,hCl⟩ := HeavyNeighbourCutRepair.exists_repaired_cut
    A Z a b m L (fun v => M.mult s(a,v)) hA hAc ha hb haZ hbZ hwa
    (by intro z hz; exact ((heavySet_mem M a b z L).mp hz).2.le)
    (by
      intro z hz hza hzb
      by_contra hn
      exact hz ((heavySet_mem M a b z L).mpr ⟨hzb,by omega⟩))
    (hCount.trans hRoom)
  have hAcross : ∀ v, v ≠ b → L < M.mult s(a,v) → v ∉ B := by
    intro v hv hmult hvB
    exact disjoint_left.mp hBZ hvB ((heavySet_mem M a b v L).mpr ⟨hv,hmult⟩)
  have hDegree : 2*M.degreeInto B a ≤ d := by
    have hs := M.degreeInto_add_compl B a
    rw [hreg a] at hs
    change M.degreeInto B a ≤ M.degreeInto Bᶜ a at hWeight
    omega
  refine ⟨B,hB,hBc,haB,hbB,hAcross,hDegree,?_,?_⟩
  · rcases hCl with hc | hc
    · have hc' : Close A B h := ⟨hc.1.trans hCount,hc.2.trans hCount⟩
      exact robust_of_close M.supportGraph A B r t h (hA.trans hB.symm) hc' hr hRobust
    · have hc' : Close Aᶜ B h := ⟨hc.1.trans hCount,hc.2.trans hCount⟩
      exact robust_of_close M.supportGraph Aᶜ B r t h (hAc.trans hB.symm) hc' hr
        (robust_compl M.supportGraph A r t hRobust)
  · intro v
    rcases hCl with hc | hc
    · have hc' : Close A B h := ⟨hc.1.trans hCount,hc.2.trans hCount⟩
      exact (discrepancy_le M.supportGraph A B h hc' v).trans_lt (by linarith [hDis v])
    · have hc' : Close Aᶜ B h := ⟨hc.1.trans hCount,hc.2.trans hCount⟩
      have hd : |(neighboursIn M.supportGraph Aᶜ v:ℝ)-
          (neighboursIn M.supportGraph Aᶜᶜ v:ℝ)| < ξ := by
        simpa only [compl_compl,abs_sub_comm] using hDis v
      exact (discrepancy_le M.supportGraph Aᶜ B h hc' v).trans_lt (by linarith)

end OverfullWork.RegularHeavyCutRepair
