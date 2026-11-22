module

public import OverfullWork.RegularHeavyCutRepair
public import OverfullWork.FrozenBlockOrientation

@[expose] public section


/-! # Construct light partners and the remainder comparison CMS (5.5)

The heavy vertices are already opposite the centre. Choose actual light
partners on its side, then orient the free blocks with these exceptions
fixed. The partner bijection and the surviving robust cut are outputs.
-/
namespace OverfullWork.HeavyNeighbourPartners
open SimpleGraph Finset PrunedCore RobustExpansion BipartiteRobustMargin BalancedCutPerturbation
open RegularHeavyCutRepair
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

theorem exists_partner_cut (M : MultiGraph V) (d m L h r t : ℕ)
    (hreg : M.IsRegularOfDegree d) (a b : V) (A : Finset V)
    (hA : A.card = m) (hAc : Aᶜ.card = m) (ha : a ∈ A) (hb : b ∉ A)
    (hAcross : ∀ v, v ≠ b → L < M.mult s(a,v) → v ∉ A)
    (hCount : (heavySet M a b L).card+1 ≤ h) (hRoom : h ≤ m) (hr : 2*h ≤ r)
    (ξ : ℝ) (hDis : ∀ v, |(neighboursIn M.supportGraph A v:ℝ)-
      (neighboursIn M.supportGraph Aᶜ v:ℝ)| < ξ)
    (hRobust : IsBipartiteRobustAt M.supportGraph A r t) :
    ∃ (B P : Finset V), B.card = m ∧ Bᶜ.card = m ∧ a ∈ B ∧ b ∉ B ∧
      Nonempty (↥(heavySet M a b L) ≃ ↥P) ∧ P ⊆ B ∧ a ∉ P ∧ b ∉ P ∧
      (∀ v ∈ P, M.mult s(a,v) ≤ L) ∧
      (∀ v, v ≠ b → L < M.mult s(a,v) → v ∉ B) ∧
      M.degreeInto (B\insert a P) a ≤ M.degreeInto (Bᶜ\insert b (heavySet M a b L)) a ∧
      2*M.degreeInto B a ≤ d ∧
      IsBipartiteRobustAt M.supportGraph B (r-2*h) (t+h) ∧
      ∀ v, |(neighboursIn M.supportGraph B v:ℝ)-
        (neighboursIn M.supportGraph Bᶜ v:ℝ)| < ξ+2*(h:ℝ) := by
  let Z := heavySet M a b L
  change Z.card+1 ≤ h at hCount
  obtain ⟨P,hPsub,hPcard⟩ := exists_subset_card_eq
    (show Z.card ≤ (A.erase a).card by rw [card_erase_of_mem ha,hA];omega)
  have haP : a ∉ P := fun hp => (mem_erase.mp (hPsub hp)).1 rfl
  have hbP : b ∉ P := fun hp => hb (mem_erase.mp (hPsub hp)).2
  have hPA : P ⊆ A := hPsub.trans (erase_subset a A)
  have hLight : ∀ v ∈ P, M.mult s(a,v) ≤ L := by
    intro v hv
    by_contra hn
    exact hAcross v (fun he => hbP (he ▸ hv)) (by omega) (hPA hv)
  have hZcomp : Z ⊆ Aᶜ := by
    intro v hv
    have hh := (heavySet_mem M a b v L).mp hv
    exact mem_compl.mpr (hAcross v hh.1 hh.2)
  have hbZ : b ∉ Z := by simp [Z,heavySet]
  have hX : insert a P ⊆ A := insert_subset ha hPA
  have hY : insert b Z ⊆ Aᶜ := insert_subset (mem_compl.mpr hb) hZcomp
  have hXY : (insert a P).card = (insert b Z).card := by simp [haP,hbZ,hPcard]
  have hWeight : (∑ v ∈ insert a P, M.mult s(a,v)) ≤ ∑ v ∈ insert b Z, M.mult s(a,v) := by
    rw [sum_insert haP,M.loopless s(a,a) (by simp),zero_add,sum_insert hbZ]
    have hp : (∑ v ∈ P, M.mult s(a,v)) ≤ L*P.card := by
      calc
        _ ≤ ∑ _v ∈ P, L := sum_le_sum hLight
        _ = _ := by simp [Nat.mul_comm]
    have hz : L*Z.card ≤ ∑ v ∈ Z, M.mult s(a,v) := by
      calc
        _ = ∑ _v ∈ Z, L := by simp [Nat.mul_comm]
        _ ≤ _ := sum_le_sum (fun v hv => ((heavySet_mem M a b v L).mp hv).2.le)
    rw [hPcard] at hp
    omega
  obtain ⟨B,hB,hBc,hXB,hYBc,hFree,hWeightB,hCl⟩ := FrozenBlockOrientation.exists_orientation
    A (insert a P) (insert b Z) m (fun v => M.mult s(a,v)) hA hAc hX hY hXY hWeight
  have hBcentre : a ∈ B := hXB (mem_insert_self _ _)
  have hbB : b ∉ B := mem_compl.mp (hYBc (mem_insert_self _ _))
  have hBacross : ∀ v, v ≠ b → L < M.mult s(a,v) → v ∉ B := by
    intro v hv hm
    exact mem_compl.mp (hYBc (mem_insert_of_mem ((heavySet_mem M a b v L).mpr ⟨hv,hm⟩)))
  have hDegree : 2*M.degreeInto B a ≤ d := by
    have hs := M.degreeInto_add_compl B a
    rw [hreg a] at hs
    change M.degreeInto B a ≤ M.degreeInto Bᶜ a at hWeightB
    omega
  have hCount' : (insert a P).card ≤ h := by rw [card_insert_of_notMem haP,hPcard];exact hCount
  refine ⟨B,P,hB,hBc,hBcentre,hbB,⟨Finset.equivOfCardEq hPcard.symm⟩,
    (fun v hv => hXB (mem_insert_of_mem hv)),haP,hbP,hLight,hBacross,hFree,hDegree,?_,?_⟩
  · rcases hCl with hc | hc
    · exact robust_of_close M.supportGraph A B r t h (hA.trans hB.symm)
        ⟨hc.1.trans hCount',hc.2.trans hCount'⟩ hr hRobust
    · exact robust_of_close M.supportGraph Aᶜ B r t h (hAc.trans hB.symm)
        ⟨hc.1.trans hCount',hc.2.trans hCount'⟩ hr (robust_compl M.supportGraph A r t hRobust)
  · intro v
    rcases hCl with hc | hc
    · have hh := discrepancy_le M.supportGraph A B h ⟨hc.1.trans hCount',hc.2.trans hCount'⟩ v
      exact hh.trans_lt (by linarith [hDis v])
    · have hh := discrepancy_le M.supportGraph Aᶜ B h ⟨hc.1.trans hCount',hc.2.trans hCount'⟩ v
      have hd : |(neighboursIn M.supportGraph Aᶜ v:ℝ)-
          (neighboursIn M.supportGraph Aᶜᶜ v:ℝ)| < ξ := by
        simpa only [compl_compl,abs_sub_comm] using hDis v
      exact hh.trans_lt (by linarith)

end OverfullWork.HeavyNeighbourPartners
