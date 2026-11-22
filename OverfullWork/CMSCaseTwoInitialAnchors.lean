module

public import OverfullWork.CMSCaseTwoAnchorGeometry
public import OverfullWork.LowSetEdgePreprocessing
public import OverfullWork.PriorityMCCPairing

@[expose] public section


/-! The two initial anchor runs in CMS Theorem 4.2, Case 2, Step 3.
The distinct exceptional vertex is protected only when it exists. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph PrunedCore MultiGraph.PartialColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V}
variable {a b w : V} {d m L r t k : ℕ} {η : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η}

theorem CaseTwoPartition.second_ordinary_neighbour_bound
    (s : CaseTwoPartition M a b d m L r t η) (E : ℕ)
    (hProfile : d ≤ M.supportGraph.degree b+M.mult s(a,b)+E) :
    (d:ℝ) < 2*((M.neighboursInto (s.part.erase a) b).card:ℝ)+
      (M.mult s(a,b):ℝ)+(E:ℝ)+η*(m:ℝ)+2 := by
  have hSplit := LowSetEdgePreprocessing.neighboursIn_add_compl M.supportGraph s.part b
  have hDis := (abs_lt.mp (s.simple_discrepancy b)).1
  have hCard : neighboursIn M.supportGraph s.part b ≤ (M.neighboursInto (s.part.erase a) b).card+1 := by
    rw [RobustExpansion.neighboursIn_eq_filter_card]
    have hs : s.part.filter (fun v => M.supportGraph.Adj b v) ⊆
        insert a (M.neighboursInto (s.part.erase a) b) := by
      intro v hv
      obtain ⟨hv,hvAdj⟩ := mem_filter.mp hv
      by_cases ha : v = a
      · exact mem_insert.mpr (Or.inl ha)
      · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_erase.mpr ⟨ha,hv⟩,hvAdj⟩))
    exact (card_le_card hs).trans (card_insert_le _ _)
  have hProfileR : (d:ℝ) ≤ (M.supportGraph.degree b:ℝ)+(M.mult s(a,b):ℝ)+(E:ℝ) := by
    exact_mod_cast hProfile
  have hSplitR : (neighboursIn M.supportGraph s.part b:ℝ)+
      (neighboursIn M.supportGraph s.partᶜ b:ℝ) = M.supportGraph.degree b := by exact_mod_cast hSplit
  have hCardR : (neighboursIn M.supportGraph s.part b:ℝ) ≤
      (M.neighboursInto (s.part.erase a) b).card+1 := by exact_mod_cast hCard
  linarith only [hProfileR,hSplitR,hCardR,hDis]

theorem CaseTwoMiddleCopies.exists_first_anchor_run (copies : CaseTwoMiddleCopies s w)
    (C : copies.graph.EdgeColoring k) (hw : w ∉ s.part) (hk : k ≤ M.degree a)
    (ξ B : ℝ)
    (hMissing : ∀ v, ((C.missingPalette v).card:ℝ) < ξ)
    (hPerColour : ∀ i : Fin k, ((C.missingSet univ i).card:ℝ) ≤ B) :
    ∃ Q : M.PartialColouring k, ∃ u : ℕ,
      (if b = w then CentreRun a (copies.partialSeed C) Q (C.missingPalette a).card u
        else ProtectedRun a b w (copies.partialSeed C) Q (C.missingPalette a).card u) ∧
      u ≤ 2*(C.missingPalette a).card ∧
      (∀ i : Fin k, (Q.colouring.colourGraph i).degree a = 1) ∧
      Q.graph.mult s(b,w) = M.mult s(b,w) ∧
      (∀ v ∈ s.part, Q.graph.mult s(a,v) = M.mult s(a,v)) ∧
      (∀ x y, x ≠ a → y ≠ a → ¬(x ∈ s.part ↔ y ∈ s.part) → Q.graph.mult s(x,y) = 0) ∧
      (∀ v, ((Q.colouring.missingPalette v).card:ℝ) < 3*ξ) ∧
      ∀ i : Fin k, ((Q.colouring.missingSet univ i).card:ℝ) ≤ B+2*ξ := by
  have hab : a ≠ b := fun he => s.second_not_mem (he ▸ s.centre_mem)
  have haw : a ≠ w := fun he => hw (he ▸ s.centre_mem)
  suffices ∃ Q : M.PartialColouring k, ∃ u : ℕ,
      (if b = w then CentreRun a (copies.partialSeed C) Q (C.missingPalette a).card u
        else ProtectedRun a b w (copies.partialSeed C) Q (C.missingPalette a).card u) ∧
      u ≤ 2*(C.missingPalette a).card ∧
      (∀ i : Fin k, (Q.colouring.colourGraph i).degree a = 1) ∧
      Q.graph.mult s(b,w) = M.mult s(b,w) ∧
      (∀ e, a ∈ e → copies.graph.mult e ≤ Q.graph.mult e) ∧
      (∀ e, a ∉ e → Q.graph.mult e ≤ copies.graph.mult e) ∧
      (∀ v, (Q.colouring.missingPalette v).card ≤ (C.missingPalette v).card+u) ∧
      ∀ i : Fin k, (Q.colouring.missingSet univ i).card ≤ (C.missingSet univ i).card+
        2*(C.missingPalette a).card by
    obtain ⟨Q,u,hRun,hu,hSat,hBundle,hIn,hAway,hGrow,hGrowColour⟩ := this
    refine ⟨Q,u,hRun,hu,hSat,hBundle,?_,?_,?_,?_⟩
    · intro v hv
      apply le_antisymm (Q.le _)
      rw [←copies.internal_centre_full v hv]
      exact hIn _ (by simp)
    · intro x y hx hy hCross
      have hh := hAway s(x,y) (by simp only [Sym2.mem_iff]; tauto)
      rwa [copies.away_crossing_zero x y hx hy hCross,Nat.le_zero] at hh
    · intro v
      have hh : ((Q.colouring.missingPalette v).card:ℝ) ≤ (C.missingPalette v).card+(u:ℝ) := by
        exact_mod_cast hGrow v
      have huR : (u:ℝ) ≤ 2*((C.missingPalette a).card:ℝ) := by exact_mod_cast hu
      linarith only [hh,huR,hMissing a,hMissing v]
    · intro i
      have hh : ((Q.colouring.missingSet univ i).card:ℝ) ≤
          (C.missingSet univ i).card+2*((C.missingPalette a).card:ℝ) := by exact_mod_cast hGrowColour i
      linarith only [hh,hPerColour i,hMissing a]
  by_cases hbw : b = w
  · obtain ⟨Q,u,hRun,hu,hSat,_⟩ := exists_centre_saturated_run a hk (copies.partialSeed C)
    change u ≤ (C.missingPalette a).card at hu
    refine ⟨Q,u,by simpa only [if_pos hbw,CaseTwoMiddleCopies.partialSeed] using hRun,by omega,hSat,?_,
      fun e ha => (hRun.bundle_bounds e).1 ha,fun e ha => (hRun.bundle_bounds e).2 ha,
      hRun.missingPalette_growth_le,fun i => (hRun.missingSet_mono i).trans (Nat.le_add_right _ _ )⟩
    rw [←hbw,Q.graph.loopless _ (by simp),M.loopless _ (by simp)]
  · obtain ⟨Q,u,hRun,hu,hSat,hBundle,_⟩ := exists_protected_centre_saturated_run a b w hab haw hbw
      hk (copies.partialSeed C) (copies.protected_triangle hw hbw)
    refine ⟨Q,u,by simpa only [if_neg hbw,CaseTwoMiddleCopies.partialSeed] using hRun,hu,hSat,?_,?_,
      hRun.away_bundle_le,
      hRun.missingPalette_growth_le,hRun.missingSet_growth_le⟩
    · exact hBundle.trans (MiddleCopyGraph.opposite_mult M s.part a b w copies.count
        (copies.inside_zero _ s.centre_mem) s.centre_mem s.second_not_mem hw)
    · intro e
      induction e using Sym2.inductionOn with
      | hf x y =>
        simp only [Sym2.mem_iff]
        rintro (rfl | rfl)
        · exact hRun.centre_bundle_mono y
        · rw [Sym2.eq_swap]
          exact hRun.centre_bundle_mono x


/-- The crossing degree and the non-heavy gap pay the ordinary
neighbours for the second anchor. Both initial runs construct a
partial colouring with a common-missing-colour pairing. -/
theorem CaseTwoMiddleCopies.exists_initial_anchor_runs (copies : CaseTwoMiddleCopies s w)
    (C : copies.graph.EdgeColoring k) (hw : w ∉ s.part) (hk : k ≤ M.degree a)
    (E : ℕ) (ξ B : ℝ) (hOrder : Fintype.card V = 2*m)
    (hMissing : ∀ v, ((C.missingPalette v).card:ℝ) < ξ)
    (hPerColour : ∀ i : Fin k, ((C.missingSet univ i).card:ℝ) ≤ B)
    (hProfile : d ≤ M.supportGraph.degree b+M.mult s(a,b)+E)
    (hGap : (M.mult s(a,b):ℝ)+(E:ℝ)+η*(m:ℝ)+6*ξ+4 ≤ (d:ℝ)) :
    ∃ Q R : M.PartialColouring k, ∃ u v : ℕ,
      (if b = w then CentreRun a (copies.partialSeed C) Q (C.missingPalette a).card u
        else ProtectedRun a b w (copies.partialSeed C) Q (C.missingPalette a).card u) ∧
      AnchoredRun s.part a b Q R (Q.colouring.missingPalette b).card v ∧
      u ≤ 2*(C.missingPalette a).card ∧ v ≤ (Q.colouring.missingPalette b).card ∧
      (∀ i : Fin k, (R.colouring.colourGraph i).degree a = 1 ∧
        (R.colouring.colourGraph i).degree b = 1) ∧
      R.graph.mult s(b,w) = M.mult s(b,w) ∧
      (∀ z ∈ s.part, R.graph.mult s(a,z) = M.mult s(a,z)) ∧
      (∀ x y, x ≠ a → y ≠ a → x ≠ b → y ≠ b →
        ¬(x ∈ s.part ↔ y ∈ s.part) → R.graph.mult s(x,y) = 0) ∧
      (∀ z, ((R.colouring.missingPalette z).card:ℝ) < 6*ξ) ∧
      Nonempty (PriorityMCCPairing.Family R.colouring s.part) ∧
      ∀ i : Fin k, ((R.colouring.missingSet univ i).card:ℝ) ≤ B+2*ξ := by
  obtain ⟨Q,u,hFirst,hu,hSat,hBundle,hInternal,hAway,hQMissing,hQColour⟩ :=
    copies.exists_first_anchor_run C hw hk ξ B hMissing hPerColour
  have hab : a ≠ b := fun he => s.second_not_mem (he ▸ s.centre_mem)
  have hFree : Q.ordinaryFree s.part a b = M.neighboursInto (s.part.erase a) b := by
    ext z
    simp only [MultiGraph.PartialColouring.ordinaryFree,MultiGraph.neighboursInto,mem_filter]
    by_cases hz : z ∈ s.part.erase a
    · obtain ⟨hza,hzA⟩ := mem_erase.mp hz
      have hZero := hAway b z hab.symm hza (by simp [s.second_not_mem,hzA])
      change (z ∈ s.part.erase a ∧ 0 < M.mult s(b,z)-Q.graph.mult s(b,z)) ↔ _
      rw [hZero,Nat.sub_zero]
    · simp only [hz,false_and]
  have hReserve : (Q.colouring.missingPalette b).card+1 ≤ (Q.ordinaryFree s.part a b).card := by
    rw [hFree]
    have hBound := s.second_ordinary_neighbour_bound E hProfile
    have hh : ((Q.colouring.missingPalette b).card:ℝ)+1 ≤
        ((M.neighboursInto (s.part.erase a) b).card:ℝ) := by
      linarith only [hBound,hQMissing b,hGap]
    exact_mod_cast hh
  obtain ⟨R,v,hSecond,hv,hSatB⟩ :=
    exists_anchored_saturated_run s.part a b s.second_not_mem Q hReserve
  have hEven : Even (Fintype.card V) := ⟨m,by omega⟩
  refine ⟨Q,R,u,v,hFirst,hSecond,hu,hv,fun i => ⟨hSecond.preserves_saturation hab hSat i,hSatB i⟩,
    (hSecond.second_bundle w hw).trans hBundle,
    fun z hz => (hSecond.anchor_bundle hab z).trans (hInternal z hz),
    ?_,?_,PriorityMCCPairing.exists_family R.colouring s.part hEven,?_⟩
  · intro x y hxa hya hxb hyb hCross
    have hh := hSecond.away_bundle_le s(x,y) (by simp only [Sym2.mem_iff]; tauto)
    rwa [hAway x y hxa hya hCross,Nat.le_zero] at hh
  · intro z
    have hh : ((R.colouring.missingPalette z).card:ℝ) ≤
        (Q.colouring.missingPalette z).card+(v:ℝ) := by
      exact_mod_cast hSecond.toCentreRun.missingPalette_growth_le z
    have hvR : (v:ℝ) ≤ (Q.colouring.missingPalette b).card := by exact_mod_cast hv
    linarith only [hh,hvR,hQMissing b,hQMissing z]
  · intro i
    exact (show ((R.colouring.missingSet univ i).card:ℝ) ≤
      ((Q.colouring.missingSet univ i).card:ℝ) by exact_mod_cast hSecond.toCentreRun.missingSet_mono i).trans
        (hQColour i)

end OverfullWork.CMSBalancedCut
