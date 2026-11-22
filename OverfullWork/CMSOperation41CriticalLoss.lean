module

public import OverfullWork.CMSOperation41CriticalEntry

@[expose] public section


/-! The fixed active sets charge later exceptional losses to edges
actually deleted. The singleton's possible last edge gets one explicit
cleanup even before the physical host layers have been packed. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
attribute [-instance] SimpleGraph.instDecidableRelAdjDeleteEdgesOfDecidablePredSym2MemSetOfDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2000000 in
/-- Algorithm 1 for the inherited singleton of degree one. This
version works on the virtual graph and updates the auxiliary degree
record. The regular ordinary host still awaits physical packing. -/
theorem virtual_cleanup_of_exhausted_singleton (S : SimpleGraph V) [sDec : DecidableRel S.Adj]
    (initial current : Finset V) (hCurrent : current ⊆ initial) (w : V) (hw : w ∈ current)
    (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (j d : ℕ)
    (hOne : S.degree w = 1) :
    let before := auxiliaryPhysicalDegree S initial P credit j
    let support := univ.filter (fun v => 0 < before v)
    current ⊆ support → Odd support.card →
    (∀ x,S.Adj w x → 2 ≤ before x) → (∀ v,before v ≤ d) →
    (∑ v ∈ support \ current,(d-before v)) ≤ 1 →
    ∃ (x : V) (T : SimpleGraph V),S.Adj w x ∧ T = S.deleteEdges {s(w,x)} ∧
      DeletionRun {w} S T ∧
      let after := auxiliaryPhysicalDegree T initial P credit j
      let support' := univ.filter (fun v => 0 < after v)
      (∀ v,after v+(if v=w ∨ v=x then 1 else 0) = before v) ∧
      support' = support.erase w ∧ current ∩ support' = current.erase w ∧
      Even support'.card ∧ support' \ current.erase w = support \ current ∧
      (∑ v ∈ support' \ current.erase w,(d-after v)) ≤ 2 := by
  cases Subsingleton.elim sDec (fun u v => Classical.propDecidable (S.Adj u v))
  intro before support hU hOdd hOther hBound hMass
  obtain ⟨x,hEdge,_⟩ := (degree_eq_one_iff_existsUnique_adj (G := S)).mp hOne
  let T := S.deleteEdges {s(w,x)}
  let after := auxiliaryPhysicalDegree T initial P credit j
  let support' := univ.filter (fun v => 0 < after v)
  have hLe : T ≤ S := deleteEdges_le _
  have hNear : PrunedCore.neighboursIn S {w} x = 1 := by
    rw [RobustExpansion.neighboursIn_eq_filter_card,filter_singleton,if_pos hEdge.symm,card_singleton]
  have hRun : DeletionRun {w} S T :=
    DeletionRun.step (DeletionRun.refl S) (mem_singleton_self _) hEdge (by rw [hOne,hNear])
  have hDegree (v : V) : T.degree v+(if v=w ∨ v=x then 1 else 0) = S.degree v :=
    WeakVALSingleEdgeDeletion.degree_delete_add S hEdge v
  have hW : before w = 1 := by rw [show before w = S.degree w from if_pos (hCurrent hw),hOne]
  have hx := hOther x hEdge
  have hExact (v : V) : after v+(if v=w ∨ v=x then 1 else 0) = before v := by
    have hDiff : (sdiff S T).degree v = if v=w ∨ v=x then 1 else 0 := by
      have h := hDegree v
      have hAdd : T.degree v+(sdiff S T).degree v = S.degree v := by
        simpa only [add_comm,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
          MaximumMatching.degree_sdiff_add_of_le S T hLe v
      omega
    have hRead : after v = before v-(sdiff S T).degree v :=
      auxiliary_physical_degree_after_cleanup S T initial P credit j hLe v
    rw [hDiff] at hRead
    by_cases h : v=w ∨ v=x
    · rcases h with rfl | rfl <;> simp only [true_or,or_true,if_true] at hRead ⊢ <;> omega
    · rw [if_neg h] at hRead ⊢
      omega
  have hZero : after w = 0 := by
    have h := hExact w
    simp only [true_or,if_true,hW] at h
    omega
  have hOtherPos (v : V) (hv : v ≠ w) : 0 < after v ↔ 0 < before v := by
    have h := hExact v
    by_cases he : v = x
    · subst v
      simp only [or_true,if_true] at h
      omega
    · simp only [hv,he,or_self,if_false,add_zero] at h
      rw [h]
  have hErase : support' = support.erase w :=
    (support_after_exhausting_singleton before after w (by omega) hZero hOtherPos).1
  have hCurrentErase : current ∩ support' = current.erase w := by
    rw [hErase]
    ext v
    simp only [mem_inter,mem_erase]
    exact ⟨fun ⟨hv,hne,_⟩ => ⟨hne,hv⟩,fun ⟨hne,hv⟩ => ⟨hv,hne,hU hv⟩⟩
  obtain ⟨hEven,hOrd,hDeficit⟩ := critical_cut_after_singleton_cleanup support current w x hU hw
    hOdd before after d (fun v _ => hBound v) hMass hExact
  refine ⟨x,T,hEdge,rfl,hRun,hExact,hErase,hCurrentErase,?_,?_,?_⟩
  · change Even support'.card
    rwa [hErase]
  · change support' \ current.erase w = support \ current
    rwa [hErase]
  · change (∑ v ∈ support' \ current.erase w,(d-after v)) ≤ 2
    rwa [hErase]

/-- Every degree loss at an inactive exceptional vertex in a pair
round is paid by a prescribed edge to an active vertex. A sequence
of such rounds cannot spend that edge twice. -/
theorem TrimmingStepSelection.inactive_pair_degree_charge
    {T : SimpleGraph V} [DecidableRel T.Adj] {initial current active : Finset V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection T initial current active degree d floor used j cap)
    (hPair : active.card = 2) (hInitial : current ⊆ initial) (v : V)
    (hv : v ∈ current) (hInactive : v ∉ active) :
    let P := R.round.words.prescribedGraph
    P.degree v ≤ 2*(P.neighborFinset v ∩ active).card := by
  intro P
  by_cases hZero : P.degree v = 0
  · simp [hZero]
  have hNone := R.special_only_when_empty (card_pos.mp (by omega : 0 < active.card))
  rcases R.exceptional_debit v hv hInactive (Nat.pos_of_ne_zero hZero) with
    ⟨w,hw,hEdge⟩ | hSpecial | ⟨w,hW,_⟩
  · have hBound := R.round.words.prescribed_graph_degree_le v
    rw [if_pos (hInitial hv)] at hBound
    have hPos : 1 ≤ (P.neighborFinset v ∩ active).card :=
      card_pos.mpr ⟨w,mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr hEdge.symm,hw⟩⟩
    change P.degree v ≤ 2 at hBound
    omega
  · rw [hNone] at hSpecial
    cases hSpecial
  · rw [hW,card_singleton] at hPair
    omega

set_option maxHeartbeats 1600000 in
/-- The loss at a fixed inactive vertex over the entire pair phase is
at most four. The bound is independent of the number of rounds. -/
theorem inherited_pair_prefix_inactive_floor
    (A : Finset V) (hPair : A.card = 2) (S P : ℕ → SimpleGraph V)
    (m floor loss : ℕ) (v : V) (hEntry : floor ≤ (S 0).degree v+loss)
    (hLayer : ∀ i < m,P i ≤ S i)
    (hNext : ∀ i < m,S (i+1) = sdiff (S i) (P i))
    (hCost : ∀ i < m,(P i).degree v ≤ 2*((P i).neighborFinset v ∩ A).card) :
    floor ≤ (S m).degree v+loss+4 := by
  have hEdges : (∑ i ∈ range m,((P i).neighborFinset v ∩ A).card) ≤ 2 := by
    rw [←hPair]
    refine (sum_le_sum (fun i _ => ?_)).trans
      (virtual_incident_deletions_into_le S S P m A v (fun _ _ => le_rfl) hLayer hNext)
    apply card_le_card
    intro x hx
    obtain ⟨hx,hA⟩ := mem_inter.mp hx
    exact mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr
      (Or.inr ((mem_neighborFinset _ _ _).mp hx)),hA⟩
  have hSpent : (∑ i ∈ range m,(P i).degree v) ≤
      2*(∑ i ∈ range m,((P i).neighborFinset v ∩ A).card) := by
    rw [mul_sum]
    exact sum_le_sum (fun i hi => hCost i (mem_range.mp hi))
  have hTotal (i : ℕ) (hi : i ≤ m) :
      (S i).degree v+(∑ j ∈ range i,(P j).degree v) = (S 0).degree v := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hi' : i < m := by omega
      have h := ih hi'.le
      have hStep : (S (i+1)).degree v+(P i).degree v = (S i).degree v := by
        rw [hNext i hi']
        simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
          MaximumMatching.degree_sdiff_add_of_le (S i) (P i) (hLayer i hi') v
      rw [sum_range_succ]
      omega
  have h := hTotal m le_rfl
  omega

/-- During singleton rounds the additional internal charge uses one
edge at the singleton, and can start only when its degree is already
bounded by the size of the exceptional set plus one. -/
theorem TrimmingStepSelection.inactive_singleton_degree_charge
    {T : SimpleGraph V} [DecidableRel T.Adj] {initial current : Finset V} {w v : V}
    {degree : V → ℕ} {d floor j cap : ℕ} {used : ℕ → Finset V}
    (R : TrimmingStepSelection T initial current {w} degree d floor used j cap)
    (hv : v ∈ current) (hne : v ≠ w) :
    let P := R.round.words.prescribedGraph
    (0 < P.degree v → P.Adj w v ∨ (R.internalCharge v ∧ P.degree v = 1)) ∧
    (R.internalCharge v → T.degree w ≤ current.card+1 ∧ P.degree w = 1) := by
  intro P
  constructor
  · intro hp
    have hNone := R.special_only_when_empty (singleton_nonempty _)
    rcases R.exceptional_debit v hv (by simpa using hne) hp with
      ⟨x,hx,hEdge⟩ | hSpecial | ⟨x,hx,hGap,hBound,hOne,hV⟩
    · exact Or.inl (mem_singleton.mp hx ▸ hEdge)
    · rw [hNone] at hSpecial
      cases hSpecial
    · exact Or.inr ⟨⟨x,hx,hGap,hBound,hOne,hV⟩,hV⟩
  · rintro ⟨x,hx,_,hSmall,hOne,_⟩
    have he : x = w := singleton_inj.mp hx.symm
    subst x
    exact ⟨by omega,hOne⟩

/-- With at most one unit of ordinary deficit, every neighbour of the
exhausted singleton has at least two units in the virtual record.
The exceptional case uses the inactive-vertex floor. -/
theorem exhausted_singleton_neighbour_has_room
    (S : SimpleGraph V) [sDec : DecidableRel S.Adj] (initial current : Finset V)
    (w : V) (P : ℕ → SimpleGraph V) (credit : ℕ → V → ℕ) (j d : ℕ) (hD : 3 ≤ d)
    (hCurrent : current ⊆ initial) :
    let degree := auxiliaryPhysicalDegree S initial P credit j
    let support := univ.filter (fun v => 0 < degree v)
    (∀ v,v ∉ initial → 0 < degree v) →
    (∀ v ∈ current,v ≠ w → 2 ≤ S.degree v) →
    (∑ v ∈ support \ current,(d-degree v)) ≤ 1 →
    ∀ x,S.Adj w x → 2 ≤ degree x := by
  cases Subsingleton.elim sDec (fun a b => Classical.propDecidable (S.Adj a b))
  intro degree support hCore hInactive hMass x hx
  by_cases hxU : x ∈ current
  · change 2 ≤ auxiliaryPhysicalDegree S initial P credit j x
    rw [auxiliaryPhysicalDegree,if_pos (hCurrent hxU)]
    exact hInactive x hxU hx.ne.symm
  have hPos : 0 < degree x := by
    by_cases hxI : x ∈ initial
    · change 0 < auxiliaryPhysicalDegree S initial P credit j x
      rw [auxiliaryPhysicalDegree,if_pos hxI]
      exact (S.degree_pos_iff_exists_adj x).mpr ⟨w,hx.symm⟩
    · exact hCore x hxI
  have hMem : x ∈ support \ current :=
    mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,hPos⟩,hxU⟩
  have h := single_le_sum (f := fun v => d-degree v) (fun _ _ => Nat.zero_le _) hMem
  omega

/-- Over the inherited singleton phase, at most two units are paid
by incidences with the singleton, and at most the exceptional cap
can be paid by the internal-charge case. -/
theorem inherited_singleton_prefix_inactive_floor
    (S P : ℕ → SimpleGraph V) (m floor loss cap : ℕ) (w v : V)
    (internal : ℕ → Prop) (hInitial : floor ≤ (S 0).degree v+loss)
    (hLayer : ∀ i < m,P i ≤ S i)
    (hNext : ∀ i < m,S (i+1) = sdiff (S i) (P i))
    (hTwo : ∀ i < m,(P i).degree v ≤ 2)
    (hCharge : ∀ i < m,0 < (P i).degree v →
      (P i).Adj w v ∨ (internal i ∧ (P i).degree v = 1))
    (hFuel : ∀ i < m,internal i → (S i).degree w ≤ cap ∧ 1 ≤ (P i).degree w) :
    floor ≤ (S m).degree v+loss+cap+2 := by
  have hInit : floor-loss ≤ (S 0).degree v := by omega
  have h := singleton_prefix_current_exceptional_degree_floor S S P m (floor-loss) cap
    {w} w v (mem_singleton_self _) internal (fun _ _ => le_rfl) hLayer hNext hInit
    (fun _ _ _ he => (he.2 he.1).elim) hTwo hCharge hFuel
  simp only [card_singleton] at h
  omega

end OverfullWork.CMSTrimmingRound
