module

public import OverfullWork.CMSOperation41DegreeHistory
public import OverfullWork.CMSOperation41ExactRecords
public import OverfullWork.CMSOperation41SingletonExhaustion

@[expose] public section


/-! Claim 4.1(4) for vertices which have not left the exceptional set.
Incidental losses use distinct edges to earlier active vertices.
Repeated special uses respect their own degree floor, and singleton
charges spend a separate bounded number of rounds. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem virtual_trimming_prefix_le
    (S T P : ℕ → SimpleGraph V) (m : ℕ) (hClean : ∀ i < m,T i ≤ S i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i)) :
    ∀ a b,a ≤ b → b ≤ m → S b ≤ S a := by
  intro a b hab hb
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    exact le_rfl
  | succ b ih =>
    by_cases ha : a = b+1
    · rw [ha]
    have hlt : b < m := by omega
    rw [hNext b hlt]
    exact (show sdiff (T b) (P b) ≤ T b from fun _ _ h => h.1).trans
      ((hClean b hlt).trans (ih (by omega) hlt.le))

set_option maxHeartbeats 2000000 in
/-- Each edge from a vertex to the union of possible active sets
pays for at most one round, across cleanup and prescriptions together. -/
theorem virtual_incident_deletions_into_le
    (S T P : ℕ → SimpleGraph V) (m : ℕ) (A : Finset V) (v : V)
    (hClean : ∀ i < m,T i ≤ S i) (hP : ∀ i < m,P i ≤ T i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i)) :
    (∑ i ∈ range m,(((sdiff (S i) (T i)) ⊔ P i).neighborFinset v ∩ A).card) ≤ A.card := by
  let N (i : ℕ) := (((sdiff (S i) (T i)) ⊔ P i).neighborFinset v ∩ A)
  have hDis : (↑(range m) : Set ℕ).PairwiseDisjoint N := by
    intro i hi j hj hne
    simp only [coe_range] at hi hj
    have hBefore (a b : ℕ) (hab : a < b) (hb : b < m) : Disjoint (N a) (N b) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have hGone := (mem_neighborFinset _ _ _).mp (mem_inter.mp hx).1
      have hLater := (mem_neighborFinset _ _ _).mp (mem_inter.mp hy).1
      have hS : (S b).Adj v x := hLater.elim And.left (fun h => hClean b hb (hP b hb h))
      have hLe := virtual_trimming_prefix_le S T P m hClean hNext (a+1) b (by omega) hb.le
      have hOld := hLe hS
      rw [hNext a (hab.trans hb)] at hOld
      exact hGone.elim (fun h => h.2 hOld.1) (fun h => hOld.2 h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hBefore i j h hj
    · exact (hBefore j i h hi).symm
  change ∑ i ∈ range m,(N i).card ≤ A.card
  rw [←card_biUnion hDis]
  exact card_le_card (fun x hx => by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    exact (mem_inter.mp hi).2)

/-- Charge a prescribed loss to a deleted matching edge, to the
special vertex, or to the one-edge charge in S2.2.1. -/
theorem exceptional_round_cost_of_classification
    (C P : SimpleGraph V) (A : Finset V) (v : V) (special internal : Prop)
    (hDis : Disjoint C P) (hCleanup : ∀ x,C.Adj v x → x ∈ A)
    (hTwo : P.degree v ≤ 2)
    (hClass : 0 < P.degree v →
      (∃ x ∈ A,P.Adj v x) ∨ special ∨ (internal ∧ P.degree v = 1)) :
    C.degree v+P.degree v ≤ 2*((C ⊔ P).neighborFinset v ∩ A).card+
      (if special then 2 else 0)+(if internal then 1 else 0) := by
  let N := (C ⊔ P).neighborFinset v ∩ A
  have hBase : C.neighborFinset v ⊆ N := by
    intro x hx
    have he := (mem_neighborFinset C v x).mp hx
    exact mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr (Or.inl he),hCleanup x he⟩
  have hC : C.degree v ≤ N.card := by rw [←card_neighborFinset_eq_degree]; exact card_le_card hBase
  change C.degree v+P.degree v ≤ 2*N.card+_+_
  by_cases hPos : 0 < P.degree v
  · rcases hClass hPos with ⟨x,hx,hAdj⟩ | hs | ⟨hi,hOne⟩
    · have hFresh : x ∉ C.neighborFinset v := fun h =>
        (disjoint_iff_inf_le.mp hDis) ⟨(mem_neighborFinset _ _ _).mp h,hAdj⟩
      have hAdd : C.degree v+1 ≤ N.card := by
        rw [←card_neighborFinset_eq_degree,←card_insert_of_notMem hFresh]
        exact card_le_card (insert_subset_iff.mpr
          ⟨mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr (Or.inr hAdj),hx⟩,hBase⟩)
      omega
    · rw [if_pos hs]
      omega
    · rw [if_pos hi]
      omega
  · omega

set_option maxHeartbeats 2000000 in
/-- Degree floor after paying twice for each deleted incident edge
into the active sets and once for each internal singleton charge. -/
theorem current_exceptional_degree_floor_of_charges
    (S T P : ℕ → SimpleGraph V) (m floor internalBound : ℕ)
    (A : Finset V) (v : V) (special : ℕ → Option V) (internal : ℕ → Prop)
    (hClean : ∀ i < m,T i ≤ S i) (hP : ∀ i < m,P i ≤ T i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i))
    (hInitial : floor ≤ (S 0).degree v)
    (hSpecial : ∀ i < m,special i = some v → floor+2 ≤ (S i).degree v ∧ 2 ≤ (P i).degree v)
    (hInternal : ((range m).filter internal).card ≤ internalBound)
    (hDebit : ∀ i < m,
      (sdiff (S i) (T i)).degree v+(P i).degree v ≤
        2*(((sdiff (S i) (T i)) ⊔ P i).neighborFinset v ∩ A).card+
          (if special i = some v then 2 else 0)+(if internal i then 1 else 0)) :
    floor ≤ (S m).degree v+2*A.card+internalBound := by
  let incident (i : ℕ) := (((sdiff (S i) (T i)) ⊔ P i).neighborFinset v ∩ A).card
  let cleanup (i : ℕ) := (sdiff (S i) (T i)).degree v
  have hBalance (i : ℕ) (hi : i < m) :
      (S (i+1)).degree v+cleanup i+(P i).degree v = (S i).degree v := by
    have hC : (T i).degree v+cleanup i = (S i).degree v := by
      simpa only [cleanup,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card,add_comm] using
        MaximumMatching.degree_sdiff_add_of_le (S i) (T i) (hClean i hi) v
    have hLayer : (S (i+1)).degree v+(P i).degree v = (T i).degree v := by
      rw [hNext i hi]
      simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le (T i) (P i) (hP i hi) v
    omega
  have hSpecialFloor := special_use_preserves_initial_floor (fun i x => (S i).degree x)
    special m floor v hInitial
    (fun i hi => by have h := hBalance i hi; omega)
    (fun i hi hs => by
      obtain ⟨hFloor,hTwo⟩ := hSpecial i hi hs
      have h := hBalance i hi
      exact ⟨hFloor,by omega⟩) m le_rfl
  have hTel (j : ℕ) (hj : j ≤ m) :
      (S 0).degree v ≤ (S j).degree v+2*(∑ i ∈ range j,incident i)+
        2*specialUseCount special j v+((range j).filter internal).card := by
    induction j with
    | zero => simp [specialUseCount]
    | succ j ih =>
      have hj' : j < m := by omega
      have hOld := ih hj'.le
      have hStep := hBalance j hj'
      have hCost := hDebit j hj'
      change cleanup j+(P j).degree v ≤ 2*incident j+
        (if special j = some v then 2 else 0)+(if internal j then 1 else 0) at hCost
      have hCount : specialUseCount special (j+1) v = specialUseCount special j v+
          (if special j = some v then 1 else 0) := by
        rw [specialUseCount,card_filter,sum_range_succ,specialUseCount,card_filter]
      have hInternalCount : ((range (j+1)).filter internal).card =
          ((range j).filter internal).card+(if internal j then 1 else 0) := by
        rw [card_filter,sum_range_succ,card_filter]
      rw [sum_range_succ,hCount,hInternalCount]
      by_cases hs : special j = some v <;> by_cases hc : internal j <;>
        simp only [hs,hc,if_true,if_false] at hCost ⊢ <;> omega
  have hIncident : (∑ i ∈ range m,incident i) ≤ A.card :=
    virtual_incident_deletions_into_le S T P m A v hClean hP hNext
  have hTotal := hTel m le_rfl
  omega

set_option maxHeartbeats 2200000 in
/-- With a fixed singleton, the degree after cleaning bounds the
number of internal charges even when earlier rounds had nonempty cleanup. -/
theorem singleton_prefix_current_exceptional_degree_floor
    (S T P : ℕ → SimpleGraph V) (m floor cap : ℕ)
    (A : Finset V) (w v : V) (hw : w ∈ A) (internal : ℕ → Prop)
    (hClean : ∀ i < m,T i ≤ S i) (hP : ∀ i < m,P i ≤ T i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i))
    (hInitial : floor ≤ (S 0).degree v)
    (hCleanup : ∀ i < m,∀ x,(sdiff (S i) (T i)).Adj v x → x ∈ A)
    (hTwo : ∀ i < m,(P i).degree v ≤ 2)
    (hClass : ∀ i < m,0 < (P i).degree v →
      (P i).Adj w v ∨ (internal i ∧ (P i).degree v = 1))
    (hCharge : ∀ i < m,internal i → (T i).degree w ≤ cap ∧ 1 ≤ (P i).degree w) :
    floor ≤ (S m).degree v+2*A.card+cap := by
  let fuel (i : ℕ) := if i < m then (T i).degree w else (S i).degree w
  have hFuelLe (i : ℕ) : fuel i ≤ (S i).degree w := by
    by_cases hi : i < m
    · rw [show fuel i = (T i).degree w from if_pos hi]
      exact degree_le_of_le (hClean i hi)
    · rw [show fuel i = (S i).degree w from if_neg hi]
  have hFuel (i : ℕ) (hi : i < m) : fuel (i+1)+(P i).degree w ≤ fuel i := by
    have hLayer : (S (i+1)).degree w+(P i).degree w = (T i).degree w := by
      rw [hNext i hi]
      simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le (T i) (P i) (hP i hi) w
    rw [show fuel i = (T i).degree w from if_pos hi,←hLayer]
    exact Nat.add_le_add_right (hFuelLe (i+1)) _
  have hCount := singleton_internal_charge_count_le fuel internal m cap
    (fun i hi => by have h := hFuel i hi; omega)
    (fun i hi h => by
      have hStep := hFuel i hi
      obtain ⟨hSmall,hDrop⟩ := hCharge i hi h
      exact ⟨by rwa [show fuel i = (T i).degree w from if_pos hi],by omega⟩)
  apply current_exceptional_degree_floor_of_charges S T P m floor cap A v (fun _ => none) internal
    hClean hP hNext hInitial (by simp) hCount
  intro i hi
  have hDis : Disjoint (sdiff (S i) (T i)) (P i) := by
    rw [disjoint_iff_inf_le]
    intro x y h
    exact h.1.2 (hP i hi h.2)
  simpa only [reduceCtorEq,if_false,add_zero] using
    exceptional_round_cost_of_classification (sdiff (S i) (T i)) (P i) A v
    (none = some v) (internal i) hDis (hCleanup i hi) (hTwo i hi)
    (fun h => (hClass i hi h).imp (fun he => ⟨w,hw,he.symm⟩) Or.inr)

omit [Fintype V] [DecidableEq V] in
/-- The scalar margin leaves room for all three selection costs:
excluded exceptional vertices, earlier uses and the other new endpoints. -/
theorem cms_projection_margin_after_trimming_losses
    (n D exceptional : ℕ) (η : ℝ) (hη : 0 ≤ η) (hSmall : η ≤ 1/16)
    (hSize : 12 ≤ η*(n:ℝ)) (hD : 24*η*(n:ℝ) ≤ (D:ℝ))
    (hExceptional : (exceptional:ℝ) ≤ η^2*(n:ℝ)) :
    5*exceptional+⌊η*(n:ℝ)⌋₊+4+(4*exceptional+2) ≤ ⌊(D:ℝ)/3-η*(n:ℝ)⌋₊ := by
  have hNonneg : 0 ≤ η*(n:ℝ) := by positivity
  have hCap := Nat.floor_le hNonneg
  have hFew : (exceptional:ℝ) ≤ (η*(n:ℝ))/16 := by
    have hProduct := mul_le_mul_of_nonneg_right hSmall hNonneg
    nlinarith only [hExceptional,hProduct]
  apply Nat.le_floor
  push_cast
  linarith only [hCap,hD,hFew,hSize]

omit [Fintype V] in
/-- The common degree margin suffices for every projection constructor
and for attaching all the retired vertices after that projection. -/
theorem projection_and_spoke_room_of_degree_floor
    (U W B : Finset V) (hW : W ⊆ U) (hB : B ⊆ U)
    (degree floor loss cap : ℕ)
    (hFloor : floor ≤ degree+loss) (hRoom : 5*U.card+cap+4+loss ≤ floor) :
    U.card+4*(W.card+1)+cap ≤ degree ∧
      U.card+(W.card+1)+cap+2*U.card ≤ degree ∧
      U.card+2+cap+2*B.card ≤ degree := by
  have hWC := card_le_card hW
  have hBC := card_le_card hB
  omega

end OverfullWork.CMSTrimmingRound
