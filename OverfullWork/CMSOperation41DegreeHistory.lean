module

public import OverfullWork.CMSOperation41RetiredDegrees
public import OverfullWork.CMSOperation41PreprocessingLoss

@[expose] public section


/-! In Step 4 the exceptional set can only shrink. The floor for
special vertices is paid by their last two-edge charge. For Claim 4.2(3)
the first cleanup at a surviving low endpoint supplies a degree upper
bound at the beginning of that cleanup. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Step 4 with the real threshold represented by its natural ceiling. -/
def nextTrimmingExceptional (U active : Finset V) (degree : V → ℕ) (d threshold : ℕ) : Finset V :=
  (U ∩ active).filter (fun v => threshold ≤ d-degree v)

omit [Fintype V] in
theorem trimming_exceptional_sets_antitone (U active : ℕ → Finset V) (degree : ℕ → V → ℕ)
    (D threshold m : ℕ)
    (hUpdate : ∀ i < m,U (i+1) = nextTrimmingExceptional (U i) (active (i+1))
      (degree (i+1)) (D-2*(i+1)) threshold) :
    ∀ j ≤ m,∀ i ≤ j,U j ⊆ U i := by
  intro j hj
  induction j with
  | zero =>
    intro i hi
    have he : i = 0 := by omega
    subst i
    exact Subset.rfl
  | succ j ih =>
    intro i hi
    have hj' : j < m := by omega
    by_cases hSame : i = j+1
    · subst i; exact Subset.rfl
    have hSub : U (j+1) ⊆ U j := by
      rw [hUpdate j hj']
      exact (filter_subset _ _).trans inter_subset_left
    exact hSub.trans (ih hj'.le i (by omega))

omit [Fintype V] in
theorem nonexceptional_degree_from_update_history (D m a : ℕ)
    (U active : ℕ → Finset V) (degree loss : ℕ → V → ℕ)
    (hFirst : ∀ v ∈ active 0,v ∉ U 0 → D ≤ degree 0 v+a)
    (hActive : ∀ i < m,active (i+1) ⊆ active i)
    (hUpdate : ∀ i < m,U (i+1) = nextTrimmingExceptional (U i) (active (i+1))
      (degree (i+1)) (D-2*(i+1)) a)
    (hStep : ∀ i < m,∀ v ∈ active (i+1),v ∉ U i →
      degree i v ≤ degree (i+1) v+(2+loss i v))
    (hRoom : 2*m ≤ D) :
    ∀ j ≤ m,∀ v ∈ active j,v ∉ U j →
      D-2*j ≤ degree j v+a+(∑ i ∈ range j,loss i v) := by
  apply retired_degree_bound_from_trimming_history D m a U active degree loss
    hFirst hActive _ hStep hRoom
  intro i hi v hv hU hn
  have hDef : ¬a ≤ D-2*(i+1)-degree (i+1) v := by
    intro h
    exact hn (by rw [hUpdate i hi]; exact mem_filter.mpr ⟨mem_inter.mpr ⟨hU,hv⟩,h⟩)
  omega

omit [Fintype V] in
/-- The original ordinary support survives every virtual prefix as long
as the total possible deletions fit below its initial degree. -/
theorem initial_core_positive_from_update_history
    (D m threshold budget : ℕ) (U : Finset V) (degree cleaned loss credit : ℕ → V → ℕ)
    (hStart : ∀ v,v ∉ U → D ≤ degree 0 v+threshold)
    (hNext : ∀ i < m,∀ v,degree (i+1) v+loss i v+(2-credit i v) = degree i v)
    (hClean : ∀ i ≤ m,∀ v,cleaned i v+loss i v = degree i v)
    (hBudget : ∀ v,∑ i ∈ range (m+1),loss i v ≤ budget)
    (hMargin : 2*m+threshold+budget < D) :
    ∀ j ≤ m,∀ v,v ∉ U → 0 < cleaned j v ∧ D-2*j ≤ cleaned j v+threshold+budget := by
  intro j hj v hv
  have hPrefix (i : ℕ) (hi : i ≤ m) :
      degree 0 v ≤ degree i v+2*i+(∑ k ∈ range i,loss k v) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hi' : i < m := by omega
      have hBefore := ih hi'.le
      have hAfter := hNext i hi' v
      rw [sum_range_succ]
      omega
  have hBound := hPrefix j hj
  have hCleaned := hClean j hj v
  have hSpent : (∑ k ∈ range j,loss k v)+loss j v ≤ budget := by
    rw [←sum_range_succ]
    exact (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ hj))
      (fun i _ _ => Nat.zero_le (loss i v))).trans (hBudget v)
  have hInitial := hStart v hv
  omega

/-- The post-cleanup estimate for all ordinary vertices. The same
argument accepts an extra cleanup loss when the inherited singleton
has its last edge removed. -/
theorem nonexceptional_degree_after_bounded_cleanup
    (D m threshold budget : ℕ) (U : ℕ → Finset V)
    (degree cleaned loss credit : ℕ → V → ℕ)
    (hFirst : ∀ v,0 < degree 0 v → v ∉ U 0 → D ≤ degree 0 v+threshold)
    (hUpdate : ∀ i < m,U (i+1) = nextTrimmingExceptional (U i)
      (univ.filter (fun v => 0 < degree (i+1) v)) (degree (i+1)) (D-2*(i+1)) threshold)
    (hRound : ∀ i < m,∀ v,degree (i+1) v+loss i v+(2-credit i v) = degree i v)
    (hClean : ∀ i < m,∀ v,cleaned i v+loss i v = degree i v)
    (hBudget : ∀ v,∑ i ∈ range m,loss i v ≤ budget)
    (hRoom : 2*m ≤ D) :
    ∀ j < m,∀ v,0 < cleaned j v → v ∉ U j →
      D-2*j ≤ cleaned j v+threshold+budget := by
  let active (i : ℕ) := (univ : Finset V).filter (fun v => 0 < degree i v)
  have hPositive (i : ℕ) (v : V) : v ∈ active i ↔ 0 < degree i v := by simp [active]
  have hActive (i : ℕ) (hi : i < m) : active (i+1) ⊆ active i := by
    intro v hv
    rw [hPositive] at hv ⊢
    have h := hRound i hi v
    omega
  have hStep (i : ℕ) (hi : i < m) (v : V) :
      degree i v ≤ degree (i+1) v+(2+loss i v) := by
    have h := hRound i hi v
    omega
  have hOrd := nonexceptional_degree_from_update_history D m threshold U active degree loss
    (fun v hv hu => hFirst v ((hPositive _ _).mp hv) hu) hActive hUpdate
    (fun i hi v _ _ => hStep i hi v) hRoom
  intro j hj v hv hU
  have hD := hClean j hj v
  have hBound := hOrd j hj.le v ((hPositive j v).mpr (by omega)) hU
  have hSpent : (∑ k ∈ range j,loss k v)+loss j v ≤ budget := by
    rw [←sum_range_succ]
    exact (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_iff.mpr hj))
      (fun i _ _ => Nat.zero_le (loss i v))).trans (hBudget v)
  omega

omit [Fintype V] in
private theorem special_use_succ (special : ℕ → Option V) (j : ℕ) (v : V) :
    specialUseCount special (j+1) v = specialUseCount special j v +
      if special j = some v then 1 else 0 := by
  rw [specialUseCount,card_filter,sum_range_succ,specialUseCount,card_filter]

omit [Fintype V] in
theorem special_use_preserves_initial_floor (degree : ℕ → V → ℕ) (special : ℕ → Option V)
    (m floor : ℕ) (v : V) (hInit : floor ≤ degree 0 v)
    (hMono : ∀ i < m,degree (i+1) v ≤ degree i v)
    (hSpecial : ∀ i < m,special i = some v →
      floor+2 ≤ degree i v ∧ degree (i+1) v+2 ≤ degree i v) :
    ∀ j ≤ m,floor+2*specialUseCount special j v ≤ degree 0 v := by
  have hBoth : ∀ j ≤ m,
      degree j v+2*specialUseCount special j v ≤ degree 0 v ∧
      floor+2*specialUseCount special j v ≤ degree 0 v := by
    intro j hj
    induction j with
    | zero => simpa [specialUseCount] using hInit
    | succ j ih =>
      have hj' : j < m := by omega
      obtain ⟨hCount,hFloor⟩ := ih hj'.le
      have hFall := hMono j hj'
      rw [special_use_succ]
      by_cases h : special j = some v
      · obtain ⟨h₁,h₂⟩ := hSpecial j hj' h
        simp only [if_pos h]
        omega
      · simp only [if_neg h,add_zero]
        omega
  exact fun j hj => (hBoth j hj).2

/-- At the first round which removes an edge incident with the low
endpoint, the pre-cleanup degree there is at most the active-set size. -/
theorem active_degree_le_of_incident_cleanup {G H : SimpleGraph V} [DecidableRel G.Adj]
    {W : Finset V} (p : DeletionRun W G H) (hInd : G.IsIndepSet (W : Set V))
    {v x : V} (hv : v ∈ W) (hBefore : G.Adj v x) (hAfter : ¬H.Adj v x) :
    G.degree v ≤ W.card := by
  by_contra! hLarge
  exact hAfter ((independent_high_active_incidence_of_preprocessing p hInd v hv hLarge x).mpr hBefore)

/-- Claim 4.2(3), mixed edge with a first cleanup at the active endpoint.
The other endpoint carries the degree it had before that cleanup, after
paying two per remaining round and its additional loss budget. -/
theorem weak_degree_sum_after_first_active_cleanup
    {G H Q : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel Q.Adj]
    {W : Finset V} (p : DeletionRun W G H) (hInd : G.IsIndepSet (W : Set V))
    {u v x : V} (hv : v ∈ W) (hx : G.Adj v x) (hx' : ¬H.Adj v x)
    (hEdge : Q.Adj u v) (d k j c a : ℕ)
    (hBefore : d+2*(j-k) ≤ G.degree u+G.degree v+a)
    (hAfter : G.degree u ≤ Q.degree u+2*(j-k)+c) :
    d+1 ≤ Q.degree u+Q.degree v+(a+W.card+c) := by
  have hSmall := active_degree_le_of_incident_cleanup p hInd hv hx hx'
  have hPos := (Q.degree_pos_iff_exists_adj v).mpr ⟨u,hEdge.symm⟩
  omega

omit [Fintype V] [DecidableEq V] in
theorem weak_degree_sum_of_inherited_active_pair (degree : ℕ → V → ℕ)
    (D start last a : ℕ) (u v : V) (hPos : start ≤ last) (hRoom : 2*last ≤ D)
    (hStart : D-2*start ≤ degree start u+degree start v+a)
    (hU : ∀ i,start ≤ i → i < last → degree i u ≤ degree (i+1) u+1)
    (hV : ∀ i,start ≤ i → i < last → degree i v ≤ degree (i+1) v+1) :
    D-2*last ≤ degree last u+degree last v+a := by
  have hKeep : ∀ i ≤ last,start ≤ i → D-2*i ≤ degree i u+degree i v+a := by
    intro i hi
    induction i with
    | zero =>
      intro he
      have h : start = 0 := by omega
      simpa [h] using hStart
    | succ i ih =>
      intro hLower
      by_cases hEq : start = i+1
      · simpa only [hEq] using hStart
      have hi' : i < last := by omega
      have hLe : start ≤ i := by omega
      have h := ih hi'.le hLe
      have h₁ := hU i hLe hi'
      have h₂ := hV i hLe hi'
      omega
  exact hKeep last le_rfl hPos

end OverfullWork.CMSTrimmingRound
