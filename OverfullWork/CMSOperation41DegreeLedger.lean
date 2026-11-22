module

public import OverfullWork.CMSOperation41CriticalChoice
public import OverfullWork.MaximumMatchingPeeling
public import OverfullWork.CMSOperation41Invariants

@[expose] public section


/-! The bookkeeping of Operation 4.1 distinguishes actual
preprocessing losses from the projected two-colour layer. Both
contribute to the degree record, including at vertices of the core. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem synchronous_layer_preserves_incidence
    (G H P Q : SimpleGraph V) (A : Finset V)
    (hSource : ∀ v ∈ A,∀ u,G.Adj v u ↔ H.Adj v u)
    (hPrescribed : ∀ v ∈ A,∀ u,P.Adj v u ↔ Q.Adj v u) :
    ∀ v ∈ A,∀ u,(G \ P).Adj v u ↔ (H \ Q).Adj v u := by
  intro v hv u
  change G.Adj v u ∧ ¬P.Adj v u ↔ H.Adj v u ∧ ¬Q.Adj v u
  rw [hSource v hv u,hPrescribed v hv u]

theorem physical_trim_degree_balance (H R Q : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel R.Adj] [DecidableRel Q.Adj]
    (hR : R ≤ H) (hQ : Q ≤ H \ R) (v : V) :
    ((H \ R) \ Q).degree v + Q.degree v + R.degree v = H.degree v := by
  rw [MaximumMatching.degree_sdiff_add_of_le (H \ R) Q hQ v,
    MaximumMatching.degree_sdiff_add_of_le H R hR v]

theorem core_degree_deficit_step (d d' D D' residual layer credit : ℕ)
    (hMaximum : D'+2 = D) (hDegree : d'+layer+residual = d)
    (hCharge : layer+credit = 2)
    (hBound : d ≤ D) (hBound' : d' ≤ D') :
    (D'-d')+credit = (D-d)+residual := by
  omega

theorem core_charge_budget_identity
    (deficit loss credit : ℕ → ℕ) (rounds : ℕ)
    (hStep : ∀ i < rounds,deficit (i+1)+credit i = deficit i+loss i) :
    (∑ i ∈ range rounds,credit i)+deficit rounds =
      deficit 0+(∑ i ∈ range rounds,loss i) := by
  have hSum (r : ℕ) (hr : r ≤ rounds) :
      (∑ i ∈ range r,credit i)+deficit r = deficit 0+(∑ i ∈ range r,loss i) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [sum_range_succ,sum_range_succ]
      have hPrev := ih (by omega)
      have h := hStep r (by omega)
      omega
  exact hSum rounds le_rfl

theorem almost_overfull_score_correction (active X : Finset V) (hX : X ⊆ active)
    (D : ℕ) (actual reference loss : V → ℕ)
    (hRef : ∀ v ∈ active,reference v = actual v+loss v)
    (hBound : ∀ v ∈ X,reference v ≤ D) :
    (∑ v ∈ X,(D-actual v))+(∑ v ∈ active \ X,actual v)+(∑ v ∈ active \ X,loss v) =
      (∑ v ∈ X,(D-reference v))+(∑ v ∈ active \ X,reference v)+(∑ v ∈ X,loss v) := by
  have hInside : (∑ v ∈ X,(D-actual v)) =
      (∑ v ∈ X,(D-reference v))+(∑ v ∈ X,loss v) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    have h := hRef v (hX hv)
    have hh := hBound v hv
    omega
  have hOutside : (∑ v ∈ active \ X,reference v) =
      (∑ v ∈ active \ X,actual v)+(∑ v ∈ active \ X,loss v) := by
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun v hv => hRef v (mem_sdiff.mp hv).1)
  rw [hInside,hOutside]
  ac_rfl

theorem preprocessed_degree_loss_le_cut {I : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (rounds : Finset I)
    (removed : I → SimpleGraph V) (W : Finset V) (v : V) (hv : v ∉ W)
    (hOrig : ∀ i ∈ rounds,removed i ≤ G)
    (hCross : ∀ i ∈ rounds,∀ u z,(removed i).Adj u z → u ∈ W ∨ z ∈ W)
    (hDis : ∀ i ∈ rounds,∀ j ∈ rounds,i ≠ j → Disjoint (removed i) (removed j)) :
    (∑ i ∈ rounds,(removed i).degree v) ≤ PrunedCore.neighboursIn G W v := by
  let N (i : I) := (removed i).neighborFinset v
  have hUnion : rounds.biUnion N ⊆ (G.neighborFinset v).filter (fun u => u ∈ W) := by
    intro u hu
    obtain ⟨i,hi,hu⟩ := mem_biUnion.mp hu
    have h := (mem_neighborFinset _ _ _).mp hu
    exact mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr (hOrig i hi h),
      (hCross i hi _ _ h).resolve_left hv⟩
  have hLe := card_le_card hUnion
  rw [card_biUnion (fun i hi j hj hij => disjoint_neighborFinset_of_disjoint
    (removed i) (removed j) v (hDis i hi j hj hij))] at hLe
  simpa only [N,card_neighborFinset_eq_degree,PrunedCore.neighboursIn] using hLe

theorem degree_floor_with_guarded_special_losses (d ordinary special : ℕ → ℕ)
    (m r : ℕ) (hFirst : m ≤ d 0)
    (hStep : ∀ i < r,d (i+1)+ordinary i+special i = d i)
    (hGuard : ∀ i < r,0 < special i → m+special i ≤ d i) :
    m ≤ d r+(∑ i ∈ range r,ordinary i) := by
  have hBound (k : ℕ) (hk : k ≤ r) : m ≤ d k+(∑ i ∈ range k,ordinary i) := by
    induction k with
    | zero => simpa using hFirst
    | succ k ih =>
      have hPrev := ih (by omega)
      have h := hStep k (by omega)
      rw [sum_range_succ]
      by_cases hp : 0 < special k
      · have hb := hGuard k (by omega) hp
        omega
      · omega
  exact hBound r le_rfl

theorem active_degree_record_excludes_almost (G : SimpleGraph V) [DecidableRel G.Adj]
    (active : Finset V) (degree : V → ℕ) (budget : ℕ)
    (hPositive : ∀ v,0 < G.degree v → v ∈ active)
    (hRecord : ∀ v ∈ active,degree v = G.degree v)
    (hNo : ¬HasAlmostOverfullRecord active G.maxDegree budget degree) :
    ∀ X : Finset V,Odd X.card → (∀ v ∈ X,0 < G.degree v) →
      OddCutDeficit.deficitMass G G.maxDegree X+(∑ v ∈ Xᶜ,G.degree v) ≤ G.maxDegree+budget → False := by
  intro X hOdd hPos hBound
  have hX : X ⊆ active := fun v hv => hPositive v (hPos v hv)
  apply hNo
  refine ⟨X,hX,hOdd,?_⟩
  have hOuter : (∑ v ∈ active \ X, G.degree v) = ∑ v ∈ Xᶜ,G.degree v := by
    have hSub : active \ X ⊆ Xᶜ := fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2
    apply sum_subset hSub
    intro v hv ho
    by_contra hh
    have hp : 0 < G.degree v := Nat.pos_of_ne_zero hh
    exact ho (mem_sdiff.mpr ⟨hPositive v hp,mem_compl.mp hv⟩)
  rw [sum_congr rfl (fun v hv => by rw [hRecord v (hX hv)]),
    sum_congr rfl (fun v hv => hRecord v (mem_sdiff.mp hv).1),hOuter]
  exact hBound

theorem no_overfull_after_clean_and_trim_of_active_records (G H L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel L.Adj]
    (active E : Finset V) (degree : V → ℕ) (r t b c a M : ℕ) :
    let R := H \ L
    let d := G.maxDegree
    H ≤ G → H.maxDegree = d → 2 ≤ d → L ≤ H →
    R.maxDegree = d-2 → (∀ v,L.degree v ≤ 2) → (∑ v,(2-L.degree v)) ≤ M →
    (∀ v,G.degree v ≤ R.degree v+c) →
    RobustExpansion.IsRobustAt R r t → t+2 ≤ d → d ≤ r*r →
    (∀ u v,G.Adj u v → d-b ≤ G.degree u+G.degree v) →
    (∀ v,v ∉ E → d ≤ G.degree v+a) →
    3*b+6*(t+c) ≤ d → 2*a+2*(t+c) ≤ d →
    (∀ v,0 < G.degree v → v ∈ active) →
    (∀ v ∈ active,degree v = G.degree v) →
    ¬HasAlmostOverfullRecord active d (M+4*(E.card+1)) degree →
    ¬R.HasOverfullSubgraph := by
  intro _ _ hGH hHD hD hLH hRD hTwo hMissing hLoss hRob hT hRate hWeak hOrd
    hMargin hOrdMargin hActive hExact hNo
  exact no_overfull_after_clean_and_trim_on_support G H L E r t b c a M
    hGH hHD hD hLH hRD hTwo hMissing hLoss hRob hT hRate hWeak hOrd hMargin hOrdMargin
    (active_degree_record_excludes_almost G active degree _ hActive hExact hNo)

end OverfullWork.CMSTrimmingRound
