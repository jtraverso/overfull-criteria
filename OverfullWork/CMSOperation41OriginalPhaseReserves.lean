module

public import OverfullWork.CMSOperation41CumulativeCleanup
public import OverfullWork.CMSOperation41CriticalTransition

@[expose] public section


/-! The original-active phase uses one finite budget for all cleanup
and one for exceptional vertices' prescribed losses. These estimates
apply to the current prefix before selecting any later round. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph LowSetEdgePreprocessing
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The original active set after cleanup discards the isolated
vertices of the current virtual graph. -/
noncomputable def originalCleanActive (low exceptional : Finset V) (G : SimpleGraph V) : Finset V :=
  (exceptional ∩ low).filter (fun v => 0 < G.degree v)

set_option maxHeartbeats 1800000 in
/-- Successive singletons of the original phase contain the same
vertex. Every internal charge spends an edge from that vertex's
remaining degree, including across intervening cleanup. -/
theorem original_phase_internal_charge_bound (low : Finset V)
    (S T P : ℕ → SimpleGraph V) (U : ℕ → Finset V) (m cap : ℕ) (internal : ℕ → Prop)
    (hClean : ∀ i < m,T i ≤ S i) (hLayer : ∀ i < m,P i ≤ T i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i))
    (hNested : ∀ j < m,∀ i ≤ j,U j ⊆ U i)
    (hCharge : ∀ i < m,internal i →
      ∃ w,originalCleanActive low (U i) (T i) = {w} ∧
        (T i).degree w ≤ cap ∧ 1 ≤ (P i).degree w) :
    ((range m).filter internal).card ≤ cap := by
  have hGraph (i j : ℕ) (hij : i ≤ j) (hj : j < m) : T j ≤ T i := by
    rcases lt_or_eq_of_le hij with hlt | rfl
    · have hSub : S (i+1) ≤ T i := by rw [hNext i (hlt.trans hj)]; exact fun _ _ h => h.1
      exact (hClean j hj).trans ((virtual_trimming_prefix_le S T P m hClean hNext
        (i+1) j (by omega) hj.le).trans hSub)
    · exact le_rfl
  have hActive (i j : ℕ) (hij : i ≤ j) (hj : j < m) :
      originalCleanActive low (U j) (T j) ⊆ originalCleanActive low (U i) (T i) := by
    intro v hv
    obtain ⟨hv₁,hv₂⟩ := mem_filter.mp hv
    obtain ⟨hU,hLow⟩ := mem_inter.mp hv₁
    exact mem_filter.mpr ⟨mem_inter.mpr ⟨hNested j hj i hij hU,hLow⟩,
      hv₂.trans_le (degree_le_of_le (hGraph i j hij hj))⟩
  by_cases hAny : ∃ i < m,internal i
  · obtain ⟨a,ha,hia⟩ := hAny
    obtain ⟨w,hw,_,_⟩ := hCharge a ha hia
    have hSame (i : ℕ) (hi : i < m) (hint : internal i) :
        (T i).degree w ≤ cap ∧ 1 ≤ (P i).degree w := by
      obtain ⟨x,hx,hxCap,hxDrop⟩ := hCharge i hi hint
      have he : x = w := by
        rcases le_total a i with hai | hia'
        · have hSub := hActive a i hai hi
          rw [hw,hx] at hSub
          exact mem_singleton.mp (hSub (mem_singleton_self _))
        · have hSub := hActive i a hia' ha
          rw [hw,hx] at hSub
          exact (mem_singleton.mp (hSub (mem_singleton_self _))).symm
      exact he ▸ ⟨hxCap,hxDrop⟩
    let fuel (i : ℕ) := if i < m then (T i).degree w else (S i).degree w
    have hFuel (i : ℕ) (hi : i < m) : fuel (i+1)+(P i).degree w ≤ fuel i := by
      have hAfter : fuel (i+1) ≤ (S (i+1)).degree w := by
        by_cases h : i+1 < m
        · simpa only [fuel,if_pos h] using (degree_le_of_le (hClean (i+1) h) (v := w))
        · simp only [fuel,if_neg h,Nat.le_refl]
      have hExact : (S (i+1)).degree w+(P i).degree w = (T i).degree w := by
        rw [hNext i hi]
        simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
          MaximumMatching.degree_sdiff_add_of_le (T i) (P i) (hLayer i hi) w
      simpa only [fuel,if_pos hi] using (Nat.add_le_add_right hAfter _).trans_eq hExact
    apply singleton_internal_charge_count_le fuel internal m cap
    · intro i hi
      have h := hFuel i hi
      omega
    · intro i hi hint
      obtain ⟨hc,hd⟩ := hSame i hi hint
      refine ⟨by simpa only [fuel,if_pos hi] using hc,?_⟩
      have h := hFuel i hi
      omega
  · have hEmpty : (range m).filter internal = ∅ := eq_empty_iff_forall_notMem.mpr (by
      intro i hi
      obtain ⟨ha,hb⟩ := mem_filter.mp hi
      exact hAny ⟨i,mem_range.mp ha,hb⟩)
    simp [hEmpty]

set_option maxHeartbeats 3600000 in
/-- Every original-active prefix has enough degree for the next
independent cleanup, and for both the projection and retired-spoke
choices after it. This includes original low vertices which have
already left the exceptional set. -/
theorem original_phase_next_round_reserves (G : SimpleGraph V) [dG : DecidableRel G.Adj]
    (initial low : Finset V) (hLow : low ⊆ initial)
    (S T P : ℕ → SimpleGraph V) (U : ℕ → Finset V) (degree credit : ℕ → V → ℕ)
    (special : ℕ → Option V) (internal : ℕ → V → Prop) (m threshold floor k : ℕ)
    (hStart : S 0 = G) (hInitial : U 0 = initial) (hDegree₀ : degree 0 = fun v => G.degree v)
    (hIndependent : G.IsIndepSet (low : Set V))
    (hClean : ∀ i < m,DeletionRun (U i ∩ low) (S i) (T i))
    (hLayer : ∀ i < m,P i ≤ T i)
    (hNext : ∀ i < m,S (i+1) = sdiff (T i) (P i))
    (hUpdate : ∀ i < m,U (i+1) = nextTrimmingExceptional (U i)
      (univ.filter (fun v => 0 < degree (i+1) v)) (degree (i+1))
      (G.maxDegree-2*(i+1)) threshold)
    (hBalance : ∀ i < m,∀ v,degree (i+1) v+(sdiff (S i) (T i)).degree v+
      (2-credit i v) = degree i v)
    (hExact : ∀ v ∈ initial,degree m v = (S m).degree v)
    (hOrd₀ : ∀ v,v ∉ initial → G.maxDegree ≤ G.degree v+threshold)
    (hFloor₀ : ∀ v ∈ initial,v ∉ low → floor ≤ G.degree v)
    (hSpecial : ∀ i < m,∀ v,special i = some v →
      floor+2 ≤ (S i).degree v ∧ 2 ≤ (P i).degree v)
    (hInternal : ∀ i < m,∀ v,internal i v →
      ∃ w,originalCleanActive low (U i) (T i) = {w} ∧
        (T i).degree w < (U i).card+2 ∧ 1 ≤ (P i).degree w)
    (hPay : ∀ i < m,∀ v ∈ U i,v ∉ low → 0 < (T i).degree v →
      (sdiff (S i) (T i)).degree v+(P i).degree v ≤
        2*(((sdiff (S i) (T i)) ⊔ P i).neighborFinset v ∩ low).card+
          (if special i = some v then 2 else 0)+(if internal i v then 1 else 0))
    (hMargin : 5*initial.card+k+4+(4*initial.card+2) ≤ floor)
    (hRange : floor+threshold+low.card ≤ G.maxDegree-2*m) :
    (∀ v,v ∉ initial → (U m ∩ low).card+2 ≤ degree m v) ∧
    ∀ v ∈ initial,v ∉ U m ∩ low → 0 < (S m).degree v →
      5*initial.card+k+4+(U m ∩ low).card ≤ (S m).degree v ∧
      floor ≤ (S m).degree v+2*low.card+initial.card+1 := by
  cases Subsingleton.elim dG (fun u v => Classical.propDecidable (G.Adj u v))
  let D := G.maxDegree
  let loss (i : ℕ) (v : V) := (sdiff (S i) (T i)).degree v
  let support (i : ℕ) := univ.filter (fun v => 0 < degree i v)
  have hCleanLe (i : ℕ) (hi : i < m) := DeletionRun.le_source (hClean i hi)
  have hNextLe (i : ℕ) (hi : i < m) : S (i+1) ≤ T i := by
    rw [hNext i hi]
    exact fun _ _ h => h.1
  have hNested := trimming_exceptional_sets_antitone U support degree D threshold m hUpdate
  have hU (i : ℕ) (hi : i ≤ m) : U i ⊆ initial := hInitial ▸ hNested i hi 0 (Nat.zero_le _)
  have hWC : (U m ∩ low).card ≤ low.card := card_le_card inter_subset_right
  have hW := card_le_card hLow
  have hSum (v : V) : (∑ i ∈ range m,loss i v) ≤ low.card := by
    rw [←Fin.sum_univ_eq_sum_range (fun i => loss i v) m]
    exact cumulative_cleanup_degree_le_original_low_card G low S T (fun i => U i ∩ low) m
      hStart hIndependent hClean (fun _ _ => Or.inl inter_subset_right) hNextLe m le_rfl v
  have hTotal (i : ℕ) (hi : i ≤ m) (v : V) :
      degree 0 v ≤ degree i v+2*i+(∑ j ∈ range i,loss j v) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hi' : i < m := by omega
      have h := ih hi'.le
      have hn := hBalance i hi' v
      rw [sum_range_succ]
      change degree (i+1) v+loss i v+(2-credit i v) = degree i v at hn
      omega
  have hCore (v : V) (hv : v ∉ initial) : (U m ∩ low).card+2 ≤ degree m v := by
    have hFirst := hOrd₀ v hv
    have hT := hTotal m le_rfl v
    rw [hDegree₀] at hT
    change G.degree v ≤ degree m v+2*m+(∑ j ∈ range m,loss j v) at hT
    have hS := hSum v
    change floor+threshold+low.card ≤ D-2*m at hRange
    change D ≤ G.degree v+threshold at hFirst
    omega
  refine ⟨hCore,?_⟩
  have hSupport (i : ℕ) (hi : i < m) : support (i+1) ⊆ support i := by
    intro v hv
    obtain ⟨_,hp⟩ := mem_filter.mp hv
    have h := hBalance i hi v
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hOrd := nonexceptional_degree_from_update_history D m threshold U support degree loss
    (by intro v _ hv; rw [hInitial] at hv; rw [hDegree₀]; exact hOrd₀ v hv)
    hSupport hUpdate
    (fun i hi v _ _ => by
      have h := hBalance i hi v
      change degree (i+1) v+loss i v+(2-credit i v) = degree i v at h
      omega)
    (by change floor+threshold+low.card ≤ D-2*m at hRange; omega)
  intro v hv hvW hp
  by_cases hvU : v ∈ U m
  · have hn : v ∉ low := fun h => hvW (mem_inter.mpr ⟨hvU,h⟩)
    have hCount := original_phase_internal_charge_bound low S T P U m (initial.card+1)
      (fun i => internal i v) hCleanLe hLayer hNext
      (fun j hj i hi => hNested j hj.le i hi) (by
        intro i hi hint
        obtain ⟨w,hw,hSmall,hDrop⟩ := hInternal i hi v hint
        have hSize := card_le_card (hU i hi.le)
        exact ⟨w,hw,by omega,hDrop⟩)
    have hPreserve := current_exceptional_degree_floor_of_charges S T P m floor
      (initial.card+1) low v special (fun i => internal i v) hCleanLe hLayer hNext
      (by rw [hStart]; exact hFloor₀ v hv hn)
      (fun i hi => hSpecial i hi v) hCount (by
        intro i hi
        have hLe : S m ≤ T i := (virtual_trimming_prefix_le S T P m hCleanLe hNext
          (i+1) m (by omega) le_rfl).trans (hNextLe i hi)
        exact hPay i hi v (hNested m le_rfl i hi.le hvU) hn
          (hp.trans_le (degree_le_of_le hLe)))
    exact ⟨by omega,by omega⟩
  · have hPos : v ∈ support m := mem_filter.mpr ⟨mem_univ _,hExact v hv ▸ hp⟩
    have hBound := hOrd m le_rfl v hPos hvU
    rw [hExact v hv] at hBound
    have hS := hSum v
    change floor+threshold+low.card ≤ D-2*m at hRange
    exact ⟨by omega,by omega⟩

end OverfullWork.CMSTrimmingRound
