module

public import OverfullWork.CMSOperation41DegreeRecords
public import OverfullWork.CMSRegularizationOddCuts
public import OverfullWork.AlmostOverfullLayerCompatibility
public import OverfullWork.AlmostOverfullOriginalGeometry
public import OverfullWork.TwoColourTrimming

@[expose] public section


/-! Class 2 and odd-set compatibility for a realized CMS trimming
round, with the actual cleanup and layer losses kept explicit. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph RobustExpansion PrunedCore OddCutDeficit NearTightOddSetGeometry
open AlmostOverfullLayerCompatibility
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem realized_layer_preserves_class_two (H L : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel L.Adj] (hD : 2 ≤ H.maxDegree)
    (hU : ¬H.EdgeColorable H.maxDegree) (hLe : L ≤ H)
    (hTwo : L.EdgeColorable 2) (hDeg : ∀ v,L.degree v ≤ 2)
    (hDemand : ∀ v,H.degree v+2 ≤ H.maxDegree+L.degree v) :
    (H \ L).maxDegree = H.maxDegree-2 ∧ ¬(H \ L).EdgeColorable (H \ L).maxDegree := by
  have hMax := TwoColourTrimming.maxDegree_sdiff_of_degree_demands H L hD hLe hDeg hDemand
  refine ⟨hMax,?_⟩
  rw [hMax]
  exact fun h => hU (TwoColourTrimming.colourable_of_two_colour_residue H L hD hLe hTwo h)

theorem selected_degrees_le_cut_add_of_loss (G R : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel R.Adj] (X A : Finset V) (hA : A ⊆ Xᶜ) (c : ℕ)
    (hLoss : ∀ v,G.degree v ≤ R.degree v+c) :
    (∑ v ∈ A,G.degree v) ≤ cutEdges R X+A.card*(Xᶜ.card+c) := by
  have hRow (v : V) (hv : v ∈ A) : G.degree v ≤ neighboursIn R X v+(Xᶜ.card+c) := by
    have h := TrimmingResidualOddGeometry.degree_add_one_le_boundary_add_complement R X v (hA hv)
    have hv := hLoss v
    omega
  have hCut := MaximumOddCutPacking.cut_eq_sum_neighboursIn R X Xᶜ disjoint_compl_right
    (fun _ _ v _ => by by_cases hv : v ∈ X <;> simp_all)
  calc
    _ ≤ ∑ v ∈ A,(neighboursIn R X v+(Xᶜ.card+c)) := sum_le_sum hRow
    _ = (∑ v ∈ A,neighboursIn R X v)+A.card*(Xᶜ.card+c) := by rw [sum_add_distrib]; simp
    _ ≤ _ := by
      rw [hCut]
      exact Nat.add_le_add_right (sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => Nat.zero_le _)) _

set_option maxHeartbeats 2200000 in
theorem no_overfull_after_clean_and_trim_on_support (G H L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel L.Adj]
    (E : Finset V) (r t b c a M : ℕ) :
    let R := H \ L
    let d := G.maxDegree
    H ≤ G → H.maxDegree = d → 2 ≤ d → L ≤ H →
    R.maxDegree = d-2 → (∀ v,L.degree v ≤ 2) → (∑ v,(2-L.degree v)) ≤ M →
    (∀ v,G.degree v ≤ R.degree v+c) →
    IsRobustAt R r t → t+2 ≤ d → d ≤ r*r →
    (∀ u v,G.Adj u v → d-b ≤ G.degree u+G.degree v) →
    (∀ v,v ∉ E → d ≤ G.degree v+a) →
    3*b+6*(t+c) ≤ d → 2*a+2*(t+c) ≤ d →
    (∀ X : Finset V,Odd X.card → (∀ v ∈ X,0 < G.degree v) →
      deficitMass G d X+(∑ v ∈ Xᶜ,G.degree v) ≤ d+(M+4*(E.card+1)) → False) →
    ¬R.HasOverfullSubgraph := by
  intro R d hGH hHD hD hLH hRD hTwo hMissing hLoss hRob hT hRate hWeak hOrd hMargin hOrdMargin hNo
  apply (no_overfull_iff_odd_cut_deficit R).mpr
  intro X hOdd
  by_contra! hCutDef
  have hCut : cutEdges R X+3 ≤ d := by omega
  have hOF : (d-2)*(X.card/2) < internalEdges R X := by
    rw [←hRD]
    apply not_le.mp
    exact fun hh => (Nat.not_le_of_lt hCutDef)
      ((odd_internal_bound_iff_cut_deficit R R.maxDegree R.degree_le_maxDegree X hOdd).mp hh)
  have hSize : d ≤ X.card+1 := by
    have hh := ResidualOverfullLocalization.degree_le_overfull_card_add_one H L (by omega) X (by exact hOdd)
      (by rw [hHD]; exact hOF)
    omega
  have hShort : Xᶜ.card < t := by
    by_contra! ht
    let P := MultiGraph.ofSimpleGraph R
    have hSupport : P.supportGraph = R := by
      ext u v
      change 0 < (if s(u,v) ∈ R.edgeSet then 1 else 0) ↔ R.Adj u v
      by_cases h : s(u,v) ∈ R.edgeSet
      · rw [if_pos h]
        exact ⟨fun _ => R.mem_edgeSet.mp h,fun _ => by decide⟩
      · rw [if_neg h]
        exact ⟨fun h' => (Nat.lt_irrefl 0 h').elim,fun h' => (h (R.mem_edgeSet.mpr h')).elim⟩
    have hCnt := card_add_card_compl X
    have hRobP : IsRobustAt P.supportGraph r t := by
      intro S hLo hHi
      have hN : neighbourhood P.supportGraph r S = neighbourhood R r S := by
        ext v
        simp only [neighbourhood,mem_filter,mem_univ,true_and,neighboursIn_eq_filter_card]
        have hEq : S.filter (P.supportGraph.Adj v) = S.filter (R.Adj v) := by
          apply filter_congr
          intro w _
          exact Iff.of_eq (congrArg (fun Q : SimpleGraph V => Q.Adj v w) hSupport)
        rw [hEq]
      rw [hN]
      exact hRob S hLo hHi
    have hh := CanonicalRegularization.robust_cut_lower P X r t hRobP (by omega) (by omega)
    rw [←cutEdges_eq_multigraph] at hh
    omega
  have hSelected (T : Finset V) (hT' : T ⊆ Xᶜ) :
      (∑ v ∈ T,G.degree v) ≤ cutEdges R X+T.card*(t+c) := by
    have hh := selected_degrees_le_cut_add_of_loss G R X T hT' c hLoss
    have h := Nat.mul_le_mul_left T.card (show Xᶜ.card+c ≤ t+c by omega)
    omega
  have hIntersect : ∀ u ∈ Xᶜ, ∀ v ∈ Xᶜ, ∀ w ∈ Xᶜ, ∀ z ∈ Xᶜ,
      G.Adj u v → G.Adj w z → u = w ∨ u = z ∨ v = w ∨ v = z := by
    intro u hu v hv w hw z hz huv hwz
    by_contra! hNe
    let T : Finset V := {u,v,w,z}
    have hTS : T ⊆ Xᶜ := insert_subset hu (insert_subset hv (insert_subset hw (singleton_subset_iff.mpr hz)))
    have hCount : T.card = 4 := by simp [T,huv.ne,hwz.ne,hNe.1,hNe.2.1,hNe.2.2.1,hNe.2.2.2]
    have hSum : (∑ x ∈ T,G.degree x) = G.degree u+G.degree v+G.degree w+G.degree z := by
      simp [T,huv.ne,hwz.ne,hNe.1,hNe.2.1,hNe.2.2.1,hNe.2.2.2,Nat.add_assoc]
    have hh := hSelected T hTS
    rw [hSum,hCount] at hh
    have h₁ := hWeak u v huv
    have h₂ := hWeak w z hwz
    omega
  have hTriangle : ∀ u ∈ Xᶜ, ∀ v ∈ Xᶜ, ∀ w ∈ Xᶜ,
      G.Adj u v → G.Adj v w → G.Adj w u → False := by
    intro u hu v hv w hw huv hvw hwu
    let T : Finset V := {u,v,w}
    have hTS : T ⊆ Xᶜ := insert_subset hu (insert_subset hv (singleton_subset_iff.mpr hw))
    have hCount : T.card = 3 := by simp [T,huv.ne,hvw.ne,hwu.ne.symm]
    have hSum : (∑ x ∈ T,G.degree x) = G.degree u+G.degree v+G.degree w := by
      simp [T,huv.ne,hvw.ne,hwu.ne.symm,Nat.add_assoc]
    have hh := hSelected T hTS
    rw [hSum,hCount] at hh
    have h₁ := hWeak u v huv
    have h₂ := hWeak v w hvw
    have h₃ := hWeak w u hwu
    omega
  have hStar : Xᶜ = ∅ ∨ ∃ v ∈ Xᶜ, ∀ u ∈ Xᶜ, ∀ w ∈ Xᶜ, G.Adj u w → u = v ∨ w = v := by
    rcases Xᶜ.eq_empty_or_nonempty with h | h
    · exact Or.inl h
    · exact Or.inr (TrimmingResidualOddGeometry.exists_common_incident_of_no_independent_no_triangle
        G Xᶜ h hIntersect hTriangle)
  have hComplement : Xᶜ.card ≤ E.card+1 := by
    have hOne : (Xᶜ \ E).card ≤ 1 := by
      apply card_le_one.mpr
      intro u hu v hv
      by_contra hn
      have hT' : ({u,v}:Finset V) ⊆ Xᶜ :=
        insert_subset (mem_sdiff.mp hu).1 (singleton_subset_iff.mpr (mem_sdiff.mp hv).1)
      have hh := hSelected _ hT'
      rw [sum_pair hn,card_pair hn] at hh
      have h₁ := hOrd u (mem_sdiff.mp hu).2
      have h₂ := hOrd v (mem_sdiff.mp hv).2
      omega
    have hSplit := card_le_card_sdiff_add_card (s := Xᶜ) (t := E)
    omega
  have hOriginal : internalEdges H X ≤ internalEdges G X := by
    apply card_le_card
    intro e he
    obtain ⟨hE,hS⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_edgeFinset.mpr (edgeSet_mono hGH (mem_edgeFinset.mp hE)),hS⟩
  have hGDef := internal_cut_deficit_identity G d G.degree_le_maxDegree X
  have hHDef := internal_cut_deficit_identity H d (fun v => hHD ▸ H.degree_le_maxDegree v) X
  have hDef := deficitMass_eq_after_layer H L hLH (by omega) (by exact hTwo)
    (fun v => by rw [hHD,←hRD]; exact R.degree_le_maxDegree v) X
  rw [hHD,←hRD] at hDef
  have hMissingX : (∑ v ∈ X, (2-L.degree v)) ≤ M :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans hMissing
  change deficitMass H d X = deficitMass R R.maxDegree X + (∑ v ∈ X, (2-L.degree v)) at hDef
  have hCutH := cutEdges_eq_residue_add_layer H L hLH X
  change cutEdges H X = cutEdges R X+cutEdges L X at hCutH
  have hLCut := cutEdges_layer_le_twice_complement L hTwo X
  have hStarBound := internalEdges_le_card_of_star G Xᶜ hStar
  have hBudget := AlmostOverfullOriginalGeometry.budget_eq_cut_deficit_add_internal G X
  have hActive (v : V) (hv : v ∈ X) : 0 < G.degree v := by
    have hPos : 0 < R.degree v := by
      by_contra! hn
      have hz : R.degree v = 0 := by omega
      have hOne : R.maxDegree-R.degree v ≤ ∑ u ∈ X,(R.maxDegree-R.degree u) :=
        single_le_sum (fun u _ => Nat.zero_le (R.maxDegree-R.degree u)) hv
      rw [hz,Nat.sub_zero] at hOne
      change R.maxDegree ≤ deficitMass R R.maxDegree X at hOne
      omega
    exact hPos.trans_le (R.degree_le_of_le (sdiff_le.trans hGH))
  apply hNo X hOdd hActive
  change deficitMass G d X + (∑ v ∈ Xᶜ,G.degree v) =
    cutEdges G X+deficitMass G d X+2*internalEdges G Xᶜ at hBudget
  change deficitMass G d X + (∑ v ∈ Xᶜ,G.degree v) ≤ d+(M+4*(E.card+1))
  omega

theorem no_overfull_after_clean_and_trim (G H L : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel L.Adj]
    (E : Finset V) (r t b c a M : ℕ) :
    let R := H \ L
    let d := G.maxDegree
    H ≤ G → H.maxDegree = d → 2 ≤ d → L ≤ H →
    R.maxDegree = d-2 → (∀ v,L.degree v ≤ 2) → (∑ v,(2-L.degree v)) ≤ M →
    (∀ v,G.degree v ≤ R.degree v+c) →
    IsRobustAt R r t → t+2 ≤ d → d ≤ r*r →
    (∀ u v,G.Adj u v → d-b ≤ G.degree u+G.degree v) →
    (∀ v,v ∉ E → d ≤ G.degree v+a) →
    3*b+6*(t+c) ≤ d → 2*a+2*(t+c) ≤ d →
    ¬HasOddAlmostOverfullSet G (M+4*(E.card+1)) →
    ¬R.HasOverfullSubgraph := by
  intro R d hGH hHD hD hLH hRD hTwo hMissing hLoss hRob hT hRate hWeak hOrd hMargin hOrdMargin hNo
  exact no_overfull_after_clean_and_trim_on_support G H L E r t b c a M
    hGH hHD hD hLH hRD hTwo hMissing hLoss hRob hT hRate hWeak hOrd hMargin hOrdMargin
    (fun X hOdd _ hBudget => hNo ⟨X,hOdd,hBudget⟩)

end OverfullWork.CMSTrimmingRound
