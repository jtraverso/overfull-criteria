module

public import OverfullWork.ConditionalIndependentIdentificationNoOverfull
public import OverfullWork.CMSRegularizationOddCuts

@[expose] public section


/-! In CMS Subcase 2.3, robust expansion supplies the small-cut
alternative for the identified star multigraph. The rest of the
no-overfull argument is the existing centre-deficit calculation. -/
namespace OverfullWork.ConditionalIndependentIdentification

open Finset SimpleGraph RobustExpansion
open scoped Classical

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem no_overfull_of_robust_budget (M : MultiGraph (Option W)) (D B h r t : ℕ)
    (hdeg : ∀ v,M.degree v ≤ D) (hstar : M.IsStarAt none)
    (hmu : ∀ v,M.mult s(none,v) ≤ h)
    (hmin : ∀ w,M.degree none ≤ M.degree (some w))
    (hodd : Odd (Fintype.card W))
    (hbudget : (∑ v ∈ (univ : Finset (Option W)).erase none,(D-M.degree v))+M.degree none ≤ D+B)
    (hRob : IsRobustAt M.supportGraph r t) (hRate : D ≤ r*r)
    (hOutside : t+B ≤ D) (hInside : t+2*h ≤ D+1)
    (haway : ∀ S : Finset (Option W),Odd S.card → none ∉ S →
      M.twiceInternal S ≤ D*(S.card-1)) : ¬M.HasOverfullSubset D := by
  apply no_overfull_of_budget_and_localization M D B h hdeg hstar hmu hmin hodd hbudget _ haway
  intro S _ hS hOver
  by_cases hComp : Sᶜ.card ≤ t
  · exact Or.inl (by omega)
  by_cases hSmall : S.card ≤ t
  · exact Or.inr (by omega)
  have hCap : (∑ v ∈ S,M.degree v) ≤ D*S.card := by
    calc
      _ ≤ ∑ _v ∈ S,D := sum_le_sum (fun v _ => hdeg v)
      _ = _ := by simp [Nat.mul_comm]
  have hIdentity := M.sum_degree_eq_internal_add_cut S
  have hSPos : 0 < S.card := card_pos.mpr ⟨none,hS⟩
  have hExpand : D*(S.card-1)+D = D*S.card := by
    rw [←Nat.mul_succ]
    congr 1
    omega
  have hCut : M.cutSize S < D := by omega
  have hBalance := card_add_card_compl S
  have hLarge := CanonicalRegularization.robust_cut_lower M S r t hRob (by omega) (by omega)
  omega

section ActualImage

open IndependentSetIdentification OddCutDeficit
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem robust_after_independent_identification (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hInd : G.IsIndepSet (Y : Set V))
    (r t : ℕ) (hRob : IsRobustAt G r t) :
    IsRobustAt (graph G Y hInd).supportGraph (r-(Y.card+1)) (t+1) := by
  let M := graph G Y hInd
  intro S hLo hHi
  by_cases hr : Y.card+1 ≤ r
  swap
  · have hz : r-(Y.card+1) = 0 := by omega
    rw [hz]
    have hn : neighbourhood M.supportGraph 0 S = univ := by ext v; simp [neighbourhood]
    change S.card+0 ≤ (neighbourhood M.supportGraph 0 S).card
    rw [hn,card_univ]
    omega
  let T : Finset V := S.eraseNone.image Subtype.val
  have hT : T.card = S.eraseNone.card := card_image_of_injective _ Subtype.val_injective
  have hSize : T.card ≤ S.card ∧ S.card ≤ T.card+1 := by
    rw [hT]
    by_cases hn : none ∈ S
    · have hh := card_eraseNone_of_mem hn
      omega
    · rw [card_eraseNone_of_not_mem hn]
      omega
  have hTLo : t ≤ T.card := by omega
  have hTHi : T.card+t ≤ Fintype.card V := by
    rw [card_vertices] at hHi
    have hComp := card_add_card_compl Y
    omega
  let R := neighbourhood G r T
  have hExpand : T.card+r ≤ R.card := hRob T hTLo hTHi
  let F : Finset (Outside Y) := univ.filter (fun v => v.val ∈ R)
  have hImg : F.image Subtype.val = R \ Y := by
    ext v
    simp only [F,mem_image,mem_sdiff,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,u.property⟩
    · rintro ⟨hv,hy⟩
      exact ⟨⟨v,hy⟩,hv,rfl⟩
  have hLoss : R.card ≤ F.card+Y.card := by
    have hSplit := card_sdiff_add_card_inter R Y
    rw [←hImg,card_image_of_injective _ Subtype.val_injective] at hSplit
    have hCap : (R∩Y).card ≤ Y.card := card_le_card inter_subset_right
    omega
  have hNb (v : Outside Y) :
      PrunedCore.neighboursIn G T v.val ≤ PrunedCore.neighboursIn M.supportGraph S (some v) := by
    let K := S.eraseNone.filter (fun u => G.Adj v.val u.val)
    have hRow : K.image Subtype.val = T.filter (G.Adj v.val) := by
      ext u
      simp only [K,T,mem_image,mem_filter]
      constructor
      · rintro ⟨w,⟨hw,hG⟩,rfl⟩
        exact ⟨⟨w,hw,rfl⟩,hG⟩
      · rintro ⟨⟨w,hw,rfl⟩,hG⟩
        exact ⟨w,⟨hw,hG⟩,rfl⟩
    have hSub : K.image some ⊆ S.filter (M.supportGraph.Adj (some v)) := by
      intro x hx
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
      obtain ⟨hS,hAdj⟩ := mem_filter.mp hu
      refine mem_filter.mpr ⟨mem_eraseNone.mp hS,?_⟩
      change 0 < (graph G Y hInd).mult s(some v,some u)
      rw [mult_some_some,if_pos hAdj]
      decide
    rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card,←hRow,
      card_image_of_injective _ Subtype.val_injective]
    exact (card_image_of_injective K (Option.some_injective _)).symm.le.trans (card_le_card hSub)
  have hSurvive : F.image some ⊆ neighbourhood M.supportGraph (r-(Y.card+1)) S := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    have hvR : v.val ∈ R := (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _,(Nat.sub_le _ _).trans ((mem_filter.mp hvR).2.trans (hNb v))⟩
  have hCount := card_le_card hSurvive
  rw [card_image_of_injective _ (Option.some_injective _)] at hCount
  change S.card+(r-(Y.card+1)) ≤ (neighbourhood M.supportGraph (r-(Y.card+1)) S).card
  omega

theorem identified_centre_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hInd : G.IsIndepSet (Y : Set V)) (d : ℕ) :
    let M := graph G Y hInd
    (∑ v ∈ (univ : Finset (Vertices Y)).erase none,(d-M.degree v))+M.degree none =
      deficitMass G d Yᶜ+(∑ y ∈ Y,G.degree y) := by
  intro M
  have hSum := sum_erase_add (univ : Finset (Vertices Y))
    (fun v => d-M.degree v) (mem_univ none)
  rw [Fintype.sum_option] at hSum
  have hDef : (∑ w : Outside Y,(d-M.degree (some w)))=deficitMass G d Yᶜ := by
    simp_rw [M,degree_some]
    exact (sum_subtype Yᶜ (fun v=>mem_compl) (fun v=>d-G.degree v)).symm
  rw [hDef] at hSum
  rw [show M.degree none = ∑ y ∈ Y,G.degree y from degree_none G Y hInd]
  omega

theorem actual_image_no_overfull_of_robust (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hInd : G.IsIndepSet (Y : Set V))
    (hNo : ¬G.HasOverfullSubgraph) (hOdd : Odd Yᶜ.card) (B r t : ℕ)
    (hMin : ∀ x,x ∉ Y → (∑ y ∈ Y,G.degree y) ≤ G.degree x)
    (hBudget : deficitMass G G.maxDegree Yᶜ+(∑ y ∈ Y,G.degree y) ≤ G.maxDegree+B)
    (hRob : IsRobustAt (graph G Y hInd).supportGraph r t)
    (hRate : G.maxDegree ≤ r*r) (hOutside : t+B ≤ G.maxDegree)
    (hInside : t+2*Y.card ≤ G.maxDegree+1) :
    ¬(graph G Y hInd).HasOverfullSubset G.maxDegree := by
  let M := graph G Y hInd
  have hOddCore : Odd (Fintype.card (Outside Y)) := by
    have hCard := card_vertices Y
    rw [show Fintype.card (Vertices Y) = Fintype.card (Option (Outside Y)) from rfl,
      Fintype.card_option] at hCard
    have hEq : Fintype.card (Outside Y) = Yᶜ.card := by omega
    rwa [hEq]
  have hDegree := (actual_image_has_maximum_degree G Y hInd hOdd hMin).1
  have hRows (v : Vertices Y) : M.mult s(none,v) ≤ Y.card := by
    cases v with
    | none => rw [M.loopless _ (by simp)]; exact Nat.zero_le _
    | some v => exact centre_mult_le G Y hInd v
  have hLowest (v : Outside Y) : M.degree none ≤ M.degree (some v) := by
    have h := hMin v.val v.property
    simpa only [M,degree_none,degree_some] using h
  have hDef := identified_centre_budget G Y hInd G.maxDegree
  apply no_overfull_of_robust_budget M G.maxDegree B Y.card r t hDegree (isStarAt G Y hInd)
    hRows hLowest hOddCore (hDef.trans_le hBudget) hRob hRate hOutside hInside
  exact twiceInternal_bound_away_centre G Y hInd hNo

end ActualImage

end OverfullWork.ConditionalIndependentIdentification
