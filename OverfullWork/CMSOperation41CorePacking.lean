module

public import OverfullWork.CMSOperation41ConnectorChoice

@[expose] public section


/-! Simultaneous packing of the fixed-core layouts of CMS Operation
4.1. The auxiliary endpoint pairs and isolated vertices are the data
selected by its degree-record procedure. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset SimpleGraph RobustExpansion DirectedReserveUsage
open scoped Classical
universe u v
variable {V : Type u}

theorem cyclicLayout_endpoint_load {n : ℕ} (hn : 2 ≤ n+1) (w : Fin (n+1) ↪ V)
    (F : Finset (Fin (n+1))) (I : Finset V) (dir : Bool) (z : V) :
    (cyclicLayout hn w F I).endpointLoad dir z ≤
      if z ∈ (cyclicLayout hn w F I).boundary then 1 else 0 := by
  let L := cyclicLayout hn w F I
  let toVertex (i : Fin (n+1)) := if dir then L.target i else L.source i
  have hInj : Function.Injective toVertex := by
    cases dir
    · exact w.injective
    · exact w.injective.comp (finRotate (n+1)).injective
  have hBoundary (i : Fin (n+1)) : toVertex i ∈ L.boundary := by
    cases dir
    · exact (L.ends i).1
    · exact (L.ends i).2.1
  letI : DecidableEq (Fin (n+1)) := fun _ _ => Classical.propDecidable _
  let S := (univ : Finset {i // i ∉ L.fixed}).filter fun i => z = toVertex i.val
  have hS : L.endpointLoad dir z = S.card := by unfold S Layout.endpointLoad; rw [card_filter]
  rw [hS]
  by_cases hz : z ∈ L.boundary
  · rw [if_pos hz]
    apply card_le_one.mpr
    intro i hi j hj
    exact Subtype.ext (hInj ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2))
  · rw [if_neg hz]
    apply Nat.le_of_eq
    apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro i hi
    exact hz ((mem_filter.mp hi).2.symm ▸ hBoundary i.val)

private theorem injective_occurrence_le_one {J : Type*} [Fintype J] (w : J ↪ V) (z : V) :
    ((univ : Finset J).filter (fun i => w i = z)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  exact w.injective ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)

set_option maxHeartbeats 2200000 in
theorem cms_operation_4_1_core_packing (a gap ν τ : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1)
    (hgap : 0 < gap) (hgapA : gap ≤ a) (hν : 0 < ν) (hντ : ν ≤ τ) (hτgap : 16384*τ ≤ gap) :
    ∃ γ ν' : ℝ, 0 < γ ∧ 0 < ν' ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] {J : Type v} [Fintype J]
        (G : SimpleGraph V) [DecidableRel G.Adj] (f : J → ℕ)
        (e : ∀ j,(Fin (f j) × Bool) ↪ V) (I : J → Finset V),
        let B : J → Finset V := fun j => univ.image (e j) ∪ I j
        let n := Fintype.card V
        N ≤ n → IsRealRobust G ν τ →
        (∀ z, |(G.degree z:ℝ)-a*(n:ℝ)| ≤ γ*(n:ℝ)) →
        (Fintype.card J:ℝ) ≤ ((a-gap)/2)*(n:ℝ) →
        (∀ j i,e j i ∉ I j) →
        (∀ j,((B j).card+2:ℕ) ≤ γ*(n:ℝ)) →
        (∀ z,(visits B z+2:ℕ) ≤ γ*(n:ℝ)) →
        ∃ (w : ∀ j, Fin (2*f j+2) ↪ V) (F : ∀ j, Finset (Fin (2*f j+2)))
          (mark : ∀ j, Fin (f j) ↪ Fin (2*f j+2)),
          let L : ∀ j, Layout V (Fin (2*f j+2)) := fun j => cyclicLayout (by omega) (w j) (F j) (I j)
          (∀ j,F j = univ.image (mark j)) ∧
          (∀ j i,w j (mark j i) = e j (i,false) ∧ w j (finRotate (2*f j+2) (mark j i)) = e j (i,true)) ∧
          (∀ j i,w j i ∉ I j) ∧
          ∃ P : CMSPacking (fun j => Fin (2*f j+2)) G L,
            IsRealRobust (G \ hostEdges G P.used) ν' τ ∧
            ∀ j,∃ T : List V,T.Nodup ∧
              (T ++ [w j 0]).IsChain (fun x y => G.Adj x y ∨
                ∃ i : Fin (f j),x = e j (i,false) ∧ y = e j (i,true)) ∧
              ∀ x,x ∈ T ↔ x ∉ I j := by
  obtain ⟨ε,ν',hε,hν',N,hPacked⟩ := cms_lemma_3_14.{u,0,v} a gap ν τ ha ha₁ hgap hgapA hν hντ hτgap
  let γ := min (1/4) (min ε (min (ε^2) (min (ε^4) (ε^3/2))))
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  have hγSmall : γ ≤ 1/4 := min_le_left _ _
  have hγε : γ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hγ₂ : γ ≤ ε^2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hγ₄ : γ ≤ ε^4 := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hγ₃ : γ ≤ ε^3/2 := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨γ,ν',hγ,hν',N,?_⟩
  intro V _ J _ G _ f e I B n hN hRob hDeg hRounds hIso hLocal hGlobal
  letI : DecidableEq V := Classical.decEq _
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hRoom (j : J) : Fintype.card J+(B j).card+1 ≤ n := by
    have h := hLocal j
    push_cast at h
    have hSize := mul_le_mul_of_nonneg_right hγSmall hn
    have hR := mul_le_mul_of_nonneg_right (show (a-gap)/2 ≤ 1/2 by linarith only [hgap,ha₁]) hn
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith only [h,hSize,hR,hRounds,hn]
  obtain ⟨x,y,hXY,_⟩ := exists_connectors_of_small_forbidden B hRoom
  have hData (j : J) := exists_cyclic_layout_of_auxiliary_edges (e j) (x j) (y j) (hXY j).1
    (fun ⟨i,hi⟩ => (hXY j).2.1 (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,hi⟩)))
    (fun ⟨i,hi⟩ => (hXY j).2.2 (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,hi⟩)))
    (I j) (fun h => (hXY j).2.1 (mem_union_right _ h)) (fun h => (hXY j).2.2 (mem_union_right _ h)) (hIso j)
  choose w F mark _ _ hIsoW hFixed _ hLong hEnds hRange using hData
  let L (j : J) : Layout V (Fin (2*f j+2)) := cyclicLayout (by omega) (w j) (F j) (I j)
  have hBoundary (j : J) : (L j).boundary ⊆ B j ∪ {x j,y j} := by
    intro z hz
    rcases mem_union.mp hz with hz|hz
    · obtain ⟨u,_,rfl⟩ := mem_image.mp hz
      rcases hRange j u with he|he|⟨i,hi⟩
      · exact mem_union_right _ (by simp [he])
      · exact mem_union_right _ (by simp [he])
      · exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,hi⟩))
    · exact mem_union_left _ (mem_union_right _ hz)
  have hVisits (z : V) : visits (fun j => (L j).boundary) z ≤ visits B z+2 := by
    let X := (univ : Finset J).filter (fun i => x i = z)
    let Y := (univ : Finset J).filter (fun i => y i = z)
    have hSub : (univ.filter fun j => z ∈ (L j).boundary) ⊆
        ((univ : Finset J).filter (fun j => z ∈ B j)) ∪ (X ∪ Y) := by
      intro j hj
      have h := hBoundary j (mem_filter.mp hj).2
      rcases mem_union.mp h with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
      · have h' : z = x j ∨ z = y j := by simpa using h
        rcases h' with h'|h'
        · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h'.symm⟩))
        · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h'.symm⟩))
    have hC := (card_le_card hSub).trans (card_union_le _ _)
    have hXY' := (card_union_le X Y).trans (Nat.add_le_add (injective_occurrence_le_one x z)
      (injective_occurrence_le_one y z))
    exact hC.trans (Nat.add_le_add_left hXY' _)
  have hEach (j : J) :
      ((L j).boundary.card:ℝ) ≤ ε^2*(n:ℝ) ∧ Fin.last (2*f j+1) ∉ (L j).fixed ∧
      (Fintype.card (Fin (2*f j+2)):ℝ) ≤ ε^4*(n:ℝ) := by
    have hSize := (card_le_card (hBoundary j)).trans (card_union_le _ _)
    have hBound : (L j).boundary.card ≤ (B j).card+2 := hSize.trans (by
      gcongr
      exact card_insert_le _ _ |>.trans (by simp))
    have hArc : 2*f j+2 ≤ (B j).card+2 := by
      have h := card_le_card (show univ.image (e j) ⊆ B j from subset_union_left)
      rw [card_image_of_injective _ (e j).injective,card_univ,Fintype.card_prod,Fintype.card_fin,
        Fintype.card_bool] at h
      omega
    refine ⟨?_,hLong j,?_⟩
    · exact (by exact_mod_cast hBound : ((L j).boundary.card:ℝ) ≤ ((B j).card+2:ℕ)).trans
        ((hLocal j).trans (mul_le_mul_of_nonneg_right hγ₂ hn))
    · rw [Fintype.card_fin]
      exact (by exact_mod_cast hArc : ((2*f j+2:ℕ):ℝ) ≤ ((B j).card+2:ℕ)).trans
        ((hLocal j).trans (mul_le_mul_of_nonneg_right hγ₄ hn))
  have hLoad (z : V) :
      ((∑ j, ((L j).endpointLoad true z+(L j).endpointLoad false z):ℕ):ℝ) ≤ ε^3*(n:ℝ) := by
    have hLocal (j : J) := Nat.add_le_add
      (cyclicLayout_endpoint_load (by omega) (w j) (F j) (I j) true z)
      (cyclicLayout_endpoint_load (by omega) (w j) (F j) (I j) false z)
    have h : (∑ j, ((L j).endpointLoad true z+(L j).endpointLoad false z)) ≤
        (∑ j : J, if z ∈ (L j).boundary then 1 else 0)+
        (∑ j : J, if z ∈ (L j).boundary then 1 else 0) := by
      rw [←sum_add_distrib]
      exact sum_le_sum (fun j _ => hLocal j)
    have hNat : (∑ j, ((L j).endpointLoad true z+(L j).endpointLoad false z)) ≤
        2*(visits B z+2) := by
      have hVisitsSum : (∑ j : J, if z ∈ (L j).boundary then 1 else 0) ≤ visits B z+2 := by
        simpa only [visits,card_filter] using hVisits z
      omega
    have hR : ((∑ j, ((L j).endpointLoad true z+(L j).endpointLoad false z):ℕ):ℝ) ≤
        2*((visits B z+2:ℕ):ℝ) := by exact_mod_cast hNat
    have hScale := mul_le_mul_of_nonneg_right hγ₃ hn
    linarith only [hR,hGlobal z,hScale]
  have hVisit (z : V) : (visits (fun j => (L j).boundary) z:ℝ) ≤ ε^2*(n:ℝ) := by
    have hh : (visits (fun j => (L j).boundary) z:ℝ) ≤ (visits B z+2:ℕ) := by exact_mod_cast hVisits z
    exact hh.trans ((hGlobal z).trans (mul_le_mul_of_nonneg_right hγ₂ hn))
  obtain ⟨P,hR⟩ := hPacked (fun j => Fin (2*f j+2)) G L (fun j => Fin.last (2*f j+1)) hN hRob
    (fun z => (hDeg z).trans (mul_le_mul_of_nonneg_right hγε hn)) hRounds hEach hLoad hVisit
  refine ⟨w,F,mark,hFixed,hEnds,hIsoW,P,hR,?_⟩
  intro j
  obtain ⟨T,hNd,_,hClose,hMem⟩ :=
    (P.configuration j).cyclic_configuration (by omega) (w j) (F j) (I j) (hIsoW j)
  refine ⟨T,hNd,hClose.imp ?_,hMem⟩
  intro u z h
  rcases h with h | ⟨k,hk,hu,hz⟩
  · exact Or.inl (P.isOrientation.1 u z h)
  · rw [hFixed j] at hk
    obtain ⟨i,_,rfl⟩ := mem_image.mp hk
    exact Or.inr ⟨i,hu.trans (hEnds j i).1,hz.trans (hEnds j i).2⟩

end OverfullWork.DirectedSpanningConfiguration
