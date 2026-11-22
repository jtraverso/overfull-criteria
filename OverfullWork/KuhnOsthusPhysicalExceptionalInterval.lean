module

public import OverfullWork.KuhnOsthusPhysicalWindingInterval
public import OverfullWork.KuhnOsthusScheduledExceptionalInterval
public import OverfullWork.KuhnOsthusWrappedExceptionalEndpoints

@[expose] public section


/-! Use actual physical pairs and neighbourhoods to construct one
complete exceptional path system in the residual host. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

theorem incidences_pull_pair {W V : Type*} [Fintype W] [Fintype V]
    (G : Digraph V) (a b : W ↪ V) (X Y : Finset W) :
    incidences (pullDirectedPair a b G) X Y = incidences G (X.map a) (Y.map b) := by
  rw [←Nat.cast_inj (R := ℝ)]
  simp only [incidences_eq_sum,sum_map]
  rfl

/-- Lemma 7.6 on one physical interval and style, from its residual
neighbourhoods and pairs. The compatible quotient and its chord and
successor graphs are constructed inside the proof. -/
theorem exists_original_interval_of_physical_pairs
    (d δ ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) (hTol : 2*δ ≤ ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n : ℕ}
      (G : Digraph V) (R : Digraph (Fin (n+1))) (Z T : Finset V) (C : Fin (n+1) → Finset V)
      (m e endpointCap endpointBudget routeCap : ℕ),
      let A := univ.biUnion C ∪ T
      let E := (windingEndpointPositions (0 : Fin (n+1))).biUnion C
      let s := finRotate (n+1)
      let loss := endpointCap+(routeCap+2)+2*endpointCap
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) →
      (∀ i, Disjoint (C i) T) → Disjoint A Z →
      (∀ i, (C i).card = m) → T.card = m →
      2*Z.card < endpointCap*(endpointBudget+1) →
      (∀ z ∈ Z, 2*Z.card+endpointBudget*m < inNeighbours G E z) →
      (∀ z ∈ Z, 2*Z.card+endpointBudget*m < outTo G E z) →
      2*(routeCap+2+2*endpointCap)+e < m-endpointCap →
      (∀ i, ¬R.Adj i i) →
      (∃ radius growth cutoff budget : ℕ, IsRobustAt R radius cutoff ∧ 0 < growth ∧
        2*(budget+1)+growth ≤ radius ∧
        (∀ i, cutoff+2*(budget+1) ≤ outDegree R i) ∧ (∀ i, cutoff ≤ inDegree R i) ∧
        Z.card*(2*((n+1)/growth+3)) < routeCap*(budget+1)) →
      (∀ i j, R.Adj i j → ∀ X ⊆ C i, ∀ Y ⊆ C j,
        e < X.card → e < Y.card → 0 < incidences G X Y) →
      loss < m → N ≤ m-loss →
      ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) →
      (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε →
      (∀ i, IsLowerSuperregularPair G δ d (C i) (if s i = 0 then T else C (s i))) →
      Nonempty (OriginalInterval G Z A (C 0) T) := by
  classical
  obtain ⟨N,hN⟩ := exists_original_interval_of_scheduled_chords_lower.{u}
    d δ ε ν τ γ hν hWidth hε hε1 hτγ hγ hd hCost hDegrees hTol
  refine ⟨N,?_⟩
  intro V _ n G R Z T C m e endpointCap endpointBudget routeCap A E s loss
    hDis hTerm hAZ hSize hT hBdg hIn hOut hRoom hLoop hRoutes hRect hm hMin hHall hPay hSR
  let W := ↥(A \ T)
  obtain ⟨cluster,coord₀,first₀,last₀,hFirst₀,hLast₀,hOrd₀,hMaps₀⟩ :=
    exists_physical_winding_interval_coordinates C 0 T hDis hTerm ((hSize 0).trans hT.symm)
  let B := (univ : Finset W).filter (fun x => cluster x = 0)
  let B₀ := intervalCluster cluster 0
  let eB : B ≃ B₀ := ⟨
    fun x => ⟨x.val,(mem_intervalCluster _ _ _).mpr (mem_filter.mp x.prop).2⟩,
    fun x => ⟨x.val,mem_filter.mpr ⟨mem_univ _,(mem_intervalCluster _ _ _).mp x.prop⟩⟩,
    fun x => Subtype.ext rfl,fun x => Subtype.ext rfl⟩
  let coord : W ⊕ B ≃ A := (Equiv.sumCongr (Equiv.refl W) eB).trans coord₀
  let first : B ≃ C 0 := eB.trans first₀
  let last : B ≃ T := eB.trans last₀
  let f : W ⊕ B ↪ V := coord.toEmbedding.trans (Function.Embedding.subtype _)
  let a : W ↪ V := Function.Embedding.inl.trans f
  have hOrd (x : W) : a x = x.val := hOrd₀ x
  have hMaps (J : Finset (Fin (n+1))) :
      (univ.filter (fun x : W => cluster x ∈ J)).map a = J.biUnion C := by
    have he : a = Function.Embedding.inl.trans
        (coord₀.toEmbedding.trans (Function.Embedding.subtype _)) := by
      ext x
      exact (hOrd x).trans (hOrd₀ x).symm
    rw [he]
    convert hMaps₀ J using 2
    ext x
    simp only [mem_filter,mem_univ,true_and]
  have hCell (i : Fin (n+1)) : (intervalCluster cluster i).map a = C i := by
    have h := hMaps {i}
    have hset : ({i} : Finset (Fin (n+1))).biUnion C = C i := by
      ext x
      simp
    rw [hset] at h
    have he : intervalCluster cluster i =
        (univ : Finset W).filter (fun x => cluster x ∈ ({i} : Finset (Fin (n+1)))) := by
      ext x
      simp only [mem_intervalCluster,mem_filter,mem_univ,true_and,mem_singleton]
    rw [he]
    exact h
  have hM (i : Fin (n+1)) : (intervalCluster cluster i).card = m := by
    rw [← card_map a,hCell,hSize]
  have hEnd : (univ : Finset B).map (Function.Embedding.inr.trans f) = T := by
    ext v
    constructor
    · intro hv
      obtain ⟨b,_,he⟩ := mem_map.mp hv
      change (coord (Sum.inr b)).val = v at he
      have he' : (coord (Sum.inr b)).val = (last b).val := hLast₀ (eB b)
      rw [he'] at he
      exact he ▸ (last b).prop
    · intro hv
      let y : T := ⟨v,hv⟩
      refine mem_map.mpr ⟨last.symm y,mem_univ _,?_⟩
      exact (hLast₀ (eB (last.symm y))).trans (congrArg Subtype.val (last.apply_symm_apply y))
  have hB : B = intervalCluster cluster 0 := by
    ext x
    simp only [B,mem_intervalCluster,mem_filter,mem_univ,true_and]
  let L := pullDirectedPair a ((wrappedTargetEmbedding B).trans f) G
  have hFree (i : Fin (n+1)) : IsLowerSuperregularPair L δ d
      (intervalCluster cluster i) (intervalCluster cluster (s i)) := by
    obtain ⟨c,hc,hc1,hcPair⟩ := hSR i
    refine ⟨c,hc,hc1,?_⟩
    apply superregular_pullDirectedPair
    rw [hCell]
    by_cases h : s i = 0
    · rw [h,←hB,map_wrapped_target_boundary,hEnd]
      simpa only [if_pos h] using hcPair
    · have hApart : Disjoint (intervalCluster cluster (s i)) B := by
        rw [hB]
        exact disjoint_left.mpr fun x hx hy => h
          (((mem_intervalCluster _ _ _).mp hx).symm.trans ((mem_intervalCluster _ _ _).mp hy))
      rw [map_wrapped_target_outside _ _ _ hApart,hCell]
      simpa only [if_neg h] using hcPair
  let H := pullDirectedPair a a G
  have hChord (i j : Fin (n+1)) (hij : R.Adj i j) :
      ∀ X ⊆ intervalCluster cluster i, ∀ Y ⊆ intervalCluster cluster j,
        e < X.card → e < Y.card → 0 < incidences H X Y := by
    intro X hX Y hY hXC hYC
    rw [incidences_pull_pair]
    apply hRect i j hij
    · rw [←hCell i]
      exact map_subset_map.mpr hX
    · rw [←hCell j]
      exact map_subset_map.mpr hY
    · rwa [card_map]
    · rwa [card_map]
  let S := (univ : Finset W).filter (fun x => cluster x ∈ windingEndpointPositions (0 : Fin (n+1)))
  have hS : S.map a = E := hMaps _
  have hm' : 0 < m := by omega
  have hW : Nonempty W := by
    obtain ⟨x,_⟩ := card_pos.mp (hm'.trans_eq (hM 0).symm)
    exact ⟨x⟩
  let : Inhabited W := ⟨Classical.choice hW⟩
  obtain ⟨endpoint,hInj,hS',hAdj,hCap⟩ := exists_wrapped_exceptional_endpoints G G le_rfl
    Z S a cluster m endpointCap endpointBudget 0 (fun i => (hM i).le) hBdg
    (by simpa only [hS,Nat.add_zero] using hIn) (by simpa only [hS,Nat.add_zero] using hOut)
    (by intro z _; simp [inDegree,outDegree,inNeighbours,Digraph.bot_adj])
  have hPos (p : Bool × Z) := (mem_windingEndpointPositions 0 (cluster (endpoint p))).mp
    ((mem_filter.mp (hS' p)).2)
  obtain ⟨radius,growth,cutoff,budget,hRob,hGrowth,hAvoid,ho,hi,hMass⟩ := hRoutes
  have hCap' (i : Fin (n+1)) : ((univ : Finset (Bool × Z)).filter
      (fun p => cluster (endpoint p) = i)).card ≤ endpointCap := by
    convert hCap i using 2
    ext p
    simp only [mem_filter,mem_univ,true_and]
  exact hN G H L R Z A (C 0) T cluster coord first last endpoint
    m (m-endpointCap) e endpointCap routeCap budget radius growth cutoff
    (fun b => hFirst₀ (eB b)) (fun b => hLast₀ (eB b)) hAZ hInj
    (fun p => (hPos p).1) (fun z => (hPos (true,z)).2.1) (fun z => (hPos (false,z)).2.2) hAdj
    (fun _ _ _ _ h => h) (split_wrapped_pair_lifts G B f) hM hCap'
    (by omega) hRoom hLoop hRob hGrowth hAvoid ho hi hMass hChord hm hMin hHall hPay hFree

end OverfullWork.DirectedRobustExpansion
