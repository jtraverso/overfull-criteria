module

public import OverfullWork.KuhnOsthusParityForwardPaths
public import OverfullWork.KuhnOsthusParityMarkOrder
public import OverfullWork.KuhnOsthusPrescribedIntervalReturn
public import OverfullWork.KuhnOsthusReserveIntervalGeometry
public import OverfullWork.KuhnOsthusClosedCycleReserve

@[expose] public section


/-! Insert the specified exceptional interval and close the first
parity reserve by advancing one copy in the same lane. -/
namespace OverfullWork.DirectedRobustExpansion

open Function Finset
open scoped Classical
variable {V : Type*} [Fintype V]

structure OrderedParityFactor (D E : Digraph V) where
  ordinary : Digraph V
  permutation : Equiv.Perm V
  mark : Bool × Fin 3 ↪ V
  order : MarkedCycleSegments permutation mark (Equiv.prodCongr (Equiv.refl Bool) (finRotate 3))
  exact_factor : ∀ x y, (ordinary ⊔ E).Adj x y ↔ permutation x = y
  ordinary_le : ordinary ≤ D
  ordinary_separate : ∀ {x y}, ordinary.Adj x y → ¬ E.Adj x y

structure WindingParityFactor (D E : Digraph V) where
  ordinary : Digraph V
  permutation : Equiv.Perm V
  exact_factor : ∀ x y, (ordinary ⊔ E).Adj x y ↔ permutation x = y
  ordinary_le : ordinary ≤ D
  ordinary_separate : ∀ {x y}, ordinary.Adj x y → ¬ E.Adj x y

/-- Insert the exceptional interval and advance one copy within
each lane at the return, retaining the traces of the forward paths. -/
theorem OrderedClusterPaths.exists_closed_winding_parity_factor {D H : Digraph V}
    {k s c t m r : ℕ} {ε d : ℝ}
    (X : Fin k → Finset V) (hk : 0 < k) (hsc : s ≤ c) (hst : s < t)
    (hct : c ≤ t) (htk : t < k) (hnt : 3 ≤ k+s-t)
    (hCover : ∀ x, ∃ i, x ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (P : OrderedClusterPaths D (cyclicCluster X hk) (Fin m × Fin 2) s c)
    (E : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) c t)
      (cyclicCluster X hk c) (cyclicCluster X hk t))
    (hPair : ∀ i, IsLowerSuperregularPair D ε d (X i) (X (finRotate k i)))
    (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1) (hr : 0 < r)
    (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    let seed := (P.orderAt s le_rfl hsc).toEmbedding.trans
      (Embedding.subtype (· ∈ cyclicCluster X hk s))
    ∃ F : WindingParityFactor D E.digraph,
      Nonempty (MarkedCycleSegments F.permutation seed (cycleAbsorberReturn m)) ∧
      ∀ j i, s+i ≤ c → (F.permutation : V → V)^[i] (seed j) = P.vertex (s+i) j := by
  intro seed
  let A := cyclicCluster X hk
  let B (i : ℕ) := A (t+i)
  let n := k+s-t
  obtain ⟨hB₀,hBn,hAll,hMeet,hDisA,hDisB⟩ :=
    cyclicCluster_complementary_intervals X hst htk hCover hDis
  obtain ⟨Q,hQ,_⟩ := P.exists_interval_path_cover hsc
    (fun i j hi hi' hj hj' h => hDisA i j hi (hi'.trans hct) hj (hj'.trans hct) h)
  let Q' := Q.rehost (le_sup_left : D ≤ D ⊔ H)
  let E' := E.rehost (le_sup_right : H ≤ D ⊔ H)
  obtain ⟨U,hU,_⟩ := Q'.exists_concat E'
    (clusterIntervalVertices_inter A hsc hct hDisA)
  let U' := U.castSupport (clusterIntervalVertices_union A hsc hct)
  let V' := U'.castBoundaries hBn.symm hB₀.symm
  have hV : V'.digraph = P.unionPaths ⊔ E.digraph := by
    dsimp only [V',U']
    rw [IntervalPathCover.castBoundaries_digraph,IntervalPathCover.castSupport_digraph,hU]
    change Q.digraph ⊔ E.digraph = _
    rw [hQ]
  let e := P.orderAt s le_rfl hsc
  have hEnd : B n = A s := hBn
  let e' : Fin m × Fin 2 ≃ B n :=
    e.trans (Equiv.subtypeEquivRight (fun x => by rw [hEnd]))
  have hPairsB (i : ℕ) : IsLowerSuperregularPair D ε d (B i) (B (i+1)) := by
    change IsLowerSuperregularPair D ε d (A (t+i)) (A (t+(i+1)))
    rw [←Nat.add_assoc]
    change IsLowerSuperregularPair D ε d (A (t+i)) (cyclicCluster X hk (t+i+1))
    rw [cyclicCluster_successor]
    exact hPair _
  obtain ⟨R,σ,hArc,_,⟨K⟩⟩ := V'.exists_factor_with_prescribed_return_in B n (2*m) r hnt e'
    (cycleAbsorberReturn m) hAll hMeet (hDisB n 0 le_rfl (by omega) (by omega))
    (fun i _ => hSize _) hDisB ε d hε hGap hd (fun i _ => hPairsB i) hr hCut hBudget
  rw [hV] at hArc
  have H₀ : MarkedCycleSegments σ seed (cycleAbsorberReturn m) :=
    K.reindex e' _ (fun _ => by simp only [Equiv.trans_apply,Equiv.symm_apply_apply])
  have hTrace (j : Fin m × Fin 2) (i : ℕ) (hi : s+i ≤ c) :
      (σ : V → V)^[i] (seed j) = P.vertex (s+i) j := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [iterate_succ_apply',ih (by omega)]
      exact (hArc _ _).mp (.inl (.inl (Digraph.iSup_adj.mpr ⟨j,s+i,by omega,by omega,rfl,rfl⟩)))
  let O := P.unionPaths ⊔ R.unionPaths
  have hO (x y : V) : (O ⊔ E.digraph).Adj x y ↔ σ x = y := by
    rw [←hArc x y]
    simp only [O,Digraph.sup_adj]
    tauto
  have hSep {x y : V} (h : O.Adj x y) (hE : E.digraph.Adj x y) : False := by
    obtain ⟨hEx,hEt⟩ := mem_sdiff.mp ((E.slots x).1.mp ⟨y,hE⟩)
    rcases h with h | h
    · have hQx : ∃ y, Q.digraph.Adj x y := ⟨y,hQ.symm ▸ h⟩
      obtain ⟨hx,hc⟩ := mem_sdiff.mp ((Q.slots x).1.mp hQx)
      have hmeet := clusterIntervalVertices_inter A (by omega : s ≤ c) hct hDisA
      have he : x ∈ clusterIntervalVertices A s c ∩ clusterIntervalVertices A c t :=
        mem_inter.mpr ⟨hx,hEx⟩
      rw [hmeet] at he
      exact hc he
    · obtain ⟨j,i,hi,hir,rfl,_⟩ := Digraph.iSup_adj.mp h
      have hMeet' : clusterIntervalVertices A s t ∩ clusterIntervalVertices B 0 n = B n ∪ B 0 := hMeet
      have hEx' : R.vertex i j ∈ clusterIntervalVertices A s t := by
        obtain ⟨w,hcw,hwt,hw⟩ := (mem_clusterIntervalVertices A c t _).mp hEx
        exact (mem_clusterIntervalVertices A s t _).mpr ⟨w,by omega,hwt,hw⟩
      have hRx : R.vertex i j ∈ clusterIntervalVertices B 0 n :=
        (mem_clusterIntervalVertices B 0 n _).mpr ⟨i,hi,hir.le,R.part i hi hir.le j⟩
      have hEnd₀ : B 0 = A t := hB₀
      rcases mem_union.mp (hMeet' ▸ mem_inter.mpr ⟨hEx',hRx⟩) with hn | h₀
      · exact disjoint_left.mp (hDisB i n hir.le le_rfl (by omega)) (R.part i hi hir.le j) hn
      · apply hEt
        change R.vertex i j ∈ A t
        rwa [←hEnd₀]
  exact ⟨⟨O,σ,hO,sup_le P.unionPaths_le R.unionPaths_le,hSep⟩,⟨H₀⟩,hTrace⟩

/-- Complete the ordinary paths by the exceptional cover and a
prescribed return, retaining the three marked physical arcs in
each row. The same return splits into two cycles. -/
theorem OrderedClusterPaths.exists_closed_parity_factor {D H : Digraph V}
    {k s a b c t m r : ℕ} {ε d : ℝ}
    (X : Fin k → Finset V) (hk : 0 < k) (hsa : s < a) (hab : a < b) (hbc : b+1 ≤ c)
    (hct : c ≤ t) (htk : t < k) (hnt : 3 ≤ k+s-t)
    (hCover : ∀ x, ∃ i, x ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m)
    (P : OrderedClusterPaths D (cyclicCluster X hk) (Fin m × Fin 2) s c)
    (j₀ : Fin m)
    (E : IntervalPathCover H (clusterIntervalVertices (cyclicCluster X hk) c t)
      (cyclicCluster X hk c) (cyclicCluster X hk t))
    (hPair : ∀ i, IsLowerSuperregularPair D ε d (X i) (X (finRotate k i)))
    (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1) (hr : 0 < r)
    (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    ∃ F : OrderedParityFactor D E.digraph,
      (∀ l, F.mark (l,0) = P.vertex s (j₀,cycleAbsorberLane l) ∧
        F.permutation (F.mark (l,0)) = P.vertex (s+1) (j₀,cycleAbsorberLane l)) ∧
      (∀ l, F.mark (l,1) = P.vertex a (j₀,cycleAbsorberLane l) ∧
        F.permutation (F.mark (l,1)) = P.vertex (a+1) (j₀,cycleAbsorberLane l)) ∧
      ∀ l, F.mark (l,2) = P.vertex b (j₀,cycleAbsorberLane l) ∧
        F.permutation (F.mark (l,2)) = P.vertex (b+1) (j₀,cycleAbsorberLane l) := by
  have hsc : s ≤ c := by omega
  obtain ⟨F,⟨H₀⟩,hTrace⟩ := P.exists_closed_winding_parity_factor X hk hsc
    (by omega) hct htk hnt hCover hDis hSize E hPair hε hGap hd hr hCut hBudget
  let σ := F.permutation
  let mark₀ := (P.orderAt s le_rfl hsc).toEmbedding.trans
    (Embedding.subtype (· ∈ cyclicCluster X hk s))
  let seed : Bool ↪ V := ⟨fun l => mark₀ (j₀,cycleAbsorberLane l),fun l l' he =>
    cycleAbsorberLane.injective (congrArg Prod.snd (mark₀.injective he))⟩
  have hPeriod (l : Bool) : b-s < minimalPeriod (σ : V → V) (seed l) := by
    let p := minimalPeriod (σ : V → V) (seed l)
    have hp : 0 < p := minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts (seed l))
    by_contra! h
    change p ≤ b-s at h
    have he : (σ : V → V)^[p] (seed l) = seed l := isPeriodicPt_minimalPeriod _ _
    change (σ : V → V)^[p] (mark₀ (j₀,cycleAbsorberLane l)) = P.vertex s (j₀,cycleAbsorberLane l) at he
    rw [hTrace _ p (by omega)] at he
    have hne := (P.unique_coordinates
      (fun i j hi hi' hj hj' hn => cyclicCluster_distinct hk hDis (by
        rwa [Nat.mod_eq_of_lt (hi'.trans_lt (hct.trans_lt htk)),
          Nat.mod_eq_of_lt (hj'.trans_lt (hct.trans_lt htk))]))
      (by omega : s ≤ s+p) (by omega : s+p ≤ c) le_rfl (by omega : s ≤ c) he).1
    omega
  obtain ⟨M,⟨hM⟩,h₀,h₁,h₂⟩ :=
    markedBicycle.exists_three_column_order σ seed (H₀.bicycle_at_copy j₀)
      (a-s) (b-s) (by omega) (by omega) hPeriod
  have hAt (l : Bool) (i : ℕ) (hi : s+i+1 ≤ c) :
      (σ : V → V)^[i] (seed l) = P.vertex (s+i) (j₀,cycleAbsorberLane l) ∧
      σ ((σ : V → V)^[i] (seed l)) = P.vertex (s+i+1) (j₀,cycleAbsorberLane l) := by
    refine ⟨hTrace _ i (by omega),?_⟩
    rw [←iterate_succ_apply' (σ : V → V) i (seed l)]
    exact hTrace _ (i+1) (by omega)
  refine ⟨⟨F.ordinary,σ,M,hM,F.exact_factor,F.ordinary_le,F.ordinary_separate⟩,?_,?_,?_⟩
  · intro l
    change M (l,0) = _ ∧ σ (M (l,0)) = _
    rw [h₀]
    exact hAt l 0 (by omega)
  · intro l
    change M (l,1) = _ ∧ σ (M (l,1)) = _
    rw [h₁]
    have h := hAt l (a-s) (by omega)
    rwa [show s+(a-s) = a by omega] at h
  · intro l
    change M (l,2) = _ ∧ σ (M (l,2)) = _
    rw [h₂]
    have h := hAt l (b-s) (by omega)
    rwa [show s+(b-s) = b by omega] at h

end OverfullWork.DirectedRobustExpansion
