module

public import OverfullWork.KuhnOsthusPrescribedIntervalReturn
public import OverfullWork.KuhnOsthusCycleAbsorberMarkOrder

@[expose] public section


/-! Close the auxiliary factor of Lemma 10.3 after its two switch
pairs and the repair pair. The forward part includes the complete
exceptional path system, and the return advances one copy in the
same row. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*} [Fintype V]

def IntervalPathCover.castBoundaries {G : Digraph V} {U S T S' T' : Finset V}
    (X : IntervalPathCover G U S T) (hS : S = S') (hT : T = T') :
    IntervalPathCover G U S' T' :=
  hT ▸ hS ▸ X

omit [Fintype V] in
theorem IntervalPathCover.castBoundaries_digraph {G : Digraph V} {U S T S' T' : Finset V}
    (X : IntervalPathCover G U S T) (hS : S = S') (hT : T = T') :
    (X.castBoundaries hS hT).digraph = X.digraph := by
  subst S'
  subst T'
  rfl

/-- The cycles of the physical reserve are exactly the orbits of the
copy-and-row return. Its initial traces still pass through the two
switch layers and the repair layer. -/
theorem OrderedClusterPaths.exists_closed_reserve_tour_in {G H : Digraph V}
    {A : ℕ → Finset V} {m : ℕ} (S : OrderedClusterPaths G A (Fin m × Fin 2) 3 12)
    (B : ℕ → Finset V) (n b c : ℕ) (hb : 15 ≤ b) (hc : b ≤ c) (hn : 3 ≤ n)
    (hB₀ : B 0 = A c) (hBn : B n = A 3)
    (E : IntervalPathCover H (clusterIntervalVertices A b c) (A b) (A c))
    (hAll : clusterIntervalVertices A 3 c ∪ clusterIntervalVertices B 0 n = univ)
    (hMeet : clusterIntervalVertices A 3 c ∩ clusterIntervalVertices B 0 n = B n ∪ B 0)
    (hSizeA : ∀ i, 12 ≤ i → i ≤ b → (A i).card = 2*m)
    (hDisA : ∀ i j, 3 ≤ i → i ≤ c → 3 ≤ j → j ≤ c → i ≠ j → Disjoint (A i) (A j))
    (hSizeB : ∀ i ≤ n, (B i).card = 2*m)
    (hDisB : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (B i) (B j))
    (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hPairsA : ∀ i, 12 ≤ i → i < b → IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (hPairsB : ∀ i < n, IsLowerSuperregularPair G ε d (B i) (B (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    let mark := (S.orderAt 3 le_rfl (by decide)).toEmbedding.trans (Embedding.subtype (· ∈ A 3))
    ∃ (P : OrderedClusterPaths G A (Fin m × Fin 2) 12 b)
      (R : OrderedClusterPaths G B (Fin m × Fin 2) 0 n) (σ : Equiv.Perm V),
      (∀ x y, (((S.unionPaths ⊔ P.unionPaths) ⊔ E.digraph) ⊔ R.unionPaths).Adj x y ↔ σ x = y) ∧
      (∀ j i, i ≤ 9 → (σ : V → V)^[i] (mark j) = S.vertex (3+i) j) ∧
      ∃ H : MarkedCycleSegments σ mark (cycleAbsorberReturn m), ∀ j, 8 < H.span j := by
  intro mark
  let e := S.orderAt 3 le_rfl (by decide)
  let f : Fin m × Fin 2 ≃ A b := (cycleAbsorberSwitchSlot m).trans
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hSizeA b (by omega) le_rfl)).symm
  obtain ⟨P,hP₀,_⟩ := exists_ordered_cluster_paths G A 12 b (2*m) r hb
    (S.orderAt 12 (by decide) le_rfl) f ε d hε hGap hd hr hCut hBudget hSizeA
    (fun i j hi hir hj hjr h => hDisA i j (by omega) (hir.trans hc) (by omega) (hjr.trans hc) h) hPairsA
  let O := S.concat P (fun j => (hP₀ j).symm)
  have hO : O.unionPaths = S.unionPaths ⊔ P.unionPaths := by
    ext x y
    simp only [OrderedClusterPaths.unionPaths,Digraph.iSup_adj,Digraph.sup_adj]
    constructor
    · rintro ⟨j,i,hi,hir,hx,hy⟩
      by_cases h : i < 12
      · exact .inl ⟨j,i,hi,h,hx.trans (S.concat_left P _ h.le j),
          hy.trans (S.concat_left P _ (by omega) j)⟩
      · exact .inr ⟨j,i,by omega,hir,hx.trans (S.concat_right P _ (by omega) j),
          hy.trans (S.concat_right P _ (by omega) j)⟩
    · rintro (⟨j,i,hi,hir,hx,hy⟩ | ⟨j,i,hi,hir,hx,hy⟩)
      · exact ⟨j,i,hi,by omega,hx.trans (S.concat_left P _ hir.le j).symm,
          hy.trans (S.concat_left P _ (by omega) j).symm⟩
      · exact ⟨j,i,by omega,hir,hx.trans (S.concat_right P _ hi j).symm,
          hy.trans (S.concat_right P _ (by omega) j).symm⟩
  obtain ⟨Q,hQ,_⟩ := O.exists_interval_path_cover (by omega : 3 ≤ b)
    (fun i j hi hir hj hjr h => hDisA i j hi (hir.trans hc) hj (hjr.trans hc) h)
  let Q' := Q.rehost (le_sup_left : G ≤ G ⊔ H)
  let E' := E.rehost (le_sup_right : H ≤ G ⊔ H)
  obtain ⟨U,hU,_⟩ := Q'.exists_concat E'  (clusterIntervalVertices_inter A (by omega : 3 ≤ b) hc hDisA)
  let U' := U.castSupport (clusterIntervalVertices_union A (by omega : 3 ≤ b) hc)
  let V' := U'.castBoundaries hBn.symm hB₀.symm
  have hV' : V'.digraph = (S.unionPaths ⊔ P.unionPaths) ⊔ E.digraph := by
    dsimp only [V',U']
    rw [IntervalPathCover.castBoundaries_digraph,IntervalPathCover.castSupport_digraph,hU]
    change Q.digraph ⊔ E.digraph = _
    rw [hQ,hO]
  let e' : Fin m × Fin 2 ≃ B n := e.trans (Equiv.subtypeEquivRight (fun x => by rw [hBn]))
  obtain ⟨R,σ,hσ,_,⟨K⟩⟩ := V'.exists_factor_with_prescribed_return_in B n (2*m) r hn e'
    (cycleAbsorberReturn m) hAll hMeet (hDisB n 0 le_rfl (by omega) (by omega)) hSizeB hDisB
    ε d hε hGap hd hPairsB hr hCut hBudget
  rw [hV'] at hσ
  have H : MarkedCycleSegments σ mark (cycleAbsorberReturn m) :=
    K.reindex e' (cycleAbsorberReturn m) (fun j => by
      simp only [Equiv.trans_apply,Equiv.symm_apply_apply])
  have hTrace (j : Fin m × Fin 2) (i : ℕ) (hi : i ≤ 9) :
      (σ : V → V)^[i] (mark j) = S.vertex (3+i) j := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [iterate_succ_apply',ih (by omega)]
      apply (hσ _ _).mp
      exact .inl (.inl (.inl (Digraph.iSup_adj.mpr ⟨j,3+i,by omega,by omega,rfl,rfl⟩)))
  refine ⟨P,R,σ,hσ,hTrace,H,?_⟩
  intro j
  by_contra! hj
  have hi := H.positive j
  have hx := hTrace j (H.span j) (by omega)
  rw [H.finish] at hx
  have hSource : mark (cycleAbsorberReturn m j) ∈ A 3 := S.part 3 le_rfl (by decide) _
  have hHit := S.part (3+H.span j) (by omega) (by omega) j
  exact disjoint_left.mp (hDisA 3 (3+H.span j) le_rfl (by omega) (by omega) (by omega) (by omega))
    hSource (hx.symm ▸ hHit)

/-- The cycles of the physical reserve are exactly the orbits of the
copy-and-row return. Its initial traces still pass through the two
switch layers and the repair layer. -/
theorem OrderedClusterPaths.exists_closed_reserve_tour {G : Digraph V}
    {A : ℕ → Finset V} {m : ℕ} (S : OrderedClusterPaths G A (Fin m × Fin 2) 3 12)
    (B : ℕ → Finset V) (n b c : ℕ) (hb : 15 ≤ b) (hc : b ≤ c) (hn : 3 ≤ n)
    (hB₀ : B 0 = A c) (hBn : B n = A 3)
    (E : IntervalPathCover G (clusterIntervalVertices A b c) (A b) (A c))
    (hAll : clusterIntervalVertices A 3 c ∪ clusterIntervalVertices B 0 n = univ)
    (hMeet : clusterIntervalVertices A 3 c ∩ clusterIntervalVertices B 0 n = B n ∪ B 0)
    (hSizeA : ∀ i, 12 ≤ i → i ≤ b → (A i).card = 2*m)
    (hDisA : ∀ i j, 3 ≤ i → i ≤ c → 3 ≤ j → j ≤ c → i ≠ j → Disjoint (A i) (A j))
    (hSizeB : ∀ i ≤ n, (B i).card = 2*m)
    (hDisB : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (B i) (B j))
    (ε d : ℝ) (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1)
    (hPairsA : ∀ i, 12 ≤ i → i < b → IsLowerSuperregularPair G ε d (A i) (A (i+1)))
    (hPairsB : ∀ i < n, IsLowerSuperregularPair G ε d (B i) (B (i+1)))
    (r : ℕ) (hr : 0 < r) (hCut : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ))) :
    let mark := (S.orderAt 3 le_rfl (by decide)).toEmbedding.trans (Embedding.subtype (· ∈ A 3))
    ∃ (P : OrderedClusterPaths G A (Fin m × Fin 2) 12 b)
      (R : OrderedClusterPaths G B (Fin m × Fin 2) 0 n) (σ : Equiv.Perm V),
      (∀ x y, (((S.unionPaths ⊔ P.unionPaths) ⊔ E.digraph) ⊔ R.unionPaths).Adj x y ↔ σ x = y) ∧
      (∀ j i, i ≤ 9 → (σ : V → V)^[i] (mark j) = S.vertex (3+i) j) ∧
      ∃ H : MarkedCycleSegments σ mark (cycleAbsorberReturn m), ∀ j, 8 < H.span j :=
  S.exists_closed_reserve_tour_in B n b c hb hc hn hB₀ hBn E hAll hMeet hSizeA hDisA
    hSizeB hDisB ε d hε hGap hd hPairsA hPairsB r hr hCut hBudget

end OverfullWork.DirectedRobustExpansion
