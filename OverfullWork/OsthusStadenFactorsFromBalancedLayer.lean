module

public import OverfullWork.OsthusStadenSliceArcTransport
public import OverfullWork.OsthusStadenMergeConfiguration

@[expose] public section


/-! Extract the physical 1-factors of §5.10 while retaining H3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- Quantitative margins for the dense successor-pair completion. -/
structure OsthusStadenDenseFactorMargins
    (n κ cutoff minDemand : ℕ) (ε d : ℝ) : Prop where
  cutoff_pos : 0 < cutoff
  large_rectangles : (n:ℝ)*ε ≤ cutoff
  available_degree : (κ:ℝ)+2*(cutoff:ℝ) ≤ (d-ε)*(n:ℝ)
  density_nonneg : 0 ≤ d-2*ε
  min_le_target : minDemand ≤ κ
  target_le_twice_min : κ ≤ 2*minDemand
  lower_density_demand : 2*(d-2*ε)*(n:ℝ) ≤ 3*(minDemand:ℝ)
  target_le_density : (κ:ℝ) ≤ (d-2*ε)*(n:ℝ)
  residual_slack : (d-2*ε)*(n:ℝ)-(minDemand:ℝ) ≤
    2*((d-2*ε)*(n:ℝ)-(κ:ℝ))

/-- A factor family with its own physical coordinates, its untouched
H3 pairs, and all incidence data needed by §5.11. -/
structure OsthusStadenPhysicalFactors {V U : Type*} [Fintype V]
    (G : Digraph V) (ordinary : Finset V) (cell : U → Finset V) (factor : Equiv.Perm U)
    (red : Finset (V × V)) (n κ : ℕ) (ε d : ℝ) where
  coord : SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n) ≃ V
  exceptional_coord : ∀ x, coord (.inl x) = x.val
  ordinary_coord : ∀ u, (univ : Finset (Fin n)).map (sliceCellEmbedding coord u) = cell u
  reserve : U → Digraph (Fin n)
  factors : Fin κ → Equiv.Perm (SliceVertex ↥(ordinaryᶜ : Finset V) U (Fin n))
  uses_red_or_successor : ∀ f, UsesSliceArcs factor
    (red.map (Equiv.prodCongr coord.symm coord.symm).toEmbedding) (factors f)
  factors_disjoint : ∀ f g, f ≠ g → ∀ x, factors f x ≠ factors g x
  factor_arcs : ∀ f x, G.Adj (coord x) (coord (factors f x))
  red_covered : ∀ e ∈ red, ∃ f, coord (factors f (coord.symm e.1)) = e.2
  reserve_arcs : ∀ u x y, (reserve u).Adj x y →
    G.Adj (coord (.inr (u,x))) (coord (.inr (factor u,y)))
  reserve_fresh : ∀ u x y f, (reserve u).Adj x y → factors f (.inr (u,x)) ≠ .inr (factor u,y)
  reserve_regular : ∀ u, IsCentredSuperregular (reserve u) ε d

universe u v

set_option maxHeartbeats 1900000 in
/-- Separate H3, then extract the κ factors of a balanced physical
layer. Every red arc lies in a factor and each ordinary factor arc
comes from the remainder of a successor pair. -/
theorem exists_factors_and_h3_of_balanced_physical_layer
    (fraction ε δ : ℝ) (hp : 0 < fraction) (hp₁ : fraction ≤ 1)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hSmall : ε ≤ δ/4) :
    ∃ N : ℕ, ∀ {U : Type u} [Fintype U] {V : Type v} [Fintype V]
      (D G : Digraph V) (factor : Equiv.Perm U) (ordinary : Finset V) (cell : U → Finset V)
      (label : V → Option U) (A : Finset (V × V)) (n κ cutoff minDemand : ℕ) (d : ℝ),
      N ≤ n → D ≤ G → digraphOfArcs A ≤ G →
      univ.biUnion cell = ordinary →
      (∀ u v, u ≠ v → Disjoint (cell u) (cell v)) →
      (∀ u, (cell u).card = n) →
      (∀ u x, label x = some u ↔ x ∈ cell u) →
      (∀ u, IsSuperregularPair D ε d (cell u) (cell (factor u))) →
      Disjoint D (digraphOfArcs A) →
      (∀ u, clusterArcMass label A true u = clusterArcMass label A false (factor u)) →
      (∀ x, x ∉ ordinary → inDegree (digraphOfArcs A) x = κ ∧ outDegree (digraphOfArcs A) x = κ) →
      (∀ x ∈ ordinary, inDegree (digraphOfArcs A) x ≤ κ-minDemand ∧ outDegree (digraphOfArcs A) x ≤ κ-minDemand) →
      OsthusStadenDenseFactorMargins n κ cutoff minDemand δ ((1-fraction)*d) →
      Nonempty (OsthusStadenPhysicalFactors G ordinary cell factor A n κ δ (fraction*d)) := by
  obtain ⟨N,hN⟩ := exists_h3_of_physical_successor_pairs.{u,v} fraction ε δ hp hp₁ hε hδ hδ₁ hSmall
  refine ⟨N,?_⟩
  intro U _ V _ D G factor ordinary cell label A n κ cutoff minDemand d hSize hD hA hCover hDis hCard hLabel
    hPair hRedDis hBalance hExact hCap margin
  obtain ⟨coord,hExc,hMap,H,R,hH,hR,hSep,hSplit⟩ := hN D factor ordinary cell n d hSize hCover hDis hCard hPair
  let A' := A.map (Equiv.prodCongr coord.symm coord.symm).toEmbedding
  have hCell (u : U) : cell u ⊆ ordinary := by
    intro x hx
    rw [←hCover]
    exact mem_biUnion.mpr ⟨u,mem_univ _,hx⟩
  have hRle (u : U) : R u ≤ pullDirectedPair (sliceCellEmbedding coord u) (sliceCellEmbedding coord (factor u)) D :=
    le_sup_right.trans_eq (hSplit u).symm
  have hHle (u : U) : H u ≤ pullDirectedPair (sliceCellEmbedding coord u) (sliceCellEmbedding coord (factor u)) D :=
    le_sup_left.trans_eq (hSplit u).symm
  obtain ⟨hBal,hEx,hLoad,hDisRed⟩ := balanced_red_data_in_successor_coordinates ordinary cell label coord
    hExc hMap hCell hLabel factor D R A κ minDemand hRle hRedDis hBalance hExact hCap
  obtain ⟨F,S,hS,hCounts,hFDis⟩ := exists_factors_of_balanced_physical_arcs factor A' R κ cutoff minDemand δ
    ((1-fraction)*d) hBal hEx hLoad hR hDisRed margin.cutoff_pos
    (by simpa only [Fintype.card_fin] using margin.large_rectangles)
    (by simpa only [Fintype.card_fin] using margin.available_degree)
    margin.density_nonneg margin.min_le_target margin.target_le_twice_min
    (by simpa only [Fintype.card_fin] using margin.lower_density_demand)
    (by simpa only [Fintype.card_fin] using margin.target_le_density)
    (by simpa only [Fintype.card_fin] using margin.residual_slack)
  have hMem := (transport_balanced_arc_data coord sliceLabel label
    (physical_label_eq_sliceLabel ordinary cell label coord hExc hMap hCell hLabel) A).1
  have hUse := factor_uses_physical_arc factor A' S F hCounts
  refine ⟨⟨coord,hExc,hMap,H,F,?_,hFDis,?_,?_,?_,?_,hH⟩⟩
  · intro f x
    exact (hUse f x).imp_right (fun ⟨u,a,b,hx,hy,_⟩ => ⟨u,a,b,hx,hy⟩)
  · intro f x
    rcases hUse f x with h | ⟨u,a,b,hx,hy,h⟩
    · exact hA ((hMem _ _).mp h)
    · have hy' : F f (.inr (u,a)) = .inr (factor u,b) := hx ▸ hy
      rw [hx,hy']
      exact hD (hRle u (hS u h))
  · rintro ⟨x,y⟩ h
    have hRed := (hMem (coord.symm x) (coord.symm y)).mpr (by simpa only [coord.apply_symm_apply] using h)
    have hPos : 0 < arcMultiplicity A' (coord.symm x) (coord.symm y) +
        DirectedMultigraphFactors.successorPairArcs factor S (coord.symm x) (coord.symm y) := by
      rw [arcMultiplicity,if_pos hRed]
      omega
    rw [← hCounts] at hPos
    obtain ⟨j,hj⟩ := card_pos.mp hPos
    simp only [mem_filter,mem_univ,true_and] at hj
    exact ⟨j,(congrArg coord hj).trans (coord.apply_symm_apply y)⟩
  · intro u x y h
    exact hD (hHle u h)
  · intro u x y f h he
    rcases hUse f (.inr (u,x)) with hRed | ⟨v,a,b,hx,hy,hB⟩
    · rw [he] at hRed
      exact disjoint_iff_inf_le.mp hRedDis ⟨hHle u h,(hMem _ _).mp hRed⟩
    · have h₁ := Sum.inr.inj hx
      have huv : u = v := congrArg Prod.fst h₁
      have hxa : x = a := congrArg Prod.snd h₁
      subst v
      subst a
      have hyb : y = b := congrArg Prod.snd (Sum.inr.inj (he.symm.trans hy))
      subst b
      exact disjoint_iff_inf_le.mp (hSep u) ⟨h,hS u hB⟩

end OverfullWork.DirectedRobustExpansion
