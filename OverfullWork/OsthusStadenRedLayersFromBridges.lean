module

public import OverfullWork.OsthusStadenPhysicalRedLayerCompletion
public import OverfullWork.OsthusStadenSpecialExceptionOnLayers

@[expose] public section


/-! Use the same red labels, trim and physical reserves for the entire
exceptional-arc construction of §5.6–§5.7. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u v

set_option maxHeartbeats 3000000 in
/-- With the scalar margins for the core and special exceptional sets,
construct the complete red layers on the original vertices. Both
arc selections use the bridge deletions already made in the input. -/
theorem exists_osthus_staden_red_layers_from_bridges
    (r s p capTypes : ℕ) [NeZero (2*s)] [NeZero p]
    (hs : 4 ≤ s) (hp : 3 ≤ p) (hpOdd : Odd p)
    (splitCore splitSpecial : ℝ) (hSplitCore : 0 < splitCore) (hSplitSpecial : 0 < splitSpecial) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      {m₀ b mBase m : ℕ} {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
      {β γ η a exc : ℝ} (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc)
      {E : Fin r → I → Digraph V} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I}
      {εBase τ ε δ d : ℝ}
      (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster B.partition i) (2*s) p mBase εBase εBase εBase)
      (R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster (g t) i) (2*s) p m τ τ τ)
      (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ ε d R)
      (D : PrimaryRedSelection (p := p) A.coordinates) (C : Equiv.Perm I)
      (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
      (src dst : RefinedFactorIndex r (2*s) p → I → RefinedVertex I (2*s) p)
      (κ loss : ℕ) (minDegree capSpecial : ℝ),
      N ≤ Fintype.card V → H ≤ G →
      (∀ t i, cluster (g t) i ⊆ cluster B.partition i) →
      (∀ j u, erase j u ∈ primaryPCells (R j.1) u) →
      Function.Injective (fun q : RefinedFactorIndex r (2*s) p × RefinedVertex I (2*s) p => erase q.1 q.2) →
      (∀ j i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧ D.selectedPCell true j (dst j i)) →
      (∀ x, B.partition x ≠ none → ((univ : Finset (Fin r)).filter (fun t => g t x = none)).card ≤ capTypes) →
      0 ≤ εBase → 8*εBase ≤ 1/9 →
      (∀ t (i : PrimaryHalfIndex I (2*s) p),
        ((primaryHalfOfIndex base i) \ primaryHalfOfIndex (R t) i).card ≤ loss) →
      (∀ x, B.partition x = none → minDegree ≤ (inDegree G x:ℝ) ∧ minDegree ≤ (outDegree G x:ℝ)) →
      let cell := fun (j : RefinedFactorIndex r (2*s) p) => primaryPCells (R j.1)
      let trim := fun j u => (cell j u).erase (erase j u)
      let ordinary := fun j => univ.biUnion (trim j)
      let Z := exceptional B.partition
      let bridges := bridgeCenters erase src
      let S := specialExceptions Z cell erase bridges
      let halfIn := fun (j : RefinedFactorIndex r (2*s) p) i =>
        primaryHalfCell (R j.1) ((A.factor j).symm (src j i)) (redPhase p j.1.val).2
      let halfOut := fun (j : RefinedFactorIndex r (2*s) p) i =>
        primaryHalfCell (R j.1) (dst j i) (redPhase p j.1.val).2
      let kCore := exceptionalPhaseBankSize r (2*s) p
      let kSpecial := capTypes*((2*s-1)*(p-1))+1
      let ell := ((2*s)*p*2:ℕ)
      let e := 8*εBase
      let volume := (Fintype.card I:ℝ)*((s-1:ℕ):ℝ)
      let total := γ*a*(Fintype.card V:ℝ)
      let capCore := (Z.card:ℝ)/(kCore:ℝ)+splitCore*(Fintype.card V:ℝ)
      (κ:ℝ) ≤ ((s-1:ℕ):ℝ)*(1-e)*(minDegree-(Z.card:ℝ)-e*((Fintype.card I:ℝ)*((ell*mBase:ℕ):ℝ))) /
          ((ell:ℝ)*(kCore:ℝ)) -
        volume*(splitCore*(Fintype.card V:ℝ)+((loss+1:ℕ):ℝ)/(kCore:ℝ)) →
      volume*((1-e)*(e*(B.size:ℝ)/(ell:ℝ))+((loss+1:ℕ):ℝ)) ≤ total/(180*(p:ℝ)) →
      volume*e*(B.size:ℝ) ≤ total/(3*(p:ℝ)) →
      (κ:ℝ)+splitSpecial*(Fintype.card V:ℝ) ≤ (total/(20*(p:ℝ)))/(kSpecial:ℝ) →
      (∀ j, ((S j).card:ℝ)/(kSpecial:ℝ)+splitSpecial*(Fintype.card V:ℝ) ≤ capSpecial) →
      ∀ (P : TrimmedPhysicalBridgeLayers G (unwoundSlice E A.label A.factor) A.factor C
          cell erase src dst halfIn halfOut κ (2*m) δ d),
        P.UsesBridgeReserves (primaryThinDigraphs B 1) (primaryThinDigraphs B 0) →
        ∃ F : RefinedFactorIndex r (2*s) p → Digraph V,
          OsthusStadenRedLayerProperties G (primaryThinDigraphs B 4) (unwoundSlice E A.label A.factor)
            F A.factor ordinary trim D.vertices (fun j i => erase j (src j i))
            P.incoming P.outgoing κ (1+capCore+capSpecial) δ d := by
  have hpPos : 0 < p := by omega
  obtain ⟨NCore,hNCore⟩ := exists_core_exception_arcs_on_trimmed_layers.{u,v} r s p
    (by omega) hp hpOdd splitCore hSplitCore
  obtain ⟨NSpecial,hNSpecial⟩ := exists_special_exception_arcs_on_trimmed_layers.{u,v} r s p capTypes
    hs hpPos splitSpecial hSplitSpecial
  refine ⟨max NCore NSpecial,?_⟩
  intro V _ I _ m₀ b mBase m G H f M β γ η a exc B E g σ εBase τ ε δ d base R A D C erase src dst κ loss
    minDegree capSpecial hSize hHost hParent hErase hFresh hRed hTypes hεBase hSmall hLoss hMin
    cell trim ordinary Z bridges S halfIn halfOut kCore kSpecial ell e volume total capCore hCoreBudget
    hLower hUpper hDemand hRoom P hRes
  obtain ⟨core,hCoreG,hCoreDis,hCoreArc,hCoreDegree,hCoreCap⟩ := hNCore D G (primaryThinDigraphs B) E
    B.partition g mBase m εBase τ base R erase κ loss minDegree ((le_max_left _ _).trans hSize)
    hεBase (by linarith only [hSmall]) hLoss hMin hCoreBudget
  obtain ⟨special,hSpecialRes,hSpecialDis,hSpecialArc,hSpecialDegree,hSpecialCap⟩ :=
    hNSpecial B base R A D erase bridges hFresh hTypes 2 3 (by decide) κ loss capSpecial
      ((le_max_right _ _).trans hSize) hεBase hSmall hLoss hLower hUpper hDemand hRoom
  let L := RefinedFactorIndex r (2*s) p
  have hHalf (q : Bool) (j : L) (i : I) (z : Fin (2*s)) (hz : z ∈ D.select q j i) (x : V)
      (hx : x ∈ (primaryHalfOfIndex (R j.1) (i,z,redPhase p j.1.val)).erase (erase j (redPLabel j.1.val i z))) :
      x ∈ ordinary j ∧ x ∈ D.vertices q j := by
    constructor
    · exact clipped_primary_half_mem_ordinary (R j.1) (erase j) (redPLabel j.1.val i z) _ hx
    · exact D.mem_vertices_of_mem_selected_half q j _ x ⟨i,z,hz,rfl⟩ (mem_erase.mp hx).2
  have hSpecRed (q : Bool) (j : L) (x : V) (hx : x ∈ specialRedTargets D base R erase q j) :
      x ∈ ordinary j ∧ x ∈ D.vertices q j := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hx
    obtain ⟨z,hz,hx⟩ := mem_biUnion.mp hi
    exact hHalf q j i z hz x (mem_inter.mp hx).2
  refine ⟨fun j => (P.graph j ⊔ core j) ⊔ special j,?_⟩
  apply complete_osthus_staden_red_layers B A D C erase src dst κ capCore capSpecial hHost hParent hErase hRed
    core special P hRes hCoreG hSpecialRes hCoreDis hSpecialDis ?_ ?_
    hCoreDegree hSpecialDegree hCoreCap hSpecialCap
  · intro j x y h
    rcases hCoreArc j x y h with ⟨hx,_,i,z,hz,hy⟩ | ⟨hy,_,i,z,hz,hx⟩
    · exact Or.inl ⟨hx,hHalf true j i z hz y hy⟩
    · exact Or.inr ⟨hy,hHalf false j i z hz x hx⟩
  · intro j x y h
    rcases hSpecialArc j x y h with ⟨hx,_,hy⟩ | ⟨hy,_,hx⟩
    · exact Or.inl ⟨hx,hSpecRed true j y hy⟩
    · exact Or.inr ⟨hy,hSpecRed false j x hx⟩

end OverfullWork.DirectedRobustExpansion
