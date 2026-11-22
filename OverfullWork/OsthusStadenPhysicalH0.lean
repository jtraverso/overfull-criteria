module

public import OverfullWork.OsthusStadenSlicesFromPrimaryFactors

@[expose] public section


/-! Read (H0) in the original vertex type, on the retained base cells. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical

/-- A base reduced pair retains the H0 lower bounds in the full reserve,
outside small exceptional sets of vertices in its two physical cells. -/
theorem primary_thin_profiles_of_reduced_pair
    {V I : Type*} [Fintype V] [Fintype I]
    {H : Digraph V} {f : V → Option I} {m₀ b : ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f
      (reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β)
      m₀ b β γ η a exc)
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 < η) (hηOne : η ≤ 1)
    (δ d : ℝ) (hδ : 0 ≤ δ) (hErr : 4*η ≤ γ*β) (hBad : η ≤ δ*β)
    (q : Fin 5) (u v : I) (hAdj : (quotient H f).Adj u v)
    (hDen : d+β ≤ density H (cluster f u) (cluster f v)) :
    let T := primaryThinDigraphs B q
    ∃ badOut badIn : Finset V,
      (badOut.card:ℝ) ≤ δ*(B.size:ℝ) ∧ (badIn.card:ℝ) ≤ δ*(B.size:ℝ) ∧
      (∀ x ∈ cluster B.partition u, x ∉ badOut →
        γ*d*(B.size:ℝ)/2 ≤ profileCount (cluster B.partition v) (outProfile T x)) ∧
      ∀ y ∈ cluster B.partition v, y ∉ badIn →
        γ*d*(B.size:ℝ)/2 ≤ profileCount (cluster B.partition u) (inProfile T y) := by
  let M := reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β
  let J := (univ : Finset (ReducedCopy M)).filter (fun e => e.1 = (u,v))
  let S := indexedArcUnion J (B.thin q)
  let T := primaryThinDigraphs B q
  let coord (i : I) := (B.kept i).trans (B.base i)
  have hCell (i : I) : (univ : Finset (Fin B.size)).map (coord i) = cluster B.partition i :=
    B.retained_cells i
  obtain ⟨badOut,badIn,hOut,hIn,hOutDeg,hInDeg⟩ :=
    osthus_staden_h0_on_primary_pair B hβ hγ hη hηOne δ d hδ hErr hBad q u v hAdj hDen
  have hEdge (x y : Fin B.size) (h : S.Adj x y) : T.Adj (coord u x) (coord v y) := by
    obtain ⟨i,hi,ha⟩ := h
    have he := (mem_filter.mp hi).2
    have hU : i.1.1 = u := congrArg Prod.fst he
    have hV : i.1.2 = v := congrArg Prod.snd he
    exact ⟨i,x,y,congrArg (fun t => coord t x) hU,congrArg (fun t => coord t y) hV,ha⟩
  refine ⟨badOut.map (coord u),badIn.map (coord v),by simpa only [card_map] using hOut,
    by simpa only [card_map] using hIn,?_,?_⟩
  · intro x hx hx'
    rw [←hCell u] at hx
    obtain ⟨z,_,rfl⟩ := mem_map.mp hx
    have hz : z ∉ badOut := fun hz => hx' (mem_map.mpr ⟨z,hz,rfl⟩)
    have hMap : (outProfile S z).map (coord v) ⊆ cluster B.partition v ∩ outProfile T (coord u z) := by
      intro y hy
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hy
      exact mem_inter.mpr ⟨(hCell v) ▸ mem_map.mpr ⟨w,mem_univ _,rfl⟩,
        mem_filter.mpr ⟨mem_univ _,hEdge z w (mem_filter.mp hw).2⟩⟩
    have h := card_le_card hMap
    rw [card_map] at h
    exact (hOutDeg z hz).trans (by unfold profileCount; exact_mod_cast h)
  · intro y hy hy'
    rw [←hCell v] at hy
    obtain ⟨z,_,rfl⟩ := mem_map.mp hy
    have hz : z ∉ badIn := fun hz => hy' (mem_map.mpr ⟨z,hz,rfl⟩)
    have hMap : (inProfile S z).map (coord u) ⊆ cluster B.partition u ∩ inProfile T (coord v z) := by
      intro x hx
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hx
      exact mem_inter.mpr ⟨(hCell u) ▸ mem_map.mpr ⟨w,mem_univ _,rfl⟩,
        mem_filter.mpr ⟨mem_univ _,hEdge w z (mem_filter.mp hw).2⟩⟩
    have h := card_le_card hMap
    rw [card_map] at h
    exact (hInDeg z hz).trans (by unfold profileCount; exact_mod_cast h)

end OverfullWork.DirectedRobustExpansion
