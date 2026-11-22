module

public import OverfullWork.OsthusStadenPrimaryReserveData
public import OverfullWork.OsthusStadenReducedBudgets

@[expose] public section


/-! Transport the local H0 bound and retain disjointness of the main
parts on the physical quotient copies. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion DirectedClusterQuotient DirectedPairEnergy
open scoped Classical

variable {V I : Type*} [Fintype V] [Fintype I]
variable {H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
variable {m₀ b : ℕ} {β γ η a exceptionBound : ℝ}

/-- The main parts sit in their respective original copies. -/
theorem OsthusStadenPrimaryReserveData.lift_main_le
    (P : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exceptionBound)
    (e : ReducedCopy M) :
    liftDirectedPair ((P.kept e.1.1).trans (P.base e.1.1))
      ((P.kept e.1.2).trans (P.base e.1.2)) (P.main e) ≤
    liftDirectedPair (P.base e.1.1) (P.base e.1.2) (P.copy e) := by
  rintro x y ⟨p,q,hx,hy,h⟩
  exact ⟨P.kept e.1.1 p,P.kept e.1.2 q,hx,hy,(P.copy_partition e p q).mpr (Or.inl h)⟩

theorem OsthusStadenPrimaryReserveData.lift_main_disjoint
    (P : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exceptionBound)
    (e e' : ReducedCopy M) (hne : e ≠ e') :
    Disjoint (liftDirectedPair ((P.kept e.1.1).trans (P.base e.1.1))
      ((P.kept e.1.2).trans (P.base e.1.2)) (P.main e))
      (liftDirectedPair ((P.kept e'.1.1).trans (P.base e'.1.1))
        ((P.kept e'.1.2).trans (P.base e'.1.2)) (P.main e')) :=
  (P.copy_disjoint e e' hne).mono (P.lift_main_le e) (P.lift_main_le e')

/-- The parallel thin copies of one actual reduced pair give the
typical degree bound H0 after paying the floor error in the density. -/
theorem osthus_staden_h0_on_primary_pair
    (P : OsthusStadenPrimaryReserveData H f
      (reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β)
      m₀ b β γ η a exceptionBound)
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 < η) (hηOne : η ≤ 1)
    (η' d : ℝ) (hη' : 0 ≤ η') (hErr : 4*η ≤ γ*β) (hBad : η ≤ η'*β)
    (j : Fin 5) (u v : I) (hAdj : (quotient H f).Adj u v)
    (hDen : d+β ≤ density H (cluster f u) (cluster f v)) :
    let M' := reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β
    let J := (univ : Finset (ReducedCopy M')).filter (fun e => e.1 = (u,v))
    let S := indexedArcUnion J (P.thin j)
    ∃ badOut badIn : Finset (Fin P.size),
      (badOut.card:ℝ) ≤ η'*(P.size:ℝ) ∧ (badIn.card:ℝ) ≤ η'*(P.size:ℝ) ∧
      (∀ x, x ∉ badOut → γ*d*(P.size:ℝ)/2 ≤ (outDegree S x:ℝ)) ∧
      (∀ x, x ∉ badIn → γ*d*(P.size:ℝ)/2 ≤ (inDegree S x:ℝ)) := by
  let M' := reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β
  let J := (univ : Finset (ReducedCopy M')).filter (fun e => e.1 = (u,v))
  have hCount : d ≤ (J.card:ℝ)*β ∧ (J.card:ℝ)*β ≤ 1 := by
    dsimp only [J]
    rw [reducedCopy_parallel_count]
    have h := reducedMultiplicity_rounding (quotient H f)
      (fun i j => density H (cluster f i) (cluster f j)) β hβ
      (fun i j _ => density_nonneg H _ _) u v
    rw [supportedDensity,if_pos hAdj] at h
    exact ⟨by linarith only [h.1,hDen,mul_comm β (M' u v:ℝ)],
      by simpa only [mul_comm] using h.2.trans (density_le_one H _ _)⟩
  have hDis (e : ReducedCopy M') (he : e ∈ J) (e' : ReducedCopy M') (he' : e' ∈ J) (hne : e ≠ e') :
      Disjoint (P.thin j e) (P.thin j e') := by
    have hu := congrArg Prod.fst (mem_filter.mp he).2
    have hv := congrArg Prod.snd (mem_filter.mp he).2
    have hu' := congrArg Prod.fst (mem_filter.mp he').2
    have hv' := congrArg Prod.snd (mem_filter.mp he').2
    rw [disjoint_iff_inf_le]
    rintro x y ⟨h,h'⟩
    have hOne : (liftDirectedPair (P.base e.1.1) (P.base e.1.2) (P.copy e)).Adj
        (P.base u (P.kept u x)) (P.base v (P.kept v y)) := by
      refine ⟨P.kept e.1.1 x,P.kept e.1.2 y,?_,?_,(P.copy_partition e x y).mpr (Or.inr ⟨j,h⟩)⟩
      · exact congrArg (fun i => P.base i (P.kept i x)) hu
      · exact congrArg (fun i => P.base i (P.kept i y)) hv
    have hTwo : (liftDirectedPair (P.base e'.1.1) (P.base e'.1.2) (P.copy e')).Adj
        (P.base u (P.kept u x)) (P.base v (P.kept v y)) := by
      refine ⟨P.kept e'.1.1 x,P.kept e'.1.2 y,?_,?_,(P.copy_partition e' x y).mpr (Or.inr ⟨j,h'⟩)⟩
      · exact congrArg (fun i => P.base i (P.kept i x)) hu'
      · exact congrArg (fun i => P.base i (P.kept i y)) hv'
    exact disjoint_iff_inf_le.mp (P.copy_disjoint e e' hne) ⟨hOne,hTwo⟩
  simpa only [Fintype.card_fin] using
    h0_degree_bounds J (P.thin j) d β γ η η' (fun e _ => P.thin_regular j e)
      hDis hη hηOne hη' hγ hErr hBad hCount (by simpa only [Fintype.card_fin] using P.size_pos)

end OverfullWork.DirectedRegularPairs
