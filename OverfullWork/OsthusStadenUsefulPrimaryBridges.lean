module

public import OverfullWork.OsthusStadenPhysicalH0
public import OverfullWork.OsthusStadenPrimaryBridgeCells

@[expose] public section


/-! Claim 5.2 from the actual H0 reserves and the adapted primary refinements. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical

set_option maxHeartbeats 1200000 in
/-- At least half the source p-cell has both required reserve degrees
into the designated halves, on the original vertices. -/
theorem useful_bridge_vertices_in_physical_cells
    {V I : Type*} [Fintype V] [Fintype I]
    {H G : Digraph V} {f : V → Option I} {m₀ b r s p m : ℕ}
    [NeZero s] [NeZero p] {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f
      (reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β)
      m₀ b β γ η a exc)
    (E : Fin r → I → Digraph V) (g : V → Option I) (τ : ℝ)
    (R : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster g i) s p m τ τ τ)
    (u v w : RefinedVertex I s p) (halfIn halfOut : Bool) (qIn qOut : Fin 5)
    (hAdjIn : (quotient H f).Adj u.1.1 v.1.1) (hAdjOut : (quotient H f).Adj v.1.1 w.1.1)
    (δ d κ : ℝ) (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 < η) (hηOne : η ≤ 1)
    (hd : 0 ≤ d) (hδ : 0 ≤ δ) (hErr : 4*η ≤ γ*β) (hBad : η ≤ δ*β)
    (hDenIn : d+β ≤ density H (cluster f u.1.1) (cluster f v.1.1))
    (hDenOut : d+β ≤ density H (cluster f v.1.1) (cluster f w.1.1))
    (hParent : ∀ i, cluster g i ⊆ cluster B.partition i)
    (hLoss : ∀ i, (((cluster B.partition i) \ cluster g i).card:ℝ) ≤ γ*d*(B.size:ℝ)/4)
    (hδSize : 4*δ*(B.size:ℝ) ≤ 2*(m:ℝ))
    (hτ : 0 ≤ τ) (hτOne : τ ≤ 1/8)
    (hFloor : 8*τ ≤ γ*d/4) (hκ : κ < (1-8*τ)*(γ*d/4)*(m:ℝ)) :
    let source := primaryPCells R v
    let targetIn := primaryHalfCell R u halfIn
    let targetOut := primaryHalfCell R w halfOut
    let HIn := primaryThinDigraphs B qIn
    let HOut := primaryThinDigraphs B qOut
    source.card ≤ 2*(source.filter (fun x =>
      κ < profileCount targetIn (inProfile HIn x) ∧ κ < profileCount targetOut (outProfile HOut x))).card := by
  let source := primaryPCells R v
  let HIn := primaryThinDigraphs B qIn
  let HOut := primaryThinDigraphs B qOut
  obtain ⟨_,badIn,_,hBadIn,_,hIn⟩ :=
    primary_thin_profiles_of_reduced_pair B hβ hγ hη hηOne δ d hδ hErr hBad qIn
      u.1.1 v.1.1 hAdjIn hDenIn
  obtain ⟨badOut,_,hBadOut,_,hOut,_⟩ :=
    primary_thin_profiles_of_reduced_pair B hβ hγ hη hηOne δ d hδ hErr hBad qOut
      v.1.1 w.1.1 hAdjOut hDenOut
  have hCellS : source ⊆ cluster B.partition v.1.1 :=
    (((R v.1.1).second _).subset _).trans
      (((R v.1.1).first.subset _).trans (hParent v.1.1))
  have hSizeS : source.card = 2*m := ((R v.1.1).second _).size _
  have hSmall (D : Finset V) (hD : (D.card:ℝ) ≤ δ*(B.size:ℝ)) : 4*D.card ≤ source.card := by
    rw [hSizeS]
    have h := mul_le_mul_of_nonneg_left hD (show (0:ℝ) ≤ 4 by norm_num)
    have h' : 4*(D.card:ℝ) ≤ 2*(m:ℝ) := by linarith only [h,hδSize]
    exact_mod_cast h'
  have hBaseCard (i : I) : (cluster B.partition i).card = B.size := by
    rw [←B.retained_cells i,card_map,card_univ,Fintype.card_fin]
  have hTransfer (i : I) (Q : Finset V)
      (hProfile : γ*d*(B.size:ℝ)/2 ≤ profileCount (cluster B.partition i) Q) :
      (γ*d/4)*((cluster g i).card:ℝ) ≤ profileCount (cluster g i) Q := by
    have hChange := profile_count_dist_le (cluster B.partition i) (cluster g i) Q
    rw [sdiff_eq_empty_iff_subset.mpr (hParent i),card_empty,
      max_eq_left (Nat.zero_le _)] at hChange
    change |profileCount (cluster B.partition i) Q-profileCount (cluster g i) Q| ≤ _ at hChange
    have hD : ((cluster g i).card:ℝ) ≤ (B.size:ℝ) := by
      rw [←hBaseCard i]
      exact_mod_cast card_le_card (hParent i)
    have hScale := mul_le_mul_of_nonneg_left hD (show 0 ≤ γ*d/4 by positivity)
    nlinarith only [hScale,hProfile,(abs_le.mp (hChange.trans (hLoss i))).2]
  have hSize (v' : RefinedVertex I s p) (half : Bool) :
      (cluster g v'.1.1).card = (s*p*2)*(primaryHalfCell R v' half).card := by
    rw [primaryHalfCell_card]
    simpa only [Fintype.card_fin,Nat.mul_assoc] using (R v'.1.1).first.card_parent
  have hUniform (v' : RefinedVertex I s p) (half : Bool) :
      UniformProfileCell (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
        (cluster g v'.1.1) (primaryHalfCell R v' half) (s*p*2) (8*τ) :=
    ((R v'.1.1).uniform_p_and_half_cells hτ hτOne _ _).2 _
  have hk : 0 < s*p*2 := Nat.mul_pos (Nat.mul_pos (NeZero.pos s) (NeZero.pos p)) (by decide)
  exact useful_bridge_vertices_of_refinements HIn HOut source (cluster g u.1.1) (cluster g w.1.1)
    (primaryHalfCell R u halfIn) (primaryHalfCell R w halfOut) badIn badOut (s*p*2) (8*τ) (γ*d/4) κ
    hk (by linarith only [hτOne]) hFloor (hSize u halfIn) (hSize w halfOut)
    ((hUniform u halfIn).inProfile (Sum.inl (some qIn)))
    ((hUniform w halfOut).outProfile (Sum.inl (some qOut)))
    (hSmall _ hBadIn) (hSmall _ hBadOut)
    (fun x hx h => hTransfer _ _ (hIn x (hCellS hx) h))
    (fun x hx h => hTransfer _ _ (hOut x (hCellS hx) h))
    (by simpa only [primaryHalfCell_card] using hκ)
    (by simpa only [primaryHalfCell_card] using hκ)

end OverfullWork.DirectedRobustExpansion
