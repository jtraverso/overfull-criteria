module

public import OverfullWork.OsthusStadenIndexedMerge
public import OverfullWork.OsthusStadenTrimmedCopies

@[expose] public section


/-! Put the saved H3 pairs and the actual factor matchings into the
same coordinates as the cut theorem. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {E I W : Type*} [Fintype W]

noncomputable def sliceCellEquiv (i : I) : W ≃ ↥(sliceCell (E := E) (W := W) i) :=
  Equiv.ofBijective
    (fun w => ⟨Sum.inr (i,w),(mem_sliceCell _ _).mpr rfl⟩)
    ⟨fun _ _ h => (Prod.mk.inj (Sum.inr.inj (congrArg Subtype.val h))).2,
      fun x => by
        obtain ⟨w,_,h⟩ := mem_map.mp x.property
        exact ⟨w,Subtype.ext h⟩⟩

theorem sliceCellEquiv_val (i : I) (w : W) :
    ((sliceCellEquiv (E := E) i w : ↥(sliceCell i)) : SliceVertex E I W) = .inr (i,w) := rfl

noncomputable def matchedCells (F : Equiv.Perm (SliceVertex E I W)) (i j : I)
    (h : (sliceCell i).image F = sliceCell j) : ↥(sliceCell (E := E) (W := W) i) ≃ ↥(sliceCell (E := E) (W := W) j) :=
  Equiv.ofBijective
    (fun x => ⟨F x,h ▸ mem_image.mpr ⟨x,x.property,rfl⟩⟩)
    ⟨fun _ _ e => Subtype.ext (F.injective (congrArg Subtype.val e)),fun y => by
      have hy : y.val ∈ (sliceCell i).image F := h.symm ▸ y.property
      obtain ⟨x,hx,e⟩ := mem_image.mp hy
      exact ⟨⟨x,hx⟩,Subtype.ext e⟩⟩

/-- Use the saved side coordinates of a successor pair to index its
reserve and all of the factor matchings on the source cut. -/
noncomputable def rotationReserveOfPairs {R : Type*} {k : ℕ}
    (σ : Equiv.Perm I) (F : Fin k → Equiv.Perm (SliceVertex E I W))
    (cluster : R → I) (H : I → Digraph W)
    (h : ∀ a f, (sliceCell (cluster a)).image (F f) = sliceCell (σ (cluster a))) :
    RotationReserve F (fun a => sliceCell (cluster a)) where
  pair a := pullDirectedPair (sliceCellEquiv (cluster a)).symm.toEmbedding
    (sliceCellEquiv (cluster a)).symm.toEmbedding (H (cluster a))
  target a := (((sliceCellEquiv (cluster a)).symm.trans
    (sliceCellEquiv (σ (cluster a)))).toEmbedding).trans (Function.Embedding.subtype _)
  matching a f := (matchedCells (F f) (cluster a) (σ (cluster a)) (h a f)).trans
    ((sliceCellEquiv (cluster a)).symm.trans (sliceCellEquiv (σ (cluster a)))).symm
  agrees a f x := by
    let e := (sliceCellEquiv (E := E) (W := W) (cluster a)).symm.trans
      (sliceCellEquiv (E := E) (W := W) (σ (cluster a)))
    change F f x.val = (e (e.symm (matchedCells (F f) _ _ (h a f) x))).val
    rw [e.apply_symm_apply]
    rfl

theorem rotationReserveOfPairs_adj {R : Type*} {k : ℕ}
    (σ : Equiv.Perm I) (F : Fin k → Equiv.Perm (SliceVertex E I W))
    (cluster : R → I) (H : I → Digraph W)
    (h : ∀ a f, (sliceCell (cluster a)).image (F f) = sliceCell (σ (cluster a)))
    (G : Digraph (SliceVertex E I W))
    (hHost : ∀ i x y, (H i).Adj x y → G.Adj (.inr (i,x)) (.inr (σ i,y))) :
    ∀ a (x y : ↥(sliceCell (cluster a))), ((rotationReserveOfPairs σ F cluster H h).pair a).Adj x y →
      G.Adj x.val ((rotationReserveOfPairs σ F cluster H h).target a y) := by
  intro a x y hEdge
  let e := sliceCellEquiv (E := E) (W := W) (cluster a)
  have hx : (Sum.inr (cluster a,e.symm x) : SliceVertex E I W) = x.val := by
    rw [←sliceCellEquiv_val,Equiv.apply_symm_apply]
  have hEnd : (rotationReserveOfPairs σ F cluster H h).target a y =
      Sum.inr (σ (cluster a),e.symm y) := rfl
  rw [←hx,hEnd]
  exact hHost _ _ _ hEdge

/-- The physical H3 superregularity gives the merge margins on the
cut coordinates. Only the numerical size and deletion budgets remain. -/
theorem rotationReserveOfPairs_margins {R : Type*} {k : ℕ}
    (σ : Equiv.Perm I) (F : Fin k → Equiv.Perm (SliceVertex E I W))
    (cluster : R → I) (H : I → Digraph W)
    (h : ∀ a f, (sliceCell (cluster a)).image (F f) = sliceCell (σ (cluster a)))
    (d ε ν τ γ ε₀ d₀ : ℝ) (N : ℕ)
    (hReg : ∀ i, IsCentredSuperregular (H i) ε₀ d₀)
    (hε₀ : 0 ≤ ε₀) (hε : 0 < ε) (hW : 0 < Fintype.card W)
    (hWidth : ε₀ ≤ ε) (hDensity : d ≤ d₀-2*ε₀)
    (hN : N ≤ Fintype.card W)
    (hCost : (k:ℝ)+ν*(Fintype.card W:ℝ) ≤ d*τ*(Fintype.card W:ℝ))
    (hDeg : γ*(Fintype.card W:ℝ)+(k:ℝ) ≤ d*(Fintype.card W:ℝ)) :
    RotationReserveMargins (rotationReserveOfPairs σ F cluster H h) d ε ν τ γ N := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro a
    rw [←sliceCell_card (E := E) (W := W) (cluster a)] at hW hN
    exact ⟨card_pos.mp hW,hN⟩
  · intro a
    simpa only [sliceCell_card] using hCost
  · intro a
    simpa only [sliceCell_card] using hDeg
  · intro a X Y hX hY
    let i := cluster a
    let e := (sliceCellEquiv (E := E) (W := W) i).symm.toEmbedding
    let B := X.map e
    let C := Y.map e
    have hn : (0:ℝ) < Fintype.card W := by exact_mod_cast hW
    rw [sliceCell_card] at hX hY
    have hPosX : X.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hε hn).trans_le hX)
    have hPosY : Y.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hε hn).trans_le hY)
    have hDown := mul_le_mul_of_nonneg_right hWidth hn.le
    have hCenter := (abs_le.mp (hReg i).1.2).1
    have hRect := uniform_incidences_lower (H i) (hReg i).1.1
      (show d₀-ε₀ ≤ density (H i) univ univ by linarith only [hCenter])
      (subset_univ B) (subset_univ C)
      (by simpa only [B,card_univ,card_map,mul_comm] using hDown.trans hX)
      (by simpa only [C,card_univ,card_map,mul_comm] using hDown.trans hY)
      hPosX.map hPosY.map
    have hInc : (incidences (pullDirectedPair e e (H i)) X Y : ℝ) = (incidences (H i) B C : ℝ) := by
      simp only [B,C,incidences_eq_sum,sum_map]
      rfl
    change d*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences (pullDirectedPair e e (H i)) X Y:ℝ)
    rw [hInc]
    rw [show d₀-ε₀-ε₀ = d₀-2*ε₀ by ring,show B.card = X.card from card_map _,show C.card = Y.card from card_map _] at hRect
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)).trans hRect.le
  · intro a x
    let e := (sliceCellEquiv (E := E) (W := W) (cluster a)).symm
    have hMap : ((univ : Finset ↥(sliceCell (cluster a))).map e.toEmbedding) = univ := by
      ext y
      simp only [mem_map,mem_univ,true_and,iff_true]
      exact e.surjective y
    have hIn := pullDirectedPair_semidegree e.toEmbedding e.toEmbedding (H (cluster a)) false x
    simp only [hMap,pairSemidegree,if_false,Bool.false_eq_true] at hIn
    change inDegree (pullDirectedPair e.toEmbedding e.toEmbedding (H (cluster a))) x =
      inDegree (H (cluster a)) (e x) at hIn
    change d*((sliceCell (cluster a)).card:ℝ) ≤
      (inDegree (pullDirectedPair e.toEmbedding e.toEmbedding (H (cluster a))) x:ℝ)
    rw [sliceCell_card,hIn]
    have hl := (abs_le.mp ((hReg (cluster a)).2 (e x)).1).1
    have hn := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg (Fintype.card W) : (0:ℝ) ≤ _)
    nlinarith only [hl,hn,mul_nonneg hε₀ (Nat.cast_nonneg (Fintype.card W) : (0:ℝ) ≤ _)]
  · intro a x
    let e := (sliceCellEquiv (E := E) (W := W) (cluster a)).symm
    have hMap : ((univ : Finset ↥(sliceCell (cluster a))).map e.toEmbedding) = univ := by
      ext y
      simp only [mem_map,mem_univ,true_and,iff_true]
      exact e.surjective y
    have hOut := pullDirectedPair_semidegree e.toEmbedding e.toEmbedding (H (cluster a)) true x
    simp only [hMap,pairSemidegree,if_true] at hOut
    change outDegree (pullDirectedPair e.toEmbedding e.toEmbedding (H (cluster a))) x =
      outDegree (H (cluster a)) (e x) at hOut
    change d*((sliceCell (cluster a)).card:ℝ) ≤
      (outDegree (pullDirectedPair e.toEmbedding e.toEmbedding (H (cluster a))) x:ℝ)
    rw [sliceCell_card,hOut]
    have hl := (abs_le.mp ((hReg (cluster a)).2 (e x)).2).1
    have hn := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg (Fintype.card W) : (0:ℝ) ≤ _)
    nlinarith only [hl,hn,mul_nonneg hε₀ (Nat.cast_nonneg (Fintype.card W) : (0:ℝ) ≤ _)]

end OverfullWork.DirectedRobustExpansion
