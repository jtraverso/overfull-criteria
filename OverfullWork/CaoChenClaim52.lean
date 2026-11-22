module

public import OverfullWork.CaoChenPaletteOverlapNormalization

@[expose] public section


/-! # An actual Claim-5.2 move preserving overlap normalization

If no selected bad colour is missing at the spine, all its selected
neighbours are low. Failure of the auxiliary-colour alternative bounds
their root overlaps by the protected palette. A constructed Fact-2 swap
creates an auxiliary colour outside that palette. Protecting two boundary
levels prevents new small-overlap A-colours. No alternative is assumed.
-/
namespace OverfullWork.CaoChenClaim52
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenMissingIntersection CaoChenOverlapNormalization
open CaoChenPaletteOverlapNormalization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- Colours outside a Kempe pair retain their entire edge classes. -/
theorem colour_class_iff_of_ne (c : PEC G (Fin G.maxDegree))
    (δ η : Fin G.maxDegree) (v : V) {γ : Fin G.maxDegree}
    (hγδ : γ≠δ) (hγη : γ≠η) (a b : V) :
    (c.kempeSwap δ η v).col a b=some γ ↔ c.col a b=some γ := by
  by_cases hr : (c.kempeGraph δ η).Reachable v a
  · exact (CaoChenPaletteKempeTransport.col_eq_swap_iff c δ η hr b γ).trans
      (by rw [Equiv.swap_apply_of_ne_of_ne hγδ hγη])
  · rw [kempeSwap_col,kempeSwapFun_of_not_reachable c δ η hr]

/-- Protected boundary colours stop new low-overlap A-roles from appearing. -/
theorem small_profiles_subset_after_swap (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y v : V} (hcm : IsColMinus c x y)
    (q : ℝ) (C : Finset (Fin G.maxDegree)) (M : ℕ)
    (δ η : Fin G.maxDegree) (hδx : c.IsFree x δ)
    (hoff : ¬(c.kempeGraph δ η).Reachable v x)
    (hδC : δ∉C) (hηC : η∉C)
    (hδR : δ∉boundaryPalette c (missing c x∪missing c y) (paletteLeaves c q x y C) M)
    (hηR : η∉boundaryPalette c (missing c x∪missing c y) (paletteLeaves c q x y C) M) :
    smallOverlapColours (c.kempeSwap δ η v) q x y C M⊆smallOverlapColours c q x y C M := by
  let c':=c.kempeSwap δ η v
  have hxmissing : missing c' x=missing c x := by
    ext γ
    simp only [mem_missing]
    exact isFree_kempeSwap_of_not_reachable c δ η hoff γ
  have hymissing : missing c' y=missing c y := by
    ext γ
    simp only [mem_missing]
    exact protected_swap_keeps_other_endpoint hG hcm hδx hoff γ
  have hbound:=lowOverlapVertices_subset_of_protected_boundary c δ η v
    (missing c x∪missing c y) (paletteLeaves c q x y C) M hδR hηR
  intro γ hγ
  obtain ⟨hγCA,w,hyw',hwlow'⟩:=mem_filter.mp hγ
  obtain ⟨hγC,hγA'⟩:=mem_inter.mp hγCA
  have hγδ : γ≠δ:=fun he => hδC (he ▸ hγC)
  have hγη : γ≠η:=fun he => hηC (he ▸ hγC)
  have hcol:=colour_class_iff_of_ne c δ η v hγδ hγη
  have hγA : γ∈paletteA c q x y := by
    obtain ⟨hpx,t,hyt,ht⟩:=(mem_paletteA c' q x y γ).mp hγA'
    apply (mem_paletteA c q x y γ).mpr
    refine ⟨?_,t,(hcol y t).mp hyt,ht⟩
    simp only [presentColours,hxmissing] at hpx ⊢
    exact hpx
  have hyw : c.col y w=some γ:=(hcol y w).mp hyw'
  have hwT : w∈paletteLeaves c q x y C:=mem_filter.mpr
    ⟨mem_univ w,γ,mem_inter.mpr ⟨hγC,hγA⟩,hyw⟩
  have hwlow : (missing c w∩(missing c x∪missing c y)).card≤M := by
    have hwin : w∈lowOverlapVertices c' (missing c x∪missing c y)
        (paletteLeaves c q x y C) M := by
      apply mem_filter.mpr
      refine ⟨hwT,?_⟩
      change (missing c' w∩(missing c' x∪missing c' y)).card≤M at hwlow'
      simpa only [hxmissing,hymissing] using hwlow'
    exact (mem_filter.mp (hbound hwin)).2
  exact mem_filter.mpr ⟨mem_inter.mpr ⟨hγC,hγA⟩,w,hyw,hwlow⟩

/-- The concrete preserved state and the newly constructed alternative. -/
structure Result (c c' : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y z : V) (α : Fin G.maxDegree) (B C : Finset (Fin G.maxDegree)) (M : ℕ) : Prop where
  cm : IsColMinus c' x y
  rootRow : ∀w,c'.col x w=c.col x w
  otherMissing : ∀γ,c'.IsFree y γ↔c.IsFree y γ
  protectedColours : ∀a b γ,γ∈C∪B → (c'.col a b=some γ↔c.col a b=some γ)
  spine : c'.col x z=some α
  spineMissing : c'.IsFree y α
  smallProfiles : smallOverlapColours c' q x y C M⊆smallOverlapColours c q x y C M
  alternative : ∃β∈B,c'.IsFree z β ∨ ∃t : V,∃δ : Fin G.maxDegree,
    c'.col z t=some β ∧ c'.IsFree x δ ∧ c'.IsFree t δ ∧ δ∉C

/-- Claim 5.2 with explicit finite budgets and an actual output colouring.
The selected B-colour classes are protected as well as C; this costs
larger constants but preserves every selected bad-colour role exactly. -/
theorem exists_claim52_colouring (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y z : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxz : c.col x z=some α) (hα : c.IsFree y α)
    (B C : Finset (Fin G.maxDegree)) (M : ℕ)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hB : ∀β∈B,β∈badColours c ((1-ε)*(G.maxDegree:ℝ)) z)
    (hsize : 1≤ε*(B.card:ℝ))
    (hthreshold : (C.card:ℝ)+((B.card-1:ℕ):ℝ)*
      ((B.card+(M+3)*C.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : B.card+(M+3)*C.card+B.card*C.card<(missing c x).card) :
    ∃c' : PEC G (Fin G.maxDegree),Result c c' ((1-ε)*(G.maxDegree:ℝ)) x y z α B C M := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  let Alt (d : PEC G (Fin G.maxDegree)):=∃β∈B,d.IsFree z β ∨ ∃t : V,∃δ : Fin G.maxDegree,
    d.col z t=some β ∧ d.IsFree x δ ∧ d.IsFree t δ ∧ δ∉C
  by_cases halt : Alt c
  · exact ⟨c,⟨hcm,fun _ => rfl,fun _ => Iff.rfl,fun _ _ _ _ => Iff.rfl,
      hxz,hα,subset_rfl,halt⟩⟩
  · have hnfree : ∀β∈B,¬c.IsFree z β := fun β hβ hfree => halt ⟨β,hβ,Or.inl hfree⟩
    let T : Finset V:=univ.filter fun t => ∃β∈B,c.col z t=some β
    have hTcard : T.card=B.card := by
      apply CaoChenPaletteCounting.card_leaves_eq_card_colours z T B
      · intro t ht
        exact (mem_filter.mp ht).2
      · intro β hβ
        obtain ⟨t,ht⟩ : ∃t,c.col z t=some β := by
          simpa only [IsFree,not_forall,not_not] using hnfree β hβ
        exact ⟨t,mem_filter.mpr ⟨mem_univ t,β,hβ,ht⟩,ht⟩
    have hTlow : ∀t∈T,(G.degree t:ℝ)<q := by
      intro t ht
      obtain ⟨β,hβ,hzt⟩:=(mem_filter.mp ht).2
      obtain ⟨w,hzw,hw⟩:=((mem_badColours c q z β).mp (hB β hβ)).resolve_left (hnfree β hβ)
      have he : t=w:=c.col_proper hzt hzw
      subst w
      exact hw
    have hroot : ∀t∈T,(missing c t∩missing c x).card≤C.card := by
      intro t ht
      obtain ⟨β,hβ,hzt⟩:=(mem_filter.mp ht).2
      apply card_le_card
      intro δ hδ
      obtain ⟨hδt,hδx⟩:=mem_inter.mp hδ
      by_contra hδC
      exact halt ⟨β,hβ,Or.inr ⟨t,δ,hzt,mem_missing.mp hδx,mem_missing.mp hδt,hδC⟩⟩
    let A:=paletteLeaves c q x y C
    let X:=missing c x∪missing c y
    let R:=boundaryPalette c X A M
    let F:=(C∪B)∪R
    have hAcard : A.card≤C.card := by
      rw [paletteLeaves_card_eq]
      exact card_le_card inter_subset_left
    have hFcard : F.card≤B.card+(M+3)*C.card := by
      have hCB:=card_union_le C B
      have hFR:=card_union_le (C∪B) R
      have hR: R.card≤(M+2)*A.card:=boundaryPalette_card_le c X A M
      have hm:=Nat.mul_le_mul_left (M+2) hAcard
      nlinarith only [hCB,hFR,hR,hm]
    have hthreshold' : (C.card:ℝ)+((T.card-1:ℕ):ℝ)*((F.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
      rw [hTcard]
      have hFR : ((F.card+1:ℕ):ℝ)≤((B.card+(M+3)*C.card+1:ℕ):ℝ) := by
        exact_mod_cast (show F.card+1≤B.card+(M+3)*C.card+1 by omega)
      have hm:=mul_le_mul_of_nonneg_left hFR (Nat.cast_nonneg (B.card-1): (0:ℝ)≤_)
      linarith only [hm,hthreshold]
    have hbudget' : F.card+T.card*C.card<(missing c x).card := by rw [hTcard];omega
    obtain ⟨v,hv,δ,η,hδF,hηF,hδx,hηx,hηv,hTδ,hoff,hrow,hprotected,hgain⟩:=
      exists_protected_kempe_improvement c x T F ε hε hεone C.card hx hTlow hroot
        (by rwa [hTcard]) hthreshold' hbudget'
    let c':=c.kempeSwap δ η v
    have hγC : ∀γ∈C,γ≠δ ∧ γ≠η := by
      intro γ hγ
      exact ⟨fun he => hδF (he ▸ mem_union_left R (mem_union_left B hγ)),
        fun he => hηF (he ▸ mem_union_left R (mem_union_left B hγ))⟩
    have hδR : δ∉R:=fun h => hδF (mem_union_right _ h)
    have hηR : η∉R:=fun h => hηF (mem_union_right _ h)
    have hδnew : c'.IsFree v δ := by
      rw [isFree_kempeSwap_of_reachable c δ η (SimpleGraph.Reachable.refl v),Equiv.swap_apply_left]
      exact hηv
    obtain ⟨β,hβ,hzv⟩:=(mem_filter.mp hv).2
    have hβδ : β≠δ:=fun he => hδF (he ▸ mem_union_left R (mem_union_right C hβ))
    have hβη : β≠η:=fun he => hηF (he ▸ mem_union_left R (mem_union_right C hβ))
    have hprotected' : ∀a b γ,γ∈C∪B → (c'.col a b=some γ↔c.col a b=some γ) := by
      intro a b γ hγ
      have hγF : γ∈F:=mem_union_left R hγ
      exact colour_class_iff_of_ne c δ η v (fun he => hδF (he ▸ hγF))
        (fun he => hηF (he ▸ hγF)) a b
    refine ⟨c',⟨hcm.kempeSwap δ η v,hrow,?_,hprotected',?_,?_,?_,?_⟩⟩
    · exact protected_swap_keeps_other_endpoint hG hcm hδx hoff
    · rw [hrow]
      exact hxz
    · exact (protected_swap_keeps_other_endpoint hG hcm hδx hoff α).mpr hα
    · apply small_profiles_subset_after_swap hG hcm q C M δ η hδx hoff
      · exact fun h => (hγC δ h).1 rfl
      · exact fun h => (hγC η h).2 rfl
      · exact hδR
      · exact hηR
    · refine ⟨β,hβ,Or.inr ⟨v,δ,?_,?_,hδnew,?_⟩⟩
      · exact (colour_class_iff_of_ne c δ η v hβδ hβη z v).mpr hzv
      · exact (isFree_kempeSwap_of_not_reachable c δ η hoff δ).mpr hδx
      · exact fun h => hδF (mem_union_left R (mem_union_left B h))

end OverfullWork.CaoChenClaim52
