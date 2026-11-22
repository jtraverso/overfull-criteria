module

public import OverfullWork.CaoChenMissingIntersection
public import OverfullWork.CaoChenPaletteKempeTransport

@[expose] public section


/-! # Constructed normalization of a finite family of missing palettes

This is the extremal-colouring step behind Cao--Chen's Claims 5.1 and 5.4.
We minimize the number of low-overlap palettes and then maximize their total
overlap with the root. A protected Kempe improvement contradicts extremality
unless fewer than L palettes have small overlap. The two-level boundary
window gives deliberately nonoptimal explicit constants.
-/
namespace OverfullWork.CaoChenOverlapNormalization
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenMissingIntersection
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

noncomputable def lowOverlapVertices (c : PEC G (Fin G.maxDegree))
    (X : Finset (Fin G.maxDegree)) (T : Finset V) (M : ℕ) : Finset V :=
  T.filter fun v => (missing c v∩X).card≤M

noncomputable def boundaryPalette (c : PEC G (Fin G.maxDegree))
    (X : Finset (Fin G.maxDegree)) (T : Finset V) (M : ℕ) : Finset (Fin G.maxDegree) :=
  (T.filter fun v => M<(missing c v∩X).card ∧ (missing c v∩X).card≤M+2).biUnion
    fun v => missing c v∩X

/-- Changing two colours loses at most two members of any fixed overlap. -/
theorem overlap_card_drop_le_two (c : PEC G (Fin G.maxDegree))
    (δ η : Fin G.maxDegree) (w v : V) (X : Finset (Fin G.maxDegree)) :
    (missing c v∩X).card≤(missing (c.kempeSwap δ η w) v∩X).card+2 := by
  have hsub : missing c v∩X⊆insert δ (insert η (missing (c.kempeSwap δ η w) v∩X)) := by
    intro γ hγ
    by_cases hγδ : γ=δ
    · simp [hγδ]
    by_cases hγη : γ=η
    · simp [hγη]
    apply mem_insert_of_mem
    apply mem_insert_of_mem
    obtain ⟨hv,hX⟩:=mem_inter.mp hγ
    exact mem_inter.mpr ⟨mem_missing.mpr
      ((kempeSwap_isFree_of_ne c δ η w v hγδ hγη).mpr (mem_missing.mp hv)),hX⟩
  have hc:=card_le_card hsub
  have hδ:=card_insert_le δ (insert η (missing (c.kempeSwap δ η w) v∩X))
  have hη:=card_insert_le η (missing (c.kempeSwap δ η w) v∩X)
  omega

omit [DecidableEq V] in
/-- The boundary palette costs at most (M+2) colours per fixed vertex. -/
theorem boundaryPalette_card_le (c : PEC G (Fin G.maxDegree))
    (X : Finset (Fin G.maxDegree)) (T : Finset V) (M : ℕ) :
    (boundaryPalette c X T M).card≤(M+2)*T.card := by
  let B:=T.filter fun v => M<(missing c v∩X).card ∧ (missing c v∩X).card≤M+2
  have hs : (∑v∈B,(missing c v∩X).card)≤B.card*(M+2) := by
    calc
      _≤∑_v∈B,(M+2):=sum_le_sum (fun v hv => (mem_filter.mp hv).2.2)
      _=_:=by simp only [sum_const,Nat.nsmul_eq_mul]
  have hb : B.card≤T.card:=card_le_card (filter_subset _ _)
  exact (card_biUnion_le.trans hs).trans (by nlinarith)

/-- Protecting the two boundary levels prevents any new low-overlap vertex. -/
theorem lowOverlapVertices_subset_of_protected_boundary
    (c : PEC G (Fin G.maxDegree)) (δ η : Fin G.maxDegree) (w : V)
    (X : Finset (Fin G.maxDegree)) (T : Finset V) (M : ℕ)
    (hδ : δ∉boundaryPalette c X T M) (hη : η∉boundaryPalette c X T M) :
    lowOverlapVertices (c.kempeSwap δ η w) X T M⊆lowOverlapVertices c X T M := by
  intro v hv
  obtain ⟨hvT,hvlow⟩:=mem_filter.mp hv
  apply mem_filter.mpr
  refine ⟨hvT,?_⟩
  by_contra hn
  have hold : M<(missing c v∩X).card:=by omega
  by_cases hb : (missing c v∩X).card≤M+2
  · have hsub : missing c v∩X⊆missing (c.kempeSwap δ η w) v∩X := by
      intro γ hγ
      have hγB : γ∈boundaryPalette c X T M:=mem_biUnion.mpr
        ⟨v,mem_filter.mpr ⟨hvT,hold,hb⟩,hγ⟩
      have hγδ : γ≠δ:=by intro he;exact hδ (he ▸ hγB)
      have hγη : γ≠η:=by intro he;exact hη (he ▸ hγB)
      obtain ⟨hγv,hγX⟩:=mem_inter.mp hγ
      exact mem_inter.mpr ⟨mem_missing.mpr
        ((kempeSwap_isFree_of_ne c δ η w v hγδ hγη).mpr (mem_missing.mp hγv)),hγX⟩
    have hc:=card_le_card hsub
    omega
  · have hc:=overlap_card_drop_le_two c δ η w v X
    omega

/-- Actual protected normalization. T is a fixed finite family of low
vertices; in the intended applications its size is bounded in epsilon
before the graph is chosen. No extremal colouring or improving swap is
assumed. The explicit numerical budgets are polynomial in |T| and M. -/
theorem exists_normalized_overlap_colouring (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y : V} (hcm₀ : IsColMinus c₀ x y)
    (T : Finset V) (F : Finset (Fin G.maxDegree)) (M L : ℕ)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hlow : ∀v∈T,(G.degree v:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hL : 1≤ε*(L:ℝ))
    (hthreshold : (M:ℝ)+((T.card-1:ℕ):ℝ)*
      ((F.card+(M+2)*T.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : F.card+(M+2)*T.card+T.card*M<(missing c₀ x).card) :
    ∃ c : PEC G (Fin G.maxDegree),IsColMinus c x y ∧
      (∀w,c.col x w=c₀.col x w) ∧
      (∀γ,c.IsFree y γ↔c₀.IsFree y γ) ∧
      (∀a b γ,γ∈F → (c.col a b=some γ ↔ c₀.col a b=some γ)) ∧
      (lowOverlapVertices c (missing c x∪missing c y) T M).card<L := by
  let P : PEC G (Fin G.maxDegree) → Prop := fun c => IsColMinus c x y ∧
    (∀w,c.col x w=c₀.col x w) ∧ (∀γ,c.IsFree y γ↔c₀.IsFree y γ) ∧
    (∀a b γ,γ∈F → (c.col a b=some γ ↔ c₀.col a b=some γ))
  let low (c : PEC G (Fin G.maxDegree)):=lowOverlapVertices c (missing c x∪missing c y) T M
  let score (c : PEC G (Fin G.maxDegree)):=∑v∈low c,(missing c v∩missing c x).card
  have hp₀ : P c₀:=⟨hcm₀,fun _ => rfl,fun _ => Iff.rfl,fun _ _ _ _ => Iff.rfl⟩
  have hlowSub (c : PEC G (Fin G.maxDegree)) : low c⊆T:=filter_subset _ _
  have hscoreBound (c : PEC G (Fin G.maxDegree)) : score c≤T.card*G.maxDegree := by
    have hb : ∀v∈low c,(missing c v∩missing c x).card≤G.maxDegree := by
      intro v _
      exact (card_le_card inter_subset_right).trans (by simpa using card_le_univ (missing c x))
    calc
      score c≤∑_v∈low c,G.maxDegree:=sum_le_sum hb
      _=(low c).card*G.maxDegree:=by simp only [sum_const,Nat.nsmul_eq_mul]
      _≤T.card*G.maxDegree:=Nat.mul_le_mul_right _ (card_le_card (hlowSub c))
  let A : ℕ → Prop:=fun n => ∃c,P c ∧ (low c).card=n
  have hA : ∃n,A n:=⟨(low c₀).card,c₀,hp₀,rfl⟩
  obtain ⟨c₁,hp₁,hval₁⟩:=Nat.find_spec hA
  let B : ℕ → Prop:=fun n => ∃c,P c ∧ (low c).card=Nat.find hA ∧ score c=n
  have hB : B (score c₁):=⟨c₁,hp₁,hval₁,rfl⟩
  obtain ⟨c,hp,hval,hscore⟩:=Nat.findGreatest_spec (hscoreBound c₁) hB
  have hmin : ∀d,P d → (low c).card≤(low d).card := by
    intro d hd
    rw [hval]
    exact Nat.find_le ⟨d,hd,rfl⟩
  have hmax : ∀d,P d → (low d).card=(low c).card → score d≤score c := by
    intro d hd heq
    have hn : B (score d):=⟨d,hd,heq.trans hval,rfl⟩
    have hh:=Nat.le_findGreatest (hscoreBound d) hn
    rwa [←hscore] at hh
  refine ⟨c,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,?_⟩
  change (low c).card<L
  by_contra hn
  have hcard : L≤(low c).card:=by omega
  let X:=missing c x∪missing c y
  let R:=boundaryPalette c X T M
  let C:=F∪R
  have hC : C.card≤F.card+(M+2)*T.card :=
    (card_union_le _ _).trans (Nat.add_le_add_left (boundaryPalette_card_le c X T M) _)
  have hFx : missing c x=missing c₀ x := by
    ext γ
    simp only [mem_missing,IsFree]
    simp_rw [hp.2.1]
  have hroot : ∀v∈low c,(missing c v∩missing c x).card≤M := by
    intro v hv
    have hvM:=(mem_filter.mp hv).2
    have hs : missing c v∩missing c x⊆missing c v∩X := by
      intro γ hγ
      exact mem_inter.mpr ⟨(mem_inter.mp hγ).1,mem_union.mpr (Or.inl (mem_inter.mp hγ).2)⟩
    exact (card_le_card hs).trans hvM
  have hsize : 1≤ε*((low c).card:ℝ) :=
    hL.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hε.le)
  have hth : (M:ℝ)+(((low c).card-1:ℕ):ℝ)*((C.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    have hN : ((low c).card-1:ℕ)≤T.card-1:=by have hh:=card_le_card (hlowSub c);omega
    have hCR : ((C.card+1:ℕ):ℝ)≤((F.card+(M+2)*T.card+1:ℕ):ℝ) := by exact_mod_cast (by omega : C.card+1≤F.card+(M+2)*T.card+1)
    have hNR : (((low c).card-1:ℕ):ℝ)≤((T.card-1:ℕ):ℝ):=by exact_mod_cast hN
    have hh:=mul_le_mul hNR hCR (by positivity) (by positivity)
    nlinarith only [hh,hthreshold]
  have hbud : C.card+(low c).card*M<(missing c x).card := by
    rw [hFx]
    have hh:=Nat.mul_le_mul_right M (card_le_card (hlowSub c))
    omega
  obtain ⟨v,hv,δ,η,hδC,hηC,hδ,hη,hvη,hTδ,hoff,hrow,hcol,hinc⟩:=
    exists_protected_kempe_improvement c x (low c) C ε hε hεone M hx
      (fun v hv => hlow v (hlowSub c hv)) hroot hsize hth hbud
  let d:=c.kempeSwap δ η v
  have hpd : P d := by
    refine ⟨hp.1.kempeSwap δ η v,fun w => (hrow w).trans (hp.2.1 w),?_,?_⟩
    · intro γ
      exact (protected_swap_keeps_other_endpoint hG hp.1 hδ hoff γ).trans (hp.2.2.1 γ)
    · intro a b γ hγ
      have hγδ : γ≠δ := by intro he;exact hδC (mem_union.mpr (Or.inl (he ▸ hγ)))
      have hγη : γ≠η := by intro he;exact hηC (mem_union.mpr (Or.inl (he ▸ hγ)))
      have he : d.col a b=some γ↔c.col a b=some γ := by
        by_cases hr : (c.kempeGraph δ η).Reachable v a
        · simpa only [Equiv.swap_apply_of_ne_of_ne hγδ hγη] using
            CaoChenPaletteKempeTransport.col_eq_swap_iff c δ η hr b γ
        · rw [kempeSwap_col,kempeSwapFun_of_not_reachable c δ η hr b]
      exact he.trans (hp.2.2.2 a b γ hγ)
  have hX : missing d x∪missing d y=X := by
    have hx' : missing d x=missing c x := by
      ext γ
      simpa only [mem_missing] using isFree_kempeSwap_of_not_reachable c δ η hoff γ
    have hy' : missing d y=missing c y := by
      ext γ
      simpa only [mem_missing] using protected_swap_keeps_other_endpoint hG hp.1 hδ hoff γ
    rw [hx',hy']
  have hsub : low d⊆low c := by
    change lowOverlapVertices d (missing d x∪missing d y) T M⊆lowOverlapVertices c X T M
    rw [hX]
    exact lowOverlapVertices_subset_of_protected_boundary c δ η v X T M
      (fun he => hδC (mem_union.mpr (Or.inr he)))
      (fun he => hηC (mem_union.mpr (Or.inr he)))
  have heq : low d=low c:=eq_of_subset_of_card_le hsub (hmin d hpd)
  have hsmax:=hmax d hpd (congrArg Finset.card heq)
  have hsinc : score c+1≤score d := by
    change (∑w∈low c,(missing c w∩missing c x).card)+1≤
      ∑w∈low d,(missing d w∩missing d x).card
    rw [heq]
    exact hinc
  omega

end OverfullWork.CaoChenOverlapNormalization
