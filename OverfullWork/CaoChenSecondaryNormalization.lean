module

public import OverfullWork.CaoChenOverlapNormalization

@[expose] public section


/-! # Root-only normalization while preserving a primary overlap profile

The second family is normalized against the root palette alone. States
retain inclusion of the primary small-overlap profile. Every improving
swap protects both CURRENT boundary windows, so no cumulative loss can
create a new primary small-overlap vertex. Both extremizers are selected
from actual colourings; no normalization or recolouring oracle is assumed.
-/
namespace OverfullWork.CaoChenSecondaryNormalization
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenMissingIntersection CaoChenOverlapNormalization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 6000000

/-- Exact invariants retained during secondary normalization. -/
structure State (c₀ c : PEC G (Fin G.maxDegree)) (x y : V)
    (F X : Finset (Fin G.maxDegree)) (A : Finset V) (M : ℕ) : Prop where
  cm : IsColMinus c x y
  rootRow : ∀w,c.col x w=c₀.col x w
  otherMissing : ∀γ,c.IsFree y γ↔c₀.IsFree y γ
  protectedColours : ∀a b γ,γ∈F → (c.col a b=some γ↔c₀.col a b=some γ)
  primarySubset : lowOverlapVertices c X A M⊆lowOverlapVertices c₀ X A M

/-- An actual root-only normalization, preserving the primary profile
with explicit finite numerical budgets for both boundary palettes. -/
theorem exists_root_overlap_normalization_preserving_primary (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y : V} (hcm₀ : IsColMinus c₀ x y)
    (T A : Finset V) (F X : Finset (Fin G.maxDegree)) (m M L : ℕ)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hlow : ∀v∈T,(G.degree v:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hL : 1≤ε*(L:ℝ))
    (hthreshold : (m:ℝ)+((T.card-1:ℕ):ℝ)*
      ((F.card+(m+2)*T.card+(M+2)*A.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : F.card+(m+2)*T.card+(M+2)*A.card+T.card*m<(missing c₀ x).card) :
    ∃c : PEC G (Fin G.maxDegree),State c₀ c x y F X A M ∧
      (lowOverlapVertices c (missing c x) T m).card<L := by
  let P (c : PEC G (Fin G.maxDegree)):=State c₀ c x y F X A M
  let low (c : PEC G (Fin G.maxDegree)):=lowOverlapVertices c (missing c x) T m
  let score (c : PEC G (Fin G.maxDegree)):=∑v∈low c,(missing c v∩missing c x).card
  have hp₀ : P c₀:=⟨hcm₀,fun _ => rfl,fun _ => Iff.rfl,fun _ _ _ _ => Iff.rfl,subset_rfl⟩
  have hlowSub (c : PEC G (Fin G.maxDegree)) : low c⊆T:=filter_subset _ _
  have hscoreBound (c : PEC G (Fin G.maxDegree)) : score c≤T.card*G.maxDegree := by
    have hb : ∀v∈low c,(missing c v∩missing c x).card≤G.maxDegree := by
      intro v _
      exact (card_le_card inter_subset_right).trans (by simpa using card_le_univ (missing c x))
    calc
      score c≤∑_v∈low c,G.maxDegree:=sum_le_sum hb
      _=(low c).card*G.maxDegree:=by simp only [sum_const,Nat.nsmul_eq_mul]
      _≤T.card*G.maxDegree:=Nat.mul_le_mul_right _ (card_le_card (hlowSub c))
  let Min : ℕ → Prop:=fun n => ∃c,P c ∧ (low c).card=n
  have hMin : ∃n,Min n:=⟨(low c₀).card,c₀,hp₀,rfl⟩
  obtain ⟨c₁,hp₁,hval₁⟩:=Nat.find_spec hMin
  let Max : ℕ → Prop:=fun n => ∃c,P c ∧ (low c).card=Nat.find hMin ∧ score c=n
  have hMax : Max (score c₁):=⟨c₁,hp₁,hval₁,rfl⟩
  obtain ⟨c,hp,hval,hscore⟩:=Nat.findGreatest_spec (hscoreBound c₁) hMax
  have hmin : ∀d,P d → (low c).card≤(low d).card := by
    intro d hd
    rw [hval]
    exact Nat.find_le ⟨d,hd,rfl⟩
  have hmax : ∀d,P d → (low d).card=(low c).card → score d≤score c := by
    intro d hd heq
    have hn : Max (score d):=⟨d,hd,heq.trans hval,rfl⟩
    have hh:=Nat.le_findGreatest (hscoreBound d) hn
    rwa [←hscore] at hh
  refine ⟨c,hp,?_⟩
  change (low c).card<L
  by_contra hn
  have hcard : L≤(low c).card:=by omega
  let R₀:=boundaryPalette c (missing c x) T m
  let R₁:=boundaryPalette c X A M
  let C:=(F∪R₀)∪R₁
  have hC : C.card≤F.card+(m+2)*T.card+(M+2)*A.card := by
    have h0:=card_union_le F R₀
    have h1:=card_union_le (F∪R₀) R₁
    change C.card≤(F∪R₀).card+R₁.card at h1
    have hc0:=boundaryPalette_card_le c (missing c x) T m
    have hc1:=boundaryPalette_card_le c X A M
    change R₀.card≤(m+2)*T.card at hc0
    change R₁.card≤(M+2)*A.card at hc1
    omega
  have hFx : missing c x=missing c₀ x := by
    ext γ
    simp only [mem_missing,IsFree]
    simp_rw [hp.rootRow]
  have hroot : ∀v∈low c,(missing c v∩missing c x).card≤m:=fun v hv => (mem_filter.mp hv).2
  have hsize : 1≤ε*((low c).card:ℝ) :=
    hL.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hε.le)
  have hth : (m:ℝ)+(((low c).card-1:ℕ):ℝ)*((C.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    have hN : ((low c).card-1:ℕ)≤T.card-1:=by have hh:=card_le_card (hlowSub c);omega
    have hCR : ((C.card+1:ℕ):ℝ)≤((F.card+(m+2)*T.card+(M+2)*A.card+1:ℕ):ℝ) := by
      exact_mod_cast (show C.card+1≤F.card+(m+2)*T.card+(M+2)*A.card+1 by omega)
    have hNR : (((low c).card-1:ℕ):ℝ)≤((T.card-1:ℕ):ℝ):=by exact_mod_cast hN
    have hh:=mul_le_mul hNR hCR (by positivity) (by positivity)
    nlinarith only [hh,hthreshold]
  have hbud : C.card+(low c).card*m<(missing c x).card := by
    rw [hFx]
    have hh:=Nat.mul_le_mul_right m (card_le_card (hlowSub c))
    omega
  obtain ⟨v,hv,δ,η,hδC,hηC,hδ,hη,hvη,hTδ,hoff,hrow,hcol,hinc⟩:=
    exists_protected_kempe_improvement c x (low c) C ε hε hεone m hx
      (fun v hv => hlow v (hlowSub c hv)) hroot hsize hth hbud
  let d:=c.kempeSwap δ η v
  have hdx : missing d x=missing c x := by
    ext γ
    simpa only [mem_missing] using isFree_kempeSwap_of_not_reachable c δ η hoff γ
  have hprimaryStep : lowOverlapVertices d X A M⊆lowOverlapVertices c X A M := by
    exact lowOverlapVertices_subset_of_protected_boundary c δ η v X A M
      (fun he => hδC (mem_union_right _ he)) (fun he => hηC (mem_union_right _ he))
  have hpd : P d := by
    refine ⟨hp.cm.kempeSwap δ η v,fun w => (hrow w).trans (hp.rootRow w),?_,?_,
      hprimaryStep.trans hp.primarySubset⟩
    · intro γ
      exact (protected_swap_keeps_other_endpoint hG hp.cm hδ hoff γ).trans (hp.otherMissing γ)
    · intro a b γ hγ
      have hγδ : γ≠δ := by intro he;exact hδC (mem_union_left _ (mem_union_left _ (he ▸ hγ)))
      have hγη : γ≠η := by intro he;exact hηC (mem_union_left _ (mem_union_left _ (he ▸ hγ)))
      have he : d.col a b=some γ↔c.col a b=some γ := by
        by_cases hr : (c.kempeGraph δ η).Reachable v a
        · simpa only [Equiv.swap_apply_of_ne_of_ne hγδ hγη] using
            CaoChenPaletteKempeTransport.col_eq_swap_iff c δ η hr b γ
        · rw [kempeSwap_col,kempeSwapFun_of_not_reachable c δ η hr b]
      exact he.trans (hp.protectedColours a b γ hγ)
  have hsub : low d⊆low c := by
    change lowOverlapVertices d (missing d x) T m⊆lowOverlapVertices c (missing c x) T m
    rw [hdx]
    exact lowOverlapVertices_subset_of_protected_boundary c δ η v (missing c x) T m
      (fun he => hδC (mem_union_left _ (mem_union_right _ he)))
      (fun he => hηC (mem_union_left _ (mem_union_right _ he)))
  have heq : low d=low c:=eq_of_subset_of_card_le hsub (hmin d hpd)
  have hsmax:=hmax d hpd (congrArg Finset.card heq)
  have hsinc : score c+1≤score d := by
    change (∑w∈low c,(missing c w∩missing c x).card)+1≤
      ∑w∈low d,(missing d w∩missing d x).card
    rw [heq]
    exact hinc
  omega

end OverfullWork.CaoChenSecondaryNormalization
