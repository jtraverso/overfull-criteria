module

public import OverfullWork.CMSOperation41UniformPacking
public import OverfullWork.CMSOperation42Round

@[expose] public section


/-! The initial exceptional set and the actual ordinary host for
Operation 4.1. The density is measured against the original order
before the exceptional vertices are removed. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph RobustExpansion CMSMatchingRemoval
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def initialExceptionalSet (G : SimpleGraph V) [DecidableRel G.Adj] (η : ℝ) : Finset V :=
  univ.filter (fun v => η*(Fintype.card V:ℝ) < (G.maxDegree:ℝ)-G.degree v)

noncomputable def initialLowSet (G : SimpleGraph V) [DecidableRel G.Adj] (η : ℝ) : Finset V :=
  (initialExceptionalSet G η).filter
    (fun v => (G.degree v:ℝ) < (G.maxDegree:ℝ)/3-η*(Fintype.card V:ℝ))

theorem initial_low_set_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (η : ℝ) (hη : 0 ≤ η)
    (hVAL : ∀ u v,G.Adj u v → G.maxDegree+2 ≤ G.degree u+G.degree v) :
    G.IsIndepSet (initialLowSet G η : Set V) := by
  rw [isIndepSet_iff]
  intro u hu v hv _ h
  have hu' := (mem_filter.mp hu).2
  have hv' := (mem_filter.mp hv).2
  have hSum : (G.maxDegree:ℝ)+2 ≤ (G.degree u:ℝ)+G.degree v := by
    exact_mod_cast hVAL u v h
  linarith only [hu',hv',hSum,mul_nonneg hη (Nat.cast_nonneg (α := ℝ) (Fintype.card V)),
    Nat.cast_nonneg (α := ℝ) G.maxDegree]

theorem initial_core_density_and_robustness (G : SimpleGraph V) [DecidableRel G.Adj]
    (α η ν τ : ℝ) (hα : 0 < α) (hη : 0 ≤ η) (hHalfη : η ≤ 1/2)
    (hν : 0 ≤ ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hHalfτ : τ ≤ 1/2) :
    let n := Fintype.card V
    let U := initialExceptionalSet G η
    let A := Uᶜ
    let H := G.induce (A : Set V)
    let d := G.maxDegree
    let a := (d:ℝ)/(n:ℝ)
    0 < n → α*(n:ℝ) ≤ (d:ℝ) → (U.card:ℝ) ≤ η^2*(n:ℝ) →
    8*(U.card:ℝ) ≤ ν*(n:ℝ) → 4*(U.card:ℝ) ≤ τ*(n:ℝ) → IsRealRobust G ν τ →
    α ≤ a ∧ a ≤ 1 ∧ (∀ v : A,|(H.degree v:ℝ)-a*(A.card:ℝ)| ≤ 3*η*(A.card:ℝ)) ∧
      IsRealRobust H (ν/2) (2*τ) := by
  intro n U A H d a hn hDense hFew hSmallν hSmallτ hRob
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have : Nonempty V := Fintype.card_pos_iff.mp hn
  have hD : d < n := G.maxDegree_lt_card_verts
  have hA : α ≤ a := (le_div_iff₀ hnR).mpr hDense
  have hTop : a ≤ 1 := (div_le_iff₀ hnR).mpr (by rw [one_mul]; exact_mod_cast hD.le)
  have hd : a*(n:ℝ) = (d:ℝ) := by
    dsimp only [a]
    exact div_mul_cancel₀ _ (ne_of_gt hnR)
  have hCard : (A.card:ℝ)+(U.card:ℝ) = (n:ℝ) := by
    have h := card_add_card_compl U
    change U.card+A.card = n at h
    exact_mod_cast (show A.card+U.card = n by omega)
  have hScale : (U.card:ℝ) ≤ (η/2)*(n:ℝ) := by
    have h := mul_nonneg hη (sub_nonneg.mpr hHalfη)
    exact hFew.trans (mul_le_mul_of_nonneg_right (show η^2 ≤ η/2 by nlinarith only [h]) hnR.le)
  have hThree : (3/2:ℝ)*(n:ℝ) ≤ 3*(A.card:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hHalfη hnR.le
    linarith only [hCard,h,hScale]
  refine ⟨hA,hTop,?_,?_⟩
  · intro v
    have hv : v.val ∉ U := mem_compl.mp v.property
    have hOld : (d:ℝ)-G.degree v.val ≤ η*(n:ℝ) := by
      by_contra! h
      exact hv (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hInd := degree_le_induced_add_complement G A v
    rw [show Aᶜ = U from compl_compl U] at hInd
    have hIndR : (G.degree v.val:ℝ) ≤ (H.degree v:ℝ)+(U.card:ℝ) := by exact_mod_cast hInd
    have hUpper : (H.degree v:ℝ) ≤ (d:ℝ) := by
      have hB := SimpleGraph.degree_le_of_le (by
        intro u w h
        obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj (Function.Embedding.subtype _) H _ _).mp h
        exact hxy : H.map (Function.Embedding.subtype (fun x : V => x ∈ A)) ≤ G) (v := v.val)
      have he := CMSTrimmingRound.map_degree_at_embedding H (Function.Embedding.subtype (fun x : V=>x∈A)) v
      exact_mod_cast he.symm.trans_le (hB.trans (G.degree_le_maxDegree _))
    have ha₀ : 0 ≤ a := hα.le.trans hA
    have hx : a*(A.card:ℝ)+a*(U.card:ℝ) = d := by rw [←mul_add,hCard,hd]
    have hU : a*(U.card:ℝ) ≤ U.card := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hTop (Nat.cast_nonneg (α := ℝ) U.card)
    have hU0 := mul_nonneg ha₀ (Nat.cast_nonneg (α := ℝ) U.card)
    have hLen := mul_le_mul_of_nonneg_left hThree hη
    apply abs_le.mpr
    constructor <;> nlinarith only [hOld,hIndR,hUpper,hx,hU,hU0,hLen,hScale,
      mul_nonneg hη hnR.le]
  · apply induced_graph_robust_of_small_complement G A ν τ hν hν₁ hτ hHalfτ hRob
    · simpa only [A,compl_compl] using hSmallν
    · simpa only [A,compl_compl] using hSmallτ

theorem initial_round_limit_fits_core (n d m k l : ℕ) (a η gap : ℝ)
    (hSize : m+k = n) (hDensity : a*(n:ℝ) = (d:ℝ))
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) (hGap : 6*gap ≤ a)
    (hSmall : (k:ℝ) ≤ η*(n:ℝ)) (hRounds : (l:ℝ) ≤ (d:ℝ)/3-η*(n:ℝ)) :
    (l:ℝ) ≤ ((a-2*gap)/2)*(m:ℝ) := by
  have hSizeR : (m:ℝ)+(k:ℝ) = (n:ℝ) := by exact_mod_cast hSize
  have hCut : a*(m:ℝ)+a*(k:ℝ) = (d:ℝ) := by rw [←mul_add,hSizeR,hDensity]
  have hK : a*(k:ℝ) ≤ (k:ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha₁ (Nat.cast_nonneg (α := ℝ) k)
  have hKn := mul_nonneg ha (Nat.cast_nonneg (α := ℝ) k)
  have hMain : (l:ℝ) ≤ (a/3)*(m:ℝ) := by linarith only [hCut,hK,hKn,hSmall,hRounds]
  exact hMain.trans (mul_le_mul_of_nonneg_right (by linarith only [hGap]) (Nat.cast_nonneg _))

end OverfullWork.CMSTrimmingRound
