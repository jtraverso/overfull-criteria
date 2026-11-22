module

public import OverfullWork.CMSRegularizationWeakVALImage
public import OverfullWork.CanonicalColouringPullback

@[expose] public section


/-! Ordering and colouring transport for the two-group identification
in CMS Subcase 2.4. -/
namespace OverfullWork.OrderedCanonicalTransport

open Finset SimpleGraph RobustExpansion PrunedCore
open scoped Classical

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem real_robust_support_reindex (M : MultiGraph V) (e : W ≃ V) (ν τ : ℝ)
    (hRob : IsRealRobust M.supportGraph ν τ) :
    IsRealRobust (reindex M e).supportGraph ν τ := by
  have hCard : Fintype.card W = Fintype.card V := Fintype.card_congr e
  intro S hLo hHi
  have hS : (S.image e).card = S.card := card_image_of_injective _ e.injective
  have hNeigh (w : W) :
      neighboursIn (reindex M e).supportGraph S w = neighboursIn M.supportGraph (S.image e) (e w) := by
    rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card,
      ←card_image_of_injective (S.filter ((reindex M e).supportGraph.Adj w)) e.injective]
    congr 1
    ext v
    constructor
    · intro hv
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
      obtain ⟨huS,hAdj⟩ := mem_filter.mp hu
      exact mem_filter.mpr ⟨mem_image.mpr ⟨u,huS,rfl⟩,hAdj⟩
    · intro hv
      obtain ⟨hvS,hAdj⟩ := mem_filter.mp hv
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hvS
      exact mem_image.mpr ⟨u,mem_filter.mpr ⟨hu,hAdj⟩,rfl⟩
  have hN : (realNeighbourhood (reindex M e).supportGraph ν S).image e =
      realNeighbourhood M.supportGraph ν (S.image e) := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      have hh := (mem_filter.mp hw).2
      rw [hNeigh w,hCard] at hh
      exact mem_filter.mpr ⟨mem_univ _,hh⟩
    · intro hv
      refine mem_image.mpr ⟨e.symm v,mem_filter.mpr ⟨mem_univ _,?_⟩,e.apply_symm_apply _⟩
      rw [hNeigh,hCard,e.apply_symm_apply]
      exact (mem_filter.mp hv).2
  have h := hRob (S.image e) (by rwa [←hCard,hS]) (by rwa [←hCard,hS])
  rw [←hN] at h
  rw [card_image_of_injective (realNeighbourhood (reindex M e).supportGraph ν S) e.injective,hS] at h
  simpa only [hCard] using h

theorem support_degree_reindex (M : MultiGraph V) (e : W ≃ V) (v : W) :
    (reindex M e).supportGraph.degree v = M.supportGraph.degree (e v) := by
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree,
    ←card_image_of_injective _ e.injective]
  congr 1
  ext w
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩ := mem_image.mp h
    exact (mem_neighborFinset M.supportGraph (e v) (e u)).mpr
      ((mem_neighborFinset (reindex M e).supportGraph v u).mp hu)
  · intro h
    refine mem_image.mpr ⟨e.symm w,(mem_neighborFinset _ _ _).mpr ?_,e.apply_symm_apply _⟩
    change M.supportGraph.Adj (e v) (e (e.symm w))
    rw [e.apply_symm_apply]
    exact (mem_neighborFinset _ _ _).mp h

end OverfullWork.OrderedCanonicalTransport

namespace OverfullWork.TwoIndependentIdentifications

open Finset SimpleGraph RobustExpansion PrunedCore OrderedCanonicalTransport
open scoped Classical
universe u

set_option maxHeartbeats 700000 in
theorem cms_colourable_of_clean_two_identifications (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (Z A : Finset V) (hA : A ⊆ Z) (hInd : G.IsIndepSet (Z : Set V)),
          let M := graph G Z A hA hInd
          let n := Fintype.card (Vertices Z)
          let d := G.maxDegree
          N ≤ n → d < n → α*(n:ℝ) ≤ (d:ℝ) → Even n →
          ((Z.card:ℝ) ≤ 2*η^2*(n:ℝ)) →
          (∀ j : Bool, (M.degree (Sum.inl j):ℝ) ≤ 10*η*(n:ℝ)) →
          (∀ x : Outside Z, (d:ℝ)-6*η*(n:ℝ) ≤ (M.supportGraph.degree (Sum.inr x):ℝ)) →
          (∀ u ∈ Z, ∀ v, G.Adj u v → d+2 ≤ G.degree u+G.degree v) →
          ¬M.HasOverfullSubset d → IsRealRobust M.supportGraph ν τ →
          G.EdgeColorable d := by
  obtain ⟨τ,hτ,hMain⟩ := CanonicalRegularization.cms_regularization_dense_two_centres α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨η₀,hη₀,hUse⟩ := hMain ν hν hντ
  let ηMax := min η₀ (α/32)
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηCap
  obtain ⟨N,hN⟩ := hUse η hη (hηCap.trans (min_le_left _ _))
  refine ⟨N,?_⟩
  intro V _ _ G _ Z A hA hInd M n d hSize hd hRel hEven hCardZ hSmall hHigh hWeak hNo hRob
  have hn : 2 ≤ n := by dsimp only [n]; rw [card_vertices]; omega
  obtain ⟨k,hk⟩ := hEven
  have hShape : n = 2*((k-1)+1) := by omega
  obtain ⟨e,hPair,hOrder⟩ := exists_paired_sorted_equiv M.degree ((k-1)+1) hShape
  let D := reindex M e
  let W := Fin ((k-1)+1) × Bool
  let a : W := (0,false)
  let b : W := (0,true)
  have hW : Fintype.card W = n := Fintype.card_congr e
  have hab : a ≠ b := by intro h; cases congrArg Prod.snd h
  have hPairD : ∀ i, D.degree (i,false) ≤ D.degree (i,true) := by
    simpa only [D,degree_reindex] using hPair
  have hOrderD : ∀ i j : Fin ((k-1)+1), i.val < j.val → D.degree (i,true) ≤ D.degree (j,false) := by
    simpa only [D,degree_reindex] using hOrder
  have hGap (i : Bool) (x : Outside Z) : M.degree (Sum.inl i) < M.degree (Sum.inr x) := by
    have hs := MultiGraph.support_degree_le_degree M (Sum.inr x)
    have hSupport : (M.supportGraph.degree (Sum.inr x):ℝ) ≤ M.degree (Sum.inr x) := by exact_mod_cast hs
    have hη' := hηCap.trans (min_le_right _ _)
    have hScale := mul_le_mul_of_nonneg_right hη' (Nat.cast_nonneg (α := ℝ) n)
    have hPos : 0 < α*(n:ℝ) := mul_pos hα (by exact_mod_cast (show 0 < n by omega))
    exact_mod_cast (show (M.degree (Sum.inl i):ℝ) < M.degree (Sum.inr x) by
      linarith only [hSmall i,hHigh x,hSupport,hScale,hPos,hRel])
  have hSecond (w : W) (hw : w ≠ a) : D.degree b ≤ D.degree w := by
    obtain ⟨i,j⟩ := w
    by_cases hi : i = 0
    · subst i
      cases j
      · exact False.elim (hw rfl)
      · exact le_rfl
    · have hi' : (0:Fin ((k-1)+1)).val < i.val :=
        Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
      cases j
      · exact hOrderD 0 i hi'
      · exact (hOrderD 0 i hi').trans (hPairD i)
  have hAnchorB : ∃ j : Bool, e b = Sum.inl j := by
    cases h : e b with
    | inl j => exact ⟨j,rfl⟩
    | inr x =>
      let j := decide (e a = Sum.inl false)
      have he : Sum.inl j ≠ e a := by
        by_cases hj : e a = Sum.inl false
        · simp [j,hj]
        · simpa [j,hj] using Ne.symm hj
      have hw : e.symm (Sum.inl j) ≠ a := fun hh => he (by rw [←hh,e.apply_symm_apply])
      have hh := hSecond (e.symm (Sum.inl j)) hw
      simp only [D,degree_reindex,h,e.apply_symm_apply] at hh
      exact False.elim ((hGap j x).not_ge hh)
  have hAnchorA : ∃ j : Bool, e a = Sum.inl j := by
    obtain ⟨j,hb⟩ := hAnchorB
    cases h : e a with
    | inl i => exact ⟨i,rfl⟩
    | inr x =>
      have hh : M.degree (e a) ≤ M.degree (e b) := hPair 0
      rw [h,hb] at hh
      exact False.elim ((hGap j x).not_ge hh)
  have hOrd (w : W) (hwa : w ≠ a) (hwb : w ≠ b) : ∃ x : Outside Z, e w = Sum.inr x := by
    cases h : e w with
    | inr x => exact ⟨x,rfl⟩
    | inl j =>
      obtain ⟨i,ha⟩ := hAnchorA
      obtain ⟨l,hb⟩ := hAnchorB
      have hil : i ≠ l := fun hh => hab (e.injective (by rw [ha,hb,hh]))
      have hj : j = i ∨ j = l := by cases i <;> cases l <;> cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | exact False.elim (hil rfl)
      rcases hj with hji|hjl
      · exact False.elim (hwa (e.injective (by rw [h,ha,hji])))
      · exact False.elim (hwb (e.injective (by rw [h,hb,hjl])))
  have hDeg (w : W) : D.degree w ≤ d := by
    simp only [D,degree_reindex]
    cases he : e w with
    | inr x => rw [degree_inr]; exact G.degree_le_maxDegree _
    | inl j =>
      have hBound := hSmall j
      have hScale := mul_le_mul_of_nonneg_right (hηCap.trans (min_le_right _ _)) (Nat.cast_nonneg (α := ℝ) n)
      have hNon := mul_nonneg hα.le (Nat.cast_nonneg (α := ℝ) n)
      have hh : (M.degree (Sum.inl j):ℝ) ≤ d := by linarith only [hBound,hScale,hRel,hNon]
      exact_mod_cast hh
  have hNoD := no_overfull_reindex M e d hNo
  have hAB : D.mult s(a,b) = 0 := by
    obtain ⟨i,ha⟩ := hAnchorA
    obtain ⟨j,hb⟩ := hAnchorB
    change M.mult s(e a,e b) = 0
    rw [ha,hb]
    exact mult_centres G Z A hA hInd i j
  have hWeighted (w : W) (hwa : w ≠ a) (hwb : w ≠ b) (i : Bool) :
      (d-D.degree w+2)*D.mult s((0,i),w) ≤ D.degree (0,i) := by
    obtain ⟨x,hx⟩ := hOrd w hwa hwb
    have hh : ∃ j : Bool,e (0,i) = Sum.inl j := by
      cases i
      · exact hAnchorA
      · exact hAnchorB
    obtain ⟨j,hj⟩ := hh
    simp only [D,degree_reindex,reindex_mult,Sym2.map_mk]
    rw [hx,hj]
    exact centre_bundle_weighted_of_weak_val G Z A hA hInd hWeak j x
  have hSmallB : (D.degree b:ℝ) ≤ 10*η*(Fintype.card W:ℝ) := by
    obtain ⟨j,hj⟩ := hAnchorB
    simp only [D,degree_reindex,hj,hW]
    exact hSmall j
  have hMult (w : W) (hwa : w ≠ a) (hwb : w ≠ b) :
      (D.mult s(a,w):ℝ) ≤ 2*η^2*(Fintype.card W:ℝ) := by
    obtain ⟨i,ha⟩ := hAnchorA
    obtain ⟨x,hx⟩ := hOrd w hwa hwb
    change (M.mult s(e a,e w):ℝ) ≤ _
    rw [ha,hx,hW]
    have hh := (centre_mult_le G Z A hA hInd i x).trans (card_le_card (part_subset Z A hA i))
    have hhR : (M.mult s(Sum.inl i,Sum.inr x):ℝ) ≤ Z.card := by exact_mod_cast hh
    exact hhR.trans hCardZ
  have hSup (w : W) (hwa : w ≠ a) (hwb : w ≠ b) :
      (d:ℝ)-6*η*(Fintype.card W:ℝ) ≤ D.supportGraph.degree w := by
    obtain ⟨x,hx⟩ := hOrd w hwa hwb
    simp only [D,support_degree_reindex,hW]
    rw [hx]
    exact hHigh x
  have hRobD := real_robust_support_reindex M e ν τ hRob
  obtain ⟨C,⟨H⟩⟩ := hN D d (by rw [hW]; exact hSize) (by rw [hW]; exact hd)
    (by rw [hW]; exact hRel) hDeg hNoD hPairD hOrderD hAB hWeighted hSmallB hMult hSup hRobD
  obtain ⟨F⟩ := CanonicalColouringPullback.restrict_copies D _ H (by
    intro t
    change D.mult t ≤ D.mult t+C.L.mult t+C.N.mult t
    omega)
  obtain ⟨I⟩ := CanonicalColouringPullback.undo_reindex M e F
  exact colourable_of_identifications G Z A hA hInd I

end OverfullWork.TwoIndependentIdentifications
