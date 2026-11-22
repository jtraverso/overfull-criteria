module

public import OverfullWork.CMSRegularizationImageTransport
public import OverfullWork.CMSRegularizationDeficitBase
public import OverfullWork.CMSOperation41ProjectedLayers

@[expose] public section


/-! Claim 4.3 on a simple stopping graph with up to two exceptional
degrees, including the extra vertex in the odd-order stopping cases. -/

namespace OverfullWork.OrderedCanonicalTransport

open Finset SimpleGraph
open scoped Classical

private theorem cutSize_reindex_simple_stop {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (M : MultiGraph V) (e : W ≃ V) (S : Finset W) :
    (reindex M e).cutSize S = M.cutSize (S.image e) := by
  have hCompl : Sᶜ.image e = (S.image e)ᶜ := by
    ext v
    have h (T : Finset W) : v ∈ T.image e ↔ e.symm v ∈ T := by
      constructor
      · intro hv
        obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
        simpa using hw
      · intro hv
        exact mem_image.mpr ⟨e.symm v,hv,e.apply_symm_apply _⟩
    simp only [h,mem_compl]
  unfold MultiGraph.cutSize
  rw [←hCompl,sum_image (fun _ _ _ _ h => e.injective h)]
  apply sum_congr rfl
  intro u _
  rw [sum_image (fun _ _ _ _ h => e.injective h)]
  rfl

end OverfullWork.OrderedCanonicalTransport

namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion OrderedCanonicalTransport PrunedCore
open scoped Classical
universe u

set_option maxHeartbeats 2400000 in
theorem cms_colourable_of_even_simple_with_degree_profiles (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ n → Even n → α*(n:ℝ) ≤ (d:ℝ) →
          ((∃ x y : V,∀ v,v ≠ x → v ≠ y → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) ∨
            ∀ p : V,(∀ v,G.degree p ≤ G.degree v) →
              ((∑ v ∈ univ.erase p,(d-G.degree v))+G.degree p : ℕ) ≤ (d:ℝ)+5*η*(n:ℝ)) →
          (∀ p q : V,p ≠ q → (∀ v,G.degree p ≤ G.degree v) →
            (∀ v,v ≠ p → G.degree q ≤ G.degree v) →
            ((G.neighborFinset p).erase q).card ≤ 1 →
              (∃ w : V,w ≠ p ∧ w ≠ q ∧ G.degree w < d ∧
                ∀ v,v ∉ ({p,q,w}:Finset V) → G.degree v = d) ∨
              ∀ v,v ≠ p → v ≠ q → d ≤ OddCutDeficit.cutEdges G {p,q,v}) →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν τ → G.EdgeColorable d := by
  obtain ⟨τ₁,hτ₁,hDense⟩ := cms_regularization_dense_simple_second α hα hα₁
  obtain ⟨τ₂,hτ₂,hBudget⟩ := cms_regularization_deficit_simple_second α hα hα₁
  let τ := min τ₁ τ₂
  refine ⟨τ,by dsimp only [τ]; positivity,?_⟩
  intro ν hν hντ
  obtain ⟨η₁,hη₁,hDense⟩ := hDense ν hν (hντ.trans (min_le_left _ _))
  obtain ⟨η₂,hη₂,hBudget⟩ := hBudget ν hν (hντ.trans (min_le_right _ _))
  let ηMax := min η₁ η₂
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  obtain ⟨N₁,hN₁⟩ := hDense η hη.le (hηMax.trans (min_le_left _ _))
  obtain ⟨N₂,hN₂⟩ := hBudget η hη.le (hηMax.trans (min_le_right _ _))
  let N₀ := max N₁ N₂
  obtain ⟨Q,hQ⟩ := exists_nat_ge (max (8/α) (1/(2*η^2)))
  refine ⟨max N₀ Q,?_⟩
  intro V _ _ G _ n d hn hEven hDens hDef hLocalG hNo hRob
  have hQR : (Q:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have hRes := hQ.trans hQR
  have hαn : 8 ≤ α*(n:ℝ) := by
    have hh := (div_le_iff₀ hα).mp ((le_max_left _ _).trans hRes)
    linarith only [hh]
  have hηn : 1 ≤ 2*η^2*(n:ℝ) := by
    have hh := (div_le_iff₀ (show 0 < 2*η^2 by positivity)).mp ((le_max_right _ _).trans hRes)
    linarith only [hh]
  have hPosN : 2 ≤ n := by
    have hαCap := mul_le_mul_of_nonneg_right hα₁ (Nat.cast_nonneg (α := ℝ) n)
    exact_mod_cast (show (2:ℝ) ≤ n by linarith only [hαn,hαCap])
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hd : d < n := G.maxDegree_lt_card_verts
  obtain ⟨k,hk⟩ := hEven
  have hShape : n = 2*((k-1)+1) := by omega
  let M := MultiGraph.ofSimpleGraph G
  obtain ⟨e,hPair,hOrder⟩ := exists_paired_sorted_equiv M.degree ((k-1)+1) hShape
  let W := Fin ((k-1)+1) × Bool
  let D := reindex M e
  let a : W := (0,false)
  let b : W := (0,true)
  have hAB : a ≠ b := by intro h; cases congrArg Prod.snd h
  have hCard : Fintype.card W = n := Fintype.card_congr e
  have hDeg (v : W) : D.degree v = G.degree (e v) := by
    simp only [D,degree_reindex,M,MultiGraph.degree_ofSimpleGraph]
  have hBound : ∀ v,D.degree v ≤ d := fun v => (hDeg v).trans_le (G.degree_le_maxDegree _)
  have hSimple (s : Sym2 W) : D.mult s ≤ 1 := by
    change (if Sym2.map e s ∈ G.edgeSet then 1 else 0) ≤ 1
    split_ifs <;> omega
  have hSupport (v : W) : D.supportGraph.degree v = D.degree v := by
    rw [←MultiGraph.degree_ofSimpleGraph,MultiGraph.of_supportGraph _ hSimple]
  have hOrderPair : ∀ i,D.degree (i,false) ≤ D.degree (i,true) := by
    simpa only [D,degree_reindex] using hPair
  have hOrderNext : ∀ i j : Fin ((k-1)+1), i.val < j.val → D.degree (i,true) ≤ D.degree (j,false) := by
    simpa only [D,degree_reindex] using hOrder
  have hFirst (v : W) : D.degree a ≤ D.degree v := by
    apply ordered_rank_mono_of_pairs hOrderPair hOrderNext
    change (pairedIndex ((k-1)+1) a).val ≤ (pairedIndex ((k-1)+1) v).val
    simp [a,pairedIndex_false_val]
  have hSecond (v : W) (hv : v ≠ a) : D.degree b ≤ D.degree v := by
    obtain ⟨i,j⟩ := v
    by_cases hi : i = 0
    · subst i
      cases j
      · exact (hv rfl).elim
      · exact le_rfl
    · have hi' : (0 : Fin ((k-1)+1)).val < i.val := by
        change 0 < i.val
        exact Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
      cases j
      · exact hOrderNext _ _ hi'
      · exact (hOrderNext _ _ hi').trans (hOrderPair _)
  have hFirstG (v : V) : G.degree (e a) ≤ G.degree v := by
    have h := hFirst (e.symm v)
    rwa [hDeg,hDeg,e.apply_symm_apply] at h
  have hOrd (hOrdG : ∃ x y : V,∀ v,v ≠ x → v ≠ y →
      (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) (v : W) (hva : v ≠ a) (hvb : v ≠ b) :
      (d:ℝ)-6*η*(Fintype.card W:ℝ) ≤ D.supportGraph.degree v := by
    obtain ⟨x,y,hOrdG⟩ := hOrdG
    rw [hSupport,hCard]
    by_contra hn
    have hBad (w : W) (hw : D.degree w ≤ D.degree v) : e w = x ∨ e w = y := by
      by_contra hw'
      push Not at hw'
      have hh := hOrdG _ hw'.1 hw'.2
      rw [←hDeg w] at hh
      exact hn (hh.trans (by exact_mod_cast hw))
    have hAV : e a ≠ e v := fun h => hva (e.injective h.symm)
    have hBV : e b ≠ e v := fun h => hvb (e.injective h.symm)
    have hAB' : e a ≠ e b := fun h => hAB (e.injective h)
    rcases hBad a (hFirst v) with ha | ha <;>
      rcases hBad b (hSecond v hva) with hb | hb <;>
      rcases hBad v le_rfl with hv | hv <;>
      grind only
  have hAdj (p q : W) : D.supportGraph.Adj p q ↔ G.Adj (e p) (e q) := by
    change 0 < (if s(e p,e q) ∈ G.edgeSet then 1 else 0) ↔ _
    by_cases h : G.Adj (e p) (e q)
    · simp [h,G.mem_edgeSet.mpr h]
    · simp [h,show s(e p,e q) ∉ G.edgeSet from fun hh => h (G.mem_edgeSet.mp hh)]
  have hErased : ((D.supportGraph.neighborFinset a).erase b).image e =
      (G.neighborFinset (e a)).erase (e b) := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      obtain ⟨hwb,hw⟩ := mem_erase.mp hw
      exact mem_erase.mpr ⟨fun hh => hwb (e.injective hh),
        (mem_neighborFinset _ _ _).mpr ((hAdj _ _).mp ((mem_neighborFinset _ _ _).mp hw))⟩
    · intro hv
      obtain ⟨hvb,hv⟩ := mem_erase.mp hv
      refine mem_image.mpr ⟨e.symm v,mem_erase.mpr ⟨?_,?_⟩,e.apply_symm_apply _⟩
      · intro hh
        apply hvb
        rw [←hh,e.apply_symm_apply]
      · apply (mem_neighborFinset _ _ _).mpr
        rw [hAdj,e.apply_symm_apply]
        exact (mem_neighborFinset _ _ _).mp hv
  have hLocal : ((D.supportGraph.neighborFinset a).erase b).card ≤ 1 →
      (∃ w : W,w ≠ a ∧ w ≠ b ∧ D.degree w < d ∧
        ∀ v,v ∉ ({a,b,w}:Finset W) → D.degree v = d) ∨
      ∀ v,v ≠ a → v ≠ b → d ≤ D.cutSize {a,b,v} := by
    intro hSmall
    have hS (v : V) (hv : v ≠ e a) : G.degree (e b) ≤ G.degree v := by
      have h := hSecond (e.symm v) (fun hh => hv (by rw [←hh,e.apply_symm_apply]))
      rwa [hDeg,hDeg,e.apply_symm_apply] at h
    have hSmall' := hSmall
    rw [←card_image_of_injective _ e.injective,hErased] at hSmall'
    rcases hLocalG (e a) (e b) (fun h => hAB (e.injective h)) hFirstG hS hSmall' with h | h
    · left
      obtain ⟨w,hwa,hwb,hdw,hEq⟩ := h
      refine ⟨e.symm w,fun hh => hwa (by rw [←hh,e.apply_symm_apply]),
        fun hh => hwb (by rw [←hh,e.apply_symm_apply]),by rwa [hDeg,e.apply_symm_apply],?_⟩
      intro v hv
      rw [hDeg]
      apply hEq
      intro hIn
      rw [mem_insert,mem_insert,mem_singleton] at hIn
      apply hv
      rw [mem_insert,mem_insert,mem_singleton]
      rcases hIn with ha | hb | hw
      · exact Or.inl (e.injective ha)
      · exact Or.inr (Or.inl (e.injective hb))
      · exact Or.inr (Or.inr (e.injective (hw.trans (e.apply_symm_apply w).symm)))
    · right
      intro v hva hvb
      rw [cutSize_reindex_simple_stop]
      simpa only [M,image_insert,image_singleton,←OddCutDeficit.cutEdges_eq_multigraph] using
        h (e v) (fun hh => hva (e.injective hh)) (fun hh => hvb (e.injective hh))
  have hMultiNo : ¬M.HasOverfullSubset d := by
    rintro ⟨S,hS⟩
    apply hNo
    refine ⟨S,?_⟩
    change d*(S.card/2) < OddCutDeficit.internalEdges G S
    rw [OddCutDeficit.internalEdges_eq_multigraph]
    exact hS
  have hNo' := no_overfull_reindex M e d hMultiNo
  have hRobM : IsRealRobust M.supportGraph ν τ := by
    intro S hLo hHi
    have hSub : realNeighbourhood G ν S ⊆ realNeighbourhood M.supportGraph ν S := by
      intro v hv
      have hNb : neighboursIn G S v ≤ neighboursIn M.supportGraph S v := by
        rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card]
        apply card_le_card
        intro w hw
        obtain ⟨hwS,hAdj⟩ := mem_filter.mp hw
        exact mem_filter.mpr ⟨hwS,by
          change 0 < (if s(v,w) ∈ G.edgeSet then 1 else 0)
          rw [if_pos (G.mem_edgeSet.mpr hAdj)]
          decide⟩
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2.trans (by exact_mod_cast hNb)⟩
    exact (hRob S hLo hHi).trans (by exact_mod_cast card_le_card hSub)
  have hRobD := real_robust_support_reindex M e ν τ hRobM
  have hRobAt (σ : ℝ) (hτσ : τ ≤ σ) : IsRealRobust D.supportGraph ν σ := by
    intro S hLo hHi
    have hScale := mul_le_mul_of_nonneg_right hτσ (Nat.cast_nonneg (α := ℝ) (Fintype.card W))
    exact hRobD S (hScale.trans hLo) (by nlinarith only [hHi,hScale])
  have hCapacity (v : W) (_ : v ≠ a) (_ : v ≠ b) :
      (D.mult s(a,v):ℝ) ≤ 2*η^2*(Fintype.card W:ℝ) := by
    rw [hCard]
    exact (by exact_mod_cast hSimple s(a,v) : (D.mult s(a,v):ℝ) ≤ 1).trans hηn
  have hCompletion : ∃ C : Completion D d,Nonempty (((D.addCopies C.L).addCopies C.N).EdgeColoring d) := by
    have hSize : N₀ ≤ Fintype.card W := by rw [hCard]; exact (le_max_left _ _).trans hn
    have hLess : d < Fintype.card W := by rwa [hCard]
    have hDens' : α*(Fintype.card W:ℝ) ≤ d := by rwa [hCard]
    rcases hDef with hRegular | hDeficit
    · exact hN₁ D d ((le_max_left _ _).trans hSize) hLess hDens' hBound hNo'
        hOrderPair hOrderNext (fun _ => hSimple _) hCapacity (hOrd hRegular) hLocal
        (hRobAt τ₁ (min_le_left _ _))
    · have hSet : (univ.erase a).image e = univ.erase (e a) := by
        ext v
        simp only [mem_image,mem_erase,mem_univ,and_true]
        constructor
        · rintro ⟨u,hu,rfl⟩
          exact fun h => hu (e.injective h)
        · intro hv
          exact ⟨e.symm v,fun h => hv (by rw [←e.apply_symm_apply v,h]),e.apply_symm_apply v⟩
      have hSum : (∑ v ∈ univ.erase a,(d-D.degree v)) = ∑ v ∈ univ.erase (e a),(d-G.degree v) := by
        simp_rw [hDeg]
        rw [←hSet,sum_image (fun _ _ _ _ h => e.injective h)]
      apply hN₂ D d ((le_max_right _ _).trans hSize) hLess hDens' hBound hNo'
        hOrderPair hOrderNext (fun _ _ _ _ => hSimple _) (fun _ => hSimple _) hCapacity
        _ hLocal (hRobAt τ₂ (min_le_right _ _))
      rw [hCard,hSum,hDeg]
      exact hDeficit (e a) hFirstG
  obtain ⟨C,⟨F⟩⟩ := hCompletion
  obtain ⟨F'⟩ := CanonicalColouringPullback.restrict_copies D _ F (by
    intro t
    change D.mult t ≤ D.mult t+C.L.mult t+C.N.mult t
    omega)
  obtain ⟨F₀⟩ := CanonicalColouringPullback.undo_reindex M e F'
  exact CMSTrimmingRound.simple_colourable_of_copy_colouring G F₀

theorem cms_colourable_of_even_simple_with_two_exceptions (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ n → Even n → α*(n:ℝ) ≤ (d:ℝ) →
          (∃ x y : V,∀ v,v ≠ x → v ≠ y → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) →
          (∀ p q : V,p ≠ q → (∀ v,G.degree p ≤ G.degree v) →
            (∀ v,v ≠ p → G.degree q ≤ G.degree v) →
            ((G.neighborFinset p).erase q).card ≤ 1 →
              (∃ w : V,w ≠ p ∧ w ≠ q ∧ G.degree w < d ∧
                ∀ v,v ∉ ({p,q,w}:Finset V) → G.degree v = d) ∨
              ∀ v,v ≠ p → v ≠ q → d ≤ OddCutDeficit.cutEdges G {p,q,v}) →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν τ → G.EdgeColorable d := by
  obtain ⟨τ,hτ,hUse⟩ := cms_colourable_of_even_simple_with_degree_profiles α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse ν hν hντ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hN⟩ := hUse η hη hηMax
  refine ⟨N,?_⟩
  intro V _ _ G _ n d hn hEven hDens hOrd hLocal hNo hRob
  exact hN G hn hEven hDens (Or.inl hOrd) hLocal hNo hRob

end OverfullWork.CanonicalRegularization
