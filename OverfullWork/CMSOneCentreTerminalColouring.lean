module

public import OverfullWork.CMSCleanupRobustness
public import OverfullWork.CMSOneCentreRobustOddCuts
public import OverfullWork.CMSOneCentreLocalProfiles
public import OverfullWork.CentredCanonicalCandidate
public import OverfullWork.CMSRegularizationDeficitBase
public import OverfullWork.CMSRegularizationImageTransport

@[expose] public section


/-! The single identification of CMS Subcase 2.3. The actual quotient
is ordered with its identified vertex first, completed, and its
colouring is pulled back to the source graph. -/
namespace OverfullWork.NormalizedCanonicalCandidate

open Finset SimpleGraph NormalizedAlmostStoppingRun IndependentSetIdentification
open OrderedCanonicalTransport RobustExpansion
open scoped Classical
universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem exists_centred_candidate_of_no_overfull_image (G : SimpleGraph V) [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) (hNo : ¬c.image.HasOverfullSubset G.maxDegree)
    (hMin : ∀ x ∈ c.set,(∑ y ∈ c.setᶜ,G.degree y) ≤ G.degree x) :
    ∃ p : Candidate c,p.centre = (0,false) := by
  have hInd : G.IsIndepSet (↑(c.setᶜ) : Set V) := by
    simpa only [coe_compl] using c.independent
  have hOdd : Odd c.setᶜᶜ.card := by simpa only [compl_compl] using c.odd
  have hMin' (x : V) (hx : x ∉ c.setᶜ) : (∑ y ∈ c.setᶜ,G.degree y) ≤ G.degree x :=
    hMin x (by simpa only [mem_compl,not_not] using hx)
  obtain ⟨hDegree,hFull⟩ := ConditionalIndependentIdentification.actual_image_has_maximum_degree
    G c.setᶜ hInd hOdd hMin'
  obtain ⟨k,hk⟩ := c.odd
  have hCard : Fintype.card (Vertices c.setᶜ) = 2*(k+1) := by
    rw [card_vertices,compl_compl,hk]
    omega
  obtain ⟨e,hPair,hOrder,⟨C⟩⟩ := exists_ordered_completion c.image G.maxDegree k hCard hDegree hNo
  exact (⟨hDegree,hFull,hNo,k,e,hPair,hOrder,C⟩ : Candidate c).exists_centred hMin

end OverfullWork.NormalizedCanonicalCandidate

namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion OddCutDeficit
open NormalizedAlmostStoppingRun NormalizedCanonicalCandidate OrderedCanonicalTransport
open IndependentSetIdentification ConditionalIndependentIdentification
open scoped Classical

universe u

theorem real_robust_identified_support {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hInd : G.IsIndepSet (Y : Set V)) (hY : 0 < Y.card)
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) :
    let n := Fintype.card V
    let m := Fintype.card (Vertices Y)
    (Y.card:ℝ)+1 ≤ (ν/2)*(n:ℝ) →
    τ*(n:ℝ)+2 ≤ (2*τ)*(m:ℝ) →
    IsRealRobust G ν τ → IsRealRobust (graph G Y hInd).supportGraph (ν/2) (2*τ) := by
  intro n m hLoss hMargin hRob
  let r := ⌈ν*(n:ℝ)⌉₊
  let t := ⌈τ*(n:ℝ)⌉₊
  have hm : m ≤ n := by
    dsimp only [m]
    rw [card_vertices]
    have hC := card_add_card_compl Y
    omega
  have hr : ν*(n:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
  have hrPos : Y.card+1 ≤ r := by
    have hh : (Y.card:ℝ)+1 ≤ (r:ℝ) := by
      have hScale : 0 ≤ ν*(n:ℝ) := by positivity
      linarith only [hLoss,hr,hScale]
    exact_mod_cast hh
  have hRScale : (ν/2)*(m:ℝ) ≤ ((r-(Y.card+1):ℕ):ℝ) := by
    rw [Nat.cast_sub hrPos,Nat.cast_add,Nat.cast_one]
    have h := mul_le_mul_of_nonneg_left (by exact_mod_cast hm : (m:ℝ) ≤ n) (by positivity : 0 ≤ ν/2)
    linarith only [h,hLoss,hr]
  have hTScale : ((t+1:ℕ):ℝ) ≤ (2*τ)*(m:ℝ) := by
    rw [Nat.cast_add,Nat.cast_one]
    have ht : (t:ℝ) < τ*(n:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
    linarith only [ht,hMargin]
  have hRobI : IsRobustAt G r t := integer_robust_of_real G ν τ hν hRob
  exact isRealRobust_of_integer _ _ _ _ _
    (robust_after_independent_identification G Y hInd r t hRobI) hRScale hTScale

set_option maxHeartbeats 3500000 in
theorem cms_colourable_of_robust_merged_stop_bounded_interval (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ,0 < τ ∧ τ ≤ α/64 ∧ ∀ ν : ℝ,0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ} (c : Certificate G B K),
          let Y := c.setᶜ
          let M := c.image
          let n := Fintype.card (Vertices Y)
          let d := G.maxDegree
          let r := ⌈ν*(n:ℝ)⌉₊
          let t := ⌈τ*(n:ℝ)⌉₊
          N ≤ n → d < n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ x ∈ c.set,(∑ y ∈ Y,G.degree y) ≤ G.degree x) →
          0 < (∑ y ∈ Y,G.degree y) → CleanedSourceVAL.IsReady G Y →
          (B:ℝ) ≤ 5*η*(n:ℝ) → (Y.card:ℝ) ≤ 2*η^2*(n:ℝ) → 2*Y.card+2 ≤ d →
          ¬G.HasOverfullSubgraph → IsRealRobust M.supportGraph ν τ →
          d ≤ r*r → t+B ≤ d → t+2*Y.card ≤ d+1 → G.EdgeColorable d := by
  obtain ⟨τ₀,hτ₀,hUse⟩ := cms_regularization_deficit_simple_second_away_from_first α hα hα₁
  let τ := min τ₀ (α/64)
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτLe : τ ≤ τ₀ := min_le_left _ _
  refine ⟨τ,hτ,min_le_right _ _,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse ν hν (hντ.trans hτLe)
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hN⟩ := hUse η hη hηMax
  refine ⟨N,?_⟩
  intro V _ _ G _ B K c Y M n d r t hn hLess hDens hMin hPos hReady hB hY hSmall
    hNo hRob hRate hOutside hInside
  have hInd : G.IsIndepSet (↑Y : Set V) := by simpa only [Y,coe_compl] using c.independent
  have hOdd : Odd Yᶜ.card := by simpa only [Y,compl_compl] using c.odd
  have hMin' (x : V) (hx : x ∉ Y) : (∑ y ∈ Y,G.degree y) ≤ G.degree x :=
    hMin x (by simpa only [Y,mem_compl,not_not] using hx)
  have hBudget : deficitMass G d Yᶜ+(∑ y ∈ Y,G.degree y) ≤ d+B := by
    simpa only [Y,d,compl_compl] using c.budget
  have hRobI : IsRobustAt M.supportGraph r t := integer_robust_of_real M.supportGraph ν τ hν.le hRob
  have hNoM : ¬M.HasOverfullSubset d := actual_image_no_overfull_of_robust G Y hInd hNo hOdd B r t
    hMin' hBudget hRobI hRate hOutside hInside
  obtain ⟨p,hCenter⟩ := exists_centred_candidate_of_no_overfull_image G c hNoM hMin
  let W := Fin (p.pairIndex+1) × Bool
  let e := p.coordinates
  let D := reindex M e
  let a : W := (0,false)
  let b : W := (0,true)
  have ha : e a = none := by
    have h : e.symm none = a := hCenter
    rw [←h,Equiv.apply_symm_apply]
  have hAB : a ≠ b := by intro h; cases congrArg Prod.snd h
  have hElse (v : W) (hv : v ≠ a) : e v ≠ none := fun h => hv (e.injective (h.trans ha.symm))
  have hCard : Fintype.card W = n := Fintype.card_congr e
  have hDeg (v : W) : D.degree v = M.degree (e v) := degree_reindex M e v
  have hBound (v : W) : D.degree v ≤ d := (hDeg v).trans_le (p.degree_le _)
  have hStar : D.IsStarAt a := by
    intro u v hu hv
    change M.mult (Sym2.map e s(u,v)) ≤ 1
    rw [Sym2.map_mk]
    exact isStarAt G Y hInd (e u) (e v) (hElse u hu) (hElse v hv)
  have hMu (v : W) : D.mult s(a,v) ≤ Y.card := by
    change M.mult s(e a,e v) ≤ Y.card
    rw [ha]
    cases h : e v with
    | none => rw [M.loopless _ (by simp)]; exact Nat.zero_le _
    | some v => exact centre_mult_le G Y hInd v
  have hCentrePos : 0 < D.degree a := by
    rw [hDeg,ha]
    change 0 < (graph G Y hInd).degree none
    rwa [degree_none]
  have hCentreMin (v : W) : D.degree a ≤ D.degree v := by
    rw [hDeg,hDeg,ha]
    cases h : e v with
    | none => exact le_rfl
    | some x =>
      change (graph G Y hInd).degree none ≤ (graph G Y hInd).degree (some x)
      rw [degree_none,degree_some]
      exact hMin' x.val x.property
  have hWeighted (v : W) : (d-D.degree v+2)*D.mult s(a,v) ≤ D.degree a := by
    rw [hDeg,hDeg,show D.mult s(a,v) = M.mult s(e a,e v) by rfl,ha]
    cases h : e v with
    | none => rw [M.loopless _ (by simp),Nat.mul_zero]; exact Nat.zero_le _
    | some x =>
      exact centre_weighted_degree_sum_of_weak_val G Y hInd (CleanedSourceVAL.weak_VAL G Y hReady) x
  have hSecondSimple (v : W) (hv : v ≠ a) : D.mult s(b,v) ≤ 1 := hStar b v hAB.symm hv
  have hPair : ∀ i,D.degree (i,false) ≤ D.degree (i,true) := by
    intro i
    rw [hDeg,hDeg]
    exact p.ordered_pair i
  have hOrder : ∀ i j : Fin (p.pairIndex+1),i.val < j.val → D.degree (i,true) ≤ D.degree (j,false) := by
    intro i j hij
    rw [hDeg,hDeg]
    exact p.ordered_next i j hij
  have hImage : (univ.erase a).image e = (univ : Finset (Vertices Y)).erase none := by
    ext v
    simp only [mem_image,mem_erase,mem_univ,and_true]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hElse u hu
    · intro hv
      exact ⟨e.symm v,fun h => hv (by rw [←(e.apply_symm_apply v),h,ha]),e.apply_symm_apply v⟩
  have hSum : (∑ v ∈ univ.erase a,(d-D.degree v))+D.degree a ≤ d+B := by
    simp_rw [hDeg]
    have h := (identified_centre_budget G Y hInd d).trans_le hBudget
    rw [←hImage,sum_image (fun _ _ _ _ h => e.injective h)] at h
    rwa [ha]
  have hSumR : ((∑ v ∈ univ.erase a,(d-D.degree v))+D.degree a : ℕ) ≤
      (d:ℝ)+5*η*(Fintype.card W:ℝ) := by
    rw [hCard]
    exact (by exact_mod_cast hSum : (_:ℝ) ≤ (d:ℝ)+B).trans (add_le_add_right hB _)
  have hBase (v : W) (_ : v ≠ a) (_ : v ≠ b) :
      (D.mult s(a,v):ℝ) ≤ 2*η^2*(Fintype.card W:ℝ) := by
    rw [hCard]
    exact (by exact_mod_cast hMu v : (D.mult s(a,v):ℝ) ≤ Y.card).trans hY
  have hRob₀ : IsRealRobust M.supportGraph ν τ₀ :=
    real_robust_of_subgraph_degree_loss M.supportGraph M.supportGraph le_rfl 0 ν ν τ τ₀
      le_rfl hτLe (by simp) (fun _ => by simp) hRob
  obtain ⟨C,⟨F⟩⟩ := hN D d (by rwa [hCard]) (by rwa [hCard]) (by rwa [hCard])
    hBound (no_overfull_reindex M e d hNoM) hPair hOrder hStar hSecondSimple hBase hSumR
    (fun hFew => Or.inr (sparse_first_bundle_triples D a b d Y.card hAB hBound hCentreMin
      hCentrePos hSmall hMu hSecondSimple hWeighted hFew))
    (real_robust_support_reindex M e ν τ₀ hRob₀)
  obtain ⟨F'⟩ := CanonicalColouringPullback.restrict_copies D _ F (by
    intro t
    change D.mult t ≤ D.mult t+C.L.mult t+C.N.mult t
    omega)
  obtain ⟨F₀⟩ := CanonicalColouringPullback.undo_reindex M e F'
  exact colourable_of_identification G Y hInd F₀

theorem cms_colourable_of_robust_merged_stop (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ,0 < τ ∧ ∀ ν : ℝ,0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ} (c : Certificate G B K),
          let Y := c.setᶜ
          let M := c.image
          let n := Fintype.card (Vertices Y)
          let d := G.maxDegree
          let r := ⌈ν*(n:ℝ)⌉₊
          let t := ⌈τ*(n:ℝ)⌉₊
          N ≤ n → d < n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ x ∈ c.set,(∑ y ∈ Y,G.degree y) ≤ G.degree x) →
          0 < (∑ y ∈ Y,G.degree y) → CleanedSourceVAL.IsReady G Y →
          (B:ℝ) ≤ 5*η*(n:ℝ) → (Y.card:ℝ) ≤ 2*η^2*(n:ℝ) → 2*Y.card+2 ≤ d →
          ¬G.HasOverfullSubgraph → IsRealRobust M.supportGraph ν τ →
          d ≤ r*r → t+B ≤ d → t+2*Y.card ≤ d+1 → G.EdgeColorable d := by
  obtain ⟨τ,hτ,_,hUse⟩ := cms_colourable_of_robust_merged_stop_bounded_interval α hα hα₁
  exact ⟨τ,hτ,hUse⟩

theorem cms_colourable_of_robust_merged_source_bounded_interval (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ,0 < σ ∧ σ ≤ α/128 ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ} (c : Certificate G B K),
          let Y := c.setᶜ
          let m := Fintype.card (Vertices Y)
          let n := Fintype.card V
          let d := G.maxDegree
          let r := ⌈(ν/2)*(m:ℝ)⌉₊
          let t := ⌈(2*σ)*(m:ℝ)⌉₊
          N ≤ m → d < m → α*(m:ℝ) ≤ (d:ℝ) →
          (∀ x ∈ c.set,(∑ y ∈ Y,G.degree y) ≤ G.degree x) →
          0 < (∑ y ∈ Y,G.degree y) → CleanedSourceVAL.IsReady G Y →
          (B:ℝ) ≤ 5*η*(m:ℝ) → (Y.card:ℝ) ≤ 2*η^2*(m:ℝ) → 2*Y.card+2 ≤ d →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν σ →
          (Y.card:ℝ)+1 ≤ (ν/2)*(n:ℝ) →
          σ*(n:ℝ)+2 ≤ (2*σ)*(m:ℝ) →
          d ≤ r*r → t+B ≤ d → t+2*Y.card ≤ d+1 → G.EdgeColorable d := by
  obtain ⟨τ,hτ,hBound,hUse⟩ := cms_colourable_of_robust_merged_stop_bounded_interval α hα hα₁
  let σ := τ/2
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hDouble : 2*σ = τ := by dsimp only [σ]; ring
  refine ⟨σ,hσ,by linarith only [hBound,hDouble],?_⟩
  intro ν hν hνσ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse (ν/2) (by positivity) (by linarith only [hνσ,hσ,hDouble])
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hN⟩ := hUse η hη hηMax
  refine ⟨N,?_⟩
  intro V _ _ G _ B K c Y m n d r t hN' hLess hDens hMin hPos hReady hB hY hSmall hNo hRob
    hLoss hMargin hRate hOutside hInside
  have hYP : 0 < Y.card := by
    by_contra! hh
    have he : Y = ∅ := card_eq_zero.mp (by omega)
    simp [he] at hPos
  have hInd : G.IsIndepSet (↑Y : Set V) := by simpa only [Y,coe_compl] using c.independent
  have hImage : IsRealRobust c.image.supportGraph (ν/2) (2*σ) :=
    real_robust_identified_support G Y hInd hYP ν σ hν.le hσ.le hLoss hMargin hRob
  have hImage' : IsRealRobust c.image.supportGraph (ν/2) τ := by rwa [hDouble] at hImage
  have hT : t = ⌈τ*(m:ℝ)⌉₊ := by dsimp only [t]; rw [hDouble]
  exact hN G c hN' hLess hDens hMin hPos hReady hB hY hSmall hNo hImage' hRate
    (by rw [←hT]; exact hOutside) (by rw [←hT]; exact hInside)

theorem cms_colourable_of_robust_merged_source (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ,0 < σ ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ} (c : Certificate G B K),
          let Y := c.setᶜ
          let m := Fintype.card (Vertices Y)
          let n := Fintype.card V
          let d := G.maxDegree
          let r := ⌈(ν/2)*(m:ℝ)⌉₊
          let t := ⌈(2*σ)*(m:ℝ)⌉₊
          N ≤ m → d < m → α*(m:ℝ) ≤ (d:ℝ) →
          (∀ x ∈ c.set,(∑ y ∈ Y,G.degree y) ≤ G.degree x) →
          0 < (∑ y ∈ Y,G.degree y) → CleanedSourceVAL.IsReady G Y →
          (B:ℝ) ≤ 5*η*(m:ℝ) → (Y.card:ℝ) ≤ 2*η^2*(m:ℝ) → 2*Y.card+2 ≤ d →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν σ →
          (Y.card:ℝ)+1 ≤ (ν/2)*(n:ℝ) →
          σ*(n:ℝ)+2 ≤ (2*σ)*(m:ℝ) →
          d ≤ r*r → t+B ≤ d → t+2*Y.card ≤ d+1 → G.EdgeColorable d := by
  obtain ⟨σ,hσ,_,hUse⟩ := cms_colourable_of_robust_merged_source_bounded_interval α hα hα₁
  exact ⟨σ,hσ,hUse⟩

end OverfullWork.CanonicalRegularization
