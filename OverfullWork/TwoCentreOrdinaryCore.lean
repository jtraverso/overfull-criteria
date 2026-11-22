module

public import OverfullWork.DenseCoreCutBound
public import OverfullWork.TwoIdentificationMultiplicities

@[expose] public section


/-! Ordinary vertices, exact counts and cut transport for two centres. -/
namespace OverfullWork.TwoCentreOrdinaryCore
open SimpleGraph Finset
open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]
set_option maxHeartbeats 8000000

def ordinary (M : MultiGraph (Sum Bool W)) : MultiGraph W where
  mult e := M.mult (Sym2.map Sum.inr e)
  loopless e he := by
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hh := Sym2.mk_isDiag_iff.mp he
      subst b
      exact M.loopless _ (by simp)

@[simp] theorem ordinary_mult (M : MultiGraph (Sum Bool W)) (u v : W) :
    (ordinary M).mult s(u,v)=M.mult s(Sum.inr u,Sum.inr v) := rfl

def ordinaryVertices (S : Finset (Sum Bool W)) : Finset W := univ.filter fun w => Sum.inr w ∈ S

theorem ordinaryVertices_compl (S : Finset (Sum Bool W)) :
    ordinaryVertices Sᶜ=(ordinaryVertices S)ᶜ := by ext w;simp [ordinaryVertices]

theorem card_split (S : Finset (Sum Bool W)) :
    S.card=(ordinaryVertices S).card+(if Sum.inl false ∈ S then 1 else 0)+
      (if Sum.inl true ∈ S then 1 else 0) := by
  have hS : S.card=∑ v : Sum Bool W, if v ∈ S then 1 else 0 := by simp
  rw [hS,Fintype.sum_sum_type,Fintype.sum_bool]
  have hOrd : (∑ w : W, if Sum.inr w ∈ S then 1 else 0)=(ordinaryVertices S).card := by
    simp [ordinaryVertices]
  rw [hOrd]
  omega

theorem cut_ordinary_le (M : MultiGraph (Sum Bool W)) (S : Finset (Sum Bool W)) :
    (ordinary M).cutSize (ordinaryVertices S) ≤ M.cutSize S := by
  have hA : (ordinaryVertices S).image Sum.inr ⊆ S := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hw).2
  have hB : ((ordinaryVertices S)ᶜ).image Sum.inr ⊆ Sᶜ := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    simpa [ordinaryVertices] using hw
  have hEq : (ordinary M).cutSize (ordinaryVertices S)=
      ∑ u ∈ (ordinaryVertices S).image Sum.inr,
        ∑ v ∈ ((ordinaryVertices S)ᶜ).image Sum.inr, M.mult s(u,v) := by
    rw [MultiGraph.cutSize,sum_image (fun _ _ _ _ h => Sum.inr.inj h)]
    simp_rw [sum_image (fun _ _ _ _ h => Sum.inr.inj h),ordinary_mult]
  rw [hEq]
  apply (sum_le_sum (fun u _ => sum_le_sum_of_subset_of_nonneg hB
    (fun _ _ _ => Nat.zero_le _))).trans
  exact sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => Nat.zero_le _)

theorem twiceInternal_away (M : MultiGraph (Sum Bool W)) (S : Finset (Sum Bool W))
    (hA : Sum.inl false ∉ S) (hB : Sum.inl true ∉ S) :
    M.twiceInternal S=(ordinary M).twiceInternal (ordinaryVertices S) := by
  have hEq : (ordinaryVertices S).image Sum.inr=S := by
    ext v
    cases v with
    | inl i => cases i <;> simp [hA,hB]
    | inr w => simp [ordinaryVertices]
  conv_lhs => rw [←hEq]
  rw [MultiGraph.twiceInternal,sum_image (fun _ _ _ _ h => Sum.inr.inj h)]
  simp_rw [sum_image (fun _ _ _ _ h => Sum.inr.inj h)]
  rfl

theorem no_overfull_of_ordinary (M : MultiGraph (Sum Bool W)) (m δ D : ℕ)
    (hReg : M.IsRegularOfDegree D) (hCard : Fintype.card W=2*m) (hm : 3 ≤ m)
    (hSimple : ∀ u v, (ordinary M).mult s(u,v) ≤ 1)
    (hMin : ∀ v, δ ≤ (ordinary M).degree v) (hδ : m+2 ≤ δ)
    (hDδ : D+2 ≤ 2*δ) (hDm : D ≤ 3*m)
    (hAway : ∀ T : Finset W, Odd T.card → (ordinary M).twiceInternal T ≤ D*(T.card-1)) :
    ¬M.HasOverfullSubset D := by
  rw [M.noOverfull_iff_odd_cut_bound hReg]
  have hEven : Even (Fintype.card (Sum Bool W)) := by
    rw [Fintype.card_sum,Fintype.card_bool,hCard]
    exact ⟨m+1,by omega⟩
  have hAwayCut : ∀ S : Finset (Sum Bool W), Odd S.card →
      Sum.inl false ∉ S → Sum.inl true ∉ S → D ≤ M.cutSize S := by
    intro S hOdd hA hB
    have hCardS := card_split S
    simp only [if_neg hA,if_neg hB,Nat.add_zero] at hCardS
    have hh := hAway (ordinaryVertices S) (by rwa [←hCardS])
    rw [←twiceInternal_away M S hA hB,←hCardS] at hh
    exact not_lt.mp ((M.odd_overfull_iff_small_cut hReg S hOdd).not.mp (not_lt.mpr hh))
  have hTiny : ∀ S : Finset (Sum Bool W), Odd S.card →
      (ordinaryVertices S).card ≤ 1 → D ≤ M.cutSize S := by
    intro S hOdd hSmall
    by_cases hBoth : Sum.inl false ∈ S ∧ Sum.inl true ∈ S
    · rw [←M.cutSize_compl S]
      exact hAwayCut Sᶜ (MultiGraph.odd_card_compl hEven hOdd)
        (by simpa using hBoth.1) (by simpa using hBoth.2)
    · have hCardS := card_split S
      have hSize : S.card ≤ 2 := by
        by_cases hA : Sum.inl false ∈ S <;> by_cases hB : Sum.inl true ∈ S <;>
          simp only [hA,hB,if_true,if_false] at hCardS <;>
          first | exact (hBoth ⟨hA,hB⟩).elim | omega
      have hOne : S.card=1 := by obtain ⟨k,hk⟩ := hOdd;omega
      obtain ⟨v,hv⟩ := card_eq_one.mp hOne
      rw [hv,CanonicalAdmissibility.cut_singleton,hReg v]
  intro S hOdd
  by_cases hS : (ordinaryVertices S).card ≤ 1
  · exact hTiny S hOdd hS
  by_cases hSc : (ordinaryVertices Sᶜ).card ≤ 1
  · rw [←M.cutSize_compl S]
    exact hTiny Sᶜ (MultiGraph.odd_card_compl hEven hOdd) hSc
  · apply (DenseCoreCutBound.cut_bound (ordinary M) m δ D hCard hm hSimple hMin hδ hDδ hDm
      (ordinaryVertices S) (by omega) ?_).trans (cut_ordinary_le M S)
    rw [←ordinaryVertices_compl]
    omega

end OverfullWork.TwoCentreOrdinaryCore
