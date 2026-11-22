module

public import OverfullWork.ExceptionalArcScheduling
public import OverfullWork.KuhnOsthusOriginalParityRound
public import OverfullWork.KuhnOsthusResidualPreprocessing

@[expose] public section


/-! The last deletion and absorption stages in the proof of
Kühn–Osthus Theorem 1.2, once the two reserves have been prepared. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

/-- The robust neighbourhood loses at most the maximum indegree of
the deleted arcs in its threshold. -/
theorem IsRealRobust.after_indegree_deletion {G H : Digraph V} {ν μ τ : ℝ}
    (hG : IsRealRobust G ν τ) (hμν : μ ≤ ν)
    (hBudget : ∀ v, (inDegree H v : ℝ) ≤ (ν-μ)*(Fintype.card V:ℝ)) :
    IsRealRobust (G \ H) μ τ := by
  intro S hLow hHigh
  have hSub : realNeighbourhood G ν S ⊆ realNeighbourhood (G \ H) μ S := by
    intro v hv
    have hCount : inNeighbours G S v ≤ inNeighbours (G \ H) S v + inDegree H v := by
      let A := S.filter (fun x => (G \ H).Adj x v)
      let B := (univ : Finset V).filter (fun x => H.Adj x v)
      have hSet : S.filter (fun x => G.Adj x v) ⊆ A ∪ B := by
        intro x hx
        obtain ⟨hx,hGx⟩ := mem_filter.mp hx
        exact mem_union.mpr (by
          by_cases h : H.Adj x v
          · exact .inr (mem_filter.mpr ⟨mem_univ _,h⟩)
          · exact .inl (mem_filter.mpr ⟨hx,hGx,h⟩))
      have hEq (D : Digraph V) (T : Finset V) :
          inNeighbours D T v = (T.filter (fun x => D.Adj x v)).card := by
        unfold inNeighbours
        congr 1
      have hA : A.card = inNeighbours (G \ H) S v := by
        rw [hEq]
        congr 1
        ext x
        simp only [A,mem_filter]
      have hB : B.card = inDegree H v := by
        rw [inDegree,hEq]
      rw [hEq,← hA,← hB]
      exact (card_le_card hSet).trans (card_union_le A B)
    have hCount' : (inNeighbours G S v:ℝ) ≤
        (inNeighbours (G \ H) S v:ℝ)+(inDegree H v:ℝ) := by exact_mod_cast hCount
    have hh := (mem_filter.mp hv).2
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    linarith only [hh,hCount',hBudget v]
  have hCard : ((realNeighbourhood G ν S).card:ℝ) ≤
      ((realNeighbourhood (G \ H) μ S).card:ℝ) := by exact_mod_cast card_le_card hSub
  have hLoss := mul_le_mul_of_nonneg_right hμν (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
  linarith only [hG S hLow hHigh,hCard,hLoss]

/-- The degree formulas of (8.3), (11.1) and (11.2) make the union of
the two reserves regular. The equality on s records the chord residue. -/
theorem kuhn_osthus_balanced_absorption_reserve (P B : Digraph V) (Z : Finset V)
    (a d r₁ r₂ r₃ q s : ℕ) (hq : 0 < q)
    (hs : (q-1)*r₃+s = r₁+r₂+d)
    (hApart : Disjoint P B)
    (hP : ∀ v, let k := if v ∈ Z then a else a+d
      inDegree P v = k ∧ outDegree P v = k)
    (hB : ∀ v, let k := if v ∈ Z then q*r₃+7*s else r₁+r₂+r₃+6*s
      inDegree B v = k ∧ outDegree B v = k) :
    ∀ v, inDegree (P ⊔ B) v = a+d+r₁+r₂+r₃+6*s ∧
      outDegree (P ⊔ B) v = a+d+r₁+r₂+r₃+6*s := by
  intro v
  obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint P B (disjoint_iff_inf_le.mp hApart) v
  rw [hi,ho,(hP v).1,(hP v).2,(hB v).1,(hB v).2]
  by_cases hv : v ∈ Z
  · have hq' : q = (q-1)+1 := by omega
    have he : q*r₃ = (q-1)*r₃+r₃ := by
      rw [← Nat.add_one_mul,← hq']
    simp only [if_pos hv]
    omega
  · simp only [if_neg hv]
    omega

omit [Fintype V] in
private theorem exact_digraph_cut (A C : Digraph V) (hC : C ≤ A) :
    C ⊔ (A \ C) = A := by
  ext x y
  simp only [Digraph.sup_adj,Digraph.sdiff_adj]
  have h : C.Adj x y → A.Adj x y := fun he => hC he
  tauto

omit [Fintype V] in
private theorem join_hamilton_packs {s t : ℕ} (F : Fin s → Equiv.Perm V) (G : Fin t → Equiv.Perm V)
    (hF : ∀ i, HasSpanningCycle (fun x y => F i x = y))
    (hG : ∀ i, HasSpanningCycle (fun x y => G i x = y))
    (hDF : ∀ i j, i ≠ j → ∀ x, F i x ≠ F j x)
    (hDG : ∀ i j, i ≠ j → ∀ x, G i x ≠ G j x)
    (hApart : Disjoint (matchingUnion F) (matchingUnion G)) :
    ∃ C : Fin (s+t) → Equiv.Perm V,
      matchingUnion C = matchingUnion F ⊔ matchingUnion G ∧
      (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧
      ∀ i j, i ≠ j → ∀ x, C i x ≠ C j x := by
  obtain ⟨hUnion,hD⟩ := matchingUnion_addCases_of_disjoint F G hDF hDG hApart
  refine ⟨fun i => Fin.addCases F G i,hUnion,?_,hD⟩
  intro i
  cases i using Fin.addCases with
  | left j => simpa only [Fin.addCases_left] using hF j
  | right j => simpa only [Fin.addCases_right] using hG j

/-- Execute the end of the proof of Theorem 1.2 with the
preprocessing and robust reserves supplied. The approximate pack
is required only in the regular robust graph left after Lemma 11.1. -/
theorem kuhn_osthus_final_assembly_from_reserves (ν τ α : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hντ : ν ≤ τ) (hτα : 128*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [Nonempty W]
      (G P B : Digraph W) (Z : Finset W) (r b r₀ t : ℕ),
      N ≤ Fintype.card W →
      (∀ v, ¬ G.Adj v v) → (∀ v, inDegree G v = r ∧ outDegree G v = r) →
      IsRealRobust G ν τ → P ⊔ B ≤ G → Disjoint P B →
      (∀ v, inDegree (P ⊔ B) v = b ∧ outDegree (P ⊔ B) v = b) →
      8*(Z.card:ℝ) ≤ (ν/2)*(Fintype.card W:ℝ)/2 →
      (Z.card:ℝ) ≤ ((ν/2)/2)^4*(Fintype.card W:ℝ) →
      b+4*Z.card+r₀ ≤ r →
      ((b+4*Z.card:ℕ):ℝ) ≤ (ν/2)*(Fintype.card W:ℝ) →
      α*(Fintype.card W:ℝ)+((b+4*Z.card:ℕ):ℝ) ≤ r →
      (∀ D : Digraph W, D ≤ G → IsRealRobust D (ν/2) τ →
        (∀ v, inDegree D v = r-b-4*Z.card ∧ outDegree D v = r-b-4*Z.card) →
        α*(Fintype.card W:ℝ) ≤ ((r-b-4*Z.card:ℕ):ℝ) →
        ∃ F : Fin (r-b-4*Z.card-r₀) → Equiv.Perm W, matchingUnion F ≤ D ∧
          (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
          ∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) →
      (∀ D : Digraph W, D ≤ G \ (P ⊔ B) →
        (∀ v, inDegree D v = r₀ ∧ outDegree D v = r₀) →
        (∀ x y, x ∈ Z → y ∈ Z → ¬ D.Adj x y) →
        ∃ (s : ℕ) (F : Fin s → Equiv.Perm W), matchingUnion F ≤ P ⊔ D ∧
          (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
          (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
          let H := (P ⊔ D) \ matchingUnion F
          (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
          (∀ v : ↥Zᶜ, inDegree (InducedDigraphSampling.induced H Zᶜ) v = t ∧
            outDegree (InducedDigraphSampling.induced H Zᶜ) v = t)) →
      (∀ H : Digraph W, H ≤ G \ B → (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) →
        (∀ v : ↥Zᶜ, inDegree (InducedDigraphSampling.induced H Zᶜ) v = t ∧
          outDegree (InducedDigraphSampling.induced H Zᶜ) v = t) →
        ∃ (s : ℕ) (F : Fin s → Equiv.Perm W), matchingUnion F = H ⊔ B ∧
          (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
          ∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) →
      Nonempty (DirectedHamiltonDecomposition G r) := by
  obtain ⟨N,hN⟩ := exists_hamilton_pack_covering_exceptional_set.{u} (ν/2) τ α (by linarith)
    (by linarith only [hν1]) (by linarith) hτα hα
  refine ⟨N,?_⟩
  intro W _ _ G P B Z r b r₀ t hNW hLoop hReg hRob hRes hPB hResDeg hEx hSize hRoom hBudget hDense
    hApprox hProcess hAbsorb
  let G₄ := G \ (P ⊔ B)
  have hG₄ (v : W) : inDegree G₄ v = r-b ∧ outDegree G₄ v = r-b := by
    obtain ⟨hi,ho⟩ := residual_semidegrees G (P ⊔ B) hRes v
    rw [(hReg v).1,(hResDeg v).1] at hi
    rw [(hReg v).2,(hResDeg v).2] at ho
    exact ⟨by dsimp [G₄]; omega,by dsimp [G₄]; omega⟩
  have hRob₄ : IsRealRobust G₄ (ν/2) τ :=
    hRob.after_indegree_deletion (by linarith) (fun v => by
      rw [(hResDeg v).1]
      push_cast at hBudget
      linarith only [hBudget,show (0:ℝ) ≤ Z.card from Nat.cast_nonneg _])
  have hDense' : α*(Fintype.card W:ℝ) ≤ ((r-b-4*Z.card:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    push_cast at hDense ⊢
    linarith only [hDense]
  have hDense₄ : α*(Fintype.card W:ℝ) ≤ ((r-b:ℕ):ℝ) :=
    hDense'.trans (by exact_mod_cast Nat.sub_le (r-b) (4*Z.card))
  obtain ⟨C₄,hAdj₄,hCycle₄,hDis₄,hZ⟩ := hN G₄ Z hNW hRob₄
    (fun v => (hG₄ v).1.symm ▸ hDense₄)
    (fun v => (hG₄ v).2.symm ▸ hDense₄)
    hEx hSize (fun v _ h => hLoop v h.1)
  have hLe₄ : matchingUnion C₄ ≤ G₄ := by rintro x y ⟨i,rfl⟩; exact hAdj₄ i x
  let G' := G₄ \ matchingUnion C₄
  have hReg' (v : W) : inDegree G' v = r-b-4*Z.card ∧ outDegree G' v = r-b-4*Z.card :=
    regular_residue_of_spanning_pack G₄ (r-b) C₄ hG₄ hAdj₄ hDis₄ v
  have hDelete : G' = G \ ((P ⊔ B) ⊔ matchingUnion C₄) := by
    ext x y
    change ((G.Adj x y ∧ ¬ (P ⊔ B).Adj x y) ∧ ¬ (matchingUnion C₄).Adj x y) ↔
      G.Adj x y ∧ ¬ ((P ⊔ B).Adj x y ∨ (matchingUnion C₄).Adj x y)
    tauto
  have hRob' : IsRealRobust G' (ν/2) τ := by
    rw [hDelete]
    apply hRob.after_indegree_deletion (by linarith)
    intro v
    have hDisj (x y : W) (h : (P ⊔ B).Adj x y ∧ (matchingUnion C₄).Adj x y) : False :=
      (hLe₄ h.2).2 h.1
    obtain ⟨_,hi⟩ := degrees_sup_of_disjoint _ _ hDisj v
    rw [hi,(hResDeg v).1,(matchingUnion_exact_semidegrees C₄ hDis₄ v).1]
    linarith only [hBudget]
  obtain ⟨C',hLe',hCycle',hDis'⟩ := hApprox G' (fun _ _ h => h.1.1) hRob' hReg' hDense'
  let D := G' \ matchingUnion C'
  have hD : D ≤ G₄ := fun _ _ h => h.1.1
  have hRegD (v : W) : inDegree D v = r₀ ∧ outDegree D v = r₀ := by
    have h := regular_residue_of_spanning_pack G' (r-b-4*Z.card) C' hReg'
      (fun i x => hLe' ⟨i,rfl⟩) hDis' v
    have he : (r-b-4*Z.card)-(r-b-4*Z.card-r₀) = r₀ := by omega
    rwa [he] at h
  have hIndD (x y : W) (hx : x ∈ Z) (hy : y ∈ Z) (h : D.Adj x y) : False := by
    obtain ⟨i,hi⟩ := hZ x hx y hy (hD h)
    exact h.1.2 ⟨i,hi⟩
  obtain ⟨s,C₀,hLe₀,hCycle₀,hDis₀,hOrd₀,hReg₀⟩ := hProcess D hD hRegD hIndD
  let H := (P ⊔ D) \ matchingUnion C₀
  have hHB : H ≤ G \ B := by
    rintro x y ⟨hp | hd,_⟩
    · exact ⟨hRes (.inl hp),fun hb => disjoint_iff_inf_le.mp hPB ⟨hp,hb⟩⟩
    · exact ⟨(hD hd).1,fun hb => (hD hd).2 (.inr hb)⟩
  obtain ⟨n,C₁,hC₁,hCycle₁,hDis₁⟩ := hAbsorb H hHB hOrd₀ hReg₀
  have h01 : Disjoint (matchingUnion C₀) (matchingUnion C₁) := by
    rw [hC₁,disjoint_iff_inf_le]
    rintro x y ⟨h₀,h₁⟩
    rcases h₁ with hh | hb
    · exact hh.2 h₀
    · rcases hLe₀ h₀ with hp | hd
      · exact disjoint_iff_inf_le.mp hPB ⟨hp,hb⟩
      · exact (hD hd).2 (.inr hb)
  obtain ⟨Cₐ,hCₐ,hCycleₐ,hDisₐ⟩ := join_hamilton_packs C₀ C₁ hCycle₀ hCycle₁ hDis₀ hDis₁ h01
  have hCₐ' : matchingUnion Cₐ = (P ⊔ B) ⊔ D := by
    rw [hCₐ,hC₁,← sup_assoc,exact_digraph_cut (P ⊔ D) _ hLe₀]
    ac_rfl
  have h4' : Disjoint (matchingUnion C₄) (matchingUnion C') := by
    rw [disjoint_iff_inf_le]
    rintro x y ⟨h₄,h'⟩
    exact (hLe' h').2 h₄
  obtain ⟨Cₚ,hCₚ,hCycleₚ,hDisₚ⟩ := join_hamilton_packs C₄ C' hCycle₄ hCycle' hDis₄ hDis' h4'
  have hCₚD : matchingUnion Cₚ ⊔ D = G₄ := by
    rw [hCₚ,sup_assoc,exact_digraph_cut G' _ hLe']
    exact exact_digraph_cut G₄ _ hLe₄
  have hMix : Disjoint (matchingUnion Cₚ) (matchingUnion Cₐ) := by
    rw [hCₚ,hCₐ',disjoint_iff_inf_le]
    rintro x y ⟨hₚ,hₐ⟩
    rcases hₚ with h₄ | h' <;> rcases hₐ with hR | hD
    · exact (hLe₄ h₄).2 hR
    · exact hD.1.2 h₄
    · exact (hLe' h').1.2 hR
    · exact hD.2 h'
  obtain ⟨F,hF,hCycleF,hDisF⟩ := join_hamilton_packs Cₚ Cₐ hCycleₚ hCycleₐ hDisₚ hDisₐ hMix
  have hUnion : matchingUnion F = G := by
    calc
      matchingUnion F = (P ⊔ B) ⊔ (matchingUnion Cₚ ⊔ D) := by rw [hF,hCₐ']; ac_rfl
      _ = (P ⊔ B) ⊔ G₄ := by rw [hCₚD]
      _ = G := exact_digraph_cut G _ hRes
  let v : W := Classical.choice inferInstance
  have he := (matchingUnion_exact_semidegrees F hDisF v).2
  rw [hUnion,(hReg v).2] at he
  rw [he]
  exact ⟨hamilton_decomposition_of_full_pack _ _ F (fun v => (hReg v).2.trans he)
    (fun i x => hUnion ▸ (show (matchingUnion F).Adj x (F i x) from ⟨i,rfl⟩)) hDisF hCycleF⟩

/-- The physical extender from Corollary 8.5 supplies the preprocessing
step of the final assembly for every possible regular leftover. -/
theorem kuhn_osthus_process_leftover_from_residual_extender
    {r l t : ℕ} {label : V → Fin 50} {Z : Finset V}
    (G P B R : Digraph V) (C : Fin r → OriginalExceptionalFactor label Z l)
    (hLoop : ∀ v, ¬ G.Adj v v)
    (hRegP : ∀ v, let a := if v ∈ Z then r*(50*l+1) else r*(50*l+1)+t
      inDegree P v+r = a ∧ outDegree P v+r = a)
    (hCSub : ∀ j, (C j).digraph ≤ P)
    (hRSub : R ≤ P)
    (hDisRC : ∀ j, Disjoint (C j).digraph R)
    (hDisC : ∀ i j, i ≠ j → Disjoint (C i).digraph (C j).digraph)
    (hL : 2452 ≤ (50*l)/1226)
    (hN : 50*l+1 ≤ Fintype.card V)
    (hZ : 2 * (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / (50*l+1))
    (hExtend : HasBoundedPathExtension (InducedDigraphSampling.induced R Zᶜ) (fun v => label v.val)
      ⌊1230 * (Fintype.card V : ℝ) / (50*l+1)⌋₊ (r*(50*l+1))) :
    ∀ D : Digraph V, D ≤ G \ (P ⊔ B) →
      (∀ v, inDegree D v = r ∧ outDegree D v = r) →
      (∀ x y, x ∈ Z → y ∈ Z → ¬ D.Adj x y) →
      ∃ (s : ℕ) (F : Fin s → Equiv.Perm V), matchingUnion F ≤ P ⊔ D ∧
        (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
        (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
        let H := (P ⊔ D) \ matchingUnion F
        (∀ x y, H.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
        (∀ v : ↥Zᶜ, inDegree (InducedDigraphSampling.induced H Zᶜ) v = t ∧
          outDegree (InducedDigraphSampling.induced H Zᶜ) v = t) := by
  intro D hD hRegD hInd
  have hPD : Disjoint P D := by
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hp,hd⟩
    exact (hD hd).2 (.inl hp)
  obtain ⟨F,hCycle,hDis,_,hLe,hSupport,hReg⟩ := kuhn_osthus_preprocessing_of_residual_extender
    P D R C hRegD hRegP (fun v h => hLoop v (hD h).1) hInd hPD
    hCSub hRSub hDisRC hDisC hL hN hZ hExtend
  exact ⟨_,F,hLe,hCycle,hDis,hSupport,hReg⟩

end OverfullWork.DirectedRobustExpansion
