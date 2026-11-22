module

public import OverfullWork.CMSCaseTwoResidueBundleReserves
public import OverfullWork.ResidueOccupiedVertexBudget

@[expose] public section


/-! Combine the actual initial rows, the two-stage residue palette
and the robust Hall iteration in CMS Theorem 4.2, Case 2. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph MultiGraph.PartialColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V}
variable {a b w : V} {d m L r t k : ℕ} {η ξ B : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η}

set_option maxHeartbeats 2300000 in
theorem CaseTwoMiddleCopies.exists_factorization_of_residue_budgets
    (copies : CaseTwoMiddleCopies s w) {R Q : M.PartialColouring k}
    (budget : s.InitialRouteBudget R w ξ B) (rows : copies.InitialCrossingRows R ξ)
    (E : Finset V) {h ell n u : ℕ} (run : GoodRouteRun s.part E h ell R Q n u)
    (hReg : M.IsRegularOfDegree d) (ha : a ∈ E) (hb : b ∈ E) (hw : w ∉ s.part)
    (hFactors : ∀ i : Fin k, ∀ v, (Q.colouring.colourGraph i).degree v = 1)
    (hCap : ∀ v, (Q.available.internalPart s.part).degree v ≤ h)
    (hInitialCap : ∀ v, (R.available.internalPart s.part).degree v ≤ h)
    (hCentre : (Q.available.internalPart s.part).degree a = 0)
    (hProtected : (Q.available.internalPart s.part).mult s(b,w) = 0)
    (Λ E₀ occ : ℕ) (κ loss : ℝ) (hΛ : L ≤ Λ)
    (hException : if (exceptionCandidates M a b Λ).card = 1 then
      w ∈ exceptionCandidates M a b Λ else w = b)
    (hq : M.mult s(b,w) ≤ E₀+2)
    (hCompare : ∀ v, v ≠ a → M.mult s(a,v) ≤ M.mult s(a,b)+E₀)
    (hProfile : d ≤ M.supportGraph.degree b+M.mult s(a,b)+E₀)
    (hSupport : ∀ v, v ≠ a → v ≠ b → (d:ℝ)/2-loss ≤ M.supportGraph.degree v)
    (hPair : (M.mult s(a,b):ℝ)+κ*(m:ℝ) ≤ (d:ℝ))
    (hOcc₂ : 2 ≤ occ)
    (hRatio : 2*(Q.available.internalPart s.part).edgeCount+6*h ≤ (3*h)*occ) :
    let F := ⌈5*ξ⌉₊+3*h
    let del := 2+⌈6*ξ⌉₊+h
    let delB := 1+⌈3*ξ⌉₊
    k+F < d →
    (E₀+3)+2*(⌈ξ⌉₊+F)+E₀ ≤ Λ →
    ((k+F:ℕ):ℝ)+(M.mult s(a,b):ℝ)/2+((E₀+3+s.heavyVertices.card:ℕ):ℝ)+2*(Λ:ℝ) < (d:ℝ) →
    η*(m:ℝ)+2*((occ+delB+F:ℕ):ℝ)+2+(E₀:ℝ) ≤ κ*(m:ℝ) →
    ((R.available.crossingSupport s.part).neighborFinset a ⊆ E ∨
      occ+F < (R.available.crossingSupport s.part).degree a) →
    occ+4 ≤ r → del+F < r →
    (t:ℝ)+(loss+η*(m:ℝ))/2+((occ+4+del+F:ℕ):ℝ) ≤ (d:ℝ)/4 →
    ∃ C : M.EdgeColoring d, C.IsFactorization := by
  let F := ⌈5*ξ⌉₊+3*h
  let del := 2+⌈6*ξ⌉₊+h
  let delB := 1+⌈3*ξ⌉₊
  dsimp only
  intro hPalette hLarge hLight hSecond hPick hVertex hDeleted hMin
  obtain ⟨q,hqSize,C,hBalance,hFirst,hSecondMass,hClear,hZero,_hOld,_hCover⟩ :=
    budget.exists_two_stage_residue_palette E hReg run hFactors hCap hCentre
  let f := q+3*h
  have hf : f ≤ F := by
    have hqCeil : q ≤ ⌈5*ξ⌉₊ := by exact_mod_cast hqSize.le.trans (Nat.le_ceil _)
    exact Nat.add_le_add_right hqCeil _
  have hQ (v : V) : Q.graph.degree v = k := by
    rw [←Q.colouring.sum_colour_degree v]
    simp_rw [hFactors]
    simp
  have hRA : R.graph.degree a = k := by
    rw [←R.colouring.sum_colour_degree a]
    have hh := fun i => (budget.anchors i).1
    simp_rw [hh]
    simp
  have hRB : R.graph.degree b = k := by
    rw [←R.colouring.sum_colour_degree b]
    have hh := fun i => (budget.anchors i).2
    simp_rw [hh]
    simp
  have hRows := rows.after_good_run run ha hb hRA hRB
  have hSupportEq := protected_centre_available_neighbours run ha hRA
  have hCrossOrd (v : V) (hva : v ≠ a) (hvb : v ≠ b) :
      (Q.graph.crossingSupport s.part).degree v ≤ del := by
    have hLoss := run.deleted_degree_budget hInitialCap v
    have hOld := budget.ordinary_deleted v hva hvb
    have hMissing : (R.colouring.missingPalette v).card ≤ ⌈6*ξ⌉₊ := by
      exact_mod_cast (budget.vertex_missing v).le.trans (Nat.le_ceil _)
    dsimp only [del]
    omega
  have hOcc (j : Fin f) : (s.part \ C.missingSet s.part j).card ≤ occ := by
    refine Fin.addCases ?_ ?_ j
    · intro i
      rw [C.occupied_card_eq_twice_internal,hFirst]
      simpa using hOcc₂
    · intro i
      have hh := hSecondMass i
      have hPos : 0 < 3*h := by have hi := i.isLt; omega
      rw [C.occupied_card_eq_twice_internal]
      apply Nat.le_of_mul_le_mul_left _ hPos
      nlinarith only [hh,hRatio]
  have hCapPalette : k+f < d := by dsimp only [F] at hf; omega
  refine s.exists_factorization_of_residue_prescriptions Q C occ del loss hReg hCapPalette.le
    hFactors hCrossOrd hSupport hBalance hOcc hVertex (by omega) ?_ ?_
  · change (t:ℝ)+(loss+η*(m:ℝ))/2+((occ+4+del+f:ℕ):ℝ) ≤ (d:ℝ)/4
    change (t:ℝ)+(loss+η*(m:ℝ))/2+((occ+4+del+F:ℕ):ℝ) ≤ (d:ℝ)/4 at hMin
    have hF : (f:ℝ) ≤ (F:ℝ) := by exact_mod_cast hf
    push_cast at hMin ⊢
    linarith only [hF,hMin]
  intro S hMono hCovers j hSame
  let i := Fin.natAdd k j
  have hEq (D : Finset V) : S.colouring.missingSet D i = C.missingSet D j := by
    simp only [i,MultiGraph.EdgeColoring.missingSet,hSame]
  have hOccA : (s.part \ S.colouring.missingSet s.part i).card ≤ occ := by
    rw [hEq]
    exact hOcc j
  have hOccB : (s.partᶜ \ S.colouring.missingSet s.partᶜ i).card ≤ occ := by
    rw [hEq,C.occupied_compl_eq_of_internal_balance _ (hBalance j)]
    exact hOcc j
  have hSecondPay : η*(m:ℝ)+2*((occ+delB+f:ℕ):ℝ)+2+(E₀:ℝ) ≤ κ*(m:ℝ) := by
    have hf' : (f:ℝ) ≤ F := by exact_mod_cast hf
    change η*(m:ℝ)+2*((occ+delB+F:ℕ):ℝ)+2+(E₀:ℝ) ≤ κ*(m:ℝ) at hSecond
    push_cast at hSecond ⊢
    linarith only [hSecond,hf']
  have hSecondReady := s.second_anchor_neighbours Q S i occ delB E₀ κ hMono (hQ b)
    hRows.second hOccA hProfile hPair hSecondPay
  have hMargin : M.mult s(b,w)-M.degreeInto s.part a ≤ E₀+2 := (Nat.sub_le _ _).trans hq
  have hFirstReady : 0 < S.available.degreeInto (S.colouring.missingSet s.partᶜ i) a := by
    dsimp only [i] at hOccB ⊢
    revert hOccB hSame
    refine Fin.addCases ?_ ?_ j
    · intro j hSame _
      let U := (M.mult s(a,b):ℝ)/2+((E₀+3+s.heavyVertices.card:ℕ):ℝ)
      have hUpper : (S.available.mult s(a,b):ℝ) ≤ U := by
        have hNat := hRows.available_second_upper S hMono
        have hNatR : (2:ℝ)*(S.available.mult s(a,b):ℝ) ≤ (M.mult s(a,b):ℝ)+
            2*((M.mult s(b,w)-M.degreeInto s.part a:ℕ):ℝ)+2*(s.heavyVertices.card:ℝ)+2 := by
          exact_mod_cast (show 2*S.available.mult s(a,b) ≤ M.mult s(a,b)+
            2*(M.mult s(b,w)-M.degreeInto s.part a)+2*s.heavyVertices.card+2 by omega)
        have hMarginR : ((M.mult s(b,w)-M.degreeInto s.part a:ℕ):ℝ) ≤ (E₀:ℝ)+2 := by
          exact_mod_cast hMargin
        dsimp only [U]
        push_cast
        linarith only [hNatR,hMarginR]
      have hL : ((k+f:ℕ):ℝ)+U+2*(Λ:ℝ) < (d:ℝ) := by
        have hf' : (f:ℝ) ≤ F := by exact_mod_cast hf
        dsimp only [U]
        change ((k+F:ℕ):ℝ)+(M.mult s(a,b):ℝ)/2+((E₀+3+s.heavyVertices.card:ℕ):ℝ)+2*(Λ:ℝ) < (d:ℝ) at hLight
        push_cast at hLight ⊢
        linarith only [hLight,hf']
      apply s.stage_one_first_anchor Q C S _ Λ U hΛ hReg hCovers hSame
        (by rw [←hBalance]; exact hFirst j) hUpper hL ?_ ?_
      · intro v hva hvb hv
        have hAcross : v ∈ s.partᶜ := mem_compl.mpr (s.heavy_across v hvb (hΛ.trans_lt hv))
        have hV := hRows.available_centre_lower S hMono (hQ a) v hAcross
        have hB' := hRows.available_centre_lower S hMono (hQ a) b (mem_compl.mpr s.second_not_mem)
        have hComp := hCompare v hva
        omega
      · exact s.unique_large_bundle_has_no_residue Q Λ hw hException hProtected
    · intro j hSame hOccB
      apply s.stage_two_first_anchor Q S _ E hReg hCapPalette (hQ a) hCovers hMono
      · intro v he hv
        rw [hSame]
        exact hClear v he hv j
      · rcases hPick with hSmall | hBig
        · exact Or.inl (by rwa [hSupportEq])
        · apply Or.inr
          have hSize := congrArg Finset.card hSupportEq
          rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at hSize
          rw [hSize]
          exact lt_of_le_of_lt (Nat.add_le_add hOccB hf) hBig
  exact S.exists_anchor_prescription i s.part a b s.centre_mem s.second_not_mem
    (by rw [hSame]; exact hZero j) hFirstReady (fun _ => hSecondReady)

end OverfullWork.CMSBalancedCut
