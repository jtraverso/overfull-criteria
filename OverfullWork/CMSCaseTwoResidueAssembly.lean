module

public import OverfullWork.CMSCaseTwoFreshColourHall
public import OverfullWork.ComplementOccupiedBudget
public import OverfullWork.FactorizationAssembly

@[expose] public section


/-! Iterate the fresh-colour Hall step and assemble the final
bipartite remainder as in CMS 4.2, Case 2, Steps 4–5. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph MultiGraph.PartialColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V}
variable {a b : V} {d m L r t k f : ℕ} {η : ℝ}

set_option maxHeartbeats 2000000 in
theorem CaseTwoPartition.exists_factorization_of_residue_prescriptions
    (s : CaseTwoPartition M a b d m L r t η) (Q₀ : M.PartialColouring k)
    (C : (Q₀.available.internalPart s.part).EdgeColoring f)
    (occ del : ℕ) (loss : ℝ) (hReg : M.IsRegularOfDegree d) (hk : k+f ≤ d)
    (hFactors : ∀ i : Fin k, ∀ v, (Q₀.colouring.colourGraph i).degree v = 1)
    (hOrdinary : ∀ v, v ≠ a → v ≠ b → (Q₀.graph.crossingSupport s.part).degree v ≤ del)
    (hSupport : ∀ v, v ≠ a → v ≠ b → (d:ℝ)/2-loss ≤ M.supportGraph.degree v)
    (hBalance : ∀ j, (C.colourGraph j).edgesWithin s.part = (C.colourGraph j).edgesWithin s.partᶜ)
    (hOccupied : ∀ j, (s.part \ C.missingSet s.part j).card ≤ occ)
    (hVertex : occ+4 ≤ r) (hDeleted : del+f < r)
    (hMin : (t:ℝ)+(loss+η*(m:ℝ))/2+((occ+4+del+f:ℕ):ℝ) ≤ (d:ℝ)/4)
    (prescribe : ∀ S : M.PartialColouring (k+f),
      (∀ e, Q₀.graph.mult e ≤ S.graph.mult e) → S.CoversInternal s.part →
      ∀ j : Fin f, S.colouring.colourGraph (Fin.natAdd k j) = C.colourGraph j →
        Nonempty (AnchorPrescription S (Fin.natAdd k j) s.part a b)) :
    ∃ F : M.EdgeColoring d, F.IsFactorization := by
  have hSeed (v : V) : Q₀.graph.degree v = k := by
    rw [←Q₀.colouring.sum_colour_degree v]
    simp_rw [hFactors]
    simp
  have hStages : ∀ t : ℕ, t ≤ f →
      ∃ S : M.PartialColouring (k+f),
        (∀ e, Q₀.graph.mult e ≤ S.graph.mult e) ∧ S.CoversInternal s.part ∧
        (∀ i : Fin k, ∀ v, (S.colouring.colourGraph (Fin.castAdd f i)).degree v=1) ∧
        (∀ j : Fin f, j.val < t → ∀ v, (S.colouring.colourGraph (Fin.natAdd k j)).degree v=1) ∧
        ∀ j : Fin f, t ≤ j.val → S.colouring.colourGraph (Fin.natAdd k j)=C.colourGraph j := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨Q₀.attach_internal_residue s.part C,?_,Q₀.attach_internal_residue_covers s.part C,?_,?_,?_⟩
      · intro e
        change Q₀.graph.mult e ≤ Q₀.graph.mult e+(Q₀.available.internalPart s.part).mult e
        omega
      · intro i v
        rw [Q₀.attach_internal_residue_old_colour]
        exact hFactors i v
      · intro j hj
        omega
      · intro j _
        exact Q₀.attach_internal_residue_fresh_colour s.part C j
    | succ t ih =>
      intro ht
      obtain ⟨S,hMono,hCover,hOld,hDone,hUntreated⟩ := ih (by omega)
      let j : Fin f := ⟨t,by omega⟩
      have hSame := hUntreated j (by dsimp only [j];omega)
      obtain ⟨z⟩ := prescribe S hMono hCover j hSame
      have hBalance' : (S.colouring.colourGraph (Fin.natAdd k j)).edgesWithin s.part =
          (S.colouring.colourGraph (Fin.natAdd k j)).edgesWithin s.partᶜ := by
        rw [hSame]
        exact hBalance j
      have hEq (D : Finset V) :
          S.colouring.missingSet D (Fin.natAdd k j) = C.missingSet D j := by
        simp only [MultiGraph.EdgeColoring.missingSet,hSame]
      obtain ⟨Q,hFull,hOther,hGrowth,_,hInternal⟩ :=
        s.exists_fresh_colour_extension Q₀ S (Fin.natAdd k j) z occ del loss
          hMono hSeed hOrdinary hSupport hBalance' (by rw [hEq]; exact hOccupied j)
          (by rw [hEq,C.occupied_compl_eq_of_internal_balance _ (hBalance j)]; exact hOccupied j)
          hVertex hDeleted hMin
      refine ⟨Q,(fun e => (hMono e).trans (hGrowth e)),?_,?_,?_,?_⟩
      · intro x y hSide
        exact (hInternal x y hSide).trans (hCover x y hSide)
      · intro i v
        have hNe : Fin.castAdd f i ≠ Fin.natAdd k j := by
          intro hh
          have hVal := congrArg Fin.val hh
          change i.val=k+j.val at hVal
          have hi := i.isLt
          omega
        rw [hOther _ hNe]
        exact hOld i v
      · intro u hu v
        by_cases he : u.val=t
        · have huj : u=j := Fin.ext he
          subst u
          exact hFull v
        · have hNe : Fin.natAdd k u ≠ Fin.natAdd k j := by
            intro hh
            have hVal := congrArg Fin.val hh
            change k+u.val=k+t at hVal
            omega
          rw [hOther _ hNe]
          exact hDone u (by omega) v
      · intro u hu
        have hNe : Fin.natAdd k u ≠ Fin.natAdd k j := by
          intro hh
          have hVal := congrArg Fin.val hh
          change k+u.val=k+t at hVal
          omega
        rw [hOther _ hNe]
        exact hUntreated u (by omega)
  obtain ⟨Q,hMono,hCover,hOld,hDone,_⟩ := hStages f (le_refl _)
  have hAll (i : Fin (k+f)) (v : V) : (Q.colouring.colourGraph i).degree v = 1 :=
    Fin.addCases (fun j => hOld j v) (fun j => hDone j j.isLt v) i
  have hRegular (v : V) : Q.graph.degree v = k+f := by
    rw [←Q.colouring.sum_colour_degree v]
    simp_rw [hAll]
    simp
  exact MultiGraph.exists_factorization_of_bipartite_residual M Q.graph s.part d (k+f)
    hk Q.le hReg hRegular ⟨Q.colouring⟩
    (MultiGraph.bipartite_residual_of_internal_cover M Q.graph s.part hCover)

end OverfullWork.CMSBalancedCut
