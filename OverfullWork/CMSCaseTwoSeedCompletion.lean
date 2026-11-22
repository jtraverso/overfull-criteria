module

public import OverfullWork.CMSCaseTwoInitialRouteBudgets
public import OverfullWork.RobustSeedCompletion
public import OverfullWork.ProtectedResidueBundles

@[expose] public section


/-! Pass the actual initial colouring to the good-path iteration of
CMS Step 3. The scalar hypotheses are finite reserve inequalities. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph MultiGraph.PartialColouring
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V}
variable {a b w : V} {d m L r t k : ℕ} {η ξ B : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η} {R : M.PartialColouring k}

set_option maxHeartbeats 1500000 in
theorem CaseTwoPartition.InitialRouteBudget.exists_completed_seed
    (budget : s.InitialRouteBudget R w ξ B) (E : Finset V) (ha : a ∈ E) (hb : b ∈ E)
    (h ell g q Wbar : ℕ) (loss : ℝ)
    (hSupport : ∀ v, v ≠ a → v ≠ b → (d:ℝ)/2-loss ≤ M.supportGraph.degree v)
    (hCap : 5*ξ ≤ (h:ℝ)) (hCard : Fintype.card V = 2*m) (hWindow : 2*t ≤ m)
    (hPos : 0 < h) (hg : 0 < g)
    (hBoot : (t:ℝ)+(loss+η*(m:ℝ))/2+(Wbar:ℝ)+((2+⌈6*ξ⌉₊+h:ℕ):ℝ) ≤ (d:ℝ)/4)
    (hForb : 4+((ell:ℝ)+1)*(B+2*ξ)+2*(E.card:ℝ)+
        4*ξ*(5+6*(ell:ℝ)*(m:ℝ))/(h:ℝ) ≤ (Wbar:ℝ))
    (hGain : Wbar+g ≤ r) (hRounds : m/g+3 ≤ ell)
    (hReserve : 4+2*ell < q) (hPred : q ≤ r-(2+⌈6*ξ⌉₊+h)) :
    ∃ Q : M.PartialColouring k, ∃ n u : ℕ,
      GoodRouteRun s.part E h ell R Q n u ∧
      (∀ i : Fin k, ∀ v, (Q.colouring.colourGraph i).degree v = 1) ∧
      (∀ v, (Q.available.internalPart s.part).degree v ≤ h) ∧
      (Q.available.internalPart s.part).degree a = 0 ∧
      (Q.available.internalPart s.part).mult s(b,w) = 0 ∧
      ((Q.available.internalPart s.part).edgeCount:ℝ) < ξ*(5+6*(ell:ℝ)*(m:ℝ)) := by
  have hResCap (v : V) : (R.available.internalPart s.part).degree v ≤ h := by
    have hDegree : (R.available.internalPart s.part).degree v ≤
        (R.available.internalPart s.part).edgeCount :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    have hEdges : (R.available.internalPart s.part).edgeCount ≤ h := by
      exact_mod_cast (budget.residue.le.trans hCap)
    exact hDegree.trans hEdges
  have hNat := Nat.mul_div_le (∑ v, (R.colouring.missingPalette v).card) 2
  have hRoundR :
      2*(((∑ v, (R.colouring.missingPalette v).card)/2:ℕ):ℝ) ≤
      ∑ v, ((R.colouring.missingPalette v).card:ℝ) := by exact_mod_cast hNat
  have hN : (Fintype.card V:ℝ) = 2*(m:ℝ) := by exact_mod_cast hCard
  have hRoute : (((∑ v, (R.colouring.missingPalette v).card)/2:ℕ):ℝ) ≤ 6*(m:ℝ)*ξ := by
    have hTotal := budget.total_missing
    rw [hN] at hTotal
    nlinarith only [hRoundR,hTotal]
  have hPotential : ((R.available.internalPart s.part).edgeCount:ℝ)+
      (ell:ℝ)*(((∑ v, (R.colouring.missingPalette v).card)/2:ℕ):ℝ) <
        ξ*(5+6*(ell:ℝ)*(m:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hRoute (Nat.cast_nonneg (α := ℝ) ell)
    nlinarith only [hh,budget.residue]
  let B₀ := ⌈6*ξ⌉₊
  have pay : RelativeSeedCompletionMargins R s.part E h ell m d r t B₀ g q Wbar loss (η*(m:ℝ)) a b := by
    refine {
      card_part := s.card_part
      card_compl := s.card_compl
      robust := s.robust
      residue_cap := hResCap
      ordinary_deleted := budget.ordinary_deleted
      first_exception := ha
      second_exception := hb
      missing := fun v => ?_
      anchors := fun i => ?_
      ordinary_support := hSupport
      discrepancy := s.simple_discrepancy
      bootstrap_margin := hBoot
      window := hWindow
      positive_cap := hPos
      positive_gain := hg
      gain := hGain
      rounds := hRounds
      reserve := hReserve
      predecessors := hPred
      forbidden_initial := ?_
    }
    · exact_mod_cast (budget.vertex_missing v).le.trans (Nat.le_ceil (6*ξ))
    · rw [(budget.anchors i).1,(budget.anchors i).2]
      simp
    · intro i
      have hCut : ((R.colouring.colourGraph i).cutSize s.part:ℝ) ≤ 2 := by exact_mod_cast budget.colour_cut i
      have hCol := mul_le_mul_of_nonneg_left (budget.colour_missing i)
        (show 0 ≤ (ell:ℝ)+1 by positivity)
      have hBase : 2*((R.colouring.colourGraph i).cutSize s.part:ℝ)+
          ((ell:ℝ)+1)*((R.colouring.missingSet univ i).card:ℝ)+2*(E.card:ℝ) ≤
          4+((ell:ℝ)+1)*(B+2*ξ)+2*(E.card:ℝ) := by nlinarith only [hCut,hCol]
      have hWeighted := mul_le_mul_of_nonneg_left hBase (Nat.cast_nonneg (α := ℝ) h)
      have hh := mul_le_mul_of_nonneg_right hForb (Nat.cast_nonneg (α := ℝ) h)
      have hH : (0:ℝ) < h := by exact_mod_cast hPos
      rw [add_mul,div_mul_cancel₀ _ hH.ne'] at hh
      apply (Nat.cast_le (α := ℝ)).mp
      push_cast
      nlinarith only [hWeighted,hh,hPotential]
  obtain ⟨Q,n,u,hRun,hFactors⟩ := exists_completed_good_run_of_relative_margins R s.part E h ell pay
  have hSize : ((Q.available.internalPart s.part).edgeCount:ℝ) ≤
      (R.available.internalPart s.part).edgeCount+(ell:ℝ)*(((∑ v, (R.colouring.missingPalette v).card)/2:ℕ):ℝ) := by
    exact_mod_cast hRun.residue_size_budget
  exact ⟨Q,n,u,hRun,hFactors,hRun.residue_cap hResCap,
    (hRun.protected_rows a ha).trans budget.centre_residue,
    (hRun.protected_internal_bundle b hb w).trans budget.protected_residue,hSize.trans_lt hPotential⟩

end OverfullWork.CMSBalancedCut
