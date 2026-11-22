module

public import OverfullWork.CaseTwoCompletionScalars
public import OverfullWork.ExtendedSeedCompletionMargins
public import OverfullWork.CanonicalLocalProfileScales
public import OverfullWork.ProtectedResidueBundles

@[expose] public section


/-! # Complete the actual nonheavy Case 2 seed from sparse source budgets

The partition scale fixes the route length before the error and source
scales. Construct the equitable seed, both anchors and the full good run.
All finite completion margins are paid from the original sparse budgets.
The result is the seed 1-factors, not the coloring of the whole candidate.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open scoped Classical
universe u
set_option maxHeartbeats 32000000

theorem exists_uniform_case_two_seed_completion (P : ℕ) (hP : 8 ≤ P) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ell : ℕ, ∃ δ : ℝ, ∃ Qs : ℕ, 0 < δ ∧ P ≤ Qs ∧
      ∀ T : ℕ, 16 ≤ T → 4 ≤ δ*(T:ℝ) → ∀ η : ℝ, 0 ≤ η → η ≤ min (δ/4) (1/32) →
        ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
          (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
          (c : Certificate G B K) (p : Candidate c),
          N ≤ Fintype.card W → Fintype.card W ≤ 2*G.maxDegree →
          B ≤ 6*(Fintype.card W/(4096*Qs^2))+6 → K ≤ Fintype.card W/(4096*Qs^2)+1 →
          p.centre=(0,false) → ∀ b : Fin (p.pairIndex+1) × Bool, b=(0,true) →
          ∀ s : p.CaseTwoPartition P T η b, ∀ w, w ∉ s.part → b ≠ w →
          ∀ r : p.CaseTwoMiddleCopies s w,
            (p.completed.mult s(p.centre,b):ℝ)+ρ*(p.pairIndex+1:ℕ) ≤ G.maxDegree →
            ∃ R Q : p.completed.PartialColouring r.seedPalette, ∃ h n t : ℕ,
              r.InitialRouteBudget R ∧
              MultiGraph.PartialColouring.GoodRouteRun s.part s.completionExceptions h ell R Q n t ∧
              (∀ i v, (Q.colouring.colourGraph i).degree v=1) ∧
              (∀ v, (Q.available.internalPart s.part).degree v ≤ h) ∧
              (Q.available.internalPart s.part).degree p.centre=0 ∧
              (Q.available.internalPart s.part).mult s(b,w)=0 ∧
              ((Q.available.internalPart s.part).edgeCount:ℝ) <
                r.seedError*(5+(ell:ℝ)*(p.pairIndex+2:ℕ)) ∧
              ∀ v ∈ s.completionExceptions,
                (Q.available.internalPart s.part).degree v=(R.available.internalPart s.part).degree v := by
  obtain ⟨ell,δ₀,hδ₀,hScalars⟩ := exists_case_two_completion_scalars P hP
  let δ := min δ₀ (ρ/8)
  have hδ : 0 < δ := by dsimp only [δ];positivity
  have hδ₀le : δ ≤ δ₀ := min_le_left _ _
  have hδρ : δ ≤ ρ/8 := min_le_right _ _
  let Q₀ := max P 128
  obtain ⟨Qs,hQs,hSource⟩ := exists_uniform_seed_error_scale δ hδ Q₀ (by dsimp only [Q₀];omega)
  have hPQ : P ≤ Qs := (le_max_left _ _).trans hQs
  have hQ128 : 128 ≤ Qs := (le_max_right _ _).trans hQs
  refine ⟨ell,δ,Qs,hδ,hPQ,?_⟩
  intro T hT hTδ η hη₀ hη
  have hηδ := hη.trans (min_le_left _ _)
  have hη32 := hη.trans (min_le_right _ _)
  obtain ⟨N₀,hN₀⟩ := hScalars T
  obtain ⟨N₁,hN₁⟩ := hSource T hTδ η hηδ
  let M := max N₀ (64*(T+2))
  let N := max N₁ (max (3*M) (64*Qs))
  refine ⟨N,?_⟩
  intro W _ _ G _ B K c p hn hWeak hB hK hCentre b hSecond s w hw hbw r hNonheavy
  let m := p.pairIndex+1
  let Y := c.setᶜ.card
  let n₀ := Fintype.card W
  have hn₁ : N₁ ≤ n₀ := (le_max_left _ _).trans hn
  have hnM : 3*M ≤ n₀ := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnQs : 64*Qs ≤ n₀ := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hY : Y ≤ n₀/(4096*Qs^2)+1 := c.complement_small.trans hK
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts := card_add_card_compl c.set
  have hCard : n₀+1=2*m+Y := by dsimp only [n₀,m,Y];omega
  have hnm := source_half_order_bound Qs n₀ m Y (by omega) hCard hY
  have hMm : M ≤ m := by omega
  have hmN : N₀ ≤ m := (le_max_left _ _).trans hMm
  have hmT : 64*(T+2) ≤ m := (le_max_right _ _).trans hMm
  have hLossNat := p.local_profile_loss_at_source_scale Qs (by omega) hnQs hB hK
  change Qs*(B+Y) ≤ 2*m at hLossNat
  have hLoss128 : 128*(B+Y) ≤ 2*m := (Nat.mul_le_mul_right _ hQ128).trans hLossNat
  have hB64 : 64*B ≤ m := by omega
  have hLoss32 : 32*(B+Y) ≤ m := by omega
  have hLoss32R : (32:ℝ)*((B+Y:ℕ):ℝ) ≤ m := by exact_mod_cast hLoss32
  have hEtaM := mul_le_mul_of_nonneg_right hη32 (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  have hLoss : ((B+Y:ℕ):ℝ)+η*(m:ℝ) ≤ (m:ℝ)/16 := by linarith
  have hError : r.seedError ≤ δ*(m:ℝ) := hN₁ n₀ m Y B hn₁ hCard hY hB
  have hError₀ : 0 ≤ r.seedError := by
    dsimp only [Candidate.CaseTwoMiddleCopies.seedError]
    positivity
  have hSmall : r.seedError ≤ δ₀*(m:ℝ) := hError.trans
    (mul_le_mul_of_nonneg_right hδ₀le (Nat.cast_nonneg m : (0:ℝ) ≤ m))
  obtain ⟨sc⟩ := hN₀ m hmN r.seedError hError₀ hSmall
  have hHalf := p.image_half_order_le_delta hWeak
  have hImage := p.maxDegree_lt_image_order_at_source_scale Qs (by omega) hnQs hB hK
  have hD : G.maxDegree ≤ 3*m := by change G.maxDegree < 2*m at hImage;omega
  have hPalette : r.seedPalette ≤ G.maxDegree := (r.palette_lt_maxDegree_of_reserves hT
    (by linarith) hmT hB64 (by change m ≤ G.maxDegree at hHalf;omega)).le
  have hGap : (p.completed.mult s(p.centre,b):ℝ)+(B:ℝ)+η*(m:ℝ)+6*r.seedError+4 ≤ G.maxDegree := by
    have hρM := mul_le_mul_of_nonneg_right hδρ (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    have hSeed : (B:ℝ)+η*(m:ℝ)+4 ≤ r.seedError := by
      dsimp only [Candidate.CaseTwoMiddleCopies.seedError]
      have hb₀ : (0:ℝ) ≤ B := Nat.cast_nonneg _
      have ht₀ : (0:ℝ) ≤ T := Nat.cast_nonneg _
      have hdiv₀ : (0:ℝ) ≤ (m/T:ℕ) := Nat.cast_nonneg _
      change (B:ℝ)+η*(m:ℝ)+4 ≤ η*(m:ℝ)+4*(B:ℝ)+(m/T:ℕ)+6*(T:ℝ)+9
      linarith
    have hρm₀ : 0 ≤ ρ*(m:ℝ) := by positivity
    change (p.completed.mult s(p.centre,b):ℝ)+ρ*(m:ℝ) ≤ G.maxDegree at hNonheavy
    nlinarith only [hError,hρM,hSeed,hNonheavy,hρm₀]
  obtain ⟨C,hC⟩ := r.exists_equitable_seed hw hD (by omega)
  obtain ⟨R,budget,hOrdinary,hCentreZero,hBundle⟩ := r.exists_initial_route_budget_with_ordinary_degree hw hbw hD
    (by omega) hHalf C hC hPalette hGap
  have hForb : ((ell:ℝ)+1)*(6*r.seedError+2)+12*(T:ℝ)+8+
      4*r.seedError*(5+(ell:ℝ)*(p.pairIndex+2:ℕ))/(sc.h:ℝ) ≤ (sc.Wbar:ℝ) := by
    convert sc.forbidden using 1 <;> dsimp only [m] <;> push_cast <;> ring
  have hSafeCentre : p.centre ∈ s.completionExceptions := by
    simp [Candidate.CaseTwoPartition.completionExceptions,Candidate.CaseTwoPartition.initialExceptions]
  have hSafeSecond : b ∈ s.completionExceptions := by
    simp [Candidate.CaseTwoPartition.completionExceptions,Candidate.CaseTwoPartition.initialExceptions]
  have pay := budget.seed_completion_margins_for_exceptions hOrdinary s.completionExceptions
    hSafeCentre hSafeSecond (s.completionExceptions_card hD (by omega)) hCentre hSecond hHalf sc.h ell sc.g sc.q sc.Wbar
    sc.cap_pos sc.gain_pos sc.cap hLoss hForb sc.forbidden_margin sc.deletion_margin
    sc.seed_window sc.gain sc.rounds sc.reserve sc.predecessors
  obtain ⟨Q,n,t,run,hFactors⟩ := MultiGraph.PartialColouring.exists_completed_good_run R s.part
    s.completionExceptions sc.h ell pay
  have hBundleZero : (R.available.internalPart s.part).mult s(b,w)=0 := by
    rw [MultiGraph.internalPart_mult,if_pos (show b ∈ s.part ↔ w ∈ s.part by
      have hb := s.second_not_mem
      tauto)]
    change p.completed.mult s(b,w)-R.graph.mult s(b,w)=0
    rw [hBundle,Nat.sub_self]
  have hCurrent : ((Q.available.internalPart s.part).edgeCount:ℝ) ≤
      (R.available.internalPart s.part).edgeCount+(ell:ℝ)*((∑ v, (R.colouring.missingPalette v).card)/2:ℕ) := by
    exact_mod_cast run.residue_size_budget
  have hResidue := hCurrent.trans_lt (budget.initial_potential_bound ell)
  exact ⟨R,Q,sc.h,n,t,budget,run,hFactors,run.residue_cap pay.residue_cap,
    (run.protected_rows p.centre hSafeCentre).trans hCentreZero,
    (run.protected_internal_bundle b hSafeSecond w).trans hBundleZero,hResidue,
    fun v hv => run.protected_rows v hv⟩

end OverfullWork.NormalizedCanonicalCandidate
