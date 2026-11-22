module

public import OverfullWork.UniformHallCompletionData
public import OverfullWork.HallRateBounds

@[expose] public section


/-! Source-paid vertex, crossing-edge and minimum-degree losses after prescriptions. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun PrunedCore
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T ell : ℕ} {η ρ : ℝ} {b : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoHallCompletion.occupied_after_prescription
    (a : p.CaseTwoHallCompletion s ell ρ)
    (S : p.completed.PartialColouring (a.middle.seedPalette+(a.fresh+3*a.cap)))
    (j : Fin (a.fresh+3*a.cap))
    (hSame : S.colouring.colourGraph (Fin.natAdd a.middle.seedPalette j)=a.palette.colourGraph j)
    (z : MultiGraph.PartialColouring.AnchorPrescription S (Fin.natAdd a.middle.seedPalette j) s.part p.centre b)
    (D : Finset (Fin (p.pairIndex+1) × Bool)) (hD : D=s.part ∨ D=s.partᶜ) :
    ((D\z.result.colouring.missingSet D (Fin.natAdd a.middle.seedPalette j)).card:ℝ) ≤
      FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ) := by
  have hMissing : S.colouring.missingSet D (Fin.natAdd a.middle.seedPalette j)=a.palette.missingSet D j := by
    ext v
    simp only [MultiGraph.EdgeColoring.missingSet,mem_filter]
    rw [hSame]
  have hBefore : ((D\S.colouring.missingSet D (Fin.natAdd a.middle.seedPalette j)).card:ℝ) ≤
      FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ)/100+2 := by
    rw [hMissing]
    rcases hD with rfl|rfl
    · exact a.occupied j
    · rw [a.palette.occupied_compl_eq_of_internal_balance j (a.balance j)]
      exact a.occupied j
  have hGrow : ((D\z.result.colouring.missingSet D (Fin.natAdd a.middle.seedPalette j)).card:ℝ) ≤
      ((D\S.colouring.missingSet D (Fin.natAdd a.middle.seedPalette j)).card:ℝ)+4 := by
    exact_mod_cast z.occupied_growth D
  linarith [a.large_order]

theorem Candidate.CaseTwoHallCompletion.deleted_after_prescription
    (a : p.CaseTwoHallCompletion s ell ρ)
    (S : p.completed.PartialColouring (a.middle.seedPalette+(a.fresh+3*a.cap)))
    (hMono : ∀ e, a.seed.graph.mult e ≤ S.graph.mult e) (j : Fin (a.fresh+3*a.cap))
    (z : MultiGraph.PartialColouring.AnchorPrescription S (Fin.natAdd a.middle.seedPalette j) s.part p.centre b)
    (v : Fin (p.pairIndex+1) × Bool)
    (hv : v ∈ z.result.colouring.missingSet univ (Fin.natAdd a.middle.seedPalette j)) :
    ((z.result.graph.crossingSupport s.part).degree v:ℝ) < FirstAnchorScale.rate P ρ*(p.pairIndex+1:ℕ) := by
  have hNe := z.missing_ne_anchors univ v hv
  have hFilled : a.seed.graph.degree v=a.middle.seedPalette := by
    rw [←a.seed.colouring.sum_colour_degree v]
    simp_rw [a.factors]
    simp
  have hDrift := a.seed.crossing_degree_after_fresh_palette z.result s.part v
    (fun e => (hMono e).trans (z.graph_mono e)) hFilled
  have hInitial := a.ordinary_deleted v hNe.1 hNe.2
  have hNat : (z.result.graph.crossingSupport s.part).degree v ≤
      2+Nat.ceil (6*a.middle.seedError)+a.cap+(a.fresh+3*a.cap) := by omega
  have hNatR : ((z.result.graph.crossingSupport s.part).degree v:ℝ) ≤
      2+(Nat.ceil (6*a.middle.seedError):ℝ)+(a.cap:ℝ)+((a.fresh:ℝ)+3*(a.cap:ℝ)) := by exact_mod_cast hNat
  have hCeil := Nat.ceil_lt_add_one (mul_nonneg (show (0:ℝ) ≤ 6 by norm_num) a.budget.error_pos.le)
  have hFresh := a.fresh_bound
  have hError := a.error_rate
  have hCap := a.cap_rate
  have hOrder := a.large_order
  linarith

theorem Candidate.CaseTwoHallCompletion.minimum_after_prescription
    (a : p.CaseTwoHallCompletion s ell ρ) (hP : 8 ≤ P) (hρ : 0 < ρ)
    (S : p.completed.PartialColouring (a.middle.seedPalette+(a.fresh+3*a.cap)))
    (hMono : ∀ e, a.seed.graph.mult e ≤ S.graph.mult e) (j : Fin (a.fresh+3*a.cap))
    (hSame : S.colouring.colourGraph (Fin.natAdd a.middle.seedPalette j)=a.palette.colourGraph j)
    (z : MultiGraph.PartialColouring.AnchorPrescription S (Fin.natAdd a.middle.seedPalette j) s.part p.centre b)
    (v : Fin (p.pairIndex+1) × Bool)
    (hv : v ∈ z.result.colouring.missingSet univ (Fin.natAdd a.middle.seedPalette j))
    (D : Finset (Fin (p.pairIndex+1) × Bool))
    (hSide : (v ∈ s.part ∧ D=s.partᶜ) ∨ (v ∉ s.part ∧ D=s.part)) :
    (p.pairIndex+1)/(1024*P)+2*(3*T+1) ≤
      neighboursIn (p.completed.supportGraph\z.result.graph.crossingSupport s.part)
        (z.result.colouring.missingSet D (Fin.natAdd a.middle.seedPalette j)) v := by
  have hNe := z.missing_ne_anchors univ v hv
  have hSupport := p.ordinary_support_half_bound a.centre_id v
    (by simpa only [←a.centre_id] using hNe.1) (by simpa only [←a.second_id] using hNe.2)
  have hMin := HallNeighbourLoss.opposite_degree_after_deletions p.completed.supportGraph
    (z.result.graph.crossingSupport s.part) s.part D
    (z.result.colouring.missingSet D (Fin.natAdd a.middle.seedPalette j)) v
    ((G.maxDegree:ℝ)/2-((B+c.setᶜ.card:ℕ):ℝ)) (η*(p.pairIndex+1:ℕ)) hSide
    (filter_subset _ _) hSupport (s.simple_discrepancy v)
  have hD : D=s.part ∨ D=s.partᶜ := by rcases hSide with ⟨_,rfl⟩|⟨_,rfl⟩ <;> tauto
  have hOccupied := a.occupied_after_prescription S j hSame z D hD
  have hDeleted := a.deleted_after_prescription S hMono j z v hv
  have hRate := FirstAnchorScale.rate_order_bounds P (p.pairIndex+1)
    ((p.pairIndex+1)/(2^30*P^3)-4*(3*T+1)) hP ρ hρ a.robust_rate
  have hHalf : ((p.pairIndex+1:ℕ):ℝ) ≤ G.maxDegree := by exact_mod_cast a.half_order
  have hEta : η*(p.pairIndex+1:ℕ) ≤ a.middle.seedError := by
    dsimp only [Candidate.CaseTwoMiddleCopies.seedError]
    linarith [show (0:ℝ) ≤ B from Nat.cast_nonneg _,show (0:ℝ) ≤ T from Nat.cast_nonneg _,
      show (0:ℝ) ≤ ((p.pairIndex+1)/T:ℕ) from Nat.cast_nonneg _]
  have hWindow := a.window
  have hError := a.error_rate
  have hLoss := a.loss_rate
  have hCompare : (((p.pairIndex+1)/(1024*P)+2*(3*T+1):ℕ):ℝ) ≤
      (neighboursIn (p.completed.supportGraph\z.result.graph.crossingSupport s.part)
        (z.result.colouring.missingSet D (Fin.natAdd a.middle.seedPalette j)) v:ℝ) := by linarith
  exact_mod_cast hCompare

end OverfullWork.NormalizedCanonicalCandidate
