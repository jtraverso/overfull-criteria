module

public import OverfullWork.CanonicalSeedCompletionMargins
public import OverfullWork.CaseTwoProtectedExceptions
public import OverfullWork.CanonicalEndpointBootstrap

@[expose] public section


/-! # Pay the finite seed criterion with an enlarged protected set

Only explicit scalar inequalities remain inputs. All graph profiles,
initial forbidden potential, saturation and residue bounds are derived
from the canonical partition and the same actual initial coloring.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 32000000

theorem Candidate.CaseTwoMiddleCopies.InitialRouteBudget.seed_completion_margins_for_exceptions
    {R : p.completed.PartialColouring r.seedPalette} (budget : r.InitialRouteBudget R)
    (hOrdinary : ∀ v, v ≠ p.centre → v ≠ b → (R.graph.crossingSupport s.part).degree v ≤ 2)
    (E : Finset (Fin (p.pairIndex+1) × Bool)) (haE : p.centre ∈ E) (hbE : b ∈ E)
    (hExceptions : E.card ≤ 6*T+2)
    (hCentre : p.centre=(0,false)) (hSecond : b=(0,true))
    (hHalf : p.pairIndex+1 ≤ G.maxDegree) (h ell g q Wbar : ℕ)
    (hPos : 0 < h) (hg : 0 < g) (hScale : 5*r.seedError ≤ (h:ℝ))
    (hLoss : ((B+c.setᶜ.card:ℕ):ℝ)+η*(p.pairIndex+1:ℕ) ≤ (p.pairIndex+1:ℕ)/16)
    (hForb : ((ell:ℝ)+1)*(6*r.seedError+2)+12*(T:ℝ)+8+
      4*r.seedError*(5+(ell:ℝ)*(p.pairIndex+2:ℕ))/(h:ℝ) ≤ (Wbar:ℝ))
    (hW : (Wbar:ℝ) ≤ (p.pairIndex+1:ℕ)/32)
    (hDeleted : 2+(Nat.ceil (6*r.seedError):ℝ)+(h:ℝ) ≤ (p.pairIndex+1:ℕ)/32)
    (hWindow : (((p.pairIndex+1)/(1024*P)+2*(3*T+1):ℕ):ℝ) ≤ (p.pairIndex+1:ℕ)/8)
    (hGain : Wbar+g ≤ (p.pairIndex+1)/(2^30*P^3)-4*(3*T+1))
    (hRounds : (p.pairIndex+1)/g+3 ≤ ell) (hReserve : 4+2*ell < q)
    (hPred : q ≤ (p.pairIndex+1)/(2^30*P^3)-4*(3*T+1)-(2+Nat.ceil (6*r.seedError)+h)) :
    MultiGraph.PartialColouring.SeedCompletionMargins R s.part E h ell
      (p.pairIndex+1) G.maxDegree ((p.pairIndex+1)/(2^30*P^3)-4*(3*T+1))
      ((p.pairIndex+1)/(1024*P)+2*(3*T+1)) (Nat.ceil (6*r.seedError)) g q Wbar
      ((B+c.setᶜ.card:ℕ):ℝ) (η*(p.pairIndex+1:ℕ)) p.centre b := by
  refine {
    card_part := s.card_part, card_compl := s.card_compl, robust := s.robust,
    residue_cap := budget.residue_cap_of_scale hScale,
    ordinary_deleted := hOrdinary,
    first_exception := haE,
    second_exception := hbE,
    missing := ?_, anchors := ?_, ordinary_support := ?_, discrepancy := s.simple_discrepancy,
    delta := hHalf, loss_margin := hLoss, forbidden_margin := hW,
    deletion_margin := by simpa only [Nat.cast_add,Nat.cast_ofNat] using hDeleted,
    seed_window := hWindow, window := s.nonvacuous,
    positive_cap := hPos, positive_gain := hg, gain := hGain, rounds := hRounds,
    reserve := hReserve, predecessors := hPred, forbidden_initial := ?_
  }
  · intro v
    exact_mod_cast (budget.missing_vertex v).le.trans (Nat.le_ceil (6*r.seedError))
  · intro i
    exact ⟨by rw [(budget.anchors i).1];decide,by rw [(budget.anchors i).2];decide⟩
  · intro v hv₀ hv₁
    exact p.ordinary_support_half_bound hCentre v (by simpa only [hCentre] using hv₀)
      (by simpa only [hSecond] using hv₁)
  · intro i
    have hCut : ((R.colouring.colourGraph i).cutSize s.part:ℝ) ≤ 2 := by exact_mod_cast budget.colour_cut i
    have hColour := mul_le_mul_of_nonneg_left (budget.missing_colour i) (show (0:ℝ) ≤ (ell:ℝ)+1 by positivity)
    have hE : (E.card:ℝ) ≤ 6*(T:ℝ)+2 := by exact_mod_cast hExceptions
    have hBase : 2*((R.colouring.colourGraph i).cutSize s.part:ℝ)+
        ((ell:ℝ)+1)*(R.colouring.missingSet univ i).card+2*(E.card:ℝ) ≤
        ((ell:ℝ)+1)*(6*r.seedError+2)+12*(T:ℝ)+8 := by nlinarith only [hCut,hColour,hE]
    have hBaseMul := mul_le_mul_of_nonneg_left hBase (Nat.cast_nonneg h : (0:ℝ) ≤ h)
    have hPotential := budget.initial_potential_bound ell
    have hCleared := mul_le_mul_of_nonneg_right hForb (Nat.cast_nonneg h : (0:ℝ) ≤ h)
    have hPosR : (0:ℝ) < h := by exact_mod_cast hPos
    rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hPosR)] at hCleared
    have hWeighted : (h:ℝ)*(2*((R.colouring.colourGraph i).cutSize s.part:ℝ)+
        ((ell:ℝ)+1)*(R.colouring.missingSet univ i).card+2*(E.card:ℝ))+
        4*((R.available.internalPart s.part).edgeCount+(ell:ℝ)*((∑ v, (R.colouring.missingPalette v).card)/2:ℕ)) ≤
        (h:ℝ)*(Wbar:ℝ) := by nlinarith only [hBaseMul,hPotential,hCleared]
    exact_mod_cast hWeighted


end OverfullWork.NormalizedCanonicalCandidate
