module

public import OverfullWork.PaperResidueAnchorConditions
public import OverfullWork.UnitInternalAnchor

@[expose] public section


/-! Centre-bundle reserves in every monotone fresh state, from actual seed rows. -/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun RegularHeavyCutRepair
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
variable {p : Candidate c} {P T : ℕ} {η : ℝ} {b w : Fin (p.pairIndex+1) × Bool}
variable {s : p.CaseTwoPartition P T η b} {r : p.CaseTwoMiddleCopies s w}
set_option maxHeartbeats 24000000

theorem Candidate.CaseTwoMiddleCopies.seed_error_basics (r : p.CaseTwoMiddleCopies s w) :
    4*(B:ℝ)+6*(T:ℝ)+9 ≤ r.seedError ∧ 0 ≤ r.seedError := by
  have hη : 0 ≤ η*(p.pairIndex+1:ℕ) :=
    (abs_nonneg _).trans (s.simple_discrepancy p.centre).le
  have hDiv : (0:ℝ) ≤ ((p.pairIndex+1)/T:ℕ) := Nat.cast_nonneg _
  have hB : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
  dsimp only [Candidate.CaseTwoMiddleCopies.seedError]
  constructor <;> linarith

theorem Candidate.CaseTwoMiddleCopies.fresh_free_bundle
    (r : p.CaseTwoMiddleCopies s w) (Q : p.completed.PartialColouring r.seedPalette)
    (f : ℕ) (S : p.completed.PartialColouring (r.seedPalette+f))
    (hMono : ∀ e, Q.graph.mult e ≤ S.graph.mult e)
    (hFilled : Q.graph.degree p.centre=r.seedPalette)
    (hRow : ∀ v ∈ s.partᶜ, Q.graph.mult s(p.centre,v) ≤ r.count v+Nat.ceil r.seedError)
    (hw : w ∉ s.part) (v : Fin (p.pairIndex+1) × Bool) (hv : v ∈ s.partᶜ) :
    p.completed.mult s(p.centre,v) ≤ 2*S.available.mult s(p.centre,v)+B+2+
      2*Nat.ceil r.seedError+2*f := by
  have hDegree := S.colouring.degree_le_palette p.centre
  have hGrowth := MultiGraph.bundle_growth_le_degree_growth Q.graph S.graph p.centre v f
    (fun x => hMono s(p.centre,x)) (by omega)
  have hUpper := r.bundle_upper v
  rw [Candidate.CaseTwoPartition.crossWeight,if_pos hv] at hUpper
  have hb : b ≠ p.centre := fun he => s.second_not_mem (he ▸ s.centre_mem)
  have hwc : w ≠ p.centre := fun he => hw (he ▸ s.centre_mem)
  have hSmall := p.off_centre_bundle_le b w hb hwc
  have hLe := S.le s(p.centre,v)
  have hSeed := hRow v hv
  change _ ≤ 2*(p.completed.mult s(p.centre,v)-S.graph.mult s(p.centre,v))+_+_+_+_
  omega

theorem Candidate.CaseTwoPartition.second_partner_weight_zero (s : p.CaseTwoPartition P T η b) :
    s.partnerWeight b=0 := by
  apply dif_neg
  intro hh
  exact ((heavySet_mem _ _ _ _ _).mp hh).1 rfl

theorem Candidate.CaseTwoMiddleCopies.fresh_second_bundle_upper
    (r : p.CaseTwoMiddleCopies s w) (Q : p.completed.PartialColouring r.seedPalette)
    (f : ℕ) (S : p.completed.PartialColouring (r.seedPalette+f))
    (hMono : ∀ e, Q.graph.mult e ≤ S.graph.mult e)
    (hRow : r.count b ≤ Q.graph.mult s(p.centre,b))
    (hw : w ∉ s.part) (hD : G.maxDegree ≤ 3*(p.pairIndex+1)) (hT : 1 ≤ T) :
    2*(S.available.mult s(p.centre,b):ℝ) ≤ (p.completed.mult s(p.centre,b):ℝ)+2*r.seedError := by
  have hH := heavySet_card_at_scale p.completed p.centre b G.maxDegree (p.pairIndex+1) T
    p.completion.regular hD hT
  have hHC : s.heavyVertices.card ≤ 3*T+1 := (card_insert_le _ _).trans (by omega)
  have hb : b ≠ p.centre := fun he => s.second_not_mem (he ▸ s.centre_mem)
  have hbw := p.off_centre_bundle_le b w hb (fun he => hw (he ▸ s.centre_mem))
  have hDef := (single_le_sum (f := r.balancing.deficit) (fun _ _ => Nat.zero_le _) (mem_univ b)).trans r.deficit_budget
  have hPair := r.paired_lower b (mem_insert_self b _)
  rw [Candidate.CaseTwoPartition.crossWeight,if_pos (mem_compl.mpr s.second_not_mem),
    s.second_partner_weight_zero] at hPair
  have hCurrent := hMono s(p.centre,b)
  have hLe := S.le s(p.centre,b)
  have hNat : 2*S.available.mult s(p.centre,b) ≤ p.completed.mult s(p.centre,b)+2*(B+3*T+3) := by
    change 2*(p.completed.mult s(p.centre,b)-S.graph.mult s(p.centre,b)) ≤ _
    omega
  have hNatR : 2*(S.available.mult s(p.centre,b):ℝ) ≤ (p.completed.mult s(p.centre,b):ℝ)+2*((B:ℝ)+3*(T:ℝ)+3) := by exact_mod_cast hNat
  have hBasic := r.seed_error_basics.1
  linarith

end OverfullWork.NormalizedCanonicalCandidate
