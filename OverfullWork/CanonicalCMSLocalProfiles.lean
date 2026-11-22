module

public import OverfullWork.CanonicalLocalProfileScales

@[expose] public section


/-! # Construct the three local profiles of CMS Theorem 4.2

Only conditions (1a), (1b), (1c) are packaged here. This does not assert
the global robust-expansion hypothesis, the strict order/degree bound,
the parameter hierarchy or the factorization conclusion of the theorem.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 12000000

def Candidate.CMSLocalProfiles (p : Candidate c) (η : ℝ) : Prop :=
  p.centre=(0,false) ∧
  (∀v : Fin (p.pairIndex+1)×Bool,2≤p.rank v →
    (p.orderedBase.mult s((0,false),v):ℝ)≤2*η^2*((2*(p.pairIndex+1):ℕ):ℝ)) ∧
  (∀v : Fin (p.pairIndex+1)×Bool,2≤p.rank v →
    (((p.rank v-1:ℕ):ℝ)/(p.rank v:ℝ))*(G.maxDegree:ℝ)-6*η*((2*(p.pairIndex+1):ℕ):ℝ)≤
      (p.completed.supportGraph.degree v:ℝ)) ∧
  (∀v : Fin (p.pairIndex+1)×Bool,p.rank v=1 →
    (G.maxDegree:ℝ)-(p.completed.mult s((0,false),v):ℝ)-13*η*((2*(p.pairIndex+1):ℕ):ℝ)≤
      (p.completed.supportGraph.degree v:ℝ)) ∧
  (∀v : Fin (p.pairIndex+1)×Bool,2≤p.rank v →
    (G.maxDegree:ℝ)-(p.completed.mult s((0,false),v):ℝ)-6*η*((2*(p.pairIndex+1):ℕ):ℝ)≤
      (p.completed.supportGraph.degree v:ℝ))

theorem Candidate.cms_local_profiles_of_losses (p : Candidate c) (η : ℝ) (hη : 0≤η)
    (hCentre : p.centre=(0,false))
    (hBundle : (c.setᶜ.card:ℝ)≤2*η^2*((2*(p.pairIndex+1):ℕ):ℝ))
    (hLoss : ((B+c.setᶜ.card:ℕ):ℝ)≤6*η*((2*(p.pairIndex+1):ℕ):ℝ)) :
    p.CMSLocalProfiles η := by
  have hB:(B:ℝ)≤((B+c.setᶜ.card:ℕ):ℝ):=by exact_mod_cast (Nat.le_add_right B c.setᶜ.card)
  have hPositive:0≤η*((2*(p.pairIndex+1):ℕ):ℝ):=mul_nonneg hη (Nat.cast_nonneg _)
  have hNeighbour:∀v : Fin (p.pairIndex+1)×Bool,1≤p.rank v →
      (G.maxDegree:ℝ)≤(p.completed.supportGraph.degree v:ℝ)+
        (p.completed.mult s((0,false),v):ℝ)+(B:ℝ):=by
    intro v hr
    have hv:v≠p.centre:=by
      intro hh
      rw [hh,hCentre] at hr
      simp [Candidate.rank,OrderedCanonicalTransport.pairedIndex] at hr
    have hh:=p.completed_neighbour_profile v hv
    rw [hCentre] at hh
    exact_mod_cast hh
  refine ⟨hCentre,?_,?_,?_,?_⟩
  · intro v hr
    have hh:=p.centre_multiplicity v
    rw [hCentre] at hh
    have hc:(p.orderedBase.mult s((0,false),v):ℝ)≤(c.setᶜ.card:ℝ):=by exact_mod_cast hh
    exact hc.trans hBundle
  · intro v hr
    have hh:=p.completed_rank_profile_real hCentre v (by omega)
    linarith only [hh,hLoss]
  · intro v hr
    have hh:=hNeighbour v (by omega)
    linarith only [hh,hB,hLoss,hPositive]
  · intro v hr
    have hh:=hNeighbour v (by omega)
    linarith only [hh,hB,hLoss]

/-- All three published local errors are discharged from the existing
sparse source budgets. The centre-first candidate is actually constructed. -/
theorem exists_centred_cms_local_profiles (η : ℝ) (hη : 0<η) :
    ∃Q : ℕ,2≤Q ∧ ∃N : ℕ,∀{V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ} (c : Certificate G B K),
      N≤Fintype.card V → B≤6*(Fintype.card V/(4096*Q^2))+6 →
      K≤Fintype.card V/(4096*Q^2)+1 → ¬G.HasOverfullSubgraph →
      c.set.card+B+2*c.setᶜ.card≤2*G.maxDegree+2 →
      (∀x∈c.set,(∑y∈c.setᶜ,G.degree y)≤G.degree x) →
      ∃p : Candidate c,p.CMSLocalProfiles η := by
  obtain ⟨Q,hQ⟩:=exists_nat_gt (max (2:ℝ) (max (1/η) (1/η^2)))
  have hQReal:(2:ℝ)≤Q:=(le_max_left _ _).trans hQ.le
  have hQN:2≤Q:=by exact_mod_cast hQReal
  have hQη:1≤η*(Q:ℝ):=by
    have hh:1/η<(Q:ℝ):=(le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hQ)
    have ht:=(div_lt_iff₀ hη).mp hh
    nlinarith only [ht]
  have hQη2:1≤η^2*(Q:ℝ):=by
    have hh:1/η^2<(Q:ℝ):=(le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hQ)
    have ht:=(div_lt_iff₀ (show 0<η^2 by positivity)).mp hh
    nlinarith only [ht]
  refine ⟨Q,hQN,64*Q,?_⟩
  intro V _ _ G _ B K c hn hB hK hNo hGap hMin
  obtain ⟨p,hCentre⟩:=exists_centred_candidate G c hNo hGap hMin
  have hBudget:=p.local_profile_loss_at_source_scale Q hQN hn hB hK
  have hCast:(Q:ℝ)*((B+c.setᶜ.card:ℕ):ℝ)≤((2*(p.pairIndex+1):ℕ):ℝ):=by exact_mod_cast hBudget
  have hLoss:((B+c.setᶜ.card:ℕ):ℝ)≤η*((2*(p.pairIndex+1):ℕ):ℝ):=by
    have h₁:=mul_le_mul_of_nonneg_left hCast hη.le
    have h₂:=mul_le_mul_of_nonneg_right hQη (Nat.cast_nonneg (B+c.setᶜ.card))
    nlinarith only [h₁,h₂]
  have hLoss2:((B+c.setᶜ.card:ℕ):ℝ)≤η^2*((2*(p.pairIndex+1):ℕ):ℝ):=by
    have h₁:=mul_le_mul_of_nonneg_left hCast (sq_nonneg η)
    have h₂:=mul_le_mul_of_nonneg_right hQη2 (Nat.cast_nonneg (B+c.setᶜ.card))
    nlinarith only [h₁,h₂]
  have hY:(c.setᶜ.card:ℝ)≤((B+c.setᶜ.card:ℕ):ℝ):=by exact_mod_cast (Nat.le_add_left c.setᶜ.card B)
  refine ⟨p,p.cms_local_profiles_of_losses η hη.le hCentre ?_ ?_⟩
  · have hPos:0≤η^2*((2*(p.pairIndex+1):ℕ):ℝ):=by positivity
    nlinarith only [hY,hLoss2,hPos]
  · have hPos:0≤η*((2*(p.pairIndex+1):ℕ):ℝ):=by positivity
    nlinarith only [hLoss,hPos]

end OverfullWork.NormalizedCanonicalCandidate
