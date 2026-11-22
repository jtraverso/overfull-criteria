module

public import OverfullWork.CaseTwoCutScales
public import OverfullWork.CanonicalCandidateAboveHalfExpansion

@[expose] public section


/-! # Uniform adjusted cut for the actual above-half canonical candidate

The density scale P is fixed before the heavy-bundle cutoff T and before
the requested simple discrepancy eta. Only the order threshold changes.
This constructs the adjusted robust cut, not its internal edge-colouring.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open PrunedCore BipartiteRobustMargin
open scoped Classical
universe u
set_option maxHeartbeats 12000000

theorem above_half_adjusted_support_cut_at_fixed_scale
    (ε : ℝ) (hε : 0 < ε) (P : ℕ) (hP : 8 ≤ P) (hPε : 1 ≤ ε*(P:ℝ))
    (T : ℕ) (hT : 1 ≤ T) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
      (c : Certificate G B K) (p : Candidate c),
      N ≤ Fintype.card V →
      ((1:ℝ)/2+ε)*(Fintype.card V:ℝ) ≤ (G.maxDegree:ℝ) →
      B ≤ 6*(Fintype.card V/(4096*P^2))+6 → K ≤ Fintype.card V/(4096*P^2)+1 →
      ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
      ∃ A : Finset (Fin (p.pairIndex+1) × Bool),
        A.card = p.pairIndex+1 ∧ Aᶜ.card = p.pairIndex+1 ∧ p.centre ∈ A ∧ b ∉ A ∧
        (∀ v, v ≠ b → (p.pairIndex+1)/T < p.completed.mult s(p.centre,v) → v ∉ A) ∧
        2*p.completed.degreeInto A p.centre ≤ G.maxDegree ∧
        IsBipartiteRobustAt p.completed.supportGraph A
          ((p.pairIndex+1)/(2^30*P^3)-2*(3*T+1)) ((p.pairIndex+1)/(1024*P)+(3*T+1)) ∧
        (0 < (p.pairIndex+1)/(2^30*P^3)-2*(3*T+1)) ∧
        (2*((p.pairIndex+1)/(1024*P)+(3*T+1)) ≤ p.pairIndex+1) ∧
        ∀ v, |(neighboursIn p.completed.supportGraph A v:ℝ)-
          (neighboursIn p.completed.supportGraph Aᶜ v:ℝ)| < η*((p.pairIndex+1:ℕ):ℝ) := by
  let τ : ℝ := min (η/2) (1/(1024*(P:ℝ)))
  have hPpos : (0:ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  obtain ⟨M₀,hM₀⟩ := MultiGraph.eventually_sixth_size τ hτ
  obtain ⟨Mη,hMη⟩ := exists_nat_gt ((4*((3*T+1:ℕ):ℝ))/η)
  let M := max M₀ (max Mη (max (2^50*P^4) ((8*(3*T+1)+1)*(2^30*P^3))))
  refine ⟨3*M,?_⟩
  intro V _ _ G _ B K c p hn hdense hB hK b hab
  let n := Fintype.card V
  let m := p.pairIndex+1
  let Y := c.setᶜ.card
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts := card_add_card_compl c.set
  have hCard : n+1 = 2*m+Y := by dsimp only [n,m,Y];omega
  have hY : Y ≤ n/(4096*P^2)+1 := c.complement_small.trans hK
  have hk : 4096*P^2*(n/(4096*P^2)) ≤ n := Nat.mul_div_le n (4096*P^2)
  have hc : 3 ≤ 4096*P^2 := by nlinarith only [hP]
  have hk3 : 3*(n/(4096*P^2)) ≤ n := (Nat.mul_le_mul_right _ hc).trans hk
  have hnm : n ≤ 3*m := by omega
  have hm : M ≤ m := by change 3*M ≤ n at hn;omega
  have hm₀ : M₀ ≤ m := (le_max_left _ _).trans hm
  have hmη : Mη ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hLarge : 2^50*P^4 ≤ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hRepair : (8*(3*T+1)+1)*(2^30*P^3) ≤ m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hNonempty : c.set.Nonempty := card_pos.mp (by obtain ⟨k,hk⟩ := c.odd;omega)
  have : Nonempty V := by obtain ⟨v,_⟩ := hNonempty;exact ⟨v⟩
  have hDn : G.maxDegree < n := G.maxDegree_lt_card_verts
  have hDenseN : (P+2)*n ≤ 2*P*G.maxDegree := by
    have h₁ := mul_le_mul_of_nonneg_left hdense (show 0 ≤ 2*(P:ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hPε (Nat.cast_nonneg n)
    exact_mod_cast (show ((P:ℝ)+2)*(n:ℝ) ≤ 2*(P:ℝ)*(G.maxDegree:ℝ) by nlinarith only [h₁,h₂])
  obtain ⟨_,hDm,_,hDensity⟩ := CanonicalCandidateAboveHalfExpansion.source_bounds
    P n m G.maxDegree Y B (by omega) hLarge hCard hY hB hDn hDenseN
  have hBq := CaseTwoCutScales.source_budget_le_q P n m B Y hP hLarge hCard hY hB
  obtain ⟨hReserve,hRoom,hNonvacuous⟩ := CaseTwoCutScales.repair_reserves P T m (by omega) hRepair
  have hξcap : τ*(m:ℝ) ≤ (m:ℝ)/(1024*(P:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (η/2) (1/(1024*(P:ℝ)))) (Nat.cast_nonneg m)
    calc
      _ ≤ (1/(1024*(P:ℝ)))*(m:ℝ) := hh
      _ = _ := by ring
  have hMoment : 30*(m:ℝ)^4 < (τ*(m:ℝ))^6 := hM₀ m hm₀
  obtain ⟨A,hA,hAc,ha,hb,hAcross,hHalf,hRobust,hPositive,hDis⟩ :=
    p.exists_case_two_adjusted_cut P T (by omega) hT hLarge hDm hBq hDensity hReserve hRoom
      b hab (τ*(m:ℝ)) (by positivity) hξcap hMoment
  have hError : τ*(m:ℝ)+2*((3*T+1:ℕ):ℝ) ≤ η*(m:ℝ) := by
    have hmηR : (Mη:ℝ) ≤ m := by exact_mod_cast hmη
    have hMul := mul_le_mul_of_nonneg_left hmηR hη.le
    have hRatio := (div_lt_iff₀ hη).mp hMη
    have hτbound := mul_le_mul_of_nonneg_right (min_le_left (η/2) (1/(1024*(P:ℝ)))) (Nat.cast_nonneg m)
    change τ*(m:ℝ) ≤ (η/2)*(m:ℝ) at hτbound
    nlinarith only [hMul,hRatio,hτbound]
  exact ⟨A,hA,hAc,ha,hb,hAcross,hHalf,hRobust,hPositive,hNonvacuous,
    fun v => (hDis v).trans_le hError⟩

theorem exists_uniform_case_two_adjusted_cut (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 8 ≤ P ∧ 1 ≤ ε*(P:ℝ) ∧ ∀ T : ℕ, 1 ≤ T → ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card V →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card V/(4096*P^2))+6 → K ≤ Fintype.card V/(4096*P^2)+1 →
        ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
        ∃ A : Finset (Fin (p.pairIndex+1) × Bool),
          A.card = p.pairIndex+1 ∧ Aᶜ.card = p.pairIndex+1 ∧ p.centre ∈ A ∧ b ∉ A ∧
          (∀ v, v ≠ b → (p.pairIndex+1)/T < p.completed.mult s(p.centre,v) → v ∉ A) ∧
          2*p.completed.degreeInto A p.centre ≤ G.maxDegree ∧
          IsBipartiteRobustAt p.completed.supportGraph A
            ((p.pairIndex+1)/(2^30*P^3)-2*(3*T+1)) ((p.pairIndex+1)/(1024*P)+(3*T+1)) ∧
          (0 < (p.pairIndex+1)/(2^30*P^3)-2*(3*T+1)) ∧
          (2*((p.pairIndex+1)/(1024*P)+(3*T+1)) ≤ p.pairIndex+1) ∧
          ∀ v, |(neighboursIn p.completed.supportGraph A v:ℝ)-
            (neighboursIn p.completed.supportGraph Aᶜ v:ℝ)| < η*((p.pairIndex+1:ℕ):ℝ) := by
  obtain ⟨P,hP⟩ := exists_nat_gt (max (8:ℝ) (1/ε))
  have hPN : 8 ≤ P := by exact_mod_cast ((le_max_left _ _).trans hP.le)
  have hPε : 1 ≤ ε*(P:ℝ) := by
    have hh : 1/ε < P := (le_max_right _ _).trans_lt hP
    have ht := (div_lt_iff₀ hε).mp hh
    nlinarith only [ht]
  exact ⟨P,hPN,hPε,fun T hT η hη =>
    above_half_adjusted_support_cut_at_fixed_scale ε hε P hPN hPε T hT η hη⟩

end OverfullWork.NormalizedCanonicalCandidate
