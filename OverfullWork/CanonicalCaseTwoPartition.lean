module

public import OverfullWork.UniformCaseTwoCut
public import OverfullWork.HeavyNeighbourPartners

@[expose] public section


/-! # The adjusted Case 2 partition, with actual partners and CMS (5.5)

This interface constructs the partition, the light partners and their
bijection, both weight inequalities, simple discrepancy and nonvacuous
robust crossing. The second free-block orientation pays another bounded
cut perturbation. The internal multicolouring is the next obligation.
-/
namespace OverfullWork.NormalizedCanonicalCandidate
open SimpleGraph Finset NormalizedAlmostStoppingRun IndependentSetIdentification
open PrunedCore BipartiteRobustMargin RegularHeavyCutRepair
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {B K : ℕ} {c : Certificate G B K}
set_option maxHeartbeats 12000000

structure Candidate.CaseTwoPartition (p : Candidate c) (P T : ℕ) (η : ℝ)
    (b : Fin (p.pairIndex+1) × Bool) where
  part : Finset (Fin (p.pairIndex+1) × Bool)
  partners : Finset (Fin (p.pairIndex+1) × Bool)
  card_part : part.card = p.pairIndex+1
  card_compl : partᶜ.card = p.pairIndex+1
  centre_mem : p.centre ∈ part
  second_not_mem : b ∉ part
  partnerEquiv : ↥(heavySet p.completed p.centre b ((p.pairIndex+1)/T)) ≃ ↥partners
  partners_subset : partners ⊆ part
  centre_not_partner : p.centre ∉ partners
  second_not_partner : b ∉ partners
  partners_light : ∀ v ∈ partners, p.completed.mult s(p.centre,v) ≤ (p.pairIndex+1)/T
  heavy_across : ∀ v, v ≠ b → (p.pairIndex+1)/T < p.completed.mult s(p.centre,v) → v ∉ part
  free_weight_le : p.completed.degreeInto (part\insert p.centre partners) p.centre ≤
    p.completed.degreeInto (partᶜ\insert b (heavySet p.completed p.centre b ((p.pairIndex+1)/T))) p.centre
  centre_internal_le_half : 2*p.completed.degreeInto part p.centre ≤ G.maxDegree
  robust : IsBipartiteRobustAt p.completed.supportGraph part
    ((p.pairIndex+1)/(2^30*P^3)-4*(3*T+1)) ((p.pairIndex+1)/(1024*P)+2*(3*T+1))
  positive : 0 < (p.pairIndex+1)/(2^30*P^3)-4*(3*T+1)
  nonvacuous : 2*((p.pairIndex+1)/(1024*P)+2*(3*T+1)) ≤ p.pairIndex+1
  simple_discrepancy : ∀ v, |(neighboursIn p.completed.supportGraph part v:ℝ)-
    (neighboursIn p.completed.supportGraph partᶜ v:ℝ)| < η*((p.pairIndex+1:ℕ):ℝ)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_uniform_case_two_partition (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, 8 ≤ P ∧ ∀ T : ℕ, 1 ≤ T → ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] {B K : ℕ}
        (c : Certificate G B K) (p : Candidate c),
        N ≤ Fintype.card W →
        ((1:ℝ)/2+ε)*(Fintype.card W:ℝ) ≤ (G.maxDegree:ℝ) →
        B ≤ 6*(Fintype.card W/(4096*P^2))+6 → K ≤ Fintype.card W/(4096*P^2)+1 →
        ∀ b : Fin (p.pairIndex+1) × Bool, p.centre ≠ b →
          Nonempty (p.CaseTwoPartition P T η b) := by
  obtain ⟨P,hP,_,hCuts⟩ := exists_uniform_case_two_adjusted_cut.{u} ε hε
  refine ⟨P,hP,?_⟩
  intro T hT η hη
  obtain ⟨N₀,hN₀⟩ := hCuts T hT (η/2) (by positivity)
  let h := 3*T+1
  let den := 2^30*P^3
  obtain ⟨Mη,hMη⟩ := exists_nat_gt ((4*(h:ℝ))/η)
  let M := max Mη ((8*h+1)*den)
  refine ⟨max N₀ (3*M),?_⟩
  intro W _ _ G _ B K c p hn hdense hB hK b hab
  obtain ⟨A,hA,hAc,ha,hb,hAcross,_,hRobust,_,_,hDis⟩ :=
    hN₀ G c p (by omega) hdense hB hK b hab
  let n := Fintype.card W
  let m := p.pairIndex+1
  let q := m/(1024*P)
  let r := m/den
  have hCoords := Fintype.card_congr p.coordinates
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,card_vertices,compl_compl] at hCoords
  have hParts := card_add_card_compl c.set
  have hCard : n+1 = 2*m+c.setᶜ.card := by dsimp only [n,m];omega
  have hY : c.setᶜ.card ≤ n/(4096*P^2)+1 := c.complement_small.trans hK
  have hk : 4096*P^2*(n/(4096*P^2)) ≤ n := Nat.mul_div_le n (4096*P^2)
  have hCoef : 3 ≤ 4096*P^2 := by nlinarith only [hP]
  have hk3 : 3*(n/(4096*P^2)) ≤ n := (Nat.mul_le_mul_right _ hCoef).trans hk
  have hnm : n ≤ 3*m := by omega
  have hm : M ≤ m := by change max N₀ (3*M) ≤ n at hn;omega
  have hmη : Mη ≤ m := (le_max_left _ _).trans hm
  have hRepair : (8*h+1)*den ≤ m := (le_max_right _ _).trans hm
  have hDen : 0 < den := by dsimp only [den];positivity
  have hReserve : 8*h+1 ≤ r := (Nat.le_div_iff_mul_le hDen).mpr hRepair
  have hRoom : h ≤ m := hReserve.trans (Nat.div_le_self m den) |>.trans' (by omega)
  have hNonempty : c.set.Nonempty := card_pos.mp (by obtain ⟨k,hk⟩ := c.odd;omega)
  have : Nonempty W := by obtain ⟨v,_⟩ := hNonempty;exact ⟨v⟩
  have hD : G.maxDegree ≤ 3*m := (G.maxDegree_lt_card_verts.le).trans hnm
  have hCount := heavySet_card_at_scale p.completed p.centre b G.maxDegree m T
    p.completion.regular hD hT
  obtain ⟨A',Z',hA',hAc',ha',hb',hEquiv,hZ'sub,hCentreZ',hSecondZ',hLight,hAcross',hFree,
      hHalf,hRobust',hDis'⟩ := HeavyNeighbourPartners.exists_partner_cut p.completed G.maxDegree m
    (m/T) h (r-2*h) (q+h) p.completion.regular p.centre b A hA hAc ha hb hAcross
    (by dsimp only [h];omega) hRoom (by omega) ((η/2)*(m:ℝ)) hDis hRobust
  have hRobustFinal : IsBipartiteRobustAt p.completed.supportGraph A' (r-4*h) (q+2*h) := by
    have h₁ : r-2*h-2*h = r-4*h := by omega
    have h₂ : q+h+h = q+2*h := by omega
    rwa [h₁,h₂] at hRobust'
  have hq : 4*q ≤ m :=
    (Nat.mul_le_mul_right q (show 4 ≤ 1024*P by omega)).trans (Nat.mul_div_le m (1024*P))
  have hhm : 8*h+1 ≤ m := hReserve.trans (Nat.div_le_self m den)
  have hError : (η/2)*(m:ℝ)+2*(h:ℝ) ≤ η*(m:ℝ) := by
    have hmηR : (Mη:ℝ) ≤ m := by exact_mod_cast hmη
    have hMul := mul_le_mul_of_nonneg_left hmηR hη.le
    have hRatio := (div_lt_iff₀ hη).mp hMη
    nlinarith only [hMul,hRatio]
  exact ⟨{
    part := A'
    partners := Z'
    card_part := hA'
    card_compl := hAc'
    centre_mem := ha'
    second_not_mem := hb'
    partnerEquiv := Classical.choice hEquiv
    partners_subset := hZ'sub
    centre_not_partner := hCentreZ'
    second_not_partner := hSecondZ'
    partners_light := hLight
    heavy_across := hAcross'
    free_weight_le := hFree
    centre_internal_le_half := hHalf
    robust := hRobustFinal
    positive := by change 0 < r-4*h;omega
    nonvacuous := by change 2*(q+2*h) ≤ m;omega
    simple_discrepancy := fun v => (hDis' v).trans_le hError
  }⟩

end OverfullWork.NormalizedCanonicalCandidate
