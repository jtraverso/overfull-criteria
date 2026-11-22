module

public import Overfull.Counting
public import Overfull.Kierstead4
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Packing low leaves linked through one prescribed colour

For a fixed colour beta, every low leaf is linked to the root through
every root-missing colour. Three-endpoint exclusion makes the common
missing palettes disjoint. The extra missing colour at the deleted-edge
endpoint yields a strict cardinal bound from actual degree thresholds.
-/
namespace OverfullWork.CaoChenLinkedPalettePacking
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000

/-- Common root palettes of universally linked leaves are pairwise disjoint. -/
theorem pairwise_disjoint_common_missing (c : PEC G (Fin G.maxDegree))
    (x : V) (β : Fin G.maxDegree) (T : Finset V) (hxT : x∉T)
    (hlink : ∀z∈T,∀δ,c.IsFree x δ → (c.kempeGraph δ β).Reachable x z) :
    Set.PairwiseDisjoint (↑T : Set V) (fun z => missing c x∩missing c z) := by
  intro z hz w hw hzw
  apply Finset.disjoint_left.mpr
  intro δ hδz hδw
  have hδx:=mem_missing.mp (mem_inter.mp hδz).1
  have hδz':=mem_missing.mp (mem_inter.mp hδz).2
  have hδw':=mem_missing.mp (mem_inter.mp hδw).2
  have hxz : x≠z:=fun he => hxT (he ▸ hz)
  have hxw : x≠w:=fun he => hxT (he ▸ hw)
  exact not_three_linked c hxz hxw hzw (Or.inl hδx) (Or.inl hδz') (Or.inl hδw')
    (hlink z hz δ hδx) (hlink w hw δ hδx)

/-- Exact packing budget: all private common palettes fit in the root palette. -/
theorem sum_common_missing_card_le_root (c : PEC G (Fin G.maxDegree))
    (x : V) (β : Fin G.maxDegree) (T : Finset V) (hxT : x∉T)
    (hlink : ∀z∈T,∀δ,c.IsFree x δ → (c.kempeGraph δ β).Reachable x z) :
    (∑z∈T,(missing c x∩missing c z).card)≤(missing c x).card := by
  have hdis:=pairwise_disjoint_common_missing c x β T hxT hlink
  have hsub : (T.biUnion fun z => missing c x∩missing c z)⊆missing c x := by
    intro δ hδ
    obtain ⟨z,_,hz⟩:=mem_biUnion.mp hδ
    exact (mem_inter.mp hz).1
  have hc:=card_le_card hsub
  rwa [card_biUnion hdis] at hc

/-- Every proper partial colouring has at least Delta-degree(v) missing colours. -/
theorem missing_card_add_degree_ge (c : PEC G (Fin G.maxDegree)) (v : V) :
    G.maxDegree≤(missing c v).card+G.degree v := by
  have h:=card_missing_add_colNbrs c v
  have hn : (colNbrs c v).card≤G.degree v :=
    (card_le_card (filter_subset _ _)).trans_eq (card_neighborFinset_eq_degree G v)
  omega

/-- The endpoint's extra missing colour strengthens the elementary
intersection bound; no Kempe or criticality assumption enters this count. -/
theorem common_missing_card_gt_half_epsilon_delta
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hx : (G.degree x:ℝ)≤ε*(G.maxDegree:ℝ)/2)
    (z : V) (hz : (G.degree z:ℝ)<(1-ε)*(G.maxDegree:ℝ)) :
    ε*(G.maxDegree:ℝ)/2<((missing c x∩missing c z).card:ℝ) := by
  have hroot:=hcm.card_missing_end (Or.inl rfl : x=x ∨ x=y)
  have hleaf:=missing_card_add_degree_ge c z
  have hinter:=Overfull.card_inter_ge (missing c x) (missing c z)
  have hrootR : ((missing c x).card:ℝ)+(G.degree x:ℝ)=(G.maxDegree:ℝ)+1 := by
    exact_mod_cast hroot
  have hleafR : (G.maxDegree:ℝ)≤((missing c z).card:ℝ)+(G.degree z:ℝ) := by
    exact_mod_cast hleaf
  have hinterR : ((missing c x).card:ℝ)+((missing c z).card:ℝ)≤
      ((missing c x∩missing c z).card:ℝ)+(G.maxDegree:ℝ) := by
    simpa only [Fintype.card_fin] using (show
      ((missing c x).card:ℝ)+((missing c z).card:ℝ)≤
        ((missing c x∩missing c z).card:ℝ)+(Fintype.card (Fin G.maxDegree):ℝ) by
      exact_mod_cast hinter)
  nlinarith only [hrootR,hleafR,hinterR,hx,hz]

/-- A low linked family has bounded size, with the strict inequality
obtained from actual degree sums rather than an assumed palette bound. -/
theorem epsilon_mul_card_lt_two_of_linked_low_leaves
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y)
    (β : Fin G.maxDegree) (T : Finset V) (ε : ℝ) (_hε : 0<ε)
    (hx : (G.degree x:ℝ)≤ε*(G.maxDegree:ℝ)/2) (hxT : x∉T)
    (hlow : ∀z∈T,(G.degree z:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hlink : ∀z∈T,∀δ,c.IsFree x δ → (c.kempeGraph δ β).Reachable x z) :
    ε*(T.card:ℝ)<2 := by
  have hbudget:=sum_common_missing_card_le_root c x β T hxT hlink
  have hrootcap : (missing c x).card≤G.maxDegree := by
    simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (missing c x))
  have hbudgetR : (∑z∈T,((missing c x∩missing c z).card:ℝ))≤(G.maxDegree:ℝ) := by
    exact_mod_cast hbudget.trans hrootcap
  by_cases hT : T.Nonempty
  · have hlarge : ∀z∈T,ε*(G.maxDegree:ℝ)/2<((missing c x∩missing c z).card:ℝ) :=
      fun z hz => common_missing_card_gt_half_epsilon_delta hcm ε hx z (hlow z hz)
    obtain ⟨z,hz⟩:=hT
    have hstrict := sum_lt_sum (fun z hz => (hlarge z hz).le) ⟨z,hz,hlarge z hz⟩
    have hstrict' : (T.card:ℝ)*(ε*(G.maxDegree:ℝ)/2)<
        ∑z∈T,((missing c x∩missing c z).card:ℝ) := by
      simpa only [sum_const,nsmul_eq_mul] using hstrict
    have hD : (0:ℝ)<(G.maxDegree:ℝ) := by
      have hp : 0<G.degree x:=(G.degree_pos_iff_exists_adj x).mpr ⟨y,hcm.adj⟩
      exact_mod_cast hp.trans_le (G.degree_le_maxDegree x)
    nlinarith only [hstrict',hbudgetR,hD]
  · have he : T=∅:=not_nonempty_iff_eq_empty.mp hT
    simp only [he,card_empty,Nat.cast_zero,mul_zero]
    norm_num

theorem card_lt_two_div_epsilon_of_linked_low_leaves
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y)
    (β : Fin G.maxDegree) (T : Finset V) (ε : ℝ) (hε : 0<ε)
    (hx : (G.degree x:ℝ)≤ε*(G.maxDegree:ℝ)/2) (hxT : x∉T)
    (hlow : ∀z∈T,(G.degree z:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hlink : ∀z∈T,∀δ,c.IsFree x δ → (c.kempeGraph δ β).Reachable x z) :
    (T.card:ℝ)<2/ε := by
  apply (lt_div_iff₀ hε).mpr
  simpa only [mul_comm] using
    epsilon_mul_card_lt_two_of_linked_low_leaves hcm β T ε hε hx hxT hlow hlink

end OverfullWork.CaoChenLinkedPalettePacking
