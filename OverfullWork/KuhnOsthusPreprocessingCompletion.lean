module

public import OverfullWork.DirectedInducedPerturbation
public import OverfullWork.OsthusStadenTrimmedCopies
public import OverfullWork.InducedDigraphSampling
public import OverfullWork.RobustRegularFactor
public import OverfullWork.ThinReserveAssembly

@[expose] public section


/-! The complementary factor in (PG2) of Kühn–Osthus Lemma 8.6,
from the available robust graph and the degree-demand margins. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem ordinary_degree_balance (S : Digraph V) (Z : Finset V)
    (hZ : ∀ v ∈ Z, inDegree S v = outDegree S v) :
    (∑ v : ↥Zᶜ, inDegree S v.val) = ∑ v : ↥Zᶜ, outDegree S v.val := by
  have hSum : (∑ v, inDegree S v) = ∑ v, outDegree S v := by
    simp only [outDegree,inDegree,inNeighbours,card_filter]
    exact sum_comm
  have hExc : (∑ v ∈ Z, inDegree S v) = ∑ v ∈ Z, outDegree S v :=
    sum_congr rfl hZ
  rw [←sum_subtype Zᶜ (fun _ => Iff.rfl) (inDegree S),
    ←sum_subtype Zᶜ (fun _ => Iff.rfl) (outDegree S)]
  have hI := sum_add_sum_compl Z (inDegree S)
  have hO := sum_add_sum_compl Z (outDegree S)
  omega

private theorem lifted_complement_support (Z : Finset V) (D : Digraph ↥Zᶜ) :
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
    ∀ x y, (liftDirectedPair e e D).Adj x y → x ∉ Z ∧ y ∉ Z := by
  intro e x y h
  obtain ⟨s,t,rfl,rfl,_⟩ := h
  exact ⟨mem_compl.mp s.prop,mem_compl.mp t.prop⟩

private theorem induced_lifted_complement (Z : Finset V) (D : Digraph ↥Zᶜ) :
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
    induced (liftDirectedPair e e D) Zᶜ = D := by
  intro e
  ext x y
  exact liftDirectedPair_adj e e D x y

/-- Construct the graph in (PG2) by prescribing both degree deficits.
The exceptional vertices of the seed already have equal semidegrees;
only the ordinary vertices receive new arcs. -/
theorem exists_preprocessing_completion
    (G S : Digraph V) (Z : Finset V) (a b ρ τ L : ℕ)
    (hSub : S ≤ G)
    (hExc : ∀ v ∈ Z, inDegree S v = a ∧ outDegree S v = a)
    (hOrd : ∀ v ∉ Z, inDegree S v ≤ b-L ∧ outDegree S v ≤ b-L)
    (hL : L ≤ b) (hTwo : b ≤ 2*L)
    (hGap : 2*(b-L)*(Zᶜ.card) ≤ L*ρ) (hSquare : 2*b*(Zᶜ.card) ≤ ρ*ρ)
    (hRobust : IsRobustAt (induced (G \ S) Zᶜ) ρ τ)
    (hIn : ∀ v : ↥Zᶜ, τ+b ≤ inDegree (induced (G \ S) Zᶜ) v)
    (hOut : ∀ v : ↥Zᶜ, 2*τ+b ≤ outDegree (induced (G \ S) Zᶜ) v) :
    ∃ D : Digraph V, D ≤ G \ S ∧
      (∀ x y, D.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
      S ⊔ D ≤ G ∧
      ∀ v, inDegree (S ⊔ D) v = (if v ∈ Z then a else b) ∧
        outDegree (S ⊔ D) v = (if v ∈ Z then a else b) := by
  let p (v : ↥Zᶜ) := b - outDegree S v.val
  let q (v : ↥Zᶜ) := b - inDegree S v.val
  have hO (v : ↥Zᶜ) := (hOrd v.val (mem_compl.mp v.prop)).2
  have hI (v : ↥Zᶜ) := (hOrd v.val (mem_compl.mp v.prop)).1
  have hp (v : ↥Zᶜ) : L ≤ p v ∧ p v ≤ b := by
    have h := hO v
    dsimp [p]
    omega
  have hq (v : ↥Zᶜ) : L ≤ q v ∧ q v ≤ b := by
    have h := hI v
    dsimp [q]
    omega
  have hP : (∑ v,p v) + (∑ v : ↥Zᶜ,outDegree S v.val) = ∑ _ : ↥Zᶜ,b := by
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun v _ => Nat.sub_add_cancel ((hO v).trans (Nat.sub_le _ _)))
  have hQ : (∑ v,q v) + (∑ v : ↥Zᶜ,inDegree S v.val) = ∑ _ : ↥Zᶜ,b := by
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun v _ => Nat.sub_add_cancel ((hI v).trans (Nat.sub_le _ _)))
  have hBalance := ordinary_degree_balance S Z (fun v hv => (hExc v hv).1.trans (hExc v hv).2.symm)
  have hPQ : (∑ v,p v) = ∑ v,q v := by omega
  obtain ⟨B,hB,hBO,hBI⟩ := exists_subdigraph_of_robust_degree_demands
    (induced (G \ S) Zᶜ) ρ τ L b p q hRobust hL hTwo
    (by simpa only [Fintype.card_coe] using hGap)
    (by simpa only [Fintype.card_coe] using hSquare) hIn hOut hp hq hPQ
  let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
  let D := liftDirectedPair e e B
  have hD : D ≤ G \ S := by
    rintro x y ⟨v,w,rfl,rfl,h⟩
    exact hB h
  have hSupport := lifted_complement_support Z B
  refine ⟨D,hD,hSupport,sup_le hSub (fun _ _ h => (hD h).1),?_⟩
  intro v
  obtain ⟨hOut',hIn'⟩ := degrees_sup_of_disjoint S D (fun _ _ h => (hD h.2).2 h.1) v
  rw [hIn',hOut']
  by_cases hv : v ∈ Z
  · have hi : inDegree D v = 0 := by
      apply card_eq_zero.mpr
      ext w
      exact ⟨fun h => ((hSupport w v (mem_filter.mp h).2).2 hv).elim,fun h => (notMem_empty _ h).elim⟩
    have ho : outDegree D v = 0 := by
      apply card_eq_zero.mpr
      ext w
      exact ⟨fun h => ((hSupport v w (mem_filter.mp h).2).1 hv).elim,fun h => (notMem_empty _ h).elim⟩
    simp only [hv,if_true,hi,ho,add_zero]
    exact hExc v hv
  · let w : ↥Zᶜ := ⟨v,mem_compl.mpr hv⟩
    have lift_deg (s : Bool) : pairSemidegree s D v = pairSemidegree s B w := by
      cases s
      · show inDegree D v = inDegree B w
        rw [←induced_lifted_complement Z B]
        rw [induced_inDegree]
        have hEq : Zᶜ ∩ inProfile D v = inProfile D v := inter_eq_right.mpr
          (fun u hu => mem_compl.mpr (hSupport u v (mem_filter.mp hu).2).1)
        rw [hEq,inProfile_card]
      · show outDegree D v = outDegree B w
        rw [←induced_lifted_complement Z B]
        rw [induced_outDegree]
        have hEq : Zᶜ ∩ outProfile D v = outProfile D v := inter_eq_right.mpr
          (fun u hu => mem_compl.mpr (hSupport v u (mem_filter.mp hu).2).2)
        rw [hEq,outProfile_card]
    simp only [hv,if_false]
    rw [show inDegree D v = inDegree B w from lift_deg false,
      show outDegree D v = outDegree B w from lift_deg true,hBI,hBO]
    have hi := (hI w).trans (Nat.sub_le b L)
    have ho := (hO w).trans (Nat.sub_le b L)
    change inDegree S v + (b - inDegree S v) = b ∧
      outDegree S v + (b - outDegree S v) = b
    exact ⟨Nat.add_sub_of_le hi,Nat.add_sub_of_le ho⟩

/-- Removing the exceptional vertices and the initial preprocessing
arcs preserves the expansion and minimum semidegrees needed in (PG2)
under the stated simultaneous budgets. -/
theorem preprocessing_complement_host
    (G S : Digraph V) (Z : Finset V) (ν τ μ σ : ℝ) (k a : ℕ)
    (hSub : S ≤ G) (hG : IsRealRobust G ν τ)
    (hLoss : ∀ v, inDegree S v ≤ k ∧ outDegree S v ≤ k)
    (hLow : τ*(Fintype.card V : ℝ) ≤ σ*(Zᶜ.card : ℝ))
    (hHigh : (1-σ)*(Zᶜ.card : ℝ) ≤ (1-τ)*(Fintype.card V : ℝ))
    (hRobustBudget : μ*(Zᶜ.card : ℝ)+(Z.card : ℝ)+(k : ℝ) ≤ ν*(Fintype.card V : ℝ))
    (hIn : ∀ v, a+k+Z.card ≤ inDegree G v)
    (hOut : ∀ v, a+k+Z.card ≤ outDegree G v) :
    IsRealRobust (induced (G \ S) Zᶜ) μ σ ∧
      ∀ v : ↥Zᶜ, a ≤ inDegree (induced (G \ S) Zᶜ) v ∧ a ≤ outDegree (induced (G \ S) Zᶜ) v := by
  have hA : IsRealRobust (induced G (univ : Finset V)) ν τ := by
    apply (induced_real_robust_iff ..).mpr
    intro T _ hT hT'
    exact hG T (by simpa only [card_univ] using hT) (by simpa only [card_univ] using hT')
  have hEq : (univ : Finset V) \ Zᶜ = Z := by simp
  have hNone : Zᶜ \ (univ : Finset V) = ∅ := by simp
  refine ⟨?_,?_⟩
  · apply induced_real_robust_of_perturbation G (G \ S) univ Zᶜ ν τ μ σ k hA
      (fun _ _ h => h.1)
    · intro v
      have hRem : G \ S ≤ G := fun _ _ h => h.1
      have hFirst := (residual_semidegrees G S hSub v).1
      have hSecond := (residual_semidegrees G (G \ S) hRem v).1
      have hBound := (hLoss v).1
      omega
    · simpa only [card_univ,hNone,card_empty,Nat.cast_zero,add_zero] using hLow
    · simpa only [card_univ] using hHigh
    · simpa only [card_univ,hEq,hNone,card_empty,Nat.cast_zero,add_zero] using hRobustBudget
  · intro v
    have hCount (T : Finset V) : T.card ≤ (Zᶜ ∩ T).card + Z.card := by
      have he : Zᶜ ∩ T = T \ Z := by
        ext w
        simp only [mem_inter,mem_compl,mem_sdiff,and_comm]
      rw [he]
      exact card_le_card_sdiff_add_card
    have hCI := hCount (inProfile (G \ S) v.val)
    have hCO := hCount (outProfile (G \ S) v.val)
    rw [inProfile_card,←induced_inDegree] at hCI
    rw [outProfile_card,←induced_outDegree] at hCO
    obtain ⟨hi,ho⟩ := residual_semidegrees G S hSub v.val
    have hPaid := hLoss v.val
    have hMinI := hIn v.val
    have hMinO := hOut v.val
    omega

end OverfullWork.DirectedRobustExpansion
