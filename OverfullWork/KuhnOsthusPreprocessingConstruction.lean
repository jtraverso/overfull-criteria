module

public import OverfullWork.KuhnOsthusPreprocessingCompletion
public import OverfullWork.KuhnOsthusResidualPreprocessing
public import OverfullWork.DirectedConfigurationDegrees

@[expose] public section


/-! Construct the preprocessing graph of Kühn–Osthus Lemma 8.6
from a packing of original exceptional factors and an extender in
their complement. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling DirectedSpanningConfiguration
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem exceptional_factor_degree {Z : Finset V} {label : V → Fin 50} {l : ℕ}
    (C : OriginalExceptionalFactor label Z l) (v : V) (hv : v ∈ Z) :
    inDegree C.digraph v = 50*l ∧ outDegree C.digraph v = 50*l := by
  have hDis : Pairwise (fun i j => Disjoint (C.path i) (C.path j)) := by
    intro i j hij
    apply disjoint_iff_inf_le.mpr
    rintro x y ⟨hi,hj⟩
    exact hij (C.disjoint i j hi hj)
  change inDegree (⨆ i, C.path i) v = _ ∧ outDegree (⨆ i, C.path i) v = _
  rw [inDegree_iSup_of_disjoint _ hDis,outDegree_iSup_of_disjoint _ hDis]
  have hin (i : Fin 50 × Fin l) : inDegree (C.path i) v = 1 := by
    obtain ⟨w,hw⟩ := (C.cover i v hv).2
    apply card_eq_one.mpr
    exact ⟨w,eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨mem_univ _,hw⟩,
      fun x hx => (C.path_system i).in_unique (mem_filter.mp hx).2 hw⟩⟩
  have hout (i : Fin 50 × Fin l) : outDegree (C.path i) v = 1 := by
    obtain ⟨w,hw⟩ := (C.cover i v hv).1
    apply card_eq_one.mpr
    exact ⟨w,eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨mem_univ _,hw⟩,
      fun x hx => (C.path_system i).out_unique (mem_filter.mp hx).2 hw⟩⟩
  simp only [hin,hout,sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,Nat.nsmul_eq_mul,mul_one,
    and_self]

/-- Semidegrees of the ambient graph obtained by lifting ordinary arcs. -/
theorem ordinary_lift_degrees (Z : Finset V) (D : Digraph ↥Zᶜ) (v : V) :
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
    let F := liftDirectedPair e e D
    (∀ hv : v ∉ Z, let w : ↥Zᶜ := ⟨v,mem_compl.mpr hv⟩
      inDegree F v = inDegree D w ∧ outDegree F v = outDegree D w) ∧
    (v ∈ Z → inDegree F v = 0 ∧ outDegree F v = 0) := by
  intro e F
  have hSupport (x y : V) (h : F.Adj x y) : x ∉ Z ∧ y ∉ Z := by
    obtain ⟨x,y,rfl,rfl,_⟩ := h
    exact ⟨mem_compl.mp x.prop,mem_compl.mp y.prop⟩
  have he : induced F Zᶜ = D := by
    ext x y
    exact liftDirectedPair_adj e e D x y
  constructor
  · intro hv w
    have hin : Zᶜ ∩ inProfile F v = inProfile F v := inter_eq_right.mpr
      (fun x hx => mem_compl.mpr (hSupport x v (mem_filter.mp hx).2).1)
    have hout : Zᶜ ∩ outProfile F v = outProfile F v := inter_eq_right.mpr
      (fun x hx => mem_compl.mpr (hSupport v x (mem_filter.mp hx).2).2)
    have hi := induced_inDegree F Zᶜ w
    have ho := induced_outDegree F Zᶜ w
    change inDegree (induced F Zᶜ) w = (Zᶜ ∩ inProfile F v).card at hi
    change outDegree (induced F Zᶜ) w = (Zᶜ ∩ outProfile F v).card at ho
    rw [he,hin] at hi
    rw [he,hout] at ho
    exact ⟨hi.symm,ho.symm⟩
  · intro hv
    constructor
    · apply Nat.eq_zero_of_not_pos
      intro hp
      obtain ⟨x,hx⟩ := card_pos.mp hp
      exact (hSupport x v (mem_filter.mp hx).2).2 hv
    · apply Nat.eq_zero_of_not_pos
      intro hp
      obtain ⟨x,hx⟩ := card_pos.mp hp
      exact (hSupport v x (mem_filter.mp hx).2).1 hv

/-- The construction of (PG1) and (PG2). The disjointness of the
extender from the exceptional factors is obtained by taking it
in the actual complement. -/
theorem kuhn_osthus_preprocessing_graph_of_reserves
    {Z : Finset V} {label : V → Fin 50} {r l : ℕ}
    (G : Digraph V) (C : Fin r → OriginalExceptionalFactor label Z l) (R₀ : Digraph ↥Zᶜ)
    (t k L : ℕ) (ν τ μ σ : ℝ)
    (hC : ∀ i, (C i).digraph ≤ G)
    (hDisC : Pairwise (fun i j => Disjoint (C i).digraph (C j).digraph))
    (hOrdC : ∀ v ∉ Z, inDegree (⨆ i, (C i).digraph) v ≤ r ∧
      outDegree (⨆ i, (C i).digraph) v ≤ r)
    (hR : R₀ ≤ induced (G \ (⨆ i, (C i).digraph)) Zᶜ)
    (hDegree : ∀ v, inDegree R₀ v ≤ k ∧ outDegree R₀ v ≤ k)
    (hG : IsRealRobust G ν τ) (hμ : 0 ≤ μ)
    (hWidthLow : τ*(Fintype.card V:ℝ) ≤ σ*(Zᶜ.card:ℝ))
    (hWidthHigh : (1-σ)*(Zᶜ.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ))
    (hBudget : μ*(Zᶜ.card:ℝ)+(Z.card:ℝ)+(k+r*(50*l):ℕ) ≤ ν*(Fintype.card V:ℝ))
    (hSlots : 1 ≤ 50*l)
    (hRoom : k+r ≤ r*(50*l)+t-L)
    (hL : L ≤ r*(50*l)+t) (hTwo : r*(50*l)+t ≤ 2*L)
    (hGap : 2*(r*(50*l)+t-L)*Zᶜ.card ≤ L*⌈μ*(Zᶜ.card:ℝ)⌉₊)
    (hSquare : 2*(r*(50*l)+t)*Zᶜ.card ≤ ⌈μ*(Zᶜ.card:ℝ)⌉₊^2)
    (hIn : ∀ v, 2*⌈σ*(Zᶜ.card:ℝ)⌉₊+(r*(50*l)+t)+(k+r*(50*l))+Z.card ≤ inDegree G v)
    (hOut : ∀ v, 2*⌈σ*(Zᶜ.card:ℝ)⌉₊+(r*(50*l)+t)+(k+r*(50*l))+Z.card ≤ outDegree G v) :
    ∃ P R : Digraph V, P ≤ G ∧ R ≤ P ∧
      induced R Zᶜ = R₀ ∧ (∀ i, (C i).digraph ≤ P ∧ Disjoint (C i).digraph R) ∧
      ∀ v, let a := if v ∈ Z then r*(50*l+1) else r*(50*l+1)+t
        inDegree P v+r = a ∧ outDegree P v+r = a := by
  let E := ⨆ i, (C i).digraph
  let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
  let R := liftDirectedPair e e R₀
  let S := E ⊔ R
  let b := r*(50*l)+t
  let N := k+r*(50*l)
  let t₀ := ⌈σ*(Zᶜ.card:ℝ)⌉₊
  have hRLe : R ≤ G \ E := by
    rintro _ _ ⟨v,w,rfl,rfl,h⟩
    exact hR h
  have hSLe : S ≤ G := sup_le (iSup_le hC) (fun _ _ h => (hRLe h).1)
  have hDis : Disjoint E R := by
    apply disjoint_iff_inf_le.mpr
    rintro x y ⟨he,hr⟩
    exact (hRLe hr).2 he
  have hExc (v : V) (hv : v ∈ Z) : inDegree E v = r*(50*l) ∧ outDegree E v = r*(50*l) := by
    change inDegree (⨆ i, (C i).digraph) v = _ ∧ outDegree (⨆ i, (C i).digraph) v = _
    rw [inDegree_iSup_of_disjoint _ hDisC,outDegree_iSup_of_disjoint _ hDisC]
    simp only [(exceptional_factor_degree (C _) v hv).1,(exceptional_factor_degree (C _) v hv).2,
      sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,and_self]
  have hSExc (v : V) (hv : v ∈ Z) :
      inDegree S v = r*(50*l) ∧ outDegree S v = r*(50*l) := by
    obtain ⟨hO,hI⟩ := degrees_sup_of_disjoint E R (fun _ _ h => (hRLe h.2).2 h.1) v
    change inDegree S v = _ at hI
    change outDegree S v = _ at hO
    obtain ⟨hRI,hRO⟩ := (ordinary_lift_degrees Z R₀ v).2 hv
    change inDegree R v = 0 at hRI
    change outDegree R v = 0 at hRO
    exact ⟨by simpa only [hI,hRI,add_zero] using (hExc v hv).1,
      by simpa only [hO,hRO,add_zero] using (hExc v hv).2⟩
  have hSOrd (v : V) (hv : v ∉ Z) : inDegree S v ≤ k+r ∧ outDegree S v ≤ k+r := by
    obtain ⟨hO,hI⟩ := degrees_sup_of_disjoint E R (fun _ _ h => (hRLe h.2).2 h.1) v
    change inDegree S v = _ at hI
    change outDegree S v = _ at hO
    obtain ⟨hRI,hRO⟩ := (ordinary_lift_degrees Z R₀ v).1 hv
    have hRDeg := hDegree ⟨v,mem_compl.mpr hv⟩
    have hE : inDegree E v ≤ r ∧ outDegree E v ≤ r := hOrdC v hv
    change inDegree R v = inDegree R₀ ⟨v,mem_compl.mpr hv⟩ at hRI
    change outDegree R v = outDegree R₀ ⟨v,mem_compl.mpr hv⟩ at hRO
    exact ⟨by omega,by omega⟩
  have hLoss (v : V) : inDegree S v ≤ N ∧ outDegree S v ≤ N := by
    by_cases hv : v ∈ Z
    · have h := hSExc v hv
      exact ⟨by omega,by omega⟩
    · have h := hSOrd v hv
      have hn : r ≤ r*(50*l) := by
        simpa only [mul_one] using Nat.mul_le_mul_left r hSlots
      exact ⟨by omega,by omega⟩
  obtain ⟨hRobust,hMin⟩ := preprocessing_complement_host G S Z ν τ μ σ N (2*t₀+b) hSLe hG
    hLoss hWidthLow hWidthHigh hBudget hIn hOut
  have hRobust' := integer_of_real (induced (G \ S) Zᶜ) μ σ hμ hRobust
  obtain ⟨B,_,_,hP,hDeg⟩ := exists_preprocessing_completion G S Z (r*(50*l)) b
    ⌈μ*(Zᶜ.card:ℝ)⌉₊ t₀ L hSLe hSExc
    (fun v hv => ⟨(hSOrd v hv).1.trans hRoom,(hSOrd v hv).2.trans hRoom⟩) hL hTwo
    hGap (by rw [pow_two] at hSquare; exact hSquare)
    (by rwa [Fintype.card_coe] at hRobust')
    (fun v => (show t₀+b ≤ 2*t₀+b by omega).trans (hMin v).1)
    (fun v => (hMin v).2)
  refine ⟨S ⊔ B,R,hP,(le_sup_right : R ≤ S).trans le_sup_left,?_,?_,?_⟩
  · ext x y
    exact liftDirectedPair_adj e e R₀ x y
  · intro i
    exact ⟨(le_iSup (fun i => (C i).digraph) i).trans (le_sup_left.trans le_sup_left),
      hDis.mono_left (le_iSup (fun i => (C i).digraph) i)⟩
  · intro v
    have h := hDeg v
    by_cases hv : v ∈ Z <;> simp only [hv,if_true,if_false,Nat.mul_add,Nat.mul_one,b] at h ⊢ <;> omega

end OverfullWork.DirectedRobustExpansion
