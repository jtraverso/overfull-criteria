module

public import OverfullWork.KuhnOsthusCodegreeCount

@[expose] public section


/-! Complete the two-sided small-set argument for Kühn–Osthus
Lemma 4.11. For a large source set, the missing targets either violate
the rectangle bound or expand too much in the reverse direction. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- An explicit form of Lemma 4.11. The cutoff for checking rectangles
can exceed the density or the scale of robust expansion. -/
theorem sparse_superregular_pair_is_robust (D : Digraph V)
    (ε ν τ L c : ℝ) (hV : 0 < Fintype.card V) (hε : 0 ≤ ε)
    (hν : 0 < ν) (hτ : 2*ν ≤ τ) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hIn : ∀ x, L ≤ (inDegree D x:ℝ)) (hOut : ∀ x, L ≤ (outDegree D x:ℝ))
    (hCodegIn : ∀ x y, x ≠ y → (commonInNeighbours D x y:ℝ) ≤ c)
    (hCodegOut : ∀ x y, x ≠ y → (commonInNeighbours (reverseArcs D) x y:ℝ) ≤ c)
    (hDiagonal : 8*((Fintype.card V:ℝ) + 10*ε*Fintype.card V*c) ≤ L^2)
    (hDiscard : 8*ν*(Fintype.card V:ℝ)^2 ≤ τ*L^2)
    (hRect : ∀ S T : Finset V, ε*(Fintype.card V:ℝ) ≤ (S.card:ℝ) →
      ε*(Fintype.card V:ℝ) ≤ (T.card:ℝ) →
      ν*(Fintype.card V:ℝ)*(T.card:ℝ) < (incidences D S T:ℝ)) :
    IsRealRobust D ν τ := by
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast hV
  have hBudget (S : Finset V) (hS : τ*n/2 ≤ (S.card:ℝ)) :
      4*ν*n^3 ≤ (S.card:ℝ)*L^2 := by
    have h₁ := mul_le_mul_of_nonneg_right hS (sq_nonneg L)
    have h₂ := mul_le_mul_of_nonneg_right hDiscard hn.le
    change (8*ν*n^2)*n ≤ (τ*L^2)*n at h₂
    linarith only [h₁,h₂]
  have hSmall (G : Digraph V) (S : Finset V) (hS : τ*n/2 ≤ (S.card:ℝ))
      (hG : ∀ x, L ≤ (outDegree G x:ℝ))
      (hC : ∀ x y, x ≠ y → (commonInNeighbours G x y:ℝ) ≤ c) :
      min (10*ε*n) (4*(S.card:ℝ)) ≤ ((realNeighbourhood G ν S).card:ℝ) :=
    small_robust_neighbourhood_of_codegrees G S ν L c (10*ε*n) hν.le hL hc
      (fun x _ => hG x) hC (hBudget S hS) hDiagonal (by positivity)
  intro S hS hMax
  let B := realNeighbourhood D ν S
  change τ*n ≤ (S.card:ℝ) at hS
  change (S.card:ℝ) ≤ (1-τ)*n at hMax
  change (S.card:ℝ)+ν*n ≤ (B.card:ℝ)
  have hντ : 2*ν*n ≤ τ*n := by nlinarith only [mul_le_mul_of_nonneg_right hτ hn.le]
  by_cases hSL : (S.card:ℝ) ≤ ε*n
  · have h' := hSmall D S (by linarith) hOut hCodegIn
    rw [min_eq_right (by linarith)] at h'
    linarith only [h',hS,hντ,(Nat.cast_nonneg S.card : (0:ℝ) ≤ S.card)]
  by_contra! hFail
  let T := Bᶜ
  have hC : (T.card:ℝ)+(B.card:ℝ) = n := by
    dsimp only [T,n]
    exact_mod_cast (card_compl_add_card B)
  have hTbig : τ*n/2 < (T.card:ℝ) := by
    have he : (1-τ)*n = n-τ*n := by ring
    rw [he] at hMax
    linarith only [hC,hMax,hFail,hντ]
  have hEdges : (incidences D S T:ℝ) ≤ ν*n*(T.card:ℝ) := by
    simp only [incidences,Nat.cast_sum]
    calc
      _ ≤ ∑ v ∈ T, ν*n := by
        apply sum_le_sum
        intro v hv
        have hn : v ∉ B := mem_compl.mp hv
        exact (lt_of_not_ge (fun hh => hn (mem_filter.mpr ⟨mem_univ _,hh⟩))).le
      _ = _ := by rw [sum_const,nsmul_eq_mul,mul_comm]
  have hTsmall : (T.card:ℝ) < ε*n :=
    lt_of_not_ge (fun h => (not_lt_of_ge hEdges) (hRect S T (le_of_not_ge hSL) h))
  let U := realNeighbourhood (reverseArcs D) ν T
  let S₀ := U ∩ S
  have hS₀ : (S₀.card:ℝ) ≤ T.card := by
    have hDst : (S₀.card:ℝ)*(ν*n) ≤ (incidences D S₀ T:ℝ) := by
      rw [incidences_eq_sum_outTo,←nsmul_eq_mul,←sum_const]
      apply sum_le_sum
      intro x hx
      have hu : x ∈ U := (mem_inter.mp hx).1
      exact (mem_filter.mp hu).2
    have hSrc : (incidences D S₀ T:ℝ) ≤ ν*n*(T.card:ℝ) := by
      apply le_trans _ hEdges
      have hSub : S₀ ⊆ S := inter_subset_right
      simp only [incidences,Nat.cast_sum]
      apply sum_le_sum
      intro v _
      exact_mod_cast card_le_card (filter_subset_filter (fun x => D.Adj x v) hSub)
    apply (mul_le_mul_iff_right₀ (mul_pos hν hn)).mp
    linarith only [hDst,hSrc]
  have hUSub : U ⊆ Sᶜ ∪ S₀ := by
    intro x hx
    by_cases h : x ∈ S
    · exact mem_union_right _ (mem_inter.mpr ⟨hx,h⟩)
    · exact mem_union_left _ (mem_compl.mpr h)
  have hUpper : (U.card:ℝ) ≤ n-(S.card:ℝ)+(T.card:ℝ) := by
    have hBound : (U.card:ℝ) ≤ (Sᶜ.card:ℝ)+S₀.card := by
      exact_mod_cast (card_le_card hUSub).trans (card_union_le _ _)
    have hPart : (Sᶜ.card:ℝ)+(S.card:ℝ) = n := by
      dsimp only [n]
      exact_mod_cast (card_compl_add_card S)
    linarith only [hBound,hS₀,hPart]
  have hReverse : ∀ x, L ≤ (outDegree (reverseArcs D) x:ℝ) := hIn
  have hLower := hSmall (reverseArcs D) T hTbig.le hReverse hCodegOut
  have hMin : 4*(T.card:ℝ) ≤ 10*ε*n := by
    linarith only [hTsmall,(Nat.cast_nonneg T.card : (0:ℝ) ≤ T.card)]
  rw [min_eq_right hMin] at hLower
  change 4*(T.card:ℝ) ≤ (U.card:ℝ) at hLower
  linarith only [hLower,hUpper,hC,hFail,hντ,hTbig]

/-- Relative density on large rectangles gives the rectangle hypothesis
of the sparse-pair expansion theorem, even for cutoffs above the density. -/
theorem sparse_pair_rectangle_of_relative_lower
    (D : Digraph V) (ε d ν : ℝ) (hV : 0 < Fintype.card V)
    (hε : 0 < ε) (hd : 0 ≤ (1-ε)*d)
    (hν : ν < (1-ε)*d*ε)
    (hReg : ∀ S T : Finset V, ε*(Fintype.card V:ℝ) ≤ (S.card:ℝ) →
      ε*(Fintype.card V:ℝ) ≤ (T.card:ℝ) →
      (1-ε)*d*(S.card:ℝ)*(T.card:ℝ) ≤ (incidences D S T:ℝ)) :
    ∀ S T : Finset V, ε*(Fintype.card V:ℝ) ≤ (S.card:ℝ) →
      ε*(Fintype.card V:ℝ) ≤ (T.card:ℝ) →
      ν*(Fintype.card V:ℝ)*(T.card:ℝ) < (incidences D S T:ℝ) := by
  intro S T hS hT
  have hn : (0:ℝ) < Fintype.card V := by exact_mod_cast hV
  have hPos := (mul_pos hε hn).trans_le hT
  have hS' := mul_le_mul_of_nonneg_left hS hd
  have hν' := mul_lt_mul_of_pos_right hν hn
  have hMid : ν*(Fintype.card V:ℝ) < (1-ε)*d*(S.card:ℝ) := by
    nlinarith only [hS',hν']
  exact (mul_lt_mul_of_pos_right hMid hPos).trans_le (hReg S T hS hT)

/-- Lemma 4.11 in the paper's sparse-superregular parameters with an
explicit hierarchy. The codegree bound is required only for distinct
vertices of each side of the identified bipartite pair. -/
theorem kuhn_osthus_sparse_pair_expansion (D : Digraph V)
    (d ε μ ζ ν τ : ℝ) (hV : 0 < Fintype.card V)
    (hd : 0 < d) (hε : 0 < ε) (hε1 : ε < 1) (hμ : 0 < μ) (hζ : 0 < ζ)
    (hν : 0 < ν) (hτ : 2*ν ≤ τ)
    (hScale : 160*ε ≤ (ζ*μ)^2)
    (hDiagonal : 16*(Fintype.card V:ℝ) ≤ (ζ*d*Fintype.card V)^2)
    (hDiscard : 8*ν ≤ τ*(ζ*d)^2)
    (hνDensity : ν < (1-ε)*d*ε)
    (hIn : ∀ x, ζ*d*(Fintype.card V:ℝ) ≤ (inDegree D x:ℝ))
    (hOut : ∀ x, ζ*d*(Fintype.card V:ℝ) ≤ (outDegree D x:ℝ))
    (hCodegIn : ∀ x y, x ≠ y →
      (commonInNeighbours D x y:ℝ) ≤ (d/μ)^2*Fintype.card V)
    (hCodegOut : ∀ x y, x ≠ y →
      (commonInNeighbours (reverseArcs D) x y:ℝ) ≤ (d/μ)^2*Fintype.card V)
    (hReg : ∀ S T : Finset V, ε*(Fintype.card V:ℝ) ≤ (S.card:ℝ) →
      ε*(Fintype.card V:ℝ) ≤ (T.card:ℝ) →
      (1-ε)*d*(S.card:ℝ)*(T.card:ℝ) ≤ (incidences D S T:ℝ)) :
    IsRealRobust D ν τ := by
  let n : ℝ := Fintype.card V
  have hEq : (ζ*μ)^2*(d/μ)^2 = (ζ*d)^2 := by
    field_simp [hμ.ne']
  have hPay := mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right hScale (sq_nonneg (d/μ))).trans_eq hEq) (sq_nonneg n)
  have hDiag' : 8*(n+10*ε*n*((d/μ)^2*n)) ≤ (ζ*d*n)^2 := by
    change 16*n ≤ (ζ*d*n)^2 at hDiagonal
    linarith only [hPay,hDiagonal]
  have hDiscard' : 8*ν*n^2 ≤ τ*(ζ*d*n)^2 := by
    have h := mul_le_mul_of_nonneg_right hDiscard (sq_nonneg n)
    linarith only [h]
  exact sparse_superregular_pair_is_robust D ε ν τ (ζ*d*n) ((d/μ)^2*n)
    hV hε.le hν hτ (by positivity) (by positivity)
    hIn hOut hCodegIn hCodegOut hDiag' hDiscard'
    (sparse_pair_rectangle_of_relative_lower D ε d ν hV hε
      (mul_nonneg (sub_nonneg.mpr hε1.le) hd.le) hνDensity hReg)

end OverfullWork.DirectedRobustExpansion
