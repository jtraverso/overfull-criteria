module

public import OverfullWork.RealDirectedRobustExpansion

@[expose] public section


/-! Robust expansion under uniform source and target fibres. The two
maps may differ, as they do for the shadow digraph in Claim 5.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {U W : Type*} [Fintype U] [Fintype W]

def fibrePullback (R : Digraph U) (src dst : W → U) : Digraph W :=
  ⟨fun x y => R.Adj (src x) (dst y)⟩

noncomputable def fibreWeight (f : W → U) (S : Finset W) (u : U) : ℕ :=
  (S.filter (fun x => f x = u)).card

theorem card_preimage_of_uniform_fibres (f : W → U) (m : ℕ)
    (hf : ∀ u, fibreWeight f univ u = m) (A : Finset U) :
    ((univ : Finset W).filter (fun x => f x ∈ A)).card = A.card*m := by
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset W) A f
  change (∑ u ∈ A,fibreWeight f univ u) = _ at h
  simpa only [hf,sum_const,Nat.nsmul_eq_mul] using h.symm

theorem fibrePullback_semidegrees (R : Digraph U) (src dst : W → U) (m : ℕ)
    (hs : ∀ u, fibreWeight src univ u = m) (ht : ∀ u, fibreWeight dst univ u = m)
    (x : W) :
    inDegree (fibrePullback R src dst) x = inDegree R (dst x)*m ∧
      outDegree (fibrePullback R src dst) x = outDegree R (src x)*m := by
  have hIn := card_preimage_of_uniform_fibres src m hs (univ.filter (fun u => R.Adj u (dst x)))
  have hOut := card_preimage_of_uniform_fibres dst m ht (univ.filter (R.Adj (src x)))
  constructor
  · change ((univ : Finset W).filter (fun y => R.Adj (src y) (dst x))).card = _
    simpa only [inDegree,inNeighbours,mem_filter,mem_univ,true_and] using hIn
  · change ((univ : Finset W).filter (fun y => R.Adj (src x) (dst y))).card = _
    simpa only [outDegree,mem_filter,mem_univ,true_and] using hOut

/-- A quantitative form of the uniform blow-up argument in Claim 5.5.
Counting the source fibres and lifting the target fibres separately
also covers the shifted shadow endpoints. -/
theorem fibrePullback_realRobust (R : Digraph U) (src dst : W → U) (m : ℕ)
    (hs : ∀ u, fibreWeight src univ u = m) (ht : ∀ u, fibreWeight dst univ u = m)
    (hm : 0 < m) (ν τ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/4)
    (hOrder : 2 ≤ τ*(Fintype.card U:ℝ)) (hR : IsRealRobust R ν τ) :
    IsRealRobust (fibrePullback R src dst) (ν^2/2) (2*τ) := by
  let n := (Fintype.card U:ℝ)
  let M := (m:ℝ)
  have hM : 0 < M := by dsimp [M]; exact_mod_cast hm
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hN : (Fintype.card W:ℝ) = n*M := by
    have h := card_preimage_of_uniform_fibres src m hs (univ : Finset U)
    simp only [mem_univ,filter_true,card_univ] at h
    dsimp [n,M]
    exact_mod_cast h
  have hν1 : ν ≤ 1 := by linarith only [hντ,hτ]
  intro S hL hU
  rw [hN] at hL hU
  let J := (univ : Finset U).filter (fun u => (ν/2)*M ≤ (fibreWeight src S u:ℝ))
  have hWt : (∑ u : U,(fibreWeight src S u:ℝ)) = S.card := by
    exact_mod_cast (show (∑ u : U,fibreWeight src S u) = S.card from by
      simpa only [fibreWeight,mem_univ,filter_true] using
        (sum_card_fiberwise_eq_card_filter S (univ : Finset U) src))
  have hMax (u : U) : (fibreWeight src S u:ℝ) ≤ M := by
    dsimp [M]
    exact_mod_cast (show fibreWeight src S u ≤ m from
      (card_le_card (filter_subset_filter _ (subset_univ S))).trans_eq (hs u))
  have hSJ : (S.card:ℝ) ≤ (J.card:ℝ)*M+n*((ν/2)*M) := by
    rw [←hWt,←sum_add_sum_compl J (fun u => (fibreWeight src S u:ℝ))]
    have hJ := sum_le_sum (s := J) (fun u _ => hMax u)
    have hJC := sum_le_sum (s := Jᶜ) (fun u hu => show (fibreWeight src S u:ℝ) ≤ (ν/2)*M from
      le_of_lt (not_le.mp (fun h => (mem_compl.mp hu) (mem_filter.mpr ⟨mem_univ _,h⟩))))
    simp only [sum_const,nsmul_eq_mul] at hJ hJC
    have hCount : (Jᶜ.card:ℝ) ≤ n := by dsimp [n]; exact_mod_cast card_le_univ Jᶜ
    have hC := mul_le_mul_of_nonneg_right hCount (by positivity : 0 ≤ (ν/2)*M)
    linarith only [hJ,hJC,hC]
  have hJlo : τ*n ≤ (J.card:ℝ) := by
    have hτν := mul_le_mul_of_nonneg_right (show ν/2 ≤ τ by linarith only [hν,hντ]) (mul_nonneg hn hM.le)
    apply (mul_le_mul_iff_of_pos_right hM).mp
    nlinarith only [hSJ,hL,hτν]
  obtain ⟨T,hTJ,hTlo,hThi,hTransfer⟩ :
      ∃ T ⊆ J, τ*n ≤ (T.card:ℝ) ∧ (T.card:ℝ) ≤ (1-τ)*n ∧
        (S.card:ℝ) ≤ ((T.card:ℝ)+ν*n/2)*M := by
    by_cases hJ : (J.card:ℝ) ≤ (1-τ)*n
    · exact ⟨J,subset_refl _,hJlo,hJ,by nlinarith only [hSJ]⟩
    · have hNonNeg : 0 ≤ (1-τ)*n := by nlinarith only [hτ,hn]
      have hFloor : ⌊(1-τ)*n⌋₊ ≤ J.card := Nat.floor_le_of_le (le_of_not_ge hJ)
      obtain ⟨T,hT,hSize⟩ := exists_subset_card_eq hFloor
      have hu := Nat.floor_le hNonNeg
      have hl := Nat.lt_floor_add_one ((1-τ)*n)
      have h1 : (1-2*τ)*n ≤ (T.card:ℝ) := by
        rw [hSize]
        linarith only [hl,hOrder]
      refine ⟨T,hT,?_,by rwa [hSize],?_⟩
      · have ht := mul_le_mul_of_nonneg_right (show τ ≤ 1-2*τ by linarith only [hτ]) hn
        linarith only [h1,ht]
      · have ht := mul_le_mul_of_nonneg_right h1 hM.le
        have hp := mul_nonneg (mul_nonneg hν.le hn) hM.le
        nlinarith only [hU,ht,hp]
  let A := realNeighbourhood R ν T
  have hSub : ((univ : Finset W).filter (fun x => dst x ∈ A)) ⊆
      realNeighbourhood (fibrePullback R src dst) (ν^2/2) S := by
    intro x hx
    have hAx := (mem_filter.mp (show dst x ∈ A from (mem_filter.mp hx).2)).2
    have hFibre : inNeighbours (fibrePullback R src dst) S x ≥
        ∑ u ∈ T.filter (fun u => R.Adj u (dst x)),fibreWeight src S u := by
      rw [show (∑ u ∈ T.filter (fun u => R.Adj u (dst x)),fibreWeight src S u) =
          (S.filter (fun y => src y ∈ T.filter (fun u => R.Adj u (dst x)))).card by
        exact sum_card_fiberwise_eq_card_filter S _ src]
      apply card_le_card
      intro y hy
      exact mem_filter.mpr ⟨(mem_filter.mp hy).1,(mem_filter.mp (mem_filter.mp hy).2).2⟩
    have hSum : (inNeighbours R T (dst x):ℝ)*((ν/2)*M) ≤
        ∑ u ∈ T.filter (fun u => R.Adj u (dst x)),(fibreWeight src S u:ℝ) := by
      simpa only [inNeighbours,sum_const,nsmul_eq_mul] using
        sum_le_sum (s := T.filter (fun u => R.Adj u (dst x))) (fun u hu => (mem_filter.mp (hTJ (mem_filter.mp hu).1)).2)
    have hX : (∑ u ∈ T.filter (fun u => R.Adj u (dst x)),(fibreWeight src S u:ℝ)) ≤
        (inNeighbours (fibrePullback R src dst) S x:ℝ) := by exact_mod_cast hFibre
    have hMul := mul_le_mul_of_nonneg_right hAx (show 0 ≤ (ν/2)*M by positivity)
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rw [hN]
    nlinarith only [hMul,hSum,hX]
  have hLift : (A.card:ℝ)*M ≤ ((realNeighbourhood (fibrePullback R src dst) (ν^2/2) S).card:ℝ) := by
    dsimp [M]
    exact_mod_cast (show A.card*m ≤ _ from
      (card_preimage_of_uniform_fibres dst m ht A).symm.trans_le (card_le_card hSub))
  have hGrow := mul_le_mul_of_nonneg_right (hR T hTlo hThi) hM.le
  have hGain := mul_le_mul_of_nonneg_right hν1 (show 0 ≤ (ν/2)*n*M by positivity)
  rw [hN]
  nlinarith only [hGrow,hLift,hTransfer,hGain]

end OverfullWork.DirectedRobustExpansion
