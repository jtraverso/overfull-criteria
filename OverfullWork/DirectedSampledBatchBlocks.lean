module

public import OverfullWork.DirectedBatchBlockSchedule
public import OverfullWork.DirectedInducedPerturbation

@[expose] public section


/-! Sample one reserve partition for a batch, assign its blocks cyclically,
and carry the robust and profile guarantees through each layout trim. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveUsage UniformSubsetSampling InducedDigraphSampling
open scoped Classical
universe u v w

private theorem card_inter_add_compl {V : Type*} [Fintype V] (X P : Finset V) :
    (X ∩ P).card+(Xᶜ ∩ P).card = P.card := by
  have hi : P.filter (fun v => v ∈ X) = X ∩ P := by
    ext v
    simp [and_comm]
  have ho : P.filter (fun v => v ∉ X) = Xᶜ ∩ P := by
    ext v
    simp [and_comm]
  rw [← hi,← ho]
  exact card_filter_add_card_filter_not _

private theorem profile_after_trim {V : Type*} [Fintype V] (X Y P : Finset V) (z : ℕ)
    (hLost : (X \ Y).card ≤ z) (hAdded : (Y \ X).card ≤ z) :
    |((Y ∩ P).card:ℝ)-((X ∩ P).card:ℝ)| ≤ (z:ℝ) := by
  have hDiff (A B : Finset V) : (A ∩ P) \ (B ∩ P) ⊆ A \ B := by
    intro x hx
    obtain ⟨ha,hp⟩ := mem_inter.mp (mem_sdiff.mp hx).1
    exact mem_sdiff.mpr ⟨ha,fun hb => (mem_sdiff.mp hx).2 (mem_inter.mpr ⟨hb,hp⟩)⟩
  have h₁ := card_le_card_sdiff_add_card (s := X ∩ P) (t := Y ∩ P)
  have h₂ := card_le_card_sdiff_add_card (s := Y ∩ P) (t := X ∩ P)
  have hX := (card_le_card (hDiff X Y)).trans hLost
  have hY := (card_le_card (hDiff Y X)).trans hAdded
  rw [abs_le]
  have h₁' : ((X ∩ P).card:ℝ) ≤ ((Y ∩ P).card:ℝ)+(z:ℝ) := by
    exact_mod_cast (show (X ∩ P).card ≤ (Y ∩ P).card+z by omega)
  have h₂' : ((Y ∩ P).card:ℝ) ≤ ((X ∩ P).card:ℝ)+(z:ℝ) := by
    exact_mod_cast (show (Y ∩ P).card ≤ (X ∩ P).card+z by omega)
  constructor <;> linarith only [h₁',h₂']

/-- The initial partition, balanced assignment, and layout trimming can
be made simultaneously. Both resulting induced digraphs are robust,
and every specified neighbourhood profile is controlled on both sides. -/
theorem exists_sampled_batch_blocks (ν τ c C η : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/8)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hC : 0 < C) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {J : Type v} [Fintype J] {P : Type w} [Fintype P]
      {k : ℕ} (_hk : 0 < k) (Γ : Digraph V) (profiles : P → Finset V)
      (boundary : J → Finset V) (size : Fin k → ℕ) (z : ℕ),
      let n := Fintype.card V
      let νs := ν^6/(2:ℝ)^60
      N ≤ n → 0 < n → IsRealRobust Γ ν τ → (∑ i,size i) = n →
      (Fintype.card P:ℝ) ≤ C*(n:ℝ) → 3*k < n^2 →
      (∀ i, c*(n:ℝ) ≤ (size i:ℝ) ∧ c*(n:ℝ) ≤ ((n-size i:ℕ):ℝ)) →
      (∀ j, (boundary j).card ≤ z) → 8*(z:ℝ) ≤ νs*(c*(n:ℝ)) →
      4*(z:ℝ) ≤ (4*τ)*(c*(n:ℝ)) →
      ∃ rank : V → Fin k, ∃ slot : J → Fin k,
        let A := fun i => slice rank (slot i) \ boundary i
        (∀ v, visits A v ≤ (Fintype.card J+k-1)/k) ∧
        ∀ i, Disjoint (boundary i) (A i) ∧ (A i).card ≤ size (slot i) ∧
          size (slot i) ≤ (A i).card+z ∧
          IsRealRobust (induced Γ (A i)) (νs/2) (8*τ) ∧
          IsRealRobust (induced Γ (A i)ᶜ) (νs/2) (8*τ) ∧
          ∀ p, |((A i ∩ profiles p).card:ℝ) -
            ((size (slot i):ℝ)/(n:ℝ))*(profiles p).card| < η*(n:ℝ)+(z:ℝ) ∧
          |(((A i)ᶜ ∩ profiles p).card:ℝ) -
            (((n-size (slot i):ℕ):ℝ)/(n:ℝ))*(profiles p).card| < η*(n:ℝ)+(z:ℝ) := by
  obtain ⟨N,hSample⟩ := exists_robust_profile_partition.{u,0,w} ν τ c C η hν hντ hτ
    hc hc₁ hC hη
  refine ⟨N,?_⟩
  intro V _ J _ P _ k hk Γ profiles boundary size z
  dsimp only
  intro hN hn hR hSizes hProfiles hkN hSmall hBound hνLoss hτLoss
  let n := Fintype.card V
  let νs := ν^6/(2:ℝ)^60
  obtain ⟨rank,hRank⟩ := hSample Γ profiles size hN hR hSizes hProfiles
    (by simpa using hkN) hSmall
  obtain ⟨slot,hApart,hVisits,hLost⟩ := exists_balanced_block_schedule hk rank boundary
  refine ⟨rank,slot,hVisits,?_⟩
  intro i
  let X := slice rank (slot i)
  let Y := X \ boundary i
  obtain ⟨hX,hRX,hRC,hProf⟩ := hRank (slot i)
  change X.card = size (slot i) at hX
  have hY : Y ⊆ X := sdiff_subset
  have hLost' : (X \ Y).card ≤ z := (hLost i).trans (hBound i)
  have hAdded' : (Y \ X).card ≤ z := by simp [sdiff_eq_empty_iff_subset.mpr hY]
  have hComp : (Yᶜ \ Xᶜ) = X \ Y := by
    ext v
    simp [and_comm]
  have hComp' : (Xᶜ \ Yᶜ) = Y \ X := by
    ext v
    simp [and_comm]
  have hSizeComp : Xᶜ.card = n-size (slot i) := by rw [card_compl,hX]
  have hν₀ : 0 ≤ νs := by positivity
  have hν₁ : νs ≤ 1 := by
    dsimp only [νs]
    have hp := pow_le_one₀ hν.le (show ν ≤ 1 by linarith only [hντ,hτ]) (n := 6)
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num
    linarith only [hp]
  have hτ₀ : 0 ≤ 4*τ := by have := hν.trans_le hντ; positivity
  have hτ₁ : 4*τ ≤ 1/2 := by linarith only [hτ]
  have hInto (B : Finset V) (h : c*(n:ℝ) ≤ (B.card:ℝ)) :
      8*(z:ℝ) ≤ νs*(B.card:ℝ) ∧ 4*(z:ℝ) ≤ (4*τ)*(B.card:ℝ) :=
    ⟨hνLoss.trans (mul_le_mul_of_nonneg_left h hν₀),hτLoss.trans (mul_le_mul_of_nonneg_left h hτ₀)⟩
  have hA := hInto X (by rw [hX]; exact (hSmall _).1)
  have hB := hInto Xᶜ (by rw [hSizeComp]; exact (hSmall _).2)
  have hRY := induced_robust_after_small_vertex_changes Γ X Y νs (4*τ) z
    hν₀ hν₁ hτ₀ hτ₁ hRX hLost' hAdded' hA.1 hA.2
  have hRY' := induced_robust_after_small_vertex_changes Γ Xᶜ Yᶜ νs (4*τ) z
    hν₀ hν₁ hτ₀ hτ₁ hRC (by rw [hComp']; exact hAdded')
    (by rw [hComp]; exact hLost') hB.1 hB.2
  have hCard := card_sdiff_add_card_eq_card hY
  refine ⟨hApart i,by rw [← hX]; exact card_le_card hY,
    by change size (slot i) ≤ Y.card+z; omega,by convert hRY using 1; ring,by convert hRY' using 1; ring,?_⟩
  intro p
  have hU := hProf p
  have hV := profile_after_trim X Y (profiles p) z hLost' hAdded'
  have hV' := profile_after_trim Xᶜ Yᶜ (profiles p) z
    (by rw [hComp']; exact hAdded') (by rw [hComp]; exact hLost')
  have hCompProfile : |((Xᶜ ∩ profiles p).card:ℝ) -
      (((n-size (slot i):ℕ):ℝ)/(n:ℝ))*(profiles p).card| < η*(n:ℝ) := by
    have he := card_inter_add_compl X (profiles p)
    have he' : ((X ∩ profiles p).card:ℝ)+((Xᶜ ∩ profiles p).card:ℝ) = (profiles p).card := by
      exact_mod_cast he
    have hSize : size (slot i) ≤ n := hX.symm ▸ card_le_univ X
    have hS : (((n-size (slot i):ℕ):ℝ)/(n:ℝ))*(profiles p).card =
        (profiles p).card-((size (slot i):ℝ)/(n:ℝ))*(profiles p).card := by
      have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      rw [Nat.cast_sub hSize]
      field_simp
    rw [hS,show ((Xᶜ ∩ profiles p).card:ℝ) = (profiles p).card-((X ∩ profiles p).card:ℝ) by linarith]
    rw [show (profiles p).card-((X ∩ profiles p).card:ℝ) -
      ((profiles p).card-((size (slot i):ℝ)/(n:ℝ))*(profiles p).card) =
      -(((X ∩ profiles p).card:ℝ)-((size (slot i):ℝ)/(n:ℝ))*(profiles p).card) by ring,abs_neg]
    exact hU
  constructor
  · exact (abs_sub_le _ ((X ∩ profiles p).card:ℝ) _).trans_lt (by linarith only [hV,hU])
  · exact (abs_sub_le _ ((Xᶜ ∩ profiles p).card:ℝ) _).trans_lt (by linarith only [hV',hCompProfile])

end OverfullWork.DirectedSpanningConfiguration
