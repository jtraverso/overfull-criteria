module

public import OverfullWork.KuhnOsthusExceptionalPairStability
public import OverfullWork.SuperregularDegreeDemands
public import OverfullWork.OsthusStadenH3Split

@[expose] public section


/-! The degree correction in Kühn–Osthus Lemma 4.6, used for the
cycle component of the chord absorber in Lemma 9.3(i). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

/-- A balanced pair with centred superregularity on its full sides is
the common-coordinate version of a physical superregular pair. -/
theorem centred_superregular_iff_pair_univ (D : Digraph V) (ε d : ℝ) :
    IsCentredSuperregular D ε d ↔ IsSuperregularPair D ε d univ univ := by
  constructor
  · rintro ⟨hReg,hDeg⟩
    refine ⟨hReg.1,hReg.2,fun x _ => ?_,fun y _ => ?_⟩
    · simpa only [card_univ,profileCount,univ_inter,outProfile,outDegree] using (hDeg x).2
    · simpa only [card_univ,profileCount,univ_inter,inProfile,inDegree,inNeighbours] using (hDeg y).1
  · rintro ⟨hReg,hDen,hOut,hIn⟩
    refine ⟨⟨hReg,hDen⟩,fun v => ⟨?_,?_⟩⟩
    · simpa only [card_univ,profileCount,univ_inter,inProfile,inDegree,inNeighbours] using hIn v (mem_univ _)
    · simpa only [card_univ,profileCount,univ_inter,outProfile,outDegree] using hOut v (mem_univ _)

/-- Trim a sampled superregular pair to an integer regular factor.
The cut margin supplies a factor, and the bound on the removed
degree preserves the regularity of the same pair. -/
theorem exists_regular_superregular_cycle_pair (D : Digraph V) (k r loss : ℕ)
    (ε η d δ : ℝ) (hG : IsCentredSuperregular D ε d)
    (hn : 0 < Fintype.card V) (hη : 0 < η) (hη1 : η ≤ 1)
    (hδ : 0 ≤ δ) (hTol : 2*(ε+δ) ≤ η)
    (hCut : (Fintype.card V:ℝ)*ε ≤ r)
    (hDegree : ((k+2*r : ℕ):ℝ) ≤ (d-ε)*(Fintype.card V:ℝ))
    (hRect : (k:ℝ) ≤ (d-2*ε)*(Fintype.card V:ℝ))
    (hLoss : (d+ε)*(Fintype.card V:ℝ) ≤ (k:ℝ)+loss)
    (hBudget : (loss:ℝ) ≤ δ*((Fintype.card V:ℝ)*η)) :
    ∃ F : Digraph V, F ≤ D ∧ IsCentredSuperregular F η ((k:ℝ)/Fintype.card V) ∧
      ∀ v, inDegree F v = k ∧ outDegree F v = k := by
  let n := Fintype.card V
  let b : ℝ := (k:ℝ)/n
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hb : b*n = k := div_mul_cancel₀ _ hn'.ne'
  have hIncl : b ≤ d-2*ε := (div_le_iff₀ hn').mpr hRect
  have hPair := (centred_superregular_iff_pair_univ D ε d).mp hG
  obtain ⟨_,_,hLarge⟩ := IsSuperregularPair.physical_lower_bounds D univ univ d ε hPair
  obtain ⟨F,hFD,hOut,hIn⟩ := exists_demands_of_dense_pair D r k k b (fun _ => k) (fun _ => k)
    (div_nonneg (Nat.cast_nonneg _) hn'.le)
    (by omega) (by rw [mul_assoc,hb]; linarith only [Nat.cast_nonneg (α := ℝ) k]) (by rw [hb])
    (by rw [hb]; simp)
    (by
      intro v
      have hv := (abs_le.mp (hG.2 v).2).1
      exact_mod_cast (show ((k+2*r:ℕ):ℝ) ≤ outDegree D v by
        linarith only [hDegree,hv])
    )
    (by
      intro v
      have hv := (abs_le.mp (hG.2 v).1).1
      exact_mod_cast (show ((k+2*r:ℕ):ℝ) ≤ inDegree D v by
        linarith only [hDegree,hv])
    )
    (by
      intro X Y hX hY
      have hX' : (r:ℝ) ≤ X.card := by exact_mod_cast hX
      have hY' : (r:ℝ) ≤ Y.card := by exact_mod_cast hY
      have hS : (((univ : Finset V).card:ℝ)*ε) ≤ r := by
        simpa only [card_univ] using hCut
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hIncl (Nat.cast_nonneg _)) (Nat.cast_nonneg _)).trans
        (hLarge X (subset_univ _) Y (subset_univ _) (hS.trans hX') (hS.trans hY')))
    (fun _ => ⟨le_rfl,le_rfl⟩) (fun _ => ⟨le_rfl,le_rfl⟩) rfl
  let H := D \ F
  have hHD : H ≤ D := fun _ _ hx => hx.1
  have hDelete : D \ H = F := by
    ext x y
    exact ⟨fun he => by
      by_contra hn
      exact he.2 ⟨he.1,hn⟩,fun he => ⟨hFD he,fun hh => hh.2 he⟩⟩
  have hBound (v : V) : inDegree H v ≤ loss := by
    have hPay := (residual_semidegrees D F hFD v).1
    rw [hIn] at hPay
    have hPay' : (inDegree H v:ℝ)+(k:ℝ) = inDegree D v := by exact_mod_cast hPay
    have hv := (abs_le.mp (hG.2 v).1).2
    exact_mod_cast (show (inDegree H v:ℝ) ≤ loss by linarith only [hPay',hLoss,hv])
  have hScale : (((univ : Finset V).card:ℝ)*ε) ≤ ((univ : Finset V).card:ℝ)*η :=
    mul_le_mul_of_nonneg_left (by linarith only [hTol,hδ,hη]) (Nat.cast_nonneg _)
  have hNon : (univ : Finset V).Nonempty := card_pos.mp (by simpa only [card_univ] using hn)
  have hUniform := (uniform_on_pair_remainder D H hHD univ univ univ univ
    (subset_refl _) (subset_refl _) hNon hNon ε η δ loss hη hη1 hScale hScale hTol
    (by simpa only [card_univ] using hBudget) hδ (fun v _ => hBound v) hG.1.1).1
  rw [hDelete] at hUniform
  have hDen : density F univ univ = b := by
    unfold density
    have hCount : incidences F univ univ = n*k := by
      change (∑ y, inDegree F y) = _
      simp only [hIn,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,n]
    rw [hCount,card_univ,Nat.cast_mul]
    change (n:ℝ)*k/((n:ℝ)*n) = b
    rw [mul_div_mul_left _ _ hn'.ne']
  refine ⟨F,hFD,⟨⟨hUniform,?_⟩,?_⟩,fun v => ⟨hIn v,hOut v⟩⟩
  · rw [hDen,sub_self,abs_zero]
    exact hη.le
  · intro v
    change |(inDegree F v:ℝ)-b*n| ≤ η*n ∧ |(outDegree F v:ℝ)-b*n| ≤ η*n
    rw [hIn,hOut,hb,sub_self,abs_zero]
    exact ⟨mul_nonneg hη.le hn'.le,mul_nonneg hη.le hn'.le⟩

/-- Sample to the desired nearby density before enforcing exact
degrees. The lower order threshold depends only on the sampling
accuracy and is uniform over the sampling fraction. -/
theorem exists_sampled_regular_superregular_cycle_pair (ε₀ ε η δ : ℝ)
    (hε₀ : 0 ≤ ε₀) (hSmall : ε₀ ≤ ε/4) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ) (hTol : 2*(ε+δ) ≤ η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V) (k r loss : ℕ) (d d' : ℝ),
      N ≤ Fintype.card V → 0 < d' → d' ≤ d → IsCentredSuperregular D ε₀ d →
      ((Fintype.card V:ℝ)*ε ≤ r) →
      (((k+2*r : ℕ):ℝ) ≤ (d'-ε)*(Fintype.card V:ℝ)) →
      ((k:ℝ) ≤ (d'-2*ε)*(Fintype.card V:ℝ)) →
      ((d'+ε)*(Fintype.card V:ℝ) ≤ (k:ℝ)+loss) →
      ((loss:ℝ) ≤ δ*((Fintype.card V:ℝ)*η)) →
      ∃ F : Digraph V, F ≤ D ∧ IsCentredSuperregular F η ((k:ℝ)/Fintype.card V) ∧
        ∀ v, inDegree F v = k ∧ outDegree F v = k := by
  obtain ⟨N,hN⟩ := exists_equal_fraction_arc_partition_uniform.{u} (ε^3/4) (by positivity)
  refine ⟨max N 1,?_⟩
  intro W _ D k r loss d d' hn hd' hd'le hD hCut hDegree hRect hLoss hBudget
  have hn' : 0 < Fintype.card W := (le_max_right N 1).trans hn
  let p := d'/d
  have hd : 0 < d := hd'.trans_le hd'le
  have hp : 0 < p := div_pos hd' hd
  have hp1 : p ≤ 1 := (div_le_one hd).mpr hd'le
  have hpd : p*d = d' := div_mul_cancel₀ _ hd.ne'
  obtain ⟨B,R,hTrack,_,_,_,hCover⟩ :=
    hN 1 p hp (by simpa only [Nat.cast_one,one_mul] using hp1)
      D ((le_max_left N 1).trans hn)
  have hBD : B 0 ≤ D := fun x y h => (hCover x y).mpr (Or.inr ⟨0,h⟩)
  have hTr : TracksArcStatistics (B 0) D p (ε^3/4) := by
    simpa only [Nat.cast_one,one_mul] using hTrack 0
  have hDg := typical_semidegrees_of_tracking (d := d) hTr hp.le hp1 hε₀ hSmall hε hε1 le_rfl
  have hB : IsCentredSuperregular (B 0) ε d' := by
    rw [←hpd]
    exact ⟨centred_regular_of_tracking hTr hp.le hp1 hD.1 hε₀ hSmall hε hε1 le_rfl hn',
      fun v => ⟨hDg.1 v (hD.2 v).1,hDg.2 v (hD.2 v).2⟩⟩
  obtain ⟨F,hFB,hF,hReg⟩ := exists_regular_superregular_cycle_pair (B 0) k r loss ε η d' δ
    hB hn' hη hη1 hδ hTol hCut hDegree hRect hLoss hBudget
  exact ⟨F,hFB.trans hBD,hF,hReg⟩

end OverfullWork.DirectedRobustExpansion
