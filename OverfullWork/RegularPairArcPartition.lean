module

public import OverfullWork.DirectedMultiwaySplit
public import OverfullWork.DirectedRegularPairs

@[expose] public section


/-! Osthus–Staden Lemma 3.7 for equal-density reserves. Independently
indexed left and right cells use the same vertex label type. -/
namespace OverfullWork.DirectedRegularPairs
open Finset DirectedRobustExpansion
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

def IsCentredRegular (D : Digraph V) (ε d : ℝ) : Prop :=
  IsUniform D ε univ univ ∧ |density D univ univ-d| ≤ ε

theorem density_error_of_tracking {D H : Digraph V} {p η δ : ℝ}
    (h : TracksArcStatistics H D p η) (hδ : 0 < δ) (hn : 0 < Fintype.card V)
    (hη : η ≤ δ^3/4) (A B : Finset V)
    (hA : δ*(Fintype.card V:ℝ) ≤ (A.card:ℝ)) (hB : δ*(Fintype.card V:ℝ) ≤ (B.card:ℝ)) :
    |density H A B-p*density D A B| ≤ δ/4 := by
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
  have hs : 0 < (A.card:ℝ)*(B.card:ℝ) :=
    mul_pos ((mul_pos hδ hnR).trans_le hA) ((mul_pos hδ hnR).trans_le hB)
  have hh := h (.inr (.inr (A,B)))
  change |(incidences H A B:ℝ)-p*(incidences D A B:ℝ)| ≤ η*(Fintype.card V:ℝ)^2 at hh
  unfold density
  rw [←mul_div_assoc,←sub_div,abs_div,abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  have hArea := mul_le_mul hA hB (mul_nonneg hδ.le hnR.le) (Nat.cast_nonneg A.card)
  have hCost := mul_le_mul_of_nonneg_right hη (sq_nonneg (Fintype.card V:ℝ))
  have hScale := mul_le_mul_of_nonneg_left hArea (show 0 ≤ δ/4 by positivity)
  nlinarith only [hh,hCost,hScale]

theorem centred_regular_of_tracking {D H : Digraph V} {p η ε δ d : ℝ}
    (hTracking : TracksArcStatistics H D p η) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hD : IsCentredRegular D ε d) (hε : 0 ≤ ε) (hSmall : ε ≤ δ/4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ δ^3/4) (hn : 0 < Fintype.card V) :
    IsCentredRegular H δ (p*d) := by
  have hSpan : δ*(Fintype.card V:ℝ) ≤ ((univ : Finset V).card:ℝ) := by
    simpa using mul_le_of_le_one_left (Nat.cast_nonneg (Fintype.card V) : 0 ≤ (_:ℝ)) hδ1
  have hFull := density_error_of_tracking hTracking hδ hn hη univ univ hSpan hSpan
  constructor
  · intro A hA B hB ha hb
    have hεδ : ε ≤ δ := by linarith only [hSmall,hδ]
    have h₀ := mul_le_mul_of_nonneg_left hεδ (Nat.cast_nonneg ((univ : Finset V).card) : 0 ≤ (_:ℝ))
    have hOld := hD.1 A hA B hB (h₀.trans ha) (h₀.trans hb)
    have hAB := density_error_of_tracking hTracking hδ hn hη A B
      (by simpa [mul_comm] using ha) (by simpa [mul_comm] using hb)
    have hScaled : |p*(density D A B-density D univ univ)| ≤ ε := by
      rw [abs_mul,abs_of_nonneg hp]
      exact (mul_le_mul_of_nonneg_left hOld.le hp).trans (mul_le_of_le_one_left hε hp1)
    have hTri := abs_add_le (density H A B-p*density D A B)
      (p*(density D A B-density D univ univ))
    have hTri' := abs_sub_le (density H A B) (p*density D univ univ) (density H univ univ)
    rw [abs_sub_comm (p*density D univ univ)] at hTri'
    have he : (density H A B-p*density D A B)+p*(density D A B-density D univ univ) =
        density H A B-p*density D univ univ := by ring
    rw [he] at hTri
    linarith only [hTri,hTri',hFull,hAB,hScaled,hSmall,hδ]
  · have hScaled : |p*(density D univ univ-d)| ≤ ε := by
      rw [abs_mul,abs_of_nonneg hp]
      exact (mul_le_mul_of_nonneg_left hD.2 hp).trans (mul_le_of_le_one_left hε hp1)
    have hh := abs_add_le (density H univ univ-p*density D univ univ) (p*(density D univ univ-d))
    rw [show density H univ univ-p*density D univ univ+p*(density D univ univ-d) =
      density H univ univ-p*d by ring] at hh
    linarith only [hh,hFull,hScaled,hSmall,hδ]

theorem typical_semidegrees_of_tracking {D H : Digraph V} {p η ε δ d : ℝ}
    (hTrack : TracksArcStatistics H D p η) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) (hSmall : ε ≤ δ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ δ^3/4) :
    (∀ v, |(inDegree D v:ℝ)-d*(Fintype.card V:ℝ)| ≤ ε*(Fintype.card V:ℝ) →
      |(inDegree H v:ℝ)-(p*d)*(Fintype.card V:ℝ)| ≤ δ*(Fintype.card V:ℝ)) ∧
    (∀ v, |(outDegree D v:ℝ)-d*(Fintype.card V:ℝ)| ≤ ε*(Fintype.card V:ℝ) →
      |(outDegree H v:ℝ)-(p*d)*(Fintype.card V:ℝ)| ≤ δ*(Fintype.card V:ℝ)) := by
  have hδ3 : δ^3 ≤ δ := by
    have h := mul_le_mul_of_nonneg_left hδ1 (sq_nonneg δ)
    have hh := mul_le_mul_of_nonneg_left hδ1 hδ.le
    nlinarith only [h,hh]
  have hAdd {x y : ℝ} (h1 : |x-p*y| ≤ η*(Fintype.card V:ℝ))
      (h2 : |y-d*(Fintype.card V:ℝ)| ≤ ε*(Fintype.card V:ℝ)) :
      |x-(p*d)*(Fintype.card V:ℝ)| ≤ δ*(Fintype.card V:ℝ) := by
    have h := abs_add_le (x-p*y) (p*(y-d*(Fintype.card V:ℝ)))
    rw [show x-p*y+p*(y-d*(Fintype.card V:ℝ)) = x-(p*d)*(Fintype.card V:ℝ) by ring,
      abs_mul,abs_of_nonneg hp] at h
    have hn := Nat.cast_nonneg (Fintype.card V) (α := ℝ)
    have h3 := (mul_le_mul_of_nonneg_left h2 hp).trans (mul_le_of_le_one_left (mul_nonneg hε hn) hp1)
    have h4 := mul_le_mul_of_nonneg_right (show η+ε ≤ δ by linarith only [hSmall,hδ3,hη,hδ]) hn
    nlinarith only [h,h1,h3,h4]
  exact ⟨fun v => hAdd (hTrack (.inl v)),fun v => hAdd (hTrack (.inr (.inl v)))⟩

/-- Split each regular pair into five thin reserves and the retained pair.
Typical semidegrees on each side remain typical in every part. -/
theorem exists_five_regular_arc_reserves (γ ε δ : ℝ) (hγ : 0 < γ) (hSum : 5*γ ≤ 1)
    (hε : 0 ≤ ε) (hSmall : ε ≤ δ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W] (D : Digraph W) (d : ℝ),
      N ≤ Fintype.card W → IsCentredRegular D ε d →
      ∃ F : Fin 5 → Digraph W, ∃ R : Digraph W,
        (∀ i, IsCentredRegular (F i) δ (γ*d)) ∧ IsCentredRegular R δ ((1-5*γ)*d) ∧
        (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ (∀ i, Disjoint (F i) R) ∧
        (∀ x y, D.Adj x y ↔ R.Adj x y ∨ ∃ i, (F i).Adj x y) ∧
        ∀ v,
          (|(inDegree D v:ℝ)-d*(Fintype.card W:ℝ)| ≤ ε*(Fintype.card W:ℝ) →
            (∀ i, |(inDegree (F i) v:ℝ)-(γ*d)*(Fintype.card W:ℝ)| ≤ δ*(Fintype.card W:ℝ)) ∧
            |(inDegree R v:ℝ)-((1-5*γ)*d)*(Fintype.card W:ℝ)| ≤ δ*(Fintype.card W:ℝ)) ∧
          (|(outDegree D v:ℝ)-d*(Fintype.card W:ℝ)| ≤ ε*(Fintype.card W:ℝ) →
            (∀ i, |(outDegree (F i) v:ℝ)-(γ*d)*(Fintype.card W:ℝ)| ≤ δ*(Fintype.card W:ℝ)) ∧
            |(outDegree R v:ℝ)-((1-5*γ)*d)*(Fintype.card W:ℝ)| ≤ δ*(Fintype.card W:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_equal_fraction_arc_partition.{u} 5 γ (δ^3/20) hγ (by simpa using hSum)
    (by positivity)
  refine ⟨max N 1,?_⟩
  intro W _ _ D d hn hD
  have hn' : 0 < Fintype.card W := (le_max_right N 1).trans hn
  obtain ⟨F,R,hF,hR,hDis,hSep,hParts⟩ := hN D ((le_max_left N 1).trans hn)
  have hErr : (5:ℝ)*(δ^3/20) ≤ δ^3/4 := by ring_nf; exact le_rfl
  have hγ1 : γ ≤ 1 := by linarith only [hγ,hSum]
  have hr0 : 0 ≤ 1-5*γ := by linarith only [hSum]
  have hr1 : 1-5*γ ≤ 1 := by linarith only [hγ]
  refine ⟨F,R,fun i => centred_regular_of_tracking (hF i) hγ.le hγ1 hD hε hSmall hδ hδ1 hErr hn',
    centred_regular_of_tracking hR hr0 hr1 hD hε hSmall hδ hδ1 hErr hn',hDis,hSep,hParts,?_⟩
  have hT := fun i => typical_semidegrees_of_tracking (d := d) (hF i) hγ.le hγ1 hε hSmall hδ hδ1 hErr
  have hRest := typical_semidegrees_of_tracking (d := d) hR hr0 hr1 hε hSmall hδ hδ1 hErr
  intro v
  exact ⟨fun hv => ⟨fun i => (hT i).1 v hv,hRest.1 v hv⟩,
    fun hv => ⟨fun i => (hT i).2 v hv,hRest.2 v hv⟩⟩

/-- Split a pair of centre density d into floor(d/β) disjoint β-pairs.
The order threshold is uniform over all original pair densities. -/
theorem exists_regular_clone_pairs (K : ℕ) (β ε δ : ℝ) (hβ : 0 < β)
    (hK : 1 ≤ (K:ℝ)*β) (hε : 0 ≤ ε) (hSmall : ε ≤ δ/4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W] (D : Digraph W) (d : ℝ),
      N ≤ Fintype.card W → IsCentredRegular D ε d → β ≤ d → d ≤ 1 →
      ∃ F : Fin ⌊d/β⌋₊ → Digraph W, ∃ R : Digraph W,
        (∀ i, IsCentredRegular (F i) δ β) ∧
        (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧ (∀ i, Disjoint (F i) R) ∧
        (∀ x y, D.Adj x y ↔ R.Adj x y ∨ ∃ i, (F i).Adj x y) ∧
        ∀ v,
          (|(inDegree D v:ℝ)-d*(Fintype.card W:ℝ)| ≤ ε*(Fintype.card W:ℝ) →
            ∀ i, |(inDegree (F i) v:ℝ)-β*(Fintype.card W:ℝ)| ≤ δ*(Fintype.card W:ℝ)) ∧
          (|(outDegree D v:ℝ)-d*(Fintype.card W:ℝ)| ≤ ε*(Fintype.card W:ℝ) →
            ∀ i, |(outDegree (F i) v:ℝ)-β*(Fintype.card W:ℝ)| ≤ δ*(Fintype.card W:ℝ)) := by
  let τ := δ^3/(4*((K:ℝ)+1))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨N,hN⟩ := exists_equal_fraction_arc_partition_uniform.{u} τ hτ
  refine ⟨max N 1,?_⟩
  intro W _ _ D d hn hD hβd hd
  let k := ⌊d/β⌋₊
  let p := β/d
  have hd0 : 0 < d := hβ.trans_le hβd
  have hp : 0 < p := div_pos hβ hd0
  have hp1 : p ≤ 1 := (div_le_one hd0).mpr hβd
  have hk : (k:ℝ) ≤ d/β := Nat.floor_le (by positivity)
  have hkd : (k:ℝ)*β ≤ d := (le_div_iff₀ hβ).mp hk
  have hSum : (k:ℝ)*p ≤ 1 := by
    dsimp [p]
    rw [←mul_div_assoc]
    exact (div_le_one hd0).mpr hkd
  have hkK : (k:ℝ) ≤ K := (mul_le_mul_iff_left₀ hβ).mp (by
    simpa only [mul_comm β] using hkd.trans (hd.trans hK))
  have hErr : (k:ℝ)*τ ≤ δ^3/4 := by
    dsimp only [τ]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 4*((K:ℝ)+1))).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hkK (pow_nonneg hδ.le 3),pow_nonneg hδ.le 3]
  have hCent : p*d = β := div_mul_cancel₀ _ hd0.ne'
  have hn' : 0 < Fintype.card W := (le_max_right N 1).trans hn
  obtain ⟨F,R,hF,_,hDis,hSep,hParts⟩ := hN k p hp hSum D ((le_max_left N 1).trans hn)
  refine ⟨F,R,?_,hDis,hSep,hParts,?_⟩
  · intro i
    simpa only [hCent] using centred_regular_of_tracking (hF i) hp.le hp1 hD hε hSmall hδ hδ1 hErr hn'
  · intro v
    have hT := fun i => typical_semidegrees_of_tracking (d := d) (hF i) hp.le hp1 hε hSmall hδ hδ1 hErr
    exact ⟨fun hv i => by simpa only [hCent] using (hT i).1 v hv,
      fun hv i => by simpa only [hCent] using (hT i).2 v hv⟩

end OverfullWork.DirectedRegularPairs
