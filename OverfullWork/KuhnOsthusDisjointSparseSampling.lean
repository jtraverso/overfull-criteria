module

public import OverfullWork.KuhnOsthusSparseReserveDeletion
public import OverfullWork.ThinReserveAssembly
public import OverfullWork.KuhnOsthusSparseSampling
public import OverfullWork.DirectedMultiwaySplit

@[expose] public section


/-! Ordered pairs used by both parts of the path extender are sampled
twice. The second part is drawn from the actual complement of the
first. Its nominal fraction is measured against the original pair. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u

/-- In each style cell, the sampled degrees are within the same
additive error used for the whole-cluster semidegrees. -/
def TracksStyleDegrees {V : Type*} [Fintype V] (H D : Digraph V) (p η : ℝ)
    (A B : Fin 50 → Finset V) : Prop :=
  ∀ v j, |(inNeighbours H (A j) v:ℝ)-p*(inNeighbours D (A j) v:ℝ)| ≤
      η*(Fintype.card V:ℝ) ∧
    |(outTo H (B j) v:ℝ)-p*(outTo D (B j) v:ℝ)| ≤ η*(Fintype.card V:ℝ)

/-- Two disjoint sparse reserves track their requested fractions
against the same host. Codegree bounds follow for both orientations. -/
theorem exists_disjoint_sparse_pair_samples_with_styles (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V) (p q : ℝ)
      (A B : Fin 50 → Finset V),
      N ≤ Fintype.card V → 0 ≤ p → p ≤ 1/4 → 0 ≤ q → p+q ≤ 1 →
      ∃ C R : Digraph V, C ≤ D ∧ R ≤ D ∧ Disjoint C R ∧
        TracksArcStatistics C D p η ∧ TracksArcStatistics R D q (η+η) ∧
        (∀ x y, x ≠ y →
          (commonInNeighbours C x y:ℝ) ≤ (p^2+η)*Fintype.card V ∧
          (commonInNeighbours (reverseArcs C) x y:ℝ) ≤ (p^2+η)*Fintype.card V ∧
          (commonInNeighbours R x y:ℝ) ≤ ((4*q/3)^2+η)*Fintype.card V ∧
          (commonInNeighbours (reverseArcs R) x y:ℝ) ≤ ((4*q/3)^2+η)*Fintype.card V) ∧
        TracksStyleDegrees C D p η A B := by
  obtain ⟨N₀,hN₀⟩ := exists_arc_sample_tracking_codegrees_and_styles.{u} η hη
  obtain ⟨N₁,hN₁⟩ := exists_arc_sample_tracking_codegrees.{u} η hη
  refine ⟨max N₀ N₁,?_⟩
  intro V _ D p q A B hn hp hpp hq hSum
  have hp1 : p ≤ 1 := by linarith
  have hRem : 0 < 1-p := by linarith
  let a := q/(1-p)
  have ha : 0 ≤ a := div_nonneg hq hRem.le
  have ha1 : a ≤ 1 := (div_le_one hRem).mpr (by linarith)
  have hAbnd : a ≤ 4*q/3 := by
    apply (div_le_iff₀ hRem).mpr
    have h := mul_le_mul_of_nonneg_right hpp hq
    nlinarith only [h]
  obtain ⟨C,hCD,hCI,hCO,hCR,hCcI,hCcO⟩ :=
    hN₀ D p (fun j => j.elim univ A) (fun j => j.elim univ B)
      hp hp1 ((le_max_left _ _).trans hn)
  obtain ⟨R,hRsub,hRI,hRO,hRR,hRcI,hRcO⟩ :=
    hN₁ (D \ C) a ha ha1 ((le_max_right _ _).trans hn)
  have hTrackC : TracksArcStatistics C D p η := by
    rintro (x | x | ⟨X,Y⟩)
    · exact (hCI x none).le
    · exact (hCO x none).le
    · exact (hCR X Y).le
  have hTrackR : TracksArcStatistics R (D \ C) a η := by
    rintro (x | x | ⟨X,Y⟩)
    · exact (hRI x).le
    · exact (hRO x).le
    · exact (hRR X Y).le
  have hTrack := TracksArcStatistics.comp (hTrackC.complement hCD) hTrackR ha ha1 hη.le
  have hEq : a*(1-p) = q := div_mul_cancel₀ q hRem.ne'
  rw [hEq] at hTrack
  have hD : D \ C ≤ D := fun _ _ h => h.1
  refine ⟨C,R,hCD,hRsub.trans hD,?_,hTrackC,hTrack,?_,
    fun v j => ⟨(hCI v (some j)).le,(hCO v (some j)).le⟩⟩
  · apply disjoint_iff_inf_le.mpr
    rintro x y ⟨hC,hR⟩
    exact (hRsub hR).2 hC
  · intro x y hxy
    let n : ℝ := Fintype.card V
    have hMax (G : Digraph V) : (commonInNeighbours G x y:ℝ) ≤ n := by
      dsimp only [n]
      exact_mod_cast (card_le_card (filter_subset _ _)).trans_eq (card_univ (α := V))
    have hBound {s t w : ℝ} (ht : 0 ≤ t) (h : |s-t^2*w| < η*n) (hw : w ≤ n) :
        s ≤ (t^2+η)*n := by
      have h' := (abs_lt.mp h).2
      have hM := mul_le_mul_of_nonneg_left hw (sq_nonneg t)
      linarith only [h',hM]
    have hq' : (a^2+η)*n ≤ ((4*q/3)^2+η)*n :=
      mul_le_mul_of_nonneg_right
        (by linarith only [pow_le_pow_left₀ ha hAbnd 2]) (by positivity)
    exact ⟨hBound hp (hCcI x y hxy) (hMax D),
      hBound hp (hCcO x y hxy) (hMax (reverseArcs D)),
      (hBound ha (hRcI x y hxy) (hMax (D \ C))).trans hq',
      (hBound ha (hRcO x y hxy) (hMax (reverseArcs (D \ C)))).trans hq'⟩


/-- Two disjoint sparse reserves track their requested fractions
against the same host. Codegree bounds follow for both orientations. -/
theorem exists_disjoint_sparse_pair_samples (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V) (p q : ℝ),
      N ≤ Fintype.card V → 0 ≤ p → p ≤ 1/4 → 0 ≤ q → p+q ≤ 1 →
      ∃ C R : Digraph V, C ≤ D ∧ R ≤ D ∧ Disjoint C R ∧
        TracksArcStatistics C D p η ∧ TracksArcStatistics R D q (η+η) ∧
        (∀ x y, x ≠ y →
          (commonInNeighbours C x y:ℝ) ≤ (p^2+η)*Fintype.card V ∧
          (commonInNeighbours (reverseArcs C) x y:ℝ) ≤ (p^2+η)*Fintype.card V ∧
          (commonInNeighbours R x y:ℝ) ≤ ((4*q/3)^2+η)*Fintype.card V ∧
          (commonInNeighbours (reverseArcs R) x y:ℝ) ≤ ((4*q/3)^2+η)*Fintype.card V) := by
  obtain ⟨N,hN⟩ := exists_disjoint_sparse_pair_samples_with_styles.{u} η hη
  refine ⟨N,?_⟩
  intro V _ D p q hn hp hpp hq hSum
  obtain ⟨C,R,hCD,hRD,hDis,hC,hR,hCodeg,_⟩ :=
    hN D p q (fun _ => univ) (fun _ => univ) hn hp hpp hq hSum
  exact ⟨C,R,hCD,hRD,hDis,hC,hR,hCodeg⟩

/-- The two sparse pairs for an ordered cluster pair shared by the
cycle reserve and the chord reserve. Their density fractions are
measured against the same original host. -/
theorem exists_disjoint_sparse_regular_reserves (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V) (d δ p q ε : ℝ),
      N ≤ Fintype.card V → 0 < d → 0 < p → p ≤ 1/4 → 0 < q → p+q ≤ 1 →
      0 < ε → δ ≤ ε → 4*δ ≤ ε*d → δ ≤ d/4 →
      η ≤ ε^3*(p*d)/2 → η+η ≤ ε^3*(q*d)/2 →
      η ≤ p/2 → η+η ≤ q → η ≤ p^2 → η ≤ q^2 → η ≤ p*d/4 →
      DirectedRegularPairs.IsCentredRegular D δ d →
      (∀ v, (d-δ)*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ) ∧
        (d-δ)*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ∃ C R : Digraph V, C ≤ D ∧ R ≤ D ∧ Disjoint C R ∧
        SparseSuccessorPairBounds C (p*d) ε (2*d/3) (1/2) ∧
        SparseSuccessorPairBounds R (q*d) ε (d/2) 0 ∧
        (∀ v, (inDegree C v:ℝ) ≤ (3*p/2)*Fintype.card V ∧
          (outDegree C v:ℝ) ≤ (3*p/2)*Fintype.card V ∧
          (inDegree R v:ℝ) ≤ 2*q*Fintype.card V ∧
          (outDegree R v:ℝ) ≤ 2*q*Fintype.card V) ∧
        (∀ X Y : Finset V, ε*(Fintype.card V:ℝ) ≤ (X.card:ℝ) →
          ε*(Fintype.card V:ℝ) ≤ (Y.card:ℝ) →
          |(incidences C X Y:ℝ)-(p*d)*(X.card:ℝ)*(Y.card:ℝ)| ≤
            ε*(p*d)*(X.card:ℝ)*(Y.card:ℝ) ∧
          |(incidences R X Y:ℝ)-(q*d)*(X.card:ℝ)*(Y.card:ℝ)| ≤
            ε*(q*d)*(X.card:ℝ)*(Y.card:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_disjoint_sparse_pair_samples.{u} η hη
  refine ⟨max N 1,?_⟩
  intro V _ D d δ p q ε hn hd hp hpUp hq hSum hε hδε hRel hδd
    hCutC hCutR hUpperC hUpperR hCodegC hCodegR hMin hHost hDegree
  obtain ⟨C,R,hCD,hRD,hDis,hTC,hTR,hCodeg⟩ :=
    hN D p q ((le_max_left _ _).trans hn) hp.le hpUp hq.le hSum
  have hV : 0 < Fintype.card V := (le_max_right _ _).trans hn
  let n : ℝ := Fintype.card V
  have hn0 : 0 < n := by dsimp only [n]; exact_mod_cast hV
  have hRegC := relative_regularity_of_arc_tracking D C d δ p ε η hV hd hp.le hε hδε hRel hCutC
    hHost (fun X Y => hTC (.inr (.inr (X,Y))))
  have hRegR := relative_regularity_of_arc_tracking D R d δ q ε (η+η) hV hd hq.le hε hδε hRel hCutR
    hHost (fun X Y => hTR (.inr (.inr (X,Y))))
  have hBoundC : (p^2+η)*n ≤ (p*d/(2*d/3))^2*n := by
    have he : p*d/(2*d/3) = 3*p/2 := by field_simp [hd.ne']
    rw [he]
    apply mul_le_mul_of_nonneg_right _ hn0.le
    nlinarith only [hCodegC,sq_nonneg p]
  have hBoundR : ((4*q/3)^2+η)*n ≤ (q*d/(d/2))^2*n := by
    have he : q*d/(d/2) = 2*q := by field_simp [hd.ne']
    rw [he]
    apply mul_le_mul_of_nonneg_right _ hn0.le
    nlinarith only [hCodegR,sq_nonneg q]
  have hLow {a b : ℝ} (hB : (d-δ)*n ≤ b) (h : |a-p*b| ≤ η*n) : (1/2)*(p*d)*n ≤ a := by
    have h₁ := (abs_le.mp h).1
    have h₂ := mul_le_mul_of_nonneg_left hB hp.le
    have h₃ := mul_le_mul_of_nonneg_right hMin hn0.le
    have h₄ := mul_le_mul_of_nonneg_right hδd (show 0 ≤ p*n by positivity)
    linarith only [h₁,h₂,h₃,h₄]
  have hHigh {a b f t u : ℝ} (hf : 0 ≤ f) (hb : b ≤ n)
      (h : |a-f*b| ≤ t*n) (hu : f+t ≤ u) : a ≤ u*n := by
    have h₁ := (abs_le.mp h).2
    have h₂ := mul_le_mul_of_nonneg_left hb hf
    have h₃ := mul_le_mul_of_nonneg_right hu hn0.le
    linarith only [h₁,h₂,h₃]
  have hC : SparseSuccessorPairBounds C (p*d) ε (2*d/3) (1/2) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro v
      exact hLow (hDegree v).1 (hTC (.inl v))
    · intro v
      exact hLow (hDegree v).2 (hTC (.inr (.inl v)))
    · intro x y he
      exact (hCodeg x y he).1.trans hBoundC
    · intro x y he
      exact (hCodeg x y he).2.1.trans hBoundC
    · intro X Y hx hy
      linarith only [(abs_le.mp (hRegC X Y hx hy)).1]
  have hR : SparseSuccessorPairBounds R (q*d) ε (d/2) 0 := by
    refine ⟨fun _ => by simp,fun _ => by simp,?_,?_,?_⟩
    · intro x y he
      exact (hCodeg x y he).2.2.1.trans hBoundR
    · intro x y he
      exact (hCodeg x y he).2.2.2.trans hBoundR
    · intro X Y hx hy
      linarith only [(abs_le.mp (hRegR X Y hx hy)).1]
  refine ⟨C,R,hCD,hRD,hDis,hC,hR,?_,fun X Y hx hy => ⟨hRegC X Y hx hy,hRegR X Y hx hy⟩⟩
  intro v
  have hi : (inDegree D v:ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast DirectedArcSelection.inDegree_le D v
  have ho : (outDegree D v:ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast DirectedArcSelection.outDegree_le D v
  exact ⟨hHigh hp.le hi (hTC (.inl v)) (by linarith only [hUpperC]),
    hHigh hp.le ho (hTC (.inr (.inl v))) (by linarith only [hUpperC]),
    hHigh hq.le hi (hTR (.inl v)) (by linarith only [hUpperR]),
    hHigh hq.le ho (hTR (.inr (.inl v))) (by linarith only [hUpperR])⟩


/-- Realize the two samples simultaneously in a family of physical
ordered pairs. A zero fraction leaves the corresponding pair empty,
so cycle and reduced supports can be prescribed independently. -/
theorem exists_sparse_reserve_unions_with_styles (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {V I : Type*}
      (a b : I → W ↪ V) (D : I → Digraph W) (p q : I → ℝ)
      (A B : I → Fin 50 → Finset W),
      N ≤ Fintype.card W →
      (∀ i, 0 ≤ p i ∧ p i ≤ 1/4 ∧ 0 ≤ q i ∧ p i+q i ≤ 1) →
      (∀ i j, i ≠ j → Disjoint (liftDirectedPair (a i) (b i) (D i))
        (liftDirectedPair (a j) (b j) (D j))) →
      ∃ C R : I → Digraph W,
        (∀ i, C i ≤ D i ∧ R i ≤ D i ∧
          (p i = 0 → C i = ⊥) ∧ (q i = 0 → R i = ⊥) ∧
          TracksArcStatistics (C i) (D i) (p i) η ∧
          TracksArcStatistics (R i) (D i) (q i) (η+η) ∧
          (∀ x y, x ≠ y →
            (commonInNeighbours (C i) x y:ℝ) ≤ ((p i)^2+η)*Fintype.card W ∧
            (commonInNeighbours (reverseArcs (C i)) x y:ℝ) ≤ ((p i)^2+η)*Fintype.card W ∧
            (commonInNeighbours (R i) x y:ℝ) ≤ ((4*q i/3)^2+η)*Fintype.card W ∧
            (commonInNeighbours (reverseArcs (R i)) x y:ℝ) ≤ ((4*q i/3)^2+η)*Fintype.card W) ∧
          TracksStyleDegrees (C i) (D i) (p i) η (A i) (B i)) ∧
        Disjoint (directedPairUnion a b C) (directedPairUnion a b R) ∧
        (directedPairUnion a b C ⊔ directedPairUnion a b R) ≤ directedPairUnion a b D := by
  obtain ⟨N,hN⟩ := exists_disjoint_sparse_pair_samples_with_styles.{u} η hη
  refine ⟨N,?_⟩
  intro W _ V I a b D p q A B hn hf hDis
  have hPick (i : I) := hN (D i) (p i) (q i) (A i) (B i) hn
    (hf i).1 (hf i).2.1 (hf i).2.2.1 (hf i).2.2.2
  choose F G hFD hGD hFG hF hG hCodeg hStyle using hPick
  let C i := if p i = 0 then (⊥ : Digraph W) else F i
  let R i := if q i = 0 then (⊥ : Digraph W) else G i
  have hFC (i : I) : C i ≤ F i := by dsimp [C]; split <;> simp
  have hGR (i : I) : R i ≤ G i := by dsimp [R]; split <;> simp
  have hCD (i : I) : C i ≤ D i := (hFC i).trans (hFD i)
  have hRD (i : I) : R i ≤ D i := (hGR i).trans (hGD i)
  have hC (i : I) : TracksArcStatistics (C i) (D i) (p i) η := by
    by_cases hp : p i = 0
    · rintro (x | x | ⟨X,Y⟩) <;>
        simp [C,hp,ArcStatistic.value,ArcStatistic.scale,inDegree,outDegree,inNeighbours,
          incidences,Digraph.bot_adj] <;> positivity
    · simpa only [C,if_neg hp] using hF i
  have hR (i : I) : TracksArcStatistics (R i) (D i) (q i) (η+η) := by
    by_cases hq : q i = 0
    · rintro (x | x | ⟨X,Y⟩) <;>
        simp [R,hq,ArcStatistic.value,ArcStatistic.scale,inDegree,outDegree,inNeighbours,
          incidences,Digraph.bot_adj] <;> positivity
    · simpa only [R,if_neg hq] using hG i
  have hCR (i : I) : Disjoint (C i) (R i) := (hFG i).mono (hFC i) (hGR i)
  refine ⟨C,R,?_,disjoint_directedPairUnions a b D C R hCD hRD hCR hDis,?_⟩
  · intro i
    refine ⟨hCD i,hRD i,fun hp => if_pos hp,fun hq => if_pos hq,hC i,hR i,?_,?_⟩
    · intro x y hxy
      obtain ⟨h₁,h₂,h₃,h₄⟩ := hCodeg i x y hxy
      have hFrev : reverseArcs (C i) ≤ reverseArcs (F i) := fun _ _ h => hFC i h
      have hGrev : reverseArcs (R i) ≤ reverseArcs (G i) := fun _ _ h => hGR i h
      have hMono {A B : Digraph W} (h : A ≤ B) :
          (commonInNeighbours A x y:ℝ) ≤ commonInNeighbours B x y := by
        exact_mod_cast commonInNeighbours_mono h x y
      exact ⟨(hMono (hFC i)).trans h₁,(hMono hFrev).trans h₂,
        (hMono (hGR i)).trans h₃,(hMono hGrev).trans h₄⟩
    · by_cases hp : p i = 0
      · intro v j
        simp [C,hp,inNeighbours,outTo,Digraph.bot_adj]
        positivity
      · simpa only [C,if_neg hp] using hStyle i
  · apply sup_le
    · rintro x y ⟨i,h⟩
      exact ⟨i,liftDirectedPair_mono _ _ (hCD i) h⟩
    · rintro x y ⟨i,h⟩
      exact ⟨i,liftDirectedPair_mono _ _ (hRD i) h⟩

/-- Realize the two samples simultaneously in a family of physical
ordered pairs. A zero fraction leaves the corresponding pair empty,
so cycle and reduced supports can be prescribed independently. -/
theorem exists_sparse_reserve_unions (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {V I : Type*}
      (a b : I → W ↪ V) (D : I → Digraph W) (p q : I → ℝ),
      N ≤ Fintype.card W →
      (∀ i, 0 ≤ p i ∧ p i ≤ 1/4 ∧ 0 ≤ q i ∧ p i+q i ≤ 1) →
      (∀ i j, i ≠ j → Disjoint (liftDirectedPair (a i) (b i) (D i))
        (liftDirectedPair (a j) (b j) (D j))) →
      ∃ C R : I → Digraph W,
        (∀ i, C i ≤ D i ∧ R i ≤ D i ∧
          (p i = 0 → C i = ⊥) ∧ (q i = 0 → R i = ⊥) ∧
          TracksArcStatistics (C i) (D i) (p i) η ∧
          TracksArcStatistics (R i) (D i) (q i) (η+η) ∧
          (∀ x y, x ≠ y →
            (commonInNeighbours (C i) x y:ℝ) ≤ ((p i)^2+η)*Fintype.card W ∧
            (commonInNeighbours (reverseArcs (C i)) x y:ℝ) ≤ ((p i)^2+η)*Fintype.card W ∧
            (commonInNeighbours (R i) x y:ℝ) ≤ ((4*q i/3)^2+η)*Fintype.card W ∧
            (commonInNeighbours (reverseArcs (R i)) x y:ℝ) ≤ ((4*q i/3)^2+η)*Fintype.card W)) ∧
        Disjoint (directedPairUnion a b C) (directedPairUnion a b R) ∧
        (directedPairUnion a b C ⊔ directedPairUnion a b R) ≤ directedPairUnion a b D := by
  obtain ⟨N,hN⟩ := exists_sparse_reserve_unions_with_styles.{u} η hη
  refine ⟨N,?_⟩
  intro W _ V I a b D p q hn hf hDis
  obtain ⟨C,R,hCR,hDis',hSub⟩ := hN a b D p q (fun _ _ => univ) (fun _ _ => univ) hn hf hDis
  refine ⟨C,R,?_,hDis',hSub⟩
  intro i
  obtain ⟨hCD,hRD,hC0,hR0,hC,hR,hCodeg,_⟩ := hCR i
  exact ⟨hCD,hRD,hC0,hR0,hC,hR,hCodeg⟩

end OverfullWork.DirectedRobustExpansion
