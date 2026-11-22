module

public import OverfullWork.KuhnOsthusCodegreeSampling
public import OverfullWork.KuhnOsthusSparseSuccessorPairs
public import OverfullWork.RegularPairArcPartition

@[expose] public section


/-! The sparse thinning needed in Lemmas 4.10(i)–(ii) and 8.2.
Uniform control of all rectangles is obtained directly from the finite
exponential budget, alongside the degree and codegree estimates. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

/-- An absolute cut tracking bound implies relative regularity on
rectangles above a prescribed size. -/
theorem relative_regularity_of_arc_tracking {V : Type u} [Fintype V]
    (D H : Digraph V) (d δ p ε η : ℝ)
    (hV : 0 < Fintype.card V) (hd : 0 < d) (hp : 0 ≤ p) (hε : 0 < ε)
    (hδε : δ ≤ ε) (hRel : 4*δ ≤ ε*d) (hCut : η ≤ ε^3*(p*d)/2)
    (hReg : IsCentredRegular D δ d)
    (hR : ∀ X Y : Finset V, |(incidences H X Y:ℝ)-p*(incidences D X Y:ℝ)| ≤
      η*(Fintype.card V:ℝ)^2) :
    ∀ X Y : Finset V, ε*(Fintype.card V:ℝ) ≤ (X.card:ℝ) →
      ε*(Fintype.card V:ℝ) ≤ (Y.card:ℝ) →
      |(incidences H X Y:ℝ)-(p*d)*(X.card:ℝ)*(Y.card:ℝ)| ≤
        ε*(p*d)*(X.card:ℝ)*(Y.card:ℝ) := by
  let n : ℝ := Fintype.card V
  have hn0 : 0 < n := by
    dsimp only [n]
    exact_mod_cast hV
  intro X Y hx hy
  let q : ℝ := (X.card:ℝ)*(Y.card:ℝ)
  have hPos : 0 < q := mul_pos ((mul_pos hε hn0).trans_le hx) ((mul_pos hε hn0).trans_le hy)
  have hArea : (ε*n)^2 ≤ q := by
    have h := mul_le_mul hx hy (mul_nonneg hε.le hn0.le) (Nat.cast_nonneg X.card)
    simpa only [pow_two,q] using h
  have hRisk : η*n^2 ≤ (ε*(p*d)/2)*q := by
    have h₁ := mul_le_mul_of_nonneg_right hCut (sq_nonneg n)
    have h₂ := mul_le_mul_of_nonneg_left hArea (show 0 ≤ ε*(p*d)/2 by positivity)
    linarith only [h₁,h₂]
  have hSmall : δ*n ≤ ε*n := mul_le_mul_of_nonneg_right hδε hn0.le
  have hRaw := (hReg.1 X (subset_univ _) Y (subset_univ _)
    (by simpa only [card_univ,mul_comm] using hSmall.trans hx)
    (by simpa only [card_univ,mul_comm] using hSmall.trans hy)).le
  have hHost : |density D X Y-d| ≤ ε*d/2 := by
    exact (abs_sub_le (density D X Y) (density D univ univ) d).trans
      ((add_le_add hRaw hReg.2).trans (by linarith only [hRel]))
  have hHost' : |(incidences D X Y:ℝ)-d*q| ≤ (ε*d/2)*q := by
    have h := mul_le_mul_of_nonneg_right hHost hPos.le
    have he : (density D X Y-d)*q = (incidences D X Y:ℝ)-d*q := by
      change ((incidences D X Y:ℝ)/q-d)*q = _
      field_simp [hPos.ne']
    rw [←abs_of_pos hPos,←abs_mul,he,abs_of_pos hPos] at h
    exact h
  have hTrack := (hR X Y).trans hRisk
  have hScaled := mul_le_mul_of_nonneg_left hHost' hp
  have he : (incidences H X Y:ℝ)-(p*d)*q =
      ((incidences H X Y:ℝ)-p*(incidences D X Y:ℝ)) + p*((incidences D X Y:ℝ)-d*q) := by ring
  have hTri := abs_add_le ((incidences H X Y:ℝ)-p*(incidences D X Y:ℝ))
    (p*((incidences D X Y:ℝ)-d*q))
  rw [←he,abs_mul,abs_of_nonneg hp] at hTri
  change |(incidences H X Y:ℝ)-(p*d)*(X.card:ℝ)*(Y.card:ℝ)| ≤ _
  have hBound : |(incidences H X Y:ℝ)-(p*d)*q| ≤ ε*(p*d)*q := by
    linarith only [hTrack,hScaled,hTri]
  simpa only [q,mul_assoc] using hBound

/-- Thin a centred regular pair with edge fraction p. The degree
lower bound is available when the host is superregular. The rectangle,
maximum degree and codegree estimates require only regularity. -/
theorem exists_sparse_regular_pair_sample (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V)
      (d δ p ε : ℝ), N ≤ Fintype.card V →
      0 < d → 0 ≤ δ → 0 < p → p ≤ 1 → 0 < ε → δ ≤ ε →
      4*δ ≤ ε*d → δ ≤ d/4 →
      η ≤ ε^3*(p*d)/2 → η ≤ p/2 → η ≤ p^2 → η ≤ p*d/4 →
      IsCentredRegular D δ d →
      ∃ H : Digraph V, H ≤ D ∧
        SparseSuccessorPairBounds H (p*d) ε (2*d/3) 0 ∧
        (∀ v, (inDegree H v:ℝ) ≤ (3*p/2)*Fintype.card V ∧
          (outDegree H v:ℝ) ≤ (3*p/2)*Fintype.card V) ∧
        (∀ X Y : Finset V, ε*(Fintype.card V:ℝ) ≤ (X.card:ℝ) →
          ε*(Fintype.card V:ℝ) ≤ (Y.card:ℝ) →
          |(incidences H X Y:ℝ)-(p*d)*(X.card:ℝ)*(Y.card:ℝ)| ≤
            ε*(p*d)*(X.card:ℝ)*(Y.card:ℝ)) ∧
        ((∀ v, (d-δ)*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ) ∧
          (d-δ)*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
          SparseSuccessorPairBounds H (p*d) ε (2*d/3) (1/2)) := by
  obtain ⟨N,hN⟩ := exists_arc_sample_tracking_codegrees.{u} η hη
  refine ⟨max N 1,?_⟩
  intro V _ D d δ p ε hn hd hδ hp hp1 hε hδε hRel hδd hCut hDeg hCodeg hMin hReg
  obtain ⟨H,hSub,hI,hO,hR,hCI,hCO⟩ := hN D p hp.le hp1 ((le_max_left _ _).trans hn)
  let n : ℝ := Fintype.card V
  have hn0 : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < Fintype.card V from (le_max_right _ _).trans hn)
  have hUniform := relative_regularity_of_arc_tracking D H d δ p ε η
    (show 0 < Fintype.card V from (le_max_right _ _).trans hn) hd hp.le hε hδε hRel hCut hReg
    (fun X Y => (hR X Y).le)
  have hCodegBound (G : Digraph V) (x y : V) : (commonInNeighbours G x y:ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast (card_le_card (filter_subset _ _)).trans_eq (card_univ (α := V))
  have hScale : (p*d/(2*d/3))^2 = (3*p/2)^2 := by
    field_simp [hd.ne']
  have hCB {a b : ℝ} (hb : b ≤ n) (h : |a-p^2*b| < η*n) :
      a ≤ (p*d/(2*d/3))^2*n := by
    rw [hScale]
    have h₁ := (abs_lt.mp h).2
    have h₂ := mul_le_mul_of_nonneg_left hb (sq_nonneg p)
    have h₃ := mul_le_mul_of_nonneg_right hCodeg hn0.le
    have h₄ : 0 ≤ p^2*n := by positivity
    nlinarith only [h₁,h₂,h₃,h₄]
  have hCIn (x y : V) (hne : x ≠ y) := hCB (hCodegBound D x y) (hCI x y hne)
  have hCOut (x y : V) (hne : x ≠ y) :=
    hCB (hCodegBound (reverseArcs D) x y) (hCO x y hne)
  have hUP {a b : ℝ} (hb : b ≤ n) (h : |a-p*b| < η*n) : a ≤ (3*p/2)*n := by
    have h₁ := (abs_lt.mp h).2
    have h₂ := mul_le_mul_of_nonneg_left hb hp.le
    have h₃ := mul_le_mul_of_nonneg_right hDeg hn0.le
    linarith only [h₁,h₂,h₃]
  have hRLower (X Y : Finset V) (hx : ε*n ≤ (X.card:ℝ)) (hy : ε*n ≤ (Y.card:ℝ)) :
      (1-ε)*(p*d)*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences H X Y:ℝ) := by
    linarith only [(abs_le.mp (hUniform X Y hx hy)).1]
  refine ⟨H,hSub,⟨fun _ => by simp,fun _ => by simp,hCIn,hCOut,hRLower⟩,?_,hUniform,?_⟩
  · intro v
    have hi : (inDegree D v:ℝ) ≤ n := by
      dsimp only [n]
      exact_mod_cast DirectedArcSelection.inDegree_le D v
    have ho : (outDegree D v:ℝ) ≤ n := by
      dsimp only [n]
      exact_mod_cast DirectedArcSelection.outDegree_le D v
    exact ⟨hUP hi (hI v),hUP ho (hO v)⟩
  · intro hHost
    have hlo {a b : ℝ} (hb : (d-δ)*n ≤ b) (h : |a-p*b| < η*n) : (1/2)*(p*d)*n ≤ a := by
      have h₁ := (abs_lt.mp h).1
      have h₂ := mul_le_mul_of_nonneg_left hb hp.le
      have h₃ := mul_le_mul_of_nonneg_right hMin hn0.le
      have h₄ := mul_le_mul_of_nonneg_right hδd (show 0 ≤ p*n by positivity)
      linarith only [h₁,h₂,h₃,h₄]
    exact ⟨fun v => hlo (hHost v).1 (hI v),fun v => hlo (hHost v).2 (hO v),hCIn,hCOut,hRLower⟩

end OverfullWork.DirectedRobustExpansion
