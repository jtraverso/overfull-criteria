module

public import OverfullWork.OsthusStadenAdaptedRefinement
public import OverfullWork.OsthusStadenSlices

@[expose] public section


/-! Transfer the two minimum-degree estimates and density control to the
actual arc slices in Osthus–Staden §5.3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
variable {V : Type*} [Fintype V]

noncomputable def outProfile (D : Digraph V) (x : V) : Finset V :=
  univ.filter (D.Adj x)

noncomputable def inProfile (D : Digraph V) (y : V) : Finset V :=
  univ.filter (fun x => D.Adj x y)

/-- Superregularity of an oriented pair, including both degree deviations
about the same density parameter. -/
def IsSuperregularPair (D : Digraph V) (ε d : ℝ) (A B : Finset V) : Prop :=
  IsUniform D ε A B ∧ |density D A B-d| ≤ ε ∧
  (∀ x ∈ A, |profileCount B (outProfile D x)-d*(B.card : ℝ)| ≤ ε*(B.card : ℝ)) ∧
  ∀ y ∈ B, |profileCount A (inProfile D y)-d*(A.card : ℝ)| ≤ ε*(A.card : ℝ)

omit [Fintype V] in
private theorem refined_degree_bound {J : Type*} {profiles : J → Finset V}
    {P A : Finset V} {k : ℕ} {ε θ d : ℝ} (j : J)
    (hP : |profileCount P (profiles j)-d*(P.card : ℝ)| ≤ ε*(P.card : ℝ))
    (hRef : UniformProfileCell profiles P A k θ) (hSize : P.card = k*A.card)
    (hk : 0 < k) (hθ : 0 ≤ θ) (hFloor : θ ≤ d-ε) :
    |profileCount A (profiles j)-d*(A.card : ℝ)| ≤ (ε+θ)*(A.card : ℝ) := by
  let q := profileCount P (profiles j)
  let a := profileCount A (profiles j)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hPcard : (P.card : ℝ) = (k : ℝ)*A.card := by exact_mod_cast hSize
  have hq : q ≤ (P.card : ℝ) := by
    change ((P ∩ profiles j).card : ℝ) ≤ P.card
    exact_mod_cast card_le_card (inter_subset_left (s₁ := P) (s₂ := profiles j))
  have hLarge : θ*(P.card : ℝ) ≤ q := by
    have h := mul_le_mul_of_nonneg_right hFloor (Nat.cast_nonneg P.card)
    linarith only [h,(abs_le.mp hP).1]
  have hSplit := hRef j hLarge
  have hDiv : (P.card : ℝ)/(k : ℝ) = A.card := by rw [hPcard,mul_div_cancel_left₀ _ hkR.ne']
  have hBase := div_le_div_of_nonneg_right hP hkR.le
  rw [mul_div_assoc,hDiv] at hBase
  have hStep := hSplit.trans (mul_le_mul_of_nonneg_left
    ((div_le_div_of_nonneg_right hq hkR.le).trans_eq hDiv) hθ)
  have hCenter : d*(P.card : ℝ)/(k : ℝ) = d*(A.card : ℝ) := by rw [mul_div_assoc,hDiv]
  change |a-d*(A.card : ℝ)| ≤ (ε+θ)*(A.card : ℝ)
  rw [show a-d*(A.card : ℝ) = (a-q/(k : ℝ))+(q-d*(P.card : ℝ))/(k : ℝ) by
    rw [sub_div,hCenter]; ring]
  apply (abs_add_le _ _).trans
  rw [abs_div,abs_of_pos hkR,add_mul]
  exact (add_le_add hStep hBase).trans_eq (add_comm _ _)

/-- Lemma 3.11(i) with explicit thresholds. Each side may be refined by
a different number of equal-sized cells. -/
theorem IsSuperregularPair.on_profile_cells (D : Digraph V) {P Q A B : Finset V}
    {ℓ k : ℕ} {ε θ η d : ℝ}
    (hPair : IsSuperregularPair D ε d P Q)
    (hA : A ⊆ P) (hB : B ⊆ Q)
    (hSizeA : P.card = ℓ*A.card) (hSizeB : Q.card = k*B.card)
    (hℓ : 0 < ℓ) (hk : 0 < k)
    (hRefA : UniformProfileCell (inProfile D) P A ℓ θ)
    (hRefB : UniformProfileCell (outProfile D) Q B k θ)
    (hθ : 0 ≤ θ) (hFloor : θ ≤ d-ε)
    (hη : max (2*ε) (ε+θ) ≤ η) (hη1 : η ≤ 1)
    (hLeft : (P.card : ℝ)*ε ≤ (A.card : ℝ)*η)
    (hRight : (Q.card : ℝ)*ε ≤ (B.card : ℝ)*η) :
    IsSuperregularPair D η d A B := by
  have hALarge := hLeft.trans (mul_le_of_le_one_right (Nat.cast_nonneg A.card) hη1)
  have hBLarge := hRight.trans (mul_le_of_le_one_right (Nat.cast_nonneg B.card) hη1)
  have hηReg : 2*ε ≤ η := (le_max_left _ _).trans hη
  have hηDeg : ε+θ ≤ η := (le_max_right _ _).trans hη
  refine ⟨uniform_on_subcells D hPair.1 hA hB hALarge hBLarge hLeft hRight hηReg,?_,?_,?_⟩
  · rw [show density D A B-d = (density D A B-density D P Q)+(density D P Q-d) by ring]
    have hDensity := add_le_add (hPair.1 A hA B hB hALarge hBLarge).le hPair.2.1
    exact (abs_add_le _ _).trans (hDensity.trans (by linarith only [hηReg]))
  · intro x hx
    exact (refined_degree_bound x (hPair.2.2.1 x (hA hx)) hRefB hSizeB hk hθ hFloor).trans
      (mul_le_mul_of_nonneg_right hηDeg (Nat.cast_nonneg B.card))
  · intro y hy
    exact (refined_degree_bound y (hPair.2.2.2 y (hB hy)) hRefA hSizeA hℓ hθ hFloor).trans
      (mul_le_mul_of_nonneg_right hηDeg (Nat.cast_nonneg A.card))

private theorem profileCount_filter (A : Finset V) (P : V → Prop) : profileCount A (univ.filter P) = ((A.filter P).card : ℝ) := by
  have he : A ∩ (univ.filter P) = A.filter P := by
    ext x
    simp
  simp only [profileCount,he]

/-- Physical slices preserve superregularity on any selected pair of
aligned cells. Together with disjointness this gives the pair property
used in Red7 before the exceptional-edge steps. -/
theorem superregular_unwoundSlice_pair {U : Type*} {r s p : ℕ}
    (copy : Fin r → U → Digraph V) (label : Fin r → V → Option (RefinedVertex U s p))
    (F : RefinedFactorIndex r s p → Equiv.Perm (RefinedVertex U s p))
    (j : RefinedFactorIndex r s p) (a : RefinedVertex U s p) (A B : Finset V) (ε d : ℝ)
    (hA : ∀ v ∈ A, label j.1 v = some a)
    (hB : ∀ v ∈ B, label j.1 v = some (F j a))
    (hR : IsSuperregularPair (copy j.1 a.1.1) ε d A B) :
    IsSuperregularPair (unwoundSlice copy label F j) ε d A B := by
  obtain ⟨hU, hD⟩ := uniform_unwoundSlice_pair copy label F j a A B ε hA hB hR.1
  refine ⟨hU,hD ▸ hR.2.1,?_,?_⟩
  · intro x hx
    have he : (B.filter ((unwoundSlice copy label F j).Adj x)) =
        (B.filter ((copy j.1 a.1.1).Adj x)) := by
      ext y
      simp only [mem_filter]
      exact and_congr_right (fun hy => unwoundSlice_pair copy label F j a (hA x hx) (hB y hy))
    unfold outProfile
    rw [profileCount_filter,he,← profileCount_filter]
    exact hR.2.2.1 x hx
  · intro y hy
    have he : (A.filter (fun x => (unwoundSlice copy label F j).Adj x y)) =
        (A.filter (fun x => (copy j.1 a.1.1).Adj x y)) := by
      ext x
      simp only [mem_filter]
      exact and_congr_right (fun hx => unwoundSlice_pair copy label F j a (hA x hx) (hB y hy))
    unfold inProfile
    rw [profileCount_filter,he,← profileCount_filter]
    exact hR.2.2.2 y hy

end OverfullWork.DirectedRobustExpansion
