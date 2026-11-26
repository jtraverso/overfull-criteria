module

public import OverfullWork.ChenShanIterationBase
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

/-- A degree test transfers through deletion. The four contributions
are the deletion budget, the sampling error, rounding, and the original
degree defect at the target scale. -/
theorem prefix_degree_after_deletion
    {m n s k K d before after D ε ξ β : ℝ}
    (hm : 0 < m) (hs : 0 ≤ s) (hsn : s ≤ n)
    (hε : 0 ≤ ε) (hξ : 0 ≤ ξ) (hRoundBudget : 1/2 ≤ ξ*n)
    (hAmbient : |d-D| ≤ ε*m)
    (hMean : |K/k*d-s/m*d| ≤ 1/2)
    (hSample : |before-K/k*d| ≤ ξ*s)
    (hAfter : after ≤ before) (hLost : before-after ≤ β*n) :
    |after-s/m*D| ≤ (ε+2*ξ+β)*n := by
  have hAmbientScaled : |s/m*d-s/m*D| ≤ ε*s := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (div_nonneg hs hm.le)]
    calc
      _ ≤ (s/m)*(ε*m) := mul_le_mul_of_nonneg_left hAmbient (div_nonneg hs hm.le)
      _ = ε*s := by field_simp
  have hSampling := abs_le.mp hSample
  have hRounding := abs_le.mp hMean
  have hScaling := abs_le.mp hAmbientScaled
  have hεs := mul_le_mul_of_nonneg_left hsn hε
  have hξs := mul_le_mul_of_nonneg_left hsn hξ
  exact abs_le.mpr ⟨by linarith only [hSampling.1,hRounding.1,hScaling.1,hLost,
      hRoundBudget,hεs,hξs], by
    linarith only [hSampling.2,hRounding.2,hScaling.2,hAfter,hLost,
      hRoundBudget,hεs,hξs]⟩

private theorem card_sub_le_incidentDegree
    {U V : Type*} (P Q : Finset U) (G : Finset (V × V)) (v : V)
    (f : U ↪ (V × V)) (hQ : Q ⊆ P)
    (hIncident : ∀ u, (f u).1 = v ∨ (f u).2 = v)
    (hLost : ∀ u ∈ P \ Q, f u ∈ G) :
    P.card-Q.card ≤ incidentDegree G v := by
  rw [← card_sdiff_of_subset hQ]
  unfold incidentDegree
  calc
    _ = ((P \ Q).map f).card := (card_map _).symm
    _ ≤ _ := by
      apply card_le_card
      intro e he
      obtain ⟨u,hu,rfl⟩ := mem_map.mp he
      exact mem_filter.mpr ⟨hLost u hu,hIncident u⟩

/-- One ordered class pair in (4.23). The map of neighbors to incident
arcs works in either orientation. The second conclusion also bounds
missing neighbors whenever the target size has the same center. -/
theorem residual_prefix_pair_degrees {A B V : Type*} [Fintype B]
    (E F : A → B → Prop) (v : A) (T : Finset B)
    (D : ℕ) (m n s : ℕ) (ε ξ β : ℝ)
    (Lost : Finset (V × V)) (source : V) (arc : B ↪ (V × V))
    (hm : 0 < m) (hs : s ≤ n)
    (hε : 0 ≤ ε) (hξ : 0 ≤ ξ) (hHalf : 1/2 ≤ ξ*n)
    (hAmbient : |((univ.filter (E v)).card : ℝ) - D| ≤ ε*m)
    (hMean : |((T.card : ℝ)/Fintype.card B)*((univ.filter (E v)).card : ℝ) -
      ((s:ℝ)/m)*((univ.filter (E v)).card : ℝ)| ≤ 1/2)
    (hSample : sampledDegreeError E v T ≤ ξ*s)
    (hSub : ∀ w ∈ T, F v w → E v w)
    (hIncident : ∀ w, (arc w).1 = source ∨ (arc w).2 = source)
    (hLost : ∀ w ∈ T, E v w → ¬ F v w → arc w ∈ Lost)
    (hBudget : (incidentDegree Lost source : ℝ) ≤ β*n) :
    |((T.filter (F v)).card : ℝ)-((s:ℝ)/m)*D| ≤ (4*ε+10*ξ+β)*n ∧
    (|((T.card : ℝ))-((s:ℝ)/m)*D| ≤ 1/2 →
      ((T.filter (fun w => ¬ F v w)).card : ℝ) ≤ (4*ε+10*ξ+β)*n) := by
  let P := T.filter (E v)
  let Q := T.filter (F v)
  have hQP : Q ⊆ P := fun w hw =>
    let ⟨hwT,hwF⟩ := mem_filter.mp hw
    mem_filter.mpr ⟨hwT,hSub w hwT hwF⟩
  have hP : (univ.filter (E v)) ∩ T = P := by
    ext w
    simp only [P,mem_inter,mem_filter,mem_univ,true_and,and_comm]
  have hSample' : |(P.card : ℝ)-((T.card : ℝ)/Fintype.card B)*
      ((univ.filter (E v)).card : ℝ)| ≤ ξ*s := by
    unfold sampledDegreeError at hSample
    simpa only [hP] using hSample
  have hCard : Q.card ≤ P.card := card_le_card hQP
  have hLostN := card_sub_le_incidentDegree P Q Lost source arc hQP hIncident (by
    intro w hw
    obtain ⟨hwP,hwQ⟩ := mem_sdiff.mp hw
    obtain ⟨hwT,hwE⟩ := mem_filter.mp hwP
    exact hLost w hwT hwE (fun hwF => hwQ (mem_filter.mpr ⟨hwT,hwF⟩)))
  have hDiff : (P.card : ℝ)-(Q.card : ℝ) ≤ (incidentDegree Lost source : ℝ) := by
    exact_mod_cast hLostN
  have hDegree := prefix_degree_after_deletion (by exact_mod_cast hm)
    (Nat.cast_nonneg _ : 0 ≤ (s:ℝ)) (by exact_mod_cast hs) hε hξ hHalf
    hAmbient hMean hSample' (by exact_mod_cast hCard) (hDiff.trans hBudget)
  have hεn := mul_nonneg hε (Nat.cast_nonneg (α := ℝ) n)
  have hξn := mul_nonneg hξ (Nat.cast_nonneg (α := ℝ) n)
  constructor
  · refine hDegree.trans ?_
    linarith only [hεn,hξn]
  · intro hSize
    have hPart := card_filter_add_card_filter_not (s := T) (F v)
    have hPartR : (Q.card : ℝ)+((T.filter (fun w => ¬ F v w)).card : ℝ) =
        T.card := by exact_mod_cast hPart
    linarith only [hPartR,(abs_le.mp hSize).2,(abs_le.mp hDegree).1,hHalf,hεn,hξn]

end OverfullWork.ChenShan
