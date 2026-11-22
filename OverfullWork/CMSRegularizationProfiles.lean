module

public import OverfullWork.CMSRegularizationOddCuts
public import OverfullWork.CompletionOffCentreBudget
public import OverfullWork.CanonicalPartitionStructure

@[expose] public section


/-! Quantitative support estimates used in CMS Claim 4.3 before
applying the regular multigraph theorem. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph OrderedCanonicalTransport
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each vertex between rank one and the given rank pays at least
the deficit of the latter vertex. -/
theorem rank_deficit_of_ordered_budget (D : MultiGraph V) (d n C : ℕ)
    (e : V ≃ Fin (n+1)) (a : V) (ha : e a = 0)
    (hOrder : ∀ v w, e v ≤ e w → D.degree v ≤ D.degree w)
    (hBudget : (∑ w ∈ univ.erase a, (d-D.degree w)) ≤ d+C) (v : V) :
    (e v).val*(d-D.degree v) ≤ d+C := by
  let S := (Ioc (0 : Fin (n+1)) (e v)).map e.symm.toEmbedding
  have hCard : S.card = (e v).val := by simp [S]
  have hSubset : S ⊆ univ.erase a := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hw
    refine mem_erase.mpr ⟨?_,mem_univ _⟩
    intro h
    have hh := congrArg e h
    change e (e.symm j) = e a at hh
    rw [e.apply_symm_apply,ha] at hh
    have hPos := (mem_Ioc.mp hj).1
    rw [hh] at hPos
    exact (lt_irrefl _) hPos
  calc
    _ = ∑ _ ∈ S, (d-D.degree v) := by simp [hCard]
    _ ≤ ∑ w ∈ S, (d-D.degree w) := by
      apply sum_le_sum
      intro w hw
      obtain ⟨j,hj,rfl⟩ := mem_map.mp hw
      apply Nat.sub_le_sub_left
      apply hOrder
      change e (e.symm j) ≤ e v
      rw [e.apply_symm_apply]
      exact (mem_Ioc.mp hj).2
    _ ≤ ∑ w ∈ univ.erase a, (d-D.degree w) :=
      sum_le_sum_of_subset_of_nonneg hSubset (fun _ _ _ => Nat.zero_le _)
    _ ≤ d+C := hBudget

/-- The ranked base support profile in the deficit alternative of
Claim 4.3, with one exceptional multiplicity row. -/
theorem ranked_support_of_star_budget (D : MultiGraph V) (d n C Y : ℕ)
    (e : V ≃ Fin (n+1)) (a : V) (ha : e a = 0)
    (hOrder : ∀ v w, e v ≤ e w → D.degree v ≤ D.degree w)
    (hD : ∀ v, D.degree v ≤ d) (hStar : D.IsStarAt a)
    (hBudget : (∑ w ∈ univ.erase a, (d-D.degree w)) ≤ d+C)
    (v : V) (hv : v ≠ a) (hY : D.mult s(a,v) ≤ Y) :
    ((((e v).val-1:ℕ):ℝ)/((e v).val:ℝ))*(d:ℝ)-
      ((C+Y:ℕ):ℝ) ≤ D.supportGraph.degree v := by
  let r := (e v).val
  have hr₁ : 1 ≤ r := by
    by_contra! h
    have hz : e v = 0 := by
      apply Fin.ext
      change r = 0
      omega
    exact hv (e.injective (hz.trans ha.symm))
  have hDef := rank_deficit_of_ordered_budget D d n C e a ha hOrder hBudget v
  have hSupport := D.star_degree_le_support_add a v hStar hv Y hY
  have hDef' : r*(d-D.degree v) ≤ d+C := hDef
  have hDegree : r*(d-D.degree v)+r*D.degree v = r*d := by
    rw [←Nat.mul_add,Nat.sub_add_cancel (hD v)]
  have hBefore : (r-1)*d+d = r*d := by
    calc
      _ = (r-1+1)*d := by ring
      _ = _ := by rw [Nat.sub_add_cancel hr₁]
  have hMul := Nat.mul_le_mul_left r hSupport
  have hC := Nat.mul_le_mul_right C hr₁
  have hCap : (r-1)*d ≤ r*(D.supportGraph.degree v+C+Y) := by
    nlinarith only [hDef',hDegree,hBefore,hMul,hC]
  have hR : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  change ((r-1:ℕ):ℝ)/(r:ℝ)*(d:ℝ)-((C+Y:ℕ):ℝ) ≤ D.supportGraph.degree v
  apply (sub_le_iff_le_add).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hR).mpr
  have hx : (((r-1:ℕ):ℝ))*(d:ℝ) ≤ (r:ℝ)*((D.supportGraph.degree v:ℝ)+(C:ℝ)+(Y:ℝ)) := by
    exact_mod_cast hCap
  push_cast
  nlinarith only [hx]

/-- Two distinct ordinary ranks yield the combined support margin
used to eliminate every small odd cut except a two-anchor triple. -/
theorem support_pair_of_ranked_bounds (D : MultiGraph V) (d t : ℕ) (E : ℝ) (a b : V)
    (rank : V → ℕ) (hInj : Function.Injective rank)
    (hRank : ∀ v, v ≠ a → v ≠ b → 2 ≤ rank v)
    (hSupport : ∀ v, v ≠ a → v ≠ b →
      (((rank v-1:ℕ):ℝ)/(rank v:ℝ))*(d:ℝ)-E ≤ D.supportGraph.degree v)
    (hMargin : 2*(t:ℝ)+2*E ≤ (d:ℝ)/6) :
    ∀ x y, x ≠ a → x ≠ b → y ≠ a → y ≠ b → x ≠ y →
      d+2*t ≤ D.supportGraph.degree x+D.supportGraph.degree y := by
  intro x y hxa hxb hya hyb hxy
  have hTwo (z : V) (hz : 2 ≤ rank z) : (1:ℝ)/2 ≤ ((rank z-1:ℕ):ℝ)/(rank z:ℝ) := by
    have hr : (0:ℝ) < rank z := by exact_mod_cast (show 0 < rank z by omega)
    have hsz : (2:ℝ) ≤ rank z := by exact_mod_cast hz
    apply (le_div_iff₀ hr).mpr
    rw [Nat.cast_sub (by omega : 1 ≤ rank z),Nat.cast_one]
    linarith only [hsz]
  have hThree (z : V) (hz : 3 ≤ rank z) : (2:ℝ)/3 ≤ ((rank z-1:ℕ):ℝ)/(rank z:ℝ) := by
    have hr : (0:ℝ) < rank z := by exact_mod_cast (show 0 < rank z by omega)
    have hsz : (3:ℝ) ≤ rank z := by exact_mod_cast hz
    apply (le_div_iff₀ hr).mpr
    rw [Nat.cast_sub (by omega : 1 ≤ rank z),Nat.cast_one]
    linarith only [hsz]
  have hRankX := hRank x hxa hxb
  have hRankY := hRank y hya hyb
  have hNe : rank x ≠ rank y := fun h => hxy (hInj h)
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  apply (Nat.cast_le (α := ℝ)).mp
  push_cast
  by_cases hX : 3 ≤ rank x
  · have hBig := mul_le_mul_of_nonneg_right (hThree x hX) hd
    have hRest := mul_le_mul_of_nonneg_right (hTwo y hRankY) hd
    linarith only [hBig,hRest,hSupport x hxa hxb,hSupport y hya hyb,hMargin]
  · have hY : 3 ≤ rank y := by omega
    have hBig := mul_le_mul_of_nonneg_right (hThree y hY) hd
    have hRest := mul_le_mul_of_nonneg_right (hTwo x hRankX) hd
    linarith only [hBig,hRest,hSupport x hxa hxb,hSupport y hya hyb,hMargin]

end OverfullWork.CanonicalRegularization
