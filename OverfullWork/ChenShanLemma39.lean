module

public import OverfullWork.ChenShanBalancedColorTransfer
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

def sideCount (C : M.EdgeColoring k) (A : Finset V) (i : Fin k) : ℤ :=
  ∑ v ∈ A, ((C.colourGraph i).degree v : ℤ)

theorem sum_colour_degrees_at_vertex (C : M.EdgeColoring k) (v : V) :
    (∑ i, (C.colourGraph i).degree v) = M.degree v := by
  simp only [MultiGraph.degree,MultiGraph.EdgeColoring.colourGraph]
  rw [sum_comm]
  exact sum_congr rfl (fun e _ => C.sum_col e)

theorem colour_degree_of_saturated (C : M.EdgeColoring k) (v : V)
    (hv : M.degree v = k) (i : Fin k) : (C.colourGraph i).degree v = 1 := by
  have h : (∑ j, (C.colourGraph j).degree v) = ∑ _j : Fin k, (1 : ℕ) := by
    rw [sum_colour_degrees_at_vertex,hv]
    simp
  exact (sum_eq_sum_iff_of_le (fun j _ => C.colourGraph_degree_le_one j v)).mp h i (mem_univ _)

theorem sum_sideCount (C : M.EdgeColoring k) (A : Finset V) :
    (∑ i, sideCount C A i) = ∑ v ∈ A, (M.degree v : ℤ) := by
  unfold sideCount
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  exact_mod_cast sum_colour_degrees_at_vertex C v

private theorem sideCount_gap_even (C : M.EdgeColoring k) (A B : Finset V)
    (hAB : Disjoint A B) (hEven : Even ((A ∪ B)ᶜ.card))
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k) (i : Fin k) :
    Even (sideCount C A i - sideCount C B i) := by
  have hMass : sideCount C univ i = 2 * ((C.colourGraph i).edgeCount : ℤ) := by
    unfold sideCount
    exact_mod_cast (C.colourGraph i).sum_degrees_eq_twice_edgeCount
  have hZ : sideCount C (A ∪ B)ᶜ i = ((A ∪ B)ᶜ.card : ℤ) := by
    unfold sideCount
    rw [sum_congr rfl (fun v hv => show ((C.colourGraph i).degree v : ℤ) = 1 by
      rw [colour_degree_of_saturated C v (hSat v hv) i]; rfl)]
    simp
  have h := sum_add_sum_compl (A ∪ B) (fun v => ((C.colourGraph i).degree v : ℤ))
  rw [sum_union hAB] at h
  change sideCount C A i + sideCount C B i + sideCount C (A ∪ B)ᶜ i = sideCount C univ i at h
  obtain ⟨t,ht⟩ := hEven
  have ht' : (((A ∪ B)ᶜ.card : ℕ) : ℤ) = (t : ℤ) + t := by exact_mod_cast ht
  exact ⟨((C.colourGraph i).edgeCount : ℤ) - t - sideCount C B i,by omega⟩

private theorem two_colour_energy_drop (x y : Fin k → ℤ) (a b : Fin k)
    (hab : a ≠ b) (p : ℤ) (hp : 0 < p) (hgap : p < x a - x b)
    (ha : y a = x a - p) (hb : y b = x b + p)
    (hRest : ∀ i, i ≠ a → i ≠ b → y i = x i) :
    (∑ i, (y i)^2) < ∑ i, (x i)^2 := by
  have hPair : (y a)^2 + (y b)^2 < (x a)^2 + (x b)^2 := by
    rw [ha,hb]
    nlinarith only [mul_pos hp (sub_pos.mpr hgap)]
  have hSum (f : Fin k → ℤ) :
      (∑ i, f i) = f a + f b + ∑ i ∈ (univ.erase a).erase b, f i := by
    have hA := sum_erase_add univ f (mem_univ a)
    have hB := sum_erase_add (univ.erase a) f (mem_erase.mpr ⟨hab.symm,mem_univ b⟩)
    omega
  rw [hSum (fun i => (y i)^2),hSum (fun i => (x i)^2)]
  have h := sum_congr (s₁ := (univ.erase a).erase b) rfl (fun i hi => by
    rw [hRest i (mem_erase.mp (mem_erase.mp hi).2).1 (mem_erase.mp hi).1] :
    ∀ i ∈ (univ.erase a).erase b, (y i)^2 = (x i)^2)
  omega

private theorem exists_minimum_energy
    (C : M.EdgeColoring k) (P : M.EdgeColoring k → Prop) (hP : P C)
    (energy : M.EdgeColoring k → ℤ) (hNonneg : ∀ D, 0 ≤ energy D) :
    ∃ D, P D ∧ ∀ F, P F → energy D ≤ energy F := by
  let Q (n : ℕ) := ∃ D, P D ∧ (energy D).toNat = n
  have hQ : ∃ n, Q n := ⟨(energy C).toNat,C,hP,rfl⟩
  obtain ⟨D,hD,hE⟩ := Nat.find_spec hQ
  refine ⟨D,hD,fun F hF => ?_⟩
  have h := Nat.find_min' hQ (show Q (energy F).toNat from ⟨F,hF,rfl⟩)
  have hd := hNonneg D
  have hf := hNonneg F
  omega

private theorem sideCount_after_swap
    (C : M.EdgeColoring k) (a b : Fin k) (S A : Finset V)
    (hclosed : ∀ u v, 0 < C.col s(u,v) a + C.col s(u,v) b → (u ∈ S ↔ v ∈ S))
    (_hab : a ≠ b) :
    let D := C.swapClosed a b S hclosed
    let p := sideCount C (A ∩ S) a - sideCount C (A ∩ S) b
    sideCount D A a = sideCount C A a - p ∧
    sideCount D A b = sideCount C A b + p ∧
    ∀ i, i ≠ a → i ≠ b → sideCount D A i = sideCount C A i := by
  intro D p
  refine ⟨?_,?_,?_⟩
  · have h := swap_closed_side_degree C a b a S A hclosed
    rw [Equiv.swap_apply_left,sum_sub_distrib] at h
    dsimp only [D,p,sideCount]
    linarith only [h]
  · have h := swap_closed_side_degree C a b b S A hclosed
    rw [Equiv.swap_apply_right,sum_sub_distrib] at h
    dsimp only [D,p,sideCount]
    linarith only [h]
  · intro i hi hj
    have h := swap_closed_side_degree C a b i S A hclosed
    rw [Equiv.swap_apply_of_ne_of_ne hi hj] at h
    simpa only [sub_self,sum_const_zero,add_zero,sideCount,D] using h

private theorem outside_side_degrees_agree (C : M.EdgeColoring k) (A B : Finset V)
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k) (a b : Fin k) :
    ∀ v, v ∉ A → v ∉ B → (C.colourGraph a).degree v = (C.colourGraph b).degree v := by
  intro v ha hb
  have hv := hSat v (mem_compl.mpr (fun h => (mem_union.mp h).elim ha hb))
  rw [colour_degree_of_saturated C v hv a,colour_degree_of_saturated C v hv b]

private theorem exists_side_balanced_coloring (C : M.EdgeColoring k) (A B : Finset V)
    (hAB : Disjoint A B) (hEven : Even ((A ∪ B)ᶜ.card))
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k)
    (hDegrees : (∑ v ∈ A, M.degree v) = ∑ v ∈ B, M.degree v) :
    ∃ D : M.EdgeColoring k, ∀ i, sideCount D A i = sideCount D B i := by
  let b (D : M.EdgeColoring k) (i : Fin k) := sideCount D A i - sideCount D B i
  let energy (D : M.EdgeColoring k) := ∑ i, (b D i)^2
  obtain ⟨D,_,hMin⟩ := exists_minimum_energy C (fun _ => True) trivial energy
    (fun F => sum_nonneg (fun _ _ => sq_nonneg _))
  have hSum : ∑ i, b D i = 0 := by
    simp only [b,sum_sub_distrib,sum_sideCount]
    exact sub_eq_zero.mpr (by exact_mod_cast hDegrees)
  refine ⟨D,?_⟩
  suffices hNonpos : ∀ i, b D i ≤ 0 by
    intro i
    have hh := (sum_eq_sum_iff_of_le (s := (univ : Finset (Fin k)))
      (fun j _ => hNonpos j)).mp (by simpa using hSum) i (mem_univ _)
    exact sub_eq_zero.mp hh
  intro a
  by_contra! ha
  obtain ⟨j,hj⟩ : ∃ j, b D j < 0 := by
    by_contra! hh
    have hh' := (sum_eq_sum_iff_of_le (s := (univ : Finset (Fin k)))
      (fun i _ => hh i)).mp (by simpa using hSum.symm) a (mem_univ _)
    omega
  have hab : a ≠ j := by rintro rfl; omega
  have ha' : 2 ≤ b D a := by
    obtain ⟨n,hn⟩ := sideCount_gap_even D A B hAB hEven hSat a
    change b D a = n+n at hn
    omega
  have hj' : b D j ≤ -2 := by
    obtain ⟨n,hn⟩ := sideCount_gap_even D A B hAB hEven hSat j
    change b D j = n+n at hn
    omega
  have hdiff : (∑ v ∈ B, (((D.colourGraph a).degree v : ℤ) - (D.colourGraph j).degree v)) <
      (∑ v ∈ A, (((D.colourGraph a).degree v : ℤ) - (D.colourGraph j).degree v)) := by
    rw [sum_sub_distrib,sum_sub_distrib]
    change sideCount D B a - sideCount D B j < sideCount D A a - sideCount D A j
    dsimp [b] at ha' hj'
    omega
  obtain ⟨z,hz⟩ := exists_component_imbalance_transfer D a j A B hAB
    (outside_side_degrees_agree D A B hSat a j) hdiff
  simp only [sum_sub_distrib] at hz
  let S := D.componentSet a j z
  change (sideCount D (A ∩ S) a - sideCount D (A ∩ S) j) -
    (sideCount D (B ∩ S) a - sideCount D (B ∩ S) j) = 2 at hz
  let F := D.swapClosed a j S (D.component_closed a j z)
  obtain ⟨hAa,hAj,hAr⟩ := sideCount_after_swap D a j S A (D.component_closed a j z) hab
  obtain ⟨hBa,hBj,hBr⟩ := sideCount_after_swap D a j S B (D.component_closed a j z) hab
  have hd := two_colour_energy_drop (b D) (b F) a j hab 2 (by norm_num) (by omega)
    (by dsimp only [b,F] at *; omega) (by dsimp only [b,F] at *; omega)
    (fun i hi hj => by simp only [b,F,hAr i hi hj,hBr i hi hj])
  exact (not_lt_of_ge (hMin F trivial)) hd


private theorem exists_balanced_swap_set (C : M.EdgeColoring k) (a b : Fin k)
    (A B : Finset V) (hAB : Disjoint A B)
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k)
    (hA : sideCount C A b < sideCount C A a)
    (hB : sideCount C B b < sideCount C B a) :
    ∃ S : Finset V, (∀ u v, 0 < C.col s(u,v) a + C.col s(u,v) b → (u ∈ S ↔ v ∈ S)) ∧
      ∃ p : ℤ, 1 ≤ p ∧ p ≤ 2 ∧ sideCount C (A ∩ S) a - sideCount C (A ∩ S) b = p ∧
        sideCount C (B ∩ S) a - sideCount C (B ∩ S) b = p := by
  let D := (C.twoColourGraph a b).ConnectedComponent
  let diff (v : V) := ((C.colourGraph a).degree v : ℤ) - (C.colourGraph b).degree v
  let x (z : D) := ∑ v ∈ A ∩ C.componentSet a b z, diff v
  let y (z : D) := ∑ v ∈ B ∩ C.componentSet a b z, diff v
  have hx : 0 < ∑ z : D, x z := by
    dsimp only [x]
    rw [sum_component_side]
    simp only [diff,sum_sub_distrib]
    exact sub_pos.mpr hA
  have hy : 0 < ∑ z : D, y z := by
    dsimp only [y]
    rw [sum_component_side]
    simp only [diff,sum_sub_distrib]
    exact sub_pos.mpr hB
  have hxEq (z : D) : x z =
      sideCount C (A ∩ C.componentSet a b z) a - sideCount C (A ∩ C.componentSet a b z) b := by
    simp [x,diff,sideCount,sum_sub_distrib]
  have hyEq (z : D) : y z =
      sideCount C (B ∩ C.componentSet a b z) a - sideCount C (B ∩ C.componentSet a b z) b := by
    simp [y,diff,sideCount,sum_sub_distrib]
  rcases exists_balanced_component_transfer univ x y
      (fun z _ => component_side_contributions C a b z A B hAB
        (outside_side_degrees_agree C A B hSat a b)) hx hy with
    ⟨z,_,hxz,hyz⟩ | ⟨z,_,t,_,hne,hAgree,hLo,hHi⟩
  · exact ⟨C.componentSet a b z,C.component_closed a b z,1,le_rfl,by norm_num,
      (hxEq z).symm.trans hxz,(hyEq z).symm.trans hyz⟩
  · let S := C.componentSet a b z
    let T := C.componentSet a b t
    have hDisj : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      have h₁ : (C.twoColourGraph a b).connectedComponentMk v = z := by
        simpa only [S,MultiGraph.EdgeColoring.componentSet,Set.mem_toFinset,
          ConnectedComponent.mem_supp_iff] using hv
      have h₂ : (C.twoColourGraph a b).connectedComponentMk v = t := by
        simpa only [T,MultiGraph.EdgeColoring.componentSet,Set.mem_toFinset,
          ConnectedComponent.mem_supp_iff] using hw
      exact hne (h₁.symm.trans h₂)
    have hClosed u v (h : 0 < C.col s(u,v) a + C.col s(u,v) b) :
        u ∈ S ∪ T ↔ v ∈ S ∪ T := by
      simp only [mem_union,C.component_closed a b z u v h,C.component_closed a b t u v h,S,T]
    have hAdd (F : Finset V) (i : Fin k) :
        sideCount C (F ∩ (S ∪ T)) i =
          sideCount C (F ∩ S) i + sideCount C (F ∩ T) i := by
      unfold sideCount
      rw [inter_union_distrib_left,sum_union (hDisj.mono inter_subset_right inter_subset_right)]
    refine ⟨S ∪ T,hClosed,x z+x t,hLo,hHi,?_,?_⟩
    · rw [hAdd,hAdd,hxEq,hxEq]
      dsimp only [S,T]
      ring
    · rw [hAdd,hAdd,hAgree,hyEq,hyEq]
      change sideCount C (B ∩ S) a + sideCount C (B ∩ T) a -
        (sideCount C (B ∩ S) b + sideCount C (B ∩ T) b) =
        sideCount C (B ∩ S) a - sideCount C (B ∩ S) b +
        (sideCount C (B ∩ T) a - sideCount C (B ∩ T) b)
      ring

/-- Chen–Shan, Lemma 3.9. The resulting proper coloring covers all
exceptional vertices in every color, has equal side counts in every
color, and the side counts differ by at most two between colors. -/
theorem exists_balanced_equitable_outside_coloring
    (C : M.EdgeColoring k) (A B : Finset V)
    (hAB : Disjoint A B) (hEven : Even ((A ∪ B)ᶜ.card))
    (hSat : ∀ v ∈ (A ∪ B)ᶜ, M.degree v = k)
    (hDegrees : (∑ v ∈ A, M.degree v) = ∑ v ∈ B, M.degree v) :
    ∃ D : M.EdgeColoring k, (∀ i, sideCount D A i = sideCount D B i) ∧
      (∀ i j, sideCount D A i ≤ sideCount D A j + 2) ∧
      (∀ v ∈ (A ∪ B)ᶜ, ∀ i, (D.colourGraph i).degree v = 1) ∧
      (∀ i, (k : ℤ) * sideCount D A i ≤ (∑ v ∈ A, (M.degree v : ℤ)) + 2*k) := by
  obtain ⟨C',hC'⟩ := exists_side_balanced_coloring C A B hAB hEven hSat hDegrees
  let P (D : M.EdgeColoring k) := ∀ i, sideCount D A i = sideCount D B i
  let energy (D : M.EdgeColoring k) := ∑ i, (sideCount D A i)^2
  obtain ⟨D,hD,hMin⟩ := exists_minimum_energy C' P hC' energy
    (fun F => sum_nonneg (fun _ _ => sq_nonneg _))
  have heq : ∀ i j, sideCount D A i ≤ sideCount D A j + 2 := by
    intro a b
    by_contra! hg
    have hab : a ≠ b := by rintro rfl; omega
    have h₁ : sideCount D A b < sideCount D A a := by omega
    have h₂ : sideCount D B b < sideCount D B a := by rw [← hD b,← hD a]; exact h₁
    obtain ⟨S,hClosed,p,hp,hp',hA,hB⟩ := exists_balanced_swap_set D a b A B hAB hSat h₁ h₂
    let F := D.swapClosed a b S hClosed
    obtain ⟨hAa,hAb,hAr⟩ := sideCount_after_swap D a b S A hClosed hab
    obtain ⟨hBa,hBb,hBr⟩ := sideCount_after_swap D a b S B hClosed hab
    simp only [hA] at hAa hAb
    simp only [hB] at hBa hBb
    have hF : P F := by
      intro i
      by_cases hi : i = a
      · subst i
        dsimp only [F]
        rw [hAa,hBa,hD]
      · by_cases hj : i = b
        · subst i
          dsimp only [F]
          rw [hAb,hBb,hD]
        · exact (hAr i hi hj).trans ((hD i).trans (hBr i hi hj).symm)
    have hdrop := two_colour_energy_drop (sideCount D A) (sideCount F A) a b hab p
      (by omega) (by omega) hAa hAb hAr
    exact (not_lt_of_ge (hMin F hF)) hdrop
  refine ⟨D,hD,heq,fun v hv i => colour_degree_of_saturated D v (hSat v hv) i,?_⟩
  intro i
  have hh := sum_le_sum (s := (univ : Finset (Fin k))) (fun j _ => heq i j)
  rw [sum_add_distrib,sum_sideCount] at hh
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm (k : ℤ) 2] using hh

end OverfullWork.ChenShan
