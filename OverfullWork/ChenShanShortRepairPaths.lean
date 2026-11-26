module

public import OverfullWork.ChenShanPathImbalance
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

private theorem directedPathArcs_subset_of_steps {G : Finset (V × V)} {l : ℕ}
    (f : Fin (l+1) ↪ V) (h : ∀ i : Fin l, (f i.castSucc, f i.succ) ∈ G) :
    directedPathArcs l f ⊆ G := by
  intro e he
  obtain ⟨i,_,rfl⟩ := mem_map.mp he
  exact h i

/-- Short directed paths supplied by large neighborhoods around three cyclic classes.
Neighborhoods and intersections are taken after excluding a given set. -/
theorem exists_short_repair_path (part : V → ZMod 3) (G : Finset (V × V))
    (F : Finset V) (u v : V) (hne : u ≠ v)
    (hArc : ∀ a b, (a,b) ∈ G → part b = part a + 1)
    (hOut : ∀ a, ∃ b, b ∉ insert u (insert v F) ∧ (a,b) ∈ G)
    (hIn : ∀ b, ∃ a, a ∉ insert u (insert v F) ∧ (a,b) ∈ G)
    (hTwo : ∀ a b, part b = part a + 2 →
      ∃ x, x ∉ insert u (insert v F) ∧ (a,x) ∈ G ∧ (x,b) ∈ G) :
    ∃ l : ℕ, l ≤ 4 ∧ ∃ f : Fin (l+1) ↪ V,
      f 0 = u ∧ f (Fin.last l) = v ∧ directedPathArcs l f ⊆ G ∧
      ∀ i : Fin (l+1), i ≠ 0 → i ≠ Fin.last l → f i ∉ F := by
  have hClass : part v = part u ∨ part v = part u + 1 ∨
      part v = part u + 2 := by
    have hAll : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    rcases hAll (part v - part u) with h | h | h
    · left; linear_combination h
    · right; left; linear_combination h
    · right; right; linear_combination h
  rcases hClass with h | h | h
  · obtain ⟨x,hx,hux⟩ := hOut u
    have hxv : part v = part x + 2 := by
      rw [h,hArc u x hux]
      rw [add_assoc,show (1 : ZMod 3)+2=0 by decide,add_zero]
    obtain ⟨y,hy,hxy,hyv⟩ := hTwo x v hxv
    simp only [mem_insert, not_or] at hx hy
    have hxy' : x ≠ y := by
      intro eq
      have hY := hArc x y hxy
      rw [eq] at hY
      exact (by decide : (1 : ZMod 3) ≠ 0) (by linear_combination -hY)
    let f : Fin 4 ↪ V := ⟨![u,x,y,v], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
    refine ⟨3,by decide,f,rfl,rfl,directedPathArcs_subset_of_steps f ?_,?_⟩
    · intro i
      fin_cases i <;> first | exact hux | exact hxy | exact hyv
    · intro i hi hl
      fin_cases i
      · exact (hi rfl).elim
      · exact hx.2.2
      · exact hy.2.2
      · exact (hl rfl).elim
  · obtain ⟨x,hx,hux⟩ := hOut u
    obtain ⟨z,hz,hzv⟩ := hIn v
    have hzx : part z = part x + 2 := by
      have hC := hArc z v hzv
      rw [h] at hC
      rw [hArc u x hux]
      have h3 : (1 : ZMod 3) + 2 = 0 := by decide
      rw [add_assoc,h3,add_zero]
      linear_combination -hC
    obtain ⟨y,hy,hxy,hyz⟩ := hTwo x z hzx
    simp only [mem_insert, not_or] at hx hy hz
    have hDifferent {a b} (hab : (a,b) ∈ G) : a ≠ b := by
      intro eq
      have hC := hArc a b hab
      rw [eq] at hC
      exact (by decide : (1 : ZMod 3) ≠ 0) (by linear_combination -hC)
    have hxz : x ≠ z := by
      intro eq
      rw [eq] at hzx
      exact (by decide : (2 : ZMod 3) ≠ 0) (by linear_combination -hzx)
    have hxy' := hDifferent hxy
    have hyz' := hDifferent hyz
    let f : Fin 5 ↪ V := ⟨![u,x,y,z,v], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
    refine ⟨4,by decide,f,rfl,rfl,directedPathArcs_subset_of_steps f ?_,?_⟩
    · intro i
      fin_cases i <;> first | exact hux | exact hxy | exact hyz | exact hzv
    · intro i hi hl
      fin_cases i
      · exact (hi rfl).elim
      · exact hx.2.2
      · exact hy.2.2
      · exact hz.2.2
      · exact (hl rfl).elim
  · obtain ⟨x,hx,hux,hxv⟩ := hTwo u v h
    simp only [mem_insert, not_or] at hx
    let f : Fin 3 ↪ V := ⟨![u,x,v], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
    refine ⟨2,by decide,f,rfl,rfl,directedPathArcs_subset_of_steps f ?_,?_⟩
    · intro i
      fin_cases i <;> first | exact hux | exact hxv
    · intro i hi hl
      fin_cases i <;> first | exact (hi rfl).elim | exact (hl rfl).elim | exact hx.2.2

end OverfullWork.ChenShan
