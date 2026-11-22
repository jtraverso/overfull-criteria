module

public import OverfullWork.TwoCentreRegularCompletion

@[expose] public section


/-! A stronger completion: added edges meet at least one of the two centres.
Consequently every all-ordinary induced subgraph remains unchanged. -/
namespace OverfullWork.TwoCentreStarCompletion
open SimpleGraph Finset TwoCentreRegularCompletion
open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]
set_option maxHeartbeats 5000000

def pair (f g : W → ℕ) (k : ℕ) : Sum Bool W → Sum Bool W → ℕ
  | Sum.inl i, Sum.inl j => if i=j then 0 else k
  | Sum.inl i, Sum.inr w => if i then g w else f w
  | Sum.inr w, Sum.inl i => if i then g w else f w
  | Sum.inr _, Sum.inr _ => 0

theorem pair_symm (f g : W → ℕ) (k : ℕ) (a b : Sum Bool W) :
    pair f g k a b=pair f g k b a := by
  cases a <;> cases b <;> simp only [pair,eq_comm]

def graph (f g : W → ℕ) (k : ℕ) : MultiGraph (Sum Bool W) where
  mult := Sym2.lift ⟨pair f g k,pair_symm f g k⟩
  loopless e he := by
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab := Sym2.mk_isDiag_iff.mp he
      subst b
      cases a <;> simp [pair]

@[simp] theorem mult_pair (f g : W → ℕ) (k : ℕ) (a b : Sum Bool W) :
    (graph f g k).mult s(a,b)=pair f g k a b := rfl

theorem degree_left (f g : W → ℕ) (k : ℕ) :
    (graph f g k).degree (Sum.inl false)=k+∑ w, f w := by
  rw [MultiGraph.degree_eq_sum_mult,Fintype.sum_sum_type,Fintype.sum_bool]
  simp [pair]

theorem degree_right (f g : W → ℕ) (k : ℕ) :
    (graph f g k).degree (Sum.inl true)=k+∑ w, g w := by
  rw [MultiGraph.degree_eq_sum_mult,Fintype.sum_sum_type,Fintype.sum_bool]
  simp [pair]

theorem degree_ordinary (f g : W → ℕ) (k : ℕ) (w : W) :
    (graph f g k).degree (Sum.inr w)=f w+g w := by
  rw [MultiGraph.degree_eq_sum_mult,Fintype.sum_sum_type,Fintype.sum_bool]
  simp [pair,Nat.add_comm]

theorem exists_completion (M : MultiGraph (Sum Bool W)) (D : ℕ)
    (hD : ∀ v, M.degree v ≤ D) (heven : Even (Fintype.card (Sum Bool W)))
    (hOrder : M.degree (Sum.inl false) ≤ M.degree (Sum.inl true))
    (hGap : M.degree (Sum.inl true) ≤ M.degree (Sum.inl false)+ordinaryDeficit M D)
    (hSmall : ordinaryDeficit M D+M.degree (Sum.inl false)+M.degree (Sum.inl true) ≤ 2*D) :
    ∃ J : MultiGraph (Sum Bool W),
      (∀ v, J.degree v=D-M.degree v) ∧ (M.addCopies J).IsRegularOfDegree D ∧
      (∀ u v : W, J.mult s(Sum.inr u,Sum.inr v)=0) := by
  let a := D-M.degree (Sum.inl false)
  let b := D-M.degree (Sum.inl true)
  let e := fun w : W => D-M.degree (Sum.inr w)
  let E := ordinaryDeficit M D
  have hA := hD (Sum.inl false)
  have hB := hD (Sum.inl true)
  have hab : b ≤ a := by dsimp only [a,b];omega
  have hbal : a ≤ b+E := by dsimp only [a,b,E];omega
  have hE : E ≤ a+b := by dsimp only [a,b,E];omega
  have hParity : Even (a+b+E) := by
    have hh := deficit_even M D hD heven
    rwa [deficit_sum] at hh
  obtain ⟨t,ht⟩ := hParity
  let k := (a+b-E)/2
  have hkA : k ≤ a := by dsimp only [k];omega
  have hkB : k ≤ b := by dsimp only [k];omega
  have hk : 2*k+E=a+b := by dsimp only [k];omega
  have hAlloc : a-k ≤ ∑ w, e w := by change a-k ≤ E;omega
  obtain ⟨f,hf,hSum⟩ := MultiGraph.bounded_allocation e (a-k) hAlloc
  let g := fun w => e w-f w
  have hG : (∑ w, g w)=b-k := by
    have hSumAll : (∑ w, g w)+(∑ w, f w)=E := by
      rw [←sum_add_distrib]
      change (∑ w, (e w-f w+f w))=∑ w, e w
      exact sum_congr rfl (fun w _ => Nat.sub_add_cancel (hf w))
    omega
  let J := graph f g k
  have hJ : ∀ v, J.degree v=D-M.degree v := by
    intro v
    cases v with
    | inl i =>
      cases i
      · rw [degree_left,hSum]
        change k+(a-k)=a
        omega
      · rw [degree_right,hG]
        change k+(b-k)=b
        omega
    | inr w =>
      rw [degree_ordinary]
      exact Nat.add_sub_of_le (hf w)
  refine ⟨J,hJ,?_,fun _ _ => rfl⟩
  intro v
  rw [MultiGraph.degree_addCopies,hJ]
  exact Nat.add_sub_of_le (hD v)

end OverfullWork.TwoCentreStarCompletion
