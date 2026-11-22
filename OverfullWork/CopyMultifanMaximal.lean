module

public import OverfullWork.CopyMultifanElementary

@[expose] public section


/-! # Construct a maximal labelled-copy multifan and prove closure -/
namespace OverfullWork.CopyMultifan
open Finset ShannonColouring
open scoped Classical
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {ends : I → V × V} {s : Finset I} {k : ℕ} {c : I → Fin k}
variable {x : V} {e : I} {L : ℕ} {y : ℕ → V} {g : ℕ → I}
set_option maxHeartbeats 12000000

theorem exists_other {h : I} (hx : Incident ends h x) : ∃ z, Joins ends h x z := by
  rcases hx with hx|hx
  · exact ⟨(ends h).2,by dsimp only [Joins];rw [hx]⟩
  · exact ⟨(ends h).1,by dsimp only [Joins];rw [hx,Sym2.eq_swap]⟩

theorem IsFan.length_le (hF : IsFan ends s c x e L y g) : L ≤ Fintype.card V := by
  have hh := card_le_card_of_injOn y (fun i (_ : i ∈ range L) => mem_univ (y i)) (by
    intro i hi j hj hij
    exact hF.inj i (mem_range.mp hi) j (mem_range.mp hj) hij)
  simpa only [card_range,card_univ] using hh

theorem exists_maximal {z : V} (hj : Joins ends e x z) :
    ∃ L y g, IsFan ends s c x e L y g ∧
      ∀ m y' g', IsFan ends s c x e m y' g' → m ≤ L := by
  let P : ℕ → Prop := fun m => ∃ y g, IsFan ends s c x e m y g
  have hP1 : P 1 := by
    refine ⟨fun _ => z,fun _ => e,by decide,rfl,fun _ _ => hj,?_,?_,?_⟩
    · intro i hi j hj _;omega
    · intro i hi0 hi;omega
    · intro i hi0 hi;omega
  have hsize : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  have hs := Nat.findGreatest_spec hsize hP1
  obtain ⟨y,g,hF⟩ := hs
  refine ⟨Nat.findGreatest P (Fintype.card V),y,g,hF,?_⟩
  intro m y' g' hm
  by_contra! hlt
  exact Nat.findGreatest_is_greatest hlt hm.length_le ⟨y',g',hm⟩

theorem IsFan.closed (hF : IsFan ends s c x e L y g)
    (hloop : ∀ h, (ends h).1 ≠ (ends h).2) (he : e ∉ s) (hc : ProperOn ends s c)
    (hNo : ¬∃ c' : I → Fin k, ProperOn ends (insert e s) c')
    (hmax : ∀ m y' g', IsFan ends s c x e m y' g' → m ≤ L) :
    ∀ i, i < L → ∀ a, Misses ends s c (y i) a →
      ∃ h, h ∈ s ∧ ∃ j, j < L ∧ Joins ends h x (y j) ∧ c h=a := by
  intro i hi a hm
  have hnx : ¬Misses ends s c x a := fun hx => hF.not_common_root hloop he hc hNo hi hx hm
  simp only [Misses,not_forall,not_not] at hnx
  obtain ⟨h,hh,hx,hcol⟩ := hnx
  obtain ⟨z,hz⟩ := exists_other hx
  by_cases hzold : ∃ j, j < L ∧ y j=z
  · obtain ⟨j,hj,hyj⟩ := hzold
    exact ⟨h,hh,j,hj,by rwa [hyj],hcol⟩
  have hznew : ∀ j, j < L → y j ≠ z := by simpa only [not_exists,not_and] using hzold
  let y' := fun n => if n < L then y n else z
  let g' := fun n => if n < L then g n else h
  have hnew : IsFan ends s c x e (L+1) y' g' := by
    refine ⟨by omega,?_,?_,?_,?_,?_⟩
    · exact (if_pos hF.pos).trans hF.start
    · intro n hn
      by_cases hnL : n < L
      · simpa only [y',g',if_pos hnL] using hF.joins n hnL
      · simpa only [y',g',if_neg hnL] using hz
    · intro n hn m hm hsame
      by_cases hnL : n < L <;> by_cases hmL : m < L
      · simp only [y',if_pos hnL,if_pos hmL] at hsame
        exact hF.inj n hnL m hmL hsame
      · simp only [y',if_pos hnL,if_neg hmL] at hsame
        exact False.elim (hznew n hnL hsame)
      · simp only [y',if_neg hnL,if_pos hmL] at hsame
        exact False.elim (hznew m hmL hsame.symm)
      · omega
    · intro n hn0 hn
      by_cases hnL : n < L
      · simpa only [g',if_pos hnL] using hF.colored n hn0 hnL
      · simpa only [g',if_neg hnL] using hh
    · intro n hn0 hn
      by_cases hnL : n < L
      · obtain ⟨j,hjn,hmiss⟩ := hF.step n hn0 hnL
        refine ⟨j,hjn,?_⟩
        simpa only [y',g',if_pos (show j < L by omega),if_pos hnL] using hmiss
      · have hnEq : n=L := by omega
        refine ⟨i,by omega,?_⟩
        simpa only [y',g',if_pos hi,if_neg hnL,hcol] using hm
  have hbad := hmax (L+1) y' g' hnew
  omega

end OverfullWork.CopyMultifan
