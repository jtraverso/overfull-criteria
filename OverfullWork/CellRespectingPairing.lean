module

public import OverfullWork.PairedPartition
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum

@[expose] public section


/-! # Constructed pairings within even cells

This is the finite pairing step of CMS Lemma 5.4. Evenness of the given
cells is explicit. Each cell is paired by a finite equivalence and the
pairings are assembled; no compatible pairing is assumed as an oracle.
-/
namespace OverfullWork.CellRespectingPairing
open Finset
open scoped Classical
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem exists_pairing (f : V→I) (m : ℕ) (hcard : Fintype.card V=2*m)
    (hEven : ∀i,Even (Fintype.card {v : V // f v=i})) :
    ∃e : (Fin m×Bool) ≃ V,∀j,f (e (j,false))=f (e (j,true)) := by
  let a:=fun i=>Fintype.card {v : V // f v=i}/2
  have ha:∀i,Fintype.card {v : V // f v=i}=2*a i:=by
    intro i
    obtain ⟨k,hk⟩:=hEven i
    dsimp [a]
    omega
  let eCell:=fun i=>(Fintype.equivOfCardEq (show
      Fintype.card (Fin (a i)×Bool)=Fintype.card {v : V // f v=i} by
        simp [ha i,Nat.mul_comm]) : (Fin (a i)×Bool) ≃ {v : V // f v=i})
  let J:=Σi,Fin (a i)
  let E:J×Bool ≃ V:=(Equiv.sigmaProdDistrib (fun i=>Fin (a i)) Bool).trans
    ((Equiv.sigmaCongrRight eCell).trans (Equiv.sigmaFiberEquiv f))
  have hJ:Fintype.card J=m:=by
    have hh:=Fintype.card_congr E
    simp only [Fintype.card_prod,Fintype.card_bool] at hh
    omega
  let index:Fin m ≃ J:=(Fintype.equivFinOfCardEq hJ).symm
  let e:(Fin m×Bool) ≃ V:=(Equiv.prodCongr index (Equiv.refl Bool)).trans E
  refine ⟨e,?_⟩
  intro j
  change f ((eCell (index j).1) ((index j).2,false)).val=
    f ((eCell (index j).1) ((index j).2,true)).val
  exact ((eCell (index j).1) ((index j).2,false)).property.trans
    ((eCell (index j).1) ((index j).2,true)).property.symm

def partner {m : ℕ} (e : (Fin m×Bool) ≃ V) (v : V) : V :=
  e ((e.symm v).1,!(e.symm v).2)

theorem partner_apply {m : ℕ} (e : (Fin m×Bool) ≃ V) (j : Fin m) (b : Bool) :
    partner e (e (j,b))=e (j,!b) := by simp [partner]

theorem partner_involutive {m : ℕ} (e : (Fin m×Bool) ≃ V) :
    Function.Involutive (partner e) := by
  intro v
  obtain ⟨⟨j,b⟩,rfl⟩:=e.surjective v
  simp only [partner_apply,Bool.not_not]

theorem partner_ne {m : ℕ} (e : (Fin m×Bool) ≃ V) (v : V) : partner e v≠v := by
  obtain ⟨⟨j,b⟩,rfl⟩:=e.surjective v
  rw [partner_apply]
  intro hh
  have hb:=congrArg Prod.snd (e.injective hh)
  cases b <;> cases hb

theorem partner_cell {m : ℕ} (f : V→I) (e : (Fin m×Bool) ≃ V)
    (hCell : ∀j,f (e (j,false))=f (e (j,true))) (v : V) : f (partner e v)=f v := by
  obtain ⟨⟨j,b⟩,rfl⟩:=e.surjective v
  rw [partner_apply]
  cases b
  · exact (hCell j).symm
  · exact hCell j

theorem partner_mem_iff {m : ℕ} (e : (Fin m×Bool) ≃ V) (A : Finset V)
    (hSep : ∀j,(e (j,true)∈A ↔ e (j,false)∉A)) (v : V) :
    partner e v∈A ↔ v∉A := by
  obtain ⟨⟨j,b⟩,rfl⟩:=e.surjective v
  rw [partner_apply]
  cases b
  · exact hSep j
  · simpa only [not_not,Bool.not_true] using (hSep j).not.symm

/-- Separating the constructed pairs divides every cell exactly in half. -/
theorem cell_halves {m : ℕ} (f : V→I) (e : (Fin m×Bool) ≃ V)
    (hCell : ∀j,f (e (j,false))=f (e (j,true))) (A : Finset V)
    (hSep : ∀j,(e (j,true)∈A ↔ e (j,false)∉A)) (i : I) :
    (A.filter fun v=>f v=i).card=(Aᶜ.filter fun v=>f v=i).card := by
  apply card_bij (fun v _=>partner e v)
  · intro v hv
    obtain ⟨hvA,hvi⟩:=mem_filter.mp hv
    refine mem_filter.mpr ⟨mem_compl.mpr ?_,?_⟩
    · intro hp
      exact ((partner_mem_iff e A hSep v).mp hp) hvA
    · rw [partner_cell f e hCell,hvi]
  · intro v _ w _ hvw
    exact (partner_involutive e).injective hvw
  · intro v hv
    obtain ⟨hvA,hvi⟩:=mem_filter.mp hv
    refine ⟨partner e v,mem_filter.mpr ⟨?_,?_⟩,partner_involutive e v⟩
    · exact (partner_mem_iff e A hSep v).mpr (mem_compl.mp hvA)
    · rw [partner_cell f e hCell,hvi]

/-- A specified pair in one cell can be made a genuine pair of the
constructed pairing by exchanging its second vertex with the existing
partner of the first. This exchange stays within the same cell. -/
theorem exists_pairing_with_pair (f : V→I) (m : ℕ) (hcard : Fintype.card V=2*m)
    (hEven : ∀i,Even (Fintype.card {v : V // f v=i}))
    (x y : V) (hxy : x≠y) (hSame : f x=f y) :
    ∃e : (Fin m×Bool) ≃ V,(∀j,f (e (j,false))=f (e (j,true))) ∧
      ∃j,(e (j,false)=x ∧ e (j,true)=y) ∨ (e (j,false)=y ∧ e (j,true)=x) := by
  obtain ⟨e,hCell⟩:=exists_pairing f m hcard hEven
  let z:=partner e x
  let σ:=Equiv.swap y z
  let e':(Fin m×Bool) ≃ V:=e.trans σ
  have hz:f z=f y:=(partner_cell f e hCell x).trans hSame
  have hσ:∀v,f (σ v)=f v:=by
    intro v
    by_cases hy:v=y
    · subst v
      simpa only [σ,Equiv.swap_apply_left] using hz
    by_cases hz':v=z
    · subst v
      simpa only [σ,Equiv.swap_apply_right] using hz.symm
    · simp [σ,Equiv.swap_apply_def,hy,hz']
  have hσx:σ x=x:=by
    have hxz:x≠z:=(partner_ne e x).symm
    simp [σ,Equiv.swap_apply_def,hxy,hxz]
  refine ⟨e',?_,?_⟩
  · intro j
    exact (hσ (e (j,false))).trans ((hCell j).trans (hσ (e (j,true))).symm)
  · obtain ⟨⟨j,b⟩,hj⟩:=e.surjective x
    have hz':z=e (j,!b):=by simp only [z,←hj,partner_apply]
    have hx':e' (j,b)=x:=by change σ (e (j,b))=x;rw [hj,hσx]
    have hy':e' (j,!b)=y:=by
      change σ (e (j,!b))=y
      rw [←hz']
      exact Equiv.swap_apply_right _ _
    refine ⟨j,?_⟩
    cases b
    · exact Or.inl ⟨hx',by simpa only [Bool.not_false] using hy'⟩
    · exact Or.inr ⟨by simpa only [Bool.not_true] using hy',hx'⟩

end OverfullWork.CellRespectingPairing
